#include <string.h>

#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string>
#include <system_error>
#include <unordered_set>
#include <utility>
#include <vector>

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
// #include "llvm/TargetParser/Host.h"

using namespace llvm;
using namespace llvm::sys;

FILE* pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE {

    IDENT = -1,         // [a-zA-Z_][a-zA-Z_0-9]*
    ASSIGN = int('='),  // '='

    // delimiters
    LBRA = int('{'),   // left brace
    RBRA = int('}'),   // right brace
    LPAR = int('('),   // left parenthesis
    RPAR = int(')'),   // right parenthesis
    SC = int(';'),     // semicolon
    COMMA = int(','),  // comma

    // types
    INT_TOK = -2,    // "int"
    FLOAT_TOK = -4,  // "float"
    BOOL_TOK = -5,   // "bool"
    VOID_TOK = -3,   // "void"

    // keywords
    EXTERN = -6,   // "extern"
    IF = -7,       // "if"
    ELSE = -8,     // "else"
    WHILE = -9,    // "while"
    RETURN = -10,  // "return"
                   // TRUE   = -12,    // "true"
                   // FALSE   = -13,    // "false"

    // literals
    INT_LIT = -14,    // [0-9]+
    FLOAT_LIT = -15,  // [0-9]+.[0-9]+
    BOOL_LIT = -16,   // "true" or "false" key words

    // logical operators
    AND = -17,  // "&&"
    OR = -18,   // "||"

    // operators
    PLUS = int('+'),     // addition or unary plus
    MINUS = int('-'),    // substraction or unary negative
    ASTERIX = int('*'),  // multiplication
    DIV = int('/'),      // division
    MOD = int('%'),      // modular
    NOT = int('!'),      // unary negation

    // comparison operators
    EQ = -19,       // equal
    NE = -20,       // not equal
    LE = -21,       // less than or equal to
    LT = int('<'),  // less than
    GE = -23,       // greater than or equal to
    GT = int('>'),  // greater than

    // special tokens
    EOF_TOK = 0,  // signal end of file

    // invalid
    INVALID = -100  // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN {
    int type = -100;
    std::string lexeme;
    int lineNo;
    int columnNo;
};

struct TokenSet {
    std::unordered_set<int> tokenSet;

    TokenSet(std::unordered_set<int> tokenSet) : tokenSet(std::move(tokenSet)) {}

    bool contains(int element) const {
        return tokenSet.find(element) != tokenSet.end();
    }
};

static std::string IdentifierStr;  // Filled in if IDENT
static int IntVal;                 // Filled in if INT_LIT
static bool BoolVal;               // Filled in if BOOL_LIT
static float FloatVal;             // Filled in if FLOAT_LIT
static std::string StringVal;      // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type) {
    TOKEN return_tok;
    return_tok.type = tok_type;
    return_tok.lexeme = lexVal;
    return_tok.lineNo = lineNo;
    return_tok.columnNo = columnNo - lexVal.length() - 1;
    return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
// gettok - Return the next token from standard input.
static TOKEN gettok() {
    static int LastChar = ' ';
    static int NextChar = ' ';

    // Skip any whitespace.
    while (isspace(LastChar)) {
        if (LastChar == '\n' || LastChar == '\r') {
            lineNo++;
            columnNo = 1;
        }
        LastChar = getc(pFile);
        columnNo++;
    }

    if (isalpha(LastChar) || LastChar == '_') {  // identifier: [a-zA-Z_][a-zA-Z_0-9]*
        IdentifierStr = LastChar;
        columnNo++;

        while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
            IdentifierStr += LastChar;
            columnNo++;
        }

        if (IdentifierStr == "int")
            return returnTok("int", INT_TOK);
        if (IdentifierStr == "bool")
            return returnTok("bool", BOOL_TOK);
        if (IdentifierStr == "float")
            return returnTok("float", FLOAT_TOK);
        if (IdentifierStr == "void")
            return returnTok("void", VOID_TOK);
        if (IdentifierStr == "bool")
            return returnTok("bool", BOOL_TOK);
        if (IdentifierStr == "extern")
            return returnTok("extern", EXTERN);
        if (IdentifierStr == "if")
            return returnTok("if", IF);
        if (IdentifierStr == "else")
            return returnTok("else", ELSE);
        if (IdentifierStr == "while")
            return returnTok("while", WHILE);
        if (IdentifierStr == "return")
            return returnTok("return", RETURN);
        if (IdentifierStr == "true") {
            BoolVal = true;
            return returnTok("true", BOOL_LIT);
        }
        if (IdentifierStr == "false") {
            BoolVal = false;
            return returnTok("false", BOOL_LIT);
        }

        return returnTok(IdentifierStr.c_str(), IDENT);
    }

    if (isdigit(LastChar) || LastChar == '.') {  // Number: [0-9]+.
        std::string NumStr;

        if (LastChar == '.') {  // Floatingpoint Number: .[0-9]+
            do {
                NumStr += LastChar;
                LastChar = getc(pFile);
                columnNo++;
            } while (isdigit(LastChar));

            FloatVal = strtof(NumStr.c_str(), nullptr);
            return returnTok(NumStr, FLOAT_LIT);
        } else {
            do {  // Start of Number: [0-9]+
                NumStr += LastChar;
                LastChar = getc(pFile);
                columnNo++;
            } while (isdigit(LastChar));

            if (LastChar == '.') {  // Floatingpoint Number: [0-9]+.[0-9]+)
                do {
                    NumStr += LastChar;
                    LastChar = getc(pFile);
                    columnNo++;
                } while (isdigit(LastChar));

                FloatVal = strtof(NumStr.c_str(), nullptr);
                return returnTok(NumStr, FLOAT_LIT);
            } else {  // Integer : [0-9]+
                IntVal = strtod(NumStr.c_str(), nullptr);
                return returnTok(NumStr, INT_LIT);
            }
        }
    }

    if (LastChar == '=') {
        NextChar = getc(pFile);
        if (NextChar == '=') {  // EQ: ==
            LastChar = getc(pFile);
            columnNo += 2;
            return returnTok("==", EQ);
        } else {
            LastChar = NextChar;
            columnNo++;
            return returnTok("=", ASSIGN);
        }
    }
    if (LastChar == '{') {
        LastChar = getc(pFile);
        columnNo++;
        return returnTok("{", LBRA);
    }
    if (LastChar == '}') {
        LastChar = getc(pFile);
        columnNo++;
        return returnTok("}", RBRA);
    }
    if (LastChar == '(') {
        LastChar = getc(pFile);
        columnNo++;
        return returnTok("(", LPAR);
    }
    if (LastChar == ')') {
        LastChar = getc(pFile);
        columnNo++;
        return returnTok(")", RPAR);
    }
    if (LastChar == ';') {
        LastChar = getc(pFile);
        columnNo++;
        return returnTok(";", SC);
    }
    if (LastChar == ',') {
        LastChar = getc(pFile);
        columnNo++;
        return returnTok(",", COMMA);
    }
    if (LastChar == '&') {
        NextChar = getc(pFile);
        if (NextChar == '&') {  // AND: &&
            LastChar = getc(pFile);
            columnNo += 2;
            return returnTok("&&", AND);
        } else {
            LastChar = NextChar;
            columnNo++;
            return returnTok("&", int('&'));
        }
    }
    if (LastChar == '|') {
        NextChar = getc(pFile);
        if (NextChar == '|') {  // OR: ||
            LastChar = getc(pFile);
            columnNo += 2;
            return returnTok("||", OR);
        } else {
            LastChar = NextChar;
            columnNo++;
            return returnTok("|", int('|'));
        }
    }
    if (LastChar == '!') {
        NextChar = getc(pFile);
        if (NextChar == '=') {  // NE: !=
            LastChar = getc(pFile);
            columnNo += 2;
            return returnTok("!=", NE);
        } else {
            LastChar = NextChar;
            columnNo++;
            return returnTok("!", NOT);
            ;
        }
    }
    if (LastChar == '<') {
        NextChar = getc(pFile);
        if (NextChar == '=') {  // LE: <=
            LastChar = getc(pFile);
            columnNo += 2;
            return returnTok("<=", LE);
        } else {
            LastChar = NextChar;
            columnNo++;
            return returnTok("<", LT);
        }
    }
    if (LastChar == '>') {
        NextChar = getc(pFile);
        if (NextChar == '=') {  // GE: >=
            LastChar = getc(pFile);
            columnNo += 2;
            return returnTok(">=", GE);
        } else {
            LastChar = NextChar;
            columnNo++;
            return returnTok(">", GT);
        }
    }
    if (LastChar == '/') {  // could be division or could be the start of a comment
        LastChar = getc(pFile);
        columnNo++;
        if (LastChar == '/') {  // definitely a comment
            do {
                LastChar = getc(pFile);
                columnNo++;
            } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

            if (LastChar != EOF)
                return gettok();
        } else
            return returnTok("/", DIV);
    }

    // Check for end of file.  Don't eat the EOF.
    if (LastChar == EOF) {
        columnNo++;
        return returnTok("0", EOF_TOK);
    }

    // Otherwise, just return the character as its ascii value.
    int ThisChar = LastChar;
    std::string s(1, ThisChar);
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

// ASTnode - Base class for all AST nodes.
class ASTnode {
   public:
    ASTnode() {}
    virtual ~ASTnode() {}
    // virtual Value* codegen() = 0;
    virtual std::string toString() const { return ""; };
};

template <typename ASTnode>
std::string to_string(const std::vector<ASTnode>& list, std::string delimiter = " ") {
    std::string result;
    for (auto& astNode : list) {
        result += (*astNode).toString() + delimiter;
    }
    if (!list.empty()) {
        result.erase(result.length() - delimiter.length());
    }
    return std::move(result);
}

class LocalDeclarationASTnode : public ASTnode {
    int type;
    std::string name;

   public:
    LocalDeclarationASTnode(){};
    LocalDeclarationASTnode(int type, std::string name) : type(type), name(name) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return std::to_string(type) + " " + name;
    };
};

class ParamASTnode : public ASTnode {
    int type;
    std::string name;

   public:
    ParamASTnode(){};
    ParamASTnode(int type, std::string name) : type(type), name(name) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return std::to_string(type) + " " + name;
    };
};

class StatementASTnode : public ASTnode {
   public:
    StatementASTnode(){};
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return "";
    };
};

class ExpressionASTnode : public StatementASTnode {
    std::string binOp;
    std::string op;
    std::unique_ptr<ExpressionASTnode> subExpression;
    std::unique_ptr<ExpressionASTnode> subExpression2;
    std::string name;
    std::vector<std::unique_ptr<ExpressionASTnode>> args;
    std::string intVal;
    std::string floatVal;
    std::string boolVal;

   public:
    ExpressionASTnode(){};
    ExpressionASTnode(std::unique_ptr<ExpressionASTnode> subExpression, std::string binOp, std::unique_ptr<ExpressionASTnode> subExpression2) : subExpression(std::move(subExpression)), binOp(binOp), subExpression2(std::move(subExpression2)) {}
    ExpressionASTnode(std::string name, std::string binOp, std::unique_ptr<ExpressionASTnode> subExpression, std::vector<std::unique_ptr<ExpressionASTnode>> args) : name(name), binOp(binOp), subExpression(std::move(subExpression)), args(std::move(args)) {}
    ExpressionASTnode(std::string op, std::unique_ptr<ExpressionASTnode> subExpression, std::string name, std::vector<std::unique_ptr<ExpressionASTnode>> args, std::string intVal, std::string floatVal, std::string boolVal) : op(op), subExpression(std::move(subExpression)), name(name), args(std::move(args)), intVal(intVal), floatVal(floatVal), boolVal(boolVal) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        std::string string = intVal + floatVal + boolVal + name;
        if (!args.empty()) {
            string += "(" + to_string(args, ", ") + ")";
        }
        if (name != "" && binOp == "" && subExpression) {
            string += "=";
        }
        if (!subExpression2) {
            string += binOp;
        }
        if (subExpression) {
            string += op + subExpression->toString();
        };
        if (subExpression2) {
            string += binOp + subExpression2->toString();
        }
        return string;
    };
};

class ReturnStatementASTnode : public StatementASTnode {
    std::unique_ptr<ExpressionASTnode> expression;

   public:
    ReturnStatementASTnode(){};
    ReturnStatementASTnode(std::unique_ptr<ExpressionASTnode> expression) : expression(std::move(expression)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return "return " + expression->toString();
    };
};

class BlockASTnode : public ASTnode {
    std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarationList;
    std::vector<std::unique_ptr<StatementASTnode>> statementList;

   public:
    BlockASTnode(){};
    BlockASTnode(std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarationList,
                 std::vector<std::unique_ptr<StatementASTnode>> statementList) : localDeclarationList(std::move(localDeclarationList)), statementList(std::move(statementList)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return " { " + to_string(localDeclarationList) + " " + to_string(statementList) + " }";
    };
};

class WhileStatementASTnode : public StatementASTnode {
    std::unique_ptr<ExpressionASTnode> expression;
    std::unique_ptr<BlockASTnode> block;

   public:
    WhileStatementASTnode(){};
    WhileStatementASTnode(std::unique_ptr<ExpressionASTnode> expression,
                          std::unique_ptr<BlockASTnode> block) : expression(std::move(expression)), block(std::move(block)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return "while (" + expression->toString() + ")" + block->toString();
    };
};

class ElseStatementASTnode : public StatementASTnode {
    std::unique_ptr<BlockASTnode> block;

   public:
    ElseStatementASTnode(){};
    ElseStatementASTnode(std::unique_ptr<BlockASTnode> block) : block(std::move(block)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return " else" + block->toString();
    };
};

class IfStatementASTnode : public StatementASTnode {
    std::unique_ptr<ExpressionASTnode> expression;
    std::unique_ptr<BlockASTnode> block;
    std::unique_ptr<ElseStatementASTnode> elseStatement;

   public:
    IfStatementASTnode(){};
    IfStatementASTnode(std::unique_ptr<ExpressionASTnode> expression,
                       std::unique_ptr<BlockASTnode> block,
                       std::unique_ptr<ElseStatementASTnode> elseStatement) : expression(std::move(expression)), block(std::move(block)), elseStatement(std::move(elseStatement)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return "if (" + expression->toString() + ")" + block->toString() + elseStatement->toString();
    };
};

class DeclarationASTnode : public ASTnode {
    int type;
    std::string name;
    std::vector<std::unique_ptr<ParamASTnode>> paramList;
    std::unique_ptr<BlockASTnode> block;

   public:
    DeclarationASTnode(){};
    DeclarationASTnode(int type, std::string name, std::vector<std::unique_ptr<ParamASTnode>> paramList,
                       std::unique_ptr<BlockASTnode> block) : type(type), name(name), paramList(std::move(paramList)), block(std::move(block)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return std::to_string(type) + " " + name + "(" + to_string(paramList, ", ") + ")" + block->toString();
    };
};

class ExternASTnode : public ASTnode {
    int type;
    std::string name;
    std::vector<std::unique_ptr<ParamASTnode>> paramList;

   public:
    ExternASTnode(){};
    ExternASTnode(int type, std::string name, std::vector<std::unique_ptr<ParamASTnode>> paramList) : type(type), name(name), paramList(std::move(paramList)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return "extern " + std::to_string(type) + " " + name + "(" + to_string(paramList, ", ") + ");";
    };
};

class ProgramASTnode : public ASTnode {
    std::vector<std::unique_ptr<ExternASTnode>> externList;
    std::vector<std::unique_ptr<DeclarationASTnode>> declarationList;

   public:
    ProgramASTnode(){};
    ProgramASTnode(std::vector<std::unique_ptr<ExternASTnode>> externList,
                   std::vector<std::unique_ptr<DeclarationASTnode>> declarationList) : externList(std::move(externList)), declarationList(std::move(declarationList)) {}
    // virtual Value* codegen() override;
    virtual std::string toString() const override {
        return to_string(externList) + " " + to_string(declarationList);
    };
};
//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
// token the parser is looking at.  getNextToken reads another token from the
// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;
static std::map<std::string, int> BinopPrecedence;

static TOKEN getNextToken() {
    if (tok_buffer.size() == 0)
        tok_buffer.push_back(gettok());

    TOKEN temp = tok_buffer.front();
    tok_buffer.pop_front();

    return CurTok = temp;
}

// LogError* - These are little helper functions for error handling.
std::unique_ptr<ASTnode> LogError(const char* Str) {
    fprintf(stderr, "Error: %s\n", Str);
    return nullptr;
}

std::unique_ptr<ASTnode> LogErrorP(const char* Str) {
    LogError(Str);
    return nullptr;
}

// struct Production {
//     static TokenSet firstSet;
// };
// TokenSet Production::firstSet = TokenSet({});

struct Expression {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse();
};
TokenSet Expression::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// arg_list ::= "," expr arg_list | epsilon
struct ArgList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExpressionASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing arg list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExpressionASTnode>> argList;
        while (firstSet.contains(CurTok.type)) {
            getNextToken();
            argList.emplace_back(std::move(Expression::Parse()));
        };
        return argList;
    }
};
TokenSet ArgList::firstSet = TokenSet({COMMA});

// args ::= expr arg_list | epsilon
struct Args {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExpressionASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing args", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExpressionASTnode>> args;
        if (Expression::firstSet.contains(CurTok.type)) {
            args.emplace_back(std::move(Expression::Parse()));
            std::vector<std::unique_ptr<ExpressionASTnode>> argList = ArgList::Parse();
            std::move(argList.begin(), argList.end(), std::back_inserter(args));
        }
        return args;
    }
};
TokenSet Args::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// ident_body ::= "(" args ")" | epsilon
struct IdentBody {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExpressionASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing identBody", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExpressionASTnode>> args;
        if (firstSet.contains(CurTok.type)) {
            getNextToken();
            args = Args::Parse();
            getNextToken();
        }
        return args;
    }
};
TokenSet IdentBody::firstSet = TokenSet({LPAR});

//  rval_term ::= "-" expr
//       | "!" expr
//       | "(" expr ")"
//       | IDENT ident_body
//       | INT_LIT | FLOAT_LIT | BOOL_LIT
struct RvalTerm {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing rvalterm", CurTok.lexeme.c_str(), CurTok.type);
        std::string op;
        std::unique_ptr<ExpressionASTnode> expression;
        std::string ident;
        std::vector<std::unique_ptr<ExpressionASTnode>> args;
        std::string intVal;
        std::string floatVal;
        std::string boolVal;
        switch (CurTok.type) {
            case IDENT:
                ident = CurTok.lexeme;
                getNextToken();
                args = IdentBody::Parse();
                break;
            case MINUS:
            case NOT:
                op = CurTok.lexeme;
                getNextToken();
                expression = Expression::Parse();
                break;
            case LPAR:
                getNextToken();
                expression = Expression::Parse();
                getNextToken();
                break;
            case INT_LIT:
                intVal = CurTok.lexeme;
                getNextToken();
                break;
            case FLOAT_LIT:
                floatVal = CurTok.lexeme;
                getNextToken();
                break;
            case BOOL_LIT:
                boolVal = CurTok.lexeme;
                getNextToken();
                break;
        }
        return std::make_unique<ExpressionASTnode>(op, std::move(expression), ident, std::move(args), intVal, floatVal, boolVal);
    }
};
TokenSet RvalTerm::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, INT_LIT, FLOAT_LIT, BOOL_LIT});

struct Rval6List {
    static TokenSet firstSet;
    static std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Parse();
};
TokenSet Rval6List::firstSet = TokenSet({ASTERIX, DIV, MOD});

struct Rval6 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse();
};
TokenSet Rval6::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// rval_6_list ::= "*" rval_6 | "/" rval_6 | "%" rval_6 | epsilon
std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Rval6List::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval6list", CurTok.lexeme.c_str(), CurTok.type);
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> rval6;
    if (Rval6List::firstSet.contains(CurTok.type)) {
        binOp = CurTok.lexeme;
        getNextToken();
        rval6 = Rval6::Parse();
    }
    return std::make_tuple(std::move(binOp), std::move(rval6));
}

// rval_6 ::= rval_term rval_6_list
std::unique_ptr<ExpressionASTnode> Rval6::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval6", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<ExpressionASTnode> rvalTerm = RvalTerm::Parse();
    std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> rval6List = Rval6List::Parse();
    std::string binOp = std::get<0>(rval6List);
    std::unique_ptr<ExpressionASTnode> rval6 = std::move(std::get<1>(rval6List));
    return std::make_unique<ExpressionASTnode>(std::move(rvalTerm), std::move(binOp), std::move(rval6));
}

struct Rval5List {
    static TokenSet firstSet;
    static std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Parse();
};
TokenSet Rval5List::firstSet = TokenSet({PLUS, MINUS});

struct Rval5 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse();
};
TokenSet Rval5::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// rval_5_list ::= "+" rval_5 | "-" rval_5 | epsilon
std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Rval5List::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval5list", CurTok.lexeme.c_str(), CurTok.type);
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> rval5;
    if (Rval5List::firstSet.contains(CurTok.type)) {
        binOp = CurTok.lexeme;
        getNextToken();
        rval5 = Rval5::Parse();
    }
    return std::make_tuple(std::move(binOp), std::move(rval5));
}

// rval_5 ::= rval_6 rval_5_list
std::unique_ptr<ExpressionASTnode> Rval5::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval5", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<ExpressionASTnode> rval6 = Rval6::Parse();
    std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> rval5List = Rval5List::Parse();
    std::string binOp = std::get<0>(rval5List);
    std::unique_ptr<ExpressionASTnode> rval5 = std::move(std::get<1>(rval5List));
    return std::make_unique<ExpressionASTnode>(std::move(rval6), std::move(binOp), std::move(rval5));
}

struct Rval4List {
    static TokenSet firstSet;
    static std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Parse();
};
TokenSet Rval4List::firstSet = TokenSet({LT, LE, GT, GE});

struct Rval4 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse();
};
TokenSet Rval4::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// rval_4_list ::= "<" rval_4 | "<=" rval_4 | ">" rval_4 | "=" rval_4 | epsilon
std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Rval4List::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval4list", CurTok.lexeme.c_str(), CurTok.type);
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> rval4;
    if (Rval4List::firstSet.contains(CurTok.type)) {
        binOp = CurTok.lexeme;
        getNextToken();
        rval4 = Rval4::Parse();
    }
    return std::make_tuple(std::move(binOp), std::move(rval4));
}

// rval_4 ::= rval_5 rval_4_list
std::unique_ptr<ExpressionASTnode> Rval4::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval4", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<ExpressionASTnode> rval5 = Rval5::Parse();
    std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> rval4List = Rval4List::Parse();
    std::string binOp = std::get<0>(rval4List);
    std::unique_ptr<ExpressionASTnode> rval4 = std::move(std::get<1>(rval4List));
    return std::make_unique<ExpressionASTnode>(std::move(rval5), std::move(binOp), std::move(rval4));
}

struct Rval3List {
    static TokenSet firstSet;
    static std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Parse();
};
TokenSet Rval3List::firstSet = TokenSet({EQ, NE});

struct Rval3 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse();
};
TokenSet Rval3::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// rval_3_list ::= "==" rval_3 | "!=" rval_3 | epsilon
std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Rval3List::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval3list", CurTok.lexeme.c_str(), CurTok.type);
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> rval3;
    if (Rval3List::firstSet.contains(CurTok.type)) {
        binOp = CurTok.lexeme;
        getNextToken();
        rval3 = Rval3::Parse();
    }
    return std::make_tuple(std::move(binOp), std::move(rval3));
}

// rval_3 ::= rval_4 rval_3_list
std::unique_ptr<ExpressionASTnode> Rval3::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval3", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<ExpressionASTnode> rval4 = Rval4::Parse();
    std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> rval3List = Rval3List::Parse();
    std::string binOp = std::get<0>(rval3List);
    std::unique_ptr<ExpressionASTnode> rval3 = std::move(std::get<1>(rval3List));
    return std::make_unique<ExpressionASTnode>(std::move(rval4), std::move(binOp), std::move(rval3));
}

struct Rval2List {
    static TokenSet firstSet;
    static std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Parse();
};
TokenSet Rval2List::firstSet = TokenSet({AND});

struct Rval2 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse();
};
TokenSet Rval2::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// rval_2_list ::= "&&" rval_2 | epsilon
std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Rval2List::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval2list", CurTok.lexeme.c_str(), CurTok.type);
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> rval2;
    if (Rval2List::firstSet.contains(CurTok.type)) {
        binOp = CurTok.lexeme;
        getNextToken();
        rval2 = Rval2::Parse();
    }
    return std::make_tuple(std::move(binOp), std::move(rval2));
}

// rval_2 ::= rval_3 rval_2_list
std::unique_ptr<ExpressionASTnode> Rval2::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval2", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<ExpressionASTnode> rval3 = std::move(Rval3::Parse());
    std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> rval2List = Rval2List::Parse();
    std::string binOp = std::get<0>(rval2List);
    std::unique_ptr<ExpressionASTnode> rval2 = std::move(std::get<1>(rval2List));
    return std::make_unique<ExpressionASTnode>(std::move(rval3), std::move(binOp), std::move(rval2));
}

struct Rval1List {
    static TokenSet firstSet;
    static std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Parse();
};
TokenSet Rval1List::firstSet = TokenSet({OR});

struct Rval1 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse();
};
TokenSet Rval1::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT});

// rval_1_list ::= "||" rval_1 | epsilon
std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> Rval1List::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval1list", CurTok.lexeme.c_str(), CurTok.type);
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> rval1;
    if (Rval1List::firstSet.contains(CurTok.type)) {
        binOp = CurTok.lexeme;
        getNextToken();
        rval1 = Rval1::Parse();
    }
    return std::make_tuple(std::move(binOp), std::move(rval1));
};

// rval_1 ::= rval_2 rval_1_list
std::unique_ptr<ExpressionASTnode> Rval1::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing rval1", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<ExpressionASTnode> rval2 = Rval2::Parse();
    std::tuple<std::string, std::unique_ptr<ExpressionASTnode>> rval1List = Rval1List::Parse();
    std::string binOp = std::get<0>(rval1List);
    std::unique_ptr<ExpressionASTnode> rval1 = std::move(std::get<1>(rval1List));
    return std::make_unique<ExpressionASTnode>(std::move(rval2), std::move(binOp), std::move(rval1));
};

// expr ::= IDENT "=" expr | rval_1
std::unique_ptr<ExpressionASTnode> Expression::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing expr", CurTok.lexeme.c_str(), CurTok.type);
    std::string ident;
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> expression;
    std::vector<std::unique_ptr<ExpressionASTnode>> args;
    if (CurTok.type == IDENT) {
        ident = CurTok.lexeme;
        getNextToken();
        if (CurTok.type == ASSIGN) {
            getNextToken();
            expression = std::move(Expression::Parse());
        } else if (Rval1List::firstSet.contains(CurTok.type) ||
                   Rval2List::firstSet.contains(CurTok.type) ||
                   Rval3List::firstSet.contains(CurTok.type) ||
                   Rval4List::firstSet.contains(CurTok.type) ||
                   Rval5List::firstSet.contains(CurTok.type) ||
                   Rval6List::firstSet.contains(CurTok.type)) {
            binOp = CurTok.lexeme;
            getNextToken();
            expression = std::move(Rval1::Parse());
        } else if (CurTok.type == LPAR) {
            args = std::move(IdentBody::Parse());
        }
    } else {
        expression = std::move(Rval1::Parse());
    }
    return std::make_unique<ExpressionASTnode>(std::move(ident), std::move(binOp), std::move(expression), std::move(args));
}

// expr_stmt ::= expr ";" | ";"
struct ExpressionStatement {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing expr stmt", CurTok.lexeme.c_str(), CurTok.type);
        std::unique_ptr<ExpressionASTnode> expression;
        if (Expression::firstSet.contains(CurTok.type)) {
            expression = Expression::Parse();
        }
        getNextToken();
        return expression;
    }
};
TokenSet ExpressionStatement::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, INT_LIT, FLOAT_LIT, BOOL_LIT, SC});

// return_stmt ::= "return" expr_stmt
struct ReturnStatement {
    static TokenSet firstSet;
    static std::unique_ptr<ReturnStatementASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing return", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();
        std::unique_ptr<ExpressionASTnode> expressionStatement = ExpressionStatement::Parse();
        return std::make_unique<ReturnStatementASTnode>(std::move(expressionStatement));
    }
};
TokenSet ReturnStatement::firstSet = TokenSet({RETURN});

struct Block {
    static TokenSet firstSet;
    static std::unique_ptr<BlockASTnode> Parse();
};
TokenSet Block::firstSet = TokenSet({LBRA});

// else_stmt  ::= "else" block | epsilon
struct ElseStatement {
    static TokenSet firstSet;
    static std::unique_ptr<ElseStatementASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing else", CurTok.lexeme.c_str(), CurTok.type);
        std::unique_ptr<BlockASTnode> block;
        if (firstSet.contains(CurTok.type)) {
            getNextToken();
            block = Block::Parse();
        }
        return std::make_unique<ElseStatementASTnode>(std::move(block));
    }
};
TokenSet ElseStatement::firstSet = TokenSet({ELSE});

// if_stmt ::= "if" "(" expr ")" block else_stmt
struct IfStatement {
    static TokenSet firstSet;
    static std::unique_ptr<IfStatementASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing if", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();
        getNextToken();
        std::unique_ptr<ExpressionASTnode> expression = Expression::Parse();
        getNextToken();
        std::unique_ptr<BlockASTnode> block = Block::Parse();
        std::unique_ptr<ElseStatementASTnode> elseStatement = ElseStatement::Parse();
        return std::make_unique<IfStatementASTnode>(std::move(expression), std::move(block), std::move(elseStatement));
    }
};
TokenSet IfStatement::firstSet = TokenSet({IF});
struct Statement {
    static TokenSet firstSet;
    static std::unique_ptr<StatementASTnode> Parse();
};
TokenSet Statement::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, INT_LIT, FLOAT_LIT, BOOL_LIT, SC, IF, WHILE, RETURN});

// while_stmt ::= "while" "(" expr ")" block
struct WhileStatement {
    static TokenSet firstSet;
    static std::unique_ptr<WhileStatementASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing while", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();
        getNextToken();
        std::unique_ptr<ExpressionASTnode> expression = Expression::Parse();
        getNextToken();
        std::unique_ptr<BlockASTnode> block = Block::Parse();
        return std::make_unique<WhileStatementASTnode>(std::move(expression), std::move(block));
    }
};
TokenSet WhileStatement::firstSet = TokenSet({WHILE});

// stmt ::= expr_stmt
//		| return_stmt
//      | while_stmt
//      | if_stmt
std::unique_ptr<StatementASTnode> Statement::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing stmt", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<StatementASTnode> statement;
    if (ReturnStatement::firstSet.contains(CurTok.type)) {
        statement = ReturnStatement::Parse();
    } else if (WhileStatement::firstSet.contains(CurTok.type)) {
        statement = WhileStatement::Parse();
    } else if (IfStatement::firstSet.contains(CurTok.type)) {
        statement = IfStatement::Parse();
    } else {
        statement = ExpressionStatement::Parse();
    }
    return statement;
}

// stmt_list ::= stmt stmt_list | epsilon
struct StatementList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<StatementASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing stmt list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<StatementASTnode>> statements;
        while (firstSet.contains(CurTok.type)) {
            statements.emplace_back(std::move(Statement::Parse()));
        }
        return statements;
    }
};
TokenSet StatementList::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, INT_LIT, FLOAT_LIT, BOOL_LIT, SC, IF, WHILE, RETURN});

// local_decl ::= var_type IDENT ";"
struct LocalDeclaration {
    static TokenSet firstSet;
    static std::unique_ptr<LocalDeclarationASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing local decl", CurTok.lexeme.c_str(), CurTok.type);
        int type = CurTok.type;
        getNextToken();  // eat type.
        std::string ident = CurTok.lexeme;
        getNextToken();
        getNextToken();
        return std::make_unique<LocalDeclarationASTnode>(std::move(type), std::move(ident));
    }
};
TokenSet LocalDeclaration::firstSet = TokenSet({INT_TOK, FLOAT_TOK, BOOL_TOK});

// local_decl_list ::= local_decl local_decl_list | epsilon
struct LocalDeclarationList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<LocalDeclarationASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing local decl list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarations;
        while (firstSet.contains(CurTok.type)) {
            localDeclarations.emplace_back(std::move(LocalDeclaration::Parse()));
        }
        return localDeclarations;
    }
};
TokenSet LocalDeclarationList::firstSet = TokenSet({INT_TOK, FLOAT_TOK, BOOL_TOK});

// block ::= "{" local_decl_list stmt_list "}"
std::unique_ptr<BlockASTnode> Block::Parse() {
    fprintf(stderr, "%s: %s with type %d\n", "Parsing block", CurTok.lexeme.c_str(), CurTok.type);
    getNextToken();  // eat "{".
    std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarations = LocalDeclarationList::Parse();
    std::vector<std::unique_ptr<StatementASTnode>> statements = StatementList::Parse();
    getNextToken();  // eat "}"
    return std::make_unique<BlockASTnode>(std::move(localDeclarations), std::move(statements));
}

// param ::= type_spec IDENT
struct Param {
    static TokenSet firstSet;
    static std::unique_ptr<ParamASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing param", CurTok.lexeme.c_str(), CurTok.type);
        int type = CurTok.type;
        getNextToken();  // eat type.
        std::string ident = CurTok.lexeme;
        getNextToken();
        return std::make_unique<ParamASTnode>(std::move(type), std::move(ident));
    }
};
TokenSet Param::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// param_list ::= "," param param_list | epsilon
struct ParamList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ParamASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing paramlist", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ParamASTnode>> paramList;
        while (firstSet.contains(CurTok.type)) {
            getNextToken();
            paramList.emplace_back(std::move(Param::Parse()));
        }
        return paramList;
    }
};
TokenSet ParamList::firstSet = TokenSet({COMMA});

// params ::= param param_list | epsilon
struct Params {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ParamASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing params", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ParamASTnode>> params;
        if (Param::firstSet.contains(CurTok.type)) {
            params.emplace_back(std::move(Param::Parse()));
            std::vector<std::unique_ptr<ParamASTnode>> paramList = ParamList::Parse();
            std::move(paramList.begin(), paramList.end(), std::back_inserter(params));
        }
        return params;
    }
};
TokenSet Params::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// func_body ::= "(" params ")" block
struct FunctionBody {
    static TokenSet firstSet;
    static std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing func body", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();
        std::vector<std::unique_ptr<ParamASTnode>> params = Params::Parse();
        getNextToken();
        std::unique_ptr<BlockASTnode> block = std::move(Block::Parse());
        return std::make_tuple(std::move(params), std::move(block));
    }
};
TokenSet FunctionBody::firstSet = TokenSet({LPAR});

// type_spec ::= "void" | var_type
//
// var_type ::= "int" | "float" | "bool"
//
// decl_body :: = ";" | func_body
struct DeclarationBody {
    static TokenSet firstSet;
    static std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing decl body", CurTok.lexeme.c_str(), CurTok.type);
        std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> functionBody;
        if (CurTok.type == SC) {
            getNextToken();
        } else {
            functionBody = FunctionBody::Parse();
        }
        return functionBody;
    }
};

// decl ::= "void" IDENT func_body | var_type IDENT decl_body
struct Declaration {
    static TokenSet firstSet;
    static std::unique_ptr<DeclarationASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing decl", CurTok.lexeme.c_str(), CurTok.type);
        std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> declarationBody;
        std::vector<std::unique_ptr<ParamASTnode>> params;
        std::unique_ptr<BlockASTnode> block;
        int type = CurTok.type;
        getNextToken();  // eat type.
        std::string ident = CurTok.lexeme;
        getNextToken();
        if (type == VOID_TOK) {
            declarationBody = FunctionBody::Parse();
        } else {
            declarationBody = DeclarationBody::Parse();
            params = std::move(std::get<0>(declarationBody));
            block = std::move(std::get<1>(declarationBody));
        }
        return std::make_unique<DeclarationASTnode>(std::move(type), std::move(ident), std::move(params), std::move(block));
    }
};
TokenSet Declaration::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// decl_list ::= decl decl_list | epsilon
struct DeclarationList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<DeclarationASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing decl list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<DeclarationASTnode>> declarationList;
        while (firstSet.contains(CurTok.type)) {
            declarationList.emplace_back(std::move(Declaration::Parse()));
        }
        return declarationList;
    }
};
TokenSet DeclarationList::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// extern ::= "extern" type_spec IDENT "(" params ")" ";"
struct Extern {
    static TokenSet firstSet;
    static std::unique_ptr<ExternASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing extern", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();  // eat extern.
        int type = CurTok.type;
        getNextToken();  // eat type.
        std::string ident = CurTok.lexeme;
        getNextToken();  // eat ident.
        getNextToken();
        std::vector<std::unique_ptr<ParamASTnode>> params = Params::Parse();
        getNextToken();
        getNextToken();
        return std::make_unique<ExternASTnode>(std::move(type), std::move(ident), std::move(params));
    }
};
TokenSet Extern::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// extern_list ::= extern extern_list | epsilon
struct ExternList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExternASTnode>> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing externlist", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExternASTnode>> externList;
        while (firstSet.contains(CurTok.type)) {
            externList.emplace_back(std::move(Extern::Parse()));
        };

        return externList;
    }
};
TokenSet ExternList::firstSet = TokenSet({EXTERN});

// program ::= extern_list decl decl_list
struct Program {
    static TokenSet firstSet;
    static std::unique_ptr<ProgramASTnode> Parse() {
        fprintf(stderr, "%s: %s with type %d\n", "Parsing program", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExternASTnode>> externList;
        std::vector<std::unique_ptr<DeclarationASTnode>> declarationList;
        if (ExternList::firstSet.contains(CurTok.type)) {
            externList = std::move(ExternList::Parse());
        }
        declarationList.emplace_back(std::move(Declaration::Parse()));
        if (DeclarationList::firstSet.contains(CurTok.type)) {
            std::vector<std::unique_ptr<DeclarationASTnode>> declarationListTail = std::move(DeclarationList::Parse());
            std::move(declarationListTail.begin(), declarationListTail.end(), std::back_inserter(declarationList));
        }
        getNextToken();
        return std::make_unique<ProgramASTnode>(std ::move(externList), std::move(declarationList));
    }
};

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

static std::unique_ptr<ProgramASTnode> Parser() {
    // fprintf(stderr, "ready> ");
    return std::move(Program::Parse());
}

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream& operator<<(llvm::raw_ostream& os,
                                     const ASTnode& ast) {
    os << ast.toString();
    return os;
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char** argv) {
    if (argc == 2) {
        pFile = fopen(argv[1], "r");
        if (pFile == NULL)
            perror("Error opening file");
    } else {
        std::cout << "Usage: ./code InputFile\n";
        return 1;
    }

    // initialize line number and column numbers to zero
    lineNo = 1;
    columnNo = 1;

    // get the first token
    getNextToken();
    // while (CurTok.type != EOF_TOK) {
    //     fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
    //             CurTok.type);
    //     getNextToken();
    // }
    // fprintf(stderr, "Lexer Finished\n");

    // Make the module, which holds all the code.
    TheModule = std::make_unique<Module>("mini-c", TheContext);

    // Run the parser now.
    std::unique_ptr<ProgramASTnode> programAST = Parser();
    fprintf(stderr, "Parsing Finished\n");

    fprintf(stderr, "%s\n", programAST->toString().c_str());
    fprintf(stderr, "AST node printing Finished\n");

    //********************* Start printing final IR **************************
    // Print out all of the generated code into a file called output.ll
    auto Filename = "output.ll";
    std::error_code EC;
    raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

    if (EC) {
        errs() << "Could not open file: " << EC.message();
        return 1;
    }
    // TheModule->print(errs(), nullptr); // print IR to terminal
    TheModule->print(dest, nullptr);
    //********************* End printing final IR ****************************

    fclose(pFile);  // close the file that contains the code that was parsed
    return 0;
}
