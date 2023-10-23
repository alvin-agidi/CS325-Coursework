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
#include "llvm/TargetParser/Host.h"

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
    VOID_TOK = -3,   // "void"
    FLOAT_TOK = -4,  // "float"
    BOOL_TOK = -5,   // "bool"

    // keywords
    EXTERN = -6,   // "extern"
    IF = -7,       // "if"
    ELSE = -8,     // "else"
    WHILE = -9,    // "while"
    RETURN = -10,  // "return"
    // TRUE   = -12,     // "true"
    // FALSE   = -13,     // "false"

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

static std::string IdentifierStr;  // Filled in if IDENT
static int IntVal;                 // Filled in if INT_LIT
static bool BoolVal;               // Filled in if BOOL_LIT
static float FloatVal;             // Filled in if FLOAT_LIT
static std::string StringVal;      // Filled in if String Literal
static int lineNo, columnNo;
static std::map<char, int> BinopPrecedence;

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
/// gettok - Return the next token from standard input.
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
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */

// program ::= extern_list decl_list
static void parser() {
    // add body
}

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken() {
    if (tok_buffer.size() == 0)
        tok_buffer.push_back(gettok());

    TOKEN temp = tok_buffer.front();
    tok_buffer.pop_front();

    return CurTok = temp;
}

static std::unique_ptr<ExprAST> ParseIntExpr() {
    auto Result = std::make_unique<IntExprAST>(IntVal);
    getNextToken();  // consume the number
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseFloatExpr() {
    auto Result = std::make_unique<FloatExprAST>(FloatVal);
    getNextToken();  // consume the number
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseBoolExpr() {
    auto Result = std::make_unique<BoolExprAST>(BoolVal);
    getNextToken();  // consume the number
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseBinaryExpr() {
    auto Result = std::make_unique<BinaryExprAST>(IdentifierStr, LHS, RHS);
    getNextToken();  // consume the number
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseParenExpr() {
    getNextToken();  // eat (.
    auto V = ParseExpression();
    if (!V)
        return nullptr;

    if (CurTok != ')')
        return LogError("expected ')'");
    getNextToken();  // eat ).
    return V;
}

static std::unique_ptr<ExprAST> ParsePrimaryExpr() {
    switch (CurTok.type) {
        default:
            return LogError("unknown token when expecting an expression");
        case IDENT:
            return ParseIdentifierExpr();
        case INT_LIT:
            return ParseIntExpr();
        case FLOAT_LIT:
            return ParseFloatExpr();
        case BOOL_LIT:
            return ParseBoolExpr();
        case "(":
            return ParseParenExpr();
    }
}

static std::unique_ptr<ExprAST> ParseExpression() {
    auto LHS = ParsePrimary();
    if (!LHS)
        return nullptr;

    return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS) {
    // If this is a binop, find its precedence.
    while (true) {
        int TokPrec = GetTokPrecedence();

        // If this is a binop that binds at least as tightly as the current binop,
        // consume it, otherwise we are done.
        if (TokPrec < ExprPrec)
            return LHS;
        // Okay, we know this is a binop.
        int BinOp = CurTok;
        getNextToken();  // eat binop

        // Parse the primary expression after the binary operator.
        auto RHS = ParsePrimary();
        if (!RHS)
            return nullptr;

        // If BinOp binds less tightly with RHS than the operator after RHS, let
        // the pending operator take RHS as its LHS.
        int NextPrec = GetTokPrecedence();
        if (TokPrec < NextPrec) {
            RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
            if (!RHS)
                return nullptr;
        }
        // Merge LHS/RHS.
        LHS = std::make_unique<BinaryExprAST>(BinOp, std::move(LHS),
                                              std::move(RHS));
    }  // loop around to the top of the while loop.
}

static std::unique_ptr<PrototypeAST> ParsePrototype() {
    if (CurTok != tok_identifier)
        return LogErrorP("Expected function name in prototype");

    std::string FnName = IdentifierStr;
    getNextToken();

    if (CurTok != '(')
        return LogErrorP("Expected '(' in prototype");

    // Read the list of argument names.
    std::vector<std::string> ArgNames;
    while (getNextToken() == tok_identifier)
        ArgNames.push_back(IdentifierStr);
    if (CurTok != ')')
        return LogErrorP("Expected ')' in prototype");

    // success.
    getNextToken();  // eat ')'.

    return std::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}

static std::unique_ptr<PrototypeAST> ParseExtern() {
    getNextToken();  // eat extern.
    return ParsePrototype();
}

static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
    if (auto E = ParseExpression()) {
        // Make an anonymous proto.
        auto Proto = std::make_unique<PrototypeAST>("", std::vector<std::string>());
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
    }
    return nullptr;
}

static std::unique_ptr<FunctionAST> ParseDefinition() {
    getNextToken();  // eat def.
    auto Proto = ParsePrototype();
    if (!Proto) return nullptr;

    if (auto E = ParseExpression())
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
    return nullptr;
}

static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
    std::string IdName = IdentifierStr;
    getNextToken();     // eat identifier.
    if (CurTok != '(')  // Simple variable ref.
        return std::make_unique<VariableExprAST>(IdName);

    // Call.
    getNextToken();  // eat (
    std::vector<std::unique_ptr<ExprAST>> Args;
    if (CurTok != ')') {
        while (true) {
            if (auto Arg = ParseExpression())
                Args.push_back(std::move(Arg));
            else
                return nullptr;

            if (CurTok == ')')
                break;

            if (CurTok != ',')
                return LogError("Expected ')' or ',' in argument list");
            getNextToken();
        }
    }

    // Eat the ')'.
    getNextToken();

    return std::make_unique<CallExprAST>(IdName, std::move(Args));
}

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

/// ASTnode - Base class for all AST nodes.
class ASTnode {
   public:
    virtual ~ASTnode() {}
    virtual Value* codegen() = 0;
    virtual std::string to_string() const { return ""; };
};

/// IntASTnode - Class for integer literals like 1, 2, 10,
class IntASTnode : public ASTnode {
    int Val;
    TOKEN Tok;
    std::string Name;

   public:
    IntASTnode(TOKEN tok, int val)
        : Val(val), Tok(tok) {
    }
    virtual Value* codegen() override;
    // virtual std::string to_string() const override {
    // return a sting representation of this AST node
    //};
};

/// FloatASTnode - Class for floating literals
class FloatASTnode : public ASTnode {
    gloat Val;
    TOKEN Tok;
    std::string Name;

   public:
    FloatASTnode(TOKEN tok, float val)
        : Val(val), Tok(tok) {
    }
    virtual Value* codegen() override;
    // virtual std::string to_string() const override {
    // return a sting representation of this AST node
    //};
};

/// FloatASTnode - Class for floating literals
class BoolASTnode : public ASTnode {
    bool Val;
    TOKEN Tok;
    std::string Name;

   public:
    BoolASTnode(TOKEN tok, bool val)
        : Val(val), Tok(tok) {
    }
    virtual Value* codegen() override;
    // virtual std::string to_string() const override {
    // return a sting representation of this AST node
    //};
};

class VariableExprAST : public ExprAST {
    std::string Name;

   public:
    VariableExprAST(const std::string& Name)
        : Name(Name) {
    }
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
    char Op;
    std::unique_ptr<ExprAST> LHS, RHS;

   public:
    BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                  std::unique_ptr<ExprAST> RHS)
        : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {
    }
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
    std::string Callee;
    std::vector<std::unique_ptr<ExprAST>> Args;

   public:
    CallExprAST(const std::string& Callee,
                std::vector<std::unique_ptr<ExprAST>> Args)
        : Callee(Callee), Args(std::move(Args)) {
    }
};

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream& operator<<(llvm::raw_ostream& os,
                                     const ASTnode& ast) {
    os << ast.to_string();
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
    BinopPrecedence['<'] = 10;
    BinopPrecedence['+'] = 20;
    BinopPrecedence['-'] = 20;
    BinopPrecedence['*'] = 40;

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
    while (CurTok.type != EOF_TOK) {
        fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
                CurTok.type);
        getNextToken();
    }
    fprintf(stderr, "Lexer Finished\n");

    // Make the module, which holds all the code.
    TheModule = std::make_unique<Module>("mini-c", TheContext);

    // Run the parser now.
    parser();
    fprintf(stderr, "Parsing Finished\n");

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
