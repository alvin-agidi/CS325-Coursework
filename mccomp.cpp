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
#include "llvm/IR/GlobalVariable.h"
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
    FLOAT_TOK = -3,  // "float"
    INT_TOK = -4,    // "int"
    BOOL_TOK = -5,   // "bool"
    VOID_TOK = -2,   // "void"

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

    // compValarison operators
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

TokenSet TYPE_TOKENS = TokenSet({FLOAT_TOK, INT_TOK, BOOL_TOK, VOID_TOK});
TokenSet VAR_TYPE_TOKENS = TokenSet({FLOAT_TOK, INT_TOK, BOOL_TOK});

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
// Code Generation
//===----------------------------------------------------------------------===//
static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, AllocaInst*> NamedValues;

static std ::map<int, Type*> TypeMap{
    {FLOAT_TOK, Type::getFloatTy(TheContext)},
    {INT_TOK, Type::getInt32Ty(TheContext)},
    {BOOL_TOK, Type::getInt1Ty(TheContext)},
    {VOID_TOK, Type::getVoidTy(TheContext)}};

static std ::map<Type*, int> TypeHierarchy{
    {Type::getFloatTy(TheContext), FLOAT_TOK},
    {Type::getInt32Ty(TheContext), INT_TOK},
    {Type::getInt1Ty(TheContext), BOOL_TOK},
    {Type::getVoidTy(TheContext), VOID_TOK}};

static std ::map<int, std::string> TypeNames{
    {FLOAT_TOK, "float"},
    {INT_TOK, "int"},
    {BOOL_TOK, "bool"},
    {VOID_TOK, "void"}};

static Type* getMaxType(Value* val1, Value* val2) {
    if (val1->getType()->isFloatTy() || val2->getType()->isFloatTy()) {
        return Type::getFloatTy(TheContext);
    } else if (val1->getType() == Type::getInt32Ty(TheContext) || val2->getType() == Type::getInt32Ty(TheContext)) {
        return Type::getInt32Ty(TheContext);
    }
    return Type::getInt1Ty(TheContext);
}

// static Value* narrowFloat(Value* val, Type* type) {
//     if (type == TypeMap.at(INT_TOK)) {
//         return Builder.CreateFPToSI(val, Type::getInt32Ty(TheContext), "toInt");
//     } else if (type == TypeMap.at(BOOL_TOK)) {
//         return Builder.CreateFPToSI(val, Type::getInt1Ty(TheContext), "toBool");
//     }
//     return val;
// };

static Value* widen(Value* val, Type* type) {
    if (val->getType() == type) {
        return val;
    } else if (val->getType() == TypeMap.at(BOOL_TOK) && type == TypeMap.at(INT_TOK)) {
        return Builder.CreateZExt(val, Type::getInt32Ty(TheContext));
    }
    return Builder.CreateSIToFP(val, Type::getFloatTy(TheContext));
};

static std::tuple<Value*, Value*> widen(Value* val1, Value* val2, Type* type) {
    return std::make_tuple(widen(val1, type), widen(val2, type));
};

// static std::tuple<Value*, Value*> widenToFloat(Value* val1, Value* val2) {
//     if (!val1->getType()->isFloatTy()) {
//         val1 = Builder.CreateSIToFP(val1, Type::getFloatTy(TheContext));
//     }
//     if (!val2->getType()->isFloatTy()) {
//         val2 = Builder.CreateSIToFP(val2, Type::getFloatTy(TheContext));
//     }
//     return std::make_tuple(val1, val2);
// };

// static Value* widenToFloat(Value* val) {
//     if (!val->getType()->isFloatTy()) {
//         val = Builder.CreateSIToFP(val, Type::getFloatTy(TheContext));
//     }
//     return val;
// };

static AllocaInst* CreateEntryBlockAlloca(Function* func, Type* type, const std::string& varName) {
    IRBuilder<> TmpB(&func->getEntryBlock(), func->getEntryBlock().begin());
    return TmpB.CreateAlloca(type, 0, varName.c_str());
}

//===----------------------------------------------------------------------===//
// Lexer
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

static void putBackToken(TOKEN tok) {
    tok_buffer.push_front(tok);
}

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

// ASTnode - Base class for all AST nodes.
struct ASTnode {
    int lineNo = CurTok.lineNo;
    ASTnode() {}
    virtual ~ASTnode() {}
    virtual Value* codeGen() = 0;
    virtual std::string toFormattedString() const { return ""; };
    virtual std::string toString(std::string offset) const { return ""; };
};

//===----------------------------------------------------------------------===//
// Error Logging
//===----------------------------------------------------------------------===//
// logError* - These are little helper functions for error handling.
void logError(std::string Str) {
    throw std::runtime_error("Error: " + Str + "\n");
}

std::unique_ptr<ASTnode> logErrorNode(std::string Str) {
    logError(Str);
    return nullptr;
}

Value* logErrorValue(std::string Str) {
    logError(Str);
    return nullptr;
}

ReturnInst* logErrorRetInst(std::string Str) {
    logError(Str);
    return nullptr;
}

static Value* createIsTrue(Value* val, std::string str) {
    if (val->getType() == TypeMap.at(BOOL_TOK)) {
        return val;
    } else if (val->getType() == TypeMap.at(INT_TOK)) {
        return Builder.CreateICmpNE(val, Builder.getInt32(0), str);
    }
    return Builder.CreateFCmpUNE(val, ConstantFP::get(TheContext, APFloat(0.0f)), str);
}

template <typename ASTnode>
std::string to_string(const std::vector<ASTnode>& list, std::string delimiter = "") {
    std::string result;
    for (auto& astNode : list) {
        result += (*astNode).toString(delimiter) + "\n";
    }
    if (!list.empty()) {
        result.erase(result.length() - 1);
    }
    return std::move(result);
}

static std::string incrementOffset(std::string offset) {
    return offset + "\t";
};

static std::string branch = "|-------";

struct ParamASTnode : public ASTnode {
    int type;
    std::string name;

    ParamASTnode(){};
    ParamASTnode(int type, std::string name) : type(type), name(name) {}
    virtual Value* codeGen() override {
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return TypeNames.at(type) + " " + name;
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Param " + TypeNames.at(type) + " " + name;
    };
};

struct LocalDeclarationASTnode : public ASTnode {
    int type;
    std::string name;

    LocalDeclarationASTnode(){};
    LocalDeclarationASTnode(int type, std::string name) : type(type), name(name) {}
    virtual Value* codeGen() override {
        AllocaInst* alloca = Builder.CreateAlloca(TypeMap.at(type), nullptr, name);
        NamedValues[name] = alloca;
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return TypeNames.at(type) + " " + name;
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Local Declaration " + TypeNames.at(type) + " " + name;
    };
};

struct ExpressionASTnode : public ASTnode {};

struct BinaryExpressionASTnode : public ExpressionASTnode {
    std::string binOp;
    std::unique_ptr<ExpressionASTnode> LHSexpression;
    std::unique_ptr<ExpressionASTnode> RHSexpression;

    BinaryExpressionASTnode(){};
    BinaryExpressionASTnode(std::unique_ptr<ExpressionASTnode> LHSexpression,
                            std::string binOp,
                            std::unique_ptr<ExpressionASTnode> RHSexpression) : LHSexpression(std::move(LHSexpression)), binOp(binOp), RHSexpression(std::move(RHSexpression)) {}
    virtual Value* codeGen() override {
        Value* LHSval = LHSexpression->codeGen();
        if (!LHSval) return nullptr;
        if (binOp == "||" || binOp == "&&") {
            Function* func = Builder.GetInsertBlock()->getParent();
            BasicBlock* rhsBB = BasicBlock::Create(TheContext, "evalRHS", func);
            BasicBlock* endBB = BasicBlock::Create(TheContext, "endBinary", func);
            Value* resVal = createIsTrue(LHSval, "lhsTmp");
            AllocaInst* alloca = Builder.CreateAlloca(resVal->getType(), resVal);
            NamedValues[alloca->getName().str()] = alloca;
            if (binOp == "||") {
                Builder.CreateCondBr(resVal, endBB, rhsBB);
            } else {
                Builder.CreateCondBr(resVal, rhsBB, endBB);
            }
            Builder.SetInsertPoint(rhsBB);
            Value* RHSval = RHSexpression->codeGen();
            if (!RHSval) return nullptr;
            resVal = createIsTrue(RHSval, "rhsTmp");
            AllocaInst* var = NamedValues[alloca->getName().str()];
            Builder.CreateStore(resVal, var);
            Builder.CreateBr(endBB);
            rhsBB = Builder.GetInsertBlock();
            Builder.SetInsertPoint(endBB);
            return Builder.CreateLoad(var->getAllocatedType(), var, alloca->getName().str());
        }
        Value* RHSval = RHSexpression->codeGen();
        if (!RHSval) return nullptr;
        Type* maxType = getMaxType(LHSval, RHSval);
        std::tie(LHSval, RHSval) = widen(LHSval, RHSval, maxType);
        if (binOp == "==") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFCmpUEQ(LHSval, RHSval, "eqTmp");
            return Builder.CreateICmpEQ(LHSval, RHSval, "eqTmp");
        } else if (binOp == "!=") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFCmpUNE(LHSval, RHSval, "neTmp");
            return Builder.CreateICmpNE(LHSval, RHSval, "eqTmp");
        } else if (binOp == "<") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFCmpULT(LHSval, RHSval, "ltTmp");
            return Builder.CreateICmpSLT(LHSval, RHSval, "eqTmp");
        } else if (binOp == "<=") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFCmpULE(LHSval, RHSval, "leTmp");
            return Builder.CreateICmpSLE(LHSval, RHSval, "eqTmp");
        } else if (binOp == ">") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFCmpUGT(LHSval, RHSval, "gtTmp");
            return Builder.CreateICmpSGT(LHSval, RHSval, "eqTmp");
        } else if (binOp == ">=") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFCmpUGE(LHSval, RHSval, "geTmp");
            return Builder.CreateICmpSGE(LHSval, RHSval, "eqTmp");
        } else if (binOp == "+") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFAdd(LHSval, RHSval, "addTmp");
            return Builder.CreateAdd(LHSval, RHSval, "addTmp");
        } else if (binOp == "-") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFSub(LHSval, RHSval, "subTmp");
            return Builder.CreateSub(LHSval, RHSval, "subTmp");
        } else if (binOp == "*") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFMul(LHSval, RHSval, "mulTmp");
            return Builder.CreateMul(LHSval, RHSval, "mulTmp");
        } else if (binOp == "/") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFDiv(LHSval, RHSval, "divTmp");
            return Builder.CreateSDiv(LHSval, RHSval, "divTmp");
        } else if (binOp == "%") {
            if (maxType == TypeMap.at(FLOAT_TOK)) return Builder.CreateFRem(LHSval, RHSval, "remTmp");
            return Builder.CreateSRem(LHSval, RHSval, "remTmp");
        }
        return logErrorValue("Invalid binary operator: " + binOp);
    }
    virtual std::string toFormattedString() const override {
        return LHSexpression->toFormattedString() + binOp + RHSexpression->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Binary Expression " + binOp + "\n" +
               LHSexpression->toString(incOffset) + "\n" +
               RHSexpression->toString(incOffset);
    }
};

struct UnaryExpressionASTnode : public ExpressionASTnode {
    std::string op;
    std::unique_ptr<ExpressionASTnode> subExpression;

    UnaryExpressionASTnode(){};
    UnaryExpressionASTnode(std::string op, std::unique_ptr<ExpressionASTnode> subExpression) : op(op), subExpression(std::move(subExpression)) {}
    virtual Value* codeGen() override {
        Value* val = subExpression->codeGen();
        if (!val) return nullptr;

        if (op == "-") {
            if (val->getType() == TypeMap.at(FLOAT_TOK)) return Builder.CreateFNeg(val, "negTmp");
            if (val->getType() == TypeMap.at(INT_TOK)) return Builder.CreateNeg(val, "negTmp");
            return Builder.CreateNot(val, "negTmp");
        } else if (op == "!") {
            if (val->getType() == TypeMap.at(FLOAT_TOK)) return Builder.CreateFCmpUEQ(val, ConstantFP::get(TheContext, APFloat(0.0f)), "notTmp");
            if (val->getType() == TypeMap.at(INT_TOK)) return Builder.CreateICmpEQ(val, Builder.getInt32(0), "notTmp");
            return Builder.CreateICmpEQ(val, Builder.getInt1(0), "notTmp");
        }
        return logErrorValue("Undeclared operator: " + op);
    }
    virtual std::string toFormattedString() const override {
        return op + subExpression->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Unary Expression " + op + "\n" + subExpression->toString(incOffset);
    };
};

struct VariableASTnode : public ExpressionASTnode {
    std::string name;

    VariableASTnode(){};
    VariableASTnode(std::string name) : name(name) {}
    virtual Value* codeGen() override {
        if (AllocaInst* var = NamedValues[name]) {
            return Builder.CreateLoad(var->getAllocatedType(), var, name);
        } else if (GlobalVariable* gVar = TheModule->getGlobalVariable(name)) {
            return Builder.CreateLoad(gVar->getValueType(), gVar, name);
        }
        return logErrorValue("Undeclared variable: " + name);
    }
    virtual std::string toFormattedString() const override {
        return name;
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Variable " + name;
    };
};

struct FunctionCallASTnode : public ExpressionASTnode {
    std::string name;
    std::vector<std::unique_ptr<ExpressionASTnode>> args;

    FunctionCallASTnode(){};
    FunctionCallASTnode(std::string name,
                        std::vector<std::unique_ptr<ExpressionASTnode>> args) : name(name), args(std::move(args)) {}
    virtual Value* codeGen() override {
        Function* func = TheModule->getFunction(name);
        if (!func)
            return logErrorValue("Undeclared function: " + name + " (line " + std::to_string(lineNo) + ")");

        if (func->arg_size() != args.size())
            return logErrorValue("Incorrect number of arguments: " + std::to_string(func->arg_size()) + " expected, " + std::to_string(args.size()) + " given");

        std::vector<Value*> argVals;
        for (std::unique_ptr<ExpressionASTnode>& arg : args) {
            argVals.push_back(arg->codeGen());
            if (!argVals.back()) return nullptr;
        }
        return Builder.CreateCall(func, argVals, "callTmp");
    }
    virtual std::string toFormattedString() const override {
        return name + "(" + to_string(args, ", ") + ")";
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        std::string string = offset + branch + "Function Call " + name;
        if (!args.empty()) string += "\n " + to_string(args, incOffset);
        return string;
    };
};

struct LiteralASTnode : public ExpressionASTnode {
    std::string floatLit;
    std::string intLit;
    std::string boolLit;

    LiteralASTnode(){};
    LiteralASTnode(std::string floatLit,
                   std::string intLit,
                   std::string boolLit) : floatLit(floatLit), intLit(intLit), boolLit(boolLit) {}
    virtual Value* codeGen() override {
        if (floatLit != "") {
            return ConstantFP::get(TheContext, APFloat(std::stof(floatLit)));
        } else if (intLit != "") {
            return Builder.getInt32(std::stoi(intLit));
        } else if (boolLit != "") {
            return Builder.getInt1(boolLit != "false");
        }
        return logErrorValue("Invalid literal");
    }
    virtual std::string toFormattedString() const override {
        return floatLit + intLit + boolLit;
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Literal " + floatLit + intLit + boolLit;
    };
};

struct AssignmentExpressionASTnode : public ExpressionASTnode {
    std::string name;
    std::unique_ptr<ExpressionASTnode> subExpression;

    AssignmentExpressionASTnode(){};
    AssignmentExpressionASTnode(std::string name,
                                std::unique_ptr<ExpressionASTnode> subExpression) : name(name), subExpression(std::move(subExpression)) {}
    virtual Value* codeGen() override {
        Value* val = subExpression->codeGen();
        Type* valType = val->getType();
        Type* varType;
        AllocaInst* var;
        GlobalVariable* gVar;
        if ((var = NamedValues[name])) {
            varType = var->getAllocatedType();
        } else if ((gVar = TheModule->getGlobalVariable(name))) {
            varType = gVar->getValueType();
        } else {
            return logErrorValue("Undeclared variable: " + name);
        }
        val = widen(val, varType);
        if (var) {
            Builder.CreateStore(val, var);
        } else if (gVar) {
            Builder.CreateStore(val, gVar);
        }
        return val;
    }
    virtual std::string toFormattedString() const override {
        return name + "=" + subExpression->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Assignment Expression " + name + " =\n" +
               subExpression->toString(incOffset);
    };
};

struct StatementASTnode : public ASTnode {
    virtual ReturnInst* codeGen() { return nullptr; };
    virtual ReturnInst* codeGen(Type* funcReturnType) = 0;
};

struct ExpressionStatementASTnode : public StatementASTnode {
    std::unique_ptr<ExpressionASTnode> expression;

    ExpressionStatementASTnode(){};
    ExpressionStatementASTnode(std::unique_ptr<ExpressionASTnode> expression) : expression(std::move(expression)) {}
    virtual ReturnInst* codeGen(Type* funcReturnType) override {
        if (expression) {
            expression->codeGen();
        }
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return expression->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string string = "";
        if (expression) string += expression->toString(offset);
        return string;
    };
};

struct ReturnStatementASTnode : public StatementASTnode {
    std::unique_ptr<ExpressionASTnode> expression;

    ReturnStatementASTnode(){};
    ReturnStatementASTnode(std::unique_ptr<ExpressionASTnode> expression) : expression(std::move(expression)) {}
    virtual ReturnInst* codeGen(Type* funcReturnType) override {
        if (expression) {
            Value* val = expression->codeGen();
            return Builder.CreateRet(val);
        };
        return Builder.CreateRetVoid();
    };
    virtual std::string toFormattedString() const override {
        return "return " + expression->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        std::string string = offset + branch + "Return";
        if (expression) string += "\n" + expression->toString(incOffset);
        return string;
    };
};

struct BlockASTnode : public StatementASTnode {
    std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarationList;
    std::vector<std::unique_ptr<StatementASTnode>> statementList;

    BlockASTnode(){};
    BlockASTnode(std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarationList,
                 std::vector<std::unique_ptr<StatementASTnode>> statementList) : localDeclarationList(std::move(localDeclarationList)), statementList(std::move(statementList)) {}
    virtual ReturnInst* codeGen(Type* funcReturnType) override {
        for (std::unique_ptr<LocalDeclarationASTnode>& localDecl : localDeclarationList) {
            localDecl->codeGen();
        }
        for (std::unique_ptr<StatementASTnode>& stmt : statementList) {
            if (ReturnInst* ret = stmt->codeGen(funcReturnType)) {
                Type* retType = ret->getReturnValue()->getType();
                if (funcReturnType && !ret->getReturnValue()) {
                    return logErrorRetInst("Missing return for function with " + TypeNames.at(TypeHierarchy.at(funcReturnType)) + " return type");
                } else if (funcReturnType && TypeHierarchy.at(retType) > TypeHierarchy.at(funcReturnType)) {
                    return logErrorRetInst("Cannot narrow type during return from " + TypeNames.at(TypeHierarchy.at(retType)) + " to " + TypeNames.at(TypeHierarchy.at(funcReturnType)));
                }
                return ret;
            }
        }
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return " { " + to_string(localDeclarationList) + " " + to_string(statementList) + " }";
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        std::string string;
        string += offset + branch + "Block\n" + string += to_string(localDeclarationList, incOffset);
        if (!localDeclarationList.empty()) string += "\n";
        string += to_string(statementList, incOffset);
        return string;
    };
};

struct WhileStatementASTnode : public StatementASTnode {
    std::unique_ptr<ExpressionASTnode> expression;
    std::unique_ptr<StatementASTnode> statement;

    WhileStatementASTnode(){};
    WhileStatementASTnode(std::unique_ptr<ExpressionASTnode> expression,
                          std::unique_ptr<StatementASTnode> statement) : expression(std::move(expression)), statement(std::move(statement)) {}
    virtual ReturnInst* codeGen(Type* funcReturnType) override {
        Value* condVal = expression->codeGen();
        if (!condVal) return nullptr;
        Value* compVal = createIsTrue(condVal, "whileCond");
        Function* func = Builder.GetInsertBlock()->getParent();
        BasicBlock* trueBB = BasicBlock::Create(TheContext, "whileTrue", func);
        BasicBlock* endBB = BasicBlock::Create(TheContext, "endWhile", func);
        Builder.CreateCondBr(compVal, trueBB, endBB);
        Builder.SetInsertPoint(trueBB);
        ReturnInst* trueVal = statement->codeGen(funcReturnType);
        condVal = expression->codeGen();
        if (!condVal) return nullptr;
        compVal = createIsTrue(condVal, "whileCond");
        Builder.CreateCondBr(compVal, trueBB, endBB);
        trueBB = Builder.GetInsertBlock();
        Builder.SetInsertPoint(endBB);
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return "while (" + expression->toFormattedString() + ")" + statement->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "While Statement\n" +
               expression->toString(incOffset) + "\n" +
               statement->toString(incOffset);
    };
};

struct ElseStatementASTnode : public StatementASTnode {
    std::unique_ptr<BlockASTnode> block;

    ElseStatementASTnode(){};
    ElseStatementASTnode(std::unique_ptr<BlockASTnode> block) : block(std::move(block)) {}
    virtual ReturnInst* codeGen(Type* funcReturnType) override {
        return block->codeGen(funcReturnType);
    }
    virtual std::string toFormattedString() const override {
        return " else" + block->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Else Statement\n" +
               block->toString(incOffset);
    };
};

struct IfStatementASTnode : public StatementASTnode {
    std::unique_ptr<ExpressionASTnode> expression;
    std::unique_ptr<BlockASTnode> block;
    std::unique_ptr<ElseStatementASTnode> elseStatement;

    IfStatementASTnode(){};
    IfStatementASTnode(std::unique_ptr<ExpressionASTnode> expression,
                       std::unique_ptr<BlockASTnode> block,
                       std::unique_ptr<ElseStatementASTnode> elseStatement) : expression(std::move(expression)), block(std::move(block)), elseStatement(std::move(elseStatement)) {}
    virtual ReturnInst* codeGen(Type* funcReturnType) override {
        Value* condVal = expression->codeGen();
        if (!condVal) return nullptr;
        Value* compVal = createIsTrue(condVal, "ifCond");
        Function* func = Builder.GetInsertBlock()->getParent();
        BasicBlock* trueBB = BasicBlock::Create(TheContext, "ifTrue", func);
        BasicBlock* falseBB;
        if (elseStatement->block) falseBB = BasicBlock::Create(TheContext, "else", func);
        BasicBlock* endBB = BasicBlock::Create(TheContext, "endIf", func);
        if (elseStatement->block) {
            Builder.CreateCondBr(compVal, trueBB, falseBB);
        } else {
            Builder.CreateCondBr(compVal, trueBB, endBB);
        }
        Builder.SetInsertPoint(trueBB);
        ReturnInst* trueVal = block->codeGen(funcReturnType);
        Builder.CreateBr(endBB);
        trueBB = Builder.GetInsertBlock();
        if (elseStatement->block) {
            Builder.SetInsertPoint(falseBB);
            ReturnInst* falseVal = elseStatement->codeGen(funcReturnType);
            Builder.CreateBr(endBB);
            falseBB = Builder.GetInsertBlock();
        }
        Builder.SetInsertPoint(endBB);
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return "if (" + expression->toFormattedString() + ")" + block->toFormattedString() + elseStatement->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        std::string string = offset + branch + "If Statement\n" +
                             expression->toString(incOffset) + "\n" +
                             block->toString(incOffset);
        if (elseStatement->block) string += "\n" + elseStatement->toString(offset);
        return string;
    };
};

struct DeclarationASTnode : public ASTnode {
    int type;
    std::string name;
    std::vector<std::unique_ptr<ParamASTnode>> paramList;
    std::unique_ptr<BlockASTnode> block;

    DeclarationASTnode(){};
    DeclarationASTnode(int type,
                       std::string name,
                       std::vector<std::unique_ptr<ParamASTnode>> paramList,
                       std::unique_ptr<BlockASTnode> block) : type(type), name(name), paramList(std::move(paramList)), block(std::move(block)) {}
    virtual Value* codeGen() override {
        if (block) {
            Function* func = TheModule->getFunction(name);
            if (!func) {
                std::vector<Type*> types;
                for (std::unique_ptr<ParamASTnode>& param : paramList) {
                    if (param->type != VOID_TOK) {
                        types.push_back(TypeMap.at(param->type));
                    }
                }
                FunctionType* ft = FunctionType::get(TypeMap.at(type), types, false);
                func = Function::Create(ft, Function::ExternalLinkage, name, TheModule.get());
                int i = 0;
                for (auto& param : func->args())
                    param.setName(paramList[i++]->name);
            }
            BasicBlock* funcBB = BasicBlock::Create(TheContext, "entry", func);
            Builder.SetInsertPoint(funcBB);

            NamedValues.clear();
            for (auto& arg : func->args()) {
                AllocaInst* alloca = CreateEntryBlockAlloca(func, arg.getType(), std::string(arg.getName()));
                Builder.CreateStore(&arg, alloca);
                NamedValues[std::string(arg.getName())] = alloca;
            }

            ReturnInst* ret = block->codeGen(func->getReturnType());
            if (func->getReturnType() && !ret) {
                return logErrorValue("Missing return for function with " + TypeNames.at(TypeHierarchy.at(func->getReturnType())) + " return type");
            }

            return func;
        } else {
            if (GlobalVariable* gVar = TheModule->getGlobalVariable(name)) {
                return logErrorValue("Global variable already declared: " + name);
            }
            GlobalVariable* gVar = new GlobalVariable(
                *TheModule,
                TypeMap.at(type),
                false,
                GlobalValue::CommonLinkage,
                Constant::getNullValue(TypeMap.at(type)),
                name);
            gVar->setAlignment(MaybeAlign(4));
        }
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return TypeNames.at(type) + " " + name + "(" + to_string(paramList, ", ") + ")" + block->toFormattedString();
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        std::string string = offset + branch + "Declaration " + TypeNames.at(type) + " " + name;
        if (block) string += "\n" +
                             to_string(paramList, incOffset) + "\n" +
                             block->toString(incOffset);
        return string;
    };
};

struct ExternASTnode : public ASTnode {
    int type;
    std::string name;
    std::vector<std::unique_ptr<ParamASTnode>> paramList;

    ExternASTnode(){};
    ExternASTnode(int type, std::string name, std::vector<std::unique_ptr<ParamASTnode>> paramList) : type(type), name(name), paramList(std::move(paramList)) {}
    virtual Value* codeGen() override {
        std::vector<Type*> types;
        for (std::unique_ptr<ParamASTnode>& param : paramList) {
            types.push_back(TypeMap.at(param->type));
        }
        FunctionType* ft = FunctionType::get(TypeMap.at(type), types, false);
        Function* func = Function::Create(ft, Function::ExternalLinkage, name, TheModule.get());
        int i = 0;
        for (auto& param : func->args())
            param.setName(paramList[i++]->name);
        return func;
    }
    virtual std::string toFormattedString() const override {
        return "extern " + TypeNames.at(type) + " " + name + "(" + to_string(paramList, ", ") + ");";
    };
    virtual std::string toString(std::string offset) const override {
        std::string incOffset = incrementOffset(offset);
        return offset + branch + "Extern " + TypeNames.at(type) + " " + name + "\n" +
               to_string(paramList, incOffset);
    };
};

struct ProgramASTnode : public ASTnode {
    std::vector<std::unique_ptr<ExternASTnode>> externList;
    std::vector<std::unique_ptr<DeclarationASTnode>> declarationList;

    ProgramASTnode(){};
    ProgramASTnode(std::vector<std::unique_ptr<ExternASTnode>> externList,
                   std::vector<std::unique_ptr<DeclarationASTnode>> declarationList) : externList(std::move(externList)), declarationList(std::move(declarationList)) {}
    virtual Value* codeGen() override {
        for (std::unique_ptr<ExternASTnode>& ext : externList) {
            ext->codeGen();
        }
        for (std::unique_ptr<DeclarationASTnode>& decl : declarationList) {
            decl->codeGen();
        }
        return nullptr;
    }
    virtual std::string toFormattedString() const override {
        return to_string(externList) + " " + to_string(declarationList);
    };
    virtual std::string toString(std::string offset = "") const override {
        std::string incOffset = incrementOffset(offset);
        return offset + "Program\n" +
               to_string(externList, offset) + "\n" +
               to_string(declarationList, offset);
    };
};

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

void checkToken(std::string expectedType, TokenSet acceptableTokens, bool consume = false) {
    if (!acceptableTokens.contains(CurTok.type)) {
        logError("Unexpected token while parsing " + expectedType + ": " + CurTok.lexeme + " (line " + std::to_string(CurTok.lineNo) + ")");
    }
    if (consume) getNextToken();
}

void checkToken(std::string expectedType, int acceptableType, bool consume = false) {
    if (CurTok.type != acceptableType) {
        logError("Unexpected token while parsing " + expectedType + ": " + CurTok.lexeme + " (line " + std::to_string(CurTok.lineNo) + ")");
    }
    if (consume) getNextToken();
}

struct Expression {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse();
};
TokenSet Expression::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// arg_list ::= "," expr arg_list | epsilon
struct ArgList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExpressionASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "arg list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExpressionASTnode>> argList;
        while (firstSet.contains(CurTok.type)) {
            getNextToken();
            argList.emplace_back(std::move(Expression::parse()));
        };
        return argList;
    }
};
TokenSet ArgList::firstSet = TokenSet({COMMA});

// args ::= expr arg_list | epsilon
struct Args {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExpressionASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "args", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExpressionASTnode>> args;
        if (Expression::firstSet.contains(CurTok.type)) {
            args.emplace_back(std::move(Expression::parse()));
            std::vector<std::unique_ptr<ExpressionASTnode>> argList = ArgList::parse();
            std::move(argList.begin(), argList.end(), std::back_inserter(args));
        }
        return args;
    }
};
TokenSet Args::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// ident_body ::= "(" args ")" | epsilon
struct IdentBody {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExpressionASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "identBody", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExpressionASTnode>> args;
        if (firstSet.contains(CurTok.type)) {
            getNextToken();
            args = Args::parse();
            checkToken("right parentesis", RPAR, true);
        }
        return args;
    }
};
TokenSet IdentBody::firstSet = TokenSet({LPAR});

//  rval_term ::= "-" rval_term
//       | "!" rval_term
//       | "(" expr ")"
//       | IDENT ident_body
//       | INT_LIT | FLOAT_LIT | BOOL_LIT
struct RvalTerm {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rvalterm", CurTok.lexeme.c_str(), CurTok.type);
        std::string intLit;
        std::string floatLit;
        std::string boolLit;
        switch (CurTok.type) {
            case IDENT: {
                std::string ident = CurTok.lexeme;
                getNextToken();
                std::vector<std::unique_ptr<ExpressionASTnode>> args;
                if (CurTok.type == LPAR) {
                    args = std::move(IdentBody::parse());
                    return std::make_unique<FunctionCallASTnode>(ident, std::move(args));
                }
                return std::make_unique<VariableASTnode>(ident);
                break;
            }
            case MINUS: {
            }
            case NOT: {
                std::string op = CurTok.lexeme;
                getNextToken();
                std::unique_ptr<ExpressionASTnode> term = std::move(RvalTerm::parse());
                return std::make_unique<UnaryExpressionASTnode>(op, std::move(term));
                break;
            }
            case LPAR: {
                getNextToken();
                std::unique_ptr<ExpressionASTnode> expression = std::move(Expression::parse());
                checkToken("right parentesis", RPAR, true);
                return std::move(expression);
                break;
            }
            case FLOAT_LIT:
                floatLit = CurTok.lexeme;
                getNextToken();
                break;
            case INT_LIT:
                intLit = CurTok.lexeme;
                getNextToken();
                break;
            case BOOL_LIT:
                boolLit = CurTok.lexeme;
                getNextToken();
                break;
        }
        return std::make_unique<LiteralASTnode>(floatLit, intLit, boolLit);
    }
};
TokenSet RvalTerm::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, FLOAT_LIT, INT_LIT, BOOL_LIT});

struct Rval6List {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<BinaryExpressionASTnode>> parse();
};
TokenSet Rval6List::firstSet = TokenSet({ASTERIX, DIV, MOD});

struct Rval6 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse();
};
TokenSet Rval6::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// rval_6_list ::= "*" rval_term rval_6_list | "/" rval_term rval_6_list | "%" rval_term rval_6_list | epsilon
std::vector<std::unique_ptr<BinaryExpressionASTnode>> Rval6List::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval6list", CurTok.lexeme.c_str(), CurTok.type);
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval6List;
    while (Rval6List::firstSet.contains(CurTok.type)) {
        std::string binOp = CurTok.lexeme;
        getNextToken();
        std::unique_ptr<ExpressionASTnode> rvalTerm = RvalTerm::parse();
        rval6List.emplace_back(std::make_unique<BinaryExpressionASTnode>(nullptr, binOp, std::move(rvalTerm)));
    }
    return std::move(rval6List);
}

// rval_6 ::= rval_term rval_6_list
std::unique_ptr<ExpressionASTnode> Rval6::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval6", CurTok.lexeme.c_str(), CurTok.type);
    checkToken("term", RvalTerm::firstSet);
    std::unique_ptr<ExpressionASTnode> root = RvalTerm::parse();
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval6List = Rval6List::parse();
    for (auto it = rval6List.begin(); it != rval6List.end(); ++it) {
        (*it)->LHSexpression = std::move(root);
        root = std::move(*it);
    }
    return std::move(root);
}

struct Rval5List {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<BinaryExpressionASTnode>> parse();
};
TokenSet Rval5List::firstSet = TokenSet({PLUS, MINUS});

struct Rval5 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse();
};
TokenSet Rval5::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// rval_5_list ::= "+" rval_6 rval_5_list | "-" rval_6 rval_5_list | epsilon
std::vector<std::unique_ptr<BinaryExpressionASTnode>> Rval5List::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval5list", CurTok.lexeme.c_str(), CurTok.type);
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval5List;
    while (Rval5List::firstSet.contains(CurTok.type)) {
        std::string binOp = CurTok.lexeme;
        getNextToken();
        std::unique_ptr<ExpressionASTnode> rval6 = Rval6::parse();
        rval5List.emplace_back(std::make_unique<BinaryExpressionASTnode>(nullptr, binOp, std::move(rval6)));
    }
    return std::move(rval5List);
}

// rval_5 ::= rval_6 rval_5_list
std::unique_ptr<ExpressionASTnode> Rval5::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval5", CurTok.lexeme.c_str(), CurTok.type);
    checkToken("term", Rval6::firstSet);
    std::unique_ptr<ExpressionASTnode> root = Rval6::parse();
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval5List = Rval5List::parse();
    for (auto it = rval5List.begin(); it != rval5List.end(); ++it) {
        (*it)->LHSexpression = std::move(root);
        root = std::move(*it);
    }
    return std::move(root);
}

struct Rval4List {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<BinaryExpressionASTnode>> parse();
};
TokenSet Rval4List::firstSet = TokenSet({LT, LE, GT, GE});

struct Rval4 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse();
};
TokenSet Rval4::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// rval_4_list ::= "<" rval_5 rval_4_list | "<=" rval_5 rval_4_list | ">" rrval_5 rval_4_list | "=" rval_5 rval_4_list | epsilon
std::vector<std::unique_ptr<BinaryExpressionASTnode>> Rval4List::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval4list", CurTok.lexeme.c_str(), CurTok.type);
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval4List;
    while (Rval4List::firstSet.contains(CurTok.type)) {
        std::string binOp = CurTok.lexeme;
        getNextToken();
        std::unique_ptr<ExpressionASTnode> rval5 = Rval5::parse();
        rval4List.emplace_back(std::make_unique<BinaryExpressionASTnode>(nullptr, binOp, std::move(rval5)));
    }
    return std::move(rval4List);
}

// rval_4 ::= rval_5 rval_4_list
std::unique_ptr<ExpressionASTnode> Rval4::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval4", CurTok.lexeme.c_str(), CurTok.type);
    checkToken("term", Rval5::firstSet);
    std::unique_ptr<ExpressionASTnode> root = Rval5::parse();
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval4List = Rval4List::parse();
    for (auto it = rval4List.begin(); it != rval4List.end(); ++it) {
        (*it)->LHSexpression = std::move(root);
        root = std::move(*it);
    }
    return std::move(root);
}

struct Rval3List {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<BinaryExpressionASTnode>> parse();
};
TokenSet Rval3List::firstSet = TokenSet({EQ, NE});

struct Rval3 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse();
};
TokenSet Rval3::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// rval_3_list ::= "==" rval_4 rval_3_list | "!=" rval_4 rval_3_list | epsilon
std::vector<std::unique_ptr<BinaryExpressionASTnode>> Rval3List::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval3list", CurTok.lexeme.c_str(), CurTok.type);
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval3List;
    while (Rval3List::firstSet.contains(CurTok.type)) {
        std::string binOp = CurTok.lexeme;
        getNextToken();
        std::unique_ptr<ExpressionASTnode> rval4 = Rval4::parse();
        rval3List.emplace_back(std::make_unique<BinaryExpressionASTnode>(nullptr, binOp, std::move(rval4)));
    }
    return std::move(rval3List);
}

// rval_3 ::= rval_4 rval_3_list
std::unique_ptr<ExpressionASTnode> Rval3::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval3", CurTok.lexeme.c_str(), CurTok.type);
    checkToken("term", Rval4::firstSet);
    std::unique_ptr<ExpressionASTnode> root = Rval4::parse();
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval3List = Rval3List::parse();
    for (auto it = rval3List.begin(); it != rval3List.end(); ++it) {
        (*it)->LHSexpression = std::move(root);
        root = std::move(*it);
    }
    return std::move(root);
}

struct Rval2List {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<BinaryExpressionASTnode>> parse();
};
TokenSet Rval2List::firstSet = TokenSet({AND});

struct Rval2 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse();
};
TokenSet Rval2::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// rval_2_list ::= "&&" rval_3 rval_2_list | epsilon
std::vector<std::unique_ptr<BinaryExpressionASTnode>> Rval2List::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval2list", CurTok.lexeme.c_str(), CurTok.type);
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval2List;
    while (Rval2List::firstSet.contains(CurTok.type)) {
        std::string binOp = CurTok.lexeme;
        getNextToken();
        std::unique_ptr<ExpressionASTnode> rval3 = Rval3::parse();
        rval2List.emplace_back(std::make_unique<BinaryExpressionASTnode>(nullptr, binOp, std::move(rval3)));
    }
    return std::move(rval2List);
}

// rval_2 ::= rval_3 rval_2_list
std::unique_ptr<ExpressionASTnode> Rval2::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval2", CurTok.lexeme.c_str(), CurTok.type);
    checkToken("term", Rval3::firstSet);
    std::unique_ptr<ExpressionASTnode> root = Rval3::parse();
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval2List = Rval2List::parse();
    for (auto it = rval2List.begin(); it != rval2List.end(); ++it) {
        (*it)->LHSexpression = std::move(root);
        root = std::move(*it);
    }
    return std::move(root);
}

struct Rval1List {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<BinaryExpressionASTnode>> parse();
};
TokenSet Rval1List::firstSet = TokenSet({OR});

struct Rval1 {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionASTnode> parse();
};
TokenSet Rval1::firstSet = TokenSet({MINUS, NOT, LPAR, IDENT, FLOAT_LIT, INT_LIT, BOOL_LIT});

// rval_1_list ::= "||" rval_2 rval_1_list | epsilon
std::vector<std::unique_ptr<BinaryExpressionASTnode>> Rval1List::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval1list", CurTok.lexeme.c_str(), CurTok.type);
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval1List;
    while (Rval1List::firstSet.contains(CurTok.type)) {
        std::string binOp = CurTok.lexeme;
        getNextToken();
        std::unique_ptr<ExpressionASTnode> rval2 = Rval2::parse();
        rval1List.emplace_back(std::make_unique<BinaryExpressionASTnode>(nullptr, binOp, std::move(rval2)));
    }
    return std::move(rval1List);
};

// rval_1 ::= rval_2 rval_1_list
std::unique_ptr<ExpressionASTnode> Rval1::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "rval1", CurTok.lexeme.c_str(), CurTok.type);
    checkToken("term", Rval2::firstSet);
    std::unique_ptr<ExpressionASTnode> root = Rval2::parse();
    std::vector<std::unique_ptr<BinaryExpressionASTnode>> rval1List = Rval1List::parse();
    for (auto it = rval1List.begin(); it != rval1List.end(); ++it) {
        (*it)->LHSexpression = std::move(root);
        root = std::move(*it);
    }
    return std::move(root);
};

// expr ::= IDENT "=" expr | rval_1
std::unique_ptr<ExpressionASTnode> Expression::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d (line %d, col %d)\n", "expr", CurTok.lexeme.c_str(), CurTok.type, CurTok.lineNo, CurTok.columnNo);
    TOKEN identTok;
    std::unique_ptr<ExpressionASTnode> expression;
    if (CurTok.type == IDENT) {
        identTok = CurTok;
        getNextToken();
        if (CurTok.type == ASSIGN) {
            getNextToken();
            expression = std::move(Expression::parse());
        } else {
            putBackToken(CurTok);
            CurTok = identTok;
            return std::move(Rval1::parse());
        }
    } else {
        return std::move(Rval1::parse());
    }
    return std::make_unique<AssignmentExpressionASTnode>(std::move(identTok.lexeme), std::move(expression));
}

// expr_stmt ::= expr ";" | ";"
struct ExpressionStatement {
    static TokenSet firstSet;
    static std::unique_ptr<ExpressionStatementASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "expr stmt", CurTok.lexeme.c_str(), CurTok.type);
        std::unique_ptr<ExpressionASTnode> expression;
        if (CurTok.type != SC) {
            expression = std::move(Expression::parse());
        }
        checkToken("semicolon", SC, true);
        return std::make_unique<ExpressionStatementASTnode>(std::move(expression));
    }
};
TokenSet ExpressionStatement::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, FLOAT_LIT, INT_LIT, BOOL_LIT, SC});

// return_stmt ::= "return" expr_stmt
struct ReturnStatement {
    static TokenSet firstSet;
    static std::unique_ptr<ReturnStatementASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "return", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();
        std::unique_ptr<ExpressionASTnode> expression = std::move(ExpressionStatement::parse()->expression);
        return std::make_unique<ReturnStatementASTnode>(std::move(expression));
    }
};
TokenSet ReturnStatement::firstSet = TokenSet({RETURN});

struct Block {
    static TokenSet firstSet;
    static std::unique_ptr<BlockASTnode> parse();
};
TokenSet Block::firstSet = TokenSet({LBRA});

// else_stmt  ::= "else" block | epsilon
struct ElseStatement {
    static TokenSet firstSet;
    static std::unique_ptr<ElseStatementASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "else", CurTok.lexeme.c_str(), CurTok.type);
        std::unique_ptr<BlockASTnode> block;
        if (firstSet.contains(CurTok.type)) {
            getNextToken();
            block = Block::parse();
        }
        return std::make_unique<ElseStatementASTnode>(std::move(block));
    }
};
TokenSet ElseStatement::firstSet = TokenSet({ELSE});

// if_stmt ::= "if" "(" expr ")" block else_stmt
struct IfStatement {
    static TokenSet firstSet;
    static std::unique_ptr<IfStatementASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "if", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();
        checkToken("left parenthesis", LPAR, true);
        std::unique_ptr<ExpressionASTnode> expression = Expression::parse();
        checkToken("right parenthesis", RPAR, true);
        std::unique_ptr<BlockASTnode> block = Block::parse();
        std::unique_ptr<ElseStatementASTnode> elseStatement = ElseStatement::parse();
        return std::make_unique<IfStatementASTnode>(std::move(expression), std::move(block), std::move(elseStatement));
    }
};
TokenSet IfStatement::firstSet = TokenSet({IF});
struct Statement {
    static TokenSet firstSet;
    static std::unique_ptr<StatementASTnode> parse();
};
TokenSet Statement::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, FLOAT_LIT, INT_LIT, BOOL_LIT, SC, LBRA, IF, WHILE, RETURN});

// while_stmt ::= "while" "(" expr ")" stmt
struct WhileStatement {
    static TokenSet firstSet;
    static std::unique_ptr<WhileStatementASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "while", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();
        checkToken("left parenthesis", LPAR, true);
        std::unique_ptr<ExpressionASTnode> expression = Expression::parse();
        checkToken("right parenthesis", RPAR, true);
        std::unique_ptr<StatementASTnode> statement = Statement::parse();
        return std::make_unique<WhileStatementASTnode>(std::move(expression), std::move(statement));
    }
};
TokenSet WhileStatement::firstSet = TokenSet({WHILE});

// stmt ::= expr_stmt
//		| return_stmt
//      | while_stmt
//      | if_stmt
std::unique_ptr<StatementASTnode> Statement::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "stmt", CurTok.lexeme.c_str(), CurTok.type);
    std::unique_ptr<StatementASTnode> statement;
    checkToken("if, return, while or expression", Statement::firstSet);
    if (Block::firstSet.contains(CurTok.type)) {
        statement = Block::parse();
    } else if (WhileStatement::firstSet.contains(CurTok.type)) {
        statement = WhileStatement::parse();
    } else if (IfStatement::firstSet.contains(CurTok.type)) {
        statement = IfStatement::parse();
    } else if (ReturnStatement::firstSet.contains(CurTok.type)) {
        statement = ReturnStatement::parse();
    } else {
        statement = ExpressionStatement::parse();
    }
    return statement;
}

// stmt_list ::= stmt stmt_list | epsilon
struct StatementList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<StatementASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "stmt list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<StatementASTnode>> statements;
        while (firstSet.contains(CurTok.type)) {
            statements.emplace_back(std::move(Statement::parse()));
        }
        return statements;
    }
};
TokenSet StatementList::firstSet = TokenSet({IDENT, MINUS, NOT, LPAR, FLOAT_LIT, INT_LIT, BOOL_LIT, SC, LBRA, IF, WHILE, RETURN});

// local_decl ::= var_type IDENT ";"
struct LocalDeclaration {
    static TokenSet firstSet;
    static std::unique_ptr<LocalDeclarationASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "local decl", CurTok.lexeme.c_str(), CurTok.type);
        checkToken("variable type", LocalDeclaration::firstSet);
        int type = CurTok.type;
        getNextToken();  // eat type.
        checkToken("identifier", IDENT);
        std::string ident = CurTok.lexeme;
        getNextToken();
        checkToken("semicolon", SC, true);
        return std::make_unique<LocalDeclarationASTnode>(std::move(type), std::move(ident));
    }
};
TokenSet LocalDeclaration::firstSet = TokenSet({INT_TOK, FLOAT_TOK, BOOL_TOK});

// local_decl_list ::= local_decl local_decl_list | epsilon
struct LocalDeclarationList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<LocalDeclarationASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "local decl list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarations;
        while (firstSet.contains(CurTok.type)) {
            localDeclarations.emplace_back(std::move(LocalDeclaration::parse()));
        }
        return localDeclarations;
    }
};
TokenSet LocalDeclarationList::firstSet = TokenSet({INT_TOK, FLOAT_TOK, BOOL_TOK});

// block ::= "{" local_decl_list stmt_list "}"
std::unique_ptr<BlockASTnode> Block::parse() {
    fprintf(stderr, "%s parse: \"%s\" with type %d\n", "block", CurTok.lexeme.c_str(), CurTok.type);
    checkToken("left brace", LBRA, true);
    std::vector<std::unique_ptr<LocalDeclarationASTnode>> localDeclarations = LocalDeclarationList::parse();
    std::vector<std::unique_ptr<StatementASTnode>> statements = StatementList::parse();
    checkToken("right brace", RBRA, true);
    return std::make_unique<BlockASTnode>(std::move(localDeclarations), std::move(statements));
}

// param ::= var_type IDENT
struct Param {
    static TokenSet firstSet;
    static std::unique_ptr<ParamASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "param", CurTok.lexeme.c_str(), CurTok.type);
        checkToken("variable type", Param::firstSet);
        int type = CurTok.type;
        getNextToken();  // eat type.
        checkToken("identifier", IDENT);
        std::string ident = CurTok.lexeme;
        getNextToken();
        return std::make_unique<ParamASTnode>(std::move(type), std::move(ident));
    }
};
TokenSet Param::firstSet = TokenSet({INT_TOK, FLOAT_TOK, BOOL_TOK});

// param_list ::= "," param param_list | epsilon
struct ParamList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ParamASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "paramlist", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ParamASTnode>> paramList;
        while (firstSet.contains(CurTok.type)) {
            getNextToken();
            paramList.emplace_back(std::move(Param::parse()));
        }
        return paramList;
    }
};
TokenSet ParamList::firstSet = TokenSet({COMMA});

// params ::= param param_list | "void" | epsilon
struct Params {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ParamASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "params", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ParamASTnode>> params;
        checkToken("type", Param::firstSet);
        if (CurTok.type == VOID_TOK) {
            std::unique_ptr<ParamASTnode> voidParam = std::make_unique<ParamASTnode>(VOID_TOK, "");
            params.emplace_back(std::move(voidParam));
            getNextToken();
        } else if (Param::firstSet.contains(CurTok.type)) {
            params.emplace_back(std::move(Param::parse()));
            std::vector<std::unique_ptr<ParamASTnode>> paramList = ParamList::parse();
            std::move(paramList.begin(), paramList.end(), std::back_inserter(params));
        }
        return params;
    }
};
TokenSet Params::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// func_body ::= "(" params ")" block
struct FunctionBody {
    static TokenSet firstSet;
    static std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "func body", CurTok.lexeme.c_str(), CurTok.type);
        checkToken("left parenthesis", LPAR, true);
        std::vector<std::unique_ptr<ParamASTnode>> params = Params::parse();
        checkToken("right parenthesis", RPAR, true);
        std::unique_ptr<BlockASTnode> block = std::move(Block::parse());
        return std::make_tuple(std::move(params), std::move(block));
    }
};
TokenSet FunctionBody::firstSet = TokenSet({LPAR});

// decl_body :: = ";" | func_body
struct DeclarationBody {
    static TokenSet firstSet;
    static std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "decl body", CurTok.lexeme.c_str(), CurTok.type);
        std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> functionBody;
        checkToken("function body or semicolon", DeclarationBody::firstSet);
        if (CurTok.type == SC) {
            getNextToken();
        } else {
            functionBody = FunctionBody::parse();
        }
        return functionBody;
    }
};
TokenSet DeclarationBody::firstSet = TokenSet({SC, LPAR});

// decl ::= "void" IDENT func_body | var_type IDENT decl_body
struct Declaration {
    static TokenSet firstSet;
    static std::unique_ptr<DeclarationASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "decl", CurTok.lexeme.c_str(), CurTok.type);
        std::tuple<std::vector<std::unique_ptr<ParamASTnode>>, std::unique_ptr<BlockASTnode>> declarationBody;
        std::vector<std::unique_ptr<ParamASTnode>> params;
        std::unique_ptr<BlockASTnode> block;
        checkToken("type", Declaration::firstSet);
        int type = CurTok.type;
        getNextToken();  // eat type.
        checkToken("identifier", IDENT);
        std::string ident = CurTok.lexeme;
        getNextToken();
        if (type == VOID_TOK) {
            declarationBody = FunctionBody::parse();
        } else {
            declarationBody = DeclarationBody::parse();
        }
        params = std::move(std::get<0>(declarationBody));
        block = std::move(std::get<1>(declarationBody));
        return std::make_unique<DeclarationASTnode>(std::move(type), std::move(ident), std::move(params), std::move(block));
    }
};
TokenSet Declaration::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// decl_list ::= decl decl_list | epsilon
struct DeclarationList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<DeclarationASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "decl list", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<DeclarationASTnode>> declarationList;
        checkToken("type", Declaration::firstSet);
        while (firstSet.contains(CurTok.type)) {
            declarationList.emplace_back(std::move(Declaration::parse()));
        }
        return declarationList;
    }
};
TokenSet DeclarationList::firstSet = TokenSet({VOID_TOK, INT_TOK, FLOAT_TOK, BOOL_TOK});

// extern ::= "extern" type_spec IDENT "(" params ")" ";"
struct Extern {
    static TokenSet firstSet;
    static std::unique_ptr<ExternASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "extern", CurTok.lexeme.c_str(), CurTok.type);
        getNextToken();  // eat extern.
        checkToken("type", TYPE_TOKENS);
        int type = CurTok.type;
        getNextToken();  // eat type.
        checkToken("identifier", IDENT);
        std::string ident = CurTok.lexeme;
        getNextToken();  // eat ident.
        checkToken("left parenthesis", LPAR, true);
        std::vector<std::unique_ptr<ParamASTnode>> params = Params::parse();
        checkToken("right parenthesis", RPAR, true);
        checkToken("semicolon", SC, true);
        return std::make_unique<ExternASTnode>(std::move(type), std::move(ident), std::move(params));
    }
};
TokenSet Extern::firstSet = TokenSet({EXTERN});

// extern_list ::= extern extern_list | epsilon
struct ExternList {
    static TokenSet firstSet;
    static std::vector<std::unique_ptr<ExternASTnode>> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "externlist", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExternASTnode>> externList;
        while (firstSet.contains(CurTok.type)) {
            externList.emplace_back(std::move(Extern::parse()));
        };
        return externList;
    }
};
TokenSet ExternList::firstSet = TokenSet({EXTERN});

// program ::= extern_list decl decl_list
struct Program {
    static TokenSet firstSet;
    static std::unique_ptr<ProgramASTnode> parse() {
        fprintf(stderr, "%s parse: \"%s\" with type %d\n", "program", CurTok.lexeme.c_str(), CurTok.type);
        std::vector<std::unique_ptr<ExternASTnode>> externList;
        std::vector<std::unique_ptr<DeclarationASTnode>> declarationList;
        if (ExternList::firstSet.contains(CurTok.type)) {
            externList = std::move(ExternList::parse());
        }
        declarationList.emplace_back(std::move(Declaration::parse()));
        if (DeclarationList::firstSet.contains(CurTok.type)) {
            std::vector<std::unique_ptr<DeclarationASTnode>> declarationListTail = std::move(DeclarationList::parse());
            std::move(declarationListTail.begin(), declarationListTail.end(), std::back_inserter(declarationList));
        }
        checkToken("semicolon", EOF_TOK, true);
        return std::make_unique<ProgramASTnode>(std ::move(externList), std::move(declarationList));
    }
};

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

static std::unique_ptr<ProgramASTnode> Parser() {
    // fprintf(stderr, "ready> ");
    return std::move(Program::parse());
}

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const ASTnode& ast) {
    os << ast.toString("");
    return os;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char** argv) {
    try {
        if (argc == 2) {
            pFile = fopen(argv[1], "r");
            if (pFile == NULL)
                perror("Error opening file");
        } else {
            std::cout << "Usage: ./code InputFile\n";
            return 1;
        }

        lineNo = 1;
        columnNo = 1;

        // get the first token
        getNextToken();
        // while (CurTok.type != EOF_TOK) {
        //     fprintf(stderr, "Token: \"%s\" with type %d\n", CurTok.lexeme.c_str(),
        //             CurTok.type);
        //     getNextToken();
        // }
        // fprintf(stderr, "Lexer Finished\n");

        // Make the module, which holds all the code.
        TheModule = std::make_unique<Module>("mini-c", TheContext);

        // Run the parser now.
        std::unique_ptr<ProgramASTnode> programAST = Parser();
        fprintf(stderr, "Parsing finished\n\n");

        // llvm::outs() << programAST << "\n";
        fprintf(stderr, "%s\n", programAST->toString().c_str());
        fprintf(stderr, "AST node printing finished\n\n");

        programAST->codeGen();
        //********************* Start printing final IR **************************
        // Print out all of the generated code into a file called output.ll
        auto Filename = "output.ll";
        std::error_code EC;
        raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

        if (EC) {
            errs() << "Could not open file: " << EC.message();
            return 1;
        }
        TheModule->print(errs(), nullptr);  // print IR to terminal
        TheModule->print(dest, nullptr);
        //********************* End printing final IR ****************************
        fprintf(stderr, "IR Code Generation finished\n");

        fclose(pFile);  // close the file that contains the code that was parsed
        return 0;
    } catch (const std::exception& e) {
        fprintf(stderr, "%s", e.what());
        std::exit(EXIT_FAILURE);
    }
}
