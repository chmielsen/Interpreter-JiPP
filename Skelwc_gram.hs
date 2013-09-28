module Skelwc_gram where

-- Haskell module generated by the BNF converter

import Abswc_gram
import ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transIdent :: Ident -> Result
transIdent x = case x of
  Ident str  -> failure x


transProg :: Prog -> Result
transProg x = case x of
  Program instructions  -> failure x


transInstruction :: Instruction -> Result
transInstruction x = case x of
  DStmt stmt  -> failure x
  DDecl decl  -> failure x


transStmt :: Stmt -> Result
transStmt x = case x of
  Assignment id exp  -> failure x
  FreeExp exp  -> failure x
  VPrint id  -> failure x
  IfSe exp stmt1 stmt2  -> failure x
  BlockS instructions  -> failure x
  WhileS exp stmt  -> failure x
  FirstS stmt  -> failure x
  TailS stmt  -> failure x
  SizeS stmt  -> failure x
  PopBackS id  -> failure x
  PopFrontS id  -> failure x
  PushBackS id exp  -> failure x
  PushFrontS id exp  -> failure x
  RetS exp  -> failure x
  EEAdd id exp  -> failure x
  EESub id exp  -> failure x
  EEMul id exp  -> failure x
  EEDiv id exp  -> failure x


transDecl :: Decl -> Result
transDecl x = case x of
  NVariable type' id  -> failure x
  NFunctionV id args instructions  -> failure x
  NFunction type' id args instructions  -> failure x


transType :: Type -> Result
transType x = case x of
  TInt  -> failure x
  TList type'  -> failure x


transArg :: Arg -> Result
transArg x = case x of
  Param type' id  -> failure x


transExp :: Exp -> Result
transExp x = case x of
  EOpA exp1 op2 exp3  -> failure x
  EOpB exp1 op2 exp3  -> failure x
  EOpC exp1 op2 exp3  -> failure x
  EOpD exp1 op2 exp3  -> failure x
  EOpE exp1 op2 exp3  -> failure x
  EVar id  -> failure x
  EInt n  -> failure x
  FunCall id exps  -> failure x
  EInc id  -> failure x
  EDecr id  -> failure x
  ESub exp  -> failure x


transOp :: Op -> Result
transOp x = case x of
  OAdd  -> failure x
  OMult  -> failure x
  ODiv  -> failure x
  OSub  -> failure x
  OLt  -> failure x
  OGt  -> failure x
  OEq  -> failure x
  OAnd  -> failure x
  OOr  -> failure x



