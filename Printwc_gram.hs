{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Printwc_gram where

-- pretty-printer generated by the BNF converter

import Abswc_gram
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)


instance Print Ident where
  prt _ (Ident i) = doc (showString ( i))



instance Print Prog where
  prt i e = case e of
   Program instructions -> prPrec i 0 (concatD [prt 0 instructions])


instance Print Instruction where
  prt i e = case e of
   DStmt stmt -> prPrec i 0 (concatD [prt 0 stmt])
   DDecl decl -> prPrec i 0 (concatD [prt 0 decl])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Stmt where
  prt i e = case e of
   Assignment id exp -> prPrec i 0 (concatD [prt 0 id , doc (showString "=") , prt 0 exp])
   FreeExp exp -> prPrec i 0 (concatD [prt 0 exp])
   VPrint id -> prPrec i 0 (concatD [doc (showString "print") , doc (showString "(") , prt 0 id , doc (showString ")")])
   IfSe exp stmt0 stmt -> prPrec i 0 (concatD [doc (showString "if") , prt 0 exp , doc (showString "then") , prt 0 stmt0 , doc (showString "else") , prt 0 stmt])
   BlockS instructions -> prPrec i 0 (concatD [doc (showString "{") , prt 0 instructions , doc (showString "}")])
   WhileS exp stmt -> prPrec i 0 (concatD [doc (showString "while") , doc (showString "(") , prt 0 exp , doc (showString ")") , prt 0 stmt])
   FirstS stmt -> prPrec i 0 (concatD [doc (showString "first(") , prt 0 stmt , doc (showString ")")])
   TailS stmt -> prPrec i 0 (concatD [doc (showString "tail(") , prt 0 stmt , doc (showString ")")])
   SizeS stmt -> prPrec i 0 (concatD [doc (showString "size(") , prt 0 stmt , doc (showString ")")])
   PopBackS id -> prPrec i 0 (concatD [doc (showString "pop_back") , doc (showString "(") , prt 0 id , doc (showString ")")])
   PopFrontS id -> prPrec i 0 (concatD [doc (showString "pop_front") , doc (showString "(") , prt 0 id , doc (showString ")")])
   PushBackS id exp -> prPrec i 0 (concatD [doc (showString "push_back") , doc (showString "(") , prt 0 id , doc (showString ",") , prt 0 exp , doc (showString ")")])
   PushFrontS id exp -> prPrec i 0 (concatD [doc (showString "push_front") , doc (showString "(") , prt 0 id , doc (showString ",") , prt 0 exp , doc (showString ")")])
   RetS exp -> prPrec i 0 (concatD [doc (showString "return") , prt 0 exp])
   EEAdd id exp -> prPrec i 0 (concatD [prt 0 id , doc (showString "+=") , prt 0 exp])
   EESub id exp -> prPrec i 0 (concatD [prt 0 id , doc (showString "-=") , prt 0 exp])
   EEMul id exp -> prPrec i 0 (concatD [prt 0 id , doc (showString "*=") , prt 0 exp])
   EEDiv id exp -> prPrec i 0 (concatD [prt 0 id , doc (showString "/=") , prt 0 exp])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Decl where
  prt i e = case e of
   NVariable type' id -> prPrec i 0 (concatD [prt 0 type' , prt 0 id])
   NFunctionV id args instructions -> prPrec i 0 (concatD [doc (showString "fun") , doc (showString "void") , prt 0 id , doc (showString "(") , prt 0 args , doc (showString ")") , doc (showString "{") , prt 0 instructions , doc (showString "}")])
   NFunction type' id args instructions -> prPrec i 0 (concatD [doc (showString "fun") , prt 0 type' , prt 0 id , doc (showString "(") , prt 0 args , doc (showString ")") , doc (showString "{") , prt 0 instructions , doc (showString "}")])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Type where
  prt i e = case e of
   TInt  -> prPrec i 0 (concatD [doc (showString "int")])
   TList type' -> prPrec i 0 (concatD [doc (showString "list") , doc (showString "<") , prt 0 type' , doc (showString ">")])


instance Print Arg where
  prt i e = case e of
   Param type' id -> prPrec i 0 (concatD [prt 0 type' , prt 0 id])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Exp where
  prt i e = case e of
   EOpA exp0 op exp -> prPrec i 0 (concatD [prt 0 exp0 , prt 0 op , prt 0 exp])
   EOpB exp0 op exp -> prPrec i 0 (concatD [prt 1 exp0 , prt 0 op , prt 1 exp])
   EOpC exp0 op exp -> prPrec i 1 (concatD [prt 1 exp0 , prt 1 op , prt 2 exp])
   EOpD exp0 op exp -> prPrec i 2 (concatD [prt 2 exp0 , prt 2 op , prt 3 exp])
   EOpE exp0 op exp -> prPrec i 0 (concatD [prt 1 exp0 , prt 0 op , prt 1 exp])
   EVar id -> prPrec i 3 (concatD [prt 0 id])
   EInt n -> prPrec i 3 (concatD [prt 0 n])
   FunCall id exps -> prPrec i 3 (concatD [prt 0 id , doc (showString "(") , prt 0 exps , doc (showString ")")])
   EInc id -> prPrec i 3 (concatD [prt 0 id , doc (showString "++")])
   EDecr id -> prPrec i 3 (concatD [prt 0 id , doc (showString "--")])
   ESub exp -> prPrec i 3 (concatD [doc (showString "-") , prt 0 exp])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Op where
  prt i e = case e of
   OAdd  -> prPrec i 1 (concatD [doc (showString "+")])
   OMult  -> prPrec i 2 (concatD [doc (showString "*")])
   ODiv  -> prPrec i 2 (concatD [doc (showString "/")])
   OSub  -> prPrec i 1 (concatD [doc (showString "-")])
   OLt  -> prPrec i 0 (concatD [doc (showString "<")])
   OGt  -> prPrec i 0 (concatD [doc (showString ">")])
   OEq  -> prPrec i 0 (concatD [doc (showString "==")])
   OAnd  -> prPrec i 0 (concatD [doc (showString "&&")])
   OOr  -> prPrec i 0 (concatD [doc (showString "||")])



