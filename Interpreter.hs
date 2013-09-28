module Interpreter where

import Control.Monad
import System.Environment
import Control.Monad.Error
import Data.IORef
import Debug.Trace
import Text.ParserCombinators.Parsec hiding (spaces)
import Text.ParserCombinators.Parsec.Error
import System.IO 

import Abswc_gram

type Env = IORef [(Ident, IORef CVal)]

-- creating empty envirtonment
nullEnv :: IO Env
nullEnv = newIORef []

-- types available in interpreter
data CVal =    List Type [CVal]
             | Int Integer
             | Func FunT

-- expression value
data ExpVal = EI Integer | EL ExpVal [CVal] | EB Bool | ERR String | EV 

type FunT = ([Arg], Env, [Instruction], ExpVal)

instance Show ExpVal where show = showType

showType :: ExpVal -> String
showType (EI n) = "int " ++ (show n)
showType (EB b) = "int " ++ (show b)
showType (EL l _) = "list<" ++ show(l) ++ ">"
showType (ERR s) = "error: " ++ s
showType EV = "void"

instance Show CVal where show = showVal

showVal :: CVal -> String
showVal (Int n) = show n
showVal (List typ contents) = "(" ++ unwordsList contents ++ ")"
showVal (Func (arguments, _, _, expectedVal)) =  "(" ++ (unwordsArgs arguments) ++ ") -> " ++ show expectedVal



interpret :: [Instruction] -> Env  -> Bool -> IO (Maybe Env)
interpret [] env enable_info = return (Just env)
interpret (i:rules_list) env enable_info = do
        res_env <- interpretInstruction i env enable_info
        case res_env of
                Nothing -> interpret rules_list env enable_info
                Just new_env -> interpret rules_list new_env enable_info


interpretInstruction :: Instruction -> Env  -> Bool -> IO (Maybe Env)
interpretInstruction (DDecl d) env enable_info = interpretDecl d env
interpretInstruction (DStmt s) env enable_info = interpretStmt s env enable_info


interpretDecl :: Decl -> Env -> IO (Maybe Env)
interpretDecl (NVariable typ name) env  = case typ of
            TInt    -> defineVar env name (Int 0)
            TList t -> defineVar env name (List t [])
            _       -> hPutStrLn stderr ("Wrong type " ++ show typ) >> return Nothing
interpretDecl (NFunction typ name argums body) env = defineVar env name (Func (argums, env, body, (typToExpVal typ)))
interpretDecl (NFunctionV name argums body) env    = defineVar env name (Func (argums, env, body, EV))
interpretDecl  _ _  = return Nothing


interpretStmt :: Stmt -> Env  -> Bool -> IO (Maybe Env )
interpretStmt (FreeExp e) env enable_info = do
        result <- (eval e env)
        case result of
            EI val -> do
                if (enable_info) then putStrLn (":- int = " ++ (show val)) else return ()
                return $ Just env
            EB val -> do
                if (enable_info) then putStrLn (":- Bool = " ++ (show val)) else return ()
                return $ Just env
            ERR s -> do
                    hPutStrLn stderr ("error: " ++ s)
                    return $ Just env
            EV -> return $ Just env
interpretStmt (Assignment (Ident name) e) env enable_info = do
        var <-getVar env (Ident name)
        case var of
            Just ioVar ->  do
                val <- (eval e env)
                case val of
                    ERR s -> do
                            hPutStrLn stderr ("error: " ++ s)
                            return Nothing
                    EI num -> do 
                            realVal <- ioVar
                            case realVal of
                                Int n -> defineVar env (Ident name)  (Int num)
                                _ -> hPutStrLn stderr ("error: Type mismatch, variable " ++ (show realVal)  ++ " is not an int") >> return Nothing
                    EL _ list  -> do
                            realVal <- ioVar
                            case realVal of
                                List t stara -> (putStrLn $ (show stara ++ " " ++ show list)) >>  defineVar env (Ident name) (List t list) 
                                _   -> hPutStrLn stderr ("error: Type mismatch, variable " ++ (show realVal) ++ " is not a list") >> return Nothing
            Nothing -> do
                hPutStrLn stderr ("error: variable " ++ name ++ " undefined")
                return Nothing

interpretStmt (EEAdd idd e) env enable_info = interpretStmt (Assignment idd (EOpC ( EVar idd) OAdd e)) env enable_info
interpretStmt (EESub idd e) env enable_info = interpretStmt (Assignment idd (EOpC ( EVar idd) OSub e)) env enable_info
interpretStmt (EEMul idd e) env enable_info = interpretStmt (Assignment idd (EOpD ( EVar idd) OMult e)) env enable_info
interpretStmt (EEDiv idd e) env enable_info = interpretStmt (Assignment idd (EOpD ( EVar idd) ODiv e)) env enable_info
interpretStmt (VPrint (Ident name)) env enable_info = do
        maybe_val <- getVar env (Ident name) 
        case maybe_val of
            Just a ->  do 
                val <- a
                putStrLn $ show val
                return $ Just env
            Nothing -> return Nothing
interpretStmt (IfSe e s1 s2) env enable_info = do
        val <- (eval e env)
        case val of
            EB True  -> interpretStmt s1 env False
            EB False -> interpretStmt s2 env False
            _ -> do
                    hPutStrLn stderr "error: Wrong expression in if statement"
                    return (Nothing)
interpretStmt (BlockS sList) env enable_info = do
            new_env <- interpret sList env False
            case new_env of
                Just _ -> return (new_env)
                Nothing -> do
                        hPutStrLn stderr "error: Bad block"
                        return (Nothing)
interpretStmt (WhileS e stm) env enable_info = do
        val <- (eval e env)
        case val of
            EB True -> do
                    new_env <- interpretStmt stm env False
                    case new_env of
                        Just environ -> interpretStmt (WhileS e stm) environ enable_info
                        Nothing -> do
                                hPutStrLn stderr "errror: Bad while body"
                                return (Nothing)
            EB False -> return (Just env)
interpretStmt (RetS _ ) env enable_info = do
        hPutStrLn stderr "error: return statement outside function"
        return (Nothing)
-- do nothing if list is empty
interpretStmt (PopBackS ident) env enable_info = do
        may_list <- getVar env ident
        case may_list of
            Just ioList -> do
                    list <- ioList
                    case list of
                        List t actual_list -> if (length actual_list) > 0
                            then setVar env ident (List t (init actual_list))
                            else return $ Just env
            Nothing -> (hPutStrLn stderr "List not defined") >> return Nothing
-- do nothing if list is empty
interpretStmt (PopFrontS ident) env enable_info = do
        may_list <- getVar env ident
        case may_list of
            Just ioList -> do
                    list <- ioList
                    case list of
                        List t actual_list -> if (length actual_list) > 0
                                then setVar env ident (List t (tail actual_list))
                                else return $ Just env
            Nothing -> (hPutStrLn stderr "List not defined") >> return Nothing
interpretStmt (PushFrontS ident e) env enable_info = do
        may_list <- getVar env ident
        case may_list of
            Just ioList -> do
                    list <- ioList
                    case list of
                        List t actual_list -> do
                                val <- eval e env
                                if expTypeEqual (typToExpVal t) val 
                                    then case val of
                                        EI num -> setVar env ident (List t ([Int num] ++ actual_list))
                                        EL tajp add_list -> setVar env ident (List t ([(List (expValToTyp tajp) add_list)]++ actual_list))
                                    else do
                                        hPutStrLn stderr ("error: Assigning type \"" ++ (show $ expValToTyp val) ++ "\" whereas should be \"list<" ++ (show t) ++ ">\"")
                                        return Nothing
            Nothing -> (hPutStrLn stderr "List not defined") >> return Nothing
interpretStmt (PushBackS ident e) env enable_info = do
        may_list <- getVar env ident
        case may_list of
            Just ioList -> do
                    list <- ioList
                    case list of
                        List t actual_list -> do
                                val <- eval e env
                                if expTypeEqual (typToExpVal t) val 
                                    then case val of
                                        EI num -> setVar env ident (List t (actual_list++[Int num]))
                                        EL tajp add_list -> setVar env ident (List t (actual_list ++ [(List (expValToTyp tajp) add_list)]))
                                    else do
                                        hPutStrLn stderr ("error: Assigning type \"" ++ (show $ expValToTyp val) ++ "\" whereas should be \"list<" ++ (show t) ++ ">\"")
                                        return Nothing
            Nothing -> (hPutStrLn stderr "List not defined") >> return Nothing




eval :: Exp -> Env  -> IO (ExpVal )
eval x env = case x of
    EOpA e1 op e2 -> let
            operator = case op of
                OAnd  -> (&&)
                OOr   -> (||)
            in do
                    ev1 <- eval e1 env
                    ev2 <- eval e2 env
                    case (ev1,ev2) of
                        (EB v1,EB v2) -> return (EB (operator v1 v2))
                        (ERR s,_)     -> return (ERR s)
                        _             -> return (ERR "undefined expression")

    EOpE e1 op e2 -> let
            operator = case op of
                OAnd  -> (&&)
                OOr   -> (||)
            in do
                    ev1 <- eval e1 env
                    ev2 <- eval e2 env
                    case (ev1,ev2) of
                        (EB v1,EB v2) -> return (EB (operator v1 v2))
                        (ERR s,_)     -> return (ERR s)
                        _             -> return (ERR "undefined expression")
    EOpB e1 op e2 -> let
            operator = case op of
                OLt  -> (<)
                OGt  -> (>)
                OEq  -> (==)
            in do
                    ev1 <- eval e1 env
                    ev2 <- eval e2 env
                    case (ev1,ev2) of
                        (EI v1,EI v2) -> return (EB (operator v1 v2))
                        (ERR s,_)     -> return (ERR s)
                        _             -> return (ERR "undefined expression")
    EOpC e1 op e2 -> let
        operator = case op of
            OAdd  -> (+)
            OSub -> (-)
        in do
                ev1 <- eval e1 env
                ev2 <- eval e2 env
                case (ev1,ev2) of
                    (EI v1,EI v2) -> return (EI (operator v1 v2))
                    (ERR s,_)     -> return (ERR s)
                    _             -> return (ERR "undefined expression")
    EOpD e1 op e2 -> let
        operator = case op of
            OMult  -> (\a b -> EI (a * b))
            ODiv    -> (\a b -> if (b == 0) then (ERR "division by zero") else (EI (a `div` b)))
        in do
                ev1 <- eval e1 env
                ev2 <- eval e2 env
                case (ev1,ev2) of
                    (EI v1,EI v2) -> return ((operator v1 v2))
                    (ERR s,_)     -> return (ERR s)
                    _         -> return (ERR "undefined expression")
    EInt x -> return (EI x)
    EVar (Ident x) -> do
            var <- (getVar env (Ident x)) 
            case var of
                Just a -> do
                    val <- a
                    case val of
                        Int num -> return (EI num)
                        List t l -> return (EL (typToExpVal t)  l)
                        _       -> return (ERR "Not an expression")
                Nothing ->  return (ERR ("variable " ++ x ++ " does not exist"))
    EInc (Ident x) -> do
            result <- eval (EVar (Ident x)) env
            case result of
                (EI v) -> setVar env (Ident x) (Int (v+1))
            return result;
    EDecr (Ident x) -> do
            result <- eval (EVar (Ident x)) env
            case result of
                (EI v) -> (setVar env (Ident x) (Int (v-1)))
            return result;
    ESub e -> do
            val <- eval e env
            case val of
                EI v -> return (EI (-v))
                _    -> return ( ERR "undefined expression" )
    FunCall (Ident fid) paramsList -> do
            maybe_fun <- getVar env (Ident fid)
            case maybe_fun of
                Nothing -> return $ ERR ("no such function: " ++ fid)
                Just f -> do
                        fun <- f
                        case fun of
                            Func (args, old_env, block, ret) -> do
                                    may_fval <- funcCall (Func (args, old_env, block, ret)) env fid
                                    case may_fval of
                                        Just expres -> if expTypeEqual ret expres
                                                then return expres
                                                else return $ ERR ("error: function " ++ fid ++ " returned bad type")
                                        Nothing     -> return EV
                            _           -> return $ ERR (fid ++ " is not a function")



--funcCall :: FunT -> Env -> [Instruction] -> Ident ->
-- empty function
funcCall (Func (_, _, [], ret)) env name = return (Nothing)
funcCall (Func (_, _, [stmt], ret)) env name = case stmt of
        DStmt (RetS e) -> do
                val <- eval e env
                return (Just val)
        instr   -> do
                new_env <- interpretInstruction instr env False
                case new_env of
                    Nothing -> return $ Just $ ERR ""
                    Just environ -> return $ Just EV
funcCall (Func (a, e, (instr:block), ret)) env name = do
        new_env <- interpretInstruction instr env False
        case new_env of
            Just environment -> funcCall (Func (a, e, block, ret)) environment name
            _                -> return $ Just $ ERR ("bad statement in function: " ++ name)


isBound :: Env -> Ident -> IO Bool
isBound envRef var = readIORef envRef >>= return . maybe False (const True) . lookup var

getVar :: Env -> Ident -> IO (Maybe (IO CVal))
getVar envRef (Ident name) = do
        env <- liftIO $ readIORef envRef
        case (lookup (Ident name) env) of
            Just value -> return $ Just $ readIORef value
            Nothing -> hPutStrLn stderr ("Variable not defined " ++ name) >> return Nothing


setVar :: Env -> Ident -> CVal -> IO (Maybe Env)
setVar envRef var value = do
        env <- liftIO $ readIORef envRef
        case (lookup var env) of
            Just valRef -> writeIORef valRef value >>  return (Just envRef)
            _ -> hPutStrLn stderr "Setting an unbound variable " >> return Nothing


defineVar :: Env -> Ident -> CVal -> IO (Maybe  Env)
defineVar envRef var value = do
        alreadyDefined <- liftIO $ isBound envRef var
        if alreadyDefined then
            setVar envRef var value 
        else do
            valueRef <- newIORef value
            env <- readIORef envRef
            writeIORef envRef ((var, valueRef) : env)
            return (Just envRef)


unwordsList :: [CVal] -> String
unwordsList = unwords . map showVal


unwordsArgs :: [Arg] -> String
unwordsArgs [] = ""
unwordsArgs [Param typ _] = show typ
unwordsArgs ((Param typ _):t) = (show typ) ++ ", " ++ unwordsArgs t


typToExpVal :: Type -> ExpVal
typToExpVal TInt = (EI 0)
typToExpVal (TList t) =  (EL ev [])
    where
        ev = typToExpVal t

expValToTyp :: ExpVal -> Type
expValToTyp (EI _) = TInt
expValToTyp (EB _) = TInt
expValToTyp (ERR _) = TInt
expValToTyp EV = TInt
expValToTyp (EL l _) = TList $ expValToTyp l


expToVarVal :: ExpVal -> CVal
expToVarVal (EI n) = Int n
expToVarVal (EL l _) = List (expValToTyp l) [(expToVarVal l)]


expTypeEqual :: ExpVal -> ExpVal -> Bool
expTypeEqual (EI _) (EI _) = True
expTypeEqual (EL t1 _) (EL t2 _) = expTypeEqual t1 t2
expTypeEqual  _ _ = False


