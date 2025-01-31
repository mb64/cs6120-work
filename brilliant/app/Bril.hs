module Bril where

import qualified Data.Text as T
import Data.Text (Text)
import Data.Char
import Data.Foldable
import Data.Aeson hiding (Bool)
import Data.Aeson qualified as Aeson
import Data.Aeson.Types (Parser)
import Data.Scientific
import Control.Monad
import Control.Applicative hiding (Const(..))

data Type = Int | Bool deriving (Show, Eq, Ord)
data Op = Add | Mul | Sub | Div | Eq | Lt | Gt | Le | Ge | Not | And | Or
        | Id | Nop | Print
        deriving (Show, Eq, Ord)

type Label = Text
type Var = Text
type FuncRef = Text
type Dest = (Var, Type)

data Lit = IntLit Int | BoolLit Bool deriving (Show, Eq, Ord)

data Instr
  = Const Dest Lit
  | Op Dest Op [Var]
  | Call (Maybe Dest) FuncRef [Var]
  | Effect Op [Var]
  deriving (Show, Eq, Ord)

data Jump
  = Jmp Label
  | Br Var Label Label
  | Ret (Maybe Var)
  deriving (Show, Eq, Ord)

data CodeItem
  = Label Label
  | Instr Instr
  | Jump Jump
  deriving (Show, Eq, Ord)

data Function = Function Text [Dest] (Maybe Type) [CodeItem] deriving (Show, Eq, Ord)
newtype Program = Program [Function] deriving (Show, Eq, Ord)

-- ToJSON instances --

instance ToJSON Type where toJSON = toJSON . map toLower . show
instance ToJSON Op where toJSON = toJSON . map toLower . show

instance ToJSON Lit where
  toJSON (IntLit x) = toJSON x
  toJSON (BoolLit x) = toJSON x

instance ToJSON Instr where
  toJSON i = object $ case i of
    Const d v -> dest d ++ ["op" .= ("const" :: String), "value" .= v]
    Op d o a -> dest d ++ op o ++ args a
    Call d f a -> foldMap dest d ++ ["funcs" .= [f]] ++ args a
    Effect o a -> op o ++ args a
    where dest (x,t) = ["dest" .= x, "type" .= t]
          op o = ["op" .= o]
          args a = ["args" .= a]

instance ToJSON Jump where
  toJSON (Jmp l) = object ["op" .= String "jmp", "labels" .= [l]]
  toJSON (Br x t f) = object ["op" .= String "br", "args" .= [x], "labels" .= [t,f]]
  toJSON (Ret Nothing) = object ["op" .= String "ret"]
  toJSON (Ret (Just x)) = object ["op" .= String "ret", "args" .= [x]]

instance ToJSON CodeItem where
  toJSON (Label l) = object ["label" .= l]
  toJSON (Instr i) = toJSON i
  toJSON (Jump j) = toJSON j

instance ToJSON Function where
  toJSON (Function name args ty instrs) = object $
    [ "name" .= name
    , "args" .= [object ["name" .= x, "type" .= t] | (x,t) <- args]
    ] ++ tyPair ++ ["instrs" .= instrs]
    where tyPair = foldMap (\t -> ["type" .= t]) ty

instance ToJSON Program where
  toJSON (Program fs) = object ["functions" .= fs]

instance FromJSON Type where
  parseJSON = withText "type" \case
    "int" -> pure Int
    "bool" -> pure Bool
    _ -> fail "bad type"

instance FromJSON Op where
  parseJSON = withText "opcode" \case
    "add" -> pure Add 
    "mul" -> pure Mul 
    "sub" -> pure Sub 
    "div" -> pure Div 
    "eq" -> pure Eq 
    "lt" -> pure Lt 
    "gt" -> pure Gt 
    "le" -> pure Le 
    "ge" -> pure Ge 
    "not" -> pure Not 
    "and" -> pure And 
    "or" -> pure Or 
    "id" -> pure Id 
    "nop" -> pure Nop 
    "print" -> pure Print
    _ -> fail "bad op"

instance FromJSON Lit where
  parseJSON (Aeson.Bool x) = pure (BoolLit x)
  parseJSON (Number x) = case toBoundedInteger x of
    Just i -> pure $ IntLit i
    Nothing -> fail "number not an integer"
  parseJSON _ = fail "bad literal"

expectOp :: String -> Object -> Parser ()
expectOp op obj = do
  op' <- obj .: "op"
  when (op /= op') $ fail $ "expected " ++ op ++ ", got " ++ op'

instance FromJSON Instr where
  parseJSON = withObject "instr" \o -> parseConst o <|> parseOp o <|> parseCall o <|> parseEffect o
    where dest o = (,) <$> o .: "dest" <*> o .: "type"
          maybeDest o = fmap Just (dest o) <|> pure Nothing
          func o = do
            [f] <- o .: "funcs"
            pure f
          parseConst o = do
            expectOp "const" o
            Const <$> dest o <*> o .: "value"
          parseOp o = Op <$> dest o <*> o .: "op" <*> o .: "args"
          parseCall o = Call <$> maybeDest o <*> func o <*> o .: "args"
          parseEffect o = Effect <$> o .: "op" <*> o .: "args"

instance FromJSON Jump where
  parseJSON = withObject "jump" \o -> parseJmp o <|> parseBr o <|> parseRet o
    where parseJmp o = do
            expectOp "jmp" o
            [lbl] <- o .: "labels"
            pure $ Jmp lbl
          parseBr o = do
            expectOp "br" o
            [arg] <- o .: "args"
            [l1, l2] <- o .: "labels"
            pure $ Br arg l1 l2
          parseRet o = do
            expectOp "ret" o
            args <- o .: "args"
            case args of
              [] -> pure $ Ret Nothing
              [x] -> pure $ Ret (Just x)
              _ -> fail "too many args for ret"

instance FromJSON CodeItem where
  parseJSON o = Instr <$> parseJSON o <|> Jump <$> parseJSON o <|> Label <$> parseLabel o
    where parseLabel = withObject "label" \o -> o .: "label"

instance FromJSON Function where
  parseJSON = withObject "function" \o -> do
    args <- o .:?= "args"
    Function
      <$> o .: "name"
      <*> traverse (\arg -> (,) <$> arg .: "name" <*> arg .: "type") args
      <*> o .:? "type"
      <*> o .: "instrs"

instance FromJSON Program where
  parseJSON = withObject "program" $ \o -> Program <$> o .: "functions"
