module Bril where

import qualified Data.Text as T
import Data.Text (Text)
import Data.Char
import Data.Maybe
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
data Dest = Dest Var Type deriving (Show, Eq, Ord)

destVar :: Dest -> Var
destVar (Dest v _) = v

data Lit = IntLit Int | BoolLit Bool deriving (Show, Eq, Ord)

data Instr
  = Constant Dest Lit
  | Op Dest Op [Var]
  | Call (Maybe Dest) FuncRef [Var]
  | Effect Op [Var]
  deriving (Show, Eq, Ord)

isPure :: Instr -> Bool
isPure (Constant _ _) = True
isPure (Op _ _ _) = True
isPure (Call _ _ _) = False
isPure (Effect _ _) = False

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

-- | Code traversals
data Visitor f = Visitor
  { visitUse :: Var -> f Var
  , visitDef :: Dest -> f Dest
  , visitOp :: Op -> f Op
  , visitLabel :: Label -> f Label
  }

defaultVisitor :: Applicative f => Visitor f
defaultVisitor = Visitor pure pure pure pure

visitVars :: Applicative f => (Var -> f Var) -> Visitor f
visitVars f = Visitor f (\(Dest x t) -> Dest <$> f x <*> pure t) pure pure

class Code a where
  visit :: Applicative f => Visitor f -> a -> f a

instance Code Var where visit = visitUse
instance Code Dest where visit = visitDef
instance Code Op where visit = visitOp
instance (Traversable f, Code a) => Code (f a) where
  visit v = traverse (visit v)

instance Code Instr where
  visit v (Constant d n) = Constant <$> visit v d <*> pure n
  visit v (Op d o xs) = Op <$> visit v d <*> visit v o <*> visit v xs
  visit v (Call d f xs) = Call <$> visit v d <*> pure f <*> visit v xs
  visit v (Effect o xs) = Effect <$> visit v o <*> visit v xs

instance Code Jump where
  visit v (Jmp l) = Jmp <$> visitLabel v l
  visit v (Br x l1 l2) = Br <$> visit v x <*> visitLabel v l1 <*> visitLabel v l2
  visit v (Ret x) = Ret <$> visit v x

instance Code CodeItem where
  visit v (Jump j) = Jump <$> visit v j
  visit v (Instr i) = Instr <$> visit v i
  visit v (Label l) = Label <$> visitLabel v l

instance Code Function where
  visit v (Function name params ret code) =
    Function name <$> visit v params <*> pure ret <*> visit v code

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
    Constant d v -> dest d ++ ["op" .= ("const" :: String), "value" .= v]
    Op d o a -> dest d ++ op o ++ args a
    Call d f a -> foldMap dest d ++ ["op" .= ("call" :: String), "funcs" .= [f]] ++ args a
    Effect o a -> op o ++ args a
    where dest (Dest x t) = ["dest" .= x, "type" .= t]
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
    , "args" .= [object ["name" .= x, "type" .= t] | Dest x t <- args]
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
  parseJSON = withObject "instr" \o -> do
    let dest o = Dest <$> o .: "dest" <*> o .: "type"
        maybeDest o = fmap Just (dest o) <|> pure Nothing
        func o = do
          [f] <- o .: "funcs"
          pure f
    o .: "op" >>= \case
      "const" -> Constant <$> dest o <*> o .: "value"
      "call" -> Call <$> maybeDest o <*> func o <*> o .: "args"
      (_ :: String) -> maybeDest o >>= \case
        Just d -> Op d <$> o .: "op" <*> o .: "args"
        Nothing -> Effect <$> o .: "op" <*> o .: "args"
    -- parseConstant o <|> parseOp o <|> parseCall o <|> parseEffect o
    --       parseConstant o = do
    --         expectOp "const" o
    --         Constant <$> dest o <*> o .: "value"
    --       parseOp o = Op <$> dest o <*> o .: "op" <*> o .: "args"
    --       parseCall o = Call <$> maybeDest o <*> func o <*> o .: "args"
    --       parseEffect o = Effect <$> o .: "op" <*> o .: "args"

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
            args <- fromMaybe [] <$> o .:? "args"
            case args of
              [] -> pure $ Ret Nothing
              [x] -> pure $ Ret (Just x)
              _ -> fail "too many args for ret"

instance FromJSON CodeItem where
  parseJSON o = Instr <$> parseJSON o <|> Jump <$> parseJSON o <|> Label <$> parseLabel o
    where parseLabel = withObject "label" \o -> o .: "label"

instance FromJSON Function where
  parseJSON = withObject "function" \o -> do
    args <- fromMaybe [] <$> o .:? "args"
    Function
      <$> o .: "name"
      <*> traverse (\arg -> Dest <$> arg .: "name" <*> arg .: "type") args
      <*> o .:? "type"
      <*> o .: "instrs"

instance FromJSON Program where
  parseJSON = withObject "program" $ \o -> Program <$> o .: "functions"
