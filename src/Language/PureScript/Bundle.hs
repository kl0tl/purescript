-- |
-- Bundles compiled PureScript modules for the browser.
--
-- This module takes as input the individual generated modules from 'Language.PureScript.Make' and
-- performs dead code elimination, filters empty modules,
-- and generates the final JavaScript bundle.
module Language.PureScript.Bundle
  ( bundle
  , bundleSM
  , guessModuleIdentifier
  , ModuleIdentifier(..)
  , moduleName
  , ModuleType(..)
  , ErrorMessage(..)
  , printErrorMessage
  , getExportedIdentifiers
  , Module
  ) where

import Prelude.Compat
import Protolude (ordNub)

import Control.Monad
import Control.Monad.Error.Class
import Control.Arrow ((&&&))

import Data.Aeson ((.=))
import Data.Array ((!))
import Data.Char (chr, digitToInt)
import Data.Foldable (fold)
import Data.Generics (GenericM, everything, everythingWithContext, everywhere, gmapMo, mkMp, mkQ, mkT)
import Data.Graph
import Data.List (stripPrefix, (\\))
import Data.Maybe (catMaybes, fromMaybe, mapMaybe, maybeToList)
import Data.Version (showVersion)
import qualified Data.Aeson as A
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text.Lazy as T

import Language.JavaScript.Parser
import Language.JavaScript.Parser.AST
import Language.JavaScript.Process.Minify

import qualified Paths_purescript as Paths

import System.FilePath (takeFileName, takeDirectory, takeDirectory, makeRelative)

import SourceMap.Types

-- | The type of error messages. We separate generation and rendering of errors using a data
-- type, in case we need to match on error types later.
data ErrorMessage
  = UnsupportedModulePath String
  | InvalidTopLevel
  | UnableToParseModule String
  | UnsupportedImport
  | UnsupportedExport
  | ErrorInModule ModuleIdentifier ErrorMessage
  | MissingEntryPoint String
  | MissingMainModule String
  deriving (Show)

-- | Modules are either "regular modules" (i.e. those generated by the PureScript compiler) or
-- foreign modules.
data ModuleType
  = Regular
  | Foreign
  deriving (Show, Eq, Ord)

showModuleType :: ModuleType -> String
showModuleType Regular = "Regular"
showModuleType Foreign = "Foreign"

-- | A module is identified by its module name and its type.
data ModuleIdentifier = ModuleIdentifier String ModuleType deriving (Show, Eq, Ord)

instance A.ToJSON ModuleIdentifier where
  toJSON (ModuleIdentifier name mt) =
    A.object [ "name" .= name
             , "type" .= show mt
             ]

moduleName :: ModuleIdentifier -> String
moduleName (ModuleIdentifier name _) = name

-- | Given a filename, assuming it is in the correct place on disk, infer a ModuleIdentifier.
guessModuleIdentifier :: MonadError ErrorMessage m => FilePath -> m ModuleIdentifier
guessModuleIdentifier filename = ModuleIdentifier (takeFileName (takeDirectory filename)) <$> guessModuleType (takeFileName filename)
  where
    guessModuleType "index.js" = pure Regular
    guessModuleType "foreign.js" = pure Foreign
    guessModuleType name = throwError $ UnsupportedModulePath name

data Visibility
  = Public
  | Internal
  deriving (Show, Eq, Ord)

-- | A piece of code is identified by its module, its name, and whether it is an internal variable
-- or a public member. These keys are used to label vertices in the dependency graph.
type Key = (ModuleIdentifier, String, Visibility)

-- | An export is either a "regular export", which exports a name from the regular module we are in,
-- or a reexport of a declaration in the corresponding foreign module.
--
-- Regular exports are labelled, since they might re-export an operator with another name.
data ExportType
  = RegularExport String
  | ForeignReexport
  deriving (Show, Eq, Ord)

-- | There are four types of module element we are interested in:
--
-- 1) Import declarations and require statements
-- 2) Member declarations
-- 3) Export lists
-- 4) Everything else
--
-- Each is labelled with the original AST node which generated it, so that we can dump it back
-- into the output during codegen.
data ModuleElement
  = Import JSModuleItem String (Either String ModuleIdentifier)
  | Member JSStatement Visibility String JSExpression [Key]
  | ExportsList [(ExportType, String, JSExpression, [Key])]
  | Other JSStatement
  | Skip JSModuleItem
  deriving (Show)

instance A.ToJSON ModuleElement where
  toJSON = \case
    (Import _ name (Right target)) ->
      A.object [ "type"   .= A.String "Import"
               , "name"   .= name
               , "target" .= target
               ]
    (Import _ name (Left targetPath)) ->
      A.object [ "type"       .= A.String "Import"
               , "name"       .= name
               , "targetPath" .= targetPath
               ]
    (Member _ visibility name _ dependsOn) ->
      A.object [ "type"       .= A.String "Member"
               , "name"       .= name
               , "visibility" .= show visibility
               , "dependsOn"  .= map keyToJSON dependsOn
               ]
    (ExportsList exports) ->
      A.object [ "type"    .= A.String "ExportsList"
               , "exports" .= map exportToJSON exports
               ]
    (Other stmt) ->
      A.object [ "type" .= A.String "Other"
               , "js"   .= getFragment (JSAstStatement stmt JSNoAnnot)
               ]
    (Skip item) ->
      A.object [ "type" .= A.String "Skip"
               , "js"   .= getFragment (JSAstModule [item] JSNoAnnot)
               ]

    where

    keyToJSON (mid, member, visibility) =
      A.object [ "module"     .= mid
               , "member"     .= member
               , "visibility" .= show visibility
               ]

    exportToJSON (RegularExport sourceName, name, _, dependsOn) =
      A.object [ "type"       .= A.String "RegularExport"
               , "name"       .= name
               , "sourceName" .= sourceName
               , "dependsOn"  .= map keyToJSON dependsOn
               ]
    exportToJSON (ForeignReexport, name, _, dependsOn) =
      A.object [ "type"      .= A.String "ForeignReexport"
               , "name"      .= name
               , "dependsOn" .= map keyToJSON dependsOn
               ]

    getFragment = ellipsize . renderToText . minifyJS
      where
      ellipsize text = if T.compareLength text 20 == GT then T.take 19 text `T.snoc` ellipsis else text
      ellipsis = '\x2026'

-- | A module is just a list of elements of the types listed above.
data Module = Module ModuleIdentifier (Maybe FilePath) [ModuleElement] deriving (Show)

instance A.ToJSON Module where
  toJSON (Module moduleId filePath elements) =
    A.object [ "moduleId" .= moduleId
             , "filePath" .= filePath
             , "elements" .= elements
             ]

-- | Prepare an error message for consumption by humans.
printErrorMessage :: ErrorMessage -> [String]
printErrorMessage (UnsupportedModulePath s) =
  [ "An ES or CommonJS module has an unsupported name (" ++ show s ++ ")."
  , "The following file names are supported:"
  , "  1) index.js (PureScript native modules)"
  , "  2) foreign.js (PureScript foreign modules)"
  ]
printErrorMessage InvalidTopLevel =
  [ "Expected a list of source elements at the top level." ]
printErrorMessage (UnableToParseModule err) =
  [ "The module could not be parsed:"
  , err
  ]
printErrorMessage UnsupportedImport =
  [ "An import was unsupported."
  , "Modules can be imported with ES namespace imports declarations:"
  , "  import * as module from \"Module.Name\""
  , "Alternatively, they can be also be imported with the CommonJS require function:"
  , "  var module = require(\"Module.Name\")"
  ]
printErrorMessage UnsupportedExport =
  [ "An export was unsupported."
  , "Declarations can be exported as ES named exports:"
  , "  export decl"
  , "Existing identifiers can be exported as well:"
  , "  export { name }"
  , "They can also be renamed on export:"
  , "  export { name as alias }"
  , "Alternatively, CommonJS exports can be defined in one of two ways:"
  , "  1) exports.name = value"
  , "  2) exports = { name: value }"
  ]
printErrorMessage (ErrorInModule mid e) =
  ("Error in module " ++ displayIdentifier mid ++ ":")
  : ""
  : map ("  " ++) (printErrorMessage e)
  where
    displayIdentifier (ModuleIdentifier name ty) =
      name ++ " (" ++ showModuleType ty ++ ")"
printErrorMessage (MissingEntryPoint mName) =
  [ "Couldn't find neither an ES nor CommonJS module for the specified entry point: " ++ mName
  ]
printErrorMessage (MissingMainModule mName) =
  [ "Couldn't find neither an ES nor CommonJS module for the specified main module: " ++ mName
  ]

-- | Calculate the ModuleIdentifier imported by an import declaration or a require(...) statement.
checkImportPath :: String -> ModuleIdentifier -> S.Set String -> Either String ModuleIdentifier
checkImportPath "./foreign.js" m _ =
  Right (ModuleIdentifier (moduleName m) Foreign)
checkImportPath name _ names
  | Just name' <- stripSuffix "/index.js" =<< stripPrefix "../" name
  , name' `S.member` names = Right (ModuleIdentifier name' Regular)
checkImportPath name _ _ = Left name

stripSuffix :: Eq a => [a] -> [a] -> Maybe [a]
stripSuffix suffix xs =
  case splitAt (length xs - length suffix) xs of
    (before, after)
      | after == suffix -> Just before
      | otherwise -> Nothing

-- | Compute the dependencies of all elements in a module, and add them to the tree.
--
-- Members and exports can have dependencies. A dependency is of one of the following forms:
--
-- 1) module.name or member["name"]
--
--    where module was imported using require
--
--    var module = require("Module.Name");
--
--    or an import declaration
--
--    import * as module from "Module.Name";
--
-- 2) name
--
--    where name is the name of a member defined in the current module.
withDeps :: Module -> Module
withDeps (Module modulePath fn es) = Module modulePath fn (map expandDeps es)
  where
  -- | Collects all modules which are imported, so that we can identify dependencies of the first type.
  imports :: [(String, ModuleIdentifier)]
  imports = mapMaybe toImport es
    where
    toImport :: ModuleElement -> Maybe (String, ModuleIdentifier)
    toImport (Import _ nm (Right mid)) = Just (nm, mid)
    toImport _ = Nothing

  -- | Collects all member names in scope, so that we can identify dependencies of the second type.
  boundNames :: [String]
  boundNames = mapMaybe toBoundName es
    where
    toBoundName :: ModuleElement -> Maybe String
    toBoundName (Member _ Internal nm _ _) = Just nm
    toBoundName _ = Nothing

  -- | Calculate dependencies and add them to the current element.
  expandDeps :: ModuleElement -> ModuleElement
  expandDeps (Member n f nm decl _) = Member n f nm decl (ordNub $ dependencies modulePath decl)
  expandDeps (ExportsList exps) = ExportsList (map expand exps)
      where
      expand (ty, nm, n1, _) = (ty, nm, n1, ordNub (dependencies modulePath n1))
  expandDeps other = other

  dependencies :: ModuleIdentifier -> JSExpression -> [Key]
  dependencies m = everythingWithContext boundNames (++) (mkQ (const [] &&& id) toReference)
    where
    toReference :: JSExpression -> [String] -> ([Key], [String])
    toReference (JSMemberDot mn _ nm) bn
      | JSIdentifier _ mn' <- mn
      , JSIdentifier _ nm' <- nm
      , Just mid <- lookup mn' imports
      = ([(mid, nm', Public)], bn)
    toReference (JSMemberSquare mn _ nm _) bn
      | JSIdentifier _ mn' <- mn
      , Just nm' <- fromStringLiteral nm
      , Just mid <- lookup mn' imports
      = ([(mid, nm', Public)], bn)
    toReference (JSIdentifier _ nm) bn
      | nm `elem` bn
      -- only add a dependency if this name is still in the list of names
      -- bound to the module level (i.e., hasn't been shadowed by a function
      -- parameter)
      = ([(m, nm, Internal)], bn)
    toReference (JSObjectLiteral _ props _) bn
      = let
          shorthandNames =
            filter (`elem` bn) $
            -- only add a dependency if this name is still in the list of
            -- names bound to the module level (i.e., hasn't been shadowed by a
            -- function parameter)
            mapMaybe unPropertyIdentRef $
            trailingCommaList props
        in
          (map (\name -> (m, name, Internal)) shorthandNames, bn)
    toReference (JSFunctionExpression _ _ _ params _ _) bn
      = ([], bn \\ (mapMaybe unIdentifier $ commaList params))
    toReference e bn
      | Just nm <- exportsAccessor e
      -- exports.foo means there's a dependency on the public member "foo" of
      -- this module.
      = ([(m, nm, Public)], bn)
    toReference _ bn = ([], bn)

    unIdentifier :: JSExpression -> Maybe String
    unIdentifier (JSIdentifier _ name) = Just name
    unIdentifier _ = Nothing

    unPropertyIdentRef :: JSObjectProperty -> Maybe String
    unPropertyIdentRef (JSPropertyIdentRef _ name) = Just name
    unPropertyIdentRef _ = Nothing

-- String literals include the quote chars
fromStringLiteral :: JSExpression -> Maybe String
fromStringLiteral (JSStringLiteral _ str) = Just $ strValue str
fromStringLiteral _ = Nothing

strValue :: String -> String
strValue str = go $ drop 1 str
  where
  go ('\\' : 'b' : xs) = '\b' : go xs
  go ('\\' : 'f' : xs) = '\f' : go xs
  go ('\\' : 'n' : xs) = '\n' : go xs
  go ('\\' : 'r' : xs) = '\r' : go xs
  go ('\\' : 't' : xs) = '\t' : go xs
  go ('\\' : 'v' : xs) = '\v' : go xs
  go ('\\' : '0' : xs) = '\0' : go xs
  go ('\\' : 'x' : a : b : xs) = chr (a' + b') : go xs
    where
    a' = 16 * digitToInt a
    b' = digitToInt b
  go ('\\' : 'u' : a : b : c : d : xs) = chr (a' + b' + c' + d') : go xs
    where
    a' = 16 * 16 * 16 * digitToInt a
    b' = 16 * 16 * digitToInt b
    c' = 16 * digitToInt c
    d' = digitToInt d
  go ('\\' : x : xs) = x : go xs
  go "\"" = ""
  go "'" = ""
  go (x : xs) = x : go xs
  go "" = ""

commaList :: JSCommaList a -> [a]
commaList JSLNil = []
commaList (JSLOne x) = [x]
commaList (JSLCons l _ x) = commaList l ++ [x]

trailingCommaList :: JSCommaTrailingList a -> [a]
trailingCommaList (JSCTLComma l _) = commaList l
trailingCommaList (JSCTLNone l) = commaList l

identName :: JSIdent -> Maybe String
identName (JSIdentName _ ident) = Just ident
identName _ = Nothing

exportStatementIdentifiers :: JSStatement -> [String]
exportStatementIdentifiers (JSVariable _ jsExpressions _) =
  varNames jsExpressions
exportStatementIdentifiers (JSConstant _ jsExpressions _) =
  varNames jsExpressions
exportStatementIdentifiers (JSLet _ jsExpressions _) =
  varNames jsExpressions
exportStatementIdentifiers (JSClass _ jsIdent _ _ _ _ _) =
  maybeToList . identName $ jsIdent
exportStatementIdentifiers (JSFunction _ jsIdent _ _ _ _ _) =
  maybeToList . identName $ jsIdent
exportStatementIdentifiers (JSGenerator _ _ jsIdent _ _ _ _ _) =
  maybeToList . identName $ jsIdent
exportStatementIdentifiers _ = []

varNames :: JSCommaList JSExpression -> [String]
varNames = mapMaybe varName . commaList
  where
  varName (JSVarInitExpression (JSIdentifier _ ident) _) = Just ident
  varName _ = Nothing

sp :: JSAnnot
sp = JSAnnot tokenPosnEmpty [ WhiteSpace tokenPosnEmpty " " ]

stringLiteral :: String -> JSExpression
stringLiteral s = JSStringLiteral JSNoAnnot $ "\"" ++ s ++ "\""

-- | Attempt to create a Module from a JavaScript AST.
--
-- Each type of module element is matched using pattern guards, and everything else is bundled into the
-- Other constructor.
toModule :: forall m. (MonadError ErrorMessage m) => S.Set String -> ModuleIdentifier -> Maybe FilePath -> JSAST -> m Module
toModule mids mid filename top
  | JSAstModule jsModuleItems _ <- top = Module mid filename . mconcat <$> traverse toModuleElements jsModuleItems
  | otherwise = err InvalidTopLevel
  where
  err :: ErrorMessage -> m a
  err = throwError . ErrorInModule mid

  toModuleElements :: JSModuleItem -> m [ModuleElement]
  toModuleElements item@(JSModuleImportDeclaration _ jsImportDeclaration)
    | JSImportDeclaration jsImportClause jsFromClause _ <- jsImportDeclaration
    , JSImportClauseNameSpace jsImportNameSpace <- jsImportClause
    , JSImportNameSpace _ _ jsIdent <- jsImportNameSpace
    , JSFromClause _ _ importPath <- jsFromClause
    , importPath' <- checkImportPath (strValue importPath) mid mids
    = fromMaybe (err UnsupportedImport) (pure <$> identName jsIdent) >>= \name ->
        pure [Import item name importPath']
  toModuleElements (JSModuleImportDeclaration _ _)
    = err UnsupportedImport

  toModuleElements (JSModuleExportDeclaration _ jsExportDeclaration)
    | JSExportFrom jsExportClause jsFromClause _ <- jsExportDeclaration
    , JSFromClause _ _ from <- jsFromClause
    , JSExportClause _ jsExportSpecifiers _ <- jsExportClause
    = pure . ExportsList <$> exportSpecifiersList (Just (strValue from)) jsExportSpecifiers
  toModuleElements (JSModuleExportDeclaration _ jsExportDeclaration)
    | JSExportLocals jsExportClause _ <- jsExportDeclaration
    , JSExportClause _ jsExportSpecifiers _ <- jsExportClause
    = pure . ExportsList <$> exportSpecifiersList Nothing jsExportSpecifiers
  toModuleElements (JSModuleExportDeclaration _ jsExportDeclaration)
    | JSExport jsStatement _ <- jsExportDeclaration
    = traverse (toExport' Nothing) (exportStatementIdentifiers jsStatement) >>= \exports ->
        pure [ Other jsStatement
             , ExportsList exports
             ]

  toModuleElements item@(JSModuleStatementListItem jsStatement)
    | Just (importName, importPath) <- matchRequire mids mid jsStatement
    = pure [Import item importName importPath]
  toModuleElements (JSModuleStatementListItem jsStatement)
    | Just (visibility, name, decl) <- matchMember jsStatement
    = pure [Member jsStatement visibility name decl []]
  toModuleElements (JSModuleStatementListItem jsStatement)
    | Just props <- matchExportsAssignment jsStatement
    = pure . ExportsList <$> traverse objectPropertyToExport (trailingCommaList props)
    where
      objectPropertyToExport :: JSObjectProperty -> m (ExportType, String, JSExpression, [Key])
      objectPropertyToExport (JSPropertyNameandValue name _ [val]) =
        (,,val,[]) <$> expressionExportType val
                   <*> extractLabel' name
      objectPropertyToExport _ = err UnsupportedExport

      expressionExportType :: JSExpression -> m ExportType
      expressionExportType (JSMemberDot f _ _)
        | JSIdentifier _ "$foreign" <- f
        = pure ForeignReexport
      expressionExportType (JSMemberSquare f _ _ _)
        | JSIdentifier _ "$foreign" <- f
        = pure ForeignReexport
      expressionExportType (JSIdentifier _ s) = pure (RegularExport s)
      expressionExportType _ = err UnsupportedExport

      extractLabel' = maybe (err UnsupportedExport) pure . extractLabel

  toModuleElements (JSModuleStatementListItem other) = pure [Other other]

  exportSpecifiersList from =
    fmap catMaybes . traverse (exportSpecifier from) . commaList

  exportSpecifier from (JSExportSpecifier jsIdent)
    = traverse (toExport' from) $ identName jsIdent
  exportSpecifier from (JSExportSpecifierAs jsIdent _ jsIdentAs)
    = sequence $ toExport from <$> identName jsIdent <*> identName jsIdentAs

  toExport :: Maybe String -> String -> String -> m (ExportType, String, JSExpression, [Key])
  toExport (Just "./foreign.js") name as =
    pure . (ForeignReexport, as,, []) $
             (JSMemberSquare (JSIdentifier sp "$foreign") JSNoAnnot
               (stringLiteral name) JSNoAnnot)
  toExport (Just _) _ _ = err UnsupportedExport
  toExport Nothing name as =
    pure (RegularExport name, as, JSIdentifier sp name, [])

  toExport' from name = toExport from name name

-- Get a list of all the exported identifiers from a foreign module.
--
-- TODO: what if we assign to exports.foo and then later assign to
-- module.exports (presumably overwriting exports.foo)?
getExportedIdentifiers :: forall m. (MonadError ErrorMessage m)
                          => String
                          -> JSAST
                          -> m [String]
getExportedIdentifiers mname top
  | JSAstModule jsModuleItems _ <- top = concat <$> traverse go jsModuleItems
  | otherwise = err InvalidTopLevel
  where
  err :: ErrorMessage -> m a
  err = throwError . ErrorInModule (ModuleIdentifier mname Foreign)

  go (JSModuleStatementListItem jsStatement)
    | Just props <- matchExportsAssignment jsStatement
    = traverse toIdent (trailingCommaList props)
    | Just (Public, name, _) <- matchMember jsStatement
    = pure [name]
    | otherwise
    = pure []
  go (JSModuleExportDeclaration _ jsExportDeclaration) =
    pure $ exportDeclarationIdentifiers jsExportDeclaration
  go _ = pure []

  toIdent (JSPropertyNameandValue name _ [_]) =
    extractLabel' name
  toIdent _ =
    err UnsupportedExport

  extractLabel' = maybe (err UnsupportedExport) pure . extractLabel

  exportDeclarationIdentifiers (JSExportFrom jsExportClause _ _) =
    exportClauseIdentifiers jsExportClause
  exportDeclarationIdentifiers (JSExportLocals jsExportClause _) =
    exportClauseIdentifiers jsExportClause
  exportDeclarationIdentifiers (JSExport jsStatement _) =
    exportStatementIdentifiers jsStatement

  exportClauseIdentifiers (JSExportClause _ jsExportsSpecifiers _) =
    mapMaybe exportSpecifierName $ commaList jsExportsSpecifiers

  exportSpecifierName (JSExportSpecifier jsIdent) = identName jsIdent
  exportSpecifierName (JSExportSpecifierAs _ _ jsIdentAs) = identName jsIdentAs

-- Matches JS statements like this:
-- var ModuleName = require("file");
matchRequire :: S.Set String
                -> ModuleIdentifier
                -> JSStatement
                -> Maybe (String, Either String ModuleIdentifier)
matchRequire mids mid stmt
  | JSVariable _ jsInit _ <- stmt
  , [JSVarInitExpression var varInit] <- commaList jsInit
  , JSIdentifier _ importName <- var
  , JSVarInit _ jsInitEx <- varInit
  , JSMemberExpression req _ argsE _ <- jsInitEx
  , JSIdentifier _ "require" <- req
  , [ Just importPath ] <- map fromStringLiteral (commaList argsE)
  , importPath' <- checkImportPath importPath mid mids
  = Just (importName, importPath')
  | otherwise
  = Nothing

-- Matches JS member declarations.
matchMember :: JSStatement -> Maybe (Visibility, String, JSExpression)
matchMember stmt
  -- var foo = expr;
  | JSVariable _ jsInit _ <- stmt
  , [JSVarInitExpression var varInit] <- commaList jsInit
  , JSIdentifier _ name <- var
  , JSVarInit _ decl <- varInit
  = Just (Internal, name, decl)
  -- exports.foo = expr; exports["foo"] = expr;
  | JSAssignStatement e (JSAssign _) decl _ <- stmt
  , Just name <- exportsAccessor e
  = Just (Public, name, decl)
  | otherwise
  = Nothing

-- Matches exports.* or exports["*"] expressions and returns the property name.
exportsAccessor :: JSExpression -> Maybe String
exportsAccessor (JSMemberDot exports _ nm)
  | JSIdentifier _ "exports" <- exports
  , JSIdentifier _ name <- nm
  = Just name
exportsAccessor (JSMemberSquare exports _ nm _)
  | JSIdentifier _ "exports" <- exports
  , Just name <- fromStringLiteral nm
  = Just name
exportsAccessor _ = Nothing

-- Matches assignments to module.exports, like this:
-- module.exports = { ... }
matchExportsAssignment :: JSStatement -> Maybe JSObjectPropertyList
matchExportsAssignment stmt
  | JSAssignStatement e (JSAssign _) decl _ <- stmt
  , JSMemberDot module' _ exports <- e
  , JSIdentifier _ "module" <- module'
  , JSIdentifier _ "exports" <- exports
  , JSObjectLiteral _ props _ <- decl
  = Just props
  | otherwise
  = Nothing

extractLabel :: JSPropertyName -> Maybe String
extractLabel (JSPropertyString _ nm) = Just $ strValue nm
extractLabel (JSPropertyIdent _ nm) = Just nm
extractLabel _ = Nothing

-- | Eliminate unused code based on the specified entry point set.
compile :: [Module] -> [ModuleIdentifier] -> [Module]
compile modules [] = modules
compile modules entryPoints = filteredModules
  where
  (graph, vertexToNode, vertexFor) = graphFromEdges verts

  -- | The vertex set
  verts :: [(ModuleElement, Key, [Key])]
  verts = do
    Module mid _ els <- modules
    concatMap (toVertices mid) els
    where
    -- | Create a set of vertices for a module element.
    --
    -- Imports declarations and require statements don't contribute towards dependencies,
    -- since they effectively get inlined wherever they are used inside other module elements.
    toVertices :: ModuleIdentifier -> ModuleElement -> [(ModuleElement, Key, [Key])]
    toVertices p m@(Member _ visibility nm _ deps) = [(m, (p, nm, visibility), deps)]
    toVertices p m@(ExportsList exps) = map toVertex exps
      where
      toVertex (ForeignReexport, nm, _, ks) = (m, (p, nm, Public), ks)
      toVertex (RegularExport _, nm, _, ks) = (m, (p, nm, Public), ks)
    toVertices _ _ = []

  -- | The set of vertices whose connected components we are interested in keeping.
  entryPointVertices :: [Vertex]
  entryPointVertices = catMaybes $ do
    (_, k@(mid, _, Public), _) <- verts
    guard $ mid `elem` entryPoints
    return (vertexFor k)

  -- | The set of vertices reachable from an entry point
  reachableSet :: S.Set Vertex
  reachableSet = S.fromList (concatMap (reachable graph) entryPointVertices)

  -- | A map from modules to the modules that are used by its reachable members.
  moduleReferenceMap :: M.Map ModuleIdentifier (S.Set ModuleIdentifier)
  moduleReferenceMap = M.fromAscListWith mappend $ map (vertToModule &&& vertToModuleRefs) $ S.toList reachableSet
    where
    vertToModuleRefs v = foldMap (S.singleton . vertToModule) $ graph ! v
    vertToModule v = m where (_, (m, _, _), _) = vertexToNode v

  filteredModules :: [Module]
  filteredModules = map filterUsed modules
    where
    filterUsed :: Module -> Module
    filterUsed (Module mid fn ds) = Module mid fn (map filterExports (go ds))
      where
      go :: [ModuleElement] -> [ModuleElement]
      go [] = []
      go (d : rest)
        | not (isDeclUsed d) = skipDecl d : go rest
        | otherwise = d : go rest

      skipDecl :: ModuleElement -> ModuleElement
      skipDecl (Import item _ _) = Skip item
      skipDecl (Member stmt _ _ _ _) = Skip $ JSModuleStatementListItem stmt
      skipDecl (ExportsList _) = Skip . JSModuleStatementListItem $ JSEmptyStatement JSNoAnnot
      skipDecl (Other stmt) = Skip $ JSModuleStatementListItem stmt
      skipDecl (Skip item) = Skip item

      -- | Filter out the exports for members which aren't used.
      filterExports :: ModuleElement -> ModuleElement
      filterExports (ExportsList exps) = ExportsList (filter (\(_, nm, _, _) -> isKeyUsed (mid, nm, Public)) exps)
      filterExports me = me

      isDeclUsed :: ModuleElement -> Bool
      isDeclUsed (Member _ visibility nm _ _) = isKeyUsed (mid, nm, visibility)
      isDeclUsed (Import _ _ (Right midRef)) = midRef `S.member` modulesReferenced
      isDeclUsed _ = True

      isKeyUsed :: Key -> Bool
      isKeyUsed k
        | Just me <- vertexFor k = me `S.member` reachableSet
        | otherwise = False

      modulesReferenced :: S.Set ModuleIdentifier
      modulesReferenced = fold $ M.lookup mid moduleReferenceMap

-- | Topologically sort the module dependency graph, so that when we generate code, modules can be
-- defined in the right order.
sortModules :: [Module] -> [Module]
sortModules modules = map (\v -> case nodeFor v of (n, _, _) -> n) (reverse (topSort graph))
  where
  (graph, nodeFor, _) = graphFromEdges $ do
    m@(Module mid _ els) <- modules
    return (m, mid, mapMaybe getKey els)

  getKey :: ModuleElement -> Maybe ModuleIdentifier
  getKey (Import _ _ (Right mi)) = Just mi
  getKey _ = Nothing

-- | A module is empty if it contains no exported members (in other words,
-- if the only things left after dead code elimination are module imports and
-- "other" foreign code).
--
-- If a module is empty, we don't want to generate code for it.
isModuleEmpty :: Module -> Bool
isModuleEmpty (Module _ _ els) = all isElementEmpty els
  where
  isElementEmpty :: ModuleElement -> Bool
  isElementEmpty (ExportsList exps) = null exps
  isElementEmpty Import{} = True
  isElementEmpty (Other _) = True
  isElementEmpty (Skip _) = True
  isElementEmpty _ = False

-- | Generate code for a set of modules, including a call to main().
--
-- Modules get defined on the global PS object, as follows:
--
--     var PS = { };
--     (function(exports) {
--       ...
--     })(PS["Module.Name"] = PS["Module.Name"] || {});
--
-- In particular, a module and its foreign imports share the same namespace inside PS.
-- This saves us from having to generate unique names for a module and its foreign imports,
-- and is safe since a module shares a namespace with its foreign imports in PureScript as well
-- (so there is no way to have overlaps in code generated by the compiler).
codeGen :: Maybe String -- ^ main module
        -> String -- ^ namespace
        -> [Module] -- ^ input modules
        -> Maybe String -- ^ output filename
        -> (Maybe SourceMapping, String)
codeGen optionsMainModule optionsNamespace ms outFileOpt = (fmap sourceMapping outFileOpt, rendered)
  where
  rendered = renderToString (JSAstProgram (prelude : concatMap fst modulesJS ++ maybe [] runMain optionsMainModule) JSNoAnnot)

  sourceMapping :: String -> SourceMapping
  sourceMapping outFile = SourceMapping {
      smFile = outFile,
      smSourceRoot = Nothing,
      smMappings = concat $
        zipWith3 (\file (pos :: Int) positions ->
          map (\(porig, pgen) -> Mapping {
                mapOriginal = Just (Pos (fromIntegral $ porig + 1) 0)
              , mapSourceFile = pathToFile <$> file
              , mapGenerated = (Pos (fromIntegral $ pos + pgen) 0)
              , mapName = Nothing
              })
            (offsets (0,0) (Right 1 : positions)))
          moduleFns
          (scanl (+) (3 + moduleLength [JSModuleStatementListItem prelude]) (map (3+) moduleLengths)) -- 3 lines between each module & at top
          (map snd modulesJS)
    }
    where
      pathToFile = makeRelative (takeDirectory outFile)

      offsets (m, n) (Left d:rest) = offsets (m+d, n) rest
      offsets (m, n) (Right d:rest) = map ((m+) &&& (n+)) [0 .. d - 1] ++ offsets (m+d, n+d) rest
      offsets _ _ = []

  moduleLength :: [JSModuleItem] -> Int
  moduleLength = everything (+) (mkQ 0 countw)
    where
      countw :: CommentAnnotation -> Int
      countw (WhiteSpace _ s) = length (filter (== '\n') s)
      countw _ = 0

  moduleLengths :: [Int]
  moduleLengths = map (sum . map (either (const 0) id) . snd) modulesJS
  moduleFns = map (\(Module _ fn _) -> fn) ms

  modulesJS = map moduleToJS ms

  moduleToJS :: Module -> ([JSStatement], [Either Int Int])
  moduleToJS (Module mid _ ds) = (wrap mid (indent (concat jsDecls)), lengths)
    where
    (jsDecls, lengths) = unzip $ map declToJS ds

    withLength :: [JSStatement] -> ([JSStatement], Either Int Int)
    withLength n = (n, Right . moduleLength $ JSModuleStatementListItem <$> n)

    declToJS :: ModuleElement -> ([JSStatement], Either Int Int)
    declToJS (Member n _ _ _ _) = withLength [n]
    declToJS (Other n) = withLength [n]
    declToJS (Skip n) = ([], Left $ moduleLength [n])
    declToJS (Import _ nm req) = withLength
      [
        JSVariable lfsp
          (cList [
            JSVarInitExpression (JSIdentifier sp nm)
              (JSVarInit sp $ either require (innerModuleReference sp . moduleName) req )
          ]) (JSSemi JSNoAnnot)
      ]
    declToJS (ExportsList exps) = withLength $ map toCommonJSExport exps

      where

      toCommonJSExport :: (ExportType, String, JSExpression, [Key]) -> JSStatement
      toCommonJSExport (_, nm, val, _) =
        JSAssignStatement
          (JSMemberSquare (JSIdentifier lfsp "exports") JSNoAnnot
            (stringLiteral nm) JSNoAnnot)
          (JSAssign sp)
          val
          (JSSemi JSNoAnnot)

  -- comma lists are reverse-consed
  cList :: [a] -> JSCommaList a
  cList [] = JSLNil
  cList [x] = JSLOne x
  cList l = go $ reverse l
    where
      go [x] = JSLOne x
      go (h:t)= JSLCons (go t) JSNoAnnot h
      go [] = error "Invalid case in comma-list"

  indent :: [JSStatement] -> [JSStatement]
  indent = everywhere (mkT squash)
    where
    squash JSNoAnnot = JSAnnot (TokenPn 0 0 2) []
    squash (JSAnnot pos ann) = JSAnnot (keepCol pos) (map splat ann)
    squash JSAnnotSpace = JSAnnot (TokenPn 0 0 2) []

    splat (CommentA pos s) = CommentA (keepCol pos) s
    splat (WhiteSpace pos w) = WhiteSpace (keepCol pos) w
    splat ann = ann

    keepCol (TokenPn _ _ c) = TokenPn 0 0 (if c >= 0 then c + 2 else 2)

  prelude :: JSStatement
  prelude = JSVariable (JSAnnot tokenPosnEmpty [ CommentA tokenPosnEmpty $ "// Generated by purs bundle " ++ showVersion Paths.version
                                               , WhiteSpace tokenPosnEmpty "\n" ])
              (cList [
                JSVarInitExpression (JSIdentifier sp optionsNamespace)
                  (JSVarInit sp (emptyObj sp))
              ]) (JSSemi JSNoAnnot)

  require :: String -> JSExpression
  require mn =
    JSMemberExpression (JSIdentifier JSNoAnnot "require") JSNoAnnot
      (cList [ stringLiteral mn ]) JSNoAnnot

  moduleReference :: JSAnnot -> String -> JSExpression
  moduleReference a mn =
    JSMemberSquare (JSIdentifier a optionsNamespace) JSNoAnnot
      (stringLiteral mn) JSNoAnnot

  innerModuleReference :: JSAnnot -> String -> JSExpression
  innerModuleReference a mn =
    JSMemberSquare (JSIdentifier a "$PS") JSNoAnnot
      (stringLiteral mn) JSNoAnnot

  emptyObj :: JSAnnot -> JSExpression
  emptyObj a = JSObjectLiteral a (JSCTLNone JSLNil) JSNoAnnot

  initializeObject :: JSAnnot -> (JSAnnot -> String -> JSExpression) -> String -> JSExpression
  initializeObject a makeReference mn =
    JSAssignExpression (makeReference a mn) (JSAssign sp)
    $ JSExpressionBinary (makeReference sp mn) (JSBinOpOr sp)
    $ emptyObj sp

  -- Like `somewhere`, but stops after the first successful transformation
  firstwhere :: MonadPlus m => GenericM m -> GenericM m
  firstwhere f x = f x `mplus` gmapMo (firstwhere f) x

  prependWhitespace :: String -> [JSStatement] -> [JSStatement]
  prependWhitespace val = fromMaybe <*> firstwhere (mkMp $ Just . reannotate)
    where
    reannotate (JSAnnot rpos annots) = JSAnnot rpos (ws : annots)
    reannotate _ = JSAnnot tokenPosnEmpty [ws]

    ws = WhiteSpace tokenPosnEmpty val

  iife :: [JSStatement] -> String -> JSExpression -> JSStatement
  iife body param arg =
    JSMethodCall (JSExpressionParen lf (JSFunctionExpression JSNoAnnot JSIdentNone JSNoAnnot (JSLOne (JSIdentifier JSNoAnnot param)) JSNoAnnot
                                                             (JSBlock sp (prependWhitespace "\n  " body) lf))
                                    JSNoAnnot)
                 JSNoAnnot
                 (JSLOne arg)
                 JSNoAnnot
                 (JSSemi JSNoAnnot)

  wrap :: ModuleIdentifier -> [JSStatement] -> [JSStatement]
  wrap (ModuleIdentifier mn mtype) ds =
    case mtype of
      Regular -> [iife (addModuleExports ds) "$PS" (JSIdentifier JSNoAnnot optionsNamespace)]
      Foreign -> [iife ds "exports" (initializeObject JSNoAnnot moduleReference mn)]
    where
      -- Insert the exports var after a directive prologue, if one is present.
      -- Per ECMA-262 5.1, "A Directive Prologue is the longest sequence of
      -- ExpressionStatement productions [...] where each ExpressionStatement
      -- [...] consists entirely of a StringLiteral [...]."
      -- (http://ecma-international.org/ecma-262/5.1/#sec-14.1)
      addModuleExports :: [JSStatement] -> [JSStatement]
      addModuleExports (x:xs) | isDirective x = x : addModuleExports xs
      addModuleExports xs
        = JSExpressionStatement (initializeObject lfsp innerModuleReference mn) (JSSemi JSNoAnnot)
        : JSVariable lfsp (JSLOne $ JSVarInitExpression (JSIdentifier sp "exports") $ JSVarInit sp (innerModuleReference sp mn)) (JSSemi JSNoAnnot)
        : xs

      isDirective (JSExpressionStatement (JSStringLiteral _ _) _) = True
      isDirective _ = False

  runMain :: String -> [JSStatement]
  runMain mn =
    [JSMethodCall
      (JSMemberDot (moduleReference lf mn) JSNoAnnot
        (JSIdentifier JSNoAnnot "main"))
      JSNoAnnot (cList []) JSNoAnnot (JSSemi JSNoAnnot)]

  lf :: JSAnnot
  lf = JSAnnot tokenPosnEmpty [ WhiteSpace tokenPosnEmpty "\n" ]


  lfsp :: JSAnnot
  lfsp = JSAnnot tokenPosnEmpty [ WhiteSpace tokenPosnEmpty "\n  " ]

-- | The bundling function.
-- This function performs dead code elimination, filters empty modules
-- and generates and prints the final JavaScript bundle.
bundleSM :: (MonadError ErrorMessage m)
       => [(ModuleIdentifier, Maybe FilePath, String)] -- ^ The input modules.  Each module should be javascript rendered from the compiler.
       -> [ModuleIdentifier] -- ^ Entry points.  These module identifiers are used as the roots for dead-code elimination
       -> Maybe String -- ^ An optional main module.
       -> String -- ^ The namespace (e.g. PS).
       -> Maybe FilePath -- ^ The output file name (if there is one - in which case generate source map)
       -> Maybe ([Module] -> m ()) -- ^ Optionally report the parsed modules prior to DCE -- used by "bundle --debug"
       -> m (Maybe SourceMapping, String)
bundleSM inputStrs entryPoints mainModule namespace outFilename reportRawModules = do
  let mid (a,_,_) = a
  forM_ mainModule $ \mname ->
    when (mname `notElem` map (moduleName . mid) inputStrs) (throwError (MissingMainModule mname))
  forM_ entryPoints $ \mIdent ->
    when (mIdent `notElem` map mid inputStrs) (throwError (MissingEntryPoint (moduleName mIdent)))
  input <- forM inputStrs $ \(ident, filename, js) -> do
                ast <- either (throwError . ErrorInModule ident . UnableToParseModule) pure $ parseModule js (moduleName ident)
                return (ident, filename, ast)

  let mids = S.fromList (map (moduleName . mid) input)

  modules <- traverse (fmap withDeps . (\(a,fn,c) -> toModule mids a fn c)) input

  forM_ reportRawModules ($ modules)

  let compiled = compile modules entryPoints
      sorted   = sortModules (filter (not . isModuleEmpty) compiled)

  return (codeGen mainModule namespace sorted outFilename)

-- | The bundling function.
-- This function performs dead code elimination, filters empty modules
-- and generates and prints the final JavaScript bundle.
bundle :: (MonadError ErrorMessage m)
       => [(ModuleIdentifier, String)] -- ^ The input modules.  Each module should be javascript rendered from the compiler.
       -> [ModuleIdentifier] -- ^ Entry points.  These module identifiers are used as the roots for dead-code elimination
       -> Maybe String -- ^ An optional main module.
       -> String -- ^ The namespace (e.g. PS).
       -> m String
bundle inputStrs entryPoints mainModule namespace = snd <$> bundleSM (map (\(a,b) -> (a,Nothing,b)) inputStrs) entryPoints mainModule namespace Nothing Nothing
