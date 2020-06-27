module Language.PureScript.TypeChecker.Newtypes where

import Prelude.Compat

import Control.Monad.Error.Class (MonadError(..))

import Language.PureScript.Errors
import Language.PureScript.Names
import Language.PureScript.Types

checkNewtype
  :: forall m
   . MonadError MultipleErrors m
  => ProperName 'TypeName
  -> [(ProperName 'ConstructorName, [SourceType])]
  -> m ()
checkNewtype _ [(_, [_])] = return ()
checkNewtype name _ = throwError . errorMessage $ InvalidNewtype name
