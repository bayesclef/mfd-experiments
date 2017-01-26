{-
 - Type signatures and functions for composable filters for pandoc.
 -}


import Text.Pandoc.Walk
import Development.Shake.FilePath

import BuildIO

module Filters where


{-

type FileRef = Either FilePath Label

data PandocOpts = PandocOpts {}

data PandocFilter = Filter {
  -- Given a Pandoc document produce a list of files or labels that can
  -- generated from that document.
  generates :: Pandoc -> BuildIO PandocOpts [FileRef],
  -- Given a Pandoc document produce a list of files or labels that are
  -- referenced from within that one.
  requires  :: Pandoc -> BuildIO PandocOpts [FileRef],
  -- Transforms a document while generating or using the files that were
  -- described.
  transform :: Pandoc -> BuildIO PandocOpts Pandoc
}

-}
