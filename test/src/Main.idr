module Main
import Control.App
import Control.App.Spec
import SeqSpec
import DepMapSpec

main : IO ()
main = do run (new emptyState (do
  SeqSpec.spec
  DepMapSpec.spec

  specFinalReport))
