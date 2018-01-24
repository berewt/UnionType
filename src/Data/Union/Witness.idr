module Data.Union.Witness

%default total
%access public export

interface Witness a where
  witness : a
