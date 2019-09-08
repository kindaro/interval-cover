#! /bin/sh
stack ghc --package deepseq --package data-ordlist --package matrix --package containers --package QuickCheck --package tasty --package tasty-quickcheck --package tasty-hunit --package set-monad -- -Wall -O2 X.hs
