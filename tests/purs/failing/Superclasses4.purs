-- @shouldFailWith CycleInTypeClassDeclaration
module Main where

class Cl a

class (Cl a) <= Cl a
