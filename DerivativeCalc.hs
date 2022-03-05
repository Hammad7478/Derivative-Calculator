{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Assign_4 where

import Test.QuickCheck


-- Name: Hammad Ur Rehman
-- Date: December 06, 2021
{- --------------------------------------------------------------------
 - Datatype: MathExpr
 - --------------------------------------------------------------------
 - Description: An Abstract Syntax Tree (AST) for encoding mathematical
 -              expressions
 - Example: The expression
 -                (abs (2*X + 1)) ^ 3
 -          can be encoded as
 -                Power 3 (Func1 Abs
 -                              (Func2 Add (Func2 Mult (Coef 2) X)
 -                                         (Coef 1)))
 - --------------------------------------------------------------------
 -}
data MathExpr a =
    X
  | Coef a
  | Func1 UnaryOp (MathExpr a)
  | Func2 BinOp (MathExpr a) (MathExpr a)
  deriving (Eq,Show,Read)

data BinOp = Add | Mult
  deriving (Show,Eq,Read)

data UnaryOp = Cos | Sin | Abs | Power Int
  deriving (Show,Eq,Read)

{- -----------------------------------------------------------------
 - eval
 - -----------------------------------------------------------------
 - Description:
 - The eval function takes an expression e of type (MathExpr a) and evaluating the function,
 - subbing in v for X. Using cases, the eval function identifies the cases of e and matches them accordingly.
 - Initially, X is set to v. If the case is of Func1, the eval function uses cases again to identify the different operators.
 - Once the operators are identified, they are applied to the expression using recursion. If the case is of Func2,
 - the eval function uses cases to identify if its either Multiplication or Addition. Once identified, s1 and s2 are
 - evaluated and added/multiplied using recursion.
 -} 
eval :: (Floating a, Eq a) => MathExpr a -> a -> a
eval e v = case e of
  X -> v
  Coef c -> c
  Func1 op e1 -> case op of
    Cos -> cos s1
    Sin -> sin s1
    Abs -> abs s1
    Power n -> s1^^ n
    where s1 = eval e1 v
  Func2 op e1 e2 -> case op of
    Add -> s1 + s2
    Mult -> s1* s2
    where s1 = eval e1 v
          s2 = eval e2 v


{- -----------------------------------------------------------------
 - instance Num a => Num (MathExpr a)
 - -----------------------------------------------------------------
 - Description:
 - instance Num a => Num (MathExpr a) has implementations for different operations on the (MathExpr a) data type.
 - x + y performs addition on the (MathExpr a) data type. 
 - x * y performs multiplication on the (MathExpr a) data type.
 - negate x switches the sign of a (MathExpr a) data type.
 - abs x gets the absolute value of a (MathExpr a) data type.
 - fromInteger i makes the value i into a (MathExpr a) data type.
 -}
instance Num a => Num (MathExpr a) where
  x + y         = Func2 Add x y
  x * y         = Func2 Mult x y
  negate x      = Func2  Mult x (-1)
  abs x         = Func1 Abs x
  fromInteger i = Coef (fromInteger i)
  signum _      = error "signum is left un-implemented"

{- -----------------------------------------------------------------
 - instance Fractional a => Fractional (MathExpr a)
 - -----------------------------------------------------------------
 - Description:
 - instance Fractional a => Fractional (MathExpr a) has implementations for two different operations on the (MathExpr a) data type.
 - recip - Finds the reciprocol by adding a power of (-1) to it.
 -}
instance Fractional a => Fractional (MathExpr a) where
  recip e        = Func1 (Power (-1)) e
  fromRational e = Coef (fromRational e)

{- -----------------------------------------------------------------
 - instance Floating a => Floating (MathExpr a)
 - -----------------------------------------------------------------
 - Description:
 - instance Floating a => Floating (MathExpr a) has implementations of pi, sin and cos on the (MathExpr a) data type.
 - pi is implemented using Coef
 - sin is implemented using Func1
 - cos is implemented using Func1
 -}
instance Floating a => Floating (MathExpr a) where
  pi      = Coef pi
  sin     = Func1 Sin
  cos     = Func1 Cos
  log     = error "log is left un-implemented"
  asin _  = error "asin is left un-implemented"
  acos _  = error "acos is left un-implemented"
  atan _  = error "atan is left un-implemented"
  sinh _  = error "sinh is left un-implemented"
  cosh _  = error "cosh is left un-implemented"
  tanh _  = error "tanh is left un-implemented"
  asinh _ = error "asinh is left un-implemented"
  acosh _ = error "acosh is left un-implemented"
  atanh _ = error "atanh is left un-implemented"
  exp _   = error "exp is left un-implemented"
  sqrt _  = error "sqrt is left un-implemented"

{- -----------------------------------------------------------------
 - diff
 - -----------------------------------------------------------------
 - Description:
 - The diff function differentiates an expression of type (MathExpr a) using the provided differential rules.
 - Using cases, initially, X is assigned as 1 (Differentiating just x would equal to 1). Then the function identifies
 - if the (MathExpr a) is a UnaryOp or a BinOp. In the case of Func1 (UnaryOp), the function uses cases to identify the
 - operation. Each respective operation is implemented using the given differential rules:
 - Cos becomes -sin(e1) * diff e1. (-sin is calculated by multiplying sin with a Coef of (-1))
 - Sin becomes cos(e1) * diff e1.
 - Abs becomes e1/abs(e1) * diff e1. (In this case, the recip function is used)
 - Power becomes n * e1^^(n-1) * diff e1
 - The last case is if (MathExpr a) is Func2 (BinQp). Cases are used again to identify if its multiplication or addition.
 - Add simply adds the two functions after they have been differentiated individually
 - Mult uses the product rule; first e2 is differentiated then multiplied with e1 then, e1 is differentiated and multiplied
 - with e2. Lastly, the two products are then added to give the final answer.
 -}
diff :: (Floating a, Eq a) => MathExpr a -> MathExpr a
diff e = case e of
  X -> Coef 1
  Coef _ -> Coef 0
  Func1 op e1 -> case op of
    Cos -> Coef (-1) * Func1 Sin e1 * differ
    Sin -> Func1 Cos e1 * differ
    Abs -> Func1 Abs (recip e1) * differ
    Power n ->  fromIntegral n * e1^^(n-1) * differ
    where differ = diff e1
  Func2 op e1 e2 -> case op of
    Add -> Func2 Add differ differ2
    Mult -> Func2 Add (Func2 Mult differ e2) (Func2 Mult e1 differ2)
    where differ = diff e1
          differ2 = diff e2
{- -----------------------------------------------------------------
 - pretty
 - -----------------------------------------------------------------
 - The pretty function uses cases to show a String representation of an expression type of (MathExpr a)
 - In case of X -> "X" is outputted.
 - In case of Coef c -> "(c)" is outputted.
 - In the case of Func1, pretty uses cases again to identify the type of operator.
    - For Cos, "cos(u0)" is outputted. Example: pretty (Func1 Cos 5) -> "cos(5)"
    - For Sin, "sin(u0)" is outputted. Example: pretty (Func1 Sin 99) -> "sin(99)"
    - For Abs, "abs(u0)" is outputted. Example: pretty (Func1 Abs 10) -> "abs(10)"
    - For Power, "(u0)^^n" is outputted. Example: pretty (Func1 (Power 5) 10) -> "(10)^^5"
  In the case of Func2, pretty uses cases again to identify whether it is Add or Mult:
    - For Add, "(5) + (10)" is outputted. Example: pretty (Func2 Add 5 10) -> "(5) + (10)"
    - For Mult, "(5) * (10)" is outputted. Example: pretty (Func2 Mult 5 10) -> "(5) * (10)".

 -}
pretty :: (Show a) => MathExpr a -> String
pretty e = case e of
  X -> "X"
  Coef c -> show c
  Func1 op e1 -> case op of
    Cos -> "cos(" ++ func_Call ++ ")"
    Sin -> "sin(" ++ func_Call ++ ")"
    Abs -> "abs(" ++ func_Call ++ ")"
    Power n -> "(" ++ func_Call ++ ")^^" ++ show n
    where func_Call = pretty e1
  Func2 op e1 e2 -> case op of
    Add -> "(" ++ func_Call ++ ") + (" ++ func_Call2 ++ ")"
    Mult -> "(" ++ func_Call ++ ") * (" ++ func_Call2 ++ ")"
    where func_Call = pretty e1
          func_Call2 = pretty e2

{- -----------------------------------------------------------------
 - Quick Check Test Cases
 - -----------------------------------------------------------------
 - eval
 - -----------------------------------------------------------------
 -}
infix 4 =~
(=~) :: (Floating a,Ord a) => a -> a -> Bool
x =~ y = abs (x - y) <= 1e-4

{- 
 - Function: eval
 - Property: eval (Func2 Mult (Coef x) X) y is correct for all x,y
 - Actual Test Result: Pass
 -}
evalChecker :: (Float,Float) -> Bool
evalChecker (x,y) = (x * y) =~ eval (Func2 Mult (Coef x) X) y

runEvalChecker :: IO ()
runEvalChecker = quickCheck  evalChecker

{- - -----------------------------------------------------------------
 - diff
 - -----------------------------------------------------------------
 - Function: diff
 - Property: eval (diff Func2 Add (Func1 (Power 4) X) (Func1 (Power 2) X)) y
 - Actual Test Result: Pass
 -}

diffChecker :: (Float, Float) -> Bool
diffChecker (x,y) = eval e1 y =~ eval (diff e2) y
                    where e1 = Func2 Add (Func2 Mult (Func2 Mult (Coef 4.0) (Func2 Mult (Func2 Mult X X) X)) (Coef 1.0)) (Func2 Mult (Func2 Mult (Coef 2.0) X) (Coef 1.0))
                          e2 = Func2 Add (Func1 (Power 4) X) (Func1 (Power 2) X)

runDiffChecker :: IO ()
runDiffChecker =  quickCheck diffChecker


{- ------------------------------------------------------------------------
 - Testing Plan
 - ------------------------------------------------------------------------
 - eval
 - ------------------------------------------------------------------------
 - Description:

 -Function: eval
 -Test Case Number: 1
 -Input: eval (Func2 Mult (Coef 5) 10) 5 
 -Expected Output: 50.0
 -Actual Output: 50.0


 -Test Case Number: 2
 -Input: eval (Func2 Mult (Coef 15) (Coef 85)) 5 
 -Expected Output: 1275.0
 -Actual Output: 1275.0

 -Test Case Number: 3
 -Input: eval (Func1 Cos pi) 5
 -Expected Output: -1.0
 -Actual Output: -1.0

 -Test Case Number: 4
 -Input: eval (5) 10
 -Expected Output: 5.0
 -Actual Output: 5.0

 - ------------------------------------------------------------------------
 - diff
 - ------------------------------------------------------------------------
 - Description:

 -Function: eval
 -Test Case Number: 1
 -Input: diff (Func2 Mult (Coef 5) (X^2))
 -Expected Output: Func2 Add (Func2 Mult (Coef 0.0) (Func2 Mult X X)) (Func2 Mult (Coef 5.0) (Func2 Add (Func2 Mult (Coef 1.0) X) (Func2 Mult X (Coef 1.0))))
 -Actual Output: Func2 Add (Func2 Mult (Coef 0.0) (Func2 Mult X X)) (Func2 Mult (Coef 5.0) (Func2 Add (Func2 Mult (Coef 1.0) X) (Func2 Mult X (Coef 1.0))))

 -Test Case Number: 2
 -Input: diff (Func2 Add (Func2 Add (Func1 (Power 3) X) (Func1 (Power 2) X)) 5)
 -Expected Output: Func2 Add (Func2 Add (Func2 Mult (Func2 Mult (Coef 3.0) (Func2 Mult X X)) (Coef 1.0)) (Func2 Mult (Func2 Mult (Coef 2.0) X) (Coef 1.0))) (Coef 0.0)
 -Actual Output: Func2 Add (Func2 Add (Func2 Mult (Func2 Mult (Coef 3.0) (Func2 Mult X X)) (Coef 1.0)) (Func2 Mult (Func2 Mult (Coef 2.0) X) (Coef 1.0))) (Coef 0.0)

 -Test Case Number: 3
 -Input: diff (Func2 Mult (Func2 Add (Func1 (Power 3) X) (Func1 (Power 2) X)) 5)
 -Expected Output: Func2 Add (Func2 Mult (Func2 Add (Func2 Mult (Func2 Mult (Coef 3.0) (Func2 Mult X X)) (Coef 1.0)) (Func2 Mult (Func2 Mult (Coef 2.0) X) (Coef 1.0))) (Coef 5.0)) (Func2 Mult (Func2 Add (Func1 (Power 3) X) (Func1 (Power 2) X)) (Coef 0.0))
 -Actual Output: Func2 Add (Func2 Mult (Func2 Add (Func2 Mult (Func2 Mult (Coef 3.0) (Func2 Mult X X)) (Coef 1.0)) (Func2 Mult (Func2 Mult (Coef 2.0) X) (Coef 1.0))) (Coef 5.0)) (Func2 Mult (Func2 Add (Func1 (Power 3) X) (Func1 (Power 2) X)) (Coef 0.0))


 - ------------------------------------------------------------------------
 - pretty
 - ------------------------------------------------------------------------
 - Description:

 -Function: pretty
 -Test Case Number: 1
 -Input: pretty (Func2 Add X (Func2 Mult (Coef 2) X))
 -Expected Output: "(X) + ((2) * (X))"
 -Actual Output: "(X) + ((2) * (X))"


 -Test Case Number: 2
 -Input: pretty (Func2 Add (Func2 Add (Func1 (Power 3) X) (Func1 (Power 2) X)) 5)
 -Expected Output: "(((X)^^3) + ((X)^^2)) + (5)"
 -Actual Output: "(((X)^^3) + ((X)^^2)) + (5)"

 -Test Case Number: 3
 -Input: pretty (diff (Func2 Mult (Coef 5) (X^2)))
 -Expected Output: "((0.0) * ((X) * (X))) + ((5.0) * (((1.0) * (X)) + ((X) * (1.0))))"
 -Actual Output: "((0.0) * ((X) * (X))) + ((5.0) * (((1.0) * (X)) + ((X) * (1.0))))"

  - ------------------------------------------------------------------------
End of Test Plan
- ------------------------------------------------------------------------
 -}