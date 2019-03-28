module EarleyParser where

import Data.List

-----------------------------------------------------
-- Definitions for a symbols, rules, grammars, trees
-----------------------------------------------------

--Tim's symbol definition
--Also contains "dummy" nonterminal symbol for extending a grammar with a new start symbol
data Symbol a b = N b | T a | D b deriving (Eq, Ord, Show) 

--Checking for nonterminal
nonterm (T _) = False
nonterm _ = True

--Checking for dummy
dummy (D _) = True
dummy _ = False

--Grammar rule
--A rule consists of a nonterminal symbol A followed by a list of symbols [B]
data Rule a b = Rule (Symbol a b) [Symbol a b] deriving Eq

--Define a show function for easier readability of rules
instance (Show a, Show b) => Show (Rule a b) where 
    show (Rule x yz) = show x ++ "-->" ++ show yz

--Get left or right side of a rule
lhs :: Rule a b -> (Symbol a b)
lhs (Rule x ys) = x

rhs :: Rule a b -> [Symbol a b]
rhs (Rule x ys) = ys

--Define a grammar to be a list of rules
type Grammar a b = [Rule a b]

--Get the start symbol of a grammar
--A start symbol is assumed to be the left side of a grammar's first rule
startSymbol :: Grammar a b -> Symbol a b
startSymbol grammar = lhs (head grammar)

--Tree definition, similar to the one from HW 6 but allows for any number of trees under a Nonleaf
data MyTree a b = Leaf a | Nonleaf b [MyTree a b] deriving (Eq, Ord)

--Display a given tree in a more readable format
--A simpler adaptation of the drawTree function from Data.Tree
displayTree :: (Show a, Show b) => MyTree a b -> IO()
displayTree tree = mapM_ putStrLn (showTree 0 tree) where
    showTree i (Leaf x) = [(map (\ _ -> ' ') [1..i]) ++ show x]
    showTree i (Nonleaf x ts) = ((map (\ _ -> ' ') [1..i]) ++ show x) :
        concat (map (showTree (i+5)) ts)

-------------------------------------------------------------------
-- Definitions for Earley parser (see write-up for more specifics)
-------------------------------------------------------------------

--Earley state definition
data State a b = 
    State Int (Symbol a b) [Symbol a b] [Symbol a b] Int String [MyTree a b] deriving (Eq)

--Show function for Earley states, using * for a dot
instance (Show a, Show b) => Show (State a b) where
    show (State origin leftNT leftDot rightDot inPos op trees) =
        "\n" ++ show leftNT ++ "-->" ++ show leftDot ++ "*" ++ show rightDot ++ "\n" ++ 
        "Position in input: " ++ show inPos ++ "\n" ++
        "Operation: " ++ show op ++ " from state set " ++ show origin ++ "\n"

--Get the list of trees from a state
getTrees :: State a b -> [MyTree a b]
getTrees (State i nt symbols symbols' d op trees) = trees

--Get initial state to seed the parser with
initState :: Grammar a b -> [State a b]
initState grammar = 
    let N x = startSymbol grammar in [State 0 (D x) [] [N x] 0 "Initialization" []]

--Scanning operation
scanning :: (Eq a, Eq b) => [a] -> State a b -> [State a b]
scanning string (State i nt lefts [] d op trees) = []
scanning string (State i nt lefts (sym:rest) d op trees) =
    if d >= length string then []
    else let currSym = string !! d 
         in [State i nt (lefts ++ [sym]) rest (d + 1) "Scanning" (trees ++ [Leaf currSym]) 
            | sym == (T currSym)]

--Prediction operation
prediction :: (Eq a, Eq b) => Grammar a b -> State a b -> [State a b]
prediction grammar state =
    let State i nt lefts rights d op trees = state in
    case rights of
        [] -> []
        sym:rest -> [State d newNT [] newRights d "Prediction" [] | 
                    (Rule newNT newRights) <- grammar, sym == newNT]

--Completion operation
completion :: (Eq a, Eq b) => State a b -> [State a b] -> [State a b]
completion (State i nt lefts (N sym:rest) d op trees) chart =
    [State i nt (lefts ++ [N sym]) rest j "Completion" (trees ++ [Nonleaf sym trees'])|
    (State d' symbol gamma [] j op trees') <- chart,
     d == d',
     symbol == N sym ]
completion (State k (N sym) gamma [] j op trees) chart =
    [State i nt (lefts ++ [N sym]) rest j "Completion" (trees' ++ [Nonleaf sym trees])|
    (State i nt lefts (symbol:rest) k' op trees') <- chart,
     k == k',
     symbol == N sym]
completion item chart = []
    
--Calculate the combined result of the three operations
result :: (Eq a,Eq b) => Grammar a b -> [a] -> State a b -> [State a b] -> [State a b]
result grammar string cause chart =
    scanning string cause ++ prediction grammar cause ++ completion cause chart

--Define a chart (since the Earley parser is a chart parser) to hold two lists of states
type Chart a b = ([State a b], [State a b])

--Initialize a chart for the parser
initChart :: (Eq a, Eq b) => Grammar a b -> [a] -> Chart a b
initChart grammar string = ([], initState grammar)

--Fill the chart using the three Earley operations
fillChart :: (Eq a, Eq b) => Grammar a b -> [a] -> Chart a b -> Chart a b
fillChart grammar string chart =
    let (calc, notCalc) = chart in
    case notCalc of 
        [] -> (calc, [])
        cause:rest -> let newCalc = calc ++ [cause] 
                          res = result grammar string cause calc 
                          newRes = res \\ (calc ++ notCalc) 
                          newNotCalc = rest ++ newRes 
                      in fillChart grammar string (newCalc, newNotCalc)

--Check if some state is a goal state
isGoal :: (Eq a, Eq b) => Grammar a b -> [a] -> State a b -> Bool
isGoal grammar string state =
    let State i nt lefts rights d op trees = state 
        ruleFinished  = i == 0 
        startSymRead  = dummy nt 
        allSymLeft    = lefts == [startSymbol grammar] 
        noSymRight    = rights == [] 
        inputFinished = d == length string 
    in and [ruleFinished, startSymRead, allSymLeft, noSymRight, inputFinished]

--Return any goal states of a given chart
goals :: (Eq a, Eq b) => Grammar a b -> [a] -> [State a b] -> [State a b]
goals grammar string chart = 
    let checkGoal = isGoal grammar string in filter checkGoal chart

--Apply this filter predicate to a parse chart to remove any of its unsuccessful nodes
clean :: (Eq a, Eq b) => [State a b] -> [State a b]
clean = filter (\ (State i nt lefts rights d op trees) -> rights == [])
 
 --Display each state in a set of states
displayStates [] = return ()
displayStates (x:xs) = do print x
                          displayStates xs

--Given a grammar and a string, parse the string using Earley's algorithm
--If output = States, display all states that the parser went through to get its result
--If hygiene = Clean, use "clean" filter to remove any nonproductive states from output
--If hygiene = Dirty, don't
--If output = ParseTree, display the resulting parse tree of the result, if there is one
earleyParse :: (Eq a, Show a, Eq b, Show b) => Grammar a b -> [a] -> OutputType -> Hygiene -> IO()
earleyParse grammar string output hygiene = 
    let anyGoals = goals grammar string states
        tree = head (getTrees (head anyGoals))
        startChart = initChart grammar string
        result = fillChart grammar string startChart
        states = fst result
    in 
        if anyGoals /= [] then
            if output == ParseTree then displayTree tree
            else if hygiene == Dirty then displayStates states
            else displayStates (clean states)
        else putStrLn "No valid parse"

--Definition for output flag
data OutputType = ParseTree | States deriving Eq

--Definition for hygiene flag
data Hygiene = Clean | Dirty deriving Eq

-------------------------------------------------------------------
-- Sample grammars (feel free to add more of your own design here)
-------------------------------------------------------------------

--Some sequence of 'a's and 'b's, followed by either an 'a' or a 'b', followed by the reverse of the sequence 
grammar1 = [Rule (N 'S') [T 'a', N 'S', T 'a'],
            Rule (N 'S') [T 'b', N 'S', T 'b'],
            Rule (N 'S') [T 'a'],
            Rule (N 'S') [T 'b'] ]

--Same as above but with an epsilon rule
grammar2 = [Rule (N 'S') [T 'a', N 'S', T 'a'],
            Rule (N 'S') [T 'b', N 'S', T 'b'],
            Rule (N 'S') [T 'a'],
            Rule (N 'S') [T 'b'],
            Rule (N 'S') []]

--Balanced parentheses
grammar3 = [Rule (N 'S') [T '(', N 'S', T ')', N 'S'],
            Rule (N 'S') []]

--Arithmetic expressions for multiplying or adding 1, 2, 3, or 4 only
grammar4 = [Rule (N 'S') [N 'S', T '+', N 'M'],
            Rule (N 'S') [N 'M'],
            Rule (N 'M') [N 'M', T '*', N 'T'],
            Rule (N 'M') [N 'T'],
            Rule (N 'T') [T '1'],
            Rule (N 'T') [T '2'],
            Rule (N 'T') [T '3'],
            Rule (N 'T') [T '4']]

--Non-terminating grammar (will hang the parser if used)
grammar5 = [Rule (N 'S') [],
            Rule (N 'S') [N 'S']]

--Ambiguous grammar
grammar6 = [Rule (N 'A') [N 'A', T '+', N 'A'],
            Rule (N 'A') [N 'A', T '-', N 'A'],
            Rule (N 'A') [N 'A', T '*', N 'A'],
            Rule (N 'A') [T 'a']]
