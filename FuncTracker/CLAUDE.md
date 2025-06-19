# Compositional Parser Combinators in Lean 4

This guide explains how to write parsers using parser combinators in a compositional (functorial) way, based on studying Lean 4's internal Parsec library and the lean4-parser package.

## Core Concepts

### 1. Parser as a Functor

A parser is fundamentally a function that transforms input into a result:

```lean
-- Lean's internal Parsec
def Parsec (ι : Type) (α : Type) : Type := ι → Parsec.ParseResult α ι

-- lean4-parser's approach with monad transformer
abbrev ParserT (ε σ τ : Type) (m : Type → Type) (α : Type) := 
  StateT σ (ExceptT ε m) α
```

The key insight: **parsers are functors** that can be composed using categorical operations:
- `map`: Transform the result of a parser
- `bind`: Sequence parsers where the second depends on the first's result
- `<|>`: Alternative/choice between parsers

### 2. Building Parsers Functorially

Start with atomic parsers and compose them into larger structures:

```lean
-- Atomic parsers
def anyChar : Parser Char      -- consume any character
def char (c : Char) : Parser Char   -- consume specific character
def satisfy (p : Char → Bool) : Parser Char  -- consume if predicate holds

-- Compose using functor operations
def digit : Parser Char := satisfy (·.isDigit)
def letter : Parser Char := satisfy (·.isAlpha)

-- Applicative composition
def twoDigits : Parser (Char × Char) := do
  let d1 ← digit
  let d2 ← digit
  return (d1, d2)

-- Alternative composition  
def alphaNum : Parser Char := letter <|> digit
```

### 3. Parser Combinator Patterns

#### Repetition Combinators
```lean
-- Zero or more (Kleene star)
partial def many (p : Parser α) : Parser (List α) :=
  (do 
    let x ← p
    let xs ← many p
    return x :: xs) <|> pure []

-- One or more (Kleene plus)
def many1 (p : Parser α) : Parser (List α) := do
  let x ← p
  let xs ← many p
  return x :: xs

-- Exactly n times
def replicateM (n : Nat) (p : Parser α) : Parser (List α) :=
  match n with
  | 0 => pure []
  | n+1 => do
    let x ← p
    let xs ← replicateM n p
    return x :: xs
```

#### Separation Combinators
```lean
-- Parse p separated by sep
def sepBy (sep : Parser β) (p : Parser α) : Parser (List α) :=
  (do
    let x ← p
    let xs ← many (sep *> p)
    return x :: xs) <|> pure []

-- Parse p separated by sep, at least one
def sepBy1 (sep : Parser β) (p : Parser α) : Parser (List α) := do
  let x ← p
  let xs ← many (sep *> p)
  return x :: xs
```

#### Bracketing Combinators
```lean
-- Parse p between open and close
def between (open : Parser β) (close : Parser γ) (p : Parser α) : Parser α := do
  let _ ← open
  let x ← p
  let _ ← close
  return x
```

### 4. Building Complex Parsers Compositionally

Example: JSON parser built from simple components:

```lean
mutual
  -- Number parser composed from digit parsers
  def number : Parser JsonNumber := do
    let sign ← optional (char '-')
    let whole ← digits
    let frac ← optional (char '.' *> digits)
    let exp ← optional (char 'e' <|> char 'E' *> signedDigits)
    return JsonNumber.mk sign whole frac exp

  -- String parser with escape handling
  def string : Parser String := do
    let _ ← char '"'
    let chars ← many (escaped <|> satisfy (· ≠ '"'))
    let _ ← char '"'
    return String.mk chars

  -- Object parser using sepBy
  def object : Parser JsonObject := 
    between (char '{') (char '}') $
      sepBy (char ',') pair
  where
    pair := do
      let key ← ws *> string <* ws
      let _ ← char ':'
      let val ← ws *> value <* ws
      return (key, val)

  -- Recursive value parser using alternatives
  def value : Parser JsonValue :=
    (JsonValue.null <$ string "null") <|>
    (JsonValue.bool true <$ string "true") <|>
    (JsonValue.bool false <$ string "false") <|>
    (JsonValue.number <$> number) <|>
    (JsonValue.string <$> string) <|>
    (JsonValue.array <$> array) <|>
    (JsonValue.object <$> object)
end
```

### 5. Error Handling and Backtracking

Proper error handling is crucial for compositional parsers:

```lean
-- Try a parser, backtrack on failure
def attempt (p : Parser α) : Parser α := fun input =>
  match p input with
  | .error _ _ => .error input "backtracked"
  | success => success

-- Lookahead without consuming input
def lookAhead (p : Parser α) : Parser α := do
  let saved ← getInput
  let result ← p
  setInput saved
  return result

-- Custom error messages
def <?> (p : Parser α) (msg : String) : Parser α := fun input =>
  match p input with
  | .error pos _ => .error pos msg
  | success => success
```

### 6. Performance Considerations

When building parsers functorially:

1. **Left-factor common prefixes**: Instead of `(string "true") <|> (string "tricky")`, use:
   ```lean
   do
     let _ ← string "tr"
     (string "ue" *> pure Value.True) <|> (string "icky" *> pure Value.Tricky)
   ```

2. **Avoid unnecessary backtracking**: Use `attempt` only when needed
3. **Build efficient primitives**: Character-level operations should be optimized

### 7. Best Practices for Compositional Design

1. **Start with a type-driven approach**: Design your AST first, then build parsers for each type
2. **Create a vocabulary of combinators**: Build domain-specific combinators from primitives
3. **Test incrementally**: Test small parsers before composing them
4. **Use type classes for flexibility**:
   ```lean
   class Stream (σ : Type) (τ : outParam Type) where
     next? : σ → Option (τ × σ)
   ```

### 8. Example: Building a 2D Table Parser

Here's how to approach parsing 2D tables compositionally:

```lean
-- Define basic tokens
inductive TableToken
  | border : Char → TableToken  -- ═, ─, │, ╔, ╗, ╚, ╝
  | cell : String → TableToken
  | newline : TableToken

-- Token-level parser
def tableTokenizer : Parser (List TableToken) := many do
  (TableToken.border <$> oneOf ['═', '─', '│', '╔', '╗', '╚', '╝']) <|>
  (TableToken.newline <$ char '\n') <|>
  (TableToken.cell <$> takeWhile (fun c => c ∉ ['│', '\n']))

-- Structure parser built on tokens
def parseRow (tokens : List TableToken) : Parser (List String) := do
  -- Parse │ cell │ cell │ ... │
  let _ ← expectBorder '│'
  let cells ← sepBy (expectBorder '│') parseCell
  let _ ← expectBorder '│'
  return cells

-- Complete table parser
def parseTable : Parser Table := do
  let _ ← parseTopBorder    -- ╔═══╗
  let rows ← many parseRow  -- │...│
  let _ ← parseBottomBorder -- ╚═══╝
  return Table.mk rows
```

## Key Takeaways

1. **Think functorially**: Parsers are functions that can be mapped, sequenced, and composed
2. **Build incrementally**: Start with atomic parsers and compose them
3. **Leverage the type system**: Use types to guide parser construction
4. **Abstract common patterns**: Create reusable combinators
5. **Test compositionally**: Test small parts before combining them

The power of parser combinators lies in their compositionality - complex parsers are just combinations of simpler ones, following the fundamental principles of functional programming.