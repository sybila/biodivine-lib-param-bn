# BooleanNet Format Specification

## Overview

BooleanNet is a text-based format for representing Boolean network models used in biological regulatory network simulation. This specification describes the syntax and semantics of the format based on the BooleanNet Python implementation (version 1.2.7).

The format supports multiple update modes:
- **synchronous** (sync): Updates performed in listed order, states change only at end of update round
- **asynchronous** (async): Updates performed in random order, states immediately reflect changes (stochastic)
- **ranked asynchronous** (rank): Updates performed in rank order, within same rank updates occur asynchronously
- **time synchronous** (time): Updates performed at time intervals, each rule has associated time delay
- **piecewise differential** (plde): Hybrid model with continuous variables governed by piecewise linear differential equations

## File Structure

A BooleanNet file consists of two main sections:

1. **Initialization section**: Defines initial values for nodes
2. **Update rules section**: Defines how node values change during simulation

## Lexical Elements

### Comments

Lines beginning with `#` are treated as comments and ignored by the parser.

```
# This is a comment
```

Empty lines and lines containing only whitespace are also ignored.

### Whitespace

Whitespace (spaces and tabs) is ignored except:
- To separate tokens
- Inside comments

Newlines are significant and terminate statements.

### Identifiers (Node Names)

**Syntax:**
```
ID := [a-zA-Z_+-][a-zA-Z0-9_+-]*
```

**Rules:**
- Node names are case-sensitive
- Must start with a letter, underscore, plus sign, or minus sign
- Can contain letters, digits, underscores, plus signs, and minus signs
- Node names must be unique in a case-insensitive manner (i.e., `Node` and `node` cannot both exist)

**Examples:**
- Valid: `A`, `Node1`, `Ca2+c`, `H+ATPase`, `IL-2`, `_temp`, `NODE_1`
- Invalid: `2A` (starts with digit), `Node` and `node` (case conflict)

### Reserved Words

The following words are reserved and cannot be used as node names:
- `True`
- `False` 
- `Random`
- `and`
- `or`
- `not`

### Operators

**Assignment Operators:**
- `=` : Initial value assignment
- `*=` : Update rule assignment (the `*` indicates the "next" value of a node)

**Logical Operators:**
- `not` : Logical negation (highest precedence)
- `and` : Logical conjunction
- `or` : Logical disjunction (lowest precedence)

**Precedence** (highest to lowest):
1. `not` (right-associative)
2. `and` (left-associative)
3. `or` (left-associative)

**Other Tokens:**
- `(` `)` : Parentheses for grouping
- `,` : Comma (used in tuples)
- `:` : Colon (follows rank labels)

### Literals

**Boolean Literals:**
- `True` : Boolean true value
- `False` : Boolean false value
- `Random` : Randomly chosen true or false value (chosen at initialization time)

**Numeric Literals:**
```
NUMBER := [+-]?\d+\.?\d*
```

Numbers are floating-point values and used only in tuple expressions (PLDE mode).

**Tuple Literals:**
```
TUPLE := '(' NUMBER ',' NUMBER ',' NUMBER ')'
```

Tuples represent `(concentration, decay, threshold)` triplets used in PLDE (piecewise linear differential equation) mode.

Example: `(1.0, 1.0, 0.5)`

The boolean interpretation of a tuple is: `concentration > threshold / decay`

## Grammar

### Initialization Statements

**Syntax:**
```
initialization := ID '=' expression
                | ID '=' ID '=' expression
                | ID '=' ID '=' ID '=' expression
                | ...
```

**Semantics:**
- Assigns an initial value to one or more nodes
- Multiple nodes can be assigned the same value using chained assignment (right-to-left evaluation)
- Each node should be initialized exactly once
- Uninitialized nodes must be handled by the implementation (typically results in an error)

**Examples:**
```
A = True
B = False
C = Random
D = E = F = True
A = (1.0, 1.0, 0.5)    # PLDE mode only
```

### Update Rule Statements

**Syntax (without rank):**
```
update_rule := ID '*=' expression
```

**Syntax (with rank):**
```
ranked_update_rule := LABEL ':' ID '*=' expression
LABEL := \d+ ':'
```

**Semantics:**
- Defines how a node's value is computed in the next state
- The `*` in `*=` denotes the "next" value of the node
- Rank labels (integers) control execution order in ranked modes
  - In PLDE, SYNC, and ASYNC modes, all ranks are treated as 1 (labels ignored)
  - In RANK and TIME modes, rules are executed in ascending rank order
  - Within the same rank, execution order depends on the mode
- Each node should have exactly one update rule

**Examples:**
```
A* = B and C
1: B* = not A
10: C* = A or B
D* = True
```

### Expressions

**Syntax:**
```
expression := ID
            | 'True'
            | 'False'
            | 'Random'
            | '(' expression ')'
            | 'not' expression
            | expression 'and' expression
            | expression 'or' expression
            | '(' NUMBER ',' NUMBER ',' NUMBER ')'
```

**Semantics:**

1. **Node Reference** (`ID`):
   - In synchronous mode: evaluates to the node's value in the previous state
   - In asynchronous mode: evaluates to the node's current (potentially updated) value

2. **Boolean Literals**:
   - `True`: evaluates to true
   - `False`: evaluates to false
   - `Random`: evaluates to a random boolean (chosen at initialization)

3. **Tuple Literals** (PLDE mode only):
   - `(conc, decay, threshold)`: represents continuous variables
   - Boolean interpretation: `conc > threshold / decay`

4. **Logical NOT**:
   - `not expr`: logical negation of expression

5. **Logical AND**:
   - `expr1 and expr2`: true if both expressions are true

6. **Logical OR**:
   - `expr1 or expr2`: true if at least one expression is true

7. **Parentheses**:
   - `(expr)`: groups expressions to override default precedence

## Complete Grammar (BNF-like notation)

```
file              := statement*

statement         := initialization
                   | update_rule
                   | ranked_update_rule
                   | comment
                   | empty_line

initialization    := ID ('=' ID)* '=' expression

update_rule       := ID '*=' expression

ranked_update_rule := LABEL ':' ID '*=' expression

expression        := primary
                   | unary_expr
                   | binary_expr
                   | '(' expression ')'

primary           := ID
                   | 'True'
                   | 'False'
                   | 'Random'
                   | tuple

tuple             := '(' NUMBER ',' NUMBER ',' NUMBER ')'

unary_expr        := 'not' expression

binary_expr       := expression 'and' expression
                   | expression 'or' expression

comment           := '#' .*

empty_line        := [ \t]*

LABEL             := \d+ ':'
ID                := [a-zA-Z_+-][a-zA-Z0-9_+-]*
NUMBER            := [+-]?\d+\.?\d*
```

## Semantic Rules

### Node Initialization

1. All nodes referenced in update rules should be initialized (unless the implementation provides a default)
2. A node cannot be initialized multiple times with different values (last assignment wins in implementation)
3. Nodes initialized with `Random` receive a randomly chosen `True` or `False` value at initialization time

### Update Rules

1. Each node should have exactly one update rule
2. Update rules cannot reference undefined nodes
3. The order of update rule execution depends on:
   - The update mode (sync, async, rank, time, plde)
   - Rank labels (in rank and time modes)
   - Random shuffling (in async mode)

### Expression Evaluation

1. **Synchronous mode** (sync, time):
   - All node references in expressions evaluate to values from the previous state
   - All updates are computed first, then applied simultaneously

2. **Asynchronous mode** (async, rank):
   - Node references evaluate to the current state (which may include updates from earlier in this round)
   - Updates are applied immediately as they are computed

3. **Boolean operations**:
   - Standard boolean logic applies
   - Short-circuit evaluation is not required but may be implemented

### Tuple Values (PLDE mode)

1. Tuples represent `(concentration, decay_rate, threshold)`
2. All three values must be numeric
3. Decay rate should be positive (typically > 0)
4. Boolean interpretation: `concentration > threshold / decay_rate`
5. Boolean literals in PLDE mode are converted to tuples:
   - `True` → `(1.0, 1.0, 0.5)`
   - `False` → `(0.0, 1.0, 0.5)`

## Update Modes

### Synchronous (sync)

- All nodes are evaluated using values from the previous state
- Updates are applied simultaneously after all evaluations
- Execution is deterministic given the same initial state

### Asynchronous (async)

- Nodes are evaluated in random order
- Each update is applied immediately
- Nodes reference current (possibly updated) values
- Execution is stochastic
- All rank labels are treated as 1

### Ranked Asynchronous (rank)

- Nodes are grouped by rank label
- Ranks are processed in ascending numerical order
- Within each rank, nodes are updated asynchronously (random order, immediate application)
- Nodes without explicit rank labels default to rank 1

### Time Synchronous (time)

- Each rank represents a time delay
- Updates occur at time points that are multiples of their rank
- Uses synchronous evaluation within each time point

### Piecewise Linear Differential Equations (plde)

- Nodes are associated with continuous variables (concentration, decay, threshold)
- Boolean rules are converted to systems of differential equations
- Numerical integration (Runge-Kutta) is used to simulate
- All rank labels are treated as 1

## Examples

### Basic Boolean Network

```
# Simple three-node network
A = True
B = False
C = False

A* = not C
B* = A and B
C* = B
```

### Ranked Asynchronous Update

```
# Network with time delays
A = B = C = D = False

5: A* = C and (not B)
10: B* = A
15: C* = D
20: D* = B
```

### Chained Initialization

```
# Multiple nodes with same initial value
Stimuli = IAP = Mcl1 = BclxL = PIAS = True
A = B = C = False
```

### PLDE Mode with Tuples

```
# Continuous dynamics
# (concentration, decay, threshold)
A = (1.0, 1.0, 0.5)
B = (0.5, 1.0, 0.5)
C = (0.0, 1.0, 0.5)

1: A* = not C
2: B* = A and B
3: C* = B
```

### Complex Boolean Expression

```
# Complex regulatory logic
GPA1 = AGB1 = True
S1P = GCR1 = False

GPA1* = (S1P or not GCR1) and AGB1
```

### Self-Regulation and Fixed Points

```
# Node that maintains its state
sFas = True
sFas* = sFas

# Node with self-loop
Apoptosis = False
Apoptosis* = Caspase or Apoptosis
```

## Implementation Notes

### Parser Considerations

1. **Tokenization**: 
   - Implement a lexer that recognizes all token types
   - Handle multi-character operators (`*=`, `not`, `and`, `or`)
   - Preserve line information for error reporting

2. **Parsing**:
   - Use operator precedence parsing for expressions
   - Track both initialization and update statements
   - Separate nodes into initialized and update-only sets

3. **Validation**:
   - Check for undefined node references
   - Verify case-unique node names
   - Ensure all nodes are properly initialized
   - Validate tuple syntax and values (PLDE mode)

4. **Error Reporting**:
   - Report line numbers for syntax errors
   - Provide meaningful error messages for semantic issues
   - Handle lexer and parser errors gracefully

### Evaluation Considerations

1. **State Management**:
   - Maintain "old" and "new" state for synchronous updates
   - For asynchronous updates, maintain single mutable state

2. **Randomization**:
   - `Random` literals should be evaluated once during initialization
   - Asynchronous mode requires random shuffling of update order
   - Use seeded random number generator for reproducibility

3. **Rank Processing**:
   - Sort ranks numerically (not lexicographically)
   - Default rank is 1 for unlabeled rules
   - In non-ranked modes, treat all ranks as equal

4. **PLDE Mode**:
   - Requires numerical integration (e.g., Runge-Kutta method)
   - Convert boolean operations to continuous functions
   - Handle tuple-to-boolean conversions

## Edge Cases and Special Behaviors

### Uninitialized Nodes

Nodes that appear in update rules but have no initialization statement:
- Should be reported as an error by default
- Or require a callback function to provide default values

### Self-Referential Rules

Nodes can reference themselves in update rules:
```
A* = A or B      # Valid: A references itself
sFas* = sFas     # Valid: maintains current value
```

Behavior depends on update mode:
- Synchronous: references previous value
- Asynchronous: references current value (may create fixed point)

### Order Independence (Synchronous)

In synchronous mode, the order of update rules in the file does not affect the result.

### Order Dependence (Asynchronous)

In asynchronous mode, execution order affects the result, making simulations stochastic.

### Case Sensitivity

Node names are case-sensitive, but multiple nodes that differ only in case are not allowed:
```
Node = True    # OK
node = False   # ERROR: conflicts with Node
```

### Special Characters in Names

Node names can include `+`, `-`, and `_` to support biological notation:
```
Ca2+c = True          # Valid: calcium concentration
H+ATPase = False      # Valid: hydrogen ATPase
IL-2 = True           # Valid: interleukin-2
```

### Boolean Operator Precedence

Without parentheses, expressions are evaluated according to precedence:
```
A or B and C      # Parsed as: A or (B and C)
not A or B        # Parsed as: (not A) or B
not A and B       # Parsed as: (not A) and B
```

### Empty Networks

A valid BooleanNet file can have:
- No initialization statements (if implementation allows defaults)
- No update rules (nodes remain constant)
- Both sections empty (minimal valid network)

## Version History

This specification is based on BooleanNet version 1.2.7 (April 24, 2014).

Key changes in version 1.2 (Nov 12, 2008):
- Library namespace changed to `boolean2`
- Added support for ranked asynchronous updates
- Added PLDE (piecewise linear differential equations) mode
- Added time synchronous update mode

## References

- **Publication**: "Boolean network simulations for life scientist" by István Albert, Juilee Thakar, Song Li, Ranran Zhang, and Réka Albert in *Source Code for Biology and Medicine* (2008)
- **Original Implementation**: Python package `booleannet` / `boolean2`
- **Parser Implementation**: Uses PLY (Python Lex-Yacc) by David Beazley

## Formal Token Specification

For implementation, here is the complete token specification:

| Token Type | Pattern | Description |
|------------|---------|-------------|
| `COMMENT` | `#.*` | Comment to end of line |
| `LABEL` | `\d+:` | Rank label (integer + colon) |
| `ID` | `[a-zA-Z_+-][a-zA-Z0-9_+-]*` | Identifier/node name |
| `NUMBER` | `[+-]?\d+\.?\d*` | Numeric literal |
| `STATE` | `True|False|Random` | Boolean state literals |
| `AND` | `and` | Logical AND operator |
| `OR` | `or` | Logical OR operator |
| `NOT` | `not` | Logical NOT operator |
| `ASSIGN` | `*` | Update marker |
| `EQUAL` | `=` | Assignment operator |
| `LPAREN` | `(` | Left parenthesis |
| `RPAREN` | `)` | Right parenthesis |
| `COMMA` | `,` | Comma separator |
| `WHITESPACE` | `[ \t]+` | Ignored |
| `NEWLINE` | `\n+` | Line terminator |

## Implementation Checklist

When implementing a BooleanNet parser, ensure:

- [ ] Lexer correctly tokenizes all token types
- [ ] Lexer handles comments and whitespace
- [ ] Parser handles initialization statements (including chained assignments)
- [ ] Parser handles update rules (with and without ranks)
- [ ] Parser correctly applies operator precedence
- [ ] Parser supports parentheses for grouping
- [ ] Semantic analysis checks for undefined nodes
- [ ] Semantic analysis enforces case-unique node names
- [ ] Semantic analysis validates all nodes are initialized
- [ ] Support for all five update modes (or subset documented)
- [ ] Tuple literals supported (if implementing PLDE mode)
- [ ] Error messages include line numbers
- [ ] Random values handled correctly during initialization
- [ ] Self-referential rules work correctly in both sync and async modes

