/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Implementation for the parsec parser combinators described in the
paper:
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf
-/
prelude
import init.data.to_string init.data.string.basic init.data.list.basic init.control.except
import init.data.repr init.lean.name init.data.dlist init.control.monad_fail init.control.combinators
import init.util

namespace lean
namespace parser
open string (iterator)

namespace parsec
@[reducible] def position : Type := nat

structure message (μ : Type := unit) :=
(it         : iterator)
(unexpected : string       := "")          -- unexpected input
(expected   : dlist string := dlist.empty) -- expected productions
(custom     : option μ)

def merge {μ : Type} (msg₁ msg₂ : message μ) : message μ :=
{ expected := msg₁.expected ++ msg₂.expected, ..msg₁ }

def expected.to_string : list string → string
| []       := ""
| [e]      := e
| [e1, e2] := e1 ++ " or " ++ e2
| (e::es)  := e ++ ", " ++ expected.to_string es

protected def message.to_string {μ : Type} (msg : message μ) : string :=
let (line, col) := msg.it.to_string.line_column msg.it.offset in
-- always print ":"; we assume at least one of `unexpected` and `expected` to be non-empty
let loc := ["error at line " ++ to_string line ++ ", column " ++ to_string col ++ ":"] in
let unexpected := (if msg.unexpected = "" then [] else ["unexpected " ++ msg.unexpected]) in
let ex_list := msg.expected.to_list in
let expected := if ex_list = [] then [] else ["expected " ++ expected.to_string ex_list] in
"\n".intercalate $ loc ++ unexpected ++ expected

instance {μ : Type} : has_to_string (message μ) :=
⟨message.to_string⟩

-- use for e.g. upcasting parsec errors with `monad_except.lift_except`
instance {μ : Type} : has_lift (message μ) string :=
⟨to_string⟩

/-
Remark: we store expected "error" messages in `ok_eps` results.
They contain the error that would have occurred if a
successful "epsilon" alternative was not taken.
-/
inductive result (μ ε α : Type)
| ok {} (a : α) (it : iterator) (expected : ε) : result
| error {} (msg : message μ) (consumed : bool) : result
open result

class expected (ε : Type) :=
(eps consumed : ε)
(bind_mk_res {μ β : Type} : ε → result μ ε β → result μ ε β)
(orelse_mk_res {μ α : Type} (msg₁ : message μ) (r : result μ ε α) : result μ ε α)
(labels_mk_res {μ α : Type} (r : result μ ε α) (lbls : dlist string) : result μ ε α)

@[inline_if_reduce] def bool_bind_mk_res {μ β : Type} (ex₁ : bool) (r : result μ bool β) : result μ bool β :=
match r with
| ok b it cns   := ok b it (ex₁ || cns)
| error msg cns := error msg (ex₁ || cns)

@[inline] def bool_orelse_mk_res {μ α : Type} (msg₁ : message μ) (r : result μ bool α) : result μ bool α :=
r

@[inline] def bool_labels_mk_res {μ α : Type} (r : result μ bool α) (lbls : dlist string) : result μ bool α :=
r

instance bool_expected : expected bool :=
{ eps := ff, consumed := tt, bind_mk_res := @bool_bind_mk_res, orelse_mk_res := @bool_orelse_mk_res,
  labels_mk_res := @bool_labels_mk_res }

abbreviation ods := option (dlist string)

@[inline_if_reduce] def ods_bind_mk_res {μ β : Type} (ex₁ : ods) (r : result μ ods β) : result μ ods β :=
match ex₁, r with
| none,     ok b it _          := ok b it none
| none,     error msg _        := error msg tt
| some ex₁, ok b it (some ex₂) := ok b it (some $ ex₁ ++ ex₂)
| some ex₁, error msg₂ ff      := error { expected := ex₁ ++ msg₂.expected, .. msg₂ } ff
| some ex₁, other              := other

@[inline_if_reduce] def ods_orelse_mk_res {μ α : Type} (msg₁ : message μ) (r : result μ ods α) : result μ ods α :=
match r with
| ok a it' (some ex₂) := ok a it' (some $ msg₁.expected ++ ex₂)
| error msg₂ ff       := error (merge msg₁ msg₂) ff
| other               := other

@[inline_if_reduce] def ods_labels_mk_res {μ α : Type} (r : result μ ods α) (lbls : dlist string) : result μ ods α :=
match r with
  | ok a it (some _) := ok a it (some lbls)
  | error msg ff     := error {expected := lbls, ..msg} ff
  | other            := other

instance dlist_expected : expected (option (dlist string)) :=
{ eps := some dlist.empty, consumed := none, bind_mk_res := @ods_bind_mk_res, orelse_mk_res := @ods_orelse_mk_res,
  labels_mk_res := @ods_labels_mk_res }

@[inline] def result.mk_eps {μ ε α : Type} [expected ε] (a : α) (it : iterator) : result μ ε α :=
result.ok a it (expected.eps ε)

@[inline] def result.mk_consumed {μ ε α : Type} [expected ε] (a : α) (it : iterator) : result μ ε α :=
result.ok a it (expected.consumed ε)
end parsec

open parsec

def parsec_t (μ ε : Type) (m : Type → Type) (α : Type) :=
iterator → m (result μ ε α)

abbreviation parsec (μ ε : Type) := parsec_t μ ε id
/-- `parsec` without custom error message type -/
abbreviation parsec' := parsec unit (option (dlist string))

namespace parsec_t
open parsec.result
variables {m : Type → Type} [monad m] {μ ε α β : Type} [expected ε]

def run (p : parsec_t μ ε m α) (s : string) (fname := "") : m (except (message μ) α) :=
do r ← p s.mk_iterator,
   pure $ match r with
   | ok a _ _     := except.ok a
   | error msg _  := except.error msg

@[inline] protected def pure (a : α) : parsec_t μ ε m α :=
λ it, pure (mk_eps a it)

def eps : parsec_t μ ε m unit :=
parsec_t.pure ()

protected def failure : parsec_t μ ε m α :=
λ it, pure (error { unexpected := "failure", it := it, custom := none } ff)

/--
  The `bind p q` combinator behaves as follows:
  1- If `p` fails, then it fails.
  2- If `p` succeeds and consumes input, then execute `q`
  3- If `q` succeeds but does not consume input, then execute `q`
     and merge error messages if both do not consume any input.
-/
@[inline] protected def bind (p : parsec_t μ ε m α) (q : α → parsec_t μ ε m β) : parsec_t μ ε m β :=
λ it, do
 r ← p it,
 match r with
 | ok a it ex₁  := expected.bind_mk_res ex₁ <$> q a it
 | error msg c  := pure (error msg c)

instance : monad (parsec_t μ ε m) :=
{ bind := λ _ _, parsec_t.bind, pure := λ _, parsec_t.pure }

instance : monad_fail parsec' :=
{ fail := λ _ s it, error { unexpected := s, it := it, custom := () } ff }

instance : monad_except (message μ) (parsec_t μ ε m) :=
{ throw := λ _ msg it, pure (error msg ff),
  catch := λ _ p c it, do
    r ← p it,
    match r with
    | error msg cns := do {
      r ← c msg msg.it,
      pure $ match r with
      | error msg' cns' := error msg' (cns || cns')
      | other := other }
    | other       := pure other }

instance : has_monad_lift m (parsec_t μ ε m) :=
{ monad_lift := λ α x it, do a ← x, pure (mk_eps a it) }

def expect (msg : message μ) (exp : string) : message μ :=
{expected := dlist.singleton exp, ..msg}

@[inline] def labels (p : parsec_t μ ε m α) (lbls : dlist string) : parsec_t μ ε m α :=
λ it, do
  r ← p it,
  pure $ expected.labels_mk_res r lbls

@[inline_if_reduce] def try_mk_res (r : result μ ε α) : result μ ε α :=
match r with
| error msg _  := error msg ff
| other        := other

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/
@[inline] def try (p : parsec_t μ ε m α) : parsec_t μ ε m α :=
λ it, do
  r ← p it,
  pure $ try_mk_res r

/--
  The `orelse p q` combinator behaves as follows:
  1- If `p` succeeds *or* consumes input, return
     its result. Otherwise, execute `q` and return its
     result.
     Recall that the `try p` combinator can be used to
     pretend that `p` did not consume any input, and
     simulate infinite lookahead.
  2- If both `p` and `q` did not consume any input, then
     combine their error messages (even if one of
     them succeeded).
-/
@[inline] protected def orelse (p q : parsec_t μ ε m α) : parsec_t μ ε m α :=
λ it, do
  r ← p it,
  match r with
  | error msg₁ ff := do { r ← q it, pure $ expected.orelse_mk_res msg₁ r }
  | other         := pure other

instance : alternative (parsec_t μ ε m) :=
{ orelse         := λ _, parsec_t.orelse,
  failure        := λ _, parsec_t.failure,
  ..parsec_t.monad }

/-- Parse `p` without consuming any input. -/
@[specialize] def lookahead (p : parsec_t μ ε m α) : parsec_t μ ε m α :=
λ it, do
  r ← p it,
  pure $ match r with
  | ok a s' _ := mk_eps a it
  | other     := other

/-- `not_followed_by p` succeeds when parser `p` fails -/
@[specialize] def not_followed_by (p : parsec' α) (msg : string := "input") : parsec' unit :=
λ it, do
  r ← p it,
  pure $ match r with
  | ok _ _ _     := error { it := it, unexpected := msg, custom := () } ff
  | error _ _    := mk_eps () it

def dbg (label : string) (p : parsec_t μ ods m α) : parsec_t μ ods m α :=
λ it, do
  r ← p it,
  pure $ trace ("DBG " ++ label ++ ": \"" ++ (it.extract (it.nextn 40)).get_or_else "" ++ "\"") $ match r : _ → result μ ods α with
  | ok a it' none      := trace ("consumed ok : '" ++ (it.extract it').get_or_else "" ++ "'") r
  | ok a it' (some ex) := trace ("empty ok : '" ++ (it.extract it').get_or_else "" ++ "'") r
  | error msg tt := trace ("consumed error : '" ++ (it.extract msg.it).get_or_else "" ++ "'\n" ++ to_string msg) r
  | error msg ff := trace ("empty error : '" ++ (it.extract msg.it).get_or_else "" ++ "'\n" ++ to_string msg) r

end parsec_t

/- Type class for abstracting from concrete monad stacks containing a `parsec` somewhere. -/
class monad_parsec (μ ε : out_param Type) (m : Type → Type) :=
-- analogous to e.g. `monad_reader.lift` before simplification (see there)
(lift {} {α : Type} : parsec μ ε α → m α)
-- Analogous to e.g. `monad_reader_adapter.map` before simplification (see there).
-- Its usage seems to be way too common to justify moving it into a separate type class.
(map {} {α : Type} : (∀ {m'} [monad m'] {α}, parsec_t μ ε m' α → parsec_t μ ε m' α) → m α → m α)

/-- `parsec` without custom error message type -/
abbreviation monad_parsec' := monad_parsec unit

variables {μ ε : Type}

instance {m : Type → Type} [monad m] : monad_parsec μ ε (parsec_t μ ε m) :=
{ lift := λ α p it, pure (p it),
  map  := λ α f x, f x }

instance monad_parsec_trans {m n : Type → Type} [has_monad_lift m n] [monad_functor m m n n] [monad_parsec μ ε m] : monad_parsec μ ε n :=
{ lift := λ α p, monad_lift (monad_parsec.lift p : m α),
  map  := λ α f x, monad_map (λ β x, (monad_parsec.map @f x : m β)) x }

namespace monad_parsec
open parsec_t
variables {m : Type → Type} [monad m] [monad_parsec μ ε m] {α β : Type} [expected ε]

def error {α : Type} (unexpected : string) (expected : dlist string := dlist.empty)
          (it : option iterator := none) (custom : option μ := none) : m α :=
lift $ λ it', result.error { unexpected := unexpected, expected := expected, it := it.get_or_else it', custom := custom } ff

@[inline] def left_over : m iterator :=
lift $ λ it, result.mk_eps it it

/-- Return the number of characters left to be parsed. -/
@[inline] def remaining : m nat :=
string.iterator.remaining <$> left_over

@[inline] def labels (p : m α) (lbls : dlist string) : m α :=
map (λ m' inst β p, @parsec_t.labels m' inst μ ε β _ p lbls) p

@[inline] def label (p : m α) (lbl : string) : m α :=
labels p (dlist.singleton lbl)

infixr ` <?> `:2 := label

@[inline] def hidden (p : m α) : m α :=
labels p dlist.empty

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/

@[inline] def try (p : m α) : m α :=
map (λ m' inst β p, @parsec_t.try m' inst μ ε β _ p) p

/-- Parse `p` without consuming any input. -/
@[inline] def lookahead (p : m α) : m α :=
map (λ m' inst β p, @parsec_t.lookahead m' inst μ ε β _ p) p

/-- Faster version of `not_followed_by (satisfy p)` -/
@[inline] def not_followed_by_sat (p : char → bool) : m unit :=
do it ← left_over,
   if !it.has_next then pure ()
   else let c := it.curr in
       if p c then error (repr c)
       else pure ()

def eoi_error (it : iterator) : result μ ε α :=
result.error { it := it, unexpected := "end of input", custom := default _ } ff

def curr : m char :=
string.iterator.curr <$> left_over

@[inline] def cond (p : char → bool) (t : m α) (e : m α) : m α :=
mcond (p <$> curr) t e

/--
If the next character `c` satisfies `p`, then
update position and return `c`. Otherwise,
generate error message with current position and character. -/
@[inline] def satisfy (p : char → bool) : m char :=
do it ← left_over,
   if !it.has_next then error "end of input"
   else let c := it.curr in
       if p c then lift $ λ _, result.ok c it.next (expected.consumed ε)
       else error (repr c)

def ch (c : char) : m char :=
satisfy (= c)

def alpha : m char :=
satisfy char.is_alpha

def digit : m char :=
satisfy char.is_digit

def upper : m char :=
satisfy char.is_upper

def lower : m char :=
satisfy char.is_lower

def any : m char :=
satisfy (λ _, true)

private def str_aux : nat → iterator → iterator → option iterator
| 0     _    it := some it
| (n+1) s_it it :=
  if it.has_next ∧ s_it.curr = it.curr then str_aux n s_it.next it.next
  else none

/--
`str s` parses a sequence of elements that match `s`. Returns the parsed string (i.e. `s`).
This parser consumes no input if it fails (even if a partial match).
Note: The behaviour of this parser is different to that the `string` parser in the Parsec_t Μ Ε M Haskell library,
as this one is all-or-nothing.
-/
def str_core (s : string) (ex : dlist string) : m string :=
if s.is_empty then pure ""
else lift $ λ it, match str_aux s.length s.mk_iterator it with
  | some it' := result.ok s it' (expected.consumed ε)
  | none     := result.error { it := it, expected := dlist.singleton (repr s), custom := none } ff

@[inline] def str (s : string) : m string :=
str_core s (dlist.singleton (repr s))

private def take_aux : nat → string → iterator → result μ ε string
| 0     r it := result.ok r it (expected.consumed ε)
| (n+1) r it :=
  if !it.has_next then eoi_error it
  else take_aux n (r.push (it.curr)) it.next

/-- Consume `n` characters. -/
def take (n : nat) : m string :=
if n = 0 then pure ""
else lift $ take_aux n ""

private def mk_string_result (r : string) (it : iterator) : result μ ε string :=
if r.is_empty then result.mk_eps r it
else result.ok r it (expected.consumed ε)

@[specialize]
private def take_while_aux (p : char → bool) : nat → string → iterator → result μ ε string
| 0     r it := mk_string_result r it
| (n+1) r it :=
  if !it.has_next then mk_string_result r it
  else let c := it.curr in
       if p c then take_while_aux n (r.push c) it.next
       else mk_string_result r it

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser does not fail. It will return an empty string if the predicate
returns `ff` on the current character. -/
@[specialize] def take_while (p : char → bool) : m string :=
lift $ λ it, take_while_aux p it.remaining "" it

@[specialize] def take_while_cont (p : char → bool) (ini : string) : m string :=
lift $ λ it, take_while_aux p it.remaining ini it

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser requires the predicate to succeed on at least once. -/
@[specialize] def take_while1 (p : char → bool) : m string :=
do c ← satisfy p,
   take_while_cont p (to_string c)

/--
Consume input as long as the predicate returns `ff` (i.e. until it returns `tt`), and return the consumed input.
This parser does not fail. -/
@[inline] def take_until (p : char → bool) : m string :=
take_while (λ c, !p c)

@[inline] def take_until1 (p : char → bool) : m string :=
take_while1 (λ c, !p c)

private def mk_consumed_result (consumed : bool) (it : iterator) : result μ ε unit :=
if consumed then result.ok () it (expected.consumed ε)
else result.mk_eps () it

@[specialize] private def take_while_aux' (p : char → bool) : nat → bool → iterator → result μ ε unit
| 0     consumed it := mk_consumed_result consumed it
| (n+1) consumed it :=
  if !it.has_next then mk_consumed_result consumed it
  else let c := it.curr in
       if p c then take_while_aux' n tt it.next
       else mk_consumed_result consumed it

/-- Similar to `take_while` but it does not return the consumed input. -/
@[specialize] def take_while' (p : char → bool) : m unit :=
lift $ λ it, take_while_aux' p it.remaining ff it

/-- Similar to `take_while1` but it does not return the consumed input. -/
@[specialize] def take_while1' (p : char → bool) : m unit :=
satisfy p *> take_while' p

/-- Consume zero or more whitespaces. -/
@[noinline] def whitespace : m unit :=
take_while' char.is_whitespace

/-- Shorthand for `p <* whitespace` -/
@[inline] def lexeme (p : m α) : m α :=
p <* whitespace

/-- Parse a numeral in decimal. -/
@[noinline] def num : m nat :=
string.to_nat <$> (take_while1 char.is_digit)

/-- Succeed only if there are at least `n` characters left. -/
def ensure (n : nat) : m unit :=
do it ← left_over,
   if n ≤ it.remaining then pure ()
   else error "end of input" (dlist.singleton ("at least " ++ to_string n ++ " characters"))

/-- Return the current position. -/
def pos : m position :=
string.iterator.offset <$> left_over

@[inline] def not_followed_by [monad_except (message μ) m] (p : m α) (msg : string := "input") : m unit :=
do it ← left_over,
   b ← lookahead $ catch (p *> pure ff) (λ _, pure tt),
   if b then pure () else error msg dlist.empty it

def eoi : m unit :=
do it ← left_over,
   if it.remaining = 0 then pure ()
   else error (repr it.curr) (dlist.singleton ("end of input"))

@[specialize] def many1_aux [alternative m] (p : m α) : nat → m (list α)
| 0     := do a ← p, pure [a]
| (n+1) := do a ← p,
              as ← (many1_aux n <|> pure []),
              pure (a::as)

@[specialize] def many1 [alternative m] (p : m α) : m (list α) :=
do r ← remaining, many1_aux p r

@[specialize] def many [alternative m] (p : m α) : m (list α) :=
many1 p <|> pure []

@[specialize] def many1_aux' [alternative m] (p : m α) : nat → m unit
| 0     := p *> pure ()
| (n+1) := p *> (many1_aux' n <|> pure ())

@[inline] def many1' [alternative m] (p : m α) : m unit :=
do r ← remaining, many1_aux' p r

@[specialize] def many' [alternative m] (p : m α) : m unit :=
many1' p <|> pure ()

@[specialize] def sep_by1 [alternative m] (p : m α) (sep : m β) : m (list α) :=
(::) <$> p <*> many (sep *> p)

@[specialize] def sep_by [alternative m] (p : m α) (sep : m β) : m (list α) :=
sep_by1 p sep <|> pure []

@[specialize] def fix_aux [alternative m] (f : m α → m α) : nat → m α
| 0     := error "fix_aux: no progress"
| (n+1) := f (fix_aux n)

@[specialize] def fix [alternative m] (f : m α → m α) : m α :=
do n ← remaining, fix_aux f (n+1)

@[specialize] def foldr_aux [alternative m] (f : α → β → β) (p : m α) (b : β) : nat → m β
| 0     := pure b
| (n+1) := (f <$> p <*> foldr_aux n) <|> pure b

/-- Matches zero or more occurrences of `p`, and folds the result. -/
@[specialize] def foldr [alternative m] (f : α → β → β) (p : m α) (b : β) : m β :=
do it ← left_over,
   foldr_aux f p b it.remaining

@[specialize] def foldl_aux [alternative m] (f : α → β → α) (p : m β) : α → nat → m α
| a 0     := pure a
| a (n+1) := (do x ← p, foldl_aux (f a x) n) <|> pure a

/-- Matches zero or more occurrences of `p`, and folds the result. -/
@[specialize] def foldl [alternative m] (f : α → β → α) (a : α) (p : m β) : m α :=
do it ← left_over,
   foldl_aux f p a it.remaining

def unexpected (msg : string) : m α :=
error msg

def unexpected_at (msg : string) (it : iterator) : m α :=
error msg dlist.empty it

/- Execute all parsers in `ps` and return the result of the longest parse(s) if any,
   or else the result of the furthest error. If there are two parses of
   equal length, the first parse wins. -/
@[specialize]
def longest_match [monad_except (message μ) m] (ps : list (m α)) : m (list α) :=
do it ← left_over,
   r ← ps.mfoldr (λ p (r : result μ ε (list α)),
     lookahead $ catch
       (do
         a ← p,
         it ← left_over,
         pure $ match r with
         | result.ok as it' _ := if it'.offset > it.offset then r
             else if it.offset > it'.offset then result.ok [a] it (expected.consumed ε)
             else result.ok (a::as) it (expected.consumed ε)
         | _                     := result.ok [a] it (expected.consumed ε))
       (λ msg, pure $ match r with
           | result.error msg' _ := if msg'.it.offset > msg.it.offset then r
             else if msg.it.offset > msg'.it.offset then result.error msg tt
             else result.error (merge msg msg') (msg.it.offset > it.offset)
           | _ := r))
    ((error "longest_match: empty list" : parsec _ _ _) it),
    lift $ λ _, r

/-- Add trace information about `p`'s input and output. -/
def dbg [monad_parsec μ ods m] (label : string) (p : m α) : m α :=
map (λ m' inst β, @parsec_t.dbg m' inst μ β label) p

@[specialize]
def observing [monad_except (message μ) m] (p : m α) : m (except (message μ) α) :=
catch (except.ok <$> p) $ λ msg, pure (except.error msg)

end monad_parsec

namespace parsec_t
open monad_parsec
variables {m : Type → Type} [monad m] {α β : Type} [expected ε]

def parse (p : parsec_t μ ε m α) (s : string) (fname := "") : m (except (message μ) α) :=
run p s fname

def parse_with_eoi (p : parsec_t μ ε m α) (s : string) (fname := "") : m (except (message μ) α) :=
run (p <* eoi) s fname

def parse_with_left_over (p : parsec_t μ ε m α) (s : string) (fname := "") : m (except (message μ) (α × iterator)) :=
run (prod.mk <$> p <*> left_over) s fname

end parsec_t

def parsec.parse [expected ε] {α : Type} (p : parsec μ ε α) (s : string) (fname := "") : except (message μ) α :=
parsec_t.parse p s fname

end parser
end lean
