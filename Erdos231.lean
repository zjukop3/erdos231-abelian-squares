/-!
# Erdős Problem 231

Is it true that for every k ≥ 2, every sequence of length 2^k - 1
over a k-symbol alphabet contains an abelian square (a contiguous
subsequence of even length ≥ 2 whose first half is a permutation
of the second half)?

Answer: NO. For k = 4, the sequence
  [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1]
has length 2^4 - 1 = 15 and contains no abelian square.

This is verified computationally by checking all contiguous subsequences.

See: https://www.erdosproblems.com/231
-/

namespace Erdos231

/-- Count occurrences of n in a list. -/
def countElem (n : Nat) : List Nat → Nat
  | [] => 0
  | m :: ms => (if m == n then 1 else 0) + countElem n ms

/-- Check if two lists are permutations (same elements, same counts). -/
def isPerm (l1 l2 : List Nat) : Bool :=
  l1.length == l2.length &&
  l1.all (fun n => countElem n l1 == countElem n l2) &&
  l2.all (fun n => countElem n l1 == countElem n l2)

/-- Check if a list is an abelian square (even length ≥ 2, first half = perm of second). -/
def isAbelianSquare (w : List Nat) : Bool :=
  if w.length % 2 == 0 then
    if 2 ≤ w.length then
      isPerm (w.take (w.length / 2)) (w.drop (w.length / 2))
    else
      false
  else
    false

/-- Check if a list contains an abelian square as a contiguous subsequence. -/
def containsAbelianSquare (w : List Nat) : Bool :=
  (List.range w.length).any (fun i =>
    (List.range (w.length - i + 1)).any (fun len =>
      isAbelianSquare ((w.drop i).take len)))

/-- The counterexample sequence (k=4, length 2^4-1=15). -/
def S : List Nat := [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1]

/-- Main theorem: S is a counterexample to Erdős 231. -/
theorem erdos_231 :
    S.length = 2^4 - 1 ∧
    S.all (fun n => if n < 4 then true else false) = true ∧
    containsAbelianSquare S = false := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end Erdos231
