import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Std.Data.HashMap

/-! Symbolic coefficient verification for Hill–Luo–Trinh–Vindas-Meléndez,
Theorem 5.9 and Conjecture 8.1, in dimensions three through five. -/

namespace ParkingPolytopeCertificate

/-- Admissible multisets satisfy Hall's inequality on each ambient subset.
The subsets are bitmasks and the list records occurrences with multiplicity. -/
private def admissible (sizes : Array Nat) (masks : List Nat) : Bool :=
  (List.range sizes.size).all fun s =>
    (masks.countP (fun a => (a &&& s) == a)) ≤ sizes[s]!

private abbrev Profiles := Std.HashMap (List (Nat × Nat)) Nat

private def addProfiles (sizes : Array Nat) : Nat → Nat → List Nat → Profiles → Profiles
  | 0, _, selected, profiles =>
    let key := (selected.eraseDups.map fun a => (sizes[a]!, selected.count a)).mergeSort
      fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2)
    profiles.insert key (profiles[key]?.getD 0 + 1)
  | left + 1, start, selected, profiles =>
    (List.range' start (sizes.size - start)).foldl (fun counts a =>
      let extended := a :: selected
      if admissible sizes extended then addProfiles sizes left a extended counts else counts)
      profiles

private def draconianProfiles (n : Nat) : Profiles :=
  let sizes := ((List.range (2 ^ n)).map fun a =>
    (List.range n).countP (fun i => a.testBit i)).toArray
  (List.range (n + 1)).foldl (fun counts copies => addProfiles sizes copies 1 [] counts) ∅

/- A monomial is encoded in base `n+1` with the generating variable in digit
zero. Exponents never exceed n, so multiplying monomials adds their keys. -/
private abbrev Coefficients := Std.HashMap Nat Int

private def addTerm (p : Coefficients) (key : Nat) (value : Int) : Coefficients :=
  let sum := p[key]?.getD 0 + value
  if sum == 0 then p.erase key else p.insert key sum

private def multiply (p q : Coefficients) : Coefficients :=
  p.fold (fun result i a => q.fold (fun result j b => addTerm result (i + j) (a * b)) result) ∅

private def w (n size : Nat) : Coefficients := Id.run do
  if size == 1 then
    return addTerm ∅ (1 + (n + 1)) 1
  let mut p : Coefficients := ∅
  for j in [0:size - 1] do
    let a := (-1 : Int) ^ j * Int.ofNat ((size - 2).choose j)
    p := addTerm p (1 + (n + 1) ^ (size - j)) a
    p := addTerm p 1 a
  return p

private def risingFactors (n : Nat) : Std.HashMap (Nat × Nat) Coefficients := Id.run do
  let mut factors : Std.HashMap (Nat × Nat) Coefficients := ∅
  for size in [1:n + 1] do
    let weight := w n size
    let mut p := addTerm ∅ 0 1
    for k in [0:size] do
      p := multiply p (addTerm weight 0 (Int.ofNat k))
      factors := factors.insert (size, k + 1) p
  return factors

/-- Multiply the Ehrhart polynomial by `n!` to keep integral coefficients,
then replace every power `t^d` by `u^d * (1-u)^(n-d)`. -/
private def scaledMagic (n : Nat) (profiles : Profiles) : Coefficients := Id.run do
  let factors := risingFactors n
  let ehrhart := profiles.fold (fun result profile count =>
    let divisor := profile.foldl (fun x (_, copies) => x * copies.factorial) 1
    let term := profile.foldl (fun p key => multiply p (factors[key]?.getD ∅))
      (addTerm ∅ 0 (Int.ofNat (count * (n.factorial / divisor))))
    term.fold (fun p key a => addTerm p key a) result) (∅ : Coefficients)
  return ehrhart.fold (fun result key a =>
    let d := key % (n + 1)
    (List.range (n - d + 1)).foldl (fun p j =>
      addTerm p (key + j) (a * (-1 : Int) ^ j * Int.ofNat ((n - d).choose j))) result) ∅

def check (n sequences groups terms : Nat) : Bool :=
  let profiles := draconianProfiles n
  let magic := scaledMagic n profiles
  profiles.fold (fun total _ count => total + count) 0 == sequences &&
  profiles.size == groups && magic.size == terms && magic[0]?.getD 0 == Int.ofNat n.factorial &&
  magic.fold (fun good _ coefficient => good && decide (0 < coefficient)) true

theorem magic_certificate_three : check 3 84 24 34 = true := by native_decide
theorem magic_certificate_four : check 4 2726 108 126 = true := by native_decide
theorem magic_certificate_five : check 5 289022 510 462 = true := by native_decide

#print axioms magic_certificate_five

end ParkingPolytopeCertificate
