module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairAddCommGroup

/-!
# The group of pairs as an extension of the torsion of the Picard group

The isomorphism classes of pairs on a scheme form an abelian group under the tensor product of
pairs (`AlgebraicGeometry.instAddCommGroupPairClasses`). This file identifies that group as an
extension: it maps onto the `n`-torsion of the Picard group by remembering only the invertible
sheaf, and the kernel of that map is the image of the global units modulo `n`-th powers, which
enter as the pairs whose invertible sheaf is trivial.

This is the pair side of the exact sequence whose cohomological side is
`AlgebraicGeometry.exists_kummerBoundary_iff` and
`AlgebraicGeometry.exists_kummerFirstCohomologyMap_iff`: those present
`H¹(S, μ_n)` as an extension of the `n`-torsion of `H¹(S, 𝐆_m)` by the global units modulo
`n`-th powers, and the statements below present the group of pairs the same way. Both sides are
now groups and both presentations are now homomorphisms, which is what a comparison map between
them has to respect.

## Main definitions

* `AlgebraicGeometry.unitPairHom` is the homomorphism from the global units, written additively,
  to the isomorphism classes of pairs, sending a unit to the pair given by the structure sheaf
  trivialized by that unit. It is additive by
  `AlgebraicGeometry.pairIsoTensorPairUnitPair`.
* `AlgebraicGeometry.pairSheafClassHom` is the homomorphism to the Picard group remembering only
  the invertible sheaf of a pair. It is additive because addition in the Picard group is the
  tensor product sheaf (Tag 01CX).

## Main results

* `AlgebraicGeometry.unitPairHom_eq_iff` and `AlgebraicGeometry.unitPairHom_eq_zero_iff`: **the
  kernel of the unit-pair homomorphism is the `n`-th powers**, so its image is the global units
  modulo `n`-th powers.
* `AlgebraicGeometry.pairSheafClassHom_eq_zero_iff`: **exactness in the middle** — a class of
  pairs has trivial invertible sheaf exactly when it comes from a global unit.
* `AlgebraicGeometry.exists_pairSheafClassHom_eq_iff`: **the image of the Picard-class
  homomorphism is exactly the `n`-torsion.**

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Picard (PicardGroup classOf classOf_eq_classOf_iff classOf_tensor)

universe u

namespace AlgebraicGeometry

/-! ### The pairs coming from a global unit -/

/-- **The homomorphism from the global units to the isomorphism classes of pairs**, sending a
unit to the structure sheaf trivialized by that unit. The global units are written additively,
as for `AlgebraicGeometry.kummerBoundaryHom`; additivity is
`AlgebraicGeometry.pairIsoTensorPairUnitPair`, that the tensor product of two unit pairs is the
unit pair of the product of the two units. -/
def unitPairHom (S : Scheme.{u}) (n : ℕ) :
    Additive (Scheme.Γ.obj (op S))ˣ →+ PairClasses S n where
  toFun f := pairClass (unitPair S n (Additive.toMul f))
  map_zero' := rfl
  map_add' f g :=
    ((pairClass_eq_iff _ _).2
      ⟨pairIsoTensorPairUnitPair (Additive.toMul f) (Additive.toMul g)⟩).symm

/-- The unit-pair homomorphism sends a global unit to the class of its unit pair. -/
theorem unitPairHom_apply (S : Scheme.{u}) (n : ℕ) (f : (Scheme.Γ.obj (op S))ˣ) :
    unitPairHom S n (Additive.ofMul f) = pairClass (unitPair S n f) := rfl

/-- **Two global units have the same class of pairs exactly when they differ by an `n`-th
power.** -/
theorem unitPairHom_eq_iff (S : Scheme.{u}) (n : ℕ)
    (f g : Additive (Scheme.Γ.obj (op S))ˣ) :
    unitPairHom S n f = unitPairHom S n g ↔
      ∃ u : (Scheme.Γ.obj (op S))ˣ,
        Additive.toMul f = u ^ n * Additive.toMul g :=
  (pairClass_eq_iff _ _).trans (pairIso_unitPair_iff S n _ _)

/-- **The kernel of the unit-pair homomorphism is the `n`-th powers of the global units**, so its
image is the global units modulo `n`-th powers. -/
theorem unitPairHom_eq_zero_iff (S : Scheme.{u}) (n : ℕ)
    (f : Additive (Scheme.Γ.obj (op S))ˣ) :
    unitPairHom S n f = 0 ↔
      ∃ u : (Scheme.Γ.obj (op S))ˣ, Additive.toMul f = u ^ n := by
  refine Iff.trans (unitPairHom_eq_iff S n f 0) (exists_congr fun u => ?_)
  rw [toMul_zero, mul_one]

/-! ### Remembering only the invertible sheaf -/

/-- The Picard class of the invertible sheaf of a pair, read on isomorphism classes of pairs: an
isomorphism of pairs is in particular an isomorphism of the invertible sheaves, so the Picard
class is the same. -/
def pairSheafClass (S : Scheme.{u}) (n : ℕ) :
    PairClasses S n → PicardGroup S.presheaf (ringSheafCond S) :=
  Quotient.lift (fun P => classOf S.presheaf (ringSheafCond S) P.sheaf P.invertible) (by
    rintro P Q ⟨φ⟩
    exact (classOf_eq_classOf_iff S.presheaf (ringSheafCond S) P.sheaf Q.sheaf
      P.invertible Q.invertible).2 ⟨φ.sheafIso⟩)

/-- **The homomorphism from the isomorphism classes of pairs to the Picard group**, remembering
only the invertible sheaf. It is additive because addition in the Picard group is the tensor
product sheaf, which is `Stacks.SheafOfModules.Picard.classOf_tensor` of Tag 01CX, and the
invertible sheaf of a tensor product of pairs is the tensor product sheaf. -/
def pairSheafClassHom (S : Scheme.{u}) (n : ℕ) :
    PairClasses S n →+ PicardGroup S.presheaf (ringSheafCond S) where
  toFun := pairSheafClass S n
  map_zero' := classOf_unit_eq_zero S
  map_add' x y := by
    refine Quotient.inductionOn₂ x y fun P Q => ?_
    exact (classOf_tensor S.presheaf (ringSheafCond S) P.sheaf Q.sheaf P.invertible
      Q.invertible (tensorPair S n P Q).invertible).symm

/-- The Picard-class homomorphism sends the class of a pair to the Picard class of its
invertible sheaf. -/
theorem pairSheafClassHom_pairClass (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n) :
    pairSheafClassHom S n (pairClass P) =
      classOf S.presheaf (ringSheafCond S) P.sheaf P.invertible := rfl

/-- The composite of the two homomorphisms is zero: a pair coming from a global unit has the
structure sheaf as its invertible sheaf. -/
theorem pairSheafClassHom_unitPairHom (S : Scheme.{u}) (n : ℕ)
    (f : Additive (Scheme.Γ.obj (op S))ˣ) :
    pairSheafClassHom S n (unitPairHom S n f) = 0 := classOf_unit_eq_zero S

/-- **Stacks Project, Tag 040Q, exactness in the middle of the pair side.** A class of pairs has
trivial Picard class — that is, its invertible sheaf is isomorphic to the structure sheaf —
exactly when it is the class of a pair coming from a global unit. The forward direction is
`AlgebraicGeometry.exists_pairIso_unitPair`, that a pair whose invertible sheaf is merely
isomorphic to the structure sheaf is isomorphic to a unit pair. -/
@[stacks 040Q "exactness in the middle of the pair side of the extension, as abelian groups: \
the kernel of the homomorphism from the isomorphism classes of pairs to the Picard group is the \
image of the homomorphism from the global units; neither the cohomology group nor the \
comparison with it occurs"]
theorem pairSheafClassHom_eq_zero_iff (S : Scheme.{u}) (n : ℕ) (x : PairClasses S n) :
    pairSheafClassHom S n x = 0 ↔
      ∃ f : Additive (Scheme.Γ.obj (op S))ˣ, unitPairHom S n f = x := by
  refine Quotient.inductionOn x fun P => ?_
  constructor
  · intro h
    obtain ⟨e⟩ := (classOf_eq_zero_iff S P.sheaf P.invertible).1 h
    obtain ⟨f, hf⟩ := exists_pairIso_unitPair S n P e
    exact ⟨Additive.ofMul f, ((pairClass_eq_iff _ _).2 hf).symm⟩
  · rintro ⟨f, hf⟩
    rw [← hf]
    exact pairSheafClassHom_unitPairHom S n f

/-- **Stacks Project, Tag 040Q, surjectivity of the pair side onto the torsion.** A Picard class
is the Picard class of a class of pairs exactly when it is `n`-torsion. This is
`AlgebraicGeometry.exists_trivializedPower_classOf_iff` read through the group of isomorphism
classes of pairs. -/
@[stacks 040Q "the image of the homomorphism from the isomorphism classes of pairs to the \
Picard group is exactly the n-torsion, as abelian groups; this is the surjectivity half of the \
pair side of the extension, and the cohomology group does not occur"]
theorem exists_pairSheafClassHom_eq_iff (S : Scheme.{u}) (n : ℕ)
    (c : PicardGroup S.presheaf (ringSheafCond S)) :
    (∃ x : PairClasses S n, pairSheafClassHom S n x = c) ↔ n • c = 0 := by
  refine Iff.trans ⟨?_, ?_⟩ (exists_trivializedPower_classOf_iff S n c)
  · rintro ⟨⟨P⟩, hx⟩
    exact ⟨P, hx⟩
  · rintro ⟨P, hP⟩
    exact ⟨pairClass P, hP⟩

end AlgebraicGeometry

end
