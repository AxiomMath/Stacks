module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# A product decomposition of a structure sheaf with two nonzero factors

`Stacks.Cohomology.InvertibleDerived.ProductDecomposition` is the datum
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of Stacks 0FPG, and several of the statements proved about it — the
orthogonality `𝒪_n ⊗ 𝒪_m = 0` for `n ≠ m`, the invertibility of `⨁_n 𝒪_n[-n]` — are
universally quantified over it with no further hypothesis.  Such a statement has content only to
the extent that the datum has inhabitants whose factors are not all zero: the only decomposition
built so far is `ProductDecomposition.oneFactorDecomposition`, which has `𝒪_0 = 𝒪_X` and the
zero ring in every other degree, and for it every off-diagonal pair `m ≠ n` has a factor with no
sections (`ProductDecomposition.subsingleton_oneFactorFamily_of_ne`), so every instance of the
orthogonality is discharged because one of the two modules is zero, and `⨁_n 𝒪_n[-n]` is
`𝒪_X[0]`.

This file builds a decomposition with **two factors that have nonzero sections**, over a ringed
space constructed for the purpose.

## The construction

Fix a topological space `T`, two points `p₀`, `p₁` of it and two commutative rings `R`, `S`.
The family is the skyscraper sheaf of `R` at `p₀` in degree `0`, the skyscraper sheaf of `S` at
`p₁` in degree `1`, and the zero ring in every other degree; the space is `T` with
`∏ᶜ` of that family as its sheaf of rings, so that the identification
`ProductDecomposition.iso` asks for is the identity.  Local finiteness holds on the whole of `T`
because only two factors have any sections at all.

Over an open set containing `p₀` the sections of the degree-zero factor are `R`, and over an
open set containing `p₁` the sections of the degree-one factor are `S`, so as soon as `R` and `S`
are nontrivial neither factor is `Subsingleton`.

## Main definitions

* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.twoFactorFamily`: the family of factors.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.twoFactorSpace`: the ringed space.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.twoFactorDecomposition`: the product
  decomposition of its structure sheaf.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.OffDiagonallyDegenerate`: the property of
  a product decomposition that for every pair of distinct degrees one of the two factors has no
  sections over any open set — the property that makes every instance of the off-diagonal
  orthogonality vacuous.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.witnessDecomposition`: a closed instance
  of the construction, `ℤ` in degrees `0` and `1` over a one-point space.

## Main results

* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.not_subsingleton_factor_zero`,
  `...not_subsingleton_factor_one`: neither of the two factors has subsingleton sections.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.not_isZero_toOXMod_unit_zero`,
  `...not_isZero_toOXMod_unit_one`: neither factor, read as an `𝒪_X`-module, is a zero object.
  This is the form the orthogonality statements consume, so it is the one that decides whether
  their conclusion is reached for a nonzero reason.
* `TwoFactorWitness.offDiagonallyDegenerate_oneFactorDecomposition`: the one-factor
  decomposition **is** off-diagonally degenerate.
* `TwoFactorWitness.not_offDiagonallyDegenerate_twoFactorDecomposition`: the two-factor
  decomposition **is not**.
* `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.not_subsingleton_structureSheaf`: the
  structure sheaf of the space is itself nonzero, so the space is not degenerate either.

## Implementation notes

The space is built from the product sheaf rather than the product being recognised inside an
existing space's structure sheaf, which is what makes `ProductDecomposition.iso` free: all three
fields of the structure are supplied honestly and none is weakened.

`skyscraperSheaf` lands in `TopCat.Sheaf`, which is a `def` wrapping
`CategoryTheory.Sheaf (Opens.grothendieckTopology _)`; the two spellings are definitionally equal
but do not unify at the `implicit` transparency that `rw` works at, so
`TwoFactorWitness.skyscraperRingSheaf` fixes the spelling once and everything downstream uses it.

The space is a ringed space, not a locally ringed one: nothing here computes the stalks, so this
is a witness for clauses (1) and (2) of Stacks 0FPG and not for clause (3), which assumes the
stalks are local rings.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.InvertibleDerived.TwoFactorWitness

variable {T : TopCat.{u}} (p₀ p₁ : T) (R S : CommRingCat.{u})

/-- The skyscraper sheaf of commutative rings at a point, read at the
`Sheaf (Opens.grothendieckTopology _)` spelling in which a `ProductDecomposition`'s factors
live. -/
def skyscraperRingSheaf : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u} :=
  letI : ∀ U : Opens T, Decidable (p₀ ∈ U) := fun _ => Classical.propDecidable _
  skyscraperSheaf p₀ R

/-- Over an open set containing the point, the sections of the skyscraper sheaf are the ring. -/
theorem skyscraperRingSheaf_obj_of_mem {U : Opens T} (hU : p₀ ∈ U) :
    (skyscraperRingSheaf p₀ R).obj.obj (op U) = R :=
  ite_eq_left hU

/-- Over an open set containing the point, the sections of the skyscraper sheaf of a nontrivial
ring are nontrivial. -/
theorem nontrivial_skyscraperRingSheaf_obj {U : Opens T} (hU : p₀ ∈ U) [hR : Nontrivial R] :
    Nontrivial ((skyscraperRingSheaf p₀ R).obj.obj (op U)) := by
  rw [skyscraperRingSheaf_obj_of_mem p₀ R hU]
  exact hR

/-- **The two-factor family**: `R` concentrated at `p₀` in degree zero, `S` concentrated at `p₁`
in degree one, and the zero ring in every other degree. -/
def twoFactorFamily : ℤ → Sheaf (Opens.grothendieckTopology T) CommRingCat.{u} :=
  fun n => if n = 0 then skyscraperRingSheaf p₀ R
    else if n = 1 then skyscraperRingSheaf p₁ S
    else zeroRingSheaf _

/-- The degree-zero member of the two-factor family is the skyscraper sheaf of `R` at `p₀`. -/
theorem twoFactorFamily_zero :
    twoFactorFamily p₀ p₁ R S 0 = skyscraperRingSheaf p₀ R :=
  ite_eq_left rfl

/-- The degree-one member of the two-factor family is the skyscraper sheaf of `S` at `p₁`. -/
theorem twoFactorFamily_one :
    twoFactorFamily p₀ p₁ R S 1 = skyscraperRingSheaf p₁ S :=
  (ite_eq_right one_ne_zero).trans (ite_eq_left rfl)

/-- Outside degrees zero and one the two-factor family is the zero sheaf of rings. -/
theorem twoFactorFamily_of_ne {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ 1) :
    twoFactorFamily p₀ p₁ R S n = zeroRingSheaf _ :=
  (ite_eq_right h0).trans (ite_eq_right h1)

/-- The zero sheaf of rings has no sections beyond zero. -/
theorem subsingleton_zeroRingSheaf_obj {D : Type u} [Category.{u} D]
    (K : GrothendieckTopology D) (U : Dᵒᵖ) :
    Subsingleton ((zeroRingSheaf.{u, u, u} K).obj.obj U) := by
  simp only [zeroRingSheaf, Sheaf.terminal_obj, Functor.const_obj_obj]
  infer_instance

/-- Outside degrees zero and one the two-factor family has no sections beyond zero.  This is the
local finiteness of the decomposition, read on the rings of sections. -/
theorem subsingleton_twoFactorFamily_of_ne {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ 1)
    (U : (Opens T)ᵒᵖ) :
    Subsingleton ((twoFactorFamily p₀ p₁ R S n).obj.obj U) := by
  rw [twoFactorFamily_of_ne p₀ p₁ R S h0 h1]
  exact subsingleton_zeroRingSheaf_obj _ U

/-- **The ringed space of the witness**: the given topological space, with the product of the
two-factor family as its sheaf of rings. -/
def twoFactorSpace : RingedSpace.{u, u} where
  carrier := T
  presheaf := (∏ᶜ twoFactorFamily p₀ p₁ R S).obj
  IsSheaf := (∏ᶜ twoFactorFamily p₀ p₁ R S).property

/-- The structure sheaf of `twoFactorSpace` *is* the product of the two-factor family, which is
what makes the identification required by `ProductDecomposition` the identity. -/
theorem twoFactorSpace_sheaf :
    (twoFactorSpace p₀ p₁ R S).sheaf = ∏ᶜ twoFactorFamily p₀ p₁ R S :=
  rfl

/-- **The two-factor product decomposition** of the structure sheaf of `twoFactorSpace`.  All
three fields are supplied: the family, the identification — the identity, because the structure
sheaf is the product — and local finiteness on the whole space, only two factors having any
sections. -/
def twoFactorDecomposition : ProductDecomposition (twoFactorSpace p₀ p₁ R S) where
  factor := twoFactorFamily p₀ p₁ R S
  iso := Iso.refl _
  locallyFinite x := ⟨⊤, by simp, by
    refine Set.Finite.subset ((Set.finite_singleton (1 : ℤ)).insert 0) ?_
    intro n hn
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact hn (subsingleton_twoFactorFamily_of_ne p₀ p₁ R S hne.1 hne.2 _)⟩

/-! ### The two factors are not zero -/

/-- Over an open set containing `p₀` the degree-zero factor has nontrivial sections. -/
theorem nontrivial_factor_zero [Nontrivial R] {U : Opens T} (hU : p₀ ∈ U) :
    Nontrivial (((twoFactorDecomposition p₀ p₁ R S).factor 0).obj.obj (op U)) := by
  rw [show (twoFactorDecomposition p₀ p₁ R S).factor 0 = skyscraperRingSheaf p₀ R from
    twoFactorFamily_zero p₀ p₁ R S]
  exact nontrivial_skyscraperRingSheaf_obj p₀ R hU

/-- Over an open set containing `p₁` the degree-one factor has nontrivial sections. -/
theorem nontrivial_factor_one [Nontrivial S] {U : Opens T} (hU : p₁ ∈ U) :
    Nontrivial (((twoFactorDecomposition p₀ p₁ R S).factor 1).obj.obj (op U)) := by
  rw [show (twoFactorDecomposition p₀ p₁ R S).factor 1 = skyscraperRingSheaf p₁ S from
    twoFactorFamily_one p₀ p₁ R S]
  exact nontrivial_skyscraperRingSheaf_obj p₁ S hU

/-- **The degree-zero factor is not `Subsingleton`** over an open set containing `p₀`.  This is
the negation of the property by which the one-factor decomposition discharges every off-diagonal
instance of the orthogonality. -/
theorem not_subsingleton_factor_zero [Nontrivial R] {U : Opens T} (hU : p₀ ∈ U) :
    ¬ Subsingleton (((twoFactorDecomposition p₀ p₁ R S).factor 0).obj.obj (op U)) :=
  haveI := nontrivial_factor_zero p₀ p₁ R S hU
  not_subsingleton _

/-- **The degree-one factor is not `Subsingleton`** over an open set containing `p₁`. -/
theorem not_subsingleton_factor_one [Nontrivial S] {U : Opens T} (hU : p₁ ∈ U) :
    ¬ Subsingleton (((twoFactorDecomposition p₀ p₁ R S).factor 1).obj.obj (op U)) :=
  haveI := nontrivial_factor_one p₀ p₁ R S hU
  not_subsingleton _

/-- If the sections of a factor over the whole space are not subsingleton, the factor, read as
an `𝒪_X`-module, is not a zero object. -/
private theorem not_isZero_toOXMod_unit_of_not_subsingleton {n : ℤ}
    (hn : ¬ Subsingleton (((twoFactorDecomposition p₀ p₁ R S).factor n).obj.obj (op ⊤))) :
    ¬ IsZero (((twoFactorDecomposition p₀ p₁ R S).toOXMod n).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        ((twoFactorDecomposition p₀ p₁ R S).factor n)))) := fun h =>
  hn (Stacks.subsingleton_of_isZero h (op ⊤))

/-- **The degree-zero factor, read as an `𝒪_X`-module, is not a zero object.**  This is the shape
in which the orthogonality statements take the factor, so it is the statement that decides
whether their conclusion is reached for a reason other than one side being zero. -/
theorem not_isZero_toOXMod_unit_zero [Nontrivial R] :
    ¬ IsZero (((twoFactorDecomposition p₀ p₁ R S).toOXMod 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        ((twoFactorDecomposition p₀ p₁ R S).factor 0)))) :=
  not_isZero_toOXMod_unit_of_not_subsingleton p₀ p₁ R S
    (not_subsingleton_factor_zero p₀ p₁ R S (U := ⊤) trivial)

/-- **The degree-one factor, read as an `𝒪_X`-module, is not a zero object.** -/
theorem not_isZero_toOXMod_unit_one [Nontrivial S] :
    ¬ IsZero (((twoFactorDecomposition p₀ p₁ R S).toOXMod 1).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        ((twoFactorDecomposition p₀ p₁ R S).factor 1)))) :=
  not_isZero_toOXMod_unit_of_not_subsingleton p₀ p₁ R S
    (not_subsingleton_factor_one p₀ p₁ R S (U := ⊤) trivial)

/-- The structure sheaf of the space is itself nonzero: a ring homomorphism out of the zero ring
cannot reach a nontrivial ring, and the degree-zero projection is one. -/
theorem not_subsingleton_structureSheaf [Nontrivial R] :
    ¬ Subsingleton ((twoFactorSpace p₀ p₁ R S).sheaf.obj.obj (op (⊤ : Opens T))) := by
  intro h
  let := h
  have h01 : (0 : ((twoFactorSpace p₀ p₁ R S).sheaf.obj.obj (op (⊤ : Opens T)))) = 1 :=
    Subsingleton.elim _ _
  have key := congrArg
    (fun r => (Pi.π (twoFactorFamily p₀ p₁ R S) 0).hom.app (op (⊤ : Opens T)) r) h01
  have hz := map_zero
    (ConcreteCategory.hom ((Pi.π (twoFactorFamily p₀ p₁ R S) 0).hom.app (op (⊤ : Opens T))))
  have ho := map_one
    (ConcreteCategory.hom ((Pi.π (twoFactorFamily p₀ p₁ R S) 0).hom.app (op (⊤ : Opens T))))
  exact @false_of_nontrivial_of_subsingleton _
      (nontrivial_factor_zero p₀ p₁ R S (U := (⊤ : Opens T)) trivial)
    (subsingleton_of_zero_eq_one (hz.symm.trans (key.trans ho)))

/-! ### The degeneracy of the one-factor decomposition, and its failure here -/

/-- A product decomposition is **off-diagonally degenerate** if for every pair of distinct
degrees `m ≠ n` one of the two factors has no sections beyond zero over any open set.  Every
instance of the orthogonality `𝒪_n ⊗ 𝒪_m = 0` formed from such a decomposition holds because one
of the two modules is zero. -/
def OffDiagonallyDegenerate {X : RingedSpace.{u, u}} (D : ProductDecomposition X) : Prop :=
  ∀ m n : ℤ, m ≠ n → ∀ U : Opens X.carrier,
    Subsingleton ((D.factor m).obj.obj (op U)) ∨ Subsingleton ((D.factor n).obj.obj (op U))

/-- **The one-factor decomposition is off-diagonally degenerate**: of two distinct degrees at
most one can be zero, and every factor in a nonzero degree has no sections. -/
theorem offDiagonallyDegenerate_oneFactorDecomposition (X : RingedSpace.{u, u}) :
    OffDiagonallyDegenerate (oneFactorDecomposition X) := by
  intro m n hmn U
  by_cases hm : m = 0
  · exact Or.inr (subsingleton_oneFactorFamily_of_ne X.sheaf (fun hn => hmn (hm.trans hn.symm)) _)
  · exact Or.inl (subsingleton_oneFactorFamily_of_ne X.sheaf hm _)

/-- **The two-factor decomposition is not off-diagonally degenerate**: at the pair `0 ≠ 1`,
over the whole space, both factors have nontrivial sections. -/
theorem not_offDiagonallyDegenerate_twoFactorDecomposition [Nontrivial R] [Nontrivial S] :
    ¬ OffDiagonallyDegenerate (twoFactorDecomposition p₀ p₁ R S) := by
  intro h
  rcases h 0 1 (by decide) ⊤ with h0 | h1
  · exact not_subsingleton_factor_zero p₀ p₁ R S (U := ⊤) trivial h0
  · exact not_subsingleton_factor_one p₀ p₁ R S (U := ⊤) trivial h1

/-! ### A closed instance

Every parameter of the construction is instantiated from declarations that assume nothing, so
there is no inhabitation question left about the datum.
-/

/-- The one-point space. -/
abbrev onePointTop : TopCat.{u} := TopCat.of PUnit.{u + 1}

/-- `ℤ` as an object of `CommRingCat.{u}`. -/
abbrev intRing : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)

/-- The ringed space of the closed instance: one point, with `ℤ × ℤ` as its ring of sections. -/
abbrev witnessSpace : RingedSpace.{u, u} :=
  twoFactorSpace (T := onePointTop.{u}) PUnit.unit PUnit.unit intRing.{u} intRing.{u}

/-- **A product decomposition of a structure sheaf with two nonzero factors**, with nothing
assumed: `ℤ` in degree zero, `ℤ` in degree one, the zero ring elsewhere. -/
abbrev witnessDecomposition : ProductDecomposition witnessSpace.{u} :=
  twoFactorDecomposition (T := onePointTop.{u}) PUnit.unit PUnit.unit intRing.{u} intRing.{u}

/-- Neither factor of `witnessDecomposition` at the pair `0 ≠ 1` is `Subsingleton`. -/
theorem not_subsingleton_witnessDecomposition_factor_zero :
    ¬ Subsingleton ((witnessDecomposition.{u}.factor 0).obj.obj (op ⊤)) :=
  not_subsingleton_factor_zero _ _ _ _ trivial

/-- Neither factor of `witnessDecomposition` at the pair `0 ≠ 1` is `Subsingleton`. -/
theorem not_subsingleton_witnessDecomposition_factor_one :
    ¬ Subsingleton ((witnessDecomposition.{u}.factor 1).obj.obj (op ⊤)) :=
  not_subsingleton_factor_one _ _ _ _ trivial

/-- **`witnessDecomposition` is not off-diagonally degenerate.**  Compare
`offDiagonallyDegenerate_oneFactorDecomposition`, which proves that the one-factor decomposition
is. -/
theorem not_offDiagonallyDegenerate_witnessDecomposition :
    ¬ OffDiagonallyDegenerate witnessDecomposition.{u} :=
  not_offDiagonallyDegenerate_twoFactorDecomposition _ _ _ _

end Stacks.Cohomology.InvertibleDerived.TwoFactorWitness

end
