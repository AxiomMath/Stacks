module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField

/-!
# The residue transcendence degree is additive, and blind to a preimmersion

`Stacks.Chow.residueTrdeg f x` is the transcendence degree of the residue-field extension
`κ(f x) ⊆ κ(x)`. It is additive along a composite, and it vanishes whenever the morphism induces
an isomorphism of residue fields — in particular for a preimmersion, whose residue-field maps are
isomorphisms because its stalk maps are surjective.

Together these two facts replace a transcendence-degree computation by a cancellation: given a
commuting square of morphisms of schemes two of whose sides are preimmersions, the residue
transcendence degrees of the other two sides at corresponding points are equal. That is what
identifies the residue transcendence degree of the generic fibre of `p : X ⟶ Y` with that of `p`
itself, in `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre`.

## Main results

* `Stacks.Chow.relativeDimension_apply_add_residueTrdeg` — the relative dimension is the base value
  plus the residue transcendence degree.
* `Stacks.Chow.residueDegree_comp` — the residue degree is multiplicative along a composite.
* `Stacks.Chow.residueTrdeg_comp` — additivity along a composite.
* `Stacks.Chow.residueTrdeg_eq_zero_of_isIso_residueFieldMap` and
  `Stacks.Chow.residueTrdeg_eq_zero_of_isPreimmersion` — the degree vanishes for a morphism whose
  residue-field map at the point is an isomorphism, and a preimmersion is such a morphism.
* `Stacks.Chow.residueDegree_eq_one_of_isPreimmersion` — a preimmersion has residue degree one
  everywhere, its residue-field maps being surjective by
  `AlgebraicGeometry.surjective_residueFieldMap_of_surjectiveOnStalks`.

## References

* [Stacks Project, Tag 030H](https://stacks.math.columbia.edu/tag/030H)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The relative dimension in terms of the residue transcendence degree -/

/-- `Stacks.Chow.relativeDimension` is the base value plus the residue transcendence degree.
This is `rfl`; it is named so that no proof has to unfold either definition. -/
theorem relativeDimension_apply_add_residueTrdeg {X S : Scheme.{u}} (δ : DimensionFunction S)
    (f : X ⟶ S) (x : X) :
    relativeDimension δ f x = δ (f.base x) + (Cardinal.toNat (residueTrdeg f x) : ℤ) :=
  rfl

/-- A bijective homomorphism of fields has degree one and transcendence degree zero. -/
private theorem finrank_eq_one_and_trdeg_eq_zero_of_bijective {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) (hφ : Function.Bijective φ) :
    let := φ.toAlgebra
    Module.finrank K L = 1 ∧ Algebra.trdeg K L = 0 := by
  let := φ.toAlgebra
  let e : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId _ _) hφ
  exact ⟨e.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self _), e.trdeg_eq.symm.trans
    trdeg_eq_zero⟩

/-- Degree and transcendence degree of a tower of field homomorphisms `K → L → M` with composite
`θ` are multiplicative, respectively additive. -/
private theorem finrank_mul_and_trdeg_add_of_comp_eq {K L M : Type u} [Field K] [Field L]
    [Field M] (φ : K →+* L) (ψ : L →+* M) (θ : K →+* M) (h : ψ.comp φ = θ) :
    let := φ.toAlgebra
    let := ψ.toAlgebra
    let := θ.toAlgebra
    Module.finrank K M = Module.finrank K L * Module.finrank L M ∧
      Algebra.trdeg K M = Algebra.trdeg K L + Algebra.trdeg L M := by
  let := φ.toAlgebra
  let := ψ.toAlgebra
  let := θ.toAlgebra
  have _ : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun a ↦ congrArg (· a) h.symm
  have _ : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective _ _).mpr φ.injective
  have _ : FaithfulSMul L M := (faithfulSMul_iff_algebraMap_injective _ _).mpr ψ.injective
  exact ⟨(Module.finrank_mul_finrank K L M).symm, (trdeg_add_eq K L (A := M)).symm⟩

/-! ### Preimmersions induce isomorphisms of residue fields -/

/-- A preimmersion has residue degree one at every point. -/
theorem residueDegree_eq_one_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : f.residueDegree x = 1 := by
  exact (finrank_eq_one_and_trdeg_eq_zero_of_bijective _
    ⟨RingHom.injective _, AlgebraicGeometry.surjective_residueFieldMap_of_surjectiveOnStalks f x⟩).1

/-! ### The residue degree is multiplicative -/

/-- **The residue degree is multiplicative along a composite.** The residue fields form a tower
`κ(g (f x)) ⊆ κ(f x) ⊆ κ(x)` and the degree of a tower of field extensions is the product of the
degrees. -/
theorem residueDegree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f.base x) * f.residueDegree x := by
  exact (finrank_mul_and_trdeg_add_of_comp_eq _ _ _
    (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x)).symm).1

/-! ### Additivity -/

/-- **The residue transcendence degree is additive along a composite.** This is Stacks 030H for
the tower `κ(g (f x)) ⊆ κ(f x) ⊆ κ(x)`; the two steps are extensions of fields, so both
faithfulness hypotheses hold. -/
theorem residueTrdeg_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    residueTrdeg (f ≫ g) x = residueTrdeg g (f.base x) + residueTrdeg f x := by
  exact (finrank_mul_and_trdeg_add_of_comp_eq _ _ _
    (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x)).symm).2

/-! ### Vanishing -/

/-- A morphism inducing an isomorphism of residue fields at `x` has residue transcendence degree
zero there. -/
theorem residueTrdeg_eq_zero_of_isIso_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hx : IsIso (f.residueFieldMap x)) : residueTrdeg f x = 0 := by
  exact (finrank_eq_one_and_trdeg_eq_zero_of_bijective _
    (ConcreteCategory.bijective_of_isIso (C := CommRingCat) (f.residueFieldMap x))).2

/-- A preimmersion has residue transcendence degree zero at every point. -/
theorem residueTrdeg_eq_zero_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f]
    (x : X) : residueTrdeg f x = 0 :=
  residueTrdeg_eq_zero_of_isIso_residueFieldMap f x (isIso_residueFieldMap_of_isPreimmersion f x)

/-- **Cancellation in a commuting square two of whose sides are preimmersions.** If
`i ≫ p = q ≫ j` with `i` and `j` preimmersions, then `p` and `q` have the same residue
transcendence degree at corresponding points. -/
theorem residueTrdeg_eq_of_comp_eq_comp {F X T Y : Scheme.{u}} (i : F ⟶ X) (p : X ⟶ Y)
    (q : F ⟶ T) (j : T ⟶ Y) [IsPreimmersion i] [IsPreimmersion j]
    (hsq : i ≫ p = q ≫ j) (y : F) :
    residueTrdeg p (i.base y) = residueTrdeg q y := by
  have h := congrArg (fun h : F ⟶ Y ↦ residueTrdeg h y) hsq
  rwa [residueTrdeg_comp i p y, residueTrdeg_comp q j y,
    residueTrdeg_eq_zero_of_isPreimmersion i y,
    residueTrdeg_eq_zero_of_isPreimmersion j (q.base y), add_zero, zero_add] at h

end Stacks.Chow

end
