module

public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass

/-!
# Evaluating a cotangent obstruction class at an ambient tower

The first clause of `Deformation.Artin.IsCotangentObstructionClass` says that at every
square-zero thickening `A' → A` of the base there *exists* a ring map `f : Λ → A'` making
`Λ → A' → A` a tower over the chosen affine open of `S`, and that for the algebra structures
built from `f` and from the surjection `A' → A` the evaluation of the class is the obstruction
element of the thickening. A consumer of the class, however, usually arrives with algebra
instances `[Algebra Λ A']`, `[Algebra A' A]` and `[IsScalarTower Λ A' A]` already in place —
for instance because `A'` was produced as a `Λ`-algebra in the first place — and needs the
same conclusion for *those* instances.

The ring map in the existential is forced: the affine open `Spec Λ ⟶ S` of the dual
deformation situation is an open immersion, hence a monomorphism, so two ring maps `Λ → A'`
whose spectra compose with it to the same structure morphism of `Spec A'` have equal spectra,
and `Spec` is faithful. Once the map is known to be the ambient `algebraMap Λ A'`, the two
algebra structures have the same structure map and are therefore equal by
`Algebra.algebra_ext`, so the conclusion transports.

## Main results

* `Deformation.Artin.eq_algebraMap_of_comp_affineOpen` — the ring map `Λ → A'` over the
  affine open of the base is unique.
* `Deformation.Artin.obstructionEvaluation_heq_obstruction_of_ambient` — the evaluation of a
  cotangent obstruction class at a square-zero thickening, computed with ambient algebra
  instances, is the obstruction element of the thickening.
* `Deformation.Artin.obstructionEvaluation_eq_obstruction_of_tower` — the same, without a cast,
  at the thickening determined by a tower `Λ → A' → A`.
* `Deformation.Artin.nonempty_underFiber_iff_obstructionEvaluation_eq_zero` — consequently
  the object lifts along the thickening exactly when the evaluation vanishes.

## References

* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- **The base ring map of a square-zero thickening is unique.** Two ring maps `Λ → A'` whose
spectra compose with an open immersion `Spec Λ ⟶ S` to the same morphism agree: the open
immersion is a monomorphism, so the two spectra agree, and `Spec` is faithful. -/
public theorem eq_algebraMap_of_comp_affineOpen {Λ A' : Type u} [CommRing Λ] [CommRing A']
    {S : Scheme.{u}} {affineOpen : Spec (.of Λ) ⟶ S} (hopen : IsOpenImmersion affineOpen)
    {g : Spec (.of A') ⟶ S} (f₁ f₂ : Λ →+* A')
    (h₁ : Spec.map (CommRingCat.ofHom f₁) ≫ affineOpen = g)
    (h₂ : Spec.map (CommRingCat.ofHom f₂) ≫ affineOpen = g) :
    f₁ = f₂ := by
  have := hopen
  exact CommRingCat.hom_ext_iff.1
    (Spec.map_injective ((cancel_mono affineOpen).1 (h₁.trans h₂.symm)))

section Ambient

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)
variable (ξ : (derivedTensorCohomology A sit.K 1).obj (derivedNaiveCotangentComplex Λ A))

/-- The transport of the first clause of `Deformation.Artin.IsCotangentObstructionClass`
across equalities of algebra structures. -/
public theorem obstructionEvaluation_eq_zero_iff_aux (A' : Type u) [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') (f : Λ →+* A')
    (hf : D.q.comp f = algebraMap Λ A)
    (heq :
      letI : Algebra Λ A' := f.toAlgebra
      letI : Algebra A' A := D.q.toAlgebra
      letI : IsScalarTower Λ A' A :=
        IsScalarTower.of_algebraMap_eq fun r =>
          (congrArg (fun g : Λ →+* A => g r) hf).symm
      obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1
          D.squareZeroSurjection.2 ξ = sit.obstruction A' D)
    [i : Algebra Λ A'] (hi : i = f.toAlgebra)
    [j : Algebra A' A] (hj : j = D.q.toAlgebra)
    [IsScalarTower Λ A' A] (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    obstructionEvaluation Λ A' A sit.K hsurj hsq ξ = 0 ↔ sit.obstruction A' D = 0 := by
  subst hi
  subst hj
  exact ⟨fun h => heq.symm.trans h, fun h => heq.trans h⟩

/-- The same transport as `Deformation.Artin.obstructionEvaluation_eq_zero_iff_aux`, stated as
an equality of the two elements. It is a heterogeneous equality because the kernel of the
ambient structure map and the kernel of the surjection of the thickening are equal only
propositionally, so the two sides a priori live in different cohomology groups. -/
public theorem obstructionEvaluation_heq_obstruction_aux (A' : Type u) [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') (f : Λ →+* A')
    (hf : D.q.comp f = algebraMap Λ A)
    (heq :
      letI : Algebra Λ A' := f.toAlgebra
      letI : Algebra A' A := D.q.toAlgebra
      letI : IsScalarTower Λ A' A :=
        IsScalarTower.of_algebraMap_eq fun r =>
          (congrArg (fun g : Λ →+* A => g r) hf).symm
      obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1
          D.squareZeroSurjection.2 ξ = sit.obstruction A' D)
    [i : Algebra Λ A'] (hi : i = f.toAlgebra)
    [j : Algebra A' A] (hj : j = D.q.toAlgebra)
    [IsScalarTower Λ A' A] (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    HEq (obstructionEvaluation Λ A' A sit.K hsurj hsq ξ) (sit.obstruction A' D) := by
  subst hi
  subst hj
  exact heq_of_eq heq

variable (hξ : IsCotangentObstructionClass Λ A B S hS toS hA X p sit ξ)

include hξ

/-- The vanishing criterion and the heterogeneous equality of the evaluation with the obstruction
element, both obtained from the existential clause of `hξ` once the ring map is identified. -/
private theorem obstructionEvaluation_iff_and_heq_of_ambient (A' : Type u)
    [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A') [Algebra Λ A'] [Algebra A' A]
    [IsScalarTower Λ A' A] (hmap : algebraMap A' A = D.q)
    (hchart : Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ sit.affineOpen =
      B.inclusion.map D.toS')
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    (obstructionEvaluation Λ A' A sit.K hsurj hsq ξ = 0 ↔ sit.obstruction A' D = 0) ∧
      HEq (obstructionEvaluation Λ A' A sit.K hsurj hsq ξ) (sit.obstruction A' D) := by
  obtain ⟨hev, -⟩ := hξ
  obtain ⟨f, hfS, hf, heq⟩ := hev A' D
  obtain rfl := eq_algebraMap_of_comp_affineOpen sit.openImmersion f (algebraMap Λ A') hfS hchart
  have hi : (inferInstance : Algebra Λ A') = _ := toAlgebra_algebraMap.symm
  have hj : (inferInstance : Algebra A' A) = D.q.toAlgebra := by rw [← hmap, toAlgebra_algebraMap]
  exact ⟨by apply obstructionEvaluation_eq_zero_iff_aux <;> assumption,
    by apply obstructionEvaluation_heq_obstruction_aux <;> assumption⟩

/-- **The evaluation of a cotangent obstruction class, for ambient algebra instances.** If
`A'` carries algebra structures making `Λ → A' → A` a tower whose base map realises the chart
`Spec A' ⟶ S` of the thickening `D`, and whose map `A' → A` is the surjection of `D`, then the
obstruction element of `D` vanishes exactly when the evaluation of the class at the ambient
tower does. -/
public theorem obstructionEvaluation_eq_zero_iff_obstruction_eq_zero (A' : Type u)
    [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A') [Algebra Λ A'] [Algebra A' A]
    [IsScalarTower Λ A' A] (hmap : algebraMap A' A = D.q)
    (hchart : Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ sit.affineOpen =
      B.inclusion.map D.toS')
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    obstructionEvaluation Λ A' A sit.K hsurj hsq ξ = 0 ↔ sit.obstruction A' D = 0 :=
  (obstructionEvaluation_iff_and_heq_of_ambient Λ A B S hS toS hA X p sit ξ hξ A' D
    hmap hchart hsurj hsq).1

/-- **The evaluation of a cotangent obstruction class is the obstruction element.** Same
hypotheses as `Deformation.Artin.obstructionEvaluation_eq_zero_iff_obstruction_eq_zero`,
stated as the equality of the two elements; it is heterogeneous because the two sides live in
`H²(K ⊗ᴸ ker (algebraMap A' A))` and `H²(K ⊗ᴸ ker D.q)` respectively, which `hmap` identifies
only propositionally. -/
public theorem obstructionEvaluation_heq_obstruction_of_ambient (A' : Type u)
    [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A') [Algebra Λ A'] [Algebra A' A]
    [IsScalarTower Λ A' A] (hmap : algebraMap A' A = D.q)
    (hchart : Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ sit.affineOpen =
      B.inclusion.map D.toS')
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    HEq (obstructionEvaluation Λ A' A sit.K hsurj hsq ξ) (sit.obstruction A' D) :=
  (obstructionEvaluation_iff_and_heq_of_ambient Λ A B S hS toS hA X p sit ξ hξ A' D
    hmap hchart hsurj hsq).2

/-- **The evaluation of a cotangent obstruction class at an ambient tower.** For a tower
`Λ → A' → A` whose second map is a square-zero surjection and whose `Spec A'` lies in the
site, the evaluation of the class at the thickening
`Deformation.Artin.squareZeroThickeningOfTower` the tower determines is the obstruction
element of that thickening. This is the cast-free form of
`Deformation.Artin.obstructionEvaluation_heq_obstruction_of_ambient`. -/
public theorem obstructionEvaluation_eq_obstruction_of_tower (A' : Type u) [CommRing A']
    [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    (hA' : B.Contains (Spec (.of A')))
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    obstructionEvaluation Λ A' A sit.K hsurj hsq ξ =
      sit.obstruction A' (squareZeroThickeningOfTower Λ A B S hS toS hA sit.affineOpen
        sit.factorization A' hA' hsurj hsq) :=
  eq_of_heq (obstructionEvaluation_heq_obstruction_of_ambient Λ A B S hS toS hA X p sit ξ hξ A'
    (squareZeroThickeningOfTower Λ A B S hS toS hA sit.affineOpen sit.factorization A' hA'
      hsurj hsq) rfl rfl hsurj hsq)

/-- **Lifting along a square-zero thickening, for ambient algebra instances.** The object of
the dual deformation situation lifts along the thickening `D` exactly when the evaluation of
a cotangent obstruction class at the ambient tower `Λ → A' → A` vanishes. -/
public theorem nonempty_underFiber_iff_obstructionEvaluation_eq_zero (A' : Type u)
    [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A') [Algebra Λ A'] [Algebra A' A]
    [IsScalarTower Λ A' A] (hmap : algebraMap A' A = D.q)
    (hchart : Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ sit.affineOpen =
      B.inclusion.map D.toS')
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    Nonempty ((Under.post p).Fiber (Under.mk (eqToHom sit.hx ≫ D.arrow))) ↔
      obstructionEvaluation Λ A' A sit.K hsurj hsq ξ = 0 :=
  (sit.obstruction_iff_lift A' D).trans
    (obstructionEvaluation_eq_zero_iff_obstruction_eq_zero Λ A B S hS toS hA X p sit ξ hξ
      A' D hmap hchart hsurj hsq).symm

end Ambient

end Deformation.Artin

end
