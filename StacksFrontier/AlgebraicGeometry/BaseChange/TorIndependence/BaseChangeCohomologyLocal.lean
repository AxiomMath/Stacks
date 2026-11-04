module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
import all StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap

/-!
# The cohomology of a derived base change of a complex over a localization

Let `R → A`, `R → R'` be homomorphisms of commutative rings, let `A → A₂` be a further
homomorphism and let `N` be an object of `D(A₂)`. The cohomology
`H^n(N|_R ⊗ᴸ_R R')` of the derived base change of `N` read over `A` carries an action of
`A ⊗_R R'` — `RingTheory.TorIndependence.baseChangeCohomology` — and the left factor acts
through the derived base change of scalar multiplication on `N`. If `s : A` becomes a *unit* in
`A₂`, then multiplication by `s` on `N` is invertible in `D(A₂)`, hence so is its image under any
functor, hence `s` acts invertibly on that cohomology.

In particular, when `A → A₂` is the localization at a prime, every element of `A` outside that
prime acts invertibly: the cohomology of the derived base change of a complex that already lives
over the localization is itself local. That is the half of the affine reduction of Stacks 0DJ8
which says that the pointwise condition (1) at a point of a chart sees only the localized
cohomology — the stalk of `K` being the localization of `RΓ(U, K)` by
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`.

## Main results

* `RingTheory.TorIndependence.isIso_smul_id`: in an `R`-linear category, `r • 𝟙 X` is invertible
  as soon as `r` is a unit.
* `RingTheory.TorIndependence.bijective_includeLeft_smul_baseChangeCohomology`: an element of `A`
  which is a unit in `A₂` acts bijectively on `H^n(N|_R ⊗ᴸ_R R')` for `N` an `A₂`-complex.

## Implementation notes

The identification of the left action with the derived base change of scalar multiplication is
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`, and the identification of
`s • 𝟙` on the restriction of `N` with the restriction of `algebraMap A A₂ s • 𝟙 N` is the
`private` `exactFunctor_scalar` of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap`, reached by
`import all` so that no second copy of it is made.

The model of the derived category is a binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for
each ring, not `HasDerivedCategory.standard`: a statement proved at one model says nothing about
another, and the consumers of Stacks 0DJ8 work at a locally small model.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

universe u w

namespace RingTheory.TorIndependence

/-- In an `R`-linear category, `r • 𝟙 X` is invertible as soon as `r` is a unit: the inverse is
`r⁻¹ • 𝟙 X`. -/
public theorem isIso_smul_id {Rr : Type*} [Ring Rr] {C : Type*} [Category C] [Preadditive C]
    [Linear Rr C] {r : Rr} (hr : IsUnit r) (X : C) : IsIso (r • 𝟙 X) := by
  obtain ⟨v, hv⟩ := hr
  refine ⟨(↑v⁻¹ : Rr) • 𝟙 X, ?_, ?_⟩ <;>
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, ← hv,
      Units.inv_mul, Units.mul_inv, one_smul]

variable {R A A₂ R' : Type u} [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
  [Algebra R A] [Algebra R R'] [Algebra A A₂]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A₂)] [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **An element of `A` which is a unit in `A₂` acts bijectively on the cohomology of the derived
base change of an `A₂`-complex.** The left tensor factor acts by the derived base change of scalar
multiplication, and scalar multiplication by `s` on an `A₂`-complex is invertible as soon as `s`
is a unit in `A₂`; a functor carries that isomorphism to an isomorphism. -/
public theorem bijective_includeLeft_smul_baseChangeCohomology
    (N : DerivedCategory (ModuleCat.{u} A₂)) (n : ℤ) {s : A}
    (hs : IsUnit (algebraMap A A₂ s)) :
    Function.Bijective
      (fun m : baseChangeCohomology (R := R) (R' := R')
          ((ModuleCat.restrictScalars (algebraMap A A₂)).mapDerivedCategory.obj N) n =>
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) s : A ⊗[R] R') • m) := by
  set K := (ModuleCat.restrictScalars (algebraMap A A₂)).mapDerivedCategory.obj N with hK
  set T := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R') with hT
  set G := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory ⋙
    T.functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n with hG
  have hsmul : (ModuleCat.restrictScalars (algebraMap A A₂)).mapDerivedCategory.map
      (algebraMap A A₂ s • 𝟙 N) = s • 𝟙 K := by
    refine exactFunctor_scalar (ModuleCat.restrictScalars (algebraMap A A₂))
      (algebraMap A A₂ s) s (fun M => ?_) N
    ext m
    rfl
  have hiso : IsIso (G.map (s • 𝟙 K)) := by
    rw [← hsmul]
    have : IsIso (algebraMap A A₂ s • 𝟙 N) := isIso_smul_id hs N
    exact Functor.map_isIso _ _
  have hfun : (fun m : baseChangeCohomology (R := R) (R' := R') K n =>
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) s : A ⊗[R] R') • m) =
      fun m => (G.map (s • 𝟙 K)).hom m := by
    funext m
    exact baseChangeCohomology_includeLeft_smul (R := R) (R' := R') K n s m
  rw [hfun]
  exact (ConcreteCategory.isIso_iff_bijective (f := G.map (s • 𝟙 K))).mp hiso

end RingTheory.TorIndependence

end
