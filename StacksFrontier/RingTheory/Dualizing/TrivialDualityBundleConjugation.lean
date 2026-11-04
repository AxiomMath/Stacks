module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModuleExtTotalBase
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.CategoryTheory.Functor.Derived.PrecompQuotient
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.RingTheory.Dualizing.BaseRingAbsoluteTensorNatural
public import StacksFrontier.RingTheory.Dualizing.DerivedHomPerfectTensor
public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolutionCompact

/-!
# The differential graded tensor factor is the change-of-rings tensor factor of Tag 06Y6

`Dualizing.derivedTensorBimoduleFunctor M` is the derived tensor product with a differential
graded `(R, A)`-bimodule `M`, read on the derived categories of `R`-modules and of `A`-modules
through `DifferentialGradedModule.degreeZeroDerivedEquivalence`. This file identifies it with
the derived change-of-rings tensor product of Stacks 06Y6,
`CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings`.

The identification is a conjugation of left derived functors by the degree-zero equivalence.
Both functors are total left derived functors of one and the same functor on cochain complexes
of `R`-modules:

* on the differential graded side, ordinary tensoring with `M` followed by the localization is
  left derivable (Tag 09LS, `DifferentialGraded.Bimodule.derivedTensorFunctor`), and that
  statement transfers from the homotopy category of differential graded modules to the modules
  themselves, where the degree-zero equivalence applies;
* the two sources are identified by the quasi-inverse
  `DifferentialGradedModule.degreeZeroTotalFunctor R R` of the degree-zero equivalence at the
  base ring, through `CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp`;
* the functors being derived are identified by
  `DifferentialGraded.absExtTensorRightTotalNatIso` — the chain-level comparison of Tag 06Y6 —
  composed with `Dualizing.baseAbsBalanceNatIso`, which replaces the relative tensor product of
  Tag 09LM by the absolute one.

Uniqueness of right Kan extensions then gives the isomorphism.

## Main results

* `Dualizing.quasiIso_eq_inverseImage_degreeZeroTotal` and
  `Dualizing.degreeZeroTotalLocalizerMorphism`: the quasi-isomorphisms of complexes of
  `R`-modules are the inverse image, along the total-direct-sum functor, of the class of
  morphisms the differential graded localization inverts; so that functor is a morphism of
  localizers, and a localized equivalence.
* `Dualizing.derivedTensorBimoduleFunctorIsoCanonical`: **the derived tensor product
  with a differential graded bimodule over the base ring is the derived change-of-rings tensor
  product of Tag 06Y6 with its complex of homogeneous components.**
* `Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical`: the same, as a proposition.

## Implementation notes

The whole file runs under `letI := f.toAlgebra` for a bare ring homomorphism `f : R →+* A`,
because `CochainComplex.extendScalarsLarge` builds the algebra structure from `f` itself and the
chain-level comparison `DifferentialGraded.absExtTensorRightIso` holds by `rfl` only there. A
consumer holding an ambient `[Algebra R A]` whose structure map is `f` can rewrite its instance
to `f.toAlgebra` by `Algebra.algebra_ext`, since an algebra structure is determined by its
structure homomorphism.

Composition of functors is associative by `rfl`, so no associators appear in the isomorphisms
built below; the ones that do appear are forced by the statements of the Mathlib lemmas being
applied.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) is the derived
  change-of-rings tensor product.
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) is the derived tensor
  product of differential graded modules.
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor
open DifferentialGraded DifferentialGradedModule

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### The total-direct-sum functor as a morphism of localizers -/

section Localizer

variable (R : Type u) [CommRing R]

/-- **The quasi-isomorphisms of complexes of `R`-modules are inverse-image-induced along the
total-direct-sum functor.** Taking the direct sum of the terms of a complex and then its
homogeneous components again is the identity, by
`DifferentialGradedModule.degreeZeroComplexNatIso`, so a morphism of complexes is a
quasi-isomorphism exactly when its image is. -/
theorem quasiIso_eq_inverseImage_degreeZeroTotal :
    HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) =
      ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
          (degreeZeroComponentFunctor R R)).inverseImage (degreeZeroTotalFunctor R R) := by
  ext K L φ
  exact ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).arrow_mk_iso_iff
    (Arrow.isoMk (degreeZeroComplexNatIso.app K) (degreeZeroComplexNatIso.app L)
      (degreeZeroComplexNatIso.hom.naturality φ).symm)).symm

/-- The total-direct-sum functor `DifferentialGradedModule.degreeZeroTotalFunctor R R` from
complexes of `R`-modules to differential graded modules over the base ring is an equivalence. -/
instance degreeZeroTotalFunctor_isEquivalence :
    (degreeZeroTotalFunctor R R).IsEquivalence :=
  inferInstanceAs (degreeZeroEquivalence (R := R) (A := R)).inverse.IsEquivalence

/-- **The total-direct-sum functor at the base ring is a morphism of localizers**, from the
quasi-isomorphisms of complexes of `R`-modules to the class of morphisms of differential graded
modules whose complexes of homogeneous components are quasi-isomorphisms. -/
def degreeZeroTotalLocalizerMorphism :
    LocalizerMorphism (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
        (degreeZeroComponentFunctor R R)) :=
  LocalizerMorphism.ofEq (quasiIso_eq_inverseImage_degreeZeroTotal R)

/-- The functor of `Dualizing.degreeZeroTotalLocalizerMorphism R` is an equivalence. -/
instance : (degreeZeroTotalLocalizerMorphism R).functor.IsEquivalence :=
  degreeZeroTotalFunctor_isEquivalence R

/-- The quasi-isomorphisms of complexes of `R`-modules are the inverse image of the target class
of `Dualizing.degreeZeroTotalLocalizerMorphism R` along its functor. -/
instance : (degreeZeroTotalLocalizerMorphism R).IsInduced :=
  ⟨(quasiIso_eq_inverseImage_degreeZeroTotal R).symm⟩

/-- `Dualizing.degreeZeroTotalLocalizerMorphism R` is a localized equivalence. -/
instance : (degreeZeroTotalLocalizerMorphism R).IsLocalizedEquivalence :=
  LocalizerMorphism.isLocalizedEquivalence_of_isInduced _

end Localizer

/-! ### The conjugation -/

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **The derived tensor product with a differential graded bimodule over the base ring is the
derived change-of-rings tensor product of Tag 06Y6.** For a differential graded
`(R, A)`-bimodule `M` over the base ring placed in degree zero, the functor
`Dualizing.derivedTensorBimoduleFunctor M : D(R) ⥤ D(A)` is isomorphic to the canonical derived
change-of-rings tensor product of Stacks 06Y6 with the complex of homogeneous components of the
right differential graded module of `M`.

Both are total left derived functors of the same functor along `DerivedCategory.Q`, so they are
isomorphic by uniqueness of right Kan extensions. -/
def derivedTensorBimoduleFunctorIsoCanonical (f : R →+* A) :
    letI := f.toAlgebra
    ∀ M : Bimodule (baseAlgebra R) (DifferentialGradedAlgebra.degreeZero R A),
      derivedTensorBimoduleFunctor M ≅
        (canonicalDerivedTensorChangeOfRings.{u, u, u} f
          (degreeZeroComplex M.rightModule)).F := by
  letI := f.toAlgebra
  intro M
  let W₁ := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let W₂ := W₁.inverseImage (degreeZeroComponentFunctor R R)
  let Φ := degreeZeroTotalLocalizerMorphism R
  let Kq := toHomotopyCategory (baseAlgebra R)
  let Lq := (quasiIsomorphisms' (baseAlgebra R)).Q
  let E := (degreeZeroDerivedEquivalence (R := R) (A := A)).functor
  let G := (degreeZeroDerivedEquivalence (R := R) (A := R)).inverse
  let LF₂ := Bimodule.derivedTensorFunctor M ⋙ E
  let α' : Lq ⋙ LF₂ ⟶ Bimodule.tensorFunctorToDerivedCategory M ⋙ E :=
    (Functor.associator Lq (Bimodule.derivedTensorFunctor M) E).inv ≫
      Functor.whiskerRight (Bimodule.derivedTensorFunctorCounit M) E
  haveI : LF₂.IsLeftDerivedFunctor α' (quasiIsomorphisms' (baseAlgebra R)) :=
    Functor.isLeftDerivedFunctor_comp_of_resolutions (quasiIsomorphisms' (baseAlgebra R))
      (Bimodule.derivedTensorFunctorCounit M) E
      (exists_resolution_map_bijective (baseAlgebra R))
  haveI : (Kq ⋙ Lq).IsLocalization W₂ := degreeZero_localization (R := R) (A := R)
  let α₂ : (Kq ⋙ Lq) ⋙ LF₂ ⟶ Kq ⋙ Bimodule.tensorFunctorToDerivedCategory M ⋙ E :=
    (Functor.associator Kq Lq LF₂).hom ≫ Functor.whiskerLeft Kq α'
  haveI : LF₂.IsLeftDerivedFunctor α₂ W₂ :=
    Functor.isLeftDerivedFunctor_precomp_whiskering Kq LF₂ α'
      (quasiIsomorphisms' (baseAlgebra R)) W₂
  let iso : Φ.functor ⋙ (Kq ⋙ Lq) ≅ DerivedCategory.Q ⋙ G :=
    (degreeZeroDerivedFactorization (R := R) (A := R)).symm
  let β : Kq ⋙ Bimodule.tensorFunctorToDerivedCategory M ⋙ E ≅
      Bimodule.tensorCompFunctor M ⋙ degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (Bimodule.tensorCompFunctor_quotient M).symm
        ((quasiIsomorphisms' (DifferentialGradedAlgebra.degreeZero R A)).Q ⋙ E) ≪≫
      Functor.isoWhiskerLeft (Bimodule.tensorCompFunctor M) degreeZeroDerivedComponentIso
  let F₁ : CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} A) :=
    (extendScalarsLarge.{u, u, u} f ⋙
      tensorRightLarge.{u, u} (degreeZeroComplex M.rightModule)) ⋙ DerivedCategory.Q
  let e₁ : Φ.functor ⋙ (Kq ⋙ Bimodule.tensorFunctorToDerivedCategory M ⋙ E) ≅ F₁ :=
    Functor.isoWhiskerLeft (degreeZeroTotalFunctor R R) β ≪≫
      Functor.isoWhiskerLeft (degreeZeroTotalFunctor R R)
        (Functor.isoWhiskerRight
          (baseAbsBalanceNatIso (DifferentialGradedAlgebra.degreeZero R A) M)
          (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q)) ≪≫
      Functor.isoWhiskerRight (absExtTensorRightTotalNatIso f M.rightModule) DerivedCategory.Q
  let e₂ : G ⋙ LF₂ ≅ derivedTensorBimoduleFunctor M := Iso.refl _
  let α₁ : DerivedCategory.Q ⋙ derivedTensorBimoduleFunctor M ⟶ F₁ :=
    Functor.whiskerLeft DerivedCategory.Q e₂.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight iso.inv LF₂ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Φ.functor α₂ ≫ e₁.hom
  haveI : (derivedTensorBimoduleFunctor M).IsLeftDerivedFunctor α₁ W₁ :=
    (Φ.isLeftDerivedFunctor_iff_precomp DerivedCategory.Q (Kq ⋙ Lq) G iso α₁ α₂ e₁ e₂
      rfl).mp inferInstance
  let T := canonicalDerivedTensorChangeOfRings.{u, u, u} f (degreeZeroComplex M.rightModule)
  haveI := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (derivedTensorBimoduleFunctor M) α₁ W₁
  haveI := Functor.IsLeftDerivedFunctor.isRightKanExtension T.F T.directCounit W₁
  exact Functor.rightKanExtensionUnique _ α₁ T.F T.directCounit

/-- **The derived tensor product with a differential graded bimodule over the base ring is the
derived change-of-rings tensor product of Tag 06Y6.** For a differential graded
`(R, A)`-bimodule `M` over the base ring placed in degree zero, the functor
`Dualizing.derivedTensorBimoduleFunctor M : D(R) ⥤ D(A)` is isomorphic to the canonical derived
change-of-rings tensor product of Stacks 06Y6 with the complex of homogeneous components of the
right differential graded module of `M`.

This is `Dualizing.derivedTensorBimoduleFunctorIsoCanonical`, read as a proposition. -/
theorem nonempty_derivedTensorBimoduleFunctor_iso_canonical (f : R →+* A) :
    letI := f.toAlgebra
    ∀ M : Bimodule (baseAlgebra R) (DifferentialGradedAlgebra.degreeZero R A),
      Nonempty (derivedTensorBimoduleFunctor M ≅
        (canonicalDerivedTensorChangeOfRings.{u, u, u} f
          (degreeZeroComplex M.rightModule)).F) := by
  let := f.toAlgebra
  exact fun M => ⟨derivedTensorBimoduleFunctorIsoCanonical f M⟩

end Dualizing

end
