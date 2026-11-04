module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange

/-!
# The base change map for étale cohomology with coefficients in a ring, on unbounded complexes

Let `Λ` be a commutative ring and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. This file constructs the canonical base change map
$$
g^{-1} Rf_* \longrightarrow Rf'_* (g')^{-1}
$$
of functors `D(X_étale, Λ) ⥤ D(Y'_étale, Λ)` on the unbounded derived categories of sheaves of
`Λ`-modules for the small étale topology ([Stacks, Tag 0A2A] with the constant sheaf of rings
`Λ` in place of `ℤ`).

The construction is the one of `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`, at
module coefficients: the underived comparison `f_* ⋙ g^{-1} ⟶ (g')^{-1} ⋙ f'_*`
(`Stacks.EtaleCohomology.etaleModuleBaseChange`) is the mate of the identification of the two
composite inverse images around the square; it is applied degreewise to unbounded complexes,
followed by the derived-functor unit of `Rf'_*`, and the result is descended along the universal
property of `Rf_* ⋙ g^{-1}` as a right derived functor of degreewise `f_* ⋙ g^{-1}`. That
universal property holds because `g^{-1}` on derived categories is a left adjoint
(`Stacks.EtaleCohomology.etaleModuleDerivedInverseImageAdj`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleComplexBaseChangeUnbounded` — the underived comparison
  applied degreewise to unbounded complexes.
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded` — the base change map
  `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on `D(X_étale, Λ)`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded_fac` characterizes the base
  change map on every unbounded complex `K`: precomposed with `g^{-1}` of the derived-functor
  unit of `Rf_*` at `K`, it is the exactness comparison of `g^{-1}`, the degreewise comparison,
  the derived-functor unit of `Rf'_*` and the exactness comparison of `(g')^{-1}`. This
  determines the map.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isKInjective` and
  `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_injective`: the base
  change map is invertible at a K-injective complex at whose terms the underived comparison is
  invertible, and whose inverse image computes `Rf'_*`.

## Implementation notes

The derived direct images are `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`,
total right derived functors along the localization `DerivedCategory.Q` of cochain complexes, in
the model `HasDerivedCategory.standard` in which they are defined.

The construction is written out at the étale functors rather than obtained from an abstract
statement about a square of abelian categories: an abstract statement receives the zero morphisms
of sheaves of modules, and the universe levels of their categories, in a spelling different from
the one of the units of the derived direct images, and reconciling the two spellings in a
statement about components exceeds the kernel's budget. Here every term is built from the units
and the underived comparison themselves, and the abstract lemmas used (`Functor.rightDerivedDesc`
and its factorization) are about functors between arbitrary categories.

The degreewise comparison is defined on functors between categories of cochain complexes spelled
as `CochainComplex`, the form of the complexes it is applied to: writing the complex shape
`ComplexShape.up ℤ` explicitly gives its instance arguments another spelling, which the kernel
reconciles with the one inside `CochainComplex` only at great cost.

`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange` is the same construction on the bounded
below derived categories `D⁺`.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/-- A natural transformation applied degreewise is invertible at a complex at whose terms it is
invertible. Stated for abstract categories, so that its instances never reduce the components. -/
theorem isIso_natTrans_mapHomologicalComplex_app {ι : Type*} {V W : Type*} [Category* V]
    [Category* W] [HasZeroMorphisms V] [HasZeroMorphisms W] {F G : V ⥤ W}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G) (c : ComplexShape ι)
    (K : HomologicalComplex V c) (h : ∀ i, IsIso (α.app (K.X i))) :
    IsIso ((NatTrans.mapHomologicalComplex α c).app K) :=
  have (i : ι) : IsIso (((NatTrans.mapHomologicalComplex α c).app K).f i) := h i
  HomologicalComplex.Hom.isIso_of_components _

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [CommRing Λ] {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g)

/-- The derived inverse image `g^{-1}` on unbounded derived categories of sheaves of
`Λ`-modules is a left adjoint, its right adjoint being the derived direct image `Rg_*`. -/
instance : (etaleModuleDerivedInverseImage.{u, r} Λ g).IsLeftAdjoint :=
  (etaleModuleDerivedInverseImageAdj.{u, r} Λ g).isLeftAdjoint

/-- The underived base change comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` applied degreewise to
unbounded complexes of sheaves of `Λ`-modules. -/
def etaleModuleComplexBaseChangeUnbounded :
    ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _ ⋙
        (etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) ⟶
      ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _ ⋙
        (etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomologicalComplex (etaleModuleBaseChange.{u, r} Λ f f' g g' h.symm) _ ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv

/-- The degreewise base change comparison is invertible at a complex at which the underived
comparison applied degreewise is: the two differ by the identifications of the action of a
composite of functors with the composite of the actions. -/
theorem isIso_etaleModuleComplexBaseChangeUnbounded_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (hK : IsIso ((NatTrans.mapHomologicalComplex
      (etaleModuleBaseChange.{u, r} Λ f f' g g' h.symm) _).app K)) :
    IsIso ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app K) := by
  have hdef : etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h =
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
        NatTrans.mapHomologicalComplex (etaleModuleBaseChange.{u, r} Λ f f' g g' h.symm) _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :=
    rfl
  have happ := (congrArg (fun t ↦ NatTrans.app t K) hdef).trans
    ((NatTrans.comp_app _ _ K).trans (congrArg (fun t ↦ _ ≫ t) (NatTrans.comp_app _ _ K)))
  exact happ ▸ inferInstance

/-- The degreewise base change comparison is invertible at a complex at whose terms the
underived comparison is invertible. -/
theorem isIso_etaleModuleComplexBaseChangeUnbounded_app_of_forall
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (hK : ∀ k : ℤ, IsIso ((etaleModuleBaseChange.{u, r} Λ f f' g g' h.symm).app (K.X k))) :
    IsIso ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app K) :=
  isIso_etaleModuleComplexBaseChangeUnbounded_app Λ f g g' f' h K
    (isIso_natTrans_mapHomologicalComplex_app _ _ K hK)

/-- The derived-functor unit exhibiting `Rf_* ⋙ g^{-1}` as a right derived functor of
degreewise `f_*` followed by `g^{-1}`: the unit of `Rf_*` whiskered with `g^{-1}`. -/
abbrev etaleModuleDerivedBaseChangeUnboundedUnit :
    ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ etaleModuleDerivedInverseImage.{u, r} Λ g ⟶
      DerivedCategory.Q ⋙ (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedInverseImage.{u, r} Λ g) :=
  Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
      (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫ (Functor.associator _ _ _).hom

/-- The transformation that the universal property of `Rf_* ⋙ g^{-1}` descends: the exactness
comparison of `g^{-1}`, the degreewise base change comparison, the derived-functor unit of
`Rf'_*`, and the exactness comparison of `(g')^{-1}`. -/
def etaleModuleDerivedBaseChangeUnboundedBeta :
    ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ etaleModuleDerivedInverseImage.{u, r} Λ g ⟶
      DerivedCategory.Q ⋙ (etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f') :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _)
      (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h)
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _)
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f') ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors.inv
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f') ≫
    (Functor.associator _ _ _).hom

/-- **The base change map** `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on the unbounded derived categories
of sheaves of `Λ`-modules for the small étale topology, attached to a commutative square
`g' ≫ f = f' ≫ g` of schemes ([Stacks, Tag 0A2A] with coefficients `Λ`). -/
def etaleModuleDerivedBaseChangeUnbounded :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedInverseImage.{u, r} Λ g ⟶
      etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f' :=
  (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
      etaleModuleDerivedInverseImage.{u, r} Λ g).rightDerivedDesc
    (etaleModuleDerivedBaseChangeUnboundedUnit.{u, r} Λ f g)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))
    (etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f')
    (etaleModuleDerivedBaseChangeUnboundedBeta.{u, r} Λ f g g' f' h)

/-- The component of the derived-functor unit of `Rf_* ⋙ g^{-1}` is `g^{-1}` applied to the
component of the unit of `Rf_*`. -/
theorem etaleModuleDerivedBaseChangeUnboundedUnit_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedBaseChangeUnboundedUnit.{u, r} Λ f g).app K =
      (etaleModuleDerivedInverseImage.{u, r} Λ g).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) := by
  simp [etaleModuleDerivedBaseChangeUnboundedUnit]

/-- The component of the transformation being descended, written out. -/
theorem etaleModuleDerivedBaseChangeUnboundedBeta_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedBaseChangeUnboundedBeta.{u, r} Λ f g g' f' h).app K =
      (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _).obj K) ≫
        DerivedCategory.Q.map
          ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
          (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').map
          ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors.inv.app K) := by
  simp [etaleModuleDerivedBaseChangeUnboundedBeta]

/-- **The characterization of the base change map on unbounded complexes.** For every complex
`K` of sheaves of `Λ`-modules on `X_étale`, the base change map at `K`, precomposed with `g^{-1}`
of the derived-functor unit of `Rf_*` at `K`, is the exactness comparison of `g^{-1}`, followed
by the degreewise base change comparison, the derived-functor unit of `Rf'_*` and the exactness
comparison of `(g')^{-1}`. -/
theorem etaleModuleDerivedBaseChangeUnbounded_fac
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedInverseImage.{u, r} Λ g).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) ≫
      (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' h).app
        (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
        (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').map
        ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors.inv.app K) := by
  have hfac : (etaleModuleDerivedBaseChangeUnboundedUnit.{u, r} Λ f g).app K ≫
      (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' h).app (DerivedCategory.Q.obj K) =
        (etaleModuleDerivedBaseChangeUnboundedBeta.{u, r} Λ f g g' f' h).app K :=
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
      etaleModuleDerivedInverseImage.{u, r} Λ g).rightDerived_fac_app
    (etaleModuleDerivedBaseChangeUnboundedUnit.{u, r} Λ f g)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))
    (etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f')
    (etaleModuleDerivedBaseChangeUnboundedBeta.{u, r} Λ f g g' f' h) K
  rw [etaleModuleDerivedBaseChangeUnboundedUnit_app,
    etaleModuleDerivedBaseChangeUnboundedBeta_app] at hfac
  exact hfac

/-- **The base change map is invertible at a K-injective complex `I`** at which the degreewise
comparison is invertible (for instance because the underived comparison is invertible at every
term of `I`, `isIso_etaleModuleComplexBaseChangeUnbounded_app_of_forall`), and whose inverse
image `(g')^{-1} I` computes `Rf'_*`: in `etaleModuleDerivedBaseChangeUnbounded_fac` every other
factor is an isomorphism, `I` computing `Rf_*` because it is K-injective. -/
theorem isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isKInjective
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hI : I.IsKInjective)
    (hbc : IsIso ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' h).app I))
    (hunit : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
      (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :
    IsIso ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' h).app
      (DerivedCategory.Q.obj I)) := by
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f I hI
  have hfac := etaleModuleDerivedBaseChangeUnbounded_fac.{u, r} Λ f g g' f' h I
  exact IsIso.of_isIso_fac_left hfac

/-- **The base change map is invertible at a K-injective complex `I` of injectives**, as soon as
the underived comparison is invertible at every injective sheaf of `Λ`-modules and `(g')^{-1} I`
computes `Rf'_*`. -/
theorem isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_injective
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hI : I.IsKInjective)
    [∀ k, Injective (I.X k)]
    (hinj : ∀ M : EtaleModules.{u, r} Λ X, Injective M →
      IsIso ((etaleModuleBaseChange.{u, r} Λ f f' g g' h.symm).app M))
    (hunit : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
      (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :
    IsIso ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' h).app
      (DerivedCategory.Q.obj I)) :=
  isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isKInjective Λ f g g' f' h I hI
    (isIso_etaleModuleComplexBaseChangeUnbounded_app_of_forall Λ f g g' f' h I
      fun k ↦ hinj (I.X k) inferInstance) hunit

end Stacks.EtaleCohomology

end
