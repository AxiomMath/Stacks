module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms

/-!
# Localization of higher direct images, read on an arbitrary injective resolution

Stacks 01E5 asserts that higher direct images commute with restriction to an open subspace, and
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso` is that isomorphism.  One
clause of the tag characterizes it by a computation on resolutions: given an injective resolution
`I` of the sheaf `ℱ`, an injective resolution `J` of its restriction `ℱ|_U`, and a cochain map
`φ : J ⟶ ℱ|_U`-resolution descending the identity, the comparison is the computation of the
right-hand side through `I`, read through `J` and `φ` and through the underived comparison
`modulePushforwardRestrictIso`.

This file proves that clause **in positive degree**.  The positive-degree half of
`higherDirectImageRestrictIso` is `higherDirectImageRestrictIsoSucc`, built from
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, and both of those are now
  readable on an arbitrary
resolution through `StacksDraft.Ch20.Sec14.DerivedCompTransport`.

## Main results

* `compRightDerivedNatIso_inv_app_comp_isoRightDerivedObj` and
  `rightDerivedCompIso_inv_app_comp_isoRightDerivedObj`: the two engines of
  `higherDirectImageRestrictIsoSucc`, inverted and evaluated against an arbitrary injective
  resolution.
* `mapComplexHomologyIso_inv_app`: the inverse of
  `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`, which is where the underived
  comparison and `CategoryTheory.ShortComplex.mapHomologyIso` enter.
* `compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_app`: the abstract form of the clause.
  For `L` exact and preserving injectives, `R` exact, and `ε : L ⋙ G ≅ P ⋙ R`, the composite
  `(L ⋙ G).rightDerived n ≅ P.rightDerived n ⋙ R` built from those two engines is computed by any
  triple `(I, J, φ)`.
* `higherDirectImageRestrictIso_injectiveResolution_succ`: that statement for Stacks 01E5, in
  positive degree.

## Implementation notes

The clause's `φ` runs from `J` to the image of `I` under restriction, i.e. it is a descent of the
identity of `ℱ|_U` *from* `J` *to* `Stacks.Cohomology.CompositeRightDerived.mapInjRes L I`; the
  hypothesis `hφ` is
`J.ι.f 0 ≫ φ.f 0 = L.map (I.ι.f 0)`, which is that descent condition after
`Stacks.Cohomology.DerivedCompTransport.mapInjRes_ι_f_zero`.  Accordingly the transport used here
is `Stacks.Cohomology.DerivedCompTransport.isoRightDerivedObj_hom_eq` together with
`compRightDerivedNatIso_hom_app_mapInjRes`, rather than the two-variable
`compRightDerivedNatIso_hom_app_eq`, whose `φ` runs the other way.

`CategoryTheory.InjectiveResolution.isoRightDerivedObj` presents the homology of the image of a
resolution as `(homologyFunctor _ _ n).obj ((F.mapHomologicalComplex _).obj K)`, whereas a
composite `L ⋙ G` presents the same object through `(L ⋙ G).mapHomologicalComplex _`.  The two
agree only after unfolding `CategoryTheory.Functor.comp` and
`CategoryTheory.Functor.mapHomologicalComplex`, so `Category.assoc` does not fire across the
junction and `rw` reports the target as not type-correct; every reassociation below is therefore a
term (`Category.assoc _ _ _` or `congrArg` elaborated against a goal stated in the desired
spelling).  For the same reason the concrete instantiation splits the identification of
`(higherDirectImageRestrictIso f V (n + 1)).hom.app M` with the composite of the two engines into
a separate `rfl`, and applies the abstract result to a `have` rather than directly to the goal:
elaborating the two steps at once exceeds the default heartbeat budget.

**The degree-zero branch is not proved here.**  `higherDirectImageRestrictIso` is defined by cases
on the degree, and in degree zero it is `higherDirectImageRestrictIsoZero`, the underived
comparison read through `CategoryTheory.Functor.rightDerivedZeroIsoSelf` on both sides; that is
what makes `higherDirectImageRestrictIso_zero_compatibility` true, and it mentions no resolution.
`CategoryTheory.InjectiveResolution.toRightDerivedZero_eq` reduces the degree-zero case of the
clause to the single equation

`ε.hom.app M ≫ R.map (I.toRightDerivedZero' P ≫ (CochainComplex.isoHomologyπ₀ _).hom) =`
`  J.toRightDerivedZero' G ≫ (CochainComplex.isoHomologyπ₀ _).hom ≫ H⁰(G φ) ≫ H⁰(ε) ≫`
`    ((P I).sc 0).mapHomologyIso R).hom`

and that equation needs the compatibility of `CategoryTheory.ShortComplex.mapHomologyIso` with
`CategoryTheory.ShortComplex.homologyπ`, namely

`(S.map F).homologyπ ≫ (S.mapHomologyIso F).hom = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ`,

since `CochainComplex.isoHomologyπ₀` *is* `homologyπ` in degree zero and
`CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles` is what turns
`CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles` and `hφ` into the naturality
square of `ε`.  Mathlib at the pinned revision has `mapCyclesIso_hom_iCycles`,
`mapHomologyIso_hom_naturality` and `CochainComplex.isoHomologyπ₀_inv_naturality`, but no lemma
relating `mapHomologyIso` to `homologyπ` or to `mapCyclesIso`, and neither does this project.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedCompTransport Stacks.Cohomology.ModuleComparison

universe u

namespace Stacks.Cohomology.HigherDirectImage

/-! ### Reading the two engines on an arbitrary injective resolution -/

/-- Isomorphisms with equal forward maps have equal inverses. -/
private theorem iso_inv_eq_of_hom_eq {A : Type*} [Category* A] {X Y : A} (e e' : X ≅ Y)
    (h : e.hom = e'.hom) : e.inv = e'.inv :=
  congrArg Iso.inv (Iso.ext h)

section Abstract

variable {C : Type*} {D : Type*} {B : Type*} {E : Type*}
  [Category* C] [Category* D] [Category* B] [Category* E]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D]
  [Abelian B] [Abelian E]
  (L : C ⥤ D) (G : D ⥤ E) (P : C ⥤ B) (R : B ⥤ E)
  [L.Additive] [G.Additive] [P.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]
  [R.PreservesHomology]
  (ε : L ⋙ G ≅ P ⋙ R)

/-- The component of the inverse of
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, read through an
arbitrary injective resolution `I` of `X` and its image under `L`.  This is
`Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_mapInjRes` inverted. -/
theorem compRightDerivedNatIso_inv_app_eq (n : ℕ) {M : C} (I : InjectiveResolution M) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).inv.app M =
      ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).isoRightDerivedObj G n).hom ≫
        (I.isoRightDerivedObj (L ⋙ G) n).inv :=
  iso_inv_eq_of_hom_eq
    ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).app M)
    (I.isoRightDerivedObj (L ⋙ G) n ≪≫
      ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).isoRightDerivedObj G n).symm)
    (compRightDerivedNatIso_hom_app_mapInjRes L G n I)

/-- The solved form of `compRightDerivedNatIso_inv_app_eq`: composing the inverse comparison with
the computation of `(L ⋙ G).rightDerived n` through `I` gives the computation of
`G.rightDerived n` at `L.obj M` through the image of `I` under `L`. -/
theorem compRightDerivedNatIso_inv_app_comp_isoRightDerivedObj (n : ℕ) {M : C}
    (I : InjectiveResolution M) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).inv.app M ≫
        (I.isoRightDerivedObj (L ⋙ G) n).hom =
      ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).isoRightDerivedObj G n).hom :=
  (congrArg (fun g => g ≫ (I.isoRightDerivedObj (L ⋙ G) n).hom)
      (compRightDerivedNatIso_inv_app_eq L G n I)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
          (fun g => ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).isoRightDerivedObj G
            n).hom ≫ g)
          (Iso.inv_hom_id _)).trans (Category.comp_id _)))

omit [HasInjectiveResolutions D] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L.PreservesInjectiveObjects] in
/-- The component of the inverse of `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`,
composed with the computation of `P.rightDerived n` through an arbitrary injective resolution `I`:
the computations through `I` of the two sides cancel, leaving only the complex-level comparison.
This is `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_eq` inverted. -/
theorem rightDerivedCompIso_inv_app_comp_isoRightDerivedObj (n : ℕ) {M : C}
    (I : InjectiveResolution M) :
    (rightDerivedCompIso P R (L ⋙ G) ε.symm n).inv.app M ≫
        R.map (I.isoRightDerivedObj P n).hom =
      (I.isoRightDerivedObj (L ⋙ G) n).hom ≫
        (mapComplexHomologyIso P R (L ⋙ G) ε.symm n).inv.app I.cocomplex := by
  have h : (rightDerivedCompIso P R (L ⋙ G) ε.symm n).inv.app M =
      ((I.isoRightDerivedObj (L ⋙ G) n).hom ≫
        (mapComplexHomologyIso P R (L ⋙ G) ε.symm n).inv.app I.cocomplex) ≫
        R.map (I.isoRightDerivedObj P n).inv :=
    iso_inv_eq_of_hom_eq ((rightDerivedCompIso P R (L ⋙ G) ε.symm n).app M)
      (R.mapIso (I.isoRightDerivedObj P n) ≪≫
        (mapComplexHomologyIso P R (L ⋙ G) ε.symm n).app I.cocomplex ≪≫
        (I.isoRightDerivedObj (L ⋙ G) n).symm)
      (rightDerivedCompIso_hom_app_eq P R (L ⋙ G) ε.symm n I)
  rw [h, Category.assoc, ← R.map_comp, Iso.inv_hom_id, R.map_id]
  exact Category.comp_id _

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [L.PreservesInjectiveObjects] in
/-- The inverse of `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` at a complex `K`:
apply the underived comparison `ε` termwise, take degree-`n` homology, and compare with the
homology computed before applying `R`. -/
theorem mapComplexHomologyIso_inv_app (n : ℕ) (K : HomologicalComplex C (ComplexShape.up ℕ)) :
    (mapComplexHomologyIso P R (L ⋙ G) ε.symm n).inv.app K =
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex ε.hom (ComplexShape.up ℕ)).app K) ≫
        ((((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).mapHomologyIso R).hom := by
  dsimp only [mapComplexHomologyIso, homologyMapFunctorIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, NatIso.ofComponents_hom_app,
    Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex]
  rfl

/-- **The abstract form of the resolution clause of Stacks 01E5.**  Let `L` be exact and preserve
injective objects, let `R` be exact, and let `ε : L ⋙ G ≅ P ⋙ R`.  The comparison
`L ⋙ G.rightDerived n ≅ P.rightDerived n ⋙ R` obtained from
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` is computed by an arbitrary triple
  consisting of an
injective resolution `I` of `M`, an injective resolution `J` of `L.obj M`, and a cochain map `φ`
from `J` to the image of `I` under `L` descending the identity of `L.obj M`. -/
theorem compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_app (n : ℕ) {M : C}
    (I : InjectiveResolution M) (J : InjectiveResolution (L.obj M))
    (φ : J.cocomplex ⟶ (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = L.map (I.ι.f 0)) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).inv.app M ≫
        (rightDerivedCompIso P R (L ⋙ G) ε.symm n).inv.app M ≫
        R.map (I.isoRightDerivedObj P n).hom =
      (J.isoRightDerivedObj G n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex ε.hom (ComplexShape.up ℕ)).app I.cocomplex) ≫
        ((((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso
          R).hom :=
  by
  rw [rightDerivedCompIso_inv_app_comp_isoRightDerivedObj, ← Category.assoc,
    compRightDerivedNatIso_inv_app_comp_isoRightDerivedObj,
    isoRightDerivedObj_hom_eq G n J (Stacks.Cohomology.CompositeRightDerived.mapInjRes L I) φ
      (hφ.trans (mapInjRes_ι_f_zero L I).symm)]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun g => (J.isoRightDerivedObj G n).hom ≫
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) ≫ g)
      (mapComplexHomologyIso_inv_app L G P R ε n I.cocomplex))

end Abstract

/-! ### Stacks 01E5 on an arbitrary injective resolution, in positive degree -/

section Restriction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- In positive degree, `higherDirectImageRestrictIso` is the composite of the inverses of the two
engines of `higherDirectImageRestrictIsoSucc`. -/
theorem higherDirectImageRestrictIso_succ_hom_app (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (higherDirectImageRestrictIso f V (n + 1)).hom.app M =
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (moduleRestriction X
        (preimageOpen f V))
          (modulePushforward (restrictedMorphism f V)) (n + 1)).inv.app M ≫
        (rightDerivedCompIso (modulePushforward f) (moduleRestriction Y V)
          (moduleRestriction X (preimageOpen f V) ⋙
            modulePushforward (restrictedMorphism f V))
          (modulePushforwardRestrictIso f V).symm (n + 1)).inv.app M := rfl

/-- **Stacks 01E5, compatibility with injective resolutions, in positive degree.**  On injective
resolutions, localization of a higher direct image is obtained by restricting the resolution and
applying the identity-on-sections comparison before taking cohomology.  The augmentation
condition `hφ` says that the comparison of resolutions descends the identity of the restricted
module.

The degree-zero case is *not* covered; see the implementation notes of this file for the one
missing Mathlib lemma. -/
theorem higherDirectImageRestrictIso_injectiveResolution_succ (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) (I : InjectiveResolution M)
    (J : InjectiveResolution ((moduleRestriction X (preimageOpen f V)).obj M))
    (φ : J.cocomplex ⟶
      ((moduleRestriction X (preimageOpen f V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 =
      (moduleRestriction X (preimageOpen f V)).map (I.ι.f 0)) :
    (higherDirectImageRestrictIso f V (n + 1)).hom.app M ≫
        (moduleRestriction Y V).map
          (I.isoRightDerivedObj (modulePushforward f) (n + 1)).hom =
      (J.isoRightDerivedObj (modulePushforward (restrictedMorphism f V)) (n + 1)).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) (n + 1)).map
          (((modulePushforward (restrictedMorphism f V)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ) ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) (n + 1)).map
          (((modulePushforwardRestrictIso f V).hom.mapHomologicalComplex
            (ComplexShape.up ℕ)).app I.cocomplex) ≫
        (((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).sc (n + 1)).mapHomologyIso (moduleRestriction Y V)).hom := by
  rw [higherDirectImageRestrictIso_succ_hom_app f V n M]
  have key := compRightDerivedNatIso_inv_comp_rightDerivedCompIso_inv_app
    (C := SheafOfModules.{u} (structureSheafRing X))
    (moduleRestriction X (preimageOpen f V))
    (modulePushforward (restrictedMorphism f V))
    (modulePushforward f) (moduleRestriction Y V) (modulePushforwardRestrictIso f V)
    (n + 1) I J φ hφ
  exact key

end Restriction

end Stacks.Cohomology.HigherDirectImage

end
