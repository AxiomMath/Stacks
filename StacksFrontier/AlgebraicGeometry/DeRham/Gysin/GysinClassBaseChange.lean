module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartData

/-!
# The degree-`c` reading of the square of Tag 0G7U, along an open immersion

Let `X` be a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, `T ⊆ X` closed and containing their common zero
locus, `ℱ` a quasi-coherent `𝒪_X`-module and `W ⊆ X` an open.
The theorem `map_cechToDerivedSupport_comp_supportPushPullbackIso_hom` of
`Stacks.Perfect.CechDerivedSupportBaseChange` is the square of [Stacks, Tag 0G7U] for an open
immersion, **in the derived category**: the
derived pullback of the comparison `𝓕^• ⟶ i_* R𝓗_T(ℱ)` of [Stacks, Tag 0G7L], followed by the
excision isomorphism of [Stacks, Tag 0G78], is that comparison for the restricted equations.

This file reads that square **in degree `p`**, i.e. on cohomology sheaves, where it becomes a
statement about `Stacks.Gysin.supportCohomologyRestrictIso` — the excision of [Stacks, Tag 0G78]
on degree-`p` cohomology sheaves, which is the transport the equation charts of
[Stacks, Tag 0G86] are built with.  That isomorphism lives here, downstream of `Perfect/`, which
is why this reading does.

## Main definitions

* `Stacks.Gysin.cechExtendHomologyRestrictIso`: **the restriction to `W` of the degree-`p`
  cohomology of the extended alternating Čech complex is the degree-`p` cohomology of the
  extended alternating Čech complex of the restricted equations.**  This is the exactness of
  restriction (`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso`) followed
  by the comparison `Stacks.Perfect.CechDerivedSupportBaseChange.restrictExtendIso` of the two
  complexes.

## Main results

* `Stacks.Gysin.singleRestrictIso_hom_eq`: **the identification
  `Stacks.Perfect.CechDerivedSupportBaseChange.singleRestrictIso` is the
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` comparison that
  `Stacks.Gysin.supportCohomologyPullbackIso` is built from**, followed by
  `Stacks.Gysin.modulePullbackRestrictFunctorIso` in degree `0`.  The two differ by the
  naturality of `HomologicalComplex.singleMapHomologicalComplex` in the functor, which is
  `singleMapHomologicalComplex_natIso`.
* `Stacks.Gysin.factors_inv_comp_mapDerivedCategory_cechToDerivedSupport`: the square, read at
  the **degreewise** pullback rather than the derived one.  Both comparisons
  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` cancel, and what is
  left of `cechRestrictIso` is the degreewise comparison of the two Čech complexes.
* `Stacks.Gysin.map_extendHomologyToSupport_comp_supportCohomologyRestrictIso`: **the degree-`p`
  reading of the square.**

## Implementation notes

**Two inputs, and nothing else.**  The square is about the derived pullback `Lι^*`; the excision
`Stacks.Gysin.supportCohomologyRestrictIso` is about the degreewise restriction `(-)|_W`.  What
bridges them is (i) that `(-)|_W` is exact, so it commutes with the cohomology of a complex —
this is where `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` and
`mapHomologicalComplexHomologyIso` enter, and `mapDerivedCategoryHomologyIso_hom_app_Q` is the
one computation needed of the first, namely its value at a complex; and (ii) that
`singleRestrictIso` is the comparison the excision is built from, which is
`singleRestrictIso_hom_eq`.  Everything else is the naturality of the four comparisons involved.

**The two spellings of the category of modules on `W`.**
`Stacks.Gysin.supportCohomologyRestrictIso` is `Stacks.Gysin.supportCohomologyPullbackIso`
conjugated by
`Stacks.Gysin.modulePullbackRestrictFunctorIso`, so a chain that relates it to anything written
with `AlgebraicGeometry.Scheme.Modules.restrictFunctor` meets both
`SheafOfModules (structureSheafRing (X|_W))` and `W.toScheme.Modules`.  The two are
definitionally equal, but instance search for `Additive` or `PreservesFiniteLimits` of the
restriction functor fails at the spelling the instance was not recorded at, and `rw`/`simp` on a
composite that mixes them does not even re-associate.  Two devices handle this, and both are
needed: an instance asked of a functor reached across an isomorphism is **transported** across
that isomorphism (`preservesZeroMorphisms_of_natIso`,
`CategoryTheory.Functor.additive_iff_of_iso`,
`CategoryTheory.Limits.preservesFiniteLimits_of_natIso`) rather than searched for again; and
every chase is stated as a helper at a **variable** category and applied with `exact`, so that
the unifier, not `rw`, is what crosses between the spellings.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.CechDerivedSupportBaseChange
open Stacks.Perfect.ExtendedAlternatingCech (cplx)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open StacksDraft.DerivedCategoryHomology

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

section Single

/-- **The comparison of a functor with the placement of an object in degree `j` is natural in
the functor.**  For an isomorphism `ρ : P ≅ R` of functors preserving zero morphisms, the
degreewise `ρ` followed by `HomologicalComplex.singleMapHomologicalComplex` for `R` is that
comparison for `P` followed by `ρ` in degree `j`.  Both sides are morphisms into a complex
concentrated in degree `j`, so only the degree-`j` component is at stake, and there both are
`ρ` at the coefficient object. -/
theorem singleMapHomologicalComplex_natIso {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroObject A] [HasZeroMorphisms B] [HasZeroObject B]
    {P R : A ⥤ B} [P.PreservesZeroMorphisms] [R.PreservesZeroMorphisms] (ρ : P ≅ R)
    {ι : Type*} [DecidableEq ι]
    (c : ComplexShape ι) (j : ι) (F : A) :
    (NatIso.mapHomologicalComplex ρ c).hom.app ((HomologicalComplex.single A c j).obj F) ≫
        (HomologicalComplex.singleMapHomologicalComplex R c j).hom.app F =
      (HomologicalComplex.singleMapHomologicalComplex P c j).hom.app F ≫
        (HomologicalComplex.single B c j).map (ρ.hom.app F) := by
  refine HomologicalComplex.to_single_hom_ext (j := j) ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    show ((NatIso.mapHomologicalComplex ρ c).hom.app
        ((HomologicalComplex.single A c j).obj F)).f j =
      ρ.hom.app (((HomologicalComplex.single A c j).obj F).X j) from rfl,
    HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  rw [← ρ.hom.naturality (HomologicalComplex.singleObjXSelf c j F).hom]

end Single

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- **The comparison of an exact functor with the cohomology of a complex is natural in the
functor.**  The instances the target functor needs are transported across the isomorphism rather
than searched for, so that the statement can be used at a functor whose target category is
spelled differently from the source's. -/
theorem mapHomologicalComplexHomologyIso_natIso {P R : C ⥤ D} [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (ρ : P ≅ R) {ι : Type*}
    (c : ComplexShape ι) (i : ι) (K : HomologicalComplex C c) :
    letI := (Functor.additive_iff_of_iso ρ).mp inferInstance
    letI := preservesFiniteLimits_of_natIso ρ
    letI := preservesFiniteColimits_of_natIso ρ
    HomologicalComplex.homologyMap ((NatIso.mapHomologicalComplex ρ c).hom.app K) i ≫
        (mapHomologicalComplexHomologyIso R c i).hom.app K =
      (mapHomologicalComplexHomologyIso P c i).hom.app K ≫ ρ.hom.app (K.homology i) := by
  let := (Functor.additive_iff_of_iso ρ).mp (inferInstance : P.Additive)
  let := preservesFiniteLimits_of_natIso ρ
  let := preservesFiniteColimits_of_natIso ρ
  let S := (HomologicalComplex.shortComplexFunctor C c i).obj K
  show ShortComplex.homologyMap (S.mapNatTrans ρ.hom) ≫ (S.mapHomologyIso R).hom =
    (S.mapHomologyIso P).hom ≫ ρ.hom.app S.homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp

variable [HasDerivedCategory C] [HasDerivedCategory D]

/-- **The comparison of an exact functor with the cohomology of the derived category, evaluated
at a complex.**  `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` is defined
by lifting a natural isomorphism through the localization `DerivedCategory.Q`; this is the value
of that lift at an object of the image of `Q`, which is the only thing about it this file needs.
The four factors are the comparison of the derived functor with the degreewise one, the two
identifications of cohomology in the derived category with cohomology of a complex, and the
degreewise comparison `mapHomologicalComplexHomologyIso`. -/
theorem mapDerivedCategoryHomologyIso_hom_app_Q
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (L : CochainComplex C ℤ) (p : ℤ) :
    (mapDerivedCategoryHomologyIso P p).hom.app (DerivedCategory.Q.obj L) =
      (DerivedCategory.homologyFunctor D p).map (P.mapDerivedCategoryFactors.hom.app L) ≫
        (DerivedCategory.homologyFunctorFactors D p).hom.app
            ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
          (mapHomologicalComplexHomologyIso P (ComplexShape.up ℤ) p).hom.app L ≫
            P.map ((DerivedCategory.homologyFunctorFactors C p).inv.app L) := by
  rw [mapDerivedCategoryHomologyIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  simp

/-- `mapDerivedCategoryHomologyIso_hom_app_Q` read on the inverses, which is the direction the
excision of [Stacks, Tag 0G78] on cohomology sheaves is built with. -/
theorem mapDerivedCategoryHomologyIso_inv_app_Q
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (L : CochainComplex C ℤ) (p : ℤ) :
    P.map ((DerivedCategory.homologyFunctorFactors C p).inv.app L) ≫
        (mapDerivedCategoryHomologyIso P p).inv.app (DerivedCategory.Q.obj L) =
      (mapHomologicalComplexHomologyIso P (ComplexShape.up ℤ) p).inv.app L ≫
        (DerivedCategory.homologyFunctorFactors D p).inv.app
            ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
          (DerivedCategory.homologyFunctor D p).map
            (P.mapDerivedCategoryFactors.inv.app L) := by
  refine (Iso.comp_inv_eq ((mapDerivedCategoryHomologyIso P p).app
    (DerivedCategory.Q.obj L))).mpr ?_
  rw [show ((mapDerivedCategoryHomologyIso P p).app (DerivedCategory.Q.obj L)).hom =
      (mapDerivedCategoryHomologyIso P p).hom.app (DerivedCategory.Q.obj L) from rfl,
    mapDerivedCategoryHomologyIso_hom_app_Q]
  simp

end General

section Degree

attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion

variable {X : Scheme.{u}} (W : X.Opens) {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules)
  [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
  (hT' : IsClosed (restrictClosedSubset W T))
  (hTe' : equationsClosedSet (fun j => W.ι.appTop (e j)) ⊆ restrictClosedSubset W T)

/-- `restrictQIso`, factor by factor. -/
theorem restrictQIso_hom_eq (C : CochainComplex X.Modules ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
    (restrictQIso W C).hom =
      (derivedPullbackOpenImmersionIso (openIncl W)).hom.app (DerivedCategory.Q.obj C) ≫
        (modulePullback (openIncl W)).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso W)
              (ComplexShape.up ℤ)).hom.app C) := rfl

/-- If `b ≫ binv = 𝟙`, `binv ≫ b' = mm` and `c ≫ d = mm ≫ c'`, then
`(a ≫ b ≫ c) ≫ d = a ≫ b' ≫ c'`. -/
theorem chase5 {C : Type*} [Category* C] {o₁ o₂ o₃ o₄ o₅ o₆ : C}
    (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (binv : o₃ ⟶ o₂) (c : o₃ ⟶ o₄) (d : o₄ ⟶ o₅)
    (mm : o₃ ⟶ o₆) (b' : o₂ ⟶ o₆) (c' : o₆ ⟶ o₅)
    (hb : b ≫ binv = 𝟙 o₂) (hm : binv ≫ b' = mm) (hcd : c ≫ d = mm ≫ c') :
    (a ≫ b ≫ c) ≫ d = a ≫ b' ≫ c' := by
  subst hm
  simp [hcd, reassoc_of% hb]

/-- **`singleRestrictIso` is the `mapDerivedCategorySingleFunctor` comparison.** -/
theorem singleRestrictIso_hom_eq :
    (singleRestrictIso W F).hom =
      (derivedPullbackOpenImmersionIso (openIncl W)).hom.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
        ((modulePullback (openIncl W)).mapDerivedCategorySingleFunctor 0).hom.app F ≫
          (DerivedCategory.singleFunctor W.toScheme.Modules 0).map
            ((modulePullbackRestrictIso W).hom.app F) := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
  refine Eq.trans (congrArg (fun z => z ≫ DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor W.ι)
        (ComplexShape.up ℤ) 0).hom.app F))
    (restrictQIso_hom_eq W ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)))
    ?_
  refine chase5 _ _ ((modulePullback (openIncl W)).mapDerivedCategoryFactors.inv.app
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)) _ _
    (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback (openIncl W))
        (ComplexShape.up ℤ) 0).hom.app F)) _ _
    ((modulePullback (openIncl W)).mapDerivedCategoryFactors.hom_inv_id_app _)
    (Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (modulePullback (openIncl W)) F)
    ?_
  refine Eq.trans (DerivedCategory.Q.map_comp _ _).symm ?_
  refine Eq.trans (congrArg DerivedCategory.Q.map
    (singleMapHomologicalComplex_natIso (modulePullbackRestrictIso W)
      (ComplexShape.up ℤ) 0 F)) ?_
  exact DerivedCategory.Q.map_comp _ _

/-- `Stacks.Gysin.supportCohomologyRestrictIso` is `supportCohomologyPullbackIso` conjugated by
`Stacks.Gysin.modulePullbackRestrictFunctorIso`, which here is written at the spelling
`Stacks.Perfect.CechDerivedSupportBaseChange.modulePullbackRestrictIso` the square is recorded
at; the two are the same expression. -/
theorem supportCohomologyRestrictIso_hom_eq (n : ℤ) :
    (supportCohomologyRestrictIso W hT hT' n F).hom =
      (modulePullbackRestrictIso W).inv.app ((supportCohomologySheafFunctor hT n).obj F) ≫
        (supportCohomologyPullbackIso (openIncl W) T hT n F).hom ≫
          (supportCohomologySheafFunctor hT' n).map ((modulePullbackRestrictIso W).hom.app F) :=
  rfl

/-- `Stacks.Gysin.supportCohomologyPullbackIso`, factor by factor. -/
theorem supportCohomologyPullbackIso_hom_eq (n : ℤ) :
    (supportCohomologyPullbackIso (openIncl W) T hT n F).hom =
      ((mapDerivedCategoryHomologyIso (modulePullback (openIncl W)) n).app
          ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))).inv ≫
        (DerivedCategory.homologyFunctor W.toScheme.Modules n).map
          ((derivedPullbackOpenImmersionIso (openIncl W)).inv.app
              ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
            (Stacks.Perfect.SupportPushExcision.supportPushPullbackIso
                (openIncl W) hT).hom.app
                ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
              (supportPush hT').map
                ((derivedPullbackOpenImmersionIso (openIncl W)).hom.app
                    ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                  ((modulePullback (openIncl W)).mapDerivedCategorySingleFunctor 0).hom.app F)) :=
  rfl

/-- The functor `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor` on a morphism is
degree-`n` cohomology of `i_* R𝓗_T` of that morphism in degree `0`. -/
theorem supportCohomologySheafFunctor_map_eq {G : X.Modules} (g : F ⟶ G) (n : ℤ) :
    (supportCohomologySheafFunctor hT n).map g =
      (DerivedCategory.homologyFunctor X.Modules n).map
        ((supportPush hT).map ((DerivedCategory.singleFunctor X.Modules 0).map g)) := rfl

/-- **The restriction of the cohomology of the extended alternating Čech complex is the
cohomology of the extended alternating Čech complex of the restricted equations.** -/
def cechExtendHomologyRestrictIso (p : ℤ) :
    (Scheme.Modules.restrictFunctor W.ι).obj
        (((cplx e F).extend ComplexShape.embeddingUpNat).homology p) ≅
      ((cplx (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F)).extend
        ComplexShape.embeddingUpNat).homology p :=
  ((mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor W.ι)
      (ComplexShape.up ℤ) p).app ((cplx e F).extend ComplexShape.embeddingUpNat)).symm ≪≫
    (HomologicalComplex.homologyFunctor W.toScheme.Modules (ComplexShape.up ℤ) p).mapIso
      (restrictExtendIso W e F)

/-- `mapHomologicalComplexHomologyIso_natIso` at the identification of the pullback of modules
along the inclusion of an open subscheme with the restriction to it. -/
theorem mapHomologicalComplexHomologyIso_natIso_restrict (p : ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
    HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso W)
            (ComplexShape.up ℤ)).hom.app
              ((cplx e F).extend
                ComplexShape.embeddingUpNat)) p ≫
        (mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor W.ι)
            (ComplexShape.up ℤ) p).hom.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat) =
      (mapHomologicalComplexHomologyIso (modulePullback (openIncl W))
            (ComplexShape.up ℤ) p).hom.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat) ≫
        (modulePullbackRestrictIso W).hom.app
          (((cplx e F).extend
            ComplexShape.embeddingUpNat).homology p) :=
  mapHomologicalComplexHomologyIso_natIso (modulePullbackRestrictIso W) (ComplexShape.up ℤ) p _

/-- `cechExtendHomologyRestrictIso`, factor by factor. -/
theorem cechExtendHomologyRestrictIso_hom (p : ℤ) :
    (cechExtendHomologyRestrictIso W e F p).hom =
      (mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor W.ι)
            (ComplexShape.up ℤ) p).inv.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat) ≫
        HomologicalComplex.homologyMap (restrictExtendIso W e F).hom p := rfl

/-- The degree-`p` cohomology of the degreewise comparison of the two Čech complexes, solved for:
it is the comparison of the pullback with cohomology, the identification of the pullback with the
restriction, and the inverse of the comparison of the restriction with cohomology. -/
theorem homologyMap_mapHomologicalComplex_eq (p : ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
    HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso W)
          (ComplexShape.up ℤ)).hom.app
            ((cplx e F).extend
              ComplexShape.embeddingUpNat)) p =
      (mapHomologicalComplexHomologyIso (modulePullback (openIncl W))
            (ComplexShape.up ℤ) p).hom.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat) ≫
        (modulePullbackRestrictIso W).hom.app
            (((cplx e F).extend
              ComplexShape.embeddingUpNat).homology p) ≫
          (mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor W.ι)
              (ComplexShape.up ℤ) p).inv.app
            ((cplx e F).extend
              ComplexShape.embeddingUpNat) := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine (Iso.eq_comp_inv ((mapHomologicalComplexHomologyIso
    (Scheme.Modules.restrictFunctor W.ι) (ComplexShape.up ℤ) p).app
      ((cplx e F).extend
        ComplexShape.embeddingUpNat))).mpr ?_
  exact mapHomologicalComplexHomologyIso_natIso_restrict W e F p

/-- The cancellation behind `cechExtendHomologyRestrictIso_hom_eq`, at a variable category. -/
theorem chaseCancel {C : Type*} [Category* C] {o₁ o₂ o₃ o₄ o₅ : C}
    (rinv : o₁ ⟶ o₂) (rhom : o₂ ⟶ o₁) (pinv : o₂ ⟶ o₃) (phom : o₃ ⟶ o₂)
    (hn : o₃ ⟶ o₄) (mr : o₁ ⟶ o₄) (hm : o₄ ⟶ o₅)
    (hr : rinv ≫ rhom = 𝟙 o₁) (hp : pinv ≫ phom = 𝟙 o₂)
    (hL : hn = phom ≫ rhom ≫ mr) :
    rinv ≫ pinv ≫ hn ≫ hm = mr ≫ hm := by
  simp [hL, reassoc_of% hp, reassoc_of% hr]

/-- **The restricted cohomology comparison, factored through the pullback spelling.** -/
theorem cechExtendHomologyRestrictIso_hom_eq (p : ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
    (modulePullbackRestrictIso W).inv.app
          (((cplx e F).extend
            ComplexShape.embeddingUpNat).homology p) ≫
        (mapHomologicalComplexHomologyIso (modulePullback (openIncl W))
              (ComplexShape.up ℤ) p).inv.app
            ((cplx e F).extend
              ComplexShape.embeddingUpNat) ≫
          HomologicalComplex.homologyMap
              ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso W)
                (ComplexShape.up ℤ)).hom.app
                  ((cplx e F).extend
                    ComplexShape.embeddingUpNat)) p ≫
            HomologicalComplex.homologyMap (restrictExtendIso W e F).hom p =
      (cechExtendHomologyRestrictIso W e F p).hom := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
  refine Eq.trans (chaseCancel _ ((modulePullbackRestrictIso W).hom.app _) _
    ((mapHomologicalComplexHomologyIso (modulePullback (openIncl W))
      (ComplexShape.up ℤ) p).hom.app _) _ _ _
    ((modulePullbackRestrictIso W).inv_hom_id_app _)
    ((mapHomologicalComplexHomologyIso (modulePullback (openIncl W))
      (ComplexShape.up ℤ) p).inv_hom_id_app _)
    (homologyMap_mapHomologicalComplex_eq W e F p))
    (cechExtendHomologyRestrictIso_hom W e F p).symm

/-! ### The derived-category core -/

/-- The chase behind `mapDerivedCategory_cechToDerivedSupport_comp`, at a variable category. -/
theorem assembleSq {E : Type*} [Category* E] (Sp : E ⥤ E)
    {x1 x2 x3 x4 z y1 y2 y3 : E}
    (w : x1 ⟶ x2) (dinv : x2 ⟶ x3) (dinv' : x1 ⟶ x4) (dp : x4 ⟶ x3)
    (exc : x3 ⟶ Sp.obj y1) (g : y1 ⟶ y2) (h : y2 ⟶ y3) (sri : y1 ⟶ y3)
    (cri : x4 ⟶ z) (kp : z ⟶ Sp.obj y3)
    (hn : w ≫ dinv = dinv' ≫ dp)
    (hL : sri = g ≫ h)
    (hsq : dp ≫ exc ≫ Sp.map sri = cri ≫ kp) :
    w ≫ (dinv ≫ exc ≫ Sp.map g) ≫ Sp.map h = dinv' ≫ cri ≫ kp := by
  simp only [Category.assoc]
  rw [← Category.assoc w dinv, hn]
  simp only [Category.assoc, ← Sp.map_comp, ← hL]
  rw [hsq]

/-- The derived pullback of the comparison of [Stacks, Tag 0G7L], read at the degreewise
pullback: the square of `CechDerivedSupportBaseChange`, with the comparison of the derived
pullback with the degreewise one inserted on both sides. -/
theorem mapDerivedCategory_cechToDerivedSupport_comp :
    (modulePullback (openIncl W)).mapDerivedCategory.map (cechToDerivedSupport e F hT hTe) ≫
        ((derivedPullbackOpenImmersionIso (openIncl W)).inv.app
              ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
            (Stacks.Perfect.SupportPushExcision.supportPushPullbackIso (openIncl W) hT).hom.app
                ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
              (supportPush hT').map
                ((derivedPullbackOpenImmersionIso (openIncl W)).hom.app
                    ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                  ((modulePullback (openIncl W)).mapDerivedCategorySingleFunctor 0).hom.app F)) ≫
          (supportPush hT').map
            ((DerivedCategory.singleFunctor W.toScheme.Modules 0).map
              ((modulePullbackRestrictIso W).hom.app F)) =
      (derivedPullbackOpenImmersionIso (openIncl W)).inv.app
          (DerivedCategory.Q.obj ((cplx e F).extend
            ComplexShape.embeddingUpNat)) ≫
        (cechRestrictIso W e F).hom ≫
          cechToDerivedSupport (fun j => W.ι.appTop (e j))
            ((Scheme.Modules.restrictFunctor W.ι).obj F) hT' hTe' :=
  assembleSq (supportPush hT') _ _ _ _ _ _ _ (singleRestrictIso W F).hom _ _
    ((derivedPullbackOpenImmersionIso (openIncl W)).inv.naturality
      (cechToDerivedSupport e F hT hTe))
    ((singleRestrictIso_hom_eq W F).trans (Category.assoc _ _ _).symm)
    (map_cechToDerivedSupport_comp_supportPushPullbackIso_hom W e F hT hTe hT' hTe')

/-- The two comparisons of the derived pullback with the degreewise pullback cancel: what is
left of `cechRestrictIso` is the degreewise comparison of the two Čech complexes. -/
theorem factors_inv_comp_cechRestrictIso :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
    (modulePullback (openIncl W)).mapDerivedCategoryFactors.inv.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat) ≫
        (derivedPullbackOpenImmersionIso (openIncl W)).inv.app
            (DerivedCategory.Q.obj ((cplx e F).extend
              ComplexShape.embeddingUpNat)) ≫
          (cechRestrictIso W e F).hom =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso W)
            (ComplexShape.up ℤ)).hom.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat)) ≫
        DerivedCategory.Q.map (restrictExtendIso W e F).hom := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
  refine Eq.trans (congrArg (fun z =>
      (modulePullback (openIncl W)).mapDerivedCategoryFactors.inv.app _ ≫
        (derivedPullbackOpenImmersionIso (openIncl W)).inv.app _ ≫ z)
    (cechRestrictIso_hom W e F)) ?_
  exact chaseCancel _
    ((modulePullback (openIncl W)).mapDerivedCategoryFactors.hom.app _) _
    ((derivedPullbackOpenImmersionIso (openIncl W)).hom.app _) _ _ _
    ((modulePullback (openIncl W)).mapDerivedCategoryFactors.inv_hom_id_app _)
    ((derivedPullbackOpenImmersionIso (openIncl W)).inv_hom_id_app _)
    (restrictQIso_hom_eq W _)

/-- Postcomposing an identity of composites. -/
theorem postcomp {C : Type*} [Category* C] {o₁ o₂ o₃ o₄ o₅ o₆ : C}
    (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (c : o₃ ⟶ o₄) (d : o₁ ⟶ o₅) (ee : o₅ ⟶ o₄) (k : o₄ ⟶ o₆)
    (h : a ≫ b ≫ c = d ≫ ee) : a ≫ b ≫ c ≫ k = d ≫ ee ≫ k := by
  simpa using h =≫ k

/-- **The derived-category identity behind the degree-`p` reading.** -/
theorem factors_inv_comp_mapDerivedCategory_cechToDerivedSupport :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
    (modulePullback (openIncl W)).mapDerivedCategoryFactors.inv.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat) ≫
        (modulePullback (openIncl W)).mapDerivedCategory.map
            (cechToDerivedSupport e F hT hTe) ≫
          ((derivedPullbackOpenImmersionIso (openIncl W)).inv.app
                ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
              (Stacks.Perfect.SupportPushExcision.supportPushPullbackIso
                  (openIncl W) hT).hom.app
                  ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                (supportPush hT').map
                  ((derivedPullbackOpenImmersionIso (openIncl W)).hom.app
                      ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                    ((modulePullback (openIncl W)).mapDerivedCategorySingleFunctor 0).hom.app
                      F)) ≫
            (supportPush hT').map
              ((DerivedCategory.singleFunctor W.toScheme.Modules 0).map
                ((modulePullbackRestrictIso W).hom.app F)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso W)
            (ComplexShape.up ℤ)).hom.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat)) ≫
        DerivedCategory.Q.map (restrictExtendIso W e F).hom ≫
          cechToDerivedSupport (fun j => W.ι.appTop (e j))
            ((Scheme.Modules.restrictFunctor W.ι).obj F) hT' hTe' := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
  refine Eq.trans (congrArg (fun z =>
      (modulePullback (openIncl W)).mapDerivedCategoryFactors.inv.app _ ≫ z)
    (mapDerivedCategory_cechToDerivedSupport_comp W e F hT hTe hT' hTe')) ?_
  exact postcomp _ _ _ _ _ _ (factors_inv_comp_cechRestrictIso W e F)

/-! ### The degree-`p` reading -/

/-- Reading an inverted naturality square, at a variable category. -/
private theorem invNat {C : Type*} [Category* C] {a b a' b' : C}
    (f : a ⟶ b) (g : a' ⟶ b') (ha : a ⟶ a') (hai : a' ⟶ a) (hb : b ⟶ b') (hbi : b' ⟶ b)
    (h : f ≫ hb = ha ≫ g) (hha : hai ≫ ha = 𝟙 a') (hhb : hb ≫ hbi = 𝟙 b) :
    hai ≫ f = g ≫ hbi := by
  rw [← Category.comp_id (hai ≫ f), ← hhb, Category.assoc, ← Category.assoc f hb hbi, h]
  simp [reassoc_of% hha]

/-- The identification of the cohomology of a complex with its cohomology in the derived
category, read on the inverses. -/
theorem homologyFunctorFactors_inv_naturality {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {L L' : CochainComplex C ℤ} (α : L ⟶ L') (p : ℤ) :
    (DerivedCategory.homologyFunctorFactors C p).inv.app L ≫
        (DerivedCategory.homologyFunctor C p).map (DerivedCategory.Q.map α) =
      HomologicalComplex.homologyMap α p ≫
        (DerivedCategory.homologyFunctorFactors C p).inv.app L' :=
  invNat _ _ _ _ _ _ (DerivedCategory.homologyFunctorFactors_hom_naturality α p)
    ((DerivedCategory.homologyFunctorFactors C p).inv_hom_id_app L)
    ((DerivedCategory.homologyFunctorFactors C p).hom_inv_id_app L')

/-- The chase behind the degree-`p` reading, at variable categories. -/
theorem assembleDeg {A B E : Type*} [Category* A] [Category* B] [Category* E]
    (Rf Pf : A ⥤ B) (HB : E ⥤ B)
    {a1 a2 a3 : A} (dq : a1 ⟶ a2) (kH : a2 ⟶ a3)
    {d1 d2 d3 : B} {e0 e1 e2 e3 e4 e5 e6 : E}
    (m3 : Rf.obj a3 ⟶ Pf.obj a3) (m4 : Pf.obj a3 ⟶ HB.obj e2)
    (n3 : Rf.obj a2 ⟶ Pf.obj a2) (q1 : Rf.obj a1 ⟶ Pf.obj a1)
    (r1 : Pf.obj a2 ⟶ HB.obj e1)
    (s1 : Pf.obj a1 ⟶ d1) (s2 : d1 ⟶ HB.obj e0)
    (t1 : d1 ⟶ d2) (u1 : d2 ⟶ HB.obj e6) (t2 : d2 ⟶ d3) (u2 : d3 ⟶ HB.obj e5)
    (fi : e0 ⟶ e1) (w : e1 ⟶ e2) (phi : e2 ⟶ e3) (sig : e3 ⟶ e4)
    (qn : e0 ⟶ e6) (qr : e6 ⟶ e5) (kp : e5 ⟶ e4) (cehri : Rf.obj a1 ⟶ d3)
    (h1 : Rf.map kH ≫ m3 = n3 ≫ Pf.map kH)
    (h2 : Rf.map dq ≫ n3 = q1 ≫ Pf.map dq)
    (h3 : Pf.map kH ≫ m4 = r1 ≫ HB.map w)
    (h4 : Pf.map dq ≫ r1 = s1 ≫ s2 ≫ HB.map fi)
    (h5 : fi ≫ w ≫ phi ≫ sig = qn ≫ qr ≫ kp)
    (h6a : s2 ≫ HB.map qn = t1 ≫ u1)
    (h6b : u1 ≫ HB.map qr = t2 ≫ u2)
    (h7 : q1 ≫ s1 ≫ t1 ≫ t2 = cehri) :
    Rf.map (dq ≫ kH) ≫ m3 ≫ (m4 ≫ HB.map phi) ≫ HB.map sig =
      cehri ≫ u2 ≫ HB.map kp := by
  rw [Rf.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Rf.map kH) m3, h1]
  simp only [Category.assoc]
  rw [← Category.assoc (Rf.map dq) n3, h2]
  simp only [Category.assoc]
  rw [← Category.assoc (Pf.map kH) m4, h3]
  simp only [Category.assoc]
  rw [← Category.assoc (Pf.map dq) r1, h4]
  simp only [Category.assoc, ← HB.map_comp]
  rw [h5]
  simp only [HB.map_comp]
  rw [← Category.assoc s2 (HB.map qn), h6a]
  simp only [Category.assoc]
  rw [← Category.assoc u1 (HB.map qr), h6b]
  simp only [Category.assoc]
  rw [show q1 ≫ s1 ≫ t1 ≫ t2 ≫ u2 ≫ HB.map kp =
    (q1 ≫ s1 ≫ t1 ≫ t2) ≫ u2 ≫ HB.map kp from by simp only [Category.assoc], h7]

/-- **The degree-`p` reading of the square of [Stacks, Tag 0G7U] for an open immersion.**  The
restriction to `W` of the degree-`p` cohomology of the comparison of [Stacks, Tag 0G7L],
followed by the excision `Stacks.Gysin.supportCohomologyRestrictIso` of [Stacks, Tag 0G78] on
degree-`p` cohomology sheaves, is the same comparison for the restricted equations and `ℱ|_W`,
read across `cechExtendHomologyRestrictIso`. -/
theorem map_extendHomologyToSupport_comp_supportCohomologyRestrictIso (p : ℕ) :
    (Scheme.Modules.restrictFunctor W.ι).map (extendHomologyToSupport e F hT hTe p) ≫
        (supportCohomologyRestrictIso W hT hT' (p : ℤ) F).hom =
      (cechExtendHomologyRestrictIso W e F (p : ℤ)).hom ≫
        extendHomologyToSupport (fun j => W.ι.appTop (e j))
          ((Scheme.Modules.restrictFunctor W.ι).obj F) hT' hTe' p := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso W)
  exact assembleDeg (Scheme.Modules.restrictFunctor W.ι) (modulePullback (openIncl W))
    (DerivedCategory.homologyFunctor W.toScheme.Modules (p : ℤ)) _ _ _ _ _
    ((modulePullbackRestrictIso W).inv.app _) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((cechExtendHomologyRestrictIso W e F (p : ℤ)).hom)
    ((modulePullbackRestrictIso W).inv.naturality _)
    ((modulePullbackRestrictIso W).inv.naturality _)
    ((mapDerivedCategoryHomologyIso (modulePullback (openIncl W)) (p : ℤ)).inv.naturality
      (cechToDerivedSupport e F hT hTe))
    (mapDerivedCategoryHomologyIso_inv_app_Q (modulePullback (openIncl W))
      ((cplx e F).extend ComplexShape.embeddingUpNat)
      (p : ℤ))
    (factors_inv_comp_mapDerivedCategory_cechToDerivedSupport W e F hT hTe hT' hTe')
    (homologyFunctorFactors_inv_naturality
      ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso W)
        (ComplexShape.up ℤ)).hom.app
          ((cplx e F).extend
            ComplexShape.embeddingUpNat)) (p : ℤ))
    (homologyFunctorFactors_inv_naturality (restrictExtendIso W e F).hom (p : ℤ))
    (cechExtendHomologyRestrictIso_hom_eq W e F (p : ℤ))

/-! ### The same, on the cohomology of the `ℕ`-graded Čech complex -/

/-- Inserting a cancelling pair of inverse isomorphisms, at a variable category. -/
theorem chaseInsert {C : Type*} [Category* C] {o₁ o₂ o₃ o₄ o₅ : C}
    (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (h : o₃ ⟶ o₄) (hi : o₄ ⟶ o₃) (k : o₃ ⟶ o₅)
    (hh : h ≫ hi = 𝟙 o₃) : (a ≫ b ≫ h) ≫ hi ≫ k = a ≫ b ≫ k := by
  simp [reassoc_of% hh]

/-- **The restriction to `W` of the degree-`p` cohomology of the extended alternating Čech
complex of [Stacks, Tag 0G7I] is the degree-`p` cohomology of that complex for the restricted
equations**, read on the `ℕ`-graded complexes.  This is
`cechExtendHomologyRestrictIso` conjugated by the two identifications of the cohomology of a
complex with the cohomology of its extension to the grading `ℤ`. -/
def cechHomologyRestrictIso (p : ℕ) :
    (Scheme.Modules.restrictFunctor W.ι).obj ((cplx e F).homology p) ≅
      (cplx (fun j => W.ι.appTop (e j))
        ((Scheme.Modules.restrictFunctor W.ι).obj F)).homology p :=
  (Scheme.Modules.restrictFunctor W.ι).mapIso
      (HomologicalComplex.extendHomologyIso (cplx e F) ComplexShape.embeddingUpNat
        (embeddingUpNat_f p)).symm ≪≫
    cechExtendHomologyRestrictIso W e F (p : ℤ) ≪≫
      HomologicalComplex.extendHomologyIso
        (cplx (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F))
        ComplexShape.embeddingUpNat (embeddingUpNat_f p)

/-- **The degree-`p` reading of the square of [Stacks, Tag 0G7U] for an open immersion, on the
cohomology of the `ℕ`-graded Čech complex.**  The restriction to `W` of
`Stacks.Perfect.SupportedFraction.cechHomologyToSupport`, followed by the excision of
[Stacks, Tag 0G78] on degree-`p` cohomology sheaves, is that map for the restricted equations and
`ℱ|_W`, read across `cechHomologyRestrictIso`.

This is the shape `Stacks.Perfect.SupportedFraction.supportedFractionSource_eq` consumes: the
class map of [Stacks, Tag 0G7Q] read on the coefficient module is the degree-`c` cohomology class
of the fraction `s / (f₁ ⋯ f_c)` followed by this map. -/
theorem map_cechHomologyToSupport_comp_supportCohomologyRestrictIso (p : ℕ) :
    (Scheme.Modules.restrictFunctor W.ι).map (cechHomologyToSupport e F hT hTe p) ≫
        (supportCohomologyRestrictIso W hT hT' (p : ℤ) F).hom =
      (cechHomologyRestrictIso W e F p).hom ≫
        cechHomologyToSupport (fun j => W.ι.appTop (e j))
          ((Scheme.Modules.restrictFunctor W.ι).obj F) hT' hTe' p := by
  refine Eq.trans (congrArg (fun z => z ≫ (supportCohomologyRestrictIso W hT hT' (p : ℤ) F).hom)
    ((Scheme.Modules.restrictFunctor W.ι).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      (Scheme.Modules.restrictFunctor W.ι).map
        (HomologicalComplex.extendHomologyIso (cplx e F) ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv ≫ z)
    (map_extendHomologyToSupport_comp_supportCohomologyRestrictIso W e F hT hTe hT' hTe' p)) ?_
  exact (chaseInsert _ _ _ _ _
    ((HomologicalComplex.extendHomologyIso
        (cplx (fun j => W.ι.appTop (e j)) ((Scheme.Modules.restrictFunctor W.ι).obj F))
        ComplexShape.embeddingUpNat (embeddingUpNat_f p)).hom_inv_id)).symm

end Degree

end Stacks.Gysin

end
