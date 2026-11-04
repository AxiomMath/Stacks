module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHom
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHom
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# The trace of the right adjoint of pushforward for a closed immersion

Let `i : Z ⟶ X` be a closed immersion and let `a` be a right adjoint of
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_X)`. The trace map `Ri_* a(K) ⟶ K`, that is the counit of `a`,
agrees with the composite

`Ri_* a(K) = Ri_* R ℰom(𝒪_Z, K) = R ℰom_{𝒪_X}(i_* 𝒪_Z, K) ⟶ K`

whose first identification is the comparison map of [Stacks, Tag 0A9X], whose second is
[Stacks, Tag 0A77], and whose last arrow is induced by the unit `𝒪_X ⟶ i_* 𝒪_Z`.

## Main definitions

* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.evaluationAtOne` is the map
  `ℰom_{𝒪_X}(i_* 𝒪_Z, -) ⟶ 𝟭` induced by the unit `𝒪_X ⟶ i_* 𝒪_Z`, namely evaluation of a
  local homomorphism at the section `1`, as `evaluationAtOne_app_val_app` records.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedEvaluationAtOne` is
  its right derived form `R ℰom_{𝒪_X}(i_* 𝒪_Z, -) ⟶ 𝟭` on `D(𝒪_X)`.

## Main results

* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedEvaluationAtOne_fac`
  and `derivedEvaluationAtOne_uniq` say that `derivedEvaluationAtOne` is the unique
  transformation out of the right derived functor which restricts to `evaluationAtOne`.
* `derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne`, in
  the same namespace: the counit of [Stacks, Tag 0A76] is the isomorphism of [Stacks, Tag 0A77]
  followed by the derived evaluation at one. This is the triangle of [Stacks, Tag 0B6M] on the
  whole of `D(𝒪_X)`, before the right adjoint `a` is brought in.
* `Stacks.Duality.rightAdjointToDerivedSheafHom_comp_derivedEvaluationAtOne`: **the statement of
  [Stacks, Tag 0B6M]**, that the trace of a right adjoint `a` of `Ri_*` is the comparison map of
  [Stacks, Tag 0A9X] followed by [Stacks, Tag 0A77] followed by the map induced by the unit.
* `Stacks.Duality.isIso_rightAdjointToDerivedSheafHom_app`: on bounded-below complexes with
  quasi-coherent cohomology the comparison map of [Stacks, Tag 0A9X] is invertible, so the two
  identifications of the displayed composite are isomorphisms.

## Implementation notes

The arrow `R ℰom_{𝒪_X}(i_* 𝒪_Z, K) ⟶ K` induced by the unit `𝒪_X ⟶ i_* 𝒪_Z` is built here from
the underived data only. Underived, the map induced by the unit followed by the identification
`ℰom_{𝒪_X}(𝒪_X, -) = 𝟭` is evaluation of a local homomorphism at the section `1`, which by
[Stacks, Tag 0A75] is the counit of `i_* ⊣ ℰom(𝒪_Z, -)` read through the internal Hom
identification: that is `evaluationAtOne`, and `evaluationAtOne_app_val_app` computes its values
on sections as evaluation at `1`. Its derived form is obtained from the universal property of
the right derived functor, so nothing is chosen and `derivedEvaluationAtOne_uniq` pins it down.

The triangle is then proved by the uniqueness half of the same universal property, applied to
`Ri_* ∘ R ℰom(𝒪_Z, -)`: both sides are transformations out of a right derived functor, so they
agree as soon as they agree after the comparison map out of the homotopy category, where the
statement is the formal cancellation of the complex-level internal Hom identification against
its inverse. The two inputs are the compatibility clause
`derivedModulePushforwardDerivedSheafHomExactSupportIso_fac_app` of [Stacks, Tag 0A77] and the
description `derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app` of the counit of
[Stacks, Tag 0A76].

Bringing in the right adjoint `a` is then the mate identity: the comparison map of
[Stacks, Tag 0A9X] is by construction the transpose of the trace of `a` along the adjunction of
[Stacks, Tag 0A76], so pushing it forward and composing with that adjunction's counit returns
the trace. Consequently the triangle holds for every `K` in `D_QCoh(𝒪_X)` and needs neither
pseudo-coherence of `i` nor boundedness of `K`; those enter only through
`isIso_rightAdjointToDerivedSheafHom_app`, which is [Stacks, Tag 0A9X] and rests, exactly as
`Stacks.Duality.isDerivedSheafHomRightAdjoint_of_pseudoCoherent` does, on part (1) of
[Stacks, Tag 0A78].

## References

* [Stacks Project, Tag 0B6M](https://stacks.math.columbia.edu/tag/0B6M)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The map `ℰom_{𝒪_X}(i_* 𝒪_Z, -) ⟶ 𝟭` induced by the unit `𝒪_X ⟶ i_* 𝒪_Z`, that is,
evaluation of a local homomorphism at the section `1`: the counit of the adjunction of
[Stacks, Tag 0A75] read through its internal Hom identification. -/
@[stacks 0B6M "the last arrow of the triangle: the map `R Eom_{O_X}(i_* O_Z, K) ⟶ K` induced
by the unit `O_X ⟶ i_* O_Z`, here underived"]
noncomputable def evaluationAtOne :
    S.homSheafFromPushforwardStructureSheaf ⟶ 𝟭 (SheafOfModules.{u} (structureSheafRing S.X)) :=
  S.modulePushforwardSheafHomExactSupportIsoHomSheaf.inv ≫
    S.modulePushforwardSheafHomExactSupportAdjunction.counit

/-- Evaluation at one, precomposed with the internal Hom identification of [Stacks, Tag 0A75],
is the counit of the adjunction `i_* ⊣ ℰom(𝒪_Z, -)`. -/
@[reassoc]
theorem modulePushforwardSheafHomExactSupportIsoHomSheaf_hom_comp_evaluationAtOne :
    S.modulePushforwardSheafHomExactSupportIsoHomSheaf.hom ≫ S.evaluationAtOne =
      S.modulePushforwardSheafHomExactSupportAdjunction.counit := by
  rw [evaluationAtOne, Iso.hom_inv_id_assoc]

/-- Evaluation at one takes a local homomorphism out of `i_* 𝒪_Z` to its value at the section
`1`, so it is the map induced by the unit `𝒪_X ⟶ i_* 𝒪_Z` followed by the identification
`ℰom_{𝒪_X}(𝒪_X, -) = 𝟭`. -/
theorem evaluationAtOne_app_val_app (F : SheafOfModules.{u} (structureSheafRing S.X))
    (U : TopologicalSpace.Opens S.X)
    (s : (S.homSheafFromPushforwardStructureSheaf.obj F).val.obj (Opposite.op U)) :
    (S.evaluationAtOne.app F).val.app (Opposite.op U) s =
      Stacks.PresheafOfModules.CoextendScalars.invSecVal (structureSheafHom S.i).hom F.val
        (Opposite.op U) s :=
  (S.modulePushforwardSheafHomExactSupportAdjunction_counit_app F U
      ((S.modulePushforwardSheafHomExactSupportIsoHomSheaf.inv.app F).val.app
        (Opposite.op U) s)).trans
    (congrArg (Stacks.PresheafOfModules.CoextendScalars.invSecVal (structureSheafHom S.i).hom
        F.val (Opposite.op U))
      (congrArg (fun f => f.val.app (Opposite.op U) s)
        (S.modulePushforwardSheafHomExactSupportIsoHomSheaf.inv_hom_id_app F)))

/-- Evaluation at one on complexes up to homotopy: the counit of the adjunction induced by
[Stacks, Tag 0A75] on homotopy categories, read through the internal Hom identification. -/
noncomputable def mapHomotopyCategoryEvaluationAtOne :
    S.homSheafFromPushforwardStructureSheaf.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      𝟭 (HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :=
  (Functor.mapHomotopyCategoryCompIso S.modulePushforwardSheafHomExactSupportIsoHomSheaf
      (ComplexShape.up ℤ)).inv ≫
    (Adjunction.mapHomotopyCategoryAdjunction
      S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit

/-- Evaluation at one on complexes up to homotopy, precomposed with the internal Hom
identification of [Stacks, Tag 0A75], is the counit of the induced adjunction. -/
@[reassoc]
theorem mapHomotopyCategoryCompIso_hom_comp_mapHomotopyCategoryEvaluationAtOne :
    (Functor.mapHomotopyCategoryCompIso S.modulePushforwardSheafHomExactSupportIsoHomSheaf
          (ComplexShape.up ℤ)).hom ≫ S.mapHomotopyCategoryEvaluationAtOne =
      (Adjunction.mapHomotopyCategoryAdjunction
        S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit := by
  rw [mapHomotopyCategoryEvaluationAtOne, Iso.hom_inv_id_assoc]

/-- Evaluation at one, as a transformation out of the internal Hom on complexes up to homotopy
into the localization: the datum from which its right derived form is constructed. -/
noncomputable def derivedEvaluationAtOneComparison :
    S.homSheafFromPushforwardStructureSheaf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :=
  Functor.whiskerRight S.mapHomotopyCategoryEvaluationAtOne DerivedCategory.Qh

/-- The components of `derivedEvaluationAtOneComparison` are the localizations of the components
of evaluation at one on complexes up to homotopy. -/
theorem derivedEvaluationAtOneComparison_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    S.derivedEvaluationAtOneComparison.app M =
      DerivedCategory.Qh.map (S.mapHomotopyCategoryEvaluationAtOne.app M) :=
  rfl

/-- The map `R ℰom_{𝒪_X}(i_* 𝒪_Z, -) ⟶ 𝟭` on `D(𝒪_X)` induced by the unit `𝒪_X ⟶ i_* 𝒪_Z`: the
transformation out of the right derived functor which restricts to evaluation at one. -/
@[stacks 0B6M "the last arrow of the triangle, constructed from the underived evaluation at the
section `1` by the universal property of the right derived functor"]
noncomputable def derivedEvaluationAtOne :
    S.derivedHomSheafFromPushforwardStructureSheaf ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :=
  S.derivedHomSheafFromPushforwardStructureSheaf.rightDerivedDesc
    S.derivedHomSheafFromPushforwardStructureSheafComparison
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))
    (𝟭 _) S.derivedEvaluationAtOneComparison

/-- The derived evaluation at one restricts to evaluation at one on complexes up to homotopy. -/
@[reassoc]
theorem derivedEvaluationAtOne_fac :
    S.derivedHomSheafFromPushforwardStructureSheafComparison ≫
        Functor.whiskerLeft DerivedCategory.Qh S.derivedEvaluationAtOne =
      S.derivedEvaluationAtOneComparison :=
  Functor.rightDerived_fac _ _ _ _ _

/-- The componentwise form of `derivedEvaluationAtOne_fac`. -/
@[reassoc]
theorem derivedEvaluationAtOne_fac_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    S.derivedHomSheafFromPushforwardStructureSheafComparison.app M ≫
        S.derivedEvaluationAtOne.app (DerivedCategory.Qh.obj M) =
      S.derivedEvaluationAtOneComparison.app M :=
  Functor.rightDerived_fac_app _ _ _ _ _ M

/-- The derived evaluation at one is the unique transformation out of the right derived functor
`R ℰom_{𝒪_X}(i_* 𝒪_Z, -)` which restricts to evaluation at one. -/
theorem derivedEvaluationAtOne_uniq
    (t : S.derivedHomSheafFromPushforwardStructureSheaf ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))))
    (ht : S.derivedHomSheafFromPushforwardStructureSheafComparison ≫
        Functor.whiskerLeft DerivedCategory.Qh t = S.derivedEvaluationAtOneComparison) :
    t = S.derivedEvaluationAtOne :=
  Functor.rightDerived_ext _ S.derivedHomSheafFromPushforwardStructureSheafComparison
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))
    _ t S.derivedEvaluationAtOne (by rw [ht, derivedEvaluationAtOne_fac])

/-- The components of the comparison map exhibiting `Ri_* ∘ R ℰom(𝒪_Z, -)` as a right derived
functor are the pushforwards of the components of the comparison map for `R ℰom(𝒪_Z, -)`. -/
theorem derivedModulePushforwardComparison_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    S.derivedModulePushforwardComparison.app M =
      (modulePushforward S.i).mapDerivedCategory.map
        (S.derivedSheafHomExactSupportComparison.app M) :=
  Category.comp_id _

/-- The identification of [Stacks, Tag 0A75] on the homotopy category, spelled out as the
composite of isomorphisms it is defined to be. -/
private theorem mapHomotopyCategoryPushforwardSheafHomExactSupportIso_eq :
    S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso =
      Functor.associator (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh (modulePushforward S.i).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ))
          (modulePushforward S.i).mapDerivedCategoryFactorsh ≪≫
        (Functor.associator (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ))
          ((modulePushforward S.i).mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.mapHomotopyCategoryCompIso S.modulePushforwardSheafHomExactSupportIsoHomSheaf
            (ComplexShape.up ℤ)) DerivedCategory.Qh :=
  rfl

/-- The components of the identification of [Stacks, Tag 0A75] on the homotopy category: the
factorization of `Ri_*` through the localization, followed by the localization of the
degreewise internal Hom identification. -/
theorem mapHomotopyCategoryPushforwardSheafHomExactSupportIso_hom_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom.app M =
      (modulePushforward S.i).mapDerivedCategoryFactorsh.hom.app
          ((S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            S.modulePushforwardSheafHomExactSupportIsoHomSheaf
              (ComplexShape.up ℤ)).hom.app M) := by
  rw [S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]

/-- The identification of [Stacks, Tag 0A75] on the homotopy category, followed by evaluation at
one, is the counit of the adjunction induced on homotopy categories, localized. -/
theorem mapHomotopyCategoryPushforwardSheafHomExactSupportIso_hom_app_comp
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom.app M ≫
        S.derivedEvaluationAtOneComparison.app M =
      (modulePushforward S.i).mapDerivedCategoryFactorsh.hom.app
          ((S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction
              (ComplexShape.up ℤ)).counit.app M) := by
  rw [S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso_hom_app M, Category.assoc,
    S.derivedEvaluationAtOneComparison_app M, ← Functor.map_comp, ← NatTrans.comp_app,
    S.mapHomotopyCategoryCompIso_hom_comp_mapHomotopyCategoryEvaluationAtOne]

/-- After the comparison maps out of the homotopy category, the counit of [Stacks, Tag 0A76]
agrees with the identification of [Stacks, Tag 0A75] followed by evaluation at one. -/
theorem derivedModulePushforwardComparison_app_comp_counit
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    S.derivedModulePushforwardComparison.app M ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (DerivedCategory.Qh.obj M) =
      S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom.app M ≫
        S.derivedEvaluationAtOneComparison.app M :=
  (congrArg (fun t => t ≫ S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
      (DerivedCategory.Qh.obj M)) (S.derivedModulePushforwardComparison_app M)).trans
    ((S.derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app M).trans
      (S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso_hom_app_comp M).symm)

/-- **The triangle of [Stacks, Tag 0B6M] on all of `D(𝒪_X)`.** The trace `Ri_* R ℰom(𝒪_Z, K) ⟶ K`
— the counit of [Stacks, Tag 0A76] — is the isomorphism of [Stacks, Tag 0A77] followed by the
map `R ℰom_{𝒪_X}(i_* 𝒪_Z, K) ⟶ K` induced by the unit `𝒪_X ⟶ i_* 𝒪_Z`. -/
@[stacks 0B6M "the triangle at the level of ringed spaces: the trace of Tag 0A76 is the
isomorphism of Tag 0A77 followed by the map induced by the unit `O_X ⟶ i_* O_Z`. Stated for
every closed quotient morphism of ringed spaces and all of `D(O_X)`, so neither a Noetherian
hypothesis nor boundedness of `K` appears"]
theorem derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne :
    S.derivedModulePushforwardDerivedSheafHomExactSupportIso.hom ≫ S.derivedEvaluationAtOne =
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit := by
  refine Functor.rightDerived_ext
    (RF := S.derivedSheafHomExactSupport ⋙ (modulePushforward S.i).mapDerivedCategory)
    (α := S.derivedModulePushforwardComparison)
    (W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
      (ComplexShape.up ℤ))
    _ _ _ (NatTrans.ext (funext fun M => ?_))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg
    (fun t => t ≫ S.derivedEvaluationAtOne.app (DerivedCategory.Qh.obj M))
    (S.derivedModulePushforwardDerivedSheafHomExactSupportIso_fac_app M)) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg
    (fun t => S.mapHomotopyCategoryPushforwardSheafHomExactSupportIso.hom.app M ≫ t)
    (S.derivedEvaluationAtOne_fac_app M)) ?_
  exact (S.derivedModulePushforwardComparison_app_comp_counit M).symm

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace Stacks.Duality

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
  (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
    ((DerivedCategory.homologyFunctor W.Modules n).obj
      ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
  (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
  (adj : quasiCoherentDerivedPushforward i hpush ⊣ a)

/-- **Stacks Project, Tag 0B6M (Example 48.9.8).** Let `i : Z ⟶ W` be a closed immersion and let
`a` be a right adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. The trace `Ri_* a(K) ⟶ K` is the
comparison map of [Stacks, Tag 0A9X] followed by the isomorphism of [Stacks, Tag 0A77] followed
by the map `R ℰom_{𝒪_W}(i_* 𝒪_Z, K) ⟶ K` induced by the unit `𝒪_W ⟶ i_* 𝒪_Z`. -/
@[stacks 0B6M "the example: the trace of a right adjoint `a` of `Ri_*` is the comparison map of
Tag 0A9X followed by Tag 0A77 followed by the map induced by the unit `O_W ⟶ i_* O_Z`. Since
Tag 0A9X enters as its comparison map rather than as an isomorphism, the statement needs neither
pseudo-coherence of `i`, nor part (1) of Tag 0A6H, nor boundedness, and holds for every `K` in
`D_QCoh(O_W)`"]
theorem rightAdjointToDerivedSheafHom_comp_derivedEvaluationAtOne
    (K : quasiCoherentDerivedCategory W) :
    (modulePushforward (closedQuotient i).i).mapDerivedCategory.map
          ((rightAdjointToDerivedSheafHom i hpush a adj).app K) ≫
        (closedQuotient i).derivedModulePushforwardDerivedSheafHomExactSupportIso.hom.app K.obj ≫
          (closedQuotient i).derivedEvaluationAtOne.app K.obj =
      (closedImmersionPushforwardModelIso i).hom.app ((a.obj K).obj) ≫
        (adj.counit.app K).hom := by
  have hAB : (closedQuotient
        i).derivedModulePushforwardDerivedSheafHomExactSupportIso.hom.app K.obj ≫
        (closedQuotient i).derivedEvaluationAtOne.app K.obj =
      (closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        K.obj :=
    (NatTrans.comp_app _ _ _).symm.trans (NatTrans.congr_app (closedQuotient
      i).derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne
      K.obj)
  refine Eq.trans (congrArg (fun t =>
    (modulePushforward (closedQuotient i).i).mapDerivedCategory.map
      ((rightAdjointToDerivedSheafHom i hpush a adj).app K) ≫ t) hAB) ?_
  refine Eq.trans (congrArg (fun s =>
    (modulePushforward (closedQuotient i).i).mapDerivedCategory.map s ≫
      (closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app K.obj)
    (rightAdjointToDerivedSheafHom_app i hpush a adj K)) ?_
  exact (Adjunction.homEquiv_counit _ _ _ _).symm.trans (Equiv.symm_apply_apply _ _)

/-- **Stacks Project, Tag 0A9X**, pointwise: on a bounded-below complex with quasi-coherent
cohomology the comparison map `a(K) ⟶ R𝓗om_{𝒪_W}(𝒪_Z, K)` of a pseudo-coherent closed immersion
is invertible, so it identifies the first two terms of the composite of [Stacks, Tag 0B6M].

The statement of [Stacks, Tag 0A9X] itself is
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion`. -/
theorem isIso_rightAdjointToDerivedSheafHom_app
    (hpc : PseudoCoherent i) (K : (isBoundedBelowQuasiCoherent W).FullSubcategory) :
    IsIso ((rightAdjointToDerivedSheafHom i hpush a adj).app K.obj) := by
  have hQC := AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus
    i hpc K.obj.obj ⟨K.property, K.obj.property⟩
  obtain ⟨s, hs⟩ := (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K.obj
    ⟨(closedQuotient i).derivedSheafHomExactSupport.obj K.obj.obj,
      hQC.2⟩).surjective (𝟙 _)
  refine ⟨s, ?_, hs⟩
  refine (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K.obj
    (a.obj K.obj)).injective ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (rightAdjointToDerivedSheafHom i hpush a adj).app K.obj ≫ t) hs).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

end Stacks.Duality

end
