module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImagePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceBaseChangeIdentification
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleBaseChangeConjugate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelMayerVietoris
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectivesEssentiallySmall

/-!
# The étale higher direct images along a quasi-compact quasi-separated morphism

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site whose underlying morphism `r` is
quasi-compact and quasi-separated.  The higher direct images `R ⁿ (ε_a)_*(𝓜)` of an
`𝒪_{X_étale}`-module quasi-coherent on the site are quasi-coherent on the site, and there is an
isomorphism

`R ⁿ (ε_a)_*(𝓕ᵃ) ≅ (R ⁿ r_* 𝓕)ᵃ`, naturally in the quasi-coherent `𝒪_X`-module `𝓕`.

## Main definitions

* `higherDirectImageAssociatedModuleIso`: the natural isomorphism `R ⁱ (ε_a)_*(𝓕ᵃ) ≅ (R ⁱ r_* 𝓕)ᵃ`
  on quasi-coherent `𝒪_X`-modules.

## Main results

* `isQuasicoherentOnSite_rightDerived_pushforward_of_qcqs`: the higher direct images along a
  quasi-compact quasi-separated morphism of a module quasi-coherent on the site are
  quasi-coherent on the site.

## References

* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

open Stacks.CechSite.SheafLevel (directImage)

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-! ### The functors `j_{V,*} j_V^{-1} ⋙ (ε_a)_*` -/

section DirectImage

variable (U : SmallEtale B X.obj X.property)

/-- Restriction of `𝒪_{X_étale}`-modules to the slice at `U` preserves finite limits. -/
instance preservesFiniteLimits_overFunctor_structureSheaf :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property) U) :=
  (Stacks.Cohomology.Localization.OfEssentiallySmall.restriction_exact
    (topology B X.obj X.property) (structureSheaf B X.obj X.property) U).1

/-- Restriction of `𝒪_{X_étale}`-modules to the slice at `U` preserves injective objects. -/
instance preservesInjectiveObjects_overFunctor_structureSheaf :
    (SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
      U).PreservesInjectiveObjects :=
  Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor_of_essentiallySmall
    (topology B X.obj X.property) (structureSheaf B X.obj X.property) U

/-- The functor `j_{U,*} j_U^{-1}` on `𝒪_{X_étale}`-modules preserves injective objects. -/
instance preservesInjectiveObjects_directImage :
    (directImage (structureSheaf B X.obj X.property) U).PreservesInjectiveObjects :=
  inferInstanceAs (SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property) U ⋙
    SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := structureSheaf B X.obj X.property)
        U)).PreservesInjectiveObjects

/-- **`j_{U,*} j_U^{-1}` followed by `(ε_a)_*` is restriction to `U_étale` followed by the direct
image along `U ⟶ X ⟶ Y`.** -/
def directImageCompPushforwardIso :
    directImage (structureSheaf B X.obj X.property) U ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ≅
      objRestrict B X.obj X.property U ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (U.obj.hom ≫ a)) :=
  Functor.isoWhiskerRight (directImageIsoPushforward B X.obj X.property U)
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (objRestrict B X.obj X.property U)
      (SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B a)
          (smallEtaleStructureMapRing B U.obj.hom) ≪≫
        (smallEtalePushforwardCompIso B U.obj.hom a).symm)

/-- **The right derived functors of `j_{U,*} j_U^{-1} ⋙ (ε_a)_*` are the higher direct images
along `U ⟶ X ⟶ Y` of the restriction to `U_étale`.** -/
def rightDerivedDirectImageCompObjIso (n : ℕ)
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    ((directImage (structureSheaf B X.obj X.property) U ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n).obj M ≅
      ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (U.obj.hom ≫ a))).rightDerived
        n).obj ((objRestrict B X.obj X.property U).obj M) :=
  haveI hacyc : Stacks.RightDerivedComp.acyclic (objRestrict B X.obj X.property U) M := fun q hq ↦
    Functor.isZero_rightDerived_of_exactFunctor _
      ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩) M q hq
  (Functor.rightDerivedIsoOfNatIso (directImageCompPushforwardIso B a U) n).app M ≪≫
    Stacks.RightDerivedComp.objIso (objRestrict B X.obj X.property U) (injectiveResolution M) hacyc
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (U.obj.hom ≫ a))) n

/-- **The right derived functors of `j_{U,*} j_U^{-1} ⋙ (ε_a)_*` preserve quasi-coherence on the
site when `U ⟶ X ⟶ Y` is quasi-compact and separated.** -/
theorem isQuasicoherentOnSite_rightDerived_directImageComp_of_isSeparatedHom
    [QuasiCompact (schemeHom B (U.obj.hom ≫ a))] [IsSeparated (schemeHom B (U.obj.hom ≫ a))]
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (hM : M.IsQuasicoherentOnSite)
    (n : ℕ) :
    (((directImage (structureSheaf B X.obj X.property) U ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n).obj
          M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (rightDerivedDirectImageCompObjIso B a U n M).symm
    (isQuasicoherentOnSite_rightDerived_pushforward_of_quasiCompact_of_isSeparatedHom B
      (U.obj.hom ≫ a) _ (isQuasicoherentOnSite_objRestrict B X.obj X.property U M hM) n)

end DirectImage

/-! ### The Mayer–Vietoris square of two opens -/

section OpensSquare

variable {X : B.Scheme} (S U : X.obj.Opens)

/-- The square of the small étale site of `X` cut out by two opens `S`, `U` of `X`: their
intersection, the two opens, and their union. -/
@[simps]
def opensSquare : Square (SmallEtale B X.obj X.property) where
  X₁ := (opensToSmallEtale B X.obj X.property).obj (S ⊓ U)
  X₂ := (opensToSmallEtale B X.obj X.property).obj S
  X₃ := (opensToSmallEtale B X.obj X.property).obj U
  X₄ := (opensToSmallEtale B X.obj X.property).obj (S ⊔ U)
  f₁₂ := (opensToSmallEtale B X.obj X.property).map (homOfLE inf_le_left)
  f₁₃ := (opensToSmallEtale B X.obj X.property).map (homOfLE inf_le_right)
  f₂₄ := (opensToSmallEtale B X.obj X.property).map (homOfLE le_sup_left)
  f₃₄ := (opensToSmallEtale B X.obj X.property).map (homOfLE le_sup_right)
  fac := Subsingleton.elim _ _

/-- The morphism from the open `S` to `S ⊔ U` in `opensSquare` is a monomorphism. -/
instance mono_opensSquare_f₂₄ : Mono (opensSquare B S U).f₂₄ :=
  ⟨fun _ _ _ ↦ (subsingleton_hom_opensToSmallEtale B X.obj X.property _ S).elim _ _⟩

/-- The morphism from the open `U` to `S ⊔ U` in `opensSquare` is a monomorphism. -/
instance mono_opensSquare_f₃₄ : Mono (opensSquare B S U).f₃₄ :=
  ⟨fun _ _ _ ↦ (subsingleton_hom_opensToSmallEtale B X.obj X.property _ U).elim _ _⟩

/-- The square of opens `S ⊓ U ⟶ S, U ⟶ S ⊔ U` is a pullback square of opens. -/
theorem isPullback_opens_inf_sup :
    IsPullback (homOfLE (inf_le_left : S ⊓ U ≤ S)) (homOfLE (inf_le_right : S ⊓ U ≤ U))
      (homOfLE (le_sup_left : S ≤ S ⊔ U)) (homOfLE (le_sup_right : U ≤ S ⊔ U)) where
  w := Subsingleton.elim _ _
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ ↦ Subsingleton.elim _ _) (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)⟩

/-- The square `opensSquare` of the small étale site is a pullback square. -/
theorem isPullback_opensSquare : (opensSquare B S U).IsPullback :=
  (isPullback_opens_inf_sup B S U).map (opensToSmallEtale B X.obj X.property)

/-- The opens `S` and `U` cover `S ⊔ U` in the small étale site: the sieve generated by the two
inclusions is a covering sieve. -/
theorem ofTwoArrows_opensSquare_mem :
    Sieve.ofTwoArrows (opensSquare B S U).f₂₄ (opensSquare B S U).f₃₄ ∈
      topology B X.obj X.property (opensSquare B S U).X₄ := by
  have hR : Sieve.ofTwoArrows (homOfLE (le_sup_left : S ≤ S ⊔ U))
      (homOfLE (le_sup_right : U ≤ S ⊔ U)) ∈ Opens.grothendieckTopology X.obj (S ⊔ U) := by
    intro x hx
    rcases TopologicalSpace.Opens.mem_sup.1 hx with hS | hU
    · exact ⟨S, homOfLE le_sup_left, Sieve.ofArrows_mk _ _ WalkingPair.left, hS⟩
    · exact ⟨U, homOfLE le_sup_right, Sieve.ofArrows_mk _ _ WalkingPair.right, hU⟩
  refine (topology B X.obj X.property).superset_covering ?_
    ((coverPreserving_opensToSmallEtale B X.obj X.property).cover_preserve hR)
  rintro Z g ⟨W, k, h, hk, -⟩
  obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  have hsub := subsingleton_hom_opensToSmallEtale B X.obj X.property Z (S ⊔ U)
  cases j
  · rw [show g = (h ≫ (opensToSmallEtale B X.obj X.property).map b) ≫
        (opensSquare B S U).f₂₄ from hsub.elim _ _]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ WalkingPair.left) _
  · rw [show g = (h ≫ (opensToSmallEtale B X.obj X.property).map b) ≫
        (opensSquare B S U).f₃₄ from hsub.elim _ _]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ WalkingPair.right) _

end OpensSquare

/-! ### The affine base -/

section AffineBase

/-- **The higher direct images along a quasi-compact quasi-separated `a` over an affine base are
quasi-coherent on the site**, for a module quasi-coherent on the site. -/
theorem isQuasicoherentOnSite_rightDerived_pushforward_of_isAffine_of_qcqs
    [AlgebraicGeometry.IsAffine Y.obj]
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (hM : M.IsQuasicoherentOnSite)
    (n : ℕ) :
    (((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n).obj
      M).IsQuasicoherentOnSite := by
  have : CompactSpace X.obj := (quasiCompact_iff_compactSpace (schemeHom B a)).1 inferInstance
  have : QuasiSeparatedSpace X.obj :=
    (quasiSeparated_iff_quasiSeparatedSpace (schemeHom B a)).1 inferInstance
  let π := SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)
  let o := opensToSmallEtale B X.obj X.property
  have hsep : ∀ W : X.obj.Opens, IsCompact (W : Set X.obj) →
      IsSeparated (W.ι ≫ schemeHom B a) → ∀ m, (((directImage (structureSheaf B X.obj X.property)
        (o.obj W) ⋙ π).rightDerived m).obj M).IsQuasicoherentOnSite := fun W hW hs m ↦ by
    have : QuasiCompact (schemeHom B ((o.obj W).obj.hom ≫ a)) :=
      (quasiCompact_iff_compactSpace (W.ι ≫ schemeHom B a)).2 (isCompact_iff_compactSpace.1 hW)
    have : IsSeparated (schemeHom B ((o.obj W).obj.hom ≫ a)) := hs
    exact isQuasicoherentOnSite_rightDerived_directImageComp_of_isSeparatedHom B a (o.obj W) M hM m
  have haff : ∀ U : X.obj.affineOpens, ∀ m, (((directImage (structureSheaf B X.obj X.property)
      (o.obj U) ⋙ π).rightDerived m).obj M).IsQuasicoherentOnSite := fun U ↦ by
    have : AlgebraicGeometry.IsAffine (U : X.obj.Opens).toScheme := U.2
    exact hsep U U.2.isCompact inferInstance
  have hP : ∀ m, (((directImage (structureSheaf B X.obj X.property) (o.obj ⊤) ⋙ π).rightDerived
      m).obj M).IsQuasicoherentOnSite := by
    refine compact_open_induction_on (P := fun S ↦ ∀ m, (((directImage
      (structureSheaf B X.obj X.property) (o.obj S) ⋙ π).rightDerived m).obj
        M).IsQuasicoherentOnSite) ⊤ isCompact_univ (haff ⟨⊥, isAffineOpen_bot _⟩)
      fun S hS U hPS m ↦ ?_
    have : AlgebraicGeometry.IsAffine (U : X.obj.Opens).toScheme := U.2
    have hSU : IsSeparated ((S ⊓ (U : X.obj.Opens)).ι ≫ schemeHom B a) := by
      rw [← Scheme.homOfLE_ι X.obj (inf_le_right : S ⊓ (U : X.obj.Opens) ≤ U), Category.assoc]
      infer_instance
    exact Stacks.CechSite.SheafLevel.prop_rightDerived_directImage_comp_of_isPullback
      (structureSheaf B X.obj X.property) π (isPullback_opensSquare B S U)
      (ofTwoArrows_opensSquare_mem B S U) (qcohOnSite B Y.obj Y.property) M
      (hsep _ (QuasiSeparatedSpace.inter_isCompact _ _ S.isOpen hS U.1.isOpen U.2.isCompact) hSU)
      hPS (haff U) m
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Functor.rightDerivedIsoOfNatIso
      (Functor.isoWhiskerRight (Stacks.CechSite.SheafLevel.directImageIsoOfIsTerminal
        (structureSheaf B X.obj X.property) (isTerminalOpensObjTop B X.obj X.property)).symm π ≪≫
          Functor.leftUnitor π) n).app M) (hP n)

end AffineBase

/-! ### A general base -/

section GeneralBase

/-- The restriction of a higher direct image along a quasi-compact quasi-separated `a` to the
slice at an object with affine scheme is quasi-coherent on the site, for a module quasi-coherent
on the site. -/
theorem isQuasicoherentOnSite_over_rightDerived_pushforward_of_isAffine_of_qcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (V : SmallEtale B Y.obj Y.property)
    (hV : AlgebraicGeometry.IsAffine (objScheme B Y.obj Y.property V))
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    ((((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
      V).IsQuasicoherentOnSite := by
  have := hV
  have : QuasiCompact (schemeHom B (objBaseChangeHom B a V)) :=
    quasiCompact_smallEtaleBaseChange_proj B a V
  have : QuasiSeparated (schemeHom B (objBaseChangeHom B a V)) :=
    quasiSeparated_smallEtaleBaseChange_proj B a V
  have hqcW : ((objRestrictFunctor B X.obj X.property
      ((smallEtaleBaseChange B a).obj V)).obj
        (𝓕.over ((smallEtaleBaseChange B a).obj V))).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_objRestrict_iff B X.obj X.property
      ((smallEtaleBaseChange B a).obj V) 𝓕).2
      (Stacks.SheafOfModules.isQuasicoherent_over 𝓕 h𝓕 _)
  have hqc := isQuasicoherentOnSite_rightDerived_pushforward_of_isAffine_of_qcqs
      B (objBaseChangeHom B a V) _ hqcW n
  have hiff : ((objRestrictFunctor B Y.obj Y.property V).obj
        ((((SheafOfModules.pushforward.{u}
          (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
            V)).IsQuasicoherentOnSite ↔
      ((((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
          V).IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
      (localizationEquivalence B Y.obj Y.property V)
      ((structureSheaf B Y.obj Y.property).over V) _
  exact hiff.1 <| SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((((objRestrictFunctor B Y.obj Y.property V).mapIso
        (rightDerivedPushforwardOverFunctorObjIso B a V 𝓕 n)) ≪≫
      rightDerivedLocalizedPushforwardObjIso B a V
        (𝓕.over ((smallEtaleBaseChange B a).obj V)) n).symm) hqc

/-- **The higher direct images along a quasi-compact quasi-separated morphism of a module
quasi-coherent on the site are quasi-coherent on the site**, over an arbitrary base. -/
theorem isQuasicoherentOnSite_rightDerived_pushforward_of_qcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    (((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffines B Y.obj Y.property _).2
    (isCartesianOnAffines_rightDerived_pushforward_of_forall_affineOpens B a 𝓕 n fun U ↦
      isQuasicoherentOnSite_over_rightDerived_pushforward_of_isAffine_of_qcqs
        B a ((opensToSmallEtale B Y.obj Y.property).obj (U : Y.obj.Opens)) U.2 𝓕 h𝓕 n)

end GeneralBase

/-! ### The comparison with the higher direct images of `𝒪_X`-modules -/

section Comparison

variable [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]

/-- For a morphism `f : T ⟶ S` of schemes of a big étale site whose underlying morphism of
schemes is quasi-compact and quasi-separated, and every degree `i`, there is a canonical
isomorphism

`R ⁱ f_{small, *}(𝓕ᵃ) ≅ (R ⁱ f_* 𝓕)ᵃ`

natural in the quasi-coherent `𝒪_T`-module `𝓕`, where `f_small = ε_f` is the morphism of small
étale ringed sites of [Stacks, Tag 070R] (2), `R ⁱ f_{small, *}` is the right derived functor of
its direct image of sheaves of modules, `R ⁱ f_*` that of the direct image of `𝒪_T`-modules, and
`𝓖 ↦ 𝓖ᵃ` the associated module of [Stacks, Tag 03DU] (4) at `τ = étale`. -/
@[stacks 071N "the ÉTALE topology of the two the tag states (\"for either the étale or Zariski \
topology\"): for f quasi-compact and quasi-separated, in every degree i, as an isomorphism of \
functors on the quasi-coherent O_T-modules (hence natural in F).  The ZARISKI topology is \
SmallZariski.higherDirectImageAssociatedModulePlusIntIso"]
def higherDirectImageAssociatedModuleIso (i : ℕ) :
    associatedModuleOnQuasicoherent B (X := X) ⋙
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived i ≅
      Stacks.Cohomology.AffineBase.quasicoherentInclusion X.obj ⋙
        (Scheme.Modules.pushforward (schemeHom B a)).rightDerived i ⋙
          associatedModule B Y.obj Y.property :=
  higherDirectImageAssociatedModuleIsoOfIsQuasicoherentOnSite B a
    (fun 𝓕 q ↦ isQuasicoherentOnSite_rightDerived_pushforward_of_qcqs B a _
      (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B X.obj X.property 𝓕.obj
        𝓕.property) q) i

/-- The component `R ⁱ f_{small, *}(𝓕ᵃ) ≅ (R ⁱ f_* 𝓕)ᵃ` of `higherDirectImageAssociatedModuleIso`
at a quasi-coherent module `𝓕`. -/
def higherDirectImageAssociatedModuleObjIso (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] (i : ℕ) :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived i).obj
        ((associatedModule B X.obj X.property).obj 𝓕) ≅
      (associatedModule B Y.obj Y.property).obj
        (((Scheme.Modules.pushforward (schemeHom B a)).rightDerived i).obj 𝓕) :=
  (higherDirectImageAssociatedModuleIso B a i).app ⟨𝓕, inferInstance⟩

/-- **Naturality of `higherDirectImageAssociatedModuleObjIso` in the module.** -/
theorem higherDirectImageAssociatedModuleObjIso_naturality {𝓕 𝓖 : X.obj.Modules}
    [𝓕.IsQuasicoherent] [𝓖.IsQuasicoherent] (α : 𝓕 ⟶ 𝓖) (i : ℕ) :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived i).map
          ((associatedModule B X.obj X.property).map α) ≫
        (higherDirectImageAssociatedModuleObjIso B a 𝓖 i).hom =
      (higherDirectImageAssociatedModuleObjIso B a 𝓕 i).hom ≫
        (associatedModule B Y.obj Y.property).map
          (((Scheme.Modules.pushforward (schemeHom B a)).rightDerived i).map α) :=
  (higherDirectImageAssociatedModuleIso B a i).hom.naturality (X := ⟨𝓕, inferInstance⟩)
    (Y := ⟨𝓖, inferInstance⟩) (ObjectProperty.homMk α)

end Comparison

end AlgebraicGeometry.SmallEtale

end
