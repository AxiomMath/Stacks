module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcULift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianInverseImageULift
public import StacksFrontier.Topology.Simplicial.QcComparisonSquare

/-!
# Stacks 09X4 on the small model of `LC_qc`, with coefficients in the universe of the spaces

Let `X` be an object of the quasi-compact site `LC_qc` of Stacks 09X2. Stacks 09X4 (1) asserts
that for an abelian sheaf `F` on `X`,

`H^n(X, F) = H^n_{qc}(X, a_X^{-1}F)`,

where `a_X : Sh(LC_qc/X) → Sh(X)` is the comparison morphism of Section 09WY. In this library it is
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcCohomologyComparisonIso`, stated on the
site `LC_qc/X` itself, whose objects form a type one universe above that of the spaces, and
therefore for abelian sheaves with values in a universe above that of the spaces.

The simplicial-site apparatus (total sites, Stacks 09X7, Stacks 09WJ) is stated on small sites
with abelian sheaves in the universe of the site, and reaches `LC_qc` through its small model
(`Stacks.Topology.LocallyQuasiCompactQcSite.smallSite`). This file proves Stacks 09X4 (1) there:
for an abelian sheaf `F` on `X` with values in the universe of the spaces,

`H^n(X, F) ≅ H^n((LC_qc)_{small}/X, a_X^{-1}F)`,

naturally in `F`, with `a_X^{-1}` the abelian inverse image of the bottom horizontal arrow of the
diagram of Stacks 0DAF (`Stacks.Topology.Simplicial.qcSmallBottomMorphism`).

## The proof

Lift the universe of the coefficients from `u` to `u + 1`. Abelian sheaf cohomology commutes
with that lift on both sites, the lift carrying injective sheaves to injective sheaves
(`Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator`). The
abelian inverse image commutes with the lift (`smallAbelianInverseImageULiftIso`), because the
sections formula of Stacks 09X3 does (`qcTopologicalInverseImageULiftIso`). In the universe `u + 1`
the comparison is Stacks 09X4 (1) on `LC_qc/X`, transported to the small model along the
identification of the two localized topoi.

## Main definitions

* `Stacks.Topology.Simplicial.qcSmallBottomMorphismOfSize`: the bottom horizontal arrow of the
  diagram of Stacks 0DAF for sheaves of sets in any universe containing that of the spaces; in
  the universe of the spaces it is `qcSmallBottomMorphism` on the nose.
* `Stacks.Topology.Simplicial.smallAbelianInverseImageULiftIso`: its abelian inverse image
  commutes with lifting the universe from `u` to `u + 1`.

## References

* [Stacks Project, Tag 09X4](https://stacks.math.columbia.edu/tag/09X4)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.UniverseLift Stacks.Topos.AbelianPushforward

universe u w t

namespace Stacks.Topology.Simplicial

open Stacks.Topology Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-! ### The bottom horizontal arrow in every coefficient universe -/

/-- **The bottom horizontal arrow of the diagram of Tag 0DAF, for sheaves of sets in any
universe containing that of the spaces**: the comparison morphism of topoi
`a_X : Sh(LC_qc/X) → Sh(X)` of Section 09WY, with `Sh(LC_qc/X)` read as the sheaves on the
localization of the small model. In the universe of the spaces it is `qcSmallBottomMorphism`. -/
def qcSmallBottomMorphismOfSize :
    MorphismOfTopoi (Sheaf (S.qcSite.smallOverTopology X) (Type (max u t)))
      (Sheaf (Opens.grothendieckTopology X.obj.obj) (Type (max u t))) :=
  (qcTopologicalMorphism.{u, w, t} S X).comp
    (MorphismOfTopoi.ofEquivalence (S.qcSite.smallOverSheafEquiv X (Type (max u t))))

/-- In the universe of the spaces the bottom horizontal arrow is `qcSmallBottomMorphism`. -/
theorem qcSmallBottomMorphismOfSize_eq :
    qcSmallBottomMorphismOfSize.{u, w, u} S X = qcSmallBottomMorphism S X :=
  rfl

/-- The direct image of the bottom horizontal arrow is restriction along `W ↦ W/X`. -/
def qcSmallBottomMorphismOfSizePushforwardIso :
    (qcSmallBottomMorphismOfSize.{u, w, t} S X).pushforward ≅
      (qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type (max u t))
        (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X) :=
  Functor.isoWhiskerRight (S.qcSite.smallOverSheafEquivInverseIso X (Type (max u t))) _ ≪≫
    Iso.refl _

/-- **Stacks 09X3 on the small model.** The inverse image of the bottom horizontal arrow is fully
faithful. -/
def qcSmallBottomMorphismOfSizeInverseImageFullyFaithful :
    (qcSmallBottomMorphismOfSize.{u, w, t} S X).inverseImage.FullyFaithful := by
  obtain ⟨hfull, hfaithful⟩ := qcTopologicalInverseImage_fullyFaithful.{u, w, t} S X
  exact (Functor.FullyFaithful.ofFullyFaithful (qcTopologicalInverseImage.{u, w, t} S X)).comp
    (S.qcSite.smallOverSheafEquiv X (Type (max u t))).fullyFaithfulFunctor

/-- The inverse image of the bottom horizontal arrow is full. -/
instance qcSmallBottomMorphismOfSize_inverseImage_full :
    (qcSmallBottomMorphismOfSize.{u, w, t} S X).inverseImage.Full :=
  (qcSmallBottomMorphismOfSizeInverseImageFullyFaithful.{u, w, t} S X).full

/-- The inverse image of the bottom horizontal arrow is faithful. -/
instance qcSmallBottomMorphismOfSize_inverseImage_faithful :
    (qcSmallBottomMorphismOfSize.{u, w, t} S X).inverseImage.Faithful :=
  (qcSmallBottomMorphismOfSizeInverseImageFullyFaithful.{u, w, t} S X).faithful

/-- The unit of the bottom horizontal arrow is invertible: its inverse image is fully faithful. -/
instance isIso_qcSmallBottomMorphismOfSize_adj_unit :
    IsIso (qcSmallBottomMorphismOfSize.{u, w, t} S X).adj.unit :=
  (qcSmallBottomMorphismOfSize.{u, w, t} S X).adj.unit_isIso_of_L_fully_faithful

/-- Restriction along `W ↦ W/X` is a right adjoint: it is the direct image of the bottom
horizontal arrow. -/
instance isRightAdjoint_qcSmallOpensFunctor_sheafPushforwardContinuous :
    ((qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type (max u t))
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).IsRightAdjoint :=
  ⟨_, ⟨(qcSmallBottomMorphismOfSize.{u, w, t} S X).adj.ofNatIsoRight
    (qcSmallBottomMorphismOfSizePushforwardIso.{u, w, t} S X)⟩⟩

/-! ### The universe lift on sheaves of sets -/

/-- Restriction along the comparison of `LC_qc/X` with its small model commutes with lifting the
universe of sheaves of sets. -/
def overPostSheafPushforwardULiftIso (P : Sheaf (S.qcSite.smallOverTopology X) (Type u)) :
    ((Over.post (X := X) S.qcSite.smallEquivalence.functor).sheafPushforwardContinuous
        (Type (u + 1)) (S.qcSite.grothendieckTopology.over X) (S.qcSite.smallOverTopology X)).obj
        ((sheafCompose (S.qcSite.smallOverTopology X) uliftFunctor.{u + 1, u}).obj P) ≅
      (sheafCompose (S.qcSite.grothendieckTopology.over X) uliftFunctor.{u + 1, u}).obj
        (((Over.post (X := X) S.qcSite.smallEquivalence.functor).sheafPushforwardContinuous
          (Type u) (S.qcSite.grothendieckTopology.over X) (S.qcSite.smallOverTopology X)).obj P) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _)

/-- The identification of the topos of `LC_qc/X` with that of the localized small model commutes
with lifting the universe of sheaves of sets. -/
def smallOverSheafEquivULiftIso (M : Sheaf (S.qcSite.grothendieckTopology.over X) (Type u)) :
    (S.qcSite.smallOverSheafEquiv X (Type (u + 1))).functor.obj
        ((sheafCompose (S.qcSite.grothendieckTopology.over X) uliftFunctor.{u + 1, u}).obj M) ≅
      (sheafCompose (S.qcSite.smallOverTopology X) uliftFunctor.{u + 1, u}).obj
        ((S.qcSite.smallOverSheafEquiv X (Type u)).functor.obj M) :=
  let E := S.qcSite.smallOverSheafEquiv X (Type u)
  let E' := S.qcSite.smallOverSheafEquiv X (Type (u + 1))
  E'.fullyFaithfulInverse.preimageIso
    (E'.unitIso.symm.app _ ≪≫
      (sheafCompose (S.qcSite.grothendieckTopology.over X) uliftFunctor.{u + 1, u}).mapIso
        (E.unitIso.app M ≪≫ (S.qcSite.smallOverSheafEquivInverseIso X (Type u)).app _) ≪≫
      (overPostSheafPushforwardULiftIso S X (E.functor.obj M)).symm ≪≫
      ((S.qcSite.smallOverSheafEquivInverseIso X (Type (u + 1))).app _).symm)

/-- **The lift of `a_X^{-1}G` is in the essential image of `a_X^{-1}` in the larger universe**,
on the small model: it is `a_X^{-1}` of the lift of `G`. -/
theorem mem_essImage_qcSmallBottomMorphismOfSize
    (G : Sheaf (Opens.grothendieckTopology X.obj.obj) (Type u)) :
    (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X).inverseImage.essImage
      ((sheafCompose (S.qcSite.smallOverTopology X) uliftFunctor.{u + 1, u}).obj
        ((qcSmallBottomMorphismOfSize.{u, w, u} S X).inverseImage.obj G)) :=
  ⟨(sheafCompose (Opens.grothendieckTopology X.obj.obj) uliftFunctor.{u + 1, u}).obj G,
    ⟨(S.qcSite.smallOverSheafEquiv X (Type (u + 1))).functor.mapIso
        (qcTopologicalInverseImageULiftIso S X G) ≪≫
      smallOverSheafEquivULiftIso S X _⟩⟩

/-! ### The abelian inverse image commutes with the universe lift -/

/-- **The abelian inverse image of the bottom horizontal arrow commutes with lifting the universe
of the coefficients** from that of the spaces to the next one. -/
def smallAbelianInverseImageULiftIso :
    uliftSheafFunctor.{u + 1, u} (Opens.grothendieckTopology X.obj.obj) ⋙
        Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X) ≅
      Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u} S X) ⋙
        uliftSheafFunctor.{u + 1, u} (S.qcSite.smallOverTopology X) :=
  haveI := isRightAdjoint_qcSmallOpensFunctor_sheafPushforwardContinuous.{u, w, u} S X
  haveI := isRightAdjoint_qcSmallOpensFunctor_sheafPushforwardContinuous.{u, w, u + 1} S X
  abelianInverseImageULiftIso.{u + 1, u} (qcSmallOpensFunctor S X)
    (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)
    (qcSmallBottomMorphismOfSize.{u, w, u} S X) (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X)
    (qcSmallBottomMorphismOfSizePushforwardIso.{u, w, u} S X)
    (qcSmallBottomMorphismOfSizePushforwardIso.{u, w, u + 1} S X) inferInstance
    (mem_essImage_qcSmallBottomMorphismOfSize S X)

/-! ### Stacks 09X4 on the small model in the universe above that of the spaces -/

section BigUniverse

/-- Abelian sheaves on the space, with values in the universe above that of the space, have
enough injectives. -/
instance enoughInjectives_sheafOpens_succ :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u + 1}) :=
  enoughInjectives_sheafOpens_site.{u, w, 0} S X

/-- Abelian sheaves on `LC_qc/X`, with values in the universe above that of the spaces, have
enough injectives. -/
instance enoughInjectives_qcSliceSheaf_succ :
    EnoughInjectives (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{u + 1}) :=
  enoughInjectives_qcSliceSheaf.{u, w, 0} S X

/-- Abelian presheaves on the space, with values in the universe above that of the space, can be
sheafified. -/
instance hasSheafify_opens_succ :
    HasSheafify (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u + 1} :=
  LocallyQuasiCompactZariskiSituation.hasSheafify_opens.{u, w, 0} S X

/-- Abelian presheaves on `LC_qc/X`, with values in the universe above that of the spaces, can be
sheafified. -/
instance hasSheafify_qcTopology_over_succ :
    HasSheafify (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{u + 1} :=
  hasSheafify_qcTopology_over_abelian.{u, w, 0} S X

/-- Global sections on the localized small model are additive. -/
instance additive_smallOverGlobalSections :
    (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections on the localized small model are additive. -/
instance additive_smallOverGlobalSections_succ :
    (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Abelian sheaves on the localized small model, with values in the universe above that of the
spaces, form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_smallOverSheaf_succ :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1}) :=
  have _ : PreservesLimits (forget AddCommGrpCat.{u + 1}) := AddCommGrpCat.forget_preservesLimits
  have _ : EssentiallySmall.{u + 1} (Over (S.qcSite.smallEquivalence.functor.obj X)) :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u, u + 1}
      (C := Over (S.qcSite.smallEquivalence.functor.obj X)))
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ AddCommGrpCat.{u + 1}

/-- Abelian sheaves on the space, with values in the universe above that of the space, form a
Grothendieck abelian category. -/
instance isGrothendieckAbelian_sheafOpens_succ :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u + 1}) :=
  Stacks.Topology.isGrothendieckAbelian_sheafOpens.{u + 1} X.obj.obj

/-- Abelian sheaves on the localized small model, with values in the universe above that of the
spaces, have enough injectives, transported from `LC_qc/X`. -/
instance enoughInjectives_smallOverSheaf :
    EnoughInjectives (Sheaf (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1}) :=
  EnoughInjectives.of_equivalence (S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}).inverse

/-- The direct image of `a_X` on abelian sheaves of `LC_qc/X`, read on the localized small model,
is restriction along `W ↦ W/X`. -/
def smallOverInverseCompDirectImageIso :
    (S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}).inverse ⋙
        qcTopologicalAbelianDirectImage.{u, w, 0} S X ≅
      (qcSmallOpensFunctor S X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X) :=
  Functor.isoWhiskerRight (S.qcSite.smallOverSheafEquivInverseIso X AddCommGrpCat.{u + 1}) _ ≪≫
    NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _))
      (fun _ => rfl)

/-- **The abelian inverse image of the bottom horizontal arrow in the universe above that of the
spaces is `a_X^{-1}` of `LC_qc/X` read on the small model**: both are left adjoint to restriction
along `W ↦ W/X`. -/
def smallAbelianInverseImageIsoLarge :
    Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X) ≅
      qcTopologicalAbelianInverseImage.{u, w, 0} S X ⋙
        (S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}).functor :=
  haveI := isRightAdjoint_qcSmallOpensFunctor_sheafPushforwardContinuous.{u, w, u + 1} S X
  (abelianInverseImageAdjRestriction (qcSmallOpensFunctor S X)
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)
      (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X)
      (qcSmallBottomMorphismOfSizePushforwardIso.{u, w, u + 1} S X)).leftAdjointUniq
    (((qcTopologicalAbelianComparisonAdjunction.{u, w, 0} S X).comp
        (S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}).toAdjunction).ofNatIsoRight
      (smallOverInverseCompDirectImageIso S X))

/-- The image in the localized small model of the terminal object `⊤/X` of `LC_qc/X` is
terminal. -/
def isTerminal_post_opensToSlice_top :
    IsTerminal ((Over.post (X := X) S.qcSite.smallEquivalence.functor).obj
      ((S.opensToSlice X).1.obj ⊤)) :=
  (opensToSlice_top_isTerminal S X).isTerminalObj _

/-- Global sections on the localized small model are the sections of `LC_qc/X` over `⊤/X`, read
through the identification of the two localized topoi. -/
def smallGlobalSectionsIso :
    Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1} ≅
      (S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}).inverse ⋙
        qcGlobalSections.{u, w, 0} S X :=
  Sheaf.ΓNatIsoSheafSections _ _ (isTerminal_post_opensToSlice_top S X) ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      (sheafSections (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1}).obj
          (op ((Over.post (X := X) S.qcSite.smallEquivalence.functor).obj
            ((S.opensToSlice X).1.obj ⊤))) ≅
        (Over.post (X := X) S.qcSite.smallEquivalence.functor).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (S.qcSite.grothendieckTopology.over X)
          (S.qcSite.smallOverTopology X) ⋙ qcGlobalSections.{u, w, 0} S X) ≪≫
    Functor.isoWhiskerRight (S.qcSite.smallOverSheafEquivInverseIso X AddCommGrpCat.{u + 1}).symm _

/-- The cohomology of the localized small model is the cohomology of `LC_qc/X`, read through the
identification of the two localized topoi. -/
def smallRightDerivedGlobalSectionsIso (n : ℕ) :
    (S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}).functor ⋙
        (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1}).rightDerived n ≅
      (qcGlobalSections.{u, w, 0} S X).rightDerived n :=
  let E := S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  Functor.isoWhiskerLeft E.functor ((Functor.rightUnitor _).symm ≪≫
      Functor.rightDerivedIsoOfSquare E.inverse
        (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1})
        (qcGlobalSections.{u, w, 0} S X) (𝟭 _)
        (Functor.rightUnitor _ ≪≫ smallGlobalSectionsIso S X) n) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- **Stacks 09X4 (1) on the small model, in the universe above that of the spaces.** -/
def smallQcCohomologyComparisonIsoSucc (n : ℕ) :
    Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X) ⋙
        (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1}).rightDerived n ≅
      (spaceGlobalSections.{u, w, 0} S X).rightDerived n :=
  Functor.isoWhiskerRight (smallAbelianInverseImageIsoLarge S X) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallRightDerivedGlobalSectionsIso S X n) ≪≫
    qcCohomologyComparisonIso.{u, w, 0} S X n

end BigUniverse

/-! ### Stacks 09X4 on the small model in the universe of the spaces -/

section SmallUniverse

attribute [local instance] enoughInjectives_sheafOpens_succ enoughInjectives_qcSliceSheaf_succ
  hasSheafify_opens_succ hasSheafify_qcTopology_over_succ isGrothendieckAbelian_smallOverSheaf_succ
  isGrothendieckAbelian_sheafOpens_succ

/-- Abelian presheaves on the space, with values in the universe of the space, can be
sheafified. -/
instance hasSheafify_opens_self :
    HasSheafify (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u} :=
  (Stacks.Topology.hasSheafify_opens X.obj.obj :
    HasSheafify (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u})

/-- Sections of abelian sheaves on the space over the whole space are additive. -/
instance additive_sheafSections_top :
    ((sheafSections (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}).obj
      (op ⊤)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Lifting the universe of abelian sheaves on the localized small model preserves injective
objects. -/
instance preservesInjectiveObjects_uliftSheafFunctor_smallOver :
    (uliftSheafFunctor.{u + 1, u} (S.qcSite.smallOverTopology X)).PreservesInjectiveObjects :=
  preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{u + 1, u + 1, u} _

/-- Lifting the universe of abelian sheaves on the space preserves injective objects. -/
instance preservesInjectiveObjects_uliftSheafFunctor_opens :
    (uliftSheafFunctor.{u + 1, u}
      (Opens.grothendieckTopology X.obj.obj)).PreservesInjectiveObjects :=
  preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{u + 1, u + 1, u} _

/-- Global sections on the localized small model commute with lifting the universe. -/
def smallGlobalSectionsULiftIso :
    Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      uliftSheafFunctor.{u + 1, u} (S.qcSite.smallOverTopology X) ⋙
        Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections _ _ Over.mkIdTerminal) _ ≪≫
    sheafSectionsULiftIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ Over.mkIdTerminal).symm

/-- **Stacks 09X4 (1) on the small model of `LC_qc`.** Let `X` be an object of `LC_qc` and let
`a_X : Sh((LC_qc)_{small}/X) → Sh(X)` be the bottom horizontal arrow of the diagram of Stacks
0DAF. For an abelian sheaf `F` on the space underlying `X`, with values in the universe of the
spaces, and every `n`,

`H^n((LC_qc)_{small}/X, a_X^{-1}F) ≅ H^n(X, F)`,

naturally in `F`. -/
def smallQcCohomologyComparisonIso (n : ℕ) :
    Sites.abelianInverseImage (qcSmallBottomMorphism S X) ⋙
        (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u}).rightDerived n ≅
      ((sheafSections (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived n :=
  rightDerivedCompIsoOfULift.{u + 1, u}
    (uliftSheafFunctor.{u + 1, u} (Opens.grothendieckTopology X.obj.obj))
    (uliftSheafFunctor.{u + 1, u} (S.qcSite.smallOverTopology X))
    (Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u} S X))
    (Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X))
    ((sheafSections (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}).obj (op ⊤))
    (spaceGlobalSections.{u, w, 0} S X)
    (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u})
    (Sheaf.Γ (S.qcSite.smallOverTopology X) AddCommGrpCat.{u + 1})
    (sheafSectionsULiftIso _ _) (smallGlobalSectionsULiftIso S X)
    (smallAbelianInverseImageULiftIso S X) n (smallQcCohomologyComparisonIsoSucc S X n)

end SmallUniverse

end Stacks.Topology.Simplicial

end
