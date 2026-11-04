module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.UnboundedBaseChangeForACocontinuousSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDerivedPushforwardCriterion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismDerivedPushforward

/-!
# The derived direct image of abelian sheaves along the augmentation of a hypercovering

Let `C` be a site, `K` a simplicial semi-representable object of `C` and
`a : Sh((C/K)_total) ⟶ Sh(C)` the morphism of topoi of Stacks 0D70 attached to the
simplicial-site situation of Stacks 0D8B. This file records two facts about the abelian derived
direct image `Ra_*`.

* The direct image of abelian sheaves along `a` is the direct image along the cocontinuous
  localization functor `j_total` (`situationAbelianTotalPushforwardIso`), so the underlying
  abelian complex of a K-injective complex of modules on the total site computes `Ra_*`
  (`isIso_derivedTotalPushforwardUnit_app_underlying_of_isKInjective`, Stacks 0D6J for that
  cocontinuous functor). No condition on `K` is used.
* For a hypercovering of `C`, `a⁻¹` of *every* complex of abelian sheaves computes `Ra_*`
  (`isIso_derivedTotalPushforwardUnit_app_inverseImage_of_hypercoveringOfTerminal`).

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardCocontinuous`: the direct
  image along `j_total`, spelled on the total site of the simplicial-site situation.
* `CategoryTheory.SimplicialSemiRepresentable.situationAbelianTotalPushforwardIso` and
  `CategoryTheory.SimplicialSemiRepresentable.homotopyTotalPushforwardCocontinuousIso`: the two
  direct images agree, degreewise and after localization.

## Main results

* `SimplicialSiteSituation.Augmentation.isIso_derivedTotalPushforwardUnit_app_inverseImage`:
  for any augmentation, if the underived and the derived units are invertible then `a⁻¹` of
  every complex computes `Ra_*`.
* `SimplicialSemiRepresentable.isIso_derivedTotalPushforwardUnit_app_underlying_of_isKInjective`:
  the underlying abelian complex of a K-injective complex of modules computes `Ra_*`.
* `isIso_derivedTotalPushforwardUnit_app_inverseImage_of_hypercoveringOfTerminal`
  (in `SimplicialSemiRepresentable`):
  for a hypercovering of `C`, `a⁻¹` of every complex of abelian sheaves computes `Ra_*`.

## References

* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **If `M ⟶ Ra_*a⁻¹M` and `M ⟶ a_*a⁻¹M` are isomorphisms for every complex `M`, then `a⁻¹` of
every complex computes `Ra_*`.** -/
theorem isIso_derivedTotalPushforwardUnit_app_inverseImage
    (hunit : IsIso (abelianTotalAdjunction S D K a).unit)
    (hderived : IsIso (derivedAugmentationUnit S D K a))
    (M : HomotopyCategory (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    IsIso ((derivedTotalPushforwardUnit S D K a).app
      (((totalInverseImageAb S D K a).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) := by
  have : IsIso ((homotopyTotalAdjunction S D K a).unit.app M) :=
    Adjunction.isIso_mapHomotopyCategoryAdjunction_unit_app _ _ _
  have hcomp : IsIso (DerivedCategory.Qh.map ((homotopyTotalAdjunction S D K a).unit.app M) ≫
      (derivedTotalPushforwardUnit S D K a).app
        (((totalInverseImageAb S D K a).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) := by
    rw [← derivedAugmentationUnit_fac_app]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Qh.map ((homotopyTotalAdjunction S D K a).unit.app M)) _

end CategoryTheory.SimplicialSiteSituation.Augmentation

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation SemiRepresentable

section General

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- The direct image `a_* : Ab((C/K)_total) ⥤ Ab(C)` along the localization functor `j_total`,
which is cocontinuous, with its source spelled as abelian sheaves on the total site of the
simplicial-site situation. -/
abbrev abelianTotalPushforwardCocontinuous :
    Sheaf ((situation J K).totalTopology) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  (totalForget K).sheafPushforwardCocontinuous AddCommGrpCat.{u} ((situation J K).totalTopology) J

/-- **The direct image of abelian sheaves along the total augmentation is the direct image along
`j_total`.** No condition on `K` is used. -/
def situationAbelianTotalPushforwardIso :
    Augmentation.abelianTotalPushforward (situation J K) (Cat.of C) J (situationAugmentation J K) ≅
      abelianTotalPushforwardCocontinuous J K :=
  Adjunction.rightAdjointUniq
    (Augmentation.abelianTotalAdjunction (situation J K) (Cat.of C) J (situationAugmentation J K))
    (((totalForget K).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      ((situation J K).totalTopology) J).ofNatIsoLeft (situationTotalInverseImageAbIso J K).symm)

/-- The direct image along `j_total` is additive. -/
theorem additive_abelianTotalPushforwardCocontinuous :
    (abelianTotalPushforwardCocontinuous J K).Additive :=
  @additive_sheafPushforwardCocontinuous_ab _ _ _ _ (situation J K).totalTopology J
    (totalForget K) (totalForget_isCocontinuous J K)

attribute [local instance] additive_abelianTotalPushforwardCocontinuous

/-- **Stacks 0D6J for `j_total`:** the direct image along `j_total` carries a K-injective
resolution of the underlying abelian complex of a K-injective complex of modules on the total
site to a quasi-isomorphism. -/
theorem quasiIso_abelianTotalPushforwardCocontinuous_map_of_isKInjective
    (O : Sheaf (situation J K).totalTopology RingCat.{u})
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (hI : I.IsKInjective)
    {Jc : CochainComplex (Sheaf (situation J K).totalTopology AddCommGrpCat.{u}) ℤ}
    (hJc : Jc.IsKInjective)
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ Jc)
    (hq : QuasiIso q) :
    QuasiIso (((abelianTotalPushforwardCocontinuous J K).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) :=
  @Stacks.Cohomology.CocontinuousForgetModule.quasiIso_cocontinuousPushforward_map_of_isKInjective
    _ _ _ _ (situation J K).totalTopology J (totalForget K)
    (totalForget_isCocontinuous J K) _ _ _ O I hI Jc hJc q hq

/-- The identification `situationAbelianTotalPushforwardIso`, read degreewise on unbounded
homotopy categories and followed by localization. -/
def homotopyTotalPushforwardCocontinuousIso :
    Augmentation.homotopyTotalPushforward (situation J K) (Cat.of C) J
        (situationAugmentation J K) ≅
      (abelianTotalPushforwardCocontinuous J K).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := Sheaf J AddCommGrpCat.{u}) :=
  haveI hgen := Augmentation.additive_abelianTotalPushforward (situation J K) (Cat.of C) J
    (situationAugmentation J K)
  Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory (situationAbelianTotalPushforwardIso J K).hom
        (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory (situationAbelianTotalPushforwardIso J K).inv
        (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id] }
    (DerivedCategory.Qh (C := Sheaf J AddCommGrpCat.{u}))

/-- The degreewise direct image along the total augmentation followed by localization inverts
the class of a K-injective resolution of the underlying abelian complex of a K-injective complex
of modules on the total site. -/
theorem isIso_homotopyTotalPushforward_map_of_isKInjective
    (O : Sheaf (situation J K).totalTopology RingCat.{u})
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (hI : I.IsKInjective)
    {Jc : CochainComplex (Sheaf (situation J K).totalTopology AddCommGrpCat.{u}) ℤ}
    (hJc : Jc.IsKInjective)
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ Jc)
    (hq : QuasiIso q) :
    IsIso ((Augmentation.homotopyTotalPushforward (situation J K) (Cat.of C) J
        (situationAugmentation J K)).map
      ((HomotopyCategory.quotient (Sheaf (situation J K).totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q)) := by
  refine (NatIso.isIso_map_iff (homotopyTotalPushforwardCocontinuousIso J K) _).mpr ?_
  rw [Functor.comp_map, Functor.mapHomotopyCategory_map]
  exact Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      (quasiIso_abelianTotalPushforwardCocontinuous_map_of_isKInjective J K O I hI hJc q hq))

/-- **The underlying abelian complex of a K-injective complex of modules on the total site
computes `Ra_*`.** No condition on `K` is used. -/
theorem isIso_derivedTotalPushforwardUnit_app_underlying_of_isKInjective
    (O : Sheaf (situation J K).totalTopology RingCat.{u})
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (hI : I.IsKInjective) :
    IsIso ((Augmentation.derivedTotalPushforwardUnit (situation J K) (Cat.of C) J
        (situationAugmentation J K)).app
      ((HomotopyCategory.quotient (Sheaf (situation J K).totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
  obtain ⟨Jc, q, hJc, hq⟩ := Augmentation.exists_kInjective_resolution_total (situation J K)
    (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  exact Augmentation.isIso_derivedTotalPushforwardUnit_app_of_quasiIso (situation J K) (Cat.of C)
    J (situationAugmentation J K) hJc q hq
    (isIso_homotopyTotalPushforward_map_of_isKInjective J K O I hI hJc q hq)

end General

section Terminal

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} P)

/-- **For a hypercovering of the site, `a⁻¹` of every complex of abelian sheaves computes
`Ra_*`.** -/
theorem isIso_derivedTotalPushforwardUnit_app_inverseImage_of_hypercoveringOfTerminal
    (M : HomotopyCategory (Sheaf P.toGrothendieck AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    IsIso ((Augmentation.derivedTotalPushforwardUnit
        (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
        (situationAugmentation P.toGrothendieck H.toSimplicialObject)).app
      (((Augmentation.totalInverseImageAb (situation P.toGrothendieck H.toSimplicialObject)
        (Cat.of C) P.toGrothendieck
        (situationAugmentation P.toGrothendieck H.toSimplicialObject)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M)) := by
  have h : ∀ E, IsIso ((Augmentation.derivedAugmentationUnit
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).app E) :=
    isIso_derivedAugmentationUnit_app_of_hypercovering_unconditional P H
  exact Augmentation.isIso_derivedTotalPushforwardUnit_app_inverseImage _ _ _ _
    (isIso_situationAbelianTotalAdjunctionUnit P H) (NatIso.isIso_of_isIso_app _) M

end Terminal

end CategoryTheory.SimplicialSemiRepresentable

end
