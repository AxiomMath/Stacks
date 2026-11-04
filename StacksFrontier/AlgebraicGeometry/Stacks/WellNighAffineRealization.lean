module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties

/-!
# The quotient stack of an affine finite flat groupoid scheme is well-nigh affine

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` affine and `s`, `t` finite, flat and
locally of finite presentation, whose schemes the big fppf site contains. Then an algebraic stack
equivalent over the site to the quotient stack `[U/R]` of its realization
(`Stacks.Groupoids.GroupoidScheme.realization`) is well-nigh affine (Stacks 0DUL): the canonical
1-morphism `U ⟶ [U/R]` is surjective, flat, finite and of finite presentation, being a base change
of `s` up to the presentation. This is the implication (2) ⇒ (1) of Stacks 0DUM read for the
groupoid schemes of Morphisms of Stacks, Lemmas 0DU3 and 0DU4, whose quotient stacks are stated
through the realization; it is what makes the étale charts of Stacks 0DU4 well-nigh affine in the
proof of Stacks 0DUE.

## Main results

* `AlgebraicGeometry.Stack.isWellNighAffine_of_equivalenceOver_quotientStack_realization`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open Stacks.Groupoids in
/-- **An algebraic stack presented by the realization of an affine finite flat groupoid scheme is
well-nigh affine** (Stacks 0DUL; (2) ⇒ (1) of Stacks 0DUM). -/
theorem isWellNighAffine_of_equivalenceOver_quotientStack_realization
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (G : GroupoidScheme S)
    (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
    (hP : B.Contains (pullback G.source G.target).left)
    (hUa : IsAffine G.objects.left)
    (hsf : IsFinite G.source.left) (hsfl : Flat G.source.left)
    (hslfp : LocallyOfFinitePresentation G.source.left)
    (htfl : Flat G.target.left) (htlfp : LocallyOfFinitePresentation G.target.left)
    (e : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (G.realization B hS hU hR hP)).p 𝒳.val.val.p) :
    IsWellNighAffine.{u, w} B S hS 𝒳 := by
  classical
  let H := G.realization B hS hU hR hP
  let U : BigFppfOver B S hS := Space.schemeSiteObject B hS hU
  have := hsfl
  have := htfl
  have := hslfp
  have := htlfp
  let p := quotientStackModelProjection.{u, w} B S hS _ H 𝒳 e
  -- the source of the realization is finite
  obtain ⟨hsProp, hsQF⟩ := (IsFinite.iff_isProper_and_locallyQuasiFinite _).1 hsf
  have hsFin : Space.finiteMorphismProperty B S hS H.source := by
    refine Space.isFinite_of_isProper_of_isLocallyQuasiFinite B S hS
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) _
      (Space.isProper_yoneda_map B S hS _ hsProp) ?_
    refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite _).2 ?_
    exact ⟨((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).1 hsf).2, hsQF⟩
  have hpfin := hasRelativeProperty_quotientStackModelProjection H 𝒳 e
    (Space.finiteMorphismProperty B S hS) hsFin
  have hplfp := hasRelativeProperty_quotientStackModelProjection H 𝒳 e
    (spaceProperty B S hS (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h))
    (GroupoidScheme.isLocallyOfFinitePresentation_realization_source B hS hU hR hP)
  obtain ⟨-, hpsurj, hpflat, -⟩ := quotientModelAtlasFppf H 𝒳 e
    (GroupoidScheme.isFlat_realization_source B hS hU hR hP)
    (GroupoidScheme.isFlat_realization_target B hS hU hR hP)
    (GroupoidScheme.isLocallyOfFinitePresentation_realization_source B hS hU hR hP)
    (GroupoidScheme.isLocallyOfFinitePresentation_realization_target B hS hU hR hP)
  -- the algebraic stack of `U` is the algebraic stack of its represented algebraic space
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let k : schemeStack.{u, w} B S hS U ⟶
      algebraicSpaceStack.{u, w} B S hS H.objects.obj H.objects.property :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (⟨eU.hom.functor, eU.hom.w⟩ : (schemeStack.{u, w} B S hS U).val.val ⥤ᵇ
        (algebraicSpaceStack.{u, w} B S hS H.objects.obj H.objects.property).val.val))
  have hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom) :=
    eU.isEquivalence_hom_functor
  have hid𝒳 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  have hrepk : IsRepresentableByAlgebraicSpaces B S hS (k ≫ p).hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (k ≫ p).hom.hom p.hom.hom
      k.hom.hom (BasedFunctor.id 𝒳.val.val) (Iso.refl _)).1
      (isRepresentableByAlgebraicSpaces_quotientStackModelProjection H 𝒳 e)
  have hrel := fun P => relativeProperty_of_equivalences B S hS P (k ≫ p).hom.hom p.hom.hom
    k.hom.hom (BasedFunctor.id 𝒳.val.val) (Iso.refl _)
  refine ⟨U, hUa, k ≫ p, isSurjective_comp_of_isEquivalence B S hS k p hk hpsurj,
    AlgebraicStacks.isFlat_comp_of_isEquivalence B S hS k p hk hpflat, ⟨hrepk, ?_⟩,
    ⟨hrepk, ?_⟩⟩
  · exact hrel (fun _ _ m => Space.IsFinite B S hS m.hom) hpfin
  · refine hrel (fun _ _ m => Space.IsFinitePresentation B S hS m.hom) ?_
    intro V y hy F hF he
    obtain ⟨⟨hsep, ⟨-, hqc⟩, -⟩, -⟩ := Space.isProper_and_isLocallyQuasiFinite_of_isFinite
      B S hS (ObjectProperty.FullSubcategory.property _)
      (ObjectProperty.FullSubcategory.property _) _ (hpfin V y hy F hF he)
    exact ⟨hplfp V y hy F hF he, hqc, Space.isQuasiSeparated_of_isSeparated B S hS hsep⟩

end AlgebraicGeometry.Stack

end
