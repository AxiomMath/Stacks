module

public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.IsomRepresentation
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceSourceFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# The presentation of an algebraic stack, tested on slice points

Let `𝒳` be an algebraic stack over `S`, with its presentation `f : (Sch/P) ⟶ 𝒳` by a scheme. For an
object `V` of the big fppf site of `S` and a 1-morphism `X : 𝒮/V ⥤ 𝒳` over the site, the base
change of `f` along `X` is represented by the presheaf of pairs `(k, m)` of a morphism `k` to `P`
and a vertical morphism `m : X ⟶ f k` (`CategoryTheory.TwoFibreProductOver.SliceSourceFibre`), and
the defining clause of the presentation says that its structural morphism to `V`, read over `S`, is
surjective and smooth.

## Main results

* `AlgebraicGeometry.Stack.exists_slicePresentation`: the presentation, with the surjectivity and
  smoothness of its base change along every slice point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An isomorphism of presheaves is surjective as a morphism of algebraic spaces. -/
lemma Space.isSurjective_of_isIso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ⟶ Y) [IsIso e] :
    Space.IsSurjective B S hS e := by
  intro y
  refine ⟨Space.pointsMap B S hS Y (inv e) y, ?_⟩
  rw [← Space.pointsMap_comp_apply, IsIso.inv_hom_id, Space.pointsMap_id_apply]

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- The presheaf on the slice `𝒮/V` of sections of the base change of a 1-morphism
`g : 𝒮/P ⥤ 𝒳` along a slice point `X : 𝒮/V ⥤ 𝒳`. -/
noncomputable abbrev slicePresentationPresheaf {P V : BigFppfOver B S hS}
    {g : Over P ⥤ 𝒳.val.obj} (hg : g ⋙ 𝒳.val.p = Over.forget P) {X : Over V ⥤ 𝒳.val.obj}
    (hX : X ⋙ 𝒳.val.p = Over.forget V) : (Over V)ᵒᵖ ⥤ Type u :=
  SliceSourceFibre.presheaf 𝒳.isFiberedInGroupoids hX hg

/-- The base change presheaf of a slice point read on the big fppf site of `V` is the one read on
the slice, transported along the iterated-slice functor. -/
noncomputable def slicePresentationBackwardIso {P V : BigFppfOver B S hS}
    {g : Over P ⥤ 𝒳.val.obj} (hg : g ⋙ 𝒳.val.p = Over.forget P) {X : Over V ⥤ 𝒳.val.obj}
    (hX : X ⋙ 𝒳.val.p = Over.forget V) :
    SliceSourceFibre.presheaf 𝒳.isFiberedInGroupoids (backward_comp_of_comp 𝒳 V hX) hg ≅
      (Over.iteratedSliceBackward V).op ⋙ slicePresentationPresheaf 𝒳 hg hX :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun s => ⟨s.k, s.m, s.vert⟩
      invFun := fun s => ⟨s.k, s.m, s.vert⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (fun _ => rfl)

/-- **The presentation of an algebraic stack, tested on slice points.** There are a scheme `P` of
the site and a 1-morphism `g : 𝒮/P ⥤ 𝒳` over the site such that, for every slice point
`X : 𝒮/V ⥤ 𝒳`, the coproduct presheaf of the base change presheaf is an algebraic space over `S`
whose structural morphism to `V` is surjective and smooth. -/
theorem exists_slicePresentation (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    ∃ (P : BigFppfOver B S hS) (g : Over P ⥤ 𝒳.val.obj) (hg : g ⋙ 𝒳.val.p = Over.forget P),
      ∀ (V : BigFppfOver B S hS) (X : Over V ⥤ 𝒳.val.obj) (hX : X ⋙ 𝒳.val.p = Over.forget V),
        IsAlgebraicSpace B S hS (OverShriek.presheaf (slicePresentationPresheaf 𝒳 hg hX)) ∧
        Space.IsSurjective B S hS
          (OverShriek.presheafToYoneda (slicePresentationPresheaf 𝒳 hg hX)) ∧
        Space.IsSmooth B S hS
          (OverShriek.presheafToYoneda (slicePresentationPresheaf 𝒳 hg hX)) := by
  have hp := 𝒳.isFiberedInGroupoids
  obtain ⟨hgp, -, -, P, f, hrep, hsm⟩ := h𝒳
  obtain ⟨g, hgdef⟩ : ∃ g : Over P ⥤ 𝒳.val.obj, g = f.toFunctor := ⟨_, rfl⟩
  have hg : g ⋙ 𝒳.val.p = Over.forget P := by
    subst hgdef
    exact f.w
  refine ⟨P, g, hg, fun V X hX => ?_⟩
  have hy := backward_comp_of_comp 𝒳 V hX
  obtain ⟨E⟩ := SliceSourceFibre.nonempty_equivalenceOver hp hy hg
    (PresheafOfCategories.isFiberedInGroupoids_fst_overMap_of (a := V.hom)
      (Functor.IsFiberedInGroupoids.over_forget P) hp hy hg)
  obtain ⟨F₀, hF₀, ⟨E₀⟩⟩ := hrep V _ hy
  have E₀' : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (Over.forget P) 𝒳.val.p
        (Over.iteratedSliceBackward V ⋙ X) g)
      (presheafOfCategories (F₀ ⋙ typeToCat)).p := by
    subst hgdef
    exact E₀
  obtain ⟨i⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff _ F₀).1 ⟨E.symm.trans E₀'⟩
  have hpres : IsAlgebraicSpace B V.left.1 V.left.2
      (SliceSourceFibre.presheaf hp hy hg) :=
    isAlgebraicSpace_of_iso B V.left.1 V.left.2
      (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso i) hF₀
  obtain ⟨hsurj, hsmooth⟩ := hsm V _ hy _ hpres (by
    subst hgdef
    exact ⟨E⟩)
  let L := (spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj
    ⟨SliceSourceFibre.presheaf hp hy hg, hpres⟩
  let J : L.1.left ≅ OverShriek.presheaf (slicePresentationPresheaf 𝒳 hg hX) :=
    (OverShriek.presheafFunctorToOver ⋙ Over.forget _).mapIso
      (Functor.isoWhiskerLeft (Over.iteratedSliceForward (Over.mk V.hom)).op
        (slicePresentationBackwardIso 𝒳 hg hX)) ≪≫
      overShriekRoundTripIso V (slicePresentationPresheaf 𝒳 hg hX)
  have hJ : J.hom ≫ OverShriek.presheafToYoneda (slicePresentationPresheaf 𝒳 hg hX) = L.1.hom := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (overShriekRoundTripIso_hom_comp V _)).trans ?_
    exact Over.w ((OverShriek.presheafFunctorToOver).map
      (Functor.isoWhiskerLeft (Over.iteratedSliceForward (Over.mk V.hom)).op
        (slicePresentationBackwardIso 𝒳 hg hX)).hom)
  have hLsp : IsAlgebraicSpace B S hS L.1.left := L.property
  have hAsp : IsAlgebraicSpace B S hS (OverShriek.presheaf (slicePresentationPresheaf 𝒳 hg hX)) :=
    isAlgebraicSpace_of_iso B S hS J.symm hLsp
  rw [(Iso.eq_inv_comp J).2 hJ]
  exact ⟨hAsp, Space.isSurjective_comp B S hS (Space.isSurjective_of_isIso J.inv) hsurj,
    Space.isSmooth_comp B S hS hAsp hLsp (isAlgebraicSpace_yoneda B S hS (Over.mk V.hom))
      _ _ (Space.isSmooth_of_isIso B S hS hAsp hLsp J.inv) hsmooth⟩

end AlgebraicGeometry.Stack

end
