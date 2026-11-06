module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EquivalenceRelationFromCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePushoutAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.CoproductKernelPair
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Gluing algebraizations

Steps 2 and 3 of the proof of **Stacks 0ARA** glue algebraizations. A morphism `g : W ⟶ X_{/T}`
is covered by `wₖ : Wₖ ⟶ W`, each `Wₖ` and each `Wₖ ×_W Wₗ` is the completion of an algebraic
space `Mₖ`, respectively `N₍ₖ,ₗ₎`, over `X` which is locally of finite type and an isomorphism
over the open subspace `U` cut out by `|X| ∖ T`, and full faithfulness of completion supplies
`t₍ₖ,ₗ₎ : N₍ₖ,ₗ₎ ⟶ Mₖ` and `s₍ₖ,ₗ₎ : N₍ₖ,ₗ₎ ⟶ Mₗ` lifting the two projections. With
`V = ∐ Mₖ` and `R = ∐ N₍ₖ,ₗ₎`, Stacks 0AR8 makes `(t, s) : R ⟶ V ×_X V` an étale equivalence
relation, Stacks 04S6 gives the quotient `X' = V/R`, and `X'_{/T} ≅ W`.

This file proves the steps of that argument which do not depend on how the `Mₖ` and `N₍ₖ,ₗ₎`
were produced.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPullback_completionSheafRestrict_sigma`: the
  completed pair `(t_{/T}, s_{/T})` is the kernel pair of the induced morphism `V_{/T} ⟶ W`,
  hence an equivalence relation (hypothesis (3) of Stacks 0AR8). The completions of `V` and `R`
  are the coproducts of the completions of the summands
  (`AlgebraicGeometry.Space.nonempty_isColimit_cofan_completionSheaf`).
* `AlgebraicGeometry.FormalSpace.isPullback_openSubspaceOfPointsRestrict_sigma`: away from `T`
  the pair `(t, s)` is the kernel pair of `V ⟶ X`, hence an equivalence relation
  (hypothesis (2) of Stacks 0AR8).
* `AlgebraicGeometry.FormalSpace.isIso_openSubspaceOfPointsRestrict_of_isIso` and
  `AlgebraicGeometry.FormalSpace.isEtale_of_isRepresentableEtale_completionSheafMap`: a morphism
  between two modifications is an isomorphism away from `T`, and it is étale as soon as its
  completion is representable étale (the étale clause of Stacks 0AR4 for algebraic spaces).
* `AlgebraicGeometry.FormalSpace.isEtale_of_isColimit_cofan` and
  `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_of_isColimit_cofan`: a morphism out of a
  coproduct of algebraic spaces is étale, respectively locally of finite type, summand by
  summand.
* `AlgebraicGeometry.FormalSpace.exists_quotient_of_isEquivalenceRelation`: the quotient of an
  étale equivalence relation of algebraic spaces over `X` (Stacks 044J, 06PG and 04S6).
* `AlgebraicGeometry.FormalSpace.epi_completionSheafMap` and
  `AlgebraicGeometry.FormalSpace.exists_iso_completionSheaf_of_isPullback`: the completion of
  the quotient is `W`.
* `AlgebraicGeometry.FormalSpace.isIso_pullback_snd_of_isPullback_quotient`: the quotient is an
  isomorphism away from `T`, when `V ⟶ X` has a section away from `T`.

## Assembly

The assembly of these steps into Steps 2 and 3 of Stacks 0ARA, with the choice of a `u`-small
subfamily of an affine étale covering of `W`, the uniform bound on the atlases of the
algebraizations and the empty covering, is in
`StacksFrontier/AlgebraicGeometry/FormalSpace/AffineCompletionEssentialSurjectivity.lean`.

## References

* [Stacks Project, Tag 0ARA](https://stacks.math.columbia.edu/tag/0ARA)
* [Stacks Project, Tag 0AR8](https://stacks.math.columbia.edu/tag/0AR8)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_CompletionGluing :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_CompletionGluing
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The completion of a coproduct of algebraic spaces over `X`, with each summand completed
along the inverse image of `T` under its own structure morphism, is the coproduct of the
completions, the injections being the restriction morphisms of completions. -/
theorem nonempty_isColimit_cofan_completionSheafRestrict {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {K : Type u}
    {A : K → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ k, IsAlgebraicSpace B S hS (A k).obj) (a : ∀ k, (A k).obj ⟶ X)
    {V : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ιV : ∀ k, A k ⟶ V)
    (hV : IsColimit (Cofan.mk V ιV)) (qV : V.obj ⟶ X) (hqV : ∀ k, (ιV k).hom ≫ qV = a k) :
    Nonempty (IsColimit (Cofan.mk
      (Space.completionSheaf B S hS V.obj (Space.pointsMap B S hS _ qV ⁻¹' T))
      (fun k ↦ Space.completionSheafRestrict B S hS (ιV k).hom _ _
        (preimage_subset_preimage_of_comp B S hS (ιV k).hom qV (a k) (hqV k) T)))) := by
  obtain ⟨hc⟩ := Space.nonempty_isColimit_cofan_completionSheaf hA ιV hV qV T
  have he : ∀ k, Space.pointsMap B S hS _ (a k) ⁻¹' T =
      Space.pointsMap B S hS _ (ιV k).hom ⁻¹' (Space.pointsMap B S hS _ qV ⁻¹' T) := fun k ↦
    (preimage_pointsMap_preimage_of_comp B S hS (ιV k).hom qV (a k) (hqV k) T).symm
  let E : ∀ k, Space.completionSheaf B S hS (A k).obj (Space.pointsMap B S hS _ (a k) ⁻¹' T) ≅
      Space.completionSheaf B S hS (A k).obj
        (Space.pointsMap B S hS _ (ιV k).hom ⁻¹' (Space.pointsMap B S hS _ qV ⁻¹' T)) :=
    fun k ↦ eqToIso (congrArg (Space.completionSheaf B S hS (A k).obj) (he k))
  have hleg : ∀ k, Space.completionSheafRestrict B S hS (ιV k).hom _ _
      (preimage_subset_preimage_of_comp B S hS (ιV k).hom qV (a k) (hqV k) T) =
        (E k).hom ≫ Space.completionSheafMap B S hS (ιV k).hom _ := fun k ↦
    completionSheafRestrict_eq_eqToHom_comp B S hS _ _ _ (he k) _
  have hfac : ∀ {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
      (g : ∀ k, Space.completionSheaf B S hS (A k).obj
        (Space.pointsMap B S hS _ (ιV k).hom ⁻¹' (Space.pointsMap B S hS _ qV ⁻¹' T)) ⟶ Y) k,
      Space.completionSheafMap B S hS (ιV k).hom _ ≫ Cofan.IsColimit.desc hc g = g k :=
    fun g k ↦ Cofan.IsColimit.fac hc g k
  refine ⟨Cofan.IsColimit.mk _ (fun s ↦ Cofan.IsColimit.desc hc (fun k ↦ (E k).inv ≫ s.inj k))
    (fun s k ↦ ?_) (fun s m hm ↦ Cofan.IsColimit.hom_ext hc _ _ fun k ↦ ?_)⟩
  · show Space.completionSheafRestrict B S hS (ιV k).hom _ _ _ ≫ _ = _
    rw [hleg, Category.assoc, hfac, Iso.hom_inv_id_assoc]
  · show Space.completionSheafMap B S hS (ιV k).hom _ ≫ m =
      Space.completionSheafMap B S hS (ιV k).hom _ ≫ _
    rw [hfac, ← hm k]
    show _ = (E k).inv ≫ Space.completionSheafRestrict B S hS (ιV k).hom _ _ _ ≫ m
    rw [hleg, Category.assoc, Iso.inv_hom_id_assoc]

/-- Two factorizations of one morphism of presheaves induce the same restriction morphism of
completions. -/
theorem completionSheafRestrict_comp_comm {F₃ F₂ F₂' F₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a₁ : F₃ ⟶ F₂} {b₁ : F₂ ⟶ F₁} {a₂ : F₃ ⟶ F₂'} {b₂ : F₂' ⟶ F₁} (h : a₁ ≫ b₁ = a₂ ≫ b₂)
    {T₃ : Set (Space.points B S hS F₃)} {T₂ : Set (Space.points B S hS F₂)}
    {T₂' : Set (Space.points B S hS F₂')} {T₁ : Set (Space.points B S hS F₁)}
    {h₁ : T₃ ⊆ Space.pointsMap B S hS F₃ a₁ ⁻¹' T₂} {h₂ : T₂ ⊆ Space.pointsMap B S hS F₂ b₁ ⁻¹' T₁}
    {h₁' : T₃ ⊆ Space.pointsMap B S hS F₃ a₂ ⁻¹' T₂'}
    {h₂' : T₂' ⊆ Space.pointsMap B S hS F₂' b₂ ⁻¹' T₁} :
    Space.completionSheafRestrict B S hS a₁ T₃ T₂ h₁ ≫
        Space.completionSheafRestrict B S hS b₁ T₂ T₁ h₂ =
      Space.completionSheafRestrict B S hS a₂ T₃ T₂' h₁' ≫
        Space.completionSheafRestrict B S hS b₂ T₂' T₁ h₂' := by
  have h₃ : T₃ ⊆ Space.pointsMap B S hS F₃ (a₁ ≫ b₁) ⁻¹' T₁ := fun x hx ↦ by
    rw [Space.pointsMap_comp]; exact h₂ (h₁ hx)
  rw [completionSheafRestrict_comp_eq B S hS a₁ b₁ _ rfl _ _ _ h₁ h₂ h₃,
    completionSheafRestrict_comp_eq B S hS a₂ b₂ _ h.symm _ _ _ h₁' h₂' h₃]

/-- **The completed relation of a gluing datum is a kernel pair.** Let `V = ∐ₖ Aₖ` and
`R = ∐ₚ Cₚ` (with `p` running over pairs) be coproducts of algebraic spaces over `X`, and let
`t, s : R ⟶ V` restrict on `Cₚ` to `fstₚ : Cₚ ⟶ A_{p.1}` and `sndₚ : Cₚ ⟶ A_{p.2}` followed
by the injections. If morphisms `βₖ : (Aₖ)_{/T} ⟶ W` make each completed square
`((fstₚ)_{/T}, (sndₚ)_{/T}, β_{p.1}, β_{p.2})` cartesian, then the `βₖ` assemble into
`φ : V_{/T} ⟶ W` and `(t_{/T}, s_{/T})` is the kernel pair of `φ`. -/
theorem exists_isPullback_completionSheafRestrict_sigma {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {K : Type u}
    {A : K → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ k, IsAlgebraicSpace B S hS (A k).obj) (a : ∀ k, (A k).obj ⟶ X)
    {V : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ιV : ∀ k, A k ⟶ V)
    (hV : IsColimit (Cofan.mk V ιV)) (qV : V.obj ⟶ X) (hqV : ∀ k, (ιV k).hom ≫ qV = a k)
    {C : K × K → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hC : ∀ p, IsAlgebraicSpace B S hS (C p).obj) (c : ∀ p, (C p).obj ⟶ X)
    {R : Sheaf (BigFppfOver.topology B S hS) (Type u)} (κ : ∀ p, C p ⟶ R)
    (hR : IsColimit (Cofan.mk R κ)) (qR : R.obj ⟶ X) (hqR : ∀ p, (κ p).hom ≫ qR = c p)
    (fst : ∀ p, C p ⟶ A p.1) (snd : ∀ p, C p ⟶ A p.2)
    (hfst : ∀ p, (fst p).hom ≫ a p.1 = c p) (hsnd : ∀ p, (snd p).hom ≫ a p.2 = c p)
    (t s : R ⟶ V) (ht : ∀ p, κ p ≫ t = fst p ≫ ιV p.1) (hs : ∀ p, κ p ≫ s = snd p ≫ ιV p.2)
    (ht' : t.hom ≫ qV = qR) (hs' : s.hom ≫ qV = qR)
    {W : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (β : ∀ k, Space.completionSheaf B S hS (A k).obj (Space.pointsMap B S hS _ (a k) ⁻¹' T) ⟶ W)
    (hsq : ∀ p, IsPullback
      (Space.completionSheafRestrict B S hS (fst p).hom _ _
        (preimage_subset_preimage_of_comp B S hS (fst p).hom (a p.1) (c p) (hfst p) T))
      (Space.completionSheafRestrict B S hS (snd p).hom _ _
        (preimage_subset_preimage_of_comp B S hS (snd p).hom (a p.2) (c p) (hsnd p) T))
      (β p.1) (β p.2)) :
    ∃ φ : Space.completionSheaf B S hS V.obj (Space.pointsMap B S hS _ qV ⁻¹' T) ⟶ W,
      (∀ k, Space.completionSheafRestrict B S hS (ιV k).hom _ _
        (preimage_subset_preimage_of_comp B S hS (ιV k).hom qV (a k) (hqV k) T) ≫ φ = β k) ∧
      IsPullback
        (Space.completionSheafRestrict B S hS t.hom _ _
          (preimage_subset_preimage_of_comp B S hS t.hom qV qR ht' T))
        (Space.completionSheafRestrict B S hS s.hom _ _
          (preimage_subset_preimage_of_comp B S hS s.hom qV qR hs' T)) φ φ := by
  obtain ⟨hcV⟩ := nonempty_isColimit_cofan_completionSheafRestrict T hA a ιV hV qV hqV
  obtain ⟨hcR⟩ := nonempty_isColimit_cofan_completionSheafRestrict T hC c κ hR qR hqR
  let φ := Cofan.IsColimit.desc hcV β
  have hφ : ∀ k, Space.completionSheafRestrict B S hS (ιV k).hom _ _
      (preimage_subset_preimage_of_comp B S hS (ιV k).hom qV (a k) (hqV k) T) ≫ φ = β k :=
    fun k ↦ Cofan.IsColimit.fac hcV β k
  have hsq' : ∀ p, IsPullback
      (Space.completionSheafRestrict B S hS (fst p).hom _ _
        (preimage_subset_preimage_of_comp B S hS (fst p).hom (a p.1) (c p) (hfst p) T))
      (Space.completionSheafRestrict B S hS (snd p).hom _ _
        (preimage_subset_preimage_of_comp B S hS (snd p).hom (a p.2) (c p) (hsnd p) T))
      (Space.completionSheafRestrict B S hS (ιV p.1).hom _ _
        (preimage_subset_preimage_of_comp B S hS (ιV p.1).hom qV (a p.1) (hqV p.1) T) ≫ φ)
      (Space.completionSheafRestrict B S hS (ιV p.2).hom _ _
        (preimage_subset_preimage_of_comp B S hS (ιV p.2).hom qV (a p.2) (hqV p.2) T) ≫ φ) := by
    intro p
    rw [hφ, hφ]
    exact hsq p
  refine ⟨φ, hφ, Sheaf.isPullback_of_isColimit_cofan (BigFppfOver.topology B S hS) _ hcV _ hcR φ
    _ _ hsq' _ _ (fun p ↦ ?_) (fun p ↦ ?_)⟩
  · exact completionSheafRestrict_comp_comm (congrArg (fun m ↦ m.hom) (ht p))
  · exact completionSheafRestrict_comp_comm (congrArg (fun m ↦ m.hom) (hs p))

/-! ### Morphisms between modifications -/

attribute [local instance] Space.pointTopology

/-- The restriction of a presheaf over `X` to the subspace cut out by any presentation of the
complement of the inverse image of `T` is an isomorphism onto `U`, if the presheaf is an
isomorphism over `U`. -/
private theorem isIso_openSubspaceOfPointsRestrict_aux
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) (y : Y ⟶ X)
    (hy : IsIso (pullback.snd y (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    {W : Set (Space.points B S hS Y)} (hW : W = (Space.pointsMap B S hS Y y ⁻¹' T)ᶜ)
    (h : W ⊆ Space.pointsMap B S hS Y y ⁻¹' Tᶜ) :
    IsIso (Space.openSubspaceOfPointsRestrict B S hS y W Tᶜ h) := by
  subst hW
  have hsq := isPullback_ι_openSubspaceOfPoints_compl B S hS y T
    (Space.openSubspaceOfPointsRestrict B S hS y _ Tᶜ h)
    (Space.openSubspaceOfPointsRestrict_comp_ι B S hS y _ _ _)
  rw [← hsq.isoPullback_hom_snd]
  infer_instance

/-- A morphism over `X` between two presheaves over `X` which are both isomorphisms over the
open subspace `U` cut out by `|X| ∖ T` restricts to an isomorphism between the subspaces cut out
by the complements of the inverse images of `T`. -/
theorem isIso_openSubspaceOfPointsRestrict_of_isIso {X N M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (f : N ⟶ M) (n : N ⟶ X) (m : M ⟶ X) (hf : f ≫ m = n)
    (hn : IsIso (pullback.snd n (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hm : IsIso (pullback.snd m (Space.openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    IsIso (Space.openSubspaceOfPointsRestrict B S hS f _ _
      (compl_subset_preimage_compl B S hS f m n hf T)) := by
  have hN := isIso_openSubspaceOfPointsRestrict_aux T n hn rfl (by rw [Set.preimage_compl])
  have hM := isIso_openSubspaceOfPointsRestrict_aux T m hm rfl (by rw [Set.preimage_compl])
  have hfac : Space.openSubspaceOfPointsRestrict B S hS f _ _
        (compl_subset_preimage_compl B S hS f m n hf T) ≫
      Space.openSubspaceOfPointsRestrict B S hS m _ Tᶜ (by rw [Set.preimage_compl]) =
      Space.openSubspaceOfPointsRestrict B S hS n _ Tᶜ (by rw [Set.preimage_compl]) := by
    rw [← cancel_mono (Space.openSubspaceOfPoints B S hS X Tᶜ).ι, Category.assoc,
      Space.openSubspaceOfPointsRestrict_comp_ι, Space.openSubspaceOfPointsRestrict_comp_ι,
      ← Category.assoc, Space.openSubspaceOfPointsRestrict_comp_ι, Category.assoc, hf]
  rw [← hfac] at hN
  exact IsIso.of_isIso_comp_right (Space.openSubspaceOfPointsRestrict B S hS f _ _
    (compl_subset_preimage_compl B S hS f m n hf T))
    (Space.openSubspaceOfPointsRestrict B S hS m _ Tᶜ _)

/-- **A morphism between modifications whose completion is representable étale is étale.**
Let `f : N ⟶ M` be a morphism over a locally Noetherian algebraic space `X` between algebraic
spaces locally of finite type over `X` which are isomorphisms over the open subspace cut out by
`|X| ∖ T`. If the completion `f_{/T}` is representable by algebraic spaces and étale, then `f`
is étale: it is an isomorphism away from `T` (`isIso_openSubspaceOfPointsRestrict_of_isIso`),
and the étale clause of Stacks 0AR4 for algebraic spaces applies. -/
theorem isEtale_of_isRepresentableEtale_completionSheafMap {X N M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hN : IsAlgebraicSpace B S hS N)
    (hM : IsAlgebraicSpace B S hS M)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (f : N ⟶ M) (n : N ⟶ X) (m : M ⟶ X)
    (hf : f ≫ m = n) (hnft : Space.IsLocallyOfFiniteType B S hS n)
    (hmft : Space.IsLocallyOfFiniteType B S hS m)
    (hn : IsIso (pullback.snd n (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hm : IsIso (pullback.snd m (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hfc : IsRepresentableEtale B S hS
      (Space.completionSheafMap B S hS f (Space.pointsMap B S hS M m ⁻¹' T))) :
    Space.IsEtale B S hS f := by
  have hiso := isIso_openSubspaceOfPointsRestrict_of_isIso T f n m hf hn hm
  have hMnoeth := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hM hX m hmft hXnoeth
  have hdom : IsAlgebraicSpace B S hS (Space.openSubspaceOfPoints B S hS N
      (Space.pointsMap B S hS N n ⁻¹' T)ᶜ).toFunctor :=
    (Space.isOpenSubspace_openSubspaceOfPoints B S hS hN _
      (hT.preimage (Space.continuous_pointsMap B S hS n)).isOpen_compl).1
  exact isEtale_of_isEtale_completionSheafMap_space B S hS hN hM f _
    (hT.preimage (Space.continuous_pointsMap B S hS m)) hMnoeth
    (isLocallyOfFiniteType_of_comp_structure B S hS n m f hf hN hM hX hnft)
    (isEtale_openComplementRestriction_of_restrict B S hS f m n hf T
      (Space.isEtale_of_isIso B S hS _)) hfc

/-- A presheaf over `X` which is an isomorphism over the open subspace `U` cut out by `|X| ∖ T`
restricts to an isomorphism from the subspace cut out by any presentation of the complement of
the inverse image of `T` onto `U`. -/
theorem isIso_openSubspaceOfPointsRestrict_of_isIso_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) (y : Y ⟶ X)
    (hy : IsIso (pullback.snd y (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    {W : Set (Space.points B S hS Y)} (hW : W = (Space.pointsMap B S hS Y y ⁻¹' T)ᶜ)
    (h : W ⊆ Space.pointsMap B S hS Y y ⁻¹' Tᶜ) :
    IsIso (Space.openSubspaceOfPointsRestrict B S hS y W Tᶜ h) :=
  isIso_openSubspaceOfPointsRestrict_aux T y hy hW h

/-- **The relation of a gluing datum is the trivial one away from `T`.** Let `V = ∐ₖ Aₖ` and
`R = ∐ₚ Cₚ` be coproducts of algebraic spaces over `X` all of whose summands are isomorphisms
over the open subspace `U` cut out by `|X| ∖ T`, and let `t, s : R ⟶ V` restrict on `Cₚ` to
morphisms over `X` into `A_{p.1}` and `A_{p.2}` followed by the injections. Then the
restrictions of `t` and `s` to the subspaces cut out by the complements of the inverse images
of `T` form the kernel pair of the restriction of `V ⟶ X`; in particular they form an
equivalence relation, which is hypothesis (2) of Stacks 0AR8. -/
theorem isPullback_openSubspaceOfPointsRestrict_sigma {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {K : Type u} {A : K → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ k, IsAlgebraicSpace B S hS (A k).obj) (a : ∀ k, (A k).obj ⟶ X)
    (haU : ∀ k, IsIso (pullback.snd (a k) (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    {V : Sheaf (BigFppfOver.topology B S hS) (Type u)} (hVsp : IsAlgebraicSpace B S hS V.obj)
    (ιV : ∀ k, A k ⟶ V) (hV : IsColimit (Cofan.mk V ιV)) (qV : V.obj ⟶ X)
    (hqV : ∀ k, (ιV k).hom ≫ qV = a k)
    {C : K × K → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hC : ∀ p, IsAlgebraicSpace B S hS (C p).obj) (c : ∀ p, (C p).obj ⟶ X)
    (hcU : ∀ p, IsIso (pullback.snd (c p) (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    {R : Sheaf (BigFppfOver.topology B S hS) (Type u)} (hRsp : IsAlgebraicSpace B S hS R.obj)
    (κ : ∀ p, C p ⟶ R) (hR : IsColimit (Cofan.mk R κ)) (qR : R.obj ⟶ X)
    (hqR : ∀ p, (κ p).hom ≫ qR = c p)
    (fst : ∀ p, C p ⟶ A p.1) (snd : ∀ p, C p ⟶ A p.2)
    (hfst : ∀ p, (fst p).hom ≫ a p.1 = c p) (hsnd : ∀ p, (snd p).hom ≫ a p.2 = c p)
    (t s : R ⟶ V) (ht : ∀ p, κ p ≫ t = fst p ≫ ιV p.1) (hs : ∀ p, κ p ≫ s = snd p ≫ ιV p.2)
    (ht' : t.hom ≫ qV = qR) (hs' : s.hom ≫ qV = qR) :
    IsPullback
      (Space.openSubspaceOfPointsRestrict B S hS t.hom _ _
        (compl_subset_preimage_compl B S hS t.hom qV qR ht' T))
      (Space.openSubspaceOfPointsRestrict B S hS s.hom _ _
        (compl_subset_preimage_compl B S hS s.hom qV qR hs' T))
      (Space.openSubspaceOfPointsRestrict B S hS qV _ Tᶜ (by rw [Set.preimage_compl]))
      (Space.openSubspaceOfPointsRestrict B S hS qV _ Tᶜ (by rw [Set.preimage_compl])) := by
  let J := BigFppfOver.topology B S hS
  let P := sheafToPresheaf J (Type u)
  -- the subspaces cut out by complements of inverse images of `T`, as sheaves
  let sub : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      ∀ (Z : Set (Space.points B S hS Y)), IsClosed Z → Sheaf J (Type u) :=
    fun hY Z hZ ↦ ⟨(Space.openSubspaceOfPoints B S hS _ Zᶜ).toFunctor,
      (Space.isOpenSubspace_openSubspaceOfPoints B S hS hY _ hZ.isOpen_compl).1.isSheaf⟩
  have hcl : ∀ {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y ⟶ Y')
      (Z : Set (Space.points B S hS Y')), IsClosed Z →
        IsClosed (Space.pointsMap B S hS Y y ⁻¹' Z) :=
    fun y Z hZ ↦ hZ.preimage (Space.continuous_pointsMap B S hS y)
  have hTV := hcl qV T hT
  have hTR := hcl qR T hT
  let V' := sub hVsp _ hTV
  let R' := sub hRsp _ hTR
  let U' : Sheaf J (Type u) := ⟨(Space.openSubspaceOfPoints B S hS X Tᶜ).toFunctor,
    (Space.isOpenSubspace_openSubspaceOfPoints B S hS hX _ hT.isOpen_compl).1.isSheaf⟩
  let A' : K → Sheaf J (Type u) := fun k ↦ sub (hA k) _ (hcl (ιV k).hom _ hTV)
  let C' : K × K → Sheaf J (Type u) := fun p ↦ sub (hC p) _ (hcl (κ p).hom _ hTR)
  have hlift : ∀ {a b c d : Sheaf J (Type u)} (f : a ⟶ b) (g : a ⟶ c) (h : b ⟶ d) (i : c ⟶ d),
      IsPullback f.hom g.hom h.hom i.hom → IsPullback f g h i := fun f g h i H ↦
    IsPullback.of_map (F := P) (by apply P.map_injective; exact H.w) H
  -- the restricted injections, and the coproduct decompositions of `V'` and `R'`
  let ιV' : ∀ k, A' k ⟶ V' := fun k ↦ ObjectProperty.homMk
    (Space.openSubspaceOfPointsRestrict B S hS (ιV k).hom _ _ (by rw [Set.preimage_compl]))
  let κ' : ∀ p, C' p ⟶ R' := fun p ↦ ObjectProperty.homMk
    (Space.openSubspaceOfPointsRestrict B S hS (κ p).hom _ _ (by rw [Set.preimage_compl]))
  let jV : V' ⟶ V := ObjectProperty.homMk (Space.openSubspaceOfPoints B S hS _ _).ι
  let jR : R' ⟶ R := ObjectProperty.homMk (Space.openSubspaceOfPoints B S hS _ _).ι
  have hV' : IsColimit (Cofan.mk V' ιV') :=
    (Sheaf.nonempty_isColimit_cofanMk_of_isPullback J ιV hV jV ιV'
      (fun k ↦ ObjectProperty.homMk (Space.openSubspaceOfPoints B S hS _ _).ι) fun k ↦
        hlift _ _ _ _ (isPullback_ι_openSubspaceOfPoints_compl B S hS (ιV k).hom _ _
          (Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _
            (by rw [Set.preimage_compl]))).flip).some
  have hR' : IsColimit (Cofan.mk R' κ') :=
    (Sheaf.nonempty_isColimit_cofanMk_of_isPullback J κ hR jR κ'
      (fun p ↦ ObjectProperty.homMk (Space.openSubspaceOfPoints B S hS _ _).ι) fun p ↦
        hlift _ _ _ _ (isPullback_ι_openSubspaceOfPoints_compl B S hS (κ p).hom _ _
          (Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _
            (by rw [Set.preimage_compl]))).flip).some
  -- the restrictions of the relation and of `V ⟶ X`
  have hpre : ∀ {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y ⟶ Y') (y' : Y' ⟶ X)
      (z : Y ⟶ X), y ≫ y' = z →
        Space.pointsMap B S hS Y z ⁻¹' T = Space.pointsMap B S hS Y y ⁻¹'
          (Space.pointsMap B S hS Y' y' ⁻¹' T) :=
    fun y y' z h ↦ (preimage_pointsMap_preimage_of_comp B S hS y y' z h T).symm
  have hsub : ∀ {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y ⟶ Y')
      (Z : Set (Space.points B S hS Y))
      (Z' : Set (Space.points B S hS Y')), Z = Space.pointsMap B S hS Y y ⁻¹' Z' →
        Zᶜ ⊆ Space.pointsMap B S hS Y y ⁻¹' Z'ᶜ := by
    intro Y Y' y Z Z' h
    rw [h, Set.preimage_compl]
  let φ : V' ⟶ U' := ObjectProperty.homMk
    (Space.openSubspaceOfPointsRestrict B S hS qV _ Tᶜ (by rw [Set.preimage_compl]))
  let fst' : ∀ p, C' p ⟶ A' p.1 := fun p ↦ ObjectProperty.homMk
    (Space.openSubspaceOfPointsRestrict B S hS (fst p).hom _ _ (hsub _ _ _ (by
      rw [← hpre (κ p).hom qR (c p) (hqR p), ← hpre (ιV p.1).hom qV (a p.1) (hqV p.1),
        ← hpre (fst p).hom (a p.1) (c p) (hfst p)])))
  let snd' : ∀ p, C' p ⟶ A' p.2 := fun p ↦ ObjectProperty.homMk
    (Space.openSubspaceOfPointsRestrict B S hS (snd p).hom _ _ (hsub _ _ _ (by
      rw [← hpre (κ p).hom qR (c p) (hqR p), ← hpre (ιV p.2).hom qV (a p.2) (hqV p.2),
        ← hpre (snd p).hom (a p.2) (c p) (hsnd p)])))
  let t' : R' ⟶ V' := ObjectProperty.homMk
    (Space.openSubspaceOfPointsRestrict B S hS t.hom _ _
      (compl_subset_preimage_compl B S hS t.hom qV qR ht' T))
  let s' : R' ⟶ V' := ObjectProperty.homMk
    (Space.openSubspaceOfPointsRestrict B S hS s.hom _ _
      (compl_subset_preimage_compl B S hS s.hom qV qR hs' T))
  -- every summand is isomorphic to `U` away from `T`
  have hι : ∀ {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : Set (Space.points B S hS Y')}
      {f g : Y ⟶ (Space.openSubspaceOfPoints B S hS Y' W).toFunctor},
      f ≫ (Space.openSubspaceOfPoints B S hS Y' W).ι =
        g ≫ (Space.openSubspaceOfPoints B S hS Y' W).ι →
        f = g := fun h ↦ (cancel_mono _).mp h
  have hisoA : ∀ k, IsIso (ιV' k ≫ φ) := fun k ↦ by
    have e : P.map (ιV' k ≫ φ) = Space.openSubspaceOfPointsRestrict B S hS (a k) _ Tᶜ
        (hsub _ _ _ (hpre (ιV k).hom qV (a k) (hqV k)).symm) := by
      apply hι
      show (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (ιV k).hom ≫ qV =
        (Space.openSubspaceOfPoints B S hS _ _).ι ≫ a k
      rw [hqV]
    have : IsIso (P.map (ιV' k ≫ φ)) := by
      rw [e]
      exact isIso_openSubspaceOfPointsRestrict_of_isIso_pullback_snd T (a k) (haU k)
        (by rw [hpre (ιV k).hom qV (a k) (hqV k)]) _
    exact isIso_of_reflects_iso _ P
  have hisoC : ∀ p, IsIso (κ' p ≫ t' ≫ φ) := fun p ↦ by
    have e : P.map (κ' p ≫ t' ≫ φ) = Space.openSubspaceOfPointsRestrict B S hS (c p) _ Tᶜ
        (hsub _ _ _ (hpre (κ p).hom qR (c p) (hqR p)).symm) := by
      apply hι
      show (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (κ p).hom ≫ t.hom ≫ qV =
        (Space.openSubspaceOfPoints B S hS _ _).ι ≫ c p
      rw [ht', hqR]
    have : IsIso (P.map (κ' p ≫ t' ≫ φ)) := by
      rw [e]
      exact isIso_openSubspaceOfPointsRestrict_of_isIso_pullback_snd T (c p) (hcU p)
        (by rw [hpre (κ p).hom qR (c p) (hqR p)]) _
    exact isIso_of_reflects_iso _ P
  have ht'' : ∀ p, κ' p ≫ t' = fst' p ≫ ιV' p.1 := fun p ↦ by
    apply P.map_injective
    apply hι
    show (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (κ p).hom ≫ t.hom =
      (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (fst p).hom ≫ (ιV p.1).hom
    rw [show (κ p).hom ≫ t.hom = (fst p).hom ≫ (ιV p.1).hom from congrArg (fun m ↦ m.hom) (ht p)]
  have hs'' : ∀ p, κ' p ≫ s' = snd' p ≫ ιV' p.2 := fun p ↦ by
    apply P.map_injective
    apply hι
    show (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (κ p).hom ≫ s.hom =
      (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (snd p).hom ≫ (ιV p.2).hom
    rw [show (κ p).hom ≫ s.hom = (snd p).hom ≫ (ιV p.2).hom from congrArg (fun m ↦ m.hom) (hs p)]
  have hst : ∀ p, κ' p ≫ s' ≫ φ = κ' p ≫ t' ≫ φ := fun p ↦ by
    apply P.map_injective
    apply hι
    show (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (κ p).hom ≫ s.hom ≫ qV =
      (Space.openSubspaceOfPoints B S hS _ _).ι ≫ (κ p).hom ≫ t.hom ≫ qV
    rw [hs', ht']
  have hsq : ∀ p, IsPullback (fst' p) (snd' p) (ιV' p.1 ≫ φ) (ιV' p.2 ≫ φ) := fun p ↦ by
    have hsnd' : IsIso (snd' p) := by
      have h : snd' p ≫ ιV' p.2 ≫ φ = κ' p ≫ t' ≫ φ := by
        rw [← Category.assoc, ← hs'', Category.assoc, hst]
      have : IsIso (snd' p ≫ ιV' p.2 ≫ φ) := by rw [h]; exact hisoC p
      exact IsIso.of_isIso_comp_right (snd' p) (ιV' p.2 ≫ φ)
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← Category.assoc, ← ht'', Category.assoc, ← hst, ← Category.assoc, hs'',
      Category.assoc]
  exact (Sheaf.isPullback_of_isColimit_cofan J ιV' hV' κ' hR' φ fst' snd' hsq t' s' ht''
    hs'').map P

/-! ### The quotient by an étale equivalence relation over `X` -/

/-- **The quotient of an étale equivalence relation of algebraic spaces over `X`.** Let
`t, s : R ⟶ V` be morphisms of algebraic spaces over `X` which form an equivalence relation and
are étale. Then there is an epimorphism of sheaves `π : V ⟶ Q` with kernel pair `(t, s)`; `Q` is
an algebraic space, `π` is étale and surjective, and the structure morphism of `V` factors
through `π`. This is Stacks 04S6 for the quotient sheaf of the relation (Stacks 044J), whose
kernel pair is the relation (Stacks 06PG). -/
theorem exists_quotient_of_isEquivalenceRelation {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {V R : Sheaf (BigFppfOver.topology B S hS) (Type u)} (hV : IsAlgebraicSpace B S hS V.obj)
    (hR : IsAlgebraicSpace B S hS R.obj) (qV : V.obj ⟶ X) (qR : R.obj ⟶ X) (t s : R ⟶ V)
    (ht : t.hom ≫ qV = qR) (hs : s.hom ≫ qV = qR) (hrel : IsEquivalenceRelation t.hom s.hom)
    (htet : Space.IsEtale B S hS t.hom) (hset : Space.IsEtale B S hS s.hom) :
    ∃ (Q : Sheaf (BigFppfOver.topology B S hS) (Type u)) (π : V ⟶ Q) (qQ : Q.obj ⟶ X),
      Epi π ∧ IsPullback t s π π ∧ IsAlgebraicSpace B S hS Q.obj ∧
        Space.IsEtale B S hS π.hom ∧ Space.IsSurjective B S hS π.hom ∧ π.hom ≫ qQ = qV := by
  let J := BigFppfOver.topology B S hS
  let : HasSheafify J (Type u) := hasSheafify_bigFppfOver B S hS
  let tb : Over.mk qR ⟶ Over.mk qV := Over.homMk t.hom ht
  let sb : Over.mk qR ⟶ Over.mk qV := Over.homMk s.hom hs
  let j : Space.PreRelation (Over.mk qR) (Over.mk qV) := prod.lift tb sb
  have htj : j.target = tb := prod.lift_fst _ _
  have hsj : j.source = sb := prod.lift_snd _ _
  have hj : IsEquivalenceRelation j.target j.source := by
    rw [htj, hsj]
    exact isEquivalenceRelation_of_left tb sb (h := hrel)
  have hpb := Space.isPullback_toQuotientSheaf j hj R.property V.property
  rw [htj, hsj] at hpb
  let Q : Sheaf J (Type u) := Space.quotientSheaf j
  let π : V ⟶ Q := ObjectProperty.homMk (Space.toQuotientSheaf j)
  have hπ : Epi π := by
    have : Sheaf.IsLocallySurjective π := Space.isLocallySurjective_toQuotientSheaf j
    exact Sheaf.epi_of_isLocallySurjective π
  have hpbsh : IsPullback t s π π := isPullback_sheaf_of_hom hpb.flip
  obtain ⟨hQ, hπet, hπs⟩ := Space.isAlgebraicSpace_of_isPullback_of_isEtale B S hS hV hR
    hpbsh.flip hset htet
  exact ⟨Q, π, (Space.quotientSheafToBase hXsh j).hom, hπ, hpbsh, hQ, hπet, hπs,
    Space.toQuotientSheaf_quotientSheafToBase hXsh j⟩

/-! ### Morphisms out of a coproduct of algebraic spaces -/

/-- The injections of a coproduct of algebraic spaces, formed among fppf sheaves of sets and
indexed by a type of the universe of the site, form an étale covering: they are open
immersions (Stacks 0F15) whose images cover the coproduct. -/
theorem isEtaleCovering_of_isColimit_cofan {I : Type u}
    {A : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj) (hX : IsAlgebraicSpace B S hS X.obj)
    (ι : ∀ i, A i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    Space.IsEtaleCovering B S hS (fun i ↦ (A i).obj) (fun i ↦ (ι i).hom) := by
  let J := BigFppfOver.topology B S hS
  have hι : ∀ i, Space.IsOpenImmersion B S hS (ι i).hom := fun i ↦
    coproductIncl_isOpenImmersion B S hS A X ι hc i
  let O : I → Subfunctor X.obj := fun i ↦ Subfunctor.range (ι i).hom
  have ho : ∀ i, Space.IsOpenSubspace B S hS (O i) := fun i ↦
    Space.isOpenSubspace_range_of_isAlgebraicSpace B S hS (hA i) (ι i).hom (hι i)
  let k : (∐ fun i ↦ (A i).obj) ⟶ (∐ fun i ↦ (O i).toFunctor) :=
    Sigma.desc fun i ↦ Subfunctor.toRange (ι i).hom ≫ Sigma.ι (fun i ↦ (O i).toFunctor) i
  have hfac : k ≫ Sigma.desc (fun i ↦ (O i).ι) = Sigma.desc (fun i ↦ (ι i).hom) := by
    apply Sigma.hom_ext
    intro i
    simp [k, O, Subfunctor.toRange_ι]
  have hloc := Space.coproduct_locallySurjective J A ι hc
  have hcov : Space.IsZariskiCover B S hS I O :=
    ⟨ho, Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  have hp := (Space.isZariskiCover_iff_iUnion_points B S hS X.obj hX I O ho).mp hcov
  have hrange : ∀ i, Set.range (Space.pointsMap B S hS (A i).obj (ι i).hom) =
      Set.range (Space.pointsMap B S hS (O i).toFunctor (O i).ι) := by
    intro i
    have hmono : Mono (ι i).hom := Space.mono_of_isOpenImmersion B S hS _ (hι i)
    have hcomp : ∀ y, Space.pointsMap B S hS (O i).toFunctor (O i).ι
        (Space.pointsMap B S hS (A i).obj (Subfunctor.toRange (ι i).hom) y) =
        Space.pointsMap B S hS (A i).obj (ι i).hom y := by
      intro y
      rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      exact ⟨_, hcomp y⟩
    · rintro x ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ :=
        Space.pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange (ι i).hom) z
      exact ⟨y, (hcomp y).symm⟩
  refine ⟨hX, hA, fun i ↦ Space.isEtale_of_isOpenImmersion B S hS (hι i), ?_⟩
  simpa only [hrange] using hp

/-- A property local at the source for a topology holds for a morphism out of a coproduct of
algebraic spaces as soon as it holds for each restriction to a summand, when the injections form
a covering for that topology. -/
private theorem of_forall_comp_cofan_of_isCovering {τ : Space.Topology}
    (Q : MorphismProperty (AlgebraicSpaces B S hS))
    [Q.IsLocalAtSource (τ.precoverage.{u, u} B S hS)] {I : Type u}
    {A : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (ι : ∀ i, A i ⟶ X) (f : X.obj ⟶ Y)
    (hcov : τ.IsCovering B S hS (fun i ↦ (A i).obj) (fun i ↦ (ι i).hom))
    (hf : ∀ i, Q (ObjectProperty.homMk ((ι i).hom ≫ f) :
      (⟨(A i).obj, hcov.2.1 i⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)) :
    Q (ObjectProperty.homMk f : (⟨X.obj, hcov.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  MorphismProperty.IsLocalAtSource.of_forall_comp (P := Q)
    (X := (⟨X.obj, hcov.1⟩ : AlgebraicSpaces B S hS))
    (show Presieve.ofArrows (fun i ↦ (⟨(A i).obj, hcov.2.1 i⟩ : AlgebraicSpaces B S hS))
      (fun i ↦ ObjectProperty.homMk (ι i).hom) ∈ τ.precoverage B S hS _ from
      ⟨I, _, _, rfl, hcov⟩) fun _ _ ⟨i⟩ ↦ hf i

/-- A morphism out of a coproduct of algebraic spaces is étale as soon as each of its
restrictions to the summands is. -/
theorem isEtale_of_isColimit_cofan {I : Type u}
    {A : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj) (hX : IsAlgebraicSpace B S hS X.obj)
    (hY : IsAlgebraicSpace B S hS Y) (ι : ∀ i, A i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (f : X.obj ⟶ Y) (hf : ∀ i, Space.IsEtale B S hS ((ι i).hom ≫ f)) :
    Space.IsEtale B S hS f := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k ↦ Space.IsEtale B S hS k.hom
  let _ : Q.IsLocalAtSource (Space.Topology.precoverage.{u, u} Space.Topology.etale B S hS) :=
    Space.isEtale_isLocalAtSource_etale.{u, u} B S hS
  exact of_forall_comp_cofan_of_isCovering (τ := Space.Topology.etale) Q hY ι f
    ⟨hX, hA, isEtaleCovering_of_isColimit_cofan hA hX ι hc⟩ hf

/-- A morphism out of a coproduct of algebraic spaces is locally of finite type as soon as each
of its restrictions to the summands is. -/
theorem isLocallyOfFiniteType_of_isColimit_cofan {I : Type u}
    {A : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj) (hX : IsAlgebraicSpace B S hS X.obj)
    (hY : IsAlgebraicSpace B S hS Y) (ι : ∀ i, A i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (f : X.obj ⟶ Y) (hf : ∀ i, Space.IsLocallyOfFiniteType B S hS ((ι i).hom ≫ f)) :
    Space.IsLocallyOfFiniteType B S hS f := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k ↦ Space.IsLocallyOfFiniteType B S hS k.hom
  let _ : Q.IsLocalAtSource (Space.Topology.precoverage.{u, u} Space.Topology.fppf B S hS) :=
    Space.isLocallyOfFiniteType_isLocalAtSource_fppf.{u, u} B S hS
  exact of_forall_comp_cofan_of_isCovering (τ := Space.Topology.fppf) Q hY ι f
    ⟨hX, hA, Space.isFppfCovering_of_isEtaleCovering B S hS
      (isEtaleCovering_of_isColimit_cofan hA hX ι hc)⟩ hf

/-! ### The completion of the quotient -/

/-- The universe lift of a locally surjective morphism of presheaves is locally surjective. -/
theorem isLocallySurjective_whiskerRight_uliftFunctor {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Functor.whiskerRight f uliftFunctor.{u + 1, u}) := by
  refine ⟨fun {U} s ↦ ?_⟩
  have h := Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) f (U := Opposite.op U) s.down
  convert h using 1
  ext V g
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.down, congrArg ULift.down hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-- The completion of an epimorphism of fppf sheaves of sets is an epimorphism: it is the base
change of the sheafified universe lift of the epimorphism (Stacks 0APV). -/
theorem epi_completionSheafMap {V Q : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (π : V ⟶ Q) [Epi π] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (qQ : Q.obj ⟶ X)
    (T : Set (Space.points B S hS X)) :
    Epi (Space.completionSheafMap B S hS π.hom (Space.pointsMap B S hS _ qQ ⁻¹' T)) := by
  let J := BigFppfOver.topology B S hS
  let : HasSheafify J (Type u) := hasSheafify_bigFppfOver B S hS
  have hπ : Presheaf.IsLocallySurjective J π.hom :=
    (Sheaf.isLocallySurjective_iff_epi π).mpr inferInstance
  have hw := isLocallySurjective_whiskerRight_uliftFunctor π.hom hπ
  have hL : Sheaf.IsLocallySurjective (Space.sheafifiedULiftMap B S hS π.hom) := by
    rw [Sheaf.IsLocallySurjective, Space.sheafifiedULiftMap_hom_eq B S hS V.property Q.property]
    infer_instance
  have hepi := Sheaf.epi_of_isLocallySurjective (Space.sheafifiedULiftMap B S hS π.hom)
  have hsq := Space.isPullback_completionSheafMap B S hS π.hom (Space.pointsMap B S hS _ qQ ⁻¹' T)
  have : Epi (pullback.snd (Space.sheafifiedULiftMap B S hS π.hom)
      (Space.completionSheafInclusion B S hS Q.obj (Space.pointsMap B S hS _ qQ ⁻¹' T))) :=
    Sheaf.epi_pullback_snd _ _ hepi
  rw [← hsq.isoPullback_hom_snd]
  infer_instance

/-- Two epimorphisms of fppf sheaves of sets out of the same sheaf with the same kernel pair
are isomorphic under it: both are the coequalizer of the kernel pair, epimorphisms of sheaves
of sets being regular. -/
theorem exists_iso_of_isPullback_of_epi.{w}
    [IsRegularEpiCategory (Sheaf (BigFppfOver.topology B S hS) (Type w))]
    {V' Q' W R' : Sheaf (BigFppfOver.topology B S hS) (Type w)} {t' s' : R' ⟶ V'}
    (π : V' ⟶ Q') (φ : V' ⟶ W) [Epi π] [Epi φ] (hπ : IsPullback t' s' π π)
    (hφ : IsPullback t' s' φ φ) :
    ∃ e : Q' ≅ W, π ≫ e.hom = φ := by
  have : IsRegularEpi π := IsRegularEpiCategory.regularEpiOfEpi π
  have : IsRegularEpi φ := IsRegularEpiCategory.regularEpiOfEpi φ
  have hπc : IsColimit (Cofork.ofπ π hπ.w) := IsKernelPair.toCoequalizer' hπ
  have hφc : IsColimit (Cofork.ofπ φ hφ.w) := IsKernelPair.toCoequalizer' hφ
  exact ⟨hπc.coconePointUniqueUpToIso hφc,
    hπc.comp_coconePointUniqueUpToIso_hom hφc WalkingParallelPair.one⟩

/-- **The completion of the quotient.** Let `π : V ⟶ Q` be an epimorphism of fppf sheaves of
sets over `X` with kernel pair `(t, s)`. If `φ : V_{/T} ⟶ W` is an epimorphism over `X_{/T}`
whose kernel pair is the completed pair `(t_{/T}, s_{/T})`, then `Q_{/T} ≅ W` over `X_{/T}`.
Completion preserves the kernel pair (Stacks 0APV) and the epimorphism
(`epi_completionSheafMap`), so `π_{/T}` and `φ` are two coequalizers of the same pair. -/
theorem exists_iso_completionSheaf_of_isPullback {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {V Q R : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (π : V ⟶ Q) [Epi π] (t s : R ⟶ V) (hk : IsPullback t s π π) (qV : V.obj ⟶ X)
    (qR : R.obj ⟶ X) (qQ : Q.obj ⟶ X) (hπq : π.hom ≫ qQ = qV) (ht' : t.hom ≫ qV = qR)
    (hs' : s.hom ≫ qV = qR) {W : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (φ : Space.completionSheaf B S hS V.obj (Space.pointsMap B S hS _ qV ⁻¹' T) ⟶ W) [Epi φ]
    (hφ : IsPullback
        (Space.completionSheafRestrict B S hS t.hom _ _
          (preimage_subset_preimage_of_comp B S hS t.hom qV qR ht' T))
        (Space.completionSheafRestrict B S hS s.hom _ _
          (preimage_subset_preimage_of_comp B S hS s.hom qV qR hs' T)) φ φ)
    (g : W ⟶ Space.completionSheaf B S hS X T)
    (hφg : φ ≫ g = Space.completionSheafMap B S hS qV T) :
    ∃ e : Space.completionSheaf B S hS Q.obj (Space.pointsMap B S hS _ qQ ⁻¹' T) ≅ W,
      e.hom ≫ g = Space.completionSheafMap B S hS qQ T := by
  have hV : Space.pointsMap B S hS _ qV ⁻¹' T =
      Space.pointsMap B S hS _ π.hom ⁻¹' (Space.pointsMap B S hS _ qQ ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS π.hom qQ qV hπq T).symm
  let cπ := Space.completionSheafRestrict B S hS π.hom (Space.pointsMap B S hS _ qV ⁻¹' T)
    (Space.pointsMap B S hS _ qQ ⁻¹' T) (preimage_subset_preimage_of_comp B S hS π.hom qQ qV hπq T)
  have hcπ : cπ = eqToHom (congrArg (Space.completionSheaf B S hS V.obj) hV) ≫
      Space.completionSheafMap B S hS π.hom (Space.pointsMap B S hS _ qQ ⁻¹' T) :=
    completionSheafRestrict_eq_eqToHom_comp B S hS _ _ _ hV _
  have := epi_completionSheafMap π qQ T
  have : Epi cπ := by
    rw [hcπ]
    infer_instance
  have hk0 : IsPullback t.hom s.hom π.hom π.hom := hk.map (sheafToPresheaf _ _)
  have hk' := isPullback_completionSheafRestrict_of_isPullback B S hS hk0
    (Space.pointsMap B S hS _ qQ ⁻¹' T) (Space.pointsMap B S hS _ qR ⁻¹' T)
    (Space.pointsMap B S hS _ qV ⁻¹' T) (Space.pointsMap B S hS _ qV ⁻¹' T) hV hV
    (preimage_pointsMap_preimage_of_comp B S hS t.hom qV qR ht' T).symm
    (preimage_pointsMap_preimage_of_comp B S hS s.hom qV qR hs' T).symm
    (preimage_subset_preimage_of_comp B S hS t.hom qV qR ht' T)
    (preimage_subset_preimage_of_comp B S hS s.hom qV qR hs' T)
    (preimage_subset_preimage_of_comp B S hS π.hom qQ qV hπq T)
    (preimage_subset_preimage_of_comp B S hS π.hom qQ qV hπq T)
  obtain ⟨e, he⟩ := exists_iso_of_isPullback_of_epi cπ φ hk' hφ
  refine ⟨e, ?_⟩
  rw [← cancel_epi cπ, ← Category.assoc, he, hφg,
    ← Space.completionSheafRestrict_self B S hS qQ T subset_rfl,
    ← Space.completionSheafRestrict_self B S hS qV T subset_rfl]
  exact (completionSheafRestrict_comp_eq B S hS _ _ _ hπq _ _ _ _ _ _).symm

/-- The open subspace cut out by any presentation of the complement of the inverse image of `T`
under `g` is the base change of the open subspace cut out by `Tᶜ`. -/
theorem isPullback_ι_openSubspaceOfPoints_of_eq {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F' ⟶ F) (T : Set (Space.points B S hS F)) {W : Set (Space.points B S hS F')}
    (hW : W = (Space.pointsMap B S hS F' g ⁻¹' T)ᶜ)
    (r : (Space.openSubspaceOfPoints B S hS F' W).toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS F Tᶜ).toFunctor)
    (hr : r ≫ (Space.openSubspaceOfPoints B S hS F Tᶜ).ι =
      (Space.openSubspaceOfPoints B S hS F' W).ι ≫ g) :
    IsPullback (Space.openSubspaceOfPoints B S hS F' W).ι r g
      (Space.openSubspaceOfPoints B S hS F Tᶜ).ι := by
  subst hW
  exact isPullback_ι_openSubspaceOfPoints_compl B S hS g T r hr

/-- Restricting a kernel-pair square over `X` to the open subspaces cut out by `|X| ∖ T` gives
a kernel-pair square. -/
theorem isPullback_openSubspaceOfPointsRestrict_of_isPullback
    {X V Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) {π : V ⟶ Q}
    {t s : R ⟶ V} (hk : IsPullback t s π π) {qV : V ⟶ X} {qR : R ⟶ X} {qQ : Q ⟶ X}
    (hπq : π ≫ qQ = qV) (ht' : t ≫ qV = qR) (hs' : s ≫ qV = qR) :
    IsPullback
      (Space.openSubspaceOfPointsRestrict B S hS t _ _
        (compl_subset_preimage_compl B S hS t qV qR ht' T))
      (Space.openSubspaceOfPointsRestrict B S hS s _ _
        (compl_subset_preimage_compl B S hS s qV qR hs' T))
      (Space.openSubspaceOfPointsRestrict B S hS π _ _
        (compl_subset_preimage_compl B S hS π qQ qV hπq T))
      (Space.openSubspaceOfPointsRestrict B S hS π _ _
        (compl_subset_preimage_compl B S hS π qQ qV hπq T)) := by
  have hbase : ∀ {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y ⟶ Y') (y' : Y' ⟶ X)
      (z : Y ⟶ X) (h : y ≫ y' = z),
      IsPullback (Space.openSubspaceOfPoints B S hS _ _).ι
        (Space.openSubspaceOfPointsRestrict B S hS y _ _
          (compl_subset_preimage_compl B S hS y y' z h T)) y
        (Space.openSubspaceOfPoints B S hS _ _).ι := fun y y' z h ↦
    isPullback_ι_openSubspaceOfPoints_of_eq y _
      (by rw [preimage_pointsMap_preimage_of_comp B S hS y y' z h T]) _ rfl
  have hP1 := hbase π qQ qV hπq
  have hP2 := hbase t qV qR ht'
  refine IsPullback.of_bot (v₂₁ := (Space.openSubspaceOfPoints B S hS _ _).ι)
    (v₂₂ := (Space.openSubspaceOfPoints B S hS _ _).ι) (h₃₁ := π) (hP2.flip.paste_vert hk) ?_
    hP1.flip
  refine (cancel_mono
    (Space.openSubspaceOfPoints B S hS Q (Space.pointsMap B S hS _ qQ ⁻¹' T)ᶜ).ι).mp ?_
  show (Space.openSubspaceOfPoints B S hS _ _).ι ≫ t ≫ π =
    (Space.openSubspaceOfPoints B S hS _ _).ι ≫ s ≫ π
  rw [hk.w]

/-- **The quotient is an isomorphism away from `T`.** Let `π : V ⟶ Q` be an epimorphism of
algebraic spaces over `X` with kernel pair `(t, s)`. If away from `T` the pair `(t, s)` is the
kernel pair of the restriction of `V ⟶ X`, and that restriction has a section, then `Q ⟶ X` is
an isomorphism over the open subspace cut out by `|X| ∖ T`: away from `T` both `Q` and `X` are
the coequalizer of the restricted pair. -/
theorem isIso_pullback_snd_of_isPullback_quotient {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {V Q R : Sheaf (BigFppfOver.topology B S hS) (Type u)} (hV : IsAlgebraicSpace B S hS V.obj)
    (hQ : IsAlgebraicSpace B S hS Q.obj) (hR : IsAlgebraicSpace B S hS R.obj) (π : V ⟶ Q)
    [Epi π] (t s : R ⟶ V) (hk : IsPullback t s π π) (qV : V.obj ⟶ X) (qR : R.obj ⟶ X)
    (qQ : Q.obj ⟶ X) (hπq : π.hom ≫ qQ = qV) (ht' : t.hom ≫ qV = qR) (hs' : s.hom ≫ qV = qR)
    (hopen : IsPullback
      (Space.openSubspaceOfPointsRestrict B S hS t.hom _ _
        (compl_subset_preimage_compl B S hS t.hom qV qR ht' T))
      (Space.openSubspaceOfPointsRestrict B S hS s.hom _ _
        (compl_subset_preimage_compl B S hS s.hom qV qR hs' T))
      (Space.openSubspaceOfPointsRestrict B S hS qV _ Tᶜ (by rw [Set.preimage_compl]))
      (Space.openSubspaceOfPointsRestrict B S hS qV _ Tᶜ (by rw [Set.preimage_compl])))
    (σ : (Space.openSubspaceOfPoints B S hS X Tᶜ).toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS V.obj (Space.pointsMap B S hS _ qV ⁻¹' T)ᶜ).toFunctor)
    (hσ : σ ≫ Space.openSubspaceOfPointsRestrict B S hS qV _ Tᶜ (by rw [Set.preimage_compl]) =
      𝟙 _) :
    IsIso (pullback.snd qQ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι) := by
  let J := BigFppfOver.topology B S hS
  let : HasSheafify J (Type u) := hasSheafify_bigFppfOver B S hS
  let P := sheafToPresheaf J (Type u)
  let sub : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      ∀ (Z : Set (Space.points B S hS Y)), IsClosed Z → Sheaf J (Type u) :=
    fun hY Z hZ ↦ ⟨(Space.openSubspaceOfPoints B S hS _ Zᶜ).toFunctor,
      (Space.isOpenSubspace_openSubspaceOfPoints B S hS hY _ hZ.isOpen_compl).1.isSheaf⟩
  let V' := sub hV _ (hT.preimage (Space.continuous_pointsMap B S hS qV))
  let Q' := sub hQ _ (hT.preimage (Space.continuous_pointsMap B S hS qQ))
  let R' := sub hR _ (hT.preimage (Space.continuous_pointsMap B S hS qR))
  let U' := sub hX T hT
  let π' := Space.openSubspaceOfPointsRestrict B S hS π.hom _ _
    (compl_subset_preimage_compl B S hS π.hom qQ qV hπq T)
  let φ := Space.openSubspaceOfPointsRestrict B S hS qV _ Tᶜ (by rw [Set.preimage_compl])
  let qQ' := Space.openSubspaceOfPointsRestrict B S hS qQ _ Tᶜ (by rw [Set.preimage_compl])
  have hP1 := isPullback_ι_openSubspaceOfPoints_of_eq π.hom _
    (by rw [preimage_pointsMap_preimage_of_comp B S hS π.hom qQ qV hπq T]) π' rfl
  have hkπ := isPullback_openSubspaceOfPointsRestrict_of_isPullback T (hk.map P) hπq ht' hs'
  let πS : V' ⟶ Q' := ObjectProperty.homMk π'
  let φS : V' ⟶ U' := ObjectProperty.homMk φ
  let tS : R' ⟶ V' := ObjectProperty.homMk (Space.openSubspaceOfPointsRestrict B S hS t.hom _ _
    (compl_subset_preimage_compl B S hS t.hom qV qR ht' T))
  let sS : R' ⟶ V' := ObjectProperty.homMk (Space.openSubspaceOfPointsRestrict B S hS s.hom _ _
    (compl_subset_preimage_compl B S hS s.hom qV qR hs' T))
  let qS : Q' ⟶ U' := ObjectProperty.homMk qQ'
  have : Epi πS := by
    have hπl : Presheaf.IsLocallySurjective J π.hom :=
      (Sheaf.isLocallySurjective_iff_epi π).mpr inferInstance
    have : Sheaf.IsLocallySurjective πS :=
      Presheaf.isLocallySurjective_of_isPullback J hP1.flip
    exact Sheaf.epi_of_isLocallySurjective πS
  have : Epi φS := by
    have : IsSplitEpi φS := ⟨⟨ObjectProperty.homMk σ, P.map_injective hσ⟩⟩
    exact IsSplitEpi.epi φS
  obtain ⟨e, he⟩ := exists_iso_of_isPullback_of_epi (t' := tS) (s' := sS) πS φS
    (isPullback_sheaf_of_hom hkπ) (isPullback_sheaf_of_hom hopen)
  have hqe : qS = e.hom := by
    rw [← cancel_epi πS, he]
    apply P.map_injective
    refine (cancel_mono (Space.openSubspaceOfPoints B S hS X Tᶜ).ι).mp ?_
    show (Space.openSubspaceOfPoints B S hS _ _).ι ≫ π.hom ≫ qQ =
      (Space.openSubspaceOfPoints B S hS _ _).ι ≫ qV
    rw [hπq]
  have : IsIso qS := hqe ▸ inferInstance
  have : IsIso qQ' := (inferInstance : IsIso (P.map qS))
  have hsq := isPullback_ι_openSubspaceOfPoints_compl B S hS qQ T qQ'
    (Space.openSubspaceOfPointsRestrict_comp_ι B S hS qQ _ _ _)
  rw [(Iso.eq_inv_comp _).mpr hsq.isoPullback_hom_snd]
  infer_instance

end AlgebraicGeometry.FormalSpace

end
