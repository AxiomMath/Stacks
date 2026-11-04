module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspacePushforwardImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspacePreimageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement

/-!
# The complement of the zero locus at a stage of an inverse system

Let `Y = lim Y_k` be a directed limit of algebraic spaces along affine monomorphisms (for
instance the system of Stacks 07VR, along closed immersions), and let `T ⊆ Y_{i₀}` be a closed
subspace of finite presentation of a quasi-compact stage, for instance `T = V(ℐ_{i₀})`.  Suppose
an open immersion `j : V ⟶ Y` from an affine scheme has image `Y ∖ (T ×_{Y_{i₀}} Y)`, and is
étale and surjective over a base `X`, as the chart `j : V ⟶ Y` of the situation of Stacks 0GUY
is when `V(ℐ) = T ×_{Y_{i₀}} Y`
(`AlgebraicGeometry.Space.preimage_eq_of_pushforwardSubmodule_eq_imageSubmodule`).  Then for
some `k ≥ i₀` the open complement `V_k = Y_k ∖ (T ×_{Y_{i₀}} Y_k)` is `V` itself, with the
open immersion `j ≫ (Y ⟶ Y_k)`, and is étale and surjective over `X`; and the zero locus of the
defining ideal of a closed subspace `Z_k ⊆ Y_k` with open complement `V_k` is the complement of
the image of `V`: the condition of the situation of Stacks 0GUY at the stage `k`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_openComplement_preimage_of_range_eq_compl_of_mono`: the
  open complement at a large stage is `V`, étale and surjective over `X`.
* `AlgebraicGeometry.Space.isOpenImmersion_of_iso_openComplement` and
  `AlgebraicGeometry.Space.idealZeroLocus_eq_compl_range_of_iso_openComplement`: a scheme
  isomorphic to the open complement of a closed subspace gives the open immersion and the zero
  locus equation of the situation of Stacks 0GUY.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SN](https://stacks.math.columbia.edu/tag/07SN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The point set of the open complement of a subfunctor is the complement of its point set. -/
private theorem range_pointsMap_openComplement_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Subfunctor F) :
    Set.range (pointsMap B S hS (openComplement B S hS T).toFunctor
        (openComplement B S hS T).ι) =
      (Set.range (pointsMap B S hS T.toFunctor T.ι))ᶜ := by
  rw [openComplement_eq_openSubspaceOfPoints_compl B S hS T]
  exact range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- Composing an isomorphism onto a subfunctor with the transport along an equality of
subfunctors does not change its composite with the inclusion. -/
private theorem trans_eqToIso_hom_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W₁ W₂ : Subfunctor F} (e : A ≅ W₁.toFunctor)
    (h : W₁ = W₂) :
    (e ≪≫ eqToIso (congrArg Subfunctor.toFunctor h)).hom ≫ W₂.ι = e.hom ≫ W₁.ι := by
  subst h
  simp

/-- **A scheme isomorphic to the open complement of a closed subspace is an open immersion into
the space.**  The closed subspace `Z` may be given through a subfunctor `T` equal to it, as when
`T = V(ℐ') ×_{Y'} Y` is the inverse image of a closed subspace of another stage. -/
theorem isOpenImmersion_of_iso_openComplement {Y : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS Y.1) {T : Subfunctor Y.1} (hZT : Z.1 = T)
    {V : BigFppfOver B S hS} (j : yoneda.obj V ⟶ Y.1)
    (e : yoneda.obj V ≅ (openComplement B S hS T).toFunctor)
    (he : e.hom ≫ (openComplement B S hS T).ι = j) :
    IsOpenImmersion B S hS j := by
  subst hZT
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp _ e.hom _
    (isOpenSubspace_openComplement B S hS Y.2 Z.1 Z.2).2

/-- **The zero locus equation of Stacks 0GUY from an open complement.**  If `j : V ⟶ Y`
identifies the scheme `V` with the open complement of a closed subspace `Z ⊆ Y` (given through a
subfunctor `T` equal to it), then the zero
locus of the defining ideal sheaf of `Z` is the complement of the image of `j`: this is the field
`AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.idealZeroLocus_I`. -/
theorem idealZeroLocus_eq_compl_range_of_iso_openComplement {Y : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS Y.1) {T : Subfunctor Y.1} (hZT : Z.1 = T)
    {V : BigFppfOver B S hS} (j : yoneda.obj V ⟶ Y.1)
    (e : yoneda.obj V ≅ (openComplement B S hS T).toFunctor)
    (he : e.hom ≫ (openComplement B S hS T).ι = j) :
    idealZeroLocus B S hS Y (definingIdealSheaf B S hS Y Z) =
      (Set.range (pointsMap B S hS (yoneda.obj V) j))ᶜ := by
  subst hZT
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) e.hom) := fun x =>
    ⟨pointsMap B S hS _ e.inv x, by
      rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id]
      rfl⟩
  rw [← he, pointsMap_comp, hsurj.range_comp, range_pointsMap_openComplement_ι, compl_compl,
    range_pointsMap_ι_eq_idealZeroLocus B S hS Y Z]

variable {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i₀ : I)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The complement of a closed subspace of a stage is the chart `V` at a later stage.**  Let
`D` be a directed inverse system of quasi-separated algebraic spaces with affine monomorphic
transition morphisms and limit `c`, let `T ⊆ D_{i₀}` be a closed subspace of finite presentation
of a quasi-compact stage, and `p : D_{i₀} ⟶ X` locally of finite presentation.  Let
`j : V ⟶ lim D` be an open immersion from an affine scheme whose image is the complement of
`T ×_{D_{i₀}} lim D`, with `V ⟶ lim D ⟶ D_{i₀} ⟶ X` étale and surjective.  Then for some
`k ≥ i₀`, the morphism `j ≫ (lim D ⟶ D_k)` identifies `V` with the open complement
`D_k ∖ (T ×_{D_{i₀}} D_k)`, which is étale and surjective over `X`.

This is `AlgebraicGeometry.Space.exists_iso_preimage_of_isLocallyOfFinitePresentation_of_mono`
for the open complement of `T`, after identifying the image of `j` with the inverse image of
that open complement through Stacks 03BZ
(`AlgebraicGeometry.Space.range_eq_openSubspaceOfPoints_of_isOpenImmersion`). -/
theorem exists_iso_openComplement_preimage_of_range_eq_compl_of_mono
    [IsDirected I (· ≤ ·)] (c : Cone D) (hc : IsLimit c)
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (hmono : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), Mono (D.map f))
    (hc' : IsAlgebraicSpace B S hS c.pt)
    (hqc : IsQuasiCompactSpace B S hS (D.obj (op i₀)))
    (T : Subfunctor (D.obj (op i₀))) (hT : IsClosedSubspace B S hS T)
    (hTfp : IsFinitePresentation B S hS T.ι)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (p : D.obj (op i₀) ⟶ X) (hp : IsLocallyOfFinitePresentation B S hS p)
    {V : BigFppfOver B S hS} (j : yoneda.obj V ⟶ c.pt) (hj : IsOpenImmersion B S hS j)
    (hjT : Set.range (pointsMap B S hS (yoneda.obj V) j) =
      (Set.range (pointsMap B S hS (T.preimage (c.π.app (op i₀))).toFunctor
        (T.preimage (c.π.app (op i₀))).ι))ᶜ)
    (het : IsEtale B S hS (j ≫ c.π.app (op i₀) ≫ p))
    (hsurj : IsSurjective B S hS (j ≫ c.π.app (op i₀) ≫ p)) :
    ∃ (k : I) (hk : i₀ ≤ k)
      (e : yoneda.obj V ≅
        (openComplement B S hS (T.preimage (D.map (homOfLE hk).op))).toFunctor),
      e.hom ≫ (openComplement B S hS (T.preimage (D.map (homOfLE hk).op))).ι =
          j ≫ c.π.app (op k) ∧
        IsOpenImmersion B S hS (j ≫ c.π.app (op k)) ∧
        IsEtale B S hS (j ≫ c.π.app (op k) ≫ D.map (homOfLE hk).op ≫ p) ∧
        IsSurjective B S hS (j ≫ c.π.app (op k) ≫ D.map (homOfLE hk).op ≫ p) := by
  set W₀ := openComplement B S hS T with hW₀
  have hW₀open : IsOpenSubspace B S hS W₀ := isOpenSubspace_openComplement B S hS (hD _) T hT
  have hW₀qc : IsQuasiCompactSpace B S hS W₀.toFunctor :=
    isQuasiCompactSpace_openComplement_of_isFinitePresentation (hD _) hqc T hT hTfp
  have hW₀p : IsLocallyOfFinitePresentation B S hS (W₀.ι ≫ p) :=
    isLocallyOfFinitePresentation_comp B S hS hW₀open.1 (hD _) hX _ _
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hW₀open.2) hp
  -- the image of `j` is the inverse image of `W₀` in the limit
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  have hrange : Subfunctor.range j = W₀.preimage (c.π.app (op i₀)) := by
    rw [range_eq_openSubspaceOfPoints_of_isOpenImmersion B S hS j hj, hjT, hW₀,
      openComplement_preimage, openComplement_eq_openSubspaceOfPoints_compl]
    rfl
  set e₁ : yoneda.obj V ≅ (W₀.preimage (c.π.app (op i₀))).toFunctor :=
    asIso (Subfunctor.toRange j) ≪≫ eqToIso (congrArg Subfunctor.toFunctor hrange) with he₁def
  have he₁ : e₁.hom ≫ (W₀.preimage (c.π.app (op i₀))).ι = j := by
    rw [he₁def, trans_eqToIso_hom_ι _ hrange, asIso_hom, Subfunctor.toRange_ι]
  have hφ : (W₀.preimage (c.π.app (op i₀))).ι ≫ c.π.app (op i₀) ≫ p =
      e₁.inv ≫ j ≫ c.π.app (op i₀) ≫ p := by
    rw [← he₁, Category.assoc, Iso.inv_hom_id_assoc]
  obtain ⟨k, hk, e₂, he₂⟩ := exists_iso_preimage_of_isLocallyOfFinitePresentation_of_mono B S hS
    D i₀ hZ c hc hD hAffine hQs hmono hc' W₀ hW₀open hW₀qc hX p hW₀p (by
      rw [hφ]
      exact isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_comp B S hS (isEtale_of_isIso B S hS e₁.inv) het))
  have hW : ∀ {k' : I} (hk' : i₀ ≤ k'), W₀.preimage (D.map (homOfLE hk').op) =
      openComplement B S hS (T.preimage (D.map (homOfLE hk').op)) := fun hk' =>
    openComplement_preimage B S hS T _
  have hstage : (e₁ ≪≫ e₂).hom ≫ (W₀.preimage (D.map (homOfLE hk).op)).ι =
      j ≫ c.π.app (op k) := by
    rw [Iso.trans_hom, Category.assoc, he₂, ← Category.assoc, he₁]
  have hopen : IsOpenImmersion B S hS (j ≫ c.π.app (op k)) := by
    rw [← hstage]
    exact MorphismProperty.RespectsIso.precomp _ (e₁ ≪≫ e₂).hom _
      (isOpenSubspace_preimage B S hS _ W₀ (hD _) (hD _) hW₀open).2
  have hcomp : j ≫ c.π.app (op k) ≫ D.map (homOfLE hk).op ≫ p = j ≫ c.π.app (op i₀) ≫ p := by
    rw [← Category.assoc (c.π.app (op k)), c.w]
  refine ⟨k, hk, (e₁ ≪≫ e₂) ≪≫ eqToIso (congrArg Subfunctor.toFunctor (hW hk)), ?_, hopen,
    ?_, ?_⟩
  · rw [trans_eqToIso_hom_ι _ (hW hk), hstage]
  · rw [hcomp]
    exact het
  · rw [hcomp]
    exact hsurj

end AlgebraicGeometry.Space

end
