module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspaceCoveringLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendCoveringsSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# Coverings of a limit by open subspaces, under the site-containment hypothesis

Quasi-compactness of a limit of quasi-compact algebraic spaces, and the stage at which an open
covering of the limit becomes a covering, under
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_limit_of_isSiteSmall`
* `AlgebraicGeometry.Space.exists_eq_top_of_covering_limit_of_isSiteSmall`
* `AlgebraicGeometry.Space.isQuasiCompactSpace_limit_of_siteContainsBaseChangeLimits`
* `AlgebraicGeometry.Space.exists_eq_top_of_covering_limit_of_siteContainsBaseChangeLimits`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of a subfunctor -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The covering statement -/

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The limit of a cofiltered inverse system of quasi-compact algebraic spaces over `S` with
affine transition morphisms is quasi-compact: the projection to a stage is affine, hence
quasi-compact, and the base change of that projection along the identity of the stage is the
limit itself. -/
theorem isQuasiCompactSpace_limit_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) :
    IsQuasiCompactSpace B S hS (limit D) := by
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit_of_isSiteSmall B S hS D hb hD hAffine
  have hqc : IsQuasiCompact B S hS (limit.π D i₀) :=
    isQuasiCompact_of_isAffineHom' B S hS (limit.π D i₀) hlim (hD i₀)
      (isAffineHom_limitπ_of_isSiteSmall B S hS D hb hAffine i₀)
  exact isQuasiCompactSpace_of_iso B S hS
    (asIso (pullback.snd (𝟙 (D.obj i₀)) (limit.π D i₀)))
    (hqc (D.obj i₀) (hD i₀) (hCompact i₀) (𝟙 (D.obj i₀)))

/-- **A monotone family of open subspaces which covers the limit is everything at a stage.**
Let `X = limit D` be the limit of a cofiltered inverse system of quasi-compact algebraic
spaces over `S` with affine transition morphisms, and let `K i` be open subspaces of the
stages whose inverse images grow: the inverse image of `K i` in `D j` lies in `K j` for every
`f : j ⟶ i`. If every point of `X` lies in the inverse image of some `K i`, then `K i = ⊤`
for some `i`.

Quasi-separatedness of the stages is not needed. -/
theorem exists_eq_top_of_covering_limit_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (K : ∀ i, Subfunctor (D.obj i)) (hK : ∀ i, IsOpenSubspace B S hS (K i))
    (hmon : ∀ {i j : I} (f : j ⟶ i), (K i).preimage (D.map f) ≤ K j)
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (K i).toFunctor (K i).ι)) :
    ∃ i, K i = ⊤ := by
  classical
  have _ : Nonempty I := IsCofiltered.nonempty
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit_of_isSiteSmall B S hS D hb hD hAffine
  -- The point set of each `K i`, and its inverse image in the limit.
  set R : ∀ i, Set (points B S hS (D.obj i)) :=
    fun i => Set.range (pointsMap B S hS (K i).toFunctor (K i).ι) with hR
  have hRopen : ∀ i, IsOpen (R i) := fun i =>
    isOpen_range_pointsMap_of_isOpenImmersion B S hS (K i).ι (hK i).2
  set W : I → Set (points B S hS (limit D)) :=
    fun i => pointsMap B S hS (limit D) (limit.π D i) ⁻¹' R i with hW
  have hWopen : ∀ i, IsOpen (W i) := fun i =>
    (hRopen i).preimage (continuous_pointsMap B S hS (limit.π D i))
  -- `W` grows along the transition morphisms.
  have hstep : ∀ {i j : I} (f : j ⟶ i), W i ⊆ W j := by
    intro i j f x hx
    have hfac : pointsMap B S hS (limit D) (limit.π D i) x =
        pointsMap B S hS (D.obj j) (D.map f)
          (pointsMap B S hS (limit D) (limit.π D j) x) := by
      rw [← Function.comp_apply (f := pointsMap B S hS (D.obj j) (D.map f)), ← pointsMap_comp,
        limit.w]
    have hmem : pointsMap B S hS (limit D) (limit.π D j) x ∈
        Set.range (pointsMap B S hS ((K i).preimage (D.map f)).toFunctor
          ((K i).preimage (D.map f)).ι) := by
      rw [range_pointsMap_preimage_ι, Set.mem_preimage, ← hfac]
      exact hx
    exact range_pointsMap_ι_subset_of_le B S hS (hmon f) hmem
  -- The family is directed, and the limit is quasi-compact.
  have hdir : Directed (· ⊆ ·) W := fun i i' =>
    ⟨IsCofiltered.min i i', hstep (IsCofiltered.minToLeft i i'),
      hstep (IsCofiltered.minToRight i i')⟩
  have hcover : (Set.univ : Set (points B S hS (limit D))) ⊆ ⋃ i, W i := by
    intro x _
    obtain ⟨i, hi⟩ := hpoint x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have _ : CompactSpace (points B S hS (limit D)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (limit D) hlim).mp
      (isQuasiCompactSpace_limit_of_isSiteSmall B S hS D hb hD hAffine hCompact)
  obtain ⟨j, hj⟩ := isCompact_univ.elim_directed_cover W hWopen hcover hdir
  -- Descend that covering to a later stage.
  obtain ⟨k, g, hk⟩ := exists_stage_preimage_eq_univ_of_isSiteSmall B S hS D hb hD hAffine
    hCompact j (V := R j) (hRopen j) (Set.univ_subset_iff.mp hj)
  refine ⟨k, eq_top_of_range_pointsMap_eq_univ B S hS (hD k) (K k) (hK k) ?_⟩
  refine Set.univ_subset_iff.mp ?_
  rw [← hk, ← range_pointsMap_preimage_ι]
  exact range_pointsMap_ι_subset_of_le B S hS (hmon g)

/-! ### Under the chapter's standing convention -/

/-- The limit of a cofiltered inverse system of quasi-compact algebraic spaces over `S` with
affine transition morphisms, when it is an algebraic space, is quasi-compact under the convention
of Section 70.2 (tag 07SD): the projection to a stage is affine by Stacks 07SF, part (1), hence
quasi-compact, and the base change of that projection along the identity of the stage is the
limit itself. -/
theorem isQuasiCompactSpace_limit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) :
    IsQuasiCompactSpace B S hS (limit D) := by
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hqc : IsQuasiCompact B S hS (limit.π D i₀) :=
    isQuasiCompact_of_isAffineHom' B S hS (limit.π D i₀) hlim (hD i₀)
      (isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv hAffine i₀)
  exact isQuasiCompactSpace_of_iso B S hS
    (asIso (pullback.snd (𝟙 (D.obj i₀)) (limit.π D i₀)))
    (hqc (D.obj i₀) (hD i₀) (hCompact i₀) (𝟙 (D.obj i₀)))

/-- **A monotone family of open subspaces which covers the limit is everything at a stage,
under the chapter's standing convention.** Let `X = limit D` be the limit of a cofiltered inverse
system of quasi-compact algebraic spaces over `S` with affine transition morphisms, and suppose
`X` is an algebraic space. Let `K i` be open subspaces of the stages whose inverse images grow:
the inverse image of `K i` in `D j` lies in `K j` for every `f : j ⟶ i`. If every point of `X`
lies in the inverse image of some `K i`, then `K i = ⊤` for some `i`.

This is `AlgebraicGeometry.Space.exists_eq_top_of_covering_limit_of_isSiteSmall` with its
smallness hypothesis replaced by the convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, through which Stacks 07SF, part (1), and
part (3) of Stacks 01Z4 for algebraic spaces hold. Nothing is asked of the index. -/
theorem exists_eq_top_of_covering_limit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (K : ∀ i, Subfunctor (D.obj i)) (hK : ∀ i, IsOpenSubspace B S hS (K i))
    (hmon : ∀ {i j : I} (f : j ⟶ i), (K i).preimage (D.map f) ≤ K j)
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (K i).toFunctor (K i).ι)) :
    ∃ i, K i = ⊤ := by
  classical
  have _ : Nonempty I := IsCofiltered.nonempty
  -- The point set of each `K i`, and its inverse image in the limit.
  set R : ∀ i, Set (points B S hS (D.obj i)) :=
    fun i => Set.range (pointsMap B S hS (K i).toFunctor (K i).ι) with hR
  have hRopen : ∀ i, IsOpen (R i) := fun i =>
    isOpen_range_pointsMap_of_isOpenImmersion B S hS (K i).ι (hK i).2
  set W : I → Set (points B S hS (limit D)) :=
    fun i => pointsMap B S hS (limit D) (limit.π D i) ⁻¹' R i with hW
  have hWopen : ∀ i, IsOpen (W i) := fun i =>
    (hRopen i).preimage (continuous_pointsMap B S hS (limit.π D i))
  -- `W` grows along the transition morphisms.
  have hstep : ∀ {i j : I} (f : j ⟶ i), W i ⊆ W j := by
    intro i j f x hx
    have hfac : pointsMap B S hS (limit D) (limit.π D i) x =
        pointsMap B S hS (D.obj j) (D.map f)
          (pointsMap B S hS (limit D) (limit.π D j) x) := by
      rw [← Function.comp_apply (f := pointsMap B S hS (D.obj j) (D.map f)), ← pointsMap_comp,
        limit.w]
    have hmem : pointsMap B S hS (limit D) (limit.π D j) x ∈
        Set.range (pointsMap B S hS ((K i).preimage (D.map f)).toFunctor
          ((K i).preimage (D.map f)).ι) := by
      rw [range_pointsMap_preimage_ι, Set.mem_preimage, ← hfac]
      exact hx
    exact range_pointsMap_ι_subset_of_le B S hS (hmon f) hmem
  -- The family is directed, and the limit is quasi-compact.
  have hdir : Directed (· ⊆ ·) W := fun i i' =>
    ⟨IsCofiltered.min i i', hstep (IsCofiltered.minToLeft i i'),
      hstep (IsCofiltered.minToRight i i')⟩
  have hcover : (Set.univ : Set (points B S hS (limit D))) ⊆ ⋃ i, W i := by
    intro x _
    obtain ⟨i, hi⟩ := hpoint x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have _ : CompactSpace (points B S hS (limit D)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (limit D) hlim).mp
      (isQuasiCompactSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hlim hD hAffine
        hCompact)
  obtain ⟨j, hj⟩ := isCompact_univ.elim_directed_cover W hWopen hcover hdir
  -- Descend that covering to a later stage.
  obtain ⟨k, g, hk⟩ := exists_stage_preimage_eq_univ_of_siteContainsBaseChangeLimits B S hS D
    hconv hD hAffine hCompact j (V := R j) (hRopen j) (Set.univ_subset_iff.mp hj)
  refine ⟨k, eq_top_of_range_pointsMap_eq_univ B S hS (hD k) (K k) (hK k) ?_⟩
  refine Set.univ_subset_iff.mp ?_
  rw [← hk, ← range_pointsMap_preimage_ι]
  exact range_pointsMap_ι_subset_of_le B S hS (hmon g)

end AlgebraicGeometry.Space

end
