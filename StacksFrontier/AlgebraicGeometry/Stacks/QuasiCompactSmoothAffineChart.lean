module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack

/-!
# A smooth affine presentation of a quasi-compact algebraic stack

A quasi-compact algebraic stack `𝒯` over `S` receives a 1-morphism from the algebraic stack of a
single affine scheme of the big fppf site which is smooth, surjective and representable by
algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.exists_affine_smooth_refinement_of_isOpenMap_surjective`: an open
  surjection from a scheme of the site onto a compact space is refined, smoothly, by an affine
  scheme of the site.
* `AlgebraicGeometry.Stack.exists_affine_smooth_surjective_of_isQuasiCompactStack`: a
  quasi-compact algebraic stack has a smooth surjective presentation by an affine scheme,
  representable by algebraic spaces.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open surjection from a scheme of the site onto a compact space is refined by an affine
scheme of the site, smoothly.** For an open surjection `m` from the underlying scheme of `U`
onto a compact space, there is a smooth morphism `k : A ⟶ U` from an affine scheme of the site
with `m ∘ k` surjective. -/
theorem exists_affine_smooth_refinement_of_isOpenMap_surjective
    (U : BigFppfOver B S hS) {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (m : (BigFppfOver.toScheme B S hS).obj U → Z)
    (hmOpen : IsOpenMap m) (hmSurj : Function.Surjective m) :
    ∃ (A : BigFppfOver B S hS) (k : A ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
        Smooth ((BigFppfOver.toScheme B S hS).map k) ∧
        Function.Surjective (m ∘ ((BigFppfOver.toScheme B S hS).map k).base) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let X := T.obj U
  have hv (i : X.affineOpens) : B.Contains i.1.toScheme :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι U.left.property
  have hcover : (Set.univ : Set Z) ⊆ ⋃ i : X.affineOpens, m '' (i.1 : Set X) := by
    intro z _
    obtain ⟨x, rfl⟩ := hmSurj z
    obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨V₀, hV₀⟩, x, hxV₀, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => m '' (i.1 : Set X)) (fun i => hmOpen _ i.1.isOpen) hcover
  let _ : Finite { i : X.affineOpens // i ∈ s } := s.finite_toSet
  let Y (i : s) : Scheme.{u} := i.val.1.toScheme
  let d : (∐ Y) ⟶ X := Limits.Sigma.desc (fun i : s => i.val.1.ι)
  have hY : B.Contains (∐ Y) := Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff
    B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 Y (fun i => hv i.val)
  let A : BigFppfOver B S hS :=
    Over.mk (⟨d ≫ B.inclusion.map U.hom⟩ : B.obj hY ⟶ B.obj hS)
  let k : A ⟶ U := Over.homMk ⟨d⟩ (by rfl)
  refine ⟨A, k, ?_, ?_, ?_⟩
  · change IsAffine (∐ Y)
    let instAff (i : s) : IsAffine (Y i) := i.val.2
    infer_instance
  · change Smooth d
    let : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (fun i => inferInstance)
  · intro z
    obtain ⟨i, hi, x, hx, hmx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
    have hdesc : Limits.Sigma.ι Y (⟨i, hi⟩ : s) ≫ d = i.1.ι := Limits.Sigma.ι_desc _ _
    refine ⟨(Limits.Sigma.ι Y (⟨i, hi⟩ : s)).base ⟨x, hx⟩, ?_⟩
    have hbase : d.base ((Limits.Sigma.ι Y (⟨i, hi⟩ : s)).base ⟨x, hx⟩) = x :=
      congrArg (fun φ : Y (⟨i, hi⟩ : s) ⟶ X => φ.base ⟨x, hx⟩) hdesc
    change m ((T.map k).base _) = z
    rw [show (T.map k).base = d.base from rfl, hbase, hmx]

/-- **A quasi-compact algebraic stack has a smooth presentation by an affine scheme.** A
quasi-compact algebraic stack `𝒯` over `S` receives a 1-morphism from the algebraic stack of an
affine scheme of the big fppf site of `S` which is smooth, surjective and representable by
algebraic spaces. -/
theorem exists_affine_smooth_surjective_of_isQuasiCompactStack
    (𝒯 : AlgebraicStacks.{u, w} B S hS)
    (h𝒯 : IsQuasiCompactStack.{u, w} B S hS 𝒯.val 𝒯.property) :
    ∃ (A : BigFppfOver B S hS) (α : schemeStack.{u, w} B S hS A ⟶ 𝒯),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧ AlgebraicStacks.IsSmooth B S hS α ∧
        IsSurjective B S hS α ∧ IsRepresentableByAlgebraicSpaces B S hS α.hom.hom := by
  classical
  obtain ⟨U, a₁, ha₁sm, ha₁su⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  have haflat : AlgebraicStacks.IsFlat B S hS a₁ :=
    AlgebraicStacks.isFlat_of_isSmooth B S hS a₁ ha₁sm
  have halfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS a₁ :=
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a₁ ha₁sm
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
  let _ := pointTopology B S hS 𝒯.val
  let _ : CompactSpace (AlgebraicStacks.points B S hS 𝒯) := h𝒯
  let φ := pointsHomeomorphScheme B S hS U
  let n : (BigFppfOver.toScheme B S hS).obj U → AlgebraicStacks.points B S hS 𝒯 :=
    AlgebraicStacks.pointsMap B S hS a₁ ∘ φ.symm
  have hnOpen : IsOpenMap n :=
    (AlgebraicStacks.isOpenMap_pointsMap B S hS a₁ haflat halfp).comp φ.symm.isOpenMap
  have hnSurj : Function.Surjective n := ha₁su.comp φ.symm.surjective
  obtain ⟨A, k, hAaff, hksm, hAsurj⟩ :=
    exists_affine_smooth_refinement_of_isOpenMap_surjective B S hS U n hnOpen hnSurj
  let _ := pointTopology B S hS (schemeFibredCategory B S hS A)
  let kk : schemeStack.{u, w} B S hS A ⟶ schemeStack.{u, w} B S hS U :=
    schemeStackMap.{u, w} B S hS k
  refine ⟨A, kk ≫ a₁, hAaff,
    AlgebraicStacks.isSmooth_comp B S hS kk a₁ (isSmooth_schemeStackMap.{u, w} B S hS k hksm) ha₁sm,
    ?_, ?_⟩
  · have hpt : ∀ y : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS A),
        AlgebraicStacks.pointsMap B S hS (kk ≫ a₁) y =
          n (((BigFppfOver.toScheme B S hS).map k).base
            (pointsHomeomorphScheme B S hS A y)) := by
      intro y
      rw [AlgebraicStacks.pointsMap_comp]
      change AlgebraicStacks.pointsMap B S hS a₁ (AlgebraicStacks.pointsMap B S hS kk y) =
        AlgebraicStacks.pointsMap B S hS a₁
          (φ.symm (((BigFppfOver.toScheme B S hS).map k).base
            (pointsHomeomorphScheme B S hS A y)))
      rw [← pointsHomeomorphScheme_naturality B S hS k y, Homeomorph.symm_apply_apply]
      rfl
    intro z
    obtain ⟨x, hx⟩ := hAsurj z
    obtain ⟨y, hy⟩ := (pointsHomeomorphScheme B S hS A).surjective x
    exact ⟨y, by rw [hpt y, hy]; exact hx⟩
  · obtain ⟨_, _, h𝒯diag, -⟩ := 𝒯.property
    exact isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source B S hS
      h𝒯diag (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS A) (kk ≫ a₁).hom

end AlgebraicGeometry.Stack
