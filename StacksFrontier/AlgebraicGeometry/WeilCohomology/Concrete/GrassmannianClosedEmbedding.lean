module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Grassmannian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Grassmannian

/-!
# Smooth projective schemes embed into Grassmannians

Let `X` be a smooth projective scheme over a field `k`. Over the affine base `Spec k` the
structure morphism of `X` is H-projective, so there is a closed immersion `X ⟶ ℙⁿ_k` over `k`;
enlarging `n` by the linear embedding `ℙⁿ_k ⟶ ℙⁿ⁺¹_k` we may assume `n ≥ 1`. By
[Stacks, Tag 089V] projective `n`-space is the Grassmannian `G(n, n + 1)`, so `X` is a closed
subscheme of the Grassmannian `G(n, n + 1)_k` with `0 < n < n + 1`. Hence every smooth
projective scheme embeds into a Grassmannian in the range of [Stacks, Tag 0FIQ], as required in
the proof of [Stacks, Tag 0FIP].

## Main results

In the namespace `Stacks.WeilCohomology`:

* `SmoothProjectiveScheme.exists_closedImmersion_grassmannian`: `X` embeds as a closed
  subscheme into some `G(l, n)_k` with `0 < l < n`.

## References

* [Stacks Project, Tag 089V](https://stacks.math.columbia.edu/tag/089V)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
* [Stacks Project, Tag 0FIP](https://stacks.math.columbia.edu/tag/0FIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- **Every smooth projective scheme embeds into a Grassmannian.** A smooth projective scheme
`X` over `k` admits a closed immersion over `k` into the Grassmannian `G(l, n)_k` for some
`0 < l < n`; one may take `G(n, n + 1)_k = ℙⁿ_k` for `n ≥ 1` (Tag 089V). -/
theorem exists_closedImmersion_grassmannian (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ∃ l n : ℕ, 0 < l ∧ l < n ∧ ∃ ψ : X ⟶ SmoothProjectiveScheme.grassmannian k l n,
      IsClosedImmersion ψ.hom.left := by
  obtain ⟨n, i, hi, hif⟩ := (isProjective_iff_isProjectiveMorphism_of_isAffine _).1
    (SmoothProjectiveScheme.isProjective X)
  obtain ⟨j, hj, hjf⟩ :=
    exists_isClosedImmersion_projectiveSpaceOver_of_le i hi hif (Nat.le_succ n)
  set S : Scheme.{u} := Spec (.of k)
  let e : projectiveSpaceOver (n + 1) S ⟶ Grassmannian.schemeOver.{u} (n + 1) (n + 2) S :=
    pullback.map (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} (n + 1)))
      (terminal.from S) (terminal.from (Grassmannian.scheme.{u} (n + 1) (n + 2))) (𝟙 S)
      (Stacks.ProjectiveSpaceModuli.grassmannianSuccIso.{u} (n + 1)).inv (𝟙 _)
      (by simp) (terminal.hom_ext _ _)
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun a c ha hc => @IsClosedImmersion.comp _ _ _ a c ha hc⟩
  have he : IsClosedImmersion e :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
      (Category.id_comp _).symm (terminal.hom_ext _ _)
  have hef : e ≫ pullback.fst _ _ = pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  refine ⟨n + 1, n + 2, Nat.succ_pos n, Nat.lt_succ_self _,
    SmoothProjectiveScheme.homMk (j ≫ e) ?_, ?_⟩
  · show (j ≫ e) ≫ pullback.fst _ _ = X.obj.hom
    rw [Category.assoc, hef]
    exact hjf
  · show IsClosedImmersion (j ≫ e)
    infer_instance

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
