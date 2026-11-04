module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.CategoryTheory.Sites.UliftYonedaCoproduct

/-!
# Covering an object of the big fppf site by a coproduct of affine opens

Every object `T` of the big fppf site of `S` is covered, surjectively and étale, by a single
object of the site which is a coproduct of the affine opens of `T`, and whose universe-lifted
representable sheaf of `Type (u + 1)` is the coproduct of theirs.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_affineOpens_surjective_etale_sigma'`: every object of
  the big fppf site of `S` admits a surjective étale morphism from a coproduct of affine opens,
  with index and members bounded in size by the object, which is also a coproduct of
  representable sheaves of `Type (u + 1)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe v u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Cofan

variable {ι : Type v} [Small.{u} ι] (X : ι → BigFppfOver B S hS)
  {V : BigFppfOver B S hS} (j : ∀ i, X i ⟶ V)
  (hj : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
    fun i => (toScheme B S hS).map (j i)))

include hj

end Cofan

/-- Every object `T` of the big fppf site of `S` is covered, surjectively and étale, by a single
object `V` of the site which is a coproduct of affine objects `X i`, with at most `T.size` members
each of size at most `T.size`, whose coproduct injections are open immersions on underlying
schemes, and whose universe-lifted representable sheaf of `Type (u + 1)` is the coproduct of
theirs. -/
theorem exists_affineOpens_surjective_etale_sigma' (T : BigFppfOver B S hS) :
    ∃ (ι : Type u) (X : ι → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, X i ⟶ V)
      (q : V ⟶ T),
      (∀ i, IsAffine ((toScheme B S hS).obj (X i))) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (j i))) ∧
      #ι ≤ ((toScheme B S hS).obj T).size ∧
      (∀ i, ((toScheme B S hS).obj (X i)).size ≤ ((toScheme B S hS).obj T).size) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Etale ((toScheme B S hS).map q) ∧
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V)
        fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))) := by
  set W : Scheme.{u} := (toScheme B S hS).obj T with hWdef
  let hU (i : W.affineOpens) : B.Contains (i.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let f (i : W.affineOpens) : B.obj (hU i) ⟶ T.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hU i)) ⟶ B.inclusion.obj T.left from i.1.ι)
  let X (i : W.affineOpens) : BigFppfOver B S hS := Over.mk (f i ≫ T.hom)
  let g (i : W.affineOpens) : X i ⟶ T := Over.homMk (f i) (by simp [X])
  have hfmap (i : W.affineOpens) : (toScheme B S hS).map (g i) = i.1.ι :=
    B.inclusion.map_preimage _
  have hgopen (i : W.affineOpens) : IsOpenImmersion ((toScheme B S hS).map (g i)) := by
    rw [hfmap i]
    infer_instance
  have hgcov : ∀ x : (toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((toScheme B S hS).map (g i)) := by
    intro x
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
    refine ⟨i, ⟨x, hxi⟩, ?_⟩
    rw [hfmap i]
    rfl
  obtain ⟨V, j, q, -, hjopen, -, hqsurj, hqetale, hsite, hsheaf⟩ :=
    exists_surjective_etale_sigma_of_etaleCover B S hS X T g
      (fun i => have _ := hgopen i; inferInstance) hgcov T.left.property
      (Scheme.mk_affineOpens_le_size W) fun i => Scheme.size_coe_opens_le W i.1
  exact ⟨W.affineOpens, X, V, j, q, fun i => i.2, hjopen, Scheme.mk_affineOpens_le_size W,
    fun i => Scheme.size_coe_opens_le W i.1, hqsurj, hqetale, hsite, hsheaf⟩

end BigFppfOver

end AlgebraicGeometry

end
