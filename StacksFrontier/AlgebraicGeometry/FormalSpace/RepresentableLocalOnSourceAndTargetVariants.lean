module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget

/-!
# Affine open covers in the big fppf site with size bounds

Every object of the big fppf site of a scheme `S` is covered by open immersions from affine
objects of the site, indexed by a type whose cardinality, like the size of each member, is bounded
by the size of the object.

## Main results

* `exists_affineOpens_cover_site'`: An object of the big fppf site of `S` is covered by open
  immersions from affine objects, with the index type and the members bounded in size by the
  object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine opens of an object of the big fppf site of `S`, as a family of objects of the
site covering it by open immersions, together with the bound on the index type and on the
members by the size of the object. -/
theorem exists_affineOpens_cover_site' (T : BigFppfOver B S hS) :
    ∃ (I : Type u) (X : I → BigFppfOver B S hS) (g : ∀ i, X i ⟶ T),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (X i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj T,
        ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      Cardinal.mk I ≤ ((BigFppfOver.toScheme B S hS).obj T).size ∧
      ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤
        ((BigFppfOver.toScheme B S hS).obj T).size := by
  classical
  set W : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj T with hWdef
  let hU (i : W.affineOpens) : B.Contains (i.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let fO (i : W.affineOpens) : B.obj (hU i) ⟶ T.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hU i)) ⟶ B.inclusion.obj T.left from i.1.ι)
  let X (i : W.affineOpens) : BigFppfOver B S hS := Over.mk (fO i ≫ T.hom)
  let g (i : W.affineOpens) : X i ⟶ T := Over.homMk (fO i) (by simp [X])
  have hfmap (i : W.affineOpens) : (BigFppfOver.toScheme B S hS).map (g i) = i.1.ι :=
    B.inclusion.map_preimage _
  refine ⟨W.affineOpens, X, g, fun i => i.2, fun i => ?_, fun x => ?_,
    Scheme.mk_affineOpens_le_size W, fun i => Scheme.size_coe_opens_le W i.1⟩
  · rw [hfmap i]
    infer_instance
  · obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
    refine ⟨i, ⟨x, hxi⟩, ?_⟩
    rw [hfmap i]
    rfl

end AlgebraicGeometry.FormalSpace

end
