module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.LocalMinimalPrime

/-!
# Translating a local ring of a group scheme to the identity

Let `G` be a group scheme over a field `k` and `g ∈ G` a point.  After base change to the residue
field `K = κ(g)` the point `g` acquires a canonical `K`-rational point `g'` of `G_K` above it, and
translation by `g'` is an automorphism of `G_K` carrying the identity to `g'`.  The local ring of
`G` at `g` therefore maps by a flat local homomorphism to the local ring of the group scheme
`G_K` over `K` at its identity.  This is the device of [Stacks, Tag 047M] and [Stacks, Tag 045X]
("we may extend the ground field at will, and then translate"), extracted so that properties of
local rings which descend along flat local homomorphisms reduce to the identity.

## Main results

* `AlgebraicGeometry.exists_flat_localHom_stalk_identity`: the local ring of a group scheme over
  `k` at any point maps by a flat local homomorphism to the local ring at the identity of a group
  scheme over a field extension of `k`.
* `AlgebraicGeometry.isReduced_stalk_of_isReduced_stalk_identity`: hence it is reduced as soon as
  that local ring at the identity is.
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- The local ring of a group scheme over a field `k` at a point `g` maps by a flat local
homomorphism to the local ring, at its identity, of a group scheme over a field extension `K`
of `k`: base change to the residue field `K = κ(g)` and translate the tautological `K`-point
above `g` to the identity. -/
theorem exists_flat_localHom_stalk_identity (k : Type u) [Field k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) (g : G.X.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (H : Over (Spec (CommRingCat.of K)))
      (_ : GrpObj H) (φ : G.X.left.presheaf.stalk g ⟶
        H.left.presheaf.stalk ((η[H]).left (IsLocalRing.closedPoint K))),
      IsLocalHom φ.hom ∧ φ.hom.Flat := by
  classical
  let f := G.X.hom
  let K := G.X.left.residueField g
  let b : Spec K ⟶ Spec (.of k) := G.X.left.fromSpecResidueField g ≫ f
  let Y : Scheme := Limits.pullback f b
  let t : Spec K ⟶ Y :=
    Limits.pullback.lift (G.X.left.fromSpecResidueField g) (𝟙 _) (by simp [b])
  let y : Y := t (IsLocalRing.closedPoint K)
  have hy : (Limits.pullback.fst f b) y = g := by
    show (t ≫ Limits.pullback.fst f b) (IsLocalRing.closedPoint K) = g
    rw [Limits.pullback.lift_fst]
    exact Scheme.fromSpecResidueField_apply g _
  let : GrpObj (Over.mk f) := G.grp
  let H : Over (Spec (.of K)) := Over.mk (Limits.pullback.snd f b)
  let : GrpObj H := Over.grpObjMkPullbackSnd
  let x' : MonoidalCategoryStruct.tensorUnit (Over (Spec (.of K))) ⟶ H :=
    Over.homMk t (by dsimp [t, H]; rw [Limits.pullback.lift_snd]; rfl)
  let α := (GrpObj.mulRight x').symm ≪≫ (GrpObj.mulRight (η[H]))
  have hα : x' ≫ α.hom = η[H] := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left y = (η[H]).left (IsLocalRing.closedPoint K) := by
    let s : Spec K := IsLocalRing.closedPoint K
    have h := congrArg
      (fun z : MonoidalCategoryStruct.tensorUnit (Over (Spec (.of K))) ⟶ H =>
        z.left s) hα
    change (t ≫ α.hom.left) s = _ at h
    rw [Scheme.Hom.comp_apply] at h
    simpa [y, s] using h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  let algK : Algebra k K := (Spec.preimage b).hom.toAlgebra
  -- the flat local map `O_{G,g} → O_{Y,y}`
  let φ₁ : G.X.left.presheaf.stalk g ⟶ Y.presheaf.stalk y :=
    (G.X.left.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
      (Limits.pullback.fst f b).stalkMap y
  -- the isomorphism `O_{Y,y} ≅ O_{H,e}` along the translation
  let φ₂ : Y.presheaf.stalk y ⟶
      H.left.presheaf.stalk ((η[H]).left (IsLocalRing.closedPoint K)) :=
    inv (α.hom.left.stalkMap y) ≫ (H.left.presheaf.stalkCongr (.of_eq hα')).hom
  refine ⟨K, inferInstance, algK, H, inferInstance, φ₁ ≫ φ₂, ?_, ?_⟩ <;>
    dsimp only [φ₁, φ₂] <;> simp only [CommRingCat.hom_comp]
  · infer_instance
  · refine RingHom.Flat.comp (RingHom.Flat.comp ?_ ?_) (RingHom.Flat.comp ?_ ?_) <;>
      first
      | exact Flat.stalkMap _ _
      | exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

end AlgebraicGeometry

end
