module

public import StacksFrontier.AlgebraicGeometry.LimitApproxChain.StageIndex

/-!
# The diagram of distinguished subalgebras over the index of pairs

Let `F : K ⥤ CommRingCat` be a diagram of rings over a preorder `K`, and let `P` single out
distinguished subalgebras of each `F.obj k`. The preorder `Stacks.StageSubalgebra F P` consists of
the pairs `(k, A)` of a stage `k` and a distinguished subalgebra `A` of `F.obj k`, with
`(k, A) ≤ (k', A')` exactly when `k ≤ k'` and the transition `F.obj k ⟶ F.obj k'` carries `A`
into `A'`. This file constructs the diagram of these subalgebras over that preorder, and the
inverse system of their spectra.

## Main definitions

* `Stacks.StageSubalgebra.stage`, `Stacks.StageSubalgebra.sub`: the stage and the subalgebra of
  a pair.
* `Stacks.StageSubalgebra.inclusionAlgHom`: the transition of `F`, restricted to the subalgebra
  at the source and corestricted to the subalgebra at the target.
* `Stacks.StageSubalgebra.inclusionHom`: the same map as a morphism of `CommRingCat`.
* `Stacks.StageSubalgebra.ringDiagram`: the diagram of distinguished subalgebras.
* `Stacks.StageSubalgebra.specDiagram`: the inverse system of their spectra, a functor out of the
  opposite preorder.

## Main results

* `Stacks.StageSubalgebra.inclusionAlgHom_coe`: the transition map of subalgebras is computed by
  the transition of `F` on underlying elements.
* `Stacks.StageSubalgebra.isAffineHom_specDiagram_map`: every transition morphism of
  `Stacks.StageSubalgebra.specDiagram` is affine.

## Implementation notes

The stages, the rings and the schemes all live in the universe `u`, so that the preorder of
pairs, read as a category, has its homs in `Type u`.

The stage and the subalgebra of a pair are reached through `Stacks.StageSubalgebra.stage` and
`Stacks.StageSubalgebra.sub` rather than through the projections of the underlying sigma type.

## What is NOT done here

The *second leg* of the glueing — the natural transformation whose components factor the models
of the overlap through these spectra — is not built here, and neither is its inverse-image
condition, for which see the image computation
`AlgebraicGeometry.exists_isFiniteTypeOpenModel_opensRange_eq`.  Nothing
here produces a cone, a limit, or an inhabitant of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`.  Tag 07RN is not proved and no tag attribute
is attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.StageSubalgebra

variable {K : Type u} [Preorder K] {F : K ⥤ CommRingCat.{u}}
  {P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop}

/-- The stage of a pair of the index. -/
def stage (j : StageSubalgebra F P) : K := j.1

/-- The distinguished subalgebra of a pair of the index. -/
def sub (j : StageSubalgebra F P) : Subalgebra ℤ (F.obj (stage j)) := j.2.1

/-- The stage inequality underlying an inequality of pairs. -/
lemma le_stage {j k : StageSubalgebra F P} (h : j ≤ k) : stage j ≤ stage k :=
  h.elim fun h _ ↦ h

/-- The transport condition underlying an inequality of pairs, at the canonical stage
inequality. -/
lemma transport_le {j k : StageSubalgebra F P} (h : j ≤ k) :
    transport (le_stage h) (sub j) ≤ sub k :=
  h.elim fun _ hle ↦ hle

/-- **The transition map of the diagram of distinguished subalgebras, as an algebra map.**  It
is the transition of the diagram of rings, restricted to the subalgebra at the source and
corestricted to the subalgebra at the target. -/
def inclusionAlgHom {j k : StageSubalgebra F P} (h : j ≤ k) : sub j →ₐ[ℤ] sub k :=
  ((F.map (homOfLE (le_stage h))).hom.toIntAlgHom.comp (sub j).val).codRestrict (sub k)
    fun a ↦ transport_le h (Subalgebra.mem_map.mpr ⟨a.1, a.2, rfl⟩)

/-- On underlying elements, `inclusionAlgHom h` is the transition map of `F`. -/
@[simp]
lemma inclusionAlgHom_coe {j k : StageSubalgebra F P} (h : j ≤ k) (a : sub j) :
    (inclusionAlgHom h a : F.obj (stage k)) =
      F.map (homOfLE (le_stage h)) (a : F.obj (stage j)) :=
  rfl

/-- The transition map of the diagram of distinguished subalgebras. -/
def inclusionHom {j k : StageSubalgebra F P} (h : j ≤ k) :
    CommRingCat.of (sub j) ⟶ CommRingCat.of (sub k) :=
  CommRingCat.ofHom (inclusionAlgHom h).toRingHom

/-- Two morphisms between subalgebras are equal if they agree on underlying elements. -/
private lemma hom_ext_of_coe_eq {j k : StageSubalgebra F P}
    {f g : CommRingCat.of (sub j) ⟶ CommRingCat.of (sub k)}
    (h : ∀ a : sub j, (f a : F.obj (stage k)) = g a) : f = g :=
  CommRingCat.hom_ext (RingHom.ext fun a ↦ Subtype.ext (h a))

/-- The transition map at a reflexive inequality is the identity. -/
lemma inclusionHom_rfl (j : StageSubalgebra F P) : inclusionHom (le_refl j) = 𝟙 _ := by
  refine hom_ext_of_coe_eq fun a ↦ ?_
  simp [inclusionHom]

/-- The transition map at a composite inequality is the composite of the transition maps. -/
lemma inclusionHom_trans {j k l : StageSubalgebra F P} (h : j ≤ k) (h' : k ≤ l) :
    inclusionHom (h.trans h') = inclusionHom h ≫ inclusionHom h' := by
  refine hom_ext_of_coe_eq fun a ↦ ?_
  change (inclusionAlgHom (h.trans h') a : F.obj (stage l)) =
    (inclusionAlgHom h' (inclusionAlgHom h a) : F.obj (stage l))
  rw [inclusionAlgHom_coe, inclusionAlgHom_coe, inclusionAlgHom_coe,
    Subsingleton.elim (homOfLE (le_stage (h.trans h')))
      (homOfLE (le_stage h) ≫ homOfLE (le_stage h')), F.map_comp]
  rfl

/-- **The diagram of distinguished subalgebras** over the index of pairs. -/
def ringDiagram (F : K ⥤ CommRingCat.{u}) (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop) :
    StageSubalgebra F P ⥤ CommRingCat.{u} where
  obj j := CommRingCat.of (sub j)
  map {_ _} u := inclusionHom (leOfHom u)
  map_id j := inclusionHom_rfl j
  map_comp {_ _ _} u v := inclusionHom_trans (leOfHom u) (leOfHom v)

/-- The object of `ringDiagram F P` at a pair is its distinguished subalgebra. -/
@[simp]
lemma ringDiagram_obj (j : StageSubalgebra F P) :
    (ringDiagram F P).obj j = CommRingCat.of (sub j) := rfl

/-- The morphism of `ringDiagram F P` along `u` is the transition map of subalgebras. -/
@[simp]
lemma ringDiagram_map {j k : StageSubalgebra F P} (u : j ⟶ k) :
    (ringDiagram F P).map u = inclusionHom (leOfHom u) := rfl

/-- The inequality of pairs underlying a morphism of the opposite preorder. -/
lemma le_of_dual_hom {j k : (StageSubalgebra F P)ᵒᵈ} (u : j ⟶ k) :
    OrderDual.ofDual k ≤ OrderDual.ofDual j := leOfHom u

/-- **The inverse system of spectra of the distinguished subalgebras** over the opposite of the
index of pairs. -/
noncomputable abbrev specDiagram (F : K ⥤ CommRingCat.{u})
    (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop) :
    (StageSubalgebra F P)ᵒᵈ ⥤ Scheme.{u} where
  obj j := Spec (CommRingCat.of (sub (OrderDual.ofDual j)))
  map {_ _} u := Spec.map (inclusionHom (le_of_dual_hom u))
  map_id j := (congrArg Spec.map (inclusionHom_rfl (OrderDual.ofDual j))).trans (Spec.map_id _)
  map_comp {_ _ _} u v :=
    (congrArg Spec.map (inclusionHom_trans (le_of_dual_hom v) (le_of_dual_hom u))).trans
      (Spec.map_comp _ _)

/-- The object of `specDiagram F P` at a pair is the spectrum of its distinguished subalgebra. -/
@[simp]
lemma specDiagram_obj (j : (StageSubalgebra F P)ᵒᵈ) :
    (specDiagram F P).obj j = Spec (CommRingCat.of (sub (OrderDual.ofDual j))) := rfl

/-- The morphism of `specDiagram F P` along `u` is the spectrum of the transition map of
subalgebras. -/
@[simp]
lemma specDiagram_map {j k : (StageSubalgebra F P)ᵒᵈ} (u : j ⟶ k) :
    (specDiagram F P).map u = Spec.map (inclusionHom (le_of_dual_hom u)) := rfl

/-- Every transition morphism of `specDiagram F P` is affine. -/
instance isAffineHom_specDiagram_map {j k : (StageSubalgebra F P)ᵒᵈ} (u : j ⟶ k) :
    IsAffineHom ((specDiagram F P).map u) :=
  inferInstanceAs (IsAffineHom (Spec.map (inclusionHom (le_of_dual_hom u))))

end Stacks.StageSubalgebra
