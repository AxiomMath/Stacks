module

public import StacksFrontier.AlgebraicGeometry.Size.Pullback

/-!
# A finite affine covering of a fibre product by products of affine opens

A quasi-compact fibre product `X ×_S Y` is covered by finitely many opens of the form
`pr₁⁻¹ U ⊓ pr₂⁻¹ V` with `U ⊆ X` and `V ⊆ Y` affine opens, each of which is itself an affine
open of `X ×_S Y`.

## Main results

* `AlgebraicGeometry.exists_finite_affine_product_cover`: **a quasi-compact fibre product is
  covered by finitely many affine opens of the form `pr₁⁻¹ U ⊓ pr₂⁻¹ V` with `U` and `V`
  affine.**

## References

* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- **A quasi-compact fibre product is covered by finitely many affine opens of the form
`pr₁⁻¹ U ⊓ pr₂⁻¹ V`, with `U` an affine open of `X` and `V` an affine open of `Y`.** -/
theorem exists_finite_affine_product_cover (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace (pullback f g : Scheme.{u})] :
    ∃ (m : ℕ) (U : Fin m → X.affineOpens) (V : Fin m → Y.affineOpens),
      (∀ i, IsAffineOpen (pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1)) ∧
      (⨆ i, pullback.fst f g ⁻¹ᵁ (U i).1 ⊓ pullback.snd f g ⁻¹ᵁ (V i).1) = ⊤ := by
  classical
  set J := {p : X.affineOpens × Y.affineOpens //
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ p.1.1 ⊓ pullback.snd f g ⁻¹ᵁ p.2.1)}
  set W : J → (pullback f g).Opens := fun p =>
    pullback.fst f g ⁻¹ᵁ p.1.1.1 ⊓ pullback.snd f g ⁻¹ᵁ p.1.2.1
  have hcover : (Set.univ : Set (pullback f g : Scheme.{u})) ⊆ ⋃ p : J, (W p : Set _) := by
    rintro x -
    obtain ⟨U, a, V, b, S₀, ha, hb, hxa, hxb⟩ := exists_basicOpen_mem_inf_preimage f g x
    have hDa : IsAffineOpen (X.basicOpen a) := U.2.basicOpen a
    have hDb : IsAffineOpen (Y.basicOpen b) := V.2.basicOpen b
    have : IsAffine (X.basicOpen a).toScheme := hDa
    have : IsAffine (Y.basicOpen b).toScheme := hDb
    have : IsAffine S₀.1.toScheme := S₀.2
    exact Set.mem_iUnion.mpr
      ⟨⟨(⟨X.basicOpen a, hDa⟩, ⟨Y.basicOpen b, hDb⟩), isAffineOpen_inf_preimage f g ha hb⟩,
        ⟨hxa, hxb⟩⟩
  obtain ⟨t, ht⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
    (fun p : J => (W p : Set (pullback f g : Scheme.{u}))) (fun p => (W p).2) hcover
  refine ⟨t.card, fun j => (t.equivFin.symm j).1.1.1, fun j => (t.equivFin.symm j).1.1.2,
    fun j => (t.equivFin.symm j).1.2, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine Opens.mem_iSup.mpr ⟨t.equivFin ⟨p, hp⟩, ?_⟩
  have hx : x ∈ W (t.equivFin.symm (t.equivFin ⟨p, hp⟩)) := by
    rw [Equiv.symm_apply_apply]
    exact hxp
  exact hx

end AlgebraicGeometry

end

end
