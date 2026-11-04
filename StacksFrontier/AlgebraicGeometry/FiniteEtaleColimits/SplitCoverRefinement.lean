module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits

/-!
# A morphism of split covers is a map of index types, locally on the base

Let `X` be a scheme and let `ι`, `κ` be finite index types. A morphism
`h : ∐_{j : κ} X ⟶ ∐_{i : ι} X` of schemes over `X` need *not* be induced by a map `κ → ι` of
index types: its restriction to the `j`-th summand is a section of the fold map
`∐_{i : ι} X ⟶ X`, and such a section is a decomposition of `X` into `ι` pieces, which is a map
of index types only when `X` has no idempotents to separate.

This file shows that it *is* induced by a map of index types locally on `X`: the opens
```
V φ = ⋂_{j : κ} (ι_j ≫ h) ⁻¹ (image of the φ j-th summand),    φ : κ → ι
```
cover `X`, and on `V φ` the `j`-th component of `h` lands in the `φ j`-th summand.

## Main results

* `Stacks.FundamentalGroup.iSup_opensRange_sigmaι` — the images of the summands cover a
  coproduct of schemes.
* `Stacks.FundamentalGroup.exists_openCover_le_preimage_opensRange` — a finite family of
  morphisms into `∐_{i : ι} X` is, on each member of an open covering of `X` indexed by
  `κ → ι`, a family of morphisms into single summands.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.FundamentalGroup

/-- **The images of the summands cover a coproduct of schemes.** -/
theorem iSup_opensRange_sigmaι {ι : Type u} (X : ι → Scheme.{u}) :
    (⨆ i, (Sigma.ι X i).opensRange) = ⊤ := by
  refine Opens.ext (Set.eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk X).surjective x
  simp only [Opens.coe_iSup, Set.mem_iUnion]
  exact ⟨i, y, (sigmaMk_mk X i y).symm⟩

/-- **A finite family of morphisms into a coproduct of copies of the base is a map of index
types, locally on the base.** For `g : κ → (X ⟶ ∐_{i : ι} X)` with `κ` finite, the opens
`V φ = ⋂_j (g j) ⁻¹ (image of the φ j-th summand)`, indexed by the maps `φ : κ → ι`, cover `X`,
and on `V φ` the morphism `g j` lands in the `φ j`-th summand. -/
theorem exists_openCover_le_preimage_opensRange {X : Scheme.{u}} {ι κ : Type u} [Finite κ]
    (g : κ → (X ⟶ ∐ fun _ : ι ↦ X)) :
    ∃ V : (κ → ι) → X.Opens, (⨆ φ, V φ) = ⊤ ∧
      ∀ φ j, V φ ≤ (g j) ⁻¹ᵁ (Sigma.ι (fun _ : ι ↦ X) (φ j)).opensRange := by
  refine ⟨fun φ ↦ ⟨⋂ j, ((g j) ⁻¹ᵁ (Sigma.ι (fun _ : ι ↦ X) (φ j)).opensRange : Set X),
      isOpen_iInter_of_finite fun j ↦ ((g j) ⁻¹ᵁ _).isOpen⟩, ?_,
    fun φ j ↦ Set.iInter_subset _ j⟩
  refine Opens.ext (Set.eq_univ_of_forall fun x ↦ ?_)
  have hmem : ∀ j, ∃ i, x ∈ (g j) ⁻¹ᵁ (Sigma.ι (fun _ : ι ↦ X) i).opensRange := by
    intro j
    have hx : (g j) x ∈ (⨆ i, (Sigma.ι (fun _ : ι ↦ X) i).opensRange) := by
      rw [iSup_opensRange_sigmaι]; trivial
    rw [Opens.mem_iSup] at hx
    exact hx.imp fun i hi ↦ (Scheme.Hom.mem_preimage (g j)).2 hi
  choose φ hφ using hmem
  simp only [Opens.coe_iSup, Set.mem_iUnion]
  exact ⟨φ, Set.mem_iInter.2 fun j ↦ hφ j⟩

end Stacks.FundamentalGroup

end
