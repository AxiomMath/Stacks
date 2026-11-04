module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctions

/-!
# One neighbourhood for finitely many sections of a fibre

The proof of [Stacks, Tag 0D2N] lifts `r + 1` sections of `ℒ ^⊗ d` from the fibre `X_y` to a
neighbourhood of `y` at once.  Lifting one section at a time gives one neighbourhood per section;
this file takes their intersection.  The point is that restriction of a section to the fibre is
unchanged by first restricting it to a smaller open of the base
(`AlgebraicGeometry.pullbackSectionHom_map`), since the fibre lies over the point and so inside
the preimage of every neighbourhood of it
(`Stacks.FormalFunctions.top_le_preimage_fiberι`).

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_mem_forall_pullbackSection_fiberι_eq`: a finite family
  of sections on the fibre, each individually a restriction from some neighbourhood, is the
  restriction of a family from one common neighbourhood.

## No attribute

No `@[stacks]` attribute is attached: this is the passage from one section to a finite family,
bookkeeping inside the proof of [Stacks, Tag 0D2N] and not the assertion of a numbered result.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-- **One neighbourhood serves finitely many sections of the fibre.**  If every member of a
finite family of sections of `ℳ|_{X_y}` is the restriction of a section of `ℳ` over `f ⁻¹ᵁ U`
for some open `U ∋ y` — a different `U` for each member — then one `U` serves the whole family.

Take the intersection of the finitely many opens, which still contains `y`, and restrict each
section to it; the restriction to the fibre does not change, by
`AlgebraicGeometry.pullbackSectionHom_map`, because the fibre lies inside the preimage of every
neighbourhood of `y`. -/
theorem exists_mem_forall_pullbackSection_fiberι_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (y : S) {ι : Type*} [Finite ι]
    (t : ι → Γ((Scheme.Modules.pullback (f.fiberι y)).obj M, ⊤))
    (h : ∀ i, ∃ (U : S.Opens) (hy : y ∈ U) (a : Γ(M, f ⁻¹ᵁ U)),
      Scheme.Modules.pullbackSection (f.fiberι y) M (f ⁻¹ᵁ U) ⊤
        (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hy) a = t i) :
    ∃ (U : S.Opens) (hy : y ∈ U) (a : ι → Γ(M, f ⁻¹ᵁ U)),
      ∀ i, Scheme.Modules.pullbackSection (f.fiberι y) M (f ⁻¹ᵁ U) ⊤
        (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hy) (a i) = t i := by
  choose U hy a ha using h
  let W : S.Opens :=
    ⟨⋂ i, (U i : Set S), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hle : ∀ i, f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U i := fun i _ hz =>
    Set.iInter_subset (fun j => (U j : Set S)) i hz
  have hyW : y ∈ W := Set.mem_iInter.mpr hy
  exact ⟨W, hyW, fun i => M.val.map (homOfLE (hle i)).op (a i), fun i =>
    (AlgebraicGeometry.pullbackSectionHom_map (f.fiberι y) M (f ⁻¹ᵁ U i) (f ⁻¹ᵁ W) (hle i) ⊤
      (Stacks.FormalFunctions.top_le_preimage_fiberι f y W hyW)
      (Stacks.FormalFunctions.top_le_preimage_fiberι f y (U i) (hy i)) (a i)).trans (ha i)⟩

end Stacks.AmpleFibreNeighbourhood

end
