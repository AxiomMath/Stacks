module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain

/-!
# Counting the blowups in a sequence of blowups at closed points

`Stacks.ResolutionOfSurfaces.PointBlowupChain X T Y f` says that `f : Y ⟶ X` is a finite
composition of blowups at closed points lying over `T`, but — being a `Prop` indexed only by its
composite morphism — it does not record how many blowups there are. Some statements name that
number: [Stacks, Tag 0CDC] resolves the standard nodal model `R[x, y]/(xy - πⁿ)` by a chain of
exactly `⌊n/2⌋` blowups at closed points. This file adds the same inductive predicate with the
number of steps as an extra index, together with the forgetful implication and the composition
rule that adds the two lengths.

## Main definitions

* `Stacks.ResolutionOfSurfaces.PointBlowupChainOfLength` — a sequence of exactly `k` blowups at
  closed points lying over a given set of points, indexed by its composite morphism.

## Main results

* `Stacks.ResolutionOfSurfaces.PointBlowupChainOfLength.toPointBlowupChain` — forgetting the
  length gives a `Stacks.ResolutionOfSurfaces.PointBlowupChain`.
* `Stacks.ResolutionOfSurfaces.PointBlowupChainOfLength.comp` — chains compose, and the lengths
  add.

## References

* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- A sequence of exactly `k` blowups at closed points lying over `T ⊆ X`, indexed by the
composite morphism to `X`: either the identity of `X`, with `k = 0`, or the blowup of such a
sequence of length `k` at a closed point of its source whose image in `X` belongs to `T`, which
has length `k + 1`. -/
public inductive PointBlowupChainOfLength (X : Scheme.{u}) (T : Set X) :
    ℕ → ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop
  | refl : PointBlowupChainOfLength X T 0 X (𝟙 X)
  | step {k : ℕ} {W : Scheme.{u}} {h : W ⟶ X} (hh : PointBlowupChainOfLength X T k W h) (w : W)
      (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T) :
      PointBlowupChainOfLength X T (k + 1)
        (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)

/-- **Forgetting the number of steps.** -/
public theorem PointBlowupChainOfLength.toPointBlowupChain {X : Scheme.{u}} {T : Set X} {k : ℕ}
    {Y : Scheme.{u}} {f : Y ⟶ X} (hf : PointBlowupChainOfLength X T k Y f) :
    PointBlowupChain X T Y f := by
  induction hf with
  | refl => exact .refl
  | step hh w hw hwT ih => exact ih.step w hw hwT

/-- **Counted chains compose, and the lengths add.** A counted chain over a set of points of the
source of another counted chain composes with it, provided that set maps into the set of the
outer chain. -/
public theorem PointBlowupChainOfLength.comp {X Y Z : Scheme.{u}} {T : Set X} {S : Set Y}
    {k l : ℕ} {f : Y ⟶ X} {g : Z ⟶ Y} (hf : PointBlowupChainOfLength X T k Y f)
    (hg : PointBlowupChainOfLength Y S l Z g) (hST : ∀ y ∈ S, f.base y ∈ T) :
    PointBlowupChainOfLength X T (k + l) Z (g ≫ f) := by
  induction hg with
  | refl => simpa using hf
  | step hh w hw hwS ih =>
    rw [Category.assoc, ← Nat.add_assoc]
    exact ih.step w hw (by simpa using hST _ hwS)

end Stacks.ResolutionOfSurfaces

end
