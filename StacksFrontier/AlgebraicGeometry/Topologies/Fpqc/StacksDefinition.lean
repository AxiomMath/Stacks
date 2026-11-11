module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
import all StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization

/-!
# The definition of an fpqc covering

Mathlib's `Scheme.fpqcPrecoverage` is the precoverage of flat, jointly surjective,
quasi-compact families. This file identifies membership in it with the literal condition of the
definition of an fpqc covering: every member is flat, and every affine open of the target is the
union of the images of finitely many affine opens of the sources.

## Main results

* `AlgebraicGeometry.ofArrows_mem_fpqcPrecoverage_iff`: a family is fpqc if and only if it is
  flat and every affine open of the target is the union of the images of finitely many affine
  opens of the sources — the definition of an fpqc covering.

## References

* [Stacks Project, Tag 022B](https://stacks.math.columbia.edu/tag/022B)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)

/-- **The fpqc coverings of a scheme.** A family `{f i : X i ⟶ T}` lies in Mathlib's fpqc
precoverage `Scheme.fpqcPrecoverage` if and only if it is an fpqc covering in the sense of the
source: every `f i` is flat, and every affine open `U` of `T` is the union of the images
`f (a j) '' V j` of finitely many affine opens `V j` of the `X (a j)`, `j : Fin n`.

Mathlib's precoverage also asks for the family to be jointly surjective; the source remarks right
after the definition that this follows from the covering condition, and the right-hand side here
does not ask for it. -/
@[stacks 022B "the fpqc coverings: Scheme.fpqcPrecoverage, with the definition's condition"]
public lemma ofArrows_mem_fpqcPrecoverage_iff :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T ↔
      ((∀ i, Flat (f i)) ∧
        ∀ U : T.Opens, IsAffineOpen U →
          ∃ (n : ℕ) (a : Fin n → I) (V : ∀ j, (X (a j)).Opens),
            (∀ j, IsAffineOpen (V j)) ∧
              ⋃ j, f (a j) '' (V j : Set (X (a j))) = (U : Set T)) := by
  rw [fpqc_mem_iff_flat_and_compactOpenCovered]
  refine and_congr_right fun _ ↦ forall_congr' fun U ↦ forall_congr' fun _ ↦ ⟨fun h ↦ ?_, ?_⟩
  · exact h.exists_mem_of_isBasis (fun i ↦ (X i).isBasis_affineOpens)
      (fun _ _ hV ↦ hV.isCompact)
  · rintro ⟨n, a, V, hV, hU⟩
    exact IsCompactOpenCovered.of_finite a V (fun j ↦ (hV j).isCompact) hU

end AlgebraicGeometry
