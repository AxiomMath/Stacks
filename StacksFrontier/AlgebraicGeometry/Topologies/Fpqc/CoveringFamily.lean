module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
public import StacksFrontier.CategoryTheory.Sites.Representable.EffectiveEpiFamily
import all StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization

/-!
# Fpqc coverings in the sense of Stacks 022B

Stacks 022B calls a family `{f i : X i ⟶ T}` an fpqc covering when every member is flat and
every affine open of `T` is the union of the images of finitely many affine opens of the
sources; this is `IsFpqcCoveringFamily`.  We identify it with membership in Mathlib's
`Scheme.fpqcPrecoverage`, whose quasi-compactness condition uses quasi-compact opens in place
of affine ones, and then state Stacks 03L7 with the 022B notion as condition (1).

## Main results

* `AlgebraicGeometry.ofArrows_mem_fpqcPrecoverage_iff_isFpqcCoveringFamily`: a family lies in
  `Scheme.fpqcPrecoverage` if and only if it is an fpqc covering in the sense of Stacks 022B.
* `AlgebraicGeometry.isFpqcCoveringFamily_iff_affine_finite_support`: a family is an fpqc
  covering if and only if it is flat and every affine open of the target is the union of the
  images of quasi-compact opens, all but finitely many of them empty.
* `AlgebraicGeometry.isFpqcCoveringFamily_iff_exists_affine_open_cover`: the same with finitely
  many quasi-compact opens over each member of some affine open covering of the target.
* `AlgebraicGeometry.isFpqcCoveringFamily_iff_pointwise_compact_open_neighborhood`: for a
  quasi-separated target, the same with a neighbourhood of every point in place of an affine
  open.

## References

* [Stacks Project, Tag 022B](https://stacks.math.columbia.edu/tag/022B)
* [Stacks Project, Tag 03L7](https://stacks.math.columbia.edu/tag/03L7)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)

/-- A family lies in Mathlib's `Scheme.fpqcPrecoverage` if and only if it is an fpqc covering
in the sense of Stacks 022B: every member is flat and every affine open of the target is the
union of the images of finitely many affine opens of the sources.  Mathlib's quasi-compactness
condition asks for quasi-compact opens instead of affine ones; a quasi-compact open is a finite
union of affine opens, and an affine open is quasi-compact. -/
@[stacks 03L7 "(1)", stacks 022B "identification with Mathlib's `Scheme.fpqcPrecoverage`"]
public lemma ofArrows_mem_fpqcPrecoverage_iff_isFpqcCoveringFamily :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T ↔ IsFpqcCoveringFamily X f := by
  rw [fpqc_mem_iff_flat_and_compactOpenCovered]
  constructor
  · rintro ⟨hflat, hcov⟩
    refine ⟨hflat, fun U hU => ?_⟩
    obtain ⟨n, a, V, hV, hEq⟩ :=
      (hcov U hU).exists_mem_of_isBasis (fun j => (X j).isBasis_affineOpens)
        (fun j W hW => hW.isCompact)
    exact ⟨n, a, V, hV, hEq⟩
  · rintro ⟨hflat, hcov⟩
    refine ⟨hflat, fun U hU => ?_⟩
    obtain ⟨n, a, V, hV, hEq⟩ := hcov U hU
    exact IsCompactOpenCovered.of_finite a V (fun j => (hV j).isCompact) hEq

/-- A family is an fpqc covering (Stacks 022B) if and only if every member is flat and every
affine open of the target is the union of the images of quasi-compact opens in the sources,
all but finitely many of which are empty. -/
@[stacks 03L7 "conditions (1) and (2)"]
public lemma isFpqcCoveringFamily_iff_affine_finite_support :
    IsFpqcCoveringFamily X f ↔
      ((∀ i, Flat (f i)) ∧
        (∀ U : T.Opens, IsAffineOpen U →
            ∃ V : ∀ i, (X i).Opens,
              ((∀ i, IsCompact (V i : Set (X i))) ∧
                ({i | V i ≠ ⊥} : Set I).Finite ∧
                ⋃ i, f i '' (V i : Set (X i)) = (U : Set T)))) :=
  (ofArrows_mem_fpqcPrecoverage_iff_isFpqcCoveringFamily f).symm.trans
    (mem_fpqcPrecoverage_iff_affine_finite_support f)

/-- A family is an fpqc covering (Stacks 022B) if and only if its members are flat and some
affine open covering of the target is, member by member, the union of images of finitely many
quasi-compact opens in the sources. -/
@[stacks 03L7 "conditions (1) and (3)"]
public lemma isFpqcCoveringFamily_iff_exists_affine_open_cover :
    IsFpqcCoveringFamily X f ↔
      ((∀ i, Flat (f i)) ∧
        ∃ (A : Type u) (U : A → T.Opens),
          ((∀ a, IsAffineOpen (U a)) ∧
            (⋃ a, (U a : Set T)) = Set.univ ∧
            ∀ a, ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (X (i j)).Opens),
              ((∀ j, IsCompact (V j : Set (X (i j)))) ∧
                ⋃ j, f (i j) '' (V j : Set (X (i j))) = (U a : Set T)))) :=
  (ofArrows_mem_fpqcPrecoverage_iff_isFpqcCoveringFamily f).symm.trans
    (mem_fpqcPrecoverage_iff_exists_affine_open_cover f)

/-- If the target is quasi-separated, a family is an fpqc covering (Stacks 022B) if and only
if its members are flat and every point has a neighborhood which is the union of the images of
finitely many quasi-compact opens in the sources. The neighborhood itself is not required to be
open. -/
@[stacks 03L7 "conditions (1) and (4)"]
public lemma isFpqcCoveringFamily_iff_pointwise_compact_open_neighborhood
    [QuasiSeparatedSpace T] :
    IsFpqcCoveringFamily X f ↔
      ((∀ i, Flat (f i)) ∧
        ∀ t : T, ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (X (i j)).Opens),
          ((∀ j, IsCompact (V j : Set (X (i j)))) ∧
            (⋃ j, f (i j) '' (V j : Set (X (i j)))) ∈ nhds t)) :=
  (ofArrows_mem_fpqcPrecoverage_iff_isFpqcCoveringFamily f).symm.trans
    (mem_fpqcPrecoverage_iff_pointwise_compact_open_neighborhood f)

end AlgebraicGeometry
