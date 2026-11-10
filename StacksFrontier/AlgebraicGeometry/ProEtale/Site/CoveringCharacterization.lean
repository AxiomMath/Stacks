module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
public import StacksCore.Tactic.StacksAttribute

/-!
# Recognizing pro-étale coverings

A family of morphisms of schemes is a pro-étale covering precisely when every member is
weakly étale and the family is an fpqc covering.  Since a weakly étale morphism is flat, this
reduces every recognition criterion for pro-étale coverings to the corresponding criterion for
fpqc coverings: a weakly étale family is a pro-étale covering as soon as every affine open of
the target is the union of the images of an almost-everywhere empty family of quasi-compact
opens, and it is enough to exhibit such finite families over the members of a single affine
open covering, or, for a quasi-separated target, pointwise neighbourhoods.

## Main results

* `AlgebraicGeometry.mem_proetalePrecoverage_iff_weaklyEtale_and_mem_fpqcPrecoverage`: the
  equivalence of conditions (1) and (2).
* `AlgebraicGeometry.mem_proetalePrecoverage_iff_affine_finite_support`: the equivalence of
  conditions (1) and (3).
* `AlgebraicGeometry.mem_proetalePrecoverage_iff_exists_affine_open_cover`: the equivalence of
  conditions (1) and (4).
* `AlgebraicGeometry.mem_proetalePrecoverage_iff_pointwise_compact_open_neighborhood`: the
  equivalence of conditions (1) and (5) for a quasi-separated target.

## Implementation notes

Being a pro-étale covering is membership of the family's presieve in
`AlgebraicGeometry.Scheme.proetalePrecoverage`, which is by definition the intersection of the
quasi-compact precoverage with the precoverage of jointly surjective weakly étale families;
being an fpqc covering is the same intersection taken with flat in place of weakly étale.  This
is what makes the equivalence of conditions (1) and (2) a matter of unfolding, after which the
remaining conditions are those of Stacks 03L7 with weakly étale in place of flat.  Their
numbering is shifted by one, because the fpqc lemma has no analogue of condition (2): conditions
(3), (4) and (5) below are conditions (2), (3) and (4) there.

An almost-everywhere empty family in condition (3) is expressed by finiteness of the set of
indices at which its open is nonempty, and the finite families of conditions (4) and (5) are
indexed by `Fin n`; that a possibly non-open image is a neighbourhood is expressed by membership
in the neighbourhood filter.

## References

* [Stacks Project, Tag 098A](https://stacks.math.columbia.edu/tag/098A)
* [Stacks Project, Tag 03L7](https://stacks.math.columbia.edu/tag/03L7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)

private lemma mem_propQCPrecoverage_ofArrows_iff (P : MorphismProperty Scheme.{u}) :
    Presieve.ofArrows X f ∈ Scheme.propQCPrecoverage P T ↔
      (Presieve.ofArrows X f ∈ Scheme.qcPrecoverage T ∧
        ((∀ x : T, ∃ i, x ∈ Set.range (f i)) ∧ ∀ i, P (f i))) := by
  change (Presieve.ofArrows X f ∈ Scheme.qcPrecoverage T ∧
    Presieve.ofArrows X f ∈ Scheme.precoverage P T) ↔ _
  rw [Scheme.ofArrows_mem_precoverage_iff]

/-- Weakly étale members are flat, so flatness may be dropped from a conjunction with them. -/
private lemma weaklyEtale_and_flat_and_iff {Q : Prop} :
    ((∀ i, WeaklyEtale (f i)) ∧ (∀ i, Flat (f i)) ∧ Q) ↔ ((∀ i, WeaklyEtale (f i)) ∧ Q) :=
  ⟨fun ⟨hwe, _, hQ⟩ => ⟨hwe, hQ⟩, fun ⟨hwe, hQ⟩ => ⟨hwe, fun i => (hwe i).flat, hQ⟩⟩

/-- **Stacks 098A, conditions (1) and (2).** A family is a pro-étale covering if and only if
every member is weakly étale and the family is an fpqc covering. -/
@[stacks 098A "conditions (1) and (2)"]
public lemma mem_proetalePrecoverage_iff_weaklyEtale_and_mem_fpqcPrecoverage :
    Presieve.ofArrows X f ∈ Scheme.proetalePrecoverage T ↔
      ((∀ i, WeaklyEtale (f i)) ∧ Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T) := by
  refine (mem_propQCPrecoverage_ofArrows_iff f @WeaklyEtale).trans <|
    Iff.trans ?_ (and_congr_right' (mem_propQCPrecoverage_ofArrows_iff f @Flat).symm)
  exact ⟨fun ⟨hqc, hsurj, hwe⟩ => ⟨hwe, hqc, hsurj, fun i => (hwe i).flat⟩,
    fun ⟨hwe, hqc, hsurj, _⟩ => ⟨hqc, hsurj, hwe⟩⟩

/-- **Stacks 098A, conditions (1) and (3).** A family is a pro-étale covering if and only if
every member is weakly étale and every affine open of the target is the union of the images of
quasi-compact opens in the sources, all but finitely many of which are empty. -/
@[stacks 098A "conditions (1) and (3)"]
public lemma mem_proetalePrecoverage_iff_affine_finite_support :
    Presieve.ofArrows X f ∈ Scheme.proetalePrecoverage T ↔
      ((∀ i, WeaklyEtale (f i)) ∧
        (∀ U : T.Opens, IsAffineOpen U →
            ∃ V : ∀ i, (X i).Opens,
              ((∀ i, IsCompact (V i : Set (X i))) ∧
                ({i | V i ≠ ⊥} : Set I).Finite ∧
                ⋃ i, f i '' (V i : Set (X i)) = (U : Set T)))) := by
  rw [mem_proetalePrecoverage_iff_weaklyEtale_and_mem_fpqcPrecoverage,
    mem_fpqcPrecoverage_iff_affine_finite_support]
  exact weaklyEtale_and_flat_and_iff f

/-- **Stacks 098A, conditions (1) and (4).** A family is a pro-étale covering if and only if
its members are weakly étale and some affine open covering of the target is, member by member,
the union of images of finitely many quasi-compact opens in the sources. -/
@[stacks 098A "conditions (1) and (4)"]
public lemma mem_proetalePrecoverage_iff_exists_affine_open_cover :
    Presieve.ofArrows X f ∈ Scheme.proetalePrecoverage T ↔
      ((∀ i, WeaklyEtale (f i)) ∧
        ∃ (A : Type u) (U : A → T.Opens),
          ((∀ a, IsAffineOpen (U a)) ∧
            (⋃ a, (U a : Set T)) = Set.univ ∧
            ∀ a, ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (X (i j)).Opens),
              ((∀ j, IsCompact (V j : Set (X (i j)))) ∧
                ⋃ j, f (i j) '' (V j : Set (X (i j))) = (U a : Set T)))) := by
  rw [mem_proetalePrecoverage_iff_weaklyEtale_and_mem_fpqcPrecoverage,
    mem_fpqcPrecoverage_iff_exists_affine_open_cover]
  exact weaklyEtale_and_flat_and_iff f

/-- **Stacks 098A, conditions (1) and (5).** If the target is quasi-separated, a family is a
pro-étale covering if and only if its members are weakly étale and every point has a
neighbourhood which is the union of the images of finitely many quasi-compact opens in the
sources. The neighbourhood itself is not required to be open. -/
@[stacks 098A "conditions (1) and (5)"]
public lemma mem_proetalePrecoverage_iff_pointwise_compact_open_neighborhood
    [QuasiSeparatedSpace T] :
    Presieve.ofArrows X f ∈ Scheme.proetalePrecoverage T ↔
      ((∀ i, WeaklyEtale (f i)) ∧
        ∀ t : T, ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (X (i j)).Opens),
          ((∀ j, IsCompact (V j : Set (X (i j)))) ∧
            (⋃ j, f (i j) '' (V j : Set (X (i j)))) ∈ nhds t)) := by
  rw [mem_proetalePrecoverage_iff_weaklyEtale_and_mem_fpqcPrecoverage,
    mem_fpqcPrecoverage_iff_pointwise_compact_open_neighborhood]
  exact weaklyEtale_and_flat_and_iff f

end AlgebraicGeometry
