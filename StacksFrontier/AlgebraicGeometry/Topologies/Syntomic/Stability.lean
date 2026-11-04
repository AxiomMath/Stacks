module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings

/-!
# Syntomic coverings satisfy the site axioms

A singleton family consisting of an isomorphism is a syntomic covering; refining every member
of a syntomic covering by a syntomic covering gives a syntomic covering; and a syntomic covering
pulls back along an arbitrary morphism to a syntomic covering. These are the three axioms a
class of covering families has to satisfy to present a topology, so the syntomic coverings
present the syntomic topology.

## Main results

* `AlgebraicGeometry.isSyntomicCovering_singleton_of_isIso` — the singleton family of an
  isomorphism.
* `AlgebraicGeometry.IsSyntomicCovering.comp` — composition with syntomic coverings of all the
  members.
* `AlgebraicGeometry.isSyntomicCovering_pullback` — stability under arbitrary base change.

## Implementation notes

The singleton family is indexed by `Unit` and a composite family by the dependent sum of its
two indexing types, so none of the three statements needs a precoverage: each is a direct
assertion about an indexed family, matching the shape of `IsSyntomicCovering`.

The base-changed family uses the categorical pullback, with its second projection as the
structure morphism to the new target; joint surjectivity of the result is the surjectivity of a
fibre product of schemes onto the factor whose own map is surjective, which is
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

## References

* [Stacks Project, Tag 0227](https://stacks.math.columbia.edu/tag/0227)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0227, part (1).** An isomorphism, regarded as a singleton family, is
a syntomic covering. -/
@[stacks 0227 "part (1)"]
public lemma isSyntomicCovering_singleton_of_isIso {T' T : Scheme.{u}}
    (f : T' ⟶ T) [IsIso f] :
    IsSyntomicCovering (fun _ : Unit ↦ T') (fun _ ↦ f) := by
  refine ⟨fun _ => syntomic_of_isOpenImmersion f,
    Set.eq_univ_iff_forall.mpr fun t => ?_⟩
  exact Set.mem_iUnion.mpr ⟨(), Set.mem_range.mpr
    ⟨inv f t, congrArg (fun k : T ⟶ T => k t) (IsIso.inv_hom_id f)⟩⟩

/-- **Stacks Project, Tag 0227, part (2).** Refining every member of a syntomic covering by a
syntomic covering gives another syntomic covering. -/
@[stacks 0227 "part (2)"]
public lemma IsSyntomicCovering.comp {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : IsSyntomicCovering X f) {J : I → Type w}
    (Y : ∀ i, J i → Scheme.{u}) (g : ∀ i j, Y i j ⟶ X i)
    (hg : ∀ i, IsSyntomicCovering (Y i) (g i)) :
    IsSyntomicCovering
      (fun ij : Σ i, J i ↦ Y ij.1 ij.2)
      (fun ij ↦ g ij.1 ij.2 ≫ f ij.1) := by
  refine ⟨fun ij => MorphismProperty.comp_mem _ _ _ ((hg ij.1).1 ij.2) (hf.1 ij.1),
    Set.eq_univ_iff_forall.mpr fun t => ?_⟩
  obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hf.2 t)
  obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp (hg i).2 x)
  exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, Set.mem_range.mpr ⟨y, by simp [hy, hx]⟩⟩

/-- **Stacks Project, Tag 0227, part (3).** Pulling a syntomic covering back along an arbitrary
morphism gives a syntomic covering. -/
@[stacks 0227 "part (3)"]
public lemma isSyntomicCovering_pullback {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) {T' : Scheme.{u}}
    (g : T' ⟶ T) (hf : IsSyntomicCovering X f) :
    IsSyntomicCovering
      (fun i ↦ pullback (f i) g)
      (fun i ↦ pullback.snd (f i) g) := by
  refine ⟨fun i => syntomic_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (f i) g) (hf.1 i), Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hf.2 (g x))
  obtain ⟨z, _, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f i) (g := g) y x hy
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨z, hzsnd⟩⟩

end AlgebraicGeometry
