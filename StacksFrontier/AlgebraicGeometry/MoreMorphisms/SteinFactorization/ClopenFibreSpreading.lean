module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Flatness.IsolatedPointsDecomposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian

/-!
# Spreading a clopen decomposition of a fibre of a proper morphism

Let `f : X ⟶ S` be a proper morphism of schemes with `S` locally Noetherian, let `s ∈ S`, and
let the fibre `f ⁻¹' {s}` be split by two closed subsets `P` and `Q` of `X` into two disjoint
pieces.  Then after an elementary étale base change `(U, u) ⟶ (S, s)` the split extends to an
open and closed subset `A` of `X ×_S U`, which meets the fibre over `u` exactly in the points
lying over `P`.

This is the topological content of the connectedness assertion of the Stein factorization for a
proper morphism over a locally Noetherian base, in the form in which it transports to a proper
cover of a proper algebraic space (Chow's lemma, Stacks 089J), where functions are not available.

## Main results

* `Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper`: the statement above.

## Implementation notes

The proof factors `f = π ∘ f'` through its Stein factorization ([Stacks, Tag 03H0]).  The first
factor `f'` has connected fibres, so each fibre of `f'` above a point of `π ⁻¹' {s}` lies in `P`
or in `Q`; and `π` is finite, so `π ⁻¹' {s}` is a finite discrete set of points.  An elementary
étale neighbourhood of `s` splitting all of them off into open and closed pieces of the base
change of `π` ([Stacks, Tag 02LN]) gives the clopen set downstairs; `A` is its preimage.

## References

* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}}

/-- Every point of the target of an isomorphism `∐ R ⟶ W` comes from one of the summands. -/
lemma exists_apply_eq_of_isIso_sigmaDesc {ι : Type} {R : ι → Scheme.{u}} {W : Scheme.{u}}
    (j : ∀ a, R a ⟶ W) [IsIso (Sigma.desc j)] (w : W) : ∃ a y, j a y = w := by
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (Sigma.desc j).base).2 w
  obtain ⟨⟨a⟩, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (Discrete.functor R) y
  refine ⟨a, y, ?_⟩
  change (Sigma.desc j) ((Sigma.ι R a) y) = _ at hy
  rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]

/-- If `∐ R ⟶ W` is an isomorphism, points of distinct summands have distinct images. -/
lemma eq_of_apply_eq_of_isIso_sigmaDesc {ι : Type} {R : ι → Scheme.{u}} {W : Scheme.{u}}
    (j : ∀ a, R a ⟶ W) [IsIso (Sigma.desc j)] {b c : ι} (p : R b) (q : R c)
    (hpq : j b p = j c q) : b = c := by
  have : (Sigma.ι R b ≫ Sigma.desc j) p = (Sigma.ι R c ≫ Sigma.desc j) q := by
    simpa only [Sigma.ι_comp_desc] using hpq
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
  exact congrArg Sigma.fst ((sigmaι_eq_iff R b c p q).mp
    ((ConcreteCategory.bijective_of_isIso (Sigma.desc j).base).1 this))

/-- If `∐ R ⟶ W` is an isomorphism, the image of a point of the summand `a` lies in the union of
the images of the summands indexed by `I` exactly when `a ∈ I`. -/
lemma apply_mem_biUnion_range_iff_of_isIso_sigmaDesc {ι : Type} {R : ι → Scheme.{u}}
    {W : Scheme.{u}} (j : ∀ a, R a ⟶ W) [IsIso (Sigma.desc j)] (I : Set ι) {a : ι} (y : R a) :
    j a y ∈ ⋃ b ∈ I, Set.range (j b).base ↔ a ∈ I := by
  simp only [Set.mem_iUnion, Set.mem_range]
  refine ⟨fun ⟨b, hb, q, hq⟩ => ?_, fun ha => ⟨a, ha, y, rfl⟩⟩
  obtain rfl := eq_of_apply_eq_of_isIso_sigmaDesc j q y hq
  exact hb

/-- Each fibre of the first Stein factor of a proper `f` over a point above `s` lies in `P` or
in `Q`, when the closed sets `P` and `Q` cover `f ⁻¹' {s}` and do not meet inside it. -/
lemma preimage_toNormalization_subset_or_subset (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S]
    {s : S} {P Q : Set X} (hP : IsClosed P) (hQ : IsClosed Q) (hcover : f ⁻¹' {s} ⊆ P ∪ Q)
    (hdisj : f ⁻¹' {s} ∩ (P ∩ Q) = ∅) {y : f.normalization} (hy : f.fromNormalization y = s) :
    f.toNormalization ⁻¹' {y} ⊆ P ∨ f.toNormalization ⁻¹' {y} ⊆ Q := by
  have : GeometricallyConnected f.toNormalization :=
    geometricallyConnected_toNormalization_of_isProper f
  have hsub : f.toNormalization ⁻¹' {y} ⊆ f ⁻¹' {s} := by
    intro z hz
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
    change f z = s
    rw [← toNormalization_fromNormalization f, Scheme.Hom.comp_apply, hz, hy]
  exact isPreconnected_iff_subset_of_disjoint_closed.mp
    (f.toNormalization.isConnected_preimage_singleton y).isPreconnected P Q hP hQ
    (hsub.trans hcover)
    (Set.eq_empty_of_subset_empty ((Set.inter_subset_inter_left _ hsub).trans hdisj.subset))

/-- **A clopen decomposition of a fibre of a proper morphism spreads out étale locally.**  Let
`f : X ⟶ S` be proper with `S` locally Noetherian, let `s ∈ S`, and let `P` and `Q` be closed
subsets of `X` which cover the fibre `f ⁻¹' {s}` and do not meet inside it.  Then there are an
elementary étale neighbourhood `(U, u)` of `s` and an open and closed subset `A` of `X ×_S U`
such that a point `z` over `u` lies in `A` exactly when its image in `X` lies in `P`. -/
theorem exists_etaleNeighborhood_isClopen_of_isProper (f : X ⟶ S) [IsProper f]
    [IsLocallyNoetherian S] (s : S) (P Q : Set X) (hP : IsClosed P) (hQ : IsClosed Q)
    (hcover : f ⁻¹' {s} ⊆ P ∪ Q) (hdisj : f ⁻¹' {s} ∩ (P ∩ Q) = ∅) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (_ : U.IsElementary)
      (A : Set (pullback f U.toBase : Scheme.{u})), IsClopen A ∧
        ∀ z : (pullback f U.toBase : Scheme.{u}), pullback.snd f U.toBase z = U.point →
          (z ∈ A ↔ pullback.fst f U.toBase z ∈ P) := by
  classical
  let g := f.toNormalization
  let π := f.fromNormalization
  have hgπ : g ≫ π = f := toNormalization_fromNormalization f
  have : IsFinite π := isFinite_fromNormalization f
  obtain ⟨n, x, hxinj, hxr⟩ := (π.finite_preimage_singleton s).fin_param
  have hx : ∀ i, π (x i) = s := fun i => hxr.subset (Set.mem_range_self i)
  obtain ⟨U, hU, R, j, hjo, hjc, hiso, v, hfin, hjx, hjv, -, hnone⟩ :=
    Stacks.Flatness.exists_etaleNeighborhood_decomposition π s _ x hx hxinj fun i =>
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (π.quasiFiniteAt (x i))
  let I₁ : Set (Option (Fin n)) := some '' {i | g ⁻¹' {x i} ⊆ P}
  let Z : Set (pullback π U.toBase : Scheme.{u}) := ⋃ a ∈ I₁, Set.range (j a).base
  have hZ : IsClopen Z := Set.Finite.isClopen_biUnion (Set.toFinite _) fun a _ =>
    ⟨(j a).isClosedEmbedding.isClosed_range, (j a).isOpenEmbedding.isOpen_range⟩
  let ψ : pullback f U.toBase ⟶ pullback π U.toBase :=
    pullback.map f U.toBase π U.toBase g (𝟙 _) (𝟙 _) (by simp [hgπ]) (by simp)
  have hψfst : ∀ z, pullback.fst π U.toBase (ψ z) = g (pullback.fst f U.toBase z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have hψsnd : ∀ z, pullback.snd π U.toBase (ψ z) = pullback.snd f U.toBase z := fun z => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id]
  refine ⟨U, hU, ψ ⁻¹' Z, hZ.preimage ψ.continuous, fun z hz => ?_⟩
  have hfz : f (pullback.fst f U.toBase z) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz, U.map_point]
  obtain ⟨a, y, hy⟩ := exists_apply_eq_of_isIso_sigmaDesc j (ψ z)
  have hyu : (j a ≫ pullback.snd π U.toBase) y = U.point := by
    rw [Scheme.Hom.comp_apply, hy, hψsnd, hz]
  cases a with
  | none =>
    obtain ⟨k, hk⟩ : g (pullback.fst f U.toBase z) ∈ Set.range x := hxr.superset <| by
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, hgπ, hfz]
    exact absurd (by rw [Scheme.Hom.comp_apply, hy, hψfst, hk]) (hnone y hyu k)
  | some i =>
    obtain rfl : y = v i := (Set.ext_iff.mp (hjv i) y).mp hyu
    have hzi : pullback.fst f U.toBase z ∈ g ⁻¹' {x i} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← hψfst, ← hy, ← Scheme.Hom.comp_apply]
      exact hjx i
    rw [Set.mem_preimage, ← hy]
    refine (apply_mem_biUnion_range_iff_of_isIso_sigmaDesc j I₁ _).trans ?_
    rw [(Option.some_injective _).mem_set_image, Set.mem_ofPred_eq]
    refine ⟨fun hsub => hsub hzi, fun hPz => ?_⟩
    rcases preimage_toNormalization_subset_or_subset f hP hQ hcover hdisj (hx i) with h | h
    · exact h
    · have : pullback.fst f U.toBase z ∈ f ⁻¹' {s} ∩ (P ∩ Q) := ⟨hfz, hPz, h hzi⟩
      exact (hdisj.subset this).elim

end Stacks.SteinFactorization

end
