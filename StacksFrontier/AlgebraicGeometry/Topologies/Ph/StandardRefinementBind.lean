module

public import StacksFrontier.AlgebraicGeometry.Topologies.StandardPhRefinement

/-!
# Composites of standard ph coverings

A standard ph covering of an affine scheme `T`, `AlgebraicGeometry.StandardPHCovering`, is the
family obtained by restricting a proper surjective morphism `g : U ⟶ T` to the members of a
finite affine open covering of `U`.

Stacks 0DBF part (2) asserts that the family of all composites
`{W_{ji} ⟶ U_j ⟶ T}` of two successive standard ph coverings is refined by a standard ph
covering. This file proves the two cases of that assertion which need no compactification of
`W_j` over `U`, namely the ones in which the presenting proper surjection of the composite can
be written down directly:

* the second stage is a Zariski covering, so that the two presentations share the scheme `U`;
* the first stage is presented by a proper surjection from an *affine* scheme, so that the two
  presenting proper surjections compose.

## Main results

* `AlgebraicGeometry.StandardPHCovering.of_comp_presentation`: a finite affine open covering of
  the source of a composite of two proper surjections onto an affine scheme is a standard ph
  covering.
* `AlgebraicGeometry.StandardPHCovering.comp`: a standard ph covering of an affine scheme `U`,
  composed with a proper surjection `U ⟶ T` onto an affine scheme, is a standard ph covering
  of `T`.
* `AlgebraicGeometry.StandardPHCovering.bind`: refining each member of a standard ph covering
  by a finite affine open covering of it gives a standard ph covering.

## Implementation notes

Families of morphisms with fixed target are `CategoryTheory.PreZeroHypercover`, and the family
of all composites of a family over the members of another family is
`CategoryTheory.PreZeroHypercover.bind`.

The general case of Stacks 0DBF part (2) is *not* proved here. The Stacks argument replaces the
proper surjection `W_j ⟶ U_j` presenting the second stage over the affine open `U_j ⊆ U` by its
scheme-theoretic closure in `ℙ^{e_j}_U`, which is proper over the whole of `U`, and that
replacement rests on Chow's lemma (Stacks 0202) over the arbitrary affine base `U_j`. See
`AlgebraicGeometry.HasChowModification` in
`StacksFrontier.AlgebraicGeometry.Limits.ChowLemma` for the state of that input.

## References

* [Stacks Project, Tag 0DBD](https://stacks.math.columbia.edu/tag/0DBD)
* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- A finite affine open covering of the source of a *composite* of two proper surjections
`W ⟶ U ⟶ T` with `T` affine is a standard ph covering of `T`. The intermediate scheme `U` is
arbitrary.

This is the last step of Stacks 0DBF part (2) and of the proof of Stacks 0ETR. -/
theorem StandardPHCovering.of_comp_presentation {ι : Type v} {T U W : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ T) [Finite ι] (hX : ∀ i, IsAffine (X i)) {p : U ⟶ T}
    {q : W ⟶ U} (k : ∀ i, X i ⟶ W) (hp : IsProper p) (hp' : Surjective p) (hq : IsProper q)
    (hq' : Surjective q) (hk : ∀ i, IsOpenImmersion (k i))
    (hcover : (⋃ i, Set.range (k i)) = Set.univ) (hcomp : ∀ i, k i ≫ q ≫ p = f i) :
    StandardPHCovering f := by
  have : IsProper p := hp
  have : IsProper q := hq
  have : Surjective p := hp'
  have : Surjective q := hq'
  exact StandardPHCovering.of_presentation f hX (q ≫ p) k inferInstance inferInstance hk hcover
    fun i ↦ (Category.assoc _ _ _).trans (hcomp i)

/-- A standard ph covering of an affine scheme `U` composed with a proper surjection
`p : U ⟶ T` onto an affine scheme is a standard ph covering of `T`.

This is the case of Stacks 0DBF part (2) in which the first of the two standard ph coverings
is presented by a proper surjection from an affine scheme. -/
theorem StandardPHCovering.comp {ι : Type v} {T U : Scheme.{u}} [IsAffine T] [IsAffine U]
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ U} (hf : StandardPHCovering f) {p : U ⟶ T}
    (hp : IsProper p) (hp' : Surjective p) :
    StandardPHCovering fun i ↦ f i ≫ p := by
  have : Finite ι := hf.finite
  obtain ⟨W, q, k, hq, hq', hk, hcover, hcomp⟩ := hf.exists_presentation
  exact StandardPHCovering.of_comp_presentation _ (fun i ↦ hf.isAffine i) k hp hp' hq hq' hk
    hcover fun i ↦ by rw [← Category.assoc, hcomp i]

/-- Refining every member of a standard ph covering of an affine scheme by a finite affine open
covering of that member gives again a standard ph covering.

This is the case of Stacks 0DBF part (2) in which the second of the two standard ph coverings
is a Zariski covering. -/
theorem StandardPHCovering.bind {T : Scheme.{u}} [IsAffine T] {E : PreZeroHypercover.{v} T}
    (hE : StandardPHCovering E.f) (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hFfinite : ∀ i, Finite (F i).I₀) (hFaffine : ∀ i a, IsAffine ((F i).X a))
    (hFopen : ∀ i a, IsOpenImmersion ((F i).f a))
    (hFcover : ∀ i, (⋃ a, Set.range ((F i).f a)) = Set.univ) :
    StandardPHCovering (E.bind F).f := by
  have : Finite E.I₀ := hE.finite
  have : ∀ i, Finite (F i).I₀ := hFfinite
  change StandardPHCovering fun s : Σ i, (F i).I₀ ↦ (F s.1).f s.2 ≫ E.f s.1
  obtain ⟨U, g, j, hg, hg', hj, hcover, hcomp⟩ := hE.exists_presentation
  refine StandardPHCovering.of_presentation _ (fun s ↦ hFaffine s.1 s.2) g
    (fun s ↦ (F s.1).f s.2 ≫ j s.1) hg hg' (fun s ↦ ?_) ?_ fun s ↦ ?_
  · have := hFopen s.1 s.2
    have := hj s.1
    infer_instance
  · refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
    obtain ⟨a, z, rfl⟩ := Set.mem_iUnion.mp (hFcover i ▸ Set.mem_univ y)
    exact Set.mem_iUnion.mpr ⟨⟨i, a⟩, z, Scheme.Hom.comp_apply _ _ _⟩
  · rw [Category.assoc, hcomp s.1]

end AlgebraicGeometry

end
