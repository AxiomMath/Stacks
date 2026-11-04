module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper

/-!
# A proper open subscheme of a finite scheme over a field has strictly smaller degree

Let `p : A ⟶ Spec k` be a finite morphism to the spectrum of a field and let `i : B ⟶ A` be an
open immersion, with `p` of degree `r` and `i ≫ p` of degree `s`. Then `s ≤ r`, which is
`AlgebraicGeometry.finite_open_rank_le_of_field`, and the inequality is **strict as soon as `i`
misses a point of `A`**.

This is the degree bookkeeping of the inductive step of [Stacks, Tag 09YB]. There the fibre of
an étale chart over a geometric point of the relative compactification splits off the point
provided by the graph of the open immersion, and the complementary piece must be shown to have
degree strictly below the degree of the chart in order to feed the induction on that degree. The
splitting itself contributes nothing beyond a point of the fibre not in the complementary piece,
so what is needed is exactly strict monotonicity of the degree under passing to an open
subscheme which omits a point — not additivity of the degree across the splitting.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isIso_of_isOpenImmersion_of_field_rank_eq`: an open immersion into a finite
  scheme over a field whose degree does not drop is an isomorphism.
* `AlgebraicGeometry.finite_open_rank_lt_of_field`: **the strict degree drop.** An open immersion
  into a finite scheme over a field which omits a point has strictly smaller degree.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion`: the same statement
  with the degree of the open subscheme produced rather than supplied, matching the shape of
  `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion`.

## Implementation notes

The argument is the one already used for the non-strict bound, pushed one step. A finite scheme
over a field is discrete, so the open immersion `i` is also a closed immersion and therefore
induces a *surjection* `Γ(A, ⊤) ⟶ Γ(B, ⊤)` of `k`-algebras; the degrees being the dimensions of
those algebras, `s ≤ r` follows. If moreover `s = r`, a surjection between `k`-vector spaces of
equal finite dimension is injective, so `i` induces an isomorphism on global sections of affine
schemes and is itself an isomorphism — whence surjective on points, contradicting the omitted
point.

`AlgebraicGeometry.isIso_of_isOpenImmersion_of_field_rank_eq` re-derives, for an open immersion,
a lemma which is `private` in
`StacksFrontier/AlgebraicGeometry/Morphisms/FibreDimension/DegreeStratification.lean` for a closed
immersion; under the Lean module system a `private` declaration may not occur in the exposed body
of a public one, so it is restated here rather than reused. No existing declaration is touched.

## What is and is not proved

Nothing here carries a Stacks attribute. No statement is made about *additivity* of the degree
across a decomposition of the source: only the strict drop under an open immersion omitting a
point, which is what the degree induction of [Stacks, Tag 09YB] consumes.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- **An open immersion into a finite scheme over a field whose degree does not drop is an
isomorphism.** The ambient scheme is discrete, so the open immersion is also a closed immersion
and its map on global sections is surjective; the two degrees are the dimensions of those global
sections over the field, so equal degrees force that surjection to be injective, and a closed
immersion of affine schemes which is injective on global sections is an isomorphism. -/
theorem isIso_of_isOpenImmersion_of_field_rank_eq
    {k : Type u} [Field k] {A B : Scheme.{u}} (i : B ⟶ A)
    (p : A ⟶ Spec (.of k)) (r s : ℕ)
    [IsOpenImmersion i] [IsFinite p] [IsFinite (i ≫ p)]
    (hr : IsFiniteLocallyFreeOfRank p r)
    (hs : IsFiniteLocallyFreeOfRank (i ≫ p) s)
    (hrs : r = s) : IsIso i := by
  have : IsFiniteLocallyFreeOfRank p r := hr
  have : IsFiniteLocallyFreeOfRank (i ≫ p) s := hs
  have : IsAffine A := isAffine_of_isAffineHom p
  have : IsAffine B := isAffine_of_isAffineHom (i ≫ p)
  have : IsArtinianScheme A := {
    toIsLocallyArtinian := IsLocallyArtinian.of_locallyQuasiFinite p
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p
  }
  have : DiscreteTopology A :=
    IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mp inferInstance |>.2
  have : IsClosedImmersion i := .of_isPreimmersion i (isClosed_discrete _)
  let A0 := Γ(A, ⊤)
  let B0 := Γ(B, ⊤)
  let α : CommRingCat.of k ⟶ Γ(A, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  let β : CommRingCat.of k ⟶ Γ(B, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ p).appTop
  let : Algebra k A0 := α.hom.toAlgebra
  let : Algebra k B0 := β.hom.toAlgebra
  have hcomp : i.appTop.hom.comp α.hom = β.hom := by
    have hcat : α ≫ i.appTop = β := by
      dsimp [α, β]
      simp only [Category.assoc]
    exact congrArg CommRingCat.Hom.hom hcat
  let φ : A0 →ₐ[k] B0 := {
    toRingHom := i.appTop.hom
    commutes' := fun x => congrArg (fun q : k →+* B0 => q x) hcomp }
  have hdimA := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank (k := k) p r
  have hdimB := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank (k := k) (i ≫ p) s
  have : Module.Finite k A0 := hdimA.1
  have : Module.Finite k B0 := hdimB.1
  have heq : Module.finrank k A0 = Module.finrank k B0 := by
    rw [hdimA.2, hdimB.2, hrs]
  have hsurj : Function.Surjective φ.toLinearMap :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hinj : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hsurj
  exact IsClosedImmersion.isIso_of_injective_of_isAffine (f := i) fun _ _ h => hinj h

/-- **The strict degree drop.** An open immersion `i : B ⟶ A` into a scheme finite of degree `r`
over a field, with `i ≫ p` of degree `s`, satisfies `s < r` as soon as some point of `A` is not
in the image of `i`.

Were `s` not below `r`, the non-strict bound `AlgebraicGeometry.finite_open_rank_le_of_field`
would force `s = r`, and `AlgebraicGeometry.isIso_of_isOpenImmersion_of_field_rank_eq` would make
`i` an isomorphism, hence surjective on points. -/
theorem finite_open_rank_lt_of_field
    {k : Type u} [Field k] {A B : Scheme.{u}} (i : B ⟶ A)
    (p : A ⟶ Spec (.of k)) (r s : ℕ)
    [IsOpenImmersion i] [IsFinite p] [IsFinite (i ≫ p)]
    (hr : IsFiniteLocallyFreeOfRank p r)
    (hs : IsFiniteLocallyFreeOfRank (i ≫ p) s)
    (a : A) (ha : a ∉ Set.range i.base) : s < r := by
  refine (finite_open_rank_le_of_field i p r s hr hs).lt_of_ne fun hsr => ha ?_
  have := isIso_of_isOpenImmersion_of_field_rank_eq i p r s hr hs hsr.symm
  refine ⟨(inv i).base a, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

/-- **The strict degree drop, with the degree of the open subscheme produced.** For an open
immersion `ι : Z' ⟶ Z` into a scheme finite locally free of rank `r` over a field, which omits a
point of `Z`, the composite `ι ≫ p` is finite locally free of some rank strictly below `r`.

This is the shape of `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion`
with the strict conclusion. -/
theorem exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion
    {k : Type u} [Field k] {Z Z' : Scheme.{u}} (p : Z ⟶ Spec (.of k)) (ι : Z' ⟶ Z)
    [IsOpenImmersion ι] [IsFinite p] (r : ℕ)
    (hr : IsFiniteLocallyFreeOfRank p r)
    (z : Z) (hz : z ∉ Set.range ι.base) :
    ∃ r' : ℕ, r' < r ∧ IsFiniteLocallyFreeOfRank (ι ≫ p) r' := by
  have : IsFiniteLocallyFreeOfRank p r := hr
  obtain ⟨r', -, hr'⟩ := exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion p ι r
  have : IsFiniteLocallyFreeOfRank (ι ≫ p) r' := hr'
  have : IsFinite (ι ≫ p) := isFinite_of_isFiniteLocallyFreeOfRank (ι ≫ p) r'
  exact ⟨r', finite_open_rank_lt_of_field ι p r r' hr hr' z hz, hr'⟩

end AlgebraicGeometry

end
