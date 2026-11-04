module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFamilyCechProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDescentDatum
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineTripleOverlap

/-!
# The affine overlaps of a covering family of affine objects

Descent along a covering family `{g i : Y i ⟶ T}` of a slice of the fppf site associated with a
category fibred in groupoids consumes, besides the family itself, the double overlaps
`Pb i j = Y i ×_T Y j` and the triple overlaps `Pb₃ i j k = Y i ×_T Pb j k`, together with five
families of projections, a diagonal of each self-overlap, the two fibre product squares and the
three commutations identifying the three projections of a triple overlap onto the members.

This file produces all of that at once, and records that the overlaps of affine objects over an
affine object are again affine, so that the rings of global functions on them are available.  It
is the family analogue of
`AlgebraicGeometry.FibredSite.exists_affine_triple_self_product`, which is the same statement for
a one-element family, where the two overlaps are the double and the triple self-product of the
single covering morphism.

Everything is returned in one existential rather than in several, as there: the equations speak of
the same morphisms the earlier components return, and an existentially quantified morphism cannot
be handed to a separate statement.

## Main results

* `AlgebraicGeometry.FibredSite.exists_affine_family_overlaps`: **a covering family of affine
  objects of a slice over an affine object has affine double and triple overlaps**, with the five
  families of projections, the diagonals, the two fibre product squares and the three commutations
  a family descent datum consumes.

## Implementation notes

The double overlaps are the chosen fibre products of the pairs of members and the triple overlaps
the chosen fibre products of a member with a double overlap, which is the shape that makes the
ring of global functions on a triple overlap come out as `Bi i ⊗[A] D j k`, the tensor product of
the ring of the member with that of the double overlap.  The conclusions are nevertheless stated
through `CategoryTheory.IsPullback` squares rather than through the chosen fibre products, so that
a consumer never has to unfold the choice.

Affineness of the triple overlap is the pairwise statement
`AlgebraicGeometry.FibredSite.isAffineOver_of_isPullback` applied twice rather than
`AlgebraicGeometry.FibredSite.isAffineOver_of_isPullback₃`, whose outer square is taken over the
first projection of the inner one and so does not have the mixed indices of a family.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

include hS in
/-- **A covering family of affine objects of a slice of the associated fppf site over an affine
object has affine double and triple overlaps.**

The double overlap `Pb i j` is a fibre product of `g i` and `g j`, with projections `pr₁ i j` and
`pr₂ i j` and, on the diagonal, a section `δ i` of both projections of `Pb i i`.  The triple
overlap `Pb₃ i j k` is a fibre product of `g i` with the composite `pr₁ j k ≫ g j`, with a
projection `q i j k` onto `Y i` and a projection `t₂₃ i j k` onto `Pb j k`, and it carries two
further projections `t₁₂ i j k` onto `Pb i j` and `t₁₃ i j k` onto `Pb i k` whose composites with
the first projections are `q i j k` and whose composites with the second projections are the two
legs of `t₂₃ i j k`.  Both overlaps are affine.

The two projections onto the double overlaps and their four equations are
`CategoryTheory.IsPullback.exists_familyCechProjections`, the diagonals are
`CategoryTheory.IsPullback.exists_diagonal` at the self-overlaps, and the affineness is
`AlgebraicGeometry.FibredSite.isAffineOver_of_isPullback`.  Neither finiteness of the index type
nor any covering property of the family is used: these are statements about the fibre products of
the members and about affineness of a fibre product, both of which hold for an arbitrary family of
affine objects over an affine object. -/
theorem exists_affine_family_overlaps (hp : p.IsFiberedInGroupoids) {x : 𝒳} {T : Over x}
    {ι : Type*} (Y : ι → Over x) (g : ∀ i, Y i ⟶ T)
    (hT : IsAffineOver B S hS (p.obj T.left))
    (hY : ∀ i, IsAffineOver B S hS (p.obj (Y i).left)) :
    ∃ (Pb : ι → ι → Over x) (Pb₃ : ι → ι → ι → Over x)
      (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j) (δ : ∀ i, Y i ⟶ Pb i i)
      (q : ∀ i j k, Pb₃ i j k ⟶ Y i) (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
      (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k) (t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k),
      (∀ i j, IsAffineOver B S hS (p.obj (Pb i j).left)) ∧
      (∀ i j k, IsAffineOver B S hS (p.obj (Pb₃ i j k).left)) ∧
      (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j)) ∧
      (∀ i j k, IsPullback (q i j k) (t₂₃ i j k) (g i) (pr₁ j k ≫ g j)) ∧
      (∀ i, δ i ≫ pr₁ i i = 𝟙 (Y i)) ∧ (∀ i, δ i ≫ pr₂ i i = 𝟙 (Y i)) ∧
      (∀ i j k, t₁₂ i j k ≫ pr₁ i j = q i j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₁ i k = q i j k) ∧
      (∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k) := by
  have _ : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  have hpb : ∀ i j, IsPullback (pullback.fst (g i) (g j)) (pullback.snd (g i) (g j))
      (g i) (g j) := fun i j => IsPullback.of_hasPullback (g i) (g j)
  have hpb₃ : ∀ i j k, IsPullback
      (pullback.fst (g i) (pullback.fst (g j) (g k) ≫ g j))
      (pullback.snd (g i) (pullback.fst (g j) (g k) ≫ g j))
      (g i) (pullback.fst (g j) (g k) ≫ g j) := fun i j k =>
    IsPullback.of_hasPullback _ _
  obtain ⟨t₁₂, t₁₃, hq₁₂, hq₁₃, hc₂, hc₃⟩ := IsPullback.exists_familyCechProjections hpb hpb₃
  choose δ hδ₁ hδ₂ using fun i => (hpb i i).exists_diagonal
  have hPaff : ∀ i j, IsAffineOver B S hS (p.obj (pullback (g i) (g j)).left) := fun i j =>
    isAffineOver_of_isPullback B S hS p hp (hpb i j) hT (hY i) (hY j)
  exact ⟨fun i j => pullback (g i) (g j),
    fun i j k => pullback (g i) (pullback.fst (g j) (g k) ≫ g j),
    fun i j => pullback.fst (g i) (g j), fun i j => pullback.snd (g i) (g j), δ,
    fun i j k => pullback.fst (g i) (pullback.fst (g j) (g k) ≫ g j), t₁₂, t₁₃,
    fun i j k => pullback.snd (g i) (pullback.fst (g j) (g k) ≫ g j), hPaff,
    fun i j k => isAffineOver_of_isPullback B S hS p hp (hpb₃ i j k) hT (hY i) (hPaff j k),
    hpb, hpb₃, hδ₁, hδ₂, hq₁₂, hq₁₃, hc₂, hc₃⟩

end AlgebraicGeometry.FibredSite

end
