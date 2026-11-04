module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AsPullback

/-!
# The diagonal square of a monomorphism (Stacks 0CBB)

For morphisms `𝒳 ⟶ 𝒳' ⟶ 𝒴` of algebraic stacks with `𝒳 ⟶ 𝒳'` a monomorphism, the canonical
square
```
  𝒳   ------->  𝒳 ×_𝒴 𝒳
  |                |
  v                v
  𝒳'  ------->  𝒳' ×_𝒴 𝒳'
```
is 2-cartesian. The source proves this in two steps: `𝒳 = 𝒳 ×_{𝒳'} 𝒳` because `𝒳 ⟶ 𝒳'` is a
monomorphism (Stacks 04ZZ), and then the comparison of a 2-fibre product over `𝒳'` with one
over `𝒴` along the relative diagonal of `𝒳' ⟶ 𝒴` (Stacks 04Z1), which is proved as
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_toRelativeDiagonalPullback`.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.isEquivalence_relativeDiagonal_of_fullyFaithful`:
  the relative diagonal of a fully faithful functor is an equivalence. This is the content of
  Stacks 04ZZ in this rendering, and it is left untagged, since Stacks 04ZZ states the
  identification `𝒳 = 𝒳 ×_{𝒳'} 𝒳` for algebraic stacks rather than this equivalence of
  categories.
* `CategoryTheory.Limits.CategoricalPullback.isEquivalence_monomorphism_diagonalComparison`:
  **Stacks 0CBB**.

## Implementation notes

Everything here is about functors between categories: this covers the underlying functors of
morphisms of algebraic stacks, and no algebraicity is used. A monomorphism of stacks is
rendered as a fully faithful functor, as elsewhere in this library, and full faithfulness is
taken as a conjunction rather than as instance arguments so that the hypothesis can be
supplied by a term.

Being a 2-fibre product square is rendered, as throughout this directory, by the induced
functor into the explicit 2-fibre product being an equivalence. The induced functor of the
square above is the composite of the relative diagonal of `𝒳 ⟶ 𝒳'` with the Stacks 04Z1
comparison `toRelativeDiagonalPullback`, so the lemma is the statement that that composite is
an equivalence — which is exactly the two steps of the source's proof, in order.

## References

* [Stacks Project, Tag 0CBB](https://stacks.math.columbia.edu/tag/0CBB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback

/-- The relative diagonal of a fully faithful functor is an equivalence of categories: an
object of `X ×_{X'} X` is a pair of objects of `X` whose images in `X'` are isomorphic, and
full faithfulness turns that isomorphism into one upstairs.

This is the content of Stacks 04ZZ in the present rendering; it is left untagged because
Stacks 04ZZ states the identification of a monomorphism's source with its self-product for
algebraic stacks rather than this equivalence of categories. -/
theorem isEquivalence_relativeDiagonal_of_fullyFaithful
    {X X' : Type*} [Category X] [Category X']
    (f : X ⥤ X') (hf : f.Full ∧ f.Faithful) :
    (relativeDiagonal f).IsEquivalence := by
  have : f.Full := hf.1
  have : f.Faithful := hf.2
  refine ⟨?_, ?_, ?_⟩
  · constructor
    intro a b u v huv
    simpa using congrArg Hom.fst huv
  · constructor
    intro a b φ
    let q : a ⟶ b := by simpa using φ.fst
    refine ⟨q, ?_⟩
    rw [relativeDiagonal_map]
    exact hom_ext rfl (hf.2.map_injective (by simpa [q] using φ.w))
  · constructor
    intro y
    rw [Functor.essImage]
    let e : y.fst ≅ y.snd := f.preimageIso y.iso
    refine ⟨y.fst, ⟨mkIso (F := f) (G := f) (Iso.refl _) e ?_⟩⟩
    simp [e, Functor.preimageIso]

/-- **Stacks 0CBB.** The square from the relative diagonal of a fully faithful functor `f` to
the relative diagonal of `f ⋙ g` is a 2-fibre product square: the induced functor into the
explicit 2-fibre product is an equivalence.

It is the composite of the relative diagonal of `f`, an equivalence because `f` is fully
faithful, with the Stacks 04Z1 comparison functor. -/
@[stacks 0CBB]
theorem isEquivalence_monomorphism_diagonalComparison
    {X X' Y : Type*} [Category X] [Category X'] [Category Y]
    (f : X ⥤ X') (g : X' ⥤ Y) (hf : f.Full ∧ f.Faithful) :
    (relativeDiagonal f ⋙ toRelativeDiagonalPullback f f g).IsEquivalence := by
  have : (relativeDiagonal f).IsEquivalence :=
    isEquivalence_relativeDiagonal_of_fullyFaithful f hf
  have : (toRelativeDiagonalPullback f f g).IsEquivalence :=
    isEquivalence_toRelativeDiagonalPullback f f g
  infer_instance

end CategoryTheory.Limits.CategoricalPullback

end
