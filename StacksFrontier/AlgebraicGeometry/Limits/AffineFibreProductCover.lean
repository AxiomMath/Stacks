module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine open coverings of fibre products

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes. Given an affine open covering of `S`
and, over each of its members `S i`, affine open coverings of the inverse images `f ⁻¹ S i` and
`g ⁻¹ S i`, the fibre products of the chosen opens over `S i` form an affine open covering of
`X ×_S Y`.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.isAffine_openCoverOfBase_bind_openCoverOfLeftRight`: every
  member of the covering assembled in this way is affine.

## References

* [Stacks Project, Tag 01JS](https://stacks.math.columbia.edu/tag/01JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace AlgebraicGeometry.Scheme.Pullback

/-- Every member of the open cover of a fibre product assembled from affine open covers over an
affine open cover of the base is affine. -/
@[stacks 01JS, ega "III 6.5.2" "more general", ega "III 6.6.4" "partial"]
theorem isAffine_openCoverOfBase_bind_openCoverOfLeftRight
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (𝒰 : Scheme.OpenCover.{v} S)
    (𝒱 : ∀ i : 𝒰.I₀, Scheme.OpenCover.{w} (pullback f (𝒰.f i)))
    (𝒲 : ∀ i : 𝒰.I₀, Scheme.OpenCover.{t} (pullback g (𝒰.f i)))
    (h𝒰 : ∀ i, IsAffine (𝒰.X i))
    (h𝒱 : ∀ i j, IsAffine ((𝒱 i).X j))
    (h𝒲 : ∀ i k, IsAffine ((𝒲 i).X k)) :
    ∀ a : ((Scheme.Pullback.openCoverOfBase 𝒰 f g).bind fun i =>
      Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i)
        (pullback.snd f (𝒰.f i)) (pullback.snd g (𝒰.f i))).I₀,
      IsAffine (((Scheme.Pullback.openCoverOfBase 𝒰 f g).bind fun i =>
        Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i)
          (pullback.snd f (𝒰.f i)) (pullback.snd g (𝒰.f i))).X a) := by
  rintro ⟨i, j, k⟩
  have := h𝒰 i
  have := h𝒱 i j
  have := h𝒲 i k
  show IsAffine (pullback ((𝒱 i).f j ≫ pullback.snd f (𝒰.f i))
    ((𝒲 i).f k ≫ pullback.snd g (𝒰.f i)))
  infer_instance

end AlgebraicGeometry.Scheme.Pullback
