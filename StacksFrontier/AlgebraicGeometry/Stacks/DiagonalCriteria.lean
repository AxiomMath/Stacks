module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# The criteria for a representable diagonal: conditions (1) and (2)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. The diagonal `𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic
spaces if and only if, for every scheme `U` over `S` and all objects `x`, `y` of the fibre of `𝒳`
over `U`, the isomorphism sheaf `Isom(x, y)` is an algebraic space over `U`.

## Main results

* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`: the
  diagonal is representable by algebraic spaces if and only if every `Isom(x, y)` is an
  algebraic space.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- The diagonal of a category fibred in groupoids over the big fppf site of `S` is representable
by algebraic spaces if and only if every isomorphism sheaf `Isom(x, y)` of two objects of a fibre
is an algebraic space over the scheme the fibre sits over. -/
@[stacks 045G "parts (1) and (2)"]
theorem hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf :
    HasRepresentableDiagonal B S hS 𝒳 ↔ IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 := by
  have hp := 𝒳.isFiberedInGroupoids
  have : 𝒳.val.p.IsFibered := hp.isFibered
  constructor
  · intro h U x y
    have h₁ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p U x
    have h₂ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p U y
    have hY : pairFunctor h₁ h₂ ⋙ ProdP 𝒳.val.p = Over.map U.hom := pairFunctor_comp h₁ h₂
    obtain ⟨F, hF, hE⟩ := h U (pairFunctor h₁ h₂) hY
    obtain ⟨i⟩ := (nonempty_equivalenceOver_fst_iff hp hY F).1 hE
    exact ⟨F, hF, ⟨i.symm.trans (Functor.isoWhiskerRight
      (Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.p U x y hp) uliftFunctor.{u, v})⟩⟩
  · intro h
    dsimp only [HasRepresentableDiagonal, IsRepresentableByAlgebraicSpaces]
    intro U Y hY
    obtain ⟨F, hF, ⟨i⟩⟩ := h U (Functor.sliceValue 𝒳.val.p U (Y₁' Y) (h1' hY))
      (Functor.sliceValue 𝒳.val.p U (Y₂' Y) (h2' hY))
    exact ⟨F, hF, (nonempty_equivalenceOver_fst_iff hp hY F).2 ⟨(Functor.isoWhiskerRight
      (Functor.vertHomPresheafIsoIsomPresheafOfPoint 𝒳.val.p hp U Y hY) uliftFunctor.{u, v}).trans
        i.symm⟩⟩

end AlgebraicGeometry.Stack

end
