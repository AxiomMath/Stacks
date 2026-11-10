module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# The vanishing locus of the norm of a function

Let `f : X ⟶ Y` be a finite morphism of schemes with a norm `N` on functions, let
`U ⊆ Y` be open and let `a ∈ Γ(X, f⁻¹U)`. This file proves that `N(a)` vanishes at `y ∈ U` —
that is, lies in the maximal ideal of `𝒪_{Y,y}` — exactly when `a` vanishes at some point of the
fibre `f⁻¹(y)`.

One direction is the vanishing axiom of a norm. The other is where finiteness enters: if `a` is
nonvanishing at every point above `y`, then the complement of the non-vanishing locus of `a`
inside the affine-free subscheme `f⁻¹U` is closed, its image under the finite — hence closed —
morphism `f⁻¹U ⟶ U` misses `y`, and over the complement of that image `a` is nonvanishing at
every point, so a unit. The norm of a unit is a unit, and a unit does not vanish anywhere.

This is the second assertion of [Stacks, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
at the level of functions; the passage from functions to maps of invertible modules is the
coefficient calculus of
`StacksFrontier/AlgebraicGeometry/NormInvertible/Coefficient.lean`.

## Main results

* `Stacks.Divisors.evaluation_norm_eq_zero_of_evaluation_eq_zero`: the easy direction, which is
  the vanishing axiom of a norm.
* `Stacks.Divisors.evaluation_norm_ne_zero_of_no_zero_in_fibre`: the finiteness direction.
* `Stacks.Divisors.evaluation_norm_eq_zero_iff_exists_zero_in_fibre`: the characterization.

## Implementation notes

The shrinking step is performed on the open subscheme `Z = f⁻¹U` of `X` and the open subscheme
`U` of `Y`, with `g = f ∣_ U : Z ⟶ U` the restricted morphism, so that `a` becomes a global
section of `Z` and its non-vanishing locus is a basic open `Z_a`. The target open produced is
the complement in `U` of `g(Z \ Z_a)`, pushed forward to `Y` along `U.ι`; `y` lies in it exactly
because `a` is nonvanishing on the whole fibre. That `a` restricted to the inverse image of that
open is a unit is `AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ`, checked stalkwise.

The comparison between the value of `N(a)` at `y` computed on `U` and computed on the smaller
open is the naturality axiom of a norm; the two restrictions of `a` agree because the two
inverse-image opens are equal, which is why a bare `congr 1` suffices there.

No invertibility and no Picard-group input appear: this is a statement about functions, and no
degree either: the hypothesis is a `Stacks.Norm.MorphismNormMap`, since only
multiplicativity, naturality and the vanishing axiom are used.

## References

* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-- If a function vanishes at a point, its norm vanishes at the image point. This is the
vanishing axiom of a norm. -/
theorem evaluation_norm_eq_zero_of_evaluation_eq_zero (f : X ⟶ Y)
    (N : MorphismNormMap f) (U : Y.Opens) (a : Γ(X, f ⁻¹ᵁ U)) (x : X) (hx : f x ∈ U)
    (ha : X.evaluation (f ⁻¹ᵁ U) x hx a = 0) :
    Y.evaluation U (f x) hx (N.app U a) = 0 :=
  N.app_eq_zero_at_image a x hx ha

/-- **If a function has no zero in the fibre over `y`, its norm does not vanish at `y`.**
Finiteness of `f` is what makes the argument work: the image of the vanishing locus is closed,
so the target can be shrunk until the function is a unit upstairs. -/
theorem evaluation_norm_ne_zero_of_no_zero_in_fibre (f : X ⟶ Y) [IsFinite f]
    (N : MorphismNormMap f) (U : Y.Opens) (a : Γ(X, f ⁻¹ᵁ U)) (y : Y) (hy : y ∈ U)
    (hzero : ∀ x : X, (hx : f x ∈ U) → f x = y →
      X.evaluation (f ⁻¹ᵁ U) x hx a = 0 → False) :
    Y.evaluation U y hy (N.app U a) ≠ 0 := by
  classical
  let B : X.Opens := f ⁻¹ᵁ U
  let Z := B.toScheme
  let g : Z ⟶ U.toScheme := f ∣_ U
  let aZ : Γ(Z, ⊤) := B.topIso.inv a
  let D : Z.Opens := Z.basicOpen aZ
  let C : Set Z := (D : Set Z)ᶜ
  have hC : IsClosed C := D.2.isClosed_compl
  have hCimg : IsClosed (g '' C) := g.isClosedMap _ hC
  let W : U.toScheme.Opens := ⟨(g '' C)ᶜ, hCimg.isOpen_compl⟩
  let V : Y.Opens := U.ι ''ᵁ W
  have hD : ∀ z : Z, z ∈ D ↔ z.1 ∈ X.basicOpen a := fun z => by
    rw [← B.ι_image_basicOpen_topIso_inv]
    exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨z', hz', h⟩ => by rwa [← Subtype.ext h]⟩
  have hyW : (⟨y, hy⟩ : U.toScheme) ∈ W := by
    change (⟨y, hy⟩ : U.toScheme) ∉ g '' C
    rintro ⟨z, hzC, hzy⟩
    have hfy : f z.1 = y :=
      calc f z.1 = U.ι (g z) := (morphismRestrict_base_coe f U z).symm
        _ = U.ι ⟨y, hy⟩ := congrArg (fun q : U.toScheme => U.ι q) hzy
        _ = y := rfl
    have hne : X.evaluation B z.1 z.2 a ≠ 0 := hzero z.1 z.2 hfy
    have hxD : z.1 ∈ X.basicOpen a :=
      (X.evaluation_ne_zero_iff_mem_basicOpen z.1 z.2 a).mp hne
    exact hzC ((hD z).2 hxD)
  have hyV : y ∈ V := ⟨⟨y, hy⟩, hyW, rfl⟩
  have hVU : V ≤ U := by
    intro y' hy'
    change y' ∈ U.ι ''ᵁ W at hy'
    obtain ⟨z, -, rfl⟩ := hy'
    exact z.2
  let i : V ⟶ U := homOfLE hVU
  let BV : X.Opens := f ⁻¹ᵁ V
  have hBV : BV ≤ B := fun x hx => hVU hx
  let j := (homOfLE hBV).op
  let aV : Γ(X, BV) := X.presheaf.map j a
  have hunitA : IsUnit aV := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ BV aV fun x hx => ?_
    have hxV : f x ∈ V := hx
    have hxW : g ⟨x, hVU hxV⟩ ∈ W := by
      change f x ∈ U.ι ''ᵁ W at hx
      obtain ⟨w, hwW, hfx⟩ := hx
      have hgw : g ⟨x, hVU hxV⟩ = w := U.ι.isOpenEmbedding.injective <|
        (morphismRestrict_base_coe f U ⟨x, hVU hxV⟩).trans hfx.symm
      rwa [hgw]
    have hxNotC : g ⟨x, hVU hxV⟩ ∉ g '' C := by simpa [W] using hxW
    have hxOpen : x ∈ X.basicOpen a := (hD _).1 (by_contra fun h => hxNotC ⟨_, h, rfl⟩)
    have hxOpenV : x ∈ X.basicOpen aV := by
      rw [X.basicOpen_res a j]
      exact ⟨hxV, hxOpen⟩
    exact (X.mem_basicOpen aV x hxV).mp hxOpenV
  have hneV : Y.evaluation V y hyV (N.app V aV) ≠ 0 :=
    ((hunitA.map (N.app V)).map (Y.evaluation V y hyV).hom).ne_zero
  have haV : aV = X.presheaf.map ((Opens.map f.base).map i).op a := by congr 1
  have heval : Y.evaluation V y hyV (N.app V aV) = Y.evaluation U y hy (N.app U a) := by
    rw [haV, N.naturality i a]
    simp [Scheme.evaluation]
  exact fun hz => hneV (heval.trans hz)

/-- **The norm of a function vanishes at `y` exactly when the function vanishes somewhere in the
fibre over `y`.** This is the function-level form of the vanishing-locus clause of Tag 0BCZ. -/
theorem evaluation_norm_eq_zero_iff_exists_zero_in_fibre (f : X ⟶ Y) [IsFinite f]
    (N : MorphismNormMap f) (U : Y.Opens) (a : Γ(X, f ⁻¹ᵁ U)) (y : Y) (hy : y ∈ U) :
    Y.evaluation U y hy (N.app U a) = 0 ↔
      ∃ x : X, ∃ hxy : f x = y,
        X.evaluation (f ⁻¹ᵁ U) x (by change f x ∈ U; rw [hxy]; exact hy) a = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hno
    exact evaluation_norm_ne_zero_of_no_zero_in_fibre f N U a y hy
      (fun x hx hxy hz => hno ⟨x, hxy, hz⟩) h
  · rintro ⟨x, hxy, hzero⟩
    subst y
    exact evaluation_norm_eq_zero_of_evaluation_eq_zero f N U a x (by exact hy) hzero

end Stacks.Divisors
