module

public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Basic

/-!
# An affine morphism is flat as a morphism onto the pushforward of its own structure sheaf

Let `f : Y ⟶ X` be an affine morphism of schemes.  The space `X` carrying the sheaf of rings
`f_* 𝒪_Y` is a ringed space, and `f` itself is a morphism of ringed spaces
`g : (Y, 𝒪_Y) ⟶ (X, f_* 𝒪_Y)` whose structure map is the identity.  This file proves that `g`
is **flat**: for every `y ∈ Y` the stalk `𝒪_{Y, y}` is a flat module over `(f_* 𝒪_Y)_{f(y)}`
along the comparison `TopCat.Presheaf.stalkPushforward`.

In the notation of the source, with `X = Spec(B)` and `Y = Spec(A)` and a point `𝔭 = y` of `Y`
over `𝔮 = f(y)`, the two stalks are `A_𝔮` and `A_𝔭`, and the second is a further localization
of the first.  The proof below is that statement with no affineness assumed of either scheme:
both stalks are localizations of `Γ(Y, f⁻¹U)` for `U` any affine open of `X` around `f(y)` —
the first by `AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`, the second by
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` at the affine open `f⁻¹U` — so
`𝒪_{Y, y}` is flat over `Γ(Y, f⁻¹U)` because a localization is flat, and flatness over the
localization `(f_* 𝒪_Y)_{f(y)}` is the same property by `Module.flat_iff_of_isLocalization`.

No containment of multiplicative sets has to be exhibited: the two localizations are compared
only through the base ring `Γ(Y, f⁻¹U)`, and what makes the three algebra structures compatible
is `TopCat.Presheaf.stalkPushforward_germ`, which says that the germ at `y` over `f⁻¹U`
factors as the germ of `f_* 𝒪_Y` at `f(y)` over `U` followed by the stalk comparison.

## Main results

* `AlgebraicGeometry.IsAffineOpen.flat_stalkPushforward` — flatness of the stalk comparison at a
  point lying in a chosen affine open of the target.
* `AlgebraicGeometry.flat_stalkPushforward_of_isAffineHom` — the same with no open chosen: for an
  affine morphism of schemes `𝒪_{Y, y}` is flat over `(f_* 𝒪_Y)_{f(y)}` for every `y`.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **The stalk comparison of an affine pushforward is flat, computed on a chosen affine open.**
Let `f : Y ⟶ X` be an affine morphism of schemes, `U` an affine open of `X` and `y` a point of
`Y` with `f y ∈ U`.  Then `𝒪_{Y, y}` is a flat module over `(f_* 𝒪_Y)_{f y}` along
`TopCat.Presheaf.stalkPushforward`.

Both rings are localizations of `Γ(Y, f⁻¹U)`: the stalk of the pushforward at `f y` by
`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`, and the stalk of `𝒪_Y` at `y`
by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` at the affine open `f⁻¹U`.  So the
second is flat over `Γ(Y, f⁻¹U)`, and `Module.flat_iff_of_isLocalization` turns that into
flatness over the first. -/
public theorem IsAffineOpen.flat_stalkPushforward {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U) {y : Y} (hy : f.base y ∈ U) :
    letI : Algebra ((f.base _* Y.presheaf).stalk (f.base y)) (Y.presheaf.stalk y) :=
      (Y.presheaf.stalkPushforward CommRingCat f.base y).hom.toAlgebra
    Module.Flat ((f.base _* Y.presheaf).stalk (f.base y)) (Y.presheaf.stalk y) := by
  have hyU : y ∈ f ⁻¹ᵁ U := hy
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).stalk (f.base y)) :=
    ((f.base _* Y.presheaf).germ U (f.base y) hy).hom.toAlgebra
  let : Algebra Γ(Y, f ⁻¹ᵁ U) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ (f ⁻¹ᵁ U) y hyU).hom.toAlgebra
  let : Algebra ((f.base _* Y.presheaf).stalk (f.base y)) (Y.presheaf.stalk y) :=
    (Y.presheaf.stalkPushforward CommRingCat f.base y).hom.toAlgebra
  -- The germ at `y` over `f⁻¹U` factors through the stalk of the pushforward at `f y`.
  have : IsScalarTower Γ(Y, f ⁻¹ᵁ U)
      ((f.base _* Y.presheaf).stalk (f.base y)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun z => by
      show (Y.presheaf.germ (f ⁻¹ᵁ U) y hyU) z = _
      rw [← TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base Y.presheaf U y hy]
      rfl
  have := hU.isLocalization_pushforwardStalk f hy
  have : Module.Flat Γ(Y, f ⁻¹ᵁ U) (Y.presheaf.stalk y) :=
    have := (hU.preimage f).isLocalization_stalk (⟨y, hyU⟩ : f ⁻¹ᵁ U)
    IsLocalization.flat _ ((hU.preimage f).primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
  exact (Module.flat_iff_of_isLocalization
    ((f.base _* Y.presheaf).stalk (f.base y))
    (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U)
      (hU.primeIdealOf ⟨f.base y, hy⟩).asIdeal.primeCompl)
    (Y.presheaf.stalk y)).mpr ‹_›

/-- **An affine morphism of schemes is flat onto the pushforward of its own structure sheaf.**
For `f : Y ⟶ X` affine and `y` a point of `Y`, the stalk `𝒪_{Y, y}` is a flat module over
`(f_* 𝒪_Y)_{f y}` along `TopCat.Presheaf.stalkPushforward`.  This is the flatness of the
morphism of ringed spaces `g : (Y, 𝒪_Y) ⟶ (X, f_* 𝒪_Y)` asserted in the proof of
[Stacks, Tag 0AVW].

An affine open of `X` around `f y` is chosen and
`AlgebraicGeometry.IsAffineOpen.flat_stalkPushforward` applied; the conclusion does not mention
it. -/
public theorem flat_stalkPushforward_of_isAffineHom {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (y : Y) :
    letI : Algebra ((f.base _* Y.presheaf).stalk (f.base y)) (Y.presheaf.stalk y) :=
      (Y.presheaf.stalkPushforward CommRingCat f.base y).hom.toAlgebra
    Module.Flat ((f.base _* Y.presheaf).stalk (f.base y)) (Y.presheaf.stalk y) := by
  obtain ⟨U, hU, hmem, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := f.base y) (U := ⊤) trivial
  exact hU.flat_stalkPushforward f hmem

end AlgebraicGeometry

end
