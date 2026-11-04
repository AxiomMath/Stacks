module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Localization

/-!
# Base change along the canonical morphism out of the spectrum of a local ring

For a scheme `X` and a point `x` of `X` the canonical morphism `X.fromSpecStalk x`,
`Spec 𝒪_{X, x} ⟶ X`, is **flat** and a **preimmersion**: on an affine open neighbourhood `U` of
`x` it is `Spec` of the germ map `Γ(X, U) → 𝒪_{X, x}`, which exhibits `𝒪_{X, x}` as a
localization of `Γ(X, U)`. Both properties are stable under base change, and a flat preimmersion
induces isomorphisms on local rings, because such a map on local rings is surjective by the
preimmersion hypothesis and injective because a flat local homomorphism is faithfully flat.

Consequently, for any morphism `ν : Y ⟶ X` the first projection of `Y ×_X Spec 𝒪_{X, x}` is an
isomorphism on every local ring, and its image is the set of points of `Y` specializing into
`x`. In particular every point `y` of `Y` lying over `x` is hit, so the fibre product has a
point over `y` whose local ring is `𝒪_{Y, y}`.

## Main results

* `AlgebraicGeometry.flat_fromSpecStalk`: the canonical morphism `Spec 𝒪_{X, x} ⟶ X` is flat.
* `AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`: a flat preimmersion induces
  isomorphisms on local rings.
* `AlgebraicGeometry.exists_point_pullback_fromSpecStalk_isIso_stalkMap`: for `ν : Y ⟶ X` and a
  point `y` of `Y` above `x`, the fibre product `Y ×_X Spec 𝒪_{X, x}` has a point over `y` at
  which the first projection induces an isomorphism of local rings.

## References

* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7), which computes the
  image of `Spec 𝒪_{X, x} ⟶ X`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The canonical morphism `Spec 𝒪_{X,x} ⟶ X` is flat.** On an affine open neighbourhood `U`
of `x` it is `Spec` of the germ map `Γ(X, U) → 𝒪_{X, x}`, which exhibits `𝒪_{X, x}` as a
localization of `Γ(X, U)` and is therefore flat. -/
public lemma flat_fromSpecStalk (X : Scheme.{u}) (x : X) :
    Flat (X.fromSpecStalk x) := by
  let U := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := X.affineCover.covers x
  show Flat (hU.fromSpecStalk hx)
  dsimp [IsAffineOpen.fromSpecStalk]
  have hflat : (X.presheaf.germ U x hx).hom.Flat := by
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := Flat.SpecMap_iff.mpr hflat
  infer_instance

/-- **A flat preimmersion induces isomorphisms on local rings.** Surjectivity of the map on
local rings is part of being a preimmersion, and injectivity holds because a flat local
homomorphism is faithfully flat, hence injective. -/
public lemma isIso_stalkMap_of_flat_isPreimmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [Flat g] [IsPreimmersion g] (x : X) : IsIso (g.stalkMap x) := by
  have hinj : Function.Injective (g.stalkMap x).hom := by
    algebraize [(g.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap g x) (g.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, g.stalkMap_surjective x⟩

/-- **The fibre product of a scheme with the spectrum of a local ring of the base has a point
over every point of the given fibre, and there it has the same local ring.** Let `ν : Y ⟶ X` be
a morphism of schemes, let `x` be a point of `X` and let `y` be a point of `Y` with `ν y = x`. Then
`Y ×_X Spec 𝒪_{X, x}` has a point `w` whose image under the first projection is `y` and at which
the first projection induces an isomorphism `𝒪_{Y, y} ≅ 𝒪_{Y ×_X Spec 𝒪_{X, x}, w}` of local
rings. -/
public theorem exists_point_pullback_fromSpecStalk_isIso_stalkMap {X Y : Scheme.{u}}
    (ν : Y ⟶ X) (x : X) (y : Y) (hy : ν.base y = x) :
    ∃ w : (pullback ν (X.fromSpecStalk x) : Scheme.{u}),
      (pullback.fst ν (X.fromSpecStalk x)).base w = y ∧
      IsIso ((pullback.fst ν (X.fromSpecStalk x)).stalkMap w) := by
  have hsq : IsPullback (pullback.snd ν (X.fromSpecStalk x))
      (pullback.fst ν (X.fromSpecStalk x)) (X.fromSpecStalk x) ν :=
    (IsPullback.of_hasPullback ν (X.fromSpecStalk x)).flip
  have : Flat (pullback.fst ν (X.fromSpecStalk x)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq (flat_fromSpecStalk X x)
  have : IsPreimmersion (pullback.fst ν (X.fromSpecStalk x)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ν)
    (g := X.fromSpecStalk x) y (IsLocalRing.closedPoint (X.presheaf.stalk x)) (by simp [hy])
  exact ⟨w, hw, isIso_stalkMap_of_flat_isPreimmersion _ w⟩

end AlgebraicGeometry

end
