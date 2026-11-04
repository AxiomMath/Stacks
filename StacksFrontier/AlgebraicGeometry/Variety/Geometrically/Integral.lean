module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometrically integral schemes

This file records the pointwise and global notions of geometric integrality. A scheme is
geometrically pointwise integral at a point when every point above it after extension of the
base field has an integral local ring. It is geometrically pointwise integral when this holds
at every point, and geometrically integral when every field extension gives an integral scheme.

## Main definitions

* `AlgebraicGeometry.GeometricallyPointwiseIntegralAt` is geometric pointwise integrality at a
  point.
* `AlgebraicGeometry.GeometricallyPointwiseIntegral` is geometric pointwise integrality at every
  point.

## Main results

* `AlgebraicGeometry.geometricallyPointwiseIntegralAt_iff` characterizes geometric pointwise
  integrality at a point using the canonical base change along every field extension.
* `AlgebraicGeometry.geometricallyPointwiseIntegral_iff` gives the corresponding
  characterization at every point.
* `AlgebraicGeometry.geometricallyIntegral_iff_isIntegral_pullback` characterizes geometric
  integrality of a scheme over a field as integrality of the base change along every field
  extension of that field.

## Implementation notes

The pointwise predicates are stated for arbitrary base schemes and arbitrary presentations of
the relevant pullback, so they are independent of a chosen model of base change. The
characterizing lemmas prove that over `Spec k` they recover the source's formulation using the
canonical pullback along `Spec.map (algebraMap k K)`. The global notion is Mathlib's existing,
more general `AlgebraicGeometry.GeometricallyIntegral`, which over `Spec k` is shown here to be
the source's condition that `X_{k'}` is integral for every field extension `k'/k`.

## References

* [Stacks Project, Tag 020H](https://stacks.math.columbia.edu/tag/020H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A morphism `f : X ⟶ Y` is geometrically pointwise integral at `x : X` if, after every
base change from the spectrum of a field, every point above `x` has an integral local ring. -/
@[stacks 020H "part (1)"]
public abbrev GeometricallyPointwiseIntegralAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    Prop :=
  ∀ ⦃K : Type u⦄ [Field K] (y : Spec (.of K) ⟶ Y) ⦃Z : Scheme.{u}⦄
    (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)),
    IsPullback fst snd f y → ∀ z : Z, fst.base z = x → IsDomain (Z.presheaf.stalk z)

/-- A morphism is geometrically pointwise integral if it is geometrically pointwise integral
at every point of its source. -/
@[stacks 020H "part (2)"]
public abbrev GeometricallyPointwiseIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X, GeometricallyPointwiseIntegralAt f x

/- `(f : X ⟶ Y) : Prop` is a signature, not a statement. It is shared by seven unrelated
predicates: `AlgebraicGeometry.Scheme.Hom.IsNormal` and `.IsRegular` (flatness plus geometric
normality, resp. regularity, of the fibre), `AlgebraicGeometry.IsNoetherianOnSpecializations`
(Noetherian stalks at the specializations of the image),
`AlgebraicGeometry.HasUniversallyBoundedFibers` (one integer bounding every fibre degree),
`AlgebraicGeometry.Scheme.Hom.InducesResidueFieldIsomorphisms` (every residue-field map is an
isomorphism),
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.DirectImageStructureSheafCommutesBaseChange` (the
degree-zero base-change map is an isomorphism for every base change) and
`GeometricallyPointwiseIntegral` above. The normal and regular predicates are the closest pair
and still differ: the conclusions are `IsNormalRing` and `IsRegularLocalRing`, over all field
extensions resp. only the essentially-finite-type ones.

The pointwise signature `(f : X ⟶ Y) (x : X) : Prop` is shared the same way, by
`GeometricallyPointwiseIntegralAt` above and `AlgebraicGeometry.Scheme.Hom.IsNormalAt` and
`.IsRegularAt`, which differ in the same place as their global forms. -/

/-- Geometric pointwise integrality at `x` is exactly integrality of the local rings at all
points above `x` in every canonical field-extension base change. -/
@[simp]
public theorem geometricallyPointwiseIntegralAt_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    GeometricallyPointwiseIntegralAt f x ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        let g : Spec (.of K) ⟶ Spec (.of k) :=
          Spec.map (CommRingCat.ofHom (algebraMap k K))
        ∀ x' : (pullback f g : Scheme.{u}),
          (pullback.fst f g).base x' = x → IsDomain ((pullback f g).presheaf.stalk x') := by
  constructor
  · intro h K _ _
    dsimp
    intro x' hx'
    exact h (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _) x' hx'
  · intro h K _ y Z fst snd hpb z hz
    let φ : k →+* K := (Spec.preimage y).hom
    let alg : Algebra k K := φ.toAlgebra
    let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom φ)
    have hy : g = y := Spec.map_preimage y
    let e : Z ≅ pullback f g :=
      (show IsPullback fst snd f g from by simpa only [hy] using hpb).isoPullback
    have hx' : (pullback.fst f g).base (e.hom.base z) = x := by
      rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_fst]
    exact ((asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv.isDomain_iff).mp
      (by simpa [g, alg, RingHom.algebraMap_toAlgebra] using
        @h K _ alg (e.hom.base z) hx')

/-- A scheme is geometrically pointwise integral exactly when the canonical base change along
every field extension has integral local rings at all of its points. -/
@[simp, ega "IV 4.6.9"]
public theorem geometricallyPointwiseIntegral_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    GeometricallyPointwiseIntegral f ↔
      ∀ (x : X) (K : Type u) [Field K] [Algebra k K],
        let g : Spec (.of K) ⟶ Spec (.of k) :=
          Spec.map (CommRingCat.ofHom (algebraMap k K))
        ∀ x' : (pullback f g : Scheme.{u}),
          (pullback.fst f g).base x' = x → IsDomain ((pullback f g).presheaf.stalk x') := by
  simp only [GeometricallyPointwiseIntegral, geometricallyPointwiseIntegralAt_iff]

/-- A scheme `X` over a field `k` is geometrically integral if and only if the base change
`X_{k'}` is integral for every field extension `k'/k`. -/
@[stacks 020H "part (3)", ega "IV 4.6.2"]
public theorem geometricallyIntegral_iff_isIntegral_pullback {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyIntegral f ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsIntegral ·) :=
    ⟨fun e h ↦ have := h; IsIntegral.of_isIso e.hom⟩
  rw [geometricallyIntegral_iff]
  exact geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms

add_to_stacks 020H "part (3)" AlgebraicGeometry.GeometricallyIntegral
add_to_sga "6 XII 1.2" "partial" AlgebraicGeometry.GeometricallyIntegral
add_to_ega "IV 4.6.2" "more general" AlgebraicGeometry.GeometricallyIntegral

end AlgebraicGeometry
