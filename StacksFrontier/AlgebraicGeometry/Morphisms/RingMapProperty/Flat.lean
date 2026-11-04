module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.LocallyOfType

/-!
# Flat morphisms are the morphisms locally of type "flat ring map"

Flatness of ring maps is a local property, so the general results on morphisms locally of
type `P` apply to it: flatness of a morphism of schemes can be checked on all pairs of affine
opens, on open coverings of the target and of the preimages, or on affine such coverings, and
it passes to restrictions to open subschemes.

## Main results

* `RingHom.Flat.stacksPropertyIsLocal`: flatness of ring maps is a local property.
* `AlgebraicGeometry.flat_iff_locallyOfType`: a morphism is flat exactly when it is locally of
  type "flat ring map".
* `AlgebraicGeometry.flat_tfae`, `AlgebraicGeometry.flat_resLE`,
  `AlgebraicGeometry.flat_tfae_and_resLE`: [Stacks Project, Tag 01U5].

## Implementation notes

The source defines a morphism `f : X → S` to be flat when every local ring map
`𝒪_{S, f(x)} → 𝒪_{X, x}` is flat (Tags 01U2 and 01U3). Mathlib's `AlgebraicGeometry.Flat`
asks instead that `𝒪_S(V) → 𝒪_X(U)` be flat for all affine opens `U ⊆ X`, `V ⊆ S` with
`f(U) ⊆ V`; the two notions agree by `AlgebraicGeometry.Flat.iff_flat_stalkMap`, so Mathlib's
notion is used throughout. The results above are the instances for `RingHom.Flat` of
`AlgebraicGeometry.locallyOfType_tfae` and `AlgebraicGeometry.locallyOfType_resLE`.

## References

* [Stacks Project, Tag 01U5](https://stacks.math.columbia.edu/tag/01U5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- Flatness of ring maps is a local property. -/
theorem RingHom.Flat.stacksPropertyIsLocal : RingHom.StacksPropertyIsLocal RingHom.Flat where
  localizationAwayPreserves := RingHom.Flat.propertyIsLocal.localizationAwayPreserves
  compPrincipalLocalizations {_ _ Rf Aa} _ _ _ _ f a _ _ _ _ _ hg :=
    ((RingHom.Flat.holdsForLocalizationAway Rf f).comp hg).comp
      (RingHom.Flat.holdsForLocalizationAway Aa a)
  ofLocalizationFiniteSpanTarget :=
    (RingHom.ofLocalizationSpanTarget_iff_finite @RingHom.Flat).mp
      RingHom.Flat.ofLocalizationSpanTarget

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A morphism of schemes is flat exactly when it is locally of type "flat ring map". -/
theorem flat_iff_locallyOfType (f : X ⟶ S) : Flat f ↔ locallyOfType RingHom.Flat f :=
  HasRingHomProperty.iff_exists_appLE (P := @Flat)
    RingHom.Flat.stacksPropertyIsLocal.stableUnderCompositionWithLocalizationAwaySource

/-- If `f` is flat then so is its restriction `U → V` to any opens `U ⊆ X`, `V ⊆ S` with
`f(U) ⊆ V`. -/
@[stacks 01U5 "moreover: restriction to open subschemes"]
theorem flat_resLE {f : X ⟶ S} (hf : Flat f) (V : S.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) : Flat (f.resLE V U e) :=
  (flat_iff_locallyOfType _).mpr (locallyOfType_resLE RingHom.Flat.stacksPropertyIsLocal
    ((flat_iff_locallyOfType f).mp hf) V U e)

/-- Flatness of a morphism of schemes can be checked on all pairs of affine opens, on open
coverings of target and preimages, or on affine such coverings.

The source defines flatness of `f` by flatness of the local ring maps
`𝒪_{S, f(x)} → 𝒪_{X, x}`; this agrees with `AlgebraicGeometry.Flat` by
`AlgebraicGeometry.Flat.iff_flat_stalkMap`. -/
@[stacks 01U5 "equivalence of (1), (2), (3) and (4)"]
theorem flat_tfae (f : X ⟶ S) :
    List.TFAE [
      Flat f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.Flat,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, Flat (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          (f.appLE V U e).hom.Flat] := by
  simp only [flat_iff_locallyOfType]
  exact locallyOfType_tfae RingHom.Flat.stacksPropertyIsLocal f

/-- The whole statement: the four characterizations of flatness agree, and flatness passes to
restrictions to open subschemes.

The source defines flatness of `f` by flatness of the local ring maps
`𝒪_{S, f(x)} → 𝒪_{X, x}`; this agrees with `AlgebraicGeometry.Flat` by
`AlgebraicGeometry.Flat.iff_flat_stalkMap`. -/
@[stacks 01U5]
theorem flat_tfae_and_resLE (f : X ⟶ S) :
    List.TFAE [
      Flat f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.Flat,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, Flat (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          (f.appLE V U e).hom.Flat] ∧
    (Flat f → ∀ (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V), Flat (f.resLE V U e)) :=
  ⟨flat_tfae f, fun hf U V e ↦ flat_resLE hf V U e⟩

end AlgebraicGeometry
