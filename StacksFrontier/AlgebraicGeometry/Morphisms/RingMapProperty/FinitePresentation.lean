module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.LocallyOfType

/-!
# Morphisms locally of finite presentation

Being of finite presentation is a local property of ring maps, so the general results on
morphisms locally of type `P` apply to it: a morphism of schemes is locally of finite
presentation exactly when it is locally of type "finitely presented ring map", this can be
checked on all pairs of affine opens or on (affine) open coverings of the source and target, and
it passes to restrictions to open subschemes.

## Main results

* `RingHom.FinitePresentation.stacksPropertyIsLocal`: being of finite presentation is a local
  property of ring maps.
* `AlgebraicGeometry.locallyOfFinitePresentation_iff_locallyOfType`: a morphism is locally of
  finite presentation exactly when it is locally of type `RingHom.FinitePresentation`.
* `AlgebraicGeometry.locallyOfFinitePresentation_tfae`,
  `AlgebraicGeometry.locallyOfFinitePresentation_resLE`,
  `AlgebraicGeometry.locallyOfFinitePresentation_tfae_and_resLE`: [Stacks Project, Tag 01TQ].

## Implementation notes

The locality of finite presentation is assembled from Mathlib's lemmas
`RingHom.finitePresentation_localizationPreserves`,
`RingHom.finitePresentation_holdsForLocalizationAway` and
`RingHom.finitePresentation_ofLocalizationSpanTarget`. Everything else is an instance of
`AlgebraicGeometry.locallyOfType_tfae` and `AlgebraicGeometry.locallyOfType_resLE`.

## References

* [Stacks Project, Tag 01TQ](https://stacks.math.columbia.edu/tag/01TQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace RingHom

/-- Being of finite presentation is a local property of ring maps. -/
theorem FinitePresentation.stacksPropertyIsLocal :
    StacksPropertyIsLocal RingHom.FinitePresentation where
  localizationAwayPreserves := finitePresentation_localizationPreserves.away
  compPrincipalLocalizations {_ _ Rf Aa} _ _ _ _ f a _ _ _ _ _ hg :=
    (finitePresentation_holdsForLocalizationAway Aa a).comp
      (hg.comp (finitePresentation_holdsForLocalizationAway Rf f))
  ofLocalizationFiniteSpanTarget :=
    (RingHom.ofLocalizationSpanTarget_iff_finite @RingHom.FinitePresentation).mp
      finitePresentation_ofLocalizationSpanTarget

end RingHom

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A morphism of schemes is locally of finite presentation exactly when it is locally of type
"ring map of finite presentation". -/
theorem locallyOfFinitePresentation_iff_locallyOfType (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔ locallyOfType RingHom.FinitePresentation f :=
  HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation) <|
    RingHom.FinitePresentation.stacksPropertyIsLocal
      |>.stableUnderCompositionWithLocalizationAwaySource

/-- If `f` is locally of finite presentation then so is its restriction `U → V` to any opens
`U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`. -/
@[stacks 01TQ "moreover: restriction to open subschemes"]
theorem locallyOfFinitePresentation_resLE {f : X ⟶ S} (hf : LocallyOfFinitePresentation f)
    (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    LocallyOfFinitePresentation (f.resLE V U e) :=
  (locallyOfFinitePresentation_iff_locallyOfType _).mpr
    (locallyOfType_resLE RingHom.FinitePresentation.stacksPropertyIsLocal
      ((locallyOfFinitePresentation_iff_locallyOfType f).mp hf) V U e)

/-- Being locally of finite presentation can be checked on all pairs of affine opens, on open
coverings of target and preimages, or on affine such coverings. -/
@[stacks 01TQ "equivalence of (1), (2), (3) and (4)"]
theorem locallyOfFinitePresentation_tfae (f : X ⟶ S) :
    List.TFAE [
      LocallyOfFinitePresentation f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.FinitePresentation,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, LocallyOfFinitePresentation (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          (f.appLE V U e).hom.FinitePresentation] := by
  simp only [locallyOfFinitePresentation_iff_locallyOfType]
  exact locallyOfType_tfae RingHom.FinitePresentation.stacksPropertyIsLocal f

/-- The whole statement: the four characterizations of being locally of finite presentation
agree, and being locally of finite presentation passes to restrictions to open subschemes. -/
@[stacks 01TQ]
theorem locallyOfFinitePresentation_tfae_and_resLE (f : X ⟶ S) :
    List.TFAE [
      LocallyOfFinitePresentation f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.FinitePresentation,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, LocallyOfFinitePresentation (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          (f.appLE V U e).hom.FinitePresentation] ∧
    (LocallyOfFinitePresentation f → ∀ (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V),
      LocallyOfFinitePresentation (f.resLE V U e)) :=
  ⟨locallyOfFinitePresentation_tfae f, fun hf U V e ↦ locallyOfFinitePresentation_resLE hf V U e⟩

end AlgebraicGeometry
