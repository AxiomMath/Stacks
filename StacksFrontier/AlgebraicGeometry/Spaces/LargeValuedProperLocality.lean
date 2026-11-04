module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProper

/-!
# Locality at the target of properness of large-valued algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Properness of a morphism of algebraic
spaces over `S` with values in `Type (max w u)` is the conjunction of three conditions —
separated, of finite type and universally closed — so it is local at the target for a
precoverage of those algebraic spaces as soon as the three conditions are. Being of finite type
is likewise local at the target as soon as being locally of finite type and being quasi-compact
are.

Properness is unchanged by precomposing with an isomorphism of the source, and the source of a
morphism representable by algebraic spaces whose target is isomorphic to a universe-lifted Yoneda
presheaf is an algebraic space.

## Main results

* `AlgebraicGeometry.Space.finiteTypePropertyULift_eq_inf`: being of finite type is being
  locally of finite type and quasi-compact.
* `AlgebraicGeometry.Space.finiteTypePropertyULift_isLocalAtTarget`: being of finite type is
  local at the target as soon as being locally of finite type and being quasi-compact are.
* `AlgebraicGeometry.Space.properPropertyULift_isLocalAtTarget`: being proper is local at the
  target as soon as being separated, being of finite type and being universally closed are.
* `AlgebraicGeometry.Space.isProperULift_precomp`: properness is unchanged by precomposing
  with an isomorphism of presheaves.
* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_isRepresentable_uliftYoneda`: the source of
  a morphism representable by algebraic spaces whose target is isomorphic to a universe-lifted
  Yoneda presheaf is an algebraic space.

## References

* [Stacks Project, Tag 02YS](https://stacks.math.columbia.edu/tag/02YS)
* [Stacks Project, Tag 041U](https://stacks.math.columbia.edu/tag/041U)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The finite type decomposition and the two locality statements -/

/-- Being of finite type is being locally of finite type and quasi-compact, as an equality of
properties of morphisms of algebraic spaces over `S` with values in `Type (max w u)`. -/
theorem finiteTypePropertyULift_eq_inf :
    finiteTypePropertyULift.{w} B S hS =
      locallyOfFiniteTypePropertyULift.{w} B S hS ⊓ quasiCompactPropertyULift.{w} B S hS :=
  rfl

/-- Being of finite type is local at the target for a precoverage of the algebraic spaces over
`S` with values in `Type (max w u)` as soon as being locally of finite type and being
quasi-compact are. -/
theorem finiteTypePropertyULift_isLocalAtTarget
    {K : Precoverage (AlgebraicSpacesULift.{w} B S hS)}
    (hlft : (locallyOfFiniteTypePropertyULift.{w} B S hS).IsLocalAtTarget K)
    (hqc : (quasiCompactPropertyULift.{w} B S hS).IsLocalAtTarget K) :
    (finiteTypePropertyULift.{w} B S hS).IsLocalAtTarget K := by
  rw [finiteTypePropertyULift_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- Being proper is local at the target for a precoverage of the algebraic spaces over `S` with
values in `Type (max w u)` as soon as being separated, being of finite type and being
universally closed are. -/
theorem properPropertyULift_isLocalAtTarget
    {K : Precoverage (AlgebraicSpacesULift.{w} B S hS)}
    (hsep : (separatedPropertyULift.{w} B S hS).IsLocalAtTarget K)
    (hft : (finiteTypePropertyULift.{w} B S hS).IsLocalAtTarget K)
    (huc : (universallyClosedPropertyULift.{w} B S hS).IsLocalAtTarget K) :
    (properPropertyULift.{w} B S hS).IsLocalAtTarget K := by
  rw [properPropertyULift_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-! ### Transport along an isomorphism -/

/-- Properness of a morphism of algebraic spaces over `S` with values in `Type (max w u)` is
unchanged by precomposing with an isomorphism of presheaves. -/
theorem isProperULift_precomp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G)
    (f : G ⟶ K) (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    (hG : IsAlgebraicSpaceULift.{w} B S hS G) (hK : IsAlgebraicSpaceULift.{w} B S hS K)
    (hf : IsProperULift.{w} B S hS f) : IsProperULift.{w} B S hS (e.hom ≫ f) :=
  MorphismProperty.RespectsIso.precomp (properPropertyULift.{w} B S hS)
    (ObjectProperty.isoMk
      (P := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u) ↦
        IsAlgebraicSpaceULift.{w} B S hS F)
      (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) e).hom
    (ObjectProperty.homMk f :
      (⟨G, hG⟩ : AlgebraicSpacesULift.{w} B S hS) ⟶ (⟨K, hK⟩ : AlgebraicSpacesULift.{w} B S hS))
    hf

/-- The source of a morphism of presheaves with values in `Type (max w u)` which is
representable by algebraic spaces and whose target is isomorphic to the universe-lifted Yoneda
presheaf of an object of the big fppf site of `S` is an algebraic space over `S`. -/
@[stacks 02YS "representable target, arbitrary value universe"]
theorem isAlgebraicSpaceULift_of_isRepresentable_uliftYoneda
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {U : BigFppfOver B S hS} (a : F ⟶ G)
    (e : G ≅ (uliftYoneda.{w}).obj U)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a) :
    IsAlgebraicSpaceULift.{w} B S hS F :=
  isAlgebraicSpaceULift_of_iso B S hS
    (IsPullback.of_vert_isIso ⟨by simp⟩ : IsPullback (a ≫ e.hom) (𝟙 F) e.inv a).isoPullback.symm
    (ha U e.inv)

end AlgebraicGeometry.Space

end
