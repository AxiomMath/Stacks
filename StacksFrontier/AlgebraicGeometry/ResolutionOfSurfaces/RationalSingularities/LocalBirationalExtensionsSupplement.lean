module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LocalBirationalExtensions
public import StacksFrontier.AlgebraicGeometry.Morphisms.ModificationProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
import StacksCore.Tactic.StacksAttribute

/-!
# Further results on `LocalBirationalExtensions`

Results about the objects of the module `RationalSingularities.LocalBirationalExtensions` that
need imports beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open GlueingNearPoint

/-! ### Normality of the spread-out scheme -/

/-- An open subscheme of a normal scheme is normal: its inclusion is a flat preimmersion. -/
private theorem isNormal_toScheme {X : Scheme.{u}} [IsNormal X] (U : X.Opens) :
    IsNormal U.toScheme :=
  isNormal_of_flat_preimmersion U.ι

/-- Normality of a scheme passes to the local ring at the image of a point where the stalk map
of a morphism from it is an isomorphism. -/
private theorem isNormalRing_stalk_of_isIso_stalkMap {X Y : Scheme.{u}} [IsNormal X] (f : X ⟶ Y)
    (w : X) [IsIso (f.stalkMap w)] : IsNormalRing (Y.presheaf.stalk (f w)) :=
  IsNormalRing.congr (asIso (f.stalkMap w)).commRingCatIsoToRingEquiv.symm
    ((isNormal_iff_stalk_isNormalRing _).mp ‹_› w)

/-- **Step 4 of the source's proof of [Stacks, Tag 0BG0]: the spread-out scheme is normal.**
Let `x` be a closed point of a normal scheme `X` and let `g : X' ⟶ X` be an isomorphism over
`X ∖ {x}` whose base change along `Spec 𝒪_{X, x} ⟶ X` is a normal scheme `Y`.  Then `X'` is
normal.

This is the source's assertion that the local ring of `X'` at a point `x'` is the local ring of
`X` at `g x'` when `g x' ≠ x`, and the local ring of `Y` at a corresponding point when
`g x' = x`.  Away from `x` this is the hypothesis that `g` restricts to an isomorphism; above `x`
it is `AlgebraicGeometry.exists_point_pullback_fromSpecStalk_isIso_stalkMap`, which produces, for
every point of `X'` over `x`, a point of the base change with the same local ring, the base
change of `Spec 𝒪_{X, x} ⟶ X` being again a flat preimmersion. -/
theorem isNormal_of_isPullback_fromSpecStalk {X : Scheme.{u}} [IsNormal X] {x : X}
    (hx : IsClosed ({x} : Set X)) {X' Y : Scheme.{u}} {g : X' ⟶ X}
    {p : Y ⟶ Spec (X.presheaf.stalk x)} {q : Y ⟶ X'} [IsNormal Y]
    (hsq : IsPullback q p g (X.fromSpecStalk x))
    (hg : IsFinitePresentationAway (puncturedOpen hx) (Over.mk g)) :
    IsNormal X' := by
  rw [isNormal_iff_stalk_isNormalRing]
  intro x'
  by_cases hgx : g.base x' = x
  · -- Above `x`: the local ring of `X'` at `x'` is a local ring of the base change `Y`.
    have _ : IsNormal (pullback g (X.fromSpecStalk x)) := isNormal_of_iso hsq.isoPullback.symm
    obtain ⟨w, hw, _⟩ := exists_point_pullback_fromSpecStalk_isIso_stalkMap g x x' hgx
    rw [← hw]
    exact isNormalRing_stalk_of_isIso_stalkMap (pullback.fst g (X.fromSpecStalk x)) w
  · -- Away from `x`: `g` restricts to an isomorphism onto the open complement of `x`.
    have hmem : x' ∈ g ⁻¹ᵁ puncturedOpen hx := by
      simpa [puncturedOpen] using hgx
    have _ : IsIso (pullback.snd g (puncturedOpen hx).ι) := hg.2
    have _ : IsIso (g ∣_ puncturedOpen hx) := by
      rw [morphismRestrict]; infer_instance
    have _ : IsNormal (puncturedOpen hx).toScheme := isNormal_toScheme _
    have _ : IsNormal (g ⁻¹ᵁ puncturedOpen hx).toScheme :=
      isNormal_of_iso (asIso (g ∣_ puncturedOpen hx))
    have _ : IsIso ((g ⁻¹ᵁ puncturedOpen hx).ι.stalkMap ⟨x', hmem⟩) :=
      isIso_stalkMap_of_flat_isPreimmersion _ _
    exact isNormalRing_stalk_of_isIso_stalkMap (g ⁻¹ᵁ puncturedOpen hx).ι ⟨x', hmem⟩

end AlgebraicGeometry

end
