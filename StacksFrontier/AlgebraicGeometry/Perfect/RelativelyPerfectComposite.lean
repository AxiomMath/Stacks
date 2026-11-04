module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso

/-!
# Relative perfectness along a composite

Let `g : X ⟶ S` and `f : Y ⟶ X` be flat and locally of finite presentation, let `K ∈ D(𝒪_X)` be
`S`-perfect and `M ∈ D(𝒪_Y)` be `X`-perfect (Stacks 0DI0). Then `M ⊗ᴸ_{𝒪_Y} Lf^*K` is `S`-perfect
for the composite `f ≫ g`.

Pseudo-coherence is preserved by derived pullback and by derived tensor products. At a point `y` of
`Y` lying over `x` of `X` lying over `s` of `S`, the stalk of `M ⊗ᴸ_{𝒪_Y} Lf^*K` is
`M_y ⊗ᴸ_{𝒪_{Y,y}} (𝒪_{Y,y} ⊗ᴸ_{𝒪_{X,x}} K_x) = M_y ⊗ᴸ_{𝒪_{X,x}} K_x` read over `𝒪_{X,x}`, whose Tor
amplitude over `𝒪_{S,s}` is bounded by the sum of the Tor amplitude of `M_y` over `𝒪_{X,x}` and the
Tor amplitude of `K_x` over `𝒪_{S,s}` (Stacks 0B66).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.RelativeStalkTensorBound`: the pointwise bound on the Tor amplitude
  of the derived stalk of `M ⊗ᴸ_{𝒪_Y} Lf^*K` over the local rings of `S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_comp_derivedTensor_of_stalkBound`: the
  reduction of the Tor clause to the pointwise bound.

## References

* [Stacks Project, Lemma 48.28.11 (Tag 0E30)](https://stacks.math.columbia.edu/tag/0E30)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 15.66.13 (Tag 0B66)](https://stacks.math.columbia.edu/tag/0B66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

/-- Restriction of scalars along a ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_0E30
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along a ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_0E30
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along a ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_0E30
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

attribute [local instance] commRing_stalk_structure_at

variable {X Y S : Scheme.{u}}

/-- **The pointwise bound for a composite.** At every point `y` of `Y`, if the derived stalk of
`M` read over `𝒪_{X, f y}` has Tor amplitude in `[c, d]` and the derived stalk of `K` at `f y`
read over `𝒪_{S, g (f y)}` has Tor amplitude in `[a, b]`, then the derived stalk of
`M ⊗ᴸ Lf^*K` at `y` read over `𝒪_{S, (f ≫ g) y}` has Tor amplitude in `[a + c, b + d]`. -/
def RelativeStalkTensorBound (g : X ⟶ S) (f : Y ⟶ X)
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Y.toRingedSpace.sheaf) : Prop :=
  ∀ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (M : DerivedCategory (OXMod.{u, u} Y.toRingedSpace)) (y : Y) (a b c d : ℤ),
    HasTorAmplitudeCanonical (ToType (X.presheaf.stalk (f.base y)))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv Y.presheaf y).symm.toRingHom.comp
            (f.stalkMap y).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} Y.toRingedSpace) y).mapDerivedCategory.obj M)) c d →
    HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (g.base (f.base y))))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X.presheaf (f.base y)).symm.toRingHom.comp
            (g.stalkMap (f.base y)).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) (f.base y)).mapDerivedCategory.obj K)) a b →
    HasTorAmplitudeCanonical (ToType (S.presheaf.stalk ((f ≫ g).base y)))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv Y.presheaf y).symm.toRingHom.comp
            ((f ≫ g).stalkMap y).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} Y.toRingedSpace) y).mapDerivedCategory.obj
            ((T.tensor.obj M).obj ((derivedPullback f.toLRSHom.toShHom).obj K)))) (a + c) (b + d)

/-- **Relative perfectness along a composite, from the pointwise bound.** If `K` is `S`-perfect
for `g` and `M` is `X`-perfect for `f`, and the pointwise bound `RelativeStalkTensorBound` holds,
then `M ⊗ᴸ Lf^*K` is `S`-perfect for `f ≫ g`. -/
theorem isPerfectRelativeTo_comp_derivedTensor_of_stalkBound (g : X ⟶ S) (f : Y ⟶ X) [Flat g]
    [LocallyOfFinitePresentation g] [Flat f] [LocallyOfFinitePresentation f]
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Y.toRingedSpace.sheaf)
    (hT : RelativeStalkTensorBound g f T)
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (M : DerivedCategory (OXMod.{u, u} Y.toRingedSpace))
    (hK : g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K)
    (hM : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) M) :
    (f ≫ g).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((T.tensor.obj M).obj ((derivedPullback f.toLRSHom.toShHom).obj K)) := by
  refine ⟨RingedSpace.isPseudoCoherent_derivedTensorProduct Y.toRingedSpace T M _ hM.1
    (Scheme.Hom.isPseudoCoherent_derivedPullback f K hK.1), ?_⟩
  obtain ⟨I, U, hU, hKU⟩ := (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover
    g _ (isGenuineRelativeTensorFamily_canonical g) K).1 hK.2
  obtain ⟨J, V, hV, hMV⟩ := (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover
    f _ (isGenuineRelativeTensorFamily_canonical f) M).1 hM.2
  refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover (f ≫ g) _
    (isGenuineRelativeTensorFamily_canonical (f ≫ g)) _).2
    ⟨I × J, fun ij => (⟨f.base ⁻¹' (U ij.1).1, (U ij.1).2.preimage f.base.hom.continuous⟩ :
      Opens Y) ⊓ V ij.2, ?_, fun ij => ?_⟩
  · refine top_unique fun y _ => ?_
    have hxU : f.base y ∈ iSup U := by rw [hU]; trivial
    have hyV : y ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hyV
    exact Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  · obtain ⟨a, b, hab⟩ := hKU ij.1
    obtain ⟨c, d, hcd⟩ := hMV ij.2
    refine ⟨a + c, b + d, fun y hy =>
      (hasTorAmplitudeCanonical_derivedStalk_relative_iff (f ≫ g) y _ _ _).2 ?_⟩
    exact hT K M y a b c d ((hasTorAmplitudeCanonical_derivedStalk_relative_iff f y M c d).1
      (hcd y hy.2)) ((hasTorAmplitudeCanonical_derivedStalk_relative_iff g (f.base y) K a b).1
      (hab (f.base y) hy.1))

end AlgebraicGeometry.Scheme.Hom

end
