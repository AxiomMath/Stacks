module

public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-!
# The quasi-inverse of affine direct image is exact

Let `f : X ⟶ S` be an affine morphism of schemes and let `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)` be the
morphism of ringed spaces whose map of structure sheaves is the identity of `f_* 𝒪_X`. Then `g`
is flat: at `x ∈ X` with image `s`, choosing an affine open `U ∋ s` with `B = Γ(X, f⁻¹U)`, the
stalk `(f_* 𝒪_X)_s` is the localization of `B` at the image of the prime of `s`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`) and `𝒪_{X,x}` is the
localization of `B` at the prime of `x`, so the stalk map is a localization, hence flat.

Pullback of modules along a flat morphism of ringed spaces is exact ([Stacks, Tag 02N4]), and the
quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of [Stacks, Tag 01SB] is that pullback, both being
left adjoint to direct image over `f_* 𝒪_X`. This is the flatness of `g` asserted in the proof of
[Stacks, Tag 0AVW].

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isFlat_pushforwardRingedMap`: `g` is flat.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModulesIsoModulePullback`: the
  quasi-inverse of Tag 01SB is the pullback of modules along `g`.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.preservesFiniteLimits_pullbackModules`: the
  quasi-inverse is left exact.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.DerivedGlueing RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.AffineQcohEquivalence

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For an affine morphism `f : X ⟶ S`, the morphism of ringed spaces
`(X, 𝒪_X) ⟶ (S, f_* 𝒪_X)` whose map of structure sheaves is the identity is flat. -/
theorem isFlat_pushforwardRingedMap [IsAffineHom f] :
    AlgebraicGeometry.IsFlat (pushforwardRingedMap (X := X.toRingedSpace) f.base) := by
  intro x
  obtain ⟨U, hU, hsU, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show f.base x ∈ (⊤ : S.Opens) from trivial)
  have hU : IsAffineOpen U := hU
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hxV : x ∈ f ⁻¹ᵁ U := hsU
  let _ : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let _ : Algebra Γ(X, f ⁻¹ᵁ U) ((f.base _* X.presheaf).stalk (f.base x)) :=
    ((f.base _* X.presheaf).germ U (f.base x) hsU).hom.toAlgebra
  let _ : Algebra Γ(X, f ⁻¹ᵁ U) (X.presheaf.stalk x) :=
    (X.presheaf.germ (f ⁻¹ᵁ U) x hxV).hom.toAlgebra
  let φ : (f.base _* X.presheaf).stalk (f.base x) ⟶ X.presheaf.stalk x :=
    (pushforwardRingedMap (X := X.toRingedSpace) f.base).hom.stalkMap x
  let _ : Algebra ((f.base _* X.presheaf).stalk (f.base x)) (X.presheaf.stalk x) := φ.hom.toAlgebra
  have h1 := hU.isLocalization_pushforwardStalk f hsU
  have h2 : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  have htower : IsScalarTower Γ(X, f ⁻¹ᵁ U) ((f.base _* X.presheaf).stalk (f.base x))
      (X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change (X.presheaf.germ (f ⁻¹ᵁ U) x hxV).hom = (φ.hom).comp
      ((f.base _* X.presheaf).germ U (f.base x) hsU).hom
    rw [← CommRingCat.hom_comp]
    congr 1
    exact (PresheafedSpace.stalkMap_germ (pushforwardRingedMap (X := X.toRingedSpace) f.base).hom
      U x hsU).trans (Category.id_comp _) |>.symm
  have hle : Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U)
      (hU.primeIdealOf ⟨f.base x, hsU⟩).asIdeal.primeCompl ≤
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    refine (hV.mem_primeCompl_iff_mem_basicOpen hxV _).mpr ?_
    change x ∈ X.basicOpen (f.app U r)
    rw [← Scheme.preimage_basicOpen]
    exact (hU.mem_primeCompl_iff_mem_basicOpen hsU r).mp hr
  have := IsLocalization.isLocalization_of_submonoid_le
    ((f.base _* X.presheaf).stalk (f.base x)) (X.presheaf.stalk x) _ _ hle
  have hflat : Module.Flat ((f.base _* X.presheaf).stalk (f.base x)) (X.presheaf.stalk x) :=
    IsLocalization.flat (X.presheaf.stalk x)
    (((hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).map
      (algebraMap Γ(X, f ⁻¹ᵁ U) ((f.base _* X.presheaf).stalk (f.base x))))
  exact hflat

/-- The quasi-inverse of [Stacks, Tag 01SB] is the pullback of modules along the morphism of ringed
spaces `(X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`. -/
def pullbackModulesIsoModulePullback :
    pullbackModules f ≅ modulePullback (pushforwardRingedMap (X := X.toRingedSpace) f.base) :=
  (pullbackPushforwardAdjunction f).leftAdjointUniq
    (modulePullbackPushforwardAdjunction (pushforwardRingedMap (X := X.toRingedSpace) f.base))

/-- **The quasi-inverse of [Stacks, Tag 01SB] is left exact** for an affine morphism. -/
instance preservesFiniteLimits_pullbackModules [IsAffineHom f] :
    PreservesFiniteLimits (pullbackModules f) :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (pullbackModulesIsoModulePullback f).symm
    (preservesFiniteLimits_modulePullback_of_isFlat
      (pushforwardRingedMap (X := X.toRingedSpace) f.base) (isFlat_pushforwardRingedMap f))

end Stacks.AlgebraicGeometry.AffineQcohEquivalence

end
