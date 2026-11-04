module

public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnit
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Pullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Eventual vanishing of the cohomology of the high twists over an affine Noetherian base

Let `f : X ⟶ U` be a proper morphism of schemes to an affine locally Noetherian scheme and `ℒ`
an ample invertible `𝒪_X`-module.  Then there is a `d₀` with `H^p(X, ℒ^{⊗ d}) = 0` for every
`d ≥ d₀` and every `p > 0`, the cohomology being the right derived functors of the global
sections of `𝒪_X`-modules.

This is clause (4) of [Stacks, Tag 0B5T], `exists_isZero_Hgroup_tensorPowTwist`, at the coherent
module `𝒪_X`, with the base `U` replaced by `Spec Γ(U, 𝒪_U)` and the cohomology groups
`Hgroup` read as derived global sections through [Stacks, Tag 01F1].

## Main results

* `Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_rightDerived_tensorPowModule`:
  the statement above.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample

universe u

namespace Stacks.AlgebraicGeometry.ProperAmpleCohomology

/-- **The high twists of an ample invertible module on a scheme proper over an affine Noetherian
scheme have no higher cohomology.**  For a proper `f : X ⟶ U` with `U` affine and locally
Noetherian and an ample invertible `ℒ` on `X`, there is a `d₀` with `H^p(X, ℒ^{⊗ d}) = 0` for all
`d ≥ d₀` and `p > 0`. -/
theorem exists_isZero_rightDerived_tensorPowModule {X U : Scheme.{u}} (f : X ⟶ U)
    [IsProper f] [IsAffine U] [IsLocallyNoetherian U] (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
        (tensorPowModule X L (d : ℤ))) := by
  have : IsNoetherianRing Γ(U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : _root_.SheafOfModules.IsCoherent (unitModule X) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X
  obtain ⟨d₀, hd₀⟩ := exists_isZero_Hgroup_tensorPowTwist (R := Γ(U, ⊤)) (f ≫ U.isoSpec.hom)
    (unitModule X) L hL
  refine ⟨d₀, fun d p hd hp => ?_⟩
  have h := (hd₀ d p hd hp).of_iso
    ((_root_.Hfunctor X.ringCatSheaf ⊤ p).mapIso
      (Stacks.Algebraization.unitTensorModulesIso X (tensorPowModule X L (d : ℤ)))).symm
  exact (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    X.ringCatSheaf ⊤ p _).2 h

open RingedSpaceModuleAdjunction in
/-- **The pullback of the high twists of an ample module along an affine morphism has no higher
cohomology over an affine Noetherian base.**  Let `g : T ⟶ Z` be an affine morphism, `ℒ` an ample
invertible `𝒪_Z`-module and `T` proper over an affine locally Noetherian scheme.  Then there is
a `d₀` with `H^p(T, g^*(ℒ^{⊗ d})) = 0` for all `d ≥ d₀` and `p > 0`.

The pullback `g^*ℒ` is ample, [Stacks, Tag 0892] part (2), an affine morphism being quasi-affine,
and `g^*(ℒ^{⊗ d}) = (g^*ℒ)^{⊗ d}`; so this is `exists_isZero_rightDerived_tensorPowModule` for
`g^*ℒ`. -/
theorem exists_isZero_rightDerived_pullback_tensorPowModule {T Z U : Scheme.{u}} (g : T ⟶ Z)
    [IsAffineHom g] (f : T ⟶ U) [IsProper f] [IsAffine U] [IsLocallyNoetherian U]
    (L : Z.Modules) [IsInvertibleModule Z L] (hL : IsAmple Z L) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived p).obj
        ((Scheme.Modules.pullback g).obj (tensorPowModule Z L (d : ℤ)))) := by
  have hLT : IsAmple T ((modulePullback g.toLRSHom.toShHom).obj L) :=
    Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom g L hL
  obtain ⟨d₀, hd₀⟩ := exists_isZero_rightDerived_tensorPowModule f
    ((modulePullback g.toLRSHom.toShHom).obj L) hLT
  refine ⟨d₀, fun d p hd hp => (hd₀ d p hd hp).of_iso ?_⟩
  exact ((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived p).mapIso
    ((Stacks.ProjectiveBundleQuotients.pullbackIso g).app _ ≪≫
      Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso g L d)

end Stacks.AlgebraicGeometry.ProperAmpleCohomology

end
