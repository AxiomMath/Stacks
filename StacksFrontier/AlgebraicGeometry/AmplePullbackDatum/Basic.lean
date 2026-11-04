module

public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleRoute.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.PullbackExtension.Basic
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Consumer

/-!
# Stacks Tag 0892 part (1): the eventual affine datum, proved

Part (1) of [Stacks, Tag 0892]: if `L` is ample relative to `f : X ⟶ S` and `M` is an ample
invertible `𝒪_S`-module, then `L ⊗ f^* M ^⊗ a` is ample for every sufficiently large `a`.

`StacksFrontier/AlgebraicGeometry/AmplePullbackPart1/Basic.lean` reduces part (1) to one pointwise
datum, `Stacks.AmplePullbackPart1.EventualAffineDatum`, and spells out under "The one missing
input, precisely" the argument that produces it, whose one nontrivial input is [Stacks, Tag 01PW]
for a module-valued coefficient. **That input is available**, as
`Stacks.Tag087SPullbackExtension.exists_tensorPow_tensorSection_pullbackModule`, with no ampleness
of `f^* M` anywhere. This file writes the argument down, so the datum is a theorem and part (1) is
unconditional.

## Main results

* `Stacks.AmplePullbackDatum.exists_pos_section_affine_nonvanishingOpenOn`: ampleness of `L` on an
  open subscheme `W ⊆ X` produces, through a given point of `W`, a section of `L ^⊗ n` over `W`
  with `n ≥ 1` whose nonvanishing open is affine. This is
  `Stacks.AmpleFamilyRelativeAmple.exists_section_affine_nonvanishingOpenOn_of_isAmple_restrict`
  with the positivity of the exponent kept, which the assembly below needs.
* `Stacks.AmplePullbackDatum.eventualAffineDatum`: **the pointwise datum, with no premise.**
* `Stacks.AmplePullbackDatum.eventualAffineDatumUniform`: the same, in the quantified form
  `Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` that
  `StacksFrontier/AlgebraicGeometry/AmpleRoute/Basic.lean` carries as a hypothesis.
* `Stacks.AmplePullbackDatum.exists_threshold_isAmple`: **part (1) of [Stacks, Tag 0892].**

## The argument

Fix `x : X`. `Stacks.AmplePullbackPart1.exists_isAmple_preimage_of_isRelativelyAmple` gives
`m ≥ 1`, a global section `t` of `M ^⊗ m` with `S_t` affine containing `f x`, and — writing
`σ := f^* t`, a global section of `(f^* M) ^⊗ m`, and `W := X_σ = f⁻¹(S_t)` — ampleness of `L`
restricted to `W`.

Ampleness of `L|_W` gives `n ≥ 1` and a section `u` of `L ^⊗ n` over `W` whose nonvanishing open
`V ⊆ W` is affine and contains `x`. Replace `u` by its `m`-th power
(`Stacks.SectionPowerOverOpen.powSectionOn`), a section of `L ^⊗ (nm)` over `W` with the *same*
nonvanishing open `V`. **That power is what removes the divisibility condition the source's own
proof carries**: the twisting degrees available below are the multiples of `m`, so the degree `k`
of the `L`-factor has to be one too.

[Stacks, Tag 01PW] at `F = L ^⊗ (nm)`, in the form
`Stacks.TensorSectionProduct.exists_tensorPow_tensorSection_nonvanishingLocus` instantiated at
`f^* M` by `Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_pullbackModule_of_isAmple`,
then produces a degree `p = m p'`, a global section `σ'` of `(f^* M) ^⊗ p` with `X_{σ'} = W`, and a
global section `τ` of `L ^⊗ (nm) ⊗ (f^* M) ^⊗ p` whose nonvanishing locus *inside `W`* is cut out
by the nonvanishing of the power of `u` alone — that is, `X_τ ∩ W = V`.

`X_τ` itself need not lie in `W`: Tag 01PW pins `τ` only on `W`. The final section is therefore
`τ ⊗ σ ^ b`, whose nonvanishing locus is `X_τ ∩ X_{σ ^ b} = X_τ ∩ W = V` exactly, by
`Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection` and
`Stacks.SectionPowerOverOpen.nonvanishingLocus_powSectionOn_top`. Its degree in `f^* M` is
`p + mb = m (p' + b)`, so with `k = nm` the exponent `a` of the datum is solved by `an = p' + b`,
which has a solution with `b ≥ 1` for every `a ≥ p' + 1` because `n ≥ 1`. The threshold of the
datum is `p' + 1`, and `Stacks.AmplePullbackDatum.splitIso` is the regrouping
`(L ^⊗ k ⊗ N ^⊗ p) ⊗ N ^⊗ (mb) ≅ L ^⊗ k ⊗ N ^⊗ (ak)` that reads the result in the module
`Stacks.AmplePullbackPart1.tensorPullbackSplitModule` the datum asks about.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory Stacks.ModuleStalk
open Stacks.AmpleEventualGeneration (tensorPowAdd)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.NonvanishingLocusRestrict (mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection
  nonvanishingLocusOn mem_nonvanishingLocusOn_iff restrictSection_sectionOfRestrictGlobalSection)
open Stacks.SectionPowerOpen (nonvanishingOpenOn)
open Stacks.SectionPowerOverOpen (powSectionOn)
open Stacks.SectionTensorFormula (tensorSection)

universe u

namespace Stacks.AmplePullbackDatum

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X S : Scheme.{u}}

/-! ### The regrouping isomorphism -/

/-- **`(F ⊗ N ^⊗ p) ⊗ N ^⊗ q ≅ F ⊗ N ^⊗ d` for `p + q = d`**, read with the second tensor product
in the `Stacks.RelativeVeryAmple.tensorModules` spelling that
`Stacks.AmplePullbackPart1.tensorPullbackSplitModule` uses.

The associator moves the bracket, `Stacks.AmpleEventualGeneration.tensorPowAdd` adds the two
exponents, and `Stacks.AmplePullbackPart1.tensorIsoTensorModules` changes the spelling of the
outer tensor product. -/
def splitIso (N : X.Modules) [IsInvertibleModule X N] (F : X.Modules) [IsInvertibleModule X F]
    (p q : ℕ) (d : ℤ) (h : (p : ℤ) + (q : ℤ) = d) :
    (((F ⊗ tensorPowModule X N (p : ℤ)) ⊗ tensorPowModule X N (q : ℤ)) : X.Modules) ≅
      Stacks.RelativeVeryAmple.tensorModules X F (tensorPowModule X N d) :=
  α_ F _ _ ≪≫ whiskerLeftIso F (tensorPowAdd h) ≪≫
    Stacks.AmplePullbackPart1.tensorIsoTensorModules X F (tensorPowModule X N d)

/-! ### A section over an open with a positive exponent -/

/-- **A section of a *positive* tensor power of `L` over an open `W`, with affine nonvanishing
locus, from ampleness of the restriction of `L` to `W`.**

This is the lemma
`Stacks.AmpleFamilyRelativeAmple.exists_section_affine_nonvanishingOpenOn_of_isAmple_restrict`
with the exponent's positivity retained. The assembly below needs it: the degree of the
`L`-factor of the datum's module is the exponent multiplied by `m`, and the datum asks for a
positive one. -/
theorem exists_pos_section_affine_nonvanishingOpenOn
    (L : X.Modules) [IsInvertibleModule X L] (W : X.Opens)
    (hamp : IsAmple W.toScheme (pullbackModule W.ι L)) (x : X) (hx : x ∈ W) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ t : Γ(tensorPowModule X L (m : ℤ), W),
      x ∈ nonvanishingOpenOn (tensorPowModule X L (m : ℤ)) W t ∧
        IsAffineOpen (nonvanishingOpenOn (tensorPowModule X L (m : ℤ)) W t) := by
  obtain ⟨m, hm, σ, hσaff, hxσ⟩ :=
    IsAmple.exists_affine_nonvanishingOpen W.toScheme _ hamp ⟨x, hx⟩
  obtain ⟨σ', hσ'def⟩ :
      ∃ σ' : Γ(pullbackModule W.ι (tensorPowModule X L (m : ℤ)), ⊤),
        σ' = ConcreteCategory.hom (Scheme.Modules.Hom.app
          (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso W.ι L m).symm.hom ⊤) σ :=
    ⟨_, rfl⟩
  have hEq : Stacks.NonvanishingOpen.nonvanishingOpen W.toScheme
      (pullbackModule W.ι (tensorPowModule X L (m : ℤ))) σ' =
      powNonvanishingOpen W.toScheme (pullbackModule W.ι L) m σ := by
    refine Opens.ext ?_
    rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, coe_powNonvanishingOpen, hσ'def]
    exact nonvanishingLocus_congr
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso W.ι L m).symm σ
  refine ⟨m, hm, Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection W
    (tensorPowModule X L (m : ℤ)) σ', ?_, ?_⟩
  · refine (mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection W
      (tensorPowModule X L (m : ℤ)) σ' ⟨x, hx⟩).mp ?_
    rw [← Stacks.NonvanishingOpen.coe_nonvanishingOpen, hEq]
    exact hxσ
  · rw [Stacks.SectionPowerOpen.isAffineOpen_nonvanishingOpenOn_iff,
      restrictSection_sectionOfRestrictGlobalSection, hEq]
    exact hσaff

/-! ### The pointwise datum -/

variable (f : X ⟶ S) (L : X.Modules) (M : S.Modules)
  [IsInvertibleModule X L] [IsInvertibleModule S M]

/-- **`Stacks.AmplePullbackPart1.EventualAffineDatum`, with no premise.**

For `L` ample relative to `f : X ⟶ S` and `M` ample on `S`: through every point of `X` there are a
threshold `e` and an affine open `V`, independent of the exponent, such that for every `a ≥ e` some
positive tensor power `L ^⊗ k ⊗ (f^* M) ^⊗ (ak)` carries a global section whose nonvanishing open
is exactly `V`.

This is the datum that `StacksFrontier/AlgebraicGeometry/AmplePullbackPart1/Basic.lean` isolates as
the single residue of part (1) of [Stacks, Tag 0892] and carries as a hypothesis in all three of
its forms. See the module documentation for the argument; the one step that file isolates,
[Stacks, Tag 01PW] for a module-valued coefficient, is
`Stacks.Tag087SPullbackExtension.exists_tensorPow_tensorSection_pullbackModule`, and the two
bookkeeping lemmas it lists beside it are
`Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr` and
`Stacks.SectionPowerOverOpen.powSectionOn`. No ampleness of `f^* M` is used: that is part (2),
which the source deduces *from* part (1). -/
theorem eventualAffineDatum (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (hM : IsAmple S M) :
    Stacks.AmplePullbackPart1.EventualAffineDatum f L M := by
  intro x
  obtain ⟨m, hm, t, -, hfx, hσ, hamp⟩ :=
    Stacks.AmplePullbackPart1.exists_isAmple_preimage_of_isRelativelyAmple f L M hL hM x
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hxW : x ∈ f ⁻¹ᵁ powNonvanishingOpen S M (m' + 1) t := hfx
  rw [← hσ] at hxW hamp
  set N := pullbackModule f M with hNdef
  set σ₀ := Stacks.NonvanishingPullback.pullbackPowSection f M (m' + 1) t with hσ₀def
  set W := powNonvanishingOpen X N (m' + 1) σ₀ with hWdef
  obtain ⟨n, hn, u, hxu, haffu⟩ := exists_pos_section_affine_nonvanishingOpenOn L W hamp x hxW
  have hukV : nonvanishingOpenOn (tensorPowModule X L ((n * (m' + 1) : ℕ) : ℤ)) W
        (powSectionOn L n u m') =
      nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) W u :=
    Stacks.SectionPowerOverOpen.nonvanishingOpenOn_powSectionOn L n u m'
  have : CompactSpace X := Stacks.AmplePullbackPart1.compactSpace_of_isAmple f L M hL hM
  have : QuasiSeparatedSpace X :=
    Stacks.Tag087SPullbackExtension.quasiSeparatedSpace_of_isRelativelyAmple f L M hL hM
  have : (tensorPowModule X L ((n * (m' + 1) : ℕ) : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L _
  obtain ⟨p, σ', τ, hdvd, hWp, hτ⟩ :=
    Stacks.TensorSectionProduct.exists_tensorPow_tensorSection_nonvanishingLocus N
      (Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_pullbackModule_of_isAmple f M hM)
      (tensorPowModule X L ((n * (m' + 1) : ℕ) : ℤ)) hm σ₀ (powSectionOn L n u m')
  obtain ⟨p', rfl⟩ := hdvd
  refine ⟨p' + 1, nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) W u, hxu, haffu, ?_⟩
  intro a ha
  have hane : a ≤ a * n := Nat.le_mul_of_pos_right a hn
  obtain ⟨b', hb'⟩ : ∃ b', a * n = p' + (b' + 1) := ⟨a * n - p' - 1, by omega⟩
  have hnat : (m' + 1) * p' + (m' + 1) * (b' + 1) = a * (n * (m' + 1)) := by
    rw [← Nat.mul_add, ← hb']; ring
  have hd : (((m' + 1) * p' : ℕ) : ℤ) + (((m' + 1) * (b' + 1) : ℕ) : ℤ) =
      (a : ℤ) * ((n * (m' + 1) : ℕ) : ℤ) := by exact_mod_cast hnat
  have hσbLoc : nonvanishingLocus (tensorPowModule X N (((m' + 1) * (b' + 1) : ℕ) : ℤ))
        (powSectionOn N (m' + 1) σ₀ b') =
      nonvanishingLocus (tensorPowModule X N ((m' + 1 : ℕ) : ℤ)) σ₀ :=
    Stacks.SectionPowerOverOpen.nonvanishingLocus_powSectionOn_top N (m' + 1) σ₀ b'
  refine ⟨n * (m' + 1), Nat.mul_pos hn (Nat.succ_pos m'),
    (splitIso N (tensorPowModule X L ((n * (m' + 1) : ℕ) : ℤ)) ((m' + 1) * p')
      ((m' + 1) * (b' + 1)) ((a : ℤ) * ((n * (m' + 1) : ℕ) : ℤ)) hd).hom.app ⊤
      (tensorSection _ (tensorPowModule X N (((m' + 1) * (b' + 1) : ℕ) : ℤ)) τ
        (powSectionOn N (m' + 1) σ₀ b')), ?_⟩
  refine Opens.ext ?_
  rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, nonvanishingLocus_congr,
    Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection, hσbLoc]
  have hWcoe : nonvanishingLocus (tensorPowModule X N ((m' + 1 : ℕ) : ℤ)) σ₀ = (W : Set X) := rfl
  rw [hWcoe, ← hukV, Stacks.SectionPowerOpen.coe_nonvanishingOpenOn]
  refine Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · exact (mem_nonvanishingLocusOn_iff _ W hy.2).mpr ((hτ y hy.2).mp hy.1)
  · exact ⟨(hτ y hy.1).mpr ((mem_nonvanishingLocusOn_iff _ W hy.1).mp hy), hy.1⟩

/-- **`Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform`, the quantified form of the datum.**
`StacksFrontier/AlgebraicGeometry/AmpleRoute/Basic.lean` carries this as a hypothesis of
`Stacks.Tag087SAmpleRoute.exists_isAmple_tensorPullbackPowModule` and of its part (2) route for
[Stacks, Tag 087S]; it is `Stacks.AmplePullbackDatum.eventualAffineDatum` with the data
universally quantified and nothing else. -/
theorem eventualAffineDatumUniform : Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform.{u} :=
  fun _ _ f L M _ _ hL hM => eventualAffineDatum f L M hL hM

/-! ### Part (1) of Stacks Tag 0892 -/

/-- **Part (1) of [Stacks, Tag 0892].** For `L` ample relative to `f : X ⟶ S` and `M` an ample
invertible `𝒪_S`-module there is a threshold `n` with `L ⊗ f^* M ^⊗ a` ample on `X` for every
`a ≥ n`.

`Stacks.AmplePullbackPart1.exists_threshold_isAmple` with both of its inputs discharged:
quasi-compactness of `X` by `Stacks.AmplePullbackPart1.compactSpace_of_isAmple`, and the pointwise
datum by `Stacks.AmplePullbackDatum.eventualAffineDatum`. The module is
`Stacks.AmplePullbackPart1.tensorPullbackPowModule`, that is `L ⊗ f^* (M ^⊗ a)`.

The tree's nearest previous statement of part (1),
`Stacks.AmplePullback.exists_isAmple_tensorPullbackPow_of_iso_unitModule`, assumes both
`L ≅ 𝒪_X` and `M ≅ 𝒪_S` and carries no attribute; this statement assumes neither. -/
@[stacks 0892 "part (1)"]
theorem exists_threshold_isAmple (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : IsAmple S M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a →
      IsAmple X (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a) :=
  Stacks.AmplePullbackPart1.exists_threshold_isAmple f L M
    (Stacks.AmplePullbackPart1.compactSpace_of_isAmple f L M hL hM)
    (eventualAffineDatum f L M hL hM)

end Stacks.AmplePullbackDatum

end
