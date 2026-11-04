module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ClosedImmersionKernel
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelComorphism
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelFiniteSupport
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelStepOne
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelStepTwo
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the identity Fourier-Mukai kernel: Tag 0G0E

Let `k` be a field, let `X` be a smooth proper `k`-scheme and let `K` be a perfect object of
`D(𝒪_{X ×_k X})`.  If the Fourier-Mukai functor `Φ_K` induces on `D_perf(𝒪_X)` an endofunctor
isomorphic to the identity, then `K ≅ Δ_*𝒪_X`.  This file completes the third step of the
source's proof and assembles the four steps into [Stacks, Tag 0G0E].

## Main results

* `AlgebraicGeometry.nonempty_derivedPushforwardSingleIso_of_isFinite_subschemeι` —
  `R p_*(𝒦[0]) ≅ (p_*𝒦)[0]` for a module whose scheme-theoretic support is finite over the
  target, `p` being affine there even when it is not affine.
* `Stacks.Duality.nonempty_iso_diagonalFourierMukaiKernel` — **[Stacks, Tag 0G0E]**.

## Implementation notes

*Why the degree-zero pushforward is available.* `pr_2` is not affine, and the library has
`H^0(R f_*(M[0])) ≅ f_*M` only for an affine morphism and for a closed embedding. It is not needed
in that generality: `𝒦` is the direct image along the closed immersion `i` cutting out its
annihilator ideal of a quasi-coherent module `𝒢`
(`Scheme.Modules.exists_isQuasicoherent_isFiniteType_pushforward_annihilatorIdeal`), and `i ≫ pr_2`
is finite by `Stacks.Duality.isFinite_subschemeι_comp_snd`, hence affine. So
`R pr_{2,*}(𝒦[0]) ≅ R pr_{2,*}(R i_*(𝒢[0])) ≅ R(i ≫ pr_2)_*(𝒢[0]) ≅ ((i ≫ pr_2)_*𝒢)[0]` and
`(i ≫ pr_2)_*𝒢 ≅ pr_{2,*}𝒦`.

*The invertibility.*  `Φ_K(𝒪_X[0]) ≅ 𝒪_X[0]` reads `R pr_{2,*}K ≅ 𝒪_X[0]` once
`L pr_1^*𝒪_X[0]` is identified with `𝒪_{X × X}[0]` — `pr_1` is flat, so this is
`AlgebraicGeometry.derivedPullbackSingleIsoOfFlat` followed by
`Stacks.PullbackAlgebra.pullbackUnitIso` — and the structure sheaf in degree zero is the
monoidal unit, `AlgebraicGeometry.dtenLeftUnitIso`.  With the previous paragraph this gives
`(pr_{2,*}𝒦)[0] ≅ 𝒪_X[0]`, hence `pr_{2,*}𝒦 ≅ 𝒪_X` by `H^0`, hence invertibility.

*The assembly.*  Steps 1 and 2 put `K` in the heart, so `K ≅ 𝒦[0]`; step 3 is
[Stacks, Tag 0FZP] at `𝒦` and `pr_2`, whose two hypotheses are the finiteness and the
invertibility above; and step 4 is
`Stacks.Duality.iso_diagonalFourierMukaiKernel_of_exists_section`.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FZP](https://stacks.math.columbia.edu/tag/0FZP)
* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`R p_*(𝒦[0]) ≅ (p_*𝒦)[0]` for a module whose scheme-theoretic support is finite over the
target.**  `p` need not be affine: it is affine on the closed subscheme cut out by the
annihilator ideal of `𝒦`, from which `𝒦` is a direct image. -/
theorem nonempty_derivedPushforwardSingleIso_of_isFinite_subschemeι
    {W Y : Scheme.{u}} (p : W ⟶ Y) (𝒦 : W.Modules) [𝒦.IsQuasicoherent] [𝒦.IsFiniteType]
    [IsFinite ((Scheme.Modules.annihilatorIdeal 𝒦).subschemeι ≫ p)] :
    Nonempty ((derivedPushforward p.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj 𝒦) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward p).obj 𝒦)) := by
  obtain ⟨G, hGqc, hGft, ⟨e⟩⟩ :=
    Scheme.Modules.exists_isQuasicoherent_isFiniteType_pushforward_annihilatorIdeal 𝒦
  refine ⟨(derivedPushforward p.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctor W.Modules 0).mapIso e.symm ≪≫
        (Stacks.Thickenings.derivedPushforwardSingleIso
          (Scheme.Modules.annihilatorIdeal 𝒦).subschemeι.toLRSHom.toShHom
          (Scheme.Modules.annihilatorIdeal 𝒦).subschemeι.isClosedEmbedding G).symm) ≪≫
    (derivedPushforwardCompIso
      (Scheme.Modules.annihilatorIdeal 𝒦).subschemeι.toLRSHom.toShHom
      p.toLRSHom.toShHom).app _ ≪≫
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso
      ((Scheme.Modules.annihilatorIdeal 𝒦).subschemeι ≫ p) 0 G hGqc).symm ≪≫
    (DerivedCategory.singleFunctor Y.Modules 0).mapIso
      (((Scheme.Modules.pushforwardComp
        (Scheme.Modules.annihilatorIdeal 𝒦).subschemeι p).app G).symm ≪≫
        (Scheme.Modules.pushforward p).mapIso e)⟩

end AlgebraicGeometry

namespace Stacks.Duality

open AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

/-- The base `Spec k` and the source `X` of a morphism locally of finite type over a field `k`
are noetherian. -/
private theorem isNoetherian_spec_and_source {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f] :
    IsNoetherian (Spec (CommRingCat.of k)) ∧ IsNoetherian X := by
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  exact ⟨this, isNoetherian_of_locallyOfFiniteType f⟩

/-- `L pr_1^*𝒪_X[0] ≅ 𝒪_{X ×_k X}[0]`: the first projection is flat, so the derived pullback of
the structure sheaf in degree zero is its ordinary pullback in degree zero, which is the
structure sheaf. -/
def derivedPullbackFstUnitIso :
    (dpull (Limits.pullback.fst f f)).obj (derivedUnitObject X) ≅
      derivedUnitObject (Limits.pullback f f) :=
  derivedPullbackSingleIsoOfFlat (Limits.pullback.fst f f)
      (SheafOfModules.unit X.ringCatSheaf) ≪≫
    (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).mapIso
      (Stacks.PullbackAlgebra.pullbackUnitIso
        (Limits.pullback.fst f f).toLRSHom.toShHom)

/-- **`R pr_{2,*}K ≅ 𝒪_X[0]`**: the value of `Φ_K` at the structure sheaf in degree zero, which
the tag's hypothesis identifies with the structure sheaf in degree zero. -/
theorem nonempty_derivedPushforwardSnd_iso_unit
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hΦ : RepresentsIdentityOnPerfect f K) :
    Nonempty ((dpush (Limits.pullback.snd f f)).obj K ≅ derivedUnitObject X) := by
  have hreg : IsRegular X := isRegular_of_smooth_over_field f
  obtain ⟨_, _⟩ := isNoetherian_spec_and_source f
  have hcoh : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hperf : perfectDerivedObjects X (derivedUnitObject X) :=
    perfectDerivedObjects_single_of_coherentObjects hreg ⟨_, hcoh⟩
  refine (nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect f K hΦ).elim fun eId => ?_
  exact ⟨(dpush (Limits.pullback.snd f f)).mapIso
      (((dtenLeftUnitIso (Limits.pullback f f)).app K).symm ≪≫
        (dtenR (Limits.pullback f f) K).mapIso (derivedPullbackFstUnitIso f).symm) ≪≫
    eId.app ⟨_, hperf⟩⟩

/-- **[Stacks, Tag 0G0E].**  Let `k` be a field, let `X` be a smooth proper scheme over `k` and
let `K` be a perfect object of `D(𝒪_{X ×_k X})`.  If the Fourier-Mukai functor
`Φ_K : D_perf(𝒪_X) ⟶ D_perf(𝒪_X)` of [Stacks, Tag 0FYQ] is isomorphic to the identity functor,
then `K ≅ Δ_*𝒪_X`. -/
@[stacks 0G0E]
theorem nonempty_iso_diagonalFourierMukaiKernel
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K)
    (hΦ : RepresentsIdentityOnPerfect f K) :
    Nonempty (K ≅ diagonalFourierMukaiKernel f) := by
  obtain ⟨_, _⟩ := isNoetherian_spec_and_source f
  have := isNoetherian_pullback_self f
  -- steps 1 and 2: `K` lies in the heart
  have := isGE_zero_of_representsIdentityOnPerfect f K hK hΦ
  have := isLE_zero_of_representsIdentityOnPerfect f K hK hΦ
  obtain ⟨𝒦, ⟨eK⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  have eKh : (DerivedCategory.homologyFunctor (Limits.pullback f f).Modules 0).obj K ≅ 𝒦 :=
    (DerivedCategory.homologyFunctor (Limits.pullback f f).Modules 0).mapIso eK ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Limits.pullback f f).Modules 0).app 𝒦
  have h𝒦coh : 𝒦.IsCoherent :=
    have := isCoherent_homology_of_perfectDerivedObjects f K hK 0
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso eKh.symm
  have : 𝒦.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : 𝒦.IsFiniteType := h𝒦coh.isFiniteType
  -- step 3: the two hypotheses of Tag 0FZP
  have := isFinite_subschemeι_comp_snd f K hΦ 𝒦 eK
  obtain ⟨ePush⟩ := nonempty_derivedPushforwardSingleIso_of_isFinite_subschemeι
    (Limits.pullback.snd f f) 𝒦
  obtain ⟨eUnit⟩ := nonempty_derivedPushforwardSnd_iso_unit f K hΦ
  have eL : (Scheme.Modules.pushforward (Limits.pullback.snd f f)).obj 𝒦 ≅
      SheafOfModules.unit X.ringCatSheaf :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app _).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules 0).mapIso
        (ePush.symm ≪≫ (dpush (Limits.pullback.snd f f)).mapIso eK.symm ≪≫ eUnit) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app _
  have := isInvertible_unit X
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pushforward (Limits.pullback.snd f f)).obj 𝒦) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso X.presheaf X.ringCatSheaf.property
      eL.symm
  obtain ⟨s, hsnd, ⟨es⟩⟩ :=
    Scheme.Modules.exists_section_iso_pushforward_of_invertible_pushforward
      (Limits.pullback.snd f f) 𝒦
  -- step 4
  refine iso_diagonalFourierMukaiKernel_of_exists_section f K hΦ ⟨s, hsnd, ⟨?_⟩⟩
  have : IsClosedImmersion (s ≫ Limits.pullback.snd f f) := by
    rw [hsnd]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (Limits.pullback.snd f f)
  exact eK ≪≫ (DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).mapIso
      (es ≪≫ (Scheme.Modules.pushforward s).mapIso eL) ≪≫
    (Stacks.Thickenings.derivedPushforwardSingleIso s.toLRSHom.toShHom
      s.isClosedEmbedding (SheafOfModules.unit X.ringCatSheaf)).symm

end Stacks.Duality

end
