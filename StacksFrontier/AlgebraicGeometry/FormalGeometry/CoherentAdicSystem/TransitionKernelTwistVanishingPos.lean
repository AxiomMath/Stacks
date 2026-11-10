module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesBaseChangeCoherent
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesCmpAssembly
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSpecStructureSections
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedFiniteTypeFromAffine
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionKernelTwistVanishing
public import
  StacksFrontier.AlgebraicGeometry.GradedProperCohomology.SubschemeAmpleCoproductTwistVanishing
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Uniform vanishing of the twisted transition kernels in every positive degree

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper, `𝓘 = I · 𝒪_X`, and `L`
an invertible `𝒪_X`-module whose restriction to the closed subscheme `V(𝓘)` is ample. For an
object `(F_n)` of `Coh(X, 𝓘)` there is one `d₀` with

  `H ᵖ(X, Ker(F_{n+1} ⟶ F_n) ⊗ L ^⊗ d) = 0`  for all `n ≥ 0`, `d ≥ d₀` and `p > 0`.

This is the argument of [Stacks, Tag 0884] — [Stacks, Tag 087Z] followed by [Stacks, Tag 0897]
part (2) — carried out in every positive degree and with ampleness asked on `V(𝓘)` only. The
degree-one case under the source's `f`-ampleness is [Stacks, Tag 0884] itself; the positive-degree
form with ampleness on the fibre is what the proof of [Stacks, Tag 0D2M] consumes, with
`I = 𝔪` the maximal ideal of a Noetherian local base.

## The route

* **Stacks 087Z**: `Stacks.Coherent.finiteTypeAssociatedGradedData` gives the graded module
  `⨁ₙ Ker(F_{n+1} ⟶ F_n)` over `⨁ₙ 𝓘ⁿ/𝓘ⁿ⁺¹`.
* It is read over the **Rees** algebra `⨁ₙ 𝓘ⁿ` through the degreewise surjection
  `Stacks.Coherent.reesToAssociatedGraded` (`Stacks.Coherent.reesTransitionGradedModule`), where
  it is of finite type (`Stacks.Coherent.isFiniteType_reesTransitionGradedModule`).
* **Stacks 0897 part (2)** is then run over `X' = Spec_X(⨁ₙ 𝓘ⁿ)`, proper over the Noetherian
  `Spec(⨁ₙ Iⁿ)`: `Stacks.Cohomology.FormalFunctions.reesBaseChangeModule` is a coherent `F'` on
  `X'` whose direct image is `∐ₙ 𝓖ₙ`, and
  `exists_isZero_Hgroup_tensorPowTwist_of_coprodIso_of_isAmple_subscheme` (in the namespace
  `Stacks.GradedProperCohomology`) is Serre vanishing for `F'` brought down to `X`. Because `𝓘`
  annihilates every transition kernel (`Stacks.Coherent.smul_piece_eq_zero_of_mem`), the module
  upstairs lives over `V(𝓘)`, and only ampleness of `L|_{V(𝓘)}` is used.

## Main results

* `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos`.

## References

* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.Blowup (reesGradedAlgebra)

universe u

namespace Stacks.Coherent

/-- The homogeneous pieces of the graded module of Stacks 087Z are the transition kernels. -/
private def modulePieceIsoTransitionKernel {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} {F : CoherentAdicSystems I} (D : AssociatedGradedData I F) (n : ℕ) :
    D.module.piece (n : ℤ) ≅ transitionKernel F n :=
  match n with
  | 0 => D.modulePieceZero
  | n + 1 => D.modulePieceSucc n

/-- **Stacks 0884 in every positive degree, with ampleness asked only on `V(𝓘)`.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper morphism, `𝓘 = I · 𝒪_X` and `L` an
invertible `𝒪_X`-module whose restriction to the closed subscheme `V(𝓘)` is ample. Let `𝓕` be an
object of `Coh(X, 𝓘)`. Then there is an integer `d₀` such that

  `H ᵖ(X, Ker(𝓕_{n+1} ⟶ 𝓕_n) ⊗ L ^⊗ d) = 0`

for every `n ≥ 0`, every `d ≥ d₀` and every `p > 0` — one `d₀` for the whole system and for all
the positive degrees at once.

The source states the case `p = 1`, which is what the proof of Stacks 0885 consumes and which is
`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule` below; the uniformity in
`p` costs nothing, because the bound is the one [Stacks, Tag 02O1] produces upstairs for the
single coherent module on `Spec_X(⨁ₙ 𝓘ⁿ)` and that bound already serves every positive degree.
The degree-`p` form is what the dévissage of [Stacks, Tag 0D2M] needs, since that runs in all
positive degrees.

The ampleness hypothesis is weaker than the source's `f`-ampleness, which it follows from
(see `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule`), and it is the
weaker one that [Stacks, Tag 0D2M] needs: there `𝓘 = 𝔪 · 𝒪_X` and `V(𝓘)` is the closed fibre.
Only ampleness on `V(𝓘)` is used because the transition kernels are annihilated by `𝓘`
(`Stacks.Coherent.smul_piece_eq_zero_of_mem`), so the coherent module on `Spec_X(⨁ₙ 𝓘ⁿ)` that
carries the vanishing lives on a closed subscheme affine over `V(𝓘)`; that is
`exists_isZero_Hgroup_tensorPowTwist_of_coprodIso_of_isAmple_subscheme` in the namespace
`Stacks.GradedProperCohomology`. -/
@[ega "III 2.4.2" "special case"]
public theorem exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple (baseIdealSheaf A I f).subscheme
      (Stacks.AmpleLocallyClosed.pullbackModule (baseIdealSheaf A I f).subschemeι L))
    (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)) :
    ∃ d₀ : ℤ, ∀ (n : ℕ) (d : ℤ), d₀ ≤ d → ∀ p : ℕ, 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
            (forget₂ CommRingCat RingCat) ((isSheaf_structureRingPresheaf X))⟩).obj
              ((transitionKernel 𝓕 n))).obj ((Stacks.Ample.tensorPowModule X L d))))) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := { }
  obtain ⟨D⟩ := finiteTypeAssociatedGradedData (baseIdealSheaf A I f) 𝓕
  -- The Rees algebra of `I` is a finite type algebra over the Noetherian `A`, hence Noetherian.
  have hBN : IsNoetherianRing ↥(reesAlgebra I) :=
    Algebra.FiniteType.isNoetherianRing A ↥(reesAlgebra I)
  -- The graded module of Stacks 087Z, read over the Rees algebra of `𝓘`.
  set M := reesTransitionGradedModule D with hM
  have hqc : ∀ n : ℤ, (M.piece n).IsQuasicoherent := D.moduleQuasicoherent
  have hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n) := D.moduleNegative
  have hftM : M.IsFiniteType := isFiniteType_reesTransitionGradedModule D
  have hX : AlgebraicGeometry.IsProper (Over.mk f).hom := ‹IsProper f›
  -- The base change: `X' = Spec_X(⨁ₙ 𝓘ⁿ)`, affine over `X` and proper over `Spec(⨁ₙ Iⁿ)`.
  have hF' : (Stacks.Cohomology.FormalFunctions.reesBaseChangeModule I (Over.mk f) M
      hqc hneg).IsCoherent :=
    Stacks.Cohomology.FormalFunctions.isCoherent_reesBaseChangeModule I (Over.mk f) M hX
      hqc hftM hneg
  have hf' : AlgebraicGeometry.IsProper
      (Stacks.Cohomology.FormalFunctions.reesSpecStructure I (Over.mk f)) :=
    Stacks.Cohomology.FormalFunctions.isProper_comp_pullbackFst_of_isClosedImmersion
      (Stacks.Cohomology.FormalFunctions.reesSpecToBase I) hX
      (Stacks.Cohomology.FormalFunctions.reesClosedImmersion I (Over.mk f))
      (Stacks.Cohomology.FormalFunctions.isClosedImmersion_reesClosedImmersion I (Over.mk f))
  -- `𝓘` annihilates every homogeneous piece of the graded module — the degree-zero piece of the
  -- associated graded algebra is `𝒪_X/𝓘` and its unit acts as the identity — hence it
  -- annihilates the coproduct of the pieces over an affine open, hence `π_* F'`.
  have hann : ∀ (U : X.affineOpens) (a : Γ(X, U.1)),
      a ∈ (baseIdealSheaf A I f).ideal U →
      ∀ m : Γ((AlgebraicGeometry.Scheme.Modules.pushforward
          (Stacks.Cohomology.FormalFunctions.reesRelativeSpec I (Over.mk f)).hom).obj
            (Stacks.Cohomology.FormalFunctions.reesBaseChangeModule I (Over.mk f) M hqc hneg),
          U.1), a • m = 0 :=
    fun U a ha m =>
      Stacks.GradedProperCohomology.smul_sections_eq_zero_of_coprodIso
        (fun n : ℕ => M.piece (n : ℤ))
        (Stacks.Cohomology.FormalFunctions.reesCoprodPushforwardIso I (Over.mk f) M hqc hneg)
        U.2.isCompact a
        (fun n x =>
          smul_piece_eq_zero_of_mem D.toAssociatedGradedAlgebraData D.module U ha (n : ℤ) x) m
  -- Serre vanishing upstairs, brought down to `X`.
  obtain ⟨d₀, hd₀⟩ :=
    @GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_coprodIso_of_isAmple_subscheme
      X (Stacks.Cohomology.FormalFunctions.reesRelativeSpec I (Over.mk f)).left
      ↥(reesAlgebra I) _ hBN
      (Stacks.Cohomology.FormalFunctions.reesRelativeSpec I (Over.mk f)).hom _
      (Stacks.Cohomology.FormalFunctions.reesSpecStructure I (Over.mk f)) hf'
      (baseIdealSheaf A I f) L _ hL
      (Stacks.Cohomology.FormalFunctions.reesBaseChangeModule I (Over.mk f) M hqc hneg) hF'
      (fun n : ℕ => M.piece (n : ℤ))
      (Stacks.Cohomology.FormalFunctions.reesCoprodPushforwardIso I (Over.mk f) M hqc hneg)
      hann
  refine ⟨(d₀ : ℤ), fun n d hd p hp => ?_⟩
  have hdn : ((d.toNat : ℤ)) = d := Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg d₀) hd)
  refine (hd₀ d.toNat p (by omega) hp n).of_iso ((Hfunctor X.ringCatSheaf ⊤ p).mapIso ?_)
  exact Stacks.RelativeVeryAmple.tensorModulesMapIso X (modulePieceIsoTransitionKernel D n).symm
    (Stacks.RelativeVeryAmple.tensorPowModuleCongr X L hdn.symm)

end Stacks.Coherent

end
