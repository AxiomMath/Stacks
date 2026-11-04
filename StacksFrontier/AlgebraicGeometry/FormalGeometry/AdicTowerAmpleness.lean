module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologicalCriterion
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AmpleFibreTwistLocalBase
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningUnwinding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemTheorem
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# Ampleness spreads out from the closed fibre over a complete base

Let `A` be a Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be proper, put
`𝓘 = I𝒪_X`, and let `ℒ` be an invertible `𝒪_X`-module whose restriction to `V(𝓘)` is ample.
Then `ℒ` is ample.

This is the step of the proof of [Stacks, Tag 089A] that makes the algebraized invertible module
ample. The source obtains it from the closed immersion into `𝐏ᴺ_A` it builds; here it is proved
directly, with the cohomological criterion of [Stacks, Tag 0B5U]: for a coherent `ℱ` the twists
`𝓘ⁿℱ(d)/𝓘ⁿ⁺¹ℱ(d)` have no higher cohomology for `d ≫ 0`, uniformly in `n` ([Stacks, Tag 0897]
part (2), with ampleness on `V(𝓘)` only), so by dévissage neither has any `ℱ(d)/𝓘ⁿℱ(d)`; the
uniform Artin–Rees bound of [Stacks, Tag 02OB] puts all of `Hᵖ(X, ℱ(d))` into `Iᵐ Hᵖ(X, ℱ(d))` for
every `m`, and since `Hᵖ(X, ℱ(d))` is a finite `A`-module ([Stacks, Tag 02O6]) and `I` lies in
the Jacobson radical of the complete ring `A`, Krull's intersection theorem makes it zero.

## Main results

* `Stacks.AdicTowerAmple.subsingleton_cohomologyOverBase_of_subsingleton_adicCohomologyTower`.
* `Stacks.AdicTowerAmple.isAmple_of_isAmple_subscheme`.
* `Stacks.AdicTowerAmple.adicTowerAmpleness`: the input
  `Stacks.AmpleFormalSystemTheorem.AdicTowerAmpleness` of [Stacks, Tag 089A] holds.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.Cohomology.FormalFunctions Stacks.AlgebraicGeometry.HyperplaneTwistSequence

universe u

namespace Stacks.AdicTowerAmple

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **Cohomology vanishes if it vanishes along the adic tower**, over a complete Noetherian base.
If `Hᵖ(X, 𝒢/𝓘ⁿ𝒢) = 0` for every `n`, then `Hᵖ(X, 𝒢) = 0`: the bound of [Stacks, Tag 02OB] puts
`Hᵖ(X, 𝒢)` inside `Iᵐ Hᵖ(X, 𝒢)` for every `m`, and Krull's intersection theorem applies to the
finite `A`-module `Hᵖ(X, 𝒢)` because `I` is in the Jacobson radical of `A`. -/
theorem subsingleton_cohomologyOverBase_of_subsingleton_adicCohomologyTower (G : X.Modules)
    (hG : G.IsCoherent) (p : ℕ)
    (htower : ∀ n : ℕ, Subsingleton (adicCohomologyTower A f I G p n)) :
    Subsingleton (cohomologyOverBase A f p G) := by
  obtain ⟨c, hc, -, -⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f ‹IsProper f› I G
      ⟨hG.1, hG.2⟩ p
      (fun A' _ _ I' X' hX' F' hF' p' =>
        let : _root_.SheafOfModules.IsCoherent F' := ⟨hF'.1, hF'.2⟩
        isCohomologyReesFinite I' X' F' p' hX')
  have : Module.Finite A (cohomologyOverBase A f p G) :=
    Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6 A ‹IsNoetherianRing A› X f
      ‹IsProper f› G hG p
  have hle : (⊤ : Submodule A (cohomologyOverBase A f p G)) ≤
      ⨅ m : ℕ, I ^ m • (⊤ : Submodule A (cohomologyOverBase A f p G)) := by
    refine le_iInf fun m x _ => ?_
    have hx : x ∈ LinearMap.ker (adicCohomologyProj A f I G p (m + c)) :=
      LinearMap.mem_ker.2 (@Subsingleton.elim _ (htower (m + c)) _ 0)
    have h := hc (m + c) (Nat.le_add_left c m) hx
    rwa [Nat.add_sub_cancel] at h
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I (IsAdicComplete.le_jacobson_bot (I := I))]
    at hle
  refine ⟨fun x y => ?_⟩
  have hx := hle (Submodule.mem_top (x := x))
  have hy := hle (Submodule.mem_top (x := y))
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]

/-- **The higher cohomology of the twists of a coherent module vanishes eventually** when `ℒ` is
ample on `V(𝓘)`, over a complete Noetherian base. -/
theorem exists_subsingleton_cohomologyOverBase_twistModule (M : X.Modules)
    [IsInvertibleModule X M]
    (hM : IsAmple (baseIdealSheaf A I f).subscheme
      (Stacks.AmpleLocallyClosed.pullbackModule (baseIdealSheaf A I f).subschemeι M))
    (F : X.Modules) (hF : F.IsCoherent) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
      Subsingleton (cohomologyOverBase A f p (twistModule X M F d)) := by
  have : F.IsCoherent := hF
  obtain ⟨d₀, hd₀⟩ :=
    exists_subsingleton_cohomologyOverBase_adicQuotientTransitionKernel A I f M hM F hF
  refine ⟨d₀, fun d hd p hp => ?_⟩
  exact subsingleton_cohomologyOverBase_of_subsingleton_adicCohomologyTower A I f
    (twistModule X M F d)
    (AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F
      (tensorPowModule X M d)) p
    (subsingleton_cohomology_idealPowerQuotient (baseIdealSheaf A I f) (twistModule X M F d) p
      fun k => hd₀ d hd p hp k)

/-- **An invertible module ample on `V(𝓘)` is ample**, over a complete Noetherian base: the
criterion (2) ⟹ (1) of [Stacks, Tag 0B5U] applied to
`exists_subsingleton_cohomologyOverBase_twistModule`. -/
theorem isAmple_of_isAmple_subscheme (M : X.Modules) [IsInvertibleModule X M]
    (hM : IsAmple (baseIdealSheaf A I f).subscheme
      (Stacks.AmpleLocallyClosed.pullbackModule (baseIdealSheaf A I f).subschemeι M)) :
    IsAmple X M := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M := ‹IsInvertibleModule X M›
  refine Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X M
    (AlgebraicGeometry.Scheme.Modules.isAmple_of_eventualTwistVanishing M f fun F hF => ?_)
  obtain ⟨d₀, hd₀⟩ := exists_subsingleton_cohomologyOverBase_twistModule A I f M hM F hF
  refine ⟨d₀.toNat, fun n p hn hp => ?_⟩
  have h : Subsingleton (((moduleGlobalSections X).rightDerived p).obj
      (twistModule X M F (n : ℤ))) := hd₀ (n : ℤ) (by omega) p hp
  exact (@ModuleCat.isZero_of_subsingleton _ _ _ h).of_iso
    (((moduleGlobalSections X).rightDerived p).mapIso
      (Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl F)
        (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X M (n : ℤ))))

omit [IsNoetherianRing A] [IsAdicComplete I A] [IsProper f] in
/-- The closed member of a cartesian adic tower over `X` is `V(𝓘)`: a closed immersion
`k₀ : X₀ ⟶ X` with ideal sheaf `𝓘` gives a morphism `V(𝓘) ⟶ X₀` over `X`. -/
lemma exists_comp_eq_subschemeι {X₀ : Scheme.{u}} (k₀ : X₀ ⟶ X) [IsClosedImmersion k₀]
    (q₀ : X₀ ⟶ adicThickening A I 0) (hcart : IsPullback k₀ q₀ f (adicThickeningι A I 0)) :
    ∃ g : (baseIdealSheaf A I f).subscheme ⟶ X₀, g ≫ k₀ = (baseIdealSheaf A I f).subschemeι := by
  have hker : k₀.ker = baseIdealSheaf A I f := by
    rw [← hcart.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      AdicFiniteAlgebra.ker_adicBaseChange_fst A I f 0, zero_add, pow_one]
  have hinv : inv k₀.toImage ≫ k₀ = k₀.imageι := by
    rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
  refine ⟨Scheme.IdealSheafData.inclusion hker.le ≫ inv k₀.toImage, ?_⟩
  rw [Category.assoc, hinv]
  exact Scheme.IdealSheafData.inclusion_subschemeι hker.le

/-- **The ampleness input of [Stacks, Tag 089A] holds**: on an H-projective `fX : X ⟶ Spec A`
carrying a cartesian adic tower, an invertible `ℒ` whose restriction to `X₀` is ample is ample.
`X₀` maps to `V(𝓘)` isomorphically over `X`, so `ℒ|_{V(𝓘)}` is ample, and
`isAmple_of_isAmple_subscheme` concludes. -/
theorem adicTowerAmpleness {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n) :
    Stacks.AmpleFormalSystemTheorem.AdicTowerAmpleness A I q := by
  intro X fX hfX k hkcart M hM hM0
  have := isProper_of_isProjectiveMorphism fX hfX
  let := hM
  have := Stacks.AmpleFormalSystemLineBundle.isClosedImmersion_of_isPullback A I fX q k hkcart 0
  obtain ⟨g, hg⟩ := exists_comp_eq_subschemeι A I fX (k 0) (q 0) (hkcart 0)
  have : IsClosedImmersion (g ≫ k 0) := by rw [hg]; infer_instance
  have : IsClosedImmersion g := IsClosedImmersion.of_comp_isClosedImmersion g (k 0)
  have h1 := Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom g
    ((Scheme.Modules.pullback (k 0)).obj M) hM0
  have hk0 : IsInvertibleModule (Xn 0) ((Scheme.Modules.pullback (k 0)).obj M) :=
    Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_pullback (k 0) M hM
  have : IsInvertibleModule (baseIdealSheaf A I fX).subscheme
      ((Scheme.Modules.pullback (k 0) ⋙ Scheme.Modules.pullback g).obj M) :=
    Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_pullback g _ hk0
  have : IsInvertibleModule (baseIdealSheaf A I fX).subscheme
      ((Scheme.Modules.pullback (g ≫ k 0)).obj M) :=
    Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_pullback (g ≫ k 0) M hM
  refine isAmple_of_isAmple_subscheme A I fX M ?_
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((Scheme.Modules.pullbackComp g (k 0)).app M ≪≫
      (Scheme.Modules.pullbackCongr hg).app M)).mp h1

end Stacks.AdicTowerAmple

end
