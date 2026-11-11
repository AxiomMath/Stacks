module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ProAdicReplacement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AnnihilatedLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageComparison
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineOpenAdicReplacement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LevelwiseAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesProIso
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkDepthEpi
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.AffineOpenDualizingCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.EssSurjRestrictOpen

/-!
# Improving coherent formal modules to depth two

This file proves [Stacks, Tag 0EJF]: under conditions (a)–(e) of the source, the canonical map
`(ℱₙ) ⟶ (ℱ''ₙ)` from an object of `Coh(X, ℐ)` to the system of its improvements along `T' ⊆ T`
has `(ℱ''ₙ)` of depth at least one on `T` and two on `T'`, and `(ℱ''ₙ)` is pro-isomorphic to an
object `(ℋₙ)` of `Coh(X, ℐ)` such that the induced `(ℱₙ) ⟶ (ℋₙ)` has kernel and cokernel
annihilated by a power of `ℐ`.

## Proof

The system `(ℱ''ₙ)` and conclusions (1), (2) are
`Stacks.Algebraization.canonicalImprovedSystem` and
`Stacks.Algebraization.depth_stalk_canonicalImprovedSystem`. For (3) and (4) the source works
on an affine open `U` with a dualizing complex and `cd ≤ d`
(`Stacks.Algebraization.exists_affineOpen_isDualizingComplex_cohomologicalDimension_le`):

* [Stacks, Tag 0EJE] gives the object `(𝒢ₙ)` of `Coh(X, ℐ)` pro-isomorphic to the depth-one
  quotients `(ℱ'ₙ)` and the epimorphism `φ : (ℱₙ) ⟶ (𝒢ₙ)` with kernel killed by a power of `ℐ`
  (`Stacks.Algebraization.exists_coherentAdicSystem_improvement`); since `φ` does not change the
  completed stalks off `V(ℐ)` (`Stacks.Algebraization.completedStalkDepth_eq_of_epi`), conditions
  (c) and (d) hold for `(𝒢ₙ)`;
* over the completion of `Γ(X, U)` these give Situation [Stacks, Tag 0EFU] with `s = 1`, and
  Theorem [Stacks, Tag 0EIE] makes `{H¹_{T'}(M'ₙ)}` essentially constant
  (`Stacks.Algebraization.isEssentiallyConstantPro_completedFormalSectionsTower`,
  `Stacks.Algebraization.isEssentiallyConstantPro_localCohomologyOne_depthOneSections`);
* hence `(Γ(U, ℱ''ₙ))` is pro-isomorphic to the adic tower of `M'' = lim Γ(U, ℱ''ₙ)`, compatibly
  with `(Γ(U, ℱₙ))`, with kernels and cokernels killed by a fixed power of `ℐ(U)`
  (`ImprovingFormalModulesDepthTwoLocal.lean`), which yields an adic replacement of
  `(ℱ''ₙ|_U)` in `Coh(U, ℐ|_U)`
  (`Stacks.Coherent.exists_coherentAdicSystem_of_affineOpenAdicReplacement`).

These local replacements glue (`Stacks.Coherent.exists_coherentAdicReplacement`), and the
annihilation of kernels and cokernels is local
(`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_restrict`).

## Main results

* `Stacks.Algebraization.exists_proIso_coherentAdicSystem_canonicalImprovedSystem`:
  [Stacks, Tag 0EJF].

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- **Gluing local adic replacements with annihilated kernels and cokernels.** Let `(Pₙ)` be an
inverse system of coherent modules with a map `τ` from an object `(ℱₙ)` of `Coh(X, ℐ)`. If around
every point there is an open `U` on which `(Pₙ|_U)` is pro-isomorphic to an object of
`Coh(U, ℐ|_U)`, compatibly with `τ` through a morphism from `(ℱₙ|_U)` whose levelwise kernels and
cokernels are killed by a power of `ℐ|_U`, then `(Pₙ)` is pro-isomorphic to an object `(ℋₙ)` of
`Coh(X, ℐ)` compatibly with `τ` through a morphism `(ℱₙ) ⟶ (ℋₙ)` whose levelwise kernels and
cokernels are killed by a power of `ℐ`. -/
theorem exists_coherentAdicReplacement_isKernelCokernelAnnihilatedByPower {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (F : Stacks.Coherent.CoherentAdicSystems I)
    (P : ℕᵒᵖ ⥤ X.Modules) [∀ n, (P.obj n).IsCoherent] (τ : F.obj ⟶ P)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
        (N : Stacks.Coherent.CoherentAdicSystems (I.comap U.ι))
        (e : InverseSequence.ProIso (P ⋙ Scheme.Modules.restrictFunctor U.ι) N.obj)
        (σ : (Stacks.Coherent.restrictFunctor I U.ι).obj F ⟶ N),
        (∀ n : ℕ, (Functor.whiskerRight τ (Scheme.Modules.restrictFunctor U.ι)).app
            (op (e.α n)) ≫ e.φ n =
          ((Stacks.Coherent.restrictFunctor I U.ι).obj F).obj.map (homOfLE (e.αle n)).op ≫
            σ.hom.app (op n)) ∧
        IsKernelCokernelAnnihilatedByPower (I.comap U.ι) σ.hom) :
    ∃ (H : Stacks.Coherent.CoherentAdicSystems I) (e : InverseSequence.ProIso P H.obj)
      (σ : F ⟶ H),
      (∀ n : ℕ, τ.app (op (e.α n)) ≫ e.φ n =
        F.obj.map (homOfLE (e.αle n)).op ≫ σ.hom.app (op n)) ∧
      IsKernelCokernelAnnihilatedByPower I σ.hom := by
  choose U hxU N e σ hσ hann using hloc
  obtain ⟨H, eH, σH, hcomp, hunique⟩ := Stacks.Coherent.exists_coherentAdicReplacement I F P τ
    (fun x => ⟨U x, hxU x, N x, ⟨e x⟩⟩)
  refine ⟨H, eH, σH, hcomp, ?_⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((U x : X.Opens) : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine isKernelCokernelAnnihilatedByPower_of_restrict I I σH (fun j : t => U j.1) ?_ ?_
  · refine top_le_iff.mp fun y _ => ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hy⟩
  · intro j
    obtain ⟨i, hi⟩ := hunique (U j.1) (N j.1) (e j.1) (σ j.1) (hσ j.1)
    have hi' : ((Stacks.Coherent.restrictFunctor I (U j.1).ι).map σH).hom ≫
        ((ObjectProperty.ι _).mapIso i).hom = (σ j.1).hom := by
      rw [← hi]
      rfl
    have := hann j.1
    rw [← hi'] at this
    exact (Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff _ _ _).1 this

/-- The terms of the cokernel of an epimorphism of `Coh(X, ℐ)` are killed by every power of `ℐ`:
they vanish. -/
theorem idealPowerMultiple_cokernel_obj_eq_bot_of_epi {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : Stacks.Coherent.CoherentAdicSystems I} (φ : F ⟶ G) [Epi φ] (c n : ℕ) :
    idealPowerMultiple I c ((cokernel φ).obj.obj (op n)) = ⊥ := by
  have hz : IsZero ((cokernel φ).obj.obj (op n)) :=
    (Functor.isZero_iff _).mp ((Stacks.Coherent.isZero_coherentAdicSystems_iff I _).mp
      (isZero_cokernel_of_epi φ)) (op n)
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun V a _ x => ?_
  have hV : IsZero ((sectionsOver V.1).obj ((cokernel φ).obj.obj (op n))) :=
    (sectionsOver V.1).map_isZero hz
  exact (ModuleCat.isZero_iff_subsingleton.mp hV).elim _ _

/-- **Stacks Project, Tag 0EJF.** Let `X` be a Noetherian scheme which locally has a dualizing
complex, `ℐ` a quasi-coherent ideal sheaf with support `Y`, `(ℱₙ)` an object of `Coh(X, ℐ)`,
`T' ⊆ T ⊆ Y` subsets stable under specialization and `d ≥ 0` an integer, such that
* (a) every point has an affine neighbourhood `U` with `cd(Γ(X, U), ℐ(U)) ≤ d`,
* (b) for `y ∈ T` and a nonmaximal prime `𝔭` of `𝒪_{X,y}^∧` with
  `V(𝔭) ∩ V(ℐ_y^∧) = {𝔪_y^∧}`, `depth((ℱ_y^∧)_𝔭) > 0`,
* (c) for `y ∈ T'` and a prime `𝔭 ∉ V(ℐ_y^∧)` of `𝒪_{X,y}^∧` with
  `V(𝔭) ∩ V(ℐ_y^∧) ≠ {𝔪_y^∧}`, `depth((ℱ_y^∧)_𝔭) ≥ 1` or
  `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 1 + d`,
* (d) for `y ∈ T'` and a nonmaximal prime `𝔭` of `𝒪_{X,y}^∧` with
  `V(𝔭) ∩ V(ℐ_y^∧) = {𝔪_y^∧}`, `depth((ℱ_y^∧)_𝔭) > 1`,
* (e) if `y ⤳ y'` is an immediate specialization of points of `Y` with `y' ∈ T'`, then `y ∈ T`.

Then the canonical map `(ℱₙ) ⟶ (ℱ''ₙ)` (each component the improvement of `ℱₙ` along `T' ⊆ T`
of [Stacks, Tag 0EI4]) satisfies
1. `depth(ℱ''_{n,y}) ≥ 1` for `y ∈ T`,
2. `depth(ℱ''_{n,y'}) ≥ 2` for `y' ∈ T'`,
3. `(ℱ''ₙ)` is pro-isomorphic to an object `(ℋₙ)` of `Coh(X, ℐ)`,
4. the induced morphism `σ : (ℱₙ) ⟶ (ℋₙ)` of `Coh(X, ℐ)` has kernel and cokernel annihilated by
   a power of `ℐ` (both in `Coh(X, ℐ)` and levelwise). -/
@[stacks 0EJF "the full lemma: under (a)-(e), the canonical map (ℱₙ) ⟶ (ℱ''ₙ), levelwise the \
improvement along T' ⊆ T, has depth(ℱ''_{n,y}) ≥ 1 for y ∈ T and depth(ℱ''_{n,y'}) ≥ 2 for \
y' ∈ T', (ℱ''ₙ) is pro-isomorphic to an object (ℋₙ) of Coh(X, ℐ), and the induced \
σ : (ℱₙ) ⟶ (ℋₙ) has kernel and cokernel annihilated by a power of ℐ: conclusions (1)-(4)"]
theorem exists_proIso_coherentAdicSystem_canonicalImprovedSystem {X : Scheme.{u}}
    [IsNoetherian X] {I : X.IdealSheafData} (hdual : HasDualizingComplexOnAffineCover X)
    (F : Stacks.Coherent.CoherentAdicSystems I) {T T' : Set X}
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (hTY : T ⊆ I.support) (hTT' : T' ⊆ T) (d : ℕ)
    (ha : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      Stacks.LocalCohomology.cohomologicalDimension Γ(X, U.1) (I.ideal U)
        (Ideal.fg_of_isNoetherianRing _) ≤ (d : ℤ))
    (hb : ∀ y ∈ T, ∀ p : PrimeSpectrum (completedLocalRing I y),
      p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      0 < completedStalkDepth I F y p)
    (hc : ∀ y ∈ T', ∀ p : PrimeSpectrum (completedLocalRing I y),
      ¬ completedLocalIdeal I y ≤ p.asIdeal →
      adicClosedFibreThrough I y p ≠ {completedMaximalIdeal I y} →
      1 ≤ completedStalkDepth I F y p ∨
        enatToEInt (completedStalkDepth I F y p) +
            krullDimToEInt (ringKrullDim (completedLocalRing I y ⧸ p.asIdeal)) >
          ((1 + d : ℤ) : EInt))
    (hd : ∀ y ∈ T', ∀ p : PrimeSpectrum (completedLocalRing I y),
      p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      1 < completedStalkDepth I F y p)
    (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T) :
    (∀ (n : ℕᵒᵖ) (x : X),
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u})
            ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val x
      (x ∈ T → (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u})
            ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val.presheaf x)) ∧
        (x ∈ T' → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u})
            ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val.presheaf x))) ∧
    (∀ n : ℕᵒᵖ, IsNestedImprovement T T'
      ((toCanonicalImprovedSystem hdual F hT hT' hTY himm).app n)) ∧
    ∃ (H : Stacks.Coherent.CoherentAdicSystems I)
      (e : InverseSequence.ProIso (canonicalImprovedSystem hdual F hT hT' hTY himm) H.obj)
      (σ : F ⟶ H),
      (∀ n : ℕ, (toCanonicalImprovedSystem hdual F hT hT' hTY himm).app (op (e.α n)) ≫ e.φ n =
        F.obj.map (homOfLE (e.αle n)).op ≫ σ.hom.app (op n)) ∧
      (∃ c : ℕ, ∀ n : ℕ, idealPowerMultiple I c ((kernel σ).obj.obj (op n)) = ⊥) ∧
      (∃ c : ℕ, ∀ n : ℕ, idealPowerMultiple I c ((cokernel σ).obj.obj (op n)) = ⊥) ∧
      IsKernelCokernelAnnihilatedByPower I σ.hom := by
  refine ⟨depth_stalk_canonicalImprovedSystem hdual F hT hT' hTY himm,
    isNestedImprovement_toUniversalImprovedSystem_app hTT'
      (isUniversal_canonicalDepthTwoImprovement hdual F hT hT' hTY himm), ?_⟩
  -- the model `(𝒢ₙ)` of the depth-one quotients, [Stacks, Tag 0EJE]
  obtain ⟨μ, hμ, hμmono, G, φ, ψ, π, hφψ, hπψ, hmapπ, hψπ, hepi, hker⟩ :=
    exists_coherentAdicSystem_improvement F T hT hTY hb
  let Mo : DepthOneAdicModel F hT :=
    { G := G, κ := ψ, μ := μ, le_μ := hμ, monotone_μ := hμmono, π := π, π_κ := hπψ,
      map_π := hmapπ, κ_π := hψπ }
  have := hepi
  obtain ⟨cφ, -, hcφ⟩ := (Stacks.Coherent.isKernelCokernelAnnihilatedByPower_hom_of_kernel_cokernel
    φ hker ⟨0, idealPowerMultiple_cokernel_obj_eq_bot_of_epi φ 0⟩).exists_kernel_eq_bot
  -- conditions (c) and (d) for `(𝒢ₙ)`
  have hcG : ∀ y ∈ T', ∀ p : PrimeSpectrum (completedLocalRing I y),
      ¬ completedLocalIdeal I y ≤ p.asIdeal →
      adicClosedFibreThrough I y p ≠ {completedMaximalIdeal I y} →
      1 ≤ completedStalkDepth I G y p ∨
        enatToEInt (completedStalkDepth I G y p) +
            krullDimToEInt (ringKrullDim (completedLocalRing I y ⧸ p.asIdeal)) >
          ((1 + d : ℤ) : EInt) := by
    intro y hy p hp hfib
    rw [completedStalkDepth_eq_of_epi φ y hker p hp]
    exact hc y hy p hp hfib
  have hdG : ∀ y ∈ T', ∀ p : PrimeSpectrum (completedLocalRing I y),
      p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      ((1 : ℕ) : ℕ∞) < completedStalkDepth I G y p := by
    intro y hy p hp hfib
    have hpI : ¬ completedLocalIdeal I y ≤ p.asIdeal := fun hle => by
      have hmem : p.asIdeal ∈ adicClosedFibreThrough I y p := ⟨p.isPrime, le_rfl, hle⟩
      rw [hfib] at hmem
      exact hp hmem
    rw [completedStalkDepth_eq_of_epi φ y hker p hpI, Nat.cast_one]
    exact hd y hy p hp hfib
  -- the local adic replacements
  have := isCoherent_canonicalImprovedSystem_obj hdual F hT hT' hTY himm
  have hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (N : Stacks.Coherent.CoherentAdicSystems (I.comap U.ι))
      (e : InverseSequence.ProIso (canonicalImprovedSystem hdual F hT hT' hTY himm ⋙
        Scheme.Modules.restrictFunctor U.ι) N.obj)
      (σ : (Stacks.Coherent.restrictFunctor I U.ι).obj F ⟶ N),
      (∀ n : ℕ, (Functor.whiskerRight (toCanonicalImprovedSystem hdual F hT hT' hTY himm)
          (Scheme.Modules.restrictFunctor U.ι)).app (op (e.α n)) ≫ e.φ n =
        ((Stacks.Coherent.restrictFunctor I U.ι).obj F).obj.map (homOfLE (e.αle n)).op ≫
          σ.hom.app (op n)) ∧
      IsKernelCokernelAnnihilatedByPower (I.comap U.ι) σ.hom := by
    intro x
    obtain ⟨V, hxV, hdualV, hcdV⟩ :=
      exists_affineOpen_isDualizingComplex_cohomologicalDimension_le hdual I d ha x
    let _ : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
    have hRA := ringKrullDim_lt_top_and_adicCompletion_of_isDualizingComplex (I.ideal V) hdualV
    have hess := isEssentiallyConstantPro_completedFormalSectionsTower V.2 hT' (hTT'.trans hTY)
      G d hdualV hcdV (fun y hy => hcG y.1 hy) (fun y hy => hdG y.1 hy)
    have hβ := isEssentiallyConstantPro_localCohomologyOne_depthOneSections hdual F hT hT' hTY
      himm V.2 Mo (hTT'.trans hTY) hRA.1 hRA.2 hess
    obtain ⟨c, ⟨i⟩, s, hcs⟩ :=
      isEssentiallyConstantPro_modelQuotientSystem hdual F hT hT' hTY hTT' himm V.2 Mo hβ
    obtain ⟨N, e, σ, hcomp, hk, hck⟩ :=
      Stacks.Coherent.exists_coherentAdicSystem_of_affineOpenAdicReplacement I F
        (canonicalImprovedSystem hdual F hT hT' hTY himm)
        (toCanonicalImprovedSystem hdual F hT hT' hTY himm) V.1 V.2
        (modelReplacement hdual F hT hT' hTY himm V.1)
        (finite_modelReplacement_quotient hdual F hT hT' hTY hTT' himm V.2 Mo hcs)
        (modelReplacementProIso hdual F hT hT' hTY hTT' himm V.2 Mo hcs)
        (modelReplacementMap hdual F hT hT' hTY hTT' himm V.2 Mo φ)
        (modelReplacementMap_compatible hdual F hT hT' hTY hTT' himm V.2 Mo hcs φ hφψ)
    refine ⟨V.1, hxV, N, e, σ, hcomp, ?_⟩
    have := AlgebraicGeometry.isNoetherian_opens_toScheme V.1
    exact Stacks.Coherent.isKernelCokernelAnnihilatedByPower_hom_of_kernel_cokernel σ
      ⟨_, hk _ fun n a ha q hq => smul_eq_zero_of_modelReplacementMap_eq_zero hdual F hT hT' hTY
        hTT' himm V.2 Mo hcs φ hcφ n a ha q hq⟩
      ⟨_, hck _ fun n a ha q => smul_mem_range_modelReplacementMap hdual F hT hT' hTY hTT' himm
        V.2 Mo hcs φ n a ha q⟩
  -- the global adic replacement
  obtain ⟨H, e, σ, hcomp, hann⟩ := exists_coherentAdicReplacement_isKernelCokernelAnnihilatedByPower
    I F (canonicalImprovedSystem hdual F hT hT' hTY himm)
    (toCanonicalImprovedSystem hdual F hT hT' hTY himm) hloc
  obtain ⟨t, htpos, ht⟩ := hann
  exact ⟨H, e, σ, hcomp,
    ⟨t, Stacks.Coherent.idealPowerMultiple_kernel_obj_eq_bot_of_termwise I I σ t fun k => (ht k).1⟩,
    ⟨t, Stacks.Coherent.idealPowerMultiple_cokernel_obj_eq_bot_of_termwise I I σ t
      fun k => (ht k).2⟩, ⟨t, htpos, ht⟩⟩

end Stacks.Algebraization

end
