module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.Flat.Pi
public import StacksFrontier.RingTheory.WeaklyEtale.Flat
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# Flatness is a local property of morphisms of Noetherian adic rings

Flatness of a continuous homomorphism of Noetherian adic topological rings is a local property in
the sense of Situation 0CBA, in the Noetherian form of Remark 0ANI.  Writing a localization
diagram as

```
B ────────→ (B')^
│             │
│ φ           │ φ'
↓             ↓
A ────────→ (A')^
```

with `B → B'` and `A → A'` étale and the completions taken over the weak ideals of definition of
`B`, resp. `A`, the three axioms are proved as follows.

* **Ascent.**  The completion `(A')^` is flat over `A'` — it is an adic completion of the
  Noetherian ring `A'` (`CompletionOver.flat_ofTarget`) — hence flat over `A`, hence flat over
  `B` once `φ` is flat.  Being a `B'`-module whose `B`-structure is the restricted one, it is then
  flat over `B'` because `B → B'` is weakly étale (Tag 092C, `flat_of_flat_of_mul_flat`).  It is
  moreover adically complete for the extension of an ideal of definition of `B`, the topologies
  being comparable by continuity, so Tag 0AGW applies over `B'` and makes `(A')^` flat over the
  completion `(B')^`.
* **Descent.**  `B → (B')^` is flat, so the hypothesis makes `B → (A')^` flat, while `A → (A')^`
  is faithfully flat (`CompletionOver.faithfullyFlat_canonicalMap`); flatness of `φ` then follows
  by permanence of flatness, Tag 0584 (2).
* **Finite products.**  A product over a finite index type is a direct sum, and direct sums of
  flat modules are flat (`RingHom.Flat.pi`).

## Main results

* `TopologicalRing.flat_isLocalNoetherian`: **Stacks 0GC9**.
* `TopologicalRing.flat_localizationPreserves`,
  `TopologicalRing.flat_faithfullyFlatDescent`,
  `TopologicalRing.flat_finiteProductPreserves`: the three axioms separately.
* `TopologicalRing.flat_isStableUnderCompositionNoetherian`: **Stacks 0GCB**, the local property
  of Stacks 0GC9 is stable under composition.

## Implementation notes

Two auxiliary results of independent interest are proved on the way.
`AdicCompletion.flat_of_flat_of_isAdicComplete` transports flatness over an adic completion to
a ring that *is* its own completion: a ring homomorphism out of `R^∧` into an `I`-adically
complete `R`-algebra `N` is flat as soon as `N^∧` is flat over `R^∧`, because the canonical map
`N → N^∧` is then `R^∧`-linear, which is checked modulo `Iⁿ` using
`AdicCompletion.pow_smul_top_eq_ker_eval`.
`TopologicalRing.isAdicComplete_of_pow_map_le` turns adic completeness for the ideal of
definition of an adic topological ring into adic completeness for any ideal a power of which is
contained in it, by Tags 090T and 0319.

## References

* [Stacks Project, Tag 0GC9](https://stacks.math.columbia.edu/tag/0GC9)
* [Stacks Project, Tag 0GCB](https://stacks.math.columbia.edu/tag/0GCB)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
-/

@[expose] public section

universe u

open TensorProduct CategoryTheory CategoryTheory.Limits

section Transport

/-- Flatness over an adic completion transported to a ring that is its own completion.  If `N` is
an `I`-adically complete `R`-algebra and `ψ : R^∧ → N` extends the structure map, then `ψ` is
flat as soon as `N^∧` is flat over `R^∧`: the canonical map `N → N^∧` is an `R^∧`-linear
bijection, since `β • n` and `b • n` agree modulo `Iⁿ N` whenever `b` represents the `n`-th
component of `β`. -/
public theorem AdicCompletion.flat_of_flat_of_isAdicComplete {R N : Type u} [CommRing R]
    [CommRing N] [Algebra R N] (I : Ideal R) (hfg : I.FG) (hcomp : IsAdicComplete I N)
    (ψ : AdicCompletion I R →+* N)
    (hψ : ψ.comp (algebraMap R (AdicCompletion I R)) = algebraMap R N)
    (h : Module.Flat (AdicCompletion I R) (AdicCompletion I N)) : ψ.Flat := by
  let instψ : Algebra (AdicCompletion I R) N := ψ.toAlgebra
  have hscalar : IsScalarTower R (AdicCompletion I R) N :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (DFunLike.congr_fun hψ r).symm
  have hmulmem : ∀ (n : ℕ), ∀ z ∈ (I ^ n • (⊤ : Submodule R N)), ∀ w : N,
      z * w ∈ (I ^ n • (⊤ : Submodule R N)) := by
    intro n z hz w
    refine Submodule.smul_induction_on hz (fun i hi x _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [smul_mul_assoc]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    · rw [add_mul]; exact Submodule.add_mem _ hx hy
  have hlin : ∀ (β : AdicCompletion I R) (m : N),
      AdicCompletion.of I N (β • m) = β • AdicCompletion.of I N m := by
    intro β m
    refine AdicCompletion.ext fun n ↦ ?_
    rw [AdicCompletion.of_apply, AdicCompletion.smul_eval, AdicCompletion.of_apply]
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (β.val n)
    rw [← hb]
    have hker : β - algebraMap R (AdicCompletion I R) b ∈
        (I ^ n • (⊤ : Submodule R (AdicCompletion I R))) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker, map_sub,
        AdicCompletion.eval_apply, AdicCompletion.eval_apply]
      simp only [AdicCompletion.algebraMap_apply, AdicCompletion.of_apply]
      rw [← hb]
      simp
    have hmap : ψ (β - algebraMap R (AdicCompletion I R) b) ∈
        (I ^ n • (⊤ : Submodule R N)) := by
      refine Submodule.smul_induction_on hker (fun i hi x _ ↦ ?_) (fun x y hx hy ↦ ?_)
      · have hsm : ψ (i • x) = i • ψ x := by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          exact congrArg (· * ψ x) (DFunLike.congr_fun hψ i)
        rw [hsm]
        exact Submodule.smul_mem_smul hi Submodule.mem_top
      · rw [map_add]; exact Submodule.add_mem _ hx hy
    have hRHS : (Submodule.Quotient.mk b : R ⧸ (I ^ n • (⊤ : Submodule R R))) •
        (I ^ n • (⊤ : Submodule R N)).mkQ m =
        (I ^ n • (⊤ : Submodule R N)).mkQ (b • m) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
      rfl
    rw [hRHS, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hrw : β • m - b • m = ψ (β - algebraMap R (AdicCompletion I R) b) * m := by
      rw [map_sub, sub_mul, Algebra.smul_def, Algebra.smul_def,
        show ψ (algebraMap R (AdicCompletion I R) b) = algebraMap R N b from
          DFunLike.congr_fun hψ b]
      rfl
    rw [hrw]
    exact hmulmem n _ hmap m
  have hbij : Function.Bijective (AdicCompletion.of I N) :=
    AdicCompletion.of_bijective_iff.mpr hcomp
  let L : N →ₗ[AdicCompletion I R] AdicCompletion I N :=
    { toFun := AdicCompletion.of I N
      map_add' := map_add _
      map_smul' := hlin }
  rw [show ψ = algebraMap (AdicCompletion I R) N from rfl, RingHom.flat_algebraMap_iff]
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective L hbij)

end Transport

namespace TopologicalRing

/-- An adic topological ring that is Noetherian is adically complete for every ideal extended
from a ring `B'` acting on it, a power of which lands inside an ideal of definition.  Tag 090T
passes completeness down to that power, and Tag 0319 back up to the ideal itself. -/
public theorem isAdicComplete_of_pow_map_le {B' M : Type u} [CommRing B'] [CommRing M]
    [TopologicalSpace M] [IsTopologicalRing M] [IsNoetherianRing M] [Algebra B' M]
    (hM : TopologicalRing.IsAdic M) (I₀ : Ideal B')
    (hpow : ∀ (I_M : Ideal M), IsIdealOfDefinition I_M →
      ∃ n : ℕ, 0 < n ∧ (I₀ ^ n).map (algebraMap B' M) ≤ I_M) :
    IsAdicComplete I₀ M := by
  obtain ⟨I_M, hdef, hadic⟩ := hM.1
  have hcompM : IsAdicComplete I_M M := by
    let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
    exact hadic.isAdicComplete_iff.mpr ⟨hM.2.2, hM.2.1⟩
  obtain ⟨n, hn, hle⟩ := hpow I_M hdef
  have hKn : ((I₀.map (algebraMap B' M)) ^ n) ≤ I_M := by rwa [← Ideal.map_pow]
  have h1 : IsAdicComplete ((I₀.map (algebraMap B' M)) ^ n) M :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete hKn hcompM (IsNoetherian.noetherian _)
  have h2 : IsAdicComplete (I₀.map (algebraMap B' M)) M :=
    (completeness_preserved (I₀.map (algebraMap B' M)) ((I₀.map (algebraMap B' M)) ^ n) hn
      Nat.one_pos le_rfl (by simpa using Ideal.pow_le_self (n := n) (by omega)) M).mpr h1
  exact (IsAdicComplete.map_algebraMap_iff I₀ M).mp h2

/-- The target of an étale ring homomorphism out of a Noetherian ring is Noetherian. -/
private theorem isNoetherianRing_of_etale {B B' : Type*} [CommRing B] [CommRing B']
    [IsNoetherianRing B] (f : B →+* B') (hf : f.Etale) : IsNoetherianRing B' := by
  let := f.toAlgebra
  obtain ⟨-, -, hfp⟩ := RingHom.Etale.iff_flat_and_formallyUnramified.mp hf
  have : Algebra.FinitePresentation B B' := hfp
  exact Algebra.FiniteType.isNoetherianRing B B'

/-- Finite products of flat morphisms of Noetherian adic topological rings are flat: this is
axiom (3) of Situation 0CBA, and holds because a product over a finite index type is a direct
sum. -/
public theorem flat_finiteProductPreserves :
    FiniteProductPreserves (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
        [IsLinearTopology R R] ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) := by
  intro B _ _ _ _ _ _ ι _ A _ _ _ _ _ _ f _ _ _ hP
  exact RingHom.Flat.pi f hP

/-- Flatness descends along a localization diagram whose horizontal map on the target side is
faithfully flat: this is axiom (2) of Situation 0CBA. -/
public theorem flat_faithfullyFlatDescent :
    FaithfullyFlatDescent (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
        [IsLinearTopology R R] ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB _ _ hff hP
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  obtain ⟨hflatB', -, -⟩ := RingHom.Etale.iff_flat_and_formallyUnramified.mp D.etaleB
  have := isNoetherianRing_of_etale _ D.etaleB
  have := isNoetherianRing_of_etale _ D.etaleA
  have h2 : ((CompletionOver.canonicalMap D.toA').comp D.map).Flat := by
    rw [D.commutes]
    exact (CompletionOver.flat_canonicalMap hB.1.1 hflatB').comp hP
  let instBA : Algebra B A := D.map.toAlgebra
  let instACo : Algebra A (CompletionOver D.toA') :=
    (CompletionOver.canonicalMap D.toA').toAlgebra
  let instBCo : Algebra B (CompletionOver D.toA') :=
    ((CompletionOver.canonicalMap D.toA').comp D.map).toAlgebra
  have htower : IsScalarTower B A (CompletionOver D.toA') :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hflatBCo : Module.Flat B (CompletionOver D.toA') :=
    RingHom.flat_algebraMap_iff.mp h2
  have hffACo : Module.FaithfullyFlat A (CompletionOver D.toA') :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (CompletionOver.faithfullyFlat_canonicalMap hA.1 hff)
  exact Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat
    (CompletionOver D.toA')

/-- Flatness ascends along a localization diagram: this is axiom (1) of Situation 0CBA. -/
public theorem flat_localizationPreserves :
    LocalizationPreserves (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
        [IsLinearTopology R R] ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' _ hP
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  have hNM : IsNoetherianRing (CompletionOver D.toA') := hA'.2
  obtain ⟨hflatA', -, -⟩ := RingHom.Etale.iff_flat_and_formallyUnramified.mp D.etaleA
  let instBB' : Algebra B B' := D.toB'.toAlgebra
  have hetB : Algebra.Etale B B' := D.etaleB
  have := isNoetherianRing_of_etale _ D.etaleB
  have := isNoetherianRing_of_etale _ D.etaleA
  let instBM : Algebra B (CompletionOver D.toA') :=
    ((CompletionOver.canonicalMap D.toA').comp D.map).toAlgebra
  let instB'M : Algebra B' (CompletionOver D.toA') :=
    (D.completedMap.comp (CompletionOver.ofTarget D.toB')).toAlgebra
  have htower : IsScalarTower B B' (CompletionOver D.toA') :=
    IsScalarTower.of_algebraMap_eq fun b ↦ DFunLike.congr_fun D.commutes b
  have hflatBM : Module.Flat B (CompletionOver D.toA') :=
    RingHom.flat_algebraMap_iff.mp (hP.comp (CompletionOver.flat_canonicalMap hA.1.1 hflatA'))
  have hflatB'M : Module.Flat B' (CompletionOver D.toA') :=
    flat_of_flat_of_mul_flat B B' (Algebra.WeaklyEtale.flat_lmul' B B')
      (CompletionOver D.toA') hflatBM
  obtain ⟨J, hJdef, hJadic⟩ := hB.1.1
  have hJfg : J.FG := IsNoetherian.noetherian J
  have hI₀fg : (J.map D.toB').FG := hJfg.map D.toB'
  have hquot : Module.Flat (B' ⧸ J.map D.toB')
      (CompletionOver D.toA' ⧸
        ((J.map D.toB') • (⊤ : Submodule B' (CompletionOver D.toA')))) :=
    Module.Flat.of_linearEquiv
      (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
        (TensorProduct.quotTensorEquivQuotSMul (CompletionOver D.toA') (J.map D.toB'))).symm
  have hulift : Module.Flat (ULift.{u} B') (ULift.{u} (CompletionOver D.toA')) :=
    Module.Flat.ulift_left_iff.mpr (Module.Flat.ulift_right_iff.mpr hflatB'M)
  have hAGW : Module.Flat (AdicCompletion (J.map D.toB') B')
      (AdicCompletion (J.map D.toB') (CompletionOver D.toA')) :=
    (AdicCompletion.isNoetherianRing_and_flat_of_flat_quotient (J.map D.toB') hI₀fg
      inferInstance hquot (isZero_Tor_one_of_flat
        (ModuleCat.of (ULift.{u} B') (ULift.{u} (CompletionOver D.toA'))) _)).2
  have hcomp : IsAdicComplete (J.map D.toB') (CompletionOver D.toA') := by
    refine isAdicComplete_of_pow_map_le hA'.1 (J.map D.toB') fun I_M hIMdef ↦ ?_
    obtain ⟨m, hm⟩ := hJdef.2
      ((algebraMap B (CompletionOver D.toA')) ⁻¹' (I_M : Set (CompletionOver D.toA')))
      ((hIMdef.1.preimage
        ((continuous_canonicalMap D.toA').comp D.continuousMap)).mem_nhds
          (by simp))
    refine ⟨m + 1, Nat.succ_pos m, ?_⟩
    rw [← Ideal.map_pow, Ideal.map_map]
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    have hxmem : algebraMap B (CompletionOver D.toA') x ∈ I_M :=
      hm (Ideal.pow_le_pow_right (Nat.le_succ m) hx)
    rwa [IsScalarTower.algebraMap_eq B B' (CompletionOver D.toA')] at hxmem
  let e := CompletionOver.adicCompletionRingEquiv hJdef hJadic D.toB'
  have hbij : Function.Bijective (CompletionOver.toAdicCompletion hJdef hJadic D.toB') :=
    CompletionOver.bijective_toAdicCompletion hJdef hJadic D.toB'
  have hkey : (e.symm : AdicCompletion (J.map D.toB') B' →+* CompletionOver D.toB').comp
      (algebraMap B' (AdicCompletion (J.map D.toB') B')) = CompletionOver.ofTarget D.toB' := by
    rw [← CompletionOver.toAdicCompletion_comp_ofTarget hJdef hJadic D.toB']
    exact RingHom.ext fun x ↦ e.symm_apply_apply (CompletionOver.ofTarget D.toB' x)
  have hcomm : (D.completedMap.comp
      (e.symm : AdicCompletion (J.map D.toB') B' →+* _)).comp
      (algebraMap B' (AdicCompletion (J.map D.toB') B')) =
      algebraMap B' (CompletionOver D.toA') := by
    rw [RingHom.comp_assoc, hkey]
    rfl
  have hψflat : (D.completedMap.comp
      (e.symm : AdicCompletion (J.map D.toB') B' →+* _)).Flat :=
    AdicCompletion.flat_of_flat_of_isAdicComplete (J.map D.toB') hI₀fg hcomp _ hcomm hAGW
  have hid : D.completedMap =
      (D.completedMap.comp (e.symm : AdicCompletion (J.map D.toB') B' →+* _)).comp
        (e : CompletionOver D.toB' →+* AdicCompletion (J.map D.toB') B') := by
    ext x
    simp
  rw [hid]
  exact (RingHom.Flat.comp_iff_of_bijective_right (f := _) hbij).mpr hψflat

/-- **Flatness is a local property of morphisms of Noetherian adic topological rings**
(Stacks 0GC9): it ascends along completed étale localization diagrams, descends along faithfully
flat ones, and is preserved by finite products of targets. -/
@[stacks 0GC9, sga "3 VIIB 1.3.4" "Flatness clause"]
public theorem flat_isLocalNoetherian :
    PropertyIsLocalNoetherian
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) where
  localizationPreserves := flat_localizationPreserves
  faithfullyFlatDescent := flat_faithfullyFlatDescent
  finiteProduct := flat_finiteProductPreserves

/-- **Stacks 0GCB.** Flatness, as a local property of morphisms of Noetherian adic topological
rings (Stacks 0GC9), is stable under composition: the composite of two flat ring homomorphisms
is flat. -/
@[stacks 0GCB]
public theorem flat_isStableUnderCompositionNoetherian :
    PropertyIsStableUnderCompositionNoetherian
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) where
  isLocal := flat_isLocalNoetherian
  comp _ _ _ _ _ _ _ hf hg := hg.comp hf

end TopologicalRing

end
