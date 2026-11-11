module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleAdicFibreDeformation

/-!
# Nonzero sections of an invertible module survive on the closed fibre

Let `A` be a Noetherian ring complete with respect to a maximal ideal `I`, let `X` be a proper
flat algebraic space over `Spec A` and `X₀ = X ×_{Spec A} Spec(A/I)` its closed fibre.  A nonzero
section `s : 𝒪_X ⟶ L` of an invertible `𝒪_X`-module gives a nonzero section of `L|_{X₀}`.

## The argument

By Grothendieck's existence theorem (Stacks 08BF, in the form of the faithfulness of
`𝓕 ↦ (𝓕|_{Xₙ})ₙ`) some `s mod Iⁿ⁺¹ L` is nonzero; take `n` least.  If `n = 0`, then `s mod I L`
is a nonzero map `𝒪_X ⟶ L / I L ≅ (ι₀)_* ι₀^* L` and its adjoint is a nonzero section of
`L|_{X₀}`.  If `n > 0`, `s mod Iⁿ⁺¹ L` lies in the kernel of `L / Iⁿ⁺¹ L ⟶ L / Iⁿ L`, which by
flatness is a finite sum of copies of `L / I L`
(`AlgebraicGeometry.Space.isIso_adicGradedKernelLift`); some component is a nonzero map
`𝒪_X ⟶ L / I L`, and one concludes as before.

## Main results

* `AlgebraicGeometry.Space.exists_unit_hom_comp_idealPowerQuotient_π_ne_zero`: a nonzero section
  of a coherent module on a proper space over a complete base is nonzero on some adic fibre,
  that is, modulo some `Iⁿ⁺¹`.
* `AlgebraicGeometry.Space.exists_unit_hom_idealPowerQuotient_one_ne_zero`: on a proper flat
  space, a nonzero section of an invertible module gives a nonzero section of `L / I L`.
* `AlgebraicGeometry.Space.exists_unit_hom_adicFibre_zero_ne_zero`: **a nonzero section of `L`
  gives a nonzero section of `L|_{X₀}`.**

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology hasCokernels_modules

section Main

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (I : Ideal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ schemeSpace (baseObject A B hA))

/-- **A nonzero section of a coherent module stays nonzero on some adic fibre**: for `X` proper
over a Noetherian `I`-adically complete ring `A` and a coherent `𝒪_X`-module `M`, a nonzero
`s : 𝒪_X ⟶ M` followed by the unit `M ⟶ (ιₙ)_* ιₙ^* M ≅ M / Iⁿ⁺¹ M` is nonzero for some `n`.
The restriction functor to the adic fibres is faithful (Stacks 08BF), and `ιₙ^* s` is adjoint
to that composite. -/
theorem exists_unit_hom_comp_idealPowerQuotient_π_ne_zero [IsNoetherianRing A]
    [IsAdicComplete I A] (hf : IsProper B (Spec (.of A)) hA f.hom)
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hM : IsCoherent B (Spec (.of A)) hA X.1 X.2 M)
    (s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⟶ M)
    (hs : s ≠ 0) :
    ∃ n : ℕ, s ≫ (modulePullbackAdjunction B (Spec (.of A)) hA
      (adicFibreInclusion A I B hA X f n)).unit.app M ≠ 0 := by
  let := SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  let O := SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))
  let ι := adicFibreInclusion A I B hA X f
  have := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.2.1.1
  have hO : IsInvertibleModule X O := Stacks.SheafOfModules.isInvertible_unit _ _
  have hOc : IsCoherent B (Spec (.of A)) hA X.1 X.2 O := isCoherent_of_isInvertible O hO
  by_contra hcon
  push Not at hcon
  have hpull : ∀ n, (modulePullback B (Spec (.of A)) hA (ι n)).map s =
      (modulePullback B (Spec (.of A)) hA (ι n)).map (0 : O ⟶ M) := fun n => by
    have h1 : s ≫ (modulePullbackAdjunction B (Spec (.of A)) hA (ι n)).unit.app M = 0 :=
      hcon n
    refine ((modulePullbackAdjunction B (Spec (.of A)) hA (ι n)).homEquiv _ _).injective ?_
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_naturality,
      Adjunction.unit_naturality, h1, zero_comp]
  have := isEquivalence_adicFibreRestriction_of_isProper I X f hf
  have hmap : (ObjectProperty.homMk s :
      (⟨O, hOc⟩ : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2) ⟶ ⟨M, hM⟩) =
        ObjectProperty.homMk 0 :=
    (adicFibreRestrictionOf I X f hf.2.1.1).map_injective (TowerSystem.hom_ext fun n => hpull n)
  exact hs (congrArg (fun χ => χ.hom) hmap)

/-- **On a proper flat space, a nonzero section of an invertible module gives a nonzero section
of `L / I L`.**  Take the least `n` with `s mod Iⁿ⁺¹ L ≠ 0`
(`AlgebraicGeometry.Space.exists_unit_hom_comp_idealPowerQuotient_π_ne_zero`); if `n > 0` the
image of `s` lies in the kernel of `L / Iⁿ⁺¹ L ⟶ L / Iⁿ L`, a finite sum of copies of `L / I L`
by flatness, and a nonzero component is the section sought. -/
theorem exists_unit_hom_idealPowerQuotient_one_ne_zero [IsNoetherianRing A] [IsAdicComplete I A]
    [I.IsMaximal] (hf : IsProper B (Spec (.of A)) hA f.hom)
    (hflat : IsFlat B (Spec (.of A)) hA f.hom)
    (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hL : IsInvertibleModule X L)
    (s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⟶ L)
    (hs : s ≠ 0) :
    ∃ c : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⟶
        idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L, c ≠ 0 := by
  let := SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  have := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.2.1.1
  have hLc : IsCoherent B (Spec (.of A)) hA X.1 X.2 L := isCoherent_of_isInvertible L hL
  let 𝓘 := baseIdealSheaf A X I
  let ι := adicFibreInclusion A I B hA X f
  have hι : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (ι n).hom :=
    isClosedImmersion_adicFibreFstHom A I B hA X.2 f.hom
  have hker : ∀ n (N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      kerIdealSmul B (Spec (.of A)) hA (ι n) N =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) N :=
    fun n N => kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple A I B hA X.2 f.hom n N
  have hq := isUnitQuotient_idealPowerQuotient B (Spec (.of A)) hA ι hι hker L
  have hex : ∃ n : ℕ, s ≫ cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1)
      L).ι ≠ 0 := by
    obtain ⟨n, hn⟩ := exists_unit_hom_comp_idealPowerQuotient_π_ne_zero I X f hf L hLc s hs
    exact ⟨n, fun h => hn (by rw [← hq.comp_hom n, ← Category.assoc, h, zero_comp])⟩
  obtain ⟨n, hn, hmin⟩ := WellFounded.has_min wellFounded_lt
    {n : ℕ | s ≫ cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) L).ι ≠ 0}
    hex
  cases n with
  | zero => exact ⟨_, hn⟩
  | succ m =>
    have hm : s ≫ cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (m + 1) L).ι =
        0 := by
      by_contra h
      exact hmin m h (Nat.lt_succ_self m)
    obtain ⟨r, a, ha, hspan, hind⟩ := Ideal.exists_pow_basis_lift I (m + 1)
    have hLq : IsCartesianOnAffineCharts L :=
      isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 L
        (isQuasicoherentOnSite_of_isInvertibleModule X L hL)
    have hiso := isIso_adicGradedKernelLift I X L (m + 1) r a ha hLq
      (fun V hV => (adicGraded_chart_conditions I X f hflat L hL hspan hind V hV).1)
      (fun V hV => (adicGraded_chart_conditions I X f hflat L hL hspan hind V hV).2)
    let c := s ≫ cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (m + 1 + 1) L).ι
    have hc : c ≫ idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 𝓘 (Nat.le_succ (m + 1))
        L = 0 := by
      rw [Category.assoc, π_comp_idealPowerQuotientMapOfLE]
      exact hm
    let k := kernel.lift _ c hc
    let g := k ≫ inv (adicGradedKernelLift I X L (m + 1) r a ha)
    have hg : g ≠ 0 := by
      intro h0
      apply hn
      change c = 0
      have hkι : k ≫ kernel.ι _ = c := kernel.lift_ι _ _ _
      have hkg : k = g ≫ adicGradedKernelLift I X L (m + 1) r a ha := by
        simp only [g, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← hkι, hkg, h0, zero_comp, zero_comp]
    by_contra hall
    push Not at hall
    exact hg (biproduct.hom_ext _ _ fun i => by rw [hall (g ≫ biproduct.π _ i), zero_comp])

/-- **A nonzero section of an invertible module gives a nonzero section on the closed fibre.**
Let `A` be a Noetherian ring complete with respect to a maximal ideal `I`, let `X` be a proper
flat algebraic space over `Spec A` and `X₀ = X ×_{Spec A} Spec(A/I)`.  For an invertible
`𝒪_X`-module `L` and a nonzero `s : 𝒪_X ⟶ L` there is a nonzero `t : 𝒪_{X₀} ⟶ L|_{X₀}`: a
nonzero `𝒪_X ⟶ L / I L ≅ (ι₀)_* ι₀^* L`
(`AlgebraicGeometry.Space.exists_unit_hom_idealPowerQuotient_one_ne_zero`) is adjoint to one. -/
theorem exists_unit_hom_adicFibre_zero_ne_zero [IsNoetherianRing A] [IsAdicComplete I A]
    [I.IsMaximal] (hf : IsProper B (Spec (.of A)) hA f.hom)
    (hflat : IsFlat B (Spec (.of A)) hA f.hom)
    (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hL : IsInvertibleModule X L)
    (s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⟶ L)
    (hs : s ≠ 0) :
    ∃ t : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f 0).1
          (adicFibreSpaceOf A I B hA X f 0).2).O)) ⟶
        (modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f 0)).obj L,
      t ≠ 0 := by
  let ι := adicFibreInclusion A I B hA X f
  let adj := modulePullbackAdjunction B (Spec (.of A)) hA (ι 0)
  have hι : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (ι n).hom :=
    isClosedImmersion_adicFibreFstHom A I B hA X.2 f.hom
  have hker : ∀ n (N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      kerIdealSmul B (Spec (.of A)) hA (ι n) N =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1) N :=
    fun n N => kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple A I B hA X.2 f.hom n N
  obtain ⟨c, hc⟩ := exists_unit_hom_idealPowerQuotient_one_ne_zero I X f hf hflat L hL s hs
  obtain ⟨e, -⟩ := exists_idealPowerQuotient_iso_comp_eq_unit_comp B (Spec (.of A)) hA ι hι
    hker 0 L _ (Iso.refl _)
  have := adj.isRightAdjoint
  have hpz := Functor.preservesZeroMorphisms_of_isRightAdjoint
    (modulePushforward B (Spec (.of A)) hA (ι 0))
  let O := SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))
  let L₀ := (modulePullback B (Spec (.of A)) hA (ι 0)).obj L
  let φ : (modulePullback B (Spec (.of A)) hA (ι 0)).obj O ⟶ L₀ :=
    (adj.homEquiv O L₀).symm (c ≫ e.hom)
  refine ⟨(modulePullbackUnitIso B (Spec (.of A)) hA (ι 0)).inv ≫ φ, fun h0 => hc ?_⟩
  have h1 : φ = 0 := ((Iso.inv_comp_eq _).mp h0).trans comp_zero
  have h2 : c ≫ e.hom = 0 := by
    have h3 : adj.homEquiv O L₀ φ = c ≫ e.hom := (adj.homEquiv O L₀).apply_symm_apply _
    rw [← h3, h1, Adjunction.homEquiv_unit, hpz.map_zero, comp_zero]
  exact ((Iso.eq_comp_inv e).mpr h2).trans zero_comp

end Main

end AlgebraicGeometry.Space

end
