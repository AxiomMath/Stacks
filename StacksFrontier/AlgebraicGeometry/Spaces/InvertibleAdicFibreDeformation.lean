module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleAdicFibreTriviality
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineCohomologyPushforwardNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerTowerCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartSectionsProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleChartSections
public import StacksFrontier.RingTheory.Flat.AdicGradedPieceFlat

/-!
# Deformations of a trivial invertible module along the adic fibres

Let `A` be a Noetherian ring complete with respect to a maximal ideal `I`, let `X` be a proper
flat algebraic space over `Spec A` and write `Xₙ = X ×_{Spec A} Spec(A/Iⁿ⁺¹)`.  If
`H¹(X₀, 𝒪_{X₀}) = 0`, an invertible `𝒪_X`-module `L` whose restriction to the closed fibre `X₀`
is trivial is trivial.

This is the step "`H¹(X, 𝒪_X) = 0` (hence all deformations of `𝒪_X` to
`Y × Spec(k[[xᵢ]]/𝔪ⁿ)` are trivial)" of the argument of the Stacks project preceding Tag 0D1R,
combined with the Grothendieck existence step of
`StacksFrontier/AlgebraicGeometry/Spaces/InvertibleAdicFibreTriviality.lean`.

## Main results

* `AlgebraicGeometry.Space.flat_chartBaseRingHom_of_isFlat`: the ring of an affine étale chart of
  a flat algebraic space over `Spec A` is flat over `A`.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isClosedImmersion`: the
  cohomology of a direct image along a closed immersion vanishes when that of the module does.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology hasCokernels_modules

/-! ### Finite sums of acyclic objects -/

section Biproduct

/-- An additive functor vanishing on `Q` vanishes on a finite sum of copies of `Q`. -/
theorem isZero_obj_biproduct_of_isZero_obj {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] (Q : C) {r : ℕ}
    [HasBiproduct (fun _ : Fin r => Q)] (h : IsZero (F.obj Q)) :
    IsZero (F.obj (⨁ fun _ : Fin r => Q)) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← F.map_id, ← biproduct.total, F.map_sum]
  exact Finset.sum_eq_zero fun i _ => by
    rw [F.map_comp, h.eq_zero_of_tgt (F.map (biproduct.π (fun _ : Fin r => Q) i)), zero_comp]

end Biproduct

/-! ### Flatness of the chart rings -/

section Flatness

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (f : X ⟶ schemeSpace (baseObject A B hA))

/-- **The ring of an affine étale chart of a flat algebraic space over `Spec A` is flat over
`A`**: the chart's structure morphism to `Spec A` is flat, and for a morphism of affine schemes
that is flatness of the ring map of global functions. -/
theorem flat_chartBaseRingHom_of_isFlat (hflat : IsFlat B (Spec (.of A)) hA f.hom)
    (V : SmallEtale B (Spec (.of A)) hA X.1)
    (hV : IsAffine ((SmallEtale.toOver B (Spec (.of A)) hA X.1 ⋙
      BigFppfOver.toScheme B (Spec (.of A)) hA).obj V)) :
    (chartBaseRingHom A X V).Flat := by
  have hfl := hflat V.obj.left (selfChart B (Spec (.of A)) hA (baseObject A B hA)).obj.left
    V.obj.hom (selfChart B (Spec (.of A)) hA (baseObject A B hA)).obj.hom
    (chartToBaseObject A B hA V) V.property
    (selfChart B (Spec (.of A)) hA (baseObject A B hA)).property
    ((isTerminal_yoneda_obj_base B _ hA).hom_ext _ _)
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V.obj.left) := hV
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (selfChart B (Spec (.of A)) hA (baseObject A B hA)).obj.left) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have h1 := HasRingHomProperty.appTop (P := @AlgebraicGeometry.Flat) _ hfl
  rw [← appTop_chartToBaseObject_comp_ΓSpecIso_inv A B hA X.2 V]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)) h1

end Flatness

/-! ### Cohomology of a direct image along a closed immersion -/

section Pushforward

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The cohomology of a direct image along a closed immersion vanishes with that of the
module**: a closed immersion is affine (Stacks 07U2), so `Hⁱ(X, ι_*F) ≅ Hⁱ(Z, F)` for a
quasi-coherent `F` (Stacks 0D2U). -/
theorem isZero_rightDerived_modulePushforward_of_isClosedImmersion {Z X : AlgebraicSpaces B S hS}
    (ι : Z ⟶ X) (hι : IsClosedImmersion B S hS ι.hom) (F : Modules.{u, u} B S hS Z.1 Z.2)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ)
    (h : have := hasInjectiveResolutions_modules B S hS Z.1 Z.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Z.1 Z.2).O)).rightDerived i).obj F)) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived
        i).obj ((modulePushforward B S hS ι).obj F)) :=
  ((globalSectionsRestrictScalars B S hS ι).map_isZero h).of_iso
    (cohomologyPushforwardLinearIsoOfIsAffineHom B S hS ι
      (isAffineHom_of_isClosedImmersion B S hS ι.hom hι) F hF i).symm

end Pushforward

/-! ### Lifting sections along an epimorphism with `H¹`-acyclic kernel -/

section Lifting

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Sections lift along an epimorphism whose kernel has vanishing `H¹`**: for an epimorphism
`g : M ⟶ N` of `𝒪_X`-modules with `H¹(X, ker g) = 0`, every section `𝒪_X ⟶ N` factors through
`g`.  This is the long exact cohomology sequence of `0 → ker g → M → N → 0` in degree zero. -/
theorem exists_unit_hom_comp_eq_of_isZero_rightDerived_one_kernel {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N) [Epi g]
    (h : have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj (kernel g)))
    (b : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶ N) :
    ∃ a : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶ M, a ≫ g = b := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have := preservesFiniteLimits_globalSectionsFunctor_ringUniverse
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let T : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
    ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel g)
      mono_f := inferInstanceAs (Mono (kernel.ι g))
      epi_g := inferInstanceAs (Epi g) }
  have h0 := Stacks.Cohomology.RightDerivedDelta.epi_rightDerived_zero_map_g
    (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) hT h
  set Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  have hΓ : Epi (Γ.map g) := by
    have e := Γ.rightDerivedZeroIsoSelf.hom.naturality g
    have : Epi (Γ.rightDerivedZeroIsoSelf.hom.app M ≫ Γ.map g) := by
      rw [← e]
      exact epi_comp' h0 inferInstance
    exact epi_of_epi (Γ.rightDerivedZeroIsoSelf.hom.app M) (Γ.map g)
  obtain ⟨σ, hσ⟩ := (ModuleCat.epi_iff_surjective (Γ.map g)).1 hΓ (N.unitHomEquiv b)
  refine ⟨M.unitHomEquiv.symm σ, N.unitHomEquiv.injective ?_⟩
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  exact (congrArg (SheafOfModules.sectionsMap g) (M.unitHomEquiv.apply_symm_apply σ)).trans hσ

end Lifting

/-! ### Sections of finite sums of morphisms -/

section Sums

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The sections of a finite sum of morphisms of `𝒪_X`-modules are the sums of the sections. -/
theorem val_app_sum_apply {ι : Type*} (s : Finset ι) {M N : Modules.{u, u} B S hS X.1 X.2}
    (f : ι → (M ⟶ N)) (U : ((smallEtaleRingedSite B S hS X.1 X.2).C)ᵒᵖ) (x : M.val.obj U) :
    (∑ i ∈ s, f i).val.app U x = ∑ i ∈ s, (f i).val.app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

end Sums

/-! ### The graded pieces of an adic filtration of a flat module -/

section GradedPiece

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (I : Ideal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)

/-- The structure ring map `A ⟶ 𝒪_X(V)` of an étale chart, with values in the ring acting on the
sections of `𝒪_X`-modules over `V`. -/
abbrev chartRingBaseHom (V : SmallEtale B (Spec (.of A)) hA X.1) :
    A →+* chartRing B (Spec (.of A)) hA X.1 X.2 V :=
  chartBaseRingHom A X V

/-- **Multiplication by `b ∈ Iʲ` as a map `L / I L ⟶ L / Iʲ⁺¹ L`.** -/
def adicGradedSmul (j : ℕ) (b : A) (hb : b ∈ I ^ j) :
    idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L ⟶
      idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (j + 1) L :=
  cokernel.desc _ (globalSmul _ (baseRingHom A B hA X.1 X.2 b) L ≫
      cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (j + 1)
        L).ι) (by
    refine (idealPowerMultiple_ι_comp_eq_zero_iff B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) 1 _).mpr fun U r hr x => ?_
    change (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (j + 1) L).ι).val.app (op U) ((globalSmul _ (baseRingHom A B hA X.1 X.2 b) L).val.app
        (op U) (r • x)) = 0
    rw [globalSmul_app, smul_smul, map_smul]
    refine isPowAnnihilated_idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (j + 1) L U _ ?_ _
    rw [pow_succ]
    exact Ideal.mul_mem_mul (chartBaseRingHom_mem_pow_baseIdealSheaf X I hb U) (by simpa using hr))

/-- The projection `L ⟶ L / I L` followed by multiplication by `b` is multiplication by `b`
followed by the projection `L ⟶ L / Iʲ⁺¹ L`. -/
@[reassoc]
theorem π_adicGradedSmul (j : ℕ) (b : A) (hb : b ∈ I ^ j) :
    cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L).ι ≫
        adicGradedSmul I X L j b hb =
      globalSmul _ (baseRingHom A B hA X.1 X.2 b) L ≫
        cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (j + 1)
          L).ι :=
  cokernel.π_desc _ _ _

/-- Multiplication by `b ∈ Iʲ` followed by `L / Iʲ⁺¹ L ⟶ L / Iʲ L` is zero. -/
theorem adicGradedSmul_comp_idealPowerQuotientMapOfLE (j : ℕ) (b : A) (hb : b ∈ I ^ j) :
    adicGradedSmul I X L j b hb ≫ idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) (Nat.le_succ j) L = 0 := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2
    (baseIdealSheaf A X I) 1 L).ι)).1 ?_
  rw [π_adicGradedSmul_assoc, π_comp_idealPowerQuotientMapOfLE, ← comp_globalSmul,
    globalSmul_idealPowerQuotient_eq_zero X I L hb, comp_zero, comp_zero]

variable (j r : ℕ) (a : Fin r → A) (ha : ∀ i, a i ∈ I ^ j)

/-- The map `⨁ᵢ L / I L ⟶ L / Iʲ⁺¹ L`, `(xᵢ) ↦ ∑ aᵢ xᵢ`. -/
def adicGradedSum : (⨁ fun _ : Fin r =>
      idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L) ⟶
    idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (j + 1) L :=
  biproduct.desc fun i => adicGradedSmul I X L j (a i) (ha i)

theorem adicGradedSum_comp_idealPowerQuotientMapOfLE :
    adicGradedSum I X L j r a ha ≫ idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) (Nat.le_succ j) L = 0 := by
  refine biproduct.hom_ext' _ _ fun i => ?_
  rw [adicGradedSum, biproduct.ι_desc_assoc, adicGradedSmul_comp_idealPowerQuotientMapOfLE,
    comp_zero]

/-- The lift of `adicGradedSum` to the kernel of `L / Iʲ⁺¹ L ⟶ L / Iʲ L`. -/
def adicGradedKernelLift : (⨁ fun _ : Fin r =>
      idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L) ⟶
    kernel (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (Nat.le_succ j) L) :=
  kernel.lift _ (adicGradedSum I X L j r a ha)
    (adicGradedSum_comp_idealPowerQuotientMapOfLE I X L j r a ha)

/-- On sections, multiplication by `b` sends the class of `x` to the class of `b • x`. -/
theorem adicGradedSmul_val_app_π (j : ℕ) (b : A) (hb : b ∈ I ^ j)
    (V : SmallEtale B (Spec (.of A)) hA X.1) (x : L.val.obj (op V)) :
    (adicGradedSmul I X L j b hb).val.app (op V)
        ((cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1
          L).ι).val.app (op V) x) =
      (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (j + 1)
        L).ι).val.app (op V) (chartRingBaseHom X V b • x) :=
  congrArg (fun φ => φ.val.app (op V) x) (π_adicGradedSmul I X L j b hb)

/-- On sections, `adicGradedSum` sends the `i`-th summand to multiplication by `aᵢ`. -/
theorem adicGradedSum_val_app_ι (i : Fin r)
    (V : SmallEtale B (Spec (.of A)) hA X.1) (y : (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) 1 L).val.obj (op V)) :
    (adicGradedSum I X L j r a ha).val.app (op V)
        ((biproduct.ι (fun _ : Fin r => idealPowerQuotient B (Spec (.of A)) hA X.1 X.2
          (baseIdealSheaf A X I) 1 L) i).val.app (op V) y) =
      (adicGradedSmul I X L j (a i) (ha i)).val.app (op V) y := by
  have h : biproduct.ι (fun _ : Fin r => idealPowerQuotient B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) 1 L) i ≫ adicGradedSum I X L j r a ha =
        adicGradedSmul I X L j (a i) (ha i) := biproduct.ι_desc _ i
  exact congrArg (fun φ => φ.val.app (op V) y) h

/-- Every section of `⨁ᵢ Q` is the sum of its components. -/
theorem eq_sum_biproduct_val_app {Q : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (V : SmallEtale B (Spec (.of A)) hA X.1) (s : (⨁ fun _ : Fin r => Q).val.obj (op V)) :
    s = ∑ i, (biproduct.ι (fun _ : Fin r => Q) i).val.app (op V)
      ((biproduct.π (fun _ : Fin r => Q) i).val.app (op V) s) := by
  have h := congrArg (fun φ => φ.val.app (op V) s) (biproduct.total (f := fun _ : Fin r => Q))
  simp only at h
  rw [val_app_sum_apply] at h
  exact h.symm

/-- On sections, the lift to the kernel followed by the inclusion of the kernel is
`adicGradedSum`. -/
theorem kernel_ι_val_app_adicGradedKernelLift (V : SmallEtale B (Spec (.of A)) hA X.1)
    (s : (⨁ fun _ : Fin r => idealPowerQuotient B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) 1 L).val.obj (op V)) :
    (kernel.ι (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (Nat.le_succ j) L)).val.app (op V) ((adicGradedKernelLift I X L j r a ha).val.app (op V) s) =
      (adicGradedSum I X L j r a ha).val.app (op V) s := by
  have h : adicGradedKernelLift I X L j r a ha ≫ kernel.ι (idealPowerQuotientMapOfLE B
      (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (Nat.le_succ j) L) =
        adicGradedSum I X L j r a ha := kernel.lift_ι _ _ _
  exact congrArg (fun φ => φ.val.app (op V) s) h

/-- On sections, `adicGradedSum` sends `∑ᵢ ιᵢ (x̄ᵢ)` to the class of `∑ᵢ aᵢ xᵢ`. -/
theorem adicGradedSum_val_app_sum (V : SmallEtale B (Spec (.of A)) hA X.1)
    (x : Fin r → L.val.obj (op V)) :
    (adicGradedSum I X L j r a ha).val.app (op V)
        (∑ i, (biproduct.ι (fun _ : Fin r => idealPowerQuotient B (Spec (.of A)) hA X.1 X.2
          (baseIdealSheaf A X I) 1 L) i).val.app (op V)
          ((cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1
            L).ι).val.app (op V) (x i))) =
      (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (j + 1)
        L).ι).val.app (op V) (∑ i, chartRingBaseHom X V (a i) • x i) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adicGradedSum_val_app_ι, adicGradedSmul_val_app_π]

variable {I X L j r a} in
/-- **`adicGradedSum` is injective on the sections over an affine chart** where `(xᵢ) ↦ ∑ aᵢ xᵢ`
is injective modulo `I`. -/
theorem injective_adicGradedSum_val_app (hLc : IsCartesianOnAffineCharts L)
    {V : SmallEtale B (Spec (.of A)) hA X.1} (hV : IsAffineChart B (Spec (.of A)) hA X.1 V)
    (hinj : ∀ x : Fin r → L.val.obj (op V),
        ∑ i, chartRingBaseHom X V (a i) • x i ∈
          chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ (j + 1) •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) →
        ∀ i, x i ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ 1 •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V)))) :
    Function.Injective ((adicGradedSum I X L j r a ha).val.app (op V)) := by
  classical
  have hIc := isCartesianOnAffineCharts_baseIdealSheaf A X I
  have hsur := fun k => surjective_val_app_idealPowerQuotient_π B (Spec (.of A)) hA X.1 X.2
    (baseIdealSheaf A X I) hIc L hLc k hV
  have hmemker : ∀ k (z : L.val.obj (op V)),
      (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        L).ι).val.app (op V) z = 0 ↔
      z ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ k •
        (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) :=
    fun k z => by
      rw [← ker_val_app_idealPowerQuotient_π B (Spec (.of A)) hA X.1 X.2
        (baseIdealSheaf A X I) hIc L hLc k hV]
      rfl
  refine (injective_iff_map_eq_zero ((adicGradedSum I X L j r a ha).val.app (op V)).hom).2
    fun w hw => ?_
  choose x hx using fun i => hsur 1 ((biproduct.π (fun _ : Fin r => idealPowerQuotient B
    (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L) i).val.app (op V) w)
  have hw' : w = ∑ i, (biproduct.ι (fun _ : Fin r => idealPowerQuotient B (Spec (.of A)) hA X.1
      X.2 (baseIdealSheaf A X I) 1 L) i).val.app (op V)
        ((cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1
          L).ι).val.app (op V) (x i)) := by
    refine (eq_sum_biproduct_val_app X r V w).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [hx i]
  have hw2 := hw
  change (adicGradedSum I X L j r a ha).val.app (op V) w = 0 at hw2
  rw [hw', adicGradedSum_val_app_sum, hmemker] at hw2
  have hx0 : ∀ i, (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) 1 L).ι).val.app (op V) (x i) = 0 := fun i =>
    (hmemker 1 (x i)).2 (hinj x hw2 i)
  rw [hw']
  simp only [hx0, map_zero, Finset.sum_const_zero]

variable {I X L j r a} in
/-- **Every section of the kernel of `L / Iʲ⁺¹ L ⟶ L / Iʲ L` over an affine chart is in the image
of `adicGradedSum`** where `(xᵢ) ↦ ∑ aᵢ xᵢ` maps onto `Iʲ L(V)` modulo `Iʲ⁺¹ L(V)`. -/
theorem exists_adicGradedSum_val_app_eq (hLc : IsCartesianOnAffineCharts L)
    {V : SmallEtale B (Spec (.of A)) hA X.1} (hV : IsAffineChart B (Spec (.of A)) hA X.1 V)
    (hsurj : ∀ y : L.val.obj (op V),
        y ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ j •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) →
        ∃ x : Fin r → L.val.obj (op V), y - ∑ i, chartRingBaseHom X V (a i) • x i ∈
          chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ (j + 1) •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))))
    (y : (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (j + 1)
      L).val.obj (op V))
    (hy : (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (Nat.le_succ j) L).val.app (op V) y = 0) :
    ∃ w, (adicGradedSum I X L j r a ha).val.app (op V) w = y := by
  classical
  have hIc := isCartesianOnAffineCharts_baseIdealSheaf A X I
  have hmemker : ∀ k (z : L.val.obj (op V)),
      (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        L).ι).val.app (op V) z = 0 ↔
      z ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ k •
        (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) :=
    fun k z => by
      rw [← ker_val_app_idealPowerQuotient_π B (Spec (.of A)) hA X.1 X.2
        (baseIdealSheaf A X I) hIc L hLc k hV]
      rfl
  obtain ⟨z, hz⟩ := surjective_val_app_idealPowerQuotient_π B (Spec (.of A)) hA X.1 X.2
    (baseIdealSheaf A X I) hIc L hLc (j + 1) hV y
  have hzj := (hmemker j z).1 (by
    have h := congrArg (fun φ => φ.val.app (op V) z)
      (π_comp_idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
        (Nat.le_succ j) L)
    have h2 : (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
        (Nat.le_succ j) L).val.app (op V) ((cokernel.π (idealPowerMultiple B (Spec (.of A)) hA
          X.1 X.2 (baseIdealSheaf A X I) (j + 1) L).ι).val.app (op V) z) = 0 := by
      rw [hz]
      exact hy
    exact h.symm.trans h2)
  obtain ⟨x, hx⟩ := hsurj z hzj
  refine ⟨∑ i, (biproduct.ι (fun _ : Fin r => idealPowerQuotient B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) 1 L) i).val.app (op V)
        ((cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1
          L).ι).val.app (op V) (x i)), ?_⟩
  rw [adicGradedSum_val_app_sum, ← hz, ← sub_eq_zero, ← map_sub, hmemker, ← neg_mem_iff,
    neg_sub]
  exact hx

/-- **The graded piece `Iʲ L / Iʲ⁺¹ L` of a flat module is a finite sum of copies of `L / I L`**:
the lift of `(xᵢ) ↦ ∑ aᵢ xᵢ` to the kernel of `L / Iʲ⁺¹ L ⟶ L / Iʲ L` is an isomorphism, as soon
as, on every affine étale chart, `(xᵢ) ↦ ∑ aᵢ xᵢ` is injective modulo `I` and surjective onto
`Iʲ L(V)` modulo `Iʲ⁺¹ L(V)`. -/
theorem isIso_adicGradedKernelLift (hLc : IsCartesianOnAffineCharts L)
    (hinj : ∀ V : SmallEtale B (Spec (.of A)) hA X.1, IsAffineChart B (Spec (.of A)) hA X.1 V →
      ∀ x : Fin r → L.val.obj (op V),
        ∑ i, chartRingBaseHom X V (a i) • x i ∈
          chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ (j + 1) •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) →
        ∀ i, x i ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ 1 •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))))
    (hsurj : ∀ V : SmallEtale B (Spec (.of A)) hA X.1, IsAffineChart B (Spec (.of A)) hA X.1 V →
      ∀ y : L.val.obj (op V),
        y ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ j •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) →
        ∃ x : Fin r → L.val.obj (op V), y - ∑ i, chartRingBaseHom X V (a i) • x i ∈
          chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ (j + 1) •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V)))) :
    IsIso (adicGradedKernelLift I X L j r a ha) := by
  refine isIso_of_forall_bijective_val_app_affine_chart B (Spec (.of A)) hA X _ fun V hV => ?_
  have hκ := kernel_ι_val_app_adicGradedKernelLift I X L j r a ha V
  have hψ := injective_adicGradedSum_val_app ha hLc hV (hinj V hV)
  have hιinj := Stacks.SheafOfModules.injective_app_of_mono (kernel.ι
    (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (Nat.le_succ j) L)) (op V)
  refine ⟨fun s t hst => hψ ((hκ s).symm.trans ((congrArg _ hst).trans (hκ t))), fun t => ?_⟩
  have hy := congrArg (fun φ => φ.val.app (op V) t) (kernel.condition
    (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (Nat.le_succ j) L))
  obtain ⟨w, hw⟩ := exists_adicGradedSum_val_app_eq ha hLc hV (hsurj V hV) _ hy
  exact ⟨w, hιinj ((hκ w).trans hw)⟩

end GradedPiece

/-! ### The graded pieces of an invertible module on a flat space -/

section Flat

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (I : Ideal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ schemeSpace (baseObject A B hA))

/-- **The chartwise conditions of `isIso_adicGradedKernelLift` for an invertible module on a flat
space.**  On an affine étale chart `V`, `L(V)` is a projective module over the chart ring, which
is flat over `A`, so `L(V)` is flat over `A`; the two conditions are then the commutative algebra
of `Module.Flat.forall_mem_smul_top_of_sum_smul_mem` and
`Submodule.exists_sub_sum_smul_mem_pow_succ_smul_top`, read through `I · 𝒪_X(V) = I 𝒪_X(V)`. -/
theorem adicGraded_chart_conditions (hflat : IsFlat B (Spec (.of A)) hA f.hom)
    (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hL : IsInvertibleModule X L)
    {j r : ℕ} {a : Fin r → A}
    (hspan : I ^ j ≤ Ideal.span (Set.range a) ⊔ I ^ (j + 1))
    (hind : ∀ c : Fin r → A, ∑ i, c i * a i ∈ I ^ (j + 1) → ∀ i, c i ∈ I)
    (V : SmallEtale B (Spec (.of A)) hA X.1) (hV : IsAffineChart B (Spec (.of A)) hA X.1 V) :
    (∀ x : Fin r → L.val.obj (op V),
        ∑ i, chartRingBaseHom X V (a i) • x i ∈
          chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ (j + 1) •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) →
        ∀ i, x i ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ 1 •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V)))) ∧
    (∀ y : L.val.obj (op V),
        y ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ j •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))) →
        ∃ x : Fin r → L.val.obj (op V), y - ∑ i, chartRingBaseHom X V (a i) • x i ∈
          chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V ^ (j + 1) •
            (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V)))) := by
  have hR : (chartBaseRingHom A X V).Flat := flat_chartBaseRingHom_of_isFlat X f hflat V hV
  let : Algebra A (chartRing B (Spec (.of A)) hA X.1 X.2 V) := (chartRingBaseHom X V).toAlgebra
  let : Module A (L.val.obj (op V)) := Module.compHom _ (chartRingBaseHom X V)
  have : IsScalarTower A (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V)) :=
    ⟨fun b c x => mul_smul (chartRingBaseHom X V b) c x⟩
  have : Module.Flat A (chartRing B (Spec (.of A)) hA X.1 X.2 V) := hR
  have hfree : SheafOfModules.IsFiniteLocallyFreeOnSite L :=
    (isFiniteLocallyFreeOfRank_one_of_isInvertible B (Spec (.of A)) hA X L
      hL.toAlgebraicGeometry).isFiniteLocallyFreeOnSite
  have : Module.Projective (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V)) :=
    (module_finite_projective_sections_of_isFiniteLocallyFreeOnSite X.2 L hfree V hV).2
  have : Module.Flat A (L.val.obj (op V)) :=
    Module.Flat.trans A (chartRing B (Spec (.of A)) hA X.1 X.2 V) (L.val.obj (op V))
  have hJ : chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V =
      Ideal.map (algebraMap A (chartRing B (Spec (.of A)) hA X.1 X.2 V)) I :=
    baseIdealSheaf_obj_of_isAffine A X I V hV
  refine ⟨fun x hx i => ?_, fun y hy => ?_⟩
  · rw [hJ, Submodule.mem_map_pow_smul_top_iff] at hx ⊢
    rw [pow_one]
    exact Module.Flat.forall_mem_smul_top_of_sum_smul_mem hind hx i
  · rw [hJ, Submodule.mem_map_pow_smul_top_iff] at hy
    obtain ⟨x, hx⟩ := Submodule.exists_sub_sum_smul_mem_pow_succ_smul_top hspan hy
    exact ⟨x, by rw [hJ, Submodule.mem_map_pow_smul_top_iff]; exact hx⟩

/-- **The graded pieces `Iʲ⁺¹ L / Iʲ⁺² L`... have no `H¹`**: for an invertible module `L` on a flat
algebraic space over a Noetherian ring with a maximal ideal `I`, the kernel of
`L / Iʲ⁺¹ L ⟶ L / Iʲ L` is a finite sum of copies of `L / I L`, so it has no `H¹` once `L / I L`
has none. -/
theorem isZero_rightDerived_one_kernel_idealPowerQuotientMapOfLE [IsNoetherianRing A] [I.IsMaximal]
    (hflat : IsFlat B (Spec (.of A)) hA f.hom)
    (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hL : IsInvertibleModule X L)
    (hQ : have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X.1 X.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived 1).obj
            (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L)))
    (j : ℕ) :
    have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived 1).obj
          (kernel (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
            (Nat.le_succ j) L))) := by
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X.1 X.2
  obtain ⟨r, a, ha, hspan, hind⟩ := Ideal.exists_pow_basis_lift I j
  have hLc : IsCartesianOnAffineCharts L :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 L
      (isQuasicoherentOnSite_of_isInvertibleModule X L hL)
  have hiso := isIso_adicGradedKernelLift I X L j r a ha hLc
    (fun V hV => (adicGraded_chart_conditions I X f hflat L hL hspan hind V hV).1)
    (fun V hV => (adicGraded_chart_conditions I X f hflat L hL hspan hind V hV).2)
  set R1 := (globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived 1
  have hb := isZero_obj_biproduct_of_isZero_obj R1
    (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) 1 L) (r := r) hQ
  exact hb.of_iso (R1.mapIso (asIso (adicGradedKernelLift I X L j r a ha))).symm

end Flat

/-! ### Triviality from the closed fibre -/

section Main

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (I : Ideal A) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ schemeSpace (baseObject A B hA))

/-- **An invertible module on a proper flat space over a complete local base, trivial on the
closed fibre, is trivial when `H¹(X₀, 𝒪_{X₀}) = 0`.**  Let `A` be a Noetherian ring complete
with respect to a maximal ideal `I`, let `X` be a proper flat algebraic space over `Spec A` and
`X₀ = X ×_{Spec A} Spec(A/I)` its closed fibre.  If `H¹(X₀, 𝒪_{X₀}) = 0` and `L` is an invertible
`𝒪_X`-module with `L|_{X₀} ≅ 𝒪_{X₀}`, then `L ≅ 𝒪_X`.

Flatness makes every graded piece `Iʲ L / Iʲ⁺¹ L` a finite sum of copies of `L / I L`, which is
the direct image of `L|_{X₀} ≅ 𝒪_{X₀}`; so these have no `H¹`, every section of `L / I L` lifts
to every `L / Iᵏ L`, and by the theorem on formal functions (Stacks 08AY) to a section of `L`,
which trivializes `L` (`AlgebraicGeometry.Space.isIso_of_epi_comp_idealQuotientπ`).  This is the
step "`H¹(X, 𝒪_X) = 0` (hence all deformations of `𝒪_X` … are trivial) and Grothendieck's
existence theorem" of the argument of the Stacks project preceding Tag 0D1R. -/
theorem nonempty_iso_unit_of_adicFibre_zero_iso_unit [IsNoetherianRing A] [IsAdicComplete I A]
    [I.IsMaximal] (hf : IsProper B (Spec (.of A)) hA f.hom)
    (hflat : IsFlat B (Spec (.of A)) hA f.hom)
    (hH1 : have := hasInjectiveResolutions_modules B (Spec (.of A)) hA
                (adicFibreSpaceOf A I B hA X f 0).1 (adicFibreSpaceOf A I B hA X f 0).2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
          (adicFibreSpaceOf A I B hA X f 0).1 (adicFibreSpaceOf A I B hA X f 0).2).O)).rightDerived
            1).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f 0).1
                (adicFibreSpaceOf A I B hA X f 0).2).O)))))
    (L : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hL : IsInvertibleModule X L)
    (h0 : Nonempty ((modulePullback B (Spec (.of A)) hA
      (adicFibreInclusion A I B hA X f 0)).obj L ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f 0).1
            (adicFibreSpaceOf A I B hA X f 0).2).O)))) :
    Nonempty (L ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))) := by
  let := SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X.1 X.2
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA
    (adicFibreSpaceOf A I B hA X f 0).1 (adicFibreSpaceOf A I B hA X f 0).2
  let φ := baseRingHom A B hA X.1 X.2
  let 𝓘 := baseIdealSheaf A X I
  let O := SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))
  let ι := adicFibreInclusion A I B hA X f
  let adj := fun n => modulePullbackAdjunction B (Spec (.of A)) hA (ι n)
  have hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1) := by
    rw [(isTerminal_yoneda_obj_base B _ hA).hom_ext ((isTerminal_yoneda_obj_base B _ hA).from X.1)
      f.hom]
    exact hf
  have := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.2.1.1
  have hLc : IsCoherent B (Spec (.of A)) hA X.1 X.2 L := isCoherent_of_isInvertible L hL
  have hLq : L.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertibleModule X L hL
  have hι : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (ι n).hom :=
    isClosedImmersion_adicFibreFstHom A I B hA X.2 f.hom
  have hker : ∀ n (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      kerIdealSmul B (Spec (.of A)) hA (ι n) M =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) M :=
    fun n M => kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple A I B hA X.2 f.hom n M
  have hq := isUnitQuotient_idealPowerQuotient B (Spec (.of A)) hA ι hι hker L
  obtain ⟨e⟩ := h0
  -- `H¹(X, L / I L) = 0`: `L / I L` is the direct image of `L|_{X₀} ≅ 𝒪_{X₀}`.
  obtain ⟨e₁, -⟩ := exists_idealPowerQuotient_iso_comp_eq_unit_comp B (Spec (.of A)) hA ι hι
    hker 0 L _ (Iso.refl _)
  have hN : IsInvertibleModule (adicFibreSpaceOf A I B hA X f 0)
      ((modulePullback B (Spec (.of A)) hA (ι 0)).obj L) :=
    modulePullbackInvertible (ι 0) L hL
  have hQ1 : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived 1).obj
          (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 1 L)) :=
    (isZero_rightDerived_modulePushforward_of_isClosedImmersion (ι 0) (hι 0) _
      (isQuasicoherentOnSite_of_isInvertibleModule _ _ hN) 1
      (hH1.of_iso (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
          (adicFibreSpaceOf A I B hA X f 0).1 (adicFibreSpaceOf A I B hA X f 0).2).O)).rightDerived
            1).mapIso e))).of_iso (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived 1).mapIso e₁)
  -- Sections of `L / I L` lift along the tower.
  have hlift : ∀ n (b : O ⟶ idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) L),
      ∃ a : O ⟶ idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1 + 1) L,
        a ≫ idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 𝓘 (Nat.le_succ (n + 1)) L = b :=
    fun n b => by
      have : Epi (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 𝓘 (Nat.le_succ (n + 1))
          L) :=
        @epi_of_epi_fac _ _ _ _ _ _ _ _ (hq.epi n)
          (π_comp_idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 𝓘 (Nat.le_succ (n + 1)) L)
      exact exists_unit_hom_comp_eq_of_isZero_rightDerived_one_kernel _
        (isZero_rightDerived_one_kernel_idealPowerQuotientMapOfLE I X f hflat L hL hQ1 (n + 1)) b
  have htower : ∀ m (b : O ⟶ idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (0 + 1) L),
      ∃ a : O ⟶ idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (m + 1) L,
        a ≫ idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 𝓘
          (Nat.add_le_add_right (Nat.zero_le m) 1) L = b := by
    intro m b
    induction m with
    | zero => exact ⟨b, by rw [idealPowerQuotientMapOfLE_refl, Category.comp_id]⟩
    | succ m ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨a', ha'⟩ := hlift m a
      refine ⟨a', ?_⟩
      rw [← idealPowerQuotientMapOfLE_comp B (Spec (.of A)) hA X.1 X.2 𝓘
        (Nat.add_le_add_right (Nat.zero_le m) 1) (Nat.le_succ (m + 1)), ← Category.assoc, ha', ha]
  -- The trivialization on `X₀` gives an epimorphism `𝒪_X ⟶ L / I L`.
  let e₂ := e ≪≫ (modulePullbackUnitIso B (Spec (.of A)) hA (ι 0)).symm
  obtain ⟨e', -⟩ := exists_idealPowerQuotient_iso_comp_eq_unit_comp B (Spec (.of A)) hA ι hι hker
    0 L _ e₂
  have hηO : Epi ((adj 0).unit.app O) := by
    have hqO := isUnitQuotient_idealPowerQuotient B (Spec (.of A)) hA ι hι hker O
    rw [← hqO.comp_hom 0]
    exact @epi_comp' _ _ _ _ _ _ _ (hqO.epi 0) (IsIso.epi_of_iso _)
  let b' : O ⟶ idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (0 + 1) L :=
    (adj 0).unit.app O ≫ e'.inv
  have hb' : Epi b' := epi_comp' hηO (IsIso.epi_of_iso _)
  -- Lift it far enough, then to `L` by the theorem on formal functions.
  obtain ⟨k, h1k, hk⟩ := exists_unit_hom_comp_idealQuotientπ_eq I X hX L (0 + 1)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a', ha'⟩ := htower m b'
  obtain ⟨s, hs⟩ := hk (a' ≫ (idealQuotientIsoIdealPowerQuotient X I L hLq (m + 1)).inv)
  have hcomm : (idealQuotientIsoIdealPowerQuotient X I L hLq (m + 1)).inv ≫
      idealQuotientMap φ L (Ideal.pow_le_pow_right h1k) =
        idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 𝓘 h1k L ≫
          (idealQuotientIsoIdealPowerQuotient X I L hLq (0 + 1)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact idealQuotientMap_comp_idealQuotientToIdealPowerQuotient X I L h1k
  have hsπ : Epi (s ≫ idealQuotientπ φ L (I ^ (0 + 1))) := by
    rw [hs, Category.assoc, hcomm, ← Category.assoc, ha']
    exact epi_comp' hb' (IsIso.epi_of_iso _)
  have hsiso : IsIso s := isIso_of_epi_comp_idealQuotientπ I X f hf L hL s hsπ
  exact ⟨(asIso s).symm⟩

end Main

end AlgebraicGeometry.Space

end
