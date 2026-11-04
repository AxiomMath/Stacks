module

public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.RingTheory.SerreIntersection.EqualCharacteristic
public import StacksFrontier.RingTheory.Tor.BaseChangeOfUniverse

/-!
# Serre's vanishing and positivity for a regular local ring containing a field
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v

namespace Stacks.SerreIntersection

section Transfer

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing A] [IsLocalRing R]
  [Module.Flat A R]

/-- **Flat base change of the Tor modules, for lengths.** Along a flat local map `A → R` with
`𝔪_A R = 𝔪_R`, the Tor modules of `R ⊗_A M` and `R ⊗_A N` over `R` have the lengths of the Tor
modules of `M` and `N` over `A`, when `M ⊗_A N` is supported in the closed point. -/
theorem length_tor_baseChange (hm : Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R)
    [IsNoetherianRing A] (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A}) (i : ℕ) :
    Module.length R (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R (R ⊗[A] M))).obj
        (ModuleCat.of R (R ⊗[A] N))) =
      Module.length A (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A N)) := by
  let eM := (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A R
    (ModuleCat.of A M)).toModuleIso
  let eN := (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A R
    (ModuleCat.of A N)).toModuleIso
  let T := ((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj (ModuleCat.of A N)
  let eT := (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv A R T).toModuleIso
  let iso : ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R (R ⊗[A] M))).obj
      (ModuleCat.of R (R ⊗[A] N)) ≅ ModuleCat.of R (R ⊗[A] T) :=
    ((Tor (ModuleCat.{u} R) i).mapIso eM.symm).app _ ≪≫
      ((Tor (ModuleCat.{u} R) i).obj _).mapIso eN.symm ≪≫
      (torBaseChangeIsoOfUniverse (S := A) (S' := R) i (ModuleCat.of A M) (ModuleCat.of A N)).symm
      ≪≫ eT
  rw [iso.toLinearEquiv.length_eq]
  exact length_baseChange hm T (Module.length_ne_top_iff.mp
    (Stacks.Intersection.length_tor_ne_top_of_support_subset M N hMN i))

/-- The Euler characteristic `χ(M, N)` is unchanged along a flat local map with trivial closed
fibre. -/
theorem torEulerCharacteristic_baseChange
    (hm : Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R)
    [IsNoetherianRing A] (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A}) :
    Stacks.Intersection.torEulerCharacteristic R (R ⊗[A] M) (R ⊗[A] N) =
      Stacks.Intersection.torEulerCharacteristic A M N := by
  unfold Stacks.Intersection.torEulerCharacteristic
  congr 1
  funext i
  rw [length_tor_baseChange hm M N hMN i]

end Transfer

section Field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- Serre's vanishing and positivity for a regular local ring containing a field, in one
statement: the reduction to the power series model, where both are
`PowerSeriesDiagonal.serre_mvPowerSeries`. -/
theorem torEulerCharacteristic_vanishing_and_positivity_of_field (F : Type v) [Field F]
    [Algebra F A] (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A}) :
    (Module.supportDim A M + Module.supportDim A N < ringKrullDim A →
        Stacks.Intersection.torEulerCharacteristic A M N = 0) ∧
      (Module.supportDim A M + Module.supportDim A N = ringKrullDim A →
        0 < Stacks.Intersection.torEulerCharacteristic A M N) := by
  obtain ⟨e⟩ := nonempty_completion_ringEquiv_model A F
  let : Algebra A (Model A) := (modelMap A e).toAlgebra
  have : Module.Flat A (Model A) := flat_modelMap A e
  have hm : Ideal.map (algebraMap A (Model A)) (maximalIdeal A) = maximalIdeal (Model A) :=
    map_modelMap_maximalIdeal A e
  have := nontrivial_baseChange hm M
  have := nontrivial_baseChange hm N
  have hsupp := support_subset_closedPoint_tensor hm M N hMN
  let : Module (PowerSeriesModel A) (Model A ⊗[A] M) :=
    (inferInstance : Module (Model A) (Model A ⊗[A] M))
  let : Module (PowerSeriesModel A) (Model A ⊗[A] N) :=
    (inferInstance : Module (Model A) (Model A ⊗[A] N))
  have : Module.Finite (PowerSeriesModel A) (Model A ⊗[A] M) :=
    (inferInstance : Module.Finite (Model A) (Model A ⊗[A] M))
  have : Module.Finite (PowerSeriesModel A) (Model A ⊗[A] N) :=
    (inferInstance : Module.Finite (Model A) (Model A ⊗[A] N))
  have key := (PowerSeriesDiagonal.serre_mvPowerSeries (Model A ⊗[A] M) (Model A ⊗[A] N)
    hsupp).2
  have hM : Module.supportDim (PowerSeriesModel A) (Model A ⊗[A] M) = Module.supportDim A M :=
    supportDim_baseChange hm M
  have hN : Module.supportDim (PowerSeriesModel A) (Model A ⊗[A] N) = Module.supportDim A N :=
    supportDim_baseChange hm N
  have hR : ringKrullDim (PowerSeriesModel A) = ringKrullDim A := ringKrullDim_model A e
  have hχ : Stacks.Intersection.torEulerCharacteristic (PowerSeriesModel A) (Model A ⊗[A] M)
      (Model A ⊗[A] N) = Stacks.Intersection.torEulerCharacteristic A M N :=
    torEulerCharacteristic_baseChange hm M N hMN
  rw [hM, hN, hR, hχ] at key
  exact key

/-- **Serre's vanishing for a regular local ring containing a field.** Let `A` be a regular local
ring containing a field and let `M`, `N` be nonzero finite `A`-modules with `M ⊗_A N` supported in
the closed point. If `dim Supp M + dim Supp N < dim A`, then `χ(M, N) = 0`. -/
@[stacks 0B0X "(1) when A contains a field: r + s < dim A gives χ(M, N) = 0"]
theorem torEulerCharacteristic_eq_zero_of_field (F : Type v) [Field F] [Algebra F A]
    (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A})
    (hlt : Module.supportDim A M + Module.supportDim A N < ringKrullDim A) :
    Stacks.Intersection.torEulerCharacteristic A M N = 0 :=
  (torEulerCharacteristic_vanishing_and_positivity_of_field F M N hMN).1 hlt

/-- **Serre's positivity for a regular local ring containing a field.** Let `A` be a regular
local ring containing a field and let `M`, `N` be nonzero finite `A`-modules with `M ⊗_A N`
supported in the closed point. If `dim Supp M + dim Supp N = dim A`, then `χ(M, N) > 0`. -/
@[stacks 0B0X "(2) when A contains a field: r + s = dim A gives χ(M, N) > 0"]
theorem torEulerCharacteristic_pos_of_field (F : Type v) [Field F] [Algebra F A]
    (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A})
    (heq : Module.supportDim A M + Module.supportDim A N = ringKrullDim A) :
    0 < Stacks.Intersection.torEulerCharacteristic A M N :=
  (torEulerCharacteristic_vanishing_and_positivity_of_field F M N hMN).2 heq

end Field

end Stacks.SerreIntersection
