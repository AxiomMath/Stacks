module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.RingTheory.Support
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroup
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentReflexive
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso.CoherentFiltration

/-!
# Dévissage of `K_0(Coh_Z(X))`: filtered short exact sequences and locally finite arrays

Third part of the proof of [Stacks, Tag 0FDT] (see
`StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso`). A short exact
sequence `0 → ℱ → 𝒢 → ℋ → 0` filtered by `ℱ ∩ ℐⁿ𝒢 ⊂ ℐⁿ𝒢 ↠ ℐⁿℋ`, its rows and their graded
pieces; the exchange of a double coproduct; and coherence of the coproducts of a locally finite
array of coherent modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.SupportedCoherentDevissage

open Scheme.Modules TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.IdealPower (idealPowerMultiple idealPowerMultiple_le_iff)
open Stacks.AlgebraicGeometry.CoherenceCriteria (coherent_tfae)
open Stacks.AlgebraicGeometry.Tag087TCoherentImage (CoherentAnnihilatedModules AnnihilatedByKer)
open scoped AlgebraicGeometry

section

-- `X.Modules` and its morphisms are definitions over `SheafOfModules`; the lemmas below are
-- stated on either side, and instance search has to see through both.
attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom

local instance {X : Scheme.{u}} (M : X.Modules) [M.IsCoherent] : M.IsQuasicoherent :=
  isQuasicoherent_of_isCoherent M

local instance {X : Scheme.{u}} (M : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    M.obj.IsCoherent :=
  CoherentAbelian.isCoherent_of_stacksIsCoherent M.property

private lemma shortExact_of_pullback {C : Type*} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) {A B D : C}
    {t : A ⟶ S.X₁} {a : A ⟶ B} {b : B ⟶ S.X₂}
    (sq : IsPullback t a S.f b) (g : B ⟶ D) (j : D ⟶ S.X₃)
    (hj : Mono j) (hg : Epi g) (comm : g ≫ j = b ≫ S.g) :
    ∃ w : a ≫ g = 0, (ShortComplex.mk a g w).ShortExact := by
  have := hj
  have := hg
  have : Mono S.f := hS.mono_f
  have : Mono a := PullbackCone.mono_snd_of_is_pullback_of_mono sq.isLimit
  have w : a ≫ g = 0 := by
    apply (cancel_mono j).mp
    rw [zero_comp, Category.assoc, comm, ← Category.assoc, ← sq.w,
      Category.assoc, S.zero, comp_zero]
  refine ⟨w, { exact := ?_ }⟩
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hS.fIsKernel (k ≫ b) (by
    rw [Category.assoc, ← comm, ← Category.assoc, hk, zero_comp])
  exact ⟨sq.lift l k hl, sq.lift_snd _ _ _⟩

noncomputable def submoduleIsoOfEq {X : Scheme.{u}} {M : X.Modules}
    {P Q : M.Submodule} (h : P = Q) : P.toSheafOfModules ≅ Q.toSheafOfModules where
  hom := submoduleInclusion h.le
  inv := submoduleInclusion h.ge
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

lemma shortExact_square_isPullback {C : Type*} [Category.{v} C] [Abelian C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (v : S ⟶ T) [Mono v.τ₃] : IsPullback S.f v.τ₁ v.τ₂ T.f := by
  have : Mono S.f := hS.mono_f
  have : Mono T.f := hT.mono_f
  have w : S.f ≫ v.τ₂ = v.τ₁ ≫ T.f := v.comm₁₂.symm
  apply IsPullback.of_isLimit (c := PullbackCone.mk S.f v.τ₁ w)
  let lift (c : PullbackCone v.τ₂ T.f) : c.pt ⟶ S.X₁ :=
    (KernelFork.IsLimit.lift' hS.fIsKernel c.fst (by
      apply (cancel_mono v.τ₃).mp
      rw [zero_comp, Category.assoc, ← v.comm₂₃, ← Category.assoc,
        c.condition, Category.assoc, T.zero, comp_zero])).1
  have hf (c : PullbackCone v.τ₂ T.f) : lift c ≫ S.f = c.fst :=
    (KernelFork.IsLimit.lift' hS.fIsKernel _ _).2
  have hg (c : PullbackCone v.τ₂ T.f) : lift c ≫ v.τ₁ = c.snd := by
    apply (cancel_mono T.f).mp
    rw [Category.assoc, v.comm₁₂, ← Category.assoc, hf, c.condition]
  refine PullbackCone.IsLimit.mk w lift hf hg ?_
  intro c m hm _
  exact (cancel_mono S.f).mp (hm.trans (hf c).symm)

noncomputable def shortExactCokernelIso {C : Type*} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) : cokernel S.f ≅ S.X₃ :=
  (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel

private lemma shortExactCokernelIso_π {C : Type*} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    cokernel.π S.f ≫ (shortExactCokernelIso hS).hom = S.g := by
  exact (cokernelIsCokernel S.f).comp_coconePointUniqueUpToIso_hom hS.gIsCokernel
    WalkingParallelPair.one

noncomputable def gradedCokernelIso {C : Type*} [Category.{v} C] [Abelian C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (v : S ⟶ T) :
    cokernel (cokernel.map v.τ₁ v.τ₂ S.f T.f v.comm₁₂) ≅ cokernel v.τ₃ :=
  (doubleCokernelIso S.f v.τ₁ v.τ₂ T.f v.comm₁₂.symm).symm ≪≫
    cokernel.mapIso _ v.τ₃ (shortExactCokernelIso hS) (shortExactCokernelIso hT) (by
      apply (cancel_epi (cokernel.π S.f)).mp
      calc
        cokernel.π S.f ≫ cokernel.map S.f T.f v.τ₁ v.τ₂ v.comm₁₂.symm ≫
            (shortExactCokernelIso hT).hom =
            v.τ₂ ≫ cokernel.π T.f ≫ (shortExactCokernelIso hT).hom := by
          simp only [cokernel.π_desc_assoc, Category.assoc]
        _ = v.τ₂ ≫ T.g := by rw [shortExactCokernelIso_π]
        _ = S.g ≫ v.τ₃ := v.comm₂₃
        _ = cokernel.π S.f ≫ (shortExactCokernelIso hS).hom ≫ v.τ₃ := by
          rw [← Category.assoc, shortExactCokernelIso_π])

noncomputable def filteredRow {X : Scheme.{u}} (I : X.IdealSheafData)
    (S : ShortComplex X.Modules) (_hS : S.ShortExact) (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk
    (comapProjection S.f (idealPowerMultiple I n S.X₂))
    ((idealPowerMultipleFunctor I n).map S.g) (by
      have : Mono (idealPowerMultiple I n S.X₃).ι :=
        mono_submodule_ι _
      apply (cancel_mono (idealPowerMultiple I n S.X₃).ι).mp
      refine Eq.trans ?_ zero_comp.symm
      exact (Category.assoc _ _ _).trans <|
        (congrArg (comapProjection S.f (idealPowerMultiple I n S.X₂) ≫ ·)
          (idealPowerMultipleFunctor_map_comp_ι I n S.g)).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ S.g) (sheafSubmoduleMap_comp_ι S.f _ _ le_rfl)).trans <|
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) S.zero).trans comp_zero)

lemma filteredRow_shortExact {X : Scheme.{u}} (I : X.IdealSheafData)
    (S : ShortComplex X.Modules) [S.X₃.IsQuasicoherent] (hS : S.ShortExact) (n : ℕ) :
    (filteredRow I S hS n).ShortExact := by
  have : Epi S.g := hS.epi_g
  exact (shortExact_of_pullback hS (comapIsPullback S.f _)
    ((idealPowerMultipleFunctor I n).map S.g)
    (idealPowerMultiple I n S.X₃).ι
    (by exact mono_submodule_ι _) (by exact idealPowerMultipleFunctor_epi I n S.g)
    (idealPowerMultipleFunctor_map_comp_ι I n S.g)).choose_spec

lemma submoduleMap_inclusion {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {P P' : M.Submodule} {Q Q' : N.Submodule}
    (hP : P ≤ P') (hQ : Q ≤ Q')
    (h : P ≤ sheafSubmoduleComap f Q) (h' : P' ≤ sheafSubmoduleComap f Q') :
    submoduleInclusion hP ≫ sheafSubmoduleMap f P' Q' h' =
      sheafSubmoduleMap f P Q h ≫ submoduleInclusion hQ := by
  ext U s
  rfl

lemma comapProjection_inclusion {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {P Q : N.Submodule} (h : P ≤ Q) :
    submoduleInclusion (show sheafSubmoduleComap f P ≤ sheafSubmoduleComap f Q from
      fun U _ hs => h U hs) ≫ comapProjection f Q =
        comapProjection f P ≫ submoduleInclusion h :=
  submoduleMap_inclusion f _ h le_rfl le_rfl

noncomputable def filteredRowStep {X : Scheme.{u}} (I : X.IdealSheafData)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    filteredRow I S hS (n + 1) ⟶ filteredRow I S hS n where
  τ₁ := submoduleInclusion (M := S.X₁)
    (P := sheafSubmoduleComap S.f (idealPowerMultiple I (n + 1) S.X₂))
    (Q := sheafSubmoduleComap S.f (idealPowerMultiple I n S.X₂))
    (fun U _ hs => idealPowerMultiple_antitone I S.X₂ (Nat.le_succ n) U hs)
  τ₂ := idealPowerStep I S.X₂ n
  τ₃ := idealPowerStep I S.X₃ n
  comm₁₂ := comapProjection_inclusion S.f (idealPowerMultiple_antitone I S.X₂ (Nat.le_succ n))
  comm₂₃ := submoduleMap_inclusion S.g
    (idealPowerMultiple_antitone I S.X₂ (Nat.le_succ n))
    (idealPowerMultiple_antitone I S.X₃ (Nat.le_succ n))
    (idealPowerMultiple_le_comap I (n + 1) S.g _ le_rfl)
    (idealPowerMultiple_le_comap I n S.g _ le_rfl)

noncomputable def sigmaCokernelIso {C : Type*} [Category.{v} C] [Abelian C]
    {A B : ℕ → C} [HasCoproduct A] [HasCoproduct B]
    (f : ∀ n, A n ⟶ B n) [HasCoproduct (fun n => cokernel (f n))] :
    cokernel (Limits.Sigma.map f) ≅ ∐ fun n => cokernel (f n) :=
  (cokernelIsCokernel (Limits.Sigma.map f)).coconePointUniqueUpToIso
    (sigmaMapCokernelIsColimit f)

noncomputable def sigmaExchange {C : Type*} [Category.{v} C]
    [HasColimitsOfShape (Discrete ℕ) C] (A : ℕ → ℕ → C) :
    (∐ fun n => ∐ fun m => A n m) ≅ ∐ fun m => ∐ fun n => A n m where
  hom := Sigma.desc fun n => Sigma.desc fun m =>
    Sigma.ι (fun n => A n m) n ≫ Sigma.ι (fun m => ∐ fun n => A n m) m
  inv := Sigma.desc fun m => Sigma.desc fun n =>
    Sigma.ι (fun m => A n m) m ≫ Sigma.ι (fun n => ∐ fun m => A n m) n
  hom_inv_id := by
    apply Sigma.hom_ext
    intro n
    apply Sigma.hom_ext
    intro m
    simp
  inv_hom_id := by
    apply Sigma.hom_ext
    intro m
    apply Sigma.hom_ext
    intro n
    simp

abbrev LocallyFiniteArray {X : Scheme.{u}} (A : ℕ → ℕ → X.Modules) : Prop :=
  ∀ U : X.affineOpens, ∃ N : ℕ, ∀ n m, N ≤ n ∨ N ≤ m →
    IsZero ((restrictFunctor U.1.ι).obj (A n m))

lemma coherent_array_row {X : Scheme.{u}} [IsLocallyNoetherian X]
    (A : ℕ → ℕ → X.Modules) (hc : ∀ n m, (A n m).IsCoherent)
    (hz : LocallyFiniteArray A) (n : ℕ) : (∐ A n).IsCoherent := by
  apply coherent_natCoproduct_of_eventually_isZero_restrict _ (hc n)
  intro U
  obtain ⟨N, hN⟩ := hz U
  exact ⟨N, fun m hm => hN n m (Or.inr hm)⟩

lemma array_row_locallyZero {X : Scheme.{u}} (A : ℕ → ℕ → X.Modules)
    (hz : LocallyFiniteArray A) :
    ∀ U : X.affineOpens, ∃ N : ℕ, ∀ n, N ≤ n →
      IsZero ((restrictFunctor U.1.ι).obj (∐ A n)) := by
  intro U
  obtain ⟨N, hN⟩ := hz U
  refine ⟨N, fun n hn => ?_⟩
  exact (isZero_coproduct _ (fun m => hN n m (Or.inl hn))).of_iso
    (PreservesCoproduct.iso (restrictFunctor U.1.ι) (A n))

lemma coherent_array_coproduct {X : Scheme.{u}} [IsLocallyNoetherian X]
    (A : ℕ → ℕ → X.Modules) (hc : ∀ n m, (A n m).IsCoherent)
    (hz : LocallyFiniteArray A) : (∐ fun n => ∐ A n).IsCoherent :=
  coherent_natCoproduct_of_eventually_isZero_restrict _
    (coherent_array_row A hc hz) (array_row_locallyZero A hz)

end

end AlgebraicGeometry.SupportedCoherentDevissage

end
