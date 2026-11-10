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
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso.IdealPowerFiltration

/-!
# Dévissage of `K_0(Coh_Z(X))`: coherent filtrations with annihilated quotients

Second part of the proof of [Stacks, Tag 0FDT] (see
`StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso`). For a closed
subscheme with ideal sheaf `ℐ`: the quotients `ℐⁿℱ/ℐⁿ⁺¹ℱ` are annihilated by `ℐ`; the short
exact sequences relating `⊕_{p ≥ 0} ℐᵖℱ`, `⊕_{p ≥ 1} ℐᵖℱ` and `gr ℱ`; intersections of
subsheaves as pullbacks; and locally finite coherent filtrations with quotients annihilated by
`ℐ`, among them the `ℐ`-adic filtration and the filtration a filtration induces on a submodule.
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

private lemma locallySurjective_of_epi {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Epi f] :
    TopCat.Presheaf.IsLocallySurjective ((Scheme.Modules.toPresheaf X).map f) := by
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
  intro x
  let G := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits X.ringCatSheaf x
  have hf : Epi (C := SheafOfModules X.ringCatSheaf) f := ‹Epi f›
  exact (ModuleCat.epi_iff_surjective (G.map f)).mp (G.map_epi f)

/-- Shrinking an open `V ≤ U` around `x` to an affine open keeps `a` in the `n`-th power of the
ideal. -/
private lemma exists_affineOpen_restrict_mem_ideal_pow {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) {U : X.affineOpens} {V : X.Opens} (hVU : V ≤ U.1) {x : X} (hxV : x ∈ V)
    {a : Γ(X, U)} (ha : a ∈ I.ideal U ^ n) :
    ∃ (W : X.affineOpens) (hWV : W.1 ≤ V), x ∈ W.1 ∧
      (X.presheaf.map (homOfLE (hWV.trans hVU)).op).hom a ∈ I.ideal W ^ n := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  refine ⟨⟨W, hW⟩, hWV, hxW, ?_⟩
  rw [← I.map_ideal (hWV.trans hVU), ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

lemma ideal_smul_idealPowerMultiple_mem {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (a : Γ(X, U)) (ha : a ∈ I.ideal U)
    (s : Γ(M, U))
    (hs : s ∈ (idealPowerMultiple I n M).toSubmodule.obj (op U.1)) :
    a • s ∈ (idealPowerMultiple I (n + 1) M).toSubmodule.obj (op U.1) := by
  rw [Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple] at hs ⊢
  rw [pow_succ', Submodule.mul_smul]
  exact Submodule.smul_mem_smul ha hs

lemma annihilated_cokernel_of_ideal_smul {X : Scheme.{u}}
    (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(N, U), ∃ t : Γ(M, U), f.val.app (op U.1) t = a • s) :
    ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(cokernel f, U), a • s = 0 := by
  intro U a ha s
  let g := cokernel.π f
  have hg := (TopCat.Presheaf.isLocallySurjective_iff _).mp (locallySurjective_of_epi g)
  apply (cokernel f).isSheaf.section_ext
  intro x hx
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ := hg U.1 s x hx
  obtain ⟨Waff, hWV, hxW, haW⟩ := exists_affineOpen_restrict_mem_ideal_pow I 1 hVU hxV
    (by rwa [pow_one])
  rw [pow_one] at haW
  have hWU := hWV.trans hVU
  let W := Waff.1
  let aW : Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom a
  obtain ⟨v, hv⟩ := h Waff aW haW (N.presheaf.map (homOfLE hWV).op t)
  refine ⟨W, hWU, hxW, ?_⟩
  change (cokernel f).presheaf.map (homOfLE hWU).op (a • s) =
    (cokernel f).presheaf.map (homOfLE hWU).op 0
  rw [map_zero, Scheme.Modules.map_smul]
  have htW : g.val.app (op W) (N.presheaf.map (homOfLE hWV).op t) =
      (cokernel f).presheaf.map (homOfLE hWU).op s := by
    rw [← restrict_comp_apply (cokernel f) hWV hVU s]
    have hn := congrArg (fun z => z t) (g.val.naturality (homOfLE hWV).op)
    exact hn.trans (congrArg ((cokernel f).presheaf.map (homOfLE hWV).op) ht)
  have htW' : g.app W (N.presheaf.map (homOfLE hWV).op t) =
      (cokernel f).presheaf.map (homOfLE hWU).op s := by
    convert! htW using 1
  rw [← htW']
  change aW • g.app W (N.presheaf.map (homOfLE hWV).op t) = 0
  rw [← Scheme.Modules.Hom.app_smul]
  change g.val.app (op W) (aW • N.presheaf.map (homOfLE hWV).op t) = 0
  rw [← hv]
  exact congrArg (fun z : M ⟶ cokernel f => z.val.app (op W) v) (cokernel.condition f)

lemma mono_sigmaMap {C : Type*} [Category.{v} C]
    [HasColimitsOfShape (Discrete ℕ) C]
    [(colim : (Discrete ℕ ⥤ C) ⥤ C).PreservesMonomorphisms]
    {F G : ℕ → C} (f : ∀ n, F n ⟶ G n) [∀ n, Mono (f n)] :
    Mono (Limits.Sigma.map f) := by
  let φ : Discrete.functor F ⟶ Discrete.functor G := Discrete.natTrans (fun n => f n.as)
  have : ∀ n, Mono (φ.app n) := fun n => inferInstanceAs (Mono (f n.as))
  have : Mono φ := NatTrans.mono_of_mono_app φ
  exact colim.map_mono' φ (coproductIsCoproduct F) (coproductIsCoproduct G)
    (Limits.Sigma.map f) (fun n => by simp [φ])

noncomputable def idealPowerStep {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (idealPowerMultiple I (n + 1) M).toSheafOfModules ⟶
      (idealPowerMultiple I n M).toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (idealPowerMultiple_antitone I M (Nat.le_succ n))⟩

lemma mono_idealPowerStep {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) : Mono (idealPowerStep I M n) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  change Mono (PresheafOfModules.Submodule.homOfLE
    (idealPowerMultiple_antitone I M (Nat.le_succ n)))
  infer_instance

lemma annihilated_idealPowerStep_cokernel {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(cokernel (idealPowerStep I M n), U), a • s = 0 := by
  apply annihilated_cokernel_of_ideal_smul
  intro U a ha s
  exact ⟨⟨a • (show Γ(M, U.1) from s.val),
    ideal_smul_idealPowerMultiple_mem I n M U a ha s.val s.property⟩,
    Subtype.ext rfl⟩

private lemma annihilated_stalk {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules)
    (h : ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(M, U), a • s = 0)
    (U : X.affineOpens) (a : Γ(X, U)) (ha : a ∈ I.ideal U)
    (x : X) (hx : x ∈ U.1) (s : (AlgebraicGeometry.SheafOfModules.stalkFunctor
      X.ringCatSheaf x).obj M) :
    (TopCat.Presheaf.germ X.ringCatSheaf.obj U.1 x hx).hom a • s = 0 := by
  obtain ⟨V, hVU, hxV, t, ht⟩ := M.presheaf.exists_le_germ_eq s hx
  obtain ⟨Waff, hWV, hxW, haW⟩ := exists_affineOpen_restrict_mem_ideal_pow I 1 hVU hxV
    (by rwa [pow_one])
  rw [pow_one] at haW
  have hWU := hWV.trans hVU
  let W := Waff.1
  let aW : Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom a
  let tW : Γ(M, W) := M.presheaf.map (homOfLE hWV).op t
  have hga : (TopCat.Presheaf.germ X.ringCatSheaf.obj W x hxW).hom aW =
      (TopCat.Presheaf.germ X.ringCatSheaf.obj U.1 x hx).hom a :=
    TopCat.Presheaf.germ_res_apply X.ringCatSheaf.obj (homOfLE hWU) x hxW a
  have hgt : (M.presheaf.germ W x hxW).hom tW = s := by
    exact (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hWV) x hxW t).trans ht
  rw [← hga, ← hgt]
  exact (PresheafOfModules.germ_ringCat_smul M.val x W hxW aW tW).symm.trans
    ((congrArg (fun t => (M.presheaf.germ W x hxW).hom t) (h Waff aW haW tW)).trans
      (map_zero _))

lemma annihilated_natCoproduct {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : ℕ → X.Modules)
    (h : ∀ n (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(F n, U), a • s = 0) :
    ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(∐ F, U), a • s = 0 := by
  intro U a ha s
  apply TopCat.Presheaf.section_ext ⟨(∐ F).presheaf, (∐ F).isSheaf⟩ U.1
  intro x hx
  let G := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  let R := TopCat.Presheaf.stalk X.ringCatSheaf.obj x
  let H := G ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  have := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits X.ringCatSheaf x
  have : PreservesColimitsOfSize.{0, 0} G := preservesColimitsOfSize_shrink G
  let r : R := (TopCat.Presheaf.germ X.ringCatSheaf.obj U.1 x hx).hom a
  let μ : H.obj (∐ F) ⟶ H.obj (∐ F) := AddCommGrpCat.ofHom
    { toFun := fun t => r • t
      map_zero' := smul_zero r
      map_add' := smul_add r }
  have hμ : μ = 0 := by
    apply (isColimitOfHasCoproductOfPreservesColimit H F).hom_ext
    intro n
    ext t
    change r • (G.map (Limits.Sigma.ι F n.as)).hom t = 0
    rw [← LinearMap.map_smul]
    rw [annihilated_stalk I (F n.as) (h n.as) U a ha x hx t, map_zero]
  have hzero : r • (show G.obj (∐ F) from
      (TopCat.Presheaf.germ (∐ F).presheaf U.1 x hx).hom s) = 0 :=
    congrArg (fun k : H.obj (∐ F) ⟶ H.obj (∐ F) =>
      k.hom ((TopCat.Presheaf.germ (∐ F).presheaf U.1 x hx).hom s)) hμ
  change (TopCat.Presheaf.germ (∐ F).val.presheaf U.1 x hx).hom (a • s) =
    (TopCat.Presheaf.germ (∐ F).val.presheaf U.1 x hx).hom 0
  exact (PresheafOfModules.germ_ringCat_smul (∐ F).val x U.1 hx a s).trans
    (hzero.trans (map_zero _).symm)

lemma sigmaMap_cokernel_condition {C : Type*} [Category.{v} C] [Abelian C]
    {F G : ℕ → C} [HasCoproduct F] [HasCoproduct G]
    (f : ∀ n, F n ⟶ G n) [HasCoproduct (fun n => cokernel (f n))] :
    Limits.Sigma.map f ≫ Limits.Sigma.map (fun n => cokernel.π (f n)) = 0 := by
  apply Limits.Sigma.hom_ext
  intro n
  simp

noncomputable def sigmaMapCokernelIsColimit
    {C : Type*} [Category.{v} C] [Abelian C]
    {F G : ℕ → C} [HasCoproduct F] [HasCoproduct G]
    (f : ∀ n, F n ⟶ G n) [HasCoproduct (fun n => cokernel (f n))] :
    IsColimit (CokernelCofork.ofπ (Limits.Sigma.map (fun n => cokernel.π (f n)))
      (sigmaMap_cokernel_condition f)) := by
  refine Limits.isColimitAux _
    (fun s => Limits.Sigma.desc (fun n => cokernel.desc (f n)
      (Limits.Sigma.ι G n ≫ s.π) ?_)) ?_ ?_
  · rw [← Limits.Sigma.ι_map_assoc, s.condition, comp_zero]
  · intro s
    apply Limits.Sigma.hom_ext
    intro n
    simp
  · intro s m hm
    apply Limits.Sigma.hom_ext
    intro n
    apply (cancel_epi (cokernel.π (f n))).mp
    have hn := congrArg (fun k => Limits.Sigma.ι G n ≫ k) hm
    simpa using hn

lemma sigmaMap_cokernel_shortExact {C : Type*} [Category.{v} C] [Abelian C]
    [HasColimitsOfShape (Discrete ℕ) C]
    [(colim : (Discrete ℕ ⥤ C) ⥤ C).PreservesMonomorphisms]
    {F G : ℕ → C} (f : ∀ n, F n ⟶ G n) [∀ n, Mono (f n)] :
    (ShortComplex.mk (Limits.Sigma.map f)
      (Limits.Sigma.map (fun n => cokernel.π (f n)))
      (sigmaMap_cokernel_condition f)).ShortExact := by
  have := mono_sigmaMap f
  have h := sigmaMapCokernelIsColimit f
  have : Epi (Limits.Sigma.map (fun n => cokernel.π (f n))) :=
    Cofork.IsColimit.epi h
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ h) inferInstance inferInstance

private lemma coherent_idealPowerStep_cokernel {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (M : X.Modules)
    [M.IsCoherent] (n : ℕ) : (cokernel (idealPowerStep I M n)).IsCoherent := by
  have := idealPowerMultiple_isCoherent I M n
  have := idealPowerMultiple_isCoherent I M (n + 1)
  exact SheafOfModules.cokernel_isCoherent (idealPowerStep I M n)

lemma coherent_idealPowerStep_cokernel_coproduct {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (M : X.Modules) [M.IsCoherent]
    (hM : SheafOfModules.supp M ⊆ (I.support : Set X)) :
    (∐ fun n => cokernel (idealPowerStep I M n)).IsCoherent := by
  apply coherent_natCoproduct_of_eventually_isZero_restrict _
    (coherent_idealPowerStep_cokernel I M)
  intro U
  obtain ⟨N, hN⟩ := idealPowerMultiple_eventually_isZero_restrict I M hM U
  refine ⟨N, fun n hn => ?_⟩
  exact isZero_restrict_cokernel (idealPowerStep I M n) U.1 (hN n hn)

noncomputable def coproductHeadTailComplex {C : Type*} [Category.{v} C]
    [Abelian C] (F : ℕ → C)
    [HasCoproduct F] [HasCoproduct (fun n => F (n + 1))] : ShortComplex C :=
  ShortComplex.mk (Limits.Sigma.ι F 0)
    (Limits.Sigma.desc (fun n => match n with
      | 0 => 0
      | n + 1 => Limits.Sigma.ι (fun j => F (j + 1)) n)) (by simp)

lemma coproductHeadTailComplex_shortExact {C : Type*} [Category.{v} C]
    [Abelian C] (F : ℕ → C)
    [HasCoproduct F] [HasCoproduct (fun n => F (n + 1))] :
    (coproductHeadTailComplex F).ShortExact := by
  have hid : (Limits.Sigma.desc (fun n => match n with | 0 => 𝟙 (F 0) | _ + 1 => 0) :
        (∐ F) ⟶ F 0) ≫ Limits.Sigma.ι F 0 +
      (Limits.Sigma.desc (fun n => match n with
        | 0 => 0
        | n + 1 => Limits.Sigma.ι (fun j => F (j + 1)) n) : (∐ F) ⟶ ∐ fun n => F (n + 1)) ≫
        Limits.Sigma.desc (fun n => Limits.Sigma.ι F (n + 1)) = 𝟙 (∐ F) := by
    apply Limits.Sigma.hom_ext
    rintro (_ | n) <;> simp [Preadditive.comp_add]
  apply ShortComplex.Splitting.shortExact
  refine
    { r := Limits.Sigma.desc (fun n => match n with | 0 => 𝟙 _ | _ + 1 => 0)
      s := Limits.Sigma.desc (fun n => Limits.Sigma.ι F (n + 1))
      f_r := by simp [coproductHeadTailComplex]
      s_g := ?_
      id := hid }
  apply Limits.Sigma.hom_ext
  intro n
  simp [coproductHeadTailComplex]

lemma idealPowerMultiple_eq_bot_of_annihilated {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules)
    (h : ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(M, U), a • s = 0) (n : ℕ) (hn : 1 ≤ n) :
    idealPowerMultiple I n M = ⊥ := by
  apply le_bot_iff.mp
  apply (idealPowerMultiple_le_iff I n M _).mpr
  intro U
  rw [bottom_toSubmodule]
  change I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤ ⊥
  have hI : I.ideal U ^ n ≤ I.ideal U := by
    simpa only [pow_one] using (Ideal.pow_le_pow_right (I := I.ideal U) hn)
  intro s hs
  change s = 0
  refine Submodule.smul_induction_on hs ?_ ?_
  · intro a ha m _
    exact h U a (hI ha) m
  · intro a b ha hb
    simp only [ha, hb, add_zero]

noncomputable def coproductIsoZeroOfIsZeroSucc {C : Type*}
    [Category.{v} C] [HasZeroMorphisms C] (F : ℕ → C) [HasCoproduct F]
    (h : ∀ n, IsZero (F (n + 1))) : (∐ F) ≅ F 0 := by
  refine
    { hom := Limits.Sigma.desc (fun n => match n with | 0 => 𝟙 _ | _ + 1 => 0)
      inv := Limits.Sigma.ι F 0
      hom_inv_id := ?_
      inv_hom_id := by simp }
  apply Limits.Sigma.hom_ext
  intro n
  cases n with
  | zero => simp
  | succ n => exact (h n).eq_of_src _ _

noncomputable def idealAssociatedGradedIsoOfAnnihilated {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules)
    (h : ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(M, U), a • s = 0) :
    (∐ fun n => cokernel (idealPowerStep I M n)) ≅ M := by
  have hz (n : ℕ) : IsZero
      (idealPowerMultiple I (n + 1) M).toSheafOfModules :=
    isZero_submodule_of_eq_bot _
      (idealPowerMultiple_eq_bot_of_annihilated I M h (n + 1) (Nat.le_add_left 1 n))
  have hq (n : ℕ) : IsZero (cokernel (idealPowerStep I M (n + 1))) :=
    IsZero.of_epi (cokernel.π (idealPowerStep I M (n + 1))) (hz n)
  have hf : idealPowerStep I M 0 = 0 := (hz 0).eq_of_src _ _
  haveI : IsIso (cokernel.π (idealPowerStep I M 0)) := cokernel.π_of_zero hf
  exact coproductIsoZeroOfIsZeroSucc _ hq ≪≫ (asIso (cokernel.π (idealPowerStep I M 0))).symm ≪≫
    eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules (idealPowerMultiple_zero I M)) ≪≫
      submoduleTopIso M

noncomputable def doubleCokernelComparison {C : Type*} [Category.{v} C] [Abelian C]
    {A B D E : C} (t : A ⟶ B) (l : A ⟶ D) (r : B ⟶ E) (b : D ⟶ E)
    (w : t ≫ r = l ≫ b) :
    cokernel (cokernel.map t b l r w) ⟶ cokernel (cokernel.map l r t b w.symm) := by
  let f := cokernel.map t b l r w
  let g := cokernel.map l r t b w.symm
  have hb : b ≫ (cokernel.π r ≫ cokernel.π g) = 0 := by
    have hπ : cokernel.π l ≫ g = b ≫ cokernel.π r := cokernel.π_desc _ _ _
    rw [← Category.assoc, ← hπ, Category.assoc, cokernel.condition, comp_zero]
  let k := cokernel.desc b (cokernel.π r ≫ cokernel.π g) hb
  refine cokernel.desc f k ?_
  apply (cancel_epi (cokernel.π t)).mp
  simp only [k, f, cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc,
    cokernel.condition_assoc, comp_zero, zero_comp]

private lemma doubleCokernelComparison_π {C : Type*} [Category.{v} C] [Abelian C]
    {A B D E : C} (t : A ⟶ B) (l : A ⟶ D) (r : B ⟶ E) (b : D ⟶ E)
    (w : t ≫ r = l ≫ b) :
    cokernel.π b ≫ cokernel.π (cokernel.map t b l r w) ≫
      doubleCokernelComparison t l r b w =
        cokernel.π r ≫ cokernel.π (cokernel.map l r t b w.symm) := by
  simp only [doubleCokernelComparison, cokernel.π_desc]

noncomputable def doubleCokernelIso {C : Type*} [Category.{v} C] [Abelian C]
    {A B D E : C} (t : A ⟶ B) (l : A ⟶ D) (r : B ⟶ E) (b : D ⟶ E)
    (w : t ≫ r = l ≫ b) :
    cokernel (cokernel.map t b l r w) ≅ cokernel (cokernel.map l r t b w.symm) where
  hom := doubleCokernelComparison t l r b w
  inv := doubleCokernelComparison l t b r w.symm
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (cokernel.map t b l r w))).mp
    apply (cancel_epi (cokernel.π b)).mp
    simp only [Category.comp_id]
    rw [← Category.assoc, ← Category.assoc, Category.assoc (cokernel.π b),
      doubleCokernelComparison_π]
    simpa only [Category.assoc] using doubleCokernelComparison_π l t b r w.symm
  inv_hom_id := by
    apply (cancel_epi (cokernel.π (cokernel.map l r t b w.symm))).mp
    apply (cancel_epi (cokernel.π r)).mp
    simp only [Category.comp_id]
    rw [← Category.assoc, ← Category.assoc, Category.assoc (cokernel.π r),
      doubleCokernelComparison_π]
    simpa only [Category.assoc] using doubleCokernelComparison_π t l r b w

noncomputable def submoduleInclusion {X : Scheme.{u}} {M : X.Modules}
    {P Q : M.Submodule} (h : P ≤ Q) : P.toSheafOfModules ⟶ Q.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE h⟩

lemma mono_submoduleInclusion {X : Scheme.{u}} {M : X.Modules}
    {P Q : M.Submodule} (h : P ≤ Q) : Mono (submoduleInclusion h) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  change Mono (PresheafOfModules.Submodule.homOfLE h)
  infer_instance

private lemma annihilated_inf_idealPowerMultiple_cokernel {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] (P : M.Submodule) (n : ℕ) :
    ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
      ∀ s : Γ(cokernel (submoduleInclusion
        (inf_le_inf_left P (idealPowerMultiple_antitone I M (Nat.le_succ n)))), U),
        a • s = 0 := by
  apply annihilated_cokernel_of_ideal_smul
  intro U a ha s
  refine ⟨⟨a • (show Γ(M, U.1) from s.val), ?_⟩, Subtype.ext rfl⟩
  change a • (show Γ(M, U.1) from s.val) ∈ P.toSubmodule.obj (op U.1) ∧
    a • (show Γ(M, U.1) from s.val) ∈ (idealPowerMultiple I (n + 1) M).toSubmodule.obj (op U.1)
  exact ⟨(P.toSubmodule.obj (op U.1)).smul_mem a s.property.1,
    ideal_smul_idealPowerMultiple_mem I n M U a ha s.val s.property.2⟩

private lemma inf_idealPowerMultiple_eventually_isZero_restrict {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (M : X.Modules) [M.IsCoherent]
    (hM : SheafOfModules.supp M ⊆ (I.support : Set X)) (P : M.Submodule)
    (U : X.affineOpens) :
    ∃ N : ℕ, ∀ n, N ≤ n → IsZero (Scheme.Modules.restrict
      (Y := X) (P ⊓ idealPowerMultiple I n M).toSheafOfModules U.1.ι) := by
  obtain ⟨N, hN⟩ := idealPowerMultiple_eventually_isZero_restrict I M hM U
  refine ⟨N, fun n hn => ?_⟩
  let f := submoduleInclusion (show P ⊓ idealPowerMultiple I n M ≤
    idealPowerMultiple I n M from inf_le_right)
  have : Mono f := mono_submoduleInclusion _
  have : Mono ((Scheme.Modules.restrictFunctor U.1.ι).map f) := Functor.map_mono _ _
  exact isZero_restrict_of_mono f (by exact inferInstance) U.1 (hN n hn)

private noncomputable def submoduleLift {X : Scheme.{u}} {M N : X.Modules}
    (f : N ⟶ M) (P : M.Submodule)
    (hf : ∀ U (s : N.val.obj U), f.val.app U s ∈ P.toSubmodule.obj U) :
    N ⟶ P.toSheafOfModules where
  val :=
    { app := fun U => ModuleCat.ofHom ((f.val.app U).hom.codRestrict _ (hf U))
      naturality := by
        intro U V g
        ext s
        apply Subtype.ext
        exact congrArg (fun k => k s) (PresheafOfModules.Hom.naturality f.val g) }

private lemma submoduleLift_comp_ι {X : Scheme.{u}} {M N : X.Modules}
    (f : N ⟶ M) (P : M.Submodule)
    (hf : ∀ U (s : N.val.obj U), f.val.app U s ∈ P.toSubmodule.obj U) :
    submoduleLift f P hf ≫ P.ι = f := by
  ext U s
  rfl

/-- A commutative square whose first leg is mono is a pullback if every cone factors through it. -/
private lemma isPullback_of_lift {C : Type*} [Category.{v} C] {A B D E : C}
    {f : A ⟶ B} {g : A ⟶ D} {h : B ⟶ E} {k : D ⟶ E} [Mono f] (w : f ≫ h = g ≫ k)
    (lift : ∀ s : PullbackCone h k, s.pt ⟶ A) (hf : ∀ s, lift s ≫ f = s.fst)
    (hg : ∀ s, lift s ≫ g = s.snd) : IsPullback f g h k :=
  IsPullback.of_isLimit (c := PullbackCone.mk f g w)
    (PullbackCone.IsLimit.mk w lift hf hg fun s _ hm _ => (cancel_mono f).mp (hm.trans (hf s).symm))

private lemma submoduleInf_isPullback {X : Scheme.{u}} {M : X.Modules}
    (P Q : M.Submodule) :
    IsPullback (submoduleInclusion (show P ⊓ Q ≤ P from inf_le_left))
      (submoduleInclusion (show P ⊓ Q ≤ Q from inf_le_right)) P.ι Q.ι := by
  let f := submoduleInclusion (show P ⊓ Q ≤ P from inf_le_left)
  let g := submoduleInclusion (show P ⊓ Q ≤ Q from inf_le_right)
  have w : f ≫ P.ι = g ≫ Q.ι := rfl
  let lift (s : PullbackCone P.ι Q.ι) : s.pt ⟶ (P ⊓ Q).toSheafOfModules :=
    submoduleLift (s.fst ≫ P.ι) (P ⊓ Q) (by
      intro U m
      refine ⟨(s.fst.val.app U m).property, ?_⟩
      have heq := congrArg (fun k : s.pt ⟶ M => k.val.app U m) s.condition
      change (s.fst.val.app U m).val = (s.snd.val.app U m).val at heq
      change (s.fst.val.app U m).val ∈ Q.toSubmodule.obj U
      rw [heq]
      exact (s.snd.val.app U m).property)
  have hf (s : PullbackCone P.ι Q.ι) : lift s ≫ f = s.fst := by
    apply (cancel_mono P.ι).mp
    rw [Category.assoc]
    change submoduleLift _ _ _ ≫ (P ⊓ Q).ι = s.fst ≫ P.ι
    exact submoduleLift_comp_ι _ _ _
  have hg (s : PullbackCone P.ι Q.ι) : lift s ≫ g = s.snd := by
    apply (cancel_mono Q.ι).mp
    rw [Category.assoc]
    change submoduleLift _ _ _ ≫ (P ⊓ Q).ι = s.snd ≫ Q.ι
    exact (submoduleLift_comp_ι _ _ _).trans s.condition
  have : Mono f := mono_submoduleInclusion _
  exact isPullback_of_lift w lift hf hg

noncomputable def supportedSheaf
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : X.Modules) [M.IsCoherent]
    (hM : SheafOfModules.supp M ⊆ Set.range i.base) :
    SupportedCoherentModules i := by
  refine ⟨⟨M, CoherentAbelian.stacksIsCoherent_of_isCoherent inferInstance⟩, ?_⟩
  change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules M).supp ⊆ _
  rw [SheafOfModules.supp_eq_moduleSheaf_supp]
  exact hM

lemma surjective_of_range_contains_kZero_classes
    {C : Type*} [Category.{v} C] [Abelian C] {G : Type*} [AddCommGroup G]
    (f : G →+ KZero C) (h : ∀ M : C, KZero.mk C M ∈ f.range) :
    Function.Surjective f := by
  have heq : QuotientAddGroup.mk' f.range = (0 : KZero C →+ KZero C ⧸ f.range) := by
    apply KZero.hom_ext
    intro M
    exact (QuotientAddGroup.eq_zero_iff _).mpr (h M)
  intro x
  have hx : x ∈ f.range := (QuotientAddGroup.eq_zero_iff _).mp
    (DFunLike.congr_fun heq x)
  exact hx


abbrev IsAnnihilated {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) : Prop :=
  ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
    ∀ m : Γ(M, U), a • m = 0

private lemma annihilated_of_mono {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (f : M ⟶ N) [Mono f] (h : IsAnnihilated I N) :
    IsAnnihilated I M := by
  intro U a ha m
  have hf : Function.Injective (f.val.app (op U.1)) :=
    (AddCommGrpCat.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app ((toPresheaf X).map f)).mp
        (Functor.map_mono (toPresheaf X) f) (op U.1))
  apply hf
  change f.app U.1 (a • m) = f.app U.1 0
  rw [Scheme.Modules.Hom.app_smul, map_zero]
  exact h U a ha _

lemma annihilated_cokernel {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (f : M ⟶ N) (h : IsAnnihilated I N) :
    IsAnnihilated I (cokernel f) := by
  apply annihilated_cokernel_of_ideal_smul
  intro U a ha s
  exact ⟨0, (map_zero _).trans (h U a ha s).symm⟩

private lemma coherent_of_isPullback {X : Scheme.{u}} [IsLocallyNoetherian X]
    {A B C D : X.Modules} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k : C ⟶ D}
    (sq : IsPullback f g h k) [B.IsCoherent] [C.IsCoherent] [D.IsCoherent] :
    A.IsCoherent := by
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  have : P.IsWeakSerreClass :=
    _root_.SheafOfModules.coherentModules_isWeakSerreClass (R := X.ringCatSheaf)
  have : PreservesFiniteLimits P.ι := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  let h' : (⟨B, inferInstance⟩ : P.FullSubcategory) ⟶ ⟨D, inferInstance⟩ :=
    ObjectProperty.homMk h
  let k' : (⟨C, inferInstance⟩ : P.FullSubcategory) ⟶ ⟨D, inferInstance⟩ :=
    ObjectProperty.homMk k
  exact P.prop_of_iso (sq.isoPullback ≪≫ (PreservesPullback.iso P.ι h' k').symm).symm
    (pullback h' k').property

lemma coherent_submodule_inf {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M : X.Modules} [M.IsCoherent] (P Q : M.Submodule)
    [P.toSheafOfModules.IsCoherent] [Q.toSheafOfModules.IsCoherent] :
    (P ⊓ Q).toSheafOfModules.IsCoherent :=
  coherent_of_isPullback (submoduleInf_isPullback P Q)

lemma submoduleSquareIsPullback {X : Scheme.{u}} {M : X.Modules}
    {A B C D : M.Submodule} (hab : A ≤ B) (hac : A ≤ C)
    (hbd : B ≤ D) (hcd : C ≤ D) (heq : A = B ⊓ C) :
    IsPullback (submoduleInclusion hab) (submoduleInclusion hac)
      (submoduleInclusion hbd) (submoduleInclusion hcd) := by
  subst A
  have := mono_submoduleInclusion hab
  exact isPullback_of_lift rfl (fun s => (submoduleInf_isPullback B C).lift s.fst s.snd
    (congrArg (· ≫ D.ι) s.condition)) (fun s => IsPullback.lift_fst _ _ _ _)
    (fun s => IsPullback.lift_snd _ _ _ _)

private lemma idealPowerMultiple_hom_eq_zero {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] {T : X.Modules}
    (f : (idealPowerMultiple I n M).toSheafOfModules ⟶ T)
    (hf : ∀ (U : X.affineOpens) (a : Γ(X, U)) (ha : a ∈ I.ideal U ^ n)
      (m : Γ(M, U)), f.val.app (op U.1)
        ⟨a • m, (idealPowerMultiple_le_iff I n M _).mp le_rfl U
          (Submodule.smul_mem_smul ha (show m ∈ (⊤ : Submodule Γ(X, U) Γ(M, U))
            from trivial))⟩ = 0) : f = 0 := by
  ext V s
  apply T.isSheaf.section_ext
  intro x hx
  let m : M.val.obj V := s.val
  have hs : m ∈ (idealPowerMultiple I n M).toSubmodule.obj V := s.property
  obtain ⟨U, hUV, hxU, hsU⟩ :=
    exists_affine_restrict_mem_idealPow I n M (V := V.unop) m hs x hx
  refine ⟨U.1, hUV, hxU, ?_⟩
  have hg := (idealPowerMultiple_le_iff I n M _).mp le_rfl U
  have hzero (m : Γ(M, U)) (hm : m ∈ I.ideal U ^ n •
      (⊤ : Submodule Γ(X, U) Γ(M, U))) :
      ∃ hmem : m ∈ (idealPowerMultiple I n M).toSubmodule.obj (op U.1),
        f.val.app (op U.1) ⟨m, hmem⟩ = 0 := by
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro a ha m hm
      exact ⟨hg (Submodule.smul_mem_smul ha hm), hf U a ha m⟩
    · intro m₁ m₂ h₁ h₂
      obtain ⟨hm₁, h₁⟩ := h₁
      obtain ⟨hm₂, h₂⟩ := h₂
      refine ⟨(idealPowerMultiple I n M).toSubmodule.obj (op U.1)
        |>.add_mem hm₁ hm₂, ?_⟩
      exact (map_add (ConcreteCategory.hom (f.val.app (op U.1))) ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩).trans
        (by rw [h₁, h₂, add_zero])
  have hn := congrArg (fun k => k s) (f.val.naturality (homOfLE hUV).op)
  change T.presheaf.map (homOfLE hUV).op (f.val.app V s) = T.presheaf.map (homOfLE hUV).op 0
  rw [map_zero]
  exact hn.symm.trans (hzero _ hsU).choose_spec

lemma idealPowerMultipleFunctor_epi {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} [N.IsQuasicoherent] (f : M ⟶ N) [Epi f] :
    Epi ((idealPowerMultipleFunctor I n).map f) := by
  apply Preadditive.epi_of_cancel_zero
  intro T g hg
  apply idealPowerMultiple_hom_eq_zero I n N g
  intro U a ha m
  apply T.isSheaf.section_ext
  intro x hx
  have hlocal := (TopCat.Presheaf.isLocallySurjective_iff _).mp (locallySurjective_of_epi f)
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ := hlocal U.1 m x hx
  obtain ⟨Wa, hWV, hxW, haW⟩ := exists_affineOpen_restrict_mem_ideal_pow I n hVU hxV ha
  have hWU := hWV.trans hVU
  let W := Wa.1
  let aW : Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom a
  let tW : Γ(M, W) := M.presheaf.map (homOfLE hWV).op t
  have htW : f.val.app (op W) tW = N.presheaf.map (homOfLE hWU).op m := by
    exact ((congrArg (fun k => k t) (f.val.naturality (homOfLE hWV).op)).trans
      (congrArg (N.presheaf.map (homOfLE hWV).op) ht)).trans
        (restrict_comp_apply N hWV hVU m)
  let v : Γ((idealPowerMultipleFunctor I n).obj M, W) :=
    ⟨aW • tW, (idealPowerMultiple_le_iff I n M _).mp le_rfl Wa
      (Submodule.smul_mem_smul haW (show tW ∈ (⊤ : Submodule Γ(X, W) Γ(M, W))
        from trivial))⟩
  let s : Γ((idealPowerMultipleFunctor I n).obj N, U) :=
    ⟨a • m, (idealPowerMultiple_le_iff I n N _).mp le_rfl U
      (Submodule.smul_mem_smul ha (show m ∈ (⊤ : Submodule Γ(X, U) Γ(N, U))
        from trivial))⟩
  have he : ((idealPowerMultipleFunctor I n).map f).val.app (op W) v =
      ((idealPowerMultipleFunctor I n).obj N).presheaf.map (homOfLE hWU).op s := by
    apply Subtype.ext
    change f.app W (aW • tW) = N.presheaf.map (homOfLE hWU).op (a • m)
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.map_smul]
    exact congrArg (aW • ·) htW
  refine ⟨W, hWU, hxW, ?_⟩
  have hn := congrArg (fun k => k s) (g.val.naturality (homOfLE hWU).op)
  change T.presheaf.map (homOfLE hWU).op (g.val.app (op U.1) s) = T.presheaf.map (homOfLE hWU).op 0
  rw [map_zero]
  exact hn.symm.trans ((congrArg (g.val.app (op W)) he.symm).trans
    (congrArg (fun k => k.val.app (op W) v) hg))

structure CoherentFiltration {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) where
  obj : ℕ → M.Submodule
  anti : Antitone obj
  zero : obj 0 = ⊤
  coherent : ∀ n, (obj n).toSheafOfModules.IsCoherent
  smul : ∀ n (U : X.affineOpens) (a : Γ(X, U)), a ∈ I.ideal U →
    ∀ m : Γ(M, U), m ∈ (obj n).toSubmodule.obj (op U.1) →
      a • m ∈ (obj (n + 1)).toSubmodule.obj (op U.1)
  locallyZero : ∀ U : X.affineOpens, ∃ N : ℕ, ∀ n, N ≤ n →
    IsZero ((restrictFunctor U.1.ι).obj (obj n).toSheafOfModules)

noncomputable def idealFiltration {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (M : X.Modules) [M.IsCoherent]
    (hM : SheafOfModules.supp M ⊆ (I.support : Set X)) : CoherentFiltration I M where
  obj n := idealPowerMultiple I n M
  anti := idealPowerMultiple_antitone I M
  zero := idealPowerMultiple_zero I M
  coherent := idealPowerMultiple_isCoherent I M
  smul n := ideal_smul_idealPowerMultiple_mem I n M
  locallyZero := idealPowerMultiple_eventually_isZero_restrict I M hM

noncomputable def filtrationStep {X : Scheme.{u}} {I : X.IdealSheafData}
    {M : X.Modules} (P : CoherentFiltration I M) (n : ℕ) :
    Quiver.Hom (V := X.Modules) (P.obj (n + 1)).toSheafOfModules (P.obj n).toSheafOfModules :=
  submoduleInclusion (P.anti (Nat.le_succ n))

lemma filtrationStep_annihilated {X : Scheme.{u}} {I : X.IdealSheafData}
    {M : X.Modules} (P : CoherentFiltration I M) (n : ℕ) :
    IsAnnihilated I (cokernel (filtrationStep P n)) := by
  apply annihilated_cokernel_of_ideal_smul
  intro U a ha m
  exact ⟨⟨a • (show Γ(M, U.1) from m.val), P.smul n U a ha m.val m.property⟩, Subtype.ext rfl⟩

private lemma filtrationStep_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {M : X.Modules} (P : CoherentFiltration I M) (n : ℕ) :
    (cokernel (filtrationStep P n)).IsCoherent := by
  have := P.coherent n
  have := P.coherent (n + 1)
  exact SheafOfModules.cokernel_isCoherent _

lemma filtrationStep_coproduct_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {M : X.Modules} (P : CoherentFiltration I M) :
    (∐ fun n => cokernel (filtrationStep P n)).IsCoherent := by
  apply coherent_natCoproduct_of_eventually_isZero_restrict _ (filtrationStep_coherent P)
  intro U
  obtain ⟨N, hN⟩ := P.locallyZero U
  exact ⟨N, fun n hn => isZero_restrict_cokernel (filtrationStep P n) U.1 (hN n hn)⟩

noncomputable def comapProjection {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (Q : N.Submodule) :
    (sheafSubmoduleComap f Q).toSheafOfModules ⟶ Q.toSheafOfModules :=
  sheafSubmoduleMap f _ _ le_rfl

lemma comapIsPullback {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (Q : N.Submodule) :
    IsPullback (sheafSubmoduleComap f Q).ι (comapProjection f Q) f Q.ι := by
  have w : (sheafSubmoduleComap f Q).ι ≫ f = comapProjection f Q ≫ Q.ι :=
    (sheafSubmoduleMap_comp_ι f _ _ le_rfl).symm
  let lift (s : PullbackCone f Q.ι) := submoduleLift s.fst (sheafSubmoduleComap f Q) (by
    intro U m
    have he := congrArg (fun k => k.val.app U m) s.condition
    change f.val.app U (s.fst.val.app U m) ∈ Q.toSubmodule.obj U
    change f.val.app U (s.fst.val.app U m) = (s.snd.val.app U m).val at he
    rw [he]
    exact (s.snd.val.app U m).property)
  have hf (s : PullbackCone f Q.ι) : lift s ≫ (sheafSubmoduleComap f Q).ι = s.fst :=
    submoduleLift_comp_ι _ _ _
  have hg (s : PullbackCone f Q.ι) : lift s ≫ comapProjection f Q = s.snd := by
    apply (cancel_mono Q.ι).mp
    rw [Category.assoc, ← w, ← Category.assoc, hf, s.condition]
  exact isPullback_of_lift w lift hf hg

private lemma comapProjection_mono {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (Q : N.Submodule) : Mono (comapProjection f Q) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (comapIsPullback f Q).isLimit

noncomputable def comapFiltration {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {M N : X.Modules} [M.IsCoherent] [N.IsCoherent]
    (f : M ⟶ N) [Mono f] (P : CoherentFiltration I N) : CoherentFiltration I M where
  obj n := sheafSubmoduleComap f (P.obj n)
  anti n m h U s hs := P.anti h U hs
  zero := by
    apply le_antisymm le_top
    intro U m hm
    change (f.val.app U).hom m ∈ (P.obj 0).toSubmodule.obj U
    rw [P.zero, top_toSubmodule]
    trivial
  coherent n := by
    have := P.coherent n
    exact coherent_of_isPullback (comapIsPullback f (P.obj n))
  smul n U a ha m hm := by
    change f.app U.1 (a • m) ∈ (P.obj (n + 1)).toSubmodule.obj (op U.1)
    rw [Scheme.Modules.Hom.app_smul]
    exact P.smul n U a ha _ hm
  locallyZero U := by
    obtain ⟨N, hN⟩ := P.locallyZero U
    refine ⟨N, fun n hn => ?_⟩
    have := comapProjection_mono f (P.obj n)
    exact isZero_restrict_of_mono (comapProjection f (P.obj n)) (by exact inferInstance) U.1
      (hN n hn)

end

end AlgebraicGeometry.SupportedCoherentDevissage

end
