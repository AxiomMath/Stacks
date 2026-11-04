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
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso.FilteredRows

/-!
# Dévissage of `K_0(Coh_Z(X))`: the isomorphism `K'_0(Z) ≅ K_0(Coh_Z(X))`

Last part of the proof of [Stacks, Tag 0FDT] (see
`StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso`). The grid
`ℐᵖℱ ∩ ℐ^q𝒢` of two filtrations, the class in `K'_0(Z)` of a coherent module annihilated by `ℐ`
and of the graded module of a filtration (independent of the filtration), the inverse map
`K_0(Coh_Z(X)) → K'_0(Z)` and its additivity, and the bijectivity of
`AlgebraicGeometry.coherentToSupportedCoherentKZeroHom`.
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

private structure CoherentGrid {X : Scheme.{u}} (I : X.IdealSheafData) where
  obj : ℕ → ℕ → X.Modules
  h : ∀ n m, obj (n + 1) m ⟶ obj n m
  v : ∀ n m, obj n (m + 1) ⟶ obj n m
  square : ∀ n m, IsPullback (h n (m + 1)) (v (n + 1) m) (v n m) (h n m)
  coherent : ∀ n m, (obj n m).IsCoherent
  locallyZero : LocallyFiniteArray obj
  annH : ∀ n m, IsAnnihilated I (cokernel (h n m))
  annV : ∀ n m, IsAnnihilated I (cokernel (v n m))

private noncomputable def intersectionGrid {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {M : X.Modules} [M.IsCoherent]
    (P Q : CoherentFiltration I M) : CoherentGrid I where
  obj n m := (P.obj n ⊓ Q.obj m).toSheafOfModules
  h n m := submoduleInclusion (inf_le_inf_right (Q.obj m) (P.anti (Nat.le_succ n)))
  v n m := submoduleInclusion (inf_le_inf_left (P.obj n) (Q.anti (Nat.le_succ m)))
  square n m := submoduleSquareIsPullback _ _ _ _ (by
    apply le_antisymm
    · exact le_inf (inf_le_inf (P.anti (Nat.le_succ n)) le_rfl)
        (inf_le_inf le_rfl (Q.anti (Nat.le_succ m)))
    · exact le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_right))
  coherent n m := by
    have := P.coherent n
    have := Q.coherent m
    exact coherent_submodule_inf _ _
  locallyZero U := by
    obtain ⟨N, hN⟩ := P.locallyZero U
    obtain ⟨K, hK⟩ := Q.locallyZero U
    refine ⟨max N K, fun n m hm => ?_⟩
    rcases hm with hn | hm
    · let f := submoduleInclusion (show P.obj n ⊓ Q.obj m ≤ P.obj n from inf_le_left)
      have : Mono f := mono_submoduleInclusion _
      exact isZero_restrict_of_mono f (by exact inferInstance) U.1
        (hN n ((le_max_left _ _).trans hn))
    · let f := submoduleInclusion (show P.obj n ⊓ Q.obj m ≤ Q.obj m from inf_le_right)
      have : Mono f := mono_submoduleInclusion _
      exact isZero_restrict_of_mono f (by exact inferInstance) U.1
        (hK m ((le_max_right _ _).trans hm))
  annH n m := by
    apply annihilated_cokernel_of_ideal_smul
    intro U a ha s
    exact ⟨⟨a • (show Γ(M, U.1) from s.val), P.smul n U a ha s.val s.property.1,
      (Q.obj m).toSubmodule.obj (op U.1) |>.smul_mem a s.property.2⟩, Subtype.ext rfl⟩
  annV n m := by
    apply annihilated_cokernel_of_ideal_smul
    intro U a ha s
    exact ⟨⟨a • (show Γ(M, U.1) from s.val), (P.obj n).toSubmodule.obj (op U.1) |>.smul_mem a
      s.property.1,
      Q.smul m U a ha s.val s.property.2⟩, Subtype.ext rfl⟩

private noncomputable def gridRow {X : Scheme.{u}} {I : X.IdealSheafData}
    (G : CoherentGrid I) (m n : ℕ) : X.Modules := cokernel (G.h n m)

private noncomputable def gridColumn {X : Scheme.{u}} {I : X.IdealSheafData}
    (G : CoherentGrid I) (n m : ℕ) : X.Modules := cokernel (G.v n m)

private noncomputable def gridRowStep {X : Scheme.{u}} {I : X.IdealSheafData}
    (G : CoherentGrid I) (m n : ℕ) : gridRow G (m + 1) n ⟶ gridRow G m n :=
  cokernel.map _ _ _ _ (G.square n m).w

private noncomputable def gridColumnStep {X : Scheme.{u}} {I : X.IdealSheafData}
    (G : CoherentGrid I) (n m : ℕ) : gridColumn G (n + 1) m ⟶ gridColumn G n m :=
  cokernel.map _ _ _ _ (G.square n m).w.symm

/-- The cokernel of a map between coherent modules is coherent. -/
private lemma isCoherent_cokernel_of_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {A B : X.Modules} (f : A ⟶ B) (hA : A.IsCoherent) (hB : B.IsCoherent) :
    (cokernel f).IsCoherent :=
  SheafOfModules.cokernel_isCoherent f

/-- Cokernels of a family of maps into a locally finite array form a locally finite array. -/
private lemma locallyFiniteArray_cokernel {X : Scheme.{u}} {A B : ℕ → ℕ → X.Modules}
    (f : ∀ n m, A n m ⟶ B n m) (hz : LocallyFiniteArray B) :
    LocallyFiniteArray (fun n m => cokernel (f n m)) := by
  intro U
  obtain ⟨N, hN⟩ := hz U
  exact ⟨N, fun n m h => isZero_restrict_cokernel (f n m) U.1 (hN n m h)⟩

private lemma gridRow_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (G : CoherentGrid I) (m n : ℕ) :
    (gridRow G m n).IsCoherent := by
  exact isCoherent_cokernel_of_isCoherent _ (G.coherent _ _) (G.coherent _ _)

private lemma gridColumn_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (G : CoherentGrid I) (n m : ℕ) :
    (gridColumn G n m).IsCoherent := by
  exact isCoherent_cokernel_of_isCoherent _ (G.coherent _ _) (G.coherent _ _)

private lemma gridRow_locallyZero {X : Scheme.{u}} {I : X.IdealSheafData}
    (G : CoherentGrid I) : LocallyFiniteArray (gridRow G) := by
  intro U
  obtain ⟨N, hN⟩ := G.locallyZero U
  exact ⟨N, fun m n h => isZero_restrict_cokernel (G.h n m) U.1 (hN n m h.symm)⟩

private lemma gridColumn_locallyZero {X : Scheme.{u}} {I : X.IdealSheafData}
    (G : CoherentGrid I) : LocallyFiniteArray (gridColumn G) := by
  exact locallyFiniteArray_cokernel (A := fun n m => G.obj n (m + 1)) G.v G.locallyZero

section AnnihilatedClasses

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Z]

/-- Coherent `𝒪_Z`-modules, in the coherence class of `Coh(Z)`, are equivalent to the coherent
`𝒪_X`-modules annihilated by the ideal sheaf of `Z`: the two coherence classes cut out the same
category, and direct image is an equivalence onto the annihilated modules ([Stacks, Tag 087T]). -/
noncomputable def annihilatedEquiv :
    Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf ≌
      CoherentAnnihilatedModules i :=
  (Stacks.SheafOfModules.coherentModulesEquiv Z.ringCatSheaf).trans
    (Stacks.AlgebraicGeometry.Tag087TCoherentImage.coherentPushforwardEquivalence i).1

local instance : HasFiniteLimits (CoherentAnnihilatedModules i) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
    (annihilatedEquiv i).inverse⟩

local instance : Abelian (CoherentAnnihilatedModules i) :=
  abelianOfEquivalence (annihilatedEquiv i).inverse

private noncomputable def annihilatedClass (M : X.Modules) [M.IsCoherent]
    (hM : IsAnnihilated i.ker M) : KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :=
  KZero.mk _ ((annihilatedEquiv i).inverse.obj
    ⟨M, inferInstance, hM⟩)

private lemma annihilatedClass_eq_of_iso {M N : X.Modules}
    [M.IsCoherent] [N.IsCoherent] (hM : IsAnnihilated i.ker M)
    (hN : IsAnnihilated i.ker N) (e : M ≅ N) :
    annihilatedClass i M hM = annihilatedClass i N hN :=
  KZero.mk_eq_of_iso ((annihilatedEquiv i).inverse.mapIso
    (ObjectProperty.isoMk _ e))

private lemma annihilatedClass_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (h₁ : IsAnnihilated i.ker S.X₁) (h₂ : IsAnnihilated i.ker S.X₂)
    (h₃ : IsAnnihilated i.ker S.X₃) :
    annihilatedClass i S.X₂ h₂ =
      annihilatedClass i S.X₁ h₁ + annihilatedClass i S.X₃ h₃ := by
  let A : CoherentAnnihilatedModules i := ⟨S.X₁, inferInstance, h₁⟩
  let B : CoherentAnnihilatedModules i := ⟨S.X₂, inferInstance, h₂⟩
  let C : CoherentAnnihilatedModules i := ⟨S.X₃, inferInstance, h₃⟩
  let f : A ⟶ B := ObjectProperty.homMk S.f
  let g : B ⟶ C := ObjectProperty.homMk S.g
  let E := ObjectProperty.ι (fun M : X.Modules =>
    M.IsCoherent ∧ AnnihilatedByKer i M)
  have w : f ≫ g = 0 := by
    apply E.map_injective
    exact S.zero
  let T := ShortComplex.mk f g w
  have hT : T.ShortExact := ShortExact.reflects_shortExact_of_faithful E hS
  exact KZero.mk_of_shortExact
    (T.map (annihilatedEquiv i).inverse)
    (hT.map_of_exact _)

private lemma annihilatedClass_telescope (A : ℕ → X.Modules)
    (f : ∀ n, A (n + 1) ⟶ A n) [∀ n, Mono (f n)]
    [SheafOfModules.IsCoherent (A 0)] [(∐ A).IsCoherent]
    [(∐ fun n => A (n + 1)).IsCoherent]
    [(∐ fun n => cokernel (f n)).IsCoherent]
    (hA : ∀ n, IsAnnihilated i.ker (A n)) :
    annihilatedClass i (A 0) (hA 0) =
      annihilatedClass i (∐ fun n => cokernel (f n))
        (annihilated_natCoproduct _ _ (fun n => annihilated_cokernel _ _ (hA n))) := by
  have h₀ := annihilated_natCoproduct i.ker A hA
  have h₁ := annihilated_natCoproduct i.ker (fun n => A (n + 1)) (fun n => hA (n + 1))
  have h₂ := annihilated_natCoproduct i.ker (fun n => cokernel (f n))
    (fun n => annihilated_cokernel _ _ (hA n))
  have : (coproductHeadTailComplex A).X₁.IsCoherent := inferInstanceAs ((A 0).IsCoherent)
  have : (coproductHeadTailComplex A).X₂.IsCoherent := inferInstanceAs ((∐ A).IsCoherent)
  have : (coproductHeadTailComplex A).X₃.IsCoherent :=
    inferInstanceAs ((∐ fun n => A (n + 1)).IsCoherent)
  have hsplit := annihilatedClass_of_shortExact i (coproductHeadTailComplex A)
    (coproductHeadTailComplex_shortExact A) (hA 0) h₀ h₁
  have hseq := annihilatedClass_of_shortExact i _ (sigmaMap_cokernel_shortExact f)
    h₁ h₀ h₂
  change annihilatedClass i (∐ A) h₀ =
    annihilatedClass i (A 0) (hA 0) +
      annihilatedClass i (∐ fun n => A (n + 1)) h₁ at hsplit
  change annihilatedClass i (∐ A) h₀ =
    annihilatedClass i (∐ fun n => A (n + 1)) h₁ +
      annihilatedClass i (∐ fun n => cokernel (f n)) h₂ at hseq
  rw [hsplit, add_comm] at hseq
  exact add_left_cancel hseq

private lemma annihilatedClass_array_telescope (A : ℕ → ℕ → X.Modules)
    (hc : ∀ n m, (A n m).IsCoherent) (hz : LocallyFiniteArray A)
    (ha : ∀ n m, IsAnnihilated i.ker (A n m))
    (f : ∀ n m, A (n + 1) m ⟶ A n m) [∀ n m, Mono (f n m)] :
    letI := coherent_array_row A hc hz 0
    let D := fun n m => cokernel (f n m)
    letI : (∐ fun n => ∐ D n).IsCoherent :=
      coherent_array_coproduct D
        (fun _ _ => isCoherent_cokernel_of_isCoherent _ (hc _ _) (hc _ _))
        (locallyFiniteArray_cokernel f hz)
    annihilatedClass i (∐ A 0) (annihilated_natCoproduct _ _ (ha 0)) =
      annihilatedClass i (∐ fun n => ∐ D n)
        (annihilated_natCoproduct _ _ (fun n => annihilated_natCoproduct _ _
          (fun m => annihilated_cokernel _ _ (ha n m)))) := by
  let B := fun n => ∐ A n
  let g := fun n => Limits.Sigma.map (f n)
  let D := fun n m => cokernel (f n m)
  have : (∐ fun n => ∐ D n).IsCoherent := coherent_array_coproduct D
    (fun n m => isCoherent_cokernel_of_isCoherent _ (hc _ _) (hc _ _))
    (locallyFiniteArray_cokernel f hz)
  have : ∀ n, (B n).IsCoherent := coherent_array_row A hc hz
  have : (∐ B).IsCoherent := coherent_array_coproduct A hc hz
  have hzB := array_row_locallyZero A hz
  have : (∐ fun n => B (n + 1)).IsCoherent :=
    coherent_natCoproduct_of_eventually_isZero_restrict _ (fun n => inferInstance) (by
      intro U
      obtain ⟨N, hN⟩ := hzB U
      exact ⟨N, fun n hn => hN (n + 1) (hn.trans (Nat.le_succ n))⟩)
  have : ∀ n, (cokernel (g n)).IsCoherent := fun n =>
    isCoherent_cokernel_of_isCoherent _ inferInstance inferInstance
  have : (∐ fun n => cokernel (g n)).IsCoherent :=
    coherent_natCoproduct_of_eventually_isZero_restrict _ (fun n => inferInstance) (by
      intro U
      obtain ⟨N, hN⟩ := hzB U
      exact ⟨N, fun n hn => isZero_restrict_cokernel (g n) U.1 (hN n hn)⟩)
  have : ∀ n, Mono (g n) := fun n => mono_sigmaMap (f n)
  have hb : ∀ n, IsAnnihilated i.ker (B n) := fun n =>
    annihilated_natCoproduct _ _ (ha n)
  exact (annihilatedClass_telescope i B g hb).trans
    (annihilatedClass_eq_of_iso i _ _ (Sigma.mapIso (fun n => sigmaCokernelIso (f n))))

private lemma annihilatedClass_grid (G : CoherentGrid i.ker) :
    letI := coherent_array_row (gridRow G) (gridRow_coherent G) (gridRow_locallyZero G) 0
    letI := coherent_array_row (gridColumn G) (gridColumn_coherent G)
      (gridColumn_locallyZero G) 0
    annihilatedClass i (∐ gridRow G 0) (annihilated_natCoproduct _ _ (fun n => G.annH n 0)) =
      annihilatedClass i (∐ gridColumn G 0) (annihilated_natCoproduct _ _ (G.annV 0)) := by
  have := coherent_array_row (gridRow G) (gridRow_coherent G) (gridRow_locallyZero G) 0
  have := coherent_array_row (gridColumn G) (gridColumn_coherent G) (gridColumn_locallyZero G) 0
  have : ∀ m n, Mono (gridRowStep G m n) := fun m n =>
    Abelian.mono_cokernel_map_of_isPullback (G.square n m)
  have : ∀ n m, Mono (gridColumnStep G n m) := fun n m =>
    Abelian.mono_cokernel_map_of_isPullback (G.square n m).flip
  have hr := annihilatedClass_array_telescope i (gridRow G) (gridRow_coherent G)
    (gridRow_locallyZero G) (fun m n => G.annH n m) (gridRowStep G)
  have hc := annihilatedClass_array_telescope i (gridColumn G) (gridColumn_coherent G)
    (gridColumn_locallyZero G) G.annV (gridColumnStep G)
  have := coherent_array_coproduct _
    (fun n m => isCoherent_cokernel_of_isCoherent (gridColumnStep G n m)
      (gridColumn_coherent G _ _) (gridColumn_coherent G _ _))
    (locallyFiniteArray_cokernel (gridColumnStep G) (gridColumn_locallyZero G))
  have := coherent_array_coproduct _
    (fun m n => isCoherent_cokernel_of_isCoherent (gridRowStep G m n)
      (gridRow_coherent G _ _) (gridRow_coherent G _ _))
    (locallyFiniteArray_cokernel (gridRowStep G) (gridRow_locallyZero G))
  refine hr.trans (Eq.trans ?_ hc.symm)
  apply annihilatedClass_eq_of_iso
  exact Sigma.mapIso (fun m => Sigma.mapIso (fun n =>
    doubleCokernelIso (G.h n (m + 1)) (G.v (n + 1) m) (G.v n m) (G.h n m)
      (G.square n m).w)) ≪≫
        sigmaExchange (fun m n => cokernel (gridColumnStep G n m))

private noncomputable def filtrationClass {M : X.Modules} (P : CoherentFiltration i.ker M) :
    KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) := by
  letI := filtrationStep_coproduct_coherent P
  exact annihilatedClass i (∐ fun n => cokernel (filtrationStep P n))
    (annihilated_natCoproduct _ _ (filtrationStep_annihilated P))

private lemma filtrationClass_independent {M : X.Modules} [M.IsCoherent]
    (P Q : CoherentFiltration i.ker M) : filtrationClass i P = filtrationClass i Q := by
  have h := annihilatedClass_grid i (intersectionGrid P Q)
  let er (n : ℕ) : gridRow (intersectionGrid P Q) 0 n ≅
      cokernel (filtrationStep P n) :=
    cokernel.mapIso _ _
      (submoduleIsoOfEq (show P.obj (n + 1) ⊓ Q.obj 0 = P.obj (n + 1) by rw [Q.zero, inf_top_eq]))
      (submoduleIsoOfEq (show P.obj n ⊓ Q.obj 0 = P.obj n by rw [Q.zero, inf_top_eq]))
      (by ext U s; rfl)
  let ec (n : ℕ) : gridColumn (intersectionGrid P Q) 0 n ≅
      cokernel (filtrationStep Q n) :=
    cokernel.mapIso _ _
      (submoduleIsoOfEq (show P.obj 0 ⊓ Q.obj (n + 1) = Q.obj (n + 1) by rw [P.zero, top_inf_eq]))
      (submoduleIsoOfEq (show P.obj 0 ⊓ Q.obj n = Q.obj n by rw [P.zero, top_inf_eq]))
      (by ext U s; rfl)
  have := filtrationStep_coproduct_coherent P
  have := filtrationStep_coproduct_coherent Q
  have := coherent_array_row (gridRow (intersectionGrid P Q))
    (gridRow_coherent _) (gridRow_locallyZero _) 0
  have := coherent_array_row (gridColumn (intersectionGrid P Q))
    (gridColumn_coherent _) (gridColumn_locallyZero _) 0
  exact (annihilatedClass_eq_of_iso i _ _ (Sigma.mapIso er).symm).trans
    (h.trans (annihilatedClass_eq_of_iso i _ _ (Sigma.mapIso ec)))

private lemma annihilatedClass_graded_shortExact
    (T : ℕ → ShortComplex X.Modules) (hT : ∀ n, (T n).ShortExact)
    (v : ∀ n, T (n + 1) ⟶ T n) [∀ n, Mono (v n).τ₃]
    [(∐ fun n => cokernel (v n).τ₁).IsCoherent]
    [(∐ fun n => cokernel (v n).τ₂).IsCoherent]
    [(∐ fun n => cokernel (v n).τ₃).IsCoherent]
    (h₁ : IsAnnihilated i.ker (∐ fun n => cokernel (v n).τ₁))
    (h₂ : IsAnnihilated i.ker (∐ fun n => cokernel (v n).τ₂))
    (h₃ : IsAnnihilated i.ker (∐ fun n => cokernel (v n).τ₃)) :
    annihilatedClass i (∐ fun n => cokernel (v n).τ₂) h₂ =
      annihilatedClass i (∐ fun n => cokernel (v n).τ₁) h₁ +
        annihilatedClass i (∐ fun n => cokernel (v n).τ₃) h₃ := by
  let f := fun n => cokernel.map (v n).τ₁ (v n).τ₂
    (T (n + 1)).f (T n).f (v n).comm₁₂
  have : ∀ n, Mono (f n) := fun n =>
    Abelian.mono_cokernel_map_of_isPullback
      (shortExact_square_isPullback (hT (n + 1)) (hT n) (v n)).flip
  let F := Limits.Sigma.map f
  have : Mono F := mono_sigmaMap f
  have : (cokernel F).IsCoherent :=
    SheafOfModules.cokernel_isCoherent F
  have hQ := annihilated_cokernel i.ker F h₂
  have hs : (ShortComplex.mk F (cokernel.π F) (cokernel.condition F)).ShortExact :=
    { exact := ShortComplex.exact_cokernel F }
  have heq := annihilatedClass_of_shortExact i _ hs h₁ h₂ hQ
  refine heq.trans (congrArg (fun z => annihilatedClass i _ h₁ + z) ?_)
  exact annihilatedClass_eq_of_iso i _ h₃
    (sigmaCokernelIso f ≪≫ Sigma.mapIso (fun n => gradedCokernelIso (hT (n + 1)) (hT n) (v n)))

end AnnihilatedClasses

/-- The support of a module in `Coh_Z(X)` lies in the support of the ideal sheaf of `Z`. -/
private lemma supp_subset_ker_support_of_supported {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : SupportedCoherentModules i) :
    SheafOfModules.supp F.obj.obj ⊆ (i.ker.support : Set X) := by
  have hF : SheafOfModules.supp F.obj.obj ⊆ Set.range i.base := by
    rw [← SheafOfModules.supp_eq_moduleSheaf_supp]
    exact F.property
  simpa only [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq] using hF

section SupportedClasses

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]

private lemma supportedClass_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (h₁ : SheafOfModules.supp S.X₁ ⊆ Set.range i.base)
    (h₂ : SheafOfModules.supp S.X₂ ⊆ Set.range i.base)
    (h₃ : SheafOfModules.supp S.X₃ ⊆ Set.range i.base) :
    KZero.mk _ (supportedSheaf i S.X₂ h₂) =
      KZero.mk _ (supportedSheaf i S.X₁ h₁) + KZero.mk _ (supportedSheaf i S.X₃ h₃) := by
  let f : supportedSheaf i S.X₁ h₁ ⟶ supportedSheaf i S.X₂ h₂ :=
    ObjectProperty.homMk (ObjectProperty.homMk S.f)
  let g : supportedSheaf i S.X₂ h₂ ⟶ supportedSheaf i S.X₃ h₃ :=
    ObjectProperty.homMk (ObjectProperty.homMk S.g)
  let E := (supportedCoherentProperty i).ι ⋙
    ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
  have w : f ≫ g = 0 := by
    apply E.map_injective
    rw [E.map_comp, E.map_zero]
    exact S.zero
  exact KZero.mk_of_shortExact (ShortComplex.mk f g w)
    (ShortExact.reflects_shortExact_of_faithful E hS)

private lemma exists_annihilated_representative
    (F : SupportedCoherentModules i) :
    ∃ M : CoherentAnnihilatedModules i,
      KZero.mk _ F = KZero.mk _ ((annihilatedToSupported i).obj M) := by
  let A : ℕ → X.Modules := fun n =>
    (idealPowerMultiple i.ker n F.obj.obj).toSheafOfModules
  let q := idealPowerStep i.ker F.obj.obj
  let Q : X.Modules := ∐ fun n => cokernel (q n)
  have hF : SheafOfModules.supp F.obj.obj ⊆ Set.range i.base := by
    rw [← SheafOfModules.supp_eq_moduleSheaf_supp]
    exact F.property
  have hI := supp_subset_ker_support_of_supported i F
  have hA (n : ℕ) : (A n).IsCoherent := idealPowerMultiple_isCoherent _ _ _
  have : (∐ A).IsCoherent := coherent_idealPowerMultiple_coproduct _ _ hI
  have : (∐ fun n => A (n + 1)).IsCoherent :=
    coherent_natCoproduct_of_eventually_isZero_restrict _ (fun n => hA (n + 1)) (by
      intro U
      obtain ⟨N, hN⟩ := idealPowerMultiple_eventually_isZero_restrict i.ker F.obj.obj hI U
      exact ⟨N, fun n hn => hN (n + 1) (hn.trans (Nat.le_succ n))⟩)
  have : Q.IsCoherent := coherent_idealPowerStep_cokernel_coproduct _ _ hI
  have hAQ := annihilated_natCoproduct i.ker (fun n => cokernel (q n))
    (annihilated_idealPowerStep_cokernel i.ker F.obj.obj)
  have hsA (n : ℕ) : SheafOfModules.supp (A n) ⊆ Set.range i.base := by
    let T := idealPowerMultiple i.ker n F.obj.obj
    have : Mono (C := X.Modules) T.ι :=
      mono_submodule_ι _
    exact (supp_subset_of_mono T.ι).trans hF
  have hsSum := supp_natCoproduct_subset A (Set.range i.base) hsA
  have hsTail := supp_natCoproduct_subset (fun n => A (n + 1)) (Set.range i.base)
    (fun n => hsA (n + 1))
  have hsQ : SheafOfModules.supp Q ⊆ Set.range i.base :=
    support_subset_range_of_annihilated i Q hAQ
  let M : CoherentAnnihilatedModules i := ⟨Q, inferInstance, hAQ⟩
  refine ⟨M, ?_⟩
  have : ∀ n, Mono (q n) := mono_idealPowerStep _ _
  have hseq := sigmaMap_cokernel_shortExact (C := X.Modules) q
  have heq := supportedClass_of_shortExact i _ hseq hsTail hsSum hsQ
  have : (A 0).IsCoherent := hA 0
  have : (coproductHeadTailComplex A).X₁.IsCoherent := hA 0
  have : (coproductHeadTailComplex A).X₂.IsCoherent :=
    inferInstanceAs ((∐ A).IsCoherent)
  have : (coproductHeadTailComplex A).X₃.IsCoherent :=
    inferInstanceAs ((∐ fun n => A (n + 1)).IsCoherent)
  have hsplit := supportedClass_of_shortExact i (coproductHeadTailComplex A)
    (coproductHeadTailComplex_shortExact A) (hsA 0) hsSum hsTail
  change KZero.mk _ (supportedSheaf i (∐ A) hsSum) =
    KZero.mk _ (supportedSheaf i (A 0) (hsA 0)) +
      KZero.mk _ (supportedSheaf i (∐ fun n => A (n + 1)) hsTail) at hsplit
  change KZero.mk _ (supportedSheaf i (∐ A) hsSum) =
    KZero.mk _ (supportedSheaf i (∐ fun n => A (n + 1)) hsTail) +
      KZero.mk _ (supportedSheaf i Q hsQ) at heq
  have hclass : KZero.mk _ (supportedSheaf i (A 0) (hsA 0)) =
      KZero.mk _ (supportedSheaf i Q hsQ) := by
    rw [hsplit, add_comm] at heq
    exact add_left_cancel heq
  have e : supportedSheaf i (A 0) (hsA 0) ≅ F := idealPowerSupportedZeroIso i F
  exact (KZero.mk_eq_of_iso e).symm.trans hclass

/-- The functor `Coh(𝒪_Z) ⥤ Coh_Z(X)` agrees on objects with direct image followed by the
inclusion of the annihilated modules. -/
private noncomputable def coherentToSupportedCoherentIso [IsLocallyNoetherian Z]
    (G : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    (coherentToSupportedCoherent i).obj G ≅
      (annihilatedToSupported i).obj ((annihilatedEquiv i).functor.obj G) :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _))

private lemma supportedPushforwardKZero_surjective [IsLocallyNoetherian Z] :
    Function.Surjective (coherentToSupportedCoherentKZeroHom i) := by
  apply surjective_of_range_contains_kZero_classes
  intro F
  obtain ⟨M, hM⟩ := exists_annihilated_representative i F
  let e := (annihilatedEquiv i)
  refine ⟨KZero.mk _ (e.inverse.obj M), ?_⟩
  rw [coherentToSupportedCoherentKZeroHom_mk, hM]
  exact KZero.mk_eq_of_iso (coherentToSupportedCoherentIso i (e.inverse.obj M) ≪≫
    (annihilatedToSupported i).mapIso (e.counitIso.app M))

private noncomputable def associatedGradedAnnihilated
    (F : SupportedCoherentModules i) :
    CoherentAnnihilatedModules i := by
  let Q : X.Modules := ∐ fun n => cokernel (idealPowerStep i.ker F.obj.obj n)
  have hI := supp_subset_ker_support_of_supported i F
  exact ⟨Q, coherent_idealPowerStep_cokernel_coproduct _ _ hI,
    annihilated_natCoproduct i.ker _ (annihilated_idealPowerStep_cokernel i.ker F.obj.obj)⟩

private noncomputable def inverseSupportedClass [IsLocallyNoetherian Z]
    (F : SupportedCoherentModules i) :
    KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) := by
  exact KZero.mk _ ((annihilatedEquiv i).inverse.obj
    (associatedGradedAnnihilated i F))

private lemma inverseSupportedClass_supportedPushforward [IsLocallyNoetherian Z]
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    inverseSupportedClass i ((coherentToSupportedCoherent i).obj F) = KZero.mk _ F := by
  let e := (annihilatedEquiv i)
  let M := e.functor.obj F
  let Q := associatedGradedAnnihilated i ((coherentToSupportedCoherent i).obj F)
  have qiso : Q ≅ M := ObjectProperty.isoMk _
    (idealAssociatedGradedIsoOfAnnihilated i.ker M.obj M.property.2)
  exact KZero.mk_eq_of_iso (e.inverse.mapIso qiso ≪≫ (e.unitIso.app F).symm)

private lemma inverseSupportedClass_additive [IsLocallyNoetherian Z]
    (S : ShortComplex (SupportedCoherentModules i))
    (hS : S.ShortExact) :
    inverseSupportedClass i S.X₂ = inverseSupportedClass i S.X₁ + inverseSupportedClass i S.X₃ := by
  let E := (supportedCoherentProperty i).ι ⋙
    ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
  let C := Stacks.SheafOfModules.coherentModules X.ringCatSheaf
  have : C.IsWeakSerreClass := inferInstance
  have : PreservesFiniteLimits C.ι := C.preservesFiniteLimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits C.ι := C.preservesFiniteColimits_ι_of_isWeakSerreClass
  let P := supportedCoherentProperty i
  have : PreservesFiniteLimits P.ι := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits P.ι := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  have : PreservesFiniteLimits E := comp_preservesFiniteLimits P.ι C.ι
  have : PreservesFiniteColimits E := comp_preservesFiniteColimits P.ι C.ι
  let T := S.map E
  have hT : T.ShortExact := hS.map_of_exact E
  have : T.X₁.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₁.obj.property
  have : T.X₂.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₂.obj.property
  have : T.X₃.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₃.obj.property
  have : Mono T.f := hT.mono_f
  have hs := supp_subset_ker_support_of_supported i
  let P₁ := idealFiltration i.ker T.X₁ (hs S.X₁)
  let P₂ := idealFiltration i.ker T.X₂ (hs S.X₂)
  let P₃ := idealFiltration i.ker T.X₃ (hs S.X₃)
  let P₁' := comapFiltration T.f P₂
  let R := filteredRow i.ker T hT
  let v := filteredRowStep i.ker T hT
  have : ∀ n, Mono (v n).τ₃ := mono_idealPowerStep i.ker T.X₃
  have : (∐ fun n => cokernel (v n).τ₁).IsCoherent := filtrationStep_coproduct_coherent P₁'
  have : (∐ fun n => cokernel (v n).τ₂).IsCoherent := filtrationStep_coproduct_coherent P₂
  have : (∐ fun n => cokernel (v n).τ₃).IsCoherent := filtrationStep_coproduct_coherent P₃
  have ha₁ : IsAnnihilated i.ker (∐ fun n => cokernel (v n).τ₁) :=
    annihilated_natCoproduct _ _ (filtrationStep_annihilated P₁')
  have ha₂ : IsAnnihilated i.ker (∐ fun n => cokernel (v n).τ₂) :=
    annihilated_natCoproduct _ _ (filtrationStep_annihilated P₂)
  have ha₃ : IsAnnihilated i.ker (∐ fun n => cokernel (v n).τ₃) :=
    annihilated_natCoproduct _ _ (filtrationStep_annihilated P₃)
  have hadd := annihilatedClass_graded_shortExact i R (filteredRow_shortExact i.ker T hT)
    v ha₁ ha₂ ha₃
  change filtrationClass i P₂ = filtrationClass i P₁' + filtrationClass i P₃ at hadd
  rw [filtrationClass_independent i P₁' P₁] at hadd
  exact hadd

end SupportedClasses
end

end AlgebraicGeometry.SupportedCoherentDevissage

namespace AlgebraicGeometry

open SupportedCoherentDevissage

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]

/-- **[Stacks, Tag 0FDT].** Let `X` be a locally Noetherian scheme and `Z ⊂ X` a closed
subscheme. The homomorphism `K'_0(Z) = K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))` induced by the exact
inclusion functor `Coh(𝒪_Z) ⥤ Coh_Z(X)` is an isomorphism. -/
@[stacks 0FDT "the homomorphism K'_0(Z) = K_0(Coh(Z)) → K_0(Coh_Z(X)) induced by the exact \
inclusion functor is an isomorphism"]
theorem coherentToSupportedCoherentKZeroHom_bijective :
    Function.Bijective (coherentToSupportedCoherentKZeroHom i) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let r := KZero.lift (inverseSupportedClass i) fun S hS => inverseSupportedClass_additive i S hS
  have hr : r.comp (coherentToSupportedCoherentKZeroHom i) = AddMonoidHom.id _ := by
    refine KZero.hom_ext fun F => ?_
    show r (coherentToSupportedCoherentKZeroHom i (KZero.mk _ F)) = KZero.mk _ F
    rw [coherentToSupportedCoherentKZeroHom_mk]
    exact (KZero.lift_mk _ _ _).trans (inverseSupportedClass_supportedPushforward i F)
  exact ⟨Function.LeftInverse.injective (g := r) fun x => DFunLike.congr_fun hr x,
    supportedPushforwardKZero_surjective i⟩

/-- **[Stacks, Tag 0FDT]**, as an isomorphism of groups `K'_0(Z) ≃+ K_0(Coh_Z(X))`. -/
def coherentToSupportedCoherentKZeroEquiv :
    KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) ≃+
      KZero (SupportedCoherentModules i) :=
  AddEquiv.ofBijective _ (coherentToSupportedCoherentKZeroHom_bijective i)

@[simp]
theorem coherentToSupportedCoherentKZeroEquiv_apply
    (x : KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf)) :
    coherentToSupportedCoherentKZeroEquiv i x = coherentToSupportedCoherentKZeroHom i x :=
  rfl

end AlgebraicGeometry

end
