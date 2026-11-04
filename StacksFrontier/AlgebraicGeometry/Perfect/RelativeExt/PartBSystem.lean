module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartBTruncation
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartAInputs
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PerfectStageNaturality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.FlatComplexBaseChange
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The approximating system of [Stacks, Tag 08IF] (B)

Let `g : U ⟶ S` be a morphism of schemes, `𝒢` a bounded complex of `𝒪_U`-modules flat over `S`,
and `E = hocolim Eₙ` in `D(𝒪_U)` with `Eₙ` perfect and `τ_{≥ -n} Eₙ ⟶ τ_{≥ -n} E` invertible
([Stacks, Tag 0DJN]). Put `Kₙ = Rg_*(Eₙ^∨ ⊗^L 𝒢)` and `Lₙ = Kₙ^∨`. When the projection formula
holds at `Eₙ^∨ ⊗^L 𝒢` on `D_QCoh(𝒪_S)`, `Kₙ` is perfect and `Lₙ ∈ D_QCoh(𝒪_S)`, this file builds:

* the system `L₀ ⟶ L₁ ⟶ ⋯` in `D(𝒪_S)`, with transition maps `L(eₙ)` the duals of the maps
  `K(eₙ) = Rg_*(eₙ^∨ ⊗ 𝒢)` (`Stacks.Cohomology.RelativeExtCanonical.stageLMap`);
* the units `uₙ : Eₙ ⟶ Φ(Lₙ)`, `Φ = Lg^*(-) ⊗^L 𝒢`, compatible with the transition maps, each
  identifying `Hom(Lₙ, N)` with `Hom(Eₙ, Φ N)` for `N ∈ D_QCoh(𝒪_S)`;

and proves that `Lₙ ⟶ Lₙ₊₁` induces an isomorphism on `τ_{≥ k}` for `k ≥ -n - b` when `𝒢` lives
in degrees `≥ b`, and that on a homotopy colimit `L = hocolim Lₙ` the units induce one
`η : E ⟶ Φ(L)` identifying `Hom(L, N)` with `Hom(E, Φ N)` for every `N ∈ D^+_QCoh(𝒪_S)`.

## Main definitions

* `Stacks.Cohomology.RelativeExt.PartBApproxSystem`: the data `Eₙ`, `cₙ` and the hypotheses on
  the stages.
* `Stacks.Cohomology.RelativeExt.partBL`, `partBTransition`, `partBSystem`, `partBUnit`.

## Main results

* `Stacks.Cohomology.RelativeExt.partBUnit_comp_transition`
* `Stacks.Cohomology.RelativeExt.isIso_truncGE_partBTransition`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

variable {U S : Scheme.{u}} (g : U ⟶ S) (G : CochainComplex (TModules U.toRingedSpace) ℤ)
  (E : DStd U)

/-- **The data of [Stacks, Tag 08IF] (B) on `U`**: a system `Eₙ` of perfect objects with
`E = hocolim Eₙ` and `τ_{≥ -n} Eₙ ≅ τ_{≥ -n} E` (as given by [Stacks, Tag 0DJN]), the
projection formula at `Eₙ^∨ ⊗^L 𝒢` on `D_QCoh(𝒪_S)`, `Kₙ = Rg_*(Eₙ^∨ ⊗^L 𝒢)` perfect and
`Lₙ = Kₙ^∨` with quasi-coherent cohomology. -/
structure PartBApproxSystem where
  /-- The system `Eₙ`. -/
  sys : ℕ ⥤ DStd U
  /-- The direct sum `⊕ Eₙ` exists. -/
  hasCoproduct : HasCoproduct sys.obj
  /-- The coprojections `cₙ : Eₙ ⟶ E`. -/
  c : ∀ n, sys.obj n ⟶ E
  /-- Each `Eₙ` is perfect. -/
  perfect : ∀ n, (Stacks.SheafOfModules.ringedSite U.toRingedSpace.sheaf).IsPerfect (sys.obj n)
  /-- `E = hocolim Eₙ` with coprojections `cₙ`. -/
  hocolim : @IsHomotopyColimitWith _ _ _ _ _ _ _ sys hasCoproduct E c
  /-- `τ_{≥ -n} Eₙ ⟶ τ_{≥ -n} E` is an isomorphism. -/
  trunc : ∀ n : ℕ, IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (c n))
  /-- The projection formula holds at `Eₙ^∨ ⊗^L 𝒢` on `D_QCoh(𝒪_S)`. -/
  projFormula : ∀ (n : ℕ) (N : DStd S), qcohDerived S N →
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap g.toLRSHom.toShHom
      (stageSource (G := G) (sys.obj n)) N)
  /-- `Kₙ = Rg_*(Eₙ^∨ ⊗^L 𝒢)` is perfect. -/
  stageKPerfect : ∀ n, (Stacks.SheafOfModules.ringedSite S.toRingedSpace.sheaf).IsPerfect
    (stageK g.toLRSHom.toShHom (G := G) (sys.obj n))
  /-- `Lₙ = Kₙ^∨` has quasi-coherent cohomology. -/
  stageLQCoh : ∀ n, qcohDerived S (stageL g.toLRSHom.toShHom (G := G) (sys.obj n))

variable {g G E} (D : PartBApproxSystem g G E)

/-- **`Lₙ = Kₙ^∨`**, `Kₙ = Rg_*(Eₙ^∨ ⊗^L 𝒢)`. -/
abbrev partBL (n : ℕ) : DStd S := stageL g.toLRSHom.toShHom (G := G) (D.sys.obj n)

/-- **The transition map `Lₙ ⟶ Lₙ₊₁`**: `L(eₙ) = K(eₙ)^∨` for the transition map
`eₙ : Eₙ ⟶ Eₙ₊₁` (`Stacks.Cohomology.RelativeExtCanonical.stageLMap`). -/
def partBTransition (n : ℕ) : partBL D n ⟶ partBL D (n + 1) :=
  Stacks.Cohomology.RelativeExtCanonical.stageLMap g.toLRSHom.toShHom (D.perfect n)
    (D.perfect (n + 1)) (D.sys.map (homOfLE (Nat.le_succ n))) (D.stageKPerfect n)
    (D.stageKPerfect (n + 1))

/-- **The system `L₀ ⟶ L₁ ⟶ ⋯` in `D(𝒪_S)`.** -/
def partBSystem : ℕ ⥤ DStd S := Functor.ofSequence (partBTransition D)

/-- The `n`-th object of `partBSystem D` is `partBL D n`. -/
theorem partBSystem_obj (n : ℕ) : (partBSystem D).obj n = partBL D n := rfl

/-- The map `n ⟶ n + 1` of `partBSystem D` is `partBTransition D n`. -/
theorem partBSystem_map_succ (n : ℕ) :
    (partBSystem D).map (homOfLE (Nat.le_succ n)) = partBTransition D n :=
  Functor.ofSequence_map_homOfLE_succ _ n

variable {D} in
/-- `Φ = Lg^*(-) ⊗^L 𝒢`. -/
abbrev partBΦ (hG : IsBoundedFlatOver g.toLRSHom.toShHom G) : DStd S ⥤ DStd U :=
  pullbackTensorDerivedFunctor hG

variable (hG : IsBoundedFlatOver g.toLRSHom.toShHom G)

/-- **The unit `uₙ : Eₙ ⟶ Φ(Lₙ)`** of the perfect stage. -/
def partBUnit (n : ℕ) : D.sys.obj n ⟶ (partBΦ hG).obj (partBL D n) :=
  perfectStageUnit g.toLRSHom.toShHom hG (D.sys.obj n) (D.perfect n) (qcohDerived S)
    (D.projFormula n) (D.stageKPerfect n) (D.stageLQCoh n)

/-- **The units are compatible with the transition maps**: `eₙ ≫ uₙ₊₁ = uₙ ≫ Φ(L(eₙ))`. -/
theorem partBUnit_comp_transition (n : ℕ) :
    D.sys.map (homOfLE (Nat.le_succ n)) ≫ partBUnit D hG (n + 1) =
      partBUnit D hG n ≫ (partBΦ hG).map (partBTransition D n) :=
  Stacks.Cohomology.RelativeExtCanonical.comp_perfectStageUnit g.toLRSHom.toShHom hG
    (D.perfect n) (D.perfect (n + 1)) _ (qcohDerived S) (D.projFormula n)
    (D.projFormula (n + 1)) (D.stageKPerfect n) (D.stageKPerfect (n + 1)) (D.stageLQCoh n)
    (D.stageLQCoh (n + 1))

/-- **Each unit identifies `Hom(Lₙ, N)` with `Hom(Eₙ, Φ N)`** for `N ∈ D_QCoh(𝒪_S)`. -/
theorem bijective_partBUnit_comp (n : ℕ) (N : DStd S) (hN : qcohDerived S N) :
    Function.Bijective (fun ψ : partBL D n ⟶ N ↦ partBUnit D hG n ≫ (partBΦ hG).map ψ) := by
  have h := ((perfectStageDualEquiv g.toLRSHom.toShHom hG (D.sys.obj n) (D.perfect n)
    (qcohDerived S) (D.projFormula n) (D.stageKPerfect n)).equiv N hN).bijective
  convert h using 1
  funext ψ
  exact (perfectStageDualEquiv_apply g.toLRSHom.toShHom hG (D.sys.obj n) (D.perfect n)
    (qcohDerived S) (D.projFormula n) (D.stageKPerfect n) (D.stageLQCoh n) hN ψ).symm

/-- The coprojections of `E = hocolim Eₙ` are compatible with the transition maps. -/
theorem partBApprox_map_comp_c (n : ℕ) :
    D.sys.map (homOfLE (Nat.le_succ n)) ≫ D.c (n + 1) = D.c n := by
  have := D.hasCoproduct
  obtain ⟨p, q, hT, hc⟩ := D.hocolim
  have h0 := comp_distTriang_mor_zero₁₂ _ hT
  have h1 := congrArg (fun k ↦ Limits.Sigma.ι D.sys.obj n ≫ k) h0
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, comp_zero] at h1
  rw [← Category.assoc, Limits.Sigma.ι_desc, Preadditive.sub_comp, Category.assoc, hc, hc,
    sub_eq_zero] at h1
  exact h1.symm

/-- The transition map `Eₙ ⟶ Eₙ₊₁` induces an isomorphism on `τ_{≥ -n}`. -/
theorem isIso_truncGE_partBApprox_map (n : ℕ) :
    IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map
      (D.sys.map (homOfLE (Nat.le_succ n)))) := by
  have h := congrArg (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map
    (partBApprox_map_comp_c D n)
  rw [CategoryTheory.Functor.map_comp] at h
  have := D.trunc n
  have : IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (D.c (n + 1))) :=
    isIso_truncGE_map_of_le _ (by push_cast; omega) (D.trunc (n + 1))
  have : IsIso ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map
      (D.sys.map (homOfLE (Nat.le_succ n))) ≫
      (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map (D.c (n + 1))) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).map
    (D.c (n + 1)))

include hG in
/-- **`Lₙ ⟶ Lₙ₊₁` induces an isomorphism on `τ_{≥ k}` for `k ≥ -n - b`**, `𝒢` living in degrees
`≥ b`. -/
theorem isIso_truncGE_partBTransition (b : ℤ) (hb : G.IsStrictlyGE b) (n : ℕ) (k : ℤ)
    (hk : -(n : ℤ) - b ≤ k) :
    IsIso ((DerivedCategory.TStructure.t.truncGE k).map (partBTransition D n)) := by
  have := hb
  refine isIso_truncGE_of_bijective_comp _ k (qcohDerived S)
    (qcohDerived_truncGE _ (D.stageLQCoh n) k) (qcohDerived_truncGE _ (D.stageLQCoh (n + 1)) k)
    fun N hN hNk => ?_
  have hΦN : ((partBΦ hG).obj N).IsGE (k + b) :=
    @Stacks.Cohomology.RelativeExtCanonical.isGE_pullbackTensorDerivedFunctor_obj _ _
      g.toLRSHom.toShHom _ hG b hb N k hNk
  have hΦN' : ((partBΦ hG).obj N).IsGE (-(n : ℤ)) :=
    DerivedCategory.TStructure.t.isGE_of_ge ((partBΦ hG).obj N) (-(n : ℤ)) (k + b) (by omega)
  have h1 := bijective_partBUnit_comp D hG n N hN
  have h2 := bijective_partBUnit_comp D hG (n + 1) N hN
  have h3 := bijective_comp_of_isIso_truncGE (D.sys.map (homOfLE (Nat.le_succ n))) _
    (isIso_truncGE_partBApprox_map D n) _ hΦN'
  have hcomm : (fun ψ : partBL D n ⟶ N ↦ partBUnit D hG n ≫ (partBΦ hG).map ψ) ∘
      (fun ψ : partBL D (n + 1) ⟶ N ↦ partBTransition D n ≫ ψ) =
      (fun x ↦ D.sys.map (homOfLE (Nat.le_succ n)) ≫ x) ∘
        (fun ψ : partBL D (n + 1) ⟶ N ↦ partBUnit D hG (n + 1) ≫ (partBΦ hG).map ψ) := by
    funext ψ
    simp only [Function.comp_apply]
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← partBUnit_comp_transition,
      Category.assoc]
  exact (Function.Bijective.of_comp_iff' h1 _).1 (hcomm ▸ h3.comp h2)

end Stacks.Cohomology.RelativeExt

end
