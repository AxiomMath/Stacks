module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompletedInducedModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.NormalSubgroupAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicGroupAlgebra
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived coinvariants of a procyclic group with trivial coefficients

Let `Γ` be a topological group, `G` a compact normal subgroup and `σ ∈ G` an element generating
every finite quotient of `G`; let `Λ` be a ring killed by an integer `n ≠ 0` such that `G` has the
`ℓ`-power quotients of `Ẑ` for every prime `ℓ ∣ n` (as in `Stacks.GroupHomology.Procyclic`). Then

`0 → Λ[[G]] --(· (σ - 1))--> Λ[[G]] --ε--> Λ → 0`

is a projective resolution of the trivial module `Λ`, so the derived coinvariants
`LH₀(G, Λ) = Λ ⊗^L_{Λ[[G]]} Λ` are `Λ` in degrees `0` and `-1` with zero differential. The trace
of an element of `Γ` on them, which gives the congruence of [Stacks, Tag 03VQ], is
`Stacks.GroupHomology.Procyclic.perfectDerivedTrace_trivialRep`.

## Main definitions

* `Stacks.GroupHomology.TrivialRep Γ Λ`: `Λ` with the trivial action of `Γ`.
* `Stacks.GroupHomology.Procyclic.koszulComplex`: the complex `Λ[[G]] --(· (σ - 1))--> Λ[[G]]`.
* `Stacks.GroupHomology.Procyclic.koszulResolution`: the projective resolution above.

## Main results

* `Stacks.GroupHomology.Procyclic.koszulπ_quasiIso`: the augmentation of the Koszul complex is a
  quasi-isomorphism onto the trivial module.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GroupHomology

open CompletedGroupAlgebra MonoidAlgebra

/-- The ring `Λ` with the trivial action of `Γ`. -/
public def TrivialRep (_Γ : Type u) (Λ : Type u) : Type u := Λ

namespace TrivialRep

variable (Γ : Type u) [Group Γ] (Λ : Type u) [Ring Λ]

/-- The additive group of `TrivialRep Γ Λ`, that of `Λ`. -/
public instance : AddCommGroup (TrivialRep Γ Λ) := inferInstanceAs (AddCommGroup Λ)

/-- The `Λ`-module structure of `TrivialRep Γ Λ`, that of `Λ` over itself. -/
public instance : Module Λ (TrivialRep Γ Λ) := inferInstanceAs (Module Λ Λ)

/-- `TrivialRep Γ Λ` is a finite `Λ`-module. -/
public instance : Module.Finite Λ (TrivialRep Γ Λ) := inferInstanceAs (Module.Finite Λ Λ)

/-- `TrivialRep Γ Λ` is a projective `Λ`-module. -/
public instance : Module.Projective Λ (TrivialRep Γ Λ) := inferInstanceAs (Module.Projective Λ Λ)

/-- `TrivialRep Γ Λ` is finite when `Λ` is. -/
public instance [Finite Λ] : Finite (TrivialRep Γ Λ) := inferInstanceAs (Finite Λ)

/-- The trivial action of `Γ` on `TrivialRep Γ Λ`: `γ • a = a`. -/
public instance : DistribMulAction Γ (TrivialRep Γ Λ) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- `γ • a = a` in the trivial representation. -/
public theorem smul_def (γ : Γ) (a : TrivialRep Γ Λ) : γ • a = a :=
  rfl

/-- The actions of `Γ` and `Λ` on `TrivialRep Γ Λ` commute. -/
public instance : SMulCommClass Γ Λ (TrivialRep Γ Λ) where
  smul_comm _ _ _ := rfl

/-- The identity `Λ → TrivialRep Γ Λ`. -/
public def of : Λ ≃ₗ[Λ] TrivialRep Γ Λ := LinearEquiv.refl Λ Λ

variable {Γ} [TopologicalSpace Γ] [IsTopologicalGroup Γ]

omit [IsTopologicalGroup Γ] in
/-- Every element of `Γ` stabilizes every point of the trivial representation. -/
public theorem isOpen_stabilizer (a : TrivialRep Γ Λ) : IsOpen {γ : Γ | γ • a = a} := by
  simp [smul_def]

omit [IsTopologicalGroup Γ] in
/-- An open normal subgroup acts trivially. -/
public theorem isSmoothFor (G : Subgroup Γ) [G.Normal] : IsSmoothFor G (TrivialRep Γ Λ) :=
  ⟨topSubgroup, fun _ _ _ => rfl⟩

end TrivialRep

namespace Procyclic

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {G : Subgroup Γ}
  [G.Normal] {Λ : Type u} [Ring Λ]

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- On the trivial representation, `Λ[[G]]` acts through the augmentation. -/
public theorem trivialRep_smul (hV : IsSmoothFor G (TrivialRep Γ Λ))
    (a : CompletedGroupAlgebra Λ G) (x : TrivialRep Γ Λ) :
    (letI := completedGroupAlgebraModule Λ hV; a • x) =
      (TrivialRep.of Γ Λ) (augmentation a * (TrivialRep.of Γ Λ).symm x) := by
  rw [completedGroupAlgebra_smul_def,
    toAddMonoidEnd_eq (TrivialRep Γ Λ) hV topSubgroup (fun _ _ _ => rfl), augmentation,
    RingHom.comp_apply]
  generalize eval topSubgroup a = y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz =>
    rw [map_add, addMonoidEnd_add_apply, hy, hz, map_add, add_mul, map_add]
  | single h b =>
    induction h using QuotientGroup.induction_on with
    | H g =>
      rw [quotientAlgebraAction_single, finiteAugmentation_single]
      rfl

/-- Right multiplication by `c` on `Λ[[G]]`, a `Λ[[G]]`-linear map. -/
public def mulRightLinear (c : CompletedGroupAlgebra Λ G) :
    CompletedGroupAlgebra Λ G →ₗ[CompletedGroupAlgebra Λ G] CompletedGroupAlgebra Λ G where
  toFun x := x * c
  map_add' x y := add_mul x y c
  map_smul' a x := mul_assoc a x c

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- `mulRightLinear c` sends `x` to `x * c`. -/
@[simp]
public theorem mulRightLinear_apply (c x : CompletedGroupAlgebra Λ G) :
    mulRightLinear c x = x * c :=
  rfl

/-- The terms of the Koszul complex: `Λ[[G]]` in degrees `0` and `1`, zero elsewhere. -/
public def koszulX (Λ : Type u) [Ring Λ] (G : Subgroup Γ) :
    ℕ → ModuleCat.{u} (CompletedGroupAlgebra Λ G)
  | 0 => ModuleCat.of _ (CompletedGroupAlgebra Λ G)
  | 1 => ModuleCat.of _ (CompletedGroupAlgebra Λ G)
  | _ + 2 => ModuleCat.of _ PUnit.{u + 1}

variable (Λ) in
/-- The differentials of the Koszul complex: right multiplication by `σ - 1`. -/
public def koszulD (σ : G) : ∀ n : ℕ, koszulX Λ G (n + 1) ⟶ koszulX Λ G n
  | 0 => ModuleCat.ofHom (mulRightLinear ((of σ : CompletedGroupAlgebra Λ G) - 1))
  | _ + 1 => 0

variable (Λ) in
/-- **The Koszul complex** `Λ[[G]] --(· (σ - 1))--> Λ[[G]]`. -/
public def koszulComplex (σ : G) : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ :=
  ChainComplex.of (koszulX Λ G) (koszulD Λ σ) fun n => by
    cases n <;> exact zero_comp

section Resolution

variable (Λ) (σ : G) (hV : IsSmoothFor G (TrivialRep Γ Λ))

/-- The augmentation `Λ[[G]] → Λ`, as a linear map to the trivial representation. -/
@[sga "5 IIIB 6.18" "more general"]
public def koszulAugmentationLinear :
    CompletedGroupAlgebra Λ G →ₗ[CompletedGroupAlgebra Λ G] toCompletedGroupAlgebraModuleCat Λ hV
    where
  toFun a := (TrivialRep.of Γ Λ (augmentation a) : TrivialRep Γ Λ)
  map_add' a b := by
    change TrivialRep.of Γ Λ (augmentation (a + b)) =
      TrivialRep.of Γ Λ (augmentation a) + TrivialRep.of Γ Λ (augmentation b)
    rw [map_add, map_add]
  map_smul' a b := by
    change TrivialRep.of Γ Λ (augmentation (a * b)) =
      (letI := completedGroupAlgebraModule Λ hV; a • TrivialRep.of Γ Λ (augmentation b))
    rw [trivialRep_smul, map_mul]
    rfl

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- `koszulAugmentationLinear Λ hV` sends `a` to the augmentation `ε(a)`. -/
public theorem koszulAugmentationLinear_apply (a : CompletedGroupAlgebra Λ G) :
    koszulAugmentationLinear Λ hV a = TrivialRep.of Γ Λ (augmentation a) :=
  rfl

/-- The augmentation `Λ[[G]] → Λ`, as a morphism to the trivial representation. -/
public def koszulAugmentation :
    (koszulComplex Λ σ).X 0 ⟶ toCompletedGroupAlgebraModuleCat Λ hV :=
  ModuleCat.ofHom (X := CompletedGroupAlgebra Λ G) (Y := toCompletedGroupAlgebraModuleCat Λ hV)
    (koszulAugmentationLinear Λ hV)

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The differential `Λ[[G]] ⟶ Λ[[G]]` of the Koszul complex is right multiplication by `σ - 1`. -/
public theorem koszulComplex_d_one_zero :
    (koszulComplex Λ σ).d 1 0 =
      ModuleCat.ofHom (mulRightLinear ((of σ : CompletedGroupAlgebra Λ G) - 1)) := by
  change ChainComplex.of.d (koszulX Λ G) (koszulD Λ σ) (0 + 1) 0 = _
  rw [ChainComplex.of_d]
  rfl

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The augmentation kills every right multiple of `σ - 1`. -/
public theorem koszulAugmentationLinear_comp_mulRight :
    koszulAugmentationLinear Λ hV ∘ₗ mulRightLinear ((of σ : CompletedGroupAlgebra Λ G) - 1) =
      0 :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, koszulAugmentationLinear_apply, LinearMap.zero_apply,
      mulRightLinear_apply, map_mul, map_sub, augmentation_of, map_one, sub_self, mul_zero,
      map_zero]
    rfl

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The differential of the Koszul complex followed by the augmentation is zero. -/
public theorem koszul_d_comp_augmentation :
    (koszulComplex Λ σ).d 1 0 ≫ koszulAugmentation Λ σ hV = 0 := by
  have key : ModuleCat.ofHom (mulRightLinear ((of σ : CompletedGroupAlgebra Λ G) - 1)) ≫
      ModuleCat.ofHom (X := CompletedGroupAlgebra Λ G)
        (Y := toCompletedGroupAlgebraModuleCat Λ hV) (koszulAugmentationLinear Λ hV) = 0 := by
    rw [← ModuleCat.ofHom_comp, koszulAugmentationLinear_comp_mulRight]
    rfl
  rw [koszulComplex_d_one_zero]
  exact key

/-- The augmentation, as a chain map to the trivial representation in degree `0`. -/
public def koszulπ :
    koszulComplex Λ σ ⟶ (ChainComplex.single₀ _).obj (toCompletedGroupAlgebraModuleCat Λ hV) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨koszulAugmentation Λ σ hV, koszul_d_comp_augmentation Λ σ hV⟩

/-- The terms of the Koszul complex are projective `Λ[[G]]`-modules. -/
public instance koszulComplex_projective (n : ℕ) : Projective ((koszulComplex Λ σ).X n) := by
  rcases n with _ | _ | n
  · exact (IsProjective.iff_projective (CompletedGroupAlgebra Λ G)).1 inferInstance
  · exact (IsProjective.iff_projective (CompletedGroupAlgebra Λ G)).1 inferInstance
  · exact (IsProjective.iff_projective PUnit.{u + 1}).1 inferInstance

end Resolution

section Exactness

variable [CompactSpace G] {σ : G} (hgen : GeneratesQuotients σ) {n : ℕ} (hn : n ≠ 0)
  (hpow : ∀ p : ℕ, p.Prime → p ∣ n → HasPrimePowerQuotients σ p) (hΛ : ∀ a : Λ, n • a = 0)
  (hV : IsSmoothFor G (TrivialRep Γ Λ))
include hgen hn hpow hΛ

omit [G.Normal] in
/-- **The Koszul complex resolves the trivial module.** -/
public theorem koszulπ_quasiIso : QuasiIso (koszulπ Λ σ hV) where
  quasiIsoAt m := by
    rcases m with _ | m
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ ?_ rfl rfl]
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff]
          intro x hx
          change TrivialRep.of Γ Λ (augmentation (show CompletedGroupAlgebra Λ G from x)) =
            (0 : TrivialRep Γ Λ) at hx
          have hx' : augmentation (show CompletedGroupAlgebra Λ G from x) = 0 :=
            (TrivialRep.of Γ Λ).injective (hx.trans (map_zero _).symm)
          obtain ⟨y, hy⟩ := exists_mul_eq_of_augmentation_eq_zero hgen hn hpow hΛ hx'
          refine ⟨y, ?_⟩
          change ((koszulComplex Λ σ).d 1 0).hom y = x
          rw [koszulComplex_d_one_zero]
          change y * ((of σ : CompletedGroupAlgebra Λ G) - 1) =
            (show CompletedGroupAlgebra Λ G from x)
          rw [← sub_one_mul_comm hgen, hy]
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          refine ⟨(const ((TrivialRep.of Γ Λ).symm (show TrivialRep Γ Λ from x)) :
            CompletedGroupAlgebra Λ G), ?_⟩
          change koszulAugmentationLinear Λ hV _ = x
          rw [koszulAugmentationLinear_apply, augmentation_const]
          exact (TrivialRep.of Γ Λ).apply_symm_apply _
      · change (koszulComplex Λ σ).d 0 0 = 0
        exact (koszulComplex Λ σ).shape 0 0 (by simp)
    · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rcases m with _ | m
      · rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
          ShortComplex.moduleCat_exact_iff]
        intro x hx
        refine ⟨0, ?_⟩
        rw [map_zero]
        change ((koszulComplex Λ σ).d 1 0).hom x = 0 at hx
        rw [koszulComplex_d_one_zero] at hx
        change (show CompletedGroupAlgebra Λ G from x) * ((of σ : CompletedGroupAlgebra Λ G) - 1) =
          0 at hx
        rw [← sub_one_mul_comm hgen] at hx
        exact (eq_zero_of_mul_eq_zero hgen hn hpow hΛ hx).symm
      · rw [HomologicalComplex.exactAt_iff' _ (m + 3) (m + 2) (m + 1) (by simp) (by simp)]
        refine ShortComplex.exact_of_isZero_X₂ _ ?_
        change IsZero (ModuleCat.of (CompletedGroupAlgebra Λ G) PUnit.{u + 1})
        exact ModuleCat.isZero_of_subsingleton _

/-- **The Koszul resolution** `0 → Λ[[G]] --(· (σ - 1))--> Λ[[G]] --ε--> Λ → 0` of the trivial
module. -/
public abbrev koszulResolution :
    ProjectiveResolution (toCompletedGroupAlgebraModuleCat Λ hV) where
  complex := koszulComplex Λ σ
  π := koszulπ Λ σ hV
  quasiIso := koszulπ_quasiIso hgen hn hpow hΛ hV

end Exactness

end Procyclic

end Stacks.GroupHomology

end
