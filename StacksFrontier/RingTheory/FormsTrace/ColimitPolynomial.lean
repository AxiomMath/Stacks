module

public import StacksFrontier.RingTheory.FormsTrace.Colimit
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Trace maps on forms over a polynomial ring in arbitrarily many variables

Let `N` be a ring, `B_N` a finite projective `N`-algebra and `σ` any type. Put
`R = N[x_s, s ∈ σ]` and `B = R ⊗_N B_N`, and for a finite subset `F ⊆ σ` put `R_F = N[x_s, s ∈ F]`
and `B_F = R_F ⊗_N B_N`. Given trace maps `Θ_F^p : Ω^p_{B_F} → Ω^p_{R_F}` with property (1) of
Stacks, Lemma 0FLB, compatible along the inclusions `F ⊆ F'`, they glue to trace maps
`Θ^p : Ω^p_B → Ω^p_R` with property (1), compatible with every `Θ_F`, and inheriting property (2)
of Proposition 0FLC and the compatibility with the de Rham differentials from the stages. This is
the passage to the limit in the proof of Proposition 0FLC.

The ring maps `R_F → R` (renaming the variables) and `B_F → B` are made algebras by scoped
instances (`open scoped Stacks.FormsTrace.PolynomialStages`); the transition maps for `F ⊆ F'`
depend on the proof of `F ⊆ F'` and are the definitions `transitionAlgebra` and
`transitionAlgebraTensor`.

The two inputs of the general gluing (`StacksFrontier/RingTheory/FormsTrace/Colimit.lean`) are
verified here: every polynomial involves finitely many variables, so the stages exhaust `R → B`;
and `Ω^p_{B_F} → Ω^p_B` is injective, being split by the retraction `B → B_F` that sends the
other variables to `0`, so compatibility along inclusions implies the compatibility in the limit.

## Main results

* `Stacks.FormsTrace.PolynomialStages.isExhaustive`: the stages exhaust `R → B`.
* `Stacks.FormsTrace.PolynomialStages.formsMap_injective`: `Ω^p_{B_F} → Ω^p_B` is injective.
* `Stacks.FormsTrace.PolynomialStages.exists_colimit`: the glued trace maps.
* `Stacks.FormsTrace.PolynomialStages.transition_comm_of_nice`,
  `Stacks.FormsTrace.PolynomialStages.exists_colimit_of_nice`: the compatibility of the stages
  is automatic over an element of `N` a power of which kills the relative differentials and which
  is a nonzerodivisor on the forms of the stages.
* `Stacks.FormsTrace.PolynomialStages.eq_of_forall_stage`: uniqueness.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

universe u

namespace Stacks.FormsTrace

namespace PolynomialStages

open DescentAux

variable (N BN : Type u) [CommRing N] [CommRing BN] [Algebra N BN] {σ : Type u}

/-- The renaming of variables `N[x_s, s ∈ F] → N[x_s, s ∈ σ]` for a finite subset `F ⊆ σ`, as an
algebra structure. -/
@[instance_reducible]
def stageAlgebra (F : Finset σ) : Algebra (MvPolynomial F N) (MvPolynomial σ N) :=
  (rename (Subtype.val : F → σ) : MvPolynomial F N →ₐ[N] MvPolynomial σ N).toRingHom.toAlgebra

attribute [scoped instance] stageAlgebra

/-- The algebra map `R_F → R` is the renaming of the variables along the inclusion `F ⊆ σ`. -/
theorem stageAlgebra_algebraMap_apply (F : Finset σ) (x : MvPolynomial F N) :
    algebraMap (MvPolynomial F N) (MvPolynomial σ N) x = rename Subtype.val x := rfl

/-- The renaming map `R_F → R` is a map of `N`-algebras. -/
scoped instance stageIsScalarTower (F : Finset σ) :
    IsScalarTower N (MvPolynomial F N) (MvPolynomial σ N) :=
  IsScalarTower.of_algebraMap_eq' (rename (R := N) (Subtype.val : F → σ)).comp_algebraMap.symm

/-- The map `B_F = R_F ⊗_N B_N → B = R ⊗_N B_N` induced by renaming the variables, as an
algebra structure. -/
@[instance_reducible]
def stageAlgebraTensor (F : Finset σ) :
    Algebra (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) :=
  (Algebra.TensorProduct.map (rename (R := N) (Subtype.val : F → σ))
    (AlgHom.id N BN)).toRingHom.toAlgebra

attribute [scoped instance] stageAlgebraTensor

/-- The algebra map `B_F → B` is the tensor product of the renaming of the variables along `F ⊆ σ`
with the identity of `B_N`. -/
theorem stageAlgebraTensor_algebraMap_apply (F : Finset σ) (x : MvPolynomial F N ⊗[N] BN) :
    algebraMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) x =
      Algebra.TensorProduct.map (rename (R := N) (Subtype.val : F → σ)) (AlgHom.id N BN) x :=
  rfl

/-- The square `R_F → B_F → B`, `R_F → R → B` commutes. -/
scoped instance stageIsScalarTowerTensor (F : Finset σ) :
    IsScalarTower (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [stageAlgebraTensor_algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl

/-- `B = R ⊗_{R_F} B_F`: the stage `R_F → B_F` base changes to `R → B`. -/
scoped instance stageIsPushout (F : Finset σ) :
    Algebra.IsPushout (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N)
      (MvPolynomial σ N ⊗[N] BN) := by
  refine Algebra.IsPushout.symm ⟨IsBaseChange.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange N (MvPolynomial F N) (MvPolynomial σ N)
      (MvPolynomial σ N) BN) fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
  | tmul a b =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    change _ = Algebra.TensorProduct.map (rename (R := N) (Subtype.val : F → σ)) (AlgHom.id N BN)
      (a ⊗ₜ b)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

open Classical in
/-- The retraction `N[x_s, s ∈ σ] → N[x_s, s ∈ F]` sending the variables outside `F` to `0`. -/
def retraction (F : Finset σ) : MvPolynomial σ N →ₐ[N] MvPolynomial F N :=
  aeval fun s => if h : s ∈ F then X ⟨s, h⟩ else 0

/-- The retraction `R → R_F` is a left inverse of the renaming of variables `R_F → R`. -/
theorem retraction_rename (F : Finset σ) (x : MvPolynomial F N) :
    retraction N F (rename Subtype.val x) = x := by
  have : (retraction N F).comp (rename Subtype.val) = AlgHom.id N (MvPolynomial F N) := by
    refine MvPolynomial.algHom_ext fun t => ?_
    rw [AlgHom.comp_apply, rename_X, retraction, aeval_X, dif_pos t.2, AlgHom.id_apply]
  exact AlgHom.congr_fun this x

/-- **The pull-back of forms from a stage is injective**: `Ω^p_{B_F} → Ω^p_B` is split by the
pull-back along the retraction `B → B_F` sending the variables outside `F` to `0`. -/
theorem formsMap_injective (F : Finset σ) (p : ℕ) :
    Function.Injective
      (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) p) := by
  let ρ : MvPolynomial σ N ⊗[N] BN →ₐ[N] MvPolynomial F N ⊗[N] BN :=
    Algebra.TensorProduct.map (retraction N F) (AlgHom.id N BN)
  refine formsMap_injective_of_leftInverse ρ.toRingHom (fun x => ?_) p
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    show ρ (algebraMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) (a ⊗ₜ b)) = a ⊗ₜ b
    rw [stageAlgebraTensor_algebraMap_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, retraction_rename, AlgHom.id_apply, AlgHom.id_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The inclusion of variables `F → F'` for `F ⊆ F'`. -/
def inclusion {F F' : Finset σ} (h : F ⊆ F') : F → F' := fun x => ⟨x.1, h x.2⟩

/-- The renaming of variables `N[x_s, s ∈ F] → N[x_s, s ∈ F']` for `F ⊆ F'`, as an algebra
structure: the transition map of the stages. -/
@[instance_reducible]
def transitionAlgebra {F F' : Finset σ} (h : F ⊆ F') :
    Algebra (MvPolynomial F N) (MvPolynomial F' N) :=
  (rename (R := N) (inclusion h)).toRingHom.toAlgebra

/-- The transition map `B_F → B_{F'}` for `F ⊆ F'`, as an algebra structure. -/
@[instance_reducible]
def transitionAlgebraTensor {F F' : Finset σ} (h : F ⊆ F') :
    Algebra (MvPolynomial F N ⊗[N] BN) (MvPolynomial F' N ⊗[N] BN) :=
  (Algebra.TensorProduct.map (rename (R := N) (inclusion h)) (AlgHom.id N BN)).toRingHom.toAlgebra

/-- Renaming the variables along `F ⊆ F'` and then along `F' ⊆ σ` is renaming them along
`F ⊆ σ`. -/
theorem rename_val_rename_inclusion {F F' : Finset σ} (h : F ⊆ F') (x : MvPolynomial F N) :
    rename (Subtype.val : F' → σ) (rename (inclusion h) x) = rename Subtype.val x := by
  rw [rename_rename]
  rfl

/-- The transition maps of the polynomial rings form towers with the maps to `R`. -/
theorem transition_isScalarTower {F F' : Finset σ} (h : F ⊆ F') :
    letI := transitionAlgebra N h
    IsScalarTower (MvPolynomial F N) (MvPolynomial F' N) (MvPolynomial σ N) :=
  let := transitionAlgebra N h
  IsScalarTower.of_algebraMap_eq fun x => (rename_val_rename_inclusion N h x).symm

/-- The transition maps of the tensor products form towers with the maps to `B`. -/
theorem transition_isScalarTower_tensor {F F' : Finset σ} (h : F ⊆ F') :
    letI := transitionAlgebraTensor N BN h
    IsScalarTower (MvPolynomial F N ⊗[N] BN) (MvPolynomial F' N ⊗[N] BN)
      (MvPolynomial σ N ⊗[N] BN) :=
  let := transitionAlgebraTensor N BN h
  IsScalarTower.of_algebraMap_eq fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a b =>
      show Algebra.TensorProduct.map (rename (R := N) (Subtype.val : F → σ)) (AlgHom.id N BN)
          (a ⊗ₜ b) = Algebra.TensorProduct.map (rename (R := N) (Subtype.val : F' → σ))
          (AlgHom.id N BN) (Algebra.TensorProduct.map (rename (R := N) (inclusion h))
            (AlgHom.id N BN) (a ⊗ₜ b))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        rename_val_rename_inclusion]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Every polynomial in the variables `σ` eventually (for all large finite `F ⊆ σ`) comes from
`N[x_s, s ∈ F]`. -/
theorem eventually_mem_range_algebraMap (r : MvPolynomial σ N) :
    ∀ᶠ F : Finset σ in Filter.atTop,
      r ∈ Set.range (algebraMap (MvPolynomial F N) (MvPolynomial σ N)) := by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename r
  exact Filter.eventually_atTop.2 ⟨s, fun F hF =>
    ⟨rename (inclusion hF) q, rename_val_rename_inclusion N hF q⟩⟩

/-- Every element of `B = R ⊗_N B_N` eventually comes from `B_F`. -/
theorem eventually_mem_range_algebraMap_tensor (b : MvPolynomial σ N ⊗[N] BN) :
    ∀ᶠ F : Finset σ in Filter.atTop,
      b ∈ Set.range (algebraMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN)) := by
  induction b using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun F => ⟨0, map_zero _⟩
  | tmul r b =>
    refine (eventually_mem_range_algebraMap N r).mono fun F ⟨q, hq⟩ => ⟨q ⊗ₜ b, ?_⟩
    rw [stageAlgebraTensor_algebraMap_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg (· ⊗ₜ[N] b) hq
  | add x y hx hy =>
    exact (hx.and hy).mono fun F ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ => ⟨a + c, by rw [map_add, ha, hc]⟩

/-- **The stages `R_F → B_F` exhaust `R → B`.** -/
theorem isExhaustive :
    IsExhaustive (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN)
      (fun F : Finset σ => MvPolynomial F N) (fun F : Finset σ => MvPolynomial F N ⊗[N] BN) :=
  isExhaustive_of_eventually Filter.atTop (eventually_mem_range_algebraMap N)
    (eventually_mem_range_algebraMap_tensor N BN)

/-- **Compatibility along the inclusions of finite sets of variables implies the compatibility
of the family in the limit.** -/
theorem isCompatibleFamily
    (Θ : ∀ (F : Finset σ) (p : ℕ), ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]
      →ₗ[MvPolynomial F N] ⋀[MvPolynomial F N]^p Ω[MvPolynomial F N⁄ℤ])
    (hc : ∀ (F F' : Finset σ) (h : F ⊆ F'),
      letI := transitionAlgebra N h
      letI := transitionAlgebraTensor N BN h
      ∀ (p : ℕ) (η : ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]),
        Θ F' p (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial F' N ⊗[N] BN) p η) =
          formsMap (MvPolynomial F N) (MvPolynomial F' N) p (Θ F p η)) :
    IsCompatibleFamily (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN) Θ := by
  classical
  intro F F' p η η' h
  let := transitionAlgebra N (Finset.subset_union_left : F ⊆ F ∪ F')
  let := transitionAlgebraTensor N BN (Finset.subset_union_left : F ⊆ F ∪ F')
  let := transitionAlgebra N (Finset.subset_union_right : F' ⊆ F ∪ F')
  let := transitionAlgebraTensor N BN (Finset.subset_union_right : F' ⊆ F ∪ F')
  have := transition_isScalarTower N (Finset.subset_union_left : F ⊆ F ∪ F')
  have := transition_isScalarTower_tensor N BN (Finset.subset_union_left : F ⊆ F ∪ F')
  have := transition_isScalarTower N (Finset.subset_union_right : F' ⊆ F ∪ F')
  have := transition_isScalarTower_tensor N BN (Finset.subset_union_right : F' ⊆ F ∪ F')
  exact formsMap_eq_of_tower (Θ F) (Θ F') (Θ (F ∪ F')) (formsMap_injective N BN (F ∪ F') p)
    (hc F (F ∪ F') Finset.subset_union_left p) (hc F' (F ∪ F') Finset.subset_union_right p) η η' h

/-- **Trace maps on the forms of a polynomial ring in arbitrarily many variables.** Let `B_N` be
a finite projective `N`-algebra, `R = N[x_s, s ∈ σ]`, `B = R ⊗_N B_N`, and for finite `F ⊆ σ` let
`R_F = N[x_s, s ∈ F]`, `B_F = R_F ⊗_N B_N`. Given families `Θ_F` on the forms of `B_F` with
property (1) of Stacks, Lemma 0FLB, compatible along the inclusions `F ⊆ F'`, there is a family
`Θ` on the forms of `B` with property (1), compatible with every `Θ_F`, which has property (2) of
Proposition 0FLC, respectively commutes with the de Rham differentials, when every `Θ_F` does. -/
theorem exists_colimit [Module.Finite N BN] [Module.Projective N BN]
    (Θ : ∀ (F : Finset σ) (p : ℕ), ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]
      →ₗ[MvPolynomial F N] ⋀[MvPolynomial F N]^p Ω[MvPolynomial F N⁄ℤ])
    (htr : ∀ F : Finset σ, IsFormsTrace (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (Θ F))
    (hc : ∀ (F F' : Finset σ) (h : F ⊆ F'),
      letI := transitionAlgebra N h
      letI := transitionAlgebraTensor N BN h
      ∀ (p : ℕ) (η : ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]),
        Θ F' p (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial F' N ⊗[N] BN) p η) =
          formsMap (MvPolynomial F N) (MvPolynomial F' N) p (Θ F p η)) :
    ∃ Θ' : ∀ p : ℕ, ⋀[MvPolynomial σ N ⊗[N] BN]^p Ω[MvPolynomial σ N ⊗[N] BN⁄ℤ]
        →ₗ[MvPolynomial σ N] ⋀[MvPolynomial σ N]^p Ω[MvPolynomial σ N⁄ℤ],
      IsFormsTrace (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN) Θ' ∧
      (∀ (F : Finset σ) (p : ℕ) (η : ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]),
        Θ' p (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) p η) =
          formsMap (MvPolynomial F N) (MvPolynomial σ N) p (Θ F p η)) ∧
      ((∀ F : Finset σ, IsWedgeLinear (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (Θ F)) →
        IsWedgeLinear (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN) Θ') ∧
      ((∀ F : Finset σ, CommutesWithD (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (Θ F)) →
        CommutesWithD (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN) Θ') :=
  ⟨colimitForms (isExhaustive N BN) Θ (isCompatibleFamily N BN Θ hc),
    isFormsTrace_colimitForms _ Θ _ htr, colimitForms_formsMap _ Θ _,
    isWedgeLinear_colimitForms _ Θ _, commutesWithD_colimitForms _ Θ _⟩

/-- The renaming map `R_F → R_{F'}` is a map of `N`-algebras. -/
theorem transition_isScalarTower_base {F F' : Finset σ} (h : F ⊆ F') :
    letI := transitionAlgebra N h
    IsScalarTower N (MvPolynomial F N) (MvPolynomial F' N) :=
  let := transitionAlgebra N h
  IsScalarTower.of_algebraMap_eq' (rename (R := N) (inclusion h)).comp_algebraMap.symm

/-- **Compatibility along the inclusions from a nice element of the base.** Let `h ∈ N` be such
that, for every finite `F ⊆ σ`, a power of `h` kills `Ω_{B_F/R_F}` and `h` is a nonzerodivisor
on the forms of `R_F`. Then any two families with property (1) of Lemma 0FLB on the stages
`F ⊆ F'` are compatible along the transition maps (`IsFormsTrace.formsMap_comm_of_isPushout`
applied to the pushout square `B_{F'} = R_{F'} ⊗_{R_F} B_F`). -/
theorem transition_comm_of_nice [Module.Finite N BN] [Module.Projective N BN] (h₀ : N)
    (hN : ∀ F : Finset σ, ∃ n : ℕ, ∀ x : Ω[MvPolynomial F N ⊗[N] BN⁄MvPolynomial F N],
      algebraMap N (MvPolynomial F N) h₀ ^ n • x = 0)
    (hreg : ∀ (F : Finset σ) (p : ℕ),
      IsSMulRegular (⋀[MvPolynomial F N]^p Ω[MvPolynomial F N⁄ℤ])
        (algebraMap N (MvPolynomial F N) h₀))
    (Θ : ∀ (F : Finset σ) (p : ℕ), ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]
      →ₗ[MvPolynomial F N] ⋀[MvPolynomial F N]^p Ω[MvPolynomial F N⁄ℤ])
    (htr : ∀ F : Finset σ, IsFormsTrace (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (Θ F))
    (F F' : Finset σ) (h : F ⊆ F') :
    letI := transitionAlgebra N h
    letI := transitionAlgebraTensor N BN h
    ∀ (p : ℕ) (η : ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]),
      Θ F' p (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial F' N ⊗[N] BN) p η) =
        formsMap (MvPolynomial F N) (MvPolynomial F' N) p (Θ F p η) := by
  let := transitionAlgebra N h
  let := transitionAlgebraTensor N BN h
  have := transition_isScalarTower_base N h
  have : IsScalarTower (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN)
      (MvPolynomial F' N ⊗[N] BN) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show _ = Algebra.TensorProduct.map (rename (R := N) (inclusion h)) (AlgHom.id N BN)
        (x ⊗ₜ 1)
      rw [Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.algebraMap_apply]
      rfl
  have : Algebra.IsPushout (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (MvPolynomial F' N)
      (MvPolynomial F' N ⊗[N] BN) := by
    refine Algebra.IsPushout.symm
      (Algebra.IsPushout.tensorProduct_tensorProduct N BN (MvPolynomial F N) (MvPolynomial F' N)
        (RingHom.ext fun b => ?_))
    show Algebra.TensorProduct.map (rename (R := N) (inclusion h)) (AlgHom.id N BN)
      (1 ⊗ₜ b) = 1 ⊗ₜ b
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  obtain ⟨n, hn⟩ := hN F
  intro p η
  refine IsFormsTrace.formsMap_comm_of_isPushout hn (fun q => ?_) (htr F) (htr F') p η
  rw [← IsScalarTower.algebraMap_apply]
  exact hreg F' q

/-- **Trace maps on the forms of a polynomial ring in arbitrarily many variables, over a nice
base element.** As `exists_colimit`, with the compatibility of the stages deduced from an element
`h ∈ N` a power of which kills every `Ω_{B_F/R_F}` and which is a nonzerodivisor on the forms of
every `R_F` (`transition_comm_of_nice`). -/
theorem exists_colimit_of_nice [Module.Finite N BN] [Module.Projective N BN] (h₀ : N)
    (hN : ∀ F : Finset σ, ∃ n : ℕ, ∀ x : Ω[MvPolynomial F N ⊗[N] BN⁄MvPolynomial F N],
      algebraMap N (MvPolynomial F N) h₀ ^ n • x = 0)
    (hreg : ∀ (F : Finset σ) (p : ℕ),
      IsSMulRegular (⋀[MvPolynomial F N]^p Ω[MvPolynomial F N⁄ℤ])
        (algebraMap N (MvPolynomial F N) h₀))
    (Θ : ∀ (F : Finset σ) (p : ℕ), ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]
      →ₗ[MvPolynomial F N] ⋀[MvPolynomial F N]^p Ω[MvPolynomial F N⁄ℤ])
    (htr : ∀ F : Finset σ, IsFormsTrace (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (Θ F)) :
    ∃ Θ' : ∀ p : ℕ, ⋀[MvPolynomial σ N ⊗[N] BN]^p Ω[MvPolynomial σ N ⊗[N] BN⁄ℤ]
        →ₗ[MvPolynomial σ N] ⋀[MvPolynomial σ N]^p Ω[MvPolynomial σ N⁄ℤ],
      IsFormsTrace (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN) Θ' ∧
      (∀ (F : Finset σ) (p : ℕ) (η : ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]),
        Θ' p (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) p η) =
          formsMap (MvPolynomial F N) (MvPolynomial σ N) p (Θ F p η)) ∧
      ((∀ F : Finset σ, IsWedgeLinear (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (Θ F)) →
        IsWedgeLinear (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN) Θ') ∧
      ((∀ F : Finset σ, CommutesWithD (MvPolynomial F N) (MvPolynomial F N ⊗[N] BN) (Θ F)) →
        CommutesWithD (MvPolynomial σ N) (MvPolynomial σ N ⊗[N] BN) Θ') :=
  exists_colimit N BN Θ htr (transition_comm_of_nice N BN h₀ hN hreg Θ htr)

/-- **Uniqueness**: a family on the forms of `B = R ⊗_N B_N` is determined by its composites with
the restrictions from the stages `B_F`. -/
theorem eq_of_forall_stage
    {Θ₁ Θ₂ : ∀ p : ℕ, ⋀[MvPolynomial σ N ⊗[N] BN]^p Ω[MvPolynomial σ N ⊗[N] BN⁄ℤ]
      →ₗ[MvPolynomial σ N] ⋀[MvPolynomial σ N]^p Ω[MvPolynomial σ N⁄ℤ]}
    (h : ∀ (F : Finset σ) (p : ℕ)
      (η : ⋀[MvPolynomial F N ⊗[N] BN]^p Ω[MvPolynomial F N ⊗[N] BN⁄ℤ]),
      Θ₁ p (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) p η) =
        Θ₂ p (formsMap (MvPolynomial F N ⊗[N] BN) (MvPolynomial σ N ⊗[N] BN) p η)) :
    Θ₁ = Θ₂ :=
  eq_of_forall_formsMap_eq (Bs := fun F : Finset σ => MvPolynomial F N ⊗[N] BN)
    (fun _ x => (isExhaustive (σ := σ) N BN).exists_formsMap_eq x) h

end PolynomialStages

end Stacks.FormsTrace

end
