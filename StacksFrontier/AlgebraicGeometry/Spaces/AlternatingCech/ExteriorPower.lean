module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Contraction on exterior powers and the Koszul complex of a presheaf of abelian groups

A linear form `d : M →ₗ[R] R` contracts the exterior algebra of `M`, and the contraction
carries `⋀^{n+1} M` into `⋀^n M`.  The resulting maps square to zero, so a presheaf `F` of
abelian groups together with a map `ε` to the constant presheaf `ℤ` gives a chain complex
whose term in degree `n` is the objectwise exterior power `⋀^{n+1} F`, the Koszul complex of
`ε`, augmented by `ε` towards the constant presheaf `ℤ`.

## Main definitions

* `exteriorPower.contract` is the contraction `⋀^{n+1} M →ₗ[R] ⋀^n M` by a linear form, the
  restriction of `CliffordAlgebra.contractLeft` to exterior powers.
* `AddCommGrpCat.presheafExteriorPower` is the objectwise exterior power over `ℤ` of a
  presheaf of abelian groups, and `AddCommGrpCat.presheafExteriorPowerOne` identifies the
  first one with the presheaf itself.
* `AddCommGrpCat.presheafKoszulDiff` is the objectwise contraction by a map to the constant
  presheaf `ℤ`, `AddCommGrpCat.presheafKoszul` the chain complex it forms, whose term in
  degree `n` is the `(n+1)`-st exterior power, and
  `AddCommGrpCat.presheafKoszulAugmentation` the map from its term in degree `0` to the
  constant presheaf `ℤ`.

## Main results

* `exteriorPower.contract_contract`: the contraction squares to zero.
* `exteriorPower.map_contract`: contraction commutes with the exterior power of a linear map
  compatible with the two linear forms.
* `exteriorPower.contract_ιMulti`: the contraction of `m 0 ∧ ⋯ ∧ m n` is the alternating sum
  over `i` of `(-1) ^ i * d (m i)` times the wedge with the `i`-th factor omitted.
* `AddCommGrpCat.presheafKoszulDiff_comp_presheafKoszulAugmentation`: the composite of the
  first differential with the augmentation vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory CliffordAlgebra ExteriorAlgebra

universe w v u

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Contraction by a linear form carries the `(n+1)`-st exterior power into the `n`-th. -/
theorem contractLeft_mem (d : Module.Dual R M) (n : ℕ) :
    ⋀[R]^(n + 1) M ≤ (⋀[R]^n M).comap (contractLeft d) := by
  set P := LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) with hP
  induction n with
  | zero =>
      change P ^ 1 ≤ _
      rw [pow_one]
      rintro x ⟨a, rfl⟩
      simp only [Submodule.mem_comap, contractLeft_ι]
      change _ ∈ P ^ 0
      rw [pow_zero]
      exact Submodule.mem_one.2 ⟨d a, rfl⟩
  | succ n ih =>
      change P ^ (n + 1 + 1) ≤ _
      rw [pow_succ' P (n + 1), Submodule.mul_le]
      rintro x ⟨a, rfl⟩ y hy
      simp only [Submodule.mem_comap, contractLeft_ι_mul]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) ?_
      change _ ∈ P ^ (n + 1)
      rw [pow_succ' P n]
      exact Submodule.mul_mem_mul ⟨a, rfl⟩ (ih hy)

/-- Contraction of the `(n+1)`-st exterior power of `M` by a linear form on `M`. -/
@[sga "7 XII 1.3.1"]
def contract (d : Module.Dual R M) (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  (contractLeft d).restrict (contractLeft_mem d n)

/-- Contraction on exterior powers is computed by contraction on the exterior algebra. -/
@[simp]
theorem coe_contract (d : Module.Dual R M) (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    (contract d n x : ExteriorAlgebra R M) = contractLeft d (x : ExteriorAlgebra R M) :=
  rfl

/-- Contracting twice by the same linear form gives zero. -/
theorem contract_contract (d : Module.Dual R M) (n : ℕ) (x : ⋀[R]^(n + 1 + 1) M) :
    contract d n (contract d (n + 1) x) = 0 :=
  Subtype.ext (by simp [contractLeft_contractLeft])

/-- Contraction commutes with the map of exterior algebras induced by a linear map, provided
the linear form on the source is the one on the target pulled back along it. -/
theorem map_contractLeft (g : M →ₗ[R] N) (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map g (contractLeft (d ∘ₗ g) x) =
      contractLeft d (ExteriorAlgebra.map g x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp [hx, hy]
  | ι_mul a x hx =>
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, map_mul,
        ExteriorAlgebra.map_apply_ι, hx, contractLeft_ι_mul]
      simp

/-- Contraction commutes with the exterior power of a linear map, provided the linear form on
the source is the one on the target pulled back along it. -/
theorem map_contract (g : M →ₗ[R] N) (d : Module.Dual R N) (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    exteriorPower.map n g (contract (d ∘ₗ g) n x) =
      contract d n (exteriorPower.map (n + 1) g x) :=
  Subtype.ext (by
    simp only [coe_map, coe_contract]
    exact map_contractLeft g d _)

/-- Contraction of a product of `n + 1` vectors in the exterior algebra is the alternating
sum of the products with one factor removed, weighted by the value of the linear form at the
removed factor. -/
theorem contractLeft_ιMulti (d : Module.Dual R M) (n : ℕ) (m : Fin (n + 1) → M) :
    contractLeft d (ExteriorAlgebra.ιMulti R (n + 1) m) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * d (m i)) •
        ExteriorAlgebra.ιMulti R n (m ∘ i.succAbove) := by
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
      have hcomp : ∀ i : Fin (n + 1),
          ExteriorAlgebra.ιMulti R (n + 1) (m ∘ i.succ.succAbove) =
            CliffordAlgebra.ι (0 : QuadraticForm R M) (m 0) *
              ExteriorAlgebra.ιMulti R n (Matrix.vecTail m ∘ i.succAbove) := by
        intro i
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        congr 1
        exact congrArg _ (funext fun j => by
          simp [Matrix.vecTail, Fin.succ_succAbove_succ])
      have h0 : m ∘ (0 : Fin (n + 2)).succAbove = Matrix.vecTail m := by
        funext j
        simp [Matrix.vecTail]
      rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, ih (Matrix.vecTail m)]
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [Finset.mul_sum, h0]
      have hstep : ∀ i : Fin (n + 1),
          CliffordAlgebra.ι (0 : QuadraticForm R M) (m 0) *
              (((-1 : R) ^ (i : ℕ) * d (Matrix.vecTail m i)) •
                ExteriorAlgebra.ιMulti R n (Matrix.vecTail m ∘ i.succAbove)) =
            -(((-1 : R) ^ ((i.succ : Fin (n + 2)) : ℕ) * d (m i.succ)) •
                ExteriorAlgebra.ιMulti R (n + 1) (m ∘ i.succ.succAbove)) := by
        intro i
        rw [mul_smul_comm, hcomp i, Fin.val_succ, pow_succ]
        simp [Matrix.vecTail, mul_comm, neg_smul]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i),
        Finset.sum_neg_distrib, sub_neg_eq_add]
      simp

/-- Contraction of a wedge of `n + 1` vectors is the alternating sum of the wedges with one
factor removed, weighted by the value of the linear form at the removed factor. -/
theorem contract_ιMulti (d : Module.Dual R M) (n : ℕ) (m : Fin (n + 1) → M) :
    contract d n (ιMulti R (n + 1) m) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * d (m i)) • ιMulti R n (m ∘ i.succAbove) :=
  Subtype.ext (by simpa using contractLeft_ιMulti d n m)

/-- Contracting an element of the second exterior power and pairing the result with the same
linear form gives zero. -/
@[ega "III 1.1.1" "The clause i_f ∘ i_f = 0"]
theorem apply_oneEquiv_contract_eq_zero (d : Module.Dual R M) (x : ⋀[R]^2 M) :
    d (oneEquiv R M (contract d 1 x)) = 0 := by
  have hx : x ∈ (⊤ : Submodule R (⋀[R]^2 M)) := Submodule.mem_top
  rw [← ιMulti_span R 2 M] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [contract_ιMulti, Fin.sum_univ_two]
      simp only [map_add, map_smul, oneEquiv_ιMulti, Function.comp_apply, Fin.isValue,
        Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, smul_eq_mul]
      simp
      ring
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul r y _ hy => simp [hy]

end exteriorPower

namespace AddCommGrpCat

variable {C : Type u} [Category.{v} C]

/-- The objectwise `n`-th exterior power over `ℤ` of a presheaf of abelian groups. -/
def presheafExteriorPower (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V := AddCommGrpCat.of (⋀[ℤ]^n (F.obj V))
  map {_ _} f :=
    AddCommGrpCat.ofHom (exteriorPower.map n (F.map f).hom.toIntLinearMap).toAddMonoidHom
  map_id V := by
    have h : exteriorPower.map n (F.map (𝟙 V)).hom.toIntLinearMap =
        LinearMap.id (R := ℤ) (M := ⋀[ℤ]^n (F.obj V)) := by
      rw [show (F.map (𝟙 V)).hom.toIntLinearMap = LinearMap.id (R := ℤ) (M := F.obj V) from
        by ext y; simp, exteriorPower.map_id]
    rw [h]
    rfl
  map_comp {V W Z} f g := by
    have h : (F.map (f ≫ g)).hom.toIntLinearMap =
        (F.map g).hom.toIntLinearMap ∘ₗ (F.map f).hom.toIntLinearMap := by
      ext y
      simp
    rw [h, exteriorPower.map_comp]
    rfl

/-- The first exterior power of a presheaf of abelian groups is the presheaf itself. -/
def presheafExteriorPowerOne (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    presheafExteriorPower F 1 ≅ F :=
  NatIso.ofComponents
    (fun V => AddEquiv.toAddCommGrpIso (exteriorPower.oneEquiv ℤ (F.obj V)).toAddEquiv)
    (fun {V W} f => by
      ext x
      exact congrFun (congrArg (fun g : ⋀[ℤ]^1 (F.obj V) →ₗ[ℤ] F.obj W => ⇑g)
        (exteriorPower.oneEquiv_naturality (F.map f).hom.toIntLinearMap)) x)

/-- The constant presheaf of integers, in the universe of the presheaves considered. -/
abbrev constantInt (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ))

/-- The linear form on the sections of `F` over `V` cut out by a map `ε` from `F` to the
constant presheaf of integers. -/
def presheafDual {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C) (V : Cᵒᵖ) :
    Module.Dual ℤ (F.obj V) :=
  (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toLinearMap ∘ₗ (ε.app V).hom.toIntLinearMap

/-- Restriction along `f` carries the linear form at the target to the one at the source. -/
theorem presheafDual_comp {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C)
    {V W : Cᵒᵖ} (f : V ⟶ W) :
    presheafDual ε W ∘ₗ (F.map f).hom.toIntLinearMap = presheafDual ε V := by
  ext x
  have h := congrFun (congrArg (fun k : F.obj V ⟶ (constantInt.{w} C).obj W => ⇑k.hom)
    (ε.naturality f)) x
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
    Functor.const_obj_map] at h
  exact congrArg (fun y : ULift.{w} ℤ => y.down) h

/-- The Koszul differential of a map to the constant presheaf of integers: objectwise
contraction of the exterior powers by the associated linear form. -/
def presheafKoszulDiff {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C) (n : ℕ) :
    presheafExteriorPower F (n + 1) ⟶ presheafExteriorPower F n where
  app V := AddCommGrpCat.ofHom (exteriorPower.contract (presheafDual ε V) n).toAddMonoidHom
  naturality {V W} f := by
    ext x
    refine Eq.symm ?_
    calc exteriorPower.map n (F.map f).hom.toIntLinearMap
            (exteriorPower.contract (presheafDual ε V) n x)
        = exteriorPower.map n (F.map f).hom.toIntLinearMap
            (exteriorPower.contract
              (presheafDual ε W ∘ₗ (F.map f).hom.toIntLinearMap) n x) := by
          rw [presheafDual_comp]
      _ = exteriorPower.contract (presheafDual ε W) n
            (exteriorPower.map (n + 1) (F.map f).hom.toIntLinearMap x) :=
          exteriorPower.map_contract _ _ n x

/-- The Koszul differential squares to zero. -/
theorem presheafKoszulDiff_comp {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C)
    (n : ℕ) : presheafKoszulDiff ε (n + 1) ≫ presheafKoszulDiff ε n = 0 := by
  ext V x
  exact exteriorPower.contract_contract (presheafDual ε V) n x

/-- The Koszul complex of a map from a presheaf of abelian groups to the constant presheaf of
integers: the term in degree `n` is the `(n+1)`-st objectwise exterior power, and the
differential is contraction by the given map. -/
def presheafKoszul {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ :=
  ChainComplex.of (fun n => presheafExteriorPower F (n + 1))
    (fun n => presheafKoszulDiff ε (n + 1)) (fun n => presheafKoszulDiff_comp ε (n + 1))

/-- The term of the Koszul complex in degree `n` is the `(n+1)`-st exterior power. -/
theorem presheafKoszul_X {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C) (n : ℕ) :
    (presheafKoszul ε).X n = presheafExteriorPower F (n + 1) :=
  rfl

/-- The differential of the Koszul complex is the contraction by the given map. -/
theorem presheafKoszul_d {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C) (n : ℕ) :
    (presheafKoszul ε).d (n + 1) n = presheafKoszulDiff ε (n + 1) :=
  ChainComplex.of_d (fun n => presheafExteriorPower F (n + 1))
    (fun n => presheafKoszulDiff ε (n + 1)) n

/-- The augmentation of the Koszul complex: the identification of its term in degree `0`, the
first exterior power of `F`, with `F`, followed by `ε`. -/
def presheafKoszulAugmentation {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C) :
    presheafExteriorPower F 1 ⟶ constantInt.{w} C :=
  (presheafExteriorPowerOne F).hom ≫ ε

/-- The first differential of the Koszul complex followed by the augmentation vanishes. -/
theorem presheafKoszulDiff_comp_presheafKoszulAugmentation
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C) :
    presheafKoszulDiff ε 1 ≫ presheafKoszulAugmentation ε = 0 := by
  ext V x
  exact congrArg (fun k : ℤ => (ULift.up k : ULift.{w} ℤ))
    (exteriorPower.apply_oneEquiv_contract_eq_zero (presheafDual ε V) x)

end AddCommGrpCat

end
