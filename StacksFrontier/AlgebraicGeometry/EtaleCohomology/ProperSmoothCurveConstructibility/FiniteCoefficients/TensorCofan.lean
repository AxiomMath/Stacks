module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

/-!
# Tensoring an `ℓ`-torsion group with a ring is a direct sum of copies of it

Let `L` be an abelian group, `ℓ` a prime and `e : ι → L` a family whose image is a basis of the
`𝔽_ℓ`-vector space `L/ℓL`, recorded by its coordinate map `κ : L →+ (ι →₀ ℤ/ℓ)`. For every abelian
group `M` killed by `ℓ`, the maps `m ↦ e i ⊗ m` exhibit `L ⊗_ℤ M` as the direct sum of copies of
`M` indexed by `ι`: indeed `L ⊗_ℤ M = (L/ℓL) ⊗_ℤ M`, and `L/ℓL` is free over `𝔽_ℓ` on the `e i`.

This is the computation behind [Stacks, Tag 0GKW]: for a ring `Λ` and a sheaf `𝒢` of
`ℤ/ℓ`-modules, the sheaf of `Λ`-modules `𝒢 ⊗_ℤ Λ̲` is, as an abelian sheaf, a direct sum of copies
of `𝒢`.

## Main results

* `Stacks.EtaleCohomology.FiniteCoefficients.isColimitTensorCofan`: the cofan
  `(L ⊗_ℤ M, m ↦ e i ⊗ m)` is a colimit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe w

namespace Stacks.EtaleCohomology.FiniteCoefficients

variable {L : Type w} [AddCommGroup L] {M : Type w} [AddCommGroup M] (ℓ : ℕ) [Fact ℓ.Prime]
  {ι : Type w} (e : ι → L) (κ : L →+ (ι →₀ ZMod ℓ))

/-- `k.val • t` is additive in `k : ℤ/ℓ` on elements `t` killed by `ℓ`. -/
theorem val_add_nsmul {T : Type*} [AddCommGroup T] {t : T} (ht : ℓ • t = 0) (k k' : ZMod ℓ) :
    (k + k').val • t = k.val • t + k'.val • t := by
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have : NeZero ℓ := ⟨hℓ.ne'⟩
  rw [ZMod.val_add, ← add_nsmul]
  conv_rhs => rw [← Nat.mod_add_div (k.val + k'.val) ℓ]
  rw [add_nsmul, mul_nsmul, ht, nsmul_zero, add_zero]

/-- The cofan `(L ⊗_ℤ M, m ↦ e i ⊗ m)` over the constant family `M`. -/
abbrev tensorCofan [Module ℤ L] [Module ℤ M] :
    Cofan (fun _ : ι ↦ AddCommGrpCat.of M) :=
  Cofan.mk (AddCommGrpCat.of (L ⊗[ℤ] M)) fun i ↦
    AddCommGrpCat.ofHom
      { toFun := fun m ↦ e i ⊗ₜ m
        map_zero' := tmul_zero _ _
        map_add' := tmul_add _ }

variable {ℓ e κ}

/-- **`L ⊗_ℤ M` is the direct sum of copies of `M` along the `e i`**, for `M` killed by `ℓ` and
`e` a family whose image is a basis of `L/ℓL` with coordinates `κ`: every `x : L` is congruent to
`∑ (κ x)ᵢ eᵢ` modulo `ℓ` (`hspan`), and `κ (e i)` is the `i`-th basis vector (`hκ`). -/
def isColimitTensorCofan [Module ℤ L] [Module ℤ M] (hM : ∀ m : M, ℓ • m = 0)
    (hspan : ∀ x : L, ∃ y : L, x = ((κ x).sum fun i k ↦ k.val • e i) + ℓ • y)
    (hκ : ∀ i, κ (e i) = Finsupp.single i 1) :
    IsColimit (tensorCofan e (L := L) (M := M)) := by
  obtain rfl : ‹Module ℤ L› = AddCommGroup.toIntModule L := Subsingleton.elim _ _
  obtain rfl : ‹Module ℤ M› = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  have hℓ1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  haveI : Fact (1 < ℓ) := ⟨hℓ1⟩
  have htors : ∀ (T : Type w) [AddCommGroup T] (g : M →+ T) (m : M), ℓ • g m = 0 := fun T _ g m ↦ by
    rw [← map_nsmul, hM, map_zero]
  let B (s : Cofan fun _ : ι ↦ AddCommGrpCat.of M) : L →+ M →+ s.pt :=
    AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk'
      (fun m ↦ (κ x).sum fun i k ↦ k.val • (s.inj i).hom m)
      (fun m m' ↦ by
        rw [← Finsupp.sum_add]
        refine Finsupp.sum_congr fun i _ ↦ ?_
        rw [map_add, nsmul_add]))
      (fun x x' ↦ by
        ext m
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add]
        exact Finsupp.sum_add_index' (fun _ ↦ by simp) fun i k k' ↦
          val_add_nsmul ℓ (htors _ (s.inj i).hom m) k k')
  refine mkCofanColimit _
    (fun s ↦ AddCommGrpCat.ofHom (TensorProduct.liftAddHom (B s) fun c x m ↦ by
      rw [map_zsmul, AddMonoidHom.coe_smul, Pi.smul_apply, map_zsmul]))
    (fun s i ↦ ?_) (fun s φ hφ ↦ ?_)
  · ext m
    change (κ (e i)).sum (fun j k ↦ k.val • (s.inj j).hom m) = (s.inj i).hom m
    rw [hκ, Finsupp.sum_single_index (by simp), ZMod.val_one, one_nsmul]
  · ext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [ha, hb]
    | tmul x m =>
      obtain ⟨y, hy⟩ := hspan x
      have hm' : (ℓ • y) ⊗ₜ[ℤ] m = 0 := by
        rw [← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.smul_tmul, Nat.cast_smul_eq_nsmul, hM,
          tmul_zero]
      change φ.hom (x ⊗ₜ m) = (κ x).sum fun i k ↦ k.val • (s.inj i).hom m
      have hx : φ.hom (x ⊗ₜ m) =
          φ.hom ((((κ x).sum fun i k ↦ k.val • e i) + ℓ • y) ⊗ₜ m) := by rw [← hy]
      rw [hx, add_tmul, hm', add_zero, Finsupp.sum, TensorProduct.sum_tmul, map_sum, Finsupp.sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hn : ∀ n : ℕ, φ.hom ((n • e i) ⊗ₜ[ℤ] m) = n • φ.hom (e i ⊗ₜ[ℤ] m) := fun n ↦ by
        induction n with
        | zero => simp
        | succ n ih => rw [succ_nsmul, add_tmul, map_add, ih, succ_nsmul]
      rw [hn, ← hφ i]
      rfl

section Basis

variable {V : Type w} [AddCommGroup V] [Module (ZMod ℓ) V]

/-- The cofan exhibiting an `𝔽_ℓ`-vector space with basis `b` as a direct sum of copies of
`ℤ/ℓ`: the `i`-th summand is `k ↦ k • b i`. -/
abbrev zmodBasisCofan (b : Module.Basis ι (ZMod ℓ) V) :
    Cofan fun _ : ι ↦ AddCommGrpCat.of (ULift.{w} (ZMod ℓ)) :=
  Cofan.mk (AddCommGrpCat.of V) fun i ↦ AddCommGrpCat.ofHom
    { toFun := fun k ↦ k.down.val • b i
      map_zero' := by simp
      map_add' := fun k k' ↦ val_add_nsmul ℓ (by
        rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]) _ _ }

/-- **An `𝔽_ℓ`-vector space is the direct sum of copies of `ℤ/ℓ` along a basis.** -/
def isColimitZModBasisCofan (b : Module.Basis ι (ZMod ℓ) V) :
    IsColimit (zmodBasisCofan b) := by
  have hval : ∀ (k : ZMod ℓ) (v : V), k.val • v = k • v := fun k v ↦ by
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_zmod_val]
  refine mkCofanColimit _
    (fun s ↦ AddCommGrpCat.ofHom ((Finsupp.liftAddHom fun i ↦
      (s.inj i).hom.comp (AddEquiv.ulift (α := ZMod ℓ)).symm.toAddMonoidHom).comp
        b.repr.toLinearMap.toAddMonoidHom)) (fun s i ↦ ?_) (fun s m hm ↦ ?_)
  · ext k
    change (Finsupp.liftAddHom fun i ↦ (s.inj i).hom.comp
      (AddEquiv.ulift (α := ZMod ℓ)).symm.toAddMonoidHom) (b.repr (k.down.val • b i)) =
        (s.inj i).hom k
    rw [hval, map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.liftAddHom_apply_single]
    rfl
  · ext v
    change m.hom v = (Finsupp.liftAddHom fun i ↦ (s.inj i).hom.comp
      (AddEquiv.ulift (α := ZMod ℓ)).symm.toAddMonoidHom) (b.repr v)
    conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, map_sum, Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hval, ← hm i]
    rfl

end Basis

section Quotient

variable (Λ : Type w) [CommRing Λ] (ℓ : ℕ) [Fact ℓ.Prime]

omit [Fact ℓ.Prime] in
/-- The quotient `Λ/ℓΛ` is annihilated by `ℓ`. -/
theorem nsmul_quotient_span (x : Λ ⧸ Ideal.span {(ℓ : Λ)}) : ℓ • x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_nsmul, nsmul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- `Λ/ℓΛ` as an `𝔽_ℓ`-vector space. -/
abbrev quotientZModModule : Module (ZMod ℓ) (Λ ⧸ Ideal.span {(ℓ : Λ)}) :=
  AddCommGroup.zmodModule (nsmul_quotient_span Λ ℓ)

attribute [local instance] quotientZModModule

/-- The index set of a basis of the `𝔽_ℓ`-vector space `Λ/ℓΛ`. -/
abbrev quotientBasisIndex : Type w :=
  Module.Free.ChooseBasisIndex (ZMod ℓ) (Λ ⧸ Ideal.span {(ℓ : Λ)})

/-- A basis of the `𝔽_ℓ`-vector space `Λ/ℓΛ`. -/
abbrev quotientBasis : Module.Basis (quotientBasisIndex Λ ℓ) (ZMod ℓ) (Λ ⧸ Ideal.span {(ℓ : Λ)}) :=
  Module.Free.chooseBasis (ZMod ℓ) (Λ ⧸ Ideal.span {(ℓ : Λ)})

/-- Lifts to `Λ` of the basis `quotientBasis Λ ℓ` of `Λ/ℓΛ`. -/
def quotientBasisLift (i : quotientBasisIndex Λ ℓ) : Λ :=
  (Ideal.Quotient.mk_surjective (quotientBasis Λ ℓ i)).choose

/-- The image in `Λ/ℓΛ` of `quotientBasisLift Λ ℓ i` is the basis vector `quotientBasis Λ ℓ i`. -/
theorem mk_quotientBasisLift (i : quotientBasisIndex Λ ℓ) :
    Ideal.Quotient.mk _ (quotientBasisLift Λ ℓ i) = quotientBasis Λ ℓ i :=
  (Ideal.Quotient.mk_surjective (quotientBasis Λ ℓ i)).choose_spec

/-- The coordinates in the basis `quotientBasis Λ ℓ` of the image in `Λ/ℓΛ`. -/
def quotientCoord : Λ →+ (quotientBasisIndex Λ ℓ →₀ ZMod ℓ) :=
  (quotientBasis Λ ℓ).repr.toLinearMap.toAddMonoidHom.comp
    (Ideal.Quotient.mk (Ideal.span {(ℓ : Λ)})).toAddMonoidHom

/-- The coordinates of `quotientBasisLift Λ ℓ i` are those of the `i`-th basis vector. -/
theorem quotientCoord_quotientBasisLift (i : quotientBasisIndex Λ ℓ) :
    quotientCoord Λ ℓ (quotientBasisLift Λ ℓ i) = Finsupp.single i 1 := by
  show (quotientBasis Λ ℓ).repr (Ideal.Quotient.mk _ (quotientBasisLift Λ ℓ i)) = _
  rw [mk_quotientBasisLift, Module.Basis.repr_self]

/-- Every `x : Λ` is, modulo `ℓΛ`, the combination of the lifts `quotientBasisLift Λ ℓ i` with
coefficients its coordinates `quotientCoord Λ ℓ x`. -/
theorem exists_eq_sum_quotientBasisLift (x : Λ) : ∃ y : Λ,
    x = ((quotientCoord Λ ℓ x).sum fun i k ↦ k.val • quotientBasisLift Λ ℓ i) + ℓ • y := by
  have hmk : Ideal.Quotient.mk (Ideal.span {(ℓ : Λ)})
      (x - (quotientCoord Λ ℓ x).sum fun i k ↦ k.val • quotientBasisLift Λ ℓ i) = 0 := by
    rw [map_sub, Finsupp.sum, map_sum]
    have : ∀ i, Ideal.Quotient.mk (Ideal.span {(ℓ : Λ)})
        ((quotientCoord Λ ℓ x i).val • quotientBasisLift Λ ℓ i) =
          quotientCoord Λ ℓ x i • quotientBasis Λ ℓ i := fun i ↦ by
      rw [map_nsmul, mk_quotientBasisLift, ← Nat.cast_smul_eq_nsmul (ZMod ℓ),
        ZMod.natCast_zmod_val]
    simp only [this]
    rw [sub_eq_zero]
    conv_lhs => rw [← (quotientBasis Λ ℓ).linearCombination_repr (Ideal.Quotient.mk _ x)]
    rfl
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  refine ⟨y, ?_⟩
  rw [nsmul_eq_mul, mul_comm, hy, add_sub_cancel]

end Quotient

end Stacks.EtaleCohomology.FiniteCoefficients

end
