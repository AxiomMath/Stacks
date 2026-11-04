module

public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import StacksCore.Algebra.Algebra.Tower
public import StacksCore.FieldTheory.Normal.AlgClosed
import StacksCore.FieldTheory.Normal.Defs
import StacksCore.FieldTheory.SeparableClosure
import StacksCore.Tactic.StacksAttribute

/-! # Basics of Galois Theory -/

@[expose] public section

add_to_stacks 0BMH "injective" IntermediateField.fixingSubgroupEquiv
add_to_stacks 0BMM "injective" IntermediateField.fixingSubgroupEquiv
add_to_stacks 0BMH "injective" AlgEquiv.restrictScalars_injective
add_to_stacks 0BMM "injective" AlgEquiv.restrictScalars_injective
add_to_stacks 0BMH "surjective" AlgEquiv.restrictNormalHom_surjective
add_to_stacks 0BMM "surjective" AlgEquiv.restrictNormalHom_surjective
add_to_stacks 09I3 "G is the Galois group" IsGaloisGroup.fixedPoints

open IntermediateField

/-- **Stacks 0EXM** (predicate version, absolute).
If `K/F` is separable and `L/F` is a normal closure of `K/F` (in the sense of
`IsNormalClosure F K L`), then `L/F` is Galois. -/
@[stacks 0EXM "predicate version (absolute)"]
theorem IsGalois.of_isNormalClosure (F K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [Algebra.IsSeparable F K] [IsNormalClosure F K L] : IsGalois F L :=
  have := IsNormalClosure.normal (F := F) (K := K) (L := L)
  have : IsGalois F (⊤ : IntermediateField F L) :=
    IsNormalClosure.normalClosure_eq_top F K L ▸ {}
  .of_algEquiv topEquiv

/-- **Stacks 0EXM** (absolute normal closure).
The (absolute) normal closure `NormalClosure F K` of a separable extension `K/F` is
Galois over `F`. -/
@[stacks 0EXM "absolute normal closure"]
instance IsGalois.normalClosure' (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Algebra.IsSeparable F K] : IsGalois F (NormalClosure F K) :=
  .of_isNormalClosure F K (NormalClosure F K)

/-- Restricting `σ.restrictScalars F` to a normal subextension `K` gives the identity. -/
private theorem restrictNormal_restrictScalars_aux {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Normal F K] (σ : Gal(L/K)) :
    (σ.restrictScalars F).restrictNormal K = 1 := by
  ext; simp [← (algebraMap K L).injective.eq_iff]

/-- **Stacks 0BMH** (exactness at the middle term).
For a tower `F ⊂ K ⊂ L` with `K/F` normal, the kernel of the restriction map
`Gal(L/F) →* Gal(K/F)` equals the image of the scalar-restriction map
`Gal(L/K) →* Gal(L/F)`. -/
@[stacks 0BMH "exact at the middle", stacks 0BMM "exact at the middle"]
theorem AlgEquiv.ker_restrictNormalHom_eq_image_restrictScalarsHom
    (F K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L] [Normal F K] :
    (AlgEquiv.restrictNormalHom K).ker =
      (AlgEquiv.restrictScalarsHom F (S := K) (A := L)).range := by
  refine Subgroup.ext fun σ ↦ ⟨fun hσ ↦ ?_, ?_⟩
  · let σ' : Gal(L/K) :=
    { __ := σ
      commutes' x := by simpa using congr(algebraMap K L ($hσ x)) }
    exact ⟨σ', by ext; simp [σ']⟩
  · rintro ⟨τ, rfl⟩
    exact restrictNormal_restrictScalars_aux τ

/-- **Stacks 0BMH** (exactness at the middle term, lift kernel to image).
For a tower `F ⊂ K ⊂ L` with `K/F` normal, any `σ ∈ Gal(L/F)` whose restriction to `K`
is the identity is the restriction of scalars of some `τ ∈ Gal(L/K)`. -/
@[stacks 0BMH "exact at the middle -- lift kernel to image",
  stacks 0BMM "exact at the middle -- lift kernel to image"]
theorem AlgEquiv.exists_restrictScalars_eq_of_restrictNormal_eq_one
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Normal F K] {σ : Gal(L/F)} (hσ : σ.restrictNormal K = 1) :
    ∃ τ : Gal(L/K), τ.restrictScalars F = σ :=
  (Subgroup.ext_iff.mp (AlgEquiv.ker_restrictNormalHom_eq_image_restrictScalarsHom F K L) σ).mp hσ

/-- **Stacks 0BMH** (composition is trivial).
For a tower `F ⊂ K ⊂ L` with `K/F` normal, restricting an element of `Gal(L/K)` to
`K` via the scalar-restriction `Gal(L/K) → Gal(L/F)` followed by `restrictNormal K`
yields the identity. -/
@[stacks 0BMH "composition is 0", stacks 0BMM "composition is 0"]
theorem AlgEquiv.restrictNormal_restrictScalars {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Normal F K] (σ : Gal(L/K)) :
    (σ.restrictScalars F).restrictNormal K = 1 :=
  restrictNormal_restrictScalars_aux σ

/-- An element of `Gal(L/K)` fixes the intermediate field `K⟮s⟯ = adjoin K s` pointwise iff
it fixes every element of the generating set `s`. -/
@[simp high]
theorem IntermediateField.mem_fixingSubgroup_adjoin_iff
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (s : Set L) (σ : Gal(L/K)) :
    σ ∈ fixingSubgroup (adjoin K s) ↔ ∀ x ∈ s, σ x = x := by
  refine ⟨fun h x hx ↦ h ⟨x, subset_adjoin _ _ hx⟩, fun h ↦ (mem_fixingSubgroup_iff _ _).mpr
    fun x hx ↦ ?_⟩
  induction hx using adjoin_induction with
  | mem _ hx => exact h _ hx
  | algebraMap => simp
  | add => simp [*]
  | mul => simp [*]
  | inv => simp [*]

/-- For a finite Galois extension `E/F`, the cardinality of the Galois group as a `Fintype`
equals `[E : F]`. `Fintype.card`-flavored variant of `IsGalois.card_aut_eq_finrank`. -/
theorem IsGalois.fintypeCard_aut_eq_finrank (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] : Fintype.card Gal(E/F) = Module.finrank F E := by
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

/-- An element `b : K` lies in the fixed field of the cyclic subgroup `⟨σ⟩ ≤ Gal(K/F)`
generated by `σ` if and only if `σ b = b`. -/
theorem IntermediateField.mem_fixedField_zpowers_iff {F K : Type*} [Field F] [Field K] [Algebra F K]
    {σ : Gal(K/F)} {b : K} : b ∈ fixedField (.zpowers σ) ↔ σ b = b := by
  rw [mem_fixedField_iff, Subgroup.forall_mem_zpowers]
  refine ⟨fun h ↦ h 1, fun h n ↦ ?_⟩
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub_one, AlgEquiv.mul_apply, AlgEquiv.coe_inv, σ.symm_apply_eq.mpr h.symm, ih]
