module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.DegreeOneNorm

/-!
# The norm maps `N_{L/K} : K^M_*(L) ⟶ K^M_*(K)` of a finite extension of fields

Let `L / K` be a finite extension of fields. This file constructs a norm map on Milnor K-theory

`N_{L/K} : K^M_i(L) ⟶ K^M_i(K)`  in every degree `i`  (`Stacks.Chow.milnorKNorm`),

the input to the tame symbol of a one-dimensional Noetherian local domain in Remark 0EAY (the
tame symbols of the discrete valuation rings of the normalization, pushed down to the residue
field of the base by the norm maps of the residue field extensions).

## Construction

Through a chosen tower of simple extensions, by strong induction on `[L : K]`
(`Stacks.Chow.milnorKNormAux`): if some `a ∈ L` is not in `K`, then
`N_{L/K} = N_{K(a)/K} ∘ N_{L/K(a)}`, where `[L : K(a)] < [L : K]` and `N_{K(a)/K}` is the norm of
the simple extension `K(a) ≅ K[X] ⧸ minpoly(a)` built from Milnor's exact sequence
(`Stacks.Chow.simpleMilnorNorm`); otherwise `K → L` is an isomorphism and `N_{L/K}` is its inverse.
The remark uses the norm only to define the extended tame symbol, so no independence of the tower
(Kato's theorem) is claimed or needed.

## Properties

Each property is checked on a simple step and on the trivial extension, and is stable under
composition along a tower (`Stacks.Chow.IsMilnorNorm`):

* `N_{L/K}` preserves the degree (`Stacks.Chow.milnorKNormRing_mem_milnorKGrading`);
* in degree zero it is multiplication by `[L : K]` (`Stacks.Chow.milnorKNormRing_one`);
* in degree one it is the field norm (`Stacks.Chow.milnorKNormRing_milnorKSymbol`);
* the projection formulas `N(ι(z) x) = z N(x)` and `N(x ι(z)) = N(x) z`
  (`Stacks.Chow.milnorKNormRing_map_mul`, `Stacks.Chow.milnorKNormRing_mul_map`);
* for an isomorphism `K ≅ L` it is the induced isomorphism
  (`Stacks.Chow.milnorKNormRing_of_bijective`).

## Main definitions

* `Stacks.Chow.milnorKNormAdjoinSimple` — the norm of `K ⊂ K(a)`.
* `Stacks.Chow.milnorKNormRing` — `N_{L/K}` on the whole Milnor K-ring.
* `Stacks.Chow.milnorKNorm` — `N_{L/K} : K^M_i(L) ⟶ K^M_i(K)`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* H. Bass, J. Tate, *The Milnor ring of a global field*, LNM 342 (1973), §I.5.
* K. Kato, *A generalization of local class field theory by using K-groups II*, §1.7.
-/

@[expose] public noncomputable section

open Polynomial Module IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

/-! ### The properties of a norm map -/

/-- The properties of a norm map `K^M_*(L) ⟶ K^M_*(K)`: it preserves the degree, is
multiplication by `[L : K]` in degree zero, the field norm in degree one, and satisfies the
projection formulas. -/
structure IsMilnorNorm (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : MilnorKRing L →+ MilnorKRing K) : Prop where
  mem_grading : ∀ {i : ℕ} {x : MilnorKRing L}, x ∈ milnorKGrading L i → N x ∈ milnorKGrading K i
  map_one : N 1 = (finrank K L : ℤ) • (1 : MilnorKRing K)
  map_symbol : ∀ b : Lˣ,
    N (milnorKSymbol L b) = milnorKSymbol K (Units.map (Algebra.norm K : L →* K) b)
  map_mul_left : ∀ (z : MilnorKRing K) (x : MilnorKRing L),
    N (milnorKRingMap (algebraMap K L) z * x) = z * N x
  map_mul_right : ∀ (x : MilnorKRing L) (z : MilnorKRing K),
    N (x * milnorKRingMap (algebraMap K L) z) = N x * z

/-- **Norm maps compose along a tower.** -/
theorem IsMilnorNorm.comp {K M L : Type u} [Field K] [Field M] [Field L] [Algebra K M]
    [Algebra M L] [Algebra K L] [IsScalarTower K M L] [FiniteDimensional K M]
    [FiniteDimensional M L] {N₁ : MilnorKRing M →+ MilnorKRing K}
    {N₂ : MilnorKRing L →+ MilnorKRing M} (h₁ : IsMilnorNorm K M N₁) (h₂ : IsMilnorNorm M L N₂) :
    IsMilnorNorm K L (N₁.comp N₂) where
  mem_grading hx := h₁.mem_grading (h₂.mem_grading hx)
  map_one := by
    rw [AddMonoidHom.comp_apply, h₂.map_one, map_zsmul, h₁.map_one, smul_smul,
      ← finrank_mul_finrank K M L]
    push_cast
    rw [mul_comm]
  map_symbol b := by
    rw [AddMonoidHom.comp_apply, h₂.map_symbol, h₁.map_symbol]
    congr 1
    exact Units.ext (by simp [Algebra.norm_norm])
  map_mul_left z x := by
    rw [IsScalarTower.algebraMap_eq K M L, milnorKRingMap_comp, RingHom.comp_apply,
      AddMonoidHom.comp_apply, h₂.map_mul_left, h₁.map_mul_left, AddMonoidHom.comp_apply]
  map_mul_right x z := by
    rw [IsScalarTower.algebraMap_eq K M L, milnorKRingMap_comp, RingHom.comp_apply,
      AddMonoidHom.comp_apply, h₂.map_mul_right, h₁.map_mul_right, AddMonoidHom.comp_apply]

/-! ### The trivial extension -/

/-- **An isomorphism `K ≅ L` gives a norm map: the induced isomorphism of Milnor K-rings.** -/
theorem isMilnorNorm_of_bijective {K L : Type u} [Field K] [Field L] [Algebra K L]
    (hb : Function.Bijective (algebraMap K L)) :
    IsMilnorNorm K L (milnorKRingMap
      ((RingEquiv.ofBijective (algebraMap K L) hb).symm : L →+* K)).toAddMonoidHom := by
  have hinv : ((RingEquiv.ofBijective (algebraMap K L) hb).symm : L →+* K).comp
      (algebraMap K L) = RingHom.id K :=
    RingHom.ext fun c ↦ (RingEquiv.ofBijective (algebraMap K L) hb).symm_apply_apply c
  have hrank : finrank K L = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K L) hb).toLinearEquiv.finrank_eq, finrank_self]
  refine ⟨fun hx ↦ milnorKRingMap_mem_milnorKGrading _ hx, ?_, fun b ↦ ?_, fun z x ↦ ?_,
    fun x z ↦ ?_⟩
  · rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, map_one, hrank, Nat.cast_one,
      one_smul]
  · rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, milnorKRingMap_milnorKSymbol]
    congr 1
    refine Units.ext ?_
    obtain ⟨c, hc⟩ := hb.2 (b : L)
    simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.coe_coe, ← hc,
      Algebra.norm_algebraMap, hrank, pow_one]
    exact (RingEquiv.ofBijective (algebraMap K L) hb).symm_apply_apply c
  · change milnorKRingMap _ (milnorKRingMap _ z * x) = z * milnorKRingMap _ x
    rw [map_mul, milnorKRingMap_comp_apply, hinv, milnorKRingMap_id_apply]
  · change milnorKRingMap _ (x * milnorKRingMap _ z) = milnorKRingMap _ x * z
    rw [map_mul, milnorKRingMap_comp_apply, hinv, milnorKRingMap_id_apply]

/-! ### The simple step `K ⊂ K(a)` -/

section Simple

variable (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]

/-- The minimal polynomial of an integral element, as a monic irreducible of its degree. -/
def minpolyOfDegree {a : L} (h : IsIntegral K a) :
    MonicIrreducibleOfDegree K (minpoly K a).natDegree :=
  ⟨minpoly K a, minpoly.monic h, minpoly.irreducible h, rfl⟩

/-- `K(a) ≅ K[X] ⧸ minpoly(a)`. -/
def adjoinSimpleEquivQuot {a : L} (h : IsIntegral K a) :
    K⟮a⟯ ≃ₐ[K] (Polynomial K ⧸ Ideal.span {poly (minpolyOfDegree K h)}) :=
  (IntermediateField.adjoinRootEquivAdjoin K h).symm

/-- **The norm map of a simple extension `K ⊂ K(a)`**: the norm of `K[X] ⧸ minpoly(a)` read
through `K(a) ≅ K[X] ⧸ minpoly(a)`. -/
def milnorKNormAdjoinSimple {a : L} (h : IsIntegral K a) : MilnorKRing K⟮a⟯ →+ MilnorKRing K :=
  (simpleMilnorNorm (minpolyOfDegree K h)).comp
    (milnorKRingMap (adjoinSimpleEquivQuot K h).toRingEquiv.toRingHom).toAddMonoidHom

/-- The isomorphism `K(a) ≅ K[X] ⧸ minpoly(a)` commutes with the structure maps from `K`. -/
theorem algebraMap_comp_adjoinSimpleEquivQuot {a : L} (h : IsIntegral K a) :
    (adjoinSimpleEquivQuot K h).toRingEquiv.toRingHom.comp (algebraMap K K⟮a⟯) =
      algebraMap K (Polynomial K ⧸ Ideal.span {poly (minpolyOfDegree K h)}) :=
  RingHom.ext fun c ↦ (adjoinSimpleEquivQuot K h).commutes c

/-- Unfolding `milnorKNormAdjoinSimple`: read through `K(a) ≅ K[X] ⧸ minpoly(a)`. -/
private theorem milnorKNormAdjoinSimple_apply {a : L} (h : IsIntegral K a) (x : MilnorKRing K⟮a⟯) :
    milnorKNormAdjoinSimple K h x = simpleMilnorNorm (minpolyOfDegree K h)
      (milnorKRingMap (adjoinSimpleEquivQuot K h).toRingEquiv.toRingHom x) :=
  rfl

/-- **The norm map of a simple extension is a norm map.** -/
theorem isMilnorNorm_milnorKNormAdjoinSimple {a : L} (h : IsIntegral K a) :
    IsMilnorNorm K K⟮a⟯ (milnorKNormAdjoinSimple K h) := by
  refine ⟨fun hx ↦ ?_, ?_, fun b ↦ ?_, fun z x ↦ ?_, fun x z ↦ ?_⟩
  · rw [milnorKNormAdjoinSimple_apply]
    exact simpleMilnorNorm_mem_milnorKGrading _ (milnorKRingMap_mem_milnorKGrading _ hx)
  · rw [milnorKNormAdjoinSimple_apply, map_one, simpleMilnorNorm_one,
      IntermediateField.adjoin.finrank h]
  · rw [milnorKNormAdjoinSimple_apply, milnorKRingMap_milnorKSymbol,
      simpleMilnorNorm_milnorKSymbol]
    congr 1
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    exact Algebra.norm_eq_of_algEquiv (adjoinSimpleEquivQuot K h) (b : K⟮a⟯)
  · rw [milnorKNormAdjoinSimple_apply, map_mul, milnorKRingMap_comp_apply,
      algebraMap_comp_adjoinSimpleEquivQuot, simpleMilnorNorm_map_mul,
      milnorKNormAdjoinSimple_apply]
  · rw [milnorKNormAdjoinSimple_apply, map_mul, milnorKRingMap_comp_apply,
      algebraMap_comp_adjoinSimpleEquivQuot, simpleMilnorNorm_mul_map,
      milnorKNormAdjoinSimple_apply]

end Simple

/-! ### The tower -/

/-- Adjoining an element outside `K` lowers the degree of the rest of the extension. -/
theorem finrank_adjoin_simple_lt {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {a : L} (ha : a ∉ Set.range (algebraMap K L)) :
    finrank K⟮a⟯ L < finrank K L := by
  have hne : K⟮a⟯ ≠ ⊥ := fun hbot ↦
    ha (IntermediateField.mem_bot.mp (adjoin_simple_eq_bot_iff.mp hbot))
  have h1 : finrank K K⟮a⟯ ≠ 1 := fun h ↦ hne (IntermediateField.finrank_eq_one_iff.mp h)
  have h0 : 0 < finrank K K⟮a⟯ := finrank_pos
  have h0' : 0 < finrank K⟮a⟯ L := finrank_pos
  rw [← finrank_mul_finrank K K⟮a⟯ L]
  exact lt_mul_left h0' (by omega)

/-- If every element of `L` comes from `K`, then `K → L` is bijective. -/
theorem bijective_algebraMap_of_forall {K L : Type u} [Field K] [Field L] [Algebra K L]
    (h : ¬∃ a : L, a ∉ Set.range (algebraMap K L)) : Function.Bijective (algebraMap K L) :=
  ⟨(algebraMap K L).injective, fun b ↦ by
    by_contra hb
    exact h ⟨b, fun ⟨c, hc⟩ ↦ hb ⟨c, hc⟩⟩⟩

open scoped Classical in
/-- **The norm map along a chosen tower of simple extensions**, by strong induction on the
degree `n = [L : K]`. -/
def milnorKNormAux (n : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (_hn : finrank K L = n) : MilnorKRing L →+ MilnorKRing K :=
  if h : ∃ a : L, a ∉ Set.range (algebraMap K L) then
    (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) h.choose)).comp
      (milnorKNormAux (finrank K⟮h.choose⟯ L) K⟮h.choose⟯ L rfl)
  else
    (milnorKRingMap ((RingEquiv.ofBijective (algebraMap K L)
      (bijective_algebraMap_of_forall h)).symm : L →+* K)).toAddMonoidHom
termination_by n
decreasing_by exact _hn ▸ finrank_adjoin_simple_lt h.choose_spec

/-- **The norm map along a chosen tower is a norm map.** -/
theorem isMilnorNorm_milnorKNormAux : ∀ (n : ℕ) (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (hn : finrank K L = n),
    IsMilnorNorm K L (milnorKNormAux n K L hn) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ hn
  rw [milnorKNormAux]
  by_cases h : ∃ a : L, a ∉ Set.range (algebraMap K L)
  · rw [dite_eq_left h]
    exact (isMilnorNorm_milnorKNormAdjoinSimple K _).comp
      (ih _ (hn ▸ finrank_adjoin_simple_lt h.choose_spec) _ _ rfl)
  · rw [dite_eq_right h]
    exact isMilnorNorm_of_bijective _

/-! ### The norm map -/

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The norm map `N_{L/K} : K^M_*(L) ⟶ K^M_*(K)` of a finite extension of fields**, on the
whole Milnor K-ring. -/
def milnorKNormRing : MilnorKRing L →+ MilnorKRing K :=
  milnorKNormAux (finrank K L) K L rfl

/-- `milnorKNormRing K L` is a norm map. -/
theorem isMilnorNorm_milnorKNormRing : IsMilnorNorm K L (milnorKNormRing K L) :=
  isMilnorNorm_milnorKNormAux _ K L rfl

variable {K L}

/-- **`N_{L/K}` preserves the degree.** -/
theorem milnorKNormRing_mem_milnorKGrading {i : ℕ} {x : MilnorKRing L}
    (hx : x ∈ milnorKGrading L i) : milnorKNormRing K L x ∈ milnorKGrading K i :=
  (isMilnorNorm_milnorKNormRing K L).mem_grading hx

variable (K L) in
/-- **Stacks 0EAY's norm maps: `N_{L/K} : K^M_i(L) ⟶ K^M_i(K)` for a finite extension `L / K`, in
every degree.** -/
def milnorKNorm (i : ℕ) : MilnorKTheory L i →+ MilnorKTheory K i where
  toFun x := ⟨milnorKNormRing K L x, milnorKNormRing_mem_milnorKGrading x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The norm map in degree `i` is the restriction of `milnorKNormRing K L`. -/
@[simp]
theorem coe_milnorKNorm (i : ℕ) (x : MilnorKTheory L i) :
    (milnorKNorm K L i x : MilnorKRing K) = milnorKNormRing K L (x : MilnorKRing L) :=
  rfl

/-- **Degree zero: `N_{L/K}(1) = [L : K]`.** -/
theorem milnorKNormRing_one :
    milnorKNormRing K L 1 = (finrank K L : ℤ) • (1 : MilnorKRing K) :=
  (isMilnorNorm_milnorKNormRing K L).map_one

/-- **Degree one: `N_{L/K} {b} = {N_{L/K}(b)}`.** -/
theorem milnorKNormRing_milnorKSymbol (b : Lˣ) :
    milnorKNormRing K L (milnorKSymbol L b) =
      milnorKSymbol K (Units.map (Algebra.norm K : L →* K) b) :=
  (isMilnorNorm_milnorKNormRing K L).map_symbol b

/-- **The projection formula `N_{L/K}(ι(z) x) = z N_{L/K}(x)`.** -/
theorem milnorKNormRing_map_mul (z : MilnorKRing K) (x : MilnorKRing L) :
    milnorKNormRing K L (milnorKRingMap (algebraMap K L) z * x) = z * milnorKNormRing K L x :=
  (isMilnorNorm_milnorKNormRing K L).map_mul_left z x

/-- **The projection formula `N_{L/K}(x ι(z)) = N_{L/K}(x) z`.** -/
theorem milnorKNormRing_mul_map (x : MilnorKRing L) (z : MilnorKRing K) :
    milnorKNormRing K L (x * milnorKRingMap (algebraMap K L) z) = milnorKNormRing K L x * z :=
  (isMilnorNorm_milnorKNormRing K L).map_mul_right x z

/-- **`N_{L/K}(ι(z)) = [L : K] z`**, the projection formula at `x = 1`. -/
theorem milnorKNormRing_milnorKRingMap (z : MilnorKRing K) :
    milnorKNormRing K L (milnorKRingMap (algebraMap K L) z) = (finrank K L : ℤ) • z := by
  rw [← mul_one (milnorKRingMap (algebraMap K L) z), milnorKNormRing_map_mul, milnorKNormRing_one,
    mul_smul_comm, mul_one]

/-- **For an isomorphism `K ≅ L`, the norm map is the induced isomorphism.** -/
theorem milnorKNormRing_of_bijective (h : Function.Bijective (algebraMap K L))
    (x : MilnorKRing L) :
    milnorKNormRing K L x =
      milnorKRingMap ((RingEquiv.ofBijective (algebraMap K L) h).symm : L →+* K) x := by
  have hno : ¬∃ a : L, a ∉ Set.range (algebraMap K L) := fun ⟨a, ha⟩ ↦ ha (h.2 a)
  rw [milnorKNormRing, milnorKNormAux, dite_eq_right hno]
  rfl

end Stacks.Chow

end
