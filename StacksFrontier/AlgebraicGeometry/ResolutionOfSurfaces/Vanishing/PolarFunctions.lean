module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ResidueFunctionIntegral
public import StacksFrontier.AlgebraicGeometry.NormalExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.OrderComparison

/-!
# Rational functions with poles along the closed fibre of a proper normal scheme

Let `A` be a local ring and `f : X ⟶ Spec A` universally closed, with `X` integral, locally
Noetherian and normal. Suppose that to every point `x ∈ X` is attached a rational function
`h x ∈ K(X)`, regular at `x` up to the functions near `x`: every `x` has a neighbourhood `U` with
`h x - h y ∈ 𝒪_{X, y}` for `y ∈ U`, and `h y ∈ 𝒪_{X, y}` at the codimension-one points `y` not
over the closed point. Then, under a mild hypothesis on the codimension-one points of the closed
fibre, `h x ∈ 𝒪_{X, x}` for every `x`.

This is the negativity argument behind the injectivity of `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹U, 𝒪_X)` in the
resolution of surfaces ([Stacks, Tag 0AXB]), carried out on rational functions. If some `h y`
has a pole at a codimension-one point `y` of the closed fibre, choose `y = y₀` maximizing the
ratio of the pole order of `h y` to the order of vanishing of an auxiliary function `φ ∈ A`, and
put `H x = (h x)^e φ^p` for the corresponding exponents. Then `H` is regular along the closure of
`y₀` (algebraic Hartogs), and its value `γ ∈ κ(y₀)` is nonzero; so `γ` is integral over the residue
field of `A` (the valuative criterion, `AlgebraicGeometry.isUnit_of_residue_eq`) and `H x` is a
unit wherever it is regular. At a point `x` of the closure of `y₀` through which passes a
codimension-one point `Q` not over the closed point at which `φ` vanishes, `H x` vanishes at
`Q`: a contradiction.

## Main definitions

* `AlgebraicGeometry.stalkSubring`: the local ring `𝒪_{X, x}` as a subring of the function field.
* `AlgebraicGeometry.baseRingToStalk`: the map `A ⟶ 𝒪_{X, x}`.
* `AlgebraicGeometry.baseFun`: the map `A ⟶ K(X)`.

## Main results

* `AlgebraicGeometry.forall_mem_stalkSubring_of_polar`: the statement above.

## References

* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
-/

@[expose] public noncomputable section

open CategoryTheory Order IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

section FunctionField

variable {X : Scheme.{u}} [IsIntegral X]

/-- The local ring `𝒪_{X, x}` of an integral scheme, as a subring of the function field. -/
abbrev stalkSubring (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

/-- The maps of the local rings to the function field are compatible with specialization. -/
lemma algebraMap_stalkSpecializes {x y : X} (h : y ⤳ x) (t : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.stalkSpecializes h t) =
      algebraMap (X.presheaf.stalk x) X.functionField t := by
  change X.presheaf.stalkSpecializes _ (X.presheaf.stalkSpecializes h t) =
    X.presheaf.stalkSpecializes _ t
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

/-- A specialization `y ⤳ x` gives an inclusion `𝒪_{X, x} ⊆ 𝒪_{X, y}` inside the function field. -/
lemma stalkSubring_le {x y : X} (h : y ⤳ x) : stalkSubring x ≤ stalkSubring y := by
  rintro _ ⟨t, rfl⟩
  exact ⟨_, algebraMap_stalkSpecializes h t⟩

/-- If `a - b` and `b` lie in the local ring at `y`, then so does `a`. -/
private lemma mem_stalkSubring_of_sub_mem {y : X} {a b : X.functionField}
    (hab : a - b ∈ stalkSubring y) (hb : b ∈ stalkSubring y) : a ∈ stalkSubring y := by
  simpa using (stalkSubring y).add_mem hab hb

variable [IsLocallyNoetherian X] [IsNormal X]

/-- **Algebraic Hartogs at a point.** On a normal integral locally Noetherian scheme, a rational
function lying in the local ring at every codimension-one point of a neighbourhood of `x` lies in
`𝒪_{X, x}`. -/
lemma mem_stalkSubring_of_forall_coheight_eq_one (x : X) (U : X.Opens) (hxU : x ∈ U)
    (z : X.functionField) (h : ∀ y ∈ U, coheight y = 1 → z ∈ stalkSubring y) :
    z ∈ stalkSubring x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hgen : genericPoint X ∈ W :=
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hnorm : IsIntegrallyClosed Γ(X, W) :=
    (isNormal_iff_forall_affineOpen_normal X).mp inferInstance ⟨W, hW⟩ inferInstance
  obtain ⟨s, hs⟩ := hW.exists_germ_eq_of_forall_coheight_eq_one hgen hnorm z
    fun y hyW hy1 => h y (hWU hyW) hy1
  refine ⟨X.presheaf.germ W x hxW s, ?_⟩
  rw [← hs]
  change X.presheaf.stalkSpecializes _ (X.presheaf.germ W x hxW s) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

/-- A nonzero rational function in the local ring at a codimension-one point has nonnegative
order of vanishing there. -/
lemma ord_nonneg_of_mem {y : X} (hy : coheight y = 1) {z : X.functionField}
    (hz0 : z ≠ 0) (hz : z ∈ stalkSubring y) : 0 ≤ X.ord z y := by
  obtain ⟨t, rfl⟩ := hz
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hz0 (map_zero _)
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) :=
    Stacks.Chow.krullDimLE_one_stalk_of_coheight_eq_one hy
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk y) (mem_nonZeroDivisors_of_ne_zero ht0))
  rw [Stacks.Chow.ord_algebraMap_eq_ringOrd hy ht0 hn.symm]
  exact Int.natCast_nonneg n

/-- At a codimension-one point of a normal scheme, a nonzero rational function with nonnegative
order of vanishing lies in the local ring. -/
lemma mem_of_ord_nonneg {y : X} (hy : coheight y = 1) {z : X.functionField}
    (hz0 : z ≠ 0) (h : 0 ≤ X.ord z y) : z ∈ stalkSubring y := by
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one hy
  exact exists_algebraMap_eq_of_zero_le_ord hy hz0 h

/-- At a codimension-one point, the order of vanishing of a nonzero element of the local ring is
positive exactly when that element lies in the maximal ideal. -/
lemma ord_pos_iff {y : X} (hy : coheight y = 1) {t : X.presheaf.stalk y} (ht0 : t ≠ 0) :
    0 < X.ord (algebraMap (X.presheaf.stalk y) X.functionField t) y ↔
      t ∈ maximalIdeal (X.presheaf.stalk y) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) :=
    Stacks.Chow.krullDimLE_one_stalk_of_coheight_eq_one hy
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk y) (mem_nonZeroDivisors_of_ne_zero ht0))
  rw [Stacks.Chow.ord_algebraMap_eq_ringOrd hy ht0 hn.symm, Nat.cast_pos]
  refine ⟨fun hpos => ?_, fun hm => ?_⟩
  · by_contra hm
    rw [Ring.ord_of_isUnit (notMem_maximalIdeal.mp hm)] at hn
    exact hpos.ne' (by exact_mod_cast hn)
  · by_contra hle
    have hn0 : Ring.ord (X.presheaf.stalk y) t = 0 := by
      simp [← hn, Nat.eq_zero_of_not_pos hle]
    exact (mem_maximalIdeal t).mp hm (Ideal.span_singleton_eq_top.mp
      (Ideal.Quotient.subsingleton_iff.mp (Module.length_eq_zero_iff.mp hn0)))

omit [IsNormal X] in
/-- The order of vanishing of `1` is zero. -/
lemma ord_one' (y : X) : X.ord (1 : X.functionField) y = 0 := by
  have h := Scheme.ord_mul (x := y) (one_ne_zero (α := X.functionField)) one_ne_zero
  rw [one_mul] at h
  omega

/-- The order of vanishing of a power. -/
lemma ord_pow' (y : X) {z : X.functionField} (hz : z ≠ 0) (n : ℕ) :
    X.ord (z ^ n) y = n * X.ord z y := by
  induction n with
  | zero => simp [ord_one']
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero n hz) hz, ih]
    push_cast
    ring

omit [IsNormal X] in
/-- The order of vanishing of an inverse. -/
lemma ord_inv' (y : X) {z : X.functionField} (hz : z ≠ 0) :
    X.ord z⁻¹ y = - X.ord z y := by
  have h := Scheme.ord_mul (x := y) hz (inv_ne_zero hz)
  rw [mul_inv_cancel₀ hz, ord_one'] at h
  omega

omit [IsNormal X] in
/-- The order of vanishing of a negative. -/
lemma ord_neg' (y : X) (z : X.functionField) : X.ord (-z) y = X.ord z y := by
  by_cases hz : z = 0
  · simp [hz]
  have h1 : X.ord (-1 : X.functionField) y = 0 := by
    have h := Scheme.ord_mul (x := y) (neg_ne_zero.mpr (one_ne_zero (α := X.functionField)))
      (neg_ne_zero.mpr one_ne_zero)
    rw [neg_one_mul, neg_neg, ord_one'] at h
    omega
  rw [← neg_one_mul, Scheme.ord_mul (neg_ne_zero.mpr one_ne_zero) hz, h1, zero_add]

/-- The order of vanishing of `a ^ e * b ^ p`. -/
private lemma ord_pow_mul_pow (y : X) {a b : X.functionField} (ha : a ≠ 0) (hb : b ≠ 0)
    (e p : ℕ) : X.ord (a ^ e * b ^ p) y = e * X.ord a y + p * X.ord b y := by
  rw [Scheme.ord_mul (pow_ne_zero _ ha) (pow_ne_zero _ hb), ord_pow' y ha, ord_pow' y hb]

/-- If `a` and `b` differ by an element of the local ring at a codimension-one point at which
`b` is not regular, then `a` and `b` have the same, negative, order of vanishing there. -/
lemma ord_eq_of_sub_mem {y : X} (hy : coheight y = 1) {a b : X.functionField}
    (hb : b ∉ stalkSubring y) (hab : a - b ∈ stalkSubring y) :
    a ≠ 0 ∧ X.ord a y = X.ord b y ∧ X.ord b y < 0 := by
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one hy
  have hb0 : b ≠ 0 := fun h => hb (h ▸ (stalkSubring y).zero_mem)
  have hblt : X.ord b y < 0 := by
    by_contra hle
    exact hb (mem_of_ord_nonneg hy hb0 (not_lt.mp hle))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hb (by simpa using (stalkSubring y).neg_mem hab)
  refine ⟨ha0, ?_, hblt⟩
  by_cases hr : a - b = 0
  · rw [sub_eq_zero.mp hr]
  have hr0 : 0 ≤ X.ord (a - b) y := ord_nonneg_of_mem hy hr hab
  have h1 : min (X.ord b y) (X.ord (a - b) y) ≤ X.ord a y := by
    simpa using Scheme.ord_add (x := y) (f := b) (g := a - b) (by simpa using ha0)
  have h2 : min (X.ord a y) (X.ord (-(a - b)) y) ≤ X.ord b y := by
    simpa using Scheme.ord_add (x := y) (f := a) (g := -(a - b)) (by simpa using hb0)
  rw [ord_neg'] at h2
  rw [min_eq_left (by omega)] at h1
  have : X.ord a y ≤ X.ord b y := by
    rcases min_choice (X.ord a y) (X.ord (a - b) y) with h | h <;> rw [h] at h2 <;> omega
  omega

end FunctionField

section Base

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The map from the base ring to a local ring of `X`. -/
def baseRingToStalk (x : X) : A →+* X.presheaf.stalk x :=
  (StructureSheaf.toStalk A (f x) ≫ f.stalkMap x).hom

/-- The maps from the base ring to the local rings are compatible with specialization. -/
lemma stalkSpecializes_baseRingToStalk {y x : X} (h : y ⤳ x) (a : A) :
    X.presheaf.stalkSpecializes h (baseRingToStalk f x a) = baseRingToStalk f y a := by
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply f y x h
    (StructureSheaf.toStalk A (f x) a)
  have h2 : (Spec (.of A)).presheaf.stalkSpecializes (f.base.hom.map_specializes h)
      (StructureSheaf.toStalk A (f x) a) = StructureSheaf.toStalk A (f y) a :=
    StructureSheaf.toStalk_stalkSpecializes_apply (f.base.hom.map_specializes h) a
  rw [h2] at h1
  exact h1.symm

/-- The residue map of the base ring at `y` is the composite through `baseRingToStalk`. -/
lemma residueAlgebraMap_eq_residue_baseRingToStalk (y : X) (a : A) :
    residueAlgebraMap f y a = X.residue y (baseRingToStalk f y a) := rfl

/-- The local rings at points over the closed point receive the maximal ideal of the base into
their maximal ideals. -/
lemma baseRingToStalk_mem_maximalIdeal [IsLocalRing A] {y : X} (a : A) (ha : a ∈ (f y).asIdeal) :
    baseRingToStalk f y a ∈ maximalIdeal (X.presheaf.stalk y) :=
  map_nonunit (f.stalkMap y).hom _ (not_isUnit_toStalk (f y) a ha)

variable [IsIntegral X]

/-- The image of an element of the base ring in the function field of `X`. -/
def baseFun (a : A) : X.functionField :=
  baseRingToStalk f (genericPoint X) a

/-- The image of an element of the base ring in the function field factors through every local
ring. -/
lemma algebraMap_baseRingToStalk (x : X) (a : A) :
    algebraMap (X.presheaf.stalk x) X.functionField (baseRingToStalk f x a) = baseFun f a :=
  stalkSpecializes_baseRingToStalk f ((genericPoint_spec X).specializes (Set.mem_univ x)) a

/-- The image of an element of the base ring lies in every local ring. -/
lemma baseFun_mem (x : X) (a : A) : baseFun f a ∈ stalkSubring x :=
  ⟨_, algebraMap_baseRingToStalk f x a⟩

/-- An element of the base ring with nonzero image in `K(X)` which lies in the maximal ideal of
the local ring at a codimension-one point `y` has positive order of vanishing at `y`. -/
private lemma ord_baseFun_pos [IsLocallyNoetherian X] [IsNormal X] {y : X}
    (hy : coheight y = 1) {a : A} (ha0 : baseFun f a ≠ 0)
    (ha : baseRingToStalk f y a ∈ maximalIdeal (X.presheaf.stalk y)) :
    0 < X.ord (baseFun f a) y := by
  have hne : baseRingToStalk f y a ≠ 0 := by
    intro h0
    apply ha0
    rw [← algebraMap_baseRingToStalk f y, h0, map_zero]
  rw [← algebraMap_baseRingToStalk f y]
  exact (ord_pos_iff hy hne).mpr ha

end Base

section Polar

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Spec (.of A)) [UniversallyClosed f]

/-- **Rational functions with poles along the closed fibre.** Let `h` attach to every point of
`X` a rational function, such that `h y` is regular at the codimension-one points `y` not over the
closed point, and every `x` has a neighbourhood on which `h x - h y` is regular at `y`. Let
`φ ∈ A` have nonzero image in `K(X)`, vanish at the codimension-one points of the closed fibre
(finite in number), and, for each such point `y`, vanish at a codimension-one point `Q` not over
the closed point which specializes to a point `x` of the closure of `y`. Then `h x` is regular at
`x` for every `x`. -/
theorem forall_mem_stalkSubring_of_polar
    (hTfin : {y : X | coheight y = 1 ∧ f y = closedPoint A}.Finite)
    (φ : A) (hφ0 : baseFun f φ ≠ 0)
    (hφT : ∀ y : X, coheight y = 1 → f y = closedPoint A →
      baseRingToStalk f y φ ∈ maximalIdeal (X.presheaf.stalk y))
    (hG : ∀ y : X, coheight y = 1 → f y = closedPoint A → ∃ x : X, y ⤳ x ∧
      ∃ Q : X, coheight Q = 1 ∧ f Q ≠ closedPoint A ∧ Q ⤳ x ∧
        baseRingToStalk f Q φ ∈ maximalIdeal (X.presheaf.stalk Q))
    (h : X → X.functionField)
    (hA : ∀ y : X, coheight y = 1 → f y ≠ closedPoint A → h y ∈ stalkSubring y)
    (hB : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, h x - h y ∈ stalkSubring y) :
    ∀ x : X, h x ∈ stalkSubring x := by
  classical
  set T : Set X := {y : X | coheight y = 1 ∧ f y = closedPoint A} with hTdef
  set T' : Set X := {y : X | y ∈ T ∧ h y ∉ stalkSubring y} with hT'def
  have hT'fin : T'.Finite := hTfin.subset fun y hy => hy.1
  -- away from `T'`, `h y` is regular at the codimension-one point `y`
  have hyreg : ∀ y : X, coheight y = 1 → y ∉ T' → h y ∈ stalkSubring y := by
    intro y hy1 hyT'
    by_cases hfy : f y = closedPoint A
    · by_contra hn
      exact hyT' ⟨⟨hy1, hfy⟩, hn⟩
    · exact hA y hy1 hfy
  rcases T'.eq_empty_or_nonempty with hemp | hT'ne
  · intro x
    obtain ⟨U, hxU, hU⟩ := hB x
    refine mem_stalkSubring_of_forall_coheight_eq_one x U hxU _ fun y hyU hy1 => ?_
    exact mem_stalkSubring_of_sub_mem (hU y hyU) (hyreg y hy1 (by simp [hemp]))
  exfalso
  -- the order of `φ` at the points of the closed fibre is positive
  have hφpos : ∀ y ∈ T, 0 < X.ord (baseFun f φ) y := by
    intro y hy
    exact ord_baseFun_pos f hy.1 hφ0 (hφT y hy.1 hy.2)
  -- the order of `h` at the points of `T'` is negative
  have hhneg : ∀ y ∈ T', X.ord (h y) y < 0 := fun y hy =>
    (ord_eq_of_sub_mem hy.1.1 hy.2 (by rw [sub_self]; exact (stalkSubring y).zero_mem)).2.2
  let r : X → ℚ := fun y => (-(X.ord (h y) y) : ℚ) / (X.ord (baseFun f φ) y : ℚ)
  obtain ⟨y0, hy0, hmax⟩ := Set.exists_max_image T' r hT'fin hT'ne
  set N : ℤ := -X.ord (h y0) y0 with hN
  set M : ℤ := X.ord (baseFun f φ) y0 with hM
  have hNpos : 0 < N := by have := hhneg y0 hy0; omega
  have hMpos : 0 < M := hφpos y0 hy0.1
  set e : ℕ := M.toNat with he
  set p : ℕ := N.toNat with hp
  have heM : (e : ℤ) = M := Int.toNat_of_nonneg hMpos.le
  have hpN : (p : ℤ) = N := Int.toNat_of_nonneg hNpos.le
  -- the ratio inequality
  have hratio : ∀ y ∈ T', 0 ≤ (e : ℤ) * X.ord (h y) y + p * X.ord (baseFun f φ) y := by
    intro y hy
    have hmy : (0 : ℚ) < X.ord (baseFun f φ) y := by exact_mod_cast hφpos y hy.1
    have hM' : (0 : ℚ) < M := by exact_mod_cast hMpos
    have hle := hmax y hy
    simp only [r] at hle
    rw [div_le_div_iff₀ hmy hM'] at hle
    rw [heM, hpN]
    have : (-(X.ord (h y) y) : ℚ) * M ≤ N * X.ord (baseFun f φ) y := by
      simpa [hN, hM] using hle
    have h' : -(X.ord (h y) y) * M ≤ N * X.ord (baseFun f φ) y := by exact_mod_cast this
    nlinarith
  let H : X → X.functionField := fun x => h x ^ e * (baseFun f φ) ^ p
  -- `H` is regular along the closure of `y0`
  have hreg : ∀ x : X, y0 ⤳ x → H x ∈ stalkSubring x := by
    intro x _
    obtain ⟨U, hxU, hU⟩ := hB x
    refine mem_stalkSubring_of_forall_coheight_eq_one x U hxU _ fun y hyU hy1 => ?_
    by_cases hyT' : y ∈ T'
    · by_cases hH0 : H x = 0
      · simp [hH0]
      obtain ⟨hx0, hord, -⟩ := ord_eq_of_sub_mem hy1 hyT'.2 (hU y hyU)
      refine mem_of_ord_nonneg hy1 hH0 ?_
      simp only [H]
      rw [ord_pow_mul_pow y hx0 hφ0, hord]
      exact hratio y hyT'
    · have hx : h x ∈ stalkSubring y :=
        mem_stalkSubring_of_sub_mem (hU y hyU) (hyreg y hy1 hyT')
      exact (stalkSubring y).mul_mem ((stalkSubring y).pow_mem hx _)
        ((stalkSubring y).pow_mem (baseFun_mem f y φ) _)
  -- the value of `H` at `y0` is a unit
  have hy01 : coheight y0 = 1 := hy0.1.1
  obtain ⟨hy0h0, -, -⟩ := ord_eq_of_sub_mem hy01 hy0.2
    (by rw [sub_self]; exact (stalkSubring y0).zero_mem)
  have hH0ne : H y0 ≠ 0 := mul_ne_zero (pow_ne_zero _ hy0h0) (pow_ne_zero _ hφ0)
  have hHord : X.ord (H y0) y0 = 0 := by
    simp only [H]
    rw [ord_pow_mul_pow y0 hy0h0 hφ0, heM, hpN, ← hM, hN]
    ring
  obtain ⟨u, hu⟩ := hreg y0 (specializes_refl y0)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hH0ne (by rw [← hu, map_zero])
  have huunit : IsUnit u := by
    by_contra hnu
    simpa [hu, hHord] using (ord_pos_iff hy01 hu0).mpr hnu
  set γ := X.residue y0 u with hγ
  have hγ0 : γ ≠ 0 := (huunit.map (X.residue y0).hom).ne_zero
  -- every regular value of `H` along the closure of `y0` reduces to `γ`
  have hcomp : ∀ (x : X) (hx : y0 ⤳ x) (t : X.presheaf.stalk x),
      algebraMap (X.presheaf.stalk x) X.functionField t = H x →
        X.residue y0 (X.presheaf.stalkSpecializes hx t) = γ := by
    intro x hx t ht
    obtain ⟨U, hxU, hU⟩ := hB x
    have hr : h x - h y0 ∈ stalkSubring y0 := hU y0 (hx.mem_open U.isOpen hxU)
    have hδ : ∃ d ∈ maximalIdeal (X.presheaf.stalk y0),
        algebraMap (X.presheaf.stalk y0) X.functionField d = (h x - h y0) / h y0 := by
      by_cases hr0 : h x - h y0 = 0
      · exact ⟨0, zero_mem _, by rw [hr0, zero_div, map_zero]⟩
      have hδ0 : (h x - h y0) / h y0 ≠ 0 := div_ne_zero hr0 hy0h0
      have hδpos : 0 < X.ord ((h x - h y0) / h y0) y0 := by
        rw [div_eq_mul_inv, Scheme.ord_mul hr0 (inv_ne_zero hy0h0), ord_inv' y0 hy0h0]
        have := ord_nonneg_of_mem hy01 hr0 hr
        omega
      obtain ⟨d, hd⟩ := mem_of_ord_nonneg hy01 hδ0 hδpos.le
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hδ0 (by rw [← hd, map_zero])
      refine ⟨d, (ord_pos_iff hy01 hd0).mp (by rw [hd]; exact hδpos), hd⟩
    obtain ⟨d, hdm, hd⟩ := hδ
    have hHx : H x = algebraMap (X.presheaf.stalk y0) X.functionField (u * (1 + d) ^ e) := by
      have hhx : h x = h y0 * (1 + (h x - h y0) / h y0) := by
        field_simp
        ring
      rw [map_mul, map_pow, map_add, map_one, hd, hu]
      simp only [H]
      rw [mul_right_comm, ← mul_pow, ← hhx]
    have hst : X.presheaf.stalkSpecializes hx t = u * (1 + d) ^ e := by
      apply IsFractionRing.injective (X.presheaf.stalk y0) X.functionField
      rw [algebraMap_stalkSpecializes, ht, hHx]
    have hr0 : X.residue y0 d = 0 := (IsLocalRing.residue_eq_zero_iff d).mpr hdm
    rw [hst, map_mul, map_pow, map_add, map_one, hr0, add_zero, one_pow, mul_one]
  have hγreg : ∀ (x : X) (hx : y0 ⤳ x), ∃ t : X.presheaf.stalk x,
      X.residue y0 (X.presheaf.stalkSpecializes hx t) = γ := fun x hx =>
    let ⟨t, ht⟩ := hreg x hx
    ⟨t, hcomp x hx t ht⟩
  -- the contradiction at a horizontal point through the closure of `y0`
  obtain ⟨x0, hx0, Q, hQ1, hfQ, hQx, hφQ⟩ := hG y0 hy01 hy0.1.2
  obtain ⟨t0, ht0⟩ := hreg x0 hx0
  have ht0unit : IsUnit t0 :=
    isUnit_of_residue_eq f y0 hy0.1.2 γ hγ0 hγreg hx0 (hcomp x0 hx0 t0 ht0)
  have hQunit : IsUnit (X.presheaf.stalkSpecializes hQx t0) := ht0unit.map _
  have hQne : X.presheaf.stalkSpecializes hQx t0 ≠ 0 := hQunit.ne_zero
  have hHQ : algebraMap (X.presheaf.stalk Q) X.functionField (X.presheaf.stalkSpecializes hQx t0) =
      H x0 := by rw [algebraMap_stalkSpecializes, ht0]
  have hnotpos : ¬ 0 < X.ord (H x0) Q := by
    rw [← hHQ, ord_pos_iff hQ1 hQne]
    exact fun hm => (mem_maximalIdeal _).mp hm hQunit
  apply hnotpos
  have hH0 : H x0 ≠ 0 := by
    rw [← hHQ]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hQne
  have hx00 : h x0 ≠ 0 := by
    intro h0
    apply hH0
    simp only [H, h0, zero_pow (Nat.pos_iff_ne_zero.mp (by omega : 0 < e)), zero_mul]
  obtain ⟨U, hxU, hU⟩ := hB x0
  have hQh : h x0 ∈ stalkSubring Q :=
    mem_stalkSubring_of_sub_mem (hU Q (hQx.mem_open U.isOpen hxU)) (hA Q hQ1 hfQ)
  have h1 := ord_nonneg_of_mem hQ1 hx00 hQh
  have h2 := ord_baseFun_pos f hQ1 hφ0 hφQ
  simp only [H]
  rw [ord_pow_mul_pow Q hx00 hφ0, hpN]
  nlinarith [Int.natCast_nonneg e]

end Polar

end AlgebraicGeometry

end
