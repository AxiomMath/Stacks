module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Basic

/-!
# The Veronese identification `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (d n)`, and its multiplicativity

Let `C` be a monoidal category and `L` an object of `C`. `Stacks.TensorPowers.natTensorPow` is the
nonnegative tensor power and `Stacks.GradedSections.powSections L n = 𝟙_ C ⟶ L ^⊗ n` the degree-`n`
piece of the section ring of Stacks Tag 01CV, multiplied by `Stacks.GradedSections.mul`. This file
builds the **Veronese identification**

`(L ^⊗ d) ^⊗ n ≅ L ^⊗ (d n)`

and proves that it carries the product of sections to the product of sections, so that it is an
isomorphism of *graded rings* and not merely a degreewise one: the section ring of `L ^⊗ d` is the
`d`-th Veronese subring `Γ_*(L)^{(d)}` of the section ring of `L`.

## Main definitions

* `Stacks.GradedSections.powPowIso` — **the Veronese identification**
  `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (d n)`, by induction on `n` out of the addition isomorphism
  `Stacks.GradedSections.powAddIso`.
* `Stacks.GradedSections.ofPowPow` — a section of `L ^⊗ (d n)` read as a section of
  `(L ^⊗ d) ^⊗ n` along that identification.

## Main results

* `Stacks.GradedSections.whiskerRight_mulMap_powAdd` — **multiplication by a section commutes with
  the addition morphism**: for `a` a section of `L ^⊗ p`,
  `(a · −) ⊗ L ^⊗ e` followed by `L ^⊗ (p + k) ⊗ L ^⊗ e ⟶ L ^⊗ (p + k + e)` is
  `L ^⊗ k ⊗ L ^⊗ e ⟶ L ^⊗ (k + e)` followed by `(a · −)`.
* `Stacks.GradedSections.mulMap_ofPowPow` — the Veronese identification turns multiplication by a
  section in the `L ^⊗ d` grading into multiplication by the same section in the `L` grading.
* `Stacks.GradedSections.ofPowPow_mul` — **the Veronese identification is multiplicative on
  sections**.
* `Stacks.GradedSections.ofPowPow_one` — it carries the unit to the unit.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the canonical
  isomorphisms `L ^⊗ n ⊗ L ^⊗ m → L ^⊗ (n + m)` and their coherence.
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) — the graded section ring.
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Stacks.TensorPowers

namespace Stacks.GradedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Veronese

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-! ### Transports against the addition morphism -/

/-- **A transport of the left factor passes through the addition morphism.** -/
@[reassoc]
theorem powCongr_whiskerRight_powAdd {L : C} {p q : ℕ} (h : p = q) (e : ℕ) :
    (powCongr L h ▷ natTensorPow L e) ≫ powAdd L q e
      = powAdd L p e ≫ powCongr L (by rw [h]) := by
  subst h
  simp

/-- **A transport of the degree being multiplied passes through multiplication by a section.** -/
@[reassoc]
theorem powCongr_comp_mulMap {L : C} {p : ℕ} (a : powSections L p) {i j : ℕ} (h : i = j) :
    powCongr L h ≫ mulMap a j = mulMap a i ≫ powCongr L (by rw [h]) := by
  subst h
  simp

/-- **A transport of the multiplier passes through multiplication by it.** -/
theorem mulMap_comp_powCongr {L : C} {p q : ℕ} (s : powSections L p) (h : p = q) (k : ℕ) :
    mulMap (s ≫ powCongr L h) k = mulMap s k ≫ powCongr L (by rw [h]) := by
  subst h
  simp

/-! ### Multiplication by a section against the addition morphism -/

/-- **Multiplication by a section commutes with the addition morphism.** For `a` a section of
`L ^⊗ p`, multiplying by `a` in degree `k` and then regrouping `L ^⊗ (p + k) ⊗ L ^⊗ e` is the
same as regrouping `L ^⊗ k ⊗ L ^⊗ e` and then multiplying by `a` in degree `k + e`. -/
@[reassoc]
theorem whiskerRight_mulMap_powAdd {L : C} {p : ℕ} (a : powSections L p) (k : ℕ) :
    ∀ e : ℕ,
      (mulMap a k ▷ natTensorPow L e) ≫ powAdd L (p + k) e
        = powAdd L k e ≫ mulMap a (k + e) ≫ powCongr L (Nat.add_assoc p k e).symm
  | 0 => by
      show (mulMap a k ▷ 𝟙_ C) ≫ (ρ_ (natTensorPow L (p + k))).hom
        = (ρ_ (natTensorPow L k)).hom ≫ mulMap a k ≫ 𝟙 _
      simp [whiskerRight_id]
  | e + 1 => by
      show (mulMap a k ▷ (natTensorPow L e ⊗ L)) ≫ powAdd L (p + k) (e + 1)
        = powAdd L k (e + 1) ≫ mulMap a (k + (e + 1)) ≫
            powCongr L (Nat.add_assoc p k (e + 1)).symm
      rw [powAdd_succ, powAdd_succ, mulMap_add_succ, ← Category.assoc,
        associator_inv_naturality_left, Category.assoc, ← comp_whiskerRight,
        whiskerRight_mulMap_powAdd a k e, comp_whiskerRight, comp_whiskerRight,
        powCongr_whiskerRight L (Nat.add_assoc p k e).symm (Nat.add_assoc p k (e + 1)).symm]
      simp only [Category.assoc]

/-! ### The Veronese identification -/

/-- **The Veronese identification `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (d n)`.** By induction on `n`: the step
splits `(L ^⊗ d) ^⊗ (n + 1)` as `(L ^⊗ d) ^⊗ n ⊗ L ^⊗ d`, rewrites the first factor by the
inductive hypothesis and closes with the addition isomorphism
`Stacks.GradedSections.powAddIso` at `(d n, d)`. -/
def powPowIso (L : C) (d : ℕ) :
    (n : ℕ) → natTensorPow (natTensorPow L d) n ≅ natTensorPow L (d * n)
  | 0 => Iso.refl _
  | n + 1 => whiskerRightIso (powPowIso L d n) (natTensorPow L d) ≪≫ powAddIso L (d * n) d

/-- The recursion defining the Veronese identification in degree zero. -/
theorem powPowIso_zero (L : C) (d : ℕ) : powPowIso L d 0 = Iso.refl _ := rfl

/-- The recursion defining the Veronese identification in a successor degree. -/
theorem powPowIso_succ (L : C) (d n : ℕ) :
    powPowIso L d (n + 1) =
      whiskerRightIso (powPowIso L d n) (natTensorPow L d) ≪≫ powAddIso L (d * n) d := rfl

/-- **A section of `L ^⊗ (d n)`, read as a section of `(L ^⊗ d) ^⊗ n`** along the Veronese
identification. This is the degree-`n` component of the graded ring map
`Γ_*(L)^{(d)} ⟶ Γ_*(L ^⊗ d)`. -/
def ofPowPow (L : C) (d n : ℕ) (a : powSections L (d * n)) : powSections (natTensorPow L d) n :=
  a ≫ (powPowIso L d n).inv

/-- `ofPowPow L d n a` is the composite of `a` with the inverse of `powPowIso L d n`. -/
theorem ofPowPow_def (L : C) (d n : ℕ) (a : powSections L (d * n)) :
    ofPowPow L d n a = a ≫ (powPowIso L d n).inv := rfl

/-- Reading a section along the Veronese identification is additive. -/
theorem ofPowPow_add [Preadditive C] (L : C) (d n : ℕ) (a b : powSections L (d * n)) :
    ofPowPow L d n (a + b) = ofPowPow L d n a + ofPowPow L d n b := by
  rw [ofPowPow_def, ofPowPow_def, ofPowPow_def, Preadditive.add_comp]

/-- Reindexing a section along an equality of degrees, as an additive map: post-composition with
`Stacks.GradedSections.powCongr`. -/
def powCongrHom [Preadditive C] (L : C) {n m : ℕ} (h : n = m) :
    powSections L n →+ powSections L m :=
  AddMonoidHom.mk' (fun s => s ≫ powCongr L h) fun _ _ => Preadditive.add_comp _ _ _ _ _ _

/-- `powCongrHom L h` sends a section `s` to its composite with `powCongr L h`. -/
@[simp]
theorem powCongrHom_apply [Preadditive C] (L : C) {n m : ℕ} (h : n = m) (s : powSections L n) :
    powCongrHom L h s = s ≫ powCongr L h := rfl

/-- Reading a section along the Veronese identification, as an additive map. This is the
degree-`n` component of `Γ_*(L)^{(d)} ⟶ Γ_*(L ^⊗ d)`. -/
def ofPowPowHom [Preadditive C] (L : C) (d n : ℕ) :
    powSections L (d * n) →+ powSections (natTensorPow L d) n :=
  AddMonoidHom.mk' (ofPowPow L d n) (ofPowPow_add L d n)

/-- `ofPowPowHom L d n` sends a section `a` to `ofPowPow L d n a`. -/
@[simp]
theorem ofPowPowHom_apply [Preadditive C] (L : C) (d n : ℕ) (a : powSections L (d * n)) :
    ofPowPowHom L d n a = ofPowPow L d n a := rfl

/-! ### Multiplicativity -/

/-- **The inductive step of `mulMap_ofPowPow`**: the identity of `mulMap_ofPowPow` in degree `m`
implies it in degree `m + 1`, with the exponents written as `n + m + 1` and `d * m + d`. -/
private theorem mulMap_ofPowPow_step (L : C) (d n m : ℕ) (a : powSections L (d * n))
    (ih : mulMap (ofPowPow L d n a) m ≫ (powPowIso L d (n + m)).hom
      = (powPowIso L d m).hom ≫ mulMap a (d * m) ≫
          powCongr L (Nat.left_distrib d n m).symm) :
    mulMap (ofPowPow L d n a) (m + 1) ≫ (powPowIso L d (n + m + 1)).hom
      = (powPowIso L d (m + 1)).hom ≫ mulMap a (d * m + d) ≫
          powCongr L (show d * n + (d * m + d) = d * (n + m) + d by
            rw [← Nat.add_assoc, ← Nat.left_distrib]) := by
  rw [mulMap_succ, powPowIso_succ, powPowIso_succ]
  simp only [Iso.trans_hom, whiskerRightIso_hom, powAddIso_hom, Category.assoc]
  rw [← Category.assoc (mulMap (ofPowPow L d n a) m ▷ natTensorPow L d),
    ← comp_whiskerRight, ih, comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc, powCongr_whiskerRight_powAdd, whiskerRight_mulMap_powAdd_assoc,
    eqToHom_trans]

/-- **The Veronese identification turns multiplication by a section in the `L ^⊗ d` grading into
multiplication by the same section in the `L` grading.** -/
theorem mulMap_ofPowPow (L : C) (d n : ℕ) (a : powSections L (d * n)) :
    ∀ m : ℕ,
      mulMap (ofPowPow L d n a) m ≫ (powPowIso L d (n + m)).hom
        = (powPowIso L d m).hom ≫ mulMap a (d * m) ≫
            powCongr L (Nat.left_distrib d n m).symm
  | 0 => by
      show ofPowPow L d n a ≫ (powPowIso L d n).hom = 𝟙 _ ≫ a ≫ 𝟙 _
      simp [ofPowPow_def]
  | m + 1 => mulMap_ofPowPow_step L d n m a (mulMap_ofPowPow L d n a m)

/-- **The Veronese identification is multiplicative on sections.** The product in the section ring
of `L ^⊗ d` of the readings of two sections is the reading of their product, after the transport
`d n + d m = d (n + m)` the grading forces. -/
theorem ofPowPow_mul (L : C) (d n m : ℕ) (a : powSections L (d * n)) (b : powSections L (d * m)) :
    mul (ofPowPow L d n a) (ofPowPow L d m b)
      = ofPowPow L d (n + m) (mul a b ≫ powCongr L (Nat.left_distrib d n m).symm) := by
  rw [mul_def, (Iso.eq_comp_inv _).2 (mulMap_ofPowPow L d n a m)]
  simp only [ofPowPow_def, mul_def, Category.assoc, Iso.inv_hom_id_assoc]

/-- **The Veronese identification carries the unit to the unit.** -/
theorem ofPowPow_one (L : C) (d : ℕ) :
    ofPowPow L d 0 (𝟙 (𝟙_ C) : powSections L (d * 0)) = 𝟙 (𝟙_ C) := by
  rw [ofPowPow_def, powPowIso_zero, Iso.refl_inv, Category.id_comp]
  rfl

end Veronese

end Stacks.GradedSections

end
