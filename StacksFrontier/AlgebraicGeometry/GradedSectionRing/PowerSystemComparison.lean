module

public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Basic

/-!
# Veronese power systems, and the comparison of two systems of tensor powers

Let `C` be a monoidal category. A `Stacks.Monoidal.PowerSystem C` is a family `obj n` of
candidate tensor powers of an object `gen`, together with `obj 0 ≅ 𝟙_ C` and the successor
comparisons `obj n ⊗ gen ≅ obj (n + 1)`, which determine multiplication isomorphisms
`μ_{p,q} : obj p ⊗ obj q ≅ obj (p + q)`.

The *`a`-th Veronese system* of `S` is the power system whose generator is `obj a`
and whose `n`-th power is `obj (a * n)`. For the tensor powers of an invertible sheaf `L` it
is the system of tensor powers of `L^{⊗ a}`, with `(L^{⊗ a})^{⊗ n}` presented as `L^{⊗ an}`
rather than as an iterated tensor product.

The *comparison* of two power systems `S` and `T` along an isomorphism
`β : S.gen ≅ T.gen` of their generators: the isomorphisms `S.obj n ≅ T.obj n` obtained by
tensoring `β` with itself `n` times. Applied to two Veronese systems, it is the `m`-th tensor
power `β^{⊗ m} : L^{⊗ am} ≅ (L')^{⊗ a'm}` of an isomorphism `β : L^{⊗ a} ≅ (L')^{⊗ a'}`.

## Main definitions

* `Stacks.Monoidal.PowerSystem.veronese`: the `a`-th Veronese system.
* `Stacks.Monoidal.PowerSystem.compare`: the comparison isomorphisms `S.obj n ≅ T.obj n`
  induced by an isomorphism of the generators.

## Main results

* `Stacks.Monoidal.PowerSystem.veronese_mulIso`: the multiplication isomorphisms of the
  Veronese system are those of the original system, with the exponents multiplied by `a`.
* `Stacks.Monoidal.PowerSystem.compare_refl`: the comparison of a system with itself along
  the identity is the identity.
* `Stacks.Monoidal.PowerSystem.compare_mul`: the comparison isomorphisms are multiplicative,
  that is, they commute with the multiplication isomorphisms of the two systems.
* `Stacks.Monoidal.PowerSystem.compare_veronese_veronese`: the comparison of the `ak`-th and
  `a'k`-th Veronese systems along the degree-`k` comparison of the `a`-th and `a'`-th ones is
  the degree-`km` comparison of the latter. In the language of tensor powers:
  `(β^{⊗ k})^{⊗ m} = β^{⊗ km}`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace Stacks.Monoidal

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace PowerSystem

/-! ### Veronese systems -/

/-- The **`a`-th Veronese system** of a power system `S`: the generator is the `a`-th power
`S.obj a`, and the `n`-th power of that generator is presented as `S.obj (a * n)`. -/
@[reducible]
def veronese (S : PowerSystem C) (a : ℕ) : PowerSystem C where
  gen := S.obj a
  obj n := S.obj (a * n)
  objZeroIso := S.objZeroIso
  succIso n := S.mulIso (a * n) a

/-- The generator of the `a`-th Veronese system is `S.obj a`. -/
@[simp]
theorem veronese_gen (S : PowerSystem C) (a : ℕ) : (S.veronese a).gen = S.obj a := rfl

/-- The `n`-th power of the `a`-th Veronese system is `S.obj (a * n)`. -/
@[simp]
theorem veronese_obj (S : PowerSystem C) (a n : ℕ) :
    (S.veronese a).obj n = S.obj (a * n) := rfl

/-- The zeroth-power identification of a Veronese system is that of the original system. -/
@[simp]
theorem veronese_objZeroIso (S : PowerSystem C) (a : ℕ) :
    (S.veronese a).objZeroIso = S.objZeroIso := rfl

/-- The successor comparison of the `a`-th Veronese system in degree `n` is the multiplication
isomorphism `S.obj (a * n) ⊗ S.obj a ≅ S.obj (a * n + a)`. -/
@[simp]
theorem veronese_succIso (S : PowerSystem C) (a n : ℕ) :
    (S.veronese a).succIso n = S.mulIso (a * n) a := rfl

/-- Transport along an equality of exponents, on the left factor of a multiplication
isomorphism. -/
theorem eqToHom_whiskerRight_mulIso (S : PowerSystem C) {m n : ℕ} (e : m = n) (b : ℕ) :
    (eqToHom (congrArg S.obj e) ▷ S.obj b) ≫ (S.mulIso n b).hom
      = (S.mulIso m b).hom ≫ eqToHom (congrArg S.obj (congrArg (· + b) e)) := by
  subst e; simp

/-- **The multiplication isomorphisms of a Veronese system are those of the original
system**, with both exponents multiplied by the weight. -/
theorem veronese_mulIso (S : PowerSystem C) (a p : ℕ) : ∀ q : ℕ,
    ((S.veronese a).mulIso p q).hom
      = (S.mulIso (a * p) (a * q)).hom
          ≫ eqToHom (congrArg S.obj (mul_add a p q).symm)
  | 0 => by simp [mulIso_zero]
  | q + 1 => by
      change ((S.veronese a).mulIso p (q + 1)).hom
          = (S.mulIso (a * p) (a * q + a)).hom
              ≫ eqToHom (congrArg S.obj (mul_add a p (q + 1)).symm)
      rw [mulIso_succ]
      simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
        veronese_mulIso S a p q, comp_whiskerRight, Category.assoc]
      rw [S.eqToHom_whiskerRight_mulIso (mul_add a p q).symm a,
        reassoc_of% S.mulIso_assoc (a * p) (a * q) a]
      simp

/-! ### The comparison of two power systems -/

/-- The **comparison isomorphisms** of two power systems along an isomorphism
`β : S.gen ≅ T.gen` of their generators: the `n`-th one is `β` tensored with itself `n`
times, read through the two systems' successor comparisons. -/
def compare (S T : PowerSystem C) (β : S.gen ≅ T.gen) : (n : ℕ) → S.obj n ≅ T.obj n
  | 0 => S.objZeroIso ≪≫ T.objZeroIso.symm
  | n + 1 => (S.succIso n).symm ≪≫ tensorIso (compare S T β n) β ≪≫ T.succIso n

/-- The comparison isomorphism in degree zero is
`S.obj 0 ≅ 𝟙_ C ≅ T.obj 0`. -/
theorem compare_zero (S T : PowerSystem C) (β : S.gen ≅ T.gen) :
    compare S T β 0 = S.objZeroIso ≪≫ T.objZeroIso.symm := rfl

/-- The comparison isomorphism in degree `n + 1` is the comparison in degree `n` tensored with
`β`, read through the two successor comparisons. -/
theorem compare_succ (S T : PowerSystem C) (β : S.gen ≅ T.gen) (n : ℕ) :
    compare S T β (n + 1)
      = (S.succIso n).symm ≪≫ tensorIso (compare S T β n) β ≪≫ T.succIso n := rfl

/-- The defining relation of the comparison isomorphisms in positive degree, as an equality of
morphisms into `T.obj (n + 1)`. -/
theorem tensorHom_compare_comp_succIso (S T : PowerSystem C) (β : S.gen ≅ T.gen) (n : ℕ) :
    ((compare S T β n).hom ⊗ₘ β.hom) ≫ (T.succIso n).hom
      = (S.succIso n).hom ≫ (compare S T β (n + 1)).hom := by
  simp [compare_succ]

/-- The comparison of a power system with itself along the identity is the identity. -/
theorem compare_refl (S : PowerSystem C) : ∀ n : ℕ,
    compare S S (Iso.refl S.gen) n = Iso.refl (S.obj n)
  | 0 => by rw [compare_zero, Iso.self_symm_id]
  | n + 1 => by
      rw [compare_succ, compare_refl S n]
      exact Iso.ext (by simp)

/-- A composite of three morphisms in the left factor of a tensor product splits off the outer
two as whiskerings. -/
theorem tensorHom_comp_comp_left {A A₀ B₀ B Ag Bg : C} (eA : A ⟶ A₀) (c : A₀ ⟶ B₀)
    (eB : B₀ ⟶ B) (bg : Ag ⟶ Bg) :
    ((eA ≫ c ≫ eB) ⊗ₘ bg) = (eA ▷ Ag) ≫ (c ⊗ₘ bg) ≫ (eB ▷ Bg) := by
  simp only [tensorHom_def, comp_whiskerRight, Category.assoc, whisker_exchange]

/-- For `cp : Ap ⟶ Bp` and isomorphisms `eA : A₀ ≅ 𝟙_ C`, `eB : B₀ ≅ 𝟙_ C`, the morphism
`cp ⊗ (eA.hom ≫ eB.inv)` intertwines the composites `Ap ⊗ A₀ ≅ Ap ⊗ 𝟙_ C ≅ Ap` and
`Bp ⊗ B₀ ≅ Bp ⊗ 𝟙_ C ≅ Bp` with `cp`. -/
theorem compare_mul_aux_zero {Ap A₀ Bp B₀ : C} (cp : Ap ⟶ Bp) (eA : A₀ ≅ 𝟙_ C)
    (eB : B₀ ≅ 𝟙_ C) :
    (cp ⊗ₘ (eA.hom ≫ eB.inv)) ≫ (Bp ◁ eB.hom) ≫ (ρ_ Bp).hom
      = (Ap ◁ eA.hom) ≫ (ρ_ Ap).hom ≫ cp := by
  rw [tensorHom_def, Category.assoc, ← whiskerLeft_comp_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, ← whisker_exchange_assoc, rightUnitor_naturality]

/-- If `cq ⊗ bg` and `cpq ⊗ bg` intertwine `σA`, `σB` and `τA`, `τB` with `cq1` and `cpq1`, and
`cp ⊗ cq` intertwines `mA` and `mB` with `cpq`, then `cp ⊗ cq1` intertwines the composite
`Ap ⊗ Aq1 ≅ Ap ⊗ (Aq ⊗ Ag) ≅ (Ap ⊗ Aq) ⊗ Ag ⟶ Apq ⊗ Ag ≅ Apq1` and its counterpart for the
`B`'s with `cpq1`. -/
theorem compare_mul_aux_succ {Ap Aq Ag Aq1 Apq Apq1 Bp Bq Bg Bq1 Bpq Bpq1 : C}
    (cp : Ap ⟶ Bp) (cq : Aq ⟶ Bq) (bg : Ag ⟶ Bg) (cq1 : Aq1 ⟶ Bq1) (cpq : Apq ⟶ Bpq)
    (cpq1 : Apq1 ⟶ Bpq1) (σA : Aq ⊗ Ag ≅ Aq1) (σB : Bq ⊗ Bg ≅ Bq1)
    (τA : Apq ⊗ Ag ≅ Apq1) (τB : Bpq ⊗ Bg ≅ Bpq1) (mA : Ap ⊗ Aq ⟶ Apq) (mB : Bp ⊗ Bq ⟶ Bpq)
    (hq : (cq ⊗ₘ bg) ≫ σB.hom = σA.hom ≫ cq1)
    (hpq : (cpq ⊗ₘ bg) ≫ τB.hom = τA.hom ≫ cpq1)
    (ih : (cp ⊗ₘ cq) ≫ mB = mA ≫ cpq) :
    (cp ⊗ₘ cq1) ≫ (Bp ◁ σB.inv) ≫ (α_ Bp Bq Bg).inv ≫ (mB ▷ Bg) ≫ τB.hom
      = (Ap ◁ σA.inv) ≫ (α_ Ap Aq Ag).inv ≫ (mA ▷ Ag) ≫ τA.hom ≫ cpq1 := by
  have hσ : cq1 ≫ σB.inv = σA.inv ≫ (cq ⊗ₘ bg) := by
    rw [(Iso.eq_comp_inv σB).2 hq, Category.assoc, Iso.inv_hom_id_assoc]
  have e1 : (cp ⊗ₘ cq1) ≫ (Bp ◁ σB.inv) = (Ap ◁ σA.inv) ≫ (cp ⊗ₘ (cq ⊗ₘ bg)) := by
    rw [← id_tensorHom Bp σB.inv, tensorHom_comp_tensorHom, Category.comp_id, hσ,
      ← id_tensorHom Ap σA.inv, tensorHom_comp_tensorHom, Category.id_comp]
  have e2 : ((cp ⊗ₘ cq) ⊗ₘ bg) ≫ (mB ▷ Bg) = (mA ▷ Ag) ≫ (cpq ⊗ₘ bg) := by
    rw [← tensorHom_id mB Bg, ← tensorHom_id mA Ag, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, ih]
  rw [reassoc_of% e1, associator_inv_naturality_assoc, reassoc_of% e2, hpq]

/-- **The comparison isomorphisms are multiplicative**: they commute with the multiplication
isomorphisms of the two power systems. -/
theorem compare_mul (S T : PowerSystem C) (β : S.gen ≅ T.gen) (p : ℕ) : ∀ q : ℕ,
    ((compare S T β p).hom ⊗ₘ (compare S T β q).hom) ≫ (T.mulIso p q).hom
      = (S.mulIso p q).hom ≫ (compare S T β (p + q)).hom
  | 0 => by
      rw [mulIso_zero, mulIso_zero, compare_zero]
      simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc]
      exact compare_mul_aux_zero (compare S T β p).hom S.objZeroIso T.objZeroIso
  | q + 1 => by
      rw [mulIso_succ, mulIso_succ, compare_succ]
      simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
        tensorIso_hom, Category.assoc]
      exact compare_mul_aux_succ (compare S T β p).hom (compare S T β q).hom β.hom
        (compare S T β (q + 1)).hom (compare S T β (p + q)).hom (compare S T β (p + q + 1)).hom
        (S.succIso q) (T.succIso q) (S.succIso (p + q)) (T.succIso (p + q))
        (S.mulIso p q).hom (T.mulIso p q).hom
        (tensorHom_compare_comp_succIso S T β q)
        (tensorHom_compare_comp_succIso S T β (p + q))
        (compare_mul S T β p q)

/-! ### Comparing two Veronese systems -/

/-- If `(eA ▷ Ag) ≫ nA.hom = mA.hom ≫ fA`, `(eB ▷ Bg) ≫ mB.hom = nB.hom ≫ fB` and
`(c ⊗ bg) ≫ nB.hom = nA.hom ≫ c₂`, then conjugating `(eA ≫ c ≫ eB) ⊗ bg` by `mA` and `mB` gives
`fA ≫ c₂ ≫ fB`. -/
theorem compare_veronese_aux {A A₀ Ag A₁ A₂ B B₀ Bg B₁ B₂ : C} (eA : A ⟶ A₀) (eB : B₀ ⟶ B)
    (c : A₀ ⟶ B₀) (bg : Ag ⟶ Bg) (c₂ : A₂ ⟶ B₂) (mA : A ⊗ Ag ≅ A₁) (nA : A₀ ⊗ Ag ≅ A₂)
    (fA : A₁ ⟶ A₂) (mB : B ⊗ Bg ≅ B₁) (nB : B₀ ⊗ Bg ≅ B₂) (fB : B₂ ⟶ B₁)
    (hA : (eA ▷ Ag) ≫ nA.hom = mA.hom ≫ fA)
    (hB : (eB ▷ Bg) ≫ mB.hom = nB.hom ≫ fB)
    (h : (c ⊗ₘ bg) ≫ nB.hom = nA.hom ≫ c₂) :
    mA.inv ≫ ((eA ≫ c ≫ eB) ⊗ₘ bg) ≫ mB.hom = fA ≫ c₂ ≫ fB := by
  rw [tensorHom_comp_comp_left, Category.assoc, Category.assoc, hB, reassoc_of% h,
    reassoc_of% hA, Iso.inv_hom_id_assoc]

/-- **The comparison of two Veronese systems is multiplicative** for the multiplication
isomorphisms of the two underlying systems. -/
theorem compare_veronese_mul (S T : PowerSystem C) {a a' : ℕ} (β : S.obj a ≅ T.obj a')
    (p q : ℕ) :
    ((compare (S.veronese a) (T.veronese a') β p).hom ⊗ₘ
        (compare (S.veronese a) (T.veronese a') β q).hom) ≫ (T.mulIso (a' * p) (a' * q)).hom
      = (S.mulIso (a * p) (a * q)).hom
          ≫ eqToHom (congrArg S.obj (mul_add a p q).symm)
          ≫ (compare (S.veronese a) (T.veronese a') β (p + q)).hom
          ≫ eqToHom (congrArg T.obj (mul_add a' p q)) := by
  have h := compare_mul (S.veronese a) (T.veronese a') β p q
  rw [veronese_mulIso, veronese_mulIso] at h
  simpa using h =≫ eqToHom (congrArg T.obj (mul_add a' p q))

/-- **The tensor powers of a tensor power of `β` are tensor powers of `β`**: comparing the
`ak`-th and `a'k`-th Veronese systems along the degree-`k` comparison of the `a`-th and
`a'`-th ones gives, in degree `m`, the degree-`km` comparison of the latter. -/
theorem compare_veronese_veronese (S T : PowerSystem C) {a a' : ℕ} (β : S.obj a ≅ T.obj a')
    (k : ℕ) : ∀ m : ℕ,
    (compare (S.veronese (a * k)) (T.veronese (a' * k))
        (compare (S.veronese a) (T.veronese a') β k) m).hom
      = eqToHom (congrArg S.obj (mul_assoc a k m)) ≫
          (compare (S.veronese a) (T.veronese a') β (k * m)).hom ≫
          eqToHom (congrArg T.obj (mul_assoc a' k m).symm)
  | 0 => by
      simp only [Nat.mul_zero, eqToHom_refl, Category.id_comp, Category.comp_id, compare_zero,
        Iso.trans_hom, Iso.symm_hom]
  | m + 1 => by
      change (compare (S.veronese (a * k)) (T.veronese (a' * k))
          (compare (S.veronese a) (T.veronese a') β k) (m + 1)).hom
        = eqToHom (congrArg S.obj (mul_assoc a k (m + 1))) ≫
            (compare (S.veronese a) (T.veronese a') β (k * m + k)).hom ≫
            eqToHom (congrArg T.obj (mul_assoc a' k (m + 1)).symm)
      rw [compare_succ]
      simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom]
      rw [compare_veronese_veronese S T β k m,
        compare_veronese_aux (eqToHom (congrArg S.obj (mul_assoc a k m)))
          (eqToHom (congrArg T.obj (mul_assoc a' k m).symm))
          (compare (S.veronese a) (T.veronese a') β (k * m)).hom
          (compare (S.veronese a) (T.veronese a') β k).hom
          (eqToHom (congrArg S.obj (mul_add a (k * m) k).symm)
            ≫ (compare (S.veronese a) (T.veronese a') β (k * m + k)).hom
            ≫ eqToHom (congrArg T.obj (mul_add a' (k * m) k)))
          (S.mulIso (a * k * m) (a * k)) (S.mulIso (a * (k * m)) (a * k)) _
          (T.mulIso (a' * k * m) (a' * k)) (T.mulIso (a' * (k * m)) (a' * k)) _
          (S.eqToHom_whiskerRight_mulIso (mul_assoc a k m) (a * k))
          (T.eqToHom_whiskerRight_mulIso (mul_assoc a' k m).symm (a' * k))
          (compare_veronese_mul S T β (k * m) k)]
      simp

end PowerSystem

end Stacks.Monoidal

end
