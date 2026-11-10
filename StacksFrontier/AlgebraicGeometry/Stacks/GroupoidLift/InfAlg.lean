module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Basic

/-!
# The algebra of triples of lifts

For a square-zero thickening `e : C' → C` of `κ`-small `A'`-algebras, the triples of elements of
`C'` with a common image in `C` form an algebra `fib3 e`, again a square-zero thickening of `C`.
For `c₁ c₂ ∈ C'` the map `(a, b, d) ↦ a + c₁ (b - a) + c₂ (d - a)` is a map of algebras
`fib3 e → C'` (`fib3Sigma`), because the differences lie in the square-zero kernel.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.fib3`, `fib3Sq` (its thickening structure),
  `fib3Proj`, `fib3Diag`, `fib3Sigma`, `fib3Lift`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} {C' C : SmallAlg A' κ} (e : SqZero C' C)

/-- The triples with a common reduction. -/
def fib3Sub : Subalgebra A' (C'.obj × C'.obj × C'.obj) where
  carrier := {x | e.q.hom.hom x.1 = e.q.hom.hom x.2.1 ∧ e.q.hom.hom x.1 = e.q.hom.hom x.2.2}
  mul_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨by simp [hx₁, hy₁], by simp [hx₂, hy₂]⟩
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨by simp [hx₁, hy₁], by simp [hx₂, hy₂]⟩
  algebraMap_mem' a := ⟨rfl, rfl⟩

/-- For `ℵ₀ < κ`, the algebra of triples has cardinality less than `κ`. -/
theorem card_fib3_lt (hκ : Cardinal.aleph0 < κ) : Cardinal.mk (fib3Sub e) < κ := by
  refine (Cardinal.mk_subtype_le _).trans_lt ?_
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt hκ.le C'.property
    (Cardinal.mul_lt_of_lt hκ.le C'.property C'.property)

variable (hκ : Cardinal.aleph0 < κ)

/-- The algebra of triples, as a small algebra. -/
abbrev fib3 : SmallAlg A' κ := SmallAlg.mk (fib3Sub e) (card_fib3_lt e hκ)

/-- The three projections. -/
def fib3Proj (k : Fin 3) : fib3 e hκ ⟶ C' :=
  SmallAlg.homMk
    { toFun := fun x ↦ ![x.1.1, x.1.2.1, x.1.2.2] k
      map_one' := by fin_cases k <;> rfl
      map_mul' := fun x y ↦ by fin_cases k <;> rfl
      map_zero' := by fin_cases k <;> rfl
      map_add' := fun x y ↦ by fin_cases k <;> rfl
      commutes' := fun a ↦ by fin_cases k <;> rfl }

/-- The `k`-th projection sends a triple to its `k`-th entry. -/
theorem fib3Proj_apply (k : Fin 3) (x : (fib3 e hκ).obj) :
    (fib3Proj e hκ k).hom.hom x = ![x.1.1, x.1.2.1, x.1.2.2] k := rfl

/-- The diagonal. -/
def fib3Diag : C' ⟶ fib3 e hκ :=
  SmallAlg.homMk
    { toFun := fun c ↦ ⟨(c, c, c), rfl, rfl⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }

/-- Each projection is a retraction of the diagonal. -/
theorem fib3Diag_proj (k : Fin 3) : fib3Diag e hκ ≫ fib3Proj e hκ k = 𝟙 C' := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  ext c
  fin_cases k <;> rfl

/-- The reduction of a triple. -/
def fib3Red : fib3 e hκ ⟶ C := fib3Proj e hκ 0 ≫ e.q

/-- **The algebra of triples is a square-zero thickening of `C`.** -/
def fib3Sq : SqZero (fib3 e hκ) C where
  q := fib3Red e hκ
  surj c := by
    obtain ⟨c', rfl⟩ := e.surj c
    exact ⟨(fib3Diag e hκ).hom.hom c', rfl⟩
  sq := by
    rw [pow_two]
    refine le_bot_iff.mp (Ideal.mul_le.mpr fun x hx y hy ↦ ?_)
    have hx₀ : e.q.hom.hom x.1.1 = 0 := hx
    have hy₀ : e.q.hom.hom y.1.1 = 0 := hy
    have h : ∀ {a b : C'.obj}, e.q.hom.hom a = 0 → e.q.hom.hom b = 0 → a * b = 0 :=
      fun ha hb ↦ mul_eq_zero_of_ker e.q.hom.hom e.sq ha hb
    rw [Ideal.mem_bot]
    refine Subtype.ext (Prod.ext (h hx₀ hy₀) (Prod.ext ?_ ?_))
    · exact h (x.2.1 ▸ hx₀) (y.2.1 ▸ hy₀)
    · exact h (x.2.2 ▸ hx₀) (y.2.2 ▸ hy₀)


/-- The product of two elements of the kernel of `e.q` vanishes. -/
theorem fib3_mul_eq_zero {a b : C'.obj} (ha : e.q.hom.hom a = 0) (hb : e.q.hom.hom b = 0) :
    a * b = 0 :=
  mul_eq_zero_of_ker e.q.hom.hom e.sq ha hb

/-- **The affine combination `a + c₁ (b - a) + c₂ (d - a)`** of a triple, a map of algebras. -/
def fib3Sigma (c₁ c₂ : C'.obj) : fib3 e hκ ⟶ C' :=
  SmallAlg.homMk
    { toFun := fun x ↦ x.1.1 + c₁ * (x.1.2.1 - x.1.1) + c₂ * (x.1.2.2 - x.1.1)
      map_one' := by
        change (1 : C'.obj) + c₁ * (1 - 1) + c₂ * (1 - 1) = 1
        ring
      map_mul' := fun x y ↦ by
        change x.1.1 * y.1.1 + c₁ * (x.1.2.1 * y.1.2.1 - x.1.1 * y.1.1) +
            c₂ * (x.1.2.2 * y.1.2.2 - x.1.1 * y.1.1) =
          (x.1.1 + c₁ * (x.1.2.1 - x.1.1) + c₂ * (x.1.2.2 - x.1.1)) *
            (y.1.1 + c₁ * (y.1.2.1 - y.1.1) + c₂ * (y.1.2.2 - y.1.1))
        have k : ∀ (z : (fib3 e hκ).obj), e.q.hom.hom (z.1.2.1 - z.1.1) = 0 ∧
            e.q.hom.hom (z.1.2.2 - z.1.1) = 0 := fun z ↦
          ⟨by rw [map_sub, z.2.1, sub_self], by rw [map_sub, z.2.2, sub_self]⟩
        have h₁ := fib3_mul_eq_zero e (k x).1 (k y).1
        have h₂ := fib3_mul_eq_zero e (k x).1 (k y).2
        have h₃ := fib3_mul_eq_zero e (k x).2 (k y).1
        have h₄ := fib3_mul_eq_zero e (k x).2 (k y).2
        linear_combination (c₁ - c₁ ^ 2) * h₁ - c₁ * c₂ * h₂ - c₁ * c₂ * h₃ +
          (c₂ - c₂ ^ 2) * h₄
      map_zero' := by
        change (0 : C'.obj) + c₁ * (0 - 0) + c₂ * (0 - 0) = 0
        ring
      map_add' := fun x y ↦ by
        change x.1.1 + y.1.1 + c₁ * (x.1.2.1 + y.1.2.1 - (x.1.1 + y.1.1)) +
            c₂ * (x.1.2.2 + y.1.2.2 - (x.1.1 + y.1.1)) = _
        ring
      commutes' := fun a ↦ by
        change algebraMap A' C'.obj a + c₁ * (algebraMap A' C'.obj a - algebraMap A' C'.obj a) +
          c₂ * (algebraMap A' C'.obj a - algebraMap A' C'.obj a) = algebraMap A' C'.obj a
        ring }

/-- `fib3Sigma e hκ c₁ c₂` sends `(a, b, d)` to `a + c₁ (b - a) + c₂ (d - a)`. -/
theorem fib3Sigma_apply (c₁ c₂ : C'.obj) (x : (fib3 e hκ).obj) :
    (fib3Sigma e hκ c₁ c₂).hom.hom x = x.1.1 + c₁ * (x.1.2.1 - x.1.1) + c₂ * (x.1.2.2 - x.1.1) :=
  rfl

/-- The affine combination `fib3Sigma e hκ c₁ c₂` is a retraction of the diagonal. -/
theorem fib3Diag_sigma (c₁ c₂ : C'.obj) : fib3Diag e hκ ≫ fib3Sigma e hκ c₁ c₂ = 𝟙 C' := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  ext c
  change c + c₁ * (c - c) + c₂ * (c - c) = c
  ring

/-- Three lifts with a common reduction, as a point of the algebra of triples. -/
def fib3Lift {Q : Type u} [CommRing Q] [Algebra A' Q] (f₀ f₁ f₂ : Q →ₐ[A'] C'.obj)
    (h₁ : e.q.hom.hom.comp f₁ = e.q.hom.hom.comp f₀)
    (h₂ : e.q.hom.hom.comp f₂ = e.q.hom.hom.comp f₀) : Q →ₐ[A'] (fib3 e hκ).obj :=
  (f₀.prod (f₁.prod f₂)).codRestrict (fib3Sub e) fun x ↦
    ⟨(congrArg (fun f : Q →ₐ[A'] C.obj ↦ f x) h₁).symm,
      (congrArg (fun f : Q →ₐ[A'] C.obj ↦ f x) h₂).symm⟩

/-- The `k`-th projection of `fib3Lift e hκ f₀ f₁ f₂ h₁ h₂` is `fₖ`. -/
theorem fib3Lift_proj {Q : Type u} [CommRing Q] [Algebra A' Q] (f₀ f₁ f₂ : Q →ₐ[A'] C'.obj)
    (h₁ : e.q.hom.hom.comp f₁ = e.q.hom.hom.comp f₀)
    (h₂ : e.q.hom.hom.comp f₂ = e.q.hom.hom.comp f₀) (k : Fin 3) :
    (fib3Proj e hκ k).hom.hom.comp (fib3Lift e hκ f₀ f₁ f₂ h₁ h₂) = ![f₀, f₁, f₂] k := by
  ext x
  fin_cases k <;> rfl

/-- The reduction of `fib3Lift e hκ f₀ f₁ f₂ h₁ h₂` is the common reduction `e.q ∘ f₀`. -/
theorem fib3Lift_red {Q : Type u} [CommRing Q] [Algebra A' Q] (f₀ f₁ f₂ : Q →ₐ[A'] C'.obj)
    (h₁ : e.q.hom.hom.comp f₁ = e.q.hom.hom.comp f₀)
    (h₂ : e.q.hom.hom.comp f₂ = e.q.hom.hom.comp f₀) :
    (fib3Sq e hκ).q.hom.hom.comp (fib3Lift e hκ f₀ f₁ f₂ h₁ h₂) = e.q.hom.hom.comp f₀ := by
  ext x
  rfl

/-- The affine combination of `fib3Lift e hκ f₀ f₁ f₂ h₁ h₂` at `x` is
`f₀ x + c₁ (f₁ x - f₀ x) + c₂ (f₂ x - f₀ x)`. -/
theorem fib3Lift_sigma {Q : Type u} [CommRing Q] [Algebra A' Q] (f₀ f₁ f₂ : Q →ₐ[A'] C'.obj)
    (h₁ : e.q.hom.hom.comp f₁ = e.q.hom.hom.comp f₀)
    (h₂ : e.q.hom.hom.comp f₂ = e.q.hom.hom.comp f₀) (c₁ c₂ : C'.obj) (x : Q) :
    (fib3Sigma e hκ c₁ c₂).hom.hom (fib3Lift e hκ f₀ f₁ f₂ h₁ h₂ x) =
      f₀ x + c₁ * (f₁ x - f₀ x) + c₂ * (f₂ x - f₀ x) :=
  rfl

/-- The diagonal composed with `f` is the point `fib3Lift` of the triple `(f, f, f)`. -/
theorem fib3Diag_comp {Q : Type u} [CommRing Q] [Algebra A' Q] (f : Q →ₐ[A'] C'.obj) :
    (fib3Diag e hκ).hom.hom.comp f = fib3Lift e hκ f f f rfl rfl :=
  AlgHom.ext fun _ ↦ rfl

end AlgebraicGeometry.Stack.GroupoidLift

end
