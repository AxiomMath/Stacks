module

public import StacksFrontier.Algebra.Homology.AbelianGroupComplexResolutions

/-!
# The product total complex of a double complex with acyclic columns

Let `K` be a double complex of abelian groups whose first index runs over `ℕ` and whose second
index runs over `ℤ`, so that its product total complex `Tot_π(K)`, with
`Tot_π^n(K) = ∏_{p + q = n} K^{p, q}`, is defined. If every column `K^{p, •}` is acyclic, then
`Tot_π(K)` is acyclic.

The proof is the diagram chase one expects, and the only point needing care is that the
construction of a primitive is infinite: a cocycle `x` of `Tot_π^{n + 1}(K)` has infinitely many
components, and a primitive is built one component at a time, the choice in column `p + 1`
depending on the choice already made in column `p`. The chase is carried by the invariant

`d_1(x^{p, n + 1 - p}) = (-1)^p d_1(d_2(y^p))`,

which says that the horizontal image of the `p`-th component of the cocycle is already accounted
for by the component of the primitive constructed so far. It is exactly what makes the next
component exist, and it propagates.

No exactness in the first index is assumed, and no boundedness: the hypothesis is acyclicity of
every column, in every degree.

## Main results

* `HomologicalComplex₂.acyclic_productTotal`: the product total complex of a double complex of
  abelian groups with acyclic columns is acyclic.
* `HomologicalComplex₂.exactAt_productTotal`: the same, one degree at a time.

## Implementation notes

The degree of the `p`-th component of a primitive of a cocycle of degree `n + 1` is `n - p`, and
this expression is never normalised; the identification of `n - p` with the second index of a
component of `Tot_π` is made by `HomologicalComplex.XIsoOfEq` once, at the end.

The invariant quantifies over the degree in which it is read, rather than fixing that degree to
`n + 1 - p`. The degree is determined by the quantified equation, so this is no weakening, and it
lets the invariant be used and established at whichever spelling of the degree the surrounding
computation produces — the alternative, transporting a differential along an equality of degrees,
turns every step into a dependent rewrite.

The recursion producing the components is a `Nat.rec` into the subtype of elements satisfying the
invariant, with the step function extracted by `choose`, as in the proof of Stacks 09J0 in
`StacksFrontier/Algebra/Homology/AbelianGroupComplexResolutions.lean`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace HomologicalComplex₂

variable {K : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ)}

/-! ### Signs -/

/-- Scaling twice by `(-1)^(p + 1)` is the identity. -/
private lemma sign_sq_smul {G : Type*} [AddCommGroup G] (p : ℕ) (A : G) :
    ((-1 : ℤ) ^ (p + 1)) • (((-1 : ℤ) ^ (p + 1)) • A) = A := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The algebraic content of the propagation step: from `A + (-1)^{p+1} B = 0` and
`A = (-1)^p C` one gets `B = C`. -/
private lemma eq_of_sign_relation {G : Type*} [AddCommGroup G] (p : ℕ) (A B C : G)
    (h : A + ((-1 : ℤ) ^ (p + 1)) • B = 0) (ha : A = ((-1 : ℤ) ^ p) • C) : B = C := by
  subst ha
  have h1 : ((-1 : ℤ) ^ (p + 1)) • B = -(((-1 : ℤ) ^ p) • C) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have h2 := congrArg (fun t : G => ((-1 : ℤ) ^ (p + 1)) • t) h1
  simp only [smul_neg] at h2
  rw [sign_sq_smul, smul_smul,
    show ((-1 : ℤ) ^ (p + 1) * (-1 : ℤ) ^ p) = -1 by
      rw [← pow_add, show p + 1 + p = 2 * p + 1 by ring, pow_succ, pow_mul]; norm_num,
    neg_smul, one_smul, neg_neg] at h2
  exact h2

/-! ### Element-wise consequences of acyclicity of a column -/

/-- Exactness of a complex of abelian groups in degree `a + 1`, on elements. -/
private lemma exactAt_succ_iff {C : HomologicalComplex AddCommGrpCat.{u} (ComplexShape.up ℤ)}
    (a : ℤ) : C.ExactAt (a + 1) ↔
      ∀ z : C.X (a + 1), C.d (a + 1) (a + 1 + 1) z = 0 → ∃ y : C.X a, C.d a (a + 1) y = z := by
  rw [HomologicalComplex.exactAt_iff' _ a (a + 1) (a + 1 + 1) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  rfl

/-- Acyclicity of a column of a double complex of abelian groups, on elements: an element of
`K^{p, b}` killed by the vertical differential is a vertical boundary. -/
private lemma column_exact (hK : ∀ p : ℕ, (K.X p).Acyclic) (p : ℕ) (a b c : ℤ)
    (hab : a + 1 = b) (hbc : b + 1 = c) (z : (K.X p).X b) (hz : (K.X p).d b c z = 0) :
    ∃ y : (K.X p).X a, (K.X p).d a b y = z := by
  subst hab
  subst hbc
  exact (exactAt_succ_iff a).mp (hK p (a + 1)) z hz

/-- The horizontal differential is a morphism of complexes, on elements. -/
private lemma horiz_vert (i j : ℕ) (a b : ℤ) (z : (K.X i).X a) :
    (K.d i j).f b ((K.X i).d a b z) = (K.X j).d a b ((K.d i j).f a z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (K.d i j).comm]

/-- Applying the horizontal differential twice is zero, on elements. -/
private lemma horiz_horiz (i j k : ℕ) (b : ℤ) (z : (K.X i).X b) :
    (K.d j k).f b ((K.d i j).f b z) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, K.d_comp_d]; rfl

/-! ### The chase -/

section

variable (K) in
/-- The invariant carried by the chase: the horizontal image of the `p`-th component of the
cocycle `x` is the horizontal image of the vertical boundary of `a`, up to the sign `(-1)^p`.
The degree in which the identity is read is quantified over; it is determined by the equation
`p + e = n + 1`. -/
private def Carried (n : ℤ) (x : K.productTotalX (n + 1)) (p : ℕ)
    (a : (K.X p).X (n - (p : ℤ))) : Prop :=
  ∀ (e : ℤ) (he : (p : ℤ) + e = n + 1),
    (K.d p (p + 1)).f e (x ⟨(p, e), he⟩) =
      ((-1 : ℤ) ^ p) • (K.d p (p + 1)).f e ((K.X p).d (n - (p : ℤ)) e a)

variable (hK : ∀ p : ℕ, (K.X p).Acyclic) (n : ℤ) (x : K.productTotalX (n + 1))
  (hx : K.productTotalD (n + 1) x = 0)

include hK hx in
/-- The first component of a primitive: it exists because the top component of the cocycle is a
vertical cocycle, and it satisfies the invariant because in degree `0` the invariant follows from
its being a primitive of that component. -/
private lemma carried_base :
    ∃ a : (K.X 0).X (n - ((0 : ℕ) : ℤ)),
      (K.X 0).d (n - ((0 : ℕ) : ℤ)) (n + 1 - ((0 : ℕ) : ℤ)) a =
          x ⟨(0, n + 1 - ((0 : ℕ) : ℤ)), by push_cast; ring⟩ ∧
        Carried K n x 0 a := by
  have hcocycle : (K.X 0).d (n + 1 - ((0 : ℕ) : ℤ)) (n + 2 - ((0 : ℕ) : ℤ))
      (x ⟨(0, n + 1 - ((0 : ℕ) : ℤ)), by push_cast; ring⟩) = 0 := by
    have h := congrFun hx ⟨(0, n + 2 - ((0 : ℕ) : ℤ)), by push_cast; ring⟩
    rw [K.productTotalD_apply_zero_left (n + 1) x (n + 2 - ((0 : ℕ) : ℤ))
      (n + 1 - ((0 : ℕ) : ℤ)) (by ring) (by push_cast; ring) (by push_cast; ring)] at h
    exact h
  obtain ⟨a, ha⟩ := column_exact hK 0 (n - ((0 : ℕ) : ℤ)) (n + 1 - ((0 : ℕ) : ℤ))
    (n + 2 - ((0 : ℕ) : ℤ)) (by ring) (by ring) _ hcocycle
  refine ⟨a, ha, fun e he => ?_⟩
  obtain rfl : e = n + 1 - ((0 : ℕ) : ℤ) := by push_cast at he ⊢; omega
  rw [ha, pow_zero, one_smul]

include hK hx in
/-- The step of the chase: given a component satisfying the invariant, the next component exists,
and satisfies the invariant in turn. -/
private lemma carried_step (p : ℕ) (a : (K.X p).X (n - (p : ℤ))) (ha : Carried K n x p a) :
    ∃ b : (K.X (p + 1)).X (n - ((p + 1 : ℕ) : ℤ)),
      (K.X (p + 1)).d (n - ((p + 1 : ℕ) : ℤ)) (n - (p : ℤ)) b =
          ((-1 : ℤ) ^ (p + 1)) • (x ⟨(p + 1, n - (p : ℤ)), by push_cast; ring⟩ -
            (K.d p (p + 1)).f (n - (p : ℤ)) a) ∧
        Carried K n x (p + 1) b := by
  have hdx : (K.d p (p + 1)).f (n + 1 - (p : ℤ))
        (x ⟨(p, n + 1 - (p : ℤ)), by push_cast; ring⟩) +
      ((-1 : ℤ) ^ (p + 1)) • (K.X (p + 1)).d (n - (p : ℤ)) (n + 1 - (p : ℤ))
        (x ⟨(p + 1, n - (p : ℤ)), by push_cast; ring⟩) = 0 := by
    have h := congrFun hx ⟨(p + 1, n + 1 - (p : ℤ)), by push_cast; ring⟩
    rw [K.productTotalD_apply_succ (n + 1) x p (n + 1 - (p : ℤ)) (n - (p : ℤ))
      (by ring) (by push_cast; ring) (by push_cast; ring)] at h
    exact h
  -- the vertical differential of the correction `z` vanishes
  have hzv : (K.X (p + 1)).d (n - (p : ℤ)) (n + 1 - (p : ℤ))
        (x ⟨(p + 1, n - (p : ℤ)), by push_cast; ring⟩) =
      (K.d p (p + 1)).f (n + 1 - (p : ℤ))
        ((K.X p).d (n - (p : ℤ)) (n + 1 - (p : ℤ)) a) :=
    eq_of_sign_relation p _ _ _ hdx (ha (n + 1 - (p : ℤ)) (by ring))
  have hz : (K.X (p + 1)).d (n - (p : ℤ)) (n + 1 - (p : ℤ))
      (x ⟨(p + 1, n - (p : ℤ)), by push_cast; ring⟩ -
        (K.d p (p + 1)).f (n - (p : ℤ)) a) = 0 := by
    rw [map_sub, hzv, ← horiz_vert p (p + 1) (n - (p : ℤ)) (n + 1 - (p : ℤ)) a, sub_self]
  obtain ⟨b, hb⟩ := column_exact hK (p + 1) (n - ((p + 1 : ℕ) : ℤ)) (n - (p : ℤ))
    (n + 1 - (p : ℤ)) (by push_cast; ring) (by ring)
    (((-1 : ℤ) ^ (p + 1)) • (x ⟨(p + 1, n - (p : ℤ)), by push_cast; ring⟩ -
      (K.d p (p + 1)).f (n - (p : ℤ)) a))
    (by rw [map_zsmul, hz, smul_zero])
  refine ⟨b, hb, fun e he => ?_⟩
  obtain rfl : e = n - (p : ℤ) := by push_cast at he ⊢; omega
  rw [hb, map_zsmul, sign_sq_smul, map_sub,
    horiz_horiz p (p + 1) (p + 1 + 1) (n - (p : ℤ)) a, sub_zero]

include hK hx in
/-- A cocycle of the product total complex is a coboundary. -/
private lemma exists_productTotal_primitive :
    ∃ y : K.productTotalX n, K.productTotalD n y = x := by
  obtain ⟨a₀, ha₀, hI₀⟩ := carried_base hK n x hx
  choose b hb₁ hb₂ using carried_step hK n x hx
  let Y : ∀ p : ℕ, {a : (K.X p).X (n - (p : ℤ)) // Carried K n x p a} := fun p =>
    Nat.rec (motive := fun p => {a : (K.X p).X (n - (p : ℤ)) // Carried K n x p a})
      ⟨a₀, hI₀⟩ (fun p a => ⟨b p a.1 a.2, hb₂ p a.1 a.2⟩) p
  let y : K.productTotalX n := fun i => ((K.X i.1.1).XIsoOfEq
    (show n - (i.1.1 : ℤ) = i.1.2 by have := i.2; omega)).hom (Y i.1.1).1
  refine ⟨y, ?_⟩
  funext ⟨⟨p, q⟩, h⟩
  rcases p with _ | p
  · obtain rfl : q = n + 1 - ((0 : ℕ) : ℤ) := by push_cast at h ⊢; omega
    rw [K.productTotalD_apply_zero_left n y (n + 1 - ((0 : ℕ) : ℤ)) (n - ((0 : ℕ) : ℤ))
      (by ring) h (by push_cast; ring)]
    change (K.X 0).d (n - ((0 : ℕ) : ℤ)) (n + 1 - ((0 : ℕ) : ℤ))
      (((K.X 0).XIsoOfEq (by push_cast; ring)).hom (Y 0).1) = _
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ConcreteCategory.id_apply]
    exact ha₀
  · obtain rfl : q = n - (p : ℤ) := by push_cast at h ⊢; omega
    rw [K.productTotalD_apply_succ n y p (n - (p : ℤ)) (n - ((p + 1 : ℕ) : ℤ))
      (by push_cast; ring) h (by push_cast; ring)]
    change (K.d p (p + 1)).f (n - (p : ℤ))
        (((K.X p).XIsoOfEq (by ring)).hom (Y p).1) +
      ((-1 : ℤ) ^ (p + 1)) • (K.X (p + 1)).d (n - ((p + 1 : ℕ) : ℤ)) (n - (p : ℤ))
        (((K.X (p + 1)).XIsoOfEq (by push_cast; ring)).hom (Y (p + 1)).1) = _
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ConcreteCategory.id_apply]
    rw [show (Y (p + 1)).1 = b p (Y p).1 (Y p).2 from rfl, hb₁ p (Y p).1 (Y p).2,
      sign_sq_smul]
    abel

end

/-! ### The theorem -/

/-- **The product total complex of a double complex with acyclic columns is acyclic**, in the
given degree. -/
theorem exactAt_productTotal (hK : ∀ p : ℕ, (K.X p).Acyclic) (i : ℤ) :
    K.productTotal.ExactAt i := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = i := ⟨i - 1, by omega⟩
  rw [exactAt_succ_iff]
  intro z hz
  have hz' : K.productTotalD (n + 1) z = 0 := by
    rw [← K.productTotal_d (n + 1)]; exact hz
  obtain ⟨y, hy⟩ := exists_productTotal_primitive hK n z hz'
  exact ⟨y, by rw [K.productTotal_d n]; exact hy⟩

/-- **The product total complex of a double complex with acyclic columns is acyclic.** -/
theorem acyclic_productTotal (hK : ∀ p : ℕ, (K.X p).Acyclic) : K.productTotal.Acyclic :=
  fun i => exactAt_productTotal hK i

end HomologicalComplex₂

end
