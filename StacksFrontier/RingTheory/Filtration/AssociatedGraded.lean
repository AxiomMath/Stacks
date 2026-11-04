module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Filtration

/-!
# The associated graded ring and module of an ideal

For an ideal `I` of a commutative ring `A`, the associated graded ring is the direct sum of the
quotients `I^n / I^(n+1)`, and for an `A`-module `M` the associated graded module is the direct
sum of the `I^n M / I^(n+1) M`. Multiplying a homogeneous ring class of degree `i` by a
homogeneous module class of degree `j` lands in degree `i + j`, which makes the first a graded
commutative ring and the second a graded module over it.

## Main definitions

* `AssociatedGraded.power`: the submodule `I^n M`.
* `AssociatedGraded.piece`: the degree `n` quotient `I^n M / I^(n+1) M`.
* `AssociatedGraded.mk`: the class of an element of `I^n M` in that quotient.
* `AssociatedGraded.gradedRing` and `AssociatedGraded.gradedModule`: the direct sums of the
  ring, resp. module, pieces.
* `AssociatedGraded.homogeneousSMul`: the action of one homogeneous class on another.
* `AssociatedGraded.gradedCommRing` and `AssociatedGraded.gradedModuleStructure`: the graded
  commutative ring structure and the graded module structure it carries.
* `AssociatedGraded.GradedLinearEquiv`: an isomorphism of associated graded modules over the same
  associated graded ring, that is, one preserving degrees and the graded scalar action.

## Main results

* `AssociatedGraded.smul_mem_power`: the degree rule `I^i · I^j M ⊆ I^(i+j) M`, which is what
  makes `homogeneousSMul` well defined.
* `AssociatedGraded.smul_eq_zero_of_mem`: `I` annihilates every homogeneous class, so the action
  of `A` on a piece factors through `A ⧸ I`.
* `AssociatedGraded.of_mul_of` and `AssociatedGraded.of_smul_of`: multiplication and scalar
  multiplication of homogeneous classes inside the direct sums.

## Implementation notes

The degree `n` quotient is formed inside the subtype `I^n M`, with denominator the preimage of
`I^(n+1) M`, so no choice of representatives is needed. The graded structures are assembled by
`DirectSum.GCommRing` and `DirectSum.Gmodule`, whose axioms are stated up to the `cast` along
`i + j` associativity and commutativity; the private lemmas below discharge them.

## References

* [Stacks Project, Section 15.4](https://stacks.math.columbia.edu/tag/07VD), the paragraph
  preceding Lemma 07VF
-/

@[expose] public section

namespace AssociatedGraded

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The `n`th term `I^n M` of the `I`-adic filtration. -/
def power (I : Ideal A) (n : ℕ) : Submodule A M := I ^ n • ⊤

/-- The zeroth term `I^0 M` of the `I`-adic filtration is all of `M`. -/
@[simp]
theorem power_zero (I : Ideal A) : power (M := M) I 0 = ⊤ := by
  simp [power]

/-- The `I`-adic filtration is decreasing: `I^(n+1) M ⊆ I^n M`. -/
theorem power_succ_le (I : Ideal A) (n : ℕ) :
    power (M := M) I (n + 1) ≤ power I n := by
  rw [power, power, pow_succ', ← Ideal.smul_eq_mul, Submodule.smul_assoc]
  exact Submodule.smul_le_right

/-- For `M = A`, the term `I^n A` of the filtration is the ideal `I^n`. -/
@[simp]
theorem ring_power_eq (I : Ideal A) (n : ℕ) :
    power (M := A) I n = (I ^ n : Submodule A A) := by
  simp [power]

/-- Multiplying an element of `I^i` by an element of `I^j M` gives an element of
`I^(i+j) M`. -/
theorem smul_mem_power (I : Ideal A) {i j : ℕ} {a : A} {m : M}
    (ha : a ∈ power (M := A) I i) (hm : m ∈ power (M := M) I j) :
    a • m ∈ power (M := M) I (i + j) := by
  rw [ring_power_eq] at ha
  rw [power, pow_add, ← Ideal.smul_eq_mul, Submodule.smul_assoc]
  exact Submodule.smul_mem_smul ha hm

/-- The degree `n` part `I^n M/I^(n+1) M` of the associated graded module. -/
abbrev piece (I : Ideal A) (n : ℕ) : Type _ :=
  (power (M := M) I n) ⧸ (power (M := M) I (n + 1)).comap
    (Submodule.subtype (power (M := M) I n))

/-- The associated graded module as a direct sum of its homogeneous parts. -/
abbrev gradedModule (I : Ideal A) (M : Type*) [AddCommGroup M] [Module A M] :=
  DirectSum ℕ (fun n => piece (M := M) I n)

/-- The associated graded ring as a direct sum of its homogeneous parts. -/
abbrev gradedRing (I : Ideal A) := gradedModule I A

/-- Scalar multiplication of homogeneous classes, from degrees `i` and `j` to `i+j`. -/
def homogeneousSMul (I : Ideal A) {i j : ℕ}
    (a : piece (M := A) I i) (m : piece (M := M) I j) :
    piece (M := M) I (i + j) :=
  Quotient.liftOn₂ a m
    (fun a m => Submodule.Quotient.mk
      (⟨(a : A) • (m : M), smul_mem_power I a.property m.property⟩ :
        power (M := M) I (i + j)))
    (by
      intro a₁ m₁ a₂ m₂ ha hm
      have ha' : (a₁ : A) - (a₂ : A) ∈ power (M := A) I (i + 1) := by
        have h := (Submodule.Quotient.eq
          ((power (M := A) I (i + 1)).comap
            (Submodule.subtype (power (M := A) I i)))).mp (Quotient.sound ha)
        exact h
      have hm' : (m₁ : M) - (m₂ : M) ∈ power (M := M) I (j + 1) := by
        have h := (Submodule.Quotient.eq
          ((power (M := M) I (j + 1)).comap
            (Submodule.subtype (power (M := M) I j)))).mp (Quotient.sound hm)
        exact h
      rw [Submodule.Quotient.eq]
      change (a₁ : A) • (m₁ : M) - (a₂ : A) • (m₂ : M) ∈
        power (M := M) I (i + j + 1)
      rw [show (a₁ : A) • (m₁ : M) - (a₂ : A) • (m₂ : M) =
          ((a₁ : A) - (a₂ : A)) • (m₁ : M) +
            (a₂ : A) • ((m₁ : M) - (m₂ : M)) by
        simp [sub_smul, smul_sub]]
      apply Submodule.add_mem
      · simpa only [add_assoc, add_comm, add_left_comm] using
          (smul_mem_power I ha' m₁.property)
      · simpa only [add_assoc, add_comm, add_left_comm] using
          (smul_mem_power I a₂.property hm'))

/-- The canonical class of an element of `I^n M` in the degree `n` piece. -/
def mk (I : Ideal A) (n : ℕ) (m : power (M := M) I n) : piece (M := M) I n :=
  Submodule.Quotient.mk m

/-- **An element of the ideal annihilates every homogeneous class.** The degree `n` piece is
`I^n M / I^(n+1) M` and `I · I^n M ⊆ I^(n+1) M`, so the action of `A` on it factors through
`A ⧸ I`: two scalars with the same image in `A ⧸ I` act alike. -/
theorem smul_eq_zero_of_mem (I : Ideal A) (n : ℕ) {a : A} (ha : a ∈ I)
    (x : piece (M := M) I n) : a • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    rw [← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    show a • (z : M) ∈ power (M := M) I (n + 1)
    have h : a • (z : M) ∈ power (M := M) I (1 + n) :=
      smul_mem_power I (by simpa using ha) z.property
    rwa [Nat.add_comm 1 n] at h

/-- The product of the classes of `a ∈ I^i` and `m ∈ I^j M` is the class of `a • m` in degree
`i + j`. -/
@[simp]
theorem homogeneousSMul_mk (I : Ideal A) {i j : ℕ}
    (a : power (M := A) I i) (m : power (M := M) I j) :
    homogeneousSMul I (mk I i a) (mk I j m) =
      mk I (i + j) ⟨(a : A) • (m : M), smul_mem_power I a.property m.property⟩ :=
  rfl

section Quotient

variable {N : Type*} [AddCommGroup N] [Module A N]

/-- `I^n (N ⧸ R)` is the image of `I^n N` under the quotient map. -/
theorem map_mkQ_power (I : Ideal A) (R : Submodule A N) (n : ℕ) :
    (power (M := N) I n).map R.mkQ = power (M := N ⧸ R) I n := by
  rw [power, power, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

/-- The class modulo `R` of an element of `I^n N` lies in `I^n (N ⧸ R)`. -/
theorem mkQ_mem_power (I : Ideal A) (R : Submodule A N) (n : ℕ) {z : N}
    (hz : z ∈ power (M := N) I n) : R.mkQ z ∈ power (M := N ⧸ R) I n := by
  rw [← map_mkQ_power I R n]
  exact ⟨z, hz, rfl⟩

/-- Every homogeneous class of `Gr_I(N ⧸ R)` is the class of an element of `I^n N`. -/
theorem exists_eq_mk_mkQ (I : Ideal A) (R : Submodule A N) (n : ℕ)
    (x : piece (M := N ⧸ R) I n) :
    ∃ z : power (M := N) I n, x = mk I n ⟨R.mkQ z, mkQ_mem_power I R n z.property⟩ := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z, hz, hzy⟩ : (y : N ⧸ R) ∈ (power (M := N) I n).map R.mkQ := by
    rw [map_mkQ_power I R n]
    exact y.property
  exact ⟨⟨z, hz⟩, by simp only [mk]; congr 1; exact Subtype.ext hzy.symm⟩

end Quotient

/-- The product of homogeneous classes is additive in the ring class. -/
theorem homogeneousSMul_add_left (I : Ideal A) {i j : ℕ}
    (a b : piece (M := A) I i) (m : piece (M := M) I j) :
    homogeneousSMul I (a + b) m = homogeneousSMul I a m + homogeneousSMul I b m := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      induction m using Quotient.inductionOn with
      | _ m =>
        refine (Submodule.Quotient.eq _).2 ?_
        show ((a : A) + (b : A)) • (m : M) -
          ((a : A) • (m : M) + (b : A) • (m : M)) ∈ power (M := M) I (i + j + 1)
        simp [add_smul]

/-- A homogeneous ring class times the zero module class is zero. -/
theorem homogeneousSMul_zero_right (I : Ideal A) {i j : ℕ}
    (a : piece (M := A) I i) :
    homogeneousSMul I a (0 : piece (M := M) I j) = 0 := by
  induction a using Quotient.inductionOn with
  | _ a =>
    show homogeneousSMul I (mk I i a) (mk I j 0) = 0
    rw [homogeneousSMul_mk]
    apply (Submodule.Quotient.mk_eq_zero _).2
    simp

/-- The zero ring class times a homogeneous module class is zero. -/
theorem homogeneousSMul_zero_left (I : Ideal A) {i j : ℕ}
    (m : piece (M := M) I j) :
    homogeneousSMul I (0 : piece (M := A) I i) m = 0 := by
  induction m using Quotient.inductionOn with
  | _ m =>
    show homogeneousSMul I (mk I i 0) (mk I j m) = 0
    rw [homogeneousSMul_mk]
    apply (Submodule.Quotient.mk_eq_zero _).2
    simp

/-- The product of homogeneous classes is additive in the module class. -/
theorem homogeneousSMul_add_right (I : Ideal A) {i j : ℕ}
    (a : piece (M := A) I i) (m₁ m₂ : piece (M := M) I j) :
    homogeneousSMul I a (m₁ + m₂) =
      homogeneousSMul I a m₁ + homogeneousSMul I a m₂ := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction m₁ using Quotient.inductionOn with
    | _ m₁ =>
      induction m₂ using Quotient.inductionOn with
      | _ m₂ =>
        refine (Submodule.Quotient.eq _).2 ?_
        show (a : A) • ((m₁ : M) + (m₂ : M)) -
          ((a : A) • (m₁ : M) + (a : A) • (m₂ : M)) ∈ power (M := M) I (i + j + 1)
        simp [smul_add]

/-- The quotient product is biadditive in each pair of degrees. -/
instance gradedNonUnitalNonAssocRing (I : Ideal A) :
    DirectSum.GNonUnitalNonAssocSemiring (fun n => piece (M := A) I n) where
  mul := homogeneousSMul I
  mul_zero := homogeneousSMul_zero_right I
  zero_mul := homogeneousSMul_zero_left I
  mul_add := homogeneousSMul_add_right I
  add_mul := homogeneousSMul_add_left I

/-- The class of `1` in degree zero. -/
instance gradedGOne (I : Ideal A) :
    GradedMonoid.GOne (fun n => piece (M := A) I n) where
  one := mk I 0 ⟨1, by simp [power]⟩

/-- The degree-indexed scalar action of the associated graded ring on the associated
graded module. -/
instance gradedSMul (I : Ideal A) :
    GradedMonoid.GSMul (fun n => piece (M := A) I n) (fun n => piece (M := M) I n) where
  smul := homogeneousSMul I

private theorem cast_mk (I : Ideal A) {i j : ℕ} (h : i = j)
    (a : power (M := M) I i) (b : power (M := M) I j)
    (hab : (a : M) = (b : M)) :
    cast (congrArg (piece (M := M) I) h) (mk I i a) = mk I j b := by
  subst j
  have : a = b := Subtype.ext hab
  subst b
  rfl

private theorem homogeneousSMul_one (I : Ideal A) {j : ℕ}
    (m : piece (M := M) I j) :
    cast (congrArg (piece (M := M) I) (zero_add j))
      (homogeneousSMul I (GradedMonoid.GOne.one : piece (M := A) I 0) m) = m := by
  induction m using Quotient.inductionOn with
  | _ m =>
    exact cast_mk I (zero_add j) _ m (by simp)

private theorem homogeneousSMul_one_right (I : Ideal A) {i : ℕ}
    (a : piece (M := A) I i) :
    cast (congrArg (piece (M := A) I) (add_zero i))
      (homogeneousSMul I a (GradedMonoid.GOne.one : piece (M := A) I 0)) = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
    exact cast_mk I (add_zero i) _ a (by simp)

private theorem homogeneousSMul_assoc (I : Ideal A) {i j k : ℕ}
    (a : piece (M := A) I i) (b : piece (M := A) I j)
    (m : piece (M := M) I k) :
    cast (congrArg (piece (M := M) I) (add_assoc i j k))
      (homogeneousSMul I (homogeneousSMul I a b) m) =
        homogeneousSMul I a (homogeneousSMul I b m) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      induction m using Quotient.inductionOn with
      | _ m =>
        exact cast_mk I (add_assoc i j k) _ _ (by simp [mul_smul])

private theorem homogeneousSMul_comm (I : Ideal A) {i j : ℕ}
    (a : piece (M := A) I i) (b : piece (M := A) I j) :
    cast (congrArg (piece (M := A) I) (add_comm i j))
      (homogeneousSMul I a b) = homogeneousSMul I b a := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      exact cast_mk I (add_comm i j) _ _ (by simp [mul_comm])

/-- The associated graded ring of the powers of an ideal. -/
instance gradedCommRing (I : Ideal A) :
    DirectSum.GCommRing (fun n => piece (M := A) I n) where
  one_mul := by
    rintro ⟨j, a⟩
    exact Sigma.ext (zero_add j)
      (heq_of_cast_eq (congrArg (piece (M := A) I) (zero_add j))
        (homogeneousSMul_one I a))
  mul_one := by
    rintro ⟨i, a⟩
    exact Sigma.ext (add_zero i)
      (heq_of_cast_eq (congrArg (piece (M := A) I) (add_zero i))
        (homogeneousSMul_one_right I a))
  mul_assoc := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, m⟩
    exact Sigma.ext (add_assoc i j k)
      (heq_of_cast_eq (congrArg (piece (M := A) I) (add_assoc i j k))
        (homogeneousSMul_assoc I a b m))
  mul_comm := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    exact Sigma.ext (add_comm i j)
      (heq_of_cast_eq (congrArg (piece (M := A) I) (add_comm i j))
        (homogeneousSMul_comm I a b))
  natCast n := mk I 0 ⟨(n : A), by simp [power]⟩
  natCast_zero := by
    apply (Submodule.Quotient.mk_eq_zero _).2
    simp
  natCast_succ n := by
    apply (Submodule.Quotient.eq _).2
    change ((n + 1 : ℕ) : A) - ((n : A) + 1) ∈ power (M := A) I 1
    simp
  intCast n := mk I 0 ⟨(n : A), by simp [power]⟩
  intCast_ofNat n := by
    apply (Submodule.Quotient.eq _).2
    change ((n : ℤ) : A) - (n : A) ∈ power (M := A) I 1
    simp
  intCast_negSucc_ofNat n := by
    apply (Submodule.Quotient.eq _).2
    change ((Int.negSucc n : ℤ) : A) - -(↑(n + 1 : ℕ) : A) ∈ power (M := A) I 1
    simp

/-- The scalar action of the associated graded ring on the associated graded module. -/
instance gradedModuleStructure (I : Ideal A) :
    DirectSum.Gmodule (fun n => piece (M := A) I n)
      (fun n => piece (M := M) I n) where
  one_smul := by
    rintro ⟨j, m⟩
    exact Sigma.ext (zero_add j)
      (heq_of_cast_eq (congrArg (piece (M := M) I) (zero_add j))
        (homogeneousSMul_one I m))
  mul_smul := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, m⟩
    exact Sigma.ext (add_assoc i j k)
      (heq_of_cast_eq (congrArg (piece (M := M) I) (add_assoc i j k))
        (homogeneousSMul_assoc I a b m))
  smul_add := homogeneousSMul_add_right I
  smul_zero := homogeneousSMul_zero_right I
  add_smul := homogeneousSMul_add_left I
  zero_smul := homogeneousSMul_zero_left I

/-- Multiplication of homogeneous classes inside the associated graded ring. -/
theorem of_mul_of (I : Ideal A) {i j : ℕ}
    (a : piece (M := A) I i) (b : piece (M := A) I j) :
    DirectSum.of (fun n => piece (M := A) I n) i a *
      DirectSum.of (fun n => piece (M := A) I n) j b =
        DirectSum.of (fun n => piece (M := A) I n) (i + j)
          (homogeneousSMul I a b) :=
  DirectSum.of_mul_of a b

/-- Scalar multiplication of homogeneous classes inside the associated graded module. -/
theorem of_smul_of (I : Ideal A) {i j : ℕ}
    (a : piece (M := A) I i) (m : piece (M := M) I j) :
    DirectSum.of (fun n => piece (M := A) I n) i a •
      DirectSum.of (fun n => piece (M := M) I n) j m =
        DirectSum.of (fun n => piece (M := M) I n) (i + j)
          (homogeneousSMul I a m) :=
  DirectSum.Gmodule.of_smul_of _ _ a m

/-- An isomorphism of associated graded modules over the same associated graded ring.
It preserves homogeneous degrees and commutes with the graded scalar action. -/
structure GradedLinearEquiv (I : Ideal A)
    (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] where
  /-- The underlying linear isomorphism over the associated graded ring. -/
  toLinearEquiv : gradedModule I M ≃ₗ[gradedRing I] gradedModule I N
  /-- A homogeneous class of degree `n` is sent to a homogeneous class of degree `n`. -/
  map_grade : ∀ (n : ℕ) (x : piece (M := M) I n),
    ∃ y : piece (M := N) I n,
      toLinearEquiv (DirectSum.of (fun k => piece (M := M) I k) n x) =
        DirectSum.of (fun k => piece (M := N) I k) n y

/-- A degreewise family of `A`-linear isomorphisms commuting with the action of the homogeneous
classes of `Gr_I(A)` assembles into an isomorphism of associated graded modules. -/
noncomputable def GradedLinearEquiv.ofPieceEquiv (I : Ideal A) {N : Type*}
    [AddCommGroup N] [Module A N]
    (e : ∀ n, piece (M := M) I n ≃ₗ[A] piece (M := N) I n)
    (he : ∀ (i j : ℕ) (a : piece (M := A) I i) (x : piece (M := M) I j),
      e (i + j) (homogeneousSMul I a x) = homogeneousSMul I a (e j x)) :
    GradedLinearEquiv I M N := by
  refine ⟨{ (DirectSum.congrLinearEquiv e).toAddEquiv with map_smul' := ?_ }, ?_⟩
  · intro a m
    change DirectSum.congrLinearEquiv e (a • m) = a • DirectSum.congrLinearEquiv e m
    induction a using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [DirectSum.Gmodule.smul_def, map_add, AddMonoidHom.add_apply]
      exact congrArg₂ (· + ·) ha hb
    | of i a =>
      induction m using DirectSum.induction_on with
      | zero => simp
      | add m m' hm hm' =>
        simp only [DirectSum.Gmodule.smul_def, map_add]
        exact congrArg₂ (· + ·) hm hm'
      | of j m =>
        rw [of_smul_of]
        change DirectSum.congrLinearEquiv e
            (DirectSum.of _ (i + j) (homogeneousSMul I a m)) = _
        simp only [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_of]
        rw [of_smul_of]
        exact congrArg _ (he i j a m)
  · intro n x
    exact ⟨e n x, by simp [DirectSum.coe_congrLinearEquiv]⟩

end AssociatedGraded

end
