module

public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# The associated graded algebra of an ideal, and isomorphisms of such

For an ideal `I` of a commutative ring `A` and a commutative `A`-algebra `M`, the associated
graded module `Gr_I(M) = ⨁_n I^n M / I^(n+1) M` carries, besides the action of `Gr_I(A)` already
supplied by `AssociatedGraded.gradedModuleStructure`, an internal multiplication: the product of
the class of `x ∈ I^i M` and the class of `y ∈ I^j M` is the class of `x y ∈ I^(i+j) M`. For
`M = A ⧸ R` the quotient of `A` by an ideal cutting out a closed subscheme of `Spec(A)` this is
the conormal algebra of that closed subscheme.

This file introduces that multiplication and the notion of an isomorphism of associated graded
algebras, `AssociatedGraded.GradedAlgEquiv`: a degreewise isomorphism of the associated graded
modules respecting the action of `Gr_I(A)`, the internal multiplication, and the unit. Such an
isomorphism is in particular an isomorphism of associated graded modules, by
`AssociatedGraded.GradedAlgEquiv.toGradedLinearEquiv`.

## Main definitions

* `AssociatedGraded.homogeneousMul`: the multiplication of homogeneous classes of `Gr_I(M)`.
* `AssociatedGraded.homogeneousOne`: the class of `1` in degree zero of `Gr_I(M)`.
* `AssociatedGraded.GradedAlgEquiv`: an isomorphism of associated graded algebras.
* `AssociatedGraded.pieceRestrictScalarsEquiv`: the restriction of scalars comparison between the
  graded pieces of a quotient ring taken over the ambient ring and over the quotient.
* `AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv`: an isomorphism of the associated graded
  algebras of two quotients `A ⧸ R` and `A ⧸ R'`, taken over `A`, read as an isomorphism of the
  associated graded algebras of those two rings in their own right.
* `AssociatedGraded.pieceMapOfRingHom` and `AssociatedGraded.pieceEquivOfRingEquiv`: the map,
  resp. the isomorphism, of degree `n` pieces induced by a ring homomorphism, resp. a ring
  isomorphism, carrying one ideal to the other.

## Main results

* `AssociatedGraded.mul_mem_power`: `I^i M · I^j M ⊆ I^(i+j) M`, which makes the multiplication
  well defined.
* `AssociatedGraded.homogeneousMul_eq_homogeneousSMul`: for `M = A` the internal multiplication
  of `Gr_I(A)` is the action `AssociatedGraded.homogeneousSMul` of `Gr_I(A)` on itself.
* `AssociatedGraded.GradedAlgEquiv.toGradedLinearEquiv`: an isomorphism of associated graded
  algebras is an isomorphism of associated graded modules over `Gr_I(A)`.
* `AssociatedGraded.power_quotient_eq_restrictScalars`: `J^n (A ⧸ R)` is the `A`-submodule
  underlying the `n`-th power of the ideal that `J` generates in `A ⧸ R`, which is what makes
  `pieceRestrictScalarsEquiv` an isomorphism.
* `AssociatedGraded.pieceRestrictScalarsEquiv_homogeneousMul` and
  `AssociatedGraded.pieceRestrictScalarsEquiv_homogeneousOne`: that comparison is multiplicative
  and unital, so `Gr_J(A ⧸ R)` as formed over `A` is the associated graded algebra of the ring
  `A ⧸ R` for the ideal `J` generates there.
* `AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv_homogeneousMul`,
  `AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv_homogeneousOne` and
  `AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv_smul_mk`: that reading is multiplicative,
  unital, and linear for the classes of a common element of `A`.
* `AssociatedGraded.pieceEquivOfRingEquiv_smul`,
  `AssociatedGraded.pieceEquivOfRingEquiv_homogeneousMul` and
  `AssociatedGraded.pieceEquivOfRingEquiv_homogeneousOne`: the transport along a ring isomorphism
  is semilinear — the action of `r` becomes the action of `f r` — multiplicative and unital, as
  are its inverse by the three `pieceEquivOfRingEquiv_symm_*` lemmas. These are what identify the
  associated graded algebra of a ring presented as a concrete quotient with that of the quotient.

## Implementation notes

An isomorphism of associated graded algebras is presented degreewise, by the family of its
homogeneous components, rather than as a ring isomorphism of the direct sums. The two carry the
same information, because the multiplication of the direct sum is determined by
`homogeneousMul` on the homogeneous components; the degreewise form is the one the comparisons
of Stacks 07VF produce and the one their consumers use, and it avoids a second
`DirectSum.GCommRing` instance on `fun n => piece (M := A) I n` for `M = A`.

## References

* [Stacks Project, Section 15.4](https://stacks.math.columbia.edu/tag/07VD)
* [Stacks Project, Tag 07VF](https://stacks.math.columbia.edu/tag/07VF)
-/

@[expose] public section

universe u

namespace AssociatedGraded

variable {A : Type u} [CommRing A] {M : Type*} [CommRing M] [Algebra A M]

/-- The product of an element of `I^i M` and an element of `I^j M` lies in `I^(i+j) M`. -/
theorem mul_mem_power (I : Ideal A) {i j : ℕ} {x y : M}
    (hx : x ∈ power (M := M) I i) (hy : y ∈ power (M := M) I j) :
    x * y ∈ power (M := M) I (i + j) := by
  rw [power] at hx hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro b hb n _
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha m _
      have hmul : (a • m) * (b • n) = (a * b) • (m * n) := by
        simp only [Algebra.smul_def, map_mul]
        ring
      rw [hmul, power, pow_add]
      exact Submodule.smul_mem_smul (Ideal.mul_mem_mul ha hb) Submodule.mem_top
    · intro u v hu hv
      rw [add_mul]
      exact Submodule.add_mem _ hu hv
  · intro u v hu hv
    rw [mul_add]
    exact Submodule.add_mem _ hu hv

/-- Multiplication of homogeneous classes of the associated graded algebra of an `A`-algebra `M`,
from degrees `i` and `j` to `i + j`. -/
def homogeneousMul (I : Ideal A) {i j : ℕ}
    (x : piece (M := M) I i) (y : piece (M := M) I j) :
    piece (M := M) I (i + j) :=
  Quotient.liftOn₂ x y
    (fun a b => Submodule.Quotient.mk
      (⟨(a : M) * (b : M), mul_mem_power I a.property b.property⟩ :
        power (M := M) I (i + j)))
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      have ha' : (a₁ : M) - (a₂ : M) ∈ power (M := M) I (i + 1) :=
        (Submodule.Quotient.eq
          ((power (M := M) I (i + 1)).comap
            (Submodule.subtype (power (M := M) I i)))).mp (Quotient.sound ha)
      have hb' : (b₁ : M) - (b₂ : M) ∈ power (M := M) I (j + 1) :=
        (Submodule.Quotient.eq
          ((power (M := M) I (j + 1)).comap
            (Submodule.subtype (power (M := M) I j)))).mp (Quotient.sound hb)
      rw [Submodule.Quotient.eq]
      change (a₁ : M) * (b₁ : M) - (a₂ : M) * (b₂ : M) ∈ power (M := M) I (i + j + 1)
      rw [show (a₁ : M) * (b₁ : M) - (a₂ : M) * (b₂ : M) =
          ((a₁ : M) - (a₂ : M)) * (b₁ : M) + (a₂ : M) * ((b₁ : M) - (b₂ : M)) by ring]
      refine Submodule.add_mem _ ?_ ?_
      · simpa only [add_right_comm] using mul_mem_power I ha' b₁.property
      · simpa only [← add_assoc] using mul_mem_power I a₂.property hb')

/-- The product of the classes of `a ∈ I^i M` and `b ∈ I^j M` is the class of `a * b` in degree
`i + j`. -/
@[simp]
theorem homogeneousMul_mk (I : Ideal A) {i j : ℕ}
    (a : power (M := M) I i) (b : power (M := M) I j) :
    homogeneousMul I (mk I i a) (mk I j b) =
      mk I (i + j) ⟨(a : M) * (b : M), mul_mem_power I a.property b.property⟩ :=
  rfl

/-- **For `M = A` the internal multiplication of `Gr_I(A)` is the action of `Gr_I(A)` on
itself.** The two are the same operation: `homogeneousSMul` multiplies representatives with the
scalar action of `A` on itself and `homogeneousMul` with the ring multiplication. This is what
lets a comparison stated with `homogeneousMul`, as `GradedAlgEquiv` states it, be used against
one stated with `homogeneousSMul`, as the affine-local descriptions of a conormal algebra state
it. -/
@[simp]
theorem homogeneousMul_eq_homogeneousSMul (I : Ideal A) {i j : ℕ}
    (x : piece (M := A) I i) (y : piece (M := A) I j) :
    homogeneousMul I x y = homogeneousSMul I x y :=
  rfl

/-- The class of `1` in degree zero of the associated graded algebra of an `A`-algebra `M`. -/
def homogeneousOne (I : Ideal A) : piece (M := M) I 0 :=
  mk I 0 ⟨1, by rw [power_zero]; trivial⟩

/-- An isomorphism of associated graded algebras over the same associated graded ring: a
degreewise isomorphism of the associated graded modules of two commutative `A`-algebras which
respects the action of `Gr_I(A)`, the internal multiplication of `Gr_I(-)`, and its unit. -/
structure GradedAlgEquiv (I : Ideal A) (M N : Type*)
    [CommRing M] [Algebra A M] [CommRing N] [Algebra A N] where
  /-- The degree `n` component of the isomorphism. -/
  toPieceEquiv (n : ℕ) : piece (M := M) I n ≃ₗ[A] piece (M := N) I n
  /-- The isomorphism commutes with the action of the homogeneous classes of `Gr_I(A)`. -/
  map_homogeneousSMul (i j : ℕ) (a : piece (M := A) I i) (x : piece (M := M) I j) :
    toPieceEquiv (i + j) (homogeneousSMul I a x) = homogeneousSMul I a (toPieceEquiv j x)
  /-- The isomorphism is multiplicative. -/
  map_homogeneousMul (i j : ℕ) (x : piece (M := M) I i) (y : piece (M := M) I j) :
    toPieceEquiv (i + j) (homogeneousMul I x y) =
      homogeneousMul I (toPieceEquiv i x) (toPieceEquiv j y)
  /-- The isomorphism carries the unit to the unit. -/
  map_homogeneousOne : toPieceEquiv 0 (homogeneousOne I) = homogeneousOne I

variable {N : Type*} [CommRing N] [Algebra A N]

/-- An isomorphism of associated graded algebras is an isomorphism of associated graded modules
over `Gr_I(A)`. -/
noncomputable def GradedAlgEquiv.toGradedLinearEquiv {I : Ideal A}
    (e : GradedAlgEquiv I M N) : GradedLinearEquiv I M N :=
  GradedLinearEquiv.ofPieceEquiv I e.toPieceEquiv e.map_homogeneousSMul

/-! ### Restriction of scalars along a quotient

The graded pieces of a quotient ring `A ⧸ R` are formed above over the *ambient* ring `A`, for
the `J`-adic filtration `power (M := A ⧸ R) J n = J^n (A ⧸ R)`. The associated graded algebra of
`A ⧸ R` in its own right — the conormal algebra of the closed subscheme of `Spec(A ⧸ R)` cut out
by `J`, say — is instead formed over `A ⧸ R`, for the powers of the ideal `J` generates there.
The two agree: `J^n (A ⧸ R)` is the `A`-submodule underlying the ideal
`(J (A ⧸ R))^n = (J.map (Ideal.Quotient.mk R))^n`. -/

/-- The `n`-th term of the `J`-adic filtration of `A ⧸ R` taken over the ambient ring `A` is the
restriction of scalars of the `n`-th power of the ideal that `J` generates in `A ⧸ R`. -/
theorem power_quotient_eq_restrictScalars (J R : Ideal A) (n : ℕ) :
    power (M := A ⧸ R) J n =
      Submodule.restrictScalars A (power (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n) := by
  rw [ring_power_eq, power, Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq, Ideal.map_pow]

/-- Membership in the `n`-th term of the `J`-adic filtration of `A ⧸ R` does not depend on
whether the filtration is taken over `A` or over `A ⧸ R`. -/
theorem mem_power_map_iff (J R : Ideal A) (n : ℕ) {x : A ⧸ R} :
    x ∈ power (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n ↔ x ∈ power (M := A ⧸ R) J n := by
  rw [power_quotient_eq_restrictScalars J R n]
  exact Iff.rfl

/-- The identity of `A ⧸ R`, as a map from the `n`-th term of the `J`-adic filtration taken over
`A` to the degree `n` piece taken over `A ⧸ R`. -/
noncomputable def pieceRestrictScalarsAux (J R : Ideal A) (n : ℕ) :
    power (M := A ⧸ R) J n →ₗ[A]
      piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n where
  toFun z := mk _ n ⟨(z : A ⧸ R), (mem_power_map_iff J R n).2 z.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity of `A ⧸ R`, as a map from the degree `n` piece of the `J`-adic filtration
taken over `A` to the degree `n` piece taken over `A ⧸ R`. -/
noncomputable def pieceRestrictScalars (J R : Ideal A) (n : ℕ) :
    piece (M := A ⧸ R) J n →ₗ[A]
      piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n :=
  Submodule.liftQ ((power (M := A ⧸ R) J (n + 1)).comap (power (M := A ⧸ R) J n).subtype)
    (pieceRestrictScalarsAux J R n)
    (fun _z hz => (Submodule.Quotient.mk_eq_zero _).2
      ((mem_power_map_iff J R (n + 1)).2 hz))

/-- `pieceRestrictScalars` is injective: the two denominators also agree. -/
theorem pieceRestrictScalars_injective (J R : Ideal A) (n : ℕ) :
    Function.Injective (pieceRestrictScalars J R n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : (Submodule.Quotient.mk
      ⟨(z : A ⧸ R), (mem_power_map_iff J R n).2 z.property⟩ :
      piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n) = 0 := hx
  refine (Submodule.Quotient.mk_eq_zero
    ((power (M := A ⧸ R) J (n + 1)).comap (power (M := A ⧸ R) J n).subtype)).2 ?_
  refine (mem_power_map_iff J R (n + 1)).1 ?_
  exact (Submodule.Quotient.mk_eq_zero
    ((power (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) (n + 1)).comap
      (power (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n).subtype)).1 hx'

/-- `pieceRestrictScalars` is surjective: the two numerators agree. -/
theorem pieceRestrictScalars_surjective (J R : Ideal A) (n : ℕ) :
    Function.Surjective (pieceRestrictScalars J R n) := by
  intro y
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk ⟨(w : A ⧸ R), (mem_power_map_iff J R n).1 w.property⟩, rfl⟩

/-- **Restriction of scalars along a quotient, degreewise.** The degree `n` piece of the
associated graded module of `A ⧸ R` for the `J`-adic filtration taken over the ambient ring `A`
is the degree `n` piece of the associated graded algebra of the ring `A ⧸ R` for the ideal that
`J` generates there. The comparison is induced by the identity of `A ⧸ R`, and is multiplicative
and unital by `pieceRestrictScalarsEquiv_homogeneousMul` and
`pieceRestrictScalarsEquiv_homogeneousOne`. -/
noncomputable def pieceRestrictScalarsEquiv (J R : Ideal A) (n : ℕ) :
    piece (M := A ⧸ R) J n ≃ₗ[A]
      piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n :=
  LinearEquiv.ofBijective (pieceRestrictScalars J R n)
    ⟨pieceRestrictScalars_injective J R n, pieceRestrictScalars_surjective J R n⟩

/-- `pieceRestrictScalarsEquiv` sends the class of `z` to the class of the same element of
`A ⧸ R`. -/
@[simp]
theorem pieceRestrictScalarsEquiv_mk (J R : Ideal A) (n : ℕ) (z : power (M := A ⧸ R) J n) :
    pieceRestrictScalarsEquiv J R n (mk J n z) =
      mk (J.map (Ideal.Quotient.mk R)) n
        ⟨(z : A ⧸ R), (mem_power_map_iff J R n).2 z.property⟩ :=
  rfl

/-- The inverse of `pieceRestrictScalarsEquiv` sends the class of `z` to the class of the same
element of `A ⧸ R`. -/
@[simp]
theorem pieceRestrictScalarsEquiv_symm_mk (J R : Ideal A) (n : ℕ)
    (z : power (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n) :
    (pieceRestrictScalarsEquiv J R n).symm (mk (J.map (Ideal.Quotient.mk R)) n z) =
      mk J n ⟨(z : A ⧸ R), (mem_power_map_iff J R n).1 z.property⟩ :=
  (pieceRestrictScalarsEquiv J R n).symm_apply_eq.2 rfl

/-- The restriction of scalars comparison is multiplicative. -/
theorem pieceRestrictScalarsEquiv_homogeneousMul (J R : Ideal A) (i j : ℕ)
    (x : piece (M := A ⧸ R) J i) (y : piece (M := A ⧸ R) J j) :
    pieceRestrictScalarsEquiv J R (i + j) (homogeneousMul J x y) =
      homogeneousMul (J.map (Ideal.Quotient.mk R))
        (pieceRestrictScalarsEquiv J R i x) (pieceRestrictScalarsEquiv J R j y) := by
  induction x using Quotient.inductionOn with
  | _ z =>
    induction y using Quotient.inductionOn with
    | _ w => rfl

/-- The restriction of scalars comparison is unital. -/
theorem pieceRestrictScalarsEquiv_homogeneousOne (J R : Ideal A) :
    pieceRestrictScalarsEquiv J R 0 (homogeneousOne J) =
      homogeneousOne (J.map (Ideal.Quotient.mk R)) :=
  rfl

/-- The inverse of the restriction of scalars comparison is multiplicative. -/
theorem pieceRestrictScalarsEquiv_symm_homogeneousMul (J R : Ideal A) (i j : ℕ)
    (x : piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) i)
    (y : piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) j) :
    (pieceRestrictScalarsEquiv J R (i + j)).symm
        (homogeneousMul (J.map (Ideal.Quotient.mk R)) x y) =
      homogeneousMul J ((pieceRestrictScalarsEquiv J R i).symm x)
        ((pieceRestrictScalarsEquiv J R j).symm y) := by
  refine (pieceRestrictScalarsEquiv J R (i + j)).symm_apply_eq.2 ?_
  rw [pieceRestrictScalarsEquiv_homogeneousMul, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- The inverse of the restriction of scalars comparison is unital. -/
theorem pieceRestrictScalarsEquiv_symm_homogeneousOne (J R : Ideal A) :
    (pieceRestrictScalarsEquiv J R 0).symm (homogeneousOne (J.map (Ideal.Quotient.mk R))) =
      homogeneousOne J :=
  (pieceRestrictScalarsEquiv J R 0).symm_apply_eq.2
    (pieceRestrictScalarsEquiv_homogeneousOne J R).symm

/-! ### Two quotients of `A`, compared in their own associated graded algebras

An `AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ R')` compares the associated graded modules of
the two quotient rings for the `J`-adic filtration taken over the *ambient* ring `A`. Conjugating
it with `pieceRestrictScalarsEquiv` on both sides reads it as a comparison of the associated
graded algebras of the two rings `A ⧸ R` and `A ⧸ R'` in their own right, for the ideals that `J`
generates in each — which is the form in which the associated graded algebra of a quotient ring
is the conormal algebra of the closed subscheme of its spectrum cut out by that ideal. -/

variable {R R' : Ideal A}

/-- **A comparison of the associated graded algebras of two quotients of `A`, read in the
quotient rings' own graded algebras.** The degree `n` component of `e`, conjugated with the
restriction of scalars comparison `pieceRestrictScalarsEquiv` on both sides. It stays `A`-linear,
and is multiplicative and unital by `GradedAlgEquiv.quotientPieceEquiv_homogeneousMul` and
`GradedAlgEquiv.quotientPieceEquiv_homogeneousOne`. -/
noncomputable def GradedAlgEquiv.quotientPieceEquiv {J : Ideal A}
    (e : GradedAlgEquiv J (A ⧸ R) (A ⧸ R')) (n : ℕ) :
    piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n ≃ₗ[A]
      piece (M := A ⧸ R') (J.map (Ideal.Quotient.mk R')) n :=
  ((pieceRestrictScalarsEquiv J R n).symm.trans (e.toPieceEquiv n)).trans
    (pieceRestrictScalarsEquiv J R' n)

/-- The quotient-ring reading of a comparison of associated graded algebras is multiplicative. -/
theorem GradedAlgEquiv.quotientPieceEquiv_homogeneousMul {J : Ideal A}
    (e : GradedAlgEquiv J (A ⧸ R) (A ⧸ R')) (i j : ℕ)
    (x : piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) i)
    (y : piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) j) :
    e.quotientPieceEquiv (i + j) (homogeneousMul (J.map (Ideal.Quotient.mk R)) x y) =
      homogeneousMul (J.map (Ideal.Quotient.mk R'))
        (e.quotientPieceEquiv i x) (e.quotientPieceEquiv j y) := by
  show pieceRestrictScalarsEquiv J R' (i + j) (e.toPieceEquiv (i + j)
      ((pieceRestrictScalarsEquiv J R (i + j)).symm
        (homogeneousMul (J.map (Ideal.Quotient.mk R)) x y))) = _
  rw [pieceRestrictScalarsEquiv_symm_homogeneousMul, e.map_homogeneousMul,
    pieceRestrictScalarsEquiv_homogeneousMul]
  rfl

/-- The quotient-ring reading of a comparison of associated graded algebras is unital. -/
theorem GradedAlgEquiv.quotientPieceEquiv_homogeneousOne {J : Ideal A}
    (e : GradedAlgEquiv J (A ⧸ R) (A ⧸ R')) :
    e.quotientPieceEquiv 0 (homogeneousOne (J.map (Ideal.Quotient.mk R))) =
      homogeneousOne (J.map (Ideal.Quotient.mk R')) := by
  show pieceRestrictScalarsEquiv J R' 0 (e.toPieceEquiv 0
      ((pieceRestrictScalarsEquiv J R 0).symm
        (homogeneousOne (J.map (Ideal.Quotient.mk R))))) = _
  rw [pieceRestrictScalarsEquiv_symm_homogeneousOne, e.map_homogeneousOne,
    pieceRestrictScalarsEquiv_homogeneousOne]

/-- The quotient-ring reading of a comparison of associated graded algebras is linear for the
classes of a common element of `A`: two scalars which lift to the same element of the ambient ring
act alike. -/
theorem GradedAlgEquiv.quotientPieceEquiv_smul_mk {J : Ideal A}
    (e : GradedAlgEquiv J (A ⧸ R) (A ⧸ R')) (n : ℕ) (a : A)
    (x : piece (M := A ⧸ R) (J.map (Ideal.Quotient.mk R)) n) :
    e.quotientPieceEquiv n ((Ideal.Quotient.mk R a) • x) =
      (Ideal.Quotient.mk R' a) • e.quotientPieceEquiv n x := by
  rw [show (Ideal.Quotient.mk R a) • x = a • x from
      (algebraMap_smul (A ⧸ R) a x).symm,
    (e.quotientPieceEquiv n).map_smul,
    show (Ideal.Quotient.mk R' a) • e.quotientPieceEquiv n x =
      a • e.quotientPieceEquiv n x from (algebraMap_smul (A ⧸ R') a _).symm]

/-! ### Comparisons induced by the identity of the ambient ring

The comparison of associated graded algebras that Stacks 07VF produces is *induced by the
identity of the ambient ring* `A`: it carries the class of `z ∈ J^n` modulo `R` to the class of
the same `z` modulo `R'`. That is more than a `GradedAlgEquiv` records, and it is what makes a
family of such comparisons over different ambient presentations compatible with each other: a
ring map between two ambient presentations carries a lift on one side to a lift on the other. -/

/-- The class modulo `R` of an element of `J^n` lies in the `n`-th term of the `J`-adic
filtration of `A ⧸ R` taken over `A`. -/
theorem mk_mem_power_quotient (J R : Ideal A) (n : ℕ) {z : A} (hz : z ∈ power (M := A) J n) :
    Ideal.Quotient.mk R z ∈ power (M := A ⧸ R) J n :=
  mkQ_mem_power J R n hz

/-- **A comparison of the associated graded algebras of two quotients of `A` is induced by the
identity of `A`** when it carries the class of `z ∈ J^n` modulo `R` to the class of the same `z`
modulo `R'`. Every homogeneous class is of that form, by `AssociatedGraded.exists_eq_mk_mkQ`, so
this determines the comparison; it is a property of the comparison and not of its type, and it is
the property the comparison of Stacks 07VF has. -/
def GradedAlgEquiv.IsInducedByIdentity {J : Ideal A} (e : GradedAlgEquiv J (A ⧸ R) (A ⧸ R')) :
    Prop :=
  ∀ (n : ℕ) (z : power (M := A) J n),
    e.toPieceEquiv n (_root_.AssociatedGraded.mk J n
        ⟨Ideal.Quotient.mk R (z : A), mk_mem_power_quotient J R n z.property⟩) =
      _root_.AssociatedGraded.mk J n
        ⟨Ideal.Quotient.mk R' (z : A), mk_mem_power_quotient J R' n z.property⟩

/-- **The quotient-ring reading of a comparison induced by the identity is induced by the
identity**: on the class of a lift `z ∈ J^n` to the ambient ring it is again the class of `z`.
This is the form in which a chart-local presentation consumes the comparison. -/
theorem GradedAlgEquiv.quotientPieceEquiv_mk_of_isInducedByIdentity {J : Ideal A}
    (e : GradedAlgEquiv J (A ⧸ R) (A ⧸ R')) (he : e.IsInducedByIdentity) (n : ℕ)
    (z : power (M := A) J n) :
    e.quotientPieceEquiv n (_root_.AssociatedGraded.mk (J.map (Ideal.Quotient.mk R)) n
        ⟨Ideal.Quotient.mk R (z : A),
          (mem_power_map_iff J R n).2 (mk_mem_power_quotient J R n z.property)⟩) =
      _root_.AssociatedGraded.mk (J.map (Ideal.Quotient.mk R')) n
        ⟨Ideal.Quotient.mk R' (z : A),
          (mem_power_map_iff J R' n).2 (mk_mem_power_quotient J R' n z.property)⟩ := by
  show pieceRestrictScalarsEquiv J R' n (e.toPieceEquiv n
      ((pieceRestrictScalarsEquiv J R n).symm
        (_root_.AssociatedGraded.mk (J.map (Ideal.Quotient.mk R)) n _))) = _
  rw [pieceRestrictScalarsEquiv_symm_mk, he n z, pieceRestrictScalarsEquiv_mk]

/-! ### Transport along a ring isomorphism

The associated graded algebra of a ring for an ideal of itself depends on the pair only up to
isomorphism: a ring isomorphism `f : A ≃+* B` carrying `I` to `I'` carries `I^n` to `I'^n`, hence
the degree `n` piece of `Gr_I(A)` to the degree `n` piece of `Gr_{I'}(B)`. The comparison is
additive, multiplicative, unital, and semilinear — the action of `r : A` becomes the action of
`f r`. This is what identifies the associated graded algebra of a ring presented as a concrete
quotient with the associated graded algebra of that quotient. -/

section RingTransport

variable {B : Type*} [CommRing B]

/-- A ring homomorphism carrying `I` into `I'` carries the `n`-th term `I^n` of the filtration of
`A` into the `n`-th term `I'^n` of the filtration of `B`. Only an inclusion of ideals is needed,
which is what a comparison of two *different* ambient presentations provides. -/
theorem map_mem_power_of_map_le (f : A →+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map f ≤ I') (n : ℕ) {x : A} (hx : x ∈ power (M := A) I n) :
    f x ∈ power (M := B) I' n := by
  rw [ring_power_eq] at hx
  rw [ring_power_eq]
  refine Ideal.pow_right_mono hI n ?_
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem f hx


/-- The inverse of a ring isomorphism carrying `I` to `I'` carries `I'` back to `I`. -/
theorem map_symm_eq_of_map_eq (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') : I'.map (f.symm : B →+* A) = I := by
  have h : ((f.symm : B →+* A).comp (f : A →+* B)) = RingHom.id A :=
    RingHom.ext fun x => f.symm_apply_apply x
  rw [← hI, Ideal.map_map, h, Ideal.map_id]

/-- **The map of degree `n` pieces induced by a ring homomorphism carrying `I` to `I'`.** It is
induced by `f` on representatives, and is well defined because `f` also carries `I^(n+1)` into
`I'^(n+1)`. -/
def pieceMapOfRingHom (f : A →+* B) {I : Ideal A} {I' : Ideal B} (hI : I.map f ≤ I') (n : ℕ) :
    piece (M := A) I n →+ piece (M := B) I' n where
  toFun x := Quotient.liftOn x
    (fun a => mk I' n ⟨f (a : A), map_mem_power_of_map_le f hI n a.property⟩)
    (fun a b hab => by
      have hab' : (a : A) - (b : A) ∈ power (M := A) I (n + 1) :=
        (Submodule.Quotient.eq ((power (M := A) I (n + 1)).comap
          (Submodule.subtype (power (M := A) I n)))).mp (Quotient.sound hab)
      refine (Submodule.Quotient.eq _).2 ?_
      change f (a : A) - f (b : A) ∈ power (M := B) I' (n + 1)
      rw [← map_sub]
      exact map_mem_power_of_map_le f hI (n + 1) hab')
  map_zero' := by
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change f (0 : A) ∈ power (M := B) I' (n + 1)
    rw [map_zero]
    exact zero_mem _
  map_add' x y := by
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        refine (Submodule.Quotient.eq _).2 ?_
        change f ((a : A) + (b : A)) - (f (a : A) + f (b : A)) ∈ power (M := B) I' (n + 1)
        rw [map_add, sub_self]
        exact zero_mem _

/-- `pieceMapOfRingHom f hI n` sends the class of `a` to the class of `f a`. -/
@[simp]
theorem pieceMapOfRingHom_mk (f : A →+* B) {I : Ideal A} {I' : Ideal B} (hI : I.map f ≤ I')
    (n : ℕ) (a : power (M := A) I n) :
    pieceMapOfRingHom f hI n (mk I n a) =
      mk I' n ⟨f (a : A), map_mem_power_of_map_le f hI n a.property⟩ :=
  rfl

/-- Classes of equal elements of `I^n M` are equal. -/
private theorem mk_congr (I : Ideal A) (n : ℕ) {x y : power (M := M) I n} (h : (x : M) = y) :
    mk I n x = mk I n y :=
  congrArg _ (Subtype.ext h)

/-- The induced map on pieces is semilinear: the action of `r` becomes the action of `f r`. -/
theorem pieceMapOfRingHom_smul (f : A →+* B) {I : Ideal A} {I' : Ideal B} (hI : I.map f ≤ I')
    (n : ℕ) (r : A) (x : piece (M := A) I n) :
    pieceMapOfRingHom f hI n (r • x) = f r • pieceMapOfRingHom f hI n x := by
  induction x using Quotient.inductionOn with
  | _ a => exact mk_congr _ _ (map_mul f r (a : A))

/-- The induced map on pieces is multiplicative. -/
theorem pieceMapOfRingHom_homogeneousMul (f : A →+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map f ≤ I') (i j : ℕ) (x : piece (M := A) I i) (y : piece (M := A) I j) :
    pieceMapOfRingHom f hI (i + j) (homogeneousMul I x y) =
      homogeneousMul I' (pieceMapOfRingHom f hI i x) (pieceMapOfRingHom f hI j y) := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact mk_congr _ _ (map_mul f (a : A) (b : A))

/-- The induced map on pieces is unital. -/
theorem pieceMapOfRingHom_homogeneousOne (f : A →+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map f ≤ I') :
    pieceMapOfRingHom f hI 0 (homogeneousOne I) = homogeneousOne I' := by
  exact mk_congr _ _ (map_one f)

/-- **Transport of the degree `n` piece of an associated graded algebra along a ring
isomorphism** carrying the one ideal to the other. It is multiplicative, unital and semilinear by
`pieceEquivOfRingEquiv_homogeneousMul`, `pieceEquivOfRingEquiv_homogeneousOne` and
`pieceEquivOfRingEquiv_smul`. -/
def pieceEquivOfRingEquiv (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') (n : ℕ) :
    piece (M := A) I n ≃+ piece (M := B) I' n where
  toFun := pieceMapOfRingHom (f : A →+* B) hI.le n
  invFun := pieceMapOfRingHom (f.symm : B →+* A) (map_symm_eq_of_map_eq f hI).le n
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ a =>
      refine (Submodule.Quotient.eq _).2 ?_
      change f.symm (f (a : A)) - (a : A) ∈ power (M := A) I (n + 1)
      rw [f.symm_apply_apply, sub_self]
      exact zero_mem _
  right_inv y := by
    induction y using Quotient.inductionOn with
    | _ b =>
      refine (Submodule.Quotient.eq _).2 ?_
      change f (f.symm (b : B)) - (b : B) ∈ power (M := B) I' (n + 1)
      rw [f.apply_symm_apply, sub_self]
      exact zero_mem _
  map_add' := (pieceMapOfRingHom (f : A →+* B) hI.le n).map_add

/-- `pieceEquivOfRingEquiv f hI n` sends the class of `a` to the class of `f a`. -/
@[simp]
theorem pieceEquivOfRingEquiv_mk (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') (n : ℕ) (a : power (M := A) I n) :
    pieceEquivOfRingEquiv f hI n (mk I n a) =
      mk I' n ⟨f (a : A), map_mem_power_of_map_le (f : A →+* B) hI.le n a.property⟩ :=
  rfl

/-- The inverse of `pieceEquivOfRingEquiv f hI n` sends the class of `b` to the class of
`f.symm b`. -/
@[simp]
theorem pieceEquivOfRingEquiv_symm_mk (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') (n : ℕ) (b : power (M := B) I' n) :
    (pieceEquivOfRingEquiv f hI n).symm (mk I' n b) =
      mk I n ⟨f.symm (b : B),
        map_mem_power_of_map_le (f.symm : B →+* A) (map_symm_eq_of_map_eq f hI).le n b.property⟩ :=
  rfl

/-- The transport along a ring isomorphism is semilinear. -/
theorem pieceEquivOfRingEquiv_smul (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') (n : ℕ) (r : A) (x : piece (M := A) I n) :
    pieceEquivOfRingEquiv f hI n (r • x) = f r • pieceEquivOfRingEquiv f hI n x :=
  pieceMapOfRingHom_smul (f : A →+* B) hI.le n r x

/-- The transport along a ring isomorphism is multiplicative. -/
theorem pieceEquivOfRingEquiv_homogeneousMul (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') (i j : ℕ)
    (x : piece (M := A) I i) (y : piece (M := A) I j) :
    pieceEquivOfRingEquiv f hI (i + j) (homogeneousMul I x y) =
      homogeneousMul I' (pieceEquivOfRingEquiv f hI i x) (pieceEquivOfRingEquiv f hI j y) :=
  pieceMapOfRingHom_homogeneousMul (f : A →+* B) hI.le i j x y

/-- The transport along a ring isomorphism is unital. -/
theorem pieceEquivOfRingEquiv_homogeneousOne (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') :
    pieceEquivOfRingEquiv f hI 0 (homogeneousOne I) = homogeneousOne I' :=
  pieceMapOfRingHom_homogeneousOne (f : A →+* B) hI.le

/-- The inverse transport is semilinear for the inverse isomorphism. -/
theorem pieceEquivOfRingEquiv_symm_smul (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') (n : ℕ) (b : B) (y : piece (M := B) I' n) :
    (pieceEquivOfRingEquiv f hI n).symm (b • y) =
      f.symm b • (pieceEquivOfRingEquiv f hI n).symm y :=
  pieceMapOfRingHom_smul (f.symm : B →+* A) (map_symm_eq_of_map_eq f hI).le n b y

/-- The inverse transport is multiplicative. -/
theorem pieceEquivOfRingEquiv_symm_homogeneousMul (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') (i j : ℕ)
    (x : piece (M := B) I' i) (y : piece (M := B) I' j) :
    (pieceEquivOfRingEquiv f hI (i + j)).symm (homogeneousMul I' x y) =
      homogeneousMul I ((pieceEquivOfRingEquiv f hI i).symm x)
        ((pieceEquivOfRingEquiv f hI j).symm y) :=
  pieceMapOfRingHom_homogeneousMul (f.symm : B →+* A) (map_symm_eq_of_map_eq f hI).le i j x y

/-- The inverse transport is unital. -/
theorem pieceEquivOfRingEquiv_symm_homogeneousOne (f : A ≃+* B) {I : Ideal A} {I' : Ideal B}
    (hI : I.map (f : A →+* B) = I') :
    (pieceEquivOfRingEquiv f hI 0).symm (homogeneousOne I') = homogeneousOne I :=
  pieceMapOfRingHom_homogeneousOne (f.symm : B →+* A) (map_symm_eq_of_map_eq f hI).le

end RingTransport

end AssociatedGraded

end
