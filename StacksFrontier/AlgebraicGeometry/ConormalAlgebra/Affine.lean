module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# The affine local model of the conormal algebra

Let `i : Z ⟶ X` be a closed immersion of affine schemes, say `Spec S ⟶ Spec R` with
`R ⟶ S` surjective with kernel `I`.  The conormal algebra of `i` is the graded
`S`-algebra `⨁ₙ Iⁿ/Iⁿ⁺¹`, and its degree-`n` piece is the pullback of the quasi-coherent
sheaf `Iⁿ` along `i`.  This file proves the ring-theoretic content of that statement:
the base change of `Iⁿ` along `R ⟶ R/I` is `Iⁿ/Iⁿ⁺¹`, canonically, and the resulting
identification is multiplicative and unital for the multiplication of the associated graded
ring of `I`.

Everything here is stated for an arbitrary ideal `I` of a commutative ring `R`, with a second
set of statements for a surjective algebra map, which is the form in which a chart of a closed
immersion presents its ideal (as `RingHom.ker` of the map on sections).

## Main definitions

* `Stacks.Conormal.powEquivPower`: `Iⁿ`, as a submodule of `R`, is the degree-`n` term
  `AssociatedGraded.power I n` of the `I`-adic filtration.
* `Stacks.Conormal.toPiece`: the canonical `R`-linear surjection `Iⁿ → Iⁿ/Iⁿ⁺¹`.
* `Stacks.Conormal.quotTensorPowEquivPiece`: the canonical identification
  `(R ⧸ I) ⊗[R] Iⁿ ≃ Iⁿ/Iⁿ⁺¹`.
* `Stacks.Conormal.surjectiveTensorPowEquivPiece`: the same identification written with the
  base change to an `R`-algebra `S` whose structure map is surjective, so that
  `I = RingHom.ker (algebraMap R S)`.

## Main results

* `Stacks.Conormal.toPiece_eq_zero_iff`, `Stacks.Conormal.toPiece_surjective` and
  `Stacks.Conormal.ker_toPiece`: the quotient presentation of the degree-`n` piece.
* `Stacks.Conormal.toPiece_mul` and `Stacks.Conormal.toPiece_one`: the presentation is
  multiplicative for `AssociatedGraded.homogeneousSMul`, and the class of `1` in degree `0`
  is the unit.
* `Stacks.Conormal.one_tmul_eq_zero_iff` and `Stacks.Conormal.one_tmul_surjective`: an element
  `a` of `Iⁿ` has `1 ⊗ₜ a = 0` in `(R ⧸ I) ⊗[R] Iⁿ` exactly when `a ∈ Iⁿ⁺¹`, and every element
  of the base change is of the form `1 ⊗ₜ a`.
* `Stacks.Conormal.surjective_one_tmul_eq_zero_iff` and
  `Stacks.Conormal.surjective_one_tmul_surjective`: the same two statements over a surjective
  algebra map.

## Implementation notes

`AssociatedGraded.power I n` is `I ^ n • ⊤` as a submodule of `R`, which is `I ^ n` but not
syntactically so;  `powEquivPower` is the (identity on carriers) linear equivalence between the
two spellings, and it is what lets the `AssociatedGraded` multiplication be used on quotients
of `↥(I ^ n)`.  The degree-`n` piece is formed inside the subtype `↥(I ^ n)` with denominator
the *preimage* of `I ^ (n + 1)`, as in `AssociatedGraded.piece`, so no choice of
representatives is needed anywhere.

The base-change identification is Mathlib's `TensorProduct.quotTensorEquivQuotSMul` together
with `Stacks.Conormal.smul_top_eq_comap`, which says that the submodule `I • ⊤` of `↥(I ^ n)`
is the preimage of `I ^ (n + 1)`.  That is the only place where `pow_succ'` — i.e.
`I ^ (n + 1) = I * I ^ n` rather than `I ^ n * I` — is used, and it is what makes the
identification `R`-linear on the nose rather than only up to the commutativity isomorphism.

The surjective-algebra-map versions are deduced from the `R ⧸ I` versions along
`Stacks.Conormal.quotKerLinearEquiv`, so they assert the same mathematics;  they are stated
separately because a closed immersion of affine schemes presents its ideal as a `RingHom.ker`
and not as an abstract ideal with a quotient.  That identification is built by hand from
`Submodule.liftQ` rather than taken from `Ideal.quotientKerAlgEquivOfSurjective`:  the latter
is indexed by an `AlgHom`, so using it for `Algebra.ofId R S` puts
`RingHom.ker (Algebra.ofId R S)` into the statement, which is only definitionally — not
syntactically — the `RingHom.ker (algebraMap R S)` that the rest of the file and every caller
uses, and the resulting quotient types then carry two different `HasQuotient` instances.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Section 15.4](https://stacks.math.columbia.edu/tag/07VD)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Conormal

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)

/-- The submodule `I • ⊤` of `↥(I ^ n)` is the preimage of `I ^ (n + 1)`. -/
theorem smul_top_eq_comap :
    I • (⊤ : Submodule R ↥(I ^ n)) = Submodule.comap (I ^ n).subtype (I ^ (n + 1)) := by
  ext a
  rw [Submodule.mem_smul_top_iff]
  show (a : R) ∈ I * I ^ n ↔ (a : R) ∈ I ^ (n + 1)
  rw [pow_succ']

/-- `I ^ n`, as a submodule of `R`, is the degree-`n` term of the `I`-adic filtration of `R`. -/
def powEquivPower : ↥(I ^ n) ≃ₗ[R] AssociatedGraded.power (M := R) I n where
  toFun a := ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩
  invFun a := ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `powEquivPower` is the identity on underlying elements of `R`. -/
@[simp]
theorem coe_powEquivPower (a : ↥(I ^ n)) : ((powEquivPower I n a : _) : R) = (a : R) := rfl

/-- The canonical `R`-linear map `I ^ n → I ^ n / I ^ (n + 1)` onto the degree-`n` piece of
the associated graded ring of `I`. -/
def toPiece : ↥(I ^ n) →ₗ[R] AssociatedGraded.piece (M := R) I n :=
  LinearMap.comp
    (Submodule.mkQ ((AssociatedGraded.power (M := R) I (n + 1)).comap
      (Submodule.subtype (AssociatedGraded.power (M := R) I n))))
    (powEquivPower I n).toLinearMap

/-- `toPiece I n a` is the class of `a` in the degree-`n` piece of the associated graded ring. -/
theorem toPiece_apply (a : ↥(I ^ n)) :
    toPiece I n a = AssociatedGraded.mk I n (powEquivPower I n a) := rfl

/-- The class of `a ∈ I ^ n` in `I ^ n / I ^ (n + 1)` vanishes exactly when `a ∈ I ^ (n + 1)`. -/
theorem toPiece_eq_zero_iff (a : ↥(I ^ n)) :
    toPiece I n a = 0 ↔ (a : R) ∈ I ^ (n + 1) := by
  rw [toPiece_apply, AssociatedGraded.mk, Submodule.Quotient.mk_eq_zero]
  simp [AssociatedGraded.ring_power_eq]

/-- The map `I ^ n → I ^ n / I ^ (n + 1)` is surjective. -/
theorem toPiece_surjective : Function.Surjective (toPiece I n) := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨(powEquivPower I n).symm a, rfl⟩

/-- The kernel of `toPiece I n` is the preimage of `I ^ (n + 1)` in `I ^ n`. -/
theorem ker_toPiece :
    LinearMap.ker (toPiece I n) = Submodule.comap (I ^ n).subtype (I ^ (n + 1)) := by
  ext a
  exact toPiece_eq_zero_iff I n a

/-- The quotient presentation is multiplicative: the class of a product of representatives is
the product of their classes. -/
theorem toPiece_mul (m : ℕ) (a : ↥(I ^ n)) (b : ↥(I ^ m)) (c : ↥(I ^ (n + m)))
    (hc : (c : R) = (a : R) * (b : R)) :
    toPiece I (n + m) c =
      AssociatedGraded.homogeneousSMul I (toPiece I n a) (toPiece I m b) := by
  rw [toPiece_apply, toPiece_apply, toPiece_apply, AssociatedGraded.homogeneousSMul_mk]
  exact congrArg (AssociatedGraded.mk I (n + m)) (Subtype.ext (by simpa [smul_eq_mul] using hc))

/-- The class of `1` in degree zero is the unit of the associated graded ring. -/
theorem toPiece_one (a : ↥(I ^ 0)) (ha : (a : R) = 1) :
    toPiece I 0 a =
      AssociatedGraded.mk I 0
        (⟨1, by simp [AssociatedGraded.power]⟩ :
          AssociatedGraded.power (M := R) I 0) := by
  rw [toPiece_apply]
  exact congrArg (AssociatedGraded.mk I 0) (Subtype.ext ha)

/-- **The degree-`n` conormal piece is a base change.** The quotient `I ^ n / I ^ (n + 1)` is
the base change of `I ^ n` along `R ⟶ R ⧸ I`. -/
noncomputable def quotTensorPowEquivPiece :
    (R ⧸ I) ⊗[R] ↥(I ^ n) ≃ₗ[R] AssociatedGraded.piece (M := R) I n :=
  (TensorProduct.quotTensorEquivQuotSMul ↥(I ^ n) I).trans
    ((Submodule.quotEquivOfEq _ _
        ((smul_top_eq_comap I n).trans (ker_toPiece I n).symm)).trans
      ((toPiece I n).quotKerEquivOfSurjective (toPiece_surjective I n)))

/-- `quotTensorPowEquivPiece` sends `1 ⊗ₜ a` to the class of `a` in `I ^ n / I ^ (n + 1)`. -/
@[simp]
theorem quotTensorPowEquivPiece_one_tmul (a : ↥(I ^ n)) :
    quotTensorPowEquivPiece I n ((1 : R ⧸ I) ⊗ₜ[R] a) = toPiece I n a := by
  rw [quotTensorPowEquivPiece, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [show ((1 : R ⧸ I) ⊗ₜ[R] a) = (Ideal.Quotient.mk I (1 : R)) ⊗ₜ[R] a from rfl,
    TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ (toPiece_surjective I n) a

/-- For `a ∈ I ^ n`, the element `1 ⊗ₜ a` of `(R ⧸ I) ⊗[R] I ^ n` vanishes exactly when
`a ∈ I ^ (n + 1)`. -/
theorem one_tmul_eq_zero_iff (a : ↥(I ^ n)) :
    (1 : R ⧸ I) ⊗ₜ[R] a = 0 ↔ (a : R) ∈ I ^ (n + 1) :=
  by rw [← (quotTensorPowEquivPiece I n).map_eq_zero_iff, quotTensorPowEquivPiece_one_tmul,
    toPiece_eq_zero_iff]

/-- Every element of `(R ⧸ I) ⊗[R] I ^ n` is of the form `1 ⊗ₜ a` with `a ∈ I ^ n`. -/
theorem one_tmul_surjective :
    Function.Surjective fun a : ↥(I ^ n) => (1 : R ⧸ I) ⊗ₜ[R] a :=
  fun x => (toPiece_surjective I n (quotTensorPowEquivPiece I n x)).imp fun _ ha =>
    (quotTensorPowEquivPiece I n).injective (by simpa using ha)

section Surjective

variable {R' S : Type*} [CommRing R'] [CommRing S] [Algebra R' S]

/-- A surjective algebra map identifies `S` with `R ⧸ RingHom.ker (algebraMap R S)`,
`R`-linearly. -/
noncomputable def quotKerLinearEquiv (hS : Function.Surjective (algebraMap R' S)) :
    (R' ⧸ RingHom.ker (algebraMap R' S)) ≃ₗ[R'] S := by
  refine LinearEquiv.ofBijective
    ((RingHom.ker (algebraMap R' S)).liftQ (Algebra.linearMap R' S) le_rfl) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  · intro s
    obtain ⟨r, hr⟩ := hS s
    exact ⟨Submodule.Quotient.mk r, hr⟩

/-- `quotKerLinearEquiv` sends the class of `r` to `algebraMap R' S r`. -/
@[simp]
theorem quotKerLinearEquiv_mk (hS : Function.Surjective (algebraMap R' S)) (r : R') :
    quotKerLinearEquiv hS (Ideal.Quotient.mk (RingHom.ker (algebraMap R' S)) r) =
      algebraMap R' S r := rfl

/-- **The degree-`n` conormal piece of a surjection is a base change.** For a surjective
algebra map `R ⟶ S` with kernel `I`, the quotient `I ^ n / I ^ (n + 1)` is the base change of
`I ^ n` to `S`. -/
noncomputable def surjectiveTensorPowEquivPiece
    (hS : Function.Surjective (algebraMap R' S)) (n : ℕ) :
    S ⊗[R'] ↥(RingHom.ker (algebraMap R' S) ^ n) ≃ₗ[R']
      AssociatedGraded.piece (M := R') (RingHom.ker (algebraMap R' S)) n :=
  (TensorProduct.congr (quotKerLinearEquiv hS).symm (LinearEquiv.refl R' _)).trans
    (quotTensorPowEquivPiece (RingHom.ker (algebraMap R' S)) n)

/-- `surjectiveTensorPowEquivPiece` sends `1 ⊗ₜ a` to the class of `a` in
`I ^ n / I ^ (n + 1)`. -/
@[simp]
theorem surjectiveTensorPowEquivPiece_one_tmul
    (hS : Function.Surjective (algebraMap R' S)) (n : ℕ)
    (a : ↥(RingHom.ker (algebraMap R' S) ^ n)) :
    surjectiveTensorPowEquivPiece hS n ((1 : S) ⊗ₜ[R'] a) =
      toPiece (RingHom.ker (algebraMap R' S)) n a := by
  rw [surjectiveTensorPowEquivPiece, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, show (quotKerLinearEquiv hS).symm (1 : S) = 1 from
      (quotKerLinearEquiv hS).symm_apply_eq.2 (by
        rw [← map_one (algebraMap R' S)]; rfl),
    quotTensorPowEquivPiece_one_tmul]

/-- For a surjective algebra map `R ⟶ S` with kernel `I` and `a ∈ I ^ n`, the element `1 ⊗ₜ a`
of `S ⊗[R] I ^ n` vanishes exactly when `a ∈ I ^ (n + 1)`. -/
theorem surjective_one_tmul_eq_zero_iff
    (hS : Function.Surjective (algebraMap R' S)) (n : ℕ)
    (a : ↥(RingHom.ker (algebraMap R' S) ^ n)) :
    (1 : S) ⊗ₜ[R'] a = 0 ↔ (a : R') ∈ RingHom.ker (algebraMap R' S) ^ (n + 1) :=
  by rw [← (surjectiveTensorPowEquivPiece hS n).map_eq_zero_iff,
    surjectiveTensorPowEquivPiece_one_tmul, toPiece_eq_zero_iff]

/-- For a surjective algebra map `R ⟶ S` with kernel `I`, every element of `S ⊗[R] I ^ n` is of
the form `1 ⊗ₜ a` with `a ∈ I ^ n`. -/
theorem surjective_one_tmul_surjective
    (hS : Function.Surjective (algebraMap R' S)) (n : ℕ) :
    Function.Surjective
      fun a : ↥(RingHom.ker (algebraMap R' S) ^ n) => (1 : S) ⊗ₜ[R'] a :=
  fun x => (toPiece_surjective _ n (surjectiveTensorPowEquivPiece hS n x)).imp fun _ ha =>
    (surjectiveTensorPowEquivPiece hS n).injective (by simpa using ha)

end Surjective

end Stacks.Conormal

end
