module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

@[expose] public section

/-!
# The quadratic extension of a ring by a module with a symmetric multiplication

Let `R` be a commutative ring and `M` an `R`-module carrying a symmetric `R`-bilinear form
`m : M × M → R` which satisfies the *exchange law* `m x y • z = m y z • x`. Then `R × M` is a
commutative `R`-algebra for the multiplication
`(a, x) * (b, y) = (a * b + m x y, a • y + b • x)`;
it is integral over `R`, the induced map of spectra is surjective, and the value `m x x` of the
form at any `x : M` is a square in it, namely the square of `(0, x)`.

The exchange law holds whenever `M` is an ideal `J` of `R` and `m x y = μ x * y` for an
`R`-linear `μ : J → R` with `μ x * y = μ y * x`; this is
`Stacks.ModuleQuadraticExtension.idealDatum`. The case `J = R` and
`μ = (u * ·)` is the ordinary double cover `R[T]/(T ^ 2 - u)`
(`Stacks.ModuleQuadraticExtension.sqrtDatum`), of which the construction is the twist by an ideal
of denominators.

## Main definitions

* `Stacks.ModuleQuadraticExtension.QuadraticDatum`: the form together with its symmetry and the
  exchange law.
* `Stacks.ModuleQuadraticExtension.Ext`: the ring `R × M`, with its `CommRing` and `Algebra R`
  instances.
* `Stacks.ModuleQuadraticExtension.idealDatum` and
  `Stacks.ModuleQuadraticExtension.sqrtDatum`: the two data above.
* `Stacks.ModuleQuadraticExtension.pairDatum`: the datum `m x y = μ x * ι y` attached to a pair
  of linear forms `ι`, `μ : M → R` with `ι` injective and `μ x * ι y = μ y * ι x`. Taking `ι`
  the inclusion of an ideal gives `idealDatum`.
* `Stacks.ModuleQuadraticExtension.Ext.map`: the functoriality of the construction in the pair
  `(R, M)`.

## Main results

* `Stacks.ModuleQuadraticExtension.Ext.isIntegral`: `R × M` is integral over `R`.
* `Stacks.ModuleQuadraticExtension.Ext.exists_isPrime_comap_eq`: every prime of `R` is the
  contraction of a prime of `R × M`; equivalently `Spec (R × M) ⟶ Spec R` is surjective.
* `Stacks.ModuleQuadraticExtension.Ext.sq_inr` and
  `Stacks.ModuleQuadraticExtension.Ext.isSquare_algebraMap_of_form_eq`: the value `m x x` is the
  square of `(0, x)`.

## References

* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
* [Stacks Project, Tag 0CNX](https://stacks.math.columbia.edu/tag/0CNX)
-/

universe u v u' v'

namespace Stacks.ModuleQuadraticExtension

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A *quadratic datum* on an `R`-module `M`: a symmetric `R`-bilinear form `M × M ⟶ R` whose
values satisfy the exchange law `form x y • z = form y z • x`. -/
structure QuadraticDatum (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] where
  /-- The bilinear form. -/
  form : M →ₗ[R] M →ₗ[R] R
  /-- The form is symmetric. -/
  form_comm : ∀ x y, form x y = form y x
  /-- The exchange law. -/
  smul_form : ∀ x y z, form x y • z = form y z • x

/-- The quadratic extension of `R` by `M` along a quadratic datum: the `R`-module `R × M` with
the multiplication `(a, x) * (b, y) = (a * b + form x y, a • y + b • x)`. -/
def Ext (_d : QuadraticDatum R M) : Type max u v := R × M

namespace Ext

variable {d : QuadraticDatum R M}

/-- The element of `Ext d` with components `a` and `x`. -/
def mk (d : QuadraticDatum R M) (a : R) (x : M) : Ext d := (a, x)

/-- The first component of an element of `Ext d`. -/
def fst (y : Ext d) : R := y.1

/-- The second component of an element of `Ext d`. -/
def snd (y : Ext d) : M := y.2

/-- The first component of `mk d a x` is `a`. -/
@[simp] lemma fst_mk (a : R) (x : M) : (mk d a x).fst = a := rfl

/-- The second component of `mk d a x` is `x`. -/
@[simp] lemma snd_mk (a : R) (x : M) : (mk d a x).snd = x := rfl

/-- Two elements of `Ext d` with the same components are equal. -/
@[ext] lemma ext' {y z : Ext d} (h1 : y.fst = z.fst) (h2 : y.snd = z.snd) : y = z :=
  Prod.ext h1 h2

/-- The additive group structure of `Ext d`, that of `R × M`. -/
instance instAddCommGroup (d : QuadraticDatum R M) : AddCommGroup (Ext d) :=
  inferInstanceAs (AddCommGroup (R × M))

/-- The `R`-module structure of `Ext d`, that of `R × M`. -/
instance instModule (d : QuadraticDatum R M) : Module R (Ext d) :=
  inferInstanceAs (Module R (R × M))

/-- The unit `(1, 0)` of `Ext d`. -/
instance : One (Ext d) := ⟨mk d 1 0⟩

/-- The multiplication `(a, x) * (b, y) = (a * b + form x y, a • y + b • x)`. -/
instance : Mul (Ext d) :=
  ⟨fun y z => mk d (y.fst * z.fst + d.form y.snd z.snd) (y.fst • z.snd + z.fst • y.snd)⟩

/-- The first component of `1` is `1`. -/
@[simp] lemma fst_one : (1 : Ext d).fst = 1 := rfl

/-- The second component of `1` is `0`. -/
@[simp] lemma snd_one : (1 : Ext d).snd = 0 := rfl

/-- The first component of `0` is `0`. -/
@[simp] lemma fst_zero : (0 : Ext d).fst = 0 := rfl

/-- The second component of `0` is `0`. -/
@[simp] lemma snd_zero : (0 : Ext d).snd = 0 := rfl

/-- The first component of a sum is the sum of the first components. -/
@[simp] lemma fst_add (y z : Ext d) : (y + z).fst = y.fst + z.fst := rfl

/-- The second component of a sum is the sum of the second components. -/
@[simp] lemma snd_add (y z : Ext d) : (y + z).snd = y.snd + z.snd := rfl

/-- The first component of `-y` is the negative of that of `y`. -/
@[simp] lemma fst_neg (y : Ext d) : (-y).fst = -y.fst := rfl

/-- The second component of `-y` is the negative of that of `y`. -/
@[simp] lemma snd_neg (y : Ext d) : (-y).snd = -y.snd := rfl

/-- The first component of a difference is the difference of the first components. -/
@[simp] lemma fst_sub (y z : Ext d) : (y - z).fst = y.fst - z.fst := rfl

/-- The second component of a difference is the difference of the second components. -/
@[simp] lemma snd_sub (y z : Ext d) : (y - z).snd = y.snd - z.snd := rfl

/-- The first component of `y * z` is `y.fst * z.fst + form y.snd z.snd`. -/
@[simp] lemma fst_mul (y z : Ext d) :
    (y * z).fst = y.fst * z.fst + d.form y.snd z.snd := rfl

/-- The second component of `y * z` is `y.fst • z.snd + z.fst • y.snd`. -/
@[simp] lemma snd_mul (y z : Ext d) :
    (y * z).snd = y.fst • z.snd + z.fst • y.snd := rfl

/-- `Ext d` is a commutative ring under the quadratic multiplication. -/
instance instCommRing (d : QuadraticDatum R M) : CommRing (Ext d) where
  __ := instAddCommGroup d
  mul_assoc y z w := by
    ext
    · change (y.fst * z.fst + d.form y.snd z.snd) * w.fst
          + d.form (y.fst • z.snd + z.fst • y.snd) w.snd
        = y.fst * (z.fst * w.fst + d.form z.snd w.snd)
          + d.form y.snd (z.fst • w.snd + w.fst • z.snd)
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · change (y.fst * z.fst + d.form y.snd z.snd) • w.snd
          + w.fst • (y.fst • z.snd + z.fst • y.snd)
        = y.fst • (z.fst • w.snd + w.fst • z.snd)
          + (z.fst * w.fst + d.form z.snd w.snd) • y.snd
      have h := d.smul_form y.snd z.snd w.snd
      simp only [add_smul, smul_add, smul_smul, h]
      rw [mul_comm w.fst y.fst, mul_comm w.fst z.fst]
      abel
  one_mul y := by
    ext
    · change 1 * y.fst + d.form 0 y.snd = y.fst
      simp
    · change (1 : R) • y.snd + y.fst • (0 : M) = y.snd
      simp
  mul_one y := by
    ext
    · change y.fst * 1 + d.form y.snd 0 = y.fst
      simp
    · change y.fst • (0 : M) + (1 : R) • y.snd = y.snd
      simp
  mul_comm y z := by
    ext
    · change y.fst * z.fst + d.form y.snd z.snd = z.fst * y.fst + d.form z.snd y.snd
      rw [mul_comm, d.form_comm]
    · change y.fst • z.snd + z.fst • y.snd = z.fst • y.snd + y.fst • z.snd
      abel
  left_distrib y z w := by
    ext
    · change y.fst * (z.fst + w.fst) + d.form y.snd (z.snd + w.snd)
        = y.fst * z.fst + d.form y.snd z.snd + (y.fst * w.fst + d.form y.snd w.snd)
      simp only [map_add]
      ring
    · change y.fst • (z.snd + w.snd) + (z.fst + w.fst) • y.snd
        = y.fst • z.snd + z.fst • y.snd + (y.fst • w.snd + w.fst • y.snd)
      simp only [smul_add, add_smul]
      abel
  right_distrib y z w := by
    ext
    · change (y.fst + z.fst) * w.fst + d.form (y.snd + z.snd) w.snd
        = y.fst * w.fst + d.form y.snd w.snd + (z.fst * w.fst + d.form z.snd w.snd)
      simp only [map_add, LinearMap.add_apply]
      ring
    · change (y.fst + z.fst) • w.snd + w.fst • (y.snd + z.snd)
        = y.fst • w.snd + w.fst • y.snd + (z.fst • w.snd + w.fst • z.snd)
      simp only [smul_add, add_smul]
      abel
  zero_mul y := by
    ext
    · change 0 * y.fst + d.form 0 y.snd = 0
      simp
    · change (0 : R) • y.snd + y.fst • (0 : M) = 0
      simp
  mul_zero y := by
    ext
    · change y.fst * 0 + d.form y.snd 0 = 0
      simp
    · change y.fst • (0 : M) + (0 : R) • y.snd = 0
      simp

/-- The structure map `R ⟶ Ext d`, `a ↦ (a, 0)`. -/
def inlHom (d : QuadraticDatum R M) : R →+* Ext d where
  toFun a := mk d a 0
  map_one' := rfl
  map_mul' a b := by
    ext
    · simp
    · simp
  map_zero' := rfl
  map_add' a b := by
    ext
    · change a + b = a + b
      rfl
    · change (0 : M) = 0 + 0
      rw [add_zero]

/-- The structure map sends `a` to `(a, 0)`. -/
@[simp] lemma inlHom_apply (a : R) : inlHom d a = mk d a 0 := rfl

/-- `Ext d` is an `R`-algebra through `inlHom d`. -/
instance : Algebra R (Ext d) := (inlHom d).toAlgebra

/-- The algebra map `R ⟶ Ext d` sends `a` to `(a, 0)`. -/
lemma algebraMap_eq (a : R) : algebraMap R (Ext d) a = mk d a 0 := by
  rw [RingHom.algebraMap_toAlgebra, inlHom_apply]

/-- The first component of the image of `a : R` is `a`. -/
@[simp] lemma fst_algebraMap (a : R) : (algebraMap R (Ext d) a).fst = a := by
  rw [algebraMap_eq, fst_mk]

/-- The second component of the image of `a : R` is `0`. -/
@[simp] lemma snd_algebraMap (a : R) : (algebraMap R (Ext d) a).snd = 0 := by
  rw [algebraMap_eq, snd_mk]

/-- The first component of `y * c` for `c : R` is `y.fst * c`. -/
@[simp] lemma fst_mul_algebraMap (y : Ext d) (c : R) :
    (y * algebraMap R (Ext d) c).fst = y.fst * c := by
  rw [fst_mul, snd_algebraMap, fst_algebraMap, map_zero, add_zero]

/-- The second component of `y * c` for `c : R` is `c • y.snd`. -/
@[simp] lemma snd_mul_algebraMap (y : Ext d) (c : R) :
    (y * algebraMap R (Ext d) c).snd = c • y.snd := by
  rw [snd_mul, snd_algebraMap, fst_algebraMap, smul_zero, zero_add]

/-- The structure map of `Ext d` is injective. -/
lemma injective_algebraMap : Function.Injective (algebraMap R (Ext d)) := by
  intro a b h
  simpa using congrArg fst h

/-- Every element of `Ext d` is integral over `R`. -/
lemma isIntegral_elem (y : Ext d) : IsIntegral R y := by
  classical
  refine ⟨Polynomial.X * Polynomial.X - Polynomial.C (2 * y.fst) * Polynomial.X
    + Polynomial.C (y.fst * y.fst - d.form y.snd y.snd), by monicity!, ?_⟩
  have key : (Polynomial.aeval y) (Polynomial.X * Polynomial.X
        - Polynomial.C (2 * y.fst) * Polynomial.X
        + Polynomial.C (y.fst * y.fst - d.form y.snd y.snd))
      = y * y - algebraMap R (Ext d) (2 * y.fst) * y
        + algebraMap R (Ext d) (y.fst * y.fst - d.form y.snd y.snd) := by
    simp
  rw [← Polynomial.aeval_def, key]
  ext
  · simp only [fst_add, fst_sub, fst_mul, fst_algebraMap, snd_algebraMap, fst_zero, map_zero,
      LinearMap.zero_apply]
    ring
  · simp only [snd_add, snd_sub, snd_mul, fst_algebraMap, snd_algebraMap, snd_zero, smul_zero,
      add_zero, two_mul, add_smul]
    abel

/-- `Ext d` is integral over `R`. -/
instance isIntegral : Algebra.IsIntegral R (Ext d) := ⟨isIntegral_elem⟩

/-- The spectrum of `Ext d` surjects onto the spectrum of `R`: every prime of `R` is the
contraction of a prime of `Ext d`. -/
lemma exists_isPrime_comap_eq (P : Ideal R) [P.IsPrime] :
    ∃ Q : Ideal (Ext d), Q.IsPrime ∧ Q.comap (algebraMap R (Ext d)) = P := by
  have hker : (⊥ : Ideal (Ext d)).comap (algebraMap R (Ext d)) ≤ P := by
    intro a ha
    have h0 : algebraMap R (Ext d) a = 0 := by simpa [Ideal.mem_comap] using ha
    have ha0 : a = 0 := injective_algebraMap (by rw [h0, map_zero])
    simp [ha0]
  obtain ⟨Q, -, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := Ext d) P ⊥ hker
  exact ⟨Q, hQ, hQ'⟩

/-- The square of `(0, x)` is the value `form x x` of the form. -/
@[simp] lemma sq_inr (x : M) : mk d 0 x ^ 2 = algebraMap R (Ext d) (d.form x x) := by
  rw [sq]
  ext
  · simp
  · simp

/-- Every value of the form becomes a square in `Ext d`. -/
lemma isSquare_algebraMap_of_form_eq {x : M} {u : R} (h : d.form x x = u) :
    IsSquare (algebraMap R (Ext d) u) :=
  ⟨mk d 0 x, by rw [← h, ← sq_inr x, sq]⟩

/-! ### Functoriality -/

section Map

variable {R' : Type u'} [CommRing R'] {M' : Type v'} [AddCommGroup M'] [Module R' M']
  {d' : QuadraticDatum R' M'} (φ : R →+* R') (ψ : M →+ M')
  (hsmul : ∀ (a : R) (x : M), ψ (a • x) = φ a • ψ x)
  (hform : ∀ x y : M, d'.form (ψ x) (ψ y) = φ (d.form x y))

/-- The ring homomorphism `Ext d ⟶ Ext d'` induced by a ring homomorphism `φ : R ⟶ R'` together
with an additive map `ψ : M ⟶ M'` which is semilinear along `φ` and carries the form of `d` to
the form of `d'`. -/
def map : Ext d →+* Ext d' where
  toFun y := mk d' (φ y.fst) (ψ y.snd)
  map_one' := by ext <;> simp
  map_mul' y z := by
    ext
    · change φ (y.fst * z.fst + d.form y.snd z.snd)
        = φ y.fst * φ z.fst + d'.form (ψ y.snd) (ψ z.snd)
      rw [hform, map_add, map_mul]
    · change ψ (y.fst • z.snd + z.fst • y.snd) = φ y.fst • ψ z.snd + φ z.fst • ψ y.snd
      rw [map_add, hsmul, hsmul]
  map_zero' := by ext <;> simp
  map_add' y z := by
    ext
    · change φ (y.fst + z.fst) = φ y.fst + φ z.fst
      rw [map_add]
    · change ψ (y.snd + z.snd) = ψ y.snd + ψ z.snd
      rw [map_add]

/-- The first component of `map φ ψ y` is `φ y.fst`. -/
@[simp] lemma fst_map (y : Ext d) : (map (d' := d') φ ψ hsmul hform y).fst = φ y.fst := rfl

/-- The second component of `map φ ψ y` is `ψ y.snd`. -/
@[simp] lemma snd_map (y : Ext d) : (map (d' := d') φ ψ hsmul hform y).snd = ψ y.snd := rfl

/-- The induced map is a map of `R`-algebras in the obvious sense: it carries the image of
`a : R` to the image of `φ a`. -/
lemma map_algebraMap (a : R) :
    map (d' := d') φ ψ hsmul hform (algebraMap R (Ext d) a) = algebraMap R' (Ext d') (φ a) := by
  ext
  · simp
  · simp [algebraMap_eq]

end Map

end Ext

/-! ### The two data of interest -/

section PairDatum

variable (ιM μ : M →ₗ[R] R)

/-- The form `(x, y) ↦ μ x * ιM y` attached to a pair of linear forms on `M`. -/
def pairForm : M →ₗ[R] M →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y : M => μ x * ιM y)
    (fun x x' y => by rw [map_add]; ring)
    (fun c x y => by rw [map_smul, smul_eq_mul, smul_eq_mul, mul_assoc])
    (fun x y y' => by rw [map_add]; ring)
    (fun c x y => by rw [map_smul, smul_eq_mul, smul_eq_mul]; ring)

/-- The value of `pairForm ιM μ` at `(x, y)` is `μ x * ιM y`. -/
@[simp] lemma pairForm_apply (x y : M) : pairForm ιM μ x y = μ x * ιM y := rfl

/-- The quadratic datum attached to a pair of linear forms `ιM`, `μ : M ⟶ R` with `ιM`
injective and `μ x * ιM y = μ y * ιM x`: the form is `(x, y) ↦ μ x * ιM y`. -/
def pairDatum (hι : Function.Injective ιM) (hμ : ∀ x y : M, μ x * ιM y = μ y * ιM x) :
    QuadraticDatum R M where
  form := pairForm ιM μ
  form_comm := hμ
  smul_form x y z := hι <| by
    rw [map_smul, map_smul, pairForm_apply, pairForm_apply, smul_eq_mul, smul_eq_mul,
      mul_right_comm (μ y) (ιM z) (ιM x), hμ y x]

/-- The form of `pairDatum ιM μ hι hμ` is `pairForm ιM μ`. -/
@[simp] lemma pairDatum_form (hι : Function.Injective ιM)
    (hμ : ∀ x y : M, μ x * ιM y = μ y * ιM x) :
    (pairDatum ιM μ hι hμ).form = pairForm ιM μ := rfl

end PairDatum

section IdealDatum

variable (J : Ideal R) (μ : J →ₗ[R] R)

/-- The form `(x, y) ↦ μ x * y` on an ideal `J`, for an `R`-linear `μ : J ⟶ R`. -/
def idealForm : J →ₗ[R] J →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y : J => μ x * (y : R))
    (fun x x' y => by rw [map_add]; ring)
    (fun c x y => by rw [map_smul, smul_eq_mul, smul_eq_mul, mul_assoc])
    (fun x y y' => by rw [Submodule.coe_add]; ring)
    (fun c x y => by rw [Submodule.coe_smul, smul_eq_mul, smul_eq_mul]; ring)

/-- The value of `idealForm J μ` at `(x, y)` is `μ x * y`. -/
@[simp] lemma idealForm_apply (x y : J) : idealForm J μ x y = μ x * (y : R) := rfl

/-- The quadratic datum attached to an ideal `J` of `R` and an `R`-linear `μ : J ⟶ R` with
`μ x * y = μ y * x`: the form is `(x, y) ↦ μ x * y`. -/
def idealDatum (hμ : ∀ x y : J, μ x * (y : R) = μ y * (x : R)) : QuadraticDatum R J :=
  pairDatum J.subtype μ (Submodule.injective_subtype J) hμ

/-- The form of `idealDatum J μ hμ` is `idealForm J μ`. -/
@[simp] lemma idealDatum_form (hμ : ∀ x y : J, μ x * (y : R) = μ y * (x : R)) :
    (idealDatum J μ hμ).form = idealForm J μ := rfl

end IdealDatum

section SqrtDatum

variable (u : R)

/-- The form `(x, y) ↦ u * x * y` on `R` itself. -/
def sqrtForm : R →ₗ[R] R →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y : R => u * x * y)
    (fun x x' y => by ring)
    (fun c x y => by rw [smul_eq_mul, smul_eq_mul]; ring)
    (fun x y y' => by ring)
    (fun c x y => by rw [smul_eq_mul, smul_eq_mul]; ring)

/-- The value of `sqrtForm u` at `(x, y)` is `u * x * y`. -/
@[simp] lemma sqrtForm_apply (x y : R) : sqrtForm u x y = u * x * y := rfl

/-- The quadratic datum of the ordinary double cover `R[T]/(T ^ 2 - u)`: the module is `R` and
the form is `(x, y) ↦ u * x * y`. -/
def sqrtDatum : QuadraticDatum R R where
  form := sqrtForm u
  form_comm x y := by rw [sqrtForm_apply, sqrtForm_apply]; ring
  smul_form x y z := by rw [sqrtForm_apply, sqrtForm_apply, smul_eq_mul, smul_eq_mul]; ring

/-- The form of `sqrtDatum u` is `sqrtForm u`. -/
@[simp] lemma sqrtDatum_form : (sqrtDatum u).form = sqrtForm u := rfl

/-- In the double cover `Ext (sqrtDatum u)` the element `u` is a square. -/
lemma isSquare_algebraMap_sqrtDatum :
    IsSquare (algebraMap R (Ext (sqrtDatum u)) u) :=
  Ext.isSquare_algebraMap_of_form_eq (x := (1 : R)) (by simp)

end SqrtDatum

end Stacks.ModuleQuadraticExtension

end
