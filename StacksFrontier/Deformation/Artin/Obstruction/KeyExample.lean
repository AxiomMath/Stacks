module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.NaiveCotangent.ExtCokernel

/-!
# The key example of an obstruction theory

Let `Λ` be a ring, let `R = Λ[x_1, …, x_n]/J` and let `𝒳 = (Sch/X)_{fppf}` with
`X = Spec R`. An object of `𝒳` over `Spec A` is a `Λ`-algebra map `R → A`, equivalently a
tuple `(a_1, …, a_n)` of elements of `A` with `f(a_1, …, a_n) = 0` for every `f ∈ J`. This
file formalizes the assertions of Stacks 07YI about the obstruction theory of `𝒳`.

The naive cotangent complex `NL_{R/Λ}` is canonically homotopy equivalent to the two-term
complex
```
J/J² ⟶ ⊕_{i = 1, …, n} R dx_i
```
(Stacks 00S1); the complex on the right is `NaiveCotangent.NL` of the presentation
`Λ[x_1, …, x_n] → R`, whose conormal module is `J/J²` and whose degree-`0` term is free on
the classes `dx_i`. For a deformation situation `(x, A' → A)` with kernel
`I = Ker(A' → A)` the obstruction module is
```
𝒪_x(M) = Hom_R(J/J², M)/Hom_R(R^{⊕n}, M) = Ext¹_R(NL_{R/Λ}, M)
```
and the obstruction element `o_x(A') ∈ 𝒪_x(I)` is the class of the map `J/J² → I` sending
`f` to `f(a'_1, …, a'_n)`, where `a'_i ∈ A'` are any lifts of the `a_i`. This class does not
depend on the chosen lifts, and it vanishes exactly when `x` lifts to an object over
`Spec A'`.

## Main definitions

* `Deformation.Artin.KeyExample.presentation` — the presentation
  `Λ[x_1, …, x_n] → Λ[x_1, …, x_n]/J` of the source, with
  `Deformation.Artin.KeyExample.presentation_ker` identifying its kernel with `J`.
* `Deformation.Artin.KeyExample.objEquivTuple` — the source's identification of an object of
  `𝒳` over `Spec A` with a tuple `(a_1, …, a_n)` annihilating `J`.
* `Deformation.Artin.KeyExample.Situation` — the algebraic datum of a deformation situation
  `(x, A' → A)` for the key example, and `Situation.Lift` a family of lifts `a'_i ∈ A'` of
  the coordinates of `x`.
* `Deformation.Artin.KeyExample.obstructionModule` — the obstruction module
  `𝒪_x(M) = Hom_R(J/J², M)/Hom_R(R^{⊕n}, M)`.
* `Deformation.Artin.KeyExample.obstructionModuleAddEquivExtOne` — its identification with
  `Ext¹_R(NL_{R/Λ}, M)`.
* `Deformation.Artin.KeyExample.Situation.Lift.obsHom` — the map `J/J² → I` of the source,
  `f ↦ f(a'_1, …, a'_n)`, and `Situation.obsClass` its class `o_x(A')`.

## Main results

* `Deformation.Artin.KeyExample.exists_isHomotopyEquiv_nl_canonical` and
  `Deformation.Artin.KeyExample.exists_basis_nl_cotangentSpace`: the homotopy equivalence of
  `NL_{R/Λ}` with `J/J² → ⊕_i R dx_i`.
* `Deformation.Artin.KeyExample.Situation.obsClass_eq`: `o_x(A')` is independent of the
  choice of lifts.
* `Deformation.Artin.KeyExample.Situation.obsClass_eq_zero_iff`: `o_x(A') = 0` if and only if
  `x` lifts to `Spec A'`.
* `Deformation.Artin.KeyExample.Situation.coe_cotangentEquivKernel_symm_obsHom_pushforward`:
  functoriality of the obstruction element along a morphism of deformation situations.

## Implementation notes

The source writes `R = Λ[x_1, …, x_n]/J`. The development is carried out for an arbitrary
presentation `P : Algebra.Generators Λ R (Fin n)` of a `Λ`-algebra `R` on `n` generators,
which is the same datum up to isomorphism: `presentation J` produces such a `P` from an ideal
`J` of `Λ[x_1, …, x_n]`, and `presentation_ker` says its kernel is `J`, so that
`P.toExtension.Cotangent` is the source's `J/J²`. The degree-`0` term
`P.toExtension.CotangentSpace = R ⊗_{Λ[x]} Ω_{Λ[x]/Λ}` is free on the classes `dx_i`, by
Mathlib's `Algebra.Generators.cotangentSpaceBasis`; this is the source's `⊕_i R dx_i`.

The obstruction module is spelled exactly as the right-hand side of
`NaiveCotangent.extOne_naiveCotangentComplex_addEquiv_cokernel` (Stacks 0GPU), so the
source's identification with `Ext¹_R(NL_{R/Λ}, M)` is that comparison read at the
presentation of the key example.

A deformation situation is bundled as `Situation`, so that the algebra structure of `A` over
`R` carried by the object `x`, and the module structures it induces, are genuine instances
attached to one parameter rather than hypotheses threaded through `letI`.

The kernel `I` has square zero, so `I/I² = I`; the obstruction maps land in
`Situation.ext.Cotangent`, which is `I/I²`, and `Situation.cotangentEquivKernel` is the
explicit `A'`-linear isomorphism with `I` itself. The description of `obsHom` as
`f ↦ f(a'_1, …, a'_n)` is recorded through that isomorphism, in
`Situation.Lift.coe_cotangentEquivKernel_symm_obsHom_mk`.

The source's `o_x(A')` is defined by choosing lifts `a'_i`; the choice is a field of
`Situation.Lift`, not an application of `Classical.choose`, and `Situation.Lift.nonempty`
records that lifts always exist because `A' → A` is surjective, so `Situation.obsClass`
together with `Situation.obsClass_eq` is a well-defined invariant of the deformation
situation.

That two families of lifts give the same class, and that a vanishing class produces a lift,
are both instances of Mathlib's `Algebra.Extension.Hom.sub`: the difference of the two maps
induced on conormal modules by two morphisms of extensions is precomposition with the
differential of the naive cotangent complex, and on the basis `dx_i` the correcting map
`Hom.sub` is computed by `Algebra.Extension.Hom.sub_one_tmul`.

## References

* [Stacks Project, Tag 07YI](https://stacks.math.columbia.edu/tag/07YI)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 0GPU](https://stacks.math.columbia.edu/tag/0GPU)
-/

@[expose] public section

universe u v

namespace Deformation.Artin.KeyExample

/-! ### The presentation `R = Λ[x_1, …, x_n]/J` -/

section Presentation

variable {Λ : Type u} [CommRing Λ] {n : ℕ} (J : Ideal (MvPolynomial (Fin n) Λ))

/-- Evaluating the variables at their own residue classes is the quotient map. -/
theorem aeval_mk_X_eq_mkₐ :
    (MvPolynomial.aeval fun i => Ideal.Quotient.mk J (MvPolynomial.X i) :
        MvPolynomial (Fin n) Λ →ₐ[Λ] MvPolynomial (Fin n) Λ ⧸ J) =
      Ideal.Quotient.mkₐ Λ J := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- The quotient `Λ[x_1, …, x_n]/J` is generated by the residue classes of the variables. -/
theorem surjective_aeval_mk_X :
    Function.Surjective ⇑(MvPolynomial.aeval fun i => Ideal.Quotient.mk J (MvPolynomial.X i) :
      MvPolynomial (Fin n) Λ →ₐ[Λ] MvPolynomial (Fin n) Λ ⧸ J) := by
  rw [aeval_mk_X_eq_mkₐ]
  exact Ideal.Quotient.mk_surjective

/-- **The presentation of the key example**: `Λ[x_1, …, x_n] → Λ[x_1, …, x_n]/J`, sending the
variable `x_i` to its residue class. -/
noncomputable def presentation :
    Algebra.Generators Λ (MvPolynomial (Fin n) Λ ⧸ J) (Fin n) :=
  Algebra.Generators.ofSurjective _ (surjective_aeval_mk_X J)

/-- The generator `x_i` of the presentation is the residue class of the variable `X i`. -/
@[simp]
theorem presentation_val (i : Fin n) :
    (presentation J).val i = Ideal.Quotient.mk J (MvPolynomial.X i) :=
  rfl

/-- The kernel of the presentation of the key example is `J`, so that the conormal module
`(presentation J).toExtension.Cotangent` is the source's `J/J²`. -/
theorem presentation_ker : (presentation J).ker = J := by
  rw [Algebra.Generators.ker_eq_ker_aeval_val]
  change RingHom.ker (MvPolynomial.aeval (R := Λ) (S₁ := MvPolynomial (Fin n) Λ ⧸ J)
    fun i => Ideal.Quotient.mk J (MvPolynomial.X i)) = J
  rw [aeval_mk_X_eq_mkₐ]
  exact Ideal.mk_ker

end Presentation

/-! ### Objects of `𝒳` over `Spec A` as tuples -/

section Objects

variable {Λ : Type u} [CommRing Λ] {n : ℕ} (J : Ideal (MvPolynomial (Fin n) Λ))
  (A : Type v) [CommRing A] [Algebra Λ A]

/-- The tuple `(a_1, …, a_n)` of an object `x`: the images of the variables. -/
noncomputable def tupleOfObj (x : (MvPolynomial (Fin n) Λ ⧸ J) →ₐ[Λ] A) :
    {a : Fin n → A // ∀ f ∈ J, MvPolynomial.aeval a f = 0} :=
  ⟨fun i => x (Ideal.Quotient.mk J (MvPolynomial.X i)), fun f hf => by
    have h : x.comp (MvPolynomial.aeval fun i => Ideal.Quotient.mk J (MvPolynomial.X i)) =
        MvPolynomial.aeval fun i => x (Ideal.Quotient.mk J (MvPolynomial.X i)) :=
      MvPolynomial.comp_aeval ..
    have h2 := AlgHom.congr_fun h f
    simp only [aeval_mk_X_eq_mkₐ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [← h2, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]⟩

/-- The `i`-th coordinate of the tuple of `x` is the image under `x` of the class of `X i`. -/
@[simp]
theorem tupleOfObj_coe (x : (MvPolynomial (Fin n) Λ ⧸ J) →ₐ[Λ] A) (i : Fin n) :
    (tupleOfObj J A x).1 i = x (Ideal.Quotient.mk J (MvPolynomial.X i)) :=
  rfl

/-- The object `x : R → A` determined by a tuple `(a_1, …, a_n)` annihilating `J`. -/
noncomputable def objOfTuple (a : {a : Fin n → A // ∀ f ∈ J, MvPolynomial.aeval a f = 0}) :
    (MvPolynomial (Fin n) Λ ⧸ J) →ₐ[Λ] A :=
  Ideal.Quotient.liftₐ J (MvPolynomial.aeval a.1) a.2

/-- The object determined by a tuple sends the class of `p` to `p(a_1, …, a_n)`. -/
@[simp]
theorem objOfTuple_mk (a : {a : Fin n → A // ∀ f ∈ J, MvPolynomial.aeval a f = 0})
    (p : MvPolynomial (Fin n) Λ) :
    objOfTuple J A a (Ideal.Quotient.mk J p) = MvPolynomial.aeval a.1 p :=
  rfl

/-- An object `x` of `𝒳 = (Sch/Spec R)_{fppf}` over `Spec A`, that is a
`Λ`-algebra map `R → A` with `R = Λ[x_1, …, x_n]/J`, is the same datum as a tuple
`(a_1, …, a_n)` of elements of `A` with `f(a_1, …, a_n) = 0` in `A` for every `f ∈ J`. -/
@[stacks 07YI "x corresponds to a tuple (a_1, …, a_n) killing J"]
noncomputable def objEquivTuple :
    ((MvPolynomial (Fin n) Λ ⧸ J) →ₐ[Λ] A) ≃
      {a : Fin n → A // ∀ f ∈ J, MvPolynomial.aeval a f = 0} where
  toFun := tupleOfObj J A
  invFun := objOfTuple J A
  left_inv x := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp
  right_inv a := by
    ext i
    simp

end Objects

/-! ### The naive cotangent complex of the key example -/

section Homotopy

variable {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R] {n : ℕ}
  (P : Algebra.Generators Λ R (Fin n))

/-- The naive cotangent complex `NL_{R/Λ}` is canonically homotopy equivalent to the two-term
complex `J/J² → ⊕_{i = 1, …, n} R dx_i` attached to the presentation `Λ[x_1, …, x_n] → R`:
there is a morphism of presentations onto the canonical presentation, and the induced chain map
is a homotopy equivalence. This is Stacks 00S1(4) read at the presentation of the key example;
`presentation_ker` identifies the conormal module of `presentation J` with `J/J²`. -/
@[stacks 07YI "NL_{R/Λ} is canonically homotopy equivalent to J/J² → ⊕ R dx_i",
  sga "6 0 4.3" "partial",
  sga "6 0 4.4" "special case"]
theorem exists_isHomotopyEquiv_nl_canonical :
    ∃ φ : P.Hom (NaiveCotangent.canonicalGenerators Λ R),
      NaiveCotangent.IsHomotopyEquiv
        (NaiveCotangent.nlMap P (NaiveCotangent.canonicalGenerators Λ R) φ) :=
  ⟨P.defaultHom _,
    (NaiveCotangent.nlMap_isHomotopyEquiv_and_isQuasiIso (R' := Λ) (S' := R)
      (by rw [Algebra.algebraMap_self]; exact Function.bijective_id)
      (by rw [Algebra.algebraMap_self]; exact Function.bijective_id)
      P _ (P.defaultHom _)).left⟩

/-- The degree-`0` term of the two-term complex of the key example is the free `R`-module
`⊕_{i = 1, …, n} R dx_i` on the classes `dx_i` of the variables. -/
@[stacks 07YI "the degree-0 term is the free module ⊕_{i = 1, …, n} R dx_i"]
theorem exists_basis_nl_cotangentSpace :
    ∃ b : Module.Basis (Fin n) R (NaiveCotangent.NL P).X₀,
      ∀ i, b i = 1 ⊗ₜ[P.toExtension.Ring]
        (KaehlerDifferential.D Λ P.toExtension.Ring) (MvPolynomial.X i) :=
  ⟨P.cotangentSpaceBasis, P.cotangentSpaceBasis_apply⟩

end Homotopy

/-! ### Deformation situations for the key example -/

variable {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R] {n : ℕ}

/-- **The algebraic datum of a deformation situation for the key example.** A surjection
`A' → A` of `Λ`-algebras whose kernel `I` has square zero, together with an object `x` of
`𝒳 = (Sch/Spec R)_{fppf}` over `Spec A`, that is a `Λ`-algebra map `R → A`. -/
structure Situation (P : Algebra.Generators Λ R (Fin n)) where
  /-- The thickened algebra `A'`. -/
  thick : Type u
  [commRingThick : CommRing thick]
  [algebraThick : Algebra Λ thick]
  /-- The algebra `A`. -/
  base : Type u
  [commRingBase : CommRing base]
  [algebraBase : Algebra Λ base]
  /-- The surjection `A' → A`. -/
  proj : thick →ₐ[Λ] base
  /-- The map `A' → A` is surjective. -/
  surjective : Function.Surjective proj
  /-- Its kernel `I` has square zero. -/
  sq_eq_bot : RingHom.ker (proj : thick →+* base) ^ 2 = ⊥
  /-- The object `x` of `𝒳` over `Spec A`. -/
  obj : R →ₐ[Λ] base

attribute [instance] Situation.commRingThick Situation.algebraThick Situation.commRingBase
  Situation.algebraBase

namespace Situation

section Basic

variable {P : Algebra.Generators Λ R (Fin n)} (t : Situation P)

/-- The object `x` makes `A` an `R`-algebra. -/
instance objAlgebra : Algebra R t.base := t.obj.toAlgebra

/-- The algebras `Λ → R → A` form a scalar tower. -/
instance objTower : IsScalarTower Λ R t.base :=
  IsScalarTower.of_algebraMap_eq fun l => (t.obj.commutes l).symm

/-- The kernel `I = Ker(A' → A)` of a deformation situation. -/
abbrev kernel : Ideal t.thick := RingHom.ker (t.proj : t.thick →+* t.base)

/-- The surjection `A' → A` viewed as an extension of `Λ`-algebras, so that its conormal
module `Algebra.Extension.Cotangent` is `I/I²`. -/
noncomputable def ext : Algebra.Extension Λ t.base :=
  Algebra.Extension.ofSurjective t.proj t.surjective

/-- The kernel of the extension `A' → A` is `I`. -/
theorem ext_ker : t.ext.ker = t.kernel := rfl

/-- The kernel of the extension `A' → A` has square zero. -/
theorem ext_sq_eq_bot : t.ext.ker ^ 2 = ⊥ := t.sq_eq_bot

/-- Because `I² = 0`, the class map `I → I/I²` is injective. -/
theorem injective_cotangent_mk :
    Function.Injective (Algebra.Extension.Cotangent.mk (P := t.ext)) := by
  intro a b hab
  have h0 : Algebra.Extension.Cotangent.mk (P := t.ext) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [Algebra.Extension.Cotangent.mk_eq_zero_iff, t.ext_sq_eq_bot, Ideal.mem_bot] at h0
  exact sub_eq_zero.1 (Subtype.ext h0)

/-- Because `I² = 0`, the conormal module `I/I²` of the extension `A' → A` is `I` itself:
`Algebra.Extension.Cotangent.mk` is an `A'`-linear isomorphism. -/
noncomputable def cotangentEquivKernel : t.ext.ker ≃ₗ[t.ext.Ring] t.ext.Cotangent :=
  LinearEquiv.ofBijective (Algebra.Extension.Cotangent.mk (P := t.ext))
    ⟨t.injective_cotangent_mk, Algebra.Extension.Cotangent.mk_surjective⟩

/-- The isomorphism `I ≃ I/I²` sends an element of `I` to its class. -/
@[simp]
theorem cotangentEquivKernel_apply (z : t.ext.ker) :
    t.cotangentEquivKernel z = Algebra.Extension.Cotangent.mk z :=
  rfl

/-- **A family of lifts of the coordinates of `x`**: elements `a'_i ∈ A'` lifting the
`a_i ∈ A`. -/
structure Lift (t : Situation P) where
  /-- The chosen lifts `a'_i ∈ A'`. -/
  val : Fin n → t.thick
  /-- Each `a'_i` lifts `a_i = x(x_i)`. -/
  proj_val : ∀ i, t.proj (val i) = t.obj (P.val i)

/-- Lifts of the coordinates always exist, because `A' → A` is surjective. -/
theorem nonempty_lift : Nonempty t.Lift := by
  choose a ha using fun i => t.surjective (t.obj (P.val i))
  exact ⟨⟨a, ha⟩⟩

/-- `x` lifts to an object of `𝒳` over `Spec A'`, that is `Lift(x, A') ≠ ∅`: there is a
`Λ`-algebra map `R → A'` whose composite with `A' → A` is `x`. -/
def HasLift (t : Situation P) : Prop :=
  ∃ y : R →ₐ[Λ] t.thick, t.proj.comp y = t.obj

end Basic

/-- The algebra map `Λ[x_1, …, x_n] → R` of a presentation is evaluation at the generators. -/
theorem algebraMap_extensionRing {P : Algebra.Generators Λ R (Fin n)} (x : P.toExtension.Ring) :
    algebraMap P.toExtension.Ring R x = MvPolynomial.aeval P.val x :=
  RingHom.congr_fun P.algebraMap_eq x

/-- A polynomial lies in the kernel `J` of the presentation exactly when it vanishes at the
generators. -/
theorem mem_ker_iff {P : Algebra.Generators Λ R (Fin n)} (f : MvPolynomial (Fin n) Λ) :
    f ∈ P.ker ↔ MvPolynomial.aeval P.val f = 0 := by
  rw [Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]

/-- Every element of `J/J²` is the class of an element of `J`. -/
theorem exists_cotangent_mk (P : Algebra.Generators Λ R (Fin n))
    (z : P.toExtension.Cotangent) : ∃ f : P.ker, Algebra.Extension.Cotangent.mk f = z := by
  obtain ⟨f, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
  exact ⟨f, rfl⟩

section Lifts

variable {P : Algebra.Generators Λ R (Fin n)} {t : Situation P}

/-- Evaluating a polynomial at the lifts `a'_i` and reducing is the same as evaluating at the
`a_i`. -/
theorem Lift.proj_comp_aeval (l : t.Lift) :
    t.proj.comp (MvPolynomial.aeval l.val) = t.obj.comp (MvPolynomial.aeval P.val) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa using l.proj_val i

/-- The morphism of extensions `(Λ[x_1, …, x_n] → R) → (A' → A)` determined by a family of
lifts: it evaluates a polynomial at the `a'_i`. -/
noncomputable def Lift.hom (l : t.Lift) : P.toExtension.Hom t.ext where
  toRingHom := (MvPolynomial.aeval l.val :
    MvPolynomial (Fin n) Λ →ₐ[Λ] t.thick).toRingHom
  toRingHom_algebraMap x := by
    change MvPolynomial.aeval l.val (algebraMap Λ (MvPolynomial (Fin n) Λ) x) =
      algebraMap Λ t.thick (algebraMap Λ Λ x)
    simp
  algebraMap_toRingHom x := by
    have h := AlgHom.congr_fun l.proj_comp_aeval x
    change t.proj (MvPolynomial.aeval l.val x) = t.obj (algebraMap P.toExtension.Ring R x)
    rw [algebraMap_extensionRing]
    exact h

/-- The morphism of extensions `Lift.hom` evaluates a polynomial at the lifts `a'_i`. -/
@[simp]
theorem Lift.hom_toRingHom_apply (l : t.Lift) (f : MvPolynomial (Fin n) Λ) :
    l.hom.toRingHom f = MvPolynomial.aeval l.val f :=
  rfl

/-- The value `f(a'_1, …, a'_n)` of an element `f ∈ J` at the lifts lies in
`I = Ker(A' → A)`. -/
theorem Lift.aeval_mem_kernel (l : t.Lift) (f : P.ker) :
    MvPolynomial.aeval l.val (f : MvPolynomial (Fin n) Λ) ∈ t.kernel := by
  have hf : MvPolynomial.aeval P.val (f : MvPolynomial (Fin n) Λ) = 0 := (mem_ker_iff _).1 f.2
  have h := AlgHom.congr_fun l.proj_comp_aeval (f : MvPolynomial (Fin n) Λ)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf, map_zero] at h
  exact h

/-- **The obstruction map**: the `R`-linear map `J/J² → I` sending the class
of `f ∈ J` to `f(a'_1, …, a'_n)`, where `a'_i` are the chosen lifts. It is the map induced
on conormal modules by the morphism of extensions `Lift.hom`; its target is `I/I²`, which is
`I` because `I² = 0` (see `Situation.cotangentEquivKernel`). -/
@[stacks 07YI "the map J/J² → I, f ↦ f(a'_1, …, a'_n)"]
noncomputable def Lift.obsHom (l : t.Lift) :
    P.toExtension.Cotangent →ₗ[R] t.ext.Cotangent :=
  Algebra.Extension.Cotangent.map l.hom

/-- **The obstruction map sends the class of `f ∈ J` to `f(a'_1, …, a'_n) ∈ I`**, through the
identification `I/I² = I` of `Situation.cotangentEquivKernel`. -/
@[stacks 07YI "o_x(A') is represented by the map f ↦ f(a'_1, …, a'_n)"]
theorem Lift.obsHom_mk (l : t.Lift) (f : P.ker) :
    l.obsHom (Algebra.Extension.Cotangent.mk f) =
      t.cotangentEquivKernel
        ⟨MvPolynomial.aeval l.val (f : MvPolynomial (Fin n) Λ), l.aeval_mem_kernel f⟩ :=
  Algebra.Extension.Cotangent.map_mk l.hom f

/-- The obstruction map kills the class of `f ∈ J` exactly when `f(a'_1, …, a'_n) = 0`. -/
private theorem Lift.obsHom_mk_eq_zero_iff (l : t.Lift) (f : P.ker) :
    l.obsHom (Algebra.Extension.Cotangent.mk f) = 0 ↔
      MvPolynomial.aeval l.val (f : MvPolynomial (Fin n) Λ) = 0 := by
  rw [l.obsHom_mk f, t.cotangentEquivKernel.map_eq_zero_iff, Subtype.ext_iff]
  rfl

/-- The difference of the obstruction maps of two families of lifts is `Hom.sub` applied after
the differential of the naive cotangent complex. -/
private theorem Lift.obsHom_sub_obsHom (l l' : t.Lift) (z : P.toExtension.Cotangent) :
    l.obsHom z - l'.obsHom z = (l.hom.sub l'.hom) (P.toExtension.cotangentComplex z) :=
  LinearMap.congr_fun (Algebra.Extension.Cotangent.map_sub_map l.hom l'.hom) z

/-- Read in `I` through `Situation.cotangentEquivKernel`, the obstruction map sends the class
of `f ∈ J` to `f(a'_1, …, a'_n)`. -/
theorem Lift.coe_cotangentEquivKernel_symm_obsHom_mk (l : t.Lift) (f : P.ker) :
    ((t.cotangentEquivKernel.symm (l.obsHom (Algebra.Extension.Cotangent.mk f))).1 :
        t.thick) =
      MvPolynomial.aeval l.val (f : MvPolynomial (Fin n) Λ) := by
  rw [l.obsHom_mk f, LinearEquiv.symm_apply_apply]

/-- The difference of two families of lifts, read on the variable `x_i`. -/
theorem Lift.coe_hom_subToKer_X (l l' : t.Lift) (i : Fin n) :
    ((l.hom.subToKer l'.hom (MvPolynomial.X i)).1 : t.thick) = l.val i - l'.val i := by
  have h : ((l.hom.subToKer l'.hom (MvPolynomial.X i)).1 : t.thick) =
      MvPolynomial.aeval l.val (MvPolynomial.X i) -
        MvPolynomial.aeval l'.val (MvPolynomial.X i) :=
    Algebra.Extension.Hom.subToKer_apply_coe l.hom l'.hom (MvPolynomial.X i)
  rw [h, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

/-- The correcting map `Hom.sub` of two families of lifts, evaluated on the basis element
`dx_i`, is the class of `a'_i - a''_i`. -/
theorem Lift.sub_cotangentSpaceBasis (l l' : t.Lift) (i : Fin n) :
    (l.hom.sub l'.hom) (P.cotangentSpaceBasis i) =
      Algebra.Extension.Cotangent.mk (l.hom.subToKer l'.hom (MvPolynomial.X i)) := by
  rw [P.cotangentSpaceBasis_apply i]
  exact Algebra.Extension.Hom.sub_one_tmul l.hom l'.hom (MvPolynomial.X i)

end Lifts

end Situation

/-! ### The obstruction module -/

/-- **The obstruction module**,
`𝒪_x(M) = Hom_R(J/J², M)/Hom_R(R^{⊕n}, M)`: the `R`-linear maps out of the conormal module
`J/J²` of the presentation, modulo those that factor through the differential
`J/J² → ⊕_i R dx_i` of the naive cotangent complex. The quotient is taken by the range of
precomposition with that differential; since `⊕_i R dx_i` is free on the `dx_i`, the
submodule divided out is the image of `Hom_R(R^{⊕n}, M)`. -/
@[stacks 07YI "the obstruction module Hom_R(J/J², M)/Hom_R(R^{⊕n}, M)"]
abbrev obstructionModule (P : Algebra.Generators Λ R (Fin n)) (M : Type v) [AddCommGroup M]
    [Module R M] :=
  (P.toExtension.Cotangent →ₗ[R] M) ⧸
    LinearMap.range ((LinearMap.lcomp R M (NaiveCotangent.NL P).d) :
      (P.toExtension.CotangentSpace →ₗ[R] M) →ₗ[R] (P.toExtension.Cotangent →ₗ[R] M))

/-- The differential of the two-term complex of the presentation is the canonical map
`J/J² → ⊕_i R dx_i`. -/
theorem nl_d_eq (P : Algebra.Generators Λ R (Fin n)) :
    (NaiveCotangent.NL P).d = P.toExtension.cotangentComplex :=
  rfl

/-- The obstruction module `Hom_R(J/J², M)/Hom_R(R^{⊕n}, M)` is
`Ext¹_R(NL_{R/Λ}, M)`: the comparison of Stacks 0GPU,
`NaiveCotangent.extOne_naiveCotangentComplex_addEquiv_cokernel`, read at the presentation of
the key example. -/
@[stacks 07YI "Hom_R(J/J², M)/Hom_R(R^{⊕n}, M) = Ext¹_R(NL_{R/Λ}, M)"]
noncomputable def obstructionModuleAddEquivExtOne
    (P : Algebra.Generators Λ R (Fin n)) (M : Type v) [AddCommGroup M] [Module R M] :=
  (NaiveCotangent.extOne_naiveCotangentComplex_addEquiv_cokernel (N := M) P).symm

namespace Situation

variable {P : Algebra.Generators Λ R (Fin n)} {t : Situation P}

/-- **The obstruction element `o_x(A')`**: the class in the obstruction module
of the map `J/J² → I`, `f ↦ f(a'_1, …, a'_n)`. -/
@[stacks 07YI "the obstruction element o_x(A')"]
noncomputable def obsClass (l : t.Lift) : obstructionModule P t.ext.Cotangent :=
  Submodule.Quotient.mk l.obsHom

/-- **`o_x(A')` does not depend on the choice of the lifts `a'_i`.** Two
families of lifts induce morphisms of extensions whose maps on conormal modules differ by
precomposition with the differential of the naive cotangent complex, so their classes in
`Hom_R(J/J², I)/Hom_R(R^{⊕n}, I)` agree. -/
@[stacks 07YI "o_x(A') is independent of the choice of lifts"]
theorem obsClass_eq (l l' : t.Lift) : obsClass l = obsClass l' := by
  refine (Submodule.Quotient.eq _).2 ⟨l.hom.sub l'.hom, ?_⟩
  exact LinearMap.ext fun z => (l.obsHom_sub_obsHom l' z).symm

/-- If `x` lifts to `Spec A'` then the obstruction element vanishes: evaluating at the
coordinates of a lift kills `J`. -/
theorem obsClass_eq_zero_of_hasLift (l : t.Lift) (h : HasLift t) : obsClass l = 0 := by
  obtain ⟨y, hy⟩ := h
  let l₀ : t.Lift :=
    { val := fun i => y (P.val i)
      proj_val := fun i => by
        have := AlgHom.congr_fun hy (P.val i)
        simpa using this }
  have hzero : l₀.obsHom = 0 := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨f, rfl⟩ := exists_cotangent_mk P z
    have hf : MvPolynomial.aeval P.val (f : MvPolynomial (Fin n) Λ) = 0 := (mem_ker_iff _).1 f.2
    rw [LinearMap.zero_apply, l₀.obsHom_mk_eq_zero_iff]
    have hc := MvPolynomial.comp_aeval_apply (f := P.val) y (f : MvPolynomial (Fin n) Λ)
    rw [hf, map_zero] at hc
    exact hc.symm
  rw [obsClass_eq l l₀, obsClass, hzero]
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.zero_mem _)

/-- If the obstruction element vanishes then `x` lifts to `Spec A'`: a map
`δ : ⊕_i R dx_i → I` with `δ ∘ d = o_x` corrects the chosen lifts `a'_i` to lifts
`a'_i - δ(dx_i)` at which every `f ∈ J` vanishes, and the corrected evaluation therefore
factors through `R`. -/
theorem hasLift_of_obsClass_eq_zero (l : t.Lift) (h : obsClass l = 0) : HasLift t := by
  have hmem : l.obsHom ∈
      LinearMap.range ((LinearMap.lcomp R t.ext.Cotangent (NaiveCotangent.NL P).d) :
        (P.toExtension.CotangentSpace →ₗ[R] t.ext.Cotangent) →ₗ[R]
          (P.toExtension.Cotangent →ₗ[R] t.ext.Cotangent)) :=
    (Submodule.Quotient.mk_eq_zero _).1 h
  obtain ⟨δ, hδ⟩ := hmem
  set ε : Fin n → t.kernel :=
    fun i => t.cotangentEquivKernel.symm (δ (P.cotangentSpaceBasis i)) with hε
  have hεval : ∀ i, Algebra.Extension.Cotangent.mk (ε i) = δ (P.cotangentSpaceBasis i) :=
    fun i => t.cotangentEquivKernel.apply_symm_apply _
  have hεker : ∀ i, t.proj ((ε i).1 : t.thick) = 0 := fun i => RingHom.mem_ker.1 (ε i).2
  let l' : t.Lift :=
    { val := fun i => l.val i - ((ε i).1 : t.thick)
      proj_val := fun i => by rw [map_sub, hεker i, sub_zero, l.proj_val i] }
  have hsub : l'.hom.sub l.hom = -δ := by
    refine Module.Basis.ext P.cotangentSpaceBasis fun i => ?_
    have h2 : l'.hom.subToKer l.hom (MvPolynomial.X i) = -(ε i) := by
      refine Subtype.ext ?_
      rw [Lift.coe_hom_subToKer_X l' l i]
      change l.val i - ((ε i).1 : t.thick) - l.val i = -((ε i).1 : t.thick)
      ring
    have h3 : Algebra.Extension.Cotangent.mk (-(ε i)) =
        -(δ (P.cotangentSpaceBasis i)) := by
      rw [← hεval i]
      exact map_neg _ _
    rw [Lift.sub_cotangentSpaceBasis l' l i, h2, h3, LinearMap.neg_apply]
  have hzero : l'.obsHom = 0 := by
    refine LinearMap.ext fun z => ?_
    have h1 := l'.obsHom_sub_obsHom l z
    have h2 : δ (P.toExtension.cotangentComplex z) = l.obsHom z :=
      LinearMap.congr_fun hδ z
    rw [hsub, LinearMap.neg_apply, h2] at h1
    have h3 := sub_eq_iff_eq_add.1 h1
    rw [neg_add_cancel] at h3
    rw [LinearMap.zero_apply]
    exact h3
  have hkill : ∀ f : MvPolynomial (Fin n) Λ, f ∈ P.ker →
      MvPolynomial.aeval l'.val f = 0 := by
    intro f hf
    exact (l'.obsHom_mk_eq_zero_iff ⟨f, hf⟩).1 (by rw [hzero, LinearMap.zero_apply])
  have hsurj : Function.Surjective
      ⇑(MvPolynomial.aeval P.val : MvPolynomial (Fin n) Λ →ₐ[Λ] R) :=
    fun s => ⟨P.σ s, P.aeval_val_σ s⟩
  have hkerEq : RingHom.ker (MvPolynomial.aeval P.val :
      MvPolynomial (Fin n) Λ →ₐ[Λ] R) = P.ker :=
    (Algebra.Generators.ker_eq_ker_aeval_val P).symm
  refine ⟨(Ideal.Quotient.liftₐ
      (RingHom.ker (MvPolynomial.aeval P.val : MvPolynomial (Fin n) Λ →ₐ[Λ] R))
      (MvPolynomial.aeval l'.val)
      (fun f hf => hkill f (hkerEq ▸ hf))).comp
    (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom, ?_⟩
  refine AlgHom.ext fun s => ?_
  obtain ⟨g, rfl⟩ := hsurj s
  have hgo : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm
      (MvPolynomial.aeval P.val g) =
      Ideal.Quotient.mk (RingHom.ker (MvPolynomial.aeval P.val :
        MvPolynomial (Fin n) Λ →ₐ[Λ] R)) g := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  have hfin := AlgHom.congr_fun l'.proj_comp_aeval g
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at hfin
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hgo]
  exact hfin

/-- **`o_x(A') = 0` if and only if `x` lifts.** This is condition (iii) of
Stacks 07YG for the key example. -/
@[stacks 07YI "o_x(A') = 0 if and only if Lift(x, A') is nonempty"]
theorem obsClass_eq_zero_iff (l : t.Lift) : obsClass l = 0 ↔ HasLift t :=
  ⟨hasLift_of_obsClass_eq_zero l, obsClass_eq_zero_of_hasLift l⟩

/-! ### Functoriality -/

/-- A morphism of deformation situations carries a family of lifts to a family of lifts: if
`ι : A' → B'` and `κ : A → B` commute with the surjections and `κ ∘ x = y`, then
`ι(a'_1), …, ι(a'_n)` are lifts of the coordinates of `y`. -/
def Lift.pushforward {t₂ : Situation P} (ι : t.thick →ₐ[Λ] t₂.thick)
    (κ : t.base →ₐ[Λ] t₂.base) (hcomm : t₂.proj.comp ι = κ.comp t.proj)
    (hobj : κ.comp t.obj = t₂.obj) (l : t.Lift) : t₂.Lift where
  val i := ι (l.val i)
  proj_val i := by
    have h1 := AlgHom.congr_fun hcomm (l.val i)
    have h2 := AlgHom.congr_fun hobj (P.val i)
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
    rw [AlgHom.comp_apply] at h2
    rw [h1, l.proj_val i, h2]

/-- **Functoriality of the obstruction element.** For a morphism of deformation
situations `(x, A' → A) → (y, B' → B)` the obstruction map of `x` is carried to the
obstruction map of `y` by the map `I → I₂` induced on kernels by `A' → B'`, so `o_x(A')`
maps to `o_y(B')`. -/
@[stacks 07YI "a morphism of deformation situations carries o_x(A') to o_y(B')"]
theorem coe_cotangentEquivKernel_symm_obsHom_pushforward {t₂ : Situation P}
    (ι : t.thick →ₐ[Λ] t₂.thick) (κ : t.base →ₐ[Λ] t₂.base)
    (hcomm : t₂.proj.comp ι = κ.comp t.proj) (hobj : κ.comp t.obj = t₂.obj) (l : t.Lift)
    (f : P.ker) :
    ((t₂.cotangentEquivKernel.symm
          ((l.pushforward ι κ hcomm hobj).obsHom
            (Algebra.Extension.Cotangent.mk f))).1 : t₂.thick) =
      ι (((t.cotangentEquivKernel.symm
        (l.obsHom (Algebra.Extension.Cotangent.mk f))).1 : t.thick)) := by
  rw [Lift.coe_cotangentEquivKernel_symm_obsHom_mk,
    Lift.coe_cotangentEquivKernel_symm_obsHom_mk]
  exact (MvPolynomial.comp_aeval_apply (f := l.val) ι _).symm

end Situation

end Deformation.Artin.KeyExample
