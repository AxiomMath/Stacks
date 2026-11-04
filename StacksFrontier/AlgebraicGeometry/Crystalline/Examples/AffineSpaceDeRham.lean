module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# Affine space over the crystalline base, and its completed de Rham complex

Fix a prime `p` and a number `r` of variables.  This module sets up the situation of the example
of [Stacks, Tag 07LK]: the base `A = 𝐙_p` with its divided power ideal `(p)`, the coordinate
ring `C = 𝐅_p[x_1, …, x_r]` presented as `C = P/J = P/pP` with `P = 𝐙_p[x_1, …, x_r]`, the
schemes `X = Spec(C)` and `S = Spec(A)`, and the completed thickening `D = P^∧` with its divided
power ideal.  On top of that it builds the complex displayed in the source,

`D → Ω¹_D → Ω²_D → ⋯`,

as the `p`-adic completion of the divided power de Rham complex of `D` over `A`.

## Main definitions

* `Crystalline.AffineSpaceCrystallineSetup` fixes `p` and `r`; the projections `A`, `P`, `J`,
  `C`, `X`, `S`, `D` give the rings, the ideal, the schemes and the completion.
* `Crystalline.AffineSpaceCrystallineSetup.baseDividedPowers`,
  `polynomialDividedPowers` and `completedDividedPowers` give the three divided power
  structures: the canonical ones on `(p) ⊆ 𝐙_p`, their extension to `J = pP`, and the completed
  structure on the completed ideal of `D`.
* `Crystalline.AffineSpaceCrystallineSetup.forms` is `Ω^i_{D/A,δ}`, the `i`-th module of divided
  power differential forms of `D` over `A` ([Stacks, Tag 07HZ]), read as an `A`-module, and
  `completedForms` is its `p`-adic completion `Ω^i_D`, the `i`-th term of the displayed complex.
* `Crystalline.AffineSpaceCrystallineSetup.completedDifferential` is the completion of the
  divided power de Rham differential and
  `Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNat` is the resulting cochain complex of
  abelian groups indexed by `ℕ`.

## Main results

* `Crystalline.AffineSpaceCrystallineSetup.coordinateRingEquiv` identifies `C = P/J` with the
  polynomial ring over `𝐅_p`, and `J_eq_span` identifies `J` with `pP`.
* `Crystalline.AffineSpaceCrystallineSetup.dividedPowers_extend` records that the divided powers
  of `(p) ⊆ 𝐙_p` extend along `𝐙_p → P` (which is [Stacks, Tag 07H1] for a principal ideal), so
  that `D` with its divided power ideal is a situation as in [Stacks, Section 07J7].
* `Crystalline.AffineSpaceCrystallineSetup.completedDifferential_ofForms` says that the completed
  differential agrees with the divided power de Rham differential on the dense image of
  `Ω^i_{D/A,δ}`, which is what characterises it, and
  `Crystalline.AffineSpaceCrystallineSetup.completedDifferential_comp` says that consecutive
  completed differentials compose to zero.

## The relation to crystalline cohomology

What is set up here is the *complex* of the source: the terms `Ω^i_D`, the differential, and the
cochain complex `deRhamComplexNat`.  That it computes `H^j(Cris(X/S), 𝒪_{X/S})`, and the four
conclusions the example draws from it, are proved for crystalline cohomology in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceCrystallineCohomology`, through
[Stacks, Lemma 60.21.4, Tag 07LH] for the presentation `P → Γ(X, 𝒪_X)`; the computations on the
complex itself are in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamVanishing`,
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamDegreeZero` and
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamTopDegree`.

## Implementation notes

The polynomial ring is `MvPolynomial (Fin r) ℤ_[p]` and `J` is defined as the image of `(p)`
under the coefficient map, with `J_eq_span` identifying it with `pP`; the quotient presentation of
`C` is retained rather than replaced by the polynomial ring over `ZMod p`, since the presentation
is what carries the divided powers.  The completion `D` is Mathlib's adic completion of `P` for
the ideal `(p)`.

The divided power de Rham differential of [Stacks, Tag 07HZ] is `A`-linear, and `(p) ⊆ A`
generates the ideal used for the completion, so `Ω^i_D` is taken to be the adic completion of
`Ω^i_{D/A,δ}` for the ideal `(p) ⊆ A`; as a submodule of `Ω^i`, `p^e` cuts out the same thing
whether `p^e` is read in `A` or in `D`.  This makes the completed differential Mathlib's
`AdicCompletion.map` of an `A`-linear map.  Degree zero of the de Rham complex is Mathlib's
degree-zero exterior power, following the convention of Tag 07HZ, rather than `D` itself.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace Crystalline

/-- The prime and the dimension of affine space in the crystalline setup of the example of
[Stacks, Tag 07LK]. -/
public structure AffineSpaceCrystallineSetup where
  /-- The residue characteristic. -/
  p : ℕ
  /-- The residue characteristic is prime. -/
  [prime : Fact p.Prime]
  /-- The dimension of affine space. -/
  r : ℕ

attribute [instance] AffineSpaceCrystallineSetup.prime

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

/-- The crystalline base ring `A = 𝐙_p`. -/
public abbrev A := PadicInt T.p

/-- The polynomial lift `P = 𝐙_p[x_1, …, x_r]`. -/
public abbrev P := MvPolynomial (Fin T.r) T.A

/-- The divided power ideal `(p) ⊆ 𝐙_p` of the crystalline base. -/
public abbrev baseIdeal : Ideal T.A := Ideal.span {(T.p : T.A)}

/-- The canonical divided powers on `(p) ⊆ 𝐙_p`. -/
public def baseDividedPowers : DividedPowers T.baseIdeal := PadicInt.dividedPowers T.p

/-- The ideal `J = pP`, expressed as the extension of `(p)` along the coefficient map. -/
public abbrev J : Ideal T.P := T.baseIdeal.map (MvPolynomial.C : T.A →+* T.P)

/-- The crystalline affine-space coordinate ring `C = P/J`. -/
public abbrev C := T.P ⧸ T.J

/-- Affine space `X = Spec(C)` over the residue field. -/
public abbrev X : Scheme := Spec (.of T.C)

/-- The crystalline base scheme `S = Spec(A)`. -/
public abbrev S : Scheme := Spec (.of T.A)

/-- The `p`-adic completion `D = P^∧` of the polynomial lift. -/
public abbrev D := AdicCompletion (DividedPowers.pAdicIdeal (A := T.P) T.p) T.P

/-- The extended ideal is the principal ideal `pP`. -/
public theorem J_eq_span : T.J = Ideal.span {(T.p : T.P)} := by
  rw [J, baseIdeal, Ideal.map_span]
  simp

/-- The quotient `C = P/J` of the polynomial lift is canonically the polynomial ring over `𝐅_p`.
The specified behaviour on constants and on the variables determines the equivalence. -/
public def coordinateRingEquiv :
    { e : T.C ≃+* MvPolynomial (Fin T.r) (ZMod T.p) //
      (∀ a : T.A, e (Ideal.Quotient.mk T.J (MvPolynomial.C a)) =
        MvPolynomial.C (PadicInt.toZMod a)) ∧
      (∀ i : Fin T.r, e (Ideal.Quotient.mk T.J (MvPolynomial.X i)) =
        MvPolynomial.X i) } := by
  let e₁ := (MvPolynomial.quotientEquivQuotientMvPolynomial
    (σ := Fin T.r) T.baseIdeal).symm.toRingEquiv
  let e₀ : T.A ⧸ T.baseIdeal ≃+* ZMod T.p :=
    (Ideal.quotEquivOfEq (PadicInt.maximalIdeal_eq_span_p (p := T.p)).symm).trans
      (PadicInt.residueField (p := T.p))
  let e₂ := MvPolynomial.mapEquiv (Fin T.r) e₀
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · intro a
    have h : e₁ (Ideal.Quotient.mk T.J (MvPolynomial.C a)) =
        MvPolynomial.C (Ideal.Quotient.mk _ a) := by
      simp [e₁, MvPolynomial.quotientEquivQuotientMvPolynomial]
    rw [RingEquiv.trans_apply, h]
    simp [e₂, e₀, PadicInt.residueField]
  · intro i
    have h : e₁ (Ideal.Quotient.mk T.J (MvPolynomial.X i)) = MvPolynomial.X i := by
      simp [e₁, MvPolynomial.quotientEquivQuotientMvPolynomial]
    rw [RingEquiv.trans_apply, h]
    simp [e₂]

/-- The canonical divided powers on `(p) ⊆ 𝐙_p` extend along the coefficient map `𝐙_p → P`.
This is [Stacks, Tag 07H1] for the principal ideal `(p)`. -/
public theorem dividedPowers_extend :
    DividedPowers.Extends T.baseDividedPowers (MvPolynomial.C : T.A →+* T.P) :=
  DividedPowers.DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat
    (_root_.DividedPowerRing.of T.A T.baseIdeal T.baseDividedPowers) (MvPolynomial.C : T.A →+* T.P)
    (Or.inr (Or.inl (inferInstanceAs T.baseIdeal.IsPrincipal)))

/-- Divided powers on `J = pP` extending those of the crystalline base. -/
public def polynomialDividedPowers : DividedPowers T.J :=
  Classical.choose T.dividedPowers_extend

/-- The coefficient map `𝐙_p → P` is a divided power morphism for the extended structure. -/
public theorem polynomialDividedPowers_isDPMorphism :
    DividedPowers.IsDPMorphism T.baseDividedPowers T.polynomialDividedPowers
      (MvPolynomial.C : T.A →+* T.P) :=
  Classical.choose_spec T.dividedPowers_extend

/-- The element `p` is zero, hence nilpotent, modulo `J`. -/
public theorem p_nilpotent_mod_J :
    IsNilpotent (Ideal.Quotient.mk T.J (T.p : T.P)) := by
  have hp : (T.p : T.P) ∈ T.J := by
    rw [T.J_eq_span]
    exact Ideal.subset_span (by simp)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
  exact IsNilpotent.zero

/-- The divided power ideal of `D`: the kernel of `D → C`, which carries the completed divided
powers of [Stacks, Tag 07KD]. -/
public abbrev completedIdeal : Ideal T.D :=
  DividedPowers.completionIdeal T.J T.p T.p_nilpotent_mod_J

/-- The completed divided power structure on `D`, from [Stacks, Tag 07KD]. -/
public abbrev completedDividedPowers : DividedPowers T.completedIdeal :=
  (DividedPowers.completedDividedPowers T.J T.polynomialDividedPowers T.p
    T.p_nilpotent_mod_J).1

/-! ### The completed divided power de Rham complex of `D` -/

/-- `Ω¹_{D/A,δ}`, the module of divided power differentials of `D` over the crystalline base
`A = 𝐙_p`, as a `D`-module. -/
public abbrev differentials :=
  dividedPowerDifferentials (A := T.A) T.completedDividedPowers

/-- The universal divided power differential `D → Ω¹_{D/A,δ}`. -/
public abbrev differential (b : T.D) : T.differentials :=
  dividedPowerDifferential (A := T.A) T.completedDividedPowers b
/-- `Ω^i_{D/A,δ}`, the `i`-th module of divided power differential forms of `D` over the
crystalline base `A = 𝐙_p` ([Stacks, Tag 07HZ]). -/
public def forms (i : ℕ) : Type :=
  dividedPowerDifferentialForms (A := T.A) T.completedDividedPowers i

/-- The additive group of `Ω^i_{D/A,δ}`. -/
public instance instAddCommGroupForms (i : ℕ) : AddCommGroup (T.forms i) :=
  inferInstanceAs (AddCommGroup
    (dividedPowerDifferentialForms (A := T.A) T.completedDividedPowers i))

/-- The `D`-module structure on `Ω^i_{D/A,δ}`. -/
public instance instModuleFormsD (i : ℕ) : Module T.D (T.forms i) :=
  inferInstanceAs (Module T.D
    (dividedPowerDifferentialForms (A := T.A) T.completedDividedPowers i))

/-- The `A`-module structure on `Ω^i_{D/A,δ}`, by restriction of scalars along `A → D`. -/
public instance instModuleFormsA (i : ℕ) : Module T.A (T.forms i) :=
  Module.restrictScalars T.A T.D (T.forms i)

/-- The `A`-action on `Ω^i_{D/A,δ}` is the `D`-action restricted along `A → D`. -/
public instance instIsScalarTowerForms (i : ℕ) : IsScalarTower T.A T.D (T.forms i) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The divided power de Rham differential `Ω^i_{D/A,δ} → Ω^{i+1}_{D/A,δ}` of
[Stacks, Tag 07HZ], which is `A`-linear. -/
public def deRhamDifferential (i : ℕ) : T.forms i →ₗ[T.A] T.forms (i + 1) :=
  (dividedPowerDeRhamComplex (A := T.A) T.completedDividedPowers).differential i

/-- `Ω^i_D`, the `i`-th term of the complex displayed in [Stacks, Tag 07LK]: the `p`-adic
completion of `Ω^i_{D/A,δ}`. -/
public def completedForms (i : ℕ) : Type := AdicCompletion T.baseIdeal (T.forms i)

/-- The additive group of `Ω^i_D`. -/
public instance instAddCommGroupCompletedForms (i : ℕ) : AddCommGroup (T.completedForms i) :=
  inferInstanceAs (AddCommGroup (AdicCompletion T.baseIdeal (T.forms i)))

/-- The `A`-module structure on `Ω^i_D`. -/
public instance instModuleCompletedForms (i : ℕ) : Module T.A (T.completedForms i) :=
  inferInstanceAs (Module T.A (AdicCompletion T.baseIdeal (T.forms i)))

/-- The canonical map `Ω^i_{D/A,δ} → Ω^i_D` onto the dense image in the completion. -/
public def ofForms (i : ℕ) : T.forms i →ₗ[T.A] T.completedForms i :=
  AdicCompletion.of T.baseIdeal (T.forms i)

/-- The `p`-adically completed divided power de Rham differential `Ω^i_D → Ω^{i+1}_D`. -/
public def completedDifferential (i : ℕ) :
    T.completedForms i →ₗ[T.A] T.completedForms (i + 1) :=
  (AdicCompletion.map T.baseIdeal (T.deRhamDifferential i)).restrictScalars T.A

/-- The completed differential agrees with the divided power de Rham differential on the dense
image of `Ω^i_{D/A,δ}` in `Ω^i_D`.  This property characterises it, since the image is dense. -/
public theorem completedDifferential_ofForms (i : ℕ) (ω : T.forms i) :
    T.completedDifferential i (T.ofForms i ω) = T.ofForms (i + 1) (T.deRhamDifferential i ω) :=
  AdicCompletion.map_of T.baseIdeal (T.deRhamDifferential i) ω

/-- Consecutive completed differentials compose to zero. -/
public theorem completedDifferential_comp (i : ℕ) :
    (T.completedDifferential (i + 1)).comp (T.completedDifferential i) = 0 := by
  have h : (T.deRhamDifferential (i + 1)).comp (T.deRhamDifferential i) = 0 :=
    (dividedPowerDeRhamComplex (A := T.A) T.completedDividedPowers).differential_squared i
  have h2 : (AdicCompletion.map T.baseIdeal (T.deRhamDifferential (i + 1))).comp
      (AdicCompletion.map T.baseIdeal (T.deRhamDifferential i)) = 0 := by
    rw [AdicCompletion.map_comp, h, AdicCompletion.map_zero]
  ext x
  exact LinearMap.congr_fun h2 x

/-- The completed divided power de Rham complex `D → Ω¹_D → Ω²_D → ⋯` of `D` over `A = 𝐙_p`,
as a cochain complex of abelian groups indexed by `ℕ`.  This is the complex displayed in
[Stacks, Tag 07LK]; it is concentrated in degrees `0, …, r` by
`Crystalline.AffineSpaceCrystallineSetup.subsingleton_completedForms`. -/
public def deRhamComplexNat : CochainComplex AddCommGrpCat.{0} ℕ :=
  CochainComplex.of (fun i ↦ AddCommGrpCat.of (T.completedForms i))
    (fun i ↦ AddCommGrpCat.ofHom (T.completedDifferential i).toAddMonoidHom)
    (fun i ↦ by
      ext x
      exact LinearMap.congr_fun (T.completedDifferential_comp i) x)

/-- The degree-`i` term of the complex is `Ω^i_D`. -/
public theorem deRhamComplexNat_X (i : ℕ) :
    T.deRhamComplexNat.X i = AddCommGrpCat.of (T.completedForms i) := rfl

/-- The differential of the complex is the completed de Rham differential. -/
public theorem deRhamComplexNat_d (i : ℕ) (x : T.completedForms i) :
    T.deRhamComplexNat.d i (i + 1) x = T.completedDifferential i x := by
  simp only [deRhamComplexNat, CochainComplex.of, CochainComplex.of_d]
  rfl

end AffineSpaceCrystallineSetup

end Crystalline

end
