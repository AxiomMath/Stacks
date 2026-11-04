module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Functoriality

/-!
# The exterior calculus of the divided power de Rham complex

[Stacks, Tag 07HZ] gives the divided power de Rham complex
`Ω^*_{B/A,δ} = (B → Ω¹_{B/A,δ} → Ω²_{B/A,δ} → ⋯)` of a divided power ring `(B, J, δ)` over `A`,
as `Crystalline.dividedPowerDeRhamComplex`, pinned by the value
`d (f₀ · d f₁ ∧ ⋯ ∧ d fᵢ) = d f₀ ∧ ⋯ ∧ d fᵢ` on the standard generators.  That pinning is all
the library records about it.  This module derives from it the three identities of exterior
calculus:

* the **Leibniz rule** `d (f · ω) = f · d ω + d f ∧ ω`;
* that the wedge is **alternating** on one-forms, `η ∧ η ∧ ω = 0`;
* the **graded Leibniz rule against a one-form**, in the form
  `d (η ∧ ω) + η ∧ d ω = (d η) ∧ ω` read in the exterior algebra, and hence
  `d (η ∧ ω) = - η ∧ d ω` for a closed one-form `η`;
* the **bigraded graded Leibniz rule** `d (ω ∧ η) = d ω ∧ η + (-1)^i ω ∧ d η`, with neither
  argument confined to degree one.

Together with `d ∘ d = 0`, already available, these are exactly the hypotheses that
`Crystalline.CompletedDeRham.IsGradedLeibniz` and
`Crystalline.CompletedDeRham.IsGradedExterior` carry as parameters, which is why they are proved
here: the family of forms of the completed de Rham complex of [Stacks, Tag 07LG] is a carried
parameter pinned by those identities alone, and nobody had supplied them for the genuine divided
power forms.

## How they are proved

The de Rham differential is only `A`-linear, so none of these is a formal consequence of
linearity.  Each is proved from the generator formula:

* The Leibniz rule is an induction over the `B`-span of the standard generators, with the scalar
  `f` universally quantified so that the scalar step `ω ↦ b · ω` is available — for a fixed `f`
  that step would need the rule for the scalar `f · b`, which is not the inductive hypothesis.
  On a generator both sides collapse, via `Crystalline.leftWedge_ιMulti`, to the same
  combination of `d f₀ ∧ ω'` and `d f ∧ ω'`, by the Leibniz rule for the universal divided power
  differential.
* Exactness of `d f` and the alternating property are immediate, the first from the generator
  formula at `d 1 = 0` and the second from `ι x · ι x = 0` in the exterior algebra.
* The graded rule is first proved for an *exact* one-form `η = d b` purely formally:
  `d b ∧ ω = d (b · ω) - b · d ω` by the Leibniz rule, and applying `d` kills the first term by
  `d ∘ d = 0` and expands the second by the Leibniz rule again.  The general case follows by
  additivity in `η`, since the one-forms `b · d f` additively generate `Ω¹_{B/A,δ}` and both
  sides of the identity are additive in `η`.  It is stated inside `ExteriorAlgebra B Ω¹_{B/A,δ}`
  because the correction term `(d η) ∧ ω` multiplies by a *two*-form, which
  `Crystalline.leftWedge` cannot express.

## Main definitions

* `Crystalline.dividedPowerDeRham` — the de Rham differential read on the exterior powers
  themselves rather than on the `RestrictScalars` synonyms, which is where the identification of
  the two is paid.
* `Crystalline.dividedPowerWedge` — the wedge product `Ω^i × Ω¹ → Ω^{i+1}` of divided power
  forms, in the variance `ω ∧ η ↦ η ∧ ω` that the completed de Rham complex uses.
* `Crystalline.twoWedge` — exterior multiplication by a two-form, `exteriorPower.wedgeMul 2 i`
  reindexed, which names the correction term of the graded Leibniz rule.

## Main results

* `Crystalline.dividedPowerDifferential_mul` — the Leibniz rule for the universal divided power
  differential.
* `Crystalline.dividedPowerDeRham_smul` — **the Leibniz rule
  `d (f · ω) = f · d ω + d f ∧ ω`.**
* `Crystalline.dividedPowerDeRham_oneForm_eq_zero` — an exact one-form is closed.
* `Crystalline.leftWedge_leftWedge_self` — the wedge is alternating on one-forms.
* `Crystalline.coe_dividedPowerDeRham_leftWedge` and
  `Crystalline.dividedPowerDeRham_leftWedge` — **the graded Leibniz rule against a one-form**, in
  the exterior algebra and as an identity of forms.
* `Crystalline.dividedPowerDeRham_leftWedge_of_closed` — **`d (η ∧ ω) = - η ∧ d ω` for a closed
  one-form `η`.**
* `Crystalline.coe_dividedPowerDeRham_wedgeMul` and
  `Crystalline.dividedPowerDeRham_wedgeMul` — **the bigraded graded Leibniz rule
  `d (ω ∧ η) = d ω ∧ η + (-1)^i ω ∧ d η`**, in the exterior algebra and as an identity of forms.
  This is the previous item with the restriction to a closed one-form lifted: the correction
  term `ω ∧ d η` has a name once the wedge is not confined to one-forms.
* `Crystalline.mapDifferentialFormsOfDPMorphism_wedge`,
  `Crystalline.mapDifferentialFormsOfDPMorphism_leftWedge` — **the comparison of forms along a
  divided power morphism respects the wedge product.**
* `Crystalline.mapDifferentialFormsOfDPMorphism_deRham` — **the comparison of forms along a
  divided power morphism is a map of divided power de Rham complexes**, `ψ (d ω) = d (ψ ω)`.
  Together with the previous item these are exactly the two compatibilities a base change map
  of de Rham complexes needs of a graded comparison of forms.
* `Crystalline.mapDifferentialFormsOfDPMorphism_oneEquiv` — in degree one the comparison of
  forms is the comparison of differentials.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

universe u v

namespace Crystalline

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (hJ : DividedPowers J)

/-! ### The Leibniz rule for the universal divided power differential -/

/-- The universal divided power differential is additive. -/
public theorem dividedPowerDifferential_add (f g : B) :
    dividedPowerDifferential (A := A) hJ (f + g) =
      dividedPowerDifferential (A := A) hJ f + dividedPowerDifferential (A := A) hJ g := by
  unfold dividedPowerDifferential
  rw [map_add, map_add]

/-- The universal divided power differential is compatible with subtraction. -/
public theorem dividedPowerDifferential_sub (f g : B) :
    dividedPowerDifferential (A := A) hJ (f - g) =
      dividedPowerDifferential (A := A) hJ f - dividedPowerDifferential (A := A) hJ g := by
  unfold dividedPowerDifferential
  rw [map_sub, map_sub]

/-- **The Leibniz rule for the universal divided power differential** `d : B → Ω¹_{B/A,δ}`: it is
the Kähler differential followed by a quotient map, so it inherits the product rule. -/
public theorem dividedPowerDifferential_mul (f g : B) :
    dividedPowerDifferential (A := A) hJ (f * g) =
      f • dividedPowerDifferential (A := A) hJ g + g • dividedPowerDifferential (A := A) hJ f := by
  unfold dividedPowerDifferential
  rw [Derivation.leibniz, map_add, map_smul, map_smul]

/-- The universal divided power differential kills `1`. -/
@[simp] public theorem dividedPowerDifferential_one :
    dividedPowerDifferential (A := A) hJ 1 = 0 := by
  unfold dividedPowerDifferential
  rw [Derivation.map_one_eq_zero, map_zero]

/-! ### The de Rham differential, read on the forms themselves -/

/-- **The divided power de Rham differential `Ω^i_{B/A,δ} → Ω^{i+1}_{B/A,δ}`**, read on the
exterior powers themselves rather than on the `RestrictScalars` synonyms through which
`Crystalline.dividedPowerDeRhamComplex` carries it.  The two types are definitionally equal and
this definition is where that identification is paid: performed inside a proof it blocks
instance search for `+` and `•` on the target, since `RestrictScalars A B X` is not reducibly
`X`. -/
public noncomputable def dividedPowerDeRham (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDifferentialForms (A := A) hJ (i + 1) :=
  (dividedPowerDeRhamComplex (A := A) hJ).differential i omega

/-- The de Rham differential is additive. -/
public theorem dividedPowerDeRham_add (i : ℕ)
    (x y : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRham hJ i (x + y) = dividedPowerDeRham hJ i x + dividedPowerDeRham hJ i y :=
  map_add ((dividedPowerDeRhamComplex (A := A) hJ).differential i) x y

/-- The de Rham differential kills zero. -/
@[simp] public theorem dividedPowerDeRham_zero (i : ℕ) :
    dividedPowerDeRham (A := A) hJ i 0 = 0 :=
  map_zero ((dividedPowerDeRhamComplex (A := A) hJ).differential i)

/-- The de Rham differential as an additive map. -/
public noncomputable def dividedPowerDeRhamHom (i : ℕ) :
    dividedPowerDifferentialForms (A := A) hJ i →+
      dividedPowerDifferentialForms (A := A) hJ (i + 1) :=
  AddMonoidHom.mk' (dividedPowerDeRham hJ i) (dividedPowerDeRham_add hJ i)

/-- The additive map `Crystalline.dividedPowerDeRhamHom` sends a form to its de Rham
differential. -/
@[simp] public theorem dividedPowerDeRhamHom_apply (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRhamHom hJ i omega = dividedPowerDeRham hJ i omega := rfl

/-- The value of the de Rham differential on a standard generator. -/
public theorem dividedPowerDeRham_generator (i : ℕ) (f : Fin (i + 1) → B) :
    dividedPowerDeRham hJ i
        (f 0 • exteriorPower.ιMulti B i
          (fun j ↦ dividedPowerDifferential (A := A) hJ (f j.succ))) =
      exteriorPower.ιMulti B (i + 1) (fun j ↦ dividedPowerDifferential (A := A) hJ (f j)) :=
  (dividedPowerDeRhamComplex (A := A) hJ).differential_generator i f

/-- Consecutive de Rham differentials compose to zero. -/
@[simp] public theorem dividedPowerDeRham_dividedPowerDeRham (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRham hJ (i + 1) (dividedPowerDeRham hJ i omega) = 0 :=
  LinearMap.congr_fun (dividedPowerDeRhamComplex_differential_squared (A := A) hJ i) omega

/-! ### The wedge product of divided power forms -/

/-- **The wedge product `Ω^i_{B/A,δ} × Ω¹_{B/A,δ} → Ω^{i+1}_{B/A,δ}`** of divided power forms, in
the variance in which `Crystalline.CompletedDeRham.complex` takes it: the first argument is the
form of degree `i`, the second the one-form, and the product is `η ∧ ω`, the one-form on the
left.  It is `Crystalline.leftWedge` read through the identification of `Ω¹` with the degree-one
exterior power. -/
public noncomputable def dividedPowerWedge (i : ℕ) :
    dividedPowerDifferentialForms (A := A) hJ i →ₗ[B]
      dividedPowerDifferentialForms (A := A) hJ 1 →ₗ[B]
        dividedPowerDifferentialForms (A := A) hJ (i + 1) :=
  LinearMap.compl₂ (leftWedge (B := B) (Omega := dividedPowerDifferentials (A := A) hJ) i).flip
    (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).toLinearMap

/-- The wedge product of a form `ω` of degree `i` with a one-form `η` is `η ∧ ω`, the left wedge
`Crystalline.leftWedge` by `η` read as an element of `Ω¹`. -/
@[simp] public theorem dividedPowerWedge_apply (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    dividedPowerWedge hJ i omega eta =
      leftWedge i (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ) eta) omega :=
  rfl

/-- A one-form, read in the exterior algebra, is the image of the universal injection. -/
public theorem coe_oneEquiv_symm (x : dividedPowerDifferentials (A := A) hJ) :
    (((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm x :
        dividedPowerDifferentialForms (A := A) hJ 1) :
      ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) = ExteriorAlgebra.ι B x := by
  rw [exteriorPower.oneEquiv_symm_apply]
  exact coe_ιMulti_one x

/-- **`Crystalline.dividedPowerWedge` is the bigraded wedge product in degrees `(1, i)`.**  Two
things separate the two spellings, and this is the bridge across both: the divided power wedge
takes its arguments in the order `(ω, η)` and multiplies them in the order `η ∧ ω`, so the
degrees appear as `(i, 1)` and the product as `wedgeMul 1 i η ω`; and the divided power wedge
lands in degree `i + 1` while `exteriorPower.wedgeMul 1 i` lands in degree `1 + i`, which is the
same number but not the same term, so a reindexing by `exteriorPower.degCongr` stands between
them. -/
public theorem dividedPowerWedge_eq_wedgeMul (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    dividedPowerWedge hJ i omega eta =
      exteriorPower.degCongr (Nat.add_comm 1 i) (exteriorPower.wedgeMul 1 i eta omega) := by
  refine Subtype.ext ?_
  rw [dividedPowerWedge_apply, leftWedge_coe, exteriorPower.coe_degCongr,
    exteriorPower.wedgeMul_apply_coe, ← coe_oneEquiv_symm hJ
      (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ) eta),
    LinearEquiv.symm_apply_apply]

/-- **The wedge product is alternating on one-forms**: wedging twice by the same one-form is
zero, because `ι x · ι x = 0` in the exterior algebra. -/
public theorem leftWedge_leftWedge_self {Omega : Type*} [AddCommGroup Omega] [Module B Omega]
    (i : ℕ) (x : Omega) (omega : ⋀[B]^i Omega) :
    leftWedge (i + 1) x (leftWedge i x omega) = 0 := by
  apply Subtype.ext
  simp only [leftWedge_coe, Submodule.coe_zero, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-! ### The Leibniz rule for the divided power de Rham differential -/

/-- Left exterior multiplication is additive in the one-form. -/
public theorem leftWedge_add_left {Omega : Type*} [AddCommGroup Omega] [Module B Omega] (i : ℕ)
    (x y : Omega) (omega : ⋀[B]^i Omega) :
    leftWedge i (x + y) omega = leftWedge i x omega + leftWedge i y omega := by
  rw [map_add, LinearMap.add_apply]

/-- Left exterior multiplication is `B`-linear in the one-form. -/
public theorem leftWedge_smul_left {Omega : Type*} [AddCommGroup Omega] [Module B Omega] (i : ℕ)
    (c : B) (x : Omega) (omega : ⋀[B]^i Omega) :
    leftWedge i (c • x) omega = c • leftWedge i x omega := by
  rw [map_smul, LinearMap.smul_apply]

/-- The de Rham differential is compatible with differences. -/
public theorem dividedPowerDeRham_sub (i : ℕ)
    (x y : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRham hJ i (x - y) = dividedPowerDeRham hJ i x - dividedPowerDeRham hJ i y :=
  map_sub ((dividedPowerDeRhamComplex (A := A) hJ).differential i) x y

/-- Induction over the `B`-span of the standard generators of the divided power forms. -/
private theorem dividedPowerForms_induction {i : ℕ}
    {motive : dividedPowerDifferentialForms (A := A) hJ i → Prop}
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (mem : ∀ c : Fin (i + 1) → B, motive (c 0 • exteriorPower.ιMulti B i
      fun j ↦ dividedPowerDifferential (A := A) hJ (c j.succ)))
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (b : B) x, motive x → motive (b • x)) : motive omega := by
  have hmem : omega ∈ Submodule.span B (Set.range fun c : Fin (i + 1) → B ↦
      c 0 • exteriorPower.ιMulti B i
        fun j ↦ dividedPowerDifferential (A := A) hJ (c j.succ)) := by
    rw [span_range_smul_ιMulti_eq_top (R := B) (dividedPowerDifferential (A := A) hJ)
      (dividedPowerDifferentials_span hJ) i]
    trivial
  induction hmem using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      exact mem c
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul b x _ hx => exact smul b x hx

/-- **The Leibniz rule `d (f · ω) = f · d ω + d f ∧ ω`** for the divided power de Rham
differential of [Stacks, Tag 07HZ].  The differential is `A`-linear only, so this is not
linearity; it is proved by induction over the `B`-span of the standard generators, with `f`
quantified inside the induction so that the scalar step of the induction is available: for a
fixed `f` that step would need the rule for the scalar `f · b`, which is not the inductive
hypothesis. -/
public theorem dividedPowerDeRham_smul (i : ℕ) (f : B)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRham hJ i (f • omega) =
      f • dividedPowerDeRham hJ i omega +
        leftWedge i (dividedPowerDifferential (A := A) hJ f) omega := by
  induction omega using dividedPowerForms_induction hJ generalizing f with
  | mem c =>
      have hgen : ∀ b : B,
          dividedPowerDeRham hJ i (b • exteriorPower.ιMulti B i
              (fun j ↦ dividedPowerDifferential (A := A) hJ (c j.succ))) =
            leftWedge i (dividedPowerDifferential (A := A) hJ b)
              (exteriorPower.ιMulti B i
                (fun j ↦ dividedPowerDifferential (A := A) hJ (c j.succ))) := by
        intro b
        have hc : (fun j : Fin (i + 1) ↦ dividedPowerDifferential (A := A) hJ
              ((Fin.cons b fun j ↦ c j.succ : Fin (i + 1) → B) j)) =
            Fin.cons (dividedPowerDifferential (A := A) hJ b)
              (fun j ↦ dividedPowerDifferential (A := A) hJ (c j.succ)) := by
          funext j
          cases j using Fin.cases <;> simp
        have hb := dividedPowerDeRham_generator (A := A) hJ i (Fin.cons b fun j ↦ c j.succ)
        simp only [Fin.cons_zero, Fin.cons_succ] at hb
        rw [hb, hc, ← leftWedge_ιMulti]
      rw [smul_smul, hgen, hgen, dividedPowerDifferential_mul, leftWedge_add_left,
        leftWedge_smul_left, leftWedge_smul_left, map_smul]
  | zero => rw [smul_zero, dividedPowerDeRham_zero, smul_zero, map_zero, add_zero]
  | add x y ihx ihy =>
      rw [smul_add, dividedPowerDeRham_add, dividedPowerDeRham_add, smul_add, map_add, ihx f,
        ihy f]
      abel
  | smul b x ih =>
      rw [smul_smul, ih (f * b), ih b, dividedPowerDifferential_mul, leftWedge_add_left,
        leftWedge_smul_left, leftWedge_smul_left, smul_add, smul_smul, map_smul]
      abel

/-- **An exact one-form is closed.**  This is the generator formula in degree one at the constant
`1`, where `d 1 = 0` makes the leading factor of the wedge vanish. -/
public theorem dividedPowerDeRham_oneForm_eq_zero (b : B) :
    dividedPowerDeRham hJ 1
        ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
          (dividedPowerDifferential (A := A) hJ b)) = 0 := by
  have hone : ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
      (dividedPowerDifferential (A := A) hJ b) :
        dividedPowerDifferentialForms (A := A) hJ 1) =
      (Fin.cons (1 : B) (fun _ : Fin 1 ↦ b) : Fin 2 → B) 0 •
        exteriorPower.ιMulti B 1
          (fun j : Fin 1 ↦ dividedPowerDifferential (A := A) hJ
            ((Fin.cons (1 : B) (fun _ : Fin 1 ↦ b) : Fin 2 → B) j.succ)) := by
    rw [Fin.cons_zero, one_smul, exteriorPower.oneEquiv_symm_apply]
    simp
  rw [hone, dividedPowerDeRham_generator hJ 1 (Fin.cons (1 : B) fun _ : Fin 1 ↦ b)]
  refine (exteriorPower.ιMulti B 2).map_coord_zero (i := 0) ?_
  simp

/-! ### The graded Leibniz rule against a one-form -/

/-- **The graded Leibniz rule against an exact one-form**: `d (d b ∧ ω) = - d b ∧ d ω`.  It is a
formal consequence of the Leibniz rule and `d ∘ d = 0`: the Leibniz rule writes `d b ∧ ω` as
`d (b · ω) - b · d ω`, the first term is killed by `d ∘ d = 0`, and the second is expanded by the
Leibniz rule again. -/
public theorem dividedPowerDeRham_leftWedge_exact (i : ℕ) (b : B)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRham hJ (i + 1)
        (leftWedge i (dividedPowerDifferential (A := A) hJ b) omega) =
      -leftWedge (i + 1) (dividedPowerDifferential (A := A) hJ b)
        (dividedPowerDeRham hJ i omega) := by
  have hsplit : leftWedge i (dividedPowerDifferential (A := A) hJ b) omega =
      dividedPowerDeRham hJ i (b • omega) - b • dividedPowerDeRham hJ i omega := by
    rw [dividedPowerDeRham_smul hJ i b omega]
    abel
  rw [hsplit, dividedPowerDeRham_sub, dividedPowerDeRham_dividedPowerDeRham, zero_sub,
    dividedPowerDeRham_smul hJ (i + 1) b (dividedPowerDeRham hJ i omega),
    dividedPowerDeRham_dividedPowerDeRham, smul_zero, zero_add]

/-- **The graded Leibniz rule against a one-form**, read in the exterior algebra:
`d (η ∧ ω) + η ∧ d ω = (d η) ∧ ω`.  The correction term wedges by a *two*-form, which
`Crystalline.leftWedge` cannot express, so the identity is stated inside
`ExteriorAlgebra B Ω¹_{B/A,δ}`, where the two-form `d η` is just an element.

Both sides are additive in `η`, and the one-forms `b · d f` additively generate `Ω¹_{B/A,δ}`, so
the identity reduces to `η = d f` and its `B`-multiples, where it follows from the Leibniz rule
and `Crystalline.dividedPowerDeRham_leftWedge_exact`. -/
public theorem coe_dividedPowerDeRham_leftWedge (i : ℕ)
    (eta : dividedPowerDifferentials (A := A) hJ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    ((dividedPowerDeRham hJ (i + 1) (leftWedge i eta omega) +
        leftWedge (i + 1) eta (dividedPowerDeRham hJ i omega) :
      dividedPowerDifferentialForms (A := A) hJ (i + 1 + 1)) :
        ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
      ((dividedPowerDeRham hJ 1
          ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm eta) :
        dividedPowerDifferentialForms (A := A) hJ (1 + 1)) :
          ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) *
        (omega : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) := by
  have hmem : eta ∈ Submodule.span B
      (Set.range (dividedPowerDifferential (A := A) hJ)) := by
    rw [dividedPowerDifferentials_span hJ]; trivial
  induction hmem using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [dividedPowerDeRham_leftWedge_exact hJ i b omega,
        dividedPowerDeRham_oneForm_eq_zero hJ b, neg_add_cancel, Submodule.coe_zero,
        Submodule.coe_zero, zero_mul]
  | zero =>
      have h0 : ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
          (0 : dividedPowerDifferentials (A := A) hJ) :
            dividedPowerDifferentialForms (A := A) hJ 1) = 0 := map_zero _
      rw [map_zero, LinearMap.zero_apply, dividedPowerDeRham_zero, map_zero,
        LinearMap.zero_apply, add_zero, h0, dividedPowerDeRham_zero, Submodule.coe_zero,
        Submodule.coe_zero, zero_mul]
  | add x y _ _ ihx ihy =>
      have hsymm : ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
          (x + y) : dividedPowerDifferentialForms (A := A) hJ 1) =
          (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm x +
            (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm y :=
        map_add _ _ _
      have hre : (dividedPowerDeRham hJ (i + 1) (leftWedge i x omega) +
            dividedPowerDeRham hJ (i + 1) (leftWedge i y omega) +
          (leftWedge (i + 1) x (dividedPowerDeRham hJ i omega) +
            leftWedge (i + 1) y (dividedPowerDeRham hJ i omega)) :
            dividedPowerDifferentialForms (A := A) hJ (i + 1 + 1)) =
          (dividedPowerDeRham hJ (i + 1) (leftWedge i x omega) +
            leftWedge (i + 1) x (dividedPowerDeRham hJ i omega)) +
          (dividedPowerDeRham hJ (i + 1) (leftWedge i y omega) +
            leftWedge (i + 1) y (dividedPowerDeRham hJ i omega)) := by abel
      rw [leftWedge_add_left, dividedPowerDeRham_add, leftWedge_add_left, hsymm,
        dividedPowerDeRham_add, hre, Submodule.coe_add, ihx, ihy, Submodule.coe_add, add_mul]
  | smul b x _ ih =>
      have hsymm : ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
          (b • x) : dividedPowerDifferentialForms (A := A) hJ 1) =
          b • (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm x :=
        map_smul _ _ _
      have hre : (b • dividedPowerDeRham hJ (i + 1) (leftWedge i x omega) +
            leftWedge (i + 1) (dividedPowerDifferential (A := A) hJ b) (leftWedge i x omega) +
            b • leftWedge (i + 1) x (dividedPowerDeRham hJ i omega) :
            dividedPowerDifferentialForms (A := A) hJ (i + 1 + 1)) =
          b • (dividedPowerDeRham hJ (i + 1) (leftWedge i x omega) +
            leftWedge (i + 1) x (dividedPowerDeRham hJ i omega)) +
          leftWedge (i + 1) (dividedPowerDifferential (A := A) hJ b) (leftWedge i x omega) := by
        rw [smul_add]; abel
      rw [leftWedge_smul_left, dividedPowerDeRham_smul, leftWedge_smul_left, hsymm,
        dividedPowerDeRham_smul, hre, Submodule.coe_add, Submodule.coe_smul, ih,
        Submodule.coe_add, Submodule.coe_smul, leftWedge_coe, leftWedge_coe, add_mul]
      rw [smul_mul_assoc, leftWedge_coe, coe_oneEquiv_symm, mul_assoc]

/-! ### The correction term as a wedge by a two-form -/

/-- **Exterior multiplication by a two-form**, `⋀^2 Ω × ⋀^i Ω → ⋀^{i+2} Ω`, with the two-form on
the left.  This is `exteriorPower.wedgeMul 2 i` reindexed from the degree `2 + i` it is built in
to the degree `i + 1 + 1` in which the correction term `(d η) ∧ ω` of the graded Leibniz rule
arises, `Crystalline.leftWedge` having raised the degree twice. -/
public noncomputable def twoWedge {Omega : Type*} [AddCommGroup Omega] [Module B Omega] (i : ℕ) :
    (⋀[B]^2 Omega) →ₗ[B] (⋀[B]^i Omega) →ₗ[B] (⋀[B]^(i + 1 + 1) Omega) :=
  LinearMap.compr₂ (exteriorPower.wedgeMul 2 i)
    (exteriorPower.degCongr (show 2 + i = i + 1 + 1 by omega)).toLinearMap

/-- Exterior multiplication by a two-form agrees with multiplication in the exterior algebra. -/
@[simp] public theorem twoWedge_coe {Omega : Type*} [AddCommGroup Omega] [Module B Omega] (i : ℕ)
    (x : ⋀[B]^2 Omega) (y : ⋀[B]^i Omega) :
    (twoWedge i x y : ExteriorAlgebra B Omega) =
      (x : ExteriorAlgebra B Omega) * (y : ExteriorAlgebra B Omega) := by
  rw [twoWedge, LinearMap.compr₂_apply, LinearEquiv.coe_coe, exteriorPower.coe_degCongr,
    exteriorPower.wedgeMul_apply_coe]

/-- **The graded Leibniz rule against a one-form, as an identity of forms**:
`d (η ∧ ω) + η ∧ d ω = (d η) ∧ ω`.  This is
`Crystalline.coe_dividedPowerDeRham_leftWedge` with the right-hand side named by
`Crystalline.twoWedge` rather than left in the exterior algebra.  It is the form in which a
`p`-adically completed closed one-form can use it, since at the level `pⁿ` of a completion a
closed one-form of the completion is closed only modulo `pⁿ`. -/
public theorem dividedPowerDeRham_leftWedge (i : ℕ)
    (eta : dividedPowerDifferentials (A := A) hJ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRham hJ (i + 1) (leftWedge i eta omega) +
        leftWedge (i + 1) eta (dividedPowerDeRham hJ i omega) =
      twoWedge i (dividedPowerDeRham hJ 1
        ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm eta)) omega := by
  apply Subtype.ext
  rw [twoWedge_coe, coe_dividedPowerDeRham_leftWedge hJ i eta omega]

/-- **`d (η ∧ ω) = - η ∧ d ω` for a closed one-form `η`.**  This is
`Crystalline.coe_dividedPowerDeRham_leftWedge` with the correction term `(d η) ∧ ω` absent.  It is
the form in which `Crystalline.CompletedDeRham.IsGradedExterior` asks for the rule, the
unrestricted rule not being expressible in the data that structure carries. -/
public theorem dividedPowerDeRham_leftWedge_of_closed (i : ℕ)
    (eta : dividedPowerDifferentials (A := A) hJ)
    (hclosed : dividedPowerDeRham hJ 1
      ((exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm eta) = 0)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    dividedPowerDeRham hJ (i + 1) (leftWedge i eta omega) +
      leftWedge (i + 1) eta (dividedPowerDeRham hJ i omega) = 0 := by
  apply Subtype.ext
  rw [coe_dividedPowerDeRham_leftWedge hJ i eta omega, hclosed]
  simp

/-! ### The bigraded graded Leibniz rule -/

/-- The de Rham differentials of two forms with the same underlying element of the exterior
algebra, in two degrees that are equal, agree in the exterior algebra.  This is the transport
that keeps the induction of `Crystalline.coe_dividedPowerDeRham_wedgeMul` free of `HEq`: the
degrees `(i + 1) + j` and `(i + j) + 1` are equal only propositionally, so an identity relating
forms built in both is not even a statement until the two are identified, and inside an
induction a `HEq` between them is unusable. -/
public theorem coe_dividedPowerDeRham_congr {m n : ℕ} (h : m = n)
    {x : dividedPowerDifferentialForms (A := A) hJ m}
    {y : dividedPowerDifferentialForms (A := A) hJ n}
    (hxy : (x : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
      (y : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ))) :
    ((dividedPowerDeRham hJ m x : dividedPowerDifferentialForms (A := A) hJ (m + 1)) :
        ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
      ((dividedPowerDeRham hJ n y : dividedPowerDifferentialForms (A := A) hJ (n + 1)) :
        ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) := by
  subst h
  rw [Subtype.coe_injective hxy]

/-- **The bigraded graded Leibniz rule for the divided power de Rham differential of
[Stacks, Tag 07HZ]**, `d (ω ∧ η) = d ω ∧ η + (-1)^i ω ∧ d η`, read in the exterior algebra: the
three products are the multiplication of `ExteriorAlgebra B Ω¹_{B/A,δ}`, in which the degree
bookkeeping disappears.

This is `Crystalline.coe_dividedPowerDeRham_leftWedge` with neither argument confined to degree
one.  It cannot be cited from the Kähler de Rham complex: `Crystalline.dividedPowerDeRham` is a
different differential, defined abstractly by its value on the standard generators on a
*quotient* of the Kähler differentials, so the induction of
`KaehlerDifferential.coe_deRhamDifferential_wedgeMul` has to be redone here.  It runs over the
`B`-span of the standard generators `b₀ · d b₁ ∧ ⋯ ∧ d b_i`, not the `A`-span the Kähler proof
uses: the `A`-module structure of the forms is carried through `RestrictScalars A B`, which is
not reducibly the identity, and paying that identification inside an induction blocks instance
search for `+` and `•` on the target.  Over the `B`-span the scalar step has content, and it
closes because the two Leibniz correction terms `d b ∧ (ω ∧ η)` and `(d b ∧ ω) ∧ η` agree by
associativity of the exterior algebra.  In degree zero the rule is the Leibniz rule
`Crystalline.dividedPowerDeRham_smul`; the inductive step peels off the leading one-form
`d b₁ ∧ ·`, where `Crystalline.dividedPowerDeRham_leftWedge_exact` applies and the sign flips. -/
public theorem coe_dividedPowerDeRham_wedgeMul (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ j) :
    ((dividedPowerDeRham hJ (i + j) (exteriorPower.wedgeMul i j omega eta) :
        dividedPowerDifferentialForms (A := A) hJ (i + j + 1)) :
      ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
      ((dividedPowerDeRham hJ i omega : dividedPowerDifferentialForms (A := A) hJ (i + 1)) :
          ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) *
          (eta : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) +
        (-1) ^ i * ((omega : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) *
          ((dividedPowerDeRham hJ j eta : dividedPowerDifferentialForms (A := A) hJ (j + 1)) :
            ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ))) := by
  induction i generalizing j with
  | zero =>
      simp only [pow_zero, one_mul]
      induction omega using dividedPowerForms_induction hJ with
      | mem c =>
          have hone : ((exteriorPower.ιMulti B 0 fun k : Fin 0 ↦
                dividedPowerDifferential (A := A) hJ (c k.succ) :
              dividedPowerDifferentialForms (A := A) hJ 0) :
                ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) = 1 := by
            rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
          have hcoe : ((c 0 • exteriorPower.ιMulti B 0 fun k : Fin 0 ↦
                dividedPowerDifferential (A := A) hJ (c k.succ) :
              dividedPowerDifferentialForms (A := A) hJ 0) :
                ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
              algebraMap B (ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ))
                (c 0) := by
            rw [SetLike.val_smul, hone, Algebra.smul_def, mul_one]
          have hd : ((dividedPowerDeRham hJ 0 (c 0 • exteriorPower.ιMulti B 0 fun k : Fin 0 ↦
                dividedPowerDifferential (A := A) hJ (c k.succ)) :
              dividedPowerDifferentialForms (A := A) hJ 1) :
                ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
              ExteriorAlgebra.ι B (dividedPowerDifferential (A := A) hJ (c 0)) := by
            rw [dividedPowerDeRham_generator hJ 0 c, exteriorPower.ιMulti_apply_coe,
              ExteriorAlgebra.ιMulti_succ_apply]
            simp
          have hleft := coe_dividedPowerDeRham_congr hJ (Nat.zero_add j)
            (x := exteriorPower.wedgeMul 0 j (c 0 • exteriorPower.ιMulti B 0 fun k : Fin 0 ↦
              dividedPowerDifferential (A := A) hJ (c k.succ)) eta)
            (y := c 0 • eta)
            (by rw [exteriorPower.wedgeMul_apply_coe, hcoe, SetLike.val_smul, Algebra.smul_def])
          rw [hleft, dividedPowerDeRham_smul, Submodule.coe_add, leftWedge_coe,
            SetLike.val_smul, hd, hcoe, Algebra.smul_def]
          abel
      | zero => simp
      | add x y hx hy =>
          rw [map_add, LinearMap.add_apply, dividedPowerDeRham_add, dividedPowerDeRham_add,
            Submodule.coe_add, Submodule.coe_add, Submodule.coe_add, hx, hy]
          simp only [add_mul]
          abel
      | smul b x hx =>
          have hws : exteriorPower.wedgeMul 0 j (b • x) eta =
              b • exteriorPower.wedgeMul 0 j x eta := by
            rw [map_smul, LinearMap.smul_apply]
          rw [hws, dividedPowerDeRham_smul, dividedPowerDeRham_smul]
          simp only [Submodule.coe_add, Submodule.coe_smul, leftWedge_coe,
            exteriorPower.wedgeMul_apply_coe]
          rw [hx]
          simp only [smul_add, add_mul, smul_mul_assoc, mul_assoc]
          abel
  | succ i ih =>
      induction omega using dividedPowerForms_induction hJ with
      | mem c =>
          set xi : dividedPowerDifferentialForms (A := A) hJ i :=
            c 0 • exteriorPower.ιMulti B i
              (fun k : Fin i ↦ dividedPowerDifferential (A := A) hJ (c k.succ.succ)) with hxi
          have hpeel : c 0 • (exteriorPower.ιMulti B (i + 1)
                fun k : Fin (i + 1) ↦ dividedPowerDifferential (A := A) hJ (c k.succ)) =
              leftWedge i (dividedPowerDifferential (A := A) hJ (c 1)) xi := by
            rw [hxi, map_smul, leftWedge_ιMulti]
            congr 1
            refine (exteriorPower.ιMulti B (i + 1)).congr_arg ?_
            funext k
            refine Fin.cases ?_ ?_ k
            · rfl
            · intro m; rfl
          rw [hpeel]
          have hassoc : ((exteriorPower.wedgeMul (i + 1) j
                  (leftWedge i (dividedPowerDifferential (A := A) hJ (c 1)) xi) eta :
                dividedPowerDifferentialForms (A := A) hJ (i + 1 + j)) :
                  ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) =
              ((leftWedge (i + j) (dividedPowerDifferential (A := A) hJ (c 1))
                  (exteriorPower.wedgeMul i j xi eta) :
                dividedPowerDifferentialForms (A := A) hJ (i + j + 1)) :
                  ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) := by
            rw [exteriorPower.wedgeMul_apply_coe, leftWedge_coe, leftWedge_coe,
              exteriorPower.wedgeMul_apply_coe, mul_assoc]
          rw [coe_dividedPowerDeRham_congr hJ (Nat.succ_add i j) hassoc,
            dividedPowerDeRham_leftWedge_exact, Submodule.coe_neg, leftWedge_coe,
            ih j xi eta, dividedPowerDeRham_leftWedge_exact, Submodule.coe_neg,
            leftWedge_coe, leftWedge_coe, pow_succ]
          have hcen (z : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) :
              ExteriorAlgebra.ι B (dividedPowerDifferential (A := A) hJ (c 1)) *
                  ((-1 : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) ^ i * z) =
                (-1 : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) ^ i *
                  (ExteriorAlgebra.ι B (dividedPowerDifferential (A := A) hJ (c 1)) * z) := by
            rw [← mul_assoc, ← ((Commute.neg_one_left
              (ExteriorAlgebra.ι B (dividedPowerDifferential (A := A) hJ (c 1)))).pow_left i).eq,
              mul_assoc]
          simp only [mul_add, mul_assoc, hcen, neg_mul, mul_neg, mul_one]
          abel
      | zero => simp
      | add x y hx hy =>
          rw [map_add, LinearMap.add_apply, dividedPowerDeRham_add, dividedPowerDeRham_add,
            Submodule.coe_add, Submodule.coe_add, Submodule.coe_add, hx, hy]
          simp only [add_mul, mul_add]
          abel
      | smul b x hx =>
          have hws : exteriorPower.wedgeMul (i + 1) j (b • x) eta =
              b • exteriorPower.wedgeMul (i + 1) j x eta := by
            rw [map_smul, LinearMap.smul_apply]
          have hsign (z : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) :
              b • ((-1 : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) ^ (i + 1) *
                  z) =
                (-1 : ExteriorAlgebra B (dividedPowerDifferentials (A := A) hJ)) ^ (i + 1) *
                  (b • z) :=
            (mul_smul_comm b _ z).symm
          rw [hws, dividedPowerDeRham_smul, dividedPowerDeRham_smul]
          simp only [Submodule.coe_add, Submodule.coe_smul, leftWedge_coe,
            exteriorPower.wedgeMul_apply_coe]
          rw [hx, smul_add, hsign]
          simp only [add_mul, smul_mul_assoc, mul_assoc]
          abel

/-- **The bigraded graded Leibniz rule for the divided power de Rham differential of
[Stacks, Tag 07HZ], as an identity of forms**,
`d (ω ∧ η) = d ω ∧ η + (-1)^i ω ∧ d η`, with all three terms transported into the single
exterior power `Ω^{i+j+1}_{B/A,δ}`.  Only `d ω ∧ η` needs a transport: it is built in degree
`(i + 1) + j`, which is the degree `(i + j) + 1` of the other two but not by definitional
unfolding, so `exteriorPower.degCongr` stands between them.

This is `Crystalline.dividedPowerDeRham_leftWedge_of_closed` with the restriction to a closed
one-form removed: that statement exists only because
`Crystalline.CompletedDeRham.IsGradedExterior` can wedge by one-forms alone, so the correction
term `ω ∧ d η` has no name there.  With the bigraded wedge it does. -/
public theorem dividedPowerDeRham_wedgeMul (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ j) :
    dividedPowerDeRham hJ (i + j) (exteriorPower.wedgeMul i j omega eta) =
      exteriorPower.degCongr (Nat.succ_add i j)
          (exteriorPower.wedgeMul (i + 1) j (dividedPowerDeRham hJ i omega) eta) +
        (-1 : B) ^ i • exteriorPower.wedgeMul i (j + 1) omega
          (dividedPowerDeRham hJ j eta) := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, exteriorPower.coe_degCongr, exteriorPower.wedgeMul_apply_coe,
    SetLike.val_smul, exteriorPower.wedgeMul_apply_coe, Algebra.smul_def,
    coe_dividedPowerDeRham_wedgeMul hJ i j omega eta]
  simp

/-- **The bigraded graded Leibniz rule with both correction terms reindexed**, by
`exteriorPower.degCongr`, into the degree `(i + j) + 1` of the left hand side.  This is
`Crystalline.dividedPowerDeRham_wedgeMul` with the second reindexing, from `i + (j + 1)`, also
written out rather than left to definitional unfolding.

That makes no difference to the content and every difference to a consumer that has to *rewrite*
with the identity: with a compound degree left implicit, each such rewrite re-checks
`i + (j + 1) ≡ (i + j) + 1` underneath the `Module` instance of an exterior power, and under a
`p`-adic completion that check is what exhausts the heartbeat budget of
`Crystalline.completedDividedPowerDeRham_wedgeMul`. -/
public theorem dividedPowerDeRham_wedgeMul_degCongr (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ j) :
    dividedPowerDeRham hJ (i + j) (exteriorPower.wedgeMul i j omega eta) =
      exteriorPower.degCongr (Nat.succ_add i j)
          (exteriorPower.wedgeMul (i + 1) j (dividedPowerDeRham hJ i omega) eta) +
        (-1 : B) ^ i • exteriorPower.degCongr (Nat.add_succ i j)
          (exteriorPower.wedgeMul i (j + 1) omega (dividedPowerDeRham hJ j eta)) := by
  exact dividedPowerDeRham_wedgeMul hJ i j omega eta

/-! ### The comparison of forms along a divided power morphism respects the wedge product -/

section Comparison

variable {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C} (epsilon : DividedPowers K)
  (f : B →ₐ[A] C) (hf : DividedPowers.IsDPMorphism hJ epsilon f.toRingHom)

/-- **In degree one the comparison of forms is the comparison of differentials**, read through
`exteriorPower.oneEquiv`.  This is what identifies the one-form slot of the wedge product on
the two sides. -/
public theorem mapDifferentialFormsOfDPMorphism_oneEquiv
    (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    exteriorPower.oneEquiv C (dividedPowerDifferentials (A := A) epsilon)
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf 1 eta) =
      mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf
        (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ) eta) := by
  set x := exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ) eta with hx
  have heta : eta = exteriorPower.ιMulti B 1 fun _ ↦ x :=
    (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).injective
      (by rw [exteriorPower.oneEquiv_ιMulti])
  rw [heta, mapDifferentialFormsOfDPMorphism_ιMulti, exteriorPower.oneEquiv_ιMulti]

/-- **The comparison of forms respects the wedge product**:
`ψ(η ∧ ω) = ψ(η) ∧ ψ(ω)`, with `η` a one-form.  The wedge product is multiplication in the
exterior algebra and `ExteriorAlgebra.mapₛₗ` is a ring homomorphism, so this is `map_mul`. -/
public theorem mapDifferentialFormsOfDPMorphism_wedge (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf (i + 1)
        (dividedPowerWedge hJ i omega eta) =
      dividedPowerWedge epsilon i
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i omega)
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf 1 eta) := by
  refine Subtype.ext ?_
  rw [dividedPowerWedge_apply, dividedPowerWedge_apply,
    mapDifferentialFormsOfDPMorphism_coe, leftWedge_coe, leftWedge_coe,
    mapDifferentialFormsOfDPMorphism_oneEquiv, map_mul, ExteriorAlgebra.mapₛₗ_ι,
    mapDifferentialFormsOfDPMorphism_coe]
  rfl

/-- **The comparison of forms respects the bigraded wedge product**:
`ψ(ω ∧ η) = ψ(ω) ∧ ψ(η)` in every bidegree `(i, j)`.  This is
`Crystalline.mapDifferentialFormsOfDPMorphism_wedge` with neither argument confined to degree
one, and it is the form a filtration of the completed de Rham complex needs, since its graded
pieces multiply forms of two arbitrary degrees.  Like the one-form case it is `map_mul` for the
ring homomorphism `ExteriorAlgebra.mapₛₗ`, and here there is not even a `oneEquiv` to carry
across: both arguments are read in the exterior algebra directly. -/
public theorem mapDifferentialFormsOfDPMorphism_wedgeMul (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ j) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf (i + j)
        (exteriorPower.wedgeMul i j omega eta) =
      exteriorPower.wedgeMul i j
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i omega)
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf j eta) :=
  Subtype.ext (by
    rw [mapDifferentialFormsOfDPMorphism_coe, exteriorPower.wedgeMul_apply_coe,
      exteriorPower.wedgeMul_apply_coe, map_mul, mapDifferentialFormsOfDPMorphism_coe,
      mapDifferentialFormsOfDPMorphism_coe])

/-- **The comparison of forms respects left exterior multiplication by a one-form**, in the
variance `Crystalline.leftWedge` uses. -/
public theorem mapDifferentialFormsOfDPMorphism_leftWedge (i : ℕ)
    (x : dividedPowerDifferentials (A := A) hJ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf (i + 1)
        (leftWedge i x omega) =
      leftWedge i (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf x)
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i omega) :=
  Subtype.ext (by
    rw [mapDifferentialFormsOfDPMorphism_coe, leftWedge_coe, leftWedge_coe, map_mul,
      ExteriorAlgebra.mapₛₗ_ι, mapDifferentialFormsOfDPMorphism_coe]
    rfl)

/-- **The comparison of forms is a map of de Rham complexes**: it intertwines the divided power
de Rham differentials, `ψ (d ω) = d (ψ ω)`.

The de Rham differential is not linear, so this is not formal.  It is proved by induction over
the `B`-span of the standard generators `b₀ · d b₁ ∧ ⋯ ∧ d bᵢ`, which is all of `Ωⁱ_{B/A,δ}` by
`Crystalline.span_range_smul_ιMulti_eq_top`.  On a generator both sides are
`d f(b₀) ∧ ⋯ ∧ d f(bᵢ)`, by `Crystalline.dividedPowerDeRham_generator` on each side.  The scalar
step is the only one with content: it compares the two Leibniz rules
`Crystalline.dividedPowerDeRham_smul`, and the correction terms match because the comparison
respects the wedge product and carries `d b` to `d f(b)`. -/
public theorem mapDifferentialFormsOfDPMorphism_deRham (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf (i + 1)
        (dividedPowerDeRham hJ i omega) =
      dividedPowerDeRham epsilon i
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ)
          epsilon f hf i omega) := by
  induction omega using dividedPowerForms_induction hJ with
  | mem c =>
      have hsm : mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i
          (c 0 • exteriorPower.ιMulti B i
            fun j ↦ dividedPowerDifferential (A := A) hJ (c j.succ)) =
          f (c 0) • exteriorPower.ιMulti C i
            fun j ↦ dividedPowerDifferential (A := A) epsilon (f (c j.succ)) := by
        rw [map_smulₛₗ, mapDifferentialFormsOfDPMorphism_ιMulti_d]
        rfl
      rw [dividedPowerDeRham_generator, mapDifferentialFormsOfDPMorphism_ιMulti_d, hsm]
      exact (dividedPowerDeRham_generator (A := A) epsilon i fun j ↦ f (c j)).symm
  | zero => rw [dividedPowerDeRham_zero, map_zero, map_zero, dividedPowerDeRham_zero]
  | add u v ihu ihv =>
      rw [dividedPowerDeRham_add, map_add, ihu, ihv, map_add, dividedPowerDeRham_add]
  | smul b u ihu =>
      rw [dividedPowerDeRham_smul, map_add, map_smulₛₗ, ihu,
        mapDifferentialFormsOfDPMorphism_leftWedge, mapDifferentialsOfDPMorphism_d,
        map_smulₛₗ, dividedPowerDeRham_smul]
      rfl

end Comparison

end Crystalline

end
