module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamExterior
public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# The `p`-adically completed divided power differentials and de Rham complex

Let `(B, J, δ)` be a divided power ring which is an `A`-algebra and let `p` be a natural number.
Write `D` for the `p`-adic completion of `B` and `Ω^i_D` for the `p`-adic completion of the
divided power differential forms `Ω^i_{B/A,δ}` of [Stacks, Tag 07HZ].  This module builds the
exterior calculus of the family `Ω^*_D`:

* the wedge product `Ω^i_D × Ω^j_D → Ω^{i+j}_D`, which is `D`-bilinear;
* the de Rham differential `Ω^i_D → Ω^{i+1}_D`, which is additive and not `D`-linear;
* the universal differential `d : D → Ω^1_D`,

and proves that they satisfy the two conditions a completed de Rham complex is built from,
`Crystalline.CompletedDeRham.IsGradedLeibniz` and
`Crystalline.CompletedDeRham.IsGradedExterior`.

Those two conditions were, until now, carried as hypotheses everywhere they appeared.  The
complex `M ⊗^∧_D Ω^*_D` of [Stacks, Proposition 60.21.3, Tag 07LG] is built in
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionDeRham.lean` over an *arbitrary*
graded family `Om : ℕ → Type v` with a wedge and a differential, pinned by exactly those two
conditions, and the module docstring there records that "all three hold for the genuine divided
power forms of [Stacks, Tag 07HZ]; they are hypotheses because the family of forms is a carried
parameter".  Nobody had supplied them for the genuine forms.  With this module
`Crystalline.CompletedDeRham.complexOfIsIntegrable` applies to `Ω^*_D`, which is the family
[Stacks, Tag 07LG] and the completed half of [Stacks, Lemma 60.20.2, Tag 07LD] are about.

## How the completion is taken

Every completion is along the ideal `(p) ⊆ B`, so that `Ω^i_D` is a module over
`D = AdicCompletion (p) B` by Mathlib's
`AdicCompletion.module : Module (AdicCompletion I R) (AdicCompletion I M)`, which is what the
completed tensor product of [Stacks, Tag 07JG] needs.

Neither of the two structure maps is `AdicCompletion.map` of anything:

* the de Rham differential is `A`-linear and not `B`-linear — already the Leibniz rule forbids
  it — so there is no `B`-linear map to complete.  It is
  `Crystalline.PAdicCompletion.mapAddHom` of the additive differential, which exists because the
  level `(p)ⁿ · Ω^i` is the subgroup `pⁿ Ω^i` cut out by an integer.
* the wedge product is `B`-bilinear, but completion is not monoidal, so there is no map
  `Ω^i_D ⊗ Ω^1_D → (Ω^i ⊗ Ω^1)^∧` to push it along.  It is
  `Crystalline.PAdicCompletion.mapBilinear` of the uncompleted wedge, built level by level, and
  the bilinearity it produces is over `D`.

Each identity is then checked at the levels, where it is the uncompleted identity of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/DeRhamExterior.lean`.  Only one is not
a plain reduction: a closed one-form of the completion is, at the level `pⁿ`, closed only
*modulo* `pⁿ`, so the graded Leibniz rule is applied in the form
`Crystalline.dividedPowerDeRham_leftWedge`, whose right-hand side `(d η) ∧ ω` is an element of
the forms and therefore lies in `pⁿ Ω^{i+2}` as soon as `d η` lies in `pⁿ Ω²`.

## Main definitions

* `Crystalline.completedDividedPowerRing` — the `p`-adic completion `D` of `B`.
* `Crystalline.completedDividedPowerForms` — the `p`-adic completion `Ω^i_D` of `Ω^i_{B/A,δ}`.
* `Crystalline.completedDividedPowerWedge` — **the wedge product `Ω^i_D × Ω^1_D → Ω^{i+1}_D` of
  completed forms**, `D`-bilinear, in the variance the completed de Rham complex uses.
* `Crystalline.completedDividedPowerWedgeMul` — **the bigraded wedge product
  `Ω^i_D × Ω^j_D → Ω^{i+j}_D`**, with `Crystalline.completedDividedPowerWedge_eq_wedgeMul`
  identifying the previous item with its bidegree `(1, i)` case.
* `Crystalline.completedDividedPowerDeRham` — **the de Rham differential of the completed
  forms**, additive.
* `Crystalline.completedFormsDifferential` — the universal differential `d : D → Ω^1_D`.
* `Crystalline.completedDividedPowerDifferentialOnRing` and
  `Crystalline.completedDividedPowerWedgeOnRing` — the universal differential and the wedge
  product read over `B` itself rather than over its completion, which is the family a completed
  de Rham complex over `B` is built from.
* `Crystalline.completedDividedPowerDeRhamComplex` — **the complex `M ⊗^∧_D Ω^*_D` of
  [Stacks, Tag 07LG] for the genuine completed divided power forms**, with every hypothesis
  about the forms discharged.
* `Crystalline.completedMapDifferentialForms` — **the comparison `Ω̂^i_B → Ω̂^i_C` of completed
  forms induced by a divided power morphism**, in every degree, semilinear over the
  morphism.

## Main results

* `Crystalline.isGradedLeibniz_completedDividedPower` — **the Leibniz rule
  `d (f · ω) = f · d ω + d f ∧ ω` for the completed forms.**
* `Crystalline.isGradedExterior_completedDividedPower` — **`d ∘ d = 0`, the wedge is alternating,
  and the graded Leibniz rule against a closed one-form, for the completed forms.**
* `Crystalline.completedDividedPowerDeRham_wedgeMul` — **the bigraded graded Leibniz rule
  `d (ω ∧ η) = d ω ∧ η + (-1)^i ω ∧ d η` for the completed forms**, in every bidegree and with no
  closedness hypothesis.  This is the previous item's third clause with the restriction to
  bidegree `(i, 1)` and to a closed one-form lifted: the term `ω ∧ d η`, which
  `Crystalline.CompletedDeRham.IsGradedExterior` cannot name, is named by
  `Crystalline.completedDividedPowerWedgeMul`.
* `Crystalline.isGradedLeibniz_completedDividedPowerOnRing` — the Leibniz rule for the family
  read over `B` itself, together with
  `Crystalline.completedDividedPowerDifferentialOnRing_add` and
  `Crystalline.completedDividedPowerDifferentialOnRing_mul`.
* `Crystalline.completedMapDifferentialForms_wedge`,
  `Crystalline.completedMapDifferentialForms_deRham` and
  `Crystalline.completedMapDifferentialForms_completedFormsDifferential_of` — **the comparison of
  completed forms respects the wedge product, the de Rham differential and the universal
  differential.**  These are exactly the three compatibilities that a base change map of
  completed de Rham complexes along `B → C` needs of a graded comparison of forms, the
  hypotheses `hpsi_wedge`, `hpsi_deRham` and `hpsi1` of
  `Crystalline.CompletedDeRham.baseChangeComplexHom`.
* `Crystalline.completedDividedPowerDeRham_of`,
  `Crystalline.completedDividedPowerWedge_of_of`,
  `Crystalline.completedFormsDifferential_of` — each structure map is the completion of
  its uncompleted counterpart, which is what pins it.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open DividedPowers

universe u v w uI

namespace Crystalline

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {J : Ideal B} (hJ : DividedPowers J)

/-! ### The completed ring and the completed forms -/

/-- **The `p`-adic completion `D` of `B`.** -/
public abbrev completedDividedPowerRing : Type v :=
  AdicCompletion (pAdicIdeal (A := B) p) B

/-- **The module `Ω^i_D`**, the `p`-adic completion of the divided power differential forms
`Ω^i_{B/A,δ}` of [Stacks, Tag 07HZ].  The completion is taken along `(p) ⊆ B`, which is what
makes it a module over `D`. -/
public abbrev completedDividedPowerForms (i : ℕ) : Type v :=
  AdicCompletion (pAdicIdeal (A := B) p) (dividedPowerDifferentialForms (A := A) hJ i)

/-! ### The universal differential of the completion -/

/-- The universal divided power differential `B → Ω^1_{B/A,δ}`, as an additive map into the
degree-one exterior power. -/
public noncomputable def dividedPowerOneForm :
    B →+ dividedPowerDifferentialForms (A := A) hJ 1 :=
  AddMonoidHom.mk'
    (fun b ↦ (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
      (dividedPowerDifferential (A := A) hJ b))
    (fun x y ↦ by rw [dividedPowerDifferential_add hJ, map_add])

/-- `dividedPowerOneForm A hJ b` is the image of `dividedPowerDifferential hJ b` under the
identification of `Ω^1_{B/A,δ}` with its first exterior power. -/
@[simp] public theorem dividedPowerOneForm_apply (b : B) :
    dividedPowerOneForm A hJ b =
      (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ)).symm
        (dividedPowerDifferential (A := A) hJ b) := rfl

/-- **The universal differential `d : D → Ω^1_D`** of the completion: the completion of the
universal divided power differential of [Stacks, Tag 07HZ].  It is additive and obeys the
Leibniz rule, but is not `D`-linear, so it is `Crystalline.PAdicCompletion.mapAddHom` and not
`AdicCompletion.map`. -/
public noncomputable def completedFormsDifferential :
    completedDividedPowerRing p (B := B) → completedDividedPowerForms p A hJ 1 :=
  fun x ↦ PAdicCompletion.mapAddHom p B B (dividedPowerOneForm A hJ) x

/-- The universal differential of the completion extends the uncompleted one. -/
@[simp] public theorem completedFormsDifferential_of (b : B) :
    completedFormsDifferential p A hJ
        (AdicCompletion.of (pAdicIdeal (A := B) p) B b) =
      AdicCompletion.of (pAdicIdeal (A := B) p)
        (dividedPowerDifferentialForms (A := A) hJ 1) (dividedPowerOneForm A hJ b) :=
  PAdicCompletion.mapAddHom_of p B B (dividedPowerOneForm A hJ) b

/-- The value of the universal differential of the completion at the level `pⁿ`. -/
public theorem completedFormsDifferential_val (n : ℕ)
    (x : completedDividedPowerRing p (B := B)) (b : B) (hb : x.val n = Submodule.Quotient.mk b) :
    (completedFormsDifferential p A hJ x).val n =
      Submodule.Quotient.mk (dividedPowerOneForm A hJ b) := by
  show PAdicCompletion.levelMap p B B (dividedPowerOneForm A hJ) n (x.val n) = _
  rw [hb, PAdicCompletion.levelMap_mk]

/-! ### The wedge product and the de Rham differential of the completed forms -/

/-- **The wedge product `Ω^i_D × Ω^1_D → Ω^{i+1}_D`** of completed forms, `D`-bilinear.
Completion is not monoidal, so this is not `AdicCompletion.map` of the uncompleted wedge; it is
built level by level by `Crystalline.PAdicCompletion.mapBilinear`. -/
public noncomputable def completedDividedPowerWedge (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₗ[completedDividedPowerRing p (B := B)]
      completedDividedPowerForms p A hJ 1 →ₗ[completedDividedPowerRing p (B := B)]
        completedDividedPowerForms p A hJ (i + 1) :=
  PAdicCompletion.mapBilinear p B (dividedPowerWedge hJ i)

/-- The wedge product of completed forms extends the uncompleted wedge. -/
@[simp] public theorem completedDividedPowerWedge_of_of (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ 1) :
    completedDividedPowerWedge p A hJ i
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ omega)
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ eta) =
      AdicCompletion.of (pAdicIdeal (A := B) p) _ (dividedPowerWedge hJ i omega eta) :=
  PAdicCompletion.mapBilinear_of_of p B (dividedPowerWedge hJ i) omega eta

/-- The value of the wedge product of completed forms at the level `pⁿ`. -/
public theorem completedDividedPowerWedge_val (i n : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ 1)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ 1)
    (hx : x.val n = Submodule.Quotient.mk omega) (hy : y.val n = Submodule.Quotient.mk eta) :
    (completedDividedPowerWedge p A hJ i x y).val n =
      Submodule.Quotient.mk (dividedPowerWedge hJ i omega eta) := by
  rw [completedDividedPowerWedge, PAdicCompletion.mapBilinear_val, hx, hy,
    PAdicCompletion.levelMapBilinear_mk_mk]

/-! ### The bigraded wedge product of the completed forms -/

/-- **The bigraded wedge product `Ω^i_D × Ω^j_D → Ω^{i+j}_D`** of completed forms, `D`-bilinear.

`Crystalline.completedDividedPowerWedge` is the special case `j = 1` that the completed de Rham
complex is built from — in the opposite variance, see
`Crystalline.completedDividedPowerWedge_eq_wedgeMul`.  The general bidegree is what a filtration
of the completed de Rham complex by `F^i ∧ Ω^*` needs, since its graded pieces multiply forms of
two arbitrary degrees.

Like the one-form case this is `Crystalline.PAdicCompletion.mapBilinear` of the uncompleted
product and not `AdicCompletion.map` of anything: completion is not monoidal, so there is no map
`Ω^i_D ⊗ Ω^j_D → (Ω^i ⊗ Ω^j)^∧` to push `exteriorPower.wedgeMul` along. -/
public noncomputable def completedDividedPowerWedgeMul (i j : ℕ) :
    completedDividedPowerForms p A hJ i →ₗ[completedDividedPowerRing p (B := B)]
      completedDividedPowerForms p A hJ j →ₗ[completedDividedPowerRing p (B := B)]
        completedDividedPowerForms p A hJ (i + j) :=
  PAdicCompletion.mapBilinear p B (exteriorPower.wedgeMul i j)

/-- The bigraded wedge product of completed forms extends the uncompleted wedge. -/
@[simp] public theorem completedDividedPowerWedgeMul_of_of (i j : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ j) :
    completedDividedPowerWedgeMul p A hJ i j
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ omega)
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ eta) =
      AdicCompletion.of (pAdicIdeal (A := B) p) _ (exteriorPower.wedgeMul i j omega eta) := by
  rw [completedDividedPowerWedgeMul, PAdicCompletion.mapBilinear_of_of]

/-- The value of the bigraded wedge product of completed forms at the level `pⁿ`. -/
public theorem completedDividedPowerWedgeMul_val (i j n : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ j)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ j)
    (hx : x.val n = Submodule.Quotient.mk omega) (hy : y.val n = Submodule.Quotient.mk eta) :
    (completedDividedPowerWedgeMul p A hJ i j x y).val n =
      Submodule.Quotient.mk (exteriorPower.wedgeMul i j omega eta) := by
  rw [completedDividedPowerWedgeMul, PAdicCompletion.mapBilinear_val, hx, hy,
    PAdicCompletion.levelMapBilinear_mk_mk]

/-- **The wedge product the completed de Rham complex is built from is the bigraded wedge product
in bidegree `(1, i)`.**  Two things stand between the two spellings, and this is the bridge
across both: `Crystalline.completedDividedPowerWedge` takes its arguments in the order `(ω, η)`
and multiplies them in the order `η ∧ ω`, and it lands in degree `i + 1` where
`Crystalline.completedDividedPowerWedgeMul 1 i` lands in degree `1 + i`.  Without this the
general wedge would be a second, unrelated product on the same forms; with it, every identity
proved for one is an identity for the other.  It is the completion of
`Crystalline.dividedPowerWedge_eq_wedgeMul`, checked at each level `pⁿ`. -/
public theorem completedDividedPowerWedge_eq_wedgeMul (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ 1) :
    completedDividedPowerWedge p A hJ i x y =
      AdicCompletion.map (pAdicIdeal (A := B) p)
        (exteriorPower.degCongr (R := B) (M := dividedPowerDifferentials (A := A) hJ)
          (Nat.add_comm 1 i)).toLinearMap
        (completedDividedPowerWedgeMul p A hJ 1 i y x) := by
  show PAdicCompletion.mapBilinear p B (dividedPowerWedge hJ i) x y = _
  refine (PAdicCompletion.mapBilinear_eq_of_val p B (dividedPowerWedge hJ i)
    (fun u v ↦ AdicCompletion.map (pAdicIdeal (A := B) p)
      (exteriorPower.degCongr (R := B) (M := dividedPowerDifferentials (A := A) hJ)
        (Nat.add_comm 1 i)).toLinearMap
      (completedDividedPowerWedgeMul p A hJ 1 i v u)) ?_ x y).symm
  intro n z w omega eta hz hw
  rw [AdicCompletion.map_val_apply,
    completedDividedPowerWedgeMul_val p A hJ 1 i n w z eta omega hw hz,
    LinearMap.reduceModIdeal_apply, LinearEquiv.coe_coe,
    dividedPowerWedge_eq_wedgeMul hJ i omega eta]

/-- **The de Rham differential `Ω^i_D → Ω^{i+1}_D`** of the completed forms.  It is additive and
not `D`-linear, so it is `Crystalline.PAdicCompletion.mapAddHom` of the uncompleted differential
and not `AdicCompletion.map` of anything. -/
public noncomputable def completedDividedPowerDeRham (i : ℕ) :
    completedDividedPowerForms p A hJ i →+ completedDividedPowerForms p A hJ (i + 1) :=
  PAdicCompletion.mapAddHom p B B (dividedPowerDeRhamHom hJ i)

/-- The de Rham differential of the completed forms extends the uncompleted one. -/
@[simp] public theorem completedDividedPowerDeRham_of (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    completedDividedPowerDeRham p A hJ i
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ omega) =
      AdicCompletion.of (pAdicIdeal (A := B) p) _ (dividedPowerDeRham hJ i omega) :=
  PAdicCompletion.mapAddHom_of p B B (dividedPowerDeRhamHom hJ i) omega

/-- The value of the de Rham differential of the completed forms at the level `pⁿ`. -/
public theorem completedDividedPowerDeRham_val (i n : ℕ)
    (x : completedDividedPowerForms p A hJ i)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (hx : x.val n = Submodule.Quotient.mk omega) :
    (completedDividedPowerDeRham p A hJ i x).val n =
      Submodule.Quotient.mk (dividedPowerDeRham hJ i omega) := by
  rw [completedDividedPowerDeRham, PAdicCompletion.mapAddHom_val, hx,
    PAdicCompletion.levelMap_mk]
  rfl

/-! ### The Leibniz rule and the exterior identities for the completed forms -/

/-- Every level `pⁿ` of an element of a `p`-adic completion is the class of some element. -/
private theorem exists_val_eq_mk {M : Type*} [AddCommGroup M] [Module B M]
    (x : AdicCompletion (pAdicIdeal (A := B) p) M) (n : ℕ) :
    ∃ m : M, x.val n = Submodule.Quotient.mk m :=
  (Submodule.Quotient.mk_surjective _ (x.val n)).imp fun _ h ↦ h.symm

/-- **The Leibniz rule `d (f · ω) = f · d ω + d f ∧ ω` for the completed divided power forms.**
This is the hypothesis `Crystalline.CompletedDeRham.IsGradedLeibniz` of the completed de Rham
complex of [Stacks, Proposition 60.21.3, Tag 07LG], discharged for the genuine completed forms
of [Stacks, Tag 07HZ].  It is checked at each level `pⁿ`, where it is the uncompleted Leibniz
rule `Crystalline.dividedPowerDeRham_smul`. -/
public theorem isGradedLeibniz_completedDividedPower :
    CompletedDeRham.IsGradedLeibniz (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ) (completedDividedPowerWedge p A hJ)
      (completedDividedPowerDeRham p A hJ) (completedFormsDifferential p A hJ) := by
  intro i f omega
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨b, hb⟩ := exists_val_eq_mk p f n
  obtain ⟨w, hw⟩ := exists_val_eq_mk p omega n
  have hsmul : (f • omega).val n = Submodule.Quotient.mk (b • w) := by
    rw [AdicCompletion.smul_eval, hb, hw]
    exact (Submodule.Quotient.mk_smul _ b w).symm
  have hL := completedDividedPowerDeRham_val p A hJ i n (f • omega) (b • w) hsmul
  have hR1 := completedDividedPowerDeRham_val p A hJ i n omega w hw
  have hdiff := completedFormsDifferential_val p A hJ n f b hb
  have hR2 := completedDividedPowerWedge_val p A hJ i n omega
    (completedFormsDifferential p A hJ f) w (dividedPowerOneForm A hJ b) hw hdiff
  have hbs : (Submodule.Quotient.mk b :
        B ⧸ (pAdicIdeal (A := B) p ^ n • ⊤ : Submodule B B)) •
      (Submodule.Quotient.mk (dividedPowerDeRham hJ i w) :
        dividedPowerDifferentialForms (A := A) hJ (i + 1) ⧸
          (pAdicIdeal (A := B) p ^ n • ⊤ :
            Submodule B (dividedPowerDifferentialForms (A := A) hJ (i + 1)))) =
      Submodule.Quotient.mk (b • dividedPowerDeRham hJ i w) :=
    (Submodule.Quotient.mk_smul _ b _).symm
  rw [hL, AdicCompletion.val_add_apply, hR2, AdicCompletion.smul_eval, hR1, hb, hbs,
    ← Submodule.Quotient.mk_add]
  congr 1
  rw [dividedPowerDeRham_smul hJ i b w, dividedPowerWedge_apply, dividedPowerOneForm_apply,
    LinearEquiv.apply_symm_apply]

/-- **The exterior identities for the completed divided power forms**: the de Rham differential
squares to zero, the wedge is alternating on one-forms, and the graded Leibniz rule holds against
a closed one-form.  This is the hypothesis
`Crystalline.CompletedDeRham.IsGradedExterior` of
`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable`, discharged for the genuine completed
forms of [Stacks, Tag 07HZ].

The third clause is the only one that is not a plain reduction to the uncompleted identity.  A
one-form of the completion which is closed is, at the level `pⁿ`, closed only modulo `pⁿ`, so the
uncompleted statement used is `Crystalline.dividedPowerDeRham_leftWedge`, which names the
correction term `(d η) ∧ ω` as a form; it then lies in `pⁿ Ω^{i+2}` because `d η` lies in
`pⁿ Ω²`. -/
public theorem isGradedExterior_completedDividedPower :
    CompletedDeRham.IsGradedExterior (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ) (completedDividedPowerWedge p A hJ)
      (completedDividedPowerDeRham p A hJ) where
  deRham_deRham i omega := by
    refine AdicCompletion.ext fun n ↦ ?_
    obtain ⟨w, hw⟩ := exists_val_eq_mk p omega n
    rw [completedDividedPowerDeRham_val p A hJ (i + 1) n _ (dividedPowerDeRham hJ i w)
      (completedDividedPowerDeRham_val p A hJ i n omega w hw),
      dividedPowerDeRham_dividedPowerDeRham]
    exact (AdicCompletion.val_zero_apply _ _ n).symm
  wedge_self i omega eta := by
    refine AdicCompletion.ext fun n ↦ ?_
    obtain ⟨w, hw⟩ := exists_val_eq_mk p omega n
    obtain ⟨e, he⟩ := exists_val_eq_mk p eta n
    rw [completedDividedPowerWedge_val p A hJ (i + 1) n _ eta (dividedPowerWedge hJ i w e) e
      (completedDividedPowerWedge_val p A hJ i n omega eta w e hw he) he]
    have hz : dividedPowerWedge hJ (i + 1) (dividedPowerWedge hJ i w e) e = 0 := by
      rw [dividedPowerWedge_apply, dividedPowerWedge_apply]
      exact leftWedge_leftWedge_self i _ w
    rw [hz]
    exact (AdicCompletion.val_zero_apply _ _ n).symm
  deRham_wedge i omega eta hclosed := by
    refine AdicCompletion.ext fun n ↦ ?_
    obtain ⟨w, hw⟩ := exists_val_eq_mk p omega n
    obtain ⟨e, he⟩ := exists_val_eq_mk p eta n
    have hcl : dividedPowerDeRham hJ 1 e ∈
        (pAdicIdeal (A := B) p ^ n • ⊤ :
          Submodule B (dividedPowerDifferentialForms (A := A) hJ (1 + 1))) := by
      have := completedDividedPowerDeRham_val p A hJ 1 n eta e he
      rw [hclosed] at this
      rw [← Submodule.Quotient.mk_eq_zero]
      exact ((AdicCompletion.val_zero_apply _ _ n).symm.trans this).symm
    rw [AdicCompletion.val_add_apply,
      completedDividedPowerDeRham_val p A hJ (i + 1) n _ (dividedPowerWedge hJ i w e)
        (completedDividedPowerWedge_val p A hJ i n omega eta w e hw he),
      completedDividedPowerWedge_val p A hJ (i + 1) n _ eta (dividedPowerDeRham hJ i w) e
        (completedDividedPowerDeRham_val p A hJ i n omega w hw) he,
      ← Submodule.Quotient.mk_add]
    refine ((Submodule.Quotient.mk_eq_zero _).mpr ?_).trans
      (AdicCompletion.val_zero_apply _ _ n).symm
    have hform : dividedPowerDeRham hJ (i + 1) (dividedPowerWedge hJ i w e) +
        dividedPowerWedge hJ (i + 1) (dividedPowerDeRham hJ i w) e =
        twoWedge i (dividedPowerDeRham hJ 1 e) w := by
      rw [dividedPowerWedge_apply, dividedPowerWedge_apply]
      have hrw := dividedPowerDeRham_leftWedge hJ i
        (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ) e) w
      rw [LinearEquiv.symm_apply_apply] at hrw
      exact hrw
    rw [hform]
    obtain ⟨z, hzz⟩ := (PAdicCompletion.mem_pow_smul_top_iff p B n _).mp hcl
    rw [hzz, map_nsmul, LinearMap.smul_apply]
    exact (PAdicCompletion.mem_pow_smul_top_iff p B n _).mpr ⟨twoWedge i z w, rfl⟩

/-- The value at the level `pⁿ` of a `D`-multiple of a completed form, for a scalar that comes
from `B`.  A general scalar of `D` acts on a level through its own residue, which is why the
statement is about one that is the image of some `b : B`: then the action is the `B`-action on the
quotient, for which `Submodule.Quotient.mk` is linear.  That is the only case the graded Leibniz
rule needs, its scalar being the sign `(-1)^i`. -/
public theorem completedDividedPowerForms_smul_val (i n : ℕ)
    (c : completedDividedPowerRing p (B := B)) (b : B)
    (hcb : c = algebraMap B (completedDividedPowerRing p (B := B)) b)
    (x : completedDividedPowerForms p A hJ i)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (hx : x.val n = Submodule.Quotient.mk omega) :
    (c • x).val n = Submodule.Quotient.mk (b • omega) := by
  subst hcb
  rw [IsScalarTower.algebraMap_smul, AdicCompletion.val_smul_apply, hx]
  rfl

/-- The value at the level `pⁿ` of a bigraded wedge product of completed forms **reindexed into
another degree**.  Reindexing is `AdicCompletion.map` of a linear map, which acts on a level by
reduction modulo `pⁿ`, so it passes through `Submodule.Quotient.mk`.

The degrees are kept as the three independent variables `i`, `j`, `k` tied by `h : i + j = k`
rather than specialised at the call site: a statement in which the reindexed degree is a
compound expression like `i + (j + 1)` forces every rewrite that touches it to re-check
`i + (j + 1) ≡ (i + j) + 1` underneath the `Module` instance of a completed exterior power, which
is what exhausts the heartbeat budget of
`Crystalline.completedDividedPowerDeRham_wedgeMul`. -/
public theorem completedDividedPowerWedgeMul_degCongr_val (i j k n : ℕ) (h : i + j = k)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ j)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (eta : dividedPowerDifferentialForms (A := A) hJ j)
    (hx : x.val n = Submodule.Quotient.mk omega) (hy : y.val n = Submodule.Quotient.mk eta) :
    (AdicCompletion.map (pAdicIdeal (A := B) p)
        (exteriorPower.degCongr (R := B) (M := dividedPowerDifferentials (A := A) hJ)
          h).toLinearMap
        (completedDividedPowerWedgeMul p A hJ i j x y)).val n =
      Submodule.Quotient.mk (exteriorPower.degCongr (R := B)
        (M := dividedPowerDifferentials (A := A) hJ) h
        (exteriorPower.wedgeMul i j omega eta)) := by
  rw [AdicCompletion.map_val_apply,
    completedDividedPowerWedgeMul_val p A hJ i j n x y omega eta hx hy]
  rfl

/-- **The bigraded graded Leibniz rule for the completed divided power forms**,
`d (ω ∧ η) = d ω ∧ η + (-1)^i ω ∧ d η`, in every bidegree `(i, j)`.

`Crystalline.CompletedDeRham.IsGradedExterior` carries the graded Leibniz rule only in bidegree
`(i, 1)`, and even there only against a *closed* one-form; its docstring records why — `d η` is a
two-form and `wedge` multiplies only by one-forms, so the term `d η ∧ ω` has no name in the data
that structure carries.  `Crystalline.completedDividedPowerWedgeMul` gives the term a name, and
this is the lemma that removes the restriction: the rule in full, in every bidegree, with no
closedness hypothesis.

It is checked at each level `pⁿ`, where it is the uncompleted
`Crystalline.dividedPowerDeRham_wedgeMul_degCongr`; unlike the closed-one-form clause of
`Crystalline.isGradedExterior_completedDividedPower` it is a plain reduction, since no term has
to be shown to vanish only modulo `pⁿ`.

Both correction terms are reindexed into the degree `(i + j) + 1` of the left hand side by
`AdicCompletion.map (exteriorPower.degCongr ...)`, as in
`Crystalline.completedDividedPowerWedge_eq_wedgeMul`: `d ω ∧ η` is built in degree `(i + 1) + j`
and `ω ∧ d η` in degree `i + (j + 1)`, both the same number as `(i + j) + 1` but neither the same
term.  The second reindexing is the identity on underlying elements and the statement would
typecheck without it; it is written out because a compound degree left to definitional unfolding
makes every rewrite that touches the term re-check `i + (j + 1) ≡ (i + j) + 1` underneath the
`Module` instance of a completed exterior power, which exhausts the heartbeat budget. -/
public theorem completedDividedPowerDeRham_wedgeMul (i j : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ j) :
    completedDividedPowerDeRham p A hJ (i + j)
        (completedDividedPowerWedgeMul p A hJ i j x y) =
      AdicCompletion.map (pAdicIdeal (A := B) p)
          (exteriorPower.degCongr (R := B) (M := dividedPowerDifferentials (A := A) hJ)
            (Nat.succ_add i j)).toLinearMap
          (completedDividedPowerWedgeMul p A hJ (i + 1) j
            (completedDividedPowerDeRham p A hJ i x) y) +
        (-1 : completedDividedPowerRing p (B := B)) ^ i •
          AdicCompletion.map (pAdicIdeal (A := B) p)
            (exteriorPower.degCongr (R := B) (M := dividedPowerDifferentials (A := A) hJ)
              (Nat.add_succ i j)).toLinearMap
            (completedDividedPowerWedgeMul p A hJ i (j + 1) x
              (completedDividedPowerDeRham p A hJ j y)) := by
  have hsc : algebraMap B (completedDividedPowerRing p (B := B)) ((-1 : B) ^ i) =
      (-1 : completedDividedPowerRing p (B := B)) ^ i := by
    rw [map_pow, map_neg, map_one]
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := exists_val_eq_mk p x n
  obtain ⟨eta, heta⟩ := exists_val_eq_mk p y n
  refine (completedDividedPowerDeRham_val p A hJ (i + j) n
      (completedDividedPowerWedgeMul p A hJ i j x y) (exteriorPower.wedgeMul i j omega eta)
      (completedDividedPowerWedgeMul_val p A hJ i j n x y omega eta homega
        heta)).trans ?_
  refine (congrArg Submodule.Quotient.mk
    (dividedPowerDeRham_wedgeMul_degCongr hJ i j omega eta)).trans ?_
  refine Eq.trans (Submodule.Quotient.mk_add _) ?_
  rw [AdicCompletion.val_add_apply]
  rw [completedDividedPowerWedgeMul_degCongr_val p A hJ (i + 1) j (i + j + 1) n
    (Nat.succ_add i j) (completedDividedPowerDeRham p A hJ i x) y
    (dividedPowerDeRham hJ i omega) eta
    (completedDividedPowerDeRham_val p A hJ i n x omega homega) heta]
  rw [completedDividedPowerForms_smul_val p A hJ (i + j + 1) n
    ((-1 : completedDividedPowerRing p (B := B)) ^ i) ((-1 : B) ^ i) hsc.symm _
    (exteriorPower.degCongr (R := B) (M := dividedPowerDifferentials (A := A) hJ)
      (Nat.add_succ i j) (exteriorPower.wedgeMul i (j + 1) omega (dividedPowerDeRham hJ j eta)))
    (completedDividedPowerWedgeMul_degCongr_val p A hJ i (j + 1) (i + j + 1) n
      (Nat.add_succ i j) x (completedDividedPowerDeRham p A hJ j y) omega
      (dividedPowerDeRham hJ j eta) homega
      (completedDividedPowerDeRham_val p A hJ j n y eta heta))]

/-! ### The completed forms as a graded family over `B` itself -/

/-- **The Leibniz rule for the universal divided power one-form**,
`d (b c) = b · d c + c · d b`, read in the degree-one exterior power. -/
public theorem dividedPowerOneForm_mul (b c : B) :
    dividedPowerOneForm A hJ (b * c) =
      b • dividedPowerOneForm A hJ c + c • dividedPowerOneForm A hJ b := by
  rw [dividedPowerOneForm_apply, dividedPowerOneForm_apply, dividedPowerOneForm_apply,
    dividedPowerDifferential_mul, map_add, map_smul, map_smul]

/-- **The universal differential `d : B → Ω^1_D` of the ring `B` itself**: the universal divided
power differential of `B` followed by the completion map.

`Crystalline.completedFormsDifferential` is the universal differential of the `p`-adic
*completion* of `B`; this is its restriction along `AdicCompletion.of`, and it is the one a
completed de Rham complex over `B` is built from — the case that matters when `B` is already
`p`-adically complete, so that it is its own completion up to a canonical isomorphism but not
literally.  The two agree wherever both are defined, by
`Crystalline.completedFormsDifferential_of`. -/
public noncomputable def completedDividedPowerDifferentialOnRing (b : B) :
    completedDividedPowerForms p A hJ 1 :=
  completedFormsDifferential p A hJ (AdicCompletion.of (pAdicIdeal (A := B) p) B b)

/-- The universal differential of the ring is the completion of the uncompleted one-form. -/
@[simp] public theorem completedDividedPowerDifferentialOnRing_eq (b : B) :
    completedDividedPowerDifferentialOnRing p A hJ b =
      AdicCompletion.of (pAdicIdeal (A := B) p) _ (dividedPowerOneForm A hJ b) :=
  completedFormsDifferential_of p A hJ b

/-- **The universal differential of the ring is additive.**  This is the hypothesis `hd'add` of
`Crystalline.CompletedDeRham.baseChangeComplexHom`. -/
public theorem completedDividedPowerDifferentialOnRing_add (b c : B) :
    completedDividedPowerDifferentialOnRing p A hJ (b + c) =
      completedDividedPowerDifferentialOnRing p A hJ b +
        completedDividedPowerDifferentialOnRing p A hJ c := by
  rw [completedDividedPowerDifferentialOnRing_eq, completedDividedPowerDifferentialOnRing_eq,
    completedDividedPowerDifferentialOnRing_eq, map_add (dividedPowerOneForm A hJ), map_add]

/-- **The Leibniz rule `d (b c) = b · d c + c · d b` for the universal differential of the
ring.**  This is the hypothesis `hd'leib` of
`Crystalline.CompletedDeRham.baseChangeComplexHom`. -/
public theorem completedDividedPowerDifferentialOnRing_mul (b c : B) :
    completedDividedPowerDifferentialOnRing p A hJ (b * c) =
      b • completedDividedPowerDifferentialOnRing p A hJ c +
        c • completedDividedPowerDifferentialOnRing p A hJ b := by
  rw [completedDividedPowerDifferentialOnRing_eq, completedDividedPowerDifferentialOnRing_eq,
    completedDividedPowerDifferentialOnRing_eq, dividedPowerOneForm_mul, map_add, map_smul,
    map_smul]

/-- **The wedge product `Ω^i_D × Ω^1_D → Ω^{i+1}_D` of the completed forms, read as
`B`-bilinear.**

`Crystalline.completedDividedPowerWedge` is bilinear over the `p`-adic completion of `B`, which
is what the completed tensor product of [Stacks, Tag 07JG] over that completion needs.  This is
the same product with its scalars restricted along `AdicCompletion.of`, which is what a completed
de Rham complex over `B` itself needs; the restriction is legitimate because the two actions on a
completed module agree through `AdicCompletion.of`, the content of Mathlib's
`IsScalarTower B (AdicCompletion I B) (AdicCompletion I M)`. -/
public noncomputable def completedDividedPowerWedgeOnRing (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₗ[B]
      completedDividedPowerForms p A hJ 1 →ₗ[B] completedDividedPowerForms p A hJ (i + 1) :=
  LinearMap.mk₂ B (fun x y ↦ completedDividedPowerWedge p A hJ i x y)
    (fun x x' y ↦ by rw [map_add, LinearMap.add_apply])
    (fun c x y ↦ by
      rw [← algebraMap_smul (completedDividedPowerRing p (B := B)) c x, LinearMap.map_smul,
        LinearMap.smul_apply,
        algebraMap_smul (completedDividedPowerRing p (B := B)) c
          (completedDividedPowerWedge p A hJ i x y)])
    (fun x y y' ↦ map_add _ y y')
    (fun c x y ↦ by
      rw [← algebraMap_smul (completedDividedPowerRing p (B := B)) c y, LinearMap.map_smul,
        algebraMap_smul (completedDividedPowerRing p (B := B)) c
          (completedDividedPowerWedge p A hJ i x y)])

/-- The `B`-bilinear wedge product is the same product. -/
@[simp] public theorem completedDividedPowerWedgeOnRing_apply (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ 1) :
    completedDividedPowerWedgeOnRing p A hJ i x y = completedDividedPowerWedge p A hJ i x y :=
  rfl

/-- **The Leibniz rule `d (b · ω) = b · d ω + d b ∧ ω` for the completed forms over `B`
itself.**  It is `Crystalline.isGradedLeibniz_completedDividedPower` at the image of `b` under
`AdicCompletion.of`, the two scalar actions agreeing through that map. -/
public theorem isGradedLeibniz_completedDividedPowerOnRing :
    CompletedDeRham.IsGradedLeibniz B (completedDividedPowerForms p A hJ)
      (completedDividedPowerWedgeOnRing p A hJ) (completedDividedPowerDeRham p A hJ)
      (completedDividedPowerDifferentialOnRing p A hJ) := by
  intro i b omega
  have hsc : algebraMap B (completedDividedPowerRing p (B := B)) b =
      AdicCompletion.of (pAdicIdeal (A := B) p) B b := AdicCompletion.algebraMap_apply _ _
  have h := isGradedLeibniz_completedDividedPower p A hJ i
    (AdicCompletion.of (pAdicIdeal (A := B) p) B b) omega
  have hs1 : AdicCompletion.of (pAdicIdeal (A := B) p) B b • omega = b • omega := by
    rw [← hsc]; exact algebraMap_smul _ b omega
  have hs2 : AdicCompletion.of (pAdicIdeal (A := B) p) B b •
        completedDividedPowerDeRham p A hJ i omega =
      b • completedDividedPowerDeRham p A hJ i omega := by
    rw [← hsc]; exact algebraMap_smul _ b _
  rw [hs1, hs2] at h
  exact h

/-! ### The completed de Rham complex of the divided power forms -/

section Complex

variable {M : Type w} [AddCommGroup M] [Module (completedDividedPowerRing p (B := B)) M]
  {ι : Type uI}

/-- **The complex `M ⊗^∧_D Ω^*_D` of [Stacks, Proposition 60.21.3, Tag 07LG], for the genuine
completed divided power forms.**  This is
`Crystalline.CompletedDeRham.complexOfIsIntegrable` instantiated at `Ω^*_D`: the two conditions
on the family of forms that it carries as parameters,
`Crystalline.CompletedDeRham.IsGradedLeibniz` and
`Crystalline.CompletedDeRham.IsGradedExterior`, are supplied by this module, so the complex of
the completed divided power forms exists with no hypothesis about the forms at all.  What
remains hypothesis is about the *connection*: `hexp` that it has a finite coordinate expansion,
`hdx` that the coordinate one-forms are closed, and `hint` integrability — the three inputs of
[Stacks, Tag 07JD].

For a pair `P : Crystalline.Pair` take `nabla := P.nabla` and `hint := P.isIntegrable`. -/
public noncomputable def completedDividedPowerDeRhamComplex
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ 1) (completedFormsDifferential p A hJ) M)
    (dx : ι → completedDividedPowerForms p A hJ 1) (theta : ι → (M → M)) (s : Finset ι)
    (hexp : CompletedDeRham.IsFiniteCoordinateExpansion p
      (completedDividedPowerRing p (B := B)) (completedDividedPowerForms p A hJ 1) dx nabla
      theta s)
    (hdx : ∀ j, completedDividedPowerDeRham p A hJ 1 (dx j) = 0)
    (hint : IsIntegrable p (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ 1) dx nabla) :
    CochainComplex AddCommGrpCat.{max v w} ℕ :=
  CompletedDeRham.complexOfIsIntegrable p (completedDividedPowerRing p (B := B))
    (completedDividedPowerForms p A hJ) (completedDividedPowerWedge p A hJ)
    (completedDividedPowerDeRham p A hJ) M nabla
    (isGradedLeibniz_completedDividedPower p A hJ) dx theta s
    (isGradedExterior_completedDividedPower p A hJ) hexp hdx hint

/-- The degree-`i` term of `M ⊗^∧_D Ω^*_D` is the completed tensor product `M ⊗̂_D Ω^i_D`. -/
public theorem completedDividedPowerDeRhamComplex_X
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ 1) (completedFormsDifferential p A hJ) M)
    (dx : ι → completedDividedPowerForms p A hJ 1) (theta : ι → (M → M)) (s : Finset ι)
    (hexp : CompletedDeRham.IsFiniteCoordinateExpansion p
      (completedDividedPowerRing p (B := B)) (completedDividedPowerForms p A hJ 1) dx nabla
      theta s)
    (hdx : ∀ j, completedDividedPowerDeRham p A hJ 1 (dx j) = 0)
    (hint : IsIntegrable p (completedDividedPowerRing p (B := B))
      (completedDividedPowerForms p A hJ 1) dx nabla) (i : ℕ) :
    (completedDividedPowerDeRhamComplex p A hJ nabla dx theta s hexp hdx hint).X i =
      AddCommGrpCat.of (CompletedTensor p (completedDividedPowerRing p (B := B))
        (completedDividedPowerForms p A hJ i) M) :=
  rfl

end Complex

/-! ### The comparison of completed forms along a divided power morphism -/

section Comparison

variable {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C} (epsilon : DividedPowers K)
  (f : B →ₐ[A] C) (hf : DividedPowers.IsDPMorphism hJ epsilon f.toRingHom)

/-- The ideal `(p) ⊆ B` maps **onto** the ideal `(p) ⊆ C` along any ring map, both being
generated by the image of the integer `p`. -/
public theorem pAdicIdeal_map_ringHom (g : B →+* C) :
    (pAdicIdeal (A := B) p).map g = pAdicIdeal (A := C) p := by
  rw [pAdicIdeal, pAdicIdeal, Ideal.map_span, Set.image_singleton, map_natCast]

/-- The ideal `(p) ⊆ B` maps into the ideal `(p) ⊆ C`.  This is what
`Crystalline.adicCompletionMapₛₗ` needs in order to complete a semilinear map along a ring
map that is not the identity. -/
public theorem pAdicIdeal_map_ringHom_le (g : B →+* C) :
    (pAdicIdeal (A := B) p).map g ≤ pAdicIdeal (A := C) p :=
  le_of_eq (pAdicIdeal_map_ringHom p g)

/-- **The comparison `Ω̂^i_B → Ω̂^i_C` of the `p`-adically completed divided power differential
forms**, induced by a divided power morphism `f : (B, J, δ) → (C, K, ε)` over `A`.

It is the `p`-adic completion of the uncompleted comparison
`Crystalline.mapDifferentialFormsOfDPMorphism`, and it exists because the ideal `(p) ⊆ B` maps
into `(p) ⊆ C`, so the two adic filtrations correspond.  Completion along an ideal is
functorial for semilinear maps carrying one ideal into the other
(`Crystalline.adicCompletionMapₛₗ`); the source and target are modules over the *different*
rings `B` and `C`, so, exactly as in the uncompleted case, the comparison is semilinear over
`f` and not linear.  `AdicCompletion.map` is the case of one ring and a linear map and does not
apply. -/
public noncomputable def completedMapDifferentialForms (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₛₗ[f.toRingHom]
      completedDividedPowerForms p A epsilon i :=
  adicCompletionMapₛₗ
    (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i)
    (pAdicIdeal_map_ringHom_le p f.toRingHom)

/-- **The comparison of completed forms extends the uncompleted comparison.**  The image of the
uncompleted forms is `p`-adically dense, so this and locality at the levels pin it down. -/
@[simp] public theorem completedMapDifferentialForms_of (i : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) hJ i) :
    completedMapDifferentialForms p A hJ epsilon f hf i
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ omega) =
      AdicCompletion.of (pAdicIdeal (A := C) p) _
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i omega) :=
  adicCompletionMapₛₗ_of _ _ omega

/-- The value of the comparison of completed forms at the level `pⁿ`. -/
public theorem completedMapDifferentialForms_val (i n : ℕ)
    (x : completedDividedPowerForms p A hJ i)
    (omega : dividedPowerDifferentialForms (A := A) hJ i)
    (hx : x.val n = Submodule.Quotient.mk omega) :
    (completedMapDifferentialForms p A hJ epsilon f hf i x).val n =
      Submodule.Quotient.mk
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ)
          epsilon f hf i omega) := by
  show adicQuotientMap _ _ n (x.val n) = _
  rw [hx]
  rfl

/-- **The comparison of completed forms respects the wedge product.**  Both sides are computed
at each level `pⁿ` from the uncompleted wedge, where the identity is
`Crystalline.mapDifferentialFormsOfDPMorphism_wedge`. -/
public theorem completedMapDifferentialForms_wedge (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ 1) :
    completedMapDifferentialForms p A hJ epsilon f hf (i + 1)
        (completedDividedPowerWedge p A hJ i x y) =
      completedDividedPowerWedge p A epsilon i
        (completedMapDifferentialForms p A hJ epsilon f hf i x)
        (completedMapDifferentialForms p A hJ epsilon f hf 1 y) := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := exists_val_eq_mk p x n
  obtain ⟨eta, heta⟩ := exists_val_eq_mk p y n
  rw [completedMapDifferentialForms_val p A hJ epsilon f hf (i + 1) n
      (completedDividedPowerWedge p A hJ i x y) (dividedPowerWedge hJ i omega eta)
      (completedDividedPowerWedge_val p A hJ i n x y omega eta homega heta),
    completedDividedPowerWedge_val p A epsilon i n _ _
      (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i omega)
      (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf 1 eta)
      (completedMapDifferentialForms_val p A hJ epsilon f hf i n x omega homega)
      (completedMapDifferentialForms_val p A hJ epsilon f hf 1 n y eta heta),
    mapDifferentialFormsOfDPMorphism_wedge]

/-- **The comparison of completed forms respects the bigraded wedge product**, in every bidegree
`(i, j)`.  This is `Crystalline.completedMapDifferentialForms_wedge` with neither argument
confined to degree one; it is what a filtration of the completed de Rham complex by `F^i ∧ Ω^*`
needs of the comparison, since its graded pieces multiply forms of two arbitrary degrees.  Both
sides are computed at each level `pⁿ` from the uncompleted bigraded wedge, where the identity is
`Crystalline.mapDifferentialFormsOfDPMorphism_wedgeMul`. -/
public theorem completedMapDifferentialForms_wedgeMul (i j : ℕ)
    (x : completedDividedPowerForms p A hJ i) (y : completedDividedPowerForms p A hJ j) :
    completedMapDifferentialForms p A hJ epsilon f hf (i + j)
        (completedDividedPowerWedgeMul p A hJ i j x y) =
      completedDividedPowerWedgeMul p A epsilon i j
        (completedMapDifferentialForms p A hJ epsilon f hf i x)
        (completedMapDifferentialForms p A hJ epsilon f hf j y) := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := exists_val_eq_mk p x n
  obtain ⟨eta, heta⟩ := exists_val_eq_mk p y n
  rw [completedMapDifferentialForms_val p A hJ epsilon f hf (i + j) n
      (completedDividedPowerWedgeMul p A hJ i j x y) (exteriorPower.wedgeMul i j omega eta)
      (completedDividedPowerWedgeMul_val p A hJ i j n x y omega eta homega heta),
    completedDividedPowerWedgeMul_val p A epsilon i j n _ _
      (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i omega)
      (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf j eta)
      (completedMapDifferentialForms_val p A hJ epsilon f hf i n x omega homega)
      (completedMapDifferentialForms_val p A hJ epsilon f hf j n y eta heta),
    mapDifferentialFormsOfDPMorphism_wedgeMul]

/-- **The comparison of completed forms is a map of completed de Rham complexes**:
`ψ (d ω) = d (ψ ω)`.  Both sides are computed at each level `pⁿ` from the uncompleted de Rham
differential, where the identity is
`Crystalline.mapDifferentialFormsOfDPMorphism_deRham`. -/
public theorem completedMapDifferentialForms_deRham (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedMapDifferentialForms p A hJ epsilon f hf (i + 1)
        (completedDividedPowerDeRham p A hJ i x) =
      completedDividedPowerDeRham p A epsilon i
        (completedMapDifferentialForms p A hJ epsilon f hf i x) := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := exists_val_eq_mk p x n
  rw [completedMapDifferentialForms_val p A hJ epsilon f hf (i + 1) n
      (completedDividedPowerDeRham p A hJ i x) (dividedPowerDeRham hJ i omega)
      (completedDividedPowerDeRham_val p A hJ i n x omega homega),
    completedDividedPowerDeRham_val p A epsilon i n _
      (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf i omega)
      (completedMapDifferentialForms_val p A hJ epsilon f hf i n x omega homega),
    mapDifferentialFormsOfDPMorphism_deRham]

/-- **The uncompleted comparison of forms carries the one-form `d b` to `d f(b)`.**  This is
`Crystalline.mapDifferentialsOfDPMorphism_d` read in the degree-one exterior power, through
`exteriorPower.oneEquiv`, which is the spelling the universal differential of the completion is
built from. -/
public theorem mapDifferentialFormsOfDPMorphism_oneForm (b : B) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ) epsilon f hf 1
        (dividedPowerOneForm A hJ b) =
      dividedPowerOneForm A epsilon (f b) := by
  refine (exteriorPower.oneEquiv C (dividedPowerDifferentials (A := A) epsilon)).injective ?_
  rw [mapDifferentialFormsOfDPMorphism_oneEquiv, dividedPowerOneForm_apply,
    dividedPowerOneForm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    mapDifferentialsOfDPMorphism_d]

/-- **The comparison of completed forms respects the universal differential**:
`ψ_1 (d b) = d (f b)` for `b` in the uncompleted ring.

Together with `Crystalline.completedMapDifferentialForms_wedge` and
`Crystalline.completedMapDifferentialForms_deRham` this is the third and last of the
compatibilities `Crystalline.CompletedDeRham.baseChangeComplexHom` asks of a graded comparison
of forms — its `hpsi1`, read for the differential `d b = completedFormsDifferential (of b)` of
the ring `B` itself rather than of its completion.  The two differentials being compared are
the completions of the uncompleted universal differentials, so this is
`Crystalline.mapDifferentialFormsOfDPMorphism_oneForm` carried across the completion. -/
public theorem completedMapDifferentialForms_completedFormsDifferential_of (b : B) :
    completedMapDifferentialForms p A hJ epsilon f hf 1
        (completedFormsDifferential p A hJ (AdicCompletion.of (pAdicIdeal (A := B) p) B b)) =
      completedFormsDifferential p A epsilon
        (AdicCompletion.of (pAdicIdeal (A := C) p) C (f b)) := by
  rw [completedFormsDifferential_of, completedMapDifferentialForms_of,
    mapDifferentialFormsOfDPMorphism_oneForm, completedFormsDifferential_of]

end Comparison

end Crystalline

end
