module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsUnitZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BigradedFormsZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRow
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialStructurePair

/-!
# The horizontal sections sit in `H⁰`, so a completed de Rham complex is never acyclic

`Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamRow.lean` derives the
hypothesis `hrows` of `...SmallSite.computes07LG_of_doubleComplex` from

`∀ b : ℕ, 0 < b → ∀ j : ℕ, IsZero ((W.degreeDeRhamComplex b).homology j)`,

the acyclicity of the completed de Rham complex `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of every positive
cosimplicial degree.  **That antecedent cannot be discharged**, and this module proves it: its
`j = 0` instance already forces the unit of `D̂(b)` to die in the completion, hence `p` to be
invertible in `D̂(b)` — which, `D̂(b)` being a `p`-adic completion, leaves only the degenerate
situations where the whole complex is zero anyway.

The reason is that `H⁰` of a de Rham complex is the group of horizontal sections, which always
contains `1 ⊗ 1`.  Concretely, for a cochain complex indexed by `ℕ` there is no incoming
differential in degree `0`, so `IsZero (K.homology 0)` makes `K.d 0 1` a monomorphism; the
differential `K.d 0 1` of `Crystalline.CompletedDeRham.complex` is `m ⊗ ω ↦ ∇m ∧ ω + m ⊗ dω`,
which kills `m ⊗ ω` whenever `∇ m = 0` and `d ω = 0`; and for the one connection that exists on
every divided power ring, `Crystalline.CompletedDeRham.unitConnection` with `∇ x = 1 ⊗ dx` — the
connection of `Crystalline.CosimplicialDPAlgebra.structurePair`, and hence of the double complex
of the coefficient sheaf `𝒪_{X/S}` — the element `m = 1`, `ω = `
`Crystalline.completedUnitZeroForm` is such a pair, because `d 1 = 0`.

## What this says about [Stacks, Tag 07LG] and about [Stacks, Lemma 60.21.2, Tag 07LD]

The completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] asserts that

`M ⊗^∧_D Ω^*_D ⟶ M ⊗^∧_D Ω^*_{D'}`

is a **quasi-isomorphism**, not that its target is acyclic; and the proof of
[Stacks, Proposition 60.21.3, Tag 07LG] uses it that way.  In the source the rows `K^{*,b}` are
each quasi-isomorphic to the row `K^{*,0} = M ⊗^∧_D Ω^*_D` and the second spectral sequence
degenerates not because the rows off `0` vanish — they do not — but because on the `E₁` page the
alternating sums of the `b + 1` identifications `H^a(K^{*,b}) = H^a(M ⊗^∧_D Ω^*_D)` are
`0, 1, 0, 1, …`, the codiagonal `D(b) → D` being a common retraction.  So the row degeneration
needs a *comparison* hypothesis and not an acyclicity hypothesis, and
`StacksDraft.TotalDegeneration.totalHomologyIsoRowZero` — whose hypothesis is the acyclicity of
the rows off `0` — cannot be the step that runs it.  The corresponding statement about the
columns is a different matter and is not affected: [Stacks, Lemma 60.19.3, Tag 07LA] genuinely
makes the columns `K^{a,*}`, `a > 0`, homotopic to zero.

Nothing here is a counterexample to a tag: it is a proof that one hypothesis of an earlier
reduction of [Stacks, Tag 07LG] in this library is unsatisfiable, so that no one tries to
discharge it from [Stacks, Tag 07LD].

## Main results

* `CochainComplex.mono_d_zero_of_isZero_homology` — in an `ℕ`-indexed cochain complex with
  vanishing `H⁰` the differential out of degree `0` is a monomorphism, there being no incoming
  differential there.
* `Crystalline.CompletedDeRham.injective_differential_zero_of_isZero_homology` — the same for
  `M ⊗^∧_D Ω^*_D`, read on elements.
* `Crystalline.CompletedDeRham.eq_zero_of_isZero_homology_of_horizontal` — **`H⁰ = 0` forces
  every horizontal `m ⊗ ω` to vanish**: if `∇ m = 0` and `d ω = 0` then `m ⊗ ω = 0` in
  `M ⊗̂_D Ω⁰_D`.
* `Crystalline.CosimplicialCompletedPair.eq_zero_of_isZero_homology_zero` — the same at one
  cosimplicial degree of a pair, which is the shape
  `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero` consumes.
* `Crystalline.CosimplicialDPAlgebra.structureNabla_one` — the unit of `D̂(b)` is horizontal for
  the universal connection, `d 1` being zero.
* `Crystalline.CosimplicialDPAlgebra.adicCompletion_of_one_eq_zero_of_isZero_homology` — **the
  antecedent of `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero`, at the pair
  of the coefficient sheaf `𝒪_{X/S}`, kills the unit of `D̂(b)`.**
* `Crystalline.CosimplicialDPAlgebra.isUnit_natCast_of_isZero_homology` — **the same antecedent
  makes `p` invertible in `D̂(b)`**, which is the statement of absurdity in its sharpest form:
  `D̂(b)` is a `p`-adic completion.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.19.3, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open DividedPowers
open scoped TensorProduct

universe u v w

/-! ### Degree zero of an `ℕ`-indexed cochain complex -/

/-- **An `ℕ`-indexed cochain complex with vanishing `H⁰` has a monomorphism out of degree `0`.**
There is no incoming differential in degree `0`, so exactness there is exactly the injectivity of
the outgoing one. -/
public theorem CochainComplex.mono_d_zero_of_isZero_homology {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℕ) (h : IsZero (K.homology 0)) : Mono (K.d 0 1) :=
  (ShortComplex.exact_iff_mono (K.sc' 0 0 1) (K.shape 0 0 (by simp))).1
    ((HomologicalComplex.exactAt_iff' K 0 0 1 CochainComplex.prev_nat_zero
      (CochainComplex.next ℕ 0)).1 ((HomologicalComplex.exactAt_iff_isZero_homology K 0).2 h))

/-- The same for a complex of abelian groups, read on elements. -/
public theorem CochainComplex.injective_d_zero_of_isZero_homology
    (K : CochainComplex AddCommGrpCat.{v} ℕ) (h : IsZero (K.homology 0)) :
    Function.Injective (K.d 0 1) :=
  (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    (CochainComplex.mono_d_zero_of_isZero_homology K h)

namespace Crystalline

/-! ### The unit zero-form under the degree-zero identification -/

section UnitZero

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **The degree-zero identification `Ω⁰_D ≅ D` carries the unit zero-form to `1`.**  This is
`Crystalline.zeroEquiv_unitZeroForm` carried across the `p`-adic completion by
`Crystalline.completedDividedPowerFormsZeroEquiv_of`. -/
@[simp] public theorem completedDividedPowerFormsZeroEquiv_completedUnitZeroForm :
    completedDividedPowerFormsZeroEquiv p A hJ (completedUnitZeroForm p A hJ) = 1 := by
  rw [completedUnitZeroForm, completedDividedPowerFormsZeroEquiv_of, zeroEquiv_unitZeroForm]
  rfl

end UnitZero

namespace CompletedDeRham

section Obstruction

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)

/-- **The degree-zero differential of `M ⊗^∧_D Ω^*_D` is injective as soon as `H⁰` vanishes.**
This is `CochainComplex.injective_d_zero_of_isZero_homology` at
`Crystalline.CompletedDeRham.complex`, whose differential out of degree `0` is
`Crystalline.CompletedDeRham.differential` by
`Crystalline.CompletedDeRham.complex_d`. -/
public theorem injective_differential_zero_of_isZero_homology
    (h : IsZero ((complex p D Om wedge deRham M nabla hleib hsq).homology 0)) :
    Function.Injective (differential p D Om wedge deRham M nabla hleib 0) := by
  have hinj := CochainComplex.injective_d_zero_of_isZero_homology
    (complex p D Om wedge deRham M nabla hleib hsq) h
  rw [complex_d p D Om wedge deRham M nabla hleib hsq 0] at hinj
  exact hinj

/-- **`H⁰` of a completed de Rham complex contains the horizontal sections.**  If `∇ m = 0` and
`d ω = 0` for a zero-form `ω`, then `m ⊗ ω` is a cocycle in degree `0`, so a vanishing `H⁰`
forces `m ⊗ ω = 0`.

The differential is `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ dω`
(`Crystalline.CompletedDeRham.differential_of_tmul`), and both terms are killed by the two
hypotheses. -/
public theorem eq_zero_of_isZero_homology_of_horizontal
    (h : IsZero ((complex p D Om wedge deRham M nabla hleib hsq).homology 0))
    (m : M) (omega : Om 0) (hm : nabla m = 0) (homega : deRham 0 omega = 0) :
    toCompletedTensor p D (Om 0) M (m ⊗ₜ[D] omega) = 0 := by
  refine injective_differential_zero_of_isZero_homology p D Om wedge deRham M nabla hleib hsq h ?_
  rw [map_zero, differential_of_tmul p D Om wedge deRham M nabla hleib 0 m omega, hm, homega,
    map_zero, TensorProduct.tmul_zero, map_zero, add_zero]

end Obstruction

end CompletedDeRham

/-! ### The obstruction at a cosimplicial pair -/

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)

/-- **The antecedent of `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero`, in
degree `j = 0`, kills every horizontal section of the cosimplicial degree `b`.**

`Crystalline.CosimplicialCompletedPair.degreeDeRhamComplex` is
`Crystalline.CompletedDeRham.complex` at the connection the pair carries, so this is
`Crystalline.CompletedDeRham.eq_zero_of_isZero_homology_of_horizontal`. -/
public theorem eq_zero_of_isZero_homology_zero (b : ℕ)
    (h : IsZero ((W.degreeDeRhamComplex b).homology 0)) (m : W.carrier b)
    (omega : E.forms p 0 b) (hm : W.nabla b m = 0) (homega : E.deRham p b 0 omega = 0) :
    toCompletedTensor p (E.completedRing p b) (E.forms p 0 b) (W.carrier b)
      (m ⊗ₜ[E.completedRing p b] omega) = 0 :=
  CompletedDeRham.eq_zero_of_isZero_homology_of_horizontal p (E.completedRing p b)
    (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) (W.carrier b) (W.nabla b)
    (E.isGradedLeibniz p b) (W.isSquareZero b) h m omega hm homega

end CosimplicialCompletedPair

/-! ### The obstruction at the pair of the coefficient sheaf `𝒪_{X/S}` -/

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- **The unit of `D̂(b)` is horizontal for the universal connection.**  The connection of
`Crystalline.CosimplicialDPAlgebra.structurePair` is `∇ x = 1 ⊗ d x`, and `d 1 = 0` by
`Crystalline.completedFormsDifferential_one`. -/
public theorem structureNabla_one (b : ℕ) :
    (E.structurePair p).nabla b (1 : E.completedRing p b) = 0 := by
  change toCompletedTensor p (E.completedRing p b) (E.forms p 1 b) (E.completedRing p b)
    ((1 : E.completedRing p b) ⊗ₜ[E.completedRing p b]
      completedFormsDifferential p A (E.dividedPowers b) 1) = 0
  rw [completedFormsDifferential_one, TensorProduct.tmul_zero, map_zero]

/-- **The degree-zero identification of the cosimplicial forms carries the unit zero-form to
`1`.**  This is `Crystalline.completedDividedPowerFormsZeroEquiv_completedUnitZeroForm` at the
divided powers of the cosimplicial degree `b`. -/
@[simp] public theorem formsZeroEquiv_completedUnitZeroForm (b : ℕ) :
    E.formsZeroEquiv p b (completedUnitZeroForm p A (E.dividedPowers b)) = 1 :=
  completedDividedPowerFormsZeroEquiv_completedUnitZeroForm p A (E.dividedPowers b)

/-- **The antecedent of `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero` forces
the unit of `D̂(b)` to die in its own `p`-adic completion.**

The horizontal section is `1 ⊗ ω₀` with `ω₀ = Crystalline.completedUnitZeroForm` the unit
zero-form, which is closed by
`Crystalline.completedDividedPowerDeRham_completedUnitZeroForm`; the identification
`Crystalline.CosimplicialDPAlgebra.formsZeroEquiv` of `Ω⁰_{D(b)}` with `D̂(b)` carries `ω₀` to
`1`, so `Crystalline.completedTensorUnitEquiv` carries `1 ⊗ ω₀` to the image of `1`. -/
public theorem adicCompletion_of_one_eq_zero_of_isZero_homology (b : ℕ)
    (h : IsZero (((E.structurePair p).degreeDeRhamComplex b).homology 0)) :
    AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p) (E.completedRing p b) 1 = 0 := by
  have hz := (E.structurePair p).eq_zero_of_isZero_homology_zero b h (1 : E.completedRing p b)
    (completedUnitZeroForm p A (E.dividedPowers b)) (E.structureNabla_one p b)
    (completedDividedPowerDeRham_completedUnitZeroForm p A (E.dividedPowers b))
  have hval := completedTensorUnitEquiv_of_tmul p (E.completedRing p b) (E.forms p 0 b)
    ((E.structurePair p).carrier b) (E.formsZeroEquiv p b) (1 : E.completedRing p b)
    (completedUnitZeroForm p A (E.dividedPowers b))
  rw [hz, map_zero, E.formsZeroEquiv_completedUnitZeroForm p b] at hval
  have hone : (1 : E.completedRing p b) • (1 : E.completedRing p b) = 1 := one_smul _ _
  exact (congrArg (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
    (E.completedRing p b)) hone.symm).trans hval.symm

/-- **The antecedent of `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero` makes
`p` invertible in `D̂(b)`** — so, since `D̂(b)` is a `p`-adic completion, it is unsatisfiable
except in the trivial situation.

`Crystalline.CosimplicialDPAlgebra.adicCompletion_of_one_eq_zero_of_isZero_homology` says the
unit of `D̂(b)` is zero at every level of its own `p`-adic completion; read at the level `p¹`
that is `1 ∈ (p) · D̂(b)`, which is an inverse of `p`. -/
public theorem isUnit_natCast_of_isZero_homology (b : ℕ)
    (h : IsZero (((E.structurePair p).degreeDeRhamComplex b).homology 0)) :
    IsUnit (p : E.completedRing p b) := by
  have hzero : (Submodule.Quotient.mk (1 : E.completedRing p b) :
      E.completedRing p b ⧸ ((pAdicIdeal (A := E.completedRing p b) p) ^ 1 • ⊤ :
        Submodule (E.completedRing p b) (E.completedRing p b))) = 0 :=
    congrArg (fun z : AdicCompletion (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b) => z.val 1)
      (E.adicCompletion_of_one_eq_zero_of_isZero_homology p b h)
  rw [Submodule.Quotient.mk_eq_zero, pow_one] at hzero
  have h1 : (1 : E.completedRing p b) ∈ pAdicIdeal (A := E.completedRing p b) p :=
    Submodule.smul_induction_on hzero (fun c hc _ _ => Ideal.mul_mem_right _ _ hc)
      (fun _ _ ha hb => Submodule.add_mem _ ha hb)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
  exact ⟨⟨(p : E.completedRing p b), c, (mul_comm _ c).trans hc, hc⟩, rfl⟩

end CosimplicialDPAlgebra

end Crystalline

end
