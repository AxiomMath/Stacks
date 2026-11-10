module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.JetFinrank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneratingSystem
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Substitution

/-!
# The immersion hypothesis of the smooth Bertini theorem

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]). Hypothesis (3) of
[Stacks, Tag 0FD6] is that the morphism `φ_{L,ψ} : X → 𝐏(V)` attached to the linear system by
[Stacks, Tag 0FCY] is an *immersion*. That morphism is built from a basis of `V` indexed by
`Fin (n + 1)` together with the generation hypothesis (2), which is
`Stacks.Bertini.FamilyDivisors.GeneratesBy` of the sibling module; this module attaches the
morphism and the immersion condition to a `Stacks.Bertini.FamilyDivisors` and hands them to the
two consumers of the proof of the tag.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.toProjectiveSpace` is the morphism `φ_{L,ψ} : X → 𝐏(V)` of
  [Stacks, Tag 0FCY] built from the family's own data in a chosen basis.
* `Stacks.Bertini.FamilyDivisors.IsImmersive` is **hypothesis (3) of [Stacks, Tag 0FD6]**: that
  morphism is an immersion.

## Main results

* `Stacks.Bertini.FamilyDivisors.IsImmersive.isImmersion`: the hypothesis in the form of the
  instance that the consumers take.
* `Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis` and
  `Stacks.Bertini.FamilyDivisors.IsImmersive.congr_basis`: **hypothesis (3) does not depend on
  the basis of the linear system it is stated at**, which is the basis-independence the source's
  statement has. See "What hypothesis (3) depends on the basis through" below.
* `Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'` and
  `Stacks.Bertini.FamilyDivisors.IsImmersive.congr_basis'`: the same with the two bases presented
  at **unrelated index types** `Fin (m + 1)` and `Fin (p + 1)`, which each basis forces to agree.
* `Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`: that transport packaged with
  hypothesis (2) at the target basis, which is **the single step by which every consumer in the
  chain moves hypothesis (3) onto the basis it states the Jacobian criterion against**.
* `Stacks.Bertini.FamilyDivisors.isImmersive_iff_isImmersion_toProjectiveSpaceOver`: the
  hypothesis read on the morphism `φ_{(L, (s₀, …, sₙ))} : X → ℙⁿ_k` of [Stacks, Tag 01ND], the
  two differing by the coordinate isomorphism of the basis.
* `Stacks.Bertini.FamilyDivisors.surjective_evalQuotient_of_isClosed`: **the evaluation
  `V → L_x/𝔪_x²L_x` at a closed point is surjective**, for `k` algebraically closed and `X` of
  finite type over it. This is
  `Stacks.ImmersionEvaluationSurjective.surjective_evalQuotient_of_isClosed` in the standing
  situation.
* `Stacks.Bertini.FamilyDivisors.finrank_ker_evalCoord_of_smooth` and
  `Stacks.Bertini.FamilyDivisors.succ_le_of_smooth`: the two numerical inputs of the dimension
  count of the proof of the tag, `dim ker ev_x = r - (n + 1)` and `n + 1 ≤ r`, in the standing
  situation.
* `Stacks.Bertini.FamilyDivisors.evalVector`: **the evaluation `ev_x : V → ℒ_x/𝔪_x²ℒ_x` with no
  basis chosen**, and `Stacks.Bertini.FamilyDivisors.evalCoord_sectionOf_apply`: the coordinate
  form of the evaluation is this map read through the coordinate isomorphism of a basis.
* `Stacks.Bertini.FamilyDivisors.surjective_evalCoord_sectionOf_iff`: **surjectivity of the
  evaluation does not depend on the basis it is read in**, and
  `Stacks.Bertini.FamilyDivisors.surjective_evalQuotient_of_isClosed_of_basis`,
  `…finrank_ker_evalCoord_of_smooth_of_basis`, `…succ_le_of_smooth_of_basis`: the three
  consequences above with the basis of hypothesis (3) and the basis of the conclusion decoupled.
  See "What hypothesis (3) depends on the basis through" below.
* `Stacks.Bertini.FamilyDivisors.exists_natCast_eq_topologicalKrullDimAt_of_isClosed`: the
  dimension `n` those two are stated at **exists** at every closed point of a smooth `X`.

## Implementation notes

`AlgebraicGeometry.toProjectiveSpaceOfModule` is stated for a module over a commutative ring in
the *same* universe as the scheme, because `𝐏(V)` is a scheme over `Spec k` built from `V`. The
declarations here are therefore about `Stacks.Bertini.FamilyDivisors.{u, u}`: the linear system
of a family whose morphism to `𝐏(V)` is formed lives in the universe of the scheme. Nothing else
in the standing situation needs that, so it is imposed only here.

The hypothesis is stated *at* a basis `b` and the generation hypothesis at the same basis, so
that the morphism it speaks about is syntactically the one the consumers
`Stacks.ImmersionEvaluationSurjective.surjective_evalQuotient_of_isClosed` and
`Stacks.JetFinrank.finrank_ker_evalCoord_of_smooth` take as an instance: both are about
`AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f` for `s` the sections of `b` and `f` the
structure morphism, and no transport along a reindexing of the basis intervenes. The family's own
basis is indexed by `Fin (dim V)` rather than `Fin (n + 1)`; moving between the two is the
business of the caller, and `Stacks.Bertini.FamilyDivisors.generatesBy_basis` supplies the
generation hypothesis at whichever basis is chosen.

No `@[stacks]` attribute is attached: a hypothesis of [Stacks, Tag 0FD6] is not an assertion of
the tag.

## What hypothesis (3) depends on the basis through

Hypothesis (3) of the source is a condition on the linear system alone — `φ_{L,ψ} : X → 𝐏(V)` is
an immersion — while `Stacks.Bertini.FamilyDivisors.IsImmersive` is stated at a basis. The basis
enters it in exactly two ways, and they are of entirely different weight.

**Through the coordinate isomorphism of `𝐏(V)`, and that is immaterial.** The basis `b` of
`AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f` serves only to coordinatize `𝐏(V)`, and
for a *fixed* family `s` two bases give morphisms differing by the change-of-basis automorphism
`AlgebraicGeometry.basisChangeProjectiveSpaceIso` of `𝐏(V)` over `Spec k`; so being an immersion
does not depend on it (`AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_congr_basis`).
Equivalently `AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_iff` already reads the
hypothesis on the morphism `φ_{(L, (s₀, …, sₙ))} : X → ℙⁿ_k`, where no basis of `V` appears.

**Through the family `sᵢ = ψ(vᵢ)`, and that is where the content is.** `IsImmersive b hb` is
`IsImmersion (φ_{(L, (ψ(b₀), …, ψ(bₙ)))})`, so a change of basis replaces the family by the
family obtained from it by an invertible `k`-linear substitution. Comparing the two morphisms
`X → ℙⁿ_k` therefore needs the behaviour of `Stacks.ProjectiveFromSections.toProjectiveSpaceOver`
under such a substitution — the linear automorphism of `ℙⁿ_k` it induces. The coordinate
isomorphisms give that automorphism for free, as
`(basisProjectiveSpaceIso b) ≪≫ (basisProjectiveSpaceIso b').symm`, but not the identity
`φ_{(L, ψ∘b')} = φ_{(L, ψ∘b)} ≫ (that automorphism)`, which is the entire content.

**That identity is now available, conditionally on one statement about ratios of sections.** It
is `Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map`, read in the polynomial model
`Proj k[T₀, …, Tₙ]` of `ℙⁿ_k` rather than in the base-change model, with the automorphism given
as `AlgebraicGeometry.Proj.map` of the graded ring automorphism
`AlgebraicGeometry.basisChangeGradedHom b b'` — the same automorphism as the conjugate of
`AlgebraicGeometry.basisChangeProjectiveSpaceIso`, by
`AlgebraicGeometry.map_basisChangeGradedHom_eq`. Three inputs made it possible, and together they
answer the old objection that what [Stacks, Tag 01ND] does is known only on the *standard* charts
`D₊(Tᵢ)` (`Stacks.ProjectiveSpaceChartRatio.chartPullback_eq`) while a substitution carries those
to the basic opens of arbitrary linear forms:

* `AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map`, naturality of Mathlib's construction in
  the **graded ring** — the companion of the source naturality
  `AlgebraicGeometry.Proj.comp_fromOfGlobalSections`, and the input that moves a substitution off
  the ring homomorphism and onto an automorphism of `Proj`;
* `Stacks.ProjectiveSpaceChartRatio.ι_toPolynomialModel`, which identifies the glued morphism
  restricted to `X_{sᵢ}` with `AlgebraicGeometry.Proj.fromOfGlobalSections` of `Tⱼ ↦ sⱼ/sᵢ`
  **over `k`**, not over `ℤ`. The glueing of `Stacks.ProjectiveFromSections` is performed over
  the integral model, where a substitution with coefficients in `k` does not act;
* the comparison over the *refined* cover by the intersections `X_{sᵢ} ⊓ X_{s'ⱼ}`, rather than
  over either family's own cover, with the resulting ambiguity by a unit absorbed by
  `AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit`.

**That identity is now unconditional, and hypothesis (3) is basis-independent.** The hypothesis
`hagree` — on each `X_{sᵢ} ⊓ X_{s'ⱼ}` the ratios `s'ₘ/s'ⱼ` are, up to one unit independent of
`m`, the substitution applied to the ratios `sₗ/sᵢ` — is discharged by
`Stacks.ProjectiveSpaceChartRatio.exists_unit_resOfLE_chartRatio_eq`, and the identity with no
hypothesis is `Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_basisChangeGradedHom`.
`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis` below is the consequence:
`IsImmersive b hb ↔ IsImmersive b' hb'` for any two bases of `V` indexed by `Fin (n + 1)`, so the
basis in the statement of hypothesis (3) is immaterial. `IsImmersive` itself is left stated at a
basis, which is what the consumers take as an instance; it is now known not to depend on it.

Two bases of `V` indexed by `Fin (n + 1)` and `Fin (m + 1)` force `n = m`, since each computes
`dim V`, and `Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'` performs that reindexing:
the independence is available with the two index types unrelated, which is the form the chain of
consumers below takes the hypothesis in. The gap recorded for [Stacks, Tag 0FD5] at
`Stacks.SectionsVanishingOnSubscheme.toProjectiveSpaceOfVanishingSections` ("the source speaks of
*the* canonical morphism, which is basis free; this construction chooses a basis") is a different
construction and stays.

**What is basis-independent, and is proved here.** Everything the proof of [Stacks, Tag 0FD6]
extracts from hypothesis (3): the surjectivity of the evaluation at a closed point and the two
numbers of the dimension count. All three follow from surjectivity of the basis-free evaluation
`Stacks.Bertini.FamilyDivisors.evalVector` — the two numbers through
`Stacks.ImmersionEvaluationSurjective.finrank_ker_evalCoord` and `…finrank_evalQuotient_le`,
whose right-hand sides mention no basis — and the coordinate isomorphism of a basis does not move
its image (`Stacks.Bertini.FamilyDivisors.range_evalCoord_sectionOf`), so the three primed
statements `…surjective_evalQuotient_of_isClosed_of_basis`,
`…finrank_ker_evalCoord_of_smooth_of_basis` and `…succ_le_of_smooth_of_basis` take hypothesis (3)
at one basis and conclude at an unrelated one — which the unprimed three do not.

**And it is carried through the chain.** The chain from these lemmas to the carriers of the tag
(`Stacks.Bertini.FamilyDivisors.exists_evalMatrix` onwards) used to pass `IsImmersive b hb` and
`JacobianAtDivisor b` at one and the same `b`. Every statement of it now has an `…_of_basis`
sibling taking the two at unrelated bases, and at unrelated index types; the Jacobian criterion
has to stay at the standing basis, the coordinates of the parameter space being coefficients
against it, so the two are separate parameters throughout. Each sibling is its unprimed form
applied to `Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`, which transports the
hypothesis onto whichever basis the criterion is stated at and supplies hypothesis (2) there as
well. The registered carriers
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_`
`basis` and `…_pointwise_of_basis'` take (3) at an arbitrary basis accordingly, as does the
dimension-data form `…forGeneral_smooth_specializedDivisor_of_generates_of_basis`; what is left
at the standing basis is only the two statements those supersede.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.ImmersionEvaluationSurjective Stacks.ProjectiveFromSections

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-! ### The morphism to the projective space of the linear system -/

/-- **The morphism `φ_{L,ψ} : X → 𝐏(V)` of [Stacks, Tag 0FCY] attached to the family of
divisors**, in a basis of `V` indexed by `Fin (n + 1)` whose sections generate `L`. -/
def toProjectiveSpace {n : ℕ} (b : Module.Basis (Fin (n + 1)) D.k D.V) (hb : D.GeneratesBy b) :
    D.X ⟶ projectiveSpaceOfModule D.k D.V :=
  toProjectiveSpaceOfModule b (fun i => D.sectionOf (b i)) hb D.toBase

/-- `φ_{L,ψ}` is a morphism of schemes over `k`. -/
theorem toProjectiveSpace_comp_toSpec {n : ℕ} (b : Module.Basis (Fin (n + 1)) D.k D.V)
    (hb : D.GeneratesBy b) :
    D.toProjectiveSpace b hb ≫ projectiveSpaceOfModuleToSpec D.k D.V = D.toBase :=
  toProjectiveSpaceOfModule_comp_toSpec b (fun i => D.sectionOf (b i)) hb D.toBase

/-! ### The immersion hypothesis -/

/-- **Hypothesis (3) of [Stacks, Tag 0FD6]: the morphism `φ_{L,ψ} : X → 𝐏(V)` is an
immersion.** -/
def IsImmersive {n : ℕ} (b : Module.Basis (Fin (n + 1)) D.k D.V) (hb : D.GeneratesBy b) : Prop :=
  IsImmersion (D.toProjectiveSpace b hb)

/-- **Hypothesis (3) in the shape the consumers take it**: an `IsImmersion` instance for the
morphism `AlgebraicGeometry.toProjectiveSpaceOfModule b s hs f` built from the family's own
sections and structure morphism. -/
theorem IsImmersive.isImmersion {n : ℕ} {b : Module.Basis (Fin (n + 1)) D.k D.V}
    {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb) :
    IsImmersion (toProjectiveSpaceOfModule b (fun i => D.sectionOf (b i)) hb D.toBase) :=
  himm

/-- **Hypothesis (3) read on the morphism to `ℙⁿ_k`.** The morphism `φ_{L,ψ} : X → 𝐏(V)` and the
morphism `φ_{(L, (s₀, …, sₙ))} : X → ℙⁿ_k` of [Stacks, Tag 01ND] differ by the coordinate
isomorphism of the basis, so either may serve as the hypothesis. -/
theorem isImmersive_iff_isImmersion_toProjectiveSpaceOver {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) D.k D.V) (hb : D.GeneratesBy b) :
    D.IsImmersive b hb ↔
      IsImmersion (toProjectiveSpaceOver (fun i => D.sectionOf (b i)) hb D.toBase) :=
  isImmersion_toProjectiveSpaceOfModule_iff b (fun i => D.sectionOf (b i)) hb D.toBase

/-! ### The immersion hypothesis does not depend on the basis -/

/-- The section of a linear combination of vectors is the combination of their sections. -/
private theorem sectionOf_sum_smul {ι : Type*} [Fintype ι] (c : ι → D.k) (u : ι → D.V) :
    D.sectionOf (∑ j, c j • u j) = ∑ j, D.baseScalar (c j) • D.sectionOf (u j) := by
  change D.ψ (∑ j, c j • u j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => D.sectionOf_smul _ _

/-- **The section of a vector is the combination of the sections of any basis of the linear
system**, the coefficients of `k` acting through the structure morphism. This is
`Stacks.Bertini.FamilyDivisors.sectionOf_eq_sum` at an arbitrary basis. -/
theorem sectionOf_eq_sum_basis {n : ℕ} (b : Module.Basis (Fin (n + 1)) D.k D.V) (v : D.V) :
    D.sectionOf v = ∑ l, D.baseScalar (b.repr v l) • D.sectionOf (b l) := by
  conv_lhs => rw [← b.sum_repr v]
  exact D.sectionOf_sum_smul _ _

/-- The scalar through which `k` acts on the global sections of `L` is
`Stacks.ProjectiveSpaceChartRatio.baseRingHom` of the structure morphism: the two spellings of
the `k`-algebra structure of `Γ(X, 𝒪_X)` agree. -/
theorem baseScalar_eq_baseRingHom (c : D.k) :
    D.baseScalar c = Stacks.ProjectiveSpaceChartRatio.baseRingHom D.toBase c := rfl

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] does not depend on the basis of the linear system it
is stated at.** This is the basis-independence the source's statement has and
`Stacks.Bertini.FamilyDivisors.IsImmersive` did not: changing the basis changes the *family*
`sᵢ = ψ(bᵢ)` by the invertible linear substitution of the change of basis, and
`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_basisChangeGradedHom` says the two
morphisms to `ℙⁿ_k` then differ by the automorphism of `ℙⁿ_k` that substitution induces.

`AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_congr_basis` is the easy half of this,
for a *fixed* family; see "What hypothesis (3) depends on the basis through" in the module
docstring. -/
theorem isImmersive_congr_basis {n : ℕ} (b b' : Module.Basis (Fin (n + 1)) D.k D.V)
    (hb : D.GeneratesBy b) (hb' : D.GeneratesBy b') :
    D.IsImmersive b hb ↔ D.IsImmersive b' hb' := by
  have := AlgebraicGeometry.isIso_map_basisChangeGradedHom b b'
  rw [D.isImmersive_iff_isImmersion_toProjectiveSpaceOver b hb,
    D.isImmersive_iff_isImmersion_toProjectiveSpaceOver b' hb',
    ← Stacks.ProjectiveSpaceChartRatio.isImmersion_toPolynomialModel_iff
      (fun i => D.sectionOf (b i)) hb D.toBase,
    ← Stacks.ProjectiveSpaceChartRatio.isImmersion_toPolynomialModel_iff
      (fun i => D.sectionOf (b' i)) hb' D.toBase,
    Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_basisChangeGradedHom
      (fun i => D.sectionOf (b i)) hb D.toBase b b' hb'
      (fun m => D.sectionOf_eq_sum_basis b (b' m))]
  exact (IsImmersion.comp_iff _ _).symm

/-- **Hypothesis (3) transported to another basis of the linear system**, the form the chain of
consumers takes it in. -/
theorem IsImmersive.congr_basis {n : ℕ} {b : Module.Basis (Fin (n + 1)) D.k D.V}
    {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb)
    (b' : Module.Basis (Fin (n + 1)) D.k D.V) (hb' : D.GeneratesBy b') :
    D.IsImmersive b' hb' :=
  (D.isImmersive_congr_basis b b' hb hb').mp himm

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] does not depend on the basis of the linear system it
is stated at, nor on the index type that basis is presented at.** This is
`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis` with the two bases allowed to be indexed
by `Fin (m + 1)` and `Fin (p + 1)` for unrelated `m` and `p`.

The two index types are forced to agree: each basis computes the dimension of `V`, so
`m + 1 = dim V = p + 1`. Once that is substituted the statement is the one-index-type form, so
nothing is added to the mathematics of `isImmersive_congr_basis` here; what is removed is the
obligation on a caller to produce its two bases at a syntactically equal index. -/
theorem isImmersive_congr_basis' {m p : ℕ} (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (b' : Module.Basis (Fin (p + 1)) D.k D.V) (hb : D.GeneratesBy b) (hb' : D.GeneratesBy b') :
    D.IsImmersive b hb ↔ D.IsImmersive b' hb' := by
  obtain rfl : p = m := by
    have hm : Module.finrank D.k D.V = m + 1 := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    have hp : Module.finrank D.k D.V = p + 1 := by
      rw [Module.finrank_eq_card_basis b', Fintype.card_fin]
    omega
  exact D.isImmersive_congr_basis b b' hb hb'

/-- **Hypothesis (3) transported to a basis of the linear system at another index type**, the
form the chain of consumers takes it in: `Stacks.Bertini.FamilyDivisors.IsImmersive.congr_basis`
with the index types of the two bases unrelated. -/
theorem IsImmersive.congr_basis' {m p : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V}
    {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb)
    (b' : Module.Basis (Fin (p + 1)) D.k D.V) (hb' : D.GeneratesBy b') :
    D.IsImmersive b' hb' :=
  (D.isImmersive_congr_basis' b b' hb hb').mp himm

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] read at any basis of the linear system, with
hypothesis (2) at that basis supplied too.** This is the single step by which a consumer stating
the hypothesis at a basis of its own moves one given at an unrelated basis onto it: the immersion
hypothesis transports by
`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'` and the generation hypothesis, being
basis free, by `Stacks.Bertini.FamilyDivisors.generatesBy_basis_of_generatesBy`, so the consumer
need not take a second generation hypothesis. -/
theorem isImmersive_basis_of_isImmersive {m p : ℕ} {b' : Module.Basis (Fin (p + 1)) D.k D.V}
    {hb' : D.GeneratesBy b'} (himm : D.IsImmersive b' hb')
    (b : Module.Basis (Fin (m + 1)) D.k D.V) :
    D.IsImmersive b (D.generatesBy_basis_of_generatesBy hb' b) :=
  (D.isImmersive_congr_basis' b' b hb' _).mp himm

/-! ### What the hypotheses are used for -/

/-- **The evaluation `V → L_x/𝔪_x²L_x` at a closed point is surjective**, under hypotheses (2)
and (3) of [Stacks, Tag 0FD6] over an algebraically closed field and for `X` locally of finite
type. This is the detail the source omits, in the standing situation. -/
theorem surjective_evalQuotient_of_isClosed [IsAlgClosed D.k] [LocallyOfFiniteType D.toBase]
    {n : ℕ} {b : Module.Basis (Fin (n + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    Function.Surjective fun c : Fin (n + 1) → D.k =>
      Submodule.Quotient.mk (p := maximalSqSmul D.L x)
        (∑ j, baseGerm D.toBase x (c j) • (D.L.presheaf.Γgerm x).hom (D.sectionOf (b j))) :=
  have := himm.isImmersion
  Stacks.ImmersionEvaluationSurjective.surjective_evalQuotient_of_isClosed
    (fun i => D.sectionOf (b i)) hb D.toBase b hx

/-- **The kernel of the evaluation at a closed point of a smooth `X` has dimension
`r - (n + 1)`**, where `r` is the dimension of the linear system and `n` the dimension of `X` at
the point: the fibre bound that the dimension count of [Stacks, Tag 0FD6] consumes, in the
standing situation. -/
theorem finrank_ker_evalCoord_of_smooth [IsAlgClosed D.k] [Smooth D.toBase] {m n : ℕ}
    {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) :
    Module.finrank D.k
        (LinearMap.ker (evalCoord (fun i => D.sectionOf (b i)) D.toBase x)) =
      (m + 1) - (n + 1) :=
  have := himm.isImmersion
  Stacks.JetFinrank.finrank_ker_evalCoord_of_smooth D.toBase x
    (fun i => D.sectionOf (b i)) hb b hx hdim

/-- **`X` has a finite dimension at each of its closed points** when it is smooth over `k`: the
local ring there is regular, so its Krull dimension is the dimension of its cotangent space.

This is what supplies the natural number `n` that `hdim` names in the results of this module and
in `Stacks.Bertini.FamilyDivisors.exists_evalMatrix`: those results are stated at a closed point
of `X` where the dimension *is* a given `n`, and this says such an `n` exists at every closed
point, with no bound on the dimension of `X` assumed. -/
theorem exists_natCast_eq_topologicalKrullDimAt_of_isClosed [IsAlgClosed D.k] [Smooth D.toBase]
    {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    ∃ n : ℕ, topologicalKrullDimAt D.X x = (n : WithBot ℕ∞) :=
  Stacks.JetFinrank.exists_natCast_eq_topologicalKrullDimAt_of_isClosed D.toBase x hx

/-- **The linear system has dimension at least `n + 1`** at a closed point of a smooth `X` of
dimension `n` there: the other numerical input of the dimension count, in the standing
situation. -/
theorem succ_le_of_smooth [IsAlgClosed D.k] [Smooth D.toBase] {m n : ℕ}
    {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) : n + 1 ≤ m + 1 :=
  have := himm.isImmersion
  Stacks.JetFinrank.succ_le_of_smooth D.toBase x (fun i => D.sectionOf (b i)) hb b hx hdim

/-! ### The evaluation does not depend on the basis -/

/-- **The evaluation `ev_x : V → ℒ_x/𝔪_x²ℒ_x` of the linear system at a point of `X`**, as a
`k`-linear map on `V` itself: a vector `v` goes to the class of the germ of `ψ(v)`. The
coordinate form `Stacks.ImmersionEvaluationSurjective.evalCoord` of the same map is this one
precomposed with the coordinate isomorphism of a basis, which is what makes its image and the
dimension of its kernel independent of the basis. -/
def evalVector (x : D.X) : D.V →ₗ[D.k] evalQuotient D.toBase D.L x where
  toFun v := evalQuotientMk D.toBase x ((D.L.presheaf.Γgerm x).hom (D.sectionOf v))
  map_add' v w := by
    show evalQuotientMk D.toBase x ((D.L.presheaf.Γgerm x).hom (D.sectionOf (v + w))) = _
    rw [D.sectionOf_add, map_add]
    rfl
  map_smul' a v := by
    change evalQuotientMk D.toBase x ((D.L.presheaf.Γgerm x).hom (D.sectionOf (a • v))) = _
    rw [D.sectionOf_smul, Stacks.ModuleStalk.Γgerm_smul]
    rfl

/-- The germ of a scalar of the base field read as a global function is the structure map of the
stalk applied to it. -/
theorem Γgerm_baseScalar (x : D.X) (c : D.k) :
    (D.X.presheaf.Γgerm x).hom (D.baseScalar c) = baseGerm D.toBase x c :=
  rfl

/-- **The coordinate form of the evaluation is the basis-free one read through the basis**: the
tuple `c` evaluates to the value of `ev_x` at the vector `∑ⱼ cⱼvⱼ`. -/
theorem evalCoord_sectionOf_apply {n : ℕ} (b : Module.Basis (Fin (n + 1)) D.k D.V) (x : D.X)
    (c : Fin (n + 1) → D.k) :
    evalCoord (fun j => D.sectionOf (b j)) D.toBase x c = D.evalVector x (∑ j, c j • b j) := by
  change evalQuotientMk D.toBase x _ =
    evalQuotientMk D.toBase x ((D.L.presheaf.Γgerm x).hom (D.sectionOf (∑ j, c j • b j)))
  rw [D.sectionOf_sum_smul, map_sum]
  exact congrArg (evalQuotientMk D.toBase x) (Finset.sum_congr rfl fun j _ => by
    rw [Stacks.ModuleStalk.Γgerm_smul, D.Γgerm_baseScalar x (c j)])

/-- **The image of the evaluation in its coordinate form is the image of the basis-free
evaluation**, for every basis of the linear system: the coordinate isomorphism of a basis is
onto `V`. -/
theorem range_evalCoord_sectionOf {n : ℕ} (b : Module.Basis (Fin (n + 1)) D.k D.V) (x : D.X) :
    LinearMap.range (evalCoord (fun j => D.sectionOf (b j)) D.toBase x) =
      LinearMap.range (D.evalVector x) := by
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  · obtain ⟨c, rfl⟩ := hq
    exact ⟨_, (D.evalCoord_sectionOf_apply b x c).symm⟩
  · obtain ⟨v, rfl⟩ := hq
    refine ⟨fun j => b.repr v j, ?_⟩
    rw [D.evalCoord_sectionOf_apply b x, b.sum_repr v]

/-- **Surjectivity of the evaluation does not depend on the basis of the linear system it is
read in.** Both coordinate forms have the image of the basis-free evaluation
`Stacks.Bertini.FamilyDivisors.evalVector` as their image. -/
theorem surjective_evalCoord_sectionOf_iff {n m : ℕ} (b : Module.Basis (Fin (n + 1)) D.k D.V)
    (b' : Module.Basis (Fin (m + 1)) D.k D.V) (x : D.X) :
    Function.Surjective (evalCoord (fun j => D.sectionOf (b j)) D.toBase x) ↔
      Function.Surjective (evalCoord (fun l => D.sectionOf (b' l)) D.toBase x) := by
  rw [← LinearMap.range_eq_top, ← LinearMap.range_eq_top, D.range_evalCoord_sectionOf b x,
    D.range_evalCoord_sectionOf b' x]

/-- **The evaluation at a closed point is surjective, from hypothesis (3) at an arbitrary basis
of the linear system.** The basis `b'` at which the immersion hypothesis is taken and the basis
`b` in whose coordinates the conclusion is read are unrelated, and `b` is not required to
generate: surjectivity is a property of the basis-free evaluation
`Stacks.Bertini.FamilyDivisors.evalVector`. -/
theorem surjective_evalCoord_sectionOf_of_isClosed [IsAlgClosed D.k]
    [LocallyOfFiniteType D.toBase] {n m : ℕ} {b' : Module.Basis (Fin (m + 1)) D.k D.V}
    {hb' : D.GeneratesBy b'} (himm : D.IsImmersive b' hb')
    (b : Module.Basis (Fin (n + 1)) D.k D.V) {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    Function.Surjective (evalCoord (fun j => D.sectionOf (b j)) D.toBase x) :=
  (D.surjective_evalCoord_sectionOf_iff b b' x).mpr
    (D.surjective_evalQuotient_of_isClosed himm hx)

/-- **The evaluation `V → L_x/𝔪_x²L_x` at a closed point is surjective**, from hypothesis (3) at
an arbitrary basis of the linear system: `Stacks.Bertini.FamilyDivisors.
surjective_evalQuotient_of_isClosed` with the basis of the hypothesis and the basis of the
conclusion decoupled. -/
theorem surjective_evalQuotient_of_isClosed_of_basis [IsAlgClosed D.k]
    [LocallyOfFiniteType D.toBase] {n m : ℕ} {b' : Module.Basis (Fin (m + 1)) D.k D.V}
    {hb' : D.GeneratesBy b'} (himm : D.IsImmersive b' hb')
    (b : Module.Basis (Fin (n + 1)) D.k D.V) {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    Function.Surjective fun c : Fin (n + 1) → D.k =>
      Submodule.Quotient.mk (p := maximalSqSmul D.L x)
        (∑ j, baseGerm D.toBase x (c j) • (D.L.presheaf.Γgerm x).hom (D.sectionOf (b j))) :=
  D.surjective_evalCoord_sectionOf_of_isClosed himm b hx

/-- **The kernel of the evaluation at a closed point of a smooth `X` has dimension
`r - (n + 1)`, from hypothesis (3) at an arbitrary basis of the linear system**:
`Stacks.Bertini.FamilyDivisors.finrank_ker_evalCoord_of_smooth` with the basis of the hypothesis
and the basis of the conclusion decoupled. -/
theorem finrank_ker_evalCoord_of_smooth_of_basis [IsAlgClosed D.k] [Smooth D.toBase]
    {m n p : ℕ} {b' : Module.Basis (Fin (m + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (p + 1)) D.k D.V) {x : D.X}
    (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) :
    Module.finrank D.k
        (LinearMap.ker (evalCoord (fun j => D.sectionOf (b j)) D.toBase x)) =
      (p + 1) - (n + 1) := by
  rw [finrank_ker_evalCoord _ D.toBase x
      (D.surjective_evalCoord_sectionOf_of_isClosed himm b hx),
    Stacks.JetFinrank.finrank_evalQuotient_of_isClosed D.toBase x hx hdim]

/-- **The linear system has dimension at least `n + 1`, from hypothesis (3) at an arbitrary basis
of the linear system**: `Stacks.Bertini.FamilyDivisors.succ_le_of_smooth` with the basis of the
hypothesis and the basis of the conclusion decoupled. -/
theorem succ_le_of_smooth_of_basis [IsAlgClosed D.k] [Smooth D.toBase] {m n p : ℕ}
    {b' : Module.Basis (Fin (m + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (p + 1)) D.k D.V) {x : D.X}
    (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) : n + 1 ≤ p + 1 := by
  have h := finrank_evalQuotient_le (fun j => D.sectionOf (b j)) D.toBase x
    (D.surjective_evalCoord_sectionOf_of_isClosed himm b hx)
  rwa [Stacks.JetFinrank.finrank_evalQuotient_of_isClosed D.toBase x hx hdim] at h

end Stacks.Bertini.FamilyDivisors

end
