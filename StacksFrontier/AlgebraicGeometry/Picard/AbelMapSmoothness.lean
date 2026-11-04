module

public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Picard.DegreeAtLeastGenus
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective

/-!
# Clause (5) of Tag 0BA0: two steps towards the smoothness of the Abel map

Let `k` be a separably closed field and let `X` be a smooth projective curve of genus `g` over
`k`. Clause (5) of [Stacks, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0) asserts that the
Abel maps

`γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}`

of clause (4) are surjective for `d ≥ g` and **smooth for `d ≥ 2g - 1`**. The surjectivity half is
proved, on `k`-points, as
`AlgebraicGeometry.exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree`. This file
holds **two of the four steps** of the smoothness half, and the smoothness assertion itself is
*not* proved here: step 3 is missing, and §"Step 3 is missing" below says so in full.

The source's argument has four steps.

1. The fibre of `γ_d` over the point corresponding to an invertible module `ℒ` is
   `Z = {D ⊂ X | 𝒪_X(D) ≅ ℒ}`, and `Z ≅ Proj(Sym(Γ(X, ℒ)^*))` — a projective space over the
   residue field. The source states this and omits its proof ("*we omit the precise formulation
   and proof*"). It is independent of `d`. **Carried**, as `HasProjectiveSpaceFibres`.
2. `dim_k H⁰(X, ℒ) = d + 1 - g` for every `ℒ` of degree `d ≥ 2g - 1`, by
   [Stacks, Tag 0B90] and Riemann-Roch. **Proved here**, and it is the only place the bound
   `2g - 1 ≤ d` is used.
3. Hence every fibre has dimension `d - g`, which is `dim Hilb^d_{X/k} - dim Pic^d_{X/k}`, so
   `γ_d` is flat by Algebra, Lemma [Stacks, Tag 00R4] (miracle flatness). **Not proved, and not
   carried either**: flatness is simply a hypothesis.
4. A flat morphism, locally of finite presentation, with smooth fibres is smooth
   ([Stacks, Tag 01V9]); this is Mathlib's
   `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`. **Proved here**, with step 1
   supplying the fibres.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_add_one_sub_genus`: Riemann-Roch in the
  form `dim_k H⁰(X, ℒ) = deg(ℒ) + 1 - g`, for an invertible module with `H¹(X, ℒ) = 0`.
* `finrank_cohomologyOverField_zero_eq_add_one_sub_genus_of_le_invertibleCurveDegree`:
  step 2, `dim_k H⁰(X, ℒ) = d + 1 - g` for `deg(ℒ) = d ≥ 2g - 1`. This is the curve-specific
  content of the file and the only place the degree bound appears.
* `AlgebraicGeometry.smooth_of_hasProjectiveSpaceFibres`: step 4. A **flat** morphism, locally of
  finite presentation, whose fibres are projective spaces over their residue fields, is smooth.
  Its statement is general: no curve, no genus and no degree bound occur in it.

## Main definitions

* `AlgebraicGeometry.HasProjectiveSpaceFibres`: step 1, the source's omitted fibre
  identification.

## Step 3 is missing

Step 3 is miracle flatness, [Stacks, Tag 00R4], applied to `γ_d`: the source's sentences
"*Since `dim H⁰(X, ℒ) = d + 1 - g` ... we conclude that `dim(Z) = d - g`. We conclude that the
fibres of the morphism `γ_d` all have dimension equal to the difference of the dimensions of
`Hilb^d_{X/k}` and `Pic^d_{X/k}`. It follows that `γ_d` is flat, see Algebra, Lemma 00R4.*" What
is needed is the **scheme-level** form of that lemma — regular source, regular target, constant
fibre dimension `dim H - dim P`, hence `Flat γ` — and the library does not have it. It has the
local-ring form, `Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add` in
`StacksFrontier/RingTheory/Flat/MiracleFlatness.lean`, and
`AlgebraicGeometry.flat_of_isCohenMacaulay` in
`StacksFrontier/AlgebraicGeometry/Groupoids/Slicing/MaximalSlice.lean`, which is not a substitute:
Cohen–Macaulayness of a morphism has stalk flatness as its first conjunct, so that lemma assumes
what step 3 has to produce. The two dimensions themselves are clause (1) and [Stacks, Tag 0B9H]
for the carried schemes.

So `Flat γ` is a **bare hypothesis** of `smooth_of_hasProjectiveSpaceFibres`. Carrying
step 3 instead as a named implication, "constancy of `dim_k H⁰(X, ℒ)` in degree `d` implies
`Flat γ`", with its antecedent proved from the degree bound, would be a pretence: the antecedent
does not mention `γ`, so under the hypotheses of the consuming theorem — which prove it — the
whole implication is *equivalent to `Flat γ`*, and the curve, the genus and the bound
`2g - 1 ≤ d` would decorate a hypothesis that says nothing about `γ_d`. The price of the honest
spelling is that what this file registers for the tag is the step from flatness to smoothness,
not the tag's assertion.

## What is carried, and why

Neither `Hilb^d_{X/k}` nor `Pic^d_{X/k}` is available as a scheme here: the first is the
representability of the Hilbert functor of points, [Stacks, Tag 0B97] — carried as a hypothesis
wherever it is used, e.g. by `AlgebraicGeometry.smoothOfRelativeDimension_of_represents` for
[Stacks, Tag 0B9H] — and the second is the representability of the Picard functor,
[Stacks, Tag 0B9Z], which the library does not have at all (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Picard/DegreeAtLeastGenus.lean`). So the two schemes and the
morphism `γ_d` of clause (4) are **carried**: they appear below as `H`, `P` and `γ : H ⟶ P`, as
the degree decomposition of clause (1) is carried in
`StacksFrontier/AlgebraicGeometry/GroupScheme/Subgroups/Clopen.lean` for clause (3). Nothing here
asserts that they exist.

Carried with them:

* `hfib : HasProjectiveSpaceFibres γ`, step 1 — the fibre of `γ_d` is a projective space over the
  residue field of its point. This is the identification the source itself leaves unproved, and it
  mentions neither `d` nor `g` nor the genus: the dimension of the projective space is
  existentially quantified, so the hypothesis is the degree-independent statement the source makes
  and not the dimension count of step 2. It is a genuine condition on `γ`, not a vacuous one: the
  isomorphism is required to commute with the two structure morphisms to `Spec κ(y)`, and the
  proof of step 4 consumes it. Its ingredients are present in the library — an effective
  Cartier divisor with `𝒪_X(D) ≅ ℒ` is a nonzero section of `ℒ` up to a scalar
  (`AlgebraicGeometry.invertibleSheafIsoZeroSchemeOfIsRegularSection` and
  `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero`), and `𝐏(V) = Proj(Sym V)`
  with its comparison to `ℙⁿ` is
  `AlgebraicGeometry.projectiveSpaceOfModule` / `AlgebraicGeometry.basisProjectiveSpaceIso` — but
  assembling them into a *scheme-theoretic* isomorphism of the fibre requires the Hilbert scheme,
  which is the carried representability.
* `[Flat γ]`, step 3, as above.
* `[LocallyOfFinitePresentation γ]`, the finite presentation of the Hilbert scheme over the
  Picard scheme, again a property of the carried schemes.

Nothing else is carried. In particular step 2 costs no hypotheses: [Stacks, Tag 0B90]
(`isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree`) gives
`H¹(X, ℒ) = 0` from `[IsAlgClosed k] [IsProper f] [IsCurve k f]` and the degree bound alone.

## The restriction on `k`, and on `X`

The tag's field is **separably closed**; the hypothesis of the dimension count below is
`IsAlgClosed k`. This is a restriction, and it comes from the library's Tag 0B90, whose statement
carries `[IsAlgClosed k]`: algebraic closedness is consumed there through the `k`-rationality of a
closed point, in the twisting-down step `AlgebraicGeometry.HasPointTwistDown` names. Weakening it
to `IsSepClosed k` means generalising
`StacksFrontier/AlgebraicGeometry/Curves/PrescribedLowCohomology.lean` and
`StacksFrontier/AlgebraicGeometry/Curves/LargeDegreeVanishing.lean` in place, which is not done here.
The restriction bears on step 2 alone; step 4, which is what carries the tag attribute, has no
hypothesis on `k` and none on `X`.

In the other direction the hypotheses on `X` are weaker than the tag's: `X` need not be smooth or
projective, only a curve over `k` — proper, of dimension at most one — with
`H⁰(X, 𝒪_X) = k`. That last is carried in the library's spelling
`IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)` exactly as in
`StacksFrontier/AlgebraicGeometry/Picard/DegreeAtLeastGenus.lean`, and is not a conclusion assumed:
for the tag's `X`, proper and geometrically integral, it is
`AlgebraicGeometry.isIso_globalSections_of_geometricallyIntegral`.

## Implementation notes

The degree is `AlgebraicGeometry.invertibleCurveDegree` ([Stacks, Tag 0AYR]) and the genus is
`AlgebraicGeometry.genus` ([Stacks, Tag 0BY7]). Invertibility is taken at the spelling
`X.presheaf X.ringCatSheaf.2`, which is the one `invertibleCurveDegree` uses, and is passed to Tag
0B90's `X.sheaf.obj X.ringCatSheaf.property` by definitional unfolding, as in
`StacksFrontier/AlgebraicGeometry/Picard/DegreeAtLeastGenus.lean`; this is why
`@invertibleCurveDegree` appears.

The Riemann-Roch rearrangement below and
`AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_invertibleCurveDegree_add_one` (Tag 0C6T,
part (1)) are two different rearrangements of one cited identity,
`AlgebraicGeometry.invertibleCurveDegree_eq_sub_of_isZero`: the latter is stated at genus zero and
obtains `H¹(X, ℒ) = 0` from the genus-zero vanishing, the former keeps the genus in the conclusion
and takes `H¹(X, ℒ) = 0` as input. Neither is an instance of the other.

The fibres are stated as `ℙⁿ` over the residue field rather than as `Proj(Sym(Γ(X, ℒ)^*))`: the
two agree by `AlgebraicGeometry.basisProjectiveSpaceIso` once a basis is chosen, and `ℙⁿ` avoids
carrying a vector space over a residue field through the statement. Smoothness of `ℙⁿ_S` over `S`
is [Stacks, Tag 0B2P], `AlgebraicGeometry.projectiveSpaceOver.smooth`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B90](https://stacks.math.columbia.edu/tag/0B90)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 0B9H](https://stacks.math.columbia.edu/tag/0B9H)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Riemann-Roch: the exact dimension of the space of sections -/

/-- **Riemann-Roch in the form `dim_k H⁰(X, ℒ) = deg(ℒ) + 1 - g`.** On a proper scheme of
dimension at most one over a field whose only global regular functions are the constants, an
invertible module with vanishing `H¹` has `dim_k H⁰(X, ℒ) = deg(ℒ) + 1 - g`.

The degree is `χ(ℒ) - χ(𝒪_X)`, which with `H^i = 0` for `i ≥ 2` reads
`(h⁰(ℒ) - h¹(ℒ)) - (1 - g)`; the hypothesis kills `h¹(ℒ)`. -/
theorem finrank_cohomologyOverField_zero_eq_add_one_sub_genus [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hone : IsZero (cohomologyOverField k f L 1)) :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) =
      @invertibleCurveDegree k _ X f _ hdim L hL + 1 - genus f := by
  have hdegeq := invertibleCurveDegree_eq_sub_of_isZero k f hdim L
    (isZero_cohomologyOverField_of_two_le' k f hdim L)
    (isZero_cohomologyOverField_of_two_le' k f hdim (SheafOfModules.unit X.ringCatSheaf))
  rw [finrank_cohomologyOverField_unit_zero_eq_one f,
    ← genus_eq_finrank_cohomologyOverField_unit_one' k f] at hdegeq
  have h1 : Module.finrank k (cohomologyOverField k f L 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero hone
    Module.finrank_zero_of_subsingleton
  rw [h1] at hdegeq
  omega

/-- **The dimension count of step 2 of the proof of clause (5) of [Stacks, Tag 0BA0]**: an
invertible module of degree at least `2g - 1` has `dim_k H⁰(X, ℒ) = deg(ℒ) + 1 - g`.

`H¹(X, ℒ) = 0` is [Stacks, Tag 0B90], stated as
`isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree` under no
hypotheses beyond `[IsAlgClosed k] [IsProper f] [IsCurve k f]` and the degree bound; Riemann-Roch
then gives the dimension. This is the only place the bound `2g - 1 ≤ deg(ℒ)` is used in the proof
of the tag's smoothness assertion. -/
theorem finrank_cohomologyOverField_zero_eq_add_one_sub_genus_of_le_invertibleCurveDegree
    [IsAlgClosed k] [IsProper f] [IsCurve k f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 2 * (genus f : ℤ) - 1 ≤ @invertibleCurveDegree k _ X f _ hdim L hL) :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) =
      @invertibleCurveDegree k _ X f _ hdim L hL + 1 - genus f :=
  have hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  finrank_cohomologyOverField_zero_eq_add_one_sub_genus k f hdim L
    (isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree
      k f L hL' hdeg)

/-! ### The carried fibre identification -/

/-- **Step 1 of the source's proof of the smoothness half of clause (5) of
[Stacks, Tag 0BA0]**: every fibre of `γ_d` is a projective space over the residue field of its
point.

The source identifies the fibre over the point corresponding to an invertible module `ℒ` with
`Proj(Sym(Γ(X, ℒ)^*))`, and omits the proof. The dimension of the projective space is
existentially quantified here, so this says only what the source says for every `d ≥ 0`, and
nothing about the dimension count that the degree bound supplies. -/
def HasProjectiveSpaceFibres {H P : Scheme.{u}} (γ : H ⟶ P) : Prop :=
  ∀ y : P, ∃ (n : ℕ) (α : γ.fiber y ≅ projectiveSpaceOverRing n (P.residueField y)),
    α.hom ≫ (projectiveSpaceOverRing n (P.residueField y) ↘ Spec (P.residueField y)) =
      γ.fiberToSpecResidueField y

/-! ### Tag 0BA0, clause (5): the step from flatness to smoothness -/

/-- **Step 4 of the source's proof of the smoothness half of clause (5) of [Stacks, Tag 0BA0]**:
a flat morphism, locally of finite presentation, whose fibres are projective spaces over their
residue fields, is smooth.

The fibres are projective spaces by `hfib`, hence smooth over their residue fields
([Stacks, Tag 0B2P]); a flat morphism, locally of finite presentation, with smooth fibres is
smooth ([Stacks, Tag 01V9]).

Applied to the Abel map `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` of clause (4) this is the last step of
the source's argument, but **the statement is general**: no curve, no genus and no degree bound
appear in it, and `Flat γ` is a hypothesis rather than a conclusion. Flatness of `γ_d` is the
source's step 3, Algebra, Lemma [Stacks, Tag 00R4], which this library has only for local rings
(`Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add`); see the module docstring. The
dimension count that step 3 consumes is proved above, as
`finrank_cohomologyOverField_zero_eq_add_one_sub_genus_of_le_invertibleCurveDegree`, but nothing
connects it to `Flat γ` without the scheme-level form of Tag 00R4.

This is a partial step towards [Stacks, Tag 0BA0], which is registered on its full statement. -/
theorem smooth_of_hasProjectiveSpaceFibres {H P : Scheme.{u}} (γ : H ⟶ P)
    [LocallyOfFinitePresentation γ] [Flat γ] (hfib : HasProjectiveSpaceFibres γ) :
    Smooth γ := by
  refine Smooth.of_smooth_fiberToSpecResidueField γ fun y => ?_
  obtain ⟨n, α, hα⟩ := hfib y
  rw [← hα]
  infer_instance

end AlgebraicGeometry

end
