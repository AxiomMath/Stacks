module

public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.Stages
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.CentralClaim
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.FibreFlatness
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.FlatLocalization
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.PrescribedResidueField
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.EssentiallySmoothFactorization
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.GlobalStage

/-!
# Inseparable residue fields

Let `k` be a field of characteristic `p > 0` and let `(Λ, 𝔪, K)` be an Artinian local
`k`-algebra with `dim_K H₁(L_{K/k}) < ∞`. Stacks 07FG asserts that `Λ` is a filtered colimit of
Artinian local `k`-algebras `A` which are essentially of finite type over `k`, over which `Λ` is
flat, and whose maximal ideal generates `𝔪`. Flatness forces each `A → Λ` to be injective, so the
filtered colimit is a *directed union of subalgebras of `Λ`*, and that is the form proved here;
the source says as much in the first line of its proof.

The approximating subalgebras are the *stages* `Ψ_σ(F[λ₁, …, λ_d])`, where `λ₁, …, λ_d` generate
`𝔪`, `σ : K → Λ` is a ring-theoretic section of the residue map and `k ⊆ F ⊆ K` is finitely
generated. The content of the tag is the *central claim* of its proof: `σ` and one such `F₀` can
be chosen so that the image of `k` in `Λ` already lies in `Ψ_σ(F₀[λ])`. That claim is where the
characteristic and the finiteness of `H₁(L_{K/k})` enter, and it is proved here.

The second half of the file assembles the ring-theoretic inputs of Stacks 07FH, the lemma which
consumes 07FG: for a Noetherian geometrically regular `k`-algebra `Λ`, a prime `𝔮`, an exponent
`n` and a finite subset `E` of `Λ_𝔮/𝔮^nΛ_𝔮`, there are `m` and `φ : k[y_1, …, y_m] → Λ` with
`𝔮Λ_𝔮 = 𝔭Λ_𝔮` for `𝔭 = φ^{-1}(𝔮)`, with `k[y]_𝔭 → Λ_𝔮` flat, and with the induced map
`k[y]_𝔭/𝔭^nk[y]_𝔭 → Λ_𝔮/𝔮^nΛ_𝔮` factoring through a local Artinian ring `D ⊇ E` by an
essentially smooth map followed by a flat one.

The development is split into the files
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField.Stages`,
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField.CentralClaim`,
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField.FibreFlatness`,
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField.FlatLocalization`,
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField.PrescribedResidueField`,
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField.EssentiallySmoothFactorization`,
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField.GlobalStage`.

## Main definitions

* `Stacks.Smoothing.coefficientStage`: for a ring-theoretic section `σ : K → Λ` of the residue
  map, a subfield `k ⊆ F ⊆ K` and elements `x₁, …, x_d` of `Λ`, the subring `Ψ_σ(F[x₁, …, x_d])`
  of `Λ`, that is, the image of the polynomial ring `F[X₁, …, X_d]` under the evaluation that
  uses `σ` on coefficients and sends `Xᵢ` to `xᵢ`. These are the approximating subalgebras.
* `Stacks.Smoothing.CoefficientSectionData`: the data produced by the central claim in the
  source's proof — a section `σ`, generators `λ₁, …, λ_d` of `𝔪`, and a finitely generated
  `k ⊆ F₀ ⊆ K` such that the image of `k` in `Λ` already lies in `Ψ_σ(F₀[λ₁, …, λ_d])`.
* `Stacks.Smoothing.primePowerQuotient`: the Artinian local ring `Λ_𝔮/𝔮^nΛ_𝔮` in which Stacks
  07FH works.

## Main results

* `Stacks.Smoothing.eval₂Hom_surjective_of_isSection`: `Ψ_σ : K[X₁, …, X_d] → Λ` is surjective
  as soon as `σ` is a section of the residue map, the `xᵢ` generate `𝔪` and `𝔪` is nilpotent.
* `Stacks.Smoothing.exists_directedOn_flat_essFiniteType`: Stacks 07FG. Under the source's own
  hypotheses the stages `Ψ_σ(F[λ])`, for `F` finitely generated over `k` and containing `F₀`,
  form a directed family of `k`-subalgebras of `Λ` which covers `Λ`, each of which is Artinian
  local and essentially of finite type over `k`, with `Λ` flat over it and with `𝔪_A Λ = 𝔪`.
  `Stacks.Smoothing.exists_directedOn_flat_essFiniteType_of_charP` is the same statement, under
  the name by which the second half of the file refers to it.
* `Stacks.Smoothing.nonempty_coefficientSectionData_of_finite_h1Cotangent`: the central claim of
  the source's proof, which produces the section `σ` and the finitely generated coefficient
  field `F₀` from the source's own assumptions — `char k = p > 0` and `dim_K H₁(L_{K/k}) < ∞`,
  with no finiteness whatever assumed of `K/k`.
* `Stacks.Smoothing.nonempty_coefficientSectionData`: that data, in the cheap case of a finitely
  generated residue field extension.
* `Stacks.Smoothing.exists_subalgebra_residueField_image_eq_of_charP`: Stacks 07FG with the
  residue field of the approximating subalgebra *prescribed*. The bare statement of the tag gives
  a directed family and nothing about which subfields of `K` occur as `A/𝔪_A`; the stages have
  residue field exactly their coefficient field `F`, and every finitely generated `F` above a
  bound depending on the prescribed finite subset occurs. This is what consumers of 07FG need in
  order to choose elements of a *given* subring of `Λ` whose differentials form a basis of
  `Ω_{A/𝔪_A ⁄ k}`.
* `Stacks.Smoothing.exists_coefficientStage_basis_kaehlerDifferential`: the λ-choice of Stacks
  07FH, the step the source's text asserts without argument. For a ring map `q : R → Λ` whose
  residues generate `K` as a fraction field, the section `σ` and the generators of `𝔪` can be
  chosen so that the coefficient field of the stage is `k(q(y)‾ : y ∈ Y)` for a finite `Y ⊆ R`
  containing any prescribed finite set and with `q(Y)` inside the stage; a basis of `Ω_{F/k}` is
  then given by differentials of residues of finitely many elements of `R` whose images lie in
  the stage.
* `Stacks.Smoothing.exists_coefficientStage_basis_kaehlerDifferential_primePowerQuotient`: the
  same in the setting of Stacks 07FH, `Λ_𝔮/𝔮^nΛ_𝔮` over a Noetherian `k`-algebra `Λ`, where the
  hypothesis on `q` holds automatically because `κ(𝔮)` is the fraction field of `Λ/𝔮`.
* `Stacks.Smoothing.exists_mvPolynomial_flat_localization`: Stacks 07FH, clause (1),
  unconditionally.
* `Stacks.Smoothing.exists_mvPolynomial_flat_localization_of_intermediateField`: clause (1) with
  the residue field of `𝔭` prescribed. For an intermediate field `k ⊆ F ⊆ κ(𝔮)` which is
  essentially of finite type over `k` and generated over `k` by residues of finitely many
  elements of `Λ`, the map `φ` can be chosen so that, in addition to all of clause (1), `κ(𝔭)`
  embeds in `F` compatibly with `k[y]_𝔭 → Λ_𝔮` and `F/κ(𝔭)` is finite separable. The hypothesis
  that `F` be generated by residues of `Λ` cannot be dropped — see the docstring for the
  non-example `Λ = k[x, y]`, `𝔮 = 0`, `F = k(x/y)` — and costs nothing in use, the subfields so
  generated being cofinal because `κ(𝔮)` is the fraction field of `Λ/𝔮`. This is the form of
  clause (1) that the joint clauses (2)+(3) need: the public clause (1),
  `exists_mvPolynomial_flat_localization`, is its specialization at `F = k`, where every variable
  maps into `𝔮` and `κ(𝔭) = k` exactly, which forces the residue extension to be separable over
  `k` and so cannot serve.
* `Stacks.Smoothing.exists_mvPolynomial_factorization_isEssentiallySmooth_flat`: Stacks 07FH,
  clause (2), unconditionally. No approximating subring is needed for this clause alone: clause
  (1) makes `u : k[y]_𝔭/𝔭^n → Λ̄` flat by base change, `u` is a local homomorphism of local
  rings, hence faithfully flat, hence injective, so `D = range u` is a local Artinian subring of
  `Λ̄` onto which `u` is an isomorphism, and `D → Λ̄` is flat.
* `Stacks.Smoothing.exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat`: Stacks 07FH,
  clauses (2) and (3) together, under the extra hypothesis that `κ(𝔮)` is a finitely generated
  field extension of `k` — which holds for every prime of a `k`-algebra of finite type. Under
  that hypothesis no approximation is needed at all: `k[y_1, …, y_m]_𝔭/𝔭^n → Λ_𝔮/𝔮^nΛ_𝔮` is
  itself essentially smooth, so `D = Λ_𝔮/𝔮^nΛ_𝔮` serves, and `E ⊆ D` is immediate. The joint
  clauses are what Stacks 07FT consumes, and they are where the difficulty is: `D` must both
  contain `E` and be essentially smooth over `k[y]_𝔭/𝔭^n`, and the two requirements pull against
  each other.
* `Stacks.Smoothing.exists_global_stage_primePowerQuotient`: **Brian Nugent's repair of the
  λ-choice of Stacks 07FH.** The approximating subalgebra `A ⊆ Λ_𝔮/𝔮^nΛ_𝔮` of Stacks 07FG can be
  built over a generating family of `𝔪_{Λ_𝔮/𝔮^nΛ_𝔮}` consisting of images of GLOBAL elements
  `μ_j ∈ 𝔮 ⊆ Λ`, with a residue field generated by residues of a finite set `S ⊆ Λ` of global
  elements whose images lie in `A`, and still containing any prescribed finite `E`. This is what
  the source's text asserts without argument and what fails for a general member of the directed
  family; the two counterexamples are in the implementation notes.
* `Stacks.Smoothing.exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat_of_charP`:
  Stacks 07FH, ALL THREE CLAUSES, in the generality of the tag — no hypothesis on `κ(𝔮)`. This
  is the lemma that Stacks 07FT consumes; `Stacks.Smoothing.hasArtinianApproximationData`, in
  `StacksFrontier/RingTheory/Smoothing/ArtinianApproximationGeneral.lean`, is 07FT itself.
* `Stacks.Smoothing.finite_and_isSeparable_of_formallySmooth_of_perfectRing` and
  `Stacks.Smoothing.not_formallySmooth_of_perfectRing_of_not_isIntegral`: the obstruction to the
  *adapted-section* strategy for the joint clauses. For `k ⊆ F ⊆ K` with `K` perfect of
  characteristic `p` and `F/k` finitely generated, `Algebra.FormallySmooth F K` forces `F/k` to
  be finite and separable; so no such `F` containing an element transcendental over `k` has `K/F`
  formally smooth, hence none has `K/F` separable (Lemma [stacks, 0322]). That strategy asks for
  a finitely generated `F` containing the `b`-coordinates of the prescribed `E` with `K/F`
  separable, and `dim_K H₁(L_{K/k}) < ∞` does not supply one: see the section
  "The separable coefficient field that the adapted-section route asks for" for the non-example,
  `k = 𝐅_p`, `K` the perfect closure of `𝐅_p(t)`, `Λ = K[x]`, `𝔮 = (x)`, `n = 2`, `E = {t}`,
  where `H₁(L_{K/k})` vanishes outright. Nugent's repair asks instead for `F'/κ(𝔭)` separable,
  which clause (1) over `F'` delivers, and never for separability of `κ(𝔮)/F'` or of
  `κ(𝔮)/κ(𝔭)`.

## Implementation notes

*The central claim.* The characteristic-`p` hypothesis and the finite dimensionality of
`H₁(L_{K/k})` are used in the source at exactly one place, the claim that some section `σ` and
some finitely generated `F₀` satisfy `i(k) ⊆ Ψ_σ(F₀[λ])`. It is proved in
`exists_section_mem_coefficientStage` by the source's induction on the nilpotency order `n` of
`𝔪`. The induction replaces `Λ` by `Λ/𝔪^{n-1}` and keeps the residue field fixed, so it is run
with the surjection onto the residue field as a *parameter* `π : Λ → K` rather than as
`IsLocalRing.residue`; `eval₂Hom_surjective_of_section` and `exists_fg_mem_stage` are stated that
way, and `eval₂Hom_surjective_of_isSection` and `exists_fg_mem_coefficientStage` are their special
cases at `π = residue Λ`. The existence of the section alone, for any `Λ` with nilpotent
maximal ideal in characteristic `p`, is Lemma [stacks, 09EZ]
(`IsLocalRing.exists_residueField_section_compatible`); what the claim adds is its compatibility
with a *finitely generated* coefficient field.

*The inductive step.* Write `I = 𝔪^{n-1}`, so that `𝔪 I = 0` and `I` is a `K`-vector space. Both
lifts the source takes — of the section `σ' : K → Λ/I` to `σ : K → Λ`, and of the induced map
`k → Ψ_{σ'}(F'[λ])` to a ring map `ρ : k → Ψ_σ(F'[λ])` — are instances of
`exists_ringHom_lift`: a field of characteristic `p` is formally smooth over `𝐅_p` by Lemma
[stacks, 0320], because `𝐅_p` is perfect. The difference `θ = i - ρ : k → I` is then a derivation
over `𝐙` (equivalently over `𝐅_p`: a `𝐙`-derivation is just an additive Leibniz map), and
`exists_derivation_sub_mem_span` corrects it by a derivation `D : K → I` so that what is left
takes values in the `k`-span of a *finite* subset of `I`. The source's `A = F[x]/(x)^n`, the
auxiliary ring on which the lifted `τ : k → A` is independent of `σ`, is not needed: the only fact
used about it is `eval₂_of_add`, that passing from `σ` to `σ + D` changes an evaluation at `λ` by
`D` of the constant term, since `D` takes values in `I` and `I 𝔪 = 0`. Finally the finitely many
correction values are absorbed into `F` by `exists_fg_subset_stage`, which replaces the source's
explicit expansion `f_j = Σ_E c_{j,E} λ^E` and the enlargement `F = F'(c_{j,E})`.

*The Jacobi–Zariski step.* Exactness of `H₁(L_{K/k}) → K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` at the middle
term (Lemma [stacks, 00S2], `Algebra.H1Cotangent.exact_δ_mapBaseChange`) exhibits the kernel of
the second map as the image of the first, hence as a finite-dimensional `K`-subspace. A finite
subset `J₀` of a chosen `k`-basis `{dy_j}` of `Ω_{k/𝐙}` therefore spans a `K`-subspace containing
that kernel, and subtracting from `θ` the `k`-linear map which agrees with it on `{dy_j}_{j ∈ J₀}`
and vanishes on the rest leaves a map that kills the kernel and so factors through `Ω_{K/𝐙}`,
after extending along a `K`-subspace inclusion. The source's four-term sequence is not needed:
only exactness at `K ⊗_k Ω_{k/𝐙}`, which does not require `H₁(L_{K/𝐙}) = 0`.

*Flatness.* The source argues that `ker Ψ_σ` is generated by finitely many polynomials which,
after enlarging `F`, have coefficients in `F`, so that `A = F[X]/(g) → K[X]/(g) = Λ` is flat by
base change along `F → K`. The route taken here is the same statement reorganized so that no
presentation of `Λ` has to be manipulated. `Λ` is a finite `K`-vector space — this is Lemma
[stacks, 07DT](1) applied to `σ`, whose composition with the residue map is the identity — so a
finite `K`-basis `b` of `Λ` can be fixed once and for all, and `F` enlarged so that `1`, the
`λᵢ` and the products `bᵢbⱼ` all have their `b`-coordinates in `F`. Then `Ψ_σ(F[λ])` is exactly
the `F`-span of `b` (`aeval_range_eq_span`), so `b` is simultaneously an `F`-basis of the stage
and a `K`-basis of `Λ`, and `free_of_basis_of_linearIndependent` turns that coincidence into an
`A`-basis of `Λ` indexed by an `F`-basis of `K`. Freeness, not merely flatness, comes out.

*Locality.* Each stage is local for the elementary reason that it surjects onto a field with
nilpotent kernel: the residue of an element of `Ψ_σ(F[λ])` lies in `F`, so the element is `σ` of
a unit of `F` plus a nilpotent unless its residue vanishes.

*Twisted scalars.* The section `σ` is in general not a `k`-algebra map — in the inseparable case
it cannot be chosen so, which is the whole difficulty of the tag. Accordingly `Λ` is given the
`K`-algebra structure `σ.toAlgebra`, for which there is **no** scalar tower `k → K → Λ`, and the
stages are subrings rather than `k`-subalgebras until the hypothesis
`CoefficientSectionData.range_algebraMap_mem` makes them `k`-subalgebras.

*The inputs of Stacks 07FH.* The lemma consuming 07FG needs, besides 07FG itself, four
ring-theoretic steps, all proved here and none of them in the source's list of citations.
`map_eq_and_flat_of_fibre` is the step at which the source passes from `k[y_1, …, y_t]` to
`k[y_1, …, y_m]`: Lemma [stacks, 07E6] delivers flatness of `Λ_𝔮` only over the localization of
the smaller polynomial ring, since it forces the number of variables to be `dim Ω_{F/k}`, while
the further variables adjoined for a regular system of parameters of `Λ_𝔮/𝔭'Λ_𝔮` have residue
zero. Flatness over the larger ring is recovered from `ringKrullDim_eq_add_of_flat` (the
dimension formula for a flat local homomorphism, read off going down), `height_le_add_of_span`
(Krull's height theorem through the fibre) and miracle flatness, Lemma [stacks, 00R4]; the ideal
identity `𝔭 = 𝔭'k[y] + (y_{t+1}, …, y_m)` that feeds them is `comap_eq_sup_span`.
`isEssentiallySmooth_of_finite_flat` is the source's closing step, from finite flat with finite
separable residue extension to essentially smooth: Lemma [stacks, 00U6] produces
`Algebra.IsEtaleAt` for the localization of the target at its own maximal ideal, and
`RingHom.IsEssentiallySmooth.comp_ringEquiv` carries the conclusion back.
`finite_and_isSeparable_of_subsingleton_kaehlerDifferential` is the source's appeal to Lemma
[stacks, 07E1] for `Ω_{F/κ(𝔭)} = 0 ⟹ F/κ(𝔭)` finite separable, obtained instead from
`Algebra.FormallyUnramified.iff_isSeparable`. `span_image_derivation_eq_top` and
`exists_basis_fin_range` make the choice of a basis of `Ω_{F/k}` among differentials of a
generating set of `F`.

*The λ-choice of Stacks 07FH is not justified by the source's text.* Having chosen `A` by 07FG,
with residue field `F ⊆ K = κ(𝔮)`, the source says: pick `λ_1, …, λ_t ∈ Λ` which map to elements
of `A` in `Λ̄` such that moreover the images of `dλ_1, …, dλ_t` form a basis of `Ω_{F/k}`. No
argument is given, and the order of the quantifiers in the text is wrong: `A` is fixed first and
never enlarged again, while for SOME members of the directed family no such `λ` exist, because
`F` is not claimed to be — and in general is not — generated by residues of `Λ`. Take
`Λ/𝔮 = k[x, y]`, so that `K = k(x, y)`, and `F = k(x/y)`: a nonconstant element of `k(x/y)` is
homogeneous of degree `0`, hence not a polynomial, so `F ∩ k[x, y] = k` and the differentials of
those residues of `Λ` which lie in `F` span `0 ≠ Ω_{F/k}`; and by
`exists_subalgebra_residueField_image_eq_of_charP` every finitely generated subfield of `K` above
a bound does occur as the residue field of such an `A`. That is the whole force of the
counterexample: it refutes the text, not the route, since nothing stops `A` from being chosen for
the purpose, and the two demands do have to be met together —
`A` must contain the images of the `λ`, which are read off `F = residue(A)`.
`exists_coefficientStage_basis_kaehlerDifferential` repairs it by choosing `A` for the purpose:
the coefficient field may be taken to be `k(Ȳ)` for a finite `Y ⊆ Λ` which contains any
prescribed finite set and all of whose images lie in the stage, and then `Ω_{k(Ȳ)/k}` is spanned
by the differentials of the residues of the elements of `Y`
(`span_derivation_eq_top_of_adjoin_eq`), so a basis is available among them. Two mechanisms do
the work: the subfields `k(Ȳ)` are cofinal among the finitely generated subfields of `K`,
because `K` is the fraction field of `Λ/𝔮` (`exists_finset_mem_adjoin_image`,
`exists_mul_residue_eq_residue_primePowerQuotient`); and the generating family of `𝔪` is part of
the data of a stage and may be enlarged by the elements `q(y) - σ(q(y)‾)` of `𝔪`
(`coefficientStage_le_append`), which puts `q(Y)` into the stage without enlarging the
coefficient field at all.

*The λ-choice without enlarging the generating family.* The repair
`exists_coefficientStage_adjoin_residue_image`
puts `q(Y)` into the stage by enlarging the generating family of `𝔪_Λ̄` with the elements
`q(y) - σ(q(y)‾)`. What that enlargement costs is a demand on the coefficient field, not
flatness: `exists_stage` proves flatness of `Λ̄` over a stage for an ARBITRARY family `x`
generating `𝔪_Λ̄`, the only hypothesis on it being `hrx`, that the `b`-coordinates of every
`x j` lie in `F`. So a badly chosen `F` breaks flatness, while the enlargement by itself does
not. (With `k = 𝐅_p`, `Λ̄ = k(v)[ε]/ε²`, `σ` the inclusion of `K = k(v)`, `F = k(v^p)` and the
family `ε, vε`, the stage is `F ⊕ (F ⊕ Fv)ε` of `F`-dimension `3`, over which freeness would
force `dim_F Λ̄ = 3p` instead of `2p`; but the `b`-coordinate of the extra generator `vε` is
`v ∉ k(v^p)`, so `hrx` fails for this `F`, and enlarging `F` to `k(v)` restores `hrx` and with
it flatness. Each enlargement of the generating family is thus paid for by an enlargement of
`F`, which is where the fixed-point problem of the λ-choice really sits.) The `p`-th-power route
dismissed in earlier drafts of this file avoids the enlargement altogether and does work, as far
as it goes. For `Q = p^j ≥ n` and any `w ∈ Λ`, Frobenius
gives `q(w^Q) = (σ(w̄) + μ)^Q = σ(w̄^Q) + μ^Q = σ(w̄^Q)` since `μ ∈ 𝔪` and `𝔪^n = 0`; so
`q(w^Q) ∈ σ(F)` lies in the stage, with its generating family untouched, as soon as `w̄^Q ∈ F`.
And `d(w̄^Q)` is zero in `Ω_{K/k}` but NOT in `Ω_{F/k}` — the module that matters — whenever
`w̄^Q` belongs to a `p`-basis of `F` over `k`: for `F = k(v^p)` the space `Ω_{F/k}` is spanned by
`d(v^p) ≠ 0`. So for any `z_1, …, z_s ∈ Λ` and `F = k(z̄_1^Q, …, z̄_s^Q)` the λ-choice is
available with `λ_i = z_i^Q`, over a stage that is a bona fide member of the directed family.
What this does NOT reach is a coefficient field containing a prescribed finite subset of `K`:
`k(z̄^Q) ⊆ k·K^Q ⊆ k·K^p`, and `K/k·K^p` is purely inseparable, so a stage whose residue field
is generated by `Q`-th powers cannot contain an element of `K ∖ k·K^p`. That is what clause (3)
needs — the coordinates of a prescribed `E ⊆ Λ̄` must lie in `F` — and it is why
`exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat` was conditional on a finitely
generated `κ(𝔮)` while clause (2) alone was not. Nugent's repair, recorded below, removes the
condition.

*The defect is about `Λ` versus `Λ_𝔮`, and there is a second counterexample.* The paragraph above
describes the λ-choice as asking for residues of `Λ` generating `F`. That is one half of it. The
sharper statement of what the source's text does not supply is this: the λ's are required to be
elements of the ORIGINAL ring `Λ`, while lifting an element of `A ⊆ Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮` produces an
element of `Λ_𝔮`, not of `Λ`. Nothing in the stated properties of `A` — Artinian local,
essentially of finite type over `k`, `Λ̄` flat over it, `𝔪_A Λ̄ = 𝔪_Λ̄` — forces a single element
of `Λ` other than those of `𝔮^n` to have its image in `A`. The counterexample of the preceding
paragraph refutes the differential-basis half; the following one, due to **Brian Nugent**,
refutes the regular-parameter half independently. Take `k = 𝐅_p`, `Λ = k[x, y]`, `𝔮 = (x)`,
`n = 2`, so `Λ_𝔮 = k[x, y]_{(x)}` is a discrete valuation ring and `Λ̄ = k(y)[x]/(x²)`, and take
`A = k[ε]/(ε²)` embedded by `ε ↦ x/y`, with `E = {x/y}`. Then `A` is local Artinian and of finite
type over `k`, `Λ̄ = A ⊗_k k(y)` so `A → Λ̄` is faithfully flat, `𝔪_A` generates `(x)Λ̄`, `E ⊆ A`
and the residue field is `F = k`, so the differential basis is empty and `t = 0`. But an element
of `Λ` lying in `𝔮` whose image lies in `A` has the form `f_0(y) + x f_1(y)` with
`f_0(y) + x f_1(y) ≡ c + d·(x/y)` in `Λ̄`, forcing `d = 0` and `f_1 = 0`, hence lies in `(x²)`;
so no regular parameter of `Λ_𝔮` can be found among the elements of `Λ` mapping into this `A`.
Both counterexamples refute the source's intermediate assertion about an arbitrary member of the
family, not the lemma.

*Nugent's repair of the λ-choice.* The two mechanisms recorded above pull against each other
because enlarging the generating family of `𝔪_Λ̄` is what puts `q(y)` into the stage, and that is
what costs flatness. **Brian Nugent**'s repair avoids enlarging the generating family at all, and
it closes the gap. Keep the generating family GLOBAL and fixed once and for all: `μ_1, …, μ_r` in
`𝔮 ⊆ Λ` with `q(μ)` generating `𝔪_Λ̄` (`exists_fin_span_eq_maximalIdeal_localization`), so that
`q(μ_j)` lies in every stage by `mem_coefficientStage_gen`. Enlarge `F` so that `E ⊆ A`
(`exists_fg_subset_coefficientStage`). Now clear denominators: pick field generators `f_1, …, f_s`
of `F/k` and write `σ(f_i) = q(a_i)/q(s_i)` with `a_i, s_i ∈ Λ` and `s_i ∉ 𝔮`, which is possible
because `K` is the fraction field of `Λ/𝔮`; let `α_i = s̄_i ∈ K` and let `P = p^j ≥ n`. Frobenius
gives `q(s_i)^P = σ(α_i^P)` exactly as in the `p`-th-power route, and therefore also
`q(a_i s_i^{P-1}) = σ(f_i) q(s_i)^P = σ(f_i α_i^P)`. Replace `F` by `F' = F(α_1^P, …, α_s^P)`.
Then the two GLOBAL elements `s_i^P` and `a_i s_i^{P-1}` of `Λ` have their images in `σ(F')`,
hence in the stage of `F'` over the UNCHANGED generating family `q(μ)` — so flatness, which
`exists_stage` grants for any family whose `b`-coordinates lie in the coefficient field, is not
disturbed, the `b`-coordinate condition being monotone in `F`. Their residues are `α_i^P` and
`f_i α_i^P`, whose ratio is `f_i`; so `k` adjoined to the residues of these `2s` global elements
is exactly `F'`, and `span_derivation_eq_top_of_adjoin_eq` makes `Ω_{F'/k}` spanned by their
differentials, from which `exists_basis_fin_range` extracts a basis. This is precisely what the
`p`-th-power route could not reach on its own: `p`-th powers alone generate only inside `k·K^P`,
and the new idea is to carry the PAIR `s_i^P`, `a_i s_i^{P-1}`, whose quotient recovers `f_i`,
so that the pair generates what neither member does. Two further remarks. First, a prescribed
finite `E ⊆ Λ̄` costs no more than a finite subset of `Λ`: every element of `Λ̄` is
`q(a) q(s)^{-1}` with `s ∉ 𝔮`, and a stage is local with `q(s)` outside its maximal ideal, so
`q(s)` is a unit there and `q(a), q(s) ∈ A` already gives `q(a)q(s)^{-1} ∈ A`. Second, the
regular parameters of the fibre `Λ_𝔮/𝔭'Λ_𝔮` demanded by clause (1) can be taken among the global
`μ_j`: their images generate the fibre's maximal ideal, and a minimal generating family may be
extracted as a SUBFAMILY, by Nakayama in the fibre, which keeps both globality and the dimension
count that `map_eq_and_flat_of_fibre` consumes. This repair is formalized in
`exists_global_stage_primePowerQuotient`, and with it the three clauses of Stacks 07FH in the
generality of the tag
(`exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat_of_charP`) and Stacks 07FT
(`Stacks.Smoothing.hasArtinianApproximationData`, in
`StacksFrontier/RingTheory/Smoothing/ArtinianApproximationGeneral.lean`).

## References

* [Stacks Project, Tag 07FG](https://stacks.math.columbia.edu/tag/07FG)
* [Stacks Project, Tag 07FH](https://stacks.math.columbia.edu/tag/07FH)
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 00U6](https://stacks.math.columbia.edu/tag/00U6)
* [Stacks Project, Tag 0320](https://stacks.math.columbia.edu/tag/0320)
* [Stacks Project, Tag 0322](https://stacks.math.columbia.edu/tag/0322)
* [Stacks Project, Tag 07DT](https://stacks.math.columbia.edu/tag/07DT)
* [Stacks Project, Tag 07E1](https://stacks.math.columbia.edu/tag/07E1)
* [Stacks Project, Tag 07E6](https://stacks.math.columbia.edu/tag/07E6)
* [Stacks Project, Tag 09EZ](https://stacks.math.columbia.edu/tag/09EZ)
-/
