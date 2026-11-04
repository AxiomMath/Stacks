module

public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.RelativelyPerfect.FlatComplex
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DiagonalModelHom
public import StacksFrontier.RingTheory.Dualizing.RelativeCoprojections

/-!
# Uniqueness of relative dualizing complexes, through the tensor--Hom diagonal

**[stacks 0E2D] itself is proved, with nothing carried, as
`Dualizing.IsRelativeDualizingComplex.nonempty_iso` in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensor`,** by an argument that forms no
tensor--Hom diagonal. This file records the source's route and the hypothesis that route carries.

Let `R → A` be a flat ring map of finite presentation, put `B = A ⊗[R] A` and write `Δ : B → A`
for the multiplication map and `p₁, p₂ : A → B` for the two coprojections. A relative dualizing
complex is an `R`-perfect object `K` of `D(A)` with `RHom_B(A, K ⊗ᴸ_A B) ≅ A`.

This file carries out the comparison argument that two relative dualizing complexes are
isomorphic. Writing `K₁` and `L₁` for the derived base changes of `K` and `L` along the left
coprojection and `A_B` for the diagonal — that is, `A` read in `D(B)` by restriction of scalars
along `Δ` — the tensor--Hom diagonal of [stacks 0BYN] at `(L₁, K₁)` and at `(K₁, L₁)` gives

`L₁ ⊗ᴸ_B A_B ≅ RHom_B(A_B, L₁ ⊗ᴸ_B K₁)`  and  `K₁ ⊗ᴸ_B A_B ≅ RHom_B(A_B, K₁ ⊗ᴸ_B L₁)`,

once the defining condition of a relative dualizing complex has been read as
`RHom_B(A_B, K₁) ≅ A_B` and `RHom_B(A_B, L₁) ≅ A_B`. The symmetry of the derived tensor product
identifies the two right-hand sides, and restriction of scalars along the left coprojection
carries `X₁ ⊗ᴸ_B A_B` back to `X`. So `K ≅ L`.

## The hypothesis that is carried, and why

The source deduces the two displayed isomorphisms from [stacks 0ATK] (3), whose hypotheses are
pseudo-coherence of the internal-Hom source, boundedness below of its target, and a lower bound
on the Tor amplitude of the tensor factor. **No invertibility criterion the library has applies
here**, and the obstruction is not one of generality: a single witness defeats all of them. Take
`R = k` a field, `A = k[x, y]/(x, y)²` and `K = L = Hom_k(A, k)`. Then `R → A` is flat of finite
presentation and `K` is a relative dualizing complex: relative perfectness is automatic over a
field, and `K ⊗ᴸ_A B ≅ Hom_k(A, A)` is the coextension of scalars of `A` along the *other*
coprojection, whose derived Hom from the diagonal is `RHom_A(A, A) = A` by adjunction, because
the restriction of the diagonal along a coprojection is `A` itself. With `B = A ⊗_k A` a
`9`-dimensional Artinian local algebra:

* the diagonal is not perfect over `B`, which kills [stacks 0ATK] (1): over an Artinian local
  ring a finite module of finite projective dimension is free, and `dim_k A = 3` is not a
  multiple of `dim_k B = 9`;
* `K ⊗ᴸ_A B` has no lower bound on its Tor amplitude over `B`, which kills both (2) and (3): the
  coprojection is flat, so tensoring with the residue field of `B` gives `K ⊗ᴸ_A k`, and
  `K = Hom_k(A, k)` has two generators and length three, hence is not free over the Artinian
  local `A`, hence has infinite projective dimension and `Tor_i^A(K, k) ≠ 0` for every `i`;
* that same bound is what the library's fourth criterion,
  `Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat`, derives from
  a tensor factor presented as the base change of a bounded-below K-flat complex. It asks the
  base change of `K` along a coprojection to come from a complex that is K-flat over `A`, which
  for `K = Hom_k(A, k)` it does not; and since its conclusion implies the bound just shown to
  fail, no reformulation of that criterion can apply either.

Adding a flatness or regularity hypothesis to the tag would not be the tag.

**At that witness `hdiag` is not merely unavailable: it is false.**
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation` computes both sides of the
tensor--Hom diagonal there. Derived Hom from the diagonal into a left base change `X₁` is
`RHom_A(X^∨, A)` for `X^∨ = Hom_k(X, k)`, so with `K = L = ω = Hom_k(A, k)` the Hom target
`ω₁ ⊗ᴸ_B ω₁ = (ω ⊗ᴸ_A ω)₁` is carried to the bidual `RHom_A(RHom_A(ω, A), A)`, whose
degree-zero cohomology is `Hom_A(Hom_A(ω, A), A) = Hom_A(k⁴, A) = (soc A)⁴ = m⁴` of dimension
`8`, while the left-hand side is `ω₁ ⊗ᴸ_B A_B ≅ ω` of dimension `3`. So the search above for a
fifth criterion is closed, and so is the reduction of `hdiag` to the one chain-level comparison
isomorphism isolated below: in the left/left configuration no proof of it can exist. The
*mixed* configuration the source uses survives that computation — see the section "Why both
base changes are taken along the left coprojection" below, and the documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`, which records that at the same
witness both sides of the mixed diagonal are `ω`.

The statement of [stacks 0E2D] is nevertheless true. What is proved here is therefore the
implication that the source's argument supports: invertibility of the two tensor--Hom diagonals
is carried as the explicit hypothesis `hdiag`, and everything else — reading the defining
condition in the internal-Hom vocabulary, the chain of isomorphisms, the symmetry, and the
descent from `D(B)` to `D(A)` along a coprojection — is proved. The docstring of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex` names what is carried. Two cases in which
nothing is carried are recorded below: the diagonal perfect over `B`, which is part (1) of
[stacks 0ATK] and is the situation of a smooth `R → A`, where the diagonal is a regular
immersion; and both base changes perfect over `B`, which is part (2).

**None of this is a defect in [stacks 0E2D].** The statement is true; what fails is the source's
*proof* of it, at the one step where it cites [stacks 0ATK] (3). Everything the source does
around that step is carried out below, and the single missing input is isolated next.

## What would discharge `hdiag`, and where the argument stops

The chain-level half is available and costs nothing. The tensor--Hom comparison
`Stacks.HomComplex.TensorHomComparison.theta` is an isomorphism of complexes as soon as the
tensor factor and the internal-Hom target are bounded below and the internal-Hom source is a
bounded-above complex of finite free modules, with no flatness and no Tor amplitude anywhere:
that is `Stacks.DerivedTensorHomDiagonal.isIso_theta_of_boundedBelow`, and its hypotheses hold
here, because `Dualizing.isPseudoCoherent_diagonal` resolves the diagonal by finite free
`B`-modules and both relative dualizing complexes are bounded, being `R`-perfect. The same
conclusion is available from the other side, from the tensor factor being a bounded complex of
finitely presented modules, since tensoring with a module commutes with arbitrary products
exactly when the module is finitely presented (`TensorProduct.piRightOfFinitePresentation`), and
`PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation` provides exactly
such a representative.

What is missing is the passage from that chain-level isomorphism to the derived diagonal. The
bridge `Stacks.DerivedTensorHomDiagonal.isIso_diagonal_of_projective_quasiIso_theta` asks the
tensor factor to be K-flat, for one reason only: the two chain-level tensor products must compute
the derived ones. In the mixed configuration — tensor factor based changed along one
coprojection, internal-Hom target along the other — one of the two is free:
`(P_K ⊗_R A) ⊗_B (A ⊗_R P_L)` is `P_K ⊗_R P_L`, which computes the derived tensor product
because a bounded complex with terms flat over `R` is K-flat over `R`. The other is the
obstruction, and it is one isomorphism:

> for `C` the chosen representative of the tensor factor and `H = Hom_B(N, F)` the Hom complex
> out of the finite free resolution `N` of the diagonal, the canonical map
> `C ⊗ᴸ_B H ⟶ C ⊗_B H` must be invertible.

K-flatness cannot supply it on either side. `C` is not K-flat over `B` — that is the content of
the witness. And `H`, whose restriction along the opposite coprojection does have flat terms, is
bounded *below* and unbounded *above*, while [stacks 064K]
(`CochainComplex.KFlat.kFlat_of_flat`) makes a complex of flat modules K-flat only when it is
bounded *above*; for bounded-below complexes of flat modules the conclusion is false in general,
and the `k^{(ℕ)}` against `k^ℕ` discrepancy recorded in
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat` is exactly this
failure.

That obligation can nevertheless be moved off `B` and onto `A`, which is as far as it has been
reduced. In the mixed configuration the tensor factor is `C = B ⊗ᴸ_A P_L` for the coprojection it
is based changed along, and `B` is flat over `A` along that coprojection, so the chain-level
projection formula `baseChangeTensorIso` of [stacks 06Y1] turns `C ⊗ᴸ_B H ⟶ C ⊗_B H` into

> `P_L ⊗ᴸ_A G ⟶ P_L ⊗_A G`,  where `G` is `H` restricted along the opposite coprojection,

and about `G` three things are known. Its terms are **flat over `A`**: each term of
`H = Hom_B(N, F)` is a finite product of finite direct sums of terms of `F = P_K ⊗_R B`, the
product being finite in each degree because `N` is bounded above and `F` bounded, and the
restriction of a term of `F` along the opposite coprojection is `(P_K)^j ⊗_R A`, flat over `A`
because `(P_K)^j` is flat over `R`. It is **bounded below**, again because `N` is bounded above
and `F` bounded. And its **cohomology is `A` in a single degree**, because `H` is
quasi-isomorphic to the diagonal by the defining condition of [stacks 0E2C] and restriction of
scalars is exact. So what is left is exactly:

> a bounded-below complex of flat `A`-modules whose cohomology is `A`, concentrated in one
> degree, computes the derived tensor product against a bounded complex.

The cohomological hypothesis in that statement is not decoration, and this is what sharpens the
appeal to [stacks 064K] above: termwise flatness over `A` *is* available here, so what fails is
not flatness but the passage from flat terms to K-flatness, and no statement about bounded-below
complexes of flat modules alone can serve. For `A = k[x]/(x²)` the complex
`A --x--> A --x--> ⋯` in degrees `≥ 0` has free terms and is bounded below, yet
`G ⊗_A k` has `k` in every degree while `G ⊗ᴸ_A k` is `k ⊗ᴸ_A k`, concentrated in degrees `≤ 0`;
that complex is `Hom_A(N, A)` for `N` the standard resolution of `k`, so its cohomology is `k`
rather than a flat module, and it is only the concentration hypothesis that excludes it.

Two further routes to the same step fail, and for one reason. A dévissage replacing the
pseudo-coherent diagonal by its perfect brutal truncations, where the diagonal is invertible by
[stacks 0ATK] (1), does not repair it: the comparison of the truncations is an isomorphism only
in a range of degrees bounded above, whereas a tensor factor of infinite Tor dimension over `B` —
which `K ⊗ᴸ_A B` is — makes each cohomology degree of the left-hand side depend on all higher
degrees of the internal-Hom object. The dual dévissage, replacing the *tensor factor* `L` by the
perfect subcomplexes `σ^{≥-n}P_L` of a bounded-above finite free resolution, for each of which
[stacks 0ATK] (2) applies outright, fails for the same reason read in the other direction: the
cones `σ^{≥-n}P_L → P_L` are cohomologically bounded *above*, by `-n`, and derived tensoring
lowers cohomological degrees rather than raising them, so the cones do not vanish in any fixed
range of degrees and letting `n` grow gains nothing.

The chain-level half of this reduction is no longer an assertion: it is proved, in the mixed
configuration where alone it can be used, as `Dualizing.exists_isIso_theta_mixed` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed`, whose module documentation carries
the sharpened account of what is left — three pieces rather than one, and the last of them a
named ring-theoretic condition which is not a theorem over every ring.

Two further routes are closed, and recorded here so that they are not retried.

*The evaluation map of the tensor--Hom adjunction does not redistribute the content.*
`StacksFrontier.RingTheory.Dualizing.RelativeBiduality` settles when the evaluation map
`RHom_A(ω, K) ⊗ᴸ_A ω ⟶ K` is invertible, and the answer closes that route twice over: invertible
for every `R`-perfect `K` forces `ω` to be tensor-invertible, i.e. `R → A` Gorenstein, which the
witness above refutes; and the conversion step
`Dualizing.nonempty_iso_of_isIso_evaluation`, which does hold, needs `RHom_A(ω, K) ≅ A` together
with invertibility at `K`, neither of which the defining condition of [stacks 0E2C] supplies —
that condition is about the base change of one complex, in `D(B)`.

*[stacks 0E2G] is downstream of this tag, not upstream.* The endomorphism statement
`A = RHom_A(K, K)` would supply the evaluation map at `K = ω`
(`Dualizing.isIso_evaluation_self_of_isIso_derivedHomothety`), but the source proves
[stacks 0E2G] from [stacks 0E2D]: once in the reduction to a Noetherian base, and once in the
Noetherian case, where [stacks 0E2D] is what identifies the given complex with `φ^!(R)` before
[stacks 0BZW] (1)(c) is applied to it. So the chain
[stacks 0BZW] (1)(c) → [stacks 0E2G] → [stacks 0E2D] is circular, and (1)(c) — available as
`Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isDualizingComplex` for a
presentation whose polynomial algebra is its own dualizing complex — does not bear on this tag
by itself.

Conversely, [stacks 0E2G] is not reachable from the comparison isomorphism this tag needs: the
module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeEndomorphisms` records that
feeding it into the two Hom computations across the diagonal,
`Dualizing.diagonalExtensionHomEquiv` and
`Dualizing.homDiagonalObjectEquivOfIsRelativeDualizingComplex`, returns
`End_{D(A)}(K) ≅ End_{D(A)}(K)`. So the two tags do not share one missing input; this one is the
weaker of the two.

So the missing prerequisite is not a further invertibility criterion for [stacks 0BYN]. Of the
remaining possibilities — that one comparison isomorphism, the Tor-amplitude bound over `B` that
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude` consumes, the mixed
configuration, and a route to [stacks 0E2D] that does not pass through [stacks 0BYN] at all —
the first two are now closed, both being stronger than the left/left `hdiag` that
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation` refutes. The last two remain. For
the fourth: the defining condition says
`Δ^!(K ⊗ᴸ_A B) ≅ A`, and what the comparison is being asked to prove is that this forces
`K ⊗ᴸ_A B ≅ p₂^!(A)`, which by `Dualizing.PolynomialPresentation`'s diagonal computation is the
base change of the upper-shriek relative dualizing complex; `K ≅ ω^•_{A/R} ≅ L` would then follow
by restriction along the multiplication map.

**The fourth is now open, and it is the one to pursue: the reduction above is an artefact of
this model, not of the tag.** `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality`
records a route that never forms the tensor--Hom diagonal and never asks for a K-flat
representative of a base change. Write `T(X) = Δ^!(p₁^*X)`, so that the defining condition reads
`T(K) ≅ A`. Then `T` commutes with derived Hom out of a pseudo-coherent object,

> `T(RHom_A(M, N)) ≅ RHom_A(M, T(N))` for `M` pseudo-coherent and `N` bounded below,

by flat base change for derived Hom along the flat coprojection ([stacks 0A6A], whose third case
is exactly these hypotheses: `Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange`),
the currying isomorphism of [stacks 0A65], the projection formula, and the adjunction
`Δ_* ⊣ Δ^!` of [stacks 0A70] — four adjunctions and no invertibility criterion. Taking `ω` to be
a relative dualizing complex which is also a dualizing complex for `A` (which `ω^•_{A/R}` is
whenever `R` is regular Noetherian of finite dimension, in particular whenever `R` is a field,
by [stacks 0BZL]), biduality writes any other `K` as the `ω`-dual of `P = RHom_A(K, ω)` and turns
`T(K) ≅ A` into `RHom_A(P, A) ≅ A`; `Dualizing.nonempty_iso_of_dual_iso_one` then converts
`P ≅ A` into `K ≅ ω`. What is left over is
`RHom_A(P, A) ≅ A ⟹ P ≅ A` for `P` with bounded coherent cohomology; **no complex of flat
modules and no acyclicity condition on the ring appears anywhere in that route**, and both inputs
the library used to lack are now proved outright. The projection formula
`A_B ⊗ᴸ_B p₁^*M ≅ Δ_*M` in `D(B)` is
`Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormula`, of which the `p₁`-restricted
`Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso` below is a
consequence, and the whole of the `D(B)` half — Step 1 — is
`Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction`.

**The implication left over is not reachable by the degree count that route proposes for it, and
that is now a matter of record rather than of effort.** The degree count — the extremal-degree
Künneth step `StacksDraft.ExtremalDegrees.extremalDegrees`, whose hypotheses at `P ⊗ᴸ_A -` the
dévissage of `StacksFrontier.Homology.Tor.ResidueDevissage` discharges — reads the extremal
nonvanishing degrees of cohomological windows it is **given**, and never produces one. It
therefore needs `ω ⊗ᴸ_A κ(m)` and `P ⊗ᴸ_A κ(m)` to be bounded *below*, which for a
pseudo-coherent factor is finite Tor dimension at `m`; by [stacks 068V] that is of the same
strength as perfectness of the factor
(`Dualizing.isPerfect_of_fibre_concentrated` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`), and with `ω` and `P` both
perfect `K ≅ RHom_A(P, ω)` is perfect as well, so that this tag is already
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange`. At the witness
above the bound is false for the same reason the Tor-amplitude route of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` fails there: `Hom_k(A, k)` is not free
over the Artinian local `A`, so it has infinite projective dimension and `Tor_i(Hom_k(A, k), k)`
is nonzero for every `i`. Everything else in the local computation is proved and assembled in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`, which also records what a
*one-sided* computation would need instead.

## Why both base changes are taken along the left coprojection

The source forms `K₁ = K ⊗ᴸ_A B` along the left coprojection but `L₂ = B ⊗ᴸ_A L` along the right
one, so that `K₁ ⊗ᴸ_B L₂` is `K ⊗ᴸ_R L` and the Tor amplitude of the tensor factor can be read
over `R`. That reading of [stacks 0ATK] (3) is exactly what fails — Tor amplitude over `R` is not
Tor amplitude over `B`. With the diagonal's invertibility carried as a hypothesis the choice is
immaterial *for the proof*, and both base changes are taken along the left coprojection below,
which is the form the definition of a relative dualizing complex is written in and keeps the
descent on one coprojection.

**It is not immaterial for the hypothesis, and that is now settled.** In the left/left
configuration `hdiag` is false at the witness above, by the computation recorded in
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`; in the mixed configuration both
sides of the diagonal are `ω` at that same witness, because `p₁^*K ⊗ᴸ_B p₂^*L` is `K ⊗ᴸ_R L`,
which at `K = L = ω` is the relative dualizing complex of `R → B`, so that the assertion becomes
`Δ^!(ω_{B/R}) ≅ ω_{A/R}` rather than `Δ^!(p₁^*(ω ⊗ᴸ_A ω)) ≅ ω`. Restating this tag in the mixed
configuration is therefore the repair, and it is
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed` in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed`. It needs neither the cross descent
`restrict_{p₁}(A_B ⊗ᴸ_B p₂^*L) ≅ L` nor monoidality of restriction along the flip of `B`: the
two sides are brought down to `D(A)` along *different* coprojections, each by its own matched
descent, which is possible because `Δ^!(p₁^*K ⊗ᴸ_B p₂^*L)` does not remember the section of `Δ`
used to reach it. Its hypothesis is still carried, and that is where a proof should be sought.

The mixed choice is nevertheless the right one for any *proof* of the hypothesis, and the
reason is not the Tor amplitude: it is that `(K ⊗ᴸ_A B) ⊗ᴸ_B (B ⊗ᴸ_A L)` is `K ⊗ᴸ_R L`, which a
bounded representative of `K` with terms flat over `R` computes on chains, whereas with both base
changes along one coprojection no representative computes it. The descent costs nothing there
either, contrary to what this file assumed before: `X₁ ⊗ᴸ_B A_B` is the restriction along the
multiplication map of `A ⊗ᴸ_B X₁`, for a base change `X₁` along *either* coprojection, so both
sides come down to `D(A)` along one and the same coprojection, and
`Dualizing.diagonalDerivedExtensionRetractionIso` and
`Dualizing.rightCoprojectionRetractionIso` identify the results with `K` and with `L`. The
symmetry of the defining condition in the two coprojections, which the mixed form needs, is
`Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight`.

## Main definitions

* `Dualizing.diagonalObject` — the diagonal `A`, read as an object of `D(A ⊗[R] A)` by
  restriction of scalars along the multiplication map.
* `Dualizing.restrictScalarsIncludeLeftTargetAsModuleIso`,
  `Dualizing.singleRestrictScalarsIncludeLeftUnitIso` — the diagonal, restricted along the left
  coprojection, is the tensor unit, as a module and as a complex.

## Main results

* `Dualizing.modelHom_diagonalObject_iso_of_derivedHom` — the defining condition of a relative
  dualizing complex, restated for the internal-Hom bifunctor of [stacks 0A63] in which the
  tensor--Hom diagonal of [stacks 0BYN] is stated.
* `Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso` — **the descent.**
  Derived tensoring the derived base change of `X` along the left coprojection with the
  diagonal, and then restricting scalars along the left coprojection, returns `X`.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex` — **[stacks 0E2D]**, with the
  invertibility of the two tensor--Hom diagonals carried as the hypothesis `hdiag`.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject`,
  `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange` —
  **[stacks 0E2D] with nothing carried** when the diagonal, respectively each of the two derived
  base changes, is a perfect object of `D(B)`: parts (1) and (2) of [stacks 0ATK] then supply
  `hdiag`.
* `Dualizing.exists_isGE_diagonalDerivedExtension_of_isRelativeDualizingComplex` — the derived
  base change of a relative dualizing complex along a coprojection is cohomologically bounded
  below.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude` — **[stacks 0E2D] with
  nothing carried** when each derived base change has Tor amplitude bounded below over `B`, which
  is part (3) of [stacks 0ATK] and is the hypothesis the source's own proof needs. This is the
  sharpest form of the implication the source supports, and it strictly weakens the hypothesis of
  the perfect-base-change case; the bound is read over `B`, which is exactly where it fails.

For a route to this tag that does not pass through [stacks 0BYN] at all see
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality`; its `D(B)` half is a theorem
(`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction`) and its local
computation is assembled in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`, whose documentation
records the one obligation that remains — a finite Tor-dimension bound on the fibres, of the same
strength as the perfectness this file already discharges.

## Implementation notes

The condition defining a relative dualizing complex is stated with `Dualizing.derivedHom`, the
derived coextension of scalars of [stacks 0A70], which lands in `D(A)`, whereas the tensor--Hom
diagonal is stated for the internal-Hom bifunctor of [stacks 0A63], which stays in `D(B)`. The
two are related by `Dualizing.nonempty_modelHom_iso_iff`, and that is the only place the two
vocabularies meet.

The descent is proved on representatives: a K-flat representative `P` of `X` over `A` has a base
change along the coprojection which is K-flat over `B` by [stacks 06Y1], so it computes both the
derived base change and the derived tensor product, and the chain-level projection formula
`baseChangeTensorIso` of [stacks 06Y1] identifies the restriction of
`A_B ⊗_B (B ⊗_A P)` with `(restriction of A_B) ⊗_A P`. The restriction of the diagonal along a
coprojection is the tensor unit because each coprojection is a section of the multiplication
map, which is `Dualizing.lmul'_comp_includeLeftRingHom`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

/-- The diagonal: the ring `A`, placed in cohomological degree zero and read as an object of
`D(A ⊗[R] A)` by restriction of scalars along the multiplication map `A ⊗[R] A → A`. -/
def diagonalObject (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))

/-- **The defining condition of a relative dualizing complex, in the internal-Hom vocabulary.**
If derived Hom from the diagonal into `X`, taken as the derived coextension of scalars of
[stacks 0A70], is `A`, then the internal derived Hom of [stacks 0A63] from the diagonal into `X`
is the diagonal. This is the form the tensor--Hom diagonal of [stacks 0BYN] consumes. -/
theorem modelHom_diagonalObject_iso_of_derivedHom (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (X : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)))
    (hX : Nonempty
      ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj X ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :
    Nonempty
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
          (Opposite.op (diagonalObject R A), X) ≅ diagonalObject R A) :=
  (nonempty_modelHom_iso_iff.{u}
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom X
      (diagonalObject R A)).2
    ⟨(ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R :
        A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.mapIso hX.some⟩

/-- Restriction of scalars along the left coprojection carries the diagonal, read on complexes,
to the tensor unit: the left coprojection is a section of the multiplication map, so the module
`A` with `A ⊗[R] A` acting through multiplication becomes `A` acting on itself. -/
def restrictScalarsIncludeLeftTargetAsModuleIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj
      (targetAsModule.{u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom) ≅
      ModuleCat.of A A :=
  (ModuleCat.restrictScalarsComp'App.{u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (RingHom.id A)
      (lmul'_comp_includeLeftRingHom R A).symm
      (ModuleCat.of A (ULift.{u} A))).symm ≪≫
    ModuleCat.restrictScalarsId'App.{u} (RingHom.id A) rfl (ModuleCat.of A (ULift.{u} A)) ≪≫
    (ULift.moduleEquiv.{u, u, u} (R := A) (M := A)).toModuleIso

/-- The diagonal, read on complexes and restricted along the left coprojection, is the tensor
unit of the monoidal category of cochain complexes of `A`-modules. -/
def singleRestrictScalarsIncludeLeftUnitIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    (CochainComplex.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
        (targetAsModule.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom)) ≅
      𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A))
      (ComplexShape.up ℤ) 0).app _ ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (restrictScalarsIncludeLeftTargetAsModuleIso R A)

/-- **The descent from `D(A ⊗[R] A)` to `D(A)`.** Derived tensoring the derived base change of
`X` along the left coprojection with the diagonal, and then restricting scalars along the left
coprojection, returns `X`.

This is the final step of the uniqueness argument: the chain of isomorphisms produced by the
tensor--Hom diagonals compares `L₁ ⊗ᴸ_B A_B` with `K₁ ⊗ᴸ_B A_B`, and this is what turns such a
comparison into an isomorphism in `D(A)`. -/
theorem nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (X : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeLeftRingHom :
            A →+* A ⊗[R] A)).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
          (diagonalObject R A, (diagonalDerivedExtension R A).obj X)) ≅ X) := by
  classical
  obtain ⟨P, hP, -, ⟨eP⟩⟩ := StacksDraft.Perfect.exists_kFlat_representative.{u, u} X
  set p₁ : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom with hp₁
  set Δ : A ⊗[R] A →+* A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom with hΔ
  -- the base change of `P` along the left coprojection is K-flat over `A ⊗[R] A`
  have hEP : ((CochainComplex.extendScalars p₁).obj P).KFlat := kFlat_baseChange p₁ P hP
  -- it computes the derived base change
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} p₁
  have hcomp : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  let eE : (diagonalDerivedExtension R A).obj X ≅
      DerivedCategory.Q.obj ((CochainComplex.extendScalars p₁).obj P) :=
    ((diagonalDerivedExtensionIsoTotalDerived R A).app X).symm ≪≫
      D.functor.mapIso eP ≪≫ @asIso _ _ _ _ (D.comparison.app P) hcomp
  -- the diagonal, read on complexes
  let eA : diagonalObject R A ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
          (targetAsModule.{u, u} Δ)) :=
    sourceSingleRestrictScalarsIsoQ.{u} Δ
  refine ⟨(ModuleCat.restrictScalars.{u} p₁).mapDerivedCategory.mapIso
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).mapIso
        (show (diagonalObject R A, (diagonalDerivedExtension R A).obj X) ≅
            (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
                (targetAsModule.{u, u} Δ)),
              DerivedCategory.Q.obj ((CochainComplex.extendScalars p₁).obj P)) from
          (eA.prod eE)) ≪≫
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction
            (A ⊗[R] A)).tensorIso _ _ hEP) ≪≫
    (ModuleCat.restrictScalars.{u} p₁).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      (baseChangeTensorIso p₁ P
          ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
            (targetAsModule.{u, u} Δ)) ≪≫
        (MonoidalCategory.tensorRight P).mapIso
          (singleRestrictScalarsIncludeLeftUnitIso R A) ≪≫
        λ_ P) ≪≫ eP.symm⟩

/-- **Stacks Project, Tag 0E2D.** Let `R → A` be a flat ring map of finite presentation. Any two
relative dualizing complexes for `R → A` are isomorphic.

The hypothesis `hdiag` is the invertibility of the tensor--Hom diagonal of [stacks 0BYN] at the
two pairs formed from the derived base changes `K₁` and `L₁` of `K` and `L` along the left
coprojection, with the diagonal as the internal-Hom source. It is what the source's appeal to
[stacks 0ATK] (3) would supply, and it is carried rather than proved: none of the three parts of
that tag, and not the library's fourth criterion either, applies to a general relative dualizing
complex, as the witness `R = k`, `A = k[x, y]/(x, y)²`, `K = L = Hom_k(A, k)` of the module
documentation shows. Everything else is proved: the defining condition of [stacks 0E2C] is
restated in the internal-Hom vocabulary by
`Dualizing.modelHom_diagonalObject_iso_of_derivedHom`, the two diagonals are composed with the
symmetry of the derived tensor product, and the resulting comparison in `D(A ⊗[R] A)` is brought
down to `D(A)` by
`Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso`.

For the two cases in which `hdiag` is discharged outright see
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject` and
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange`.

**`hdiag` cannot be discharged in general, because at that witness it is false.**
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation` computes both sides of the
diagonal there and finds `3 ≠ 8`.  The source's *mixed* configuration — the base change of `K`
along the left coprojection and of `L` along the right — survives the same computation, and
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` is this tag restated with it.  So the
implication below is true, and the three specialisations below are true and unconditional, but
the hypothesis they discharge is not a theorem: their hypotheses are not removable, and a
proof of the hypothesis belongs at the mixed form. -/
theorem nonempty_iso_of_isRelativeDualizingComplex (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L)
    (hdiag :
      IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((diagonalDerivedExtension R A).obj L) ((diagonalDerivedExtension R A).obj K)
          (diagonalObject R A)) ∧
        IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((diagonalDerivedExtension R A).obj K) ((diagonalDerivedExtension R A).obj L)
          (diagonalObject R A))) :
    Nonempty (K ≅ L) := by
  classical
  obtain ⟨hd₁, hd₂⟩ := hdiag
  let T := StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)
  let H := StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)
  let K₁ := (diagonalDerivedExtension R A).obj K
  let L₁ := (diagonalDerivedExtension R A).obj L
  let AB := diagonalObject R A
  have eK := (modelHom_diagonalObject_iso_of_derivedHom R A K₁ hK.diagonalDerivedHom).some
  have eL := (modelHom_diagonalObject_iso_of_derivedHom R A L₁ hL.diagonalDerivedHom).some
  let c₁ : T.obj (L₁, AB) ≅ H.obj (Opposite.op AB, T.obj (L₁, K₁)) :=
    T.mapIso (Iso.prod (Iso.refl L₁) eK.symm) ≪≫
      @asIso _ _ _ _ (StacksDraft.DerivedHom.derivedTensorHomDiagonal L₁ K₁ AB) hd₁
  let c₂ : T.obj (K₁, AB) ≅ H.obj (Opposite.op AB, T.obj (K₁, L₁)) :=
    T.mapIso (Iso.prod (Iso.refl K₁) eL.symm) ≪≫
      @asIso _ _ _ _ (StacksDraft.DerivedHom.derivedTensorHomDiagonal K₁ L₁ AB) hd₂
  let main : T.obj (L₁, AB) ≅ T.obj (K₁, AB) :=
    c₁ ≪≫ H.mapIso (Iso.prod (Iso.refl (Opposite.op AB))
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction
        (A ⊗[R] A)).tensorSwap L₁ K₁)) ≪≫ c₂.symm
  refine ⟨(nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso R A K).some.symm ≪≫
    (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[R] A)).mapDerivedCategory.mapIso
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction
          (A ⊗[R] A)).tensorSwap AB K₁ ≪≫ main.symm ≪≫
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction
          (A ⊗[R] A)).tensorSwap AB L₁).symm) ≪≫
    (nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso R A L).some⟩

/-- **[stacks 0E2D] when the diagonal is perfect, with nothing carried.** If the diagonal `A`,
read as an object of `D(A ⊗[R] A)` by restriction of scalars along the multiplication map, is a
perfect object there, then any two relative dualizing complexes for `R → A` are isomorphic.

Perfectness of the internal-Hom source is part (1) of [stacks 0ATK], which supplies both
tensor--Hom diagonals of `hdiag` at once, for either order of the two base changes. This is the
situation of a smooth `R → A`, whose diagonal is a regular immersion and so resolved by a Koszul
complex; the witness of the module documentation is the opposite extreme, a diagonal that is not
perfect because `dim_k A` does not divide `dim_k (A ⊗_k A)`. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L)
    (hperf : StacksDraft.Perfect.IsPerfect (diagonalObject R A)) :
    Nonempty (K ≅ L) :=
  have h := fun X Y => Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal X Y
    (diagonalObject R A) 0 (Or.inl hperf)
  nonempty_iso_of_isRelativeDualizingComplex R A K L hK hL ⟨h _ _, h _ _⟩

/-- **[stacks 0E2D] when the two base changes are perfect, with nothing carried.** If the derived
base changes of `K` and of `L` along the left coprojection are perfect objects of
`D(A ⊗[R] A)`, then `K` and `L` are isomorphic.

Perfectness of the *tensor factor* is part (2) of [stacks 0ATK], and each of the two diagonals of
`hdiag` has one of the two base changes as its tensor factor, so both are needed. For the witness
of the module documentation neither is perfect, the base change along a coprojection of
`Hom_k(A, k)` having infinite Tor dimension over `A ⊗_k A`. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L)
    (hKperf : StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj K))
    (hLperf : StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj L)) :
    Nonempty (K ≅ L) :=
  have h := fun X Y (hX : StacksDraft.Perfect.IsPerfect X) =>
    Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal X Y (diagonalObject R A) 0
      (Or.inr (Or.inl hX))
  nonempty_iso_of_isRelativeDualizingComplex R A K L hK hL ⟨h _ _ hLperf, h _ _ hKperf⟩

/-- **The derived base change of a relative dualizing complex is bounded below.** Relative
perfectness provides a representative that is a bounded complex of `A`-modules flat over `R`
([stacks 0DHV]); extension of scalars along the left coprojection preserves its strict lower
bound, being applied degreewise, and a strict lower bound on a representative is a cohomological
lower bound on the object it represents.

This is the hypothesis "`L` is bounded below" of [stacks 0ATK] (3) at the two tensor--Hom
diagonals of `Dualizing.nonempty_iso_of_isRelativeDualizingComplex`; only the first of the two
conditions defining a relative dualizing complex enters. -/
theorem exists_isGE_diagonalDerivedExtension_of_isRelativeDualizingComplex (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K) :
    ∃ a : ℤ, DerivedCategory.IsGE ((diagonalDerivedExtension R A).obj K) a := by
  obtain ⟨P, a, b, hGE, hLE, hflat, hfp, ⟨e⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ K).1 hK.relativelyPerfect
  have := hGE
  have := Stacks.DerivedTensorHomDiagonal.isStrictlyGE_extendScalars
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) P a
  exact ⟨a, DerivedCategory.TStructure.t.isGE_of_iso
    (diagonalDerivedExtensionIso R A K P e.symm).symm a⟩

/-- **[stacks 0E2D] with the Tor-amplitude bound of [stacks 0ATK] (3), with nothing carried.**
If each of the two derived base changes of `K` and `L` along the left coprojection has Tor
amplitude bounded below over `A ⊗[R] A` — that is, tensoring it with a module placed in degree
zero gives nothing in degrees below a fixed `a` — then `K` and `L` are isomorphic.

This is the hypothesis the source's proof actually needs, in place of `hdiag`: part (3) of
[stacks 0ATK] asks for a pseudo-coherent internal-Hom source, which the diagonal is
(`Dualizing.isPseudoCoherent_diagonal`), a bounded-below internal-Hom target, which both base
changes are
(`Dualizing.exists_isGE_diagonalDerivedExtension_of_isRelativeDualizingComplex`), and exactly
this bound on the tensor factor.

**The hypothesis is formally weaker than that of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange` — a perfect object
has Tor amplitude bounded below — but it is not weaker in substance: at a relative dualizing
complex the two single out the same objects.**  This is
`Dualizing.isPerfect_of_isRelativeDualizingComplex_of_torAmplitude` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTorAmplitudeDescent`, which descends the
bound from `A ⊗[R] A` to `A` — every `A`-module being the restriction along the left coprojection
of its own restriction along the multiplication map — and then reads pseudo-coherence together
with a Tor-amplitude window as perfectness.  So the route the source's proof takes through
[stacks 0ATK] (3) reaches the perfect case of [stacks 0E2D] and no further.

The bound is read over `A ⊗[R] A`, which is where [stacks 0ATK] takes it, and that is precisely
what fails for a general relative dualizing complex: the source reads the Tor amplitude of
`K ⊗ᴸ_A (A ⊗[R] A)` over `R`, over which it is bounded because `K` is `R`-perfect, whereas the
witness `R = k`, `A = k[x, y]/(x, y)²`, `K = L = Hom_k(A, k)` of the module documentation has
`Tor_i` over `A ⊗_k A` nonzero in every degree. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L) (a : ℤ)
    (hKtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N))))
    (hLtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj L)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N)))) :
    Nonempty (K ≅ L) :=
  nonempty_iso_of_isRelativeDualizingComplex R A K L hK hL
    ⟨Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal
        ((diagonalDerivedExtension R A).obj L) ((diagonalDerivedExtension R A).obj K)
        (diagonalObject R A) a
        (Or.inr (Or.inr ⟨isPseudoCoherent_diagonal R A,
          exists_isGE_diagonalDerivedExtension_of_isRelativeDualizingComplex R A K hK, hLtor⟩)),
      Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal
        ((diagonalDerivedExtension R A).obj K) ((diagonalDerivedExtension R A).obj L)
        (diagonalObject R A) a
        (Or.inr (Or.inr ⟨isPseudoCoherent_diagonal R A,
          exists_isGE_diagonalDerivedExtension_of_isRelativeDualizingComplex R A L hL,
          hKtor⟩))⟩

end

end Dualizing

end
