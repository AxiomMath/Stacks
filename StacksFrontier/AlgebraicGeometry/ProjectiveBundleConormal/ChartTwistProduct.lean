module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct.ScalarIdentity
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct.TautologicalChart
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct.ReindexFrame

/-!
# The scalar identity for the twisted tautological map of Tag 0B3V clause 3 on a chart

`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt` computes the map
of [Stacks, Tag 0B3V] clause 3 on a product section `κ ⊗ w` of `ker(q) ⊗ 𝓛^{⊗ -1}` over a chart
`W`, and leaves the resulting section of the ideal sheaf `ℐ(σ)` as a hypothesis `hy`: a section
over an open `V` of `𝐏(ℰ)` whose image in `𝒪_{𝐏(ℰ)}` is the value of the untwisted tautological
map `ṽ` on the corresponding product section upstairs. By
`Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_tensorSectionsAt` that value is the
multiplication `Stacks.SheafOfModules.Invertible.sectionMulNegOne` of `v(π^*κ)` with `w₀`.

**This file is the algebra of that product.** It is a statement about sections of the structure
sheaf of `𝐏(ℰ)` alone: no sheaf-of-modules isomorphism is split and no ideal sheaf is built.

Two things are proved, and then combined.

* The pairing `𝒪(1) ⊗ 𝒪(-1) ≅ 𝒪` is **linear in its `𝒪(1)` slot**, so a scalar factored out of
  the degree-one section comes out of the product as a function. Hence the ratio identity of
  `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio` — a degree-one section is a
  function times the degree-one section of the frame — becomes an identity between *functions*:
  `ṽ(κ ⊗ w₀) = (ratio) · ṽ(s ⊗ w₀)`.
* That **ratio is killed by `σ`** when `κ` comes from `ker(q)`. This is the geometric content of
  clause 3's chart computation, read directly on `𝐏(ℰ)`: the point of the affine bundle named by
  `σ|_W` is its origin, so every affine coordinate `ι κ / ι s` with `κ ∈ ker p` vanishes on it.

So the product `ṽ(κ ⊗ w₀)` is a function on `V` that `σ` pulls back to `0`; it lies in the ideal
of the section, which is what makes it the image of a section of `ℐ(σ)`.

## Main results

* `Stacks.ProjectiveBundleConormal.sectionMulNegOne_smul_left` and
  `sectionMulNegOne_smul_left_eq_mul`: **the pairing is linear in the `𝒪(1)` slot.**
* `Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_tensorPowerSucc` and
  `sectionMulNegOne_eq_negOneMulIso`: **the pairing evaluated on a named pair.** The product of a
  section of `L` with a section of `L^{⊗ -1}` is the successor comparison of [Stacks, Tag 01CU]
  on the product section with the factors exchanged, hence is the left-hand side of the
  hypothesis `hup` of
  `Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app`. The two crossings
  this needs between the monoidal tensor product and the tensor product sheaf of
  [Stacks, Tag 01CA], and between the two spellings of the unit, are
  `Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso` and
  `sheafifyUnitIso_eq_unitIso`.
* `Stacks.ProjectiveBundleConormal.kernelTautologicalMap_unitSection` and
  `kernelTautologicalMap_res_unitSection`: `v` on the canonical section of `π^*ker q` attached to
  `k : Γ(ker q, W)` is the degree-one tautological section of `ι k`, restricted.
* `Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_tensorSectionsAt_eq_mul`: **the
  scalar identity.** If the degree-one section `v(z)` is `g` times a reference section `b`, then
  `ṽ` on the product section determined by `z` and `w` is `g` times the product of `b` with `w`.
* `Stacks.ProjectiveBundleConormal.appLE_eq_zero_of_tautologicalSectionOver_eq_smul`: **the ratio
  of a kernel section vanishes on the section.** If the degree-one section of `ι k`, `k` a
  section of `ker q`, is `g` times the degree-one section of a frame section `s`, then `σ` pulls
  `g` back to `0`.
* `Stacks.ProjectiveBundleConormal.appLE_kernelTautologicalMapTwisted_tensorSectionsAt_eq_zero`:
  the two together — `σ` pulls `ṽ(κ ⊗ w)` back to `0`.
* `Stacks.ProjectiveBundleConormal.tautologicalChart`: **the chart the ratio exists on**, the
  open `π⁻¹W ∩ D₊(ι s)` of `𝐏(ℰ)` read upstairs as the nonvanishing locus of the degree-one
  section attached to `s`, with `tautologicalChart_le` and `le_preimage_tautologicalChart` the
  two inequalities the statements above are parametrised by.
* `Stacks.ProjectiveBundleConormal.exists_tautologicalSectionOver_res_eq_smul`: **the ratio
  exists there.** On that chart the degree-one section attached to `s` generates `𝒪(1)`, so the
  one attached to any `m` is a function times it.
* `Stacks.ProjectiveBundleConormal.basicOpen_le_preimage_chartMap_tautologicalChart`: **the
  affine chart of the frame lies inside that chart**, read through `chartMap`. This is what lets
  the *target* half of clause 3 be computed over the tautological chart, which is the only open
  over which the two halves of the chart computation can meet.
* `Stacks.ProjectiveBundleConormal.appLE_tautologicalChart_kernelTautologicalMapTwisted_eq_zero`:
  **the vanishing with nothing left to assume** — on that chart, `σ` pulls `ṽ(π^*k ⊗ w)` back to
  `0` for every section `k` of `ker q` over `W` and every `w`.
* `Stacks.ProjectiveBundleConormal.appLE_appLE_toBase`: **a section of `π` splits `appLE` on
  functions** — `σ^♯(π^♯a) = a`, the only use made of `σ ≫ π = 𝟙 X` below.
* `Stacks.ProjectiveBundleConormal.pullbackSection_smul_appLE_toBase`: **a scalar multiple of a
  pulled-back section is a pulled-back section**, the scalar upstairs being `π^♯` of the one
  downstairs.
* `Stacks.ProjectiveBundleConormal.hom_pullbackSection_smul_tautologicalSectionOver` and
  `exists_hom_pullbackSection_tautologicalChart_eq`: **`b₀ ↦ e(σ^*b₀)` is onto the sections of
  `𝓛` over `W`**, the witness being `π^♯(eL c)` times the degree-one section of `s` restricted to
  the chart — first with that witness named, which is the form the upstairs hypothesis `hup`
  needs, then with it forgotten. This is the reachability statement the downstairs hypothesis
  `hdown` of `Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` needs.
* `Stacks.ProjectiveBundleConormal.notMem_maximalIdeal_smul_top_smul_of_isUnit`: **a unit multiple
  of a section generating at every point of an open generates there too**, on a ringed space with
  local stalks and for an arbitrary sheaf of modules.
* `Stacks.ProjectiveBundleConormal.isUnit_linearEquiv_of_tensorPairing_eq_unitSection`: **a frame
  sends a section pairing to the unit section to a unit.** These two are the generator facts the
  witness above needs: the scalar `π^♯(eL c)` is a unit because `eL c` is.
* `Stacks.ProjectiveBundleConormal.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app`:
  **the hypothesis `hw` of
  `Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt`,
  discharged on the chart** for a section `w` of `𝓛^{⊗ -1}` generating on `W`. Both pairings that
  `Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` asks for are produced
  here — `hdown` from the pairing existence of [Stacks, Tag 01CY] with the generator in the second
  factor, `hup` from the generation of the witness just described.
* `Stacks.ProjectiveBundleConormal`
  `.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_restrictIsoUnit`: **the same with
  nothing left to assume**, for the section that a trivialisation of `(𝓛^{⊗ -1})|_W` names.
* `Stacks.ProjectiveBundleConormal`
  `.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned`: **`hw` with the section
  `w₀` it returns pinned**, by the value — `1` — of its pairing with the degree-one section of
  the frame. The two statements above determine `σ^*w₀` and hence `w₀` only modulo the ideal of
  the section, which is not enough for the chart computation of clause 3; this one takes the
  degree-one section of `s` itself for the `b₀` of `hup`, at the cost of asking for the
  downstairs pairing `hpair` which the other two get for free.
* `Stacks.ProjectiveBundleConormal.unitSection_res` and `tautologicalSectionOver_res`: **the
  degree-one section attached to a section of `ℰ` is compatible with shrinking the base open.**
* `Stacks.ProjectiveBundleConormal.smul_res_injective_of_subset_nonvanishingLocusOn`: the
  injectivity half of generation on a nonvanishing locus, which the development had only in its
  surjectivity half (`exists_eq_smul_res_of_subset_nonvanishingLocusOn`).
* `Stacks.ProjectiveBundleConormal.res_eq_res_of_tautologicalSectionOver_eq_smul`: **two ratios
  of the same pair of degree-one sections agree where they meet.** A ratio given on an arbitrary
  open `V` of `𝐏(ℰ)` over `U`, and the ratio the chart over an open `W ≤ U` produces, agree on
  `V ⊓ tautologicalChart E W (s|_W)`. This is what lets a ratio the caller supplies on an
  unrelated `V` be recognised in the chart computation.
* `Stacks.ProjectiveBundleConormal.exists_isAffineOpen_chartLinearForm_eq_one`: **a section of
  `ℰ` whose image pairs to `1` carries a frame around every point of its domain** — the chart
  data of clause 3 at a section that is *given* rather than chosen, which
  `Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` cannot supply.

## Implementation notes

**No tag is attached, and in particular no `@[stacks 0B3V]`.** A scalar identity between two
sections of a structure sheaf is one step of clause 3, not the clause; attaching the tag to it
would register a statement strictly weaker than the clause asserts. The whole
`ProjectiveBundleConormal` directory carries no `@[stacks …]` for the same reason, and this file
keeps it that way. The *normalization* clause of the tag — the value of the conormal map on
`k ⊗ s̄^{⊗ -1}` — is closed in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.GeneratorLocality`, which is where its
attribute sits; the last two inputs it needed are the reindexing and frame statements at the end
of this file.

**Three scalar spellings are in play and the choice is forced.** `Γ(M, U)` is the only spelling
carrying the `Module Γ(X, U) Γ(M, U)` instance, so `r • a` elaborates only when both arguments are
read at it; `(kernelTautologicalMap E Q).val.app (op V) z` and
`M.val.map (homOfLE hV).op a` are *not* read at it — the first displays as `M.val.obj (op V)` and
the second lands in a `ModuleCat.restrictScalars`, and both make the `•` notation fail to
synthesise `HSMul`. So every scalar action on such a term is written
`(M.smul r).hom _`, the spelling of
`Stacks.ProjectiveBundleConormal.eq_of_smul_pullbackSection_eq`, and the restriction maps that
feed a `•` are written `M.presheaf.map`. The two restriction spellings agree definitionally, so a
consumer holding one can use a lemma stated at the other.

**Nothing is rewritten on a module.** Every comparison is cancelled forwards with `Eq.trans` and
`congrArg`, following the discipline recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio`; the only tactic steps on a
goal are the last four of
`appLE_eq_zero_of_tautologicalSectionOver_eq_smul`, which are pure `Γ(X, W)`-algebra.

**The zero morphism is read on a section by `rfl`**, which is how
`Q.q (ι k) = 0` is obtained from `CategoryTheory.Limits.kernel.condition`.

**`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Sections` is imported here, and this
is the only module that imports it.** The `hw` result below is the meeting point of the two
halves: the reachability statement and the chart live here, the base-change comparison on a
section lives there. The import adds 64 modules to this module's closure (2332 to
2396); the other direction — the `hw` result placed in `Sections`, importing this module — would
have added 537 to that module's closure (1859 to 2396), so this is the cheap direction. No other
module imports either of the two, so nothing downstream pays.

## Not done here

**The ratio is not *computed* here, only shown to exist** — which is all the hypothesis `hz` of
the scalar identity asks for, and `Stacks.ProjectiveBundleConormal.tautologicalChart` is the open
on which existence holds. What is proved here instead is that the degree-one section of `s`
*generates* `𝒪(1)` on its nonvanishing locus
(`Stacks.ProjectiveBundleConormal.exists_eq_smul_res_of_subset_nonvanishingLocusOn`), which
identifies the ratio up to nothing at all and uses only invertibility of `𝒪(1)`. That remains the
right statement for the consumers that want existence alone, and
`exists_tautologicalSectionOver_res_eq_smul` keeps its weaker form for them.

The identification of the ratio with `ι m / ι s`, which has to cross the open immersion
`Stacks.ProjectiveBundleConormal.chartMap` to land on an open of `𝐏(ℰ)`, is proved in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatioSplit`: the transport is
`Stacks.ProjectiveBundleConormal.appLE_chartMap_eq_awayToSection_of_res_eq_smul`, and it is
carried on across `splitChartMap` into `Sym_{Γ(X,W)}(ker p)`, where `ι k / ι s ↦ ι k`, by
`Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι`. The general form
is stated at an *opaque* morphism into `Proj` with the open as a variable
(`appLE_eq_awayToSection_of_res_eq_smul`), which keeps the chart layer out of the statement
entirely and makes the chart instantiation a cheap application.

That identification is **not** needed for clause 3's scalar
identity, and this file's own route does not use it.

**The reference product `hg₀` is evaluated.** The scalar identity takes the value `g₀` of
`Stacks.SheafOfModules.Invertible.sectionMulNegOne` on the pair `(b₀, w)` as a parameter, which
costs nothing there because the conclusion is that `σ` kills the whole product. But the chart
computation of clause 3 needs more of that pairing than the scalar identity does: the hypotheses
`hup` and `hdown` of
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` ask for a pair of
sections *pairing to `1`*, which naturality and the identification with Tag 01CU's coherent
multiplication (`Stacks.SheafOfModules.Invertible.sectionMulNegOne_eq_coherent`) do not give,
as the "Not done here" of `StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Evaluation`
records. `Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso` evaluates
it: the product is the successor comparison of Tag 01CU on the product section with the factors
exchanged, which is exactly the left-hand side of `hup`. The statement wanted is
*on an open where a section `b₀` of an invertible `L` generates, there is a section `w₀` of
`L^{⊗ -1}` pairing with it to `1`*, and it is proved:
`Stacks.SheafOfModules.exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top`
(`StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator`) is the inverse-section
clause of [Stacks, Tag 01CY] for a section defined on an open, and
`Stacks.ProjBundleInverseBaseChange.exists_negOneMulIso_hom_tensorSectionsAt_eq_one` is it read
against `Stacks.ProjBundleInverseBaseChange.negOneMulIso`, which is exactly the hypothesis `hup`
of `Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app`.

**`hdown` is closed, and with it `hw` on the chart.** The *downstairs* hypothesis `hdown` of that
theorem has both of its pairing arguments already determined — `w` is the section the comparison
is evaluated at and `e(σ^*b₀)` is fixed by the `b₀` that `hup` consumed — so it is not an
existence statement about the pairing. What discharges it is that the section of `𝓛` the pairing
determines lie in the image of `b₀ ↦ e(σ^*b₀)`, which
`Stacks.ProjectiveBundleConormal.hom_pullbackSection_smul_tautologicalSectionOver` gives. The two
assemblies that stand between that and `hdown` are done, and
`Stacks.ProjectiveBundleConormal.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app`
is the result:

* the pairing partner of a generating section of `𝓛^{⊗ -1}`. `Stacks.SheafOfModules`
  `.exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top` produces the inverse
  factor from a generating section of the module, which is the `hup` direction; `hdown` needs it
  the other way round, and `Stacks.ProjBundleInverseBaseChange`
  `.exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top_right` is that — the
  braiding of the tensor product sheaf and nothing else. The trivialisation it is read against is
  `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'`, the crossing from
  `Stacks.SheafOfModules.tensorPairing` to
  `Stacks.ProjBundleInverseBaseChange.negOneMulIso'` that `negOneMulPairingIso` performs in the
  `hup` direction; in this factor order no braiding is needed, so
  `Stacks.SheafOfModules.tensorPairing` against it *is* `hdown`, definitionally. The germ
  hypothesis on `w` is
  `Stacks.ProjectiveBundleConormal.notMem_maximalIdeal_smul_top_restrictIsoUnit_res`, the
  germ condition for the section a trivialisation of a restriction names, read on the restriction
  of that section to the chart.
* that the witness above *generates* `𝒪(1)` on the chart, which `hup` requires of `b₀`. The
  witness is `π^♯(eL c)` times a generating section, so it generates exactly when `eL c` is a
  unit. **Both the unit comparison of two generators and the stability of the germ condition
  under multiplication by a unit are stated in the development.** The stability is
  `Stacks.SheafOfModules.smul_notMem_maximalIdeal_smul_top_iff`
  (`StacksFrontier/AlgebraicGeometry/QuasiAffineNonvanishing/Basic.lean`), an `iff`; the unit
  comparison is `Stacks.SheafOfModules.isUnit_of_smul_eq_generator`
  (`StacksFrontier/AlgebraicGeometry/NormInvertible/Generators.lean`) for two sections generating on
  every smaller open, and
  `Stacks.SheafOfModules.Invertible.isUnit_linearEquiv_of_surjective_smul` in the cheaper form the
  chart actually has, where the frame `eL` normalises `q s` to `1` and only surjectivity over `W`
  is known. The two assemblies are
  `Stacks.ProjectiveBundleConormal.isUnit_linearEquiv_of_tensorPairing_eq_unitSection` and
  `notMem_maximalIdeal_smul_top_smul_of_isUnit`, the generation of the degree-one section of `s`
  on the chart coming from `Stacks.ProjectiveBundleConormal.coe_tautologicalChart` crossed to the
  `𝔪_y • ⊤` spelling by `Stacks.NonvanishingPullback.mem_maximalSmul_iff`.

**`hpair` is discharged on a chart, and not here.** It is
`Stacks.ProjectiveBundleConormal.tensorPairing_chartTrivialisation_eq_unitSection` of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTrivialisationPairing`, which imports
this module; the paragraphs below record what that requires.
`exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned` asks that `q s` and `w` pair
to `1` downstairs. For the `w` a trivialisation `θ` of `(𝓛^{⊗ -1})|_W` names, that pairing is the
value at `q s` of the frame `θ` induces, which is `1` exactly when the frame `eL` of `hs` is that
one.

`Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` returns `eL` and the
trivialisation `τ` of `𝓛|_W` related to each other; without a relation, `pairing(q s, w)` would
only be a unit for general chart data. It returns
`τ` together with `τ = Stacks.ProjectiveBundleConormal.chartTrivialisation Q hU e s hs`, whose
trivialisation is built from the spanning section `q s` itself via
`Stacks.ProjectiveBundleConormal.span_singleton_app_eq_top_of_chartLinearForm_eq_one`, i.e. from
the frame condition alone.

This relation is necessary but **not** sufficient. `hpair` additionally needs two section
formulas, **both proved** in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTrivialisationPairing`:

* `(restrictIsoUnitOfSpanEqTop L U hU t ht).inv 1 = t` is
  `Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop_inv_val_app_one`. The whole chain
  is **definitional on sections** except for `one_smul` and the unit
  comparison. `Stacks.SheafOfModules.isoUnitOver` on a section is `c ↦ c · a` by `rfl` (now
  `Stacks.SheafOfModules.isoUnitOver_inv_val_app`), `Scheme.Modules.overFunctorEquiv` is the
  identity on sections in both directions by `rfl`, `Scheme.Modules.overEquiv` re-indexes the open
  by `rfl`, and `Stacks.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit` splits by `rfl`; the
  unit comparison is
  `Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictUnitIso_inv_val_app_one`.
* `pairing(τ⁻¹ 1, (restrictInverseTwistIso Q.L W τ)⁻¹ 1) = 1` is
  `Stacks.ProjectiveBundleConormal.sectionMulNegOne_restrictInverseTwistIso_inv_one`, and the
  crossing from `sectionMulNegOne` to `tensorPairing` against
  `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'` is
  `Stacks.ProjectiveBundleConormal.tensorPairing_negOneMulPairingIso'`. The crossing has to read
  `Stacks.SheafOfModules.tensorPairing` at an **opaque** trivialisation: with
  `negOneMulPairingIso'` written out, the identification of `tensorPairing ψ V a b` with
  `ψ.hom.val.app (op V) (tensorSectionsAt … a b)` — a `rfl` for abstract `ψ` — is a
  deterministic timeout at `whnf`.

Item 2 of the "What is not done" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting` records the same facts.

**The germ condition on `w` cannot be written as a standalone statement at this spelling, and is
not.** `Submodule (ringStalk X y) (grpStalk X (Invertible.tensorPower …).val y)` has no
synthesizable `Module` instance — nor does it for a *variable* `M : X.Modules`; instance search
finds the stalk module structure only for a module variable over the root-namespace
`structureSheafRing` of a ringed space, which is how
`Stacks.ProjectiveBundleConormal.notMem_maximalIdeal_smul_top_smul_of_isUnit` and
`notMem_maximalIdeal_smul_top_restrictIsoUnit_res` are written. The hypothesis of
`exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app` is therefore the *generation*
condition — `d ↦ d · w|_V` bijective for every `V ≤ W` — which does elaborate at the
`presheaf.map` spelling and which
`Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_forall_bijective_smul` and
`bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top` convert to and from the germ
condition on application.

**No section of `ℐ(σ)` is named here.** The conclusion of the chart statements below is an
equation in `Γ(X, W)` after `σ`. The target identification read on the canonical generator of the
tilde, which turning that into the equation clause 3 reduces to also needs, is
`Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`
— but it is usable only over `Stacks.ProjectiveBundleConormal.tautologicalChart`, not over
`π⁻¹W`, i.e. not at the instance that
`Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTilde` and hence
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq'` are built from; the
open the chart earns there is `basicOpen_le_preimage_chartMap_tautologicalChart` below.
**Its first factor is not the obstruction**:
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` is characterised — `Stacks.Divisors.conormalSheafIsoNegativeTwist_apply`
carries `@[stacks 0B3P "canonical ideal quotient"]`, is axiom-clean, and characterises it on
sections over an affine open with an affine model, `conormalSheafIsoNegativeTwist` being *defined*
as `conormalSheafIsoPullbackSelf D.subschemeι`; its general form is
`Stacks.Conormal.factoredAffineConormalIsoCotangent_pullbackIdealSheafIso_unit`. What is missing
is a section formula for the other three factors:
`Stacks.Conormal.Locality.conormalRestrictIso` has one
(`Stacks.Conormal.Locality.conormalRestrictIso_unit_app`), while
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` and
`Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource` are
characterised only at the level of the adjunction unit, never on a section.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/
