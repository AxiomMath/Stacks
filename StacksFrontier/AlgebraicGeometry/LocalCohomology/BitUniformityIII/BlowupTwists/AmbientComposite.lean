module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwists.ThickeningTwists

/-!
# Tag 0GA7 for the blowup: the ambient composite `𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q)` vanishes

This part proves `ambientTwistMap_comp_thickeningTwistProj_eq_zero` through the local
factorisation of `ambientTwistMap` near the points where `b⁽¹⁾` is invertible, and records why
`GeometricInput` is not inhabited in the repository.

## Why `GeometricInput` is not inhabited here

**No witness for `GeometricInput` is constructed**, so the four clauses below are theorems about
the actual blowup which are nevertheless conditional, and Tag 0GA7 is not closed by them. The
obstruction is not one absent lemma but four. Each is described below, together with the
results the library does have towards it.

**(1) `ambα` is constructed: it is `ambientTwistMap` of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/AmbientTwistMap.lean`, and it is
not a field.** Only `divα` remains unconstructible here. The counting argument that rules out
the naive construction is recorded in that file's module docstring together with the repair.

In brief: `blowupTwist I q` is `twistingSheaf (Stacks.Blowup.reesGrading I) q`, the associated
sheaf of `twistGrading (reesGrading I) q`, whose degree-`i` piece is `I^{i+q}` when `i + q ≥ 0`
and `0` below. So `S(q+1)` is generated over `S` by its lowest piece `S(q+1)_{-q-1} = S₀ = A`,
while `S(q)_{-q-1} = S_{-1} = 0`: a degree-preserving `S`-linear map `S(q+1) ⟶ S(q)` is
determined by the image of `1 ∈ A`, which has nowhere to go, so the only such map is zero. The
honest map is the family of inclusions `I^{i+q+1} ⊆ I^{i+q}` — in the Rees model `S ⊆ A[X]`,
*division by `X`*, `Polynomial.divX` — and that family fails `S`-linearity in exactly one
degree, `i = -q-1`, where its source is `A` and its target is `0`. So
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap` cannot produce `ambα`
with the ring itself as its source module, and `Stacks.Blowup.reesDivide` is not the device
either: that is a ring map to a chart ring, not a module map.

**(2) The repair — the saturation comparison plus the truncation — is proved, and `ambα` is
built from it.** What produces the first map is: *a degree-preserving map of graded `S`-modules
bijective in all large degrees induces an isomorphism of associated sheaves*, which is

`isIso_associatedModuleSheafMap_of_eventually_bijective`

in the namespace `Stacks.AlgebraicGeometry.ProjStalkGlobalSections`, of
`StacksFrontier/AlgebraicGeometry/ProjStalkGlobalSections/SheafMapIsIso.lean` — public, axiom-clean,
stated for two *arbitrary* graded modules over `𝒮` with independent `SetLike` carriers,
the one real restriction being `{S M N : Type u}`, satisfied here. (It is not in the
`ProjSerreCorrespondence` namespace.)

Its companion is one piece of generic graded-algebra infrastructure, *the truncation of
a graded module above a degree*, which is `Stacks.GradedModule.truncationAbove` of
`StacksFrontier/RingTheory/GradedAlgebra/ModuleTruncation.lean`: the submodule of `M` cut out by
the vanishing of every homogeneous component in degrees `< N₀`, equal to `⨆_{i ≥ N₀} 𝒨 i` by
`Stacks.GradedModule.truncationAbove_eq_span`, with its `DirectSum.Decomposition` and
`SetLike.GradedSMul` instances and its inclusion into `M`. It is a submodule because `𝒮` is
nonnegatively graded, so the action only raises degrees. It is not in Mathlib either — the
nearest declaration there, `DirectSum.isInternal_biSup_submodule_of_iSupIndep`, is indexed by a
subtype of the index type rather than by `ℤ` with `⊥` outside, and carries no `GradedSMul`
content.

At `N₀ = -q` and the twist `S(q+1)`, the truncation's underlying module is the irrelevant ideal
`S₊`, and:

* its inclusion into `S(q+1)` is bijective in every degree `≥ -q`, so by the comparison above
  `(S₊(q+1))~ ≅ 𝒪_X(q+1)` — this is `Stacks.Blowup.reesTruncationComparison`;
* `divX` is a degree-preserving `S`-linear map from it to `S(q)`, *because* the one degree where
  `S`-linearity failed, `i = -q-1`, is exactly the degree the truncation removed: linearity on
  `S₊` is the cancellation of `X` from `X · divX (c · p) = c · p = X · (c · divX p)`.

`ambientTwistMap I q` is the first iso inverted and composed with the second map, and it is
canonical: no generator is chosen anywhere. Its definition is marked `irreducible` so that the
unifier does not unfold the comparison isomorphism when the map appears as an argument;
`Stacks.Blowup.twistShiftMap_eq` and
`Stacks.LocalCohomology.UniformityIII.ambientTwistMap_eq` are the way in.

`divα` needs this *and* the ideal-sheaf side, since the thickenings `𝒪_{Yₙ}` are pushforwards
along closed immersions cut out by powers of the ideal sheaf rather than `Proj`-graded objects;
the extra map is `ℐ_Y ⊗ 𝒪_{Yₙ} ⟶ 𝒪_{Y_{n+1}}`, for which `Stacks.Divisors.idealAction` and
`Stacks.Divisors.idealActionFactor` of
`StacksFrontier/AlgebraicGeometry/Divisors/IdealActionFactorization.lean` are the primitives. So
`divα` is still a field, and so is `amb_shortExact`. Of the three `amb_*` fields none is left:
`amb_sq_left` is `blowupΓMap_ambientTwistMap_ambientSections` below, proved from the naturality
of the canonical section of a homogeneous element and from
`divX (monomial (q+1) x) = monomial q x`, and it needed no comparison between the two models;
and `amb_comp` is `ambientTwistMap_comp_thickeningTwistProj_eq_zero` below, which does need
one, and the paragraphs below record how it is made. What `amb_shortExact` asks beyond the
complex condition is *exactness*; entry (2c) below says what that now reduces to, and it is
**not** the identification of `𝒪_{Y₁}` with `𝒪_X/I𝒪_X`, which is proved.

**The engine of that comparison is proved, and it is not an iso but a containment.** The
one thing the ideal-sheaf model asks of the first map is that its image lie in `I·𝒪_X(q)`, and
that is
`Stacks.Blowup.exists_mem_degreeZeroModuleAt_map_reesShift` of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/TwistShiftIdeal.lean`: at every
point `x` of `X` there is a `b ∈ I` with `b⁽¹⁾ ∉ x` — the degree-one standard opens cover `X`,
`Stacks.Blowup.exists_reesDegOne_mem_primeCompl` — and in the degree-zero localization at `x`
the map `divX` induces, every element of the stalk of `𝒪_X(q+1)` goes to `b` times an element
of the stalk of `𝒪_X(q)`. The whole content is the one-line identity
`Stacks.Blowup.reesDegOne_mul_reesShift`, `b⁽¹⁾ · divX m = bX · divX m = b · m`, valid on the
truncation because an element of it has vanishing constant term; localised, it rewrites
`divX m / s` as `b · (m / (b⁽¹⁾·s))`, the denominator's extra degree being exactly the shift
from `S(q+1)` to `S(q)`. No generator of `I` is chosen globally and no hypothesis on `A`
enters. This is [Stacks, Tag 02OS] part (3) in the only direction that is a statement about the
`Proj`-graded twists; it is *not* the identification `𝒪_X(1) = 𝒪_X(-Y)`, which is an equality of
subsheaves of `𝒪_X`, so nothing there carries a Tag 02OS attribute.

**All four steps between that containment and the complex condition are now theorems**, and the
complex condition with them.

* the *stalk bridge*, carrying the containment from `Stacks.Blowup.reesShift` to the morphism
  `Stacks.Blowup.twistShiftMap` itself, is
  `Stacks.Blowup.exists_mem_degreeZeroModuleAt_stalkMap_twistShiftMap` of
  `StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/TwistShiftIdeal.lean`, with
  `Stacks.Blowup.exists_mem_degreeZeroModuleAt_stalkShift` the form to use. It is
  `Stacks.Blowup.twistShiftMap_eq` plus
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.stalkMap_associatedModuleSheafMap_eval`, and
  the comparison isomorphism contributes nothing to the image. Three earlier spellings each
  exhausted the 200 000-heartbeat budget at `isDefEq`; what works is to keep the stalk functor
  away from every composite — `AlgebraicGeometry.SheafOfModules.stalkMap` is used only through
  `stalkMap_germ`, which holds for an arbitrary morphism, and the factorisation is performed on
  *sections* instead, by `Stacks.Blowup.app_twistShiftMap`. That file's implementation notes
  record the three distinct ways the budget blows and the remedy for each, including that the
  budget is per declaration and is spent by a statement before its proof begins, which is why
  `Stacks.Blowup.stalkShift` is a named definition;
* the *interchange identity* is `ambientTwistMap_comp_thickeningTwistProj` below, which reduces
  the complex condition to the single vanishing
  `thickeningSheaf I 1 ◁ ambientTwistMap I q = 0`. **That reduction is not the route taken**, and
  the paragraph after this list says why; what replaces it is `app_thickeningTwistProj`, the
  evaluation of the second map of the sequence on a local section as a pure tensor whose left
  factor is the image of `1`;
* the *ideal-sheaf step*, that `I` kills `𝒪_{Y₁}`, is `app_top_thickeningProj_one_eq_zero`
  below: the global section of `𝒪_X` pulled back from `b ∈ I` along the blowup morphism is zero
  on the exceptional divisor. The route is not the ideal-sheaf submodule API but the pullback
  square of `AlgebraicGeometry.Scheme.IdealSheafData.comapIso`, which factors
  `(J.comap f).subschemeι ≫ f` through `J.subschemeι`, together with
  `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app` at `⊤` on the *affine* base —
  that is `app_top_unitToPushforwardObjUnit_eq_zero_of_comap`, stated with the identification of
  the ideal sheaf as a hypothesis so that `subst` removes it and the first thickening, a first
  power, is read off `pow_one`. Carrying it to an arbitrary open is naturality of
  `thickeningProj` and `PresheafOfModules.naturality_apply` and nothing else, and that is
  `app_thickeningProj_one_restrict_eq_zero`, with
  `app_thickeningProj_one_map_restrict_eq_zero` the form restricted in two steps `⊤ ≥ U ≥ V`
  that the local factorisation's scalar is in. Both are chained by `Eq.trans` and `congrArg` in
  term mode: a `rw` with the `⊤`-sections statement leaves an unsolved goal, the two spellings of
  the application of `(thickeningProj I 1).val.app _` — with and without the explicit `.hom` —
  not matching syntactically;
* the *local factorisation on sections* — near any point at which `b⁽¹⁾` is invertible, the
  image of a section of `𝒪_X(q+1)` is `b ·` a section of `𝒪_X(q)` — is
  `Stacks.Blowup.exists_restrict_appTwistShift_eq_smul` of
  `StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/TwistShiftLocal.lean`, where
  every ingredient of it is proved too
  (`Stacks.Blowup.exists_forall_appTwistShift_val`, `Stacks.Blowup.shiftFractionSection`,
  `Stacks.Blowup.map_reesShift_eq_val_smul`, `Stacks.Blowup.map_reesShift_eq_zero`,
  `Stacks.Blowup.map_eq_smul_of_pointwise`). Its content is
  the same `Stacks.Blowup.map_reesShift_mk`, applied to the single fraction the local-fraction
  condition already supplies near the point; **no stalk functor and no germ appears**, so the
  stalk bridge of the previous item is not what this route needs. That file's implementation
  notes record what its elaboration costs: the cost is not in the statement but in `rcases`,
  which must not be used while the goal is the factorisation.

**The reduction of the complex condition through the interchange identity is not the route to
take.** `Stacks.SheafOfModules.OnSpace.tensor_hom_ext` *does* reduce
`thickeningSheaf I 1 ◁ ambientTwistMap I q = 0` to pure tensors, legitimately, because the
sections of `Stacks.SheafOfModules.OnSpace.tensorSheaf` form a sheaf and a locally zero section
is zero. But the goal it leaves mentions both `X.Modules` and
`SheafOfModules (structureSheafRing X.toRingedSpace)`, is reported as not type-correct at
`implicit` transparency, and has the two tensor factors written as
`(ULift.equivalence.symm.inverse.obj _).down` — the `ULift` copy on which
`Stacks.SheafOfModules.OnSpace.monoidal` is transported — so **no `rw` with `whiskerLeft_tmul`
fires**; this is the same obstacle the implementation notes below record for the associativity
step of the whiskering argument. Passing `A` and `B` as named arguments fixes the factors, as
`AlgebraicGeometry.schemeTheoreticSupport_iff_exceptionalTwistContraction_eq_zero` does.

What remains against the `◁` statement even then is its arbitrary left factor: it would need
`b • s = thickeningProj(b) * s` for an arbitrary section `s` of `𝒪_{Y₁}`, i.e.
`ModuleCat.restrictScalars.smul_def` transported through
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, whose two spellings of the scalar ring are not
reachable by instance search. Evaluating the composite
`ambientTwistMap I q ≫ thickeningTwistProj I 1 q` on a section needs none of that:
`thickeningTwistProj` is by definition the left unitor followed by a right whiskering, so on a
section it is the pure tensor of `𝒪_X ⟶ 𝒪_{Y₁}` applied to **`1`** with the section — that is
`app_thickeningTwistProj` below, `Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply` and
`whiskerRight_tmul` chained by `congrArg` as *terms*, the lambda of the `congrArg` carrying the
type of the intermediate section explicitly, since the whiskering's source object is written at
the `ULift` spelling and an inferred lambda reports an application type mismatch; and a left
factor which is the image of `1` is one the scalar can move onto, becoming the image of itself by
`Stacks.SheafOfModules.smul_app_one`. So the `◁` vanishing, whose exact Lean statement is
`∀ q : ℕ, (thickeningSheaf I 1 ◁ ambientTwistMap I q) = 0`, is strictly stronger than the complex
condition and is not proved; the complex condition itself is
`ambientTwistMap I q ≫ thickeningTwistProj I 1 q = 0`, and the pieces below prove it on
sections.

Two further things are proved and are *not* used by the complex condition as it is proved here.
The first is
the stalk bridge of the previous item; a stalk-level argument would also have needed the stalk of
a sheafified tensor product as the tensor product of the stalks, for which
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorStalkRingedSpace.lean` is the primitive, and
the containment read back through the `AddEquiv`
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkEquiv` and its
scalar compatibility `associatedModuleSheafStalkEquiv_germ_smul`. Neither is needed on sections.
The second is the ideal-sheaf submodule API
(`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` of
`StacksFrontier/AlgebraicGeometry/Modules/IdealSheafDataSubmodule.lean`),
`Stacks.AlgebraicGeometry.IdealSheafSequence.divisorIdeal_shortExact` and
`Stacks.Blowup.exists_isRegular_ideal_comap_toSpec_eq_span` of
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalCartier.lean`, which computes
`(thickeningIdeal I 1).ideal` on the chart `D₊(b⁽¹⁾)` as `Ideal.span {b}`: the ideal-sheaf step
is proved from the `⊤`-sections statement and naturality, so the chart computation is not wanted
either. It stays recorded because it is one of the two local inputs entry (2c) below needs.

Two further halves remain in the tree and are *not* needed on this route, being the
torsion-cokernel argument this replaces:
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isZero_associatedModuleSheaf_of_isIPowerTorsion`
([Stacks, Tag 0BXD]) and `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff`
of `StacksFrontier/AlgebraicGeometry/ProjSaturation/Basic.lean` ([Stacks, Tag 0BXK]). It remains
true that no statement in either tree says
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor` preserves
monomorphisms, kernels or cokernels — the eventual-bijectivity comparison is what makes that
unnecessary. The *ring-level* analogue is available —
`Stacks.AlgebraicGeometry.RelativeProjChain.isIso_projMapData_twistMap_of_eventually_bijective`,
[Stacks, Tag 07ZE] part (3).

**Chart gluing is not the route.** `Stacks.Blowup.negativeTwist'OverChartIso` compares the two
models over one chart, but both its sides are written `(…).over (chartImage I hb)`, i.e. sheaves
on the slice site, and for that spelling the library has only faithfulness
(`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`) and no amalgamation; the
gluing API that exists (`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover`,
`TopCat.Sheaf.LocalModuleHom.gluedHom`) is indexed by `Opens` or by
`AlgebraicGeometry.Scheme.Modules.restrict`. Worse, that comparison is built at a generator of
the centre obtained from an `Exists`, and two generators of a principal ideal differ by a unit,
so the overlap comparison gluing needs cannot even be stated until the generator is fixed
canonically; see `Stacks.Blowup.negativeTwist'OverChartIsoOfGen`, which makes the dependence a
parameter.

Equivalently, in the geometric spelling: a morphism `𝒪_X(1) ⟶ 𝒪_X` is a global section of
`𝒪_X(-1)`, and `Γ(X, 𝒪_X(-1))` exceeds the degree-`0` piece `S_{-1} = 0` of the shifted module
by precisely the discrepancy that comparison measures. Naming that section is the identification
`𝒪_X(1) = 𝒪_X(-Y)` of [Stacks, Tag 02OS] part (3), which the repository has only for the
ideal-sheaf model of the twists: `AlgebraicGeometry.exceptionalTwistInclusion` of
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalTwist.lean`, the inclusion
`idealPowerKernel (exceptionalIdeal ℐ) c ⟶ 𝒪`. No file in either tree mentions both
`idealPowerKernel` and a twisting sheaf, so the ideal-sheaf and `Proj`-graded models of the
twists are nowhere compared; the one place the identification appears for a graded model is a
`private` declaration inside the proof of Stacks 0B64 (twisted cohomology vanishing),
stated for the *relative*-`Proj` twists, and not available here.

**(2a) Which fields can be shed at all.** Seven of the eleven cannot, and the reason is the
*shape* of the structure rather than any missing lemma, so no search for one will help.
`div_comp`, `div_shortExact` and `div_sq_left` are properties of the data field `divα`: a proof
replacing one of them would have to hold for an arbitrary `divα`, and none of the three does
(`divα := 0` satisfies `div_comp` and no other). Likewise `base_vanishing`, `base_surjective`
and `base_ker_le` are properties of the data `q₀`, asked for `q ≥ q₀`, and `base_vanishing_gt`
of the data `d`, asked for `i > d`: replacing one would mean proving it for *every* value of
that data, i.e. at `q₀ = 0` and at `d = 0`, where each is false. Those four therefore cannot be
shed before `d` and `q₀` are pinned by definitions, which is the base-change identification of
Tag 0GA6 recorded as the fifth missing piece at the end of this register.

So exactly two fields are open to attack. `divα` is data, and constructing it sheds `div_comp`
and `div_sq_left` with it — the square
`thickeningTwistProj I n (q+1) ≫ divα n q = ambientTwistMap I q ≫ thickeningTwistProj I (n+1) q`
is what `div_sq_left` is, read on the sections coming from `I^{q+1}` through
`blowupΓMap_ambientTwistMap_ambientSections`. And `amb_shortExact` is the **only** field that is
a property of maps already constructed, hence the only one that can be shed on its own.

**(2b) The twists on `X` are invertible.**
`Stacks.Blowup.isInvertible_blowUpTwist` of
`StacksFrontier/AlgebraicGeometry/Blowup/TwistDegreeOne.lean` ([Stacks, Tag 02NS] part (2)): every
`𝒪_X(n)`, `n : ℤ`, is an invertible sheaf, because the Rees algebra is generated in degree one
over its degree-zero part (`Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top`), the
degree-one standard opens therefore cover `X`, and `𝒪_X(n)` is trivial on each of them
(`Stacks.AlgebraicGeometry.ProjDegreeOne.twistingSheafOverBasicOpenDegreeOneIsoUnit`).
`Stacks.Blowup.isFiniteLocallyFreeOfRank_one_blowUpTwist` is the same statement as finite local
freeness of rank one. Consequently `- ⊗ 𝒪_X(q)` is an *equivalence* of `X.Modules`
(`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible`), so it is exact and
carries a short exact sequence to a short exact sequence.

**(2c) `𝒪_{Yₙ} = 𝒪_X/ℐ_{Yₙ}` is proved, globally, and what is left of `amb_shortExact` is
Tag 02OS part (3) alone.** `Yₙ` is a closed subscheme of `X`, so `𝒪_X ⟶ 𝒪_{Yₙ}` is an
epimorphism — `epi_thickeningProj` below, which is [Stacks, Tag 01QO] for a closed immersion of
schemes in the spelling `Stacks.IdealSheafSequence.divisorQuotientMap_eq` supplies — and
`Stacks.IdealSheafSequence.divisorIdeal_shortExact` ([Stacks, Tag 0C6K]) at
`thickeningIdeal I n` is the short exact sequence `0 → ℐ_{Yₙ} → 𝒪_X → 𝒪_{Yₙ} → 0` itself. No
chart and no localisation is involved, and the effective-Cartier hypothesis of Tag 0C6K is not
used.

With (2b) that leaves one obligation for `amb_shortExact`: a morphism `𝒪_X(1) ⟶ ℐ_Y` which is
an **isomorphism** and which composed with `ℐ_Y ⟶ 𝒪_X` is `ambientTwistMap I 0`. That is
[Stacks, Tag 02OS] part (3), and given it the field is the sequence of the previous paragraph at
`n = 1` tensored by `𝒪_X(q)`. The morphism itself needs nothing new: `ℐ_Y` is
`kernel (thickeningProj I 1)`, so it is the kernel lift of `ambientTwistMap I 0` against the
complex condition at `q = 0`. What is open is that the lift is an isomorphism — and since both
sides are invertible, by (2b) for `𝒪_X(1)` and by
`Stacks.Divisors.isInvertible_negativeTwist` at the effective Cartier divisor
`Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec_ofIdealTop` for `ℐ_Y`, it is enough to
check it on the degree-one charts `D₊(b⁽¹⁾)`, `b ∈ I`, where `𝒪_X(1)` is trivialised by the
trivialisation named in (2b) and `(thickeningIdeal I 1).ideal` is `Ideal.span {b}` with `b`
regular by `Stacks.Blowup.exists_isRegular_ideal_comap_toSpec_eq_span`. **This is not the chart
gluing ruled out below**: nothing is glued and no generator is chosen to build anything — an
already-constructed morphism is checked locally, which `Stacks.SheafOfModules.OnSpace`'s
locality lemmas do.

That reduction is now a theorem, in the form that needs no morphism to be named:
`shortExact_ambientTwistMap_of_isIso_kernelLift` below says that the field holds at `q` as soon
as the *kernel lift* of `ambientTwistMap I q` along `thickeningTwistProj I 1 q` is an
isomorphism. So the field is one `IsIso` per `q` and nothing else, and the kernel it lands in is
the one `twistedThickeningIdealMap I 1 q` — the inclusion `ℐ_Y ⊗ 𝒪_X(q) ⟶ 𝒪_X(q)`, a
monomorphism by `mono_twistedThickeningIdealMap` — also lands in.

**(2d) The whiskering half of (2c).** `Epi (thickeningProj I n ▷ blowupTwist I q)` is not found
by instance search, and what instance search misses is only the *spelling*: the monoidal tensor
product of two morphisms at `Stacks.SheafOfModules.OnSpace.monoidal` is the canonical induced
map on sheafified tensor products **on the nose**, by
`Stacks.SheafOfModules.OnSpace.tensorHom_eq` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyFiniteFreeSummand/LeftDualOnSpace.lean`;
at a second factor which is an identity that is `whiskerRight_eq_tensorSheafMap` below, and
through it the epimorphism clause of [Stacks, Tag 01CC]
(`AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi`, an instance already) applies directly.
So `epi_whiskerRight_of_epi` and `epi_thickeningTwistProj` are theorems, and the equivalence of
(2b) is not what makes the second map surjective.

Flatness, not the equivalence, is what gives the *left* exactness of the twist: every twist is
finite locally free (`isFiniteLocallyFree_blowupTwist`, from Tag 02NS(2) through
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`) hence flat by [Stacks,
Tag 05P2] (`isFlat_blowupTwist`), and `- ⊗ 𝒪_X(q)` therefore preserves monomorphisms
(`mono_whiskerRight_blowupTwist`). With these, `twistedThickeningIdealMap` — the inclusion
`ℐ_{Yₙ} ⊗ 𝒪_X(q) ⟶ 𝒪_X(q)` — is a monomorphism killed by the restriction to the exceptional
divisor, which is an epimorphism.

What is *not* proved of the twisted ideal sequence is its exactness at the middle term, and the
obstruction is again a spelling. [Stacks, Tag 01CC]'s middle clause
`AlgebraicGeometry.SheafOfModules.tensorSheafMap_exact` applies — it accepts the short complex of
`Stacks.IdealSheafSequence.divisorIdeal_shortExact` without any transport, provided the complex
is *passed* rather than rebuilt, since rebuilding it triggers a synthesis of
`HasZeroMorphisms` at the `SheafOfModules (structureSheafRing _)` spelling which fails — but its
conclusion is a short complex whose middle object is `tensorSheaf _ (𝟙_ _) (𝒪_X(q))`, and
comparing it with `𝒪_X(q)` needs the left unitor of the monoidal structure as an `Iso`
*in that spelling*. `λ_ (blowupTwist I q)` is an `Iso` of `X.Modules`, whose `Category` instance
is `AlgebraicGeometry.Scheme.Modules.instCategory` and not `SheafOfModules.instCategory`, and the
two `Iso` types are not interchangeable: the application is rejected as a type mismatch rather
than accepted up to definitional unfolding. Closing this needs the left unitor named at the
third spelling, i.e. `Stacks.SheafOfModules.OnSpace.monoidal (blowupScheme I).toRingedSpace` as
a local instance alongside the two already here, and the comparison stated there.

Nothing above is needed for the reduction of the field itself: that is
`shortExact_ambientTwistMap_of_isIso_kernelLift`, which is pure category theory
(`shortExact_of_isIso_kernelLift`) on top of `epi_thickeningTwistProj`. The twisted ideal
sequence is what identifies the kernel the lift lands in, and so what turns the `IsIso` into
Tag 02OS(3).

**(2e) The multiplication of twists at the Rees grading is constructed, and so is the compatibility
of `twistShiftMap` with multiplication by a degree-one generator.** Both live in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/TwistShiftMultiplication.lean`.

`Stacks.Blowup.isIso_twistMultiplicationMap_reesGrading` makes
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap (reesGrading I) a b :
𝒪_X(a) ⊗ 𝒪_X(b) ⟶ 𝒪_X(a+b)` an isomorphism for all `a b : ℤ`: it is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin` at
`Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top`, the same hypothesis (2b) uses.

The compatibility is *not* stated against `twistMultiplicationMap`. The other multiplication is
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap 𝒮 i n k h a : 𝒪(n) ⟶ 𝒪(k)`,
multiplication by a single homogeneous scalar `a` of degree `i` with `i + n = k`, and with that
`Stacks.Blowup.twistShiftMap` commutes **on both sides**: for `b ∈ I` and the degree-one element
`b⁽¹⁾ = bX`, `Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap` and
`Stacks.Blowup.twistShiftMap_comp_twistScalarSheafMap_reesDegOne` say that multiplication by
`b⁽¹⁾` composed with `twistShiftMap` in either order is multiplication by `b`. That is [Stacks,
Tag 02OS] part (3) at the level of morphisms of twisting sheaves — its algebraic form on the
truncation `S₊`, `Stacks.Blowup.reesDegOne_mul_reesShift`, is available, and what lifting
it needed was the factorisation `Stacks.Blowup.reesDegOneTrunc` of multiplication by `b⁽¹⁾`
through that truncation. Two consequences are immediate: wherever multiplication by `b` is a
monomorphism on the twists, so is `twistShiftMap`; and wherever multiplication by `b⁽¹⁾` is
invertible, `twistShiftMap` is its inverse followed by multiplication by `b`.

**The reduction from all `q` to `q = 0` is open, and what it needs is three
pieces.** The instantiated multiplication gives `𝒪_X(1) ⊗ 𝒪_X(q) ≅ 𝒪_X(q+1)`;
the obstruction is that `ambientTwistMap I q` has to be `ambientTwistMap I 0` whiskered by
`𝒪_X(q)` read through that isomorphism, and `twistShiftMap` is not a scalar multiplication, so
the two-sided compatibility above does not give it directly. Composing the wanted identity with
multiplication by `b⁽¹⁾` reduces it to:

* the compatibility of `twistScalarSheafMap` with `twistMultiplicationMap`, i.e. associativity
  `(b⁽¹⁾·ς)·τ = b⁽¹⁾·(ς·τ)`. This is checkable pointwise: two morphisms out of a sheafified
  tensor product agree when they agree on local pure tensors
  (`Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext`), the multiplication of a pure
  tensor of honest sections is the pointwise product of the local values
  (`Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul`), and
  `twistScalarSheafMap` acts pointwise by `LocalizedModule.map`
  (`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafMap_app_apply`);
* that multiplication by `b⁽¹⁾` restricts to an **isomorphism** over `D₊(b⁽¹⁾)`. The
  trivialisation
  `Stacks.AlgebraicGeometry.ProjDegreeOne.twistingSheafOverBasicOpenDegreeOneIsoUnit` is there,
  but it is never compared with `twistScalarSheafMap`;
* a locality principle for an equality of morphisms,
  `Stacks.SheafOfModules.OnSpace.hom_ext_of_locally`, run over the cover by the `D₊(b⁽¹⁾)`,
  `b ∈ I`, which is `Stacks.Blowup.exists_reesDegOne_mem_primeCompl`.

None of the three is a chart gluing of the kind ruled out below: no generator is chosen to
*build* anything, and the morphisms being compared are already constructed.

**(3) Serre's theorems on `X`, [Stacks, Tag 0AG6] parts (2) and (3). Both are now theorems, and
neither is a field.**

Serre *vanishing* on an arbitrary `Proj` is indeed unavailable: it is the standing hypothesis
`Stacks.AlgebraicGeometry.ProjSerreDevissage.HasEventuallyAcyclicTwists` of this repository's
dévissage, discharged only for projective space
(`Stacks.ProjectiveSpace.SerreVanishing.hasEventuallyAcyclicTwists_polyGrading`). But that
dévissage is not the route for the blowup, and on the blowup the vanishing does not have to be
assumed: it is `Stacks.LocalCohomology.UniformityIII.amb_serre` below, which is
`Stacks.Blowup.exists_isZero_Hgroup_twistingSheaf_reesGrading` of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveSerreVanishing.lean`, transported along the
projective embedding rather than proved on `Proj(⨁ₙ Iⁿ)` directly. With `I` generated by
`x : Fin (m+1) → A` — a Noetherian `A` always supplies such a family —
`Stacks.Blowup.isClosedImmersion_blowUpSpecToProjSpace` embeds `X` in
`Proj (MvPolynomial.homogeneousSubmodule (Fin (m+1)) A)`, which is the same constant as the
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A m` the projective-space results are stated
over; `Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap` — [Stacks, Tag 01N1] part (3),
`Stacks.AlgebraicGeometry.ProjTwistMono.isIso_projMapData_twistMap`, already transported off the
domain of definition `U(ψ)` — identifies `i^*𝒪_ℙ(q)` with `𝒪_X(q)`, its hypotheses being
`Stacks.Blowup.surjective_reesPresentation` and
`Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading`;
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` ([Stacks, Tag 01E8] at a
closed immersion) rewrites `i_*𝒪_X ⊗ 𝒪_ℙ(q)` as `i_*(𝒪_X ⊗ i^*𝒪_ℙ(q))`, and the left unitor
finishes; `AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion` ([Stacks, Tag 087T])
makes `i_*𝒪_X` coherent, `𝒪_X` itself being coherent by
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit` on the locally Noetherian `X`;
`Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent`
([Stacks, Tag 01YS] part (4)) then kills `Hⁱ(ℙ, i_*𝒪_X ⊗ 𝒪_ℙ(q))` for `q` large; and
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` ([Stacks, Tag 089W]) carries that
back to `Hⁱ(X, 𝒪_X(q))` — the restriction of scalars it introduces does not change the carrier,
and only a `Subsingleton` is wanted here.

Part (3), `H⁰(X, 𝒪_X(q)) = Iᑫ` for `q ≫ 0`, used to be the field `amb_serre_sections` and is
now `Stacks.Blowup.exists_forall_bijective_ambientSections`, which clause (4) below calls for its
starting threshold. It is assembled from two halves. The injective half is
`Stacks.LocalCohomology.UniformityIII.exists_forall_injective_ambientSections`, proved for an
arbitrary Noetherian graded ring generated in degree one: by [Stacks, Tag 0BXK] a homogeneous
element with vanishing section is `𝒮₊`-power torsion, finitely many such elements generate the
rest, and in large enough degree the homogeneous coefficients of a combination lie deep enough in
`𝒮₊` to annihilate every generator. The surjective half is
`Stacks.Blowup.exists_forall_surjective_ambientSections`, which runs the embedding of the
previous paragraph on sections instead of on cohomology: the surjection
`Γ(ℙ, 𝒪_ℙ(q)) ⟶ Γ(X, 𝒪_X(q))` and the computation `Γ(ℙ, 𝒪_ℙ(q)) = (A[T₀, …, T_m])_q` are maps
out of the same group, because the projection formula read on `⊤`-sections is the adjunction
unit read on `⊤`-sections. Neither half goes through
`Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_bijective_degreeNToGlobalSections`
([Stacks, Tag 0AG7]), which is conditional on homogeneous generating data for the kernel and the
cokernel of the comparison map; that route was the one previously recorded here as the only one,
and it is not the route taken.

**(4) The remaining fields are the Situation itself, with one exception.** `base_vanishing`,
`base_surjective` and `base_ker_le` are the *definition* of `q(S)`, so they need the programme
of (3) run on `Y = Proj(Gr_I(A))` rather than on `X` — and, by (2a), they cannot be shed at all
before `q₀` is pinned; and `div_shortExact` and `amb_shortExact` are the exactness of the two
sequences, for which (2c) says what is left. The exception is `base_vanishing_gt`, Grothendieck
vanishing above the fibre dimension: that is a theorem of the source and not part of the
Situation, so it is a genuine gap rather than a hypothesis of the tag. [Stacks, Tag 02V7] is
registered in this repository only at fibre dimension zero
(`Stacks.AlgebraicGeometry.FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_zero`),
and [Stacks, Tag 0E7D], the general statement it would come from, carries that vanishing as its
own hypothesis `hstalk` outside fibre dimension zero.

**Summary.** Items (1) and (2) are settled for the *ambient* sequence, apart from its
exactness: its first map `ambα` is the theorem `ambientTwistMap`, the square `amb_sq_left` is
`blowupΓMap_ambientTwistMap_ambientSections`, and the complex condition `amb_comp` is
`ambientTwistMap_comp_thickeningTwistProj_eq_zero`, so `GeometricInput` has **eleven** fields
rather than fourteen. Tag 0GA7 is not unconditional, and what stands between is: `divα`
and the two exactness fields — the exactness ones needing the `Proj`-graded and ideal-sheaf
models of the twists compared as an *equality* of subsheaves rather than the containment that is
proved, which by (2c) is the single statement [Stacks, Tag 02OS] part (3) and nothing
besides; the three `n = 1` fields, which need the programme of (3) run on `Y`; and
`base_vanishing_gt`. Item (3) is independent of all of these: both of Serre's theorems on `X`
are theorems while the sequences are still incomplete.

For `amb_shortExact` that single statement is now *isolated in Lean* rather than only in prose:
by `shortExact_ambientTwistMap_of_isIso_kernelLift` the field follows from
`IsIso (kernel.lift (thickeningTwistProj I 1 q) (ambientTwistMap I q) _)` for each `q`, and
everything else the field asserts — the surjectivity of the second map, the exactness at the
middle, the injectivity of the first — is discharged. The field is therefore **not** shed:
`GeometricInput` still has eleven fields, and the eleventh is that family of isomorphisms. What
a `q = 0` reduction of it still needs is named in (2e), where the multiplication of twists and
the two-sided compatibility of `Stacks.Blowup.twistShiftMap` with multiplication by a
degree-one generator are proved.

By (2a) the eleven fields are not eleven independent targets. Seven of them — the three `n = 1`
fields, `base_vanishing_gt`, and the three properties `div_comp`, `div_shortExact`,
`div_sq_left` of `divα` — are properties of the *data* fields `q₀`, `d` and `divα`, and no
theorem can replace one of them while that data is a field. The two targets are `divα`, whose
construction would shed `div_comp` and `div_sq_left` with it, and `amb_shortExact`, the only
field that is a property of maps this file has already built.

The integers `d` and `q₀` are fields of `GeometricInput`, pinned by the properties that *define*
`d(S)` and `q(S)`, read on `X`. Identifying them with `AssociatedGraded.dInvariant` and
`AssociatedGraded.qInvariant` of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/AssociatedGradedInvariants.lean`, which are read
off `Y = Proj(Gr_I(A))`, is the base-change identification `Y = X ×_{Spec A} Spec(A/I)` of
Tag 0GA6; that identification is **not** proved here either, and is the fifth missing piece of
the Situation, independent of the four above.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGlobalSections degreeSection)

universe u
universe v w

namespace Stacks.LocalCohomology.UniformityIII

section Objects

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
  sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

section AmbComp

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

open AlgebraicGeometry.ProjectiveSpectrum.Proj (structureSheaf)
open Stacks.SheafOfModules.OnSpace (tensorObjTmul unitSection sheaf_comp_app_apply
  leftUnitor_inv_apply whiskerRight_tmul tensorObjTmul_app_one_smul_eq_zero
  tensorObjTmul_eq_zero_of_locally)

/-- **The value of a pulled-back coefficient at a point of the blowup**: the global section of
`𝒪_X` that `b : A` gives along the blowup morphism has the constant fraction `b/1` as its value
at every point.

`Stacks.Blowup.toSpec` is `AlgebraicGeometry.Proj.toSpecZero` followed by `Spec` of the
identification of `A` with the degree-zero part of the Rees algebra, so this is
`Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val` read through
`SetLike.GradeZero.coe_algebraMap`. It is what feeds the scalar hypothesis of the local
factorisation, which takes its scalar as a parameter constrained only by its values. -/
theorem val_appTop_toSpec (b : A) (x : ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I)) :
    HomogeneousLocalization.val
        (((Stacks.Blowup.toSpec I).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)).1 ⟨x, trivial⟩) =
      algebraMap (reesAlgebra I) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        ((Stacks.Blowup.reesConst I b : reesAlgebra I)) := by
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Stacks.Blowup.toSpec I).appTop =
      CommRingCat.ofHom (Stacks.Blowup.reesGradingZeroEquiv I).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Stacks.Blowup.reesGrading I 0))).inv ≫
          (Proj.toSpecZero (Stacks.Blowup.reesGrading I)).appTop :=
    (Scheme.ΓSpecIso_inv_naturality_assoc
      (CommRingCat.ofHom (Stacks.Blowup.reesGradingZeroEquiv I).toRingHom)
      (Proj.toSpecZero (Stacks.Blowup.reesGrading I)).appTop).symm
  refine Eq.trans (congrArg (fun z : Γ(blowupScheme I, ⊤) =>
      HomogeneousLocalization.val (z.1 ⟨x, trivial⟩))
    (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hcomp) b)) ?_
  refine (Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val
    (Stacks.Blowup.reesGrading I) (Stacks.Blowup.reesGradingZeroEquiv I b) x).trans ?_
  refine congrArg (algebraMap (reesAlgebra I)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)) ?_
  change ((algebraMap A (Stacks.Blowup.reesGrading I 0) b :
    Stacks.Blowup.reesGrading I 0) : reesAlgebra I) = _
  rw [SetLike.GradeZero.coe_algebraMap]

/-- The section `𝒪_X ⟶ 𝒪_{Yₙ}` of `1` restricts to the section of `1`. This is the left factor
of the pure tensor below, and the only thing needed about it is that restriction does not move
it. -/
theorem map_app_thickeningProj_one (n : ℕ) {U V : (blowupScheme I).Opens} (hV : V ≤ U) :
    ((thickeningSheaf I n).val.map (homOfLE hV).op).hom
        (((thickeningProj I n).val.app (op U)).hom
          (1 : (blowupScheme I).ringCatSheaf.obj.obj (op U))) =
      ((thickeningProj I n).val.app (op V)).hom
        (1 : (blowupScheme I).ringCatSheaf.obj.obj (op V)) :=
  (PresheafOfModules.naturality_apply (thickeningProj I n).val (homOfLE hV).op
      (1 : (blowupScheme I).ringCatSheaf.obj.obj (op U))).symm.trans
    (congrArg (fun z : (SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.obj (op V) =>
        ((thickeningProj I n).val.app (op V)).hom z)
      (PresheafOfModules.unit_map_one (blowupScheme I).ringCatSheaf.obj (homOfLE hV).op))

/-- Restriction along `V ≤ U` preserves vanishing under `𝒪_X ⟶ 𝒪_{Y₁}`: this is naturality of
`thickeningProj` and the fact that restriction is additive. -/
private theorem app_thickeningProj_one_map_eq_zero
    {U V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I))} (hV : V ≤ U)
    {s : (SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.obj (op U)}
    (hs : ((thickeningProj I 1).val.app (op U)) s = 0) :
    ((thickeningProj I 1).val.app (op V))
        (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map (homOfLE hV).op) s) = 0 :=
  (PresheafOfModules.naturality_apply (thickeningProj I 1).val (homOfLE hV).op s).trans
    ((congrArg ((thickeningSheaf I 1).val.map (homOfLE hV).op) hs).trans
      (map_zero ((thickeningSheaf I 1).val.map (homOfLE hV).op).hom))

/-- **`I` kills `𝒪_{Y₁}` on every open.** `app_top_thickeningProj_one_eq_zero` says the global
function pulled back from `b ∈ I` is zero on the exceptional divisor; this is its restriction to
an arbitrary open, and it is naturality of `thickeningProj` and nothing else. -/
theorem app_thickeningProj_one_restrict_eq_zero {b : A} (hb : b ∈ I)
    (V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I))) :
    ((thickeningProj I 1).val.app (op V))
        (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map
            (homOfLE (le_top : V ≤ ⊤)).op)
          ((Stacks.Blowup.toSpec I).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b))) = 0 :=
  app_thickeningProj_one_map_eq_zero I le_top (app_top_thickeningProj_one_eq_zero I hb)

/-- `app_thickeningProj_one_restrict_eq_zero` with the restriction performed in two steps,
`⊤ ≥ U ≥ V`. This is the spelling the local factorisation produces: its scalar is a section over
`U` and its conclusion restricts that section along `V ≤ U`. -/
theorem app_thickeningProj_one_map_restrict_eq_zero {b : A} (hb : b ∈ I)
    {U V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I))} (hV : V ≤ U) :
    ((thickeningProj I 1).val.app (op V))
        (((structureSheaf (Stacks.Blowup.reesGrading I)).obj.map (homOfLE hV).op)
          (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map
              (homOfLE (le_top : U ≤ ⊤)).op)
            ((Stacks.Blowup.toSpec I).appTop.hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)))) = 0 :=
  app_thickeningProj_one_map_eq_zero I hV (app_thickeningProj_one_restrict_eq_zero I hb U)

/-- **The canonical map `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)` on a local section is a pure tensor** whose left
factor is the image of `1`. `thickeningTwistProj` is the inverse left unitor followed by a right
whiskering, so this is `Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply` followed by
`Stacks.SheafOfModules.OnSpace.whiskerRight_tmul`, chained by `congrArg` in term mode: a `rw`
does not fire, the whiskering's source object being written at the `ULift` spelling on which
`Stacks.SheafOfModules.OnSpace.monoidal` is transported.

A left factor which is the image of `1` is one a scalar can move onto, by
`Stacks.SheafOfModules.smul_app_one`; that is why the composite is evaluated this way rather than
reduced through the interchange identity `ambientTwistMap_comp_thickeningTwistProj`. -/
theorem app_thickeningTwistProj (n q : ℕ) (U : (Opens (blowupScheme I).carrier)ᵒᵖ)
    (z : (blowupTwist I q).val.obj U) :
    ((thickeningTwistProj I n q).val.app U) z =
      tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I n) (blowupTwist I q) U
        (((thickeningProj I n).val.app U)
          (1 : (blowupScheme I).ringCatSheaf.obj.obj U)) z :=
  (sheaf_comp_app_apply (blowupScheme I).toRingedSpace (λ_ (blowupTwist I q)).inv
      (thickeningProj I n ▷ blowupTwist I q) U z).trans
    ((congrArg (fun w : (𝟙_ ((blowupScheme I).Modules) ⊗ blowupTwist I q).val.obj U =>
        ((thickeningProj I n ▷ blowupTwist I q).val.app U) w)
      (leftUnitor_inv_apply (blowupScheme I).toRingedSpace (blowupTwist I q) U z)).trans
      (whiskerRight_tmul (blowupScheme I).toRingedSpace (thickeningProj I n)
        (blowupTwist I q) U (unitSection (blowupScheme I).toRingedSpace U 1) z))

/-- **The pure tensor of the second sequence vanishes where the right factor factors.** If the
restriction of a section of `𝒪_X(q)` to `V` is `r·c` for a scalar `r` killed by
`𝒪_X ⟶ 𝒪_{Y₁}`, then the pure tensor of the restricted image of `1` with that restriction is
zero: the scalar moves across the tensor onto the left factor, where it is the image of itself.

The scalar is a parameter with its value given by a hypothesis rather than written out. Written
out, the restriction `(…).obj.map i r` has to be elaborated against the module structure of the
tensor factor, and the `HSMul` instance is then not found — the target of
`PresheafOfModules.map` is wrapped in `ModuleCat.restrictScalars`, and here, unlike in
`Stacks.Blowup.map_eq_smul_of_pointwise`, the carrier is reached only through the `def`
`AlgebraicGeometry.Scheme.Modules`, which instance search does not unfold. With the scalar a
variable the instance is found and the two spellings meet once, at an application. -/
theorem tensorObjTmul_app_one_eq_zero_of_restrict_eq_smul (q : ℕ)
    {U V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I))} (hV : V ≤ U)
    (r : (blowupScheme I).ringCatSheaf.obj.obj (op V))
    (z : (blowupTwist I q).val.obj (op U)) (c : (blowupTwist I q).val.obj (op V))
    (hc : (((blowupTwist I q).val.map (homOfLE hV).op) z :
        (blowupTwist I q).val.obj (op V)) = r • c)
    (hr : ((thickeningProj I 1).val.app (op V)) r = 0) :
    tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I 1) (blowupTwist I q) (op V)
        (((thickeningSheaf I 1).val.map (homOfLE hV).op)
          (((thickeningProj I 1).val.app (op U))
            (1 : (blowupScheme I).ringCatSheaf.obj.obj (op U))))
        (((blowupTwist I q).val.map (homOfLE hV).op) z) = 0 :=
  (congrArg₂ (tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I 1)
      (blowupTwist I q) (op V)) (map_app_thickeningProj_one I 1 hV) hc).trans
    (tensorObjTmul_app_one_smul_eq_zero (blowupScheme I).toRingedSpace (blowupTwist I q)
      (thickeningProj I 1) (op V) _ c hr)

/-- **Near every point the pure tensor of the second sequence vanishes.** The degree-one standard
opens `D₊(b⁽¹⁾)`, `b ∈ I`, cover the blowup, so at any point there is a `b ∈ I` with `b⁽¹⁾`
invertible there (`Stacks.Blowup.exists_reesDegOne_mem_primeCompl`); near that point the image of
a section of `𝒪_X(q+1)` is `b·` a section of `𝒪_X(q)`
(`Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`), the scalar being the pullback of `b`,
whose values `val_appTop_toSpec` supplies; and that scalar is killed by `𝒪_X ⟶ 𝒪_{Y₁}`
(`app_thickeningProj_one_map_restrict_eq_zero`). -/
theorem exists_tensorObjTmul_app_one_eq_zero (q : ℕ)
    (U : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I)))
    (z : (blowupTwist I (q + 1)).val.obj (op U))
    (x : ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I)) (hx : x ∈ U) :
    ∃ (V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I))) (hV : V ≤ U), x ∈ V ∧
      tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I 1) (blowupTwist I q) (op V)
        (((thickeningSheaf I 1).val.map (homOfLE hV).op)
          (((thickeningProj I 1).val.app (op U))
            (1 : (blowupScheme I).ringCatSheaf.obj.obj (op U))))
        (((blowupTwist I q).val.map (homOfLE hV).op)
          (((ambientTwistMap I q).val.app (op U)) z)) = 0 := by
  refine (Stacks.Blowup.exists_reesDegOne_mem_primeCompl I x).elim
    fun b h => h.elim fun hb hbx => ?_
  refine (Stacks.Blowup.exists_restrict_appTwistShift_eq_smul I (q : ℤ) U z x hx hb hbx
      (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map
          (homOfLE (le_top : U ≤ ⊤)).op)
        ((Stacks.Blowup.toSpec I).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)))
      (fun y => val_appTop_toSpec I b y.1)).elim fun V h => h.elim fun hV h =>
    h.2.elim fun c hc => ⟨V, hV, h.1, ?_⟩
  refine tensorObjTmul_app_one_eq_zero_of_restrict_eq_smul I q hV _
    (((ambientTwistMap I q).val.app (op U)) z) c ?_
    (app_thickeningProj_one_map_restrict_eq_zero I hb hV)
  refine Eq.trans (congrArg (fun w : (blowupTwist I q).val.obj (op U) =>
    (((blowupTwist I q).val.map (homOfLE hV).op) w :
      (blowupTwist I q).val.obj (op V)))
    ((Stacks.Blowup.appTwistShift_eq I (q : ℤ) (op U) z).symm)) hc

/-- **The second sequence of [Stacks, Tag 0GA7] is a complex**, which was the field `amb_comp`
of `GeometricInput`: the composite `𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q)` is zero.

Evaluated on a local section the composite is, by `app_thickeningTwistProj`, the pure tensor of
`𝒪_X ⟶ 𝒪_{Y₁}` applied to `1` with the image of the section, and
`exists_tensorObjTmul_app_one_eq_zero` kills that pure tensor near every point of the open. The
sections of the sheafified tensor product form a sheaf, so a local pure tensor vanishing near
every point vanishes (`Stacks.SheafOfModules.OnSpace.tensorObjTmul_eq_zero_of_locally`), and a
morphism of sheaves of modules which is zero on every section is zero.

This is the route the obstruction register above prescribes, and not the reduction through the
interchange identity `ambientTwistMap_comp_thickeningTwistProj`: the `◁` vanishing
`∀ q, thickeningSheaf I 1 ◁ ambientTwistMap I q = 0` is strictly stronger and remains open. -/
theorem ambientTwistMap_comp_thickeningTwistProj_eq_zero (q : ℕ) :
    ambientTwistMap I q ≫ thickeningTwistProj I 1 q = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
  refine Eq.trans (sheaf_comp_app_apply (blowupScheme I).toRingedSpace (ambientTwistMap I q)
    (thickeningTwistProj I 1 q) U z) ?_
  refine Eq.trans (app_thickeningTwistProj I 1 q U ((ambientTwistMap I q).val.app U z)) ?_
  refine Eq.trans (tensorObjTmul_eq_zero_of_locally (blowupScheme I).toRingedSpace
    (thickeningSheaf I 1) (blowupTwist I q) U.unop _ _ (fun x hx =>
      exists_tensorObjTmul_app_one_eq_zero I q U.unop z x hx)) ?_
  refine Eq.symm ?_
  change ((0 : (blowupTwist I (q + 1)).val ⟶ (thickeningTwist I 1 q).val).app U).hom z = 0
  simp

end AmbComp

end Objects

end Stacks.LocalCohomology.UniformityIII

end
