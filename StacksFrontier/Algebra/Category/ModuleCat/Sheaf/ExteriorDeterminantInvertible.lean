module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseInvertibleDescent
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant of a flat sheaf of modules of finite presentation, with flatness as a sheaf

Let `(X, O_X)` be a ringed space and `F` a flat sheaf of `O_X`-modules of finite presentation.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraDeterminant` builds the determinant
`det(F) ⊆ ⋀(F)` as the direct sum over the degrees of the annihilators of the degree-one part,
and `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorStalk` identifies each of
its stalks with the determinant line of the corresponding stalk of `F`, hence proves that every
stalk of `det(F)` is an invertible module. Both of those files take flatness in its *stalkwise*
form, as a hypothesis `∀ x, Module.Flat O_{X,x} F_x`.

This file removes that hypothesis. Flatness of a sheaf of modules is
`AlgebraicGeometry.SheafOfModules.IsFlat`, exactness of tensoring by it, and Tag 05NE
(`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`) identifies it with stalkwise
flatness; `Stacks.SheafOfModules.flat_stalk_of_isFlat` below is that identification transported
to the spellings the determinant development uses. So the only hypotheses left on Tag 0FJN
here are `F` flat, `F` of finite presentation, and the one gap named in the implementation
notes, the finite presentation of `det(F)`.

It also proves that the inclusion `det(F) ⟶ ⋀(F)` is a monomorphism, through a general
statement about coproducts of monomorphisms of sheaves of modules on a space.

## Main results

* `SheafOfModules.mono_sigmaMap_of_injective_stalkMapL`: **an `ℕ`-indexed coproduct of
  morphisms of sheaves of modules on a space is a monomorphism as soon as each summand is
  injective on every stalk.** The stalk of the coproduct is the direct sum of the stalks
  (Tag 01AH), on which the coproduct of the morphisms acts summandwise.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantι_mono`: **the inclusion
  `det(F) ⟶ ⋀(F)` is a monomorphism.**
* `Stacks.SheafOfModules.flat_stalk_of_isFlat`: **Tag 05NE in the spellings of the determinant
  development** — a flat sheaf of modules on a ringed space has flat stalks, for the module
  structure `Stacks.SheafOfModules.stalkModule`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_stalk_invertible_of_isFlat`:
  every stalk of `det(F)` is an invertible module, for `F` flat of finite presentation.
Tag 0FJN itself is not stated in this file. Nothing in it is assumed about `det(F)`: the
finite presentation of `det(F)`, which the source does not assume, is
`SheafOfModules.TensorExteriorSymmetricAlgebras.isFinitePresentation_determinant_of_isFlat`, and
the tag is carried by
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_isInvertible_of_isFlat` beside it,
both in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DeterminantFinitePresentationFlat.lean`.
That statement lives there rather than here because this file cannot import
the one that proves the finite presentation: the closure of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact`, which that proof needs,
makes `HasCoproduct` unsynthesizable in the coproduct section of this file. The two are
incompatible for reasons that have nothing to do with the determinant.

## Implementation notes

**What the finite presentation of `det(F)` took, and the route that gave it.** It was the one
hypothesis this file carried that is about `det(F)` rather than about `F`, and it is now proved —
but by the rank-idempotent route of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DeterminantFinitePresentationFlat.lean`, which
presents `det(F)` finitely on a trivialising open directly, and *not* by the source's route
through the local description `det(F)|_U ≅ ℱ_{det M}`. The record below of what the source's own
route has and still owes is therefore about that route, which remains unfinished and is no
longer needed for the tag:

* `A.determinant.IsFinitePresentation`. The source gets this from the local description
  `det(F)|_U ≅ F_{det M}` obtained from the local direct-summand form of flat modules of finite
  presentation (Tag 08BL,
  `Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_isFlat_of_isFinitePresentation`, in
  `LocallyFiniteFreeSummand/FlatFinitePresentation.lean`) together with the associated-sheaf
  comparison of Tag 01BH. Nothing here does that; the paragraph **What the source's route has**
  below says which of its steps the repository now carries. The *locality* of
  finite presentation, which is the only other thing that route needs, is in the repository and
  is
  public — `Stacks.SheafOfModules.isFinitePresentation_of_coversTop` in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleFinitePresentation.lean` — so this
  hypothesis reduces entirely to the local description. Note that 08BL is stated at a different
  spelling of the sheaf of rings than this development uses, and that the difference is not
  nothing: see step 1 below.

The passage from invertible stalks to an invertible sheaf, for modules of finite presentation,
is also **not assumed**: it is
`Stacks.SheafOfModules.stalkwiseInvertibleDescent`, proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkwiseInvertibleDescent.lean`, and this
statement now discharges it there. Two things about it are worth noting. The
unrestricted statement is **false** — that file carries the counterexample, a two-point space
whose restriction map is zero — so the restriction to modules of finite presentation is doing
real work. And it is **not** implied by the locality of invertibility
(`Stacks.SheafOfModules.invertibleIsLocal_ringedSpace`): that descends invertibility along a
covering, whereas this descends it from the stalks, and `Module.Invertible O_x M_x` is the
bijectivity of a contraction rather than a trivialization, so no generator can be lifted and
the covering the local statement consumes is never produced.

**What the source's route has.** The source does not prove `det(F)` of finite presentation and
then descend from the stalks; it shows `det(F)|_U ≅ F_{det M}` on a trivialising open and
concludes because `det(F)` is then locally the pullback of an invertible module along
`X → ({*}, R)`, and invertibility is local. **That last step — the locality of invertibility —
is now proved**, `Stacks.SheafOfModules.invertibleIsLocal_ringedSpace` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalSpace.lean`; see step 4 below.
**The step the route concludes with is proved too**:
`Stacks.AssociatedSheaf.isInvertible_associatedSheaf`
(`StacksFrontier/Topology/Sheaves/Modules/AssociatedSheaf/Tensor.lean`) says that `ℱ_N` is an
invertible sheaf of modules whenever `N` is an invertible module, which is what makes
`det(F)|_U ≅ ℱ_{det M}` worth having; it rests on construction (3) being monoidal on an
arbitrary ringed space, `associatedSheafTensorIso` and `associatedSheafUnitIso` in the same
file. Four further inputs of the route are also in the repository:

* `Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat`
  (`StacksFrontier/Topology/Sheaves/Modules/AssociatedSheaf/FreeRetract.lean`) is the trivialising
  open itself: Tag 08BL in the form this argument consumes it, giving `F|_U ≅ ℱ_M` for a finite
  projective `𝒪_X(U)`-module `M`. See step 3 below for its shape and for what it does *not*
  need.
* `ProjectiveDeterminant.submoduleRetract`
  (`StacksFrontier/Algebra/Module/Projective/Determinant/Summand.lean`) exhibits the determinant
  line as a **direct summand** of the exterior algebra, which is what makes `ℱ_{det M}` a
  subsheaf of `ℱ_{⋀ M}`: construction (3) carries a split injection, and only a split
  injection, to a monomorphism.
* `Stacks.AssociatedSheaf.exteriorPowerIso`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerAssociatedSheaf.lean`) is
  `ℱ_{⋀ⁿ_R M} ≅ ⋀ⁿ(ℱ_M)` on an **arbitrary** ringed space, for an arbitrary bundle of algebras
  on `ℱ_M`. It is the ringed-space form of the exterior-power clause of Tag 01I8, whose two
  legs — the presheaf-level base change
  `AlgebraicGeometry.specTildeExteriorPowerPresheafIso` and the presheaf-model form of Tag 01CG,
  `SheafOfModules.presheafModelExteriorPowerIso` — were already stated in that generality.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_iff_of_generatesBelow`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAnnihilatorGenerated.lean`) is the
  step the source marks as having details omitted — *annihilators cannot be defined as the
  sheafification of taking annihilators on sections over opens*. For `F` generated below `U` by
  a family of sections over `U`, which is what 08BL's retraction off `O_U^{⊕n}` supplies, the
  annihilator condition over all arrows out of `U` collapses to annihilation by that family
  over `U` itself.

**What that route still needs.** Four steps stand between those inputs and `det(F)` itself. The
second is settled, the fourth — the locality of invertibility — is proved, the first is not
vacuous but is a spelling matter rather than mathematics, and the third, the assembly, is the
long one and the only one left. Step 3 lists what the assembly still needs: two pieces, and they
are independent of one another.

1. *The spelling of 08BL's sheaf of rings.* **This is not vacuous.** Tag 08BL
   (`Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_isFlat_of_isFinitePresentation`, in
   `LocallyFiniteFreeSummand/FlatFinitePresentation.lean`), construction (3) and
   `Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat` index their sheaves of
   modules by `structureSheafRing X`, while the determinant development indexes them by
   `structureSheafRing X`. The two are definitionally equal, but they are **not** interchangeable
   in a statement, for a reason that is not transparency:
   `SheafOfModules.TensorExteriorSymmetricAlgebras` is indexed by
   `CategoryTheory.Sheaf.toRingCat J Osharp` with `Osharp` to be found by unification, and
   `structureSheafRing X` is an application of `toRingCat` whereas `structureSheafRing X` is an
   anonymous constructor, so no amount of unfolding makes the latter unify —
   `TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier) G` simply fails to
   elaborate for `G : SheafOfModules (structureSheafRing Y)`. That is why the statements in the
   `RingedSpace` sections below are written at `structureSheafRing Y`, and it is also why instance
   synthesis does not carry `G.IsFinitePresentation` across: it has to be passed by name, which is
   how `exists_isDirectSummandOfFiniteFree_restrict_of_isFlat` (in
   `Stacks.Cohomology.OpcyclesFiniteFreeSummand`) consumes 08BL and how
   `SheafOfModules.TensorExteriorSymmetricAlgebras.nonempty_ringedSpaceDeterminantStalkEquiv`
   consumes the determinant. The one statement here that is stated at `structureSheafRing`,
   `Stacks.SheafOfModules.flat_stalk_of_isFlat`, is the bridge: it is 08BL's spelling, and it
   applies to a `structureSheafRing`-indexed sheaf of modules because that use is a type ascription
   rather than a unification against `toRingCat`.

2. *The base change of the determinant,* `det(M) ⊗_R S = det(M ⊗_R S)`, which the source cites
   alongside the annihilator description. **This step is done.** The annihilator half of Tag
   0FJA is `ProjectiveDeterminant.determinant_submodule_eq_annihilator`
   (`StacksFrontier/Algebra/Module/Projective/Determinant/Basic.lean`); the base-change half is
   `ProjectiveDeterminant.baseChangeEquiv`
   (`StacksFrontier/Algebra/Module/Projective/Determinant/BaseChange.lean`), the comparison
   `A ⊗_R det(M) ≃ det(A ⊗_R M)` for `M` finite projective, with no flatness hypothesis on
   `A`. The form the assembly consumes is the **degreewise** one,
   `ProjectiveDeterminant.component_baseChange_map`: the base-change comparison of exterior
   algebras carries the `n`-th rank-stratum summand of `det(A ⊗_R M)` onto the base change of
   the `n`-th summand of `det(M)`. Three further degreewise statements accompany it, all needed
   because the sheaf-level determinant is graded while Tag 0FJA is not:
   `ProjectiveDeterminant.component_eq_exteriorPower_inf_annihilator`
   (`StacksFrontier/Algebra/Module/Projective/Determinant/Graded.lean`), the degreewise form of
   Tag 0FJA; `ProjectiveDeterminant.map_annihilatorPart_eq_component` in the same file, which is
   that statement written at the spelling `Stacks.ExteriorAnnihilator.part` is **defined** at,
   so it applies to `part R M n` with no transport; and
   `ProjectiveDeterminant.annihilatorPart_baseChange_map`, the base change of that submodule,
   which is the module-level input to `annₙ(F|_U) ≅ ℱ_{partₙ(det M)}`. The base-change
   comparison of exterior algebras all of this runs through is **not** missing from the
   repository: it is `ExteriorAlgebra.exists_algEquiv_baseChange`
   (`StacksFrontier/RingTheory/TensorAlgebra/Localization.lean`), tagged 0C6F (3), and
  `StacksFrontier/Algebra/Module/Projective/Determinant/Basic.lean` already imports and uses it.
  The three degreewise statements are
   kept in the module-level tree rather than beside `part`, which is where they are consumed,
   because their content involves no sheaf.

3. *The assembly.* `det(F)` is `∐ₙ (A.exteriorAnnihilator n)`, so the local description has to
   be built degreewise and summed: `annₙ(F|_U) ≅ ℱ_{part ₙ(det M)}` for each `n`, with
   `Stacks.ExteriorAnnihilator.part` the degreewise piece of the annihilator, and then the
   commutation of construction (3) with the direct sum. `exteriorPowerIso` supplies
   `(⋀ⁿF)|_U ≅ ℱ_{⋀ⁿM}` and `isExteriorAnnihilated_iff_of_generatesBelow` cuts the annihilator
   condition over `U` down to the generating family, whose `GeneratesBelow` hypothesis 08BL's
   retraction supplies — a split epimorphism is surjective on sections, not merely locally so.
   This is the long step. It would also give the finite presentation of `det(F)` — finite
   presentation of a sheaf of modules is by definition local, and the determinant of a finite
   projective module is invertible (`ProjectiveDeterminant.invertible`) hence of finite
   presentation — but that is now proved another way, by the rank idempotents, so this step is no
   longer on the path to Tag 0FJN.

   The four inputs this step needs are all available:

   * **`F|_U ≅ ℱ_M` for a finite projective `𝒪(U)`-module `M`.** **This is done**, as
     `Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat`
     (`StacksFrontier/Topology/Sheaves/Modules/AssociatedSheaf/FreeRetract.lean`): it takes exactly
     Tag 08BL's hypotheses and a point of the space, and gives an open `U` around it, a module
     `M` over `𝒪_X(U)` carrying `Module.Finite` and `Module.Projective`, and `F|_U ≅ ℱ_M`, the
     module being `Γ(U, F)` itself.

     Producing `M` does not require reading the retraction's idempotent off
     `End(SheafOfModules.free (ULift (Fin n)))`: no idempotent is named in the proof and no
     matrix description is used. The *unit* of the adjunction of Tag 01BH(4) is an isomorphism at a
     finite free module, because `Stacks.SheafOfModules.freeSectionsIso` computes the sections
     of a finite free sheaf of modules as tuples and
     `Stacks.AssociatedSheaf.freeIsoAssociatedSheaf` identifies that sheaf with `ℱ_{R^I}`; the
     triangle identity then makes the *counit* an isomorphism at `ℱ_{R^n}` hence at `𝒪^{⊕n}`;
     being a counit-isomorphism passes to retracts, with the inverse read off the retraction;
     and the counit at `F` *is* the comparison `ℱ_{Γ(U,F)} ≅ F`. Applying global sections to
     08BL's retraction exhibits `Γ(U, F)` as a direct summand of `𝒪_X(U)^n`, hence finite and
     projective. The statement is given on the **restricted ringed space** `U` rather than on
     the slice site over `U`, and that is forced rather than chosen: construction (3) takes a
     ring map into the sections over a *terminal* object, so `ℱ_M` cannot be written on the
     slice site at all. The slice-site form is
     `Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_retract_free_over`.
   * **Construction (3) carries a direct summand to a subsheaf**, so that
     `ℱ_{partₙ(det M)} ⟶ ℱ_{⋀ⁿ M}` is a monomorphism. **Construction (3) does not carry an
     arbitrary submodule to the corresponding subsheaf.** `ℱ_M` is
     base change `M ↦ 𝒪_X(V) ⊗_R M` followed by sheafification; sheafification is exact, but
     base change along `R → 𝒪_X(V)` carries an injection to an injection only when the
     injection splits or `𝒪_X(V)` is flat over `R`, and on the stalks, where monomorphy of a
     morphism of sheaves of modules is detected, the map is `𝒪_x ⊗_R M' → 𝒪_x ⊗_R M`. The true
     form is proved: `Stacks.AssociatedSheaf.isSplitMono_associatedSheafFunctor_map` and
     `mono_associatedSheafFunctor_map` carry a `CategoryTheory.Retract` of modules to a split
     monomorphism of sheaves of modules.

     That suffices here, because the determinant line **is** a direct summand of the exterior
     algebra, and that is now proved too: `ProjectiveDeterminant.submoduleRetract`, with the
     degreewise forms `ProjectiveDeterminant.componentRetract` and
     `componentRetractExteriorAlgebra`
     (`StacksFrontier/Algebra/Module/Projective/Determinant/Summand.lean`). The projection is the
     degreewise projection of the internal grading `ExteriorAlgebra.gradedAlgebra` followed by
     multiplication by the rank idempotent, summed over the finitely many degrees whose rank
     strata cover `Spec R`; on `component R M n` the `n`-th term is the identity, because the
     idempotent acts as the identity there, and the others vanish for reasons of degree.
   * **Construction (3) commutes with the `ℕ`-indexed coproduct.** This one is available:
     `Stacks.AssociatedSheaf.coproductIso`
     (`StacksFrontier/Topology/Sheaves/Modules/AssociatedSheaf/Coproduct.lean`) instantiates clause
     (2) of Tag 01BH, `preservesColimitsOfSize_associatedSheafFunctor`, at a coproduct, which is
     the shape `det(F)` is built at.
   * **`ℱ_N` of finite presentation for `N` finite projective.** Available by composition:
     `Stacks.AssociatedSheaf.associatedSheaf_isFinitePresentation` wants
     `Module.FinitePresentation`, which `Module.finitePresentation_of_projective` supplies.

   One further input the assembly needs, the restriction of the degreewise annihilators to the
   trivialising open, is also available now. `det(F)` is the coproduct of the *submodules*
   `A.exteriorAnnihilator n`; the coproduct restricts to a slice site by
   `SheafOfModules.overSigmaIso` composed with `SheafOfModules.sigmaShrinkIso`
   (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/QuasicoherentGradedCoprod.lean`, the shrink
   being needed because `overSigmaIso` indexes by the module universe while `det(F)` is indexed
   by `ℕ`), and the submodules restrict by `SheafOfModules.Submodule.over`
   (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SubmoduleOver.lean`), whose
   `over_toSheafOfModules` says that restricting a submodule and then taking its sheaf of
   modules gives the same sheaf of modules as the other order — on the nose, since restriction
   to a slice site only reindexes.

   The `GeneratesBelow` hypothesis of `isExteriorAnnihilated_iff_of_generatesBelow` is also
   discharged now, by `Stacks.SheafOfModules.generatesBelow_of_retract`
   (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GeneratesBelowFreeRetract.lean`), directly
   from 08BL's retract and on an arbitrary site: the retraction is a split epimorphism, hence
   surjective on sections over *every* object and not merely locally so, and the tautological
   sections of a finite free sheaf of modules are global, so their images generate. Since the
   retract and the annihilator condition for `det(F|_U)` are both read on the slice site over
   `U`, applying it there needs no translation between the two sites.

   **What the assembly still needs.** Of the five pieces of this step, three are proved and two
   remain. The two are independent of one another, and neither is a lemma.

   * **The determinant across the restriction to a slice site. This is proved.**
     `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantOverIso`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SliceDeterminant.lean`) is
     `det(F)|_U ≅ det(F|_U)` on an arbitrary site, for `B` any bundle of algebras of `F|_U` on
     the slice site — `SheafOfModules.algebras (J.over U) (F.over U)`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/AlgebraBundleStalk.lean`) supplies one on an
     arbitrary site. It rests on
     `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAnnihilatorOverIso`, the degreewise
     statement, which is the content; the sum over the degrees is then the restriction functor
     preserving the `ℕ`-indexed coproduct, which it does because it is a left adjoint. The only
     hypothesis the sum adds is `HasBinaryProducts C`, which is where the right adjoint
     `Over.star U` lives and which the site of opens of a space has.

     What made the degreewise statement possible is
     `SheafOfModules.isExteriorAlgebra_over` with
     `SheafOfModules.exteriorOverIso_generator`, `exteriorOverIso_mul` and `exteriorOverIso_one`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SliceExteriorAlgebra.lean`): the restriction
     of an exterior algebra of `F` is an exterior algebra of `F|_U` *with its algebra
     structure*, so the comparison of the restricted exterior powers with `B`'s carries the
     generator and the multiplication, which is exactly what `IsExteriorAnnihilated` is phrased
     in. These are the slice-site analogues of `exteriorAlgebraIso_generator` and of
     `exteriorAlgebraIso_mul`, and they are the whole of what is needed:
     `Stacks.SheafOfModules.exteriorPowerOverIso`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SlicePowerRestriction.lean`) compares
     `(⋀ⁿ F)|_U` with `⋀ⁿ(F|_U)` but is built from the two universal properties and carries
     neither compatibility, which is why it cannot be used for the annihilator.

    **Transporting `A` instead of building `B` does not work.**
    `SheafOfModules.GradedAlgebra.IsExteriorAlgebra` is
     `IsUniversal (fun _ κ => SquareZero κ)`, a universal property quantified over *every*
     graded algebra on the site. The restriction of `A.exterior` to `J.over U` therefore does
     not inherit it from `A` by formal nonsense: that would need the direct image along the
     localization to carry a graded algebra on `J.over U` back to one on `J`, compatibly with
     the multiplications, and nothing does. `isExteriorAlgebra_over` instead compares both sides
     through the model they are built from — the degreewise sheafification of the sectionwise
     exterior power — where the comparison is componentwise the identity.

     The degreewise statement cannot be the equality
     `(A.exteriorAnnihilator n).over U = B.exteriorAnnihilator n`, which is not type-correct: the
     two sides are submodules of
     different sheaves of modules — `(A.exteriorPower n).over U` and `B.exteriorPower n` — which
     are only isomorphic, so no equality of submodules can be stated. What is proved is the
     isomorphism of `((A.exteriorAnnihilator n).over U).toSheafOfModules` with
     `(B.exteriorAnnihilator n).toSheafOfModules`, the two sheaves of modules of the restricted
     submodule and of the annihilator of `B`.

     The quantification over arrows crosses with nothing to prove, and
     `CategoryTheory.Over.ofArrowOut` is that bijection: an arrow `W ⟶ V.left`
     of `C` makes `W` an object over `U` by composing with `V.hom`. What the *reverse* inclusion
     needs, and what it uses, is only that the comparison of exterior powers is an isomorphism;
     no essential surjectivity of the restriction functor is involved.
   * **The passage between the slice site over `U` and the restricted ringed space `U`.** Piece
     one lives on the restricted ringed space of necessity, while the determinant and
     `Stacks.InvertibleLocallyFree.InvertibleIsLocal` are stated on the slice site. Since `ℱ_M`
     cannot be moved, the determinant has to be, along
     `TopologicalSpace.Opens.sheafOfModulesEquivOver`;
     `Stacks.AssociatedSheaf.restrictOverRetract` does exactly this for 08BL's retract and is
     the pattern. The bundle of algebras can be carried along an *isomorphism* of sheaves of
     modules, `SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/AlgebraBundleStalk.lean`), and the way
     through is to take the bundle `SheafOfModules.ringedSpaceAlgebras` of the restricted ringed
     space and compare.

     **What remains of this piece once the restriction is known.** `determinantOverIso` puts
     `det(F)|_U` on the slice site as `det(F|_U)`, and
     `Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_retract_free_over` gives
     `F|_U ≅ j⁻¹ℱ_M` **on the slice site**, `j` being
     `TopologicalSpace.Opens.sheafOfModulesEquivOver`; `determinantIsoOfIso`, which is a
     same-site statement, then identifies `det(F|_U)` with `det(j⁻¹ℱ_M)`. So what is left of
     this piece is a single comparison across the equivalence: either `det(j⁻¹N) ≅ j⁻¹det(N)`,
     or — weaker, and possibly cheaper, since invertibility is all that is wanted of
     `ℱ_{det M}` in the end — the transport of `Stacks.SheafOfModules.IsInvertible` along `j`.

     **The exterior algebra does cross the change of site, and with its algebra structure.**
     `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExteriorAlgebra` is the
     pushforward twin of `SheafOfModules.isExteriorAlgebra_over`: `SheafOfModules
     .isExteriorAlgebra_pushforward` says the pushforward of an exterior algebra of `M` along a
     continuous and cocontinuous functor of sites is an exterior algebra of `G_*M`, and
     `SheafOfModules.exteriorPushforwardIso_generator` and `exteriorPushforwardIso_mul` are the
     generator and multiplication compatibilities that
     `Stacks.SheafOfModules.exteriorPowerPushforwardIso` lacked. What that does *not* give is a
     comparison of the determinants: `SheafOfModules.TensorExteriorSymmetricAlgebras
     .exteriorAnnihilatorPushforward` carries `annₙ(M)` into `annₙ(G_*M)` for an arbitrary such
     `G`, but the reverse inclusion needs `G` essentially surjective (`IsExteriorAnnihilated`
     quantifies over *all* arrows out of the object), presenting the pushforward of a
     `SheafOfModules.Submodule` as a submodule needs `G` cover-preserving, and `determinant` is
     a coproduct, which the right adjoint `sheafPushforwardFunctor` need not preserve. All three
     hold for `TopologicalSpace.Opens.overEquivalence`, which is an equivalence; the general-`G`
     statement is false and must not be stated.

     **There is no constant-rank shortcut here, and the reason is the hypothesis
     of Tag 0FJN itself.** It is tempting to avoid the question by reducing to constant rank,
     where `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower` makes
     the determinant the top exterior power and the exterior power crosses any change of site on
     its own. But a flat sheaf of modules of finite presentation on a *ringed* space is not
     locally of constant rank, not even after shrinking the open: its stalks are flat and of
     finite presentation over `𝒪_x`, hence finite projective there, and a finite projective
     module over a ring that is not local is not free. Concretely, take `X` a one-point space
     with `𝒪_X(X) = R` for a ring `R` carrying an idempotent `e ∉ {0, 1}`, and `F` the sheaf
     with `F(X) = eR ⊕ ((1 - e)R)²`. Then `F` is flat and of finite presentation, its rank is
     `1` on one factor of `R` and `2` on the other, and the only open cover of `X` by nonempty
     opens is `{X}` itself, so no `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F
     r` holds for any `r` on any refinement. `det(F)` is correspondingly nonzero in two degrees,
     so `isZero_exteriorAnnihilator` fails and `determinantIsoExteriorPower` does not apply even
     locally. This is also why the source's own proof produces a finite *projective* module `M`
     and not a free one, and why
     `Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat` gives `Module.Projective`
     rather than a basis. The constant-rank machinery of
     `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantTopPower` and of Tag 0B38
     is therefore not available on this route at all, and the two pieces here have to be done as
     stated.
   * **`annₙ(ℱ_M) ≅ ℱ_{partₙ(det M)}`.** Both sides are subsheaves of `ℱ_{⋀ⁿ M} ≅ ⋀ⁿ(ℱ_M)` and
     both membership conditions are local, so the two can be compared on stalks, where
     `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv` gives `𝒪_x ⊗_R N` and the base
     change of the determinant identifies them —
     `ProjectiveDeterminant.annihilatorPart_baseChange_map` with
     `component_eq_exteriorPower_inf_annihilator`. The *morphism* still has to be produced
     first: a stalkwise comparison upgrades a morphism to an isomorphism and does not supply
     one.
   * **`ℱ_N` is invertible for `N` an invertible module.** **This step is done**, as
     `Stacks.AssociatedSheaf.isInvertible_associatedSheaf`
     (`StacksFrontier/Topology/Sheaves/Modules/AssociatedSheaf/Tensor.lean`), with the
     `AlgebraicGeometry.SheafOfModules.IsInvertible` form, at the sheaf condition this file
     carries, as `isInvertible_associatedSheaf_algebraicGeometry`. It is how the source
     concludes, and it is proved the source's way, through Tag 0B8K (1) ⟺ (2): the tensor
     inverse of `ℱ_N` is `ℱ_{N^∨}`, because construction (3) *is* monoidal on an arbitrary
     ringed space. Both comparisons this needs are proved
     there: `associatedSheafTensorIso`, `ℱ_{M ⊗_R N} ≅ ℱ_M ⊗_{𝒪_X} ℱ_N`, and
     `associatedSheafUnitIso`, `ℱ_R ≅ 𝒪_X`.

     The route is the one the private `associatedSheafTensorIso` of
     `StacksFrontier/AlgebraicGeometry/Schemes/ZariskiAndSeparation/AffineTensor.lean` takes for
    `Spec R`, but it is **not** a statement-only generalisation of it. That file discharges the
    naturality of the presheaf-level
     comparison by `with_unfolding_all rfl`, and over a general ringed space that is false:
     `TensorProduct.AlgebraTensorModule.distribBaseChange` sends `a ⊗ (m ⊗ n)` to
     `(a ⊗ m) ⊗ (1 ⊗ n)`, so the naturality square commutes only through `map_one` of the
     restriction map, which on `Spec R` is a definitional equality of pointwise units and in
     general is a proof. The new file transports along `map_one` instead.

     Note also that the *other* available route to invertibility is genuinely closed here, and
     not by accident: `Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one`
     (`LocallyTrivialInvertible/Basic.lean`) is unconditional, but an invertible module is
     projective of rank one rather than free, the opens of `X` have nothing to do with the opens
     of `Spec R`, and `Stacks.RingedSpace.exists_isInvertible_not_isFiniteLocallyFreeOfRank_one`
     exhibits an invertible sheaf of modules on a ringed space that is not locally free of rank
     one. So the tensor characterisation is not a convenience.
   * **The locality of finite presentation**, which is what makes the finite presentation of
     `det(F)` free once the local description is in hand. **This step is done**: it is public as
     `Stacks.SheafOfModules.isFinitePresentation_of_coversTop`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleFinitePresentation.lean`), for a
     covering of the top object of a site, and it is the form the determinant argument actually
     calls — the per-member hypothesis is a global finite presentation on each member, which is
     exactly what `exists_isFinite_presentation_determinant_over` supplies.

4. *The locality of invertibility.* **This step is done.** Invertibility is
   `Stacks.SheafOfModules.IsInvertible`, the existence of a tensor
   inverse (Tag 0B8K (1) ⟺ (2),
   `Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`), so concluding from
   invertibility on a cover is a descent problem, and for a general ringed space it is the
  `Prop` `Stacks.InvertibleLocallyFree.InvertibleIsLocal`. That `Prop` is **proved**, on an
  arbitrary site by `Stacks.SheafOfModules.invertibleIsLocal`
   (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalDual.lean`) and for a ringed
   space by `Stacks.SheafOfModules.invertibleIsLocal_ringedSpace`
   (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalSpace.lean`). The proof is the
   source's own and needs no descent theory: the dual sheaf `M^∨ = SheafHom(M, O)` is a global
   construction, its evaluation pairing commutes with restriction to a localized site (Tag
   0E8H), sheafification inverts the restricted pairing on each member of the covering because
   `M|_U` is invertible there (Tag 040A (2)), local bijectivity descends along the covering, and
   Tag 0B8K (2) ⟹ (1) finishes. So what stands between the inputs above and the source's
   own route to Tag 0FJN is step 3 alone, the assembly — which, as that step says, would also
   give the finite presentation of `det(F)`. That finite presentation is proved by the
   rank-idempotent route instead, so the tag no longer waits on this route.

   Note that the earlier route over a locally ringed base,
   `Stacks.Modules.isInvertible_of_isInvertible_restrict_of_iSup_eq_top`
   (`StacksFrontier/AlgebraicGeometry/InvertibleLocal/Basic.lean`), is still not available for a
   ringed space: it trivializes the module locally, and that is precisely what
   `Stacks.RingedSpace.exists_isInvertible_not_isFiniteLocallyFreeOfRank_one` refutes. The
   dual-sheaf route avoids trivializing anything, which is why it goes through.

**Why the stalkwise descent is not proved here.** The argument is the third paragraph of the
proof of Tag 0B8K: for `M` of finite presentation the evaluation pairing
`SheafHom(M, O) ⊗ M ⟶ O` is at each stalk the contraction
`Hom_{O_x}(M_x, O_x) ⊗ M_x → O_x`, whose bijectivity *is* `Module.Invertible O_x M_x`
(Mathlib's `Module.Invertible` is defined as bijectivity of `TensorProduct.contractLeft`), and
a pairing that sheafification inverts gives invertibility by
`Stacks.SheafOfModules.isInvertible_of_pairing` (Tag 0B8K (2) ⟹ (1)). Every *ingredient* of
that argument is in the repository, but they are stated in four mutually unreducible
frameworks, and the compatibility that would join them — the stalk of the evaluation morphism,
read through the two stalk comparisons, is the contraction — is in none of them:

* the dual `SheafHom(M, O)` and its evaluation pairing are
  `Stacks.SheafOfModules.dualSheaf` and `evaluationPresheaf`/`evaluation`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean`), over
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf`, on an arbitrary site;
* Tag 01CP, `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearEquivOfFinitePresentation`,
  is stated for an abstract `SheafHom` record over `structureSheaf Rc` with
  `Rc : TopCat.Sheaf CommRingCat`, and takes the stalk of that record's `obj`, not of
  `dualSheaf`;
* Tag 01CB, `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, is stated for that
  file's own `tensorSheaf`, built from a hand-made `presheafTensor` rather than from Mathlib's
  monoidal product, over `structureSheafRing X`;
* the stalkwise criterion that turns a bijection into an isomorphism,
  `AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`, is stated over a
  `Sheaf (Opens.grothendieckTopology X) RingCat`.

The underlying objects do agree — `presheafTensor X F G = PresheafOfModules.tensorObj F G`
holds by `rfl`, as `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorEncodings.lean` records
for the other spellings — but recognising it costs tens of seconds of unification per
comparison, and `TensorStalkRingedSpace` itself needs
`set_option backward.isDefEq.respectTransparency false` to do its own. Joining the four is a
development in its own right, not a lemma.

**Why monomorphy of `det(F) ⟶ ⋀(F)` is proved stalkwise.** Mathlib's `Sigma.map_mono` wants
`HasBiproduct` of the two families, which an `ℕ`-indexed family in an abelian category does not
have — the coproduct and the product differ. What is available is that the stalk functor
preserves the coproduct (Tag 01AH, `SheafOfModules.natStalkCoprodEquiv`) and that monomorphy of
a morphism of sheaves of modules on a space is stalkwise
(`AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap`), and on the direct sum of the
stalks the coproduct of the morphisms is `DirectSum.lmap` of their stalk maps, which is
injective as soon as each of them is.

**Two spellings of the stalk map.** `AlgebraicGeometry.SheafOfModules.stalkMap` and
`PresheafOfModules.stalkMapL` are the same function, but their sources are
`AlgebraicGeometry.SheafOfModules.stalkObj O x M` and `TopCat.Presheaf.stalk M.val.presheaf x`,
which are equal only after unfolding a colimit cocone; a goal rewritten with
`stalkMap_hom_eq_stalkMapL` therefore stops being type-correct at `implicit` transparency.
The identification is used in term mode only, through `Eq.trans`, exactly as
`SheafOfModules.isIso_exteriorPowerProdHom` does.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.Sheaf

universe u

/-! ### Coproducts of monomorphisms of sheaves of modules on a space -/

namespace SheafOfModules

variable {X : TopCat.{u}}
  {Osharp : Sheaf (Opens.grothendieckTopology (X : Type u)) CommRingCat.{u}}
  (Q Q' : ℕ → SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp))
  (p : ∀ n, Q n ⟶ Q' n) (x : (X : Type u))

/-- **The coproduct of a family of morphisms acts summandwise on the stalks.** Under the
comparison of Tag 01AH the stalk of `∐ p` sends the `n`-th summand to the `n`-th summand by the
stalk map of `p n`, because `Sigma.ι Q n ≫ Sigma.map p = p n ≫ Sigma.ι Q' n`. -/
lemma stalkMapL_sigmaMap_of (n : ℕ)
    (t : ToType (TopCat.Presheaf.stalk (Q n).val.presheaf x)) :
    PresheafOfModules.stalkMapL x (CategoryTheory.Limits.Sigma.map p).val
        (natStalkCoprodEquiv Q x (DirectSum.of _ n t)) =
      natStalkCoprodEquiv Q' x
        (DirectSum.of _ n (PresheafOfModules.stalkMapL x (p n).val t)) := by
  rw [natStalkCoprodEquiv_of, natStalkCoprodEquiv_of]
  have h := (stalkMapL_comp_of_comp_eq_comp x (CategoryTheory.Limits.Sigma.ι Q n)
        (CategoryTheory.Limits.Sigma.map p) _ rfl).trans
      (stalkMapL_comp_of_comp_eq_comp x (p n) (CategoryTheory.Limits.Sigma.ι Q' n) _
        (CategoryTheory.Limits.Sigma.ι_map p n).symm).symm
  exact DFunLike.congr_fun h t

/-- `SheafOfModules.stalkMapL_sigmaMap_of` as an equality of linear maps: the summands generate
the direct sum, so the formula on them determines the stalk of the coproduct. -/
lemma stalkMapL_sigmaMap_comp_natStalkCoprodEquiv :
    (PresheafOfModules.stalkMapL x (CategoryTheory.Limits.Sigma.map p).val).comp
        (natStalkCoprodEquiv Q x).toLinearMap =
      (natStalkCoprodEquiv Q' x).toLinearMap.comp
        (DirectSum.lmap fun n => PresheafOfModules.stalkMapL x (p n).val) := by
  refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    DirectSum.lof_eq_of, DirectSum.lmap_of]
  exact stalkMapL_sigmaMap_of Q Q' p x n t

/-- **The stalk of a coproduct of stalkwise injective morphisms is injective.** On the direct
sum of the stalks the coproduct is `DirectSum.lmap` of the stalk maps. -/
lemma injective_stalkMapL_sigmaMap
    (hp : ∀ n, Function.Injective (PresheafOfModules.stalkMapL x (p n).val)) :
    Function.Injective (PresheafOfModules.stalkMapL x
      (CategoryTheory.Limits.Sigma.map p).val) := by
  have h := stalkMapL_sigmaMap_comp_natStalkCoprodEquiv Q Q' p x
  have hinj : Function.Injective
      ((PresheafOfModules.stalkMapL x (CategoryTheory.Limits.Sigma.map p).val).comp
        (natStalkCoprodEquiv Q x).toLinearMap) := by
    rw [h]
    exact (natStalkCoprodEquiv Q' x).injective.comp ((DirectSum.lmap_injective _).mpr hp)
  exact (Function.Injective.of_comp_iff' _ (natStalkCoprodEquiv Q x).bijective).mp hinj

/-- **An `ℕ`-indexed coproduct of morphisms of sheaves of modules on a space is a monomorphism
as soon as each summand is injective on every stalk.** Monomorphy is stalkwise, and on the
stalks the coproduct acts summandwise. -/
theorem mono_sigmaMap_of_injective_stalkMapL
    (hp : ∀ (y : (X : Type u)) (n : ℕ),
      Function.Injective (PresheafOfModules.stalkMapL y (p n).val)) :
    Mono (CategoryTheory.Limits.Sigma.map p) := by
  rw [AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
  intro y
  rw [funext (stalkMap_hom_eq_stalkMapL y (CategoryTheory.Limits.Sigma.map p))]
  exact injective_stalkMapL_sigmaMap Q Q' p y (hp y)

end SheafOfModules

/-! ### The inclusion of the determinant into the exterior algebra -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {X : TopCat.{u}}
  {Osharp : Sheaf (Opens.grothendieckTopology (X : Type u)) CommRingCat.{u}}
  {F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology (X : Type u)) Osharp)}

/-- **The inclusion `det(F) ⟶ ⋀(F)` is a monomorphism.** The determinant is the coproduct of
the degreewise annihilators and its inclusion is the coproduct of their inclusions; each of
those is injective on every stalk, because a section of a submodule of a sheaf of modules whose
germ vanishes vanishes on a smaller object (`injective_submoduleStalkι`). -/
theorem determinantι_mono
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology (X : Type u)) F) :
    Mono A.determinantι :=
  SheafOfModules.mono_sigmaMap_of_injective_stalkMapL _ _
    (fun n => (A.exteriorAnnihilator n).ι) fun y _ => injective_submoduleStalkι y

end SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### Flatness of a sheaf of modules gives flatness of its stalks -/

namespace Stacks.SheafOfModules

open AlgebraicGeometry RingedSpaceModuleAdjunction

/-- **Tag 05NE, in the spellings the determinant development uses.** A flat sheaf of modules on
a ringed space has flat stalks, for the module structure
`Stacks.SheafOfModules.stalkModule`.

The content is `AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`; what this adds is that
the index `structureSheafRing Y` of the determinant development is
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`, and that
`Stacks.SheafOfModules.stalkModule` is the module structure that theorem's statement supplies
by `inferInstanceAs`. Both hold by `rfl`, but the universe arguments of
`AlgebraicGeometry.SheafOfModules.IsFlat` are not determined by `F` alone, so they are written
out; this is the spelling Tag 08BL uses as well. -/
@[stacks 05NE
    "flat implies stalkwise flat, for a ringed space, in the `structureSheafRing` spelling"]
theorem flat_stalk_of_isFlat {Y : RingedSpace.{u, u}}
    (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F)
    (x : Y) :
    @Module.Flat _ _ _ _ (Stacks.SheafOfModules.stalkModule F x) :=
  (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat Y.sheaf F).mp hF x

end Stacks.SheafOfModules

/-! ### Tag 0FJN with flatness as a hypothesis on the sheaf -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

section RingedSpace

open AlgebraicGeometry RingedSpaceModuleAdjunction

/-- **The stalks of the determinant of a flat sheaf of modules of finite presentation are
invertible modules.** This is
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_stalk_invertible` with flatness
taken as flatness of the sheaf rather than of each stalk.

The sheaf of rings is written `structureSheafRing Y`, the spelling the determinant development
uses, and *not* `structureSheafRing Y`: the two are definitionally equal, but only
`structureSheafRing Y` unifies with the `CategoryTheory.Sheaf.toRingCat J Osharp` that
`SheafOfModules.TensorExteriorSymmetricAlgebras` is indexed by, since `structureSheafRing` is an
anonymous constructor rather than an application of `toRingCat`. See the implementation notes of
this file. -/
theorem determinant_stalk_invertible_of_isFlat {Y : RingedSpace.{u, u}}
    (G : SheafOfModules.{u} (structureSheafRing Y)) [G.IsFinitePresentation]
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier) G)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) G)
    (x : Y) :
    @Module.Invertible _ _ _ _ (Stacks.SheafOfModules.stalkModule A.determinant x) :=
  determinant_stalk_invertible G A (Stacks.SheafOfModules.flat_stalk_of_isFlat G hflat) x

end RingedSpace

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
