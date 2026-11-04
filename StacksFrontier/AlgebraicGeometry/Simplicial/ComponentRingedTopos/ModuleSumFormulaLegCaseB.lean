module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaSituation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLeg
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationRestrictTranspose
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafificationUnit
import StacksFrontier.CategoryTheory.Adjunction.CompTranspose

/-!
# The summand inclusions of the module direct-sum formula, case (B)

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `O` be a sheaf of commutative rings on its total site. The direct-sum
formula of Stacks 0D72 (6) writes the restriction to degree `m` of module lower shriek from
degree `n` as the direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the pullbacks `f_φ^*` of
sheaves of modules along the transition morphisms of ringed topoi. The isomorphism itself says
nothing about which summand a given map lands in; what identifies the decomposition is that the
`φ`th summand inclusion is the canonical map
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` attached to `φ`.

In case (B) that identification is made before sheafification, where the summand inclusions of
the formula are, by construction, colimit injections over the comma category on the degree-`n`
component inclusion. This file supplies that presheaf-level step — the `φ`th summand inclusion of
`CategoryTheory.CocontinuousSimplicialSite.presheafSumFormulaB` is the leg
`Stacks.Sites.ComponentModuleSumFormula.sumFormulaLeg` of `φ` — and the steps that carry it
towards the sheaf level: the reduction of the summand inclusion of
`…moduleSumFormulaB` to the one of `…componentModuleSumFormulaB`, the reading of the latter
through the chain of comparisons that formula is built from, and the transposition of the summand
comparison `…transitionPullbackModulesIsoB` along the Stacks 03D7 adjunction of the two-field
transition morphism, and the reduction of the resulting comparison to an equation between sections
of sheaves of sets. The sheaf-level equation itself is not yet here; what is still missing is
recorded in the implementation notes.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB`: **the leg equation itself**,
  as a `Prop`-valued definition — the summand inclusion of `…moduleSumFormulaB` is the canonical
  leg `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`. It is not yet proved, but
  `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_comparison` derives it from
  the one step that is missing.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_presheafSumFormulaB_inv`: the `φ`th
  summand inclusion of the presheaf-level direct-sum formula of case (B), followed by the inverse
  of that formula, is the presheaf-level leg of `φ`.
* `CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_moduleSumFormulaB_inv_eq`: that same
  summand inclusion for the sheaf-level formula `…moduleSumFormulaB`, reduced to the one for
  `…componentModuleSumFormulaB` conjugated by the summand comparison
  `…transitionPullbackModulesIsoB`.
* `CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_componentModuleSumFormulaB_hom`: the
  `φ`th summand inclusion of `…componentModuleSumFormulaB`, read through the chain that formula is
  built from: the presheaf-level summand inclusion whiskered by the forgetful functor and by
  sheafification, followed by the sheafification-restriction commutation and the presheaf
  description of module lower shriek.
* `CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_componentModuleSumFormulaB_hom_app`:
  that same summand inclusion read at an object, with the whiskerings carried out.
* `CategoryTheory.CocontinuousSimplicialSite`'s
  `homEquiv_sheafificationCompRestrict_eq_pushforward₀_map`:
  **the two abstract comparisons inside the summand inclusion transpose away.** Along the
  sheafification adjunction of the degree-`m` component, the transpose of
  `Stacks.SheafOfModules.sheafificationCompRestrictIso.inv` followed by the degree-`m` restriction
  of `…componentModuleLowerShriekIsoSheafification.inv` is the presheaf-level restriction along
  the degree-`m` component inclusion of the sheafification transpose of
  `…componentModuleLowerShriekIsoSheafification.inv` itself. This is step 3 of the route recorded
  in the implementation notes, and the step those notes used to record as the wall.
* `CategoryTheory.CocontinuousSimplicialSite.toPresheaf_map_homEquiv_sheafificationCompRestrict`,
  `…homEquiv_pushforward₀_map_eq_comp_unit` and
  `…toSheafify_comp_forget_map_unit_eq_toPresheaf_map_comp`: the three halves that statement is
  assembled from, kept apart because the assembly does not fit one declaration's heartbeat budget.
* `CategoryTheory.CocontinuousSimplicialSite.homEquiv_transitionModulePullbackAdjunctionB_val`:
  the transpose along the case-(B) summand's adjunction, on underlying presheaves of modules — the
  transpose along the composite of the three presheaf-level adjunctions that
  `CategoryTheory.Adjunction.restrictFullyFaithful` cuts it down from, followed by the comparison
  of the two readings of the direct image of presheaves of modules.
* `CategoryTheory.CocontinuousSimplicialSite`'s
  `homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val` and
  `…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map`:
  **steps 1 to 3 of the route, chained.** The transpose of the `φ`th summand inclusion of
  `…componentModuleSumFormulaB` along the case-(B) summand's adjunction, read on underlying
  presheaves of modules: first split into the three concrete transposes, then with the
  sheafification transpose of the two abstract comparisons replaced by the presheaf-level
  restriction along the degree-`m` component inclusion of the sheafification transpose `η_X`.
* `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_ranπ`: **the passage to
  sections of step 5.** The leg equation holds as soon as the two sides of the comparison
  hypothesis agree on every section of every underlying sheaf of sets, leg of the right Kan
  extension by leg.
* `CategoryTheory.CocontinuousSimplicialSite.componentModuleLowerShriekAdjunction_unit_app_val`
  and `…homEquiv_moduleSumFormulaLeg_app_val`: **step 4 of the route.** The unit of
  `g_{n!} ⊣ g_n^*` is, on underlying presheaves of modules, the presheaf-level pullback transpose
  of that same `η_X`; so the right-hand side of the comparison hypothesis is that transpose
  followed by the direct-image transition of Stacks 09WF. Both sides of the hypothesis are now
  expressed through the one morphism `η_X`.
*
  `…homEquiv_leftAdjointUniq_transitionModulePullbackAdjunctionB`:
  the comparison of left adjoints that the summand comparison
  `…transitionPullbackModulesIsoB` used to be built from transposes away: along the Stacks 03D7
  adjunction of the modules development it becomes the transposition along the case-(B) summand's
  own adjunction, followed by the comparison of the two right adjoints. It is superseded by
  `…homEquiv_transitionPullbackModulesIsoB_hom_app_comp`, which does the same along the Stacks
  03D7 adjunction of the two-field morphism.

## Implementation notes

The presheaf-level formula `CategoryTheory.CocontinuousSimplicialSite.presheafSumFormulaB` is the
formula of `Stacks.Sites.ComponentModuleSumFormula.colimitPullbackRestrictionIsoCoproduct`
transported along three comparisons: `Stacks.PullbackColimit.pullbackIso`, which identifies
Mathlib's abstract pullback of presheaves of modules with the objectwise colimit model;
`CategoryTheory.CocontinuousSimplicialSite.extendScalarsIdIso`, which removes the extension of
scalars along the identity structure map; and the left unitor. So the summand inclusion is the
leg conjugated by those three, and the statement below records exactly that conjugate rather than
the bare leg.

Only the two outer comparisons survive in the statement: the left unitor and the associator are
the identity on components, so they disappear under the normalisation, while the extension of
scalars and Mathlib's pullback do not. The leg itself is reached by
`CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv` at the leg cofan
`Stacks.Sites.ComponentModuleSumFormula.isColimitCofanSumFormulaLegNatTrans`, which is what
`colimitPullbackRestrictionIsoCoproduct` is built from; the extension of scalars is moved past the
summand inclusion by naturality of the latter, which is a morphism of functors.

*What is still missing, and what blocks it.* The sheaf-level equation

```
Limits.Sigma.ι (fun ψ : n ⟶ m => (situation C).transitionPullbackModules' P ψ) φ ≫
    (moduleSumFormulaB C P n m).inv =
  (situation C).moduleSumFormulaLeg P φ
```

is well typed — it is now the declaration
`CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB` rather than only a sentence in
these notes — and `…sigma_ι_comp_moduleSumFormulaB_inv_eq` together with
`…sigma_ι_comp_componentModuleSumFormulaB_hom` reduce it to an equation between two natural
transformations out of `…transitionPullbackModules'`: the summand comparison followed by the
presheaf-level summand inclusion carried through sheafification, against the canonical leg. Both
sides are maps out of a left adjoint, so the comparison is made after transposing, and the
transpose of the leg is `…homEquiv_moduleSumFormulaLeg_app`.

*The step that used to block this is now closed.* It was the one that moves that transposition
between the two spellings of Stacks 03D7: `…homEquiv_moduleSumFormulaLeg_app` transposes along
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`, of the two-field morphism,
whereas `…transitionPullbackModulesIsoB` used to be built against
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, with an `eqToIso` in front of it
carrying `AlgebraicGeometry.RingedToposHom.pullbackModules_toRingedToposModulesHom`. No
`eqToHom` algebra could cancel that transport at a use site, however the statement was arranged,
because **every defeq check which can reach `f.toRingedToposModulesHom ≟ f.toModulesHom` is
unbounded**: the two readings agree only propositionally, which is the content of
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom_eq_toModulesHom`, so a kernel asked to
compare them grinds through the two inverse-image structure maps and never stops.

The fix was to remove the transport rather than to cancel it, and it has been applied in both
cases. `…transitionPullbackModulesIsoB` is now `CategoryTheory.Adjunction.leftAdjointUniq` of the
*two-field* adjunction — whose left adjoint already *is* the summand
`…transitionPullbackModules'` — against `…transitionModulePullbackAdjunctionB`, with the comparison
of the right adjoints collected in
`CategoryTheory.CocontinuousSimplicialSite.transitionRingedToposPushforwardModulesIsoB`. That
comparison carried the transport too, between its two honest factors, and no longer does: both it
and its case-(A) counterpart
`CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA` are now built at the
`AlgebraicGeometry.RingedToposHom.toModulesHom` reading, which is the one
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is defined at, so the transport
does not occur anywhere on the path from the summand to the canonical leg. The measurements that
forced that are recorded at `…transitionRingedToposPushforwardModulesIsoA`.

*What the rebuild left, and what it cost.* Transposing the rebuilt comparison away is
`CategoryTheory.CocontinuousSimplicialSite.homEquiv_transitionPullbackModulesIsoB_hom_app_comp`,
and it is not simply
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` written out. That form cannot
be elaborated at a concrete comparison, for a reason unrelated to the readings: projecting
`CategoryTheory.Iso.hom` out of a `…leftAdjointUniq` standing under a hom-set bijection, against
an expected type, forces the elaborator to reduce the comparison to a structure, and reducing it
reaches the two adjunctions' data. That is a deterministic `whnf` timeout at *elaboration* time,
and it is insensitive to how the statement is arranged — naming the
`CategoryTheory.Adjunction.ofNatIsoRight`, leaving the comparison as a definition to be unfolded,
and writing the whole `…leftAdjointUniq` out in full all fail the same way. The same identity
built *upwards*, by instantiating a general lemma and letting its type be inferred, costs under a
second. So the comparison is kept opaque: it is passed to
`CategoryTheory.Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_ofNatIsoRight_symm` as a variable,
together with `…transitionPullbackModulesIsoB_eq`, which records the definition as a
propositional equality where the one `δ`-step it needs is affordable.

`…homEquiv_leftAdjointUniq_transitionModulePullbackAdjunctionB` below is the superseded form of
that statement: it transposes the same comparison of left adjoints along the modules
development's adjunction. It is true and self-contained and is left standing.

*What is still missing, precisely.* Case (A) is done:
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA` proves the leg equation there, by
discharging the comparison factor in
`…map_sheafAdjunction_unit_comp_ranComparisonSheaf_eq_restrictTransitionModules`.
Case (B) is *not* done, and the reason is not the one these notes used to give. What used to be
recorded here — that two independent elaborations of the composite stating the comparison factor
cannot be compared inside one declaration's budget, so no shape of the hypothesis is usable — is
false, or at any rate was an artefact of the transport: in case (A) the comparison factor is one
`congrArg` reading an existing presheaf-level statement on a single section, and the leg equation
is four `refine`s.

Two things stand between case (B) and the same treatment.

The first is the one these notes already named: case (B) has no transposition formula for the
summand inclusion of `…componentModuleSumFormulaB` to play the part that
`CategoryTheory.SimplicialSite.homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq` plays in
case (A), because the identification there is made before sheafification. Its ingredients are
here — `…sigma_ι_comp_presheafSumFormulaB_inv` and
`…sigma_ι_comp_componentModuleSumFormulaB_hom` — and what is missing is their transposition along
`…transitionModulePullbackAdjunctionB`, which is a
`CategoryTheory.Adjunction.restrictFullyFaithful` of the threefold composite of restriction of
presheaves of modules along `u_φ`, extension of scalars and sheafification.

The second is new, and is why the case-(A) proof cannot simply be transcribed. In case (A) the
comparison factor is an equality of morphisms *between the same modules of sections*: the source
of `…transitionRingedToposPushforwardModulesIsoA` is
`CategoryTheory.SheafOfModules.pushforward` at `O(φ)`, whose modules of sections are
definitionally those of `AlgebraicGeometry.RingedToposHom.pushforwardModules`, and the comparison
is the identity on them by `Eq.refl`. In case (B) the source is
`Stacks.SheafOfModules.pushforwardCocontinuous`, and there the two modules of sections are *not*
definitionally equal: the statement `(… .hom.app T).val.app U x = x` is rejected as
ill-typed, with `getLimitCone` named as the definition the module system does not expose. So the
case-(B) comparison is a genuine Kan-extension comparison and not an identity, and the
identification has to go through the per-leg descriptions this file's companion already carries
for exactly that purpose — `…fSharpB_leg`, `…ranπ_restrictTransition`,
`…ringFsharpInverseImage_app_apply` and `…hcompatB` in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaCaseBSummand.lean`.

*The route, worked out and partly built.* The hypothesis of
`…moduleSumFormulaLegEqB_of_comparison` is an equation between two morphisms
`X ⟶ f_{φ*}(g_m^*g_{n!}X)` of sheaves of modules on the degree-`n` component. Neither side can be
read on a section as it stands: the left-hand side transposes along an adjunction built by
`CategoryTheory.Adjunction.restrictFullyFaithful`, and three of the isomorphisms inside the
summand inclusion —
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification`,
`Stacks.SheafOfModules.sheafificationCompRestrictIso` and
`CategoryTheory.CocontinuousSimplicialSite.extendScalarsIdIso` — are each a
`CategoryTheory.Adjunction.leftAdjointUniq`, which has no elementwise description at all. They
have to be transposed away, abstractly, *before* anything is evaluated on a section. The steps
are:

1. `…homEquiv_transitionModulePullbackAdjunctionB_val` below removes
   `…restrictFullyFaithful`, leaving the transpose along the composite of the three concrete
   presheaf-level adjunctions (restriction along `u_φ`, extension of scalars, sheafification)
   followed by the comparison
   `Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso`, which is the identity on
   underlying presheaves of abelian groups. **Proved.**
2. `CategoryTheory.Adjunction.comp_homEquiv_apply` splits that into the three transposes, applied
   innermost first, and `CategoryTheory.Adjunction.homEquiv_naturality_left` for the
   sheafification adjunction strips the whiskered presheaf-level summand inclusion of
   `…sigma_ι_comp_presheafSumFormulaB_inv` off the front. What is left is the sheafification
   transpose of the two remaining factors of `…sigma_ι_comp_componentModuleSumFormulaB_hom`.
3. That transpose should be `(g_m)_*` of `η_X`, where
   `η_X` is the sheafification transpose of
   `…componentModuleLowerShriekIsoSheafification.inv.app X`, a morphism of presheaves of modules
   from the presheaf-level pullback of `X` to the underlying presheaf of `g_{n!}X`. Apply the hom
   bijection of `Stacks.SheafOfModules.RestrictRan.adjunction` for the degree-`m` component
   inclusion, which is injective; on the left it turns into the transpose along the other of the
   two adjunctions `…sheafificationCompRestrictIso` compares, by
   `CategoryTheory.Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp` at
   `Stacks.SheafOfModules.sheafificationCompRestrictIso_eq`; on the right it turns into
   `η_X` followed by `Stacks.SheafOfModules.RestrictRan.adjunction`'s unit; and the two meet at
   `Stacks.SheafOfModules.RestrictRan.sheafAdjunction_unit_app_val`. **Proved**, as
   `…homEquiv_sheafificationCompRestrict_eq_pushforward₀_map` below.
4. The right-hand side of the hypothesis is, by
   `CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app`, the unit of
   `g_{n!} ⊣ g_n^*` followed by `…restrictTransitionModules`; and
   `SheafOfModules.pullbackPushforwardAdjunction_unit_app_val` reads that unit, on underlying
   presheaves, as the presheaf-level pullback transpose of *the same* `η_X`. **Proved**,
   generically, in
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackSheafificationUnit.lean`.
5. With both sides expressed through `η_X`, go to sections. The passage itself is
   `…moduleSumFormulaLegEqB_of_ranπ` below and is **done**: comparing by
   `Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor` lands in sheaves of *sets*,
   where the direct image is the right Kan extension and `Stacks.SheafOfModules.ranπ_ext`
   applies — the `getLimitCone` obstruction recorded above is an obstruction to comparing
   *modules* of sections, not to this. What remains is to identify the two legs. The right-hand
   leg is available: `CategoryTheory.SimplicialSiteSituation`'s
   `moduleSheafFunctor_map_restrictTransitionModules_app` reads the direct-image transition of
   Stacks 09WF on underlying sheaves of sets — it is `rfl` — and
   `…ranπ_restrictTransition`, now stated at an arbitrary sheaf of sets rather than at the
   structure sheaf, computes its leg. The left-hand leg is not: it needs
   `Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ` for the Kan-extension transpose,
   `Stacks.SheafOfModules.ranπ_ranCompIso_hom_app` for
   `…transitionPushforwardModulesIsoB`, and
   `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id`
   for the other factor of `…transitionRingedToposPushforwardModulesIsoB`. **`η_X` should then
   factor out of both legs by its own naturality**, leaving a statement with no sheafification and
   no Kan extension in it: the germ at the index `…componentCostructuredArrow` of `1 ⊗ x|_ψ` is
   the restriction of the germ at the identity index, which is
   `Stacks.PullbackColimit.germ_eq_map_unit` together with `…germ_restrict`.

   *Where it stops.* Not in the germ computation, which has not been reached: at the
   first factor of the left-hand leg. Absorbing the second factor of
   `…transitionRingedToposPushforwardModulesIsoB` — which `rfl` makes the identity on sheaves of
   sets — requires identifying
   `Stacks.Sheaves.RingedToposModules.pushforwardModules` at
   `AlgebraicGeometry.RingedToposHom.toModulesHom` with
   `AlgebraicGeometry.RingedToposHom.pushforwardModules` *under* `Sheaf.moduleSheafFunctor.obj`,
   and outside `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullback.lean` that
   identification is refused with `CategoryTheory.Limits.getLimitCone` named as the definition
   whose body is not exposed. It is not a heartbeat limit and raising one would not help. The way
   round is to stay at the level of *sections*, where
   `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso_hom_app_val_app` already records the
   factor as the identity by `rfl`; the elementwise statement of
   `…moduleSumFormulaLegEqB_of_ranπ` is spelled so that this is possible.

*The wall at step 3 is closed, and what it actually was.* These notes used to record step 3 as
blocked: transposing along the sheafification adjunction produces
`CategoryTheory.PresheafOfModules.restrictScalars (𝟙 O)` in the right adjoint — the shape of
Mathlib's `CategoryTheory.PresheafOfModules.sheafificationAdjunction` — and every route from
`(restrictScalars (𝟙 O)).map h` to `h` is a deterministic timeout at these concrete arguments,
both as a `rfl` between the two spellings of the step's statement (`isDefEq`, 200000 heartbeats)
and as a general `rfl` lemma instantiated at the unit (`whnf`). That measurement stands. What does
not stand is the conclusion drawn from it, and the two things the notes said did not exist.

`CategoryTheory.PresheafOfModules.restrictScalarsId`, the isomorphism
`restrictScalars (𝟙 R) ≅ 𝟭 _` built objectwise from `ModuleCat.restrictScalarsId'`, is in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DirectImage.lean`, with
`CategoryTheory.PresheafOfModules.toPresheaf_map_restrictScalars_id_map` — an `rfl` — beside it;
and the formal half of step 3 is in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafificationRestrictTranspose.lean`, as
`Stacks.SheafOfModules.toPresheaf_map_homEquiv_sheafificationCompRestrictIso_inv_app_comp`.
Neither is needed in the form the notes asked for: the whole step is taken on *underlying
presheaves of abelian groups*, where restriction of scalars along an identity changes nothing the
presheaf can see, and `CategoryTheory.PresheafOfModules.toPresheaf` is faithful. Two further
measurements at these concrete arguments, against what the notes predicted: the object-level
crossing `((forget O ⋙ restrictScalars (𝟙 O.obj)).obj M) = M.val` is `rfl` and costs nothing, and
so is its composite with the presheaf-level restriction along the degree-`m` component inclusion.
It is only `(restrictScalars (𝟙 O)).map` that is unbounded.

*The two measurements that shape step 3's proof, and which are new.* First, crossing those two
definitionally equal spellings *underneath the right Kan extension*
`Stacks.SheafOfModules.ranPushforward` is a deterministic `isDefEq` timeout, while crossing them
on their own is free. So `…homEquiv_pushforward₀_map_eq_comp_unit` states its transpose at the
spelling the restriction forces rather than at the one
`CategoryTheory.SheafOfModules.forget` of the component restriction produces, and the one crossing
that remains is taken where the elaborator reaches it with the other spelling as the expected
type. Second, the three halves do not fit in one declaration: assembled inline, the final
`CategoryTheory.Eq.trans` against a `congrArg` of the naturality of the Kan-extension unit is a
`whnf` timeout, and splitting the proof into
`…toPresheaf_map_homEquiv_sheafificationCompRestrict`,
`…homEquiv_pushforward₀_map_eq_comp_unit` and
`…toSheafify_comp_forget_map_unit_eq_toPresheaf_map_comp` is what makes each of them cheap. A
`congrArg` motive whose abstracted variable has a metavariable type leaves
`CategoryTheory.Category` unresolved, so every `CategoryTheory.Functor.map_comp` in those proofs is
supplied with both of its factors written out.

*What is left, and where.* Steps 1 to 4 of the route are done, and both sides of the comparison
hypothesis are now expressed through the one morphism `η_X`. Steps 1 to 3 are chained in
`…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val` (step 1
`…homEquiv_transitionModulePullbackAdjunctionB_val`, with the summand inclusion read by
`…sigma_ι_comp_componentModuleSumFormulaB_hom_app` and the composite transpose split by step 2,
`Stacks.CategoryTheory.homEquiv_comp_comp_map_comp` of
`StacksFrontier/CategoryTheory/Adjunction/CompTranspose.lean`) and in
`…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map` (step 3,
`…homEquiv_sheafificationCompRestrict_eq_pushforward₀_map`). Step 4 is
`…componentModuleLowerShriekAdjunction_unit_app_val`, which instantiates
`SheafOfModules.pullbackPushforwardAdjunction_unit_app_val` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackSheafificationUnit.lean` at the component
inclusion, together with `…homEquiv_moduleSumFormulaLeg_app_val`. Of step 5, the passage to
sections is `…moduleSumFormulaLegEqB_of_ranπ` and the right-hand leg's two ingredients are
`CategoryTheory.SimplicialSiteSituation.moduleSheafFunctor_map_restrictTransitionModules_app` and
`…ranπ_restrictTransition`; the left-hand leg, where `η_X` factors out by its own naturality, and
the germ computation are not done.

*The chaining obstruction is a spelling, not a statement.* Chaining steps 1 to 3 into one
statement is not obstructed by the `PresheafOfModules.pushforward₀ … |>.map` of the
sheafification transpose in the reduced right-hand side. In the naive spelling the statement
times out (`whnf`,
200000 heartbeats, deterministic) *at the trailing factor*
`Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.hom.app`, and it does so
whether or not step 3 has been applied — removing the `pushforward₀ … |>.map` and leaving the
sheafification transpose unevaluated times out identically. What causes it is the *spelling of the
target object* of the extension-of-scalars transpose. The right adjoint of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction` is
`CategoryTheory.SheafOfModules.forget` followed by restriction of scalars along an identity, so
that is the spelling `Stacks.CategoryTheory.homEquiv_comp_comp_map_comp` hands over; written that
way, the trailing comparison has to cross it against `T.val` *underneath*
`CategoryTheory.PresheafOfModules.restrictScalars` and the right Kan extension
`Stacks.SheafOfModules.ranPushforward`, which is the unbounded crossing. Written as `T.val` the
whole statement elaborates in under two seconds and the proof closes by `congrArg`, the two
spellings being crossed where the elaborator meets them without the Kan extension in the way.
Both chained statements below are therefore spelled with `T.val`.

*Stacks 0D9T in case (B).* The route from the leg equation to the tag is case-agnostic and is run
in the module `…ComponentRingedTopos.DerivedModuleSumFormulaSummandLegB`, whose three statements
carry
`CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB` as a hypothesis and are
otherwise unconditional.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sites.ComponentModuleSumFormula

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  isRightAdjointPushforwardComponentB

/-- **The `φ`th summand inclusion of the presheaf-level direct-sum formula of case (B) is the
presheaf-level leg of `φ`.** Composed with the inverse of
`CategoryTheory.CocontinuousSimplicialSite.presheafSumFormulaB`, the summand inclusion at `φ` is
`Stacks.Sites.ComponentModuleSumFormula.sumFormulaLeg` at `φ`, conjugated by the two comparisons
the formula is transported along: extension of scalars at the identity structure map, and the
identification of Mathlib's pullback of presheaves of modules with the objectwise colimit
model. -/
theorem sigma_ι_comp_presheafSumFormulaB_inv (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (X : PresheafOfModules.{u}
      (((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj) ⋙ forget₂ CommRingCat RingCat)) :
    (Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
          (presheafSumFormulaB C P n m).inv).app X =
      (transitionPullbackPresheafModules C P.obj φ).map
          ((extendScalarsIdIso ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)).inv.app X) ≫
        sumFormulaLeg C P.obj
            ((Stacks.PullbackModel.extendScalars
              (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))).obj X) φ ≫
          (PresheafOfModules.pushforward₀OfCommRingCat
              (Grothendieck.ι C.underlying (op m)) P.obj).map
            ((Stacks.PullbackColimit.pullbackIso
              (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))).inv.app X) := by
  simp only [presheafSumFormulaB, pullbackRestrictionIsoCompCoproduct, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ _)
    ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ).naturality
      ((extendScalarsIdIso ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)).inv.app X)).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun k => (transitionPullbackPresheafModules C P.obj φ).map
      ((extendScalarsIdIso ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)).inv.app X) ≫ k) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine congrArg (fun k => k ≫ (PresheafOfModules.pushforward₀OfCommRingCat
      (Grothendieck.ι C.underlying (op m)) P.obj).map
      ((Stacks.PullbackColimit.pullbackIso
        (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))).inv.app X)) ?_
  exact congrArg (fun z => NatTrans.app z _)
    ((isColimitCofanSumFormulaLegNatTrans C n m P.obj).comp_coconePointUniqueUpToIso_inv
      (coproductIsCoproduct _) ⟨φ⟩)


/-- The `φ`th summand inclusion of the case-(B) direct-sum formula for sheaves of modules,
followed by the inverse of that formula, is the summand comparison
`CategoryTheory.CocontinuousSimplicialSite.transitionPullbackModulesIsoB` followed by the `φ`th
summand inclusion of
`CategoryTheory.CocontinuousSimplicialSite.componentModuleSumFormulaB`.

This is the bookkeeping half of the identification: `…moduleSumFormulaB` is
`…componentModuleSumFormulaB` turned round and transported summandwise, so the summand inclusion
of the one is the summand inclusion of the other conjugated by the summand comparison. -/
theorem sigma_ι_comp_moduleSumFormulaB_inv_eq (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    Limits.Sigma.ι (fun ψ : n ⟶ m => (situation C).transitionPullbackModules' P ψ) φ ≫
        (moduleSumFormulaB C P n m).inv =
      (transitionPullbackModulesIsoB C P φ).hom ≫
        Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
          (componentModuleSumFormulaB C P n m).hom := by
  let : HasColimitsOfShape (Discrete (n ⟶ m))
      (_root_.SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n) ⥤
        _root_.SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) m)) :=
    functorCategoryHasColimitsOfShape
  refine Eq.trans (congrArg
    (fun k => Limits.Sigma.ι
        (fun ψ : n ⟶ m => (situation C).transitionPullbackModules' P ψ) φ ≫ k)
    (?_ : (moduleSumFormulaB C P n m).inv =
      (Limits.Sigma.mapIso fun ψ : n ⟶ m => (transitionPullbackModulesIsoB C P ψ).symm).inv ≫
        (componentModuleSumFormulaB C P n m).hom)) ?_
  · rfl
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ (componentModuleSumFormulaB C P n m).hom)
    (Limits.Sigma.ι_mapIso_inv (fun ψ : n ⟶ m => (transitionPullbackModulesIsoB C P ψ).symm) φ)) ?_
  exact Category.assoc _ _ _


/-- **The `φ`th summand inclusion of the case-(B) direct-sum formula for sheaves of modules,
read through the chain the formula is built from.** The formula
`CategoryTheory.CocontinuousSimplicialSite.componentModuleSumFormulaB` is the presheaf-level
formula whiskered by the forgetful functor and by sheafification, preceded by the commutation of
sheafification with restriction to the degree-`m` component and by the presheaf description of
module lower shriek; so its `φ`th summand inclusion is the summand inclusion of
`…presheafSumFormulaB`, whiskered the same way and followed by those two comparisons. -/
theorem sigma_ι_comp_componentModuleSumFormulaB_hom (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m) :
    Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
        (componentModuleSumFormulaB C P n m).hom =
      Functor.whiskerLeft (forgetB C P n)
          (Functor.whiskerRight
            (Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
              (presheafSumFormulaB C P n m).inv) (sheafifyB C P m)) ≫
        Functor.whiskerLeft (forgetB C P n ⋙ PresheafOfModules.pullback.{u}
            (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj))
            (Stacks.SheafOfModules.sheafificationCompRestrictIso
              (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology m) (situation C).totalTopology
              (totalRingSheafB C P)).inv ≫
          Functor.whiskerRight
            (SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
              (situation C) (totalRingSheafB C P) n).inv
            ((situation C).componentModuleRestriction (totalRingSheafB C P) m) := by
  simp only [componentModuleSumFormulaB, Iso.symm_hom]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ _)
    ((isColimitCofanB C P n m).comp_coconePointUniqueUpToIso_inv
      (coproductIsCoproduct _) ⟨φ⟩)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine congrArg (fun k => k ≫ _) ?_
  refine Eq.trans (Functor.whiskerLeft_comp (forgetB C P n) _ _).symm ?_
  exact congrArg (Functor.whiskerLeft (forgetB C P n))
    (Functor.whiskerRight_comp _ _ (sheafifyB C P m)).symm

/-- **The summand comparison of case (B) transposes away.** The comparison of left adjoints
inside `CategoryTheory.CocontinuousSimplicialSite.transitionPullbackModulesIsoB`, followed by a
morphism out of the case-(B) summand, transposes along the Stacks 03D7 adjunction of the modules
development — at the four-field reading `AlgebraicGeometry.RingedToposHom.toModulesHom` of the
transition morphism of ringed topoi — to the transposition of that morphism along the case-(B)
summand's own adjunction `…transitionModulePullbackAdjunctionB`, followed by the comparison
`…transitionPushforwardModulesIsoB` of the two right adjoints.

Both left adjoints have the one direct image of
`Stacks.SheafOfModules.pushforwardCocontinuous` for a right adjoint, so the comparison of them is
`CategoryTheory.Adjunction.leftAdjointUniq`, whose defining property is exactly that its
transposition is the other adjunction's unit.

It is superseded by `…homEquiv_transitionPullbackModulesIsoB_hom_app_comp`, which does the same
along the Stacks 03D7 adjunction of the two-field morphism; it is true and self-contained and is
left standing. -/
theorem homEquiv_leftAdjointUniq_transitionModulePullbackAdjunctionB
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m))
    (g : (transitionModulePullbackB C P n m φ).obj X ⟶ T) :
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            ((situation C).transitionRingedToposHom P φ).toModulesHom).homEquiv X T
          ((Adjunction.leftAdjointUniq
            ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
                ((situation C).transitionRingedToposHom P
                  φ).toModulesHom).ofNatIsoRight
              (transitionPushforwardModulesIsoB C P φ).symm)
            (transitionModulePullbackAdjunctionB C P φ)).hom.app X ≫ g) =
        (transitionModulePullbackAdjunctionB C P φ).homEquiv X T g ≫
          (transitionPushforwardModulesIsoB C P φ).hom.app T :=
    (Iso.comp_inv_eq ((transitionPushforwardModulesIsoB C P φ).app T)).mp
      ((Adjunction.homEquiv_ofNatIsoRight_apply
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          ((situation C).transitionRingedToposHom P φ).toModulesHom)
        (transitionPushforwardModulesIsoB C P φ).symm _).symm.trans
        (Adjunction.homEquiv_leftAdjointUniq_hom_app_comp _
          (transitionModulePullbackAdjunctionB C P φ) g))

/-- **The transpose along the case-(B) summand's adjunction, on underlying presheaves of
modules.** `CategoryTheory.CocontinuousSimplicialSite.transitionModulePullbackAdjunctionB` is
`CategoryTheory.Adjunction.restrictFullyFaithful` of the composite of three presheaf-level
adjunctions along the forgetful functor of sheaves of modules; so the transpose of a morphism out
of the summand is, on underlying presheaves of modules, the transpose along that composite
adjunction followed by the comparison
`Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso` of the two readings of the
direct image of presheaves of modules.

This is the step that removes `CategoryTheory.Adjunction.restrictFullyFaithful` from the
computation of the transpose: what is left is a composite of three *concrete* adjunctions, whose
hom bijections are the right-Kan-extension adjunct, extension of scalars and sheafification, and
each of those has an elementwise description.

*Why the two comparisons that `…restrictFullyFaithful` inserts disappear.* The one on the source
is `CategoryTheory.Functor.rightUnitor` of the left adjoint, whose component is the identity
because the summand is *defined* as that composite; the one on the target is the comparison kept
in the statement. The identity component has to be cancelled by
`CategoryTheory.Functor.map_id` applied as a term and not by `simp` or `rw`: both spellings of the
degree-`n` sheaf of modules occur in the goal — `CategoryTheory.CocontinuousSimplicialSite.forgetB`
and `CategoryTheory.SheafOfModules.forget` of it, and `X.val` beside both — and there
`simp` cannot even apply `CategoryTheory.Category.assoc` to a visibly left-associated composite. -/
theorem homEquiv_transitionModulePullbackAdjunctionB_val (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m))
    (k : (transitionModulePullbackB C P n m φ).obj X ⟶ T) :
    ((transitionModulePullbackAdjunctionB C P φ).homEquiv X T k).val =
      ((Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
          (ringSheafB C P n).obj).comp
        ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).comp
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheafB C P m).obj)))).homEquiv X.val T k ≫
        (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso
          (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val := by
  refine Eq.trans (congrArg (fun z : X ⟶ (Stacks.SheafOfModules.pushforwardCocontinuous.{u}
        (transitionFunctorB C φ) (fSharpB C P φ)).obj T => z.val)
      (Adjunction.restrictFullyFaithful_homEquiv_apply
        ((Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
            (ringSheafB C P n).obj).comp
          ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).comp
            (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafB C P m).obj))))
        (_root_.SheafOfModules.fullyFaithfulForget.{u} (ringSheafB C P n))
        (Functor.FullyFaithful.id _) _ _ k)) ?_
  refine Eq.trans ((_root_.SheafOfModules.fullyFaithfulForget.{u}
    (ringSheafB C P n)).map_preimage _) ?_
  refine Eq.trans ?_ (congrArg (fun z => z ≫
    (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso
      (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val)
      (Adjunction.homEquiv_unit
        (adj := (Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
            (ringSheafB C P n).obj).comp
          ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).comp
            (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafB C P m).obj))))
        (f := k)).symm)
  refine Eq.trans (congrArg (fun z => _ ≫ z)
    ((congrArg (fun z => z ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.id_comp _))) ?_
  exact (Category.assoc _ _ _).symm


/-- **The `φ`th summand inclusion of the case-(B) direct-sum formula, read at an object.**
`CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_componentModuleSumFormulaB_hom` is an
equality of natural transformations; this is its component at `X`, with the whiskerings carried
out, which is the form in which the transposition formulas below consume it. -/
theorem sigma_ι_comp_componentModuleSumFormulaB_hom_app (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    (Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
        (componentModuleSumFormulaB C P n m).hom).app X =
      (sheafifyB C P m).map
          ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
            (presheafSumFormulaB C P n m).inv).app ((forgetB C P n).obj X)) ≫
        (Stacks.SheafOfModules.sheafificationCompRestrictIso
              (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology m) (situation C).totalTopology
              (totalRingSheafB C P)).inv.app
            ((PresheafOfModules.pullback.{u}
              (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
                ((forgetB C P n).obj X)) ≫
          ((situation C).componentModuleRestriction (totalRingSheafB C P) m).map
            ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
              (situation C) (totalRingSheafB C P) n).inv.app X) :=
  congrArg (fun z => NatTrans.app z X)
    (sigma_ι_comp_componentModuleSumFormulaB_hom C P n m φ)

/-- The transpose of `F.map h` along `F ⊣ G` is `h` followed by the unit. -/
private theorem homEquiv_map_eq_comp_unit {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {X Y : C} (h : X ⟶ Y) :
    adj.homEquiv X (F.obj Y) (F.map h) = h ≫ adj.unit.app Y :=
  (Adjunction.homEquiv_unit adj _ _ _).trans (adj.unit_naturality h)

/-- **The transpose of the last two factors of the case-(B) summand inclusion, on underlying
presheaves of abelian groups.** The two abstract comparisons inside the summand inclusion —
`Stacks.SheafOfModules.sheafificationCompRestrictIso` and
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification` — are
transposed away: along the composite of the right-Kan-extension adjunction for the degree-`m`
component inclusion and the sheafification adjunction on that component, the transpose of the
first followed by the second is `CategoryTheory.toSheafify` followed by the transpose of module
lower shriek's presheaf description along
`Stacks.SheafOfModules.RestrictRan.sheafAdjunction`.

This is `Stacks.SheafOfModules.toPresheaf_map_homEquiv_sheafificationCompRestrictIso_inv_app_comp`
at the simplicial data, with the trailing `componentModuleRestriction` of the comparison moved out
of the transpose by `CategoryTheory.Adjunction.unit_naturality`. It is the left half of
`…homEquiv_sheafificationCompRestrict_eq_pushforward₀_map`, kept apart
from the right half because the two together do not fit one declaration's heartbeat budget. -/
theorem toPresheaf_map_homEquiv_sheafificationCompRestrict (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map
      ((Stacks.SheafOfModules.RestrictRan.adjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        ((_root_.SheafOfModules.forget.{u} (ringSheafB C P m) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheafB C P m).obj)).obj
        (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)))
        ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheafB C P m).obj)).homEquiv
          ((PresheafOfModules.pushforward₀.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).obj ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)))
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
          ((Stacks.SheafOfModules.sheafificationCompRestrictIso
                (SimplicialSiteSituation.componentFunctor (situation C) m)
                ((situation C).componentTopology m) (situation C).totalTopology
                (totalRingSheafB C P)).inv.app ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)) ≫
            ((situation C).componentModuleRestriction (totalRingSheafB C P) m).map
              ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X)))) =
      toSheafify (situation C).totalTopology ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)).presheaf ≫
      (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map
        ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)).map
          (((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X) ≫
            (Stacks.SheafOfModules.RestrictRan.sheafAdjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        ((situation C).componentTopology m) (situation C).totalTopology
        (totalRingSheafB C P)).unit.app
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))) := by
  refine Eq.trans (congrArg (fun z => (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C
    P).obj).map z)
    (Eq.trans (Adjunction.homEquiv_unit (Stacks.SheafOfModules.RestrictRan.adjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj) _ _ _)
      (Stacks.CategoryTheory.comp_homEquiv_apply _ _ _ _ _).symm)) ?_
  refine Eq.trans
    (Stacks.SheafOfModules.toPresheaf_map_homEquiv_sheafificationCompRestrictIso_inv_app_comp
      (SimplicialSiteSituation.componentFunctor (situation C) m)
      ((situation C).componentTopology m) (situation C).totalTopology
      (totalRingSheafB C P) _ _) ?_
  exact congrArg (fun z => toSheafify (situation C).totalTopology _ ≫
    (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map
      ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)).map z))
    (homEquiv_map_eq_comp_unit (Stacks.SheafOfModules.RestrictRan.sheafAdjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        ((situation C).componentTopology m) (situation C).totalTopology
        (totalRingSheafB C P)) ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X))

/-- **The right-Kan-extension transpose of a restricted morphism is that morphism followed by the
unit.** At the morphism of interest — the transpose along sheafification on the total site of
`…componentModuleLowerShriekIsoSheafification.inv`, restricted to the degree-`m` component — this
is `CategoryTheory.Adjunction.homEquiv_unit` followed by naturality of the unit.

The target of the transpose is spelled as the restriction of the restriction of scalars rather
than through `CategoryTheory.SheafOfModules.forget` of the component restriction: the two are
definitionally equal, but comparing them *underneath* the right Kan extension
`Stacks.SheafOfModules.ranPushforward` is an `isDefEq` timeout, while comparing them on
their own is `rfl` and costs nothing. -/
theorem homEquiv_pushforward₀_map_eq_comp_unit (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    (Stacks.SheafOfModules.RestrictRan.adjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        ((PresheafOfModules.pushforward₀.{u}
          (SimplicialSiteSituation.componentFunctor (situation C) m)
          (totalRingSheafB C P).obj).obj
        ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P) ⋙
            PresheafOfModules.restrictScalars (𝟙 (totalRingSheafB C P).obj)).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)))
        ((PresheafOfModules.pushforward₀.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).map ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (totalRingSheafB C P).obj)).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X))) =
      ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (totalRingSheafB C P).obj)).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X)) ≫
            (Stacks.SheafOfModules.RestrictRan.adjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).unit.app ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)
          ⋙
          PresheafOfModules.restrictScalars (𝟙 (totalRingSheafB C P).obj)).obj
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)) :=
  homEquiv_map_eq_comp_unit (Stacks.SheafOfModules.RestrictRan.adjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj) ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (totalRingSheafB C P).obj)).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X))

/-- **The shared middle expression, re-read as the sheafification transpose followed by the
right-Kan-extension unit.** `CategoryTheory.toSheafify` followed by the underlying presheaf of
`…componentModuleLowerShriekIsoSheafification.inv` and of the unit of
`Stacks.SheafOfModules.RestrictRan.sheafAdjunction` is the underlying presheaf of the composite of
the sheafification transpose with the unit of
`Stacks.SheafOfModules.RestrictRan.adjunction`.

The two units are identified by `Stacks.SheafOfModules.RestrictRan.sheafAdjunction_unit_app_val`;
everything else is `CategoryTheory.Functor.map_comp` and associativity, each supplied as a term
with both factors written out, because a `congrArg` motive whose abstracted variable has a
metavariable type leaves the category instance unresolved. -/
theorem toSheafify_comp_forget_map_unit_eq_toPresheaf_map_comp (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    toSheafify (situation C).totalTopology ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)).presheaf ≫
      (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map
        ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)).map
          (((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X) ≫
            (Stacks.SheafOfModules.RestrictRan.sheafAdjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        ((situation C).componentTopology m) (situation C).totalTopology
        (totalRingSheafB C P)).unit.app
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))) =
      (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map
        (((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (totalRingSheafB C P).obj)).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X)) ≫
        (Stacks.SheafOfModules.RestrictRan.adjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).unit.app ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)
          ⋙
          PresheafOfModules.restrictScalars (𝟙 (totalRingSheafB C P).obj)).obj
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))) := by
  refine Eq.trans (congrArg (fun z => toSheafify (situation C).totalTopology
      ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)).presheaf ≫ (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C
              P).obj).map z)
    (CategoryTheory.Functor.map_comp (_root_.SheafOfModules.forget.{u} (totalRingSheafB C P))
      ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X)
      ((Stacks.SheafOfModules.RestrictRan.sheafAdjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        ((situation C).componentTopology m) (situation C).totalTopology
        (totalRingSheafB C P)).unit.app (((situation C).componentModuleLowerShriek (totalRingSheafB
          C P) n).obj X)))) ?_
  refine Eq.trans (congrArg (fun z => toSheafify (situation C).totalTopology
      ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)).presheaf ≫ z)
    ((PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map_comp
      ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)).map
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X))
      ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)).map
        ((Stacks.SheafOfModules.RestrictRan.sheafAdjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        ((situation C).componentTopology m) (situation C).totalTopology
        (totalRingSheafB C P)).unit.app (((situation C).componentModuleLowerShriek (totalRingSheafB
          C P) n).obj X))))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => (toSheafify (situation C).totalTopology
      ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)).presheaf ≫ (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C
              P).obj).map
      ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)).map
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X))) ≫
      (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map z)
    (Stacks.SheafOfModules.RestrictRan.sheafAdjunction_unit_app_val.{u}
      (SimplicialSiteSituation.componentFunctor (situation C) m)
      ((situation C).componentTopology m) (situation C).totalTopology
      (totalRingSheafB C P) (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj
        X))) ?_
  exact ((PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map_comp
    ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (totalRingSheafB C P).obj)).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X))
    ((Stacks.SheafOfModules.RestrictRan.adjunction.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).unit.app ((_root_.SheafOfModules.forget.{u} (totalRingSheafB C P)
          ⋙
          PresheafOfModules.restrictScalars (𝟙 (totalRingSheafB C P).obj)).obj
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)))).symm

/-- **Stacks 0D72 (6), case (B), step 3: the two abstract comparisons of the summand inclusion
transpose to the presheaf-level restriction of module lower shriek's sheafification transpose.**
Along the sheafification adjunction of the degree-`m` component, the transpose of
`Stacks.SheafOfModules.sheafificationCompRestrictIso.inv` followed by the degree-`m` restriction
of `…componentModuleLowerShriekIsoSheafification.inv` is the presheaf-level restriction along the
degree-`m` component inclusion of the sheafification transpose
`η_X` of `…componentModuleLowerShriekIsoSheafification.inv` itself.

This is the step the implementation notes of this file used to record as the wall: the transpose
along the sheafification adjunction has
`CategoryTheory.PresheafOfModules.restrictScalars (𝟙 O)` in its right adjoint, and comparing
`(restrictScalars (𝟙 O)).map h` with `h` is a deterministic timeout. The way round it is not to
compare them: `CategoryTheory.PresheafOfModules.toPresheaf` is faithful and does not see the
action, so the whole step is taken on underlying presheaves of abelian groups, where
`CategoryTheory.PresheafOfModules.toPresheaf_map_restrictScalars_id_map` is `rfl`. The injectivity
of the hom bijection of `Stacks.SheafOfModules.RestrictRan.adjunction` for the degree-`m`
component inclusion is what turns the two one-step transposes into a transpose along their
composite, which is the adjunction
`Stacks.SheafOfModules.sheafificationCompRestrictIso` compares. -/
theorem homEquiv_sheafificationCompRestrict_eq_pushforward₀_map (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheafB C P m).obj)).homEquiv
        ((PresheafOfModules.pushforward₀.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).obj ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)))
        (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
        ((Stacks.SheafOfModules.sheafificationCompRestrictIso
              (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology m) (situation C).totalTopology
              (totalRingSheafB C P)).inv.app ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X)) ≫
          ((situation C).componentModuleRestriction (totalRingSheafB C P) m).map
            ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X)) =
      (PresheafOfModules.pushforward₀.{u}
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        (totalRingSheafB C P).obj).map ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (totalRingSheafB C P).obj)).homEquiv
        ((PresheafOfModules.pullback.{u}
          (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
            ((forgetB C P n).obj X))
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)
        ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
          (situation C) (totalRingSheafB C P) n).inv.app X)) := by
  refine ((Stacks.SheafOfModules.RestrictRan.adjunction.{u}
      (SimplicialSiteSituation.componentFunctor (situation C) m)
      (totalRingSheafB C P).obj).homEquiv _ _).injective ?_
  refine (PresheafOfModules.toPresheaf _).map_injective ?_
  exact ((toPresheaf_map_homEquiv_sheafificationCompRestrict C P n m X).trans
    (toSheafify_comp_forget_map_unit_eq_toPresheaf_map_comp C P n m X)).trans
    (congrArg (fun z => (PresheafOfModules.toPresheaf.{u} (totalRingSheafB C P).obj).map z)
      (homEquiv_pushforward₀_map_eq_comp_unit C P n m X).symm)

/-- **The unit of `g_{n!} ⊣ g_n^*` on the degree-`n` component, on underlying presheaves of
modules.** It is the transpose, along the presheaf-level pullback–pushforward adjunction of the
component inclusion, of the morphism `η_X` -- the transpose along sheafification on the total site
of `…componentModuleLowerShriekIsoSheafification.inv` at `X`.

This is step 4 of the route recorded in the implementation notes. Lower shriek of modules from a
component *is* Mathlib's pullback of sheaves of modules over the identity structure map, by
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriek_eq_pullback`, and its presheaf
description *is* `SheafOfModules.pullbackIso`; so this is
`SheafOfModules.pullbackPushforwardAdjunction_unit_app_val` instantiated at the component
inclusion, with the identity for the structure map. -/
theorem componentModuleLowerShriekAdjunction_unit_app_val (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n : SimplexCategory)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    (((situation C).componentModuleLowerShriekAdjunction (totalRingSheafB C P) n).unit.app X).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (𝟙 (ringSheafB C P n).obj)).homEquiv X.val
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val
        ((PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (totalRingSheafB C P).obj)).homEquiv _ _
          ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
            (situation C) (totalRingSheafB C P) n).inv.app X)) :=
  _root_.SheafOfModules.pullbackPushforwardAdjunction_unit_app_val.{u}
    (F := SimplicialSiteSituation.componentFunctor (situation C) n)
    (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n)) X

/-- **The right-hand side of the comparison hypothesis, expressed through `η_X`.** The transpose
of the canonical leg along the Stacks 03D7 adjunction of the transition morphism of ringed topoi
is, on underlying presheaves of modules, the presheaf-level pullback transpose of `η_X` followed
by the direct-image transition of Stacks 09WF.

This is `CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app` with its unit
read by `…componentModuleLowerShriekAdjunction_unit_app_val`; it is the form in which the
right-hand side of the hypothesis of
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_comparison` meets the
left-hand side, both sides being expressed through the same `η_X`. -/
theorem homEquiv_moduleSumFormulaLeg_app_val (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
          (((situation C).moduleSumFormulaLeg P φ).app X)).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (𝟙 (ringSheafB C P n).obj)).homEquiv X.val
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X).val
          ((PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 (totalRingSheafB C P).obj)).homEquiv _ _
            ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
              (situation C) (totalRingSheafB C P) n).inv.app X)) ≫
        (((situation C).restrictTransitionModules P φ).app
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val :=
  (congrArg (fun z : X ⟶ ((situation C).transitionRingedToposHom P φ).pushforwardModules.obj
        (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)) => z.val)
      ((situation C).homEquiv_moduleSumFormulaLeg_app P φ X)).trans
    (congrArg (fun z => z ≫ (((situation C).restrictTransitionModules P φ).app
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val)
      (componentModuleLowerShriekAdjunction_unit_app_val C P n X))

/-- **Steps 1 and 2 of the route: the transpose of the case-(B) summand inclusion, split into its
three concrete factors.** On underlying presheaves of modules, the transpose along
`…transitionModulePullbackAdjunctionB` of the `φ`th summand inclusion of
`…componentModuleSumFormulaB` is: the right-Kan-extension transpose of the extension-of-scalars
transpose of (the presheaf-level summand inclusion followed by the sheafification transpose of the
two abstract comparisons), followed by the comparison of the two readings of the direct image of
presheaves of modules.

This is `…homEquiv_transitionModulePullbackAdjunctionB_val` (step 1), with the summand inclusion
read by `…sigma_ι_comp_componentModuleSumFormulaB_hom_app` and the composite transpose split by
`Stacks.CategoryTheory.homEquiv_comp_comp_map_comp` (step 2).

*The spelling of the target is load-bearing.* The target of the extension-of-scalars transpose is
written `T.val`, the underlying presheaf of modules of the degree-`m` restriction of `g_{n!}X`,
and not `CategoryTheory.SheafOfModules.forget` of it followed by restriction of scalars along the
identity, which is what the right adjoint of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction` produces. The two are definitionally
equal, but with the second the final factor
`Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso` cannot be typed against the
composite's target: that is a `whnf` timeout at 200000 heartbeats. It is the *spelling* that is
infeasible, not the statement. -/
theorem homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    ((transitionModulePullbackAdjunctionB C P φ).homEquiv X
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
          ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
            (componentModuleSumFormulaB C P n m).hom).app X)).val =
      (Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
            (ringSheafB C P n).obj).homEquiv X.val
          ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val)
          ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).homEquiv
            ((PresheafOfModules.pushforward₀.{u} (transitionFunctorB C φ)
              (ringSheafB C P n).obj).obj X.val)
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val
            ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
                  (presheafSumFormulaB C P n m).inv).app ((forgetB C P n).obj X) ≫
              (PresheafOfModules.sheafificationAdjunction.{u}
                  (𝟙 (ringSheafB C P m).obj)).homEquiv
                ((PresheafOfModules.pushforward₀.{u}
                  (SimplicialSiteSituation.componentFunctor (situation C) m)
                  (totalRingSheafB C P).obj).obj ((PresheafOfModules.pullback.{u}
                    (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
                      ((forgetB C P n).obj X)))
                (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
                  (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
                ((Stacks.SheafOfModules.sheafificationCompRestrictIso
                      (SimplicialSiteSituation.componentFunctor (situation C) m)
                      ((situation C).componentTopology m) (situation C).totalTopology
                      (totalRingSheafB C P)).inv.app ((PresheafOfModules.pullback.{u}
                    (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
                      ((forgetB C P n).obj X)) ≫
                  ((situation C).componentModuleRestriction (totalRingSheafB C P) m).map
                    ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
                      (situation C) (totalRingSheafB C P) n).inv.app X)))) ≫
        (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso
          (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val := by
  refine Eq.trans (homEquiv_transitionModulePullbackAdjunctionB_val C P φ X
    (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
      (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
    ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
      (componentModuleSumFormulaB C P n m).hom).app X)) ?_
  refine congrArg (fun z => z ≫
    (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso
      (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app
      (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val) ?_
  refine Eq.trans (congrArg
    (((Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
          (ringSheafB C P n).obj).comp
        ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).comp
          (PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (ringSheafB C P m).obj)))).homEquiv X.val
      (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)))
    (sigma_ι_comp_componentModuleSumFormulaB_hom_app C P n m φ X)) ?_
  exact Stacks.CategoryTheory.homEquiv_comp_comp_map_comp
    (Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
      (ringSheafB C P n).obj)
    (Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ))
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheafB C P m).obj)) X.val _ _

/-- **Steps 1 to 3 of the route, chained: the transpose of the case-(B) summand inclusion,
expressed through `η_X`.** The sheafification transpose of the two abstract comparisons in
`…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val` is the presheaf-level restriction
along the degree-`m` component inclusion of `η_X`, by
`…homEquiv_sheafificationCompRestrict_eq_pushforward₀_map`; so the whole transpose is expressed
through the same `η_X` that `…homEquiv_moduleSumFormulaLeg_app_val` expresses the other side of
the comparison hypothesis through.

This is the left-hand side of the hypothesis of
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_comparison`, read on
underlying presheaves of modules and before the comparison
`…transitionRingedToposPushforwardModulesIsoB` of the two direct images is applied. -/
theorem homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) :
    ((transitionModulePullbackAdjunctionB C P φ).homEquiv X
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
          ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
            (componentModuleSumFormulaB C P n m).hom).app X)).val =
      (Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
            (ringSheafB C P n).obj).homEquiv X.val
          ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val)
          ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).homEquiv
            ((PresheafOfModules.pushforward₀.{u} (transitionFunctorB C φ)
              (ringSheafB C P n).obj).obj X.val)
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val
            ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
                  (presheafSumFormulaB C P n m).inv).app ((forgetB C P n).obj X) ≫
              (PresheafOfModules.pushforward₀.{u}
                  (SimplicialSiteSituation.componentFunctor (situation C) m)
                  (totalRingSheafB C P).obj).map
                ((PresheafOfModules.sheafificationAdjunction.{u}
                    (𝟙 (totalRingSheafB C P).obj)).homEquiv
                  ((PresheafOfModules.pullback.{u}
                    (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).obj
                      ((forgetB C P n).obj X))
                  (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)
                  ((SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
                    (situation C) (totalRingSheafB C P) n).inv.app X)))) ≫
        (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso
          (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val :=
  (homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val C P n m φ X).trans
    (congrArg (fun z => z ≫
        (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso
          (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val)
      (congrArg ((Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
            (ringSheafB C P n).obj).homEquiv X.val
          ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val))
        (congrArg ((Stacks.PullbackModel.extendScalarsAdjunction
              (ringTransition C P.obj φ)).homEquiv
            ((PresheafOfModules.pushforward₀.{u} (transitionFunctorB C φ)
              (ringSheafB C P n).obj).obj X.val)
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).val)
          (congrArg (fun z =>
              (Limits.Sigma.ι (fun ψ : n ⟶ m => transitionPullbackPresheafModules C P.obj ψ) φ ≫
                  (presheafSumFormulaB C P n m).inv).app ((forgetB C P n).obj X) ≫ z)
            (homEquiv_sheafificationCompRestrict_eq_pushforward₀_map C P n m X)))))

/-- **The leg equation of Stacks 0D72 (6) in case (B)**: the `φ`th summand inclusion of the
direct-sum formula `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaB` that Stacks 0D74
consumes, followed by the inverse of that formula, is the canonical map
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` attached to `φ`.

This is the statement Stacks 0D9E (2) waits on in case (B), and the counterpart of
`CategoryTheory.SimplicialSite.ModuleSumFormulaLegEqA`. It is a `Prop`-valued definition, in the
style of `CategoryTheory.SimplicialSiteSituation.DerivedModuleSumFormulaSummand`, because it is
not yet proved; the implementation notes above record what is left of it and what the obstruction
to assembling the remaining pieces is. -/
def ModuleSumFormulaLegEqB (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    Prop :=
  Limits.Sigma.ι (fun ψ : n ⟶ m => (situation C).transitionPullbackModules' P ψ) φ ≫
      (moduleSumFormulaB C P n m).inv =
    (situation C).moduleSumFormulaLeg P φ

/-- **Stacks 0D72 (6) in case (B): the leg equation
`CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB` holds as soon as the comparison
factor is identified.**

This is the case-(B) counterpart of
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA_of_comparison`, with the same shape and the
same reason for it. Both sides are maps out of a left adjoint, so they are compared after
transposing along the Stacks 03D7 adjunction
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` of the transition morphism of
ringed topoi, whose left adjoint already *is* the summand
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`. The summand inclusion of
`…moduleSumFormulaB` is the summand inclusion of `…componentModuleSumFormulaB` conjugated by the
summand comparison, which is
`CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_moduleSumFormulaB_inv_eq`, and that
comparison transposes away by
`CategoryTheory.CocontinuousSimplicialSite.homEquiv_transitionPullbackModulesIsoB_hom_app_comp`.
What is left is the hypothesis.

*What the hypothesis comes down to.* Unlike case (A), case (B) has no transposition formula for
the summand inclusion of `…componentModuleSumFormulaB`: the decomposition there is identified
before sheafification, by
`CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_presheafSumFormulaB_inv` and
`CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_componentModuleSumFormulaB_hom`, so the
hypothesis still has to be read through those and then compared against
`CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app`. That comparison is the
identification of the comparison factor described above, and in case (A) it is the same remaining
step.

*Why the hypothesis is written out as a `∀` rather than named by a `Prop`-valued definition, and
why the summand comparison is rewritten at the level of natural transformations before the
component is introduced.* Both are the heartbeat budget rather than a choice, and the
measurements are in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaLegA.lean`.

One thing is specific to case (B): the sheaf of rings has to be spelled
`CategoryTheory.CocontinuousSimplicialSite.totalRingSheafB`, which is what
`…componentModuleSumFormulaB` and `…transitionModulePullbackAdjunctionB` are stated at, and not
`(Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)`, which that
abbreviation unfolds to in one step. The two are the same term after that step, but with the second
the hypothesis cannot be elaborated at all: projecting `CategoryTheory.Adjunction.homEquiv` out of
`…transitionModulePullbackAdjunctionB`, which is a
`CategoryTheory.Adjunction.restrictFullyFaithful` of a threefold composite, already forces that
adjunction to a structure, and asking for the step as well exhausts the budget there. With the
matching spelling the whole declaration costs under three seconds. -/
theorem moduleSumFormulaLegEqB_of_comparison (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (hR : ∀ X : _root_.SheafOfModules.{u} (ringSheafB C P n),
      (transitionModulePullbackAdjunctionB C P φ).homEquiv X
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
            ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
              (componentModuleSumFormulaB C P n m).hom).app X) ≫
          (transitionRingedToposPushforwardModulesIsoB C P φ).hom.app
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)) =
        ((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
          (((situation C).moduleSumFormulaLeg P φ).app X)) :
    ModuleSumFormulaLegEqB C P φ := by
  refine Eq.trans (sigma_ι_comp_moduleSumFormulaB_inv_eq C P φ) ?_
  refine NatTrans.ext (funext fun X => ?_)
  refine (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X
    (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
      (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))).injective ?_
  exact (homEquiv_transitionPullbackModulesIsoB_hom_app_comp C P φ X _ _).trans (hR X)

/-- **Stacks 0D72 (6) in case (B): the leg equation follows from the elementwise, leg-by-leg
equation of sections.** It suffices to compare the two sides of the comparison hypothesis of
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_comparison` on each section
of each underlying sheaf of sets, leg of the right Kan extension by leg.

This is the passage to sections of step 5 of the route recorded in the implementation notes, and
it goes through *sheaves of sets* rather than modules of sections. The direct image of sheaves of
modules along the transition morphism of ringed topoi has no elementwise description — the module
system does not expose `CategoryTheory.Limits.getLimitCone`, through which its modules of sections
are built — but its underlying sheaf of sets is the right Kan extension along the transition
functor, by `Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor` and
`Stacks.SheafOfModules.ranπ_ext`, so the comparison is made there.

What is left after this is the content of step 5: identifying each of the two legs. The right-hand
leg is the unit of `g_{n!} ⊣ g_n^*` on a section followed by
`CategoryTheory.SimplicialSiteSituation.moduleSheafFunctor_map_restrictTransitionModules_app` and
`…ranπ_restrictTransition`; the left-hand leg, which is where the germ computation sits, is
not. -/
theorem moduleSumFormulaLegEqB_of_ranπ (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (hleg : ∀ (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
      (V : ((situation C).component n)ᵒᵖ)
      (j : StructuredArrow V (transitionFunctorB C φ).op)
      (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V),
      Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
          (Sheaf.moduleSheaf (ringSheafB C P m)
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj
                X))).obj V j
          (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
            ((transitionModulePullbackAdjunctionB C P φ).homEquiv X
                  (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
                    (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
                  ((Limits.Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackB C P n m ψ) φ ≫
                    (componentModuleSumFormulaB C P n m).hom).app X) ≫
                (transitionRingedToposPushforwardModulesIsoB C P φ).hom.app
                  (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
                    (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj
                      X)))).hom.app V y) =
        Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
          (Sheaf.moduleSheaf (ringSheafB C P m)
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj
                X))).obj V j
          (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
            (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X
              (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
                (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
              (((situation C).moduleSumFormulaLeg P φ).app X))).hom.app V y)) :
    ModuleSumFormulaLegEqB C P φ :=
  moduleSumFormulaLegEqB_of_comparison C P φ fun X =>
    Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
      (R := ringSheafB C P n) (M := X)
      (N := ((situation C).transitionRingedToposHom P φ).pushforwardModules.obj
        (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)))
      (Sheaf.hom_ext_sections fun V y =>
        Stacks.SheafOfModules.ranπ_ext (transitionFunctorB C φ).op
          (Sheaf.moduleSheaf (ringSheafB C P m)
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))).obj
          (fun jj => hleg X V jj y))

end CategoryTheory.CocontinuousSimplicialSite

end
