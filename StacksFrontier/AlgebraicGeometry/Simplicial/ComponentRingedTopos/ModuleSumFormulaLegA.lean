module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanSumFormulaLegs
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseA
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLeg
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaTransitionA

/-!
# The summand inclusions of the module direct-sum formula, case (A)

`CategoryTheory.SimplicialSite.componentModuleSumFormulaA` writes the restriction to degree `m`
of module lower shriek from degree `n` as the direct sum, over the simplex maps `φ : [n] ⟶ [m]`,
of the module pullbacks along the transitions. The isomorphism itself says nothing about which
summand a given map lands in; what identifies the decomposition is that the `φ`th summand
inclusion is the *canonical* map attached to `φ`, namely the unit of `g_{n!} ⊣ g_n^*` followed by
the transition of Stacks 09WF.

Both sides are maps out of a left adjoint, so they are compared after transposing. The transpose
of the summand inclusion is the comparison
`Stacks.SheafOfModules.RestrictRan.ranComparisonSheaf` of right adjoints, because the formula is
produced by the ran criterion; that is
`Stacks.SheafOfModules.RestrictRan.homEquiv_sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom`
specialized to the simplicial data. The comparison is then identified, on underlying presheaves
of abelian groups, with restriction along the cross-fibre arrow `(φ, 𝟙)` — which is exactly the
direct-image transition of Stacks 09WF in case (A),
`CategoryTheory.SimplicialSiteSituation.restrictTransition_inl_app`.

## Main results

* `CategoryTheory.SimplicialSite.homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom`: the
  transposition formula for the `φ`th summand inclusion, for an arbitrary map out of the
  composite.
* `SimplicialSite.toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf_component`:
  the comparison of right adjoints, precomposed with the restricted unit of the degree-`m`
  adjunction, is restriction along `(φ, 𝟙)` on underlying presheaves of abelian groups.
* `CategoryTheory.SimplicialSite.homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq`:
  **the summand inclusion is the canonical map.** Its transpose is the unit of
  `g_{n!} ⊣ g_n^*` followed by that comparison.
* `CategoryTheory.SimplicialSite.sigma_ι_comp_moduleSumFormulaA_inv_eq`: the summand inclusion of
  the formula `…moduleSumFormulaA` that Stacks 0D74 consumes, reduced to the one of
  `…componentModuleSumFormulaA` conjugated by the summand comparison.
* `SimplicialSite.map_sheafAdjunction_unit_comp_ranComparisonSheaf_eq_restrictTransitionModules`:
  **the comparison factor**, as an equality of morphisms of sheaves of modules — the restricted
  unit followed by the comparison of right adjoints and by the comparison of the two direct
  images is the direct-image transition of Stacks 09WF.
* `CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA`: **the leg equation of Stacks 0D72 (6) in
  case (A)**, proved.

## Main definitions

* `CategoryTheory.SimplicialSite.ModuleSumFormulaLegEqA`: **the leg equation itself**, as a
  `Prop`-valued definition — the summand inclusion of `…moduleSumFormulaA` is the canonical leg
  `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`. It is proved, by
  `CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA`; the definition is kept because
  `CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA_of_comparison`, which reduces it to the
  comparison factor, is stated against it.

## Implementation notes

The identification is in two statements rather than one, and it is stated against the case-(A)
direct-sum formula rather than against the canonical leg of an arbitrary situation. Both are forced
by the tree rather than chosen, and together they are where this file stops short of the shape of
its abelian counterpart `…sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg'`.

The canonical map this file compares the summand inclusion against is *not*
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`, the leg built from
`CategoryTheory.SimplicialSiteSituation.fiberTransitionModules` in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaLeg.lean`, which
is the shape of the abelian counterpart. That leg is well typed — the summand
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules` and the transition of
Stacks 09WF now sit over one and the same functor, by
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom_eq_toModulesHom` — and so is the
equation `Sigma.ι … ≫ (moduleSumFormulaA …).inv = moduleSumFormulaLeg …`, which is now a
declaration, `CategoryTheory.SimplicialSite.ModuleSumFormulaLegEqA`, rather than only a sentence
in these notes. It is now also *proved*, by
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA`. The two steps it needed are recorded
here, because what unblocked the second of them was a change to the comparison of direct images
rather than anything in this file.

The first is the comparison of two Stacks 03D7 adjunctions on the one left adjoint, and it is no
longer an obstruction: the summand comparison
`CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA` is now built against
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` of the transition — whose left
adjoint already *is* the summand
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules` — with its right adjoint
turned by `CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA`. So it is a
bare `CategoryTheory.Adjunction.leftAdjointUniq` carrying no transport, and
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` transposes it away against the
same adjunction that `CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app`
uses.

It used to be built against the adjunction of the modules development at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, the other reading of the morphism,
which left a `CategoryTheory.eqToIso` in front of the comparison. That transport cannot be
cancelled at any price, and the measurements are in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaLegCaseB.lean`,
which is blocked on the same step in case (B): every definitional comparison which can reach
`f.toRingedToposModulesHom ≟ f.toModulesHom` is unbounded, because the two readings agree only
propositionally.

The statement that transposes the comparison away now exists too, as
`CategoryTheory.SimplicialSite.homEquiv_transitionPullbackModulesIsoA_hom_app_comp`, beside the
comparison itself in the module
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseASummand`.
Writing `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` out at this comparison
directly does not work, and the reason is worth recording because it is not the one the rest of
these notes would predict. It is *not* the propositional-only agreement of the two readings of
the morphism of ringed topoi: the comparison was rebuilt precisely to keep them apart, and
nothing in the identity reaches them. It is the direction in which the elaborator is driven.

Writing the identity out asks the elaborator to project `CategoryTheory.Iso.hom` out of a
`CategoryTheory.Adjunction.leftAdjointUniq` standing under a hom-set bijection, against an
expected type; to do that it must reduce the comparison to a structure, and reducing it reaches
the two adjunctions' data. That is a deterministic `whnf` timeout at *elaboration* time — not a
kernel timeout — and it happens whether the `CategoryTheory.Adjunction.ofNatIsoRight` is named in
the statement, or the comparison is left as a definition to be unfolded, or the whole
`…leftAdjointUniq` is written out in full. The same identity built *upwards*, by instantiating
the general lemma and letting its type be inferred, costs under a second and produces exactly the
type that cannot be elaborated downwards.

So the comparison is kept opaque: it is passed to
`CategoryTheory.Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_ofNatIsoRight_symm` as a variable,
together with `CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA_eq`, which records the
definition as a propositional equality and is the one place the `δ`-step is affordable. What is
still missing for the sheaf-level equation is therefore only the identification of the comparison
factor described below.

The second was the comparison factor, which
`…toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf_component` identifies on *underlying
presheaves of abelian groups* rather than as an equality of morphisms of sheaves of modules against
`CategoryTheory.SimplicialSiteSituation.restrictTransitionModulesApp`. That gap is closed by
`…map_sheafAdjunction_unit_comp_ranComparisonSheaf_eq_restrictTransitionModules`, which reads that
statement on one module of sections; everything else there is `Eq.refl`.

That identification cannot be made at the level of presheaves of abelian groups, which is why it
is not simply the statement below read through
`CategoryTheory.PresheafOfModules.toPresheaf`. The two direct images have the same *sections*:
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` is the identity on them, and so the
underlying modules of sections of `CategoryTheory.SheafOfModules.pushforward` at `O(φ)` and of
`AlgebraicGeometry.RingedToposHom.pushforwardModules` are definitionally equal. Their underlying
presheaves of abelian groups are *not*: `…pushforwardModules` reaches its sections through
`CategoryTheory.Limits.getLimitCone`, whose definition the module system does not expose, so
`CategoryTheory.PresheafOfModules.toPresheaf` of it and the restriction
`(u_φ ⋙ g_m)^{op} ⋙ ℱ` that the statement below produces are not definitionally equal and an
equation between morphisms of those presheaves is not even well typed. The identification has
therefore to be made one module of sections at a time, and there each of the three factors of
`…transitionRingedToposPushforwardModulesIsoA` is the identity.

The two statements are kept apart for a reason of the same kind, one level down. Their composite
would
have to equate the implicit source object of `≫` in `…componentModuleLowerShriekAdjunction`'s
unit — which is intrinsically `(g_{n!} ⋙ g_n^*).obj X` — with `g_n^*.obj (g_{n!}.obj X)`, and
every route to that (`rw`, `simp only`, `congr 1`, a `congrArg` whose lambda forces the
spelling) sends the unifier into `g_{n!}`, which is
`CategoryTheory.Functor.leftAdjoint` of the restriction, i.e. an `Exists.choose`, and exhausts
its heartbeats there.

*The assembly, and what unblocked it.* The chain is
`CategoryTheory.SimplicialSite.sigma_ι_comp_moduleSumFormulaA_inv_eq`, then
`CategoryTheory.SimplicialSite.homEquiv_transitionPullbackModulesIsoA_hom_app_comp` — these two
are `CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA_of_comparison` — then
`CategoryTheory.SimplicialSite.homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq`, the
comparison factor, and
`CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app`.

What blocked it was not the heartbeat budget but the *transport* that used to sit in the middle of
`CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA`: the `eqToIso` of
`AlgebraicGeometry.RingedToposHom.pushforwardModules_toRingedToposModulesHom`. Everything else
about the comparison factor is `Eq.refl` on a section, and that one factor is not: on underlying
sheaves of sets its source and target are
`Stacks.Sheaves.RingedToposModules.pushforwardModules` at the two readings of the morphism of
ringed topoi, whose comparison is unbounded: at 200000 heartbeats and with the kernel's own
limit, `(Sheaf.moduleSheafFunctor _).obj ((pushforwardModules k).obj T)` at the two readings
is a *kernel* deterministic timeout by `rfl`, so `CategoryTheory.eqToHom_refl` cannot be applied
to that factor and no arrangement of
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_eqToIso_hom_app` recovers it either.
So the transport is avoided altogether: the comparison of direct images is built at
`AlgebraicGeometry.RingedToposHom.toModulesHom`, which is the reading
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is defined at, so the only
comparison left is
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`. Retargeting it costs one `congrArg`
over `AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage` — an equality
of *morphisms* of sheaves of rings, where a transport is affordable — inside
`CategoryTheory.SimplicialSite.restrictionPushforwardRingMap_eq`.

Two measurements about the *shape* of the assembly stand, and they are why the proofs below are
written as they are. Writing `(transitionRingedToposPushforwardModulesIsoA C P φ).hom.app …` into
a `congrArg` motive elaborates but spends the whole budget, so the two factorisation steps are
`CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq` with the unwhiskered factor left to
unification. And restating the three-factor composite of the comparison at a component —
`(A ≪≫ B ≪≫ C).hom.app T = A.hom.app T ≫ B.hom.app T ≫ C.hom.app T` by `rfl` — is a `whnf`
timeout, while the same restatement at the level of isomorphisms, `… = A ≪≫ B ≪≫ C`, costs
nothing; neither is needed now, because the composite is read on a section where the whole thing
is `Eq.refl`.

The two statements are nevertheless still kept apart, for the reason one level down recorded
above.

The transposition formula is stated for an arbitrary map `f` out of the composite rather than at
`f = 𝟙`, matching
`CategoryTheory.Functor.homEquiv_sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv`,
because that is the shape in which the generic statement is proved and the shape in which a
consumer that post-composes uses it.

`CategoryTheory.SimplicialSiteSituation.componentModuleRestriction` is a `def` whose body is
`CategoryTheory.SheafOfModules.pushforward` at the identity structure map, and
`…componentModuleLowerShriekAdjunction` is
`CategoryTheory.SheafOfModules.pullbackPushforwardAdjunction` at the same structure map; the
`IsRightAdjoint` instances differ but are proofs of a `Prop`, so the two spellings are
definitionally equal and the generic statements transfer by `exact`. Instance search does not
unfold the `def`, so the instance is passed by hand.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor Stacks.SheafOfModules.RestrictRan

universe u

namespace CategoryTheory.SimplicialSite

attribute [local instance] SimplicialSiteSituation.hasWeakSheafifyComponent

variable (C : SimplicialSite.{u}) (O : Sheaf (situation C).totalTopology RingCat.{u})

/-- **The transposition formula for the `φ`th summand inclusion of the case-(A) direct-sum
formula.** Transposing along the adjunction of the summand, after precomposing with the summand
inclusion, is transposing along the composite adjunction `g_{n!} ⊣ g_n^*` followed by `g_m^*`'s
and then postcomposing with the comparison `ranComparisonSheaf` of right adjoints. -/
theorem homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom (n m : SimplexCategory) (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} ((situation C).componentRingSheaf O n))
    (T : _root_.SheafOfModules.{u} ((situation C).componentRingSheaf O m))
    (f : ((situation C).componentModuleLowerShriek O n ⋙
      (situation C).componentModuleRestriction O m).obj X ⟶ T) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ringTransitionA C O φ)).homEquiv X T
        ((Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackA C O ψ) φ ≫
          (componentModuleSumFormulaA C O n m).hom).app X ≫ f) =
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
              (F := SimplicialSiteSituation.componentFunctor (situation C) n)
              (𝟙 ((situation C).componentRingSheaf O n))).comp
            (sheafAdjunction.{u} (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology m)
              (situation C).totalTopology O)).homEquiv X T f ≫
        (ranComparisonSheaf.{u} (SimplicialSiteSituation.componentFunctor (situation C) n)
          (SimplicialSiteSituation.componentFunctor (situation C) m)
          ((situation C).componentTopology n) ((situation C).componentTopology m)
          (situation C).totalTopology O (transitionFunctorA C φ)
          (transitionNatTransA C φ)).app T := by
  have : (_root_.SheafOfModules.pushforward.{u}
      (F := SimplicialSiteSituation.componentFunctor (situation C) n)
      (𝟙 ((situation C).componentRingSheaf O n))).IsRightAdjoint :=
    SimplicialSiteSituation.componentModuleRestriction_isRightAdjoint _ O n
  exact homEquiv_sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom
    (SimplicialSiteSituation.componentFunctor (situation C) n)
    (SimplicialSiteSituation.componentFunctor (situation C) m)
    ((situation C).componentTopology n) ((situation C).componentTopology m)
    (situation C).totalTopology O (fun ψ : n ⟶ m => transitionFunctorA C ψ)
    (fun ψ : n ⟶ m => transitionNatTransA C ψ)
    (fun P U => isLimitFanRanComponent C U P) φ X T f

/-- **The comparison of right adjoints is restriction along the cross-fibre arrow `(φ, 𝟙)`**, in
case (A) and at the component spellings. This is
`Stacks.SheafOfModules.RestrictRan.toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf`
at the simplicial data, restated with `…componentModuleRestriction` in place of
`CategoryTheory.SheafOfModules.pushforward` at the identity structure map and with
`…componentRingSheaf` in place of `Stacks.SheafOfModules.RestrictRan.ringSheaf`. Each pair is
definitionally equal, but the generic statement is written with the second spelling of each and
every consumer here with the first, and the composite's implicit source object then differs
between the two, which is what blocks every rewrite inside a larger goal. -/
theorem toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf_component
    (n m : SimplexCategory) (φ : n ⟶ m) (B : _root_.SheafOfModules.{u} O) :
    (PresheafOfModules.toPresheaf ((situation C).componentRingSheaf O n).obj).map
        ((((situation C).componentModuleRestriction O n).map
              ((sheafAdjunction.{u} (SimplicialSiteSituation.componentFunctor (situation C) m)
                ((situation C).componentTopology m)
                (situation C).totalTopology O).unit.app B) ≫
            (ranComparisonSheaf.{u} (SimplicialSiteSituation.componentFunctor (situation C) n)
              (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology n) ((situation C).componentTopology m)
              (situation C).totalTopology O (transitionFunctorA C φ)
              (transitionNatTransA C φ)).app
              (((situation C).componentModuleRestriction O m).obj B)).val) =
      Functor.whiskerRight (NatTrans.op (transitionNatTransA C φ)) B.val.presheaf :=
  toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf
    (SimplicialSiteSituation.componentFunctor (situation C) n)
    (SimplicialSiteSituation.componentFunctor (situation C) m)
    ((situation C).componentTopology n) ((situation C).componentTopology m)
    (situation C).totalTopology O (transitionFunctorA C φ) (transitionNatTransA C φ) B

/-- **The comparison factor of case (A) is the direct-image transition of Stacks 09WF.** The
restriction to degree `n` of the unit of the degree-`m` adjunction, followed by the comparison
`Stacks.SheafOfModules.RestrictRan.ranComparisonSheaf` of right adjoints and then by the
comparison `CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA` of the two
direct images, is
`CategoryTheory.SimplicialSiteSituation.restrictTransitionModules`.

This is the step the leg equation of Stacks 0D72 (6) was missing in case (A). Its content is
`…toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf_component`, the same composite read
on underlying presheaves of abelian groups; everything else is definitional, and the proof is one
`congrArg` reading that statement on a single section.

*Why it is now one `congrArg`.* The two sides are compared one module of sections at a time, and
there each factor of `…transitionRingedToposPushforwardModulesIsoA` is the identity *by
`Eq.refl`*: `CategoryTheory.SheafOfModules.pushforwardCongr` and
`Stacks.Sheaves.ToposPullback.pushforwardRestrictionModulesIso` are built from the identity map on
sections and `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` from
`Stacks.Sheaves.RingedToposModules.ofSheafHom` of an identity. The right-hand side is
`…ofSheafHom` of `CategoryTheory.SimplicialSiteSituation.restrictTransition`, whose case-(A)
value on a section is restriction along the cross-fibre arrow `(φ, 𝟙)` by
`CategoryTheory.SimplicialSiteSituation.restrictTransition_inl_app`, again by `Eq.refl`; and
`CategoryTheory.SimplicialSite.transitionNatTransA` is that same arrow. So the whole equation is
the presheaf-level statement above, read at one object and one section.

This relies on `…transitionRingedToposPushforwardModulesIsoA` carrying no transport across the
two readings of a morphism of ringed topoi; with such a transport the comparison of its source
and target on underlying sheaves of sets is a kernel timeout, and no arrangement avoids it. -/
theorem map_sheafAdjunction_unit_comp_ranComparisonSheaf_eq_restrictTransitionModules
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory) (φ : n ⟶ m)
    (B : _root_.SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    ((situation C).componentModuleRestriction
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n).map
          ((sheafAdjunction.{u} (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology m) (situation C).totalTopology
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (situation C).totalTopology) P))).unit.app B) ≫
        (ranComparisonSheaf.{u} (SimplicialSiteSituation.componentFunctor (situation C) n)
              (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology n) ((situation C).componentTopology m)
              (situation C).totalTopology
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
              (transitionFunctorA C φ) (transitionNatTransA C φ)).app
            (((situation C).componentModuleRestriction
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                m).obj B) ≫
          (transitionRingedToposPushforwardModulesIsoA C P φ).hom.app
            (((situation C).componentModuleRestriction
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                m).obj B) =
      ((situation C).restrictTransitionModules P φ).app B := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact congrArg (fun z : (PresheafOfModules.toPresheaf
      ((situation C).componentRingSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n).obj).obj
        (((situation C).componentModuleRestriction
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
            n).obj B).val ⟶ _ =>
      (z.app U).hom x)
    (toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf_component C
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n m φ B)

/-- **Stacks 0D72 (6) in case (A): the `φ`th summand inclusion of the direct-sum formula for
sheaves of modules is the canonical map attached to `φ`.** Transposed under the adjunction of the
summand, the inclusion is the unit of `g_{n!} ⊣ g_n^*`, followed by the restriction to degree `n`
of the unit of the degree-`m` adjunction and then the comparison `ranComparisonSheaf` of right
adjoints.

That second factor is restriction along the cross-fibre arrow `(φ, 𝟙)` — the direct-image
transition of Stacks 09WF in case (A) — by
`…toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf_component`. The two statements
together are what pins the decomposition down: the isomorphism of the direct-sum formula is
otherwise opaque, and the assertion of Stacks 0D72 (6) is not that some isomorphism exists but that
this particular family of canonical maps exhibits one. -/
theorem homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq
    (n m : SimplexCategory) (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} ((situation C).componentRingSheaf O n)) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ringTransitionA C O φ)).homEquiv X
            (((situation C).componentModuleRestriction O m).obj
              (((situation C).componentModuleLowerShriek O n).obj X))
        ((Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackA C O ψ) φ ≫
          (componentModuleSumFormulaA C O n m).hom).app X) =
      ((situation C).componentModuleLowerShriekAdjunction O n).unit.app X ≫
        (((situation C).componentModuleRestriction O n).map
            ((sheafAdjunction.{u} (SimplicialSiteSituation.componentFunctor (situation C) m)
                ((situation C).componentTopology m) (situation C).totalTopology O).unit.app
              (((situation C).componentModuleLowerShriek O n).obj X)) ≫
          (ranComparisonSheaf.{u} (SimplicialSiteSituation.componentFunctor (situation C) n)
              (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology n) ((situation C).componentTopology m)
              (situation C).totalTopology O (transitionFunctorA C φ)
              (transitionNatTransA C φ)).app
            (((situation C).componentModuleRestriction O m).obj
              (((situation C).componentModuleLowerShriek O n).obj X))) := by
  have hcomp := (congrArg
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
        (ringTransitionA C O φ)).homEquiv X
          (((situation C).componentModuleRestriction O m).obj
            (((situation C).componentModuleLowerShriek O n).obj X)))
      (Category.comp_id ((Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackA C O ψ) φ ≫
        (componentModuleSumFormulaA C O n m).hom).app X)).symm).trans
    (homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom C O n m φ X
      (((situation C).componentModuleRestriction O m).obj
        (((situation C).componentModuleLowerShriek O n).obj X)) (𝟙 _))
  have hunit : ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
              (F := SimplicialSiteSituation.componentFunctor (situation C) n)
              (𝟙 ((situation C).componentRingSheaf O n))).comp
            (sheafAdjunction.{u} (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology m)
              (situation C).totalTopology O)).homEquiv X _ (𝟙 _) =
      ((situation C).componentModuleLowerShriekAdjunction O n).unit.app X ≫
        ((situation C).componentModuleRestriction O n).map
          ((sheafAdjunction.{u} (SimplicialSiteSituation.componentFunctor (situation C) m)
              ((situation C).componentTopology m) (situation C).totalTopology O).unit.app
            (((situation C).componentModuleLowerShriek O n).obj X)) :=
    (Adjunction.homEquiv_id _ X).trans (Adjunction.comp_unit_app _ _ X)
  exact hcomp.trans ((congrArg (fun g => g ≫ _) hunit).trans (Category.assoc _ _ _))


/-- The `φ`th summand inclusion of the case-(A) direct-sum formula for sheaves of modules,
followed by the inverse of that formula, is the summand comparison
`CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA` followed by the `φ`th summand
inclusion of `CategoryTheory.SimplicialSite.componentModuleSumFormulaA`.

This is the bookkeeping half of the identification: `…moduleSumFormulaA` is
`…componentModuleSumFormulaA` turned round and transported summandwise, so the summand inclusion
of the one is the summand inclusion of the other conjugated by the summand comparison. It is the
case-(A) counterpart of
`CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_moduleSumFormulaB_inv_eq`. -/
theorem sigma_ι_comp_moduleSumFormulaA_inv_eq
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m => (situation C).transitionPullbackModules' P ψ) φ ≫
        (moduleSumFormulaA C P n m).inv =
      (transitionPullbackModulesIsoA C P φ).hom ≫
        Sigma.ι (fun ψ : n ⟶ m =>
            transitionModulePullbackA C
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                ψ) φ ≫
          (componentModuleSumFormulaA C
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
              n m).hom := by
  let : HasColimitsOfShape (Discrete (n ⟶ m))
      (_root_.SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n) ⥤
        _root_.SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) m)) :=
    functorCategoryHasColimitsOfShape
  refine Eq.trans (congrArg
    (fun k => Sigma.ι
        (fun ψ : n ⟶ m => (situation C).transitionPullbackModules' P ψ) φ ≫ k)
    (?_ : (moduleSumFormulaA C P n m).inv =
      (Sigma.mapIso fun ψ : n ⟶ m => (transitionPullbackModulesIsoA C P ψ).symm).inv ≫
        (componentModuleSumFormulaA C
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
            n m).hom)) ?_
  · rfl
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ (componentModuleSumFormulaA C
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n m).hom)
    (Sigma.ι_mapIso_inv (fun ψ : n ⟶ m => (transitionPullbackModulesIsoA C P ψ).symm) φ)) ?_
  exact Category.assoc _ _ _

/-- **The leg equation of Stacks 0D72 (6) in case (A)**: the `φ`th summand inclusion of the
direct-sum formula `CategoryTheory.SimplicialSite.moduleSumFormulaA` that Stacks 0D74 consumes,
followed by the inverse of that formula, is the canonical map
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` attached to `φ`.

This is the statement Stacks 0D9E (2) waits on, and the module counterpart of the abelian
`…sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg'`. It is a `Prop`-valued
definition because `CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA_of_comparison`, which
reduces it to the comparison factor, is stated against it; the equation itself is proved, by
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA`. -/
def ModuleSumFormulaLegEqA (P : Sheaf (situation C).totalTopology CommRingCat.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) : Prop :=
  Sigma.ι (fun ψ : n ⟶ m => (situation C).transitionPullbackModules' P ψ) φ ≫
      (moduleSumFormulaA C P n m).inv =
    (situation C).moduleSumFormulaLeg P φ

/-- **Stacks 0D72 (6) in case (A): the leg equation
`CategoryTheory.SimplicialSite.ModuleSumFormulaLegEqA` holds as soon as the comparison factor is
identified.**

Both sides are maps out of a left adjoint, so they are compared after transposing along the Stacks
03D7 adjunction `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` of the transition
morphism of ringed topoi, whose left adjoint already *is* the summand
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`. The summand inclusion of
`…moduleSumFormulaA` is the summand inclusion of `…componentModuleSumFormulaA` conjugated by the
summand comparison, which is `CategoryTheory.SimplicialSite.sigma_ι_comp_moduleSumFormulaA_inv_eq`,
and that comparison transposes away by
`CategoryTheory.SimplicialSite.homEquiv_transitionPullbackModulesIsoA_hom_app_comp`. The hypothesis
— that the transpose of the summand inclusion of `…componentModuleSumFormulaA`, corrected by the
comparison `CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA` of the two
direct images, is the transpose of the canonical leg — is discharged by
`…map_sheafAdjunction_unit_comp_ranComparisonSheaf_eq_restrictTransitionModules`, so this
statement's only remaining purpose is to be the step that
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA` takes.

*What the hypothesis comes down to.* By
`CategoryTheory.SimplicialSite.homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq` its
left-hand side is the unit of `g_{n!} ⊣ g_n^*` followed by the restriction to degree `n` of the
unit of the degree-`m` adjunction and the comparison
`Stacks.SheafOfModules.RestrictRan.ranComparisonSheaf` of right adjoints; by
`CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app` its right-hand side is
that same unit followed by the direct-image transition
`CategoryTheory.SimplicialSiteSituation.restrictTransitionModules` of Stacks 09WF. So the content
is the identification of those second factors, and the implementation notes of this file say why
it has to be made one module of sections at a time and what still stops the two statements from
being joined inside one declaration.

*Why the hypothesis is written out as a `∀` rather than named by a `Prop`-valued definition.*
Named, it is cheap in the signature but the `δ`-step that applies it at `X` no longer fits in what
the proof has left; written out, the signature costs more and the application is a bare
instantiation. The second budget is the one that closes. The same arrangement is why the summand
comparison is rewritten here at the level of natural transformations, before `X` is introduced,
rather than at a component: writing `(transitionPullbackModulesIsoA C P φ).hom.app X` into a
`have` asks the elaborator to project `CategoryTheory.Iso.hom` out of a
`CategoryTheory.Adjunction.leftAdjointUniq` against an expected type, which is the reduction the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaCaseASummand.lean`
measure as unaffordable; taken from the stored right-hand side of
`…sigma_ι_comp_moduleSumFormulaA_inv_eq` it costs nothing. -/
theorem moduleSumFormulaLegEqA_of_comparison
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (hR : ∀ X : _root_.SheafOfModules.{u} ((situation C).componentRingSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n),
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
              (ringTransitionA C
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                  φ)).homEquiv X
            (((situation C).componentModuleRestriction
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                  m).obj
              (((situation C).componentModuleLowerShriek
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                  n).obj X))
            ((Sigma.ι (fun ψ : n ⟶ m => transitionModulePullbackA C
                  ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                    ψ) φ ≫
              (componentModuleSumFormulaA C
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                  n m).hom).app X) ≫
          (transitionRingedToposPushforwardModulesIsoA C P φ).hom.app
            (((situation C).componentModuleRestriction
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                  m).obj
              (((situation C).componentModuleLowerShriek
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                  n).obj X)) =
        ((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X
          (((situation C).componentModuleRestriction
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                m).obj
            (((situation C).componentModuleLowerShriek
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
                n).obj X))
          (((situation C).moduleSumFormulaLeg P φ).app X)) :
    ModuleSumFormulaLegEqA C P φ := by
  refine Eq.trans (sigma_ι_comp_moduleSumFormulaA_inv_eq C P φ) ?_
  refine NatTrans.ext (funext fun X => ?_)
  refine (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X
    (((situation C).componentModuleRestriction
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) m).obj
      (((situation C).componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P))
          n).obj X))).injective ?_
  exact (homEquiv_transitionPullbackModulesIsoA_hom_app_comp C P φ X _ _).trans (hR X)

/-- **Stacks 0D72 (6) in case (A): the leg equation.** The `φ`th summand inclusion of the
direct-sum formula `CategoryTheory.SimplicialSite.moduleSumFormulaA` that Stacks 0D74 consumes,
followed by the inverse of that formula, is the canonical map
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` attached to `φ`.

This is `CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA_of_comparison` with its hypothesis
discharged by `…map_sheafAdjunction_unit_comp_ranComparisonSheaf_eq_restrictTransitionModules`. The
chain is: transpose the summand inclusion by
`…homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq`, which produces the unit of
`g_{n!} ⊣ g_n^*` followed by the comparison factor; identify that factor with the direct-image
transition of Stacks 09WF; and recognise the result as the transpose of the canonical leg by
`CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app`.

Two things about the shape are forced rather than chosen. The two factorisation steps are
`CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq` with the unwhiskered factor left to
unification: writing `(transitionRingedToposPushforwardModulesIsoA C P φ).hom.app …` into a
`congrArg` motive instead elaborates, but spends the whole heartbeat budget doing it. And the two
sides spell the total sheaf of rings differently —
`(Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)` on the
transposition side and `(situation C).totalRingSheaf P` on the canonical-leg side. Reconciled last,
when both sides are one and the same unit followed by one and the same transition, that is a
congruence on the arguments and costs nothing; reconciled earlier it makes the unifier compare the
two `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekAdjunction`s, which reaches
`Exists.choose`. -/
theorem moduleSumFormulaLegEqA (P : Sheaf (situation C).totalTopology CommRingCat.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    ModuleSumFormulaLegEqA C P φ := by
  refine moduleSumFormulaLegEqA_of_comparison C P φ (fun X => ?_)
  refine Eq.trans (eq_whisker (homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq C
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n m φ X) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).trans
    (map_sheafAdjunction_unit_comp_ranComparisonSheaf_eq_restrictTransitionModules
      C P n m φ _))) ?_
  exact (SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app (situation C) P φ X).symm

end CategoryTheory.SimplicialSite

end
