module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegCaseB

/-!
# The left-hand leg of the case-(B) leg equation, on sections

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `O` be a sheaf of commutative rings on its total site. The leg equation of
Stacks 0D72 (6) in case (B),
`CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB`, is reduced by
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_ranπ` to an elementwise
equation between sections of sheaves of *sets*, leg of the right Kan extension by leg. This file
takes the left-hand side of that equation apart.

The left-hand side is the transpose of the `φ`th summand inclusion of
`…componentModuleSumFormulaB`, followed by the comparison
`…transitionRingedToposPushforwardModulesIsoB` of the two direct images, read on the underlying
sheaf of sets and then through the leg of the Kan extension. Both factors of that comparison are
removed here: the one which is the identity on sheaves of sets, and the genuine Kan-extension
comparison, which the leg absorbs.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite`'s
  `moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app`:
  **the second factor of the comparison drops out on sections.** The comparison
  `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` between the modules development's
  direct image and `AlgebraicGeometry.RingedToposHom.pushforwardModules` is the identity on
  sections, so a composite ending in it is, on sections, the composite without it.
* `CategoryTheory.CocontinuousSimplicialSite`'s
  `ranπ_moduleSheafFunctor_map_transitionPushforwardModulesIsoB_hom_app`:
  **the first factor is absorbed by the leg of the Kan extension.** The comparison
  `…transitionPushforwardModulesIsoB` is, on underlying sheaves of sets, Mathlib's comparison of
  the right Kan extension of a presheaf of abelian groups with the right Kan extension of its
  underlying presheaf of sets, and that comparison carries legs to legs.
* `CategoryTheory.CocontinuousSimplicialSite`'s
  `ranπ_moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app`:
  the two together — **the left-hand leg with the whole comparison removed**: the leg at `(U, ψ)`
  of the comparison applied to a section is the leg of the Kan extension at the sheaf of modules
  itself, applied to the image of the section under the transpose alone.
* `CategoryTheory.CocontinuousSimplicialSite.ranπ_moduleSheafFunctor_map_comp_eq_sourceMap`:
  **the left-hand leg, computed.** Granted that the transpose is, on underlying presheaves of
  modules, the transpose along `Stacks.SheafOfModules.RestrictRan.adjunction` of a morphism `E`
  out of the restriction along `u_φ` followed by the comparison that moves the restriction of
  scalars past the Kan extension — which is what steps 1 to 3 of the route recorded in
  `…ComponentRingedTopos.ModuleSumFormulaLegCaseB` give — the leg at `(U, ψ)` on a section `y` is
  `E` at `U` applied to the restriction of `y` along `ψ`. Nothing of the two direct images, of
  the right Kan extension or of the adjunction survives in it.
* `CategoryTheory.CocontinuousSimplicialSite.moduleSheafFunctor_map_hom_app_apply`,
  `…toPresheaf_map_ranPushforwardRestrictScalarsIso_hom_app`,
  `…toPresheaf_map_comp_ranPushforwardRestrictScalarsIso_hom_app` and
  `…toPresheaf_map_ranPushforwardRestrictScalarsIso_hom_app_apply`: the bridges that carry that
  leg to the underlying presheaves of modules, which is where
  `…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map` describes
  the transpose.

* `CategoryTheory.CocontinuousSimplicialSite.extendScalarsIdIso_hom_app_tmul` and
  `…extendScalarsIdIso_inv_app_apply`: **extension of scalars along an identity, on sections.**
  The comparison `…extendScalarsIdIso` of that extension with the identity functor is a
  `CategoryTheory.Adjunction.leftAdjointUniq` and so has no description by unfolding; its forward
  direction sends the pure tensor `1 ⊗ m` to `m`, and its inverse sends `m` to `1 ⊗ m`.

* `CategoryTheory.CocontinuousSimplicialSite`'s
  `ranπ_moduleSheafFunctor_map_homEquiv_moduleSumFormulaLeg_app`: **the right-hand leg,
  computed.** The leg at `(U, ψ)` of the transpose of the canonical leg
  `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`, read on a section `y`, is the
  unit of `g_{n!} ⊣ g_n^*` on `y`, restricted along `ψ` and then along the cross-fibre arrow
  `(φ, 𝟙)`. Nothing of the direct image or of the Kan extension survives in it either.

## Implementation notes

*What the two legs leave.* With both sides of the hypothesis of
`…moduleSumFormulaLegEqB_of_ranπ` computed, that hypothesis is an equation between two sections
of the underlying sheaf of *sets* of `g_{n!}X` over one object of the total site, both built from
the one morphism `η_X` — the sheafification transpose of
`…componentModuleLowerShriekIsoSheafification.inv` at `X`. On the left `η_X` is reached through
the extension-of-scalars transpose of the presheaf-level summand inclusion, on the right through
the presheaf-level pullback transpose; `η_X` factors out of both by its own naturality, and what
is left is the germ identity recorded in step 5 of the route in
`…ComponentRingedTopos.ModuleSumFormulaLegCaseB`. That identity is not proved here; what follows
is what it comes down to, and which pieces of it exist.

Writing `F` for the degree-`n` component inclusion, the left-hand leg is `E` at `U` on the
restriction of `y` along `ψ`, and `E` is the extension-of-scalars transpose of the presheaf-level
summand inclusion followed by the degree-`m` restriction of `η_X`. Reading the transpose on a
section — `Stacks.PullbackModel.extendScalarsAdjunction_homEquiv_app_apply` — and the summand
inclusion through `…sigma_ι_comp_presheafSumFormulaB_inv`, the left-hand leg becomes `η_X` at
`F(U)` applied to

`(Stacks.PullbackColimit.pullbackIso _).inv` of
`Stacks.Sites.ComponentModuleSumFormula.sumFormulaLeg` of
`(…extendScalarsIdIso _).inv` of the pure tensor `1 ⊗ y|_ψ`,

while the right-hand leg is, by `CategoryTheory.PresheafOfModules.homEquiv_app_pullbackAdjUnit`,
the restriction along `ψ` and `(φ, 𝟙)` of `η_X` at `F(V)` applied to
`CategoryTheory.PresheafOfModules.pullbackAdjUnit` of `y`. So `η_X` factors out by naturality and
the residue is an identity between sections of the presheaf-level pullback alone:
`Stacks.PullbackMonoidalSite.pullbackIso_inv_germ` identifies the right-hand side's
`…pullbackAdjUnit` with the germ at the identity index, and
`Stacks.PullbackColimit.germ_eq_map_unit` together with
`Stacks.PullbackColimit.germ_restrict` identify the germ at the index
`CategoryTheory.CocontinuousSimplicialSite.componentCostructuredArrow` that
`Stacks.Sites.ComponentModuleSumFormula.sumFormulaLeg_app` produces with its restriction.

Two elementwise readings are needed for that, and both now exist. One is
`Stacks.PullbackModel.extendScalarsAdjunction_homEquiv_app_apply`, the transpose along extension
of scalars on a section, supplied in the generic file where its siblings live —
`Stacks.PullbackModel.homEquiv_apply_tmul` is the `ModuleCat`-level statement and does not give
it, because `CategoryTheory.Adjunction.homEquiv` is derived from the unit rather than being a
field. The other is supplied here:
`CategoryTheory.CocontinuousSimplicialSite.extendScalarsIdIso_hom_app_tmul` and
`…extendScalarsIdIso_inv_app_apply`. That comparison is a
`CategoryTheory.Adjunction.leftAdjointUniq`, so it has no elementwise description by unfolding;
the pattern `Stacks.PullbackMonoidalSite.pullbackIso_hom_pullbackAdjUnit` uses for the other
`leftAdjointUniq` on this path applies verbatim, with
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` in place of
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`: the second adjunction is
`CategoryTheory.Adjunction.id`, whose unit is the identity, so the transpose of the comparison is
the identity and reading the transpose on a section is the whole of the proof.

*A measurement about the identity natural transformation.* In the statements of those two
readings the ring map at `V` must be written `CategoryTheory.NatTrans.app (𝟙 S) V` and not
`(𝟙 S).app V`. The two elaborate to the same term, but the field-notation spelling has to put
`𝟙 S`'s type into a form whose head is a constant — it is `CategoryStruct.toQuiver.1 S S` as
written — and that is a `whnf` deterministic timeout at 200000 heartbeats inside the pure tensor,
while `CategoryTheory.NatTrans.app (𝟙 S) V` costs nothing. Outside an expected type the same
field access fails outright, with `Invalid field notation` naming that type.

*Why the comparison is taken apart on sections and not as a morphism.* Identifying
`Stacks.Sheaves.RingedToposModules.pushforwardModules` at
`AlgebraicGeometry.RingedToposHom.toModulesHom` with
`AlgebraicGeometry.RingedToposHom.pushforwardModules` *underneath* `Sheaf.moduleSheafFunctor` —
which is what the morphism-level statement
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id`
asks for — is refused outside
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullback.lean`, with
`CategoryTheory.Limits.getLimitCone` named as the definition whose body the module system does
not expose. That is a visibility limit and not a heartbeat limit, so raising a heartbeat budget
would not help. On *sections* there is no such obstruction: both readings of the direct image
have the direct image of the underlying sheaf of sets for their underlying sheaf of sets, by
`Stacks.Sheaves.RingedToposModules.moduleSheaf_pushforwardModules` and
`AlgebraicGeometry.RingedToposHom.pushforwardModulesUnderlyingIso`, each an `Eq.refl`, and the
whole second factor drops by `Eq.refl` at these concrete arguments. The hypothesis of
`…moduleSumFormulaLegEqB_of_ranπ` is spelled on sections for exactly this reason.

*Proof style.* Every proof here is a term. The goals are only type-correct after unfolding
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf`, so `simp` reports that it made no
progress and `rw` cannot find its pattern; the measurements are in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaLegCaseB.lean`.

*Two measurements of this file's own.* First, splitting the composite with
`CategoryTheory.Functor.map_comp` and `CategoryTheory.Category.assoc` before dropping the second
factor is a *kernel* deterministic timeout, even though each half elaborates: the kernel is asked
to reduce the associativity witness at the category of sheaves of modules on the degree-`n`
component. Dropping the whole second factor in one `Eq.refl`, which is what
`…moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app` does, costs
nothing.

Second, the trailing comparison
`Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso` cannot be cancelled as an
identity *morphism* at these arguments, and the obstruction is the one the implementation notes of
`…ComponentRingedTopos.ModuleSumFormulaLegCaseB` record: the two definitionally equal spellings of
the underlying presheaf of the Kan extension cannot be crossed *underneath*
`Stacks.SheafOfModules.ranPushforward`, as three formulations show. Stating that the comparison is
the
identity at the spelling `(u_φ)^{op}.ran.obj T.val.presheaf` is `Eq.refl` and free; stating it at
the spelling `((ranPushforward …).obj ((restrictScalars …).obj T.val)).presheaf`, which is what
`CategoryTheory.Category.comp_id` would need, is a kernel deterministic timeout; and supplying
that object to `CategoryTheory.Category.comp_id` explicitly moves the timeout to `whnf` at
elaboration. The comparison is therefore removed on a *section*, by
`…toPresheaf_map_ranPushforwardRestrictScalarsIso_hom_app_apply`, where the crossing happens at
one object of the site and each side unfolds to the right Kan extension of the same presheaf.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sites.ComponentModuleSumFormula

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  isRightAdjointPushforwardComponentB

/-- **The comparison of the two readings of the direct image of modules is, on sections, its
first factor alone.** The second factor of
`CategoryTheory.CocontinuousSimplicialSite.transitionRingedToposPushforwardModulesIsoB` is
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`, which is the identity on sections by
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso_hom_app_val_app`; so a morphism into
the direct image of `AlgebraicGeometry.RingedToposHom.pushforwardModules` which ends in the whole
comparison is, read on a section of the underlying sheaf of sets, the one which ends in
`…transitionPushforwardModulesIsoB` alone.

This is where the obstruction recorded in the implementation notes is passed: on sections the two
readings of the direct image have the same underlying sheaf of sets by `Eq.refl`, and the whole
identification is one. -/
theorem moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m))
    (A : X ⟶ (Stacks.SheafOfModules.pushforwardCocontinuous.{u} (transitionFunctorB C φ)
      (fSharpB C P φ)).obj T)
    (V : ((situation C).component n)ᵒᵖ)
    (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V) :
    ((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
          (A ≫ (transitionRingedToposPushforwardModulesIsoB C P φ).hom.app T)).hom.app V y =
      ((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
          ((transitionPushforwardModulesIsoB C P φ).hom.app T)).hom.app V
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map A).hom.app V y) :=
  rfl

/-- **The leg of the Kan extension absorbs the comparison of the two direct images along the
cocontinuous transition functor.** On underlying sheaves of sets,
`CategoryTheory.CocontinuousSimplicialSite.transitionPushforwardModulesIsoB` is Mathlib's
comparison `CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves` for the forgetful functor
of abelian groups, and `Stacks.SheafOfModules.ranπ_ranCompIso_hom_app` says that comparison
carries the leg at `(U, ψ)` of the limit cone computing the extension of the underlying presheaf
of sets to the leg of the limit cone computing the extension at `AddCommGrpCat`. -/
theorem ranπ_moduleSheafFunctor_map_transitionPushforwardModulesIsoB_hom_app
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m)) (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (z : (Sheaf.moduleSheaf (ringSheafB C P n)
      ((Stacks.SheafOfModules.pushforwardCocontinuous.{u} (transitionFunctorB C φ)
        (fSharpB C P φ)).obj T)).obj.obj V) :
    Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
        (Sheaf.moduleSheaf (ringSheafB C P m) T).obj V j
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
          ((transitionPushforwardModulesIsoB C P φ).hom.app T)).hom.app V z) =
      (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op T.val.presheaf V j).hom z :=
  Stacks.SheafOfModules.ranπ_ranCompIso_hom_app (transitionFunctorB C φ) T.val.presheaf V j z

/-- **The left-hand leg of the case-(B) leg equation, with the comparison of the two direct
images removed.** The leg at `(U, ψ)` of the transpose of the summand inclusion followed by
`…transitionRingedToposPushforwardModulesIsoB`, read on a section, is the leg of the right Kan
extension at the sheaf of modules itself, applied to the image of the section under the transpose
alone.

This is the left-hand side of the hypothesis of
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_ranπ`, with the whole
comparison gone. It is stated for an arbitrary morphism `A` into the direct image along the
cocontinuous transition functor, so that
`…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map` can be
applied to the transpose afterwards. -/
theorem ranπ_moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m))
    (A : X ⟶ (Stacks.SheafOfModules.pushforwardCocontinuous.{u} (transitionFunctorB C φ)
      (fSharpB C P φ)).obj T)
    (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V) :
    Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
        (Sheaf.moduleSheaf (ringSheafB C P m) T).obj V j
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
          (A ≫ (transitionRingedToposPushforwardModulesIsoB C P φ).hom.app T)).hom.app V y) =
      (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op T.val.presheaf V j).hom
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map A).hom.app V y) :=
  (congrArg (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
      (Sheaf.moduleSheaf (ringSheafB C P m) T).obj V j)
    (moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app
      C P φ X T A V y)).trans
    (ranπ_moduleSheafFunctor_map_transitionPushforwardModulesIsoB_hom_app C P φ T V j _)

/-- **A morphism of sheaves of modules, read on a section of the underlying sheaf of sets, is its
underlying presheaf morphism on that section.** The underlying sheaf of sets of a sheaf of modules
is the underlying presheaf of abelian groups composed with the forgetful functor, so this holds by
definition.

It is stated at the sheaves of rings of case (B) rather than in general because that is the
spelling of its call site: it is what carries
`…ranπ_moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app` to the
description of the transpose on underlying presheaves of modules. -/
theorem moduleSheafFunctor_map_hom_app_apply (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n : SimplexCategory)
    (X Y : _root_.SheafOfModules.{u} (ringSheafB C P n)) (A : X ⟶ Y)
    (V : ((situation C).component n)ᵒᵖ)
    (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V) :
    ((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map A).hom.app V y =
      (((PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map A.val).app V).hom y :=
  rfl

/-- **The trailing comparison of the transpose is the identity on underlying presheaves.**
`Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso`, which moves a restriction of
scalars past the right Kan extension, is built from
`CategoryTheory.PresheafOfModules.homMk` at an identity natural transformation, so the forgetful
functor to presheaves of abelian groups sends it to that identity. -/
theorem toPresheaf_map_ranPushforwardRestrictScalarsIso_hom_app
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m)) :
    (PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map
        ((Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.{u}
          (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val) =
      𝟙 ((transitionFunctorB C φ).op.ran.obj T.val.presheaf) :=
  rfl


/-- **The underlying presheaf morphism of a composite ending in the trailing comparison, split.**
This is `CategoryTheory.Functor.map_comp` for
`CategoryTheory.PresheafOfModules.toPresheaf`, instantiated at the comparison that moves a
restriction of scalars past the right Kan extension. It is stated rather than used inline because
the two factors have to be supplied explicitly: a `congrArg` motive whose abstracted variable has
a metavariable type leaves `CategoryTheory.Category` unresolved. -/
theorem toPresheaf_map_comp_ranPushforwardRestrictScalarsIso_hom_app
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m))
    (p : X.val ⟶ (Stacks.SheafOfModules.ranPushforward.{u} (transitionFunctorB C φ)
      (Stacks.SheafOfModules.RestrictRan.unitRingHom (transitionFunctorB C φ)
        (T := (ringSheafB C P n).obj))).obj
      ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj T.val)) :
    (PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map
        (p ≫ (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.{u}
          (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val) =
      (PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map p ≫
        (PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map
          ((Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.{u}
            (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val) :=
  (PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map_comp p
    ((Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.{u}
      (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val)

/-- **The trailing comparison fixes every section.** This is
`…toPresheaf_map_ranPushforwardRestrictScalarsIso_hom_app` read on a section, and it is how the
comparison is removed from the chain below.

*The reading on a section is the affordable one.* Removing the comparison as an identity *morphism*
means forming `f ≫ 𝟙` and cancelling it with `CategoryTheory.Category.comp_id`, and that is
unaffordable at these arguments however it is arranged: the identity has to be typed at one of the
two spellings of the Kan extension's underlying presheaf, and crossing the other spelling against
it *underneath* `Stacks.SheafOfModules.ranPushforward` is a deterministic timeout — in the kernel
when the crossing is left to `CategoryTheory.Category.comp_id`'s implicit argument, and at `whnf`
during elaboration when that argument is supplied. On a section the two spellings are crossed at
one object of the site, where each unfolds to the right Kan extension of the same presheaf, and
the whole statement is `Eq.refl`. -/
theorem toPresheaf_map_ranPushforwardRestrictScalarsIso_hom_app_apply
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m)) (V : ((situation C).component n)ᵒᵖ)
    (w : ((transitionFunctorB C φ).op.ran.obj T.val.presheaf).obj V) :
    (((PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map
          ((Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.{u}
            (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val)).app V).hom w = w :=
  rfl

/-- **The left-hand leg of the case-(B) leg equation, elementwise.** Let `A` be a morphism from a
sheaf of modules `X` on the degree-`n` component to the direct image along the cocontinuous
transition functor of `T`, and suppose its underlying presheaf morphism is the transpose along
`Stacks.SheafOfModules.RestrictRan.adjunction` of a morphism `E` out of the restriction of
presheaves of modules along `u_φ`, followed by the comparison that moves the restriction of
scalars past the right Kan extension. That is the shape in which
`…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map` describes the
transpose of the `φ`th summand inclusion of `…componentModuleSumFormulaB`.

Then the leg at `(U, ψ)` of `A` followed by the comparison
`…transitionRingedToposPushforwardModulesIsoB`, read on a section `y`, is `E` at `U` applied to
the restriction of `y` along `ψ`. **Nothing of the two direct images, of the right Kan extension
or of the adjunction is left in the right-hand side**: this is the left-hand side of the
hypothesis of `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB_of_ranπ`,
computed.

The morphism `E` and the description `hA` of `A` are arguments rather than written out, so that
the statement is short enough to read and so that the chain is run once; instantiating `hA` at
`…homEquiv_sigma_ι_comp_componentModuleSumFormulaB_hom_app_val_eq_pushforward₀_map` gives the
left-hand leg at the actual transpose, with `E` the extension-of-scalars transpose of the
presheaf-level summand inclusion followed by the degree-`m` restriction of `η_X`. -/
theorem ranπ_moduleSheafFunctor_map_comp_eq_sourceMap (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m))
    (A : X ⟶ (Stacks.SheafOfModules.pushforwardCocontinuous.{u} (transitionFunctorB C φ)
      (fSharpB C P φ)).obj T)
    (E : (PresheafOfModules.pushforward₀.{u} (transitionFunctorB C φ)
          (ringSheafB C P n).obj).obj X.val ⟶
      (PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj T.val)
    (hA : A.val =
      (Stacks.SheafOfModules.RestrictRan.adjunction (transitionFunctorB C φ)
            (ringSheafB C P n).obj).homEquiv X.val
          ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj T.val) E ≫
        (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.{u}
          (transitionFunctorB C φ) (ringTransitionB C P φ)).hom.app T.val)
    (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V) :
    Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
        (Sheaf.moduleSheaf (ringSheafB C P m) T).obj V j
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
          (A ≫ (transitionRingedToposPushforwardModulesIsoB C P φ).hom.app T)).hom.app V y) =
      ((Stacks.SheafOfModules.RestrictRan.sourceMap (transitionFunctorB C φ) X.val
            ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj T.val)
            E).app j.right).hom
        ((X.val.presheaf.map j.hom).hom y) := by
  have h : ∀ t t' : X.val.presheaf ⟶ (transitionFunctorB C φ).op.ran.obj T.val.presheaf, t = t' →
      (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op T.val.presheaf V j).hom
        ((t.app V).hom y) =
      (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op T.val.presheaf V j).hom
        ((t'.app V).hom y) := fun _ _ e => e ▸ rfl
  refine Eq.trans
    (ranπ_moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app
      C P φ X T A V j y) ?_
  refine Eq.trans (congrArg
    (fun t : X.val ⟶ ((Stacks.SheafOfModules.pushforwardCocontinuous.{u}
        (transitionFunctorB C φ) (fSharpB C P φ)).obj T).val =>
      (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op T.val.presheaf V j).hom
        ((((PresheafOfModules.toPresheaf.{u} (ringSheafB C P n).obj).map t).app V).hom y)) hA) ?_
  refine Eq.trans (h _ _
    (toPresheaf_map_comp_ranPushforwardRestrictScalarsIso_hom_app C P φ X T _)) ?_
  refine Eq.trans (congrArg
    (fun z => (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op T.val.presheaf V j).hom z)
    (toPresheaf_map_ranPushforwardRestrictScalarsIso_hom_app_apply C P φ T V _)) ?_
  refine Eq.trans (h _ _
    (Stacks.SheafOfModules.RestrictRan.toPresheaf_map_adjunction_homEquiv
      (transitionFunctorB C φ) (ringSheafB C P n).obj X.val
      ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj T.val) E)) ?_
  exact Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ_apply_addCommGrp
    (transitionFunctorB C φ).op
    (Stacks.SheafOfModules.RestrictRan.sourceMap (transitionFunctorB C φ) X.val
      ((PresheafOfModules.restrictScalars.{u} (ringTransitionB C P φ)).obj T.val) E) V j y

/-- **A composite of morphisms of sheaves of modules, read on a section.** It holds by
definition; it is stated because the two factors have to be supplied explicitly, a `congrArg`
motive whose abstracted variable has a metavariable type leaving `CategoryTheory.Category`
unresolved. -/
theorem moduleSheafFunctor_map_comp_hom_app (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n : SimplexCategory)
    (X Y Z : _root_.SheafOfModules.{u} (ringSheafB C P n)) (a : X ⟶ Y) (b : Y ⟶ Z)
    (V : ((situation C).component n)ᵒᵖ)
    (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V) :
    ((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map (a ≫ b)).hom.app V y =
      ((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map b).hom.app V
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map a).hom.app V y) :=
  rfl

/-- **The right-hand leg of the case-(B) leg equation, elementwise.** The leg at `(U, ψ)` of the
transpose of the canonical leg `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`, read
on a section `y`, is: the unit of `g_{n!} ⊣ g_n^*` on `y`, restricted along `ψ` and then along the
cross-fibre arrow `(φ, 𝟙)`.

The transpose is the unit followed by the direct-image transition of Stacks 09WF, by
`CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app`; on underlying sheaves
of sets that transition is the one of Stacks 09WF for sheaves of sets, by
`CategoryTheory.SimplicialSiteSituation.moduleSheafFunctor_map_restrictTransitionModules_app`,
and `…ranπ_restrictTransition` computes its leg.

**Nothing of the direct image or of the Kan extension is left in the right-hand side either**, so
with `…ranπ_moduleSheafFunctor_map_comp_eq_sourceMap` for the other side the hypothesis of
`…moduleSumFormulaLegEqB_of_ranπ` is reduced to an equation between two restrictions of sections
of the underlying sheaf of sets of `g_{n!}X`. -/
theorem ranπ_moduleSheafFunctor_map_homEquiv_moduleSumFormulaLeg_app
    (C : CocontinuousSimplicialSite.{u})
    (P : Sheaf (situation C).totalTopology CommRingCat.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n)) (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (y : (Sheaf.moduleSheaf (ringSheafB C P n) X).obj.obj V) :
    Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
        (Sheaf.moduleSheaf (ringSheafB C P m)
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))).obj V j
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
          (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X
            (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
            (((situation C).moduleSumFormulaLeg P φ).app X))).hom.app V y) =
      (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
              (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)).obj).app
          j.right
        ((((situation C).restrict n).obj
              (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
                (((situation C).componentModuleLowerShriek
                  (totalRingSheafB C P) n).obj X))).obj.map j.hom
          (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
            (((situation C).componentModuleLowerShriekAdjunction
              (totalRingSheafB C P) n).unit.app X)).hom.app V y)) := by
  refine Eq.trans (congrArg
    (fun t : X ⟶ ((situation C).transitionRingedToposHom P φ).pushforwardModules.obj
        (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)) =>
      Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
        (Sheaf.moduleSheaf (ringSheafB C P m)
          (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
            (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))).obj V j
        (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map t).hom.app V y))
    ((situation C).homEquiv_moduleSumFormulaLeg_app P φ X)) ?_
  refine Eq.trans (congrArg
    (fun z => Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
      (Sheaf.moduleSheaf (ringSheafB C P m)
        (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))).obj V j z)
    (moduleSheafFunctor_map_comp_hom_app C P n X
      (((situation C).componentModuleRestriction (totalRingSheafB C P) n).obj
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X))
      (((situation C).transitionRingedToposHom P φ).pushforwardModules.obj
        (((situation C).componentModuleRestriction (totalRingSheafB C P) m).obj
          (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)))
      (((situation C).componentModuleLowerShriekAdjunction (totalRingSheafB C P) n).unit.app X)
      (((situation C).restrictTransitionModules P φ).app
        (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)) V y)) ?_
  exact ranπ_restrictTransition C φ
    (Sheaf.moduleSheaf.{u, u, u} (totalRingSheafB C P)
      (((situation C).componentModuleLowerShriek (totalRingSheafB C P) n).obj X)) V j
    (((Sheaf.moduleSheafFunctor (ringSheafB C P n)).map
      (((situation C).componentModuleLowerShriekAdjunction
        (totalRingSheafB C P) n).unit.app X)).hom.app V y)

/-- **The identity extension of scalars, on a pure tensor.**
`CategoryTheory.CocontinuousSimplicialSite.extendScalarsIdIso` is a
`CategoryTheory.Adjunction.leftAdjointUniq`, so it has no description by unfolding; this reads it
on sections. Its forward direction sends the pure tensor `1 ⊗ m` to `m`.

The proof is the pattern `Stacks.PullbackMonoidalSite.pullbackIso_hom_pullbackAdjUnit` uses for
the other `leftAdjointUniq` on this path: the transpose of the comparison is the unit of the
second adjunction, `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app`, and here that
second adjunction is `CategoryTheory.Adjunction.id`, whose unit is the identity; the transpose on
a section is `Stacks.PullbackModel.extendScalarsAdjunction_homEquiv_app_apply`. -/
theorem extendScalarsIdIso_hom_app_tmul {D : Type u} [SmallCategory D]
    (S : Dᵒᵖ ⥤ CommRingCat.{u})
    (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) (V : Dᵒᵖ) (m : M.obj V) :
    PresheafOfModules.Hom.app ((extendScalarsIdIso S).hom.app M) V
        (Stacks.PullbackModel.tmul (NatTrans.app (𝟙 S) V).hom 1 m) = m :=
  (Stacks.PullbackModel.extendScalarsAdjunction_homEquiv_app_apply (𝟙 S)
      ((extendScalarsIdIso S).hom.app M) V m).symm.trans
    (PresheafOfModules.hom_congr_apply'
      (Adjunction.homEquiv_leftAdjointUniq_hom_app
        (Stacks.PullbackModel.extendScalarsAdjunction (𝟙 S)) Adjunction.id M) V m)

/-- **The identity extension of scalars, inverted, on a section.** The backward direction of
`CategoryTheory.CocontinuousSimplicialSite.extendScalarsIdIso` sends a section `m` to the pure
tensor `1 ⊗ m`.

This is the reading the presheaf-level formula needs: `…presheafSumFormulaB` inserts the inverse
of this comparison, so a section fed to the formula is first turned into a pure tensor. -/
theorem extendScalarsIdIso_inv_app_apply {D : Type u} [SmallCategory D]
    (S : Dᵒᵖ ⥤ CommRingCat.{u})
    (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) (V : Dᵒᵖ) (m : M.obj V) :
    PresheafOfModules.Hom.app ((extendScalarsIdIso S).inv.app M) V m =
      Stacks.PullbackModel.tmul (NatTrans.app (𝟙 S) V).hom 1 m :=
  (congrArg (PresheafOfModules.Hom.app ((extendScalarsIdIso S).inv.app M) V)
      (extendScalarsIdIso_hom_app_tmul S M V m)).symm.trans
    (PresheafOfModules.hom_congr_apply' ((extendScalarsIdIso S).hom_inv_id_app M) V
      (Stacks.PullbackModel.tmul (NatTrans.app (𝟙 S) V).hom 1 m))

end CategoryTheory.CocontinuousSimplicialSite

end
