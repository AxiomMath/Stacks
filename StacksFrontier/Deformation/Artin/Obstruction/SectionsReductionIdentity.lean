module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsReductionMap

/-!
# The remaining half of condition (iii) of Stacks 07YG for the example of Stacks 07YH

`Deformation.Artin.SectionsSheaf.sectionsPresheafOver_map_quotHom` says that the restriction map
of the functor `F` of [Stacks, Tag 07YH] is the canonical reduction
`Deformation.Artin.SectionsSheaf.reductionMap`, `𝓕_{A'} ⟶ i_* 𝓕_A`, on global sections. What
condition (iii) still owes is the identification of that reduction with the **third map of the
sheaf-level sequence of clause (2)**,

```
𝓕_{A'} ≅ 𝓕_{A'} ⊗_{A'} A' ⟶ 𝓕_{A'} ⊗_{A'} A ≅ i_*(𝓕_A ⊗_A A) ≅ i_* 𝓕_A,
```

built from `Deformation.Artin.SectionsSheaf.tensorSheafFunctorObjSelf`, the map induced by
`A' → A`, and `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` at `M = A`.

This file proves that identification in the bifunctor spelling of the tensor product. The one
equation of morphisms of structure sheaves it used to be reduced to is
`Deformation.Artin.SectionsSheaf.reductionUnitHom_comp_modulePullbackObjUnitIso`, and what is
left is the transport of the conclusion into the source's own spelling.

## Main definitions

* `Deformation.Artin.SectionsSheaf.quotCoeff` — the ring map `φ` read as a map of `A'`-modules
  `A' ⟶ A`, which is the middle map of the sequence `0 → I → A' → A → 0`.
* `Deformation.Artin.SectionsSheaf.reductionUnitHom` — **the structure-sheaf component of the
  third map**: the morphism `𝒪_{W_{A'}} ⟶ i_*(π_A^* Ã)` obtained from `quotCoeff`, the comparison
  of [Stacks, Tag 01I9] and the affine base-change isomorphism of [Stacks, Tag 02KG].

## Main results

* `Deformation.Artin.SectionsSheaf.reductionMap_eq_tensorProjectionFormula` — **the canonical
  reduction is the projection-formula composite** of the structure-sheaf component: the inverse
  left unitor, that component in the first tensor factor, the projection-formula map of the
  immersion, and the left unitor together with `baseChangeSheafIso` in the second.
  Unconditional.
* `Deformation.Artin.SectionsSheaf.reductionUnitHom_comp_modulePullbackObjUnitIso` — **the
  composite of [Stacks, Tag 01I9] and [Stacks, Tag 02KG] at the module `A` is the canonical
  `𝒪_{W_{A'}} ⟶ i_* 𝒪_{W_A}`**, and `..reductionUnitHom_eq` is the contraction of the two affine
  factors of `reductionUnitHom` into the structure morphism of `Spec φ` that it goes through.
* `Deformation.Artin.SectionsSheaf.reductionMap_eq_unit_comp` — the reduction is the unit of the
  pullback--pushforward adjunction followed by the direct image of `baseChangeSheafIso`.
* `Deformation.Artin.SectionsSheaf.unit_comp_eq_tensorProjectionFormulaGen` — **the unit of
  `i^* ⊣ i_*` as a projection-formula composite**, at variable schemes and modules: the same
  identity `reductionMap_eq_tensorProjectionFormula` needs, with every scheme, module and arrow
  a variable, so that its use is a substitution rather than a definitional comparison at a
  concrete fibre product. Its `γ` is spelled through `structureSheafRing` and
  `X.toLocallyRingedSpace.toSheafedSpace`, the spellings `modulePullbackObjUnitIso` gives, for
  the reason the "what is not done" of this file counts out.
* `Deformation.Artin.SectionsSheaf.tensorSheafFunctorObjSelf_hom` and `..._inv` — the unitor
  `𝓕 ⊗_R R ≅ 𝓕` read in the uncurried spelling of
  `Stacks.SheafOfModules.Tensor.sheafTensor`. Both hold by
  `rfl`; together with `..tensorSheafFunctor_map_eq`, which is the same for the functor on
  morphisms and already lives in
  `StacksFrontier/Deformation/Artin/Obstruction/SectionsCoefficientIdentity.lean`, they are the
  dictionary between the flipped `Stacks.SheafOfModules.Tensor.sheafTensor` spelling that
  `tensorSheafFunctor` is built from and the uncurried spelling the projection formula is stated
  in.
* `Deformation.Artin.SectionsSheaf.immersionProjectionFormulaIso_hom` — the projection-formula
  isomorphism of the immersion is `CategoryTheory.adjunctionTensorMap`, the canonical adjoint
  transpose of the comparison of [Stacks, Tag 01CD], and not an unspecified isomorphism of
  objects.
* `Deformation.Artin.SectionsSheaf.eqToHom_tensorSheafFunctor_obj_eq` and `..._symm` — the two
  transports between the two spellings of `𝓕 ⊗_R M` are identities, stated at a variable `π`.
* `Deformation.Artin.SectionsSheaf.pushforwardTensorSheafIso_eq` —
  `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` read as the chain of five
  comparisons it is defined to be, so that `CategoryTheory.Iso.trans_hom` applies to it, and
  `..pushforwardTensorSheafIso_hom` the same chain read on `hom`.
* `Deformation.Artin.SectionsSheaf.tensorTransport` — **the abstract assembly** of the transport
  into the source's spelling: four arrows constrained to be the four factors of the third map of
  the sequence of clause (2) compose to the projection-formula composite of the single
  first-factor arrow they amount to. Its application to the concrete data is what the "what is
  not done" of this file measures.

## Implementation notes

The reduction is
`Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_leftUnitObj_comp`, the
left-handed counterpart of `..adjunctionTensorMap_unitObj_comp`:
the projection-formula map with a *unit object* in its first argument, composed with the two left
unitors, is the unit of the adjunction — which is exactly `reductionMap` by
`reductionMap_eq_unit_comp`. Its two standing hypotheses are both already in the library:
`Stacks.RingedSpace.comparison_leftUnitor` is the left-unitor coherence of Tag 01CD, and
`Stacks.RingedSpace.tensorSheafUnitLeftIso_naturality` the naturality of the unitor. Its one
hypothesis on the data is `hunit`, and that is the only mathematics left.

The goal of `reductionUnitHom_comp_modulePullbackObjUnitIso` is **not type-correct at the
`implicit` transparency level** — the unit object it mentions is spelled
`SheafOfModules.unit (structureRingSheaf (pullback (Over.mk t).hom q).toRingedSpace)` where the
`Scheme.Modules` functors around it want `(pullback (Over.mk t).hom q).Modules` — so no `rw` or
`simp` fires on it and its proof, like the transport below, is a term built from `Eq.trans` and
`congrArg`. The general input it uses,
`Stacks.AlgebraicGeometry.AffineBaseChange.baseChangeNatTrans_structureUnitHom`, is stated at
**variable** schemes and with both spellings reconciled by the ascribed
`..AffineBaseChange.unitObj`, which is what makes the tactic layer usable there.

`reductionMap_eq_unit_comp` is **not** proved by `rfl`, although it is true by `rfl`: the kernel
times out on it. Unfolding `reductionMap` exposes `Scheme.Modules.pullbackCongr` applied to
`baseChangeMap_comp_snd q (quotHom φ t)`, and comparing that against the same proof term inside
`baseChangeSheafIso` is a defeq check at a concrete fibre product, which asks for
`Limits.getLimitCone`. The cure is the one `reductionMap_eq_iff` already uses: go through the
adjunction bijection, whose round trip `Equiv.symm_apply_apply` leaves `baseChangeSheafIso`
opaque. This is the same effect the "implementation notes" of
`StacksFrontier/Deformation/Artin/Obstruction/SectionsReductionMap.lean` record for statements.

The three `rfl` lemmas about `tensorSheafFunctorObjSelf` are stated at a **variable** morphism
`π : X ⟶ Spec R` and a variable module, not at the base-change projections. At the fibre products
the same `rfl`s are not cheap, for the reason above.

## What is not done

**The transport to the source's spelling.** `reductionMap_eq_tensorProjectionFormula` is
stated in the uncurried spelling of `Stacks.SheafOfModules.Tensor.sheafTensor`; the sequence of
clause (2) is stated through `tensorSheafFunctor` and
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`. The three `rfl` lemmas above
are the dictionary for the two unitors and for the functor on morphisms, and
`immersionProjectionFormulaIso_hom` for the projection formula. What is missing is the
corresponding *assembly*: the four dictionary lemmas above have to be composed, and the
composites of the uncurried `Stacks.SheafOfModules.Tensor.sheafTensor` on morphisms collapsed by
`CategoryTheory.Functor.map_comp` together with three identities in the product category.

**Three direct routes fail in the tactic layer.** Writing the collapsed
composite out and proving it by `rfl` — even with `immersionProjectionFormulaIso` kept behind
its constant, so that no `asIso` is unfolded — dies with `(kernel) deterministic timeout`; the
cost is the unfolding of the flipped `Stacks.SheafOfModules.Tensor.sheafTensor`, which the
implementation notes of
`StacksFrontier/Deformation/Artin/Obstruction/SectionsBaseChangeTensor.lean` already warn is
affordable only once per end.
`dsimp only [Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso]` makes the goal
**not type-correct at the `implicit` transparency level**
(`(pullback (Over.mk t).hom q).ringCatSheaf`, a `TopCat.Sheaf`, against
`CategoryTheory.Sheaf (Opens.grothendieckTopology ...)`), and every subsequent `simp only` refuses
the goal. And `rw [tensorSheafFunctorObjSelf_inv]` reports
"did not find an occurrence of the pattern" on a goal that visibly contains it, for the same
reason: the motive `rw` builds crosses between `X.ringCatSheaf` and
`structureRingSheaf X.toRingedSpace`, which the motive type-check will not make.

So the assembly has to be written in **term mode**, with `Eq.trans` and `congrArg` and no
`rw`, which is the cure the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackSheafTensorMonoidal.lean` prescribe for
this clash: cross between the two spellings inside a defeq-tolerant `:=`.

**Both halves of that assembly are here.** The
dictionary is complete: `pushforwardTensorSheafIso_hom` reads
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` on `hom` as the five arrows
the abstract assembly wants, and `tensorTransport` is the abstract assembly itself — every arrow
a variable constrained by an equation, in the style of
`Deformation.Artin.SectionsSheaf.tensorAssemble`. Each of the two checks in seconds on its own.
What does **not** check is their *application* to the concrete data:
`tensorTransport (Functor.uncurry.obj (Tensor.sheafTensor …)) … (Scheme.Modules.pushforward …)`
with
`hα := tensorSheafFunctorObjSelf_inv`, `hβ := ..tensorSheafFunctor_map_eq`,
`hγ := pushforwardTensorSheafIso_hom`, `hδ := congrArg _ tensorSheafFunctorObjSelf_hom`,
`hr := rfl`, the two transports and `hP := immersionProjectionFormulaIso_hom` elaborates and
then dies with `(kernel) deterministic timeout`.

The cause is the following. `tensorTransport` types its four factors as
`Z ⟶ L.obj (U₁, Q)`, `L.obj (U₁, Q) ⟶ L.obj (U₂, Q)`, and so on — the **bifunctor** spelling —
while the four concrete factors are typed through `(tensorSheafFunctor π F).obj M`. So checking
the application makes the definitional comparison of the two spellings **once per factor**,
five times in one declaration, and the implementation notes of
`StacksFrontier/Deformation/Artin/Obstruction/SectionsBaseChangeTensor.lean` record that one
unfolding of the flipped `Stacks.SheafOfModules.Tensor.sheafTensor` per end is the whole
budget. Pre-stating the two
transports in the bifunctor spelling and the association of `reductionUnitHom` as named `rfl`
lemmas — so that those two comparisons move into declarations of their own — does **not** help:
it removes two of the five, and the application still times out (37 s to the kernel
timeout, against 11 s for the whole file without it).

What would remove the remaining three is an ascribed `def` for each of the four factors, typed
in the bifunctor spelling with the source-spelling term as its body — the cure
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackStrictUnit.lean` prescribes, which pays
one comparison per `def` and in its own kernel check. That is what is left to do, and it is
plumbing: no mathematics remains in the transport.

**`reductionMap_eq_tensorProjectionFormula` is proved, and what made it fit the kernel is
worth recording, because the same arithmetic governs the transport above.** Its proof is
`reductionMap_eq_unit_comp` composed with `unit_comp_eq_tensorProjectionFormulaGen` at the
base-change data, and the general identity is stated at variable schemes and modules and checks
on its own; but writing that instantiation directly under the statement timed the kernel out,
and so did four ways round it (spelling the bifunctor at
`Stacks.SheafOfModules.Tensor.sheafTensor ⟨(pullback _ _).toRingedSpace.presheaf, _⟩` rather
than at `(pullback _ _).sheaf`; splitting the instantiation off into a declaration of its own;
re-ascribing `reductionUnitHom` so that its codomain is spelled with `SheafOfModules.unit`
rather than `(tilde.functor A).obj (ModuleCat.of A A)`; and a `generalize` chain, which fails
in the *elaborator* instead — abstracting
`(Scheme.Modules.pullback (pullback.fst (quotOver φ t).hom q)).obj ((tilde.functor A).obj
(ModuleCat.of A A))`, the step the later scheme abstractions need, exhausts the heartbeat
budget on its own).

The cost comes in two sizes. A cross-spelling
comparison of two *objects* of a category at a concrete fibre product — here
`(modulePullback _).obj (SheafOfModules.unit (structureSheafRing (Spec A).toRingedSpace))`, the
source `modulePullbackObjUnitIso` gives its own comparison, against
`(Scheme.Modules.pullback _).obj ((tilde.functor A).obj (ModuleCat.of A A))`, the one
`reductionUnitHom` fixes — asks for the carrier of the pullback and so for
`Limits.getLimitCone`, and is worth about a third of a kernel check: two
independent copies of the statement of `reductionMap_eq_tensorProjectionFormula` fit in one
check together, and the statement pays exactly one, in `γ ×ₘ _`. A cross-spelling comparison
*inside* `CategoryTheory.Functor.map` of the uncurried
`Stacks.SheafOfModules.Tensor.sheafTensor`, on the other hand, fills a kernel check **by
itself**: the congruence on the arguments fails before it reaches the morphism, and what is
left is a `whnf` of the bifunctor, which the implementation notes of
`StacksFrontier/Deformation/Artin/Obstruction/SectionsBaseChangeTensor.lean` already price at one
per end.

So the discipline that makes such a statement provable is: **let the kernel cross between two
spellings at an object, never under a `Functor.map`.** Concretely,
`reductionMap_eq_tensorProjectionFormulaOfUnitHom` takes the comparison of [Stacks, Tag 01I9]
as a variable `γ` whose declared type is the one the statement's own `γ ×ₘ _` elaborates to —
including the spellings `structureSheafRing` rather than `structureRingSheaf` and
`X.toLocallyRingedSpace.toSheafedSpace` rather than `X.toRingedSpace`, which are the ones
`modulePullbackObjUnitIso` gives through `Scheme.Hom.toLRSHom.toShHom` — so that every argument
of the general identity is matched first-order, the helper's conclusion *is* the statement
syntactically, and the one object comparison that remains is the one the statement cannot avoid.
The γ binder of `unit_comp_eq_tensorProjectionFormulaGen` carries those same two spellings for
the same reason; at a variable scheme they cost nothing there.

Also not stated here is the site-level form; see the "what is not done" of
`StacksFrontier/Deformation/Artin/Obstruction/SectionsReductionMap.lean` for the
`Deformation.Artin.SiteAlgebra.Hom.specMap_comp_toScheme` bookkeeping that it needs in addition.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Deformation.Artin.SectionsSheaf

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (φ : A' ⟶ A) (t : Spec A' ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- The ring map `φ` as a map of `A'`-modules `A' ⟶ A`. -/
def quotCoeff :
    ModuleCat.of A' A' ⟶ (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A) :=
  ModuleCat.ofHom (X := ModuleCat.of A' A')
    (Y := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A))
    { toFun := φ.hom
      map_add' := map_add _
      map_smul' := fun a x => map_mul φ.hom a x }

section ObjSelf

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  (F : SheafOfModules.{u} X.ringCatSheaf)

/-- The unitor `𝓕 ⊗_R R ≅ 𝓕`, read in the bifunctor spelling. -/
theorem tensorSheafFunctorObjSelf_hom :
    (tensorSheafFunctorObjSelf π F).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          (((modulePullbackObjUnitIso π.toLRSHom.toShHom).hom ×ₘ 𝟙 F) :
            (((Scheme.Modules.pullback π).obj ((tilde.functor R).obj (ModuleCat.of R R)),
                F) : _ × _) ⟶
              (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), F)) ≫
        (tensorSheafUnitLeftIso X.toRingedSpace F).hom :=
  rfl

/-- The inverse unitor, read in the bifunctor spelling. -/
theorem tensorSheafFunctorObjSelf_inv :
    (tensorSheafFunctorObjSelf π F).inv =
      (tensorSheafUnitLeftIso X.toRingedSpace F).inv ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          (((modulePullbackObjUnitIso π.toLRSHom.toShHom).inv ×ₘ 𝟙 F) :
            ((SheafOfModules.unit (structureRingSheaf X.toRingedSpace), F) : _ × _) ⟶
              ((Scheme.Modules.pullback π).obj ((tilde.functor R).obj (ModuleCat.of R R)), F)) :=
  rfl

/-- The transport between the two spellings of `𝓕 ⊗_R M` is the identity: the equality it
transports along holds by `rfl`. Stated at a variable `π`, where the one unfolding of
the flipped `Stacks.SheafOfModules.Tensor.sheafTensor` it costs is affordable. -/
theorem eqToHom_tensorSheafFunctor_obj_eq (M : ModuleCat.{u} R) :
    eqToHom (tensorSheafFunctor_obj_eq π F M) = 𝟙 ((tensorSheafFunctor π F).obj M) :=
  rfl

/-- The same transport in the other direction. -/
theorem eqToHom_tensorSheafFunctor_obj_eq_symm (M : ModuleCat.{u} R) :
    eqToHom (tensorSheafFunctor_obj_eq π F M).symm =
      𝟙 (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).obj
        ((Scheme.Modules.pullback π).obj ((tilde.functor R).obj M), F)) :=
  rfl

end ObjSelf

/-- The structure-sheaf component of the third map of the sheaf-level sequence of clause (2). -/
def reductionUnitHom :
    SheafOfModules.unit
        (structureRingSheaf (pullback (Over.mk t).hom q).toRingedSpace) ⟶
      (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).obj
        ((Scheme.Modules.pullback (pullback.fst (quotOver φ t).hom q)).obj
          ((tilde.functor A).obj (ModuleCat.of A A))) :=
  (modulePullbackObjUnitIso (pullback.fst (Over.mk t).hom q).toLRSHom.toShHom).inv ≫
    (Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).map
        ((tilde.functor A').map (quotCoeff φ)) ≫
      (Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).map
          (tildePushforwardIso φ (ModuleCat.of A A)).inv ≫
        (affineBaseChangeIso φ t q ((tilde.functor A).obj (ModuleCat.of A A))).hom

/-- `reductionUnitHom` with its two affine factors contracted: the comparison of
[Stacks, Tag 01I9] at the module `A` turns the middle map of `0 → I → A' → A → 0` into the
structure morphism of `Spec φ`, by
`Stacks.AlgebraicGeometry.AffineBaseChange.tilde_map_comp_pushforwardTildeIso_inv`. -/
theorem reductionUnitHom_eq :
    reductionUnitHom φ t q =
      (modulePullbackObjUnitIso (pullback.fst (Over.mk t).hom q).toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).map
            (Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom (Spec.map φ)) ≫
          (affineBaseChangeIso φ t q ((tilde.functor A).obj (ModuleCat.of A A))).hom :=
  congrArg
    (fun z => (modulePullbackObjUnitIso
        (pullback.fst (Over.mk t).hom q).toLRSHom.toShHom).inv ≫ z)
    ((Category.assoc _ _ _).symm.trans
      (congrArg
        (fun u => u ≫ (affineBaseChangeIso φ t q
          ((tilde.functor A).obj (ModuleCat.of A A))).hom)
        ((Functor.map_comp _ _ _).symm.trans
          (congrArg
            (fun v => (Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).map v)
            (Stacks.AlgebraicGeometry.AffineBaseChange.tilde_map_comp_pushforwardTildeIso_inv
              φ (quotCoeff φ) (map_one φ.hom))))))

/-- **The equation `hunit`**: the composite of [Stacks, Tag 01I9] and the affine base-change
isomorphism of [Stacks, Tag 02KG] at the module `A` is the canonical
`𝒪_{W_{A'}} ⟶ i_* 𝒪_{W_A}`.

This is the whole mathematical content that the remaining half of condition (iii) of
[Stacks, Tag 07YG] for the example of [Stacks, Tag 07YH] was waiting on. It is the general
statement
`Stacks.AlgebraicGeometry.AffineBaseChange.baseChangeNatTrans_structureUnitHom` — that the
base-change morphism of a commutative square carries the structure morphism of `f` to the
structure morphism of `f'` — at the base-change square of a deformation situation, together
with `reductionUnitHom_eq`. -/
theorem reductionUnitHom_comp_modulePullbackObjUnitIso :
    reductionUnitHom φ t q ≫
        (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
          (modulePullbackObjUnitIso
            (pullback.fst (quotOver φ t).hom q).toLRSHom.toShHom).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap q (quotHom φ t))).unit.app
          (SheafOfModules.unit
            (structureRingSheaf (pullback (Over.mk t).hom q).toRingedSpace)) ≫
        (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
          (modulePullbackObjUnitIso
            (baseChangeMap q (quotHom φ t)).toLRSHom.toShHom).hom :=
  ((congrArg
        (fun z => z ≫ (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
          (modulePullbackObjUnitIso
            (pullback.fst (quotOver φ t).hom q).toLRSHom.toShHom).hom)
        (reductionUnitHom_eq φ t q)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
            (fun z => (modulePullbackObjUnitIso
              (pullback.fst (Over.mk t).hom q).toLRSHom.toShHom).inv ≫ z)
            ((Category.assoc _ _ _).trans
              (Stacks.AlgebraicGeometry.AffineBaseChange.baseChangeNatTrans_structureUnitHom
                (isPullback_baseChangeMap q (quotHom φ t)).flip.w))).trans
          (Iso.inv_hom_id_assoc _ _)))).trans
    (Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso
      (baseChangeMap q (quotHom φ t))).symm

/-- `reductionMap` is the unit followed by the direct image of `baseChangeSheafIso`. -/
theorem reductionMap_eq_unit_comp :
    reductionMap φ t q 𝓕 =
      (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap q (quotHom φ t))).unit.app
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕) ≫
        (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
          (baseChangeSheafIso φ t q 𝓕).hom :=
  (reductionMap_eq_iff φ t q 𝓕 _).mpr
    (((Scheme.Modules.pullbackPushforwardAdjunction
          (baseChangeMap q (quotHom φ t))).homEquiv _ _).symm_apply_apply
      (baseChangeSheafIso φ t q 𝓕).hom).symm

/-- The projection-formula isomorphism of the immersion is the canonical adjoint transpose of
the comparison of [Stacks, Tag 01CD], and not an unspecified isomorphism of objects. -/
theorem immersionProjectionFormulaIso_hom
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t)))
    (G : (pullback (quotOver φ t).hom q).Modules) :
    (immersionProjectionFormulaIso φ t q 𝓕 hi G).hom =
      adjunctionTensorMap
        (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap q (quotHom φ t)))
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (pullback (Over.mk t).hom q).sheaf)))
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (pullback (quotOver φ t).hom q).sheaf)))
        (comparisonNatTrans (baseChangeMap q (quotHom φ t)).toLRSHom.toShHom) G
        ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕) :=
  rfl

/-- `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`, read as the chain of five
comparisons it is defined to be. Holding by `rfl` -- the only step is the `letI` of the
closed-immersion instance -- it is what lets `CategoryTheory.Iso.trans_hom` be applied to it:
unfolding the definition inside the tactic layer instead makes the goal not type-correct at the
`implicit` transparency level. -/
theorem pushforwardTensorSheafIso_eq
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t))) (M : ModuleCat.{u} A) :
    Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso φ t q 𝓕 hi M =
      eqToIso (tensorSheafFunctor_obj_eq (pullback.fst (Over.mk t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
          ((ModuleCat.restrictScalars φ.hom).obj M)) ≪≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (pullback (Over.mk t).hom q).sheaf))).mapIso
          (Iso.prod ((Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).mapIso
              (tildePushforwardIso φ M).symm ≪≫
            affineBaseChangeIso φ t q ((tilde.functor A).obj M))
            (Iso.refl ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕))) ≪≫
        immersionProjectionFormulaIso φ t q 𝓕 hi ((Scheme.Modules.pullback
          (pullback.fst (quotOver φ t).hom q)).obj ((tilde.functor A).obj M)) ≪≫
        (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).mapIso
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (pullback (quotOver φ t).hom q).sheaf))).mapIso
            (Iso.prod (Iso.refl ((Scheme.Modules.pullback
                (pullback.fst (quotOver φ t).hom q)).obj ((tilde.functor A).obj M)))
              (baseChangeSheafIso φ t q 𝓕))) ≪≫
        (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).mapIso
          (eqToIso (tensorSheafFunctor_obj_eq (pullback.fst (quotOver φ t).hom q)
            ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕) M)).symm :=
  rfl

/-- **`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` on `hom`**, as the
composite of five arrows: the transport of `tensorSheafFunctor_obj_eq`, the comparisons of
[Stacks, Tag 01I9] and [Stacks, Tag 02KG] in the first tensor factor, the projection formula of
the immersion, `baseChangeSheafIso` in the second factor, and the transport back. This is
`pushforwardTensorSheafIso_eq` read on `hom`, and it is the `hγ` that `tensorTransport` below
consumes.

The projection formula is kept behind the constant `immersionProjectionFormulaIso`: writing
`CategoryTheory.adjunctionTensorMap` here instead — which is the same morphism, by
`immersionProjectionFormulaIso_hom` — makes the kernel time out, because the definitional
comparison of the two then has to be made inside a term that also carries five unfoldings of
the flipped `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
theorem pushforwardTensorSheafIso_hom
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t))) (M : ModuleCat.{u} A) :
    (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso φ t q 𝓕 hi M).hom =
      eqToHom (tensorSheafFunctor_obj_eq (pullback.fst (Over.mk t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
          ((ModuleCat.restrictScalars φ.hom).obj M)) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (pullback (Over.mk t).hom q).sheaf))).map
            (((Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).map
                  (tildePushforwardIso φ M).inv ≫
                (affineBaseChangeIso φ t q ((tilde.functor A).obj M)).hom) ×ₘ
              𝟙 ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)) ≫
          (immersionProjectionFormulaIso φ t q 𝓕 hi ((Scheme.Modules.pullback
              (pullback.fst (quotOver φ t).hom q)).obj ((tilde.functor A).obj M))).hom ≫
            (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
                (((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    (pullback (quotOver φ t).hom q).sheaf))).map
                  (𝟙 ((Scheme.Modules.pullback
                      (pullback.fst (quotOver φ t).hom q)).obj ((tilde.functor A).obj M)) ×ₘ
                    (baseChangeSheafIso φ t q 𝓕).hom)) ≫
              (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
                (eqToHom (tensorSheafFunctor_obj_eq (pullback.fst (quotOver φ t).hom q)
                  ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)
                  M).symm) :=
  congrArg Iso.hom (pushforwardTensorSheafIso_eq φ t q 𝓕 hi M)

/-- **The assembly of the transport, in the abstract.** For a tensor bifunctor `L` on `𝒞`, a
second one `L'` on `𝒟`, a functor `G : 𝒟 ⥤ 𝒞`, and four arrows `α`, `β`, `γ`, `δ` constrained to
be the four factors of the third map of the sheaf-level sequence of clause (2), the composite
`α ≫ β ≫ γ ≫ δ` is the projection-formula composite of the single arrow `r` that the three
first-factor arrows compose to.

Every arrow is a variable constrained by an equation rather than written out, the two transports
included, exactly as in `Deformation.Artin.SectionsSheaf.tensorAssemble`: the two spellings of
the tensor product of sheaves of modules on a scheme are definitionally equal and not
syntactically, so a conclusion written out in one of them would not match a goal written in the
other first-order. The product morphisms are taken apart by `CategoryTheory.Prod.hom_ext`,
composition in a product category being componentwise by `rfl`. -/
theorem tensorTransport {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (L : 𝒞 × 𝒞 ⥤ 𝒞) (L' : 𝒟 × 𝒟 ⥤ 𝒟) (G : 𝒟 ⥤ 𝒞)
    {U₀ U₁ U₂ Q Z : 𝒞} {V₀ V₁ Q₁ Y : 𝒟}
    (α : Z ⟶ L.obj (U₁, Q)) (β : L.obj (U₁, Q) ⟶ L.obj (U₂, Q))
    (γ : L.obj (U₂, Q) ⟶ G.obj (L'.obj (V₀, Y)))
    (δ : G.obj (L'.obj (V₀, Y)) ⟶ G.obj Y)
    (lamInv : Z ⟶ L.obj (U₀, Q)) (u₀ : U₀ ⟶ U₁) (u₁ : U₁ ⟶ U₂) (u₂ : U₂ ⟶ G.obj V₀)
    (r : U₀ ⟶ G.obj V₀)
    (e₁ : L.obj (U₂, Q) ⟶ L.obj (U₂, Q))
    (P P' : L.obj (G.obj V₀, Q) ⟶ G.obj (L'.obj (V₀, Q₁)))
    (b : Q₁ ⟶ Y) (c : V₀ ⟶ V₁)
    (e₂ : L'.obj (V₀, Y) ⟶ L'.obj (V₀, Y))
    (lam'Hom : L'.obj (V₁, Y) ⟶ Y)
    (hα : α = lamInv ≫ L.map (u₀ ×ₘ 𝟙 Q))
    (hβ : β = L.map (u₁ ×ₘ 𝟙 Q))
    (hγ : γ = e₁ ≫ L.map (u₂ ×ₘ 𝟙 Q) ≫ P' ≫ G.map (L'.map (𝟙 V₀ ×ₘ b)) ≫ G.map e₂)
    (hδ : δ = G.map (L'.map (c ×ₘ 𝟙 Y) ≫ lam'Hom))
    (hr : u₀ ≫ u₁ ≫ u₂ = r) (he₁ : e₁ = 𝟙 _) (he₂ : e₂ = 𝟙 _) (hP : P' = P) :
    α ≫ β ≫ γ ≫ δ =
      lamInv ≫ L.map (r ×ₘ 𝟙 Q) ≫ P ≫ G.map (L'.map (c ×ₘ b) ≫ lam'Hom) := by
  subst hα; subst hβ; subst hγ; subst hδ; subst hr; subst he₁; subst he₂; subst hP
  rw [show ((u₀ ≫ u₁ ≫ u₂) ×ₘ 𝟙 Q : ((U₀, Q) : 𝒞 × 𝒞) ⟶ (G.obj V₀, Q)) =
        (u₀ ×ₘ 𝟙 Q) ≫ (u₁ ×ₘ 𝟙 Q) ≫ (u₂ ×ₘ 𝟙 Q) from
      Prod.hom_ext rfl (by simp),
    show (c ×ₘ b : ((V₀, Q₁) : 𝒟 × 𝒟) ⟶ (V₁, Y)) = (𝟙 V₀ ×ₘ b) ≫ (c ×ₘ 𝟙 Y) from
      Prod.hom_ext (by simp) (by simp)]
  simp only [Functor.map_comp, Category.assoc, G.map_id, Category.id_comp, Category.comp_id]

/-- **The unit of `i^* ⊣ i_*` is the projection-formula composite of a structure-sheaf
component**, at variable data: for a morphism of schemes `i`, an `𝒪_{X'}`-module `Q`, an
`𝒪_X`-module `G` and arrows `c : 𝒪_{X'} ⟶ i_*G`, `γ : G ⟶ 𝒪_X` whose composite is the canonical
`𝒪_{X'} ⟶ i_*𝒪_X` (`hc`), and any `k : i^*Q ⟶ Y`, the unit at `Q` followed by `i_*k` is the
inverse left unitor, `c` in the first tensor factor, the projection-formula map of `i`, and
`(γ, k)` together with the left unitor on `X`.

This is `Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_leftUnitObj_comp` with
its data read through the `Scheme.Modules` functors, and it is stated at **variable** schemes and
modules for the reason the "implementation notes" above record: the abstract lemma types its
arrows through `Stacks.RingedSpace.pullbackFunctor` and `..tensorSheafUnitLeftIso`, so applying
it makes the definitional comparison with the `Scheme.Modules` spelling once per arrow, and at
the concrete fibre products of a deformation situation that fills a kernel check by itself. At
variable data each of those comparisons is between two spellings of a variable scheme, and the
instantiation below is a substitution. -/
theorem unit_comp_eq_tensorProjectionFormulaGen {X' X : Scheme.{u}} (i : X ⟶ X')
    (Q : X'.Modules) {G : X.Modules}
    (c : SheafOfModules.unit (structureRingSheaf X'.toRingedSpace) ⟶
      (Scheme.Modules.pushforward i).obj G)
    (γ : G ⟶ SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toSheafedSpace))
    (hc : c ≫ (Scheme.Modules.pushforward i).map γ =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit (structureRingSheaf X'.toRingedSpace)) ≫
        (Scheme.Modules.pushforward i).map (modulePullbackObjUnitIso i.toLRSHom.toShHom).hom)
    {Y : X.Modules} (k : (Scheme.Modules.pullback i).obj Q ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app Q ≫
        (Scheme.Modules.pushforward i).map k =
      (tensorSheafUnitLeftIso X'.toRingedSpace Q).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(X'.toRingedSpace).presheaf, (X'.toRingedSpace).IsSheaf⟩)).map (c ×ₘ 𝟙 Q) ≫
          adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction i)
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(X'.toRingedSpace).presheaf, (X'.toRingedSpace).IsSheaf⟩))
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩))
              (comparisonNatTrans i.toLRSHom.toShHom) G Q ≫
            (Scheme.Modules.pushforward i).map
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).map (γ ×ₘ k) ≫
                (tensorSheafUnitLeftIso X.toRingedSpace Y).hom) :=
  (Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_leftUnitObj_comp
    (Scheme.Modules.pullbackPushforwardAdjunction i)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(X'.toRingedSpace).presheaf, (X'.toRingedSpace).IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩))
    (comparisonNatTrans i.toLRSHom.toShHom)
    (tensorSheafUnitLeftIso X'.toRingedSpace)
    (tensorSheafUnitLeftIso X.toRingedSpace)
    (modulePullbackObjUnitIso i.toLRSHom.toShHom)
    (fun morphism => tensorSheafUnitLeftIso_naturality _ morphism)
    (fun moduleObj => comparison_leftUnitor i.toLRSHom.toShHom moduleObj)
    c γ hc Q k).symm

/-- `reductionMap_eq_tensorProjectionFormula` with the comparison `π_A^* Ã ≅ 𝒪_{W_A}` of
[Stacks, Tag 01I9] at `M = A` left as a **variable** `γ`, constrained by the one equation
`hγ` on it that the identity needs.

This is the instantiation of `unit_comp_eq_tensorProjectionFormulaGen` at the base-change data,
and it is split off from the statement below for a reason that is arithmetic and not
mathematical. Instantiating the general identity makes the kernel compare the two spellings of
the source of `modulePullbackObjUnitIso` — `(modulePullback _).obj (SheafOfModules.unit
(structureSheafRing (Spec A).toRingedSpace))`, which is its own, against
`(Scheme.Modules.pullback _).obj ((tilde.functor A).obj (ModuleCat.of A A))`, which is the one
`reductionUnitHom` fixes — and at the concrete fibre product that comparison asks for the
carrier of the pullback, so a single one of them is worth about a third of a kernel check.
The statement below pays one on its own account, in `γ ×ₘ _`, and that leaves no room for the
instantiation to pay a second.

With `γ` a variable, every argument of the general identity is matched first-order here and
this declaration pays none; the statement below is then this one applied, and pays exactly the
one its own `γ ×ₘ _` already costs.

The binder's type is therefore written to be **the type the statement's `γ ×ₘ _` elaborates
to**, not the type one would write freshly: its source is the `Scheme.Modules` module, which is
what `adjunctionTensorMap` fixes there, and its target is
`SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toSheafedSpace)` — the spelling
`modulePullbackObjUnitIso` gives through `Scheme.Hom.toLRSHom.toShHom`, rather than
`structureRingSheaf X.toRingedSpace`. The two are the same object by `rfl`, and the difference
matters only because it would land *inside* `CategoryTheory.Functor.map` of the uncurried
`Stacks.SheafOfModules.Tensor.sheafTensor`, where the congruence on arguments fails before it
reaches the morphism and the comparison becomes a `whnf` of the bifunctor — the one step that
fills a kernel check by itself. -/
private theorem reductionMap_eq_tensorProjectionFormulaOfUnitHom
    (γ : (Scheme.Modules.pullback (pullback.fst (quotOver φ t).hom q)).obj
          ((tilde.functor A).obj (ModuleCat.of A A)) ⟶
        SheafOfModules.unit (structureSheafRing
          (pullback (quotOver φ t).hom q).toLocallyRingedSpace.toSheafedSpace))
    (hγ : reductionUnitHom φ t q ≫
        (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map γ =
      (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap q (quotHom φ t))).unit.app
          (SheafOfModules.unit
            (structureRingSheaf (pullback (Over.mk t).hom q).toRingedSpace)) ≫
        (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
          (modulePullbackObjUnitIso
            (baseChangeMap q (quotHom φ t)).toLRSHom.toShHom).hom) :
    reductionMap φ t q 𝓕 =
      (tensorSheafUnitLeftIso (pullback (Over.mk t).hom q).toRingedSpace
            ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((pullback (Over.mk t).hom q).toRingedSpace).presheaf,
                ((pullback (Over.mk t).hom q).toRingedSpace).IsSheaf⟩)).map
            (reductionUnitHom φ t q ×ₘ
              𝟙 ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)) ≫
          adjunctionTensorMap
              (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap q (quotHom φ t)))
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((pullback (Over.mk t).hom q).toRingedSpace).presheaf,
                  ((pullback (Over.mk t).hom q).toRingedSpace).IsSheaf⟩))
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((pullback (quotOver φ t).hom q).toRingedSpace).presheaf,
                  ((pullback (quotOver φ t).hom q).toRingedSpace).IsSheaf⟩))
              (comparisonNatTrans (baseChangeMap q (quotHom φ t)).toLRSHom.toShHom)
              ((Scheme.Modules.pullback (pullback.fst (quotOver φ t).hom q)).obj
                ((tilde.functor A).obj (ModuleCat.of A A)))
              ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕) ≫
            (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨((pullback (quotOver φ t).hom q).toRingedSpace).presheaf,
                      ((pullback (quotOver φ t).hom q).toRingedSpace).IsSheaf⟩)).map
                  (γ ×ₘ
                    (baseChangeSheafIso φ t q 𝓕).hom) ≫
                (tensorSheafUnitLeftIso (pullback (quotOver φ t).hom q).toRingedSpace
                  ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)).hom) :=
  (reductionMap_eq_unit_comp φ t q 𝓕).trans
    (unit_comp_eq_tensorProjectionFormulaGen (baseChangeMap q (quotHom φ t))
      ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
      (reductionUnitHom φ t q) γ hγ (baseChangeSheafIso φ t q 𝓕).hom)

/-- **`reductionMap` is the projection-formula composite of the structure-sheaf component.**
The canonical reduction `𝓕_{A'} ⟶ i_*𝓕_A` is the inverse left unitor, the structure-sheaf
component `reductionUnitHom` in the first tensor factor, the projection-formula map of the
immersion, and the left unitor together with `baseChangeSheafIso` in the second.

It is unconditional: the equation that the structure-sheaf component is the canonical
`𝒪_{W_{A'}} ⟶ i_*𝒪_{W_A}` is `reductionUnitHom_comp_modulePullbackObjUnitIso`. What is still
missing from the identification of condition (iii) is only the *transport* between this
bifunctor spelling and the `tensorSheafFunctor` spelling of
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`; see the "what is not done" of
this file. -/
theorem reductionMap_eq_tensorProjectionFormula :
    reductionMap φ t q 𝓕 =
      (tensorSheafUnitLeftIso (pullback (Over.mk t).hom q).toRingedSpace
            ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((pullback (Over.mk t).hom q).toRingedSpace).presheaf,
                ((pullback (Over.mk t).hom q).toRingedSpace).IsSheaf⟩)).map
            (reductionUnitHom φ t q ×ₘ
              𝟙 ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)) ≫
          adjunctionTensorMap
              (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap q (quotHom φ t)))
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((pullback (Over.mk t).hom q).toRingedSpace).presheaf,
                  ((pullback (Over.mk t).hom q).toRingedSpace).IsSheaf⟩))
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((pullback (quotOver φ t).hom q).toRingedSpace).presheaf,
                  ((pullback (quotOver φ t).hom q).toRingedSpace).IsSheaf⟩))
              (comparisonNatTrans (baseChangeMap q (quotHom φ t)).toLRSHom.toShHom)
              ((Scheme.Modules.pullback (pullback.fst (quotOver φ t).hom q)).obj
                ((tilde.functor A).obj (ModuleCat.of A A)))
              ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕) ≫
            (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).map
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨((pullback (quotOver φ t).hom q).toRingedSpace).presheaf,
                      ((pullback (quotOver φ t).hom q).toRingedSpace).IsSheaf⟩)).map
                  ((modulePullbackObjUnitIso
                        (pullback.fst (quotOver φ t).hom q).toLRSHom.toShHom).hom ×ₘ
                    (baseChangeSheafIso φ t q 𝓕).hom) ≫
                (tensorSheafUnitLeftIso (pullback (quotOver φ t).hom q).toRingedSpace
                  ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)).hom) :=
  reductionMap_eq_tensorProjectionFormulaOfUnitHom φ t q 𝓕
    (modulePullbackObjUnitIso (pullback.fst (quotOver φ t).hom q).toLRSHom.toShHom).hom
    (reductionUnitHom_comp_modulePullbackObjUnitIso φ t q)

end Deformation.Artin.SectionsSheaf

end
