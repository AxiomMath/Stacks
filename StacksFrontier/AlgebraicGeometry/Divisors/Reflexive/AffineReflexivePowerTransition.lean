module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineMulSectionTilde
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineReflexivePowerTilde

/-!
# The transitions of the reflexive power system on an affine scheme

`AlgebraicGeometry.reflexivePowerTildeIso` identifies the reflexive powers of `M^~` with the
associated sheaves of the module-level reflexive powers of `M`.  **This file shows that
identification compatible with the transition maps**, which are multiplication by a fixed
section `s`, so that the two `ℕ`-indexed systems of [Stacks, Tag 0EBN] correspond.

## The argument

In degrees `≥ 1` the sheaf-level transition is multiplication by `s` into the tensor product
followed by the canonical map to the reflexive hull, and the comparison of the next power is
`AlgebraicGeometry.doubleDualTensorTildeIso`, which is the double dual of the tensor comparison
followed by `AlgebraicGeometry.reflexiveHullTildeIso`.  Naturality of the canonical map to the
double dual slides the tensor comparison past it, leaving two squares already proved:

* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_unitHomEquiv_symm` and
  `…mulSectionHom_tensorSheafIso`, which say that multiplication by `s` into `M^~ ⊗ G`,
  read across the affine tensor comparison, is `tilde.map` of `x ↦ s ⊗ x`;
* `AlgebraicGeometry.toDoubleDual_reflexiveHullTildeIso`, which says that the canonical map to
  the double dual, read across the affine hull comparison, is `tilde.map` of
  `Module.Dual.eval`.

Composing the two `tilde.map`s gives `tilde.map` of the module-level transition, which is
exactly `Module.Dual.eval ∘ (s ⊗ ·)`.

Degree `0` is `AlgebraicGeometry.reflexivePowerTildeIso_transition_zero`, in
`AffineReflexivePowerTilde.lean`: there the transition is not a hull map but the morphism
`𝒪_{Spec R} ⟶ M^~` attached to `s`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom_tensorTilde`: multiplication by `s`
  across the tensor comparison.
* `Stacks.AlgebraicGeometry.ReflexivePowers.transition_square`: **the transition square**, for
  an arbitrary comparison `G ≅ N^~` of the previous term.
* `Stacks.AlgebraicGeometry.ReflexivePowers.transition_succ`: that square at the reflexive
  powers.
* `Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerTildeIso_transition`: **the square in
  every degree**, degree `0` included.

## Implementation notes

The proofs are written as chains of `Eq.trans` and `congrArg` rather than `rw` chains.  A goal
here mixes `(Spec R).Modules` with `SheafOfModules (structureSheafRing _)`, which it unfolds to;
such a goal is not type-correct at `implicit` transparency, so `rw` reports "did not find an
occurrence" even on syntactically present patterns, while term-mode steps are checked at default
transparency and go through.  For the same reason `transition_succ` converts the definitional
identities one named step at a time: checking them simultaneously exhausts the kernel's
deterministic timeout.

The chain is split across several declarations on purpose, and the splits are not cosmetic:
each is a point at which one kernel defeq would otherwise be replayed inside a motive spanning
a whole composite, which exhausts the deterministic timeout.

* `dualIso_hom_eq` and `dualIso_dualIso_hom_eq` are `rfl` lemmas stated for a **variable**
  scheme and variable modules.  Reducing `dualIso (dualIso e)` to `doubleDualMap e.hom` directly
  on the sheaves at hand does not fit in the kernel's budget; proved at variables it is
  discharged on small terms, and `doubleDualTensorTildeIso_hom_eq` instantiates the result
  instead of replaying the reduction.  This one lemma is what makes `transition_square` go
  through: without it every arrangement of the reassociation chain times out.
* `transition_square_inner` proves the square with no `mulSectionHom` prefix, so the
  reassociation steps carry short motives, and `transition_square` whiskers it on once.
* `reflexivePowerTransition_succ_comp` is the same device applied to the last step, where the
  identification at issue is `reflexivePower (M^~) (n + 2)` against
  `dualSheaf (dualSheaf (…sheafTensor… (M^~) (reflexivePower (M^~) (n + 1))))`, i.e. the `n + 2`
  case of `reflexivePower` (`ReflexivePowers.lean:111`) composed with `reflexiveHull`.  Each half
  of that identification is affordable on its own at these sheaves: the object-level identity,
  the same identity as a type ascription on `toDoubleDual`, the module-level identity, and the
  unfoldings of `reflexivePowerTransition` and of `reflexivePowerTildeIso` all check as one-line
  `rfl` lemmas.  Their *sum* inside one declaration does not, so what fails is the budget and
  not the defeq.  `reflexivePowerTransition_succ_comp` therefore states the upstream
  `reflexivePowerTransition_succ` composed with a **variable** `g` whose domain is already written
  at the `reflexivePower F (n + 2)` spelling, at a variable scheme and module: the identification
  is discharged there on small terms, and instantiating at
  `g := (reflexivePowerTildeIso R M (n + 2)).hom` is a syntactic argument check.
* The steps use `whisker_eq`/`eq_whisker` rather than `congrArg` with a lambda motive, except in
  `reflexivePowerTransition_succ_comp`, which closes with `congr 1`.  There the stated left side
  has codomain `reflexivePower F (n + 1 + 1)`: since `reflexivePower` recurses three ways
  (`0 | 1 | n + 2`) it is a stuck `Nat.casesOn` at a variable `n`, while the right side carries
  `toDoubleDual`'s codomain `dualSheaf (dualSheaf (…))`.  The heads differ, so congruence cannot
  fire and lazy delta unfolds the duals over the tensor terms.  `eq_whisker` forces both sides of
  the whiskering to carry one object, so the comparison runs on the whole composites; `congr 1`
  splits the composition first and compares the objects argument-wise, which is measurably
  cheaper (33.4 s to 27.0 s).  The residue is that one crossing, and removing it needs
  `reflexivePower`'s equation visible to defeq, which belongs to `ReflexivePowers.lean`.

Arrangements of the last step that do **not** fit the kernel's budget, each giving
`(kernel) deterministic timeout`:

* `transition_succ := transition_succ_square R M s n`, leaving the whole identification to the
  kernel as one defeq at the application.
* `transition_succ_unfold` restated so that both sides carry the same
  `(reflexivePowerTildeIso R M (n + 2)).hom`, with the identification moved into a type
  ascription on `toDoubleDual`, proved by `eq_whisker` of `reflexivePowerTransition_succ`.
* `eq_whisker` of `reflexivePowerTransition_succ` against `(reflexivePowerTildeIso R M
  (n + 2)).hom` with no ascription, which is the same step without the variable `g`.
* `conv_lhs => rw [...]` for the two rewrites: it elaborates to a goal whose two sides are
  printed identically, but that is an elaborator result only, and closing it with `rfl` moves
  the failure from `unsolved goals` to a kernel timeout on the `conv`-generated motives.  `conv`
  does not confine the cost from the kernel's point of view.
* the eight-step reassociation of `transition_square` with the `mulSectionHom` prefix replaced
  by a **variable** of the tensor-sheaf type, so that no motive carries the
  monoidal-versus-`sheafTensor` junction at all.  The cost was never that junction, and no
  change to `OnSpaceMonoidal` or to `reflexivePowerTransition`'s signature is called for.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBQ](https://stacks.math.columbia.edu/tag/0EBQ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

open _root_.AlgebraicGeometry

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M]
  (s : M) {G : (Spec R).Modules} {N : ModuleCat.{u} R} [Module.Finite R N]

omit [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] in
/-- Multiplication by `s` into `M^~ ⊗ G`, compared across the tensor comparison, is `tilde.map`
of `x ↦ s ⊗ x`. -/
theorem mulSectionHom_tensorTilde (α : G ≅ tilde N) :
    mulSectionHom (Spec R).toRingedSpace ((tilde M).unitHomEquiv.symm (tildeGlobalSection M s)) ≫
        ((tensorSheafIso (Spec R) (Iso.refl (tilde M)) α).hom ≫
          (tensorSheafTildeIso R M N).hom) =
      α.hom ≫ tilde.map (ModuleCat.ofHom (TensorProduct.mk R M N s)) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (tensorSheafTildeIso R M N).hom)
    (mulSectionHom_tensorSheafIso (Spec R) _ α)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => α.hom ≫ z)
    (mulSectionHom_unitHomEquiv_symm R M N (tildeGlobalSection M s) s rfl)

/-- The dual of an isomorphism of modules is the dual of its forward morphism.  Stated for a
variable scheme and variable modules: the kernel discharges it there on small terms, and the
consumers below instantiate it rather than replaying the reduction on the sheaves at hand. -/
theorem dualIso_hom_eq {Y : Scheme.{u}} {F' G' : Y.Modules} (e : F' ≅ G') :
    (dualIso e).hom = dualMap e.hom := rfl

/-- The double dual of an isomorphism is the double dual of its forward morphism, again at
variables. -/
theorem dualIso_dualIso_hom_eq {Y : Scheme.{u}} {F' G' : Y.Modules} (e : F' ≅ G') :
    (dualIso (dualIso e)).hom = doubleDualMap e.hom :=
  (dualIso_hom_eq (dualIso e)).trans (congrArg dualMap (dualIso_hom_eq e))

/-- `AlgebraicGeometry.doubleDualTensorTildeIso` is by definition the double dual of the tensor
comparison composed with the affine reflexive-hull comparison; this reads that definition on the
forward morphisms, with the composite still written as one isomorphism. -/
theorem doubleDualTensorTildeIso_hom_trans
    [Module.Finite R (M ⊗ N : ModuleCat.{u} R)] (α : G ≅ tilde N) :
    (doubleDualTensorTildeIso R (Iso.refl (tilde M)) α).hom =
      (dualIso (dualIso (tensorSheafIso (Spec R) (Iso.refl (tilde M)) α ≪≫
            tensorSheafTildeIso R M N)) ≪≫
        reflexiveHullTildeIso R (M ⊗ N : ModuleCat.{u} R)).hom := rfl

/-- The forward morphism of `AlgebraicGeometry.doubleDualTensorTildeIso`: the double dual of the
tensor comparison, followed by the affine reflexive-hull comparison. -/
theorem doubleDualTensorTildeIso_hom_eq [Module.Finite R (M ⊗ N : ModuleCat.{u} R)]
    (α : G ≅ tilde N) :
    (doubleDualTensorTildeIso R (Iso.refl (tilde M)) α).hom =
      doubleDualMap ((tensorSheafIso (Spec R) (Iso.refl (tilde M)) α).hom ≫
          (tensorSheafTildeIso R M N).hom) ≫
        (reflexiveHullTildeIso R (M ⊗ N : ModuleCat.{u} R)).hom :=
  (doubleDualTensorTildeIso_hom_trans R M α).trans
    ((Iso.trans_hom _ _).trans
      (eq_whisker (dualIso_dualIso_hom_eq
          (tensorSheafIso (Spec R) (Iso.refl (tilde M)) α ≪≫ tensorSheafTildeIso R M N))
        (reflexiveHullTildeIso R (M ⊗ N : ModuleCat.{u} R)).hom))

/-- **The inner square.**  The canonical map to the double dual of `M^~ ⊗ G`, read across
`AlgebraicGeometry.doubleDualTensorTildeIso`, is the tensor comparison followed by `tilde.map`
of evaluation. -/
theorem transition_square_inner (α : G ≅ tilde N) :
    toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj
          ((tilde M))).obj (G))) ≫
      (doubleDualTensorTildeIso R (Iso.refl (tilde M)) α).hom =
    ((tensorSheafIso (Spec R) (Iso.refl (tilde M)) α).hom ≫
        (tensorSheafTildeIso R M N).hom) ≫
      tilde.map (ModuleCat.ofHom (Module.Dual.eval R (M ⊗ N : ModuleCat.{u} R))) := by
  have : Module.Finite R (M ⊗ N : ModuleCat.{u} R) := Module.Finite.tensorProduct R M N
  refine (whisker_eq _ (doubleDualTensorTildeIso_hom_eq R M α)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker
    (toDoubleDual_naturality ((tensorSheafIso (Spec R) (Iso.refl (tilde M)) α).hom ≫
      (tensorSheafTildeIso R M N).hom)).symm
    (reflexiveHullTildeIso R (M ⊗ N : ModuleCat.{u} R)).hom).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact whisker_eq
    ((tensorSheafIso (Spec R) (Iso.refl (tilde M)) α).hom ≫ (tensorSheafTildeIso R M N).hom)
    (toDoubleDual_reflexiveHullTildeIso R (M ⊗ N : ModuleCat.{u} R))

/-- **The transition square.** -/
theorem transition_square (α : G ≅ tilde N) :
    (mulSectionHom (Spec R).toRingedSpace
          ((tilde M).unitHomEquiv.symm (tildeGlobalSection M s)) ≫
        toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj
              ((tilde M))).obj (G)))) ≫
      (doubleDualTensorTildeIso R (Iso.refl (tilde M)) α).hom =
    α.hom ≫ tilde.map (ModuleCat.ofHom
      ((Module.Dual.eval R (M ⊗ N : ModuleCat.{u} R)).comp (TensorProduct.mk R M N s))) := by
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (transition_square_inner R M α)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (mulSectionHom_tensorTilde R M s α)
    (tilde.map (ModuleCat.ofHom (Module.Dual.eval R (M ⊗ N : ModuleCat.{u} R))))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact whisker_eq α.hom (tilde.map_comp _ _).symm

/-- The comparison of the `n + 2`-nd reflexive power is `doubleDualTensorTildeIso` applied to
the comparison of the previous one. -/
theorem reflexivePowerTildeIso_succ_succ_hom (n : ℕ) :
    (reflexivePowerTildeIso R M (n + 2)).hom =
      (doubleDualTensorTildeIso R (Iso.refl (tilde M))
        (reflexivePowerTildeIso R M (n + 1))).hom := rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- The module-level transition out of degree `n + 1` is evaluation after `s ⊗ ·`. -/
theorem moduleReflexivePowerTransition_succ_eq (n : ℕ) :
    Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerTransition M s (n + 1) =
      ModuleCat.ofHom ((Module.Dual.eval R
          (M ⊗ Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower M (n + 1) :
            ModuleCat.{u} R)).comp
        (TensorProduct.mk R M
          (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower M (n + 1)) s)) := rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- `tilde.map` of the module-level transition out of degree `n + 1`. -/
theorem tilde_map_moduleReflexivePowerTransition_succ (n : ℕ) :
    tilde.map (ModuleCat.ofHom ((Module.Dual.eval R
          (M ⊗ Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower M (n + 1) :
            ModuleCat.{u} R)).comp
        (TensorProduct.mk R M
          (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower M (n + 1)) s))) =
      tilde.map (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerTransition
        M s (n + 1)) :=
  congrArg tilde.map (moduleReflexivePowerTransition_succ_eq R M s n).symm

/-- The transition out of degree `n + 1`, whiskered by any morphism out of the `n + 2`-nd power.
Stated at a **variable** scheme, a variable module and a variable `g` whose domain is written at
the `reflexivePower _ (n + 2)` spelling: the identification of that spelling with the reflexive
hull of the tensor product is then discharged on small terms, and the consumers below instantiate
the result instead of replaying it on the sheaves at hand. -/
theorem reflexivePowerTransition_succ_comp {Y : Scheme.{u}} (F : Y.Modules) (t : F.sections)
    (n : ℕ) {T : Y.Modules} (g : reflexivePower F (n + 2) ⟶ T) :
    reflexivePowerTransition F t (n + 1) ≫ g =
      (mulSectionHom Y.toRingedSpace (F.unitHomEquiv.symm t) ≫
          toDoubleDual ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (F)).obj
                ((reflexivePower F (n + 1)))))) ≫ g := by
  congr 1

/-- The sheaf-level transition out of degree `n + 1` and the next comparison, both written out. -/
theorem transition_succ_unfold (n : ℕ) :
    reflexivePowerTransition (X := Spec R) (tilde M) (tildeGlobalSection M s) (n + 1) ≫
        (reflexivePowerTildeIso R M (n + 2)).hom =
      (mulSectionHom (Spec R).toRingedSpace
            ((tilde M).unitHomEquiv.symm (tildeGlobalSection M s)) ≫
          toDoubleDual (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj
                ((tilde M))).obj ((reflexivePower (X := Spec R) (tilde M) (n + 1))))) ≫
        (doubleDualTensorTildeIso R (Iso.refl (tilde M))
          (reflexivePowerTildeIso R M (n + 1))).hom :=
  (reflexivePowerTransition_succ_comp (tilde M) (tildeGlobalSection M s) n
      (reflexivePowerTildeIso R M (n + 2)).hom).trans
    (whisker_eq _ (reflexivePowerTildeIso_succ_succ_hom R M n))

/-- The transition square at the previous comparison, followed by the identification of the
module-level transition. -/
theorem transition_succ_square (n : ℕ) :
    (mulSectionHom (Spec R).toRingedSpace
            ((tilde M).unitHomEquiv.symm (tildeGlobalSection M s)) ≫
          toDoubleDual (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj
                ((tilde M))).obj ((reflexivePower (X := Spec R) (tilde M) (n + 1))))) ≫
        (doubleDualTensorTildeIso R (Iso.refl (tilde M))
          (reflexivePowerTildeIso R M (n + 1))).hom =
      (reflexivePowerTildeIso R M (n + 1)).hom ≫
        tilde.map (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerTransition
          M s (n + 1)) :=
  (transition_square R M s (reflexivePowerTildeIso R M (n + 1))).trans
    (whisker_eq (reflexivePowerTildeIso R M (n + 1)).hom
      (tilde_map_moduleReflexivePowerTransition_succ R M s n))

/-- The transition square at the reflexive powers, in degrees `≥ 1`. -/
theorem transition_succ (n : ℕ) :
    reflexivePowerTransition (X := Spec R) (tilde M) (tildeGlobalSection M s) (n + 1) ≫
        (reflexivePowerTildeIso R M (n + 2)).hom =
      (reflexivePowerTildeIso R M (n + 1)).hom ≫
        tilde.map (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerTransition
          M s (n + 1)) :=
  (transition_succ_unfold R M s n).trans (transition_succ_square R M s n)

/-- **The comparison of the two reflexive power systems is compatible with every transition.**
Degree `0` is `AlgebraicGeometry.reflexivePowerTildeIso_transition_zero` and the higher degrees
are `transition_succ`. -/
theorem reflexivePowerTildeIso_transition (n : ℕ) :
    reflexivePowerTransition (X := Spec R) (tilde M) (tildeGlobalSection M s) n ≫
        (reflexivePowerTildeIso R M (n + 1)).hom =
      (reflexivePowerTildeIso R M n).hom ≫
        tilde.map (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerTransition
          M s n) := by
  cases n with
  | zero => exact reflexivePowerTildeIso_transition_zero R M s
  | succ n => exact transition_succ R M s n

end Stacks.AlgebraicGeometry.ReflexivePowers

end
