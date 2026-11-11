module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangePullback

/-!
# The inverse image of modules on the fppf site preserves the presheaf-level `LQCoh^fbc`

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`.  **Stacks 0771** part (3) says
that the inverse image `f^*` carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`.  This file proves
the analogue for the presheaf-level `LQCoh^fbc`
(`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange`), whose flat base change
property is strictly stronger than **Stacks 0762**, on the modules on the fppf site
`AlgebraicGeometry.Stack.fppfModules`.  Part (3) itself, at the sheaf-level reading of
**Stacks 0762**, is `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfModulesPullback`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_fppfModulesPullback`:
  the inverse image statement for the presheaf-level `LQCoh^fbc` on the fppf sites.

## Implementation notes

`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_stackInverseImage` is the
same statement for the inverse image of *presheaves* of modules on the associated étale site,
stated at the structure functor `f ⋙ 𝒪_𝒴` of the composite presentation.  Passing to the
inverse image of fppf *sheaves* of modules at `𝒳`'s own structure functor needs no further
mathematics, and in particular neither a sheafification nor a comparison of the two topologies:

* `AlgebraicGeometry.Stack.modulePullback` takes no sheafification.  It is
  `SheafOfModules.pushforward` along the morphism's functor with an `eqToHom` on scalars; its
  underlying map of abelian presheaves is precomposition with `f.op` by `rfl`
  (`AlgebraicGeometry.Stack.modulePullback_obj_val_presheaf`), and
  `AlgebraicGeometry.Stack.modulePullbackForgetIso`, which identifies it with
  `PresheafOfModules.pushforward₀` followed by restriction of scalars, is `Iso.refl`.
* `AlgebraicGeometry.Stack.ringStructureSheafCore_obj` is `rfl` and does not depend on its
  topology argument, so the étale and the fppf structure sheaves have the same underlying
  presheaf of rings and the modules over them are the same type.

What does separate the two is one step, and it is a dependent transport rather than mathematics.
The presheaf-level statement is indexed by the structure functor `homFunctor f ⋙ 𝒪_𝒴` of the
composite presentation, whereas a consumer needs `𝒳`'s own; the two are equal by
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p` (**Stacks 02XP** clause (2), the field
`w` of the based functor), but propositionally and not definitionally, and
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` depends on that functor both
in its `IsFiberedInGroupoids` argument and in the type of its module, so rewriting along the
equality leaves a motive that does not typecheck.  Taking the structure functor as a *parameter*
removes the obstruction: `CategoryTheory.Functor.IsFiberedInGroupoids` is a `Prop`, so
substituting the identification moves the goal to the composite presentation, where the
presheaf-level statement closes it outright.  That is why `p` and `e` are parameters below; a
consumer instantiates `p` at `𝒳`'s own functor and `e` at `homFunctor_comp_p`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 02XP](https://stacks.math.columbia.edu/tag/02XP)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The inverse image on the fppf sites preserves the presheaf-level `LQCoh^fbc`.**  Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and let `F` be a module on the fppf site of `𝒴`
lying in the presheaf-level `LQCoh^fbc(𝒪_𝒴)`.  Then the inverse image `f^*F` lies in the
presheaf-level `LQCoh^fbc(𝒪_𝒳)`.

This is not **Stacks 0771** part (3): the presheaf-level flat base change property is strictly
stronger than **Stacks 0762**, so the hypothesis leaves out members of `LQCoh^fbc` such as
`𝒪(-1)` on `ℙ¹`.  Part (3) is
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfModulesPullback`.

`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_stackInverseImage` is
this statement for the inverse image of *presheaves* of modules, stated at the structure functor
`f ⋙ 𝒪_𝒴` of the composite presentation; the structure functor of the source is a parameter `p`
here, together with the identification `e`, so that substituting `e` puts the goal at the
composite presentation where that statement applies.  See the implementation notes. -/
theorem isLocallyQuasicoherentWithFlatBaseChange_fppfModulesPullback
    {p : 𝒳.val.val.obj ⥤ BigFppfOver B S hS}
    (e : CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p = p)
    (hp : p.IsFiberedInGroupoids) (F : fppfModules B S hS 𝒴)
    (hF : locallyQuasicoherentFlatBaseChangeFppfModules B E hE S hS 𝒴 F) :
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS p hp
      ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS p 𝒴.val.val.p hp
        𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor f.hom) e
        B.topology le_rfl).obj F).val := by
  subst e
  exact isLocallyQuasicoherentWithFlatBaseChange_stackInverseImage
    B E hE S hS f F.val hF

end AlgebraicGeometry.Stack

end
