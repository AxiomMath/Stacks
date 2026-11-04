module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage

/-!
# Inverse image of fppf modules preserves `LQCoh^fbc` (Stacks 0771 part (3))

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0771** part (3) says that
the inverse image `f^*` carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`. This file states it for
the inverse image of sheaves of modules on the fppf sites, `AlgebraicGeometry.Stack.modulePullback`
of **Stacks 06WE**, which is the functor `AlgebraicGeometry.Stack.fppfModulesPullback` that
**Stacks 07BE** pulls back along; membership in `LQCoh^fbc` is tested on the underlying presheaf of
modules, as in `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModules`.

The inverse image of sheaves of modules along `f` is restriction along `f` followed by the change
of scalars along the equality `f ⋙ q = p` of structure functors. Once that equality is
substituted it is the inverse image of presheaves of modules on the étale sites, for which local
quasi-coherence is **Stacks 06WL** and the flat base change property is **Stacks 0764** part (1),
proved in `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_modulePullback`: the
  statement for any 1-morphism `f` with `f ⋙ q = p` and any topology coarser than the fppf one.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModules_fppfModulePullback`:
  **Stacks 0771** part (3) on the fppf sites of algebraic stacks.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w t


namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0771 part (3)** for the inverse image of sheaves of modules of Stacks 06WE, for a
1-morphism of categories fibred in groupoids given by a functor `f` with `f ⋙ q = p`, for any
topology `τ` coarser than the fppf one and at the module universe of the schemes. -/
theorem isLocallyQuasicoherentWithFlatBaseChange_modulePullback
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v} [Category.{w} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq τ hτ))
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS q hq F.val) :
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((modulePullback.{u, v, w, u, v, w} B S hS p q hp hq f hf τ hτ).obj F).val := by
  subst hf
  have hfib : (f ⋙ q).IsFibredOneMorphism q f := hq.isFibredOneMorphism rfl
  exact ⟨isLocallyQuasicoherent_modulePullback B E h S hS q hq f hp hfib F.val hF.1,
    hasFlatBaseChangeProperty_modulePresheafPullback B E h S hS q hq f hp hfib F.val hF.1.1
      hF.2⟩

/-- **Stacks 0771 part (3)** on the fppf sites of algebraic stacks. Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S` and let `F` be a module on the fppf site of `𝒴` lying in
`LQCoh^fbc(𝒪_𝒴)`. Then its inverse image `f^*F`, the module of Stacks 06WE on the fppf site of
`𝒳`, lies in `LQCoh^fbc(𝒪_𝒳)`.

The functor is `AlgebraicGeometry.Stack.fppfModulesPullback`, written out, so that this is
exactly the module-level statement consumed by Stacks 07BE. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModules_fppfModulePullback
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (F : fppfModules B S hS 𝒴)
    (hF : locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒴 F) :
    locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳
      ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl).obj F) :=
  isLocallyQuasicoherentWithFlatBaseChange_modulePullback B E h S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    B.topology le_rfl F hF

end AlgebraicGeometry.Stack
