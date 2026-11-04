module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Parasitic modules and vanishing of the pullback to the flat-fppf site

Let `𝒳` be an algebraic stack and `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` the morphism of ringed
topoi of **Stacks 0788** (2). A sheaf of modules on `𝒳_{fppf}` is parasitic exactly when its
pullback `g^*F` vanishes.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_pullbackModules`: **Stacks 07AR** (2).
* `AlgebraicGeometry.Stack.isZero_sheafOfModules_iff_forall_subsingleton`: a sheaf of modules on
  any site vanishes exactly when all of its modules of sections do.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Stack

universe u v w

/-- A sheaf of modules vanishes exactly when all of its modules of sections do. -/
theorem isZero_sheafOfModules_iff_forall_subsingleton {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) :
    IsZero M ↔ ∀ X, Subsingleton (M.val.obj X) := by
  constructor
  · intro h X
    exact ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation _ X) h)
  · intro h
    rw [IsZero.iff_id_eq_zero]
    apply (SheafOfModules.forget R).map_injective
    simp only [Functor.map_zero]
    ext X m
    exact (h X).elim _ _

/-- A sheaf of modules vanishes exactly when all of its modules of sections do. This is the
module-local name of `isZero_sheafOfModules_iff_forall_subsingleton`. -/
private alias isZero_sheafOfModules_iff := isZero_sheafOfModules_iff_forall_subsingleton

namespace FlatFppf

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07AR** (2). A sheaf of modules on the fppf site of an algebraic stack is parasitic
exactly when its pullback along the flat-fppf morphism of ringed topoi of **Stacks 0788** (2)
vanishes.

The flat-fppf site has the flat objects of `𝒳` for its objects, and the pullback along `g` is
restriction to them (`AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`), so the two conditions
are the same condition read on the two sites. -/
@[stacks 07AR "part (2), the flat-fppf site"]
theorem isParasitic_iff_isZero_pullbackModules
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (fppfRingedTopos B S hS 𝒳).O)) :
    IsParasitic B S hS 𝒳 .fppf F.val ↔
      IsZero ((RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
        (ringedToposModulesHom B S hS 𝒳)).obj F) := by
  rw [((modulePullbackIso B S hS 𝒳).app F).isZero_iff,
    isZero_sheafOfModules_iff ((moduleRestriction B S hS 𝒳).obj F)]
  constructor
  · rintro h ⟨x, hx⟩
    exact h x hx
  · intro h x hx
    exact h (op ⟨x, hx⟩)

end FlatFppf

end AlgebraicGeometry.Stack

end
