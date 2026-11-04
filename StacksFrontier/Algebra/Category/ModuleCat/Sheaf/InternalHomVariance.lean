module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Variance of the internal Hom of sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `F` be a sheaf of
`O`-modules. Tag 03EM shows that the internal Hom presheaf `internalHom O F G` is a sheaf as
soon as `G` is, so internal Hom with `F` fixed is a functor on sheaves of `O`-modules. Stacks
03EN asserts that this functor commutes with arbitrary limits.

The proof is the presheaf statement plus the fact that limits of sheaves of modules are
computed on the underlying presheaves of modules. The forgetful functor to presheaves of
modules both preserves and reflects limits, and composing it with internal Hom gives back the
presheaf internal-Hom functor on the nose, so the sheaf-level functor preserves limits exactly
because the presheaf-level one does.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor`: internal Hom from a fixed
  sheaf of modules, functorial by postcomposition in the target.

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits`: it preserves
  arbitrary limits.

## Implementation notes

The sheaf of rings over which modules are taken is `Stacks.SheafOfModules.Tensor.ringSheaf O`,
the structure sheaf
with commutativity forgotten; it carries the `HasSheafCompose` hypothesis for
`forget₂ CommRingCat RingCat` as an instance argument, as the rest of this development does.

The module universe is an independent `m`, combined as `max u v w m` so that the sheaf-level
functor is an endofunctor of one category of sheaves of modules. This is available because Tag
03EM leaves the module universe of `internalHom` free; the natural isomorphism to the presheaf
functor is `Iso.refl` objectwise, the two functors having literally the same object and
morphism parts.

The second-variable sheaf half of Stacks 03EN is proved here. The presheaf halves are
`Stacks.PresheafOfModules.InternalHom.internalHomFunctor_preservesColimitsOfShape` and
`Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits`, and the
first-variable sheaf half is
`Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor_preservesColimitsOfShape`.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.InternalHom

universe v u w m

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w})

/-- Internal Hom from a fixed sheaf of modules, functorial by postcomposition in the
target. -/
noncomputable def internalHomSecondFunctor
    (F : _root_.SheafOfModules.{max u v w m} (Tensor.ringSheaf O)) :
    _root_.SheafOfModules.{max u v w m} (Tensor.ringSheaf O) ⥤
      _root_.SheafOfModules.{max u v w m} (Tensor.ringSheaf O) where
  obj G := ⟨internalHom O.obj F.val G.val,
    internalHom_isSheaf O.obj F.val G.val G.isSheaf⟩
  map f := ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapRight O.obj F.val f.val⟩
  map_id G := _root_.SheafOfModules.hom_ext <|
    (Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{v, u, w, m}
      O.obj F.val).map_id G.val
  map_comp f g := _root_.SheafOfModules.hom_ext <|
    (Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{v, u, w, m}
      O.obj F.val).map_comp f.val g.val

/-- **Stacks 03EN, sheaf case, second variable.** Internal Hom from a fixed sheaf of modules
commutes with arbitrary limits. -/
@[stacks 03EN "sheaf_second_variable", sga "4 IV 12.2" "partial"]
noncomputable instance internalHomSecondFunctor_preservesLimits
    (F : _root_.SheafOfModules.{max u v w m} (Tensor.ringSheaf O)) :
    PreservesLimits (internalHomSecondFunctor.{v, u, w, m} J O F) := by
  let e : internalHomSecondFunctor.{v, u, w, m} J O F ⋙
      _root_.SheafOfModules.forget.{max u v w m} (Tensor.ringSheaf O) ≅
      _root_.SheafOfModules.forget.{max u v w m} (Tensor.ringSheaf O) ⋙
        Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{v, u, w, m}
          O.obj F.val := by
    refine NatIso.ofComponents (fun G => Iso.refl _) ?_
    intro G H f
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  have hRight : PreservesLimits
      (_root_.SheafOfModules.forget.{max u v w m} (Tensor.ringSheaf O) ⋙
        Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{v, u, w, m}
          O.obj F.val) :=
    @comp_preservesLimits _ _ _ _ _ _ _ _
      (_root_.SheafOfModules.forgetPreservesLimitsOfSize _)
      (Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits
        O.obj F.val)
  have hUnderlying : PreservesLimits
      (internalHomSecondFunctor.{v, u, w, m} J O F ⋙
        _root_.SheafOfModules.forget.{max u v w m} (Tensor.ringSheaf O)) :=
    @preservesLimits_of_natIso _ _ _ _ _ _ e.symm hRight
  let := (_root_.SheafOfModules.fullyFaithfulForget.{max u v w m}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).full
  let := (_root_.SheafOfModules.fullyFaithfulForget.{max u v w m}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).faithful
  exact preservesLimits_of_reflects_of_preserves _
    (_root_.SheafOfModules.forget.{max u v w m} (Tensor.ringSheaf O))

end Stacks.SheafOfModules.InternalHom

end
