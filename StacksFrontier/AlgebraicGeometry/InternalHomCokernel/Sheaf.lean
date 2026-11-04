module

public import StacksFrontier.AlgebraicGeometry.InternalHomCokernel.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction

/-!
# The local-cokernel hypotheses of a ringed site, in the sheaf spelling

`StacksFrontier/AlgebraicGeometry/InternalHomCokernel/Basic.lean` shows that internal Hom
carries a local cokernel in the first variable to a kernel, with the two hypotheses stated for
the restriction functor `restrFun` of Tag 03EM, which acts on presheaves of modules.  On a
ringed site the objects in question are sheaves of modules and the cokernel is a cokernel of
sheaves of modules, so this file restates the hypotheses in terms of
`SheafOfModules.over`, which is the spelling an argument about sheaves of modules produces.

The translation is definitional: the underlying presheaf of `N.over V` is
`(restrFun O V).obj N.val` and the underlying presheaf morphism of `b.over V` is
`(restrFun O V).map b.val`, both on the nose.  What the translation buys is that the two
hypotheses can then be discharged from facts about the category of sheaves of modules --- an
epimorphism there, and the universal property of a cokernel there --- rather than from facts
about presheaves of modules, where neither holds.

## Main definitions

* `internalHomKernelIsoOfSheafCokernel`: the isomorphism of
  `InternalHomCokernel/Basic.lean`, from hypotheses on `b.over V` rather than on
  `(restrFun O V).map b.val`.

## Main results

* `cancel_restrFun_map_val_of_epi`: an epimorphism of sheaves of modules on each slice can be
  cancelled from the left in the presheaf spelling, even though it is not an epimorphism of
  presheaves of modules.
* `exists_restrFun_desc`: likewise for the descent property.

## Implementation notes

A morphism of sheaves of modules is a one-field structure wrapping a morphism of the underlying
presheaves of modules, so the translations are `SheafOfModules.hom_ext` in one direction and
`congrArg SheafOfModules.Hom.val` in the other.

The epimorphism hypothesis is taken slicewise, as `∀ V, Epi (b.over V)`, rather than as `Epi b`
together with a preservation statement, so that the file needs no sheafification instances;
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CokernelFinitePresentation.lean` is what supplies
it from `Epi b` where those instances are available.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.PresheafOfModules.InternalHom

universe v u

namespace Stacks.SheafOfModules.InternalHom

variable (Y : RingedSite.{u, v, max u v})
variable {A B N G : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

/-- **A slicewise epimorphism of sheaves of modules cancels in the presheaf spelling.**  This is
not an instance of `cancel_epi` for presheaves of modules: `b.over V` is an epimorphism of
sheaves of modules, hence only locally surjective, and the morphisms cancelled are morphisms
into the sheaf `G.over V`. -/
public theorem cancel_restrFun_map_val_of_epi (b : B ⟶ N) (hepi : ∀ V : Y.C, Epi (b.over V))
    (V : Y.C)
    (w w' : (restrFun Y.O.obj V).obj N.val ⟶ (restrFun Y.O.obj V).obj G.val)
    (h : (restrFun Y.O.obj V).map b.val ≫ w = (restrFun Y.O.obj V).map b.val ≫ w') :
    w = w' := by
  have := hepi V
  have h' : (b.over V) ≫ (⟨w⟩ : N.over V ⟶ G.over V)
      = (b.over V) ≫ (⟨w'⟩ : N.over V ⟶ G.over V) :=
    SheafOfModules.hom_ext h
  exact congrArg SheafOfModules.Hom.val ((cancel_epi (b.over V)).mp h')

/-- **The descent hypothesis of `internalHomKernelIso`, from the sheaf spelling.** -/
public theorem exists_restrFun_desc (a : A ⟶ B) (b : B ⟶ N)
    (hdesc : ∀ (V : Y.C) (t : B.over V ⟶ G.over V), a.over V ≫ t = 0 →
      ∃ w : N.over V ⟶ G.over V, b.over V ≫ w = t)
    (V : Y.C) (t : (restrFun Y.O.obj V).obj B.val ⟶ (restrFun Y.O.obj V).obj G.val)
    (ht : (restrFun Y.O.obj V).map a.val ≫ t = 0) :
    ∃ w, (restrFun Y.O.obj V).map b.val ≫ w = t := by
  obtain ⟨w, hw⟩ := hdesc V ⟨t⟩ (SheafOfModules.hom_ext ht)
  exact ⟨w.val, congrArg SheafOfModules.Hom.val hw⟩

/-- **Internal Hom on a ringed site carries a slicewise cokernel of sheaves of modules in the
first variable to a kernel.** -/
public noncomputable def internalHomKernelIsoOfSheafCokernel (a : A ⟶ B) (b : B ⟶ N)
    (hab : a ≫ b = 0) (hepi : ∀ V : Y.C, Epi (b.over V))
    (hdesc : ∀ (V : Y.C) (t : B.over V ⟶ G.over V), a.over V ≫ t = 0 →
      ∃ w : N.over V ⟶ G.over V, b.over V ≫ w = t) :
    internalHom Y.O.obj N.val G.val
      ≅ kernel (internalHomMapLeft Y.O.obj (G := G.val) a.val) :=
  internalHomKernelIso Y.O.obj a.val b.val (congrArg SheafOfModules.Hom.val hab)
    (cancel_restrFun_map_val_of_epi Y b hepi) (exists_restrFun_desc Y a b hdesc)

end Stacks.SheafOfModules.InternalHom

end
