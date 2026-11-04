module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModulesMap
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Sheaves of modules are invariant under a 2-isomorphism of morphisms of ringed topoi

Let `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be two morphisms of ringed topoi in the sense of
Stacks 01D3 part (2) and let `t : f ≅ g` be a 2-isomorphism between them in the sense of
Stacks 04IC, i.e. an isomorphism `t.e : f_* ≅ g_*` of the underlying direct-image functors
whose value at `O_C` carries the structure map of `f` to the structure map of `g`. This file
shows that the two direct images of sheaves of modules of Stacks 03D6 part (1) are isomorphic,
and hence — by uniqueness of left adjoints — that the two pullbacks of Stacks 03D6 part (2)
are isomorphic as well.

This is the reusable statement that a *commutative diagram* of ringed topoi, which Stacks
expresses as a 2-isomorphism of the two composites, induces a commutative diagram of the
associated pullbacks of sheaves of modules. Every localization square of Stacks 04J0 is of
that form, and this is what turns such a square into a square of module pullbacks.

## The argument

Invertibility is used only at the end. A 2-morphism of morphisms of ringed topoi already
induces a map of the direct images of a sheaf of modules, and that construction is
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pushforwardModulesMap` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModulesMap`. Each
component of the isomorphism here is that construction applied to `t.toTwoMorphism` and to
`t.symm.toTwoMorphism`, with `t.e.hom_inv_id_app` and `t.e.inv_hom_id_app` for the two
identities.

`pullbackModulesIso` is then uniqueness of left adjoints, which does need the inverse.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardModulesIso`: a 2-isomorphism of
  morphisms of ringed topoi induces an isomorphism of the two direct images of sheaves of
  modules.
* `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`: and hence an isomorphism of the
  two pullbacks of sheaves of modules.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {f g : RingedToposHom X Y} (t : TwoIso f g)
  (F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))

/-- **The two direct images of a sheaf of modules along 2-isomorphic morphisms of ringed topoi
agree.** The comparison is the 2-isomorphism evaluated at the underlying sheaf of sets of the
module. -/
def pushforwardModulesIsoApp :
    (pushforwardModules f).obj F ≅ (pushforwardModules g).obj F where
  hom := t.toTwoMorphism.pushforwardModulesMapApp F
  inv := t.symm.toTwoMorphism.pushforwardModulesMapApp F
  hom_inv_id := hom_ext_moduleSheafFunctor (t.e.hom_inv_id_app _)
  inv_hom_id := hom_ext_moduleSheafFunctor (t.e.inv_hom_id_app _)

/-- **Stacks 03D6 part (1) is invariant under a 2-isomorphism of morphisms of ringed topoi.**
2-isomorphic morphisms of ringed topoi have isomorphic direct images of sheaves of modules.
Its components are `AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardModulesIsoApp`, and
naturality holds on underlying sheaves of sets, where both functors are a direct image and the
comparison is the naturality of the 2-isomorphism.

This is the form in which a commutative square of ringed topoi — Stacks says that a diagram of
ringed topoi commutes when its two composites are 2-isomorphic — becomes a commutative square
of direct images of sheaves of modules. -/
def pushforwardModulesIso : pushforwardModules f ≅ pushforwardModules g :=
  NatIso.ofComponents (fun F ↦ t.pushforwardModulesIsoApp F) fun {_ _} φ ↦
    t.toTwoMorphism.pushforwardModulesMap.naturality φ

/-- **On underlying sheaves of sets the comparison of the two direct images of sheaves of
modules *is* the 2-isomorphism.** A morphism of sheaves of modules is determined by its
underlying morphism of sheaves of sets, so this pins
`AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardModulesIso` down rather than merely
exhibiting it.

It is the companion of
`AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pushforwardModulesMap` for
a 2-isomorphism, and it is what identifies a commuting square of direct images of sheaves of
modules with the underlying commuting square of direct images of sheaves of sets. -/
@[simp]
theorem moduleSheafFunctor_map_pushforwardModulesIso_hom_app :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        (t.pushforwardModulesIso.hom.app F) =
      t.e.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) F) :=
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D6 part (2) is invariant under a 2-isomorphism of morphisms of ringed topoi.**
2-isomorphic morphisms of ringed topoi have isomorphic pullbacks of sheaves of modules.

Both pullbacks are left adjoints of the two direct images, which agree by
`AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardModulesIso`, so this is uniqueness of left
adjoints. It is the form in which a commutative square of ringed topoi becomes a commutative
square of pullbacks of sheaves of modules, and in particular the form in which the
localization squares of Stacks 04J0 are used. -/
def pullbackModulesIso : f.toModulesHom.pullbackModules ≅ g.toModulesHom.pullbackModules :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules f).ofNatIsoRight t.pushforwardModulesIso)
    (pullbackAdjPushforwardModules g)

end AlgebraicGeometry.RingedToposHom.TwoIso

end
