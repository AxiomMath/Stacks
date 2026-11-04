module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Sheaves of modules along a 2-morphism of morphisms of ringed topoi

Let `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be two morphisms of ringed topoi in the sense of
Stacks 01D3 part (2) and let `t : f ⟶ g` be a 2-morphism between them in the sense of
Stacks 04IC: a transformation `t : f_* ⟶ g_*` of the underlying direct-image functors whose value
at `O_C` carries the structure map of `f` to the structure map of `g`. This file produces the
induced transformation of the direct images of sheaves of modules of Stacks 03D6 part (1), and
the adjoint transformation of the pullbacks of Stacks 03D6 part (2), which runs the other way.

Invertibility is not used here — a 2-morphism gives a map of direct images and, by the two
adjunctions, a map of pullbacks. The invertible case,
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules`, builds its
isomorphism out of these declarations applied to a 2-isomorphism and to its inverse. The
non-invertible case is what states a *transition* map, which Stacks 07TF asks to be an
isomorphism rather than assuming it is one.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoMorphism.pushforwardModulesMap`: the transformation
  `f_* ⟶ g_*` of direct images of sheaves of modules induced by a 2-morphism.
* `AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap`: its mate `g^* ⟶ f^*` on
  pullbacks of sheaves of modules.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pushforwardModulesMap`:
  on underlying sheaves of sets the induced transformation *is* the given 2-morphism, so it is
  pinned down rather than merely exhibited.
* `AlgebraicGeometry.RingedToposHom.TwoMorphism.isIso_whiskerRight_pushforwardModulesMap` and
  `.isIso_whiskerLeft_pullbackModulesMap`: a 2-morphism that becomes invertible once a further
  morphism of ringed topoi `k : Y ⟶ Z` is appended to it induces an invertible transformation of
  direct images of modules after `k_*`, and an invertible transformation of pullbacks of modules
  after `k^*`. This is how a 2-morphism that is not itself invertible still produces an
  isomorphism of modules over the composite.

## Implementation notes

The underlying sheaf of sets of a direct image of a sheaf of modules is the direct image of its
underlying sheaf of sets on the nose, so the component of the 2-morphism at that sheaf is already
a candidate; what has to be checked is that it is additive and linear, and both are read on
sections, where the operations of a direct image are the operations of the module transported
along `f_* ⋙ Γ(Z, -)`. Additivity is `CategoryTheory.Sheaf.moduleAddObj_naturality` and linearity
is `CategoryTheory.Sheaf.moduleSMulObj_naturality` followed by the observation that the
2-morphism carries the scalar `f♯r` to `g♯r`, which is its compatibility with the structure maps.
This is the argument of the invertible case with the inverse direction deleted.

The mate is taken with `CategoryTheory.conjugateEquiv` at the adjunctions of Stacks 03D7, so the
induced map of pullbacks is the unique one whose transpose is the map of direct images.

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

namespace AlgebraicGeometry.RingedToposHom.TwoMorphism

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {f g : RingedToposHom X Y} (t : TwoMorphism f g)
  (F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))

/-- The comparison of the underlying sheaves of sets of the two direct images of a sheaf of
modules along 2-morphic morphisms of ringed topoi: the 2-morphism evaluated at the underlying
sheaf of sets of the module.

A `def` with an ascribed type. The underlying sheaf of sets of a direct image of a sheaf of
modules *is* the direct image of the underlying sheaf of sets, but the two spellings are not
syntactically equal; ascribing the type discharges the identification once. -/
def pushforwardSheafMap :
    Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
        ((pushforwardModules f).obj F) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
          ((pushforwardModules g).obj F) :=
  t.t.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) F)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The 2-morphism, read on sections of the underlying sheaves of sets over an object of the
target site, carries the structure map of `f` to the structure map of `g`. This is
`AlgebraicGeometry.RingedToposHom.TwoMorphism.commutes` applied to a section. -/
theorem sectionsFunctor_map_t_app_fSharpRing (Z : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    (Sheaf.sectionsFunctor Y.J Z).map
        (t.t.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
        ((Sheaf.sectionsFunctor Y.J Z).map
          ((sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing) r) =
      (Sheaf.sectionsFunctor Y.J Z).map
        ((sheafCompose Y.J (forget RingCat.{w'})).map g.fSharpRing) r :=
  have h : (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing ≫
      t.t.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) =
      (sheafCompose Y.J (forget RingCat.{w'})).map g.fSharpRing := t.commutes
  ((Sheaf.sectionsFunctor Y.J Z).map_comp_apply _ _ r).symm.trans
    (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J Z).map m r) h)

/-- The comparison of the two direct images is additive on sections: both additions are the
addition of the module transported along the direct image, and a natural transformation of the
two transporting functors carries the one to the other. -/
theorem sectionsFunctor_map_pushforwardSheafMap_add (Z : Y.Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
        ((pushforwardModules f).obj F))) :
    (Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F) (x + y) =
      (Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F) x +
        (Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F) y :=
  (congrArg ((Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F))
      (f.pushforwardModules_add F Z x y)).trans
    ((Sheaf.moduleAddObj_naturality ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) F
          (Functor.whiskerRight t.t (Sheaf.sectionsFunctor Y.J Z)) x y).trans
      (g.pushforwardModules_add F Z _ _).symm)

/-- The comparison of the two direct images is linear on sections: both scalar actions are the
action of the module transported along the direct image, with the scalar carried along the
structure map, and the 2-morphism carries the one structure map to the other. -/
theorem sectionsFunctor_map_pushforwardSheafMap_smul (Z : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
        ((pushforwardModules f).obj F))) :
    (Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F) (r • x) =
      r • (Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F) x :=
  (congrArg ((Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F))
      (f.pushforwardModules_smul F Z r x)).trans
    ((Sheaf.moduleSMulObj_naturality ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) F
          (Functor.whiskerRight t.t (Sheaf.sectionsFunctor Y.J Z)) _ x).trans
      ((congrArg (fun s ↦
            Sheaf.moduleSMulObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) F
              (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z) s
              ((Sheaf.sectionsFunctor Y.J Z).map (t.pushforwardSheafMap F) x))
          (t.sectionsFunctor_map_t_app_fSharpRing Z r)).trans
        (g.pushforwardModules_smul F Z r _).symm))

/-- **The direct images of a sheaf of modules along 2-morphic morphisms of ringed topoi are
compared by the 2-morphism.** The comparison is the 2-morphism evaluated at the underlying sheaf
of sets of the module. -/
def pushforwardModulesMapApp : (pushforwardModules f).obj F ⟶ (pushforwardModules g).obj F :=
  ofSheafHom (t.pushforwardSheafMap F)
    (t.sectionsFunctor_map_pushforwardSheafMap_add F)
    (t.sectionsFunctor_map_pushforwardSheafMap_smul F)

/-- **Stacks 03D6 part (1) is functorial in a 2-morphism of morphisms of ringed topoi.** A
2-morphism `f ⟶ g` induces a transformation `f_* ⟶ g_*` of the direct images of sheaves of
modules. Its components are
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pushforwardModulesMapApp`, and naturality holds on
underlying sheaves of sets, where both functors are a direct image and the comparison is the
naturality of the 2-morphism. -/
def pushforwardModulesMap : pushforwardModules f ⟶ pushforwardModules g where
  app M := t.pushforwardModulesMapApp M
  naturality M N φ :=
    hom_ext_moduleSheafFunctor
      (((Sheaf.moduleSheafFunctor
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map_comp
            ((pushforwardModules f).map φ) (t.pushforwardModulesMapApp N)).trans
        ((t.t.naturality ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).map φ)).trans
          ((Sheaf.moduleSheafFunctor
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map_comp
            (t.pushforwardModulesMapApp M) ((pushforwardModules g).map φ)).symm))

/-- On underlying sheaves of sets the induced transformation of direct images of sheaves of
modules *is* the given 2-morphism. A morphism of sheaves of modules is determined by its
underlying morphism of sheaves of sets, so this pins the transformation down. -/
@[simp]
theorem moduleSheafFunctor_map_pushforwardModulesMap :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
        (t.pushforwardModulesMap.app F) =
      t.pushforwardSheafMap F :=
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D6 part (2) is functorial in a 2-morphism of morphisms of ringed topoi**, the
other way round. A 2-morphism `f ⟶ g` induces a transformation `g^* ⟶ f^*` of the pullbacks of
sheaves of modules: the mate of
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pushforwardModulesMap` under the two adjunctions of
Stacks 03D7.

Being a mate, it is the unique transformation whose transpose is the transformation of direct
images. -/
def pullbackModulesMap : g.toModulesHom.pullbackModules ⟶ f.toModulesHom.pullbackModules :=
  (conjugateEquiv (pullbackAdjPushforwardModules f)
    (pullbackAdjPushforwardModules g)).symm t.pushforwardModulesMap

/-! ## Appending a further morphism of ringed topoi

A 2-morphism need not be invertible, and then neither of the two transformations above is. What
happens in practice is that the 2-morphism becomes invertible once a further morphism of ringed
topoi `k : Y ⟶ Z` is appended to it — the situation of two morphisms that agree only after being
composed with a third. The two statements below carry that invertibility to sheaves of modules.

Both are proved here, in the general setting, rather than at the morphisms of ringed topoi a
consumer has in hand: the underlying sheaf of sets of a direct image of modules is the direct
image of the underlying sheaf of sets by `Eq.refl`, and that definitional identity is cheap while
the morphisms of ringed topoi are variables and expensive once they are concrete terms. -/

section Appended

universe v'' u'' w''

variable {Z : RingedTopos.{v'', u'', w''}}
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A 2-morphism invertible after appending `k` induces an invertible transformation of direct
images of modules after `k_*`.**

A morphism of sheaves of modules is invertible as soon as its underlying morphism of sheaves of
sets is, and that underlying morphism is here the 2-morphism with `k_*` appended, because the
direct image of a sheaf of modules has the direct image of its underlying sheaf of sets
underneath. -/
theorem isIso_whiskerRight_pushforwardModulesMap (k : RingedToposHom Y Z)
    (h : IsIso (Functor.whiskerRight t.t k.toToposHom.pushforward)) :
    IsIso (Functor.whiskerRight t.pushforwardModulesMap k.pushforwardModules) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  refine (isIso_iff_of_reflects_iso
    ((Functor.whiskerRight t.pushforwardModulesMap k.pushforwardModules).app M)
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O))).mp ?_
  have e1 : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)).map
        ((Functor.whiskerRight t.pushforwardModulesMap k.pushforwardModules).app M) =
      k.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
          (t.pushforwardModulesMap.app M)) := rfl
  rw [e1, moduleSheafFunctor_map_pushforwardModulesMap]
  exact Iso.isIso_hom ((@asIso _ _ _ _
    (Functor.whiskerRight t.t k.toToposHom.pushforward) h).app
    (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M))

variable [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **The same invertibility on pullbacks of modules, after `k^*`.**

The transformation of pullbacks is the mate of the transformation of direct images, and
prepending a left adjoint to a mate is appending its right adjoint to the transformation it is
the mate of (`CategoryTheory.conjugateEquiv_whiskerLeft`). Conjugation carries isomorphisms to
isomorphisms, which is `CategoryTheory.conjugateIsoEquiv`. -/
theorem isIso_whiskerLeft_pullbackModulesMap (k : RingedToposHom Y Z)
    (h : IsIso (Functor.whiskerRight t.pushforwardModulesMap k.pushforwardModules)) :
    IsIso (Functor.whiskerLeft (k.toModulesHom.pullbackModules) t.pullbackModulesMap) := by
  have hconj : conjugateEquiv (pullbackAdjPushforwardModules f)
      (pullbackAdjPushforwardModules g) t.pullbackModulesMap = t.pushforwardModulesMap :=
    (conjugateEquiv _ _).apply_symm_apply _
  have hcw := conjugateEquiv_whiskerLeft (pullbackAdjPushforwardModules f)
    (pullbackAdjPushforwardModules g) (pullbackAdjPushforwardModules k) t.pullbackModulesMap
  have key : Functor.whiskerLeft (k.toModulesHom.pullbackModules) t.pullbackModulesMap =
      ((conjugateIsoEquiv
          ((pullbackAdjPushforwardModules k).comp (pullbackAdjPushforwardModules f))
          ((pullbackAdjPushforwardModules k).comp (pullbackAdjPushforwardModules g))).symm
        (@asIso _ _ _ _
          (Functor.whiskerRight t.pushforwardModulesMap k.pushforwardModules) h)).hom :=
    (Equiv.eq_symm_apply (conjugateEquiv _ _)).mpr
      (hcw.trans (congrArg (fun q ↦ Functor.whiskerRight q k.pushforwardModules) hconj))
  rw [key]
  exact Iso.isIso_hom _

end Appended

end AlgebraicGeometry.RingedToposHom.TwoMorphism

end
