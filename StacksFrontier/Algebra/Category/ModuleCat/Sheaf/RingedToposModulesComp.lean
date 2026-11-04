module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# The scalar action of a direct image of modules, read through an arbitrary functor

The scalar action on the inverse image and on the direct image of a sheaf of modules along a
morphism of ringed topoi, transported along an arbitrary finite-product-preserving functor to
types, and the underlying sheaf of sets of a composite of two direct images of modules.

## Main results

* `Stacks.Sheaves.ToposPullback.moduleSMulObj_pullbackModuleObj`: the action on an inverse
  image of a sheaf of modules, transported along a functor `P`, is the action on the original
  module transported along `Φ ⋙ P`.
* `Stacks.Sheaves.RingedToposModules.moduleSMulObj_pushforwardModules`: the action on a direct
  image along a morphism of ringed topoi, transported along `P`, is the action on the original
  module transported along `f_* ⋙ P`, with the scalar carried along the direct-image form
  `f♯ : O_D ⟶ f_*O_C` of the structure map.
* `Stacks.Sheaves.RingedToposModules.moduleSheaf_pushforwardModules_comp`: a composite of two
  direct images of modules and the direct image along the composite morphism of ringed topoi
  have the *same* underlying sheaf of sets.

## Implementation notes

`moduleSheaf_pushforwardModules_comp` chains three instances of
`Stacks.Sheaves.RingedToposModules.moduleSheaf_pushforwardModules` rather than closing by `rfl`:
the direct unification of the two sides exhausts the default heartbeat budget, because it
unfolds `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` on both sides.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe t ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'}) (G : SheafOfModules.{ww'} O)

/-- The action on the inverse image of a sheaf of modules along `Φ`, transported to the image of
a finite-product-preserving functor `P` to types, is the action on the original module
transported along `Φ ⋙ P`. -/
lemma moduleSMulObj_pullbackModuleObj (P : Sheaf J (Type ww) ⥤ Type t)
    [PreservesFiniteProducts P]
    (r : P.obj (Φ.obj (Sheaf.ringSheaf O))) (m : P.obj (Φ.obj (Sheaf.moduleSheaf O G))) :
    Sheaf.moduleSMulObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) P r m =
      Sheaf.moduleSMulObj O G (Φ ⋙ P) r m := by
  have : PreservesFiniteProducts (Φ ⋙ P) := inferInstance
  show P.map _ (Functor.prodObjMk r m) =
    (Φ ⋙ P).map (Sheaf.moduleSMulHom O G) (Functor.prodObjMk (P := Φ ⋙ P) r m)
  refine Eq.symm (Eq.trans (congrArg
    (fun n ↦ P.map n (Functor.prodObjMk (P := Φ ⋙ P) r m)) (moduleSMul_map_aux' J Φ O G)) ?_)
  refine Eq.trans (P.map_comp_apply _ _ _) ?_
  congr 1
  rw [Functor.map_prodComparison_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.RingedToposModules

open AlgebraicGeometry

universe t w w' w'' v u v' u' v'' u''

section Pushforward

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y)

/-- The action on the direct image of a sheaf of modules along a morphism of ringed topoi,
transported to the image of a finite-product-preserving functor `P` to types, is the action on
the original module transported along `f_* ⋙ P`, with the scalar carried along the direct-image
form `f♯ : O_D ⟶ f_*O_C` of the structure map. -/
lemma moduleSMulObj_pushforwardModules
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (P : Sheaf Y.J (Type w') ⥤ Type t) [PreservesFiniteProducts P]
    (r : P.obj (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (m : P.obj (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj M))) :
    Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M) P r m =
      Sheaf.moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        (f.toToposHom.pushforward ⋙ P)
        (P.map ((sheafCompose Y.J (forget RingCat.{w'})).map f.fSharp) r) m := by
  have : PreservesFiniteProducts (f.toToposHom.pushforward ⋙ P) := inferInstance
  refine Eq.trans (moduleSMulObj_restrictScalars
    (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((pushforwardModuleFunctor f.toToposHom
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)) P r m) ?_
  refine Eq.trans (moduleSMulObj_pullbackModuleObj Y.J f.toToposHom.pushforward
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M) P _ m) ?_
  refine Eq.trans (moduleSMulObj_restrictScalars f.fSharpInverseImage M
    (f.toToposHom.pushforward ⋙ P) _ m) ?_
  congr 1
  refine Eq.trans ?_ (congrArg (fun n ↦ P.map n r) (fSharp_underlying f)).symm
  exact (P.map_comp_apply _ _ _).symm

/-- The underlying morphism of sheaves of sets of the direct image of a morphism of sheaves of
modules along a morphism of ringed topoi is the direct image of the underlying morphism. -/
lemma moduleSheafFunctor_map_pushforwardModules_map
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : M ⟶ N) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pushforwardModules f).map α) =
      f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map α) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Pushforward

section Composition

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

/-- A composite of two direct images of sheaves of modules and the direct image along the
composite morphism of ringed topoi have the same underlying sheaf of sets. -/
theorem moduleSheaf_pushforwardModules_comp (g : AlgebraicGeometry.RingedToposHom Y Z)
    (f : AlgebraicGeometry.RingedToposHom X Y)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        ((pushforwardModules g.toRingedToposModulesHom).obj
          ((pushforwardModules f.toRingedToposModulesHom).obj M)) =
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        ((pushforwardModules (g.comp f).toRingedToposModulesHom).obj M) :=
  (moduleSheaf_pushforwardModules g.toRingedToposModulesHom
      ((pushforwardModules f.toRingedToposModulesHom).obj M)).trans
    ((congrArg g.toToposHom.pushforward.obj
        (moduleSheaf_pushforwardModules f.toRingedToposModulesHom M)).trans
      (moduleSheaf_pushforwardModules (g.comp f).toRingedToposModulesHom M).symm)

end Composition

end Stacks.Sheaves.RingedToposModules

end
