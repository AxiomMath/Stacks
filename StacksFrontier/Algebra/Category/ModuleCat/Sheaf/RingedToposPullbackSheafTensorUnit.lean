module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackRightUnitality

/-!
# The right unitor of the strict structure is the unit law of `⊗_O`, and its pullback

Let `O` be a sheaf of commutative rings on a site, with sections in a universe `w` independent of
the two universes of the site. The right unitor `F ⊗ O ≅ F` of the strict monoidal structure
`Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` (the structure of Tag 01CA whose tensor
product is the tensor product sheaf on the nose) is the unit law
`Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections` of the tensor bifunctor of Tag 06YM: both
are the sheafification of the presheaf right unitor followed by the counit of sheafification.

For a morphism of ringed topoi this reads the right-unitality coherence of Tag 03EL,
`Stacks.SheafOfModules.RingedToposPullback.rightUnitality`, at the tensor bifunctor of Tag 06YM.

## Main results

* `Stacks.SheafOfModules.Strict.rightUnitor_hom_eq_sheafTensorUnitIsoFreeSections`.
* `Stacks.SheafOfModules.RingedToposPullback.pullbackModules_map_sheafTensorUnitIsoFreeSections`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe w v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

attribute [local instance] monoidalUnderlyingRingSheaf

/-- **The right unitor of the strict monoidal structure is the unit law of `⊗_O`**, at a free
universe of the sections: `ρ_F` is `Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections O F`. -/
theorem rightUnitor_hom_eq_sheafTensorUnitIsoFreeSections
    (F : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    (ρ_ F).hom = (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections O F).hom :=
  (congrArg Iso.hom (Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor O.obj
    (TensorEncodings.isSheaf_structureRingPresheaf O) F)).trans rfl

end Stacks.SheafOfModules.Strict

namespace Stacks.SheafOfModules.RingedToposPullback

open AlgebraicGeometry Stacks.Sheaves.RingedToposModules

universe v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

attribute [local instance] Strict.monoidalUnderlyingRingSheaf

/-- **The right-unitality coherence of Tag 03EL for the unit law of `⊗_O`**:
`f^*(F ⊗ O_D ≅ F)` is the comparison of Tag 03EL followed by `f^*F ⊗ ν` for the unit comparison
`ν : f^*O_D ≅ O_C` and by the unit law of `f^*F`. This is
`Stacks.SheafOfModules.RingedToposPullback.rightUnitality` read at the tensor bifunctor of
Tag 06YM. -/
theorem pullbackModules_map_sheafTensorUnitIsoFreeSections
    (F : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.pullbackModules.map (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections Y.O F).hom =
      (Stacks.SheafOfModules.pullbackTensorIso f).hom.app
          (F, _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (f.pullbackModules.obj F)).map
            (pullbackModulesObjUnitIso f).inv ≫
          (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O
            (f.pullbackModules.obj F)).hom := by
  have h := rightUnitality f F
  rw [Strict.rightUnitor_hom_eq_sheafTensorUnitIsoFreeSections,
    Strict.rightUnitor_hom_eq_sheafTensorUnitIsoFreeSections,
    Strict.whiskerLeft_eq_tensorSheafBifunctor_map, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp] at h
  exact h

end Stacks.SheafOfModules.RingedToposPullback

end
