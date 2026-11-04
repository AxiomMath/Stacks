module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules

/-!
# The unit of the module adjunction at the unit module is the unit of the ring adjunction

For a morphism of topoi `f` and a sheaf of rings `O` on its target, the adjunction of
Stacks 03D3 between the inverse image and the direct image of sheaves of modules has a unit
`O-Mod ∋ G ⟶ f_*f⁻¹G`.  At `G = O` itself, read as a module over itself, the underlying morphism
of sheaves of sets of that unit is the unit of `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of
`O` — the same morphism the unit of the ring-level adjunction of Stacks 00YV reduces to.

## Main results

* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_unit_app_unit`.
* `Stacks.Sheaves.RingedToposModules.unit_app_unit_val_app_eq_commRingUnit`: the same read on
  sections against the unit of the adjunction of Stacks 00YV on sheaves of commutative rings.
* `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules_unit_app_val_app`: the unit
  of the adjunction of Stacks 03D7 for a morphism of ringed topoi, in its two factors on
  sections — the unit of Stacks 03D3 followed by the direct image of the unit of Stacks 03CZ.
  The factorization itself is the base's
  `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules_unit_app`, in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainSections`.

## Implementation notes

The adjunction of Stacks 03D3 is built by `CategoryTheory.Adjunction.mkOfHomEquiv`, whose unit at
an object is the hom-set bijection applied to the identity — `rfl`, since `mkOfHomEquiv` records
that unit as structure data.  Reading that bijection on underlying sheaves of sets is
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_toposModulesHomEquiv`, also `rfl`, and
what is left is `CategoryTheory.Adjunction.homEquiv_id` for `f⁻¹ ⊣ f_*`.  The two objects it has
to be read at agree on the nose by
`Stacks.Sheaves.ToposPullback.pullbackModuleObj_unit` and
`Stacks.Sheaves.ToposPullback.moduleSheaf_unit`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

namespace Stacks.Sheaves.RingedToposModules

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- **The unit of the adjunction of Stacks 03D3 at the unit module is the unit of `f⁻¹ ⊣ f_*`**
on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_unit_app_unit :
    (Sheaf.moduleSheafFunctor O).map
        ((inverseImageAdjDirectImageModules f O).unit.app (SheafOfModules.unit O)) =
      f.adj.unit.app (Sheaf.ringSheaf O) :=
  have h0 : (inverseImageAdjDirectImageModules f O).unit.app (SheafOfModules.unit O) =
      toposModulesHomEquiv f O (SheafOfModules.unit O)
        ((inverseImageModules f O).obj (SheafOfModules.unit O))
        (𝟙 ((inverseImageModules f O).obj (SheafOfModules.unit O))) := rfl
  Eq.trans (congrArg (Sheaf.moduleSheafFunctor O).map h0)
    (Eq.trans (moduleSheafFunctor_map_toposModulesHomEquiv f O _)
      (Eq.trans
        (congrArg (fun m ↦ f.adj.homEquiv (Sheaf.moduleSheaf O (SheafOfModules.unit O))
            (Sheaf.moduleSheaf (inverseImageRingSheaf f O)
              ((inverseImageModules f O).obj (SheafOfModules.unit O))) m)
          (CategoryTheory.Functor.map_id
            (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O))
            ((inverseImageModules f O).obj (SheafOfModules.unit O))))
        (f.adj.homEquiv_id (Sheaf.ringSheaf O))))

/-! ### The module unit and the ring unit -/

section CommRing

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [K.HasSheafCompose (forget CommRingCat.{w'})]
  (A : Sheaf K CommRingCat.{w'})

/-- **The unit of Stacks 03D3 at the structure sheaf read as a module over itself is the unit of
the ring-level adjunction of Stacks 00YV**, on sections.  Both are the unit of `f⁻¹ ⊣ f_*` on the
underlying sheaf of sets. -/
theorem unit_app_unit_val_app_eq_commRingUnit (U : Dᵒᵖ) (b : ToType (A.obj.obj U)) :
    ((inverseImageAdjDirectImageModules f (Stacks.SheafOfModules.Tensor.ringSheaf A)).unit.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A))).val.app U b =
      ((commRingImageAdjunction f).unit.app A).hom.app U b :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor K U).map m b)
    ((moduleSheafFunctor_map_unit_app_unit f (Stacks.SheafOfModules.Tensor.ringSheaf A)).trans
      (forget_map_commRingImageAdjunction_unit_app f A).symm)

end CommRing

/-! ### The unit of Stacks 03LU, in its two factors -/

section RingedTopos

open AlgebraicGeometry

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (g : RingedToposHom X Y)
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The unit of Stacks 03D7 on sections, in its two factors. -/
theorem pullbackAdjPushforwardModules_unit_app_val_app
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (U : Y.Cᵒᵖ)
    (x : M.val.obj U) :
    ((pullbackAdjPushforwardModules g).unit.app M).val.app U x =
      ((directImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing g)
            (inverseImageRingSheaf g.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageModules g.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))).val.app U
        (((inverseImageAdjDirectImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).unit.app M).val.app U x) :=
  congrArg (fun m ↦ (m.val.app U) x) (pullbackAdjPushforwardModules_unit_app g M)

end RingedTopos

end Stacks.Sheaves.RingedToposModules

end
