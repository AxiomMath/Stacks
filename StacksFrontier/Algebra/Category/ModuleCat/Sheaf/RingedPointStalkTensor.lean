module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The stalk of a tensor product of sheaves of modules at a point of a ringed topos

Let `(Sh(C), O)` be a ringed topos and let `p` be a point of `Sh(C)`. Section 18.37 of the
source observes that, since `p⁻¹` is the stalk functor, the point may be read as a morphism of
ringed topoi

`(p, id) : (Sh(pt), O_p) ⟶ (Sh(C), O)`,

whose pullback functor on modules `p^* : Mod(O) ⥤ Mod(O_p)` *is* the stalk. That reading is
`Stacks.Sheaves.RingedPoint.RingedPointSituation`, and the identification of `p^*` with the
module-valued stalk is `RingedPointSituation.pullbackStalkIso`.

This file draws the consequence the source uses when it says that "taking stalks at `p`
commutes with `⊗`": **Stacks 03EL**, the compatibility of pullback with the tensor product
along an arbitrary morphism of ringed topoi, instantiated at the morphism out of the ringed
point. No new mathematics is needed — once the point is a morphism of ringed topoi and its
pullback is the stalk, the general statement specialises.

## Main results

* `Stacks.Sheaves.RingedPoint.RingedPointSituation.stalkTensorIso`: the module-valued stalk at
  a point of a ringed topos commutes with the tensor product of sheaves of modules,

  `(F ⊗_O G)_p ≅ F_p ⊗_{O_p} G_p`,

  naturally in the pair `(F, G)`.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.stalkTensorObjIso`: the same isomorphism
  read on a single pair of sheaves of modules.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.stalkTensorUnderlyingIso`: the underlying
  sheaf of sets of the stalk of a tensor product is the stalk `p⁻¹(F ⊗_O G)` of the underlying
  sheaf, naturally in the pair.

## Implementation notes

The instances the general tensor product needs on the site of the point
(`HasSheafCompose (forget AddCommGrpCat)`, `HasWeakSheafify` and `WEqualsLocallyBijective`) are
taken as hypotheses rather than derived, because `RingedPointSituation` is stated for an
arbitrary presentation of the point and so its site is arbitrary. For the canonical
presentation `Stacks.Sheaves.RingedPoint.ringedPointSituation` the site carries the trivial
topology, where every presheaf is a sheaf, so all three are available there.

## References

* [Stacks Project, Tag 05V6](https://stacks.math.columbia.edu/tag/05V6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedPoint.RingedPointSituation

universe v u w vₚ uₚ

variable {X : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {p : PointOfTopos.{w, v, u} X.J}
  (s : RingedPointSituation.{v, u, w, vₚ, uₚ} X p)
  [s.point.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
  [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The stalk commutes with the tensor product of sheaves of modules.** At a point `p` of a
ringed topos `(Sh(C), O)` the module-valued stalk carries a tensor product of sheaves of
`O`-modules to the tensor product of the stalks over `O_p`,

`(F ⊗_O G)_p ≅ F_p ⊗_{O_p} G_p`,

naturally in `F` and in `G`. This is Tag 03EL — the compatibility of pullback with the tensor
product along a morphism of ringed topoi — read along the morphism out of the ringed point of
Section 18.37, whose pullback on modules is the stalk
(`RingedPointSituation.pullbackStalkIso`). -/
@[stacks 03EL "the stalk at a point of a ringed topos commutes with the tensor product"]
def stalkTensorIso :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)) ⋙ s.stalkModules ≅
      Functor.prod s.stalkModules s.stalkModules ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor s.point.O)) :=
  Functor.isoWhiskerLeft _ s.pullbackStalkIso.symm ≪≫
    Stacks.SheafOfModules.pullbackTensorIso s.toRingedToposHom ≪≫
    Functor.isoWhiskerRight (NatIso.prod s.pullbackStalkIso s.pullbackStalkIso) _

/-- The isomorphism `(F ⊗_O G)_p ≅ F_p ⊗_{O_p} G_p` of `stalkTensorIso` read on a single pair
of sheaves of `O`-modules. -/
def stalkTensorObjIso (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    s.stalkModules.obj (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor s.point.O).obj (s.stalkModules.obj F)).obj
          (s.stalkModules.obj G) :=
  s.stalkTensorIso.app (F, G)

/-- The underlying sheaf of the stalk of a tensor product of sheaves of modules is the stalk
`p⁻¹(F ⊗_O G)` of the underlying sheaf, naturally in the pair: combine `stalkTensorIso` with
the identification `RingedPointSituation.stalkModulesUnderlyingIso` of the underlying sheaf of
the module-valued stalk with the stalk of the underlying sheaf. -/
def stalkTensorUnderlyingIso :
    Functor.prod s.stalkModules s.stalkModules ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor s.point.O)) ⋙
          Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
            s.pointEquiv.functor ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)) ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ p.inverseImage :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight s.stalkTensorIso.symm
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
        s.pointEquiv.functor) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)))
      s.stalkModulesUnderlyingIso

end Stacks.Sheaves.RingedPoint.RingedPointSituation

end
