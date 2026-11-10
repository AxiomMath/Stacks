module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Deformation.ToposThickening.TwoExtensions

/-!
# Compatibility of the ideal action with a map of extensions

A morphism between the middle terms of two extensions over a first order thickening, compatible
with the given maps on their kernel and quotient modules, intertwines their canonical
ideal-action maps.

The middle-term morphism is required to commute with both maps of the two short exact sequences.
The induced map on the tensor products is the one coming from the identity on the ideal and the
given map on quotients, and the compatibility is an equality of morphisms of sheaves of modules.

## Main definitions

* `Deformation.ToposThickening.idealTensorMap`: the map on the tensor products induced by the
  identity on the square-zero ideal and the given map of quotient modules.

## Main results

* `Deformation.ToposThickening.idealActionMap_naturality`: the compatibility of the two
  ideal-action maps.

## References

* [Stacks Project, Tag 08MC](https://stacks.math.columbia.edu/tag/08MC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-- The map on the tensor products with the square-zero ideal induced by the given map of
quotient modules. -/
noncomputable def idealTensorMap (D : TwoExtensions i) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj D.thickening.I).obj D.F ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj D.thickening.I).obj D.G :=
  (PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 D.thickening.I.val) D.quotientMap.val)

/-- A map of extensions compatible with its maps on kernels and quotients commutes with
multiplication by sections of the square-zero ideal. -/
theorem idealActionMap_naturality
    (D : TwoExtensions i)
    (φ' : D.firstExtension.Z.left ⟶ D.secondExtension.Z.left)
    (hkernel : D.firstExtension.f ≫ φ' =
      (SheafOfModules.restrictScalars
        ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map
          D.kernelMap ≫ D.secondExtension.f)
    (hquotient : φ' ≫ D.secondExtension.g =
      D.firstExtension.g ≫
        (SheafOfModules.restrictScalars
          ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map
            D.quotientMap) :
    D.firstActionMap.val ≫ D.kernelMap =
      idealTensorMap D ≫ D.secondActionMap.val := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj D.thickening.I.val D.F.val
  let adj := PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)
  let left := adj.homEquiv P D.L (D.firstActionMap.val ≫ D.kernelMap)
  let right := adj.homEquiv P D.L (idealTensorMap D ≫ D.secondActionMap.val)
  have hL := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf Y.J D.L.val.presheaf (forget AddCommGrpCat.{w'})
      D.L.isSheaf)
  have hg : Presheaf.IsLocallySurjective Y.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj).map
        D.firstExtension.g.val) :=
    sheafModule_epi_locallySurjective D.firstExtension.g
  apply (adj.homEquiv P D.L).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a x
  change left.app U
      (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x) =
    right.app U (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x)
  apply (hL.isSeparated _ (Presheaf.imageSieve_mem Y.J
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj).map
      D.firstExtension.g.val) x)).ext
  rintro V m ⟨x', hx'⟩
  change D.L.val.map m.op (left.app U
      (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x)) =
    D.L.val.map m.op (right.app U
      (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x))
  have hnat : ∀ f : type_of% left, D.L.val.map m.op (f.app U
        (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x)) =
      f.app (Opposite.op V) (P.map m.op
        (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x)) :=
    fun f => (PresheafOfModules.naturality_apply f m.op _).symm
  let : Module (((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj (Opposite.op V))
      (D.thickening.I.val.obj (Opposite.op V)) :=
    (D.thickening.I.val.obj (Opposite.op V)).isModule
  let : Module (((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj (Opposite.op V))
      (D.F.val.obj (Opposite.op V)) := (D.F.val.obj (Opposite.op V)).isModule
  let : Module (((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj (Opposite.op V))
      (D.G.val.obj (Opposite.op V)) := (D.G.val.obj (Opposite.op V)).isModule
  let aV : D.thickening.I.val.obj (Opposite.op V) := D.thickening.I.val.map m.op a
  let xV : D.F.val.obj (Opposite.op V) := D.F.val.map m.op x
  have htmul : P.map m.op
        (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x) =
      aV ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj
        (Opposite.op V)] xV := rfl
  change D.firstExtension.g.val.app (Opposite.op V) x' = D.F.val.map m.op x at hx'
  let gxV : D.F.val.obj (Opposite.op V) := D.firstExtension.g.val.app (Opposite.op V) x'
  have hxV : xV = gxV := hx'.symm
  rw [hnat left, hnat right, htmul, hxV]
  have hright : right = PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 D.thickening.I.val)
      D.quotientMap.val ≫ adj.homEquiv _ D.L D.secondActionMap.val :=
    adj.homEquiv_naturality_left _ _
  rw [hright]
  change left.app (Opposite.op V)
      (aV ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj (Opposite.op V)]
        gxV) =
    (adj.homEquiv (PresheafOfModulesOfCommRing.Monoidal.tensorObj D.thickening.I.val D.G.val) D.L
        D.secondActionMap.val).app (Opposite.op V)
      (aV ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj (Opposite.op V)]
        D.quotientMap.val.app (Opposite.op V) gxV)
  have hq := congrArg (fun k => k.val.app (Opposite.op V) x') hquotient
  change D.secondExtension.g.val.app (Opposite.op V) (φ'.val.app (Opposite.op V) x') =
    D.quotientMap.val.app (Opposite.op V)
      (D.firstExtension.g.val.app (Opposite.op V) x') at hq
  rw [← hq]
  have hmono : Mono D.secondExtension.f.val :=
    (SheafOfModules.forget _).map_mono D.secondExtension.f
  apply PresheafOfModules.injective_of_mono D.secondExtension.f.val (Opposite.op V)
  have hb := D.firstActionMap.property (Opposite.op V) aV x'
  have hk := congrArg (fun k => k.val.app (Opposite.op V)
    (D.firstActionMap.val.val.app (Opposite.op V)
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj
          X.O)).obj)).unit.app
        (PresheafOfModules.tensorObj D.thickening.I.val D.F.val)).app (Opposite.op V)
        (aV ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj (Opposite.op V)]
          gxV)))) hkernel
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (D.firstExtension.Z.left.val.obj (Opposite.op V)) :=
    (D.firstExtension.Z.left.val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (D.secondExtension.Z.left.val.obj (Opposite.op V)) :=
    (D.secondExtension.Z.left.val.obj (Opposite.op V)).isModule
  have hs := D.secondActionMap.property (Opposite.op V) aV (φ'.val.app (Opposite.op V) x')
  refine hk.symm.trans ?_
  refine (congrArg (fun z => φ'.val.app (Opposite.op V) z) hb).trans ?_
  refine Eq.trans ?_ hs.symm
  exact map_smul _ _ _

end Deformation.ToposThickening

end
