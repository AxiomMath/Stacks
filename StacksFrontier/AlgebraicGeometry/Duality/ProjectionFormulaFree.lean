module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits
import all StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# The projection formula at a coproduct, and at a free module

Let `h : T ⟶ S` be a morphism of schemes and `G` a sheaf of `𝒪_T`-modules.  The
projection-formula morphism of `StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula`,

`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`,

is natural in `H`, and this file records both sides as functors of `H` and the morphism as a
natural transformation between them.  The point of doing so is the dévissage step: both
functors carry a coproduct cofan to a colimit cofan when `h` is quasi-compact, so the
projection formula holds at a coproduct as soon as it holds at each summand.  Combined with the
unconditional case `H = 𝒪_S` of
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_unit`, that gives the
projection formula for every free module `𝒪_S^{(ι)}`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectionFormula.tensorPushforwardFunctor`: the source
  `H ↦ h_*G ⊗_{𝒪_S} H`.
* `Stacks.AlgebraicGeometry.ProjectionFormula.pullbackTensorPushforwardFunctor`: the target
  `H ↦ h_*(G ⊗_{𝒪_T} h^*H)`.
* `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaNatTrans`: the
  projection-formula morphism as a natural transformation between the two.

## Main results

* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isColimit_cofan`:
  the dévissage step.  For a quasi-compact `h`, if the projection-formula morphism is
  invertible at each member of a family, it is invertible at the coproduct.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_free`: the projection
  formula for a free module on the target, for every quasi-compact `h` and every `G`.

## Implementation notes

The two colimit-preservation facts are quoted rather than reproved.  Tensoring with a fixed
sheaf of modules preserves all colimits — Tag 05NB,
`Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits` — and at the ringed-space
site its functor agrees with `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` in the
  second argument on the nose, so
no transport is needed.  The pushforward of a quasi-compact morphism of schemes preserves
coproducts, which is `AlgebraicGeometry.schemePushforward_preservesCoproducts`; that
declaration is `private`, so it is reached by `import all` and used only inside proofs.  It is
stated for `AlgebraicGeometry.Scheme.Modules.pushforward`, which is
`RingedSpaceModuleAdjunction.modulePushforward` on the structure morphism definitionally, so it
applies to the spelling used here directly.

The dévissage itself is `CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan`, which is
already available and is not reproved here.

Quasi-compactness, not affineness, is what the coproduct step needs, and no quasi-coherence
hypothesis appears: the results below are therefore stated for an arbitrary quasi-compact
morphism and an arbitrary `G`.  An affine morphism is quasi-compact, so they specialize to the
setting of Stacks 0FZE.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.AlgebraicGeometry.ProjectionFormula

open RingedSpaceModuleAdjunction Stacks.SheafOfModules.TensorColimits

universe u

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-! ### The two sides as functors of the module on the target -/

/-- The source of the projection-formula morphism, as a functor of the module on the target:
`H ↦ h_*G ⊗_{𝒪_S} H`. -/
def tensorPushforwardFunctor (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing S.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing S.toRingedSpace) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (J := (Opens.grothendieckTopology S.carrier))
    (S.toRingedSpace.sheaf)).obj ((modulePushforward h.toLRSHom.toShHom).obj G)

/-- The target of the projection-formula morphism, as a functor of the module on the target:
`H ↦ h_*(G ⊗_{𝒪_T} h^*H)`. -/
def pullbackTensorPushforwardFunctor (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing S.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing S.toRingedSpace) :=
  modulePullback h.toLRSHom.toShHom ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (J := (Opens.grothendieckTopology T.carrier)) (T.toRingedSpace.sheaf)).obj G ⋙
      modulePushforward h.toLRSHom.toShHom

/-- The value of `tensorPushforwardFunctor h G` at `H` is `h_*G ⊗_{𝒪_S} H`. -/
@[simp]
lemma tensorPushforwardFunctor_obj (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (tensorPushforwardFunctor h G).obj H =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.toRingedSpace.sheaf).obj
        (((modulePushforward h.toLRSHom.toShHom).obj G))).obj (H)) :=
  rfl

/-- The value of `pullbackTensorPushforwardFunctor h G` at `H` is `h_*(G ⊗_{𝒪_T} h^*H)`. -/
@[simp]
lemma pullbackTensorPushforwardFunctor_obj
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (pullbackTensorPushforwardFunctor h G).obj H =
      (modulePushforward h.toLRSHom.toShHom).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} T.toRingedSpace.sheaf).obj
          (G)).obj (((modulePullback h.toLRSHom.toShHom).obj H)))) :=
  rfl

/-- Tensoring on the left with a fixed `A` acts on `k` as the uncurried tensor on `(𝟙 A, k)`. -/
private lemma sheafTensor_obj_map_eq_uncurry_map (X : Scheme.{u})
    (A : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {F F' : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} (k : F ⟶ F') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj A).map
        k =
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf)).map
        (((𝟙 A), k) : (_, _) ⟶ (_, _)) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map X.toRingedSpace.sheaf A k).trans
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.toRingedSpace.sheaf (𝟙 A) k).symm

/-- The image of `k : H ⟶ H'` under `tensorPushforwardFunctor h G` is `𝟙_{h_*G} ⊗ k`. -/
lemma tensorPushforwardFunctor_map (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    {H H' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (k : H ⟶ H') :
    (tensorPushforwardFunctor h G).map k =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.toRingedSpace.sheaf)).map
        (((𝟙 ((modulePushforward h.toLRSHom.toShHom).obj G)), k) : (_, _) ⟶ (_, _))) :=
  sheafTensor_obj_map_eq_uncurry_map S _ k

/-- The image of `k : H ⟶ H'` under `pullbackTensorPushforwardFunctor h G` is
`h_*(𝟙 G ⊗ h^*k)`. -/
lemma pullbackTensorPushforwardFunctor_map
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    {H H' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (k : H ⟶ H') :
    (pullbackTensorPushforwardFunctor h G).map k =
      (modulePushforward h.toLRSHom.toShHom).map
        (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} T.toRingedSpace.sheaf)).map
          (((𝟙 G), ((modulePullback h.toLRSHom.toShHom).map k)) : (_, _) ⟶ (_, _)))) :=
  congrArg (modulePushforward h.toLRSHom.toShHom).map
    (sheafTensor_obj_map_eq_uncurry_map T G _)

/-- The projection-formula morphism as a natural transformation in the module on the target. -/
def projectionFormulaNatTrans (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) :
    tensorPushforwardFunctor h G ⟶ pullbackTensorPushforwardFunctor h G where
  app H := projectionFormulaMap h G H
  naturality H H' k := by
    rw [tensorPushforwardFunctor_map, pullbackTensorPushforwardFunctor_map]
    have hn := projectionFormulaMap_natural h (𝟙 G) k
    rw [CategoryTheory.Functor.map_id] at hn
    exact hn

/-- The component of `projectionFormulaNatTrans h G` at `H` is `projectionFormulaMap h G H`. -/
@[simp]
lemma projectionFormulaNatTrans_app (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (projectionFormulaNatTrans h G).app H = projectionFormulaMap h G H :=
  rfl

/-! ### Both sides preserve coproducts -/

/-- Tensoring preserves coproducts, so the source functor does: this is Tag 05NB at the
ringed-space site. -/
lemma preservesColimitsOfShape_tensorPushforwardFunctor
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (tensorPushforwardFunctor h G) :=
  (tensorLeft_preservesColimits (Opens.grothendieckTopology S.carrier) S.toRingedSpace.sheaf
    ((modulePushforward h.toLRSHom.toShHom).obj G)).preservesColimitsOfShape

/-- The pushforward along a quasi-compact morphism of schemes preserves coproducts of sheaves
of modules.  This is `AlgebraicGeometry.schemePushforward_preservesCoproducts`, which is
`private`, restated for the `RingedSpaceModuleAdjunction.modulePushforward` spelling that the
projection-formula morphism uses; the two agree definitionally. -/
lemma preservesColimitsOfShape_modulePushforward [QuasiCompact h] (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (modulePushforward h.toLRSHom.toShHom) :=
  _root_.AlgebraicGeometry.schemePushforward_preservesCoproducts h ι

/-- The target functor carries a colimit cocone of a discrete diagram to a colimit cocone: the
pullback is a left adjoint, tensoring is Tag 05NB, and the pushforward of a quasi-compact
morphism preserves coproducts.

The three witnesses are applied through their fields rather than through
`CategoryTheory.Limits.isColimitOfPreserves`, which takes them as instance arguments: instance
search does not see past the two spellings `AlgebraicGeometry.Scheme.Modules.pushforward` and
`RingedSpaceModuleAdjunction.modulePushforward` of the pushforward, nor past the two spellings
of the ring of scalars that `tensorLeft` uses. -/
def isColimitMapCoconePullbackTensorPushforwardFunctor [QuasiCompact h]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {ι : Type u}
    {Z : Discrete ι ⥤ SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} {c : Cocone Z}
    (hc : IsColimit c) :
    IsColimit ((pullbackTensorPushforwardFunctor h G).mapCocone c) := by
  have hpull : PreservesColimitsOfShape (Discrete ι)
      (modulePullback h.toLRSHom.toShHom) :=
    ((modulePullbackPushforwardAdjunction
      h.toLRSHom.toShHom).leftAdjoint_preservesColimits).preservesColimitsOfShape
  have hten : PreservesColimitsOfShape (Discrete ι)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (J := (Opens.grothendieckTopology T.carrier)) (T.toRingedSpace.sheaf)).obj G) :=
    (tensorLeft_preservesColimits (Opens.grothendieckTopology T.carrier)
      T.toRingedSpace.sheaf G).preservesColimitsOfShape
  have hpush := preservesColimitsOfShape_modulePushforward h ι
  exact (hpush.preservesColimit.preserves
    (hten.preservesColimit.preserves
      (hpull.preservesColimit.preserves hc).some).some).some

/-! ### The dévissage step, and the free case -/

/-- **The dévissage step for Stacks Tag 0FZE.**  For a quasi-compact morphism of schemes, if the
projection-formula morphism is invertible at every member of a family of modules on the target,
then it is invertible at the coproduct of the family. -/
lemma isIso_projectionFormulaMap_of_isColimit_cofan [QuasiCompact h]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {ι : Type u}
    {f : ι → SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (c : Cofan f)
    (hc : IsColimit c)
    (hf : ∀ i, IsIso (projectionFormulaMap h G (f i))) :
    IsIso (projectionFormulaMap h G c.pt) :=
  CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan (projectionFormulaNatTrans h G) c
    ((preservesColimitsOfShape_tensorPushforwardFunctor h G
      ι).preservesColimit.preserves hc).some
    (isColimitMapCoconePullbackTensorPushforwardFunctor h G hc) hf

/-- **The projection formula for a free module on the target.**  For every quasi-compact
morphism of schemes `h : T ⟶ S`, every sheaf of `𝒪_T`-modules `G` and every family of copies of
`𝒪_S`, the projection-formula morphism is invertible at the coproduct — with no affineness and
no quasi-coherence.  This is the base case of the dévissage in `H` for Stacks 0FZE. -/
lemma isIso_projectionFormulaMap_free [QuasiCompact h]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {ι : Type u}
    (c : Cofan (fun _ : ι => SheafOfModules.unit (structureSheafRing S.toRingedSpace)))
    (hc : IsColimit c) :
    IsIso (projectionFormulaMap h G c.pt) :=
  isIso_projectionFormulaMap_of_isColimit_cofan h G c hc fun _ =>
    isIso_projectionFormulaMap_unit h G

end Stacks.AlgebraicGeometry.ProjectionFormula

end
