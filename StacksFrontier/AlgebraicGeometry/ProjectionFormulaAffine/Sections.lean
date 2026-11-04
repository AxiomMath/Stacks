module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.AffineTransport
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections

/-!
# The projection-formula map on local sections

`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` is defined by adjunction, as the
transpose of
the Stacks 01CD comparison composed with the counit, and so says nothing on its face about
what it does to a section.  This file computes it.

For a morphism of schemes `h : T ⟶ S`, an open `U` of `S`, a section `a` of `h_*G` over `U`
--- that is, a section of `G` over `h⁻¹U` --- and a section `b` of `H` over `U`, the
projection-formula map carries the image of `a ⊗ b` in `(h_*G ⊗_{𝒪_S} H)(U)` to the image of
`a ⊗ b♯` in `(G ⊗_{𝒪_T} h^*H)(h⁻¹U)`, where `b♯` is the section of `h^*H` over `h⁻¹U` given by
the unit of `h^* ⊣ h_*`.  There are no hypotheses: `h` is arbitrary and `G`, `H` need not be
quasi-coherent.

Since the images of pure tensors of sections generate a tensor product of sheaves of modules
--- `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf_hom_ext` --- this formula
-- *determines* the projection-formula
map, which is `projectionFormulaMap_unique`.

## Main results

* `Stacks.ProjectionFormula.projectionFormulaMap_app_toTensorSheafSection`: the formula above.
* `Stacks.ProjectionFormula.projectionFormulaMap_app_top`: its reading over the whole base,
  which is the form the affine criterion
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` consumes.
* `Stacks.ProjectionFormula.projectionFormulaMap_unique`: a morphism with the same effect on
  images of pure tensors of sections *is* the projection-formula map.

## Implementation notes

The proof is the composite of three facts, none of which is about the projection formula.
Writing `η`, `ε` for the unit and counit of `h^* ⊣ h_*`:

* the transpose of a composite is the transpose followed by the pushforward
  (`Adjunction.homEquiv_naturality_right`), which splits `projectionFormulaMap` into the
  transpose of the 01CD comparison and the pushforward of `ε ⊗ 𝟙`;
* the canonicality clause of Stacks 01CD,
  `Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul`, which computes the first factor
  on the image of `a ⊗ b` as the image of `η a ⊗ η b`;
* the triangle identity `Adjunction.right_triangle_components`, read on sections, which turns
  `ε (η a)` back into `a`.

Three spellings of the structure sheaf of a scheme are in play and all are equal by `rfl`, so the
three facts are restated here in the vocabulary of `projectionFormulaMap` --- `structureSheafRing`,
`modulePullback`, `modulePushforward`,
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` --- and discharged by `exact`,
which crosses the difference.  `rw` does not: the pattern it builds from a lemma stated in another
spelling carries that spelling's instances and fails to match a goal in this one.

A section of `h_*G` over `U` and a section of `G` over `h⁻¹U` are the same term, the pushforward
of a presheaf of modules being given by reindexing, so no transport appears in the statement.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace Stacks.ProjectionFormula

open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula

universe u

variable {T S : Scheme.{u}} (h : T ⟶ S)
  (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))

/-- **The projection-formula map on a pure tensor of sections.**  Over an open `U` of `S` it
carries the image of `a ⊗ b`, for `a` a section of `h_*G` over `U` and `b` a section of `H`
over `U`, to the image of `a ⊗ η b`, where `η` is the unit of `h^* ⊣ h_*`.

No hypothesis is placed on `h`, `G` or `H`. -/
theorem projectionFormulaMap_app_toTensorSheafSection (U : Opens S.carrier)
    (a : ((modulePushforward h.toLRSHom.toShHom).obj G).val.obj (op U))
    (b : H.val.obj (op U)) :
    ((projectionFormulaMap h G H).val.app (op U)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection S.toRingedSpace
          ((modulePushforward h.toLRSHom.toShHom).obj G) H (op U)
          (a ⊗ₜ[S.toRingedSpace.presheaf.obj (op U)] b))
      = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection T.toRingedSpace G
          ((modulePullback h.toLRSHom.toShHom).obj H)
          (op ((opensMap h.toLRSHom.toShHom).obj U))
          (a ⊗ₜ[T.toRingedSpace.presheaf.obj (op ((opensMap h.toLRSHom.toShHom).obj U))]
            (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app H).val.app
              (op U)).hom b) := by
  have key : projectionFormulaMap h G H =
      ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
        ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((modulePushforward h.toLRSHom.toShHom).obj G, H))) ≫
      (modulePushforward h.toLRSHom.toShHom).map
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
          (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G,
            𝟙 ((modulePullback h.toLRSHom.toShHom).obj H)) : (_, _) ⟶ (_, _))) :=
    (projectionFormulaMap_eq h G H).trans
      (Adjunction.homEquiv_naturality_right _ _ _)
  have hc : ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
        ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((modulePushforward h.toLRSHom.toShHom).obj G, H))).val.app (op U)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection S.toRingedSpace
          ((modulePushforward h.toLRSHom.toShHom).obj G) H (op U)
          (a ⊗ₜ[S.toRingedSpace.presheaf.obj (op U)] b)))
      = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection T.toRingedSpace
          ((modulePullback h.toLRSHom.toShHom).obj
            ((modulePushforward h.toLRSHom.toShHom).obj G))
          ((modulePullback h.toLRSHom.toShHom).obj H)
          (op ((opensMap h.toLRSHom.toShHom).obj U))
          ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app
              ((modulePushforward h.toLRSHom.toShHom).obj G)).val.app (op U)).hom a
            ⊗ₜ[T.toRingedSpace.presheaf.obj (op ((opensMap h.toLRSHom.toShHom).obj U))]
            (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app H).val.app
              (op U)).hom b) :=
    Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul _ _ _ (op U) a b
  have htri : (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G).val.app
        (op ((opensMap h.toLRSHom.toShHom).obj U))).hom
      ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app
          ((modulePushforward h.toLRSHom.toShHom).obj G)).val.app (op U)).hom a) = a :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (congrArg (fun φ : (modulePushforward h.toLRSHom.toShHom).obj G ⟶
          (modulePushforward h.toLRSHom.toShHom).obj G => φ.val.app (op U))
        ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).right_triangle_components
          (Y := G)))) a
  have hm : ∀ (m : ((modulePullback h.toLRSHom.toShHom).obj
          ((modulePushforward h.toLRSHom.toShHom).obj G)).val.obj
          (op ((opensMap h.toLRSHom.toShHom).obj U)))
      (n : ((modulePullback h.toLRSHom.toShHom).obj H).val.obj
          (op ((opensMap h.toLRSHom.toShHom).obj U))),
      (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
          (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G,
            𝟙 ((modulePullback h.toLRSHom.toShHom).obj H)) : (_, _) ⟶ (_, _))).val.app
            (op ((opensMap h.toLRSHom.toShHom).obj U))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection T.toRingedSpace
          ((modulePullback h.toLRSHom.toShHom).obj
            ((modulePushforward h.toLRSHom.toShHom).obj G))
          ((modulePullback h.toLRSHom.toShHom).obj H)
          (op ((opensMap h.toLRSHom.toShHom).obj U))
          (m ⊗ₜ[T.toRingedSpace.presheaf.obj (op ((opensMap h.toLRSHom.toShHom).obj U))] n))
        = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection T.toRingedSpace G
            ((modulePullback h.toLRSHom.toShHom).obj H)
            (op ((opensMap h.toLRSHom.toShHom).obj U))
            ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G).val.app
                (op ((opensMap h.toLRSHom.toShHom).obj U))).hom m
              ⊗ₜ[T.toRingedSpace.presheaf.obj (op ((opensMap h.toLRSHom.toShHom).obj U))] n) :=
    fun m n => Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
      _ _ _ _ _ _ _ _ m n
  rw [key]
  show (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
            (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G,
              𝟙 ((modulePullback h.toLRSHom.toShHom).obj H)) : (_, _) ⟶ (_, _))).val.app
          (op ((opensMap h.toLRSHom.toShHom).obj U))).hom
      ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
        ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((modulePushforward h.toLRSHom.toShHom).obj G, H))).val.app (op U)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection S.toRingedSpace
          ((modulePushforward h.toLRSHom.toShHom).obj G) H (op U)
          (a ⊗ₜ[S.toRingedSpace.presheaf.obj (op U)] b))) = _
  rw [hc]
  exact (hm _ _).trans
    (congrArg (fun z => Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
      T.toRingedSpace G
      ((modulePullback h.toLRSHom.toShHom).obj H)
      (op ((opensMap h.toLRSHom.toShHom).obj U))
      (z ⊗ₜ[T.toRingedSpace.presheaf.obj (op ((opensMap h.toLRSHom.toShHom).obj U))]
        (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app H).val.app
          (op U)).hom b)) htri)

/-- **The projection-formula map on global sections.**  This is
`projectionFormulaMap_app_toTensorSheafSection` over the whole of `S`, where the preimage open
is the whole of `T`.  It is the form the
affine criterion `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`
consumes. -/
theorem projectionFormulaMap_app_top
    (a : ((modulePushforward h.toLRSHom.toShHom).obj G).val.obj (op ⊤))
    (b : H.val.obj (op ⊤)) :
    ((projectionFormulaMap h G H).val.app (op ⊤)).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection S.toRingedSpace
          ((modulePushforward h.toLRSHom.toShHom).obj G) H (op ⊤)
          (a ⊗ₜ[S.toRingedSpace.presheaf.obj (op ⊤)] b))
      = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection T.toRingedSpace G
          ((modulePullback h.toLRSHom.toShHom).obj H) (op ⊤)
          (a ⊗ₜ[T.toRingedSpace.presheaf.obj (op ⊤)]
            (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app H).val.app
              (op ⊤)).hom b) :=
  projectionFormulaMap_app_toTensorSheafSection h G H ⊤ a b

/-- **The formula of `projectionFormulaMap_app_toTensorSheafSection` determines the
projection-formula map.**  A morphism with the same effect on the images of pure tensors of
sections is the projection-formula map, by
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf_hom_ext`.

This is what turns a diagram chase ending in the projection-formula map into a computation on
sections. -/
theorem projectionFormulaMap_unique
    (θ : ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj
          ((modulePushforward h.toLRSHom.toShHom).obj G)).obj H ⟶
      (modulePushforward h.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj G).obj
          ((modulePullback h.toLRSHom.toShHom).obj H)))
    (hθ : ∀ (U : Opens S.carrier)
      (a : ((modulePushforward h.toLRSHom.toShHom).obj G).val.obj (op U))
      (b : H.val.obj (op U)),
      (θ.val.app (op U)).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection S.toRingedSpace
            ((modulePushforward h.toLRSHom.toShHom).obj G) H (op U)
            (a ⊗ₜ[S.toRingedSpace.presheaf.obj (op U)] b))
        = Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection T.toRingedSpace G
            ((modulePullback h.toLRSHom.toShHom).obj H)
            (op ((opensMap h.toLRSHom.toShHom).obj U))
            (a ⊗ₜ[T.toRingedSpace.presheaf.obj (op ((opensMap h.toLRSHom.toShHom).obj U))]
              (((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app H).val.app
                (op U)).hom b)) :
    θ = projectionFormulaMap h G H :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf_hom_ext fun U a b =>
    (hθ U.unop a b).trans
      (projectionFormulaMap_app_toTensorSheafSection h G H U.unop a b).symm

end Stacks.ProjectionFormula

end
