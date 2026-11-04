module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# Sections of tensor products and their restriction to an open

This file collects the calculations with sections of tensor products of sheaves of modules
used for the sections on the nonvanishing open of a section of an invertible sheaf, and the
comparison of tensor products with restriction to an open subspace of a ringed space.

## Implementation notes

Restricting a tensor product to an open subspace compares sheafification on the ambient
space with sheafification on the site over that open. The comparison is carried out on the
presheaf tensor products, where `Stacks.SheafOfModules.presheafTensorOverIso` identifies the
two parallel constructions of the sectionwise tensor product componentwise, and transported
across the sheafification adjunction by
`Stacks.SheafOfModules.tensorRestrictionIso`, whose being an isomorphism is checked by local
bijectivity of the sheafification unit.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] _root_.SheafOfModules.forget PresheafOfModules.restrictScalars
  TopCat.Presheaf.IsSheaf TopCat.Sheaf AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance_reducible] TensorSheafification.structureSheaf

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace DirectSum
open scoped _root_.Stacks.SheafOfModules.TensorProduct

universe u

section TensorCalculation

open CategoryTheory MonoidalCategory Opposite
open scoped _root_.Stacks.SheafOfModules.TensorProduct
universe v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

variable (M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))

/-- The section of a tensor product determined by a pair of sections is natural in the open:
restricting it is the section determined by the two restrictions. -/
theorem tensorSections_naturalAt {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : M.val.obj U) (n : N.val.obj U) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
      (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (N))).val.map f).hom (tensorSectionsAt O hO
      U M N m n) =
      tensorSectionsAt O hO V M N ((M.val.map f).hom m) ((N.val.map f).hom n) := by
  have h := (TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).naturality f
  have hh := congrArg (fun k => k.hom (m ⊗ₜ[O.obj U] n)) h
  change ((TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).app V).hom
    ((M.val.map f).hom m ⊗ₜ[O.obj V] (N.val.map f).hom n) = _ at hh
  exact hh.symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- An isomorphism of sheaves of modules is bijective on sections, in one direction. -/
theorem sheafIso_hom_inv_apply (e : M ≅ N) (U : Cᵒᵖ) (n : N.val.obj U) :
    (e.hom.val.app U).hom ((e.inv.val.app U).hom n) = n :=
  congrArg (fun k : N ⟶ N => (k.val.app U).hom n) e.inv_hom_id

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- An isomorphism of sheaves of modules is bijective on sections, in the other direction. -/
theorem sheafIso_inv_hom_apply (e : M ≅ N) (U : Cᵒᵖ) (m : M.val.obj U) :
    (e.inv.val.app U).hom ((e.hom.val.app U).hom m) = m :=
  congrArg (fun k : M ⟶ M => (k.val.app U).hom m) e.hom_inv_id

/-- The inverse of the left unitor sends a section to its tensor with the unit section `1`. -/
theorem tensorSections_leftUnitorInvAt (U : Cᵒᵖ) (m : M.val.obj U) :
    ((Invertible.tensorProductLeftUnitor O hO M).inv.val.app U).hom m =
      tensorSectionsAt O hO U (SheafOfModules.unit _) M (1 : O.obj U) m :=
  (congrArg _ (tensorSections_leftUnitorAt O hO U M m)).symm.trans
    (sheafIso_inv_hom_apply O hO _ _ (Invertible.tensorProductLeftUnitor O hO M) U _)

/-- The inverse of the right unitor sends a section to its tensor with the unit section `1`. -/
theorem tensorSections_rightUnitorInvAt (U : Cᵒᵖ) (m : M.val.obj U) :
    ((Invertible.tensorProductRightUnitor O hO M).inv.val.app U).hom m =
      tensorSectionsAt O hO U M (SheafOfModules.unit _) m (1 : O.obj U) :=
  (congrArg _ (tensorSections_rightUnitorAt O hO U M m)).symm.trans
    (sheafIso_inv_hom_apply O hO _ _ (Invertible.tensorProductRightUnitor O hO M) U _)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The additive equivalence on sections induced by an isomorphism of sheaves of modules. -/
noncomputable def sheafIsoAddEquiv (e : M ≅ N) (U : Cᵒᵖ) :
    M.val.obj U ≃+ N.val.obj U where
  toFun := (e.hom.val.app U).hom
  invFun := (e.inv.val.app U).hom
  left_inv := sheafIso_inv_hom_apply O hO M N e U
  right_inv := sheafIso_hom_inv_apply O hO M N e U
  map_add' := (e.hom.val.app U).hom.map_add

/-- Multiplying a twisted section by a section of a tensor power, written on pure tensors:
the coherence isomorphisms move the tensor power past the twist. -/
theorem tensorPowerAction_pure
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ) (U : Cᵒᵖ)
    (a : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj U)
    (b : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj U) (t : M.val.obj U) :
    ((Invertible.tensorProductBraiding O hO _ _ ≪≫
      Invertible.tensorProductAssociator O hO M _ _ ≪≫
      Invertible.tensorProductIso O hO (Iso.refl M)
        (TensorPower.coherentMulIso O hO L (m : ℤ) (n : ℤ)) ≪≫
      Invertible.tensorProductIso O hO (Iso.refl M)
        (TensorPower.tensorPowerReindex O hO L (Int.add_comm (m : ℤ) (n : ℤ))) ≪≫
      Invertible.tensorProductIso O hO (Iso.refl M)
        (TensorPower.tensorPowerReindex O hO L (Int.natCast_add n m).symm)).hom.val.app U).hom
      (tensorSectionsAt O hO U _ _ a (tensorSectionsAt O hO U _ _ t b)) =
    tensorSectionsAt O hO U M _ t
      (((TensorPower.coherentMulIso O hO L (n : ℤ) (m : ℤ) ≪≫
        TensorPower.tensorPowerReindex O hO L (Int.natCast_add n m).symm).hom.val.app U).hom
          (tensorSectionsAt O hO U _ _ a b)) := by
  simp only [Iso.trans_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  have hβ : ((Invertible.tensorProductBraiding O hO _ _).hom.val.app U).hom
      (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (n : ℤ)) _ a
        (tensorSectionsAt O hO U M (TensorPower.tensorPower O hO L (m : ℤ)) t b)) =
      tensorSectionsAt O hO U _ (TensorPower.tensorPower O hO L (n : ℤ))
        (tensorSectionsAt O hO U M (TensorPower.tensorPower O hO L (m : ℤ)) t b) a :=
    tensorSections_braidingAt O hO U _ _ _ _
  have hα : ((Invertible.tensorProductAssociator O hO M (TensorPower.tensorPower O hO L (m : ℤ))
        (TensorPower.tensorPower O hO L (n : ℤ))).hom.val.app U).hom
      (tensorSectionsAt O hO U _ (TensorPower.tensorPower O hO L (n : ℤ))
        (tensorSectionsAt O hO U M (TensorPower.tensorPower O hO L (m : ℤ)) t b) a) =
      tensorSectionsAt O hO U M _ t
        (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
          (TensorPower.tensorPower O hO L (n : ℤ)) b a) :=
    tensorSections_associatorAt O hO U _ _ _ _ _ _
  have hμ : ((Invertible.tensorProductIso O hO (Iso.refl M)
        (TensorPower.coherentMulIso O hO L (m : ℤ) (n : ℤ))).hom.val.app U).hom
      (tensorSectionsAt O hO U M _ t
        (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
          (TensorPower.tensorPower O hO L (n : ℤ)) b a)) =
      tensorSectionsAt O hO U M _ t
        (((TensorPower.coherentMulIso O hO L (m : ℤ) (n : ℤ)).hom.val.app U).hom
          (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
            (TensorPower.tensorPower O hO L (n : ℤ)) b a)) :=
    tensorSections_tensorProductIsoAt O hO U _ _ _ _ _ _ _ _
  have hρ₁ : ((Invertible.tensorProductIso O hO (Iso.refl M)
        (TensorPower.tensorPowerReindex O hO L (Int.add_comm (m : ℤ) (n : ℤ)))).hom.val.app U).hom
      (tensorSectionsAt O hO U M _ t
        (((TensorPower.coherentMulIso O hO L (m : ℤ) (n : ℤ)).hom.val.app U).hom
          (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
            (TensorPower.tensorPower O hO L (n : ℤ)) b a))) =
      tensorSectionsAt O hO U M _ t
        (((TensorPower.tensorPowerReindex O hO L (Int.add_comm (m : ℤ) (n : ℤ))).hom.val.app U).hom
          (((TensorPower.coherentMulIso O hO L (m : ℤ) (n : ℤ)).hom.val.app U).hom
            (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
              (TensorPower.tensorPower O hO L (n : ℤ)) b a))) :=
    tensorSections_tensorProductIsoAt O hO U _ _ _ _ _ _ _ _
  have hρ₂ : ((Invertible.tensorProductIso O hO (Iso.refl M)
        (TensorPower.tensorPowerReindex O hO L (Int.natCast_add n m).symm)).hom.val.app U).hom
      (tensorSectionsAt O hO U M _ t
        (((TensorPower.tensorPowerReindex O hO L (Int.add_comm (m : ℤ) (n : ℤ))).hom.val.app U).hom
          (((TensorPower.coherentMulIso O hO L (m : ℤ) (n : ℤ)).hom.val.app U).hom
            (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
              (TensorPower.tensorPower O hO L (n : ℤ)) b a)))) =
      tensorSectionsAt O hO U M _ t
        (((TensorPower.tensorPowerReindex O hO L (Int.natCast_add n m).symm).hom.val.app U).hom
          (((TensorPower.tensorPowerReindex O hO L (Int.add_comm (m : ℤ) (n : ℤ))).hom.val.app
            U).hom
            (((TensorPower.coherentMulIso O hO L (m : ℤ) (n : ℤ)).hom.val.app U).hom
              (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
                (TensorPower.tensorPower O hO L (n : ℤ)) b a)))) :=
    tensorSections_tensorProductIsoAt O hO U _ _ _ _ _ _ _ _
  have hβ' : ((Invertible.tensorProductBraiding O hO (TensorPower.tensorPower O hO L (n : ℤ))
        (TensorPower.tensorPower O hO L (m : ℤ))).hom.val.app U).hom
      (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (n : ℤ))
        (TensorPower.tensorPower O hO L (m : ℤ)) a b) =
      tensorSectionsAt O hO U (TensorPower.tensorPower O hO L (m : ℤ))
        (TensorPower.tensorPower O hO L (n : ℤ)) b a :=
    tensorSections_braidingAt O hO U _ _ _ _
  rw [hβ, hα, hμ, hρ₁, hρ₂, TensorPower.coherentMulIso_comm O hO L (n : ℤ) (m : ℤ), ← hβ']
  rfl

end TensorCalculation

section AcceptedStatementInstances

-- An imported instance gives a second route to terminal objects; disabling it keeps the
-- terminal object in which the statements below are phrased.
attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

variable (X : Scheme.{u})
  (L F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- The structure presheaf of rings of `X`. -/
public abbrev sectionSiteRing := X.toRingedSpace.presheaf
/-- The structure presheaf of rings of `X` is a sheaf. -/
public abbrev sectionSiteSheaf :=
  (structureSheafRing X.toRingedSpace).property

/-! The tensor product is defined by sheafifying the sectionwise tensor product.
Restriction to an open therefore requires a comparison between sheafification on
the ambient space and on the open subspace. -/

/-- Restriction to the slice site over `U` commutes with the canonical objectwise tensor
product. Every component of the comparison is the identity on the tensor product of sections. -/
noncomputable def presheafTensorOverIso
    (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) :
    (PresheafOfModules.pushforward (F := Over.forget U)
        (𝟙 ((structureSheafRing X).over U).obj)).obj
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))) ≅
      (PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((F.over U).val) ((G.over U).val)) :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

/-- The unit of sheafification on the ambient space, read on the site over `U`. -/
noncomputable def tensorRestrictionPushforward
    (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) :
    (PresheafOfModules.pushforward
        (𝟙 ((structureSheafRing X).over U).obj)).obj
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))) ⟶
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        (G))).over U).val :=
  (PresheafOfModules.pushforward _).map
    (TensorStalkRingedSpace.sheafifyUnit X ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val)
      (G.val))))

/-- The canonical map from the presheaf tensor product on the site over `U` into the restriction
of the tensor product sheaf: the unit of sheafification on the ambient space, read over `U`. -/
noncomputable def tensorRestrictionMap
    (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) :
    (PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((F.over U).val) ((G.over U).val)) ⟶
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        (G))).over U).val :=
  (presheafTensorOverIso X F G U).inv ≫ tensorRestrictionPushforward X F G U

/-- Over `U`, the unit of sheafification on the ambient space is locally injective: it is the
restriction of a sheafification unit along `Over.forget U`. -/
theorem isLocallyInjective_tensorRestrictionPushforward
    (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) :
    Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X.carrier).over U)
      ((PresheafOfModules.toPresheaf
        (TensorSheafification.structureSheaf (X.sheaf.over U).obj
          ((Presheaf.isSheaf_iff_isSheaf_comp
            ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
            (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)).obj).map
        (tensorRestrictionPushforward X F G U)) := by
  show Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X.carrier).over U)
    (Functor.whiskerLeft (CategoryTheory.Over.forget U).op
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
        (TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))))
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
        (TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))) := by
    show Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier)
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))).presheaf)
    infer_instance
  exact Presheaf.isLocallyInjective_whisker ((Opens.grothendieckTopology X.carrier).over U)
    (Opens.grothendieckTopology X.carrier) (CategoryTheory.Over.forget U) _

/-- Over `U`, the unit of sheafification on the ambient space is locally surjective. -/
theorem isLocallySurjective_tensorRestrictionPushforward
    (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) :
    Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U)
      ((PresheafOfModules.toPresheaf
        (TensorSheafification.structureSheaf (X.sheaf.over U).obj
          ((Presheaf.isSheaf_iff_isSheaf_comp
            ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
            (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)).obj).map
        (tensorRestrictionPushforward X F G U)) := by
  show Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U)
    (Functor.whiskerLeft (CategoryTheory.Over.forget U).op
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
        (TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))))
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
        (TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))) := by
    show Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier)
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))).presheaf)
    infer_instance
  exact Presheaf.isLocallySurjective_whisker ((Opens.grothendieckTopology X.carrier).over U)
    (Opens.grothendieckTopology X.carrier) (CategoryTheory.Over.forget U) _

noncomputable def tensorRestrictionIso
    (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
      (G))).over U ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X.sheaf.over U).obj,
        Presheaf.isSheaf_of_isSheaf_comp _ ((X.sheaf.over U).obj) (forget₂ CommRingCat RingCat)
        (((Presheaf.isSheaf_iff_isSheaf_comp
          ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
          (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property))⟩).obj ((F.over U))).obj
            ((G.over U))) := by
  let J := Opens.grothendieckTopology X.carrier
  let JU := J.over U
  let O := (X.sheaf.over U).obj
  let hO := (Presheaf.isSheaf_iff_isSheaf_comp JU O
    (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property
  let P : PresheafOfModules (TensorSheafification.structureRingPresheaf O) :=
    (PresheafOfModules.tensorObj (O := O) ((F.over U).val) ((G.over U).val))
  let M := ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
    (F)).obj (G))).over U
  let γ := tensorRestrictionMap X F G U
  let L := TensorSheafification.sheafify O hO
  let η := TensorSheafification.toSheafify O hO P
  let adj := TensorSheafification.sheafifyAdjunction O hO
  let e : L.obj P ⟶ M := (adj.homEquiv P M).symm γ
  let forgetMap := (SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
    PresheafOfModules.restrictScalars (𝟙 (TensorSheafification.structureSheaf O hO).obj))
  have hecomp : η ≫ forgetMap.map e = γ :=
    (adj.homEquiv_unit (f := e)).symm.trans ((adj.homEquiv P M).apply_symm_apply γ)
  let _νI : Presheaf.IsLocallyInjective JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
        (tensorRestrictionPushforward X F G U)) :=
    isLocallyInjective_tensorRestrictionPushforward X F G U
  let _νS : Presheaf.IsLocallySurjective JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
        (tensorRestrictionPushforward X F G U)) :=
    isLocallySurjective_tensorRestrictionPushforward X F G U
  have hγI : Presheaf.IsLocallyInjective JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map γ) := by
    change Presheaf.IsLocallyInjective JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
          (presheafTensorOverIso X F G U).inv ≫
        (PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
          (tensorRestrictionPushforward X F G U))
    let _iI : Presheaf.IsLocallyInjective JU
        ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
          (presheafTensorOverIso X F G U).inv) :=
      Presheaf.isLocallyInjective_of_injective JU _ (fun _ _ _ h => h)
    exact Presheaf.isLocallyInjective_comp JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
        (presheafTensorOverIso X F G U).inv)
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
        (tensorRestrictionPushforward X F G U))
  have hγS : Presheaf.IsLocallySurjective JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map γ) := by
    change Presheaf.IsLocallySurjective JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
          (presheafTensorOverIso X F G U).inv ≫
        (PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
          (tensorRestrictionPushforward X F G U))
    let _iS : Presheaf.IsLocallySurjective JU
        ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
          (presheafTensorOverIso X F G U).inv) :=
      Presheaf.isLocallySurjective_of_surjective JU _ (fun _ y => ⟨y, rfl⟩)
    exact Presheaf.isLocallySurjective_comp JU
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
        (presheafTensorOverIso X F G U).inv)
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj).map
        (tensorRestrictionPushforward X F G U))
  let toAbU := PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf O hO).obj
  let ηAb := toAbU.map η
  let γAb := toAbU.map γ
  let eAb := toAbU.map e.val
  have hηW : JU.W ηAb := by
    change JU.W (CategoryTheory.toSheafify JU P.presheaf)
    exact JU.W_toSheafify P.presheaf
  have hγW : JU.W γAb :=
    (JU.W_iff_isLocallyBijective γAb).2 ⟨hγI, hγS⟩
  have hηIso : IsIso ((presheafToSheaf JU AddCommGrpCat).map ηAb) :=
    (JU.W_iff ηAb).mp hηW
  have hγIso : IsIso ((presheafToSheaf JU AddCommGrpCat).map γAb) :=
    (JU.W_iff γAb).mp hγW
  have heMapIso : IsIso ((presheafToSheaf JU AddCommGrpCat).map eAb) := by
    let _hη := hηIso
    let _hγ := hγIso
    have hcompAb : ηAb ≫ eAb = γAb := by
      change toAbU.map (η ≫ e.val) = toAbU.map γ
      convert congrArg (fun k => toAbU.map k) hecomp using 1 <;> rfl
    have hcomp : (presheafToSheaf JU AddCommGrpCat).map ηAb ≫
        (presheafToSheaf JU AddCommGrpCat).map eAb =
        (presheafToSheaf JU AddCommGrpCat).map γAb :=
      ((presheafToSheaf JU AddCommGrpCat).map_comp ηAb eAb).symm.trans
        (congrArg (presheafToSheaf JU AddCommGrpCat).map hcompAb)
    have : IsIso ((presheafToSheaf JU AddCommGrpCat).map ηAb ≫
        (presheafToSheaf JU AddCommGrpCat).map eAb) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((presheafToSheaf JU AddCommGrpCat).map ηAb)
      ((presheafToSheaf JU AddCommGrpCat).map eAb)
  have heW : JU.W eAb := (JU.W_iff eAb).2 heMapIso
  have heSheafIso : IsIso ((SheafOfModules.toSheaf
      (TensorSheafification.structureSheaf O hO)).map e) := by
    apply (JU.W_sheafToPresheaf_map_iff_isIso _).1
    exact heW
  have heIso : IsIso e :=
    (isIso_iff_of_reflects_iso e
      (SheafOfModules.toSheaf (TensorSheafification.structureSheaf O hO))).mp heSheafIso
  exact (asIso e).symm

noncomputable def tensorRestrictionIsoOnScheme
    (A B : SheafOfModules.{u} (TensorSheafification.structureSheaf
      (sectionSiteRing X) (sectionSiteSheaf X))) (U : Opens X.toRingedSpace) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (A)).obj (B))).over U ≅
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X.toRingedSpace.sheaf.over U).obj,
      Presheaf.isSheaf_of_isSheaf_comp _ ((X.toRingedSpace.sheaf.over U).obj) (forget₂ CommRingCat
      RingCat) (((Presheaf.isSheaf_iff_isSheaf_comp
        ((Opens.grothendieckTopology X.toRingedSpace.carrier).over U)
        (X.toRingedSpace.sheaf.over U).obj (forget₂ CommRingCat RingCat)).mp
        (X.toRingedSpace.sheaf.over U).property))⟩).obj ((A.over U))).obj ((B.over U))) := by
  exact tensorRestrictionIso X.toRingedSpace A B U

theorem tensorRestrictionIso_inv_tensorAt
    (A B : SheafOfModules.{u} (TensorSheafification.structureSheaf
      (sectionSiteRing X) (sectionSiteSheaf X))) (U : Opens X.toRingedSpace)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    ((tensorRestrictionIsoOnScheme X A B U).inv.val.app (op (Over.mk (𝟙 U)))).hom
      (tensorSectionsAt (X.toRingedSpace.sheaf.over U).obj
        ((Presheaf.isSheaf_iff_isSheaf_comp
          ((Opens.grothendieckTopology X.toRingedSpace.carrier).over U)
          (X.toRingedSpace.sheaf.over U).obj (forget₂ CommRingCat RingCat)).mp
          (X.toRingedSpace.sheaf.over U).property)
        (op (Over.mk (𝟙 U))) (A.over U) (B.over U) a b) =
      tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) A B a b := by
  let O := (X.toRingedSpace.sheaf.over U).obj
  let hO := (Presheaf.isSheaf_iff_isSheaf_comp
    ((Opens.grothendieckTopology X.toRingedSpace.carrier).over U)
    O (forget₂ CommRingCat RingCat)).mp (X.toRingedSpace.sheaf.over U).property
  let P := (PresheafOfModules.tensorObj (O := O) ((A.over U).val) ((B.over U).val))
  let M := ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
    ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B))).over U
  let γ := tensorRestrictionMap X.toRingedSpace A B U
  let adj := TensorSheafification.sheafifyAdjunction O hO
  let e := (adj.homEquiv P M).symm γ
  have he : TensorSheafification.toSheafify O hO P ≫ e.val = γ :=
    (adj.homEquiv_unit (f := e)).symm.trans ((adj.homEquiv P M).apply_symm_apply γ)
  exact congrArg (fun k => (k.app (op (Over.mk (𝟙 U)))).hom
    (a ⊗ₜ[O.obj (op (Over.mk (𝟙 U)))] b)) he

end AcceptedStatementInstances

end Stacks.SheafOfModules

end
