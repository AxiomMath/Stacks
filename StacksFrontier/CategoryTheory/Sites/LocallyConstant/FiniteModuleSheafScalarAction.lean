module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteRingModuleUnderlyingAbelian
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ModuleScalarAction

/-!
# Finite locally constant sheaves of modules as abelian sheaves with scalar operations

Let `(C, J)` be a site and let `Λ` be a **finite** ring. The finite locally constant sheaves of
`Λ`-modules on `C` are the finite locally constant sheaves of abelian groups equipped with
additive scalar operations, that is, the additive functors from `CategoryTheory.SingleObj Λ` to
the finite locally constant abelian sheaves.

This is the restriction of `CategoryTheory.moduleSheafScalarActionEquivalence` to the finite
locally constant objects on both sides; what makes the restriction possible is that finite local
constancy of a sheaf of `Λ`-modules is a property of its underlying abelian sheaf,
`Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheaf_iff_forget₂`.

## Main results

* `Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence` — the
  equivalence.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5), part (3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Stacks.ConstantSheaf

universe v u r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ] [Finite Λ]

/-- The finite locally constant sheaves of abelian groups form a preadditive category. -/
public instance preadditive_finiteLocallyConstantAbelianSheaf :
    Preadditive (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory :=
  Preadditive.fullSubcategory _

/-- The finite locally constant sheaves of `Λ`-modules form a preadditive category. -/
public instance preadditive_finiteLocallyConstantModuleSheaf :
    Preadditive
      (ObjectProperty.FullSubcategory (fun F : Sheaf J (ModuleCat.{max u v} Λ) ↦
        IsFiniteLocallyConstant J F)) :=
  Preadditive.fullSubcategory _


/-! ### Biproducts among the finite locally constant abelian sheaves -/

section Biproducts

variable [HasPullbacks C]

/-- Finite local constancy of an abelian sheaf is invariant under isomorphism. -/
public instance isClosedUnderIsomorphisms_isFiniteLocallyConstantAbelianSheaf :
    ObjectProperty.IsClosedUnderIsomorphisms
      (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J) where
  of_iso {F F'} e hF := by
    refine ⟨fun U ↦ ?_⟩
    obtain ⟨I, V, f, hcov, h⟩ := hF.exists_finite_cover U
    refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨φ⟩⟩ := h i
    exact ⟨E, hE, ⟨φ ≪≫ (J.overPullback AddCommGrpCat.{max u v} (V i)).mapIso e⟩⟩

/-- A binary product of finite abelian groups is finite. -/
public theorem finite_prod_addCommGrp (A B : AddCommGrpCat.{w})
    (hA : Finite (ToType A)) (hB : Finite (ToType B)) : Finite (ToType (A ⨯ B)) := by
  have := hA
  have := hB
  have e : A ⨯ B ≅ AddCommGrpCat.of (ToType A × ToType B) :=
    limit.isoLimitCone (AddCommGrpCat.binaryProductLimitCone A B)
  exact Finite.of_equiv _ ((forget AddCommGrpCat.{w}).mapIso e).symm.toEquiv

/-- **A binary product of finite locally constant abelian sheaves is finite locally constant.**
On a common refinement of the two trivializing coverings both factors are constant, with finite
values `A` and `B`; restriction to a slice and the constant sheaf functor both preserve binary
products, so the product is constant there with the finite value `A ⨯ B`. -/
public theorem isFiniteLocallyConstant_abelian_prod
    (F G : Sheaf J AddCommGrpCat.{max u v})
    (hF : IsFiniteLocallyConstant J F) (hG : IsFiniteLocallyConstant J G) :
    IsFiniteLocallyConstant J (F ⨯ G) := by
  refine ⟨fun U ↦ ?_⟩
  obtain ⟨I, V, f, hcov, hFV⟩ := hF.exists_finite_cover U
  refine exists_cover_trans J (P := fun W ↦ ∃ E : AddCommGrpCat.{max u v},
    Finite (ToType E) ∧ Nonempty ((constantSheaf (J.over W) AddCommGrpCat.{max u v}).obj E ≅
      (J.overPullback AddCommGrpCat.{max u v} W).obj (F ⨯ G))) hcov fun i ↦ ?_
  obtain ⟨A, hA, ⟨a⟩⟩ := hFV i
  obtain ⟨I', W, g, hcov', hGW⟩ := hG.exists_finite_cover (V i)
  refine ⟨I', W, g, hcov', fun j ↦ ?_⟩
  obtain ⟨B, hB, ⟨b⟩⟩ := hGW j
  have a' : (constantSheaf (J.over (W j)) AddCommGrpCat.{max u v}).obj A ≅
      (J.overPullback AddCommGrpCat.{max u v} (W j)).obj F :=
    Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap J AddCommGrpCat.{max u v}
      (g j) F A a
  refine ⟨A ⨯ B, finite_prod_addCommGrp.{max u v} A B hA hB, ⟨?_⟩⟩
  exact (PreservesLimitPair.iso
      (constantSheaf (J.over (W j)) AddCommGrpCat.{max u v}) A B) ≪≫
    prod.mapIso a' b ≪≫
    (PreservesLimitPair.iso
      (J.overPullback AddCommGrpCat.{max u v} (W j)) F G).symm

/-- The finite locally constant abelian sheaves are closed under binary products. -/
public instance isClosedUnderLimitsOfShape_pair_finiteLocallyConstantAbelianSheaf :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J) (Discrete WalkingPair) :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨D, hD⟩
    exact ObjectProperty.prop_of_iso (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J)
      (HasLimit.isoOfNatIso (diagramIsoPair D)).symm
      (isFiniteLocallyConstant_abelian_prod J _ _ (hD ⟨WalkingPair.left⟩)
        (hD ⟨WalkingPair.right⟩)))

/-- The finite locally constant abelian sheaves have binary products. -/
public instance hasBinaryProducts_finiteLocallyConstantAbelianSheaf :
    HasBinaryProducts (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory :=
  inferInstance

/-- The finite locally constant abelian sheaves have a zero object: the zero sheaf is finite
locally constant. -/
public instance hasZeroObject_finiteLocallyConstantAbelianSheaf :
    HasZeroObject (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory := by
  let := hasSheafify_addCommGrp.{v, u, u} J
  refine ⟨⟨⟨0, isFiniteLocallyConstant_zero J⟩, ?_⟩⟩
  rw [IsZero.iff_id_eq_zero]
  exact ObjectProperty.hom_ext _
    ((IsZero.iff_id_eq_zero (0 : Sheaf J AddCommGrpCat.{max u v})).mp (isZero_zero _))

end Biproducts

section Equivalence

variable [J.HasSheafCompose (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})]
  [ReflectsLimitsOfSize.{v, max v u}
    (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})]

/-- Scalar multiplication on a finite locally constant sheaf of `Λ`-modules, as a functor from
the one-object category on `Λ` to the finite locally constant abelian sheaves. -/
public def finiteModuleSheafScalarFunctor
    (M : ObjectProperty.FullSubcategory (fun F : Sheaf J (ModuleCat.{max u v} Λ) ↦
      IsFiniteLocallyConstant J F)) :
    SingleObj Λ ⥤ (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory :=
  ObjectProperty.lift _ (moduleSheafScalarFunctor J Λ M.obj)
    fun _ ↦ isFiniteLocallyConstant_forget₂Module J Λ M.obj M.property

/-- The scalar operations on a finite locally constant sheaf of `Λ`-modules are additive. -/
public instance finiteModuleSheafScalarFunctor_additive
    (M : ObjectProperty.FullSubcategory (fun F : Sheaf J (ModuleCat.{max u v} Λ) ↦
      IsFiniteLocallyConstant J F)) :
    (finiteModuleSheafScalarFunctor J Λ M).Additive where
  map_add := by
    rintro ⟨⟩ ⟨⟩ a b
    exact ObjectProperty.hom_ext _ (moduleSheafScalarFunctor J Λ M.obj).map_add

/-- A finite locally constant sheaf of `Λ`-modules, read as a finite locally constant abelian
sheaf with additive scalar operations. -/
public def finiteModuleSheafToScalarAction :
    ObjectProperty.FullSubcategory (fun F : Sheaf J (ModuleCat.{max u v} Λ) ↦
        IsFiniteLocallyConstant J F) ⥤
      (SingleObj Λ ⥤+ (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) where
  obj M := AdditiveFunctor.of (finiteModuleSheafScalarFunctor J Λ M)
  map f := ObjectProperty.homMk
    { app := fun _ ↦ ObjectProperty.homMk
        ((sheafCompose J
          (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})).map f.hom)
      naturality := fun _ _ a ↦ ObjectProperty.hom_ext _
        (((moduleSheafToScalarAction J Λ).map f.hom).hom.naturality a) }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The abelian sheaf with additive scalar operations attached to an additive functor into the
finite locally constant abelian sheaves. -/
public def scalarActionToFiniteModuleSheafObj
    (F : SingleObj Λ ⥤+ (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) :
    ObjectProperty.FullSubcategory (fun G : Sheaf J (ModuleCat.{max u v} Λ) ↦
      IsFiniteLocallyConstant J G) := by
  letI : (F.obj ⋙ ObjectProperty.ι
      (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J)).Additive := by
    have := F.property
    infer_instance
  refine ⟨(scalarActionToModuleSheaf J Λ).obj
    (AdditiveFunctor.of (F.obj ⋙ ObjectProperty.ι _)), ?_⟩
  refine (isFiniteLocallyConstant_moduleSheaf_iff_forget₂ J Λ _).mpr ?_
  exact (F.obj.obj (SingleObj.star Λ)).property

/-- An additive functor into the finite locally constant abelian sheaves, read as a finite
locally constant sheaf of `Λ`-modules. -/
public def scalarActionToFiniteModuleSheaf :
    (SingleObj Λ ⥤+ (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) ⥤
      ObjectProperty.FullSubcategory (fun G : Sheaf J (ModuleCat.{max u v} Λ) ↦
        IsFiniteLocallyConstant J G) where
  obj := scalarActionToFiniteModuleSheafObj J Λ
  map {F H} f := ObjectProperty.homMk
    ((scalarActionToModuleSheaf J Λ).map (ObjectProperty.homMk
      (Functor.whiskerRight f.hom (ObjectProperty.ι _))))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- **A finite locally constant sheaf of `Λ`-modules over a finite ring is a finite locally
constant abelian sheaf with additive scalar operations.** -/
public def finiteLocallyConstantModuleSheafScalarActionEquivalence :
    ObjectProperty.FullSubcategory (fun F : Sheaf J (ModuleCat.{max u v} Λ) ↦
        IsFiniteLocallyConstant J F) ≌
      (SingleObj Λ ⥤+ (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) where
  functor := finiteModuleSheafToScalarAction J Λ
  inverse := scalarActionToFiniteModuleSheaf J Λ
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun ⟨⟩ ↦ Iso.refl _) (by rintro ⟨⟩ ⟨⟩ a; ext; rfl)))
    (by intros; rfl)

end Equivalence

end Stacks.ConstantSheaf

end
