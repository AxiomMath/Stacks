module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unit of a derived adjunction with fully faithful exact left adjoint

Let `L ⊣ R` be an adjunction between abelian categories with enough injectives in which `L` is
exact and the unit `𝟭 ⟶ R ∘ L` is an isomorphism. The adjunction descends to the bounded below
derived categories, `RL ⊣ RR` (`CategoryTheory.Adjunction.rightDerivedFunctorPlus`), and its unit
at `K ∈ D⁺` is the canonical map `K ⟶ RR(L K)`. This file shows that this unit is an isomorphism
as soon as `L` carries injective objects to objects which are right acyclic for `R`; in that case
`L` carries *every* object to an object right acyclic for `R`.

The argument is the one of [Stacks, Tag 099V]: represent `K` by a bounded below complex `I` of
injective objects; then `L I` is a bounded below complex of `R`-acyclic objects, so it computes
`RR` (Leray's acyclicity lemma, [Stacks, Tag 015E]), and `R(L I) = I`.

A unit which is an isomorphism makes `RL` fully faithful, and an exact functor which is fully
faithful on `D⁺` is bijective on `Ext` groups, these being morphisms in the derived category
between bounded below objects.

## Main results

* `CategoryTheory.Adjunction.isIso_mapHomotopyCategoryPlus_unit`: the degreewise unit on
  bounded below homotopy categories is invertible when the unit is.
* `CategoryTheory.Adjunction.rightDerivedFunctorPlus_unit_app_Qh_obj_fac`: the derived unit at
  the image of a complex `X` is the degreewise unit followed by the unit of `RR` at `L X`.
* `CategoryTheory.Adjunction.isIso_rightDerivedFunctorPlus_unit`: the derived unit is an
  isomorphism.
* `CategoryTheory.Adjunction.rightAcyclic_obj_of_isIso_unit`: every `L A` is right acyclic for
  `R`.
* `CategoryTheory.Functor.mapExt_bijective_of_mapDerivedCategoryPlus`: an exact functor which is
  fully faithful on bounded below derived categories induces bijections on `Ext` groups.

## References

* [Stacks Project, Tag 099V](https://stacks.math.columbia.edu/tag/099V)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] (adj : L ⊣ R)

/-- The degreewise unit of `adj` on bounded below homotopy categories is an isomorphism when the
unit of `adj` is. -/
instance isIso_mapHomotopyCategoryPlus_unit [IsIso adj.unit] :
    IsIso adj.mapHomotopyCategoryPlus.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have : IsIso ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app
      ((HomotopyCategory.Plus.ι A).obj K).as) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (asIso adj.unit)
      (ComplexShape.up ℤ)).hom.app _))
  have : IsIso ((HomotopyCategory.Plus.ι A).map (adj.mapHomotopyCategoryPlus.unit.app K)) := by
    have h : (HomotopyCategory.Plus.ι A).map (adj.mapHomotopyCategoryPlus.unit.app K) = _ :=
      (adj.mapHomotopyCategory (ComplexShape.up ℤ)).map_restrictFullyFaithful_unit_app
        (L := L.mapHomotopyCategoryPlus) (R := R.mapHomotopyCategoryPlus)
        (HomotopyCategory.Plus.fullyFaithfulι A) (HomotopyCategory.Plus.fullyFaithfulι B)
        (Iso.refl _) (Iso.refl _) K
    rw [h, mapHomotopyCategory_unit_app]
    have h₁ := Functor.map_isIso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.ι A).obj K).as)
    have h₂ := Functor.map_isIso (R.mapHomotopyCategory (ComplexShape.up ℤ))
      ((Iso.refl (HomotopyCategory.Plus.ι A ⋙ L.mapHomotopyCategory (ComplexShape.up ℤ))).app
        K).hom
    have h₃ := ((Iso.refl (HomotopyCategory.Plus.ι B ⋙ R.mapHomotopyCategory
      (ComplexShape.up ℤ))).app (L.mapHomotopyCategoryPlus.obj K)).isIso_hom
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₃)
  exact (HomotopyCategory.Plus.fullyFaithfulι A).isIso_of_isIso_map _

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [EnoughInjectives A] [EnoughInjectives B] [L.PreservesHomology]

/-- The functor `K⁺(B) ⥤ D⁺(A)` induced by `R` has a right derived functor with respect to
quasi-isomorphisms, namely `Functor.rightDerivedFunctorPlus` with unit
`Functor.rightDerivedFunctorPlusUnith`. -/
local instance : (R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso B) :=
  Functor.HasRightDerivedFunctor.mk' (RF := R.rightDerivedFunctorPlus)
    (α := R.rightDerivedFunctorPlusUnith)

/-- **The derived unit on the image of a complex.** For `X ∈ K⁺(A)`, the unit of the derived
adjunction `RL ⊣ RR` at the image of `X` in `D⁺(A)`, followed by `RR` of the comparison
`RL(X) ≅ L(X)`, is the image of the degreewise unit `X ⟶ R(L X)` followed by the canonical map
`R(L X) ⟶ RR(L X)`. -/
theorem rightDerivedFunctorPlus_unit_app_Qh_obj_fac (X : HomotopyCategory.Plus A) :
    letI := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Qh.obj X) ≫
        R.rightDerivedFunctorPlus.map ((asIso L.rightDerivedFunctorPlusUnith).inv.app X) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app X) ≫
        R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj X) := by
  let := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have : (L.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (asIso L.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso L.rightDerivedFunctorPlusUnith).symm _)
  exact adj.mapHomotopyCategoryPlus.derivedη_fac_app (HomotopyCategory.Plus.quasiIso A) _ _ X

/-- The derived unit at the image of a complex `X` is an isomorphism exactly when the canonical
map `R(L X) ⟶ RR(L X)` is, provided the unit of `adj` is an isomorphism. -/
theorem isIso_rightDerivedFunctorPlus_unit_app_Qh_obj_iff [IsIso adj.unit]
    (X : HomotopyCategory.Plus A) :
    IsIso (adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Qh.obj X)) ↔
      IsIso (R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj X)) := by
  let := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  rw [← isIso_comp_right_iff _
    (R.rightDerivedFunctorPlus.map ((asIso L.rightDerivedFunctorPlusUnith).inv.app X)),
    adj.rightDerivedFunctorPlus_unit_app_Qh_obj_fac X, isIso_comp_left_iff]

/-- **The derived unit is an isomorphism** ([Stacks, Tag 099V]). Let `L ⊣ R` be an adjunction
between abelian categories with enough injectives such that `L` is exact, the unit is an
isomorphism, and `L` carries injective objects to objects right acyclic for `R`. Then the unit
`K ⟶ RR(RL K)` of the derived adjunction on bounded below derived categories is an
isomorphism. -/
theorem isIso_rightDerivedFunctorPlus_unit [IsIso adj.unit]
    (h : ∀ I : A, Injective I → R.rightAcyclic (L.obj I)) :
    IsIso adj.rightDerivedFunctorPlus.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
  obtain ⟨M, -, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let X := (HomotopyCategory.Plus.quotient A).obj
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj M)
  let e' : DerivedCategory.Plus.Qh.obj X ≅ K :=
    (DerivedCategory.Plus.quotientCompQhIso A).app _ ≪≫ e
  refine (NatTrans.isIso_app_iff_of_iso _ e').1 ?_
  rw [isIso_rightDerivedFunctorPlus_unit_app_Qh_obj_iff]
  let I := ((InjectiveObject.ι A).mapCochainComplexPlus.obj M).obj
  have hLI : CochainComplex.plus B ((L.mapHomologicalComplex _).obj I) :=
    (L.mapCochainComplexPlus.obj ((InjectiveObject.ι A).mapCochainComplexPlus.obj M)).property
  exact R.isIso_totalRightDerivedUnit_app_of_rightAcyclic _ hLI
    (fun n ↦ h (I.X n) (inferInstanceAs (Injective ((InjectiveObject.ι A).obj (M.obj.X n)))))

/-- **Every object is carried to an `R`-acyclic object.** Under the hypotheses of
`CategoryTheory.Adjunction.isIso_rightDerivedFunctorPlus_unit`, `L A` is right acyclic for `R`
for every object `A`, not only for the injective ones. -/
theorem rightAcyclic_obj_of_isIso_unit [IsIso adj.unit]
    (h : ∀ I : A, Injective I → R.rightAcyclic (L.obj I)) (F : A) :
    R.rightAcyclic (L.obj F) := by
  have := adj.isIso_rightDerivedFunctorPlus_unit h
  have hX := (adj.isIso_rightDerivedFunctorPlus_unit_app_Qh_obj_iff
    ((HomotopyCategory.Plus.singleFunctor A 0).obj F)).1 inferInstance
  change IsIso (R.rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.singleFunctor B 0).obj (L.obj F)))
  exact (NatTrans.isIso_app_iff_of_iso _ ((L.mapSinglePlusIso).app F)).1 hX

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- If the action of an exact functor on bounded below derived categories is fully faithful,
then its action on unbounded derived categories is bijective on morphisms between bounded below
objects. -/
theorem mapDerivedCategory_map_bijective_of_plus [F.mapDerivedCategoryPlus.Full]
    [F.mapDerivedCategoryPlus.Faithful] {K L : DerivedCategory A}
    (hK : DerivedCategory.TStructure.t.plus K) (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (F.mapDerivedCategory.map : (K ⟶ L) → _) := by
  let K' : DerivedCategory.Plus A := ⟨K, hK⟩
  let L' : DerivedCategory.Plus A := ⟨L, hL⟩
  let hι := (DerivedCategory.TStructure.t (C := A)).plus.fullyFaithfulι
  have : (F.mapDerivedCategory.map : (K ⟶ L) → _) =
      (DerivedCategory.Plus.ι.map : (F.mapDerivedCategoryPlus.obj K' ⟶
          F.mapDerivedCategoryPlus.obj L') → _) ∘ F.mapDerivedCategoryPlus.map ∘
        (hι.homEquiv (X := K') (Y := L')).symm := by
    funext φ
    change _ = F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
      (hι.preimage (X := K') (Y := L') φ))
    rw [hι.map_preimage]
  rw [this]
  exact ((DerivedCategory.TStructure.t (C := B)).plus.fullyFaithfulι.map_bijective _ _).comp
    (((Functor.FullyFaithful.ofFullyFaithful F.mapDerivedCategoryPlus).map_bijective _ _).comp
      (hι.homEquiv (X := K') (Y := L')).symm.bijective)

/-- **An exact functor which is fully faithful on bounded below derived categories induces
bijections on `Ext`.** For objects `X` and `Y` of `A` and `n : ℕ`, the map
`Ext X Y n → Ext (F X) (F Y) n` induced by `F` is bijective. -/
@[sga "6 II 2.1.3" "special case"]
theorem mapExt_bijective_of_mapDerivedCategoryPlus [F.mapDerivedCategoryPlus.Full]
    [F.mapDerivedCategoryPlus.Faithful] [HasExt.{w} A] [HasExt.{w'} B] (X Y : A) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  let G := F.mapDerivedCategory
  let α := (F.mapDerivedCategorySingleFunctor 0).inv.app X
  let β := (F.mapDerivedCategorySingleFunctor 0).hom.app Y
  let g : ShiftedHom ((DerivedCategory.singleFunctor A 0).obj X)
      ((DerivedCategory.singleFunctor A 0).obj Y) (n : ℤ) →
      ShiftedHom ((DerivedCategory.singleFunctor B 0).obj (F.obj X))
        ((DerivedCategory.singleFunctor B 0).obj (F.obj Y)) (n : ℤ) :=
    fun φ ↦ α ≫ φ.map G ≫ β⟦(n : ℤ)⟧'
  have hX : DerivedCategory.TStructure.t.plus ((DerivedCategory.singleFunctor A 0).obj X) :=
    ⟨0, inferInstance⟩
  have hY : DerivedCategory.TStructure.t.plus
      (((DerivedCategory.singleFunctor A 0).obj Y)⟦(n : ℤ)⟧) :=
    DerivedCategory.TStructure.t.plus.le_shift (n : ℤ) _ ⟨0, inferInstance⟩
  have hmap : Function.Bijective (fun φ : ShiftedHom ((DerivedCategory.singleFunctor A 0).obj X)
      ((DerivedCategory.singleFunctor A 0).obj Y) (n : ℤ) ↦ φ.map G) := by
    have e : (fun φ : ShiftedHom ((DerivedCategory.singleFunctor A 0).obj X)
        ((DerivedCategory.singleFunctor A 0).obj Y) (n : ℤ) ↦ φ.map G) =
        (Iso.homCongr (Iso.refl _) ((G.commShiftIso (n : ℤ)).app _)) ∘ G.map := by
      funext φ
      simp [ShiftedHom.map]
    rw [e]
    exact ((Iso.homCongr (Iso.refl _) ((G.commShiftIso (n : ℤ)).app _)).bijective).comp
      (F.mapDerivedCategory_map_bijective_of_plus hX hY)
  have hg : Function.Bijective g :=
    ((Iso.homCongr (asIso α).symm ((shiftFunctor _ (n : ℤ)).mapIso (asIso β))).bijective).comp
      hmap
  have : (F.mapExtAddHom X Y n : Ext.{w} X Y n → Ext.{w'} (F.obj X) (F.obj Y) n) =
      Ext.homEquiv.symm ∘ g ∘ Ext.homEquiv := by
    funext e
    apply Ext.homEquiv.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact Ext.mapExactFunctor_hom F e
  rw [this]
  exact Ext.homEquiv.symm.bijective.comp (hg.comp Ext.homEquiv.bijective)

end CategoryTheory.Functor

end
