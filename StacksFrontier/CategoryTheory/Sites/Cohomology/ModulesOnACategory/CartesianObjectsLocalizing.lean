module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Shift.AdjunctionMateCommShift
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedObjectSizeSmall
import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian objects form a localizing subcategory

Let `C` be a category, regarded as a site with the chaotic topology, let `O` be a presheaf of
rings on `C` and let `bc` be derived base-change data for `O` in the sense of
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData`. Stacks 0GYW says that the
full subcategory `QC(O)` of the derived category `D(O)` cut out by the cartesian condition
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.IsQC bc` is strictly full, saturated,
triangulated, and closed under arbitrary direct sums.

For each morphism `a : V ⟶ U` of `Cᵒᵖ` the comparison maps assemble into a natural
transformation `RΓ(V, -) ⋙ baseChange a ⟶ RΓ(U, -)`, and `IsQC bc` is the intersection over all
`a` of the loci where these transformations are invertible. The four assertions are properties
of such loci:

* strict fullness and stability under retracts hold for the invertibility locus of any natural
  transformation;
* triangulatedness holds once both functors are triangulated and the transformation commutes
  with the shift;
* closure under direct sums holds once both functors preserve the direct sums in question; here
  coproducts in `D(O)` and in `D(O(U))` exist at the module universe (Tag 079Q), and the
  localization functor of a Grothendieck abelian category preserves direct sums (Tag 07D9).

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms`: `QC(O)` is a
  strictly full subcategory.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isSaturated`: `QC(O)` is closed under
  direct summands.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isTriangulated`: `QC(O)` is a
  triangulated subcategory.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderColimitsOfShape`: `QC(O)`
  is closed under arbitrary direct sums.

## Implementation notes

The source states the four assertions for the canonical base-change data, derived extension of
scalars along the restriction maps of `O`. Here they are stated for arbitrary base-change data
`bc`; base-change data is determined up to canonical natural isomorphism by its adjunction, so
specializing `bc` recovers the assertions of the source.

## References

* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open ZeroObject
open Stacks.DerivedCategoryComparisons (isIso_app_of_retract
  isIso_app_isClosedUnderIsomorphisms isIso_app_isTriangulated
  localization_liftNatTrans_commShift)

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

attribute [local instance] HasDerivedCategory.standard

universe w u v r j q

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-! ### Generalities on the invertibility locus of a natural transformation -/

/-- In a `q`-locally small preadditive category with a zero object, a direct sum has a `q`-small
set of nonzero summands. -/
private lemma small_nonzero_support_of_isColimit
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [LocallySmall.{q} D] {J : Type j} (K : Discrete J ⥤ D)
    (s : Cocone K) (hs : IsColimit s) :
    Small.{q} {i : J // ¬ IsZero (K.obj ⟨i⟩)} := by
  classical
  let S := {i : J // ¬ IsZero (K.obj ⟨i⟩)}
  let f (T : Set S) : s.pt ⟶ s.pt :=
    hs.desc {
      pt := s.pt
      ι := Discrete.natTrans (fun i => if hi : ¬ IsZero (K.obj i) then
          if (⟨i.as, hi⟩ : S) ∈ T then s.ι.app i else 0 else 0
      )
    }
  have hf (T : Set S) (i : S) :
      s.ι.app ⟨i.1⟩ ≫ f T = if i ∈ T then s.ι.app ⟨i.1⟩ else 0 := by
    dsimp [f]
    rw [hs.fac]
    simp [i.2]
  have hι (i : S) : s.ι.app ⟨i.1⟩ ≠ 0 := by
    intro hz
    let t : Cocone K := {
      pt := K.obj ⟨i.1⟩
      ι := Discrete.natTrans (fun k => if hk : k.as = i.1 then
          eqToHom (congrArg K.obj (Discrete.ext hk)) else 0
      )
    }
    have hid : s.ι.app ⟨i.1⟩ ≫ hs.desc t = 𝟙 (K.obj ⟨i.1⟩) := by
      simp [t]
    rw [hz, zero_comp] at hid
    exact i.2 ((IsZero.iff_id_eq_zero _).2 hid.symm)
  have hinj : Function.Injective f := by
    intro T T' h
    ext i
    have heq : s.ι.app ⟨i.1⟩ ≫ f T = s.ι.app ⟨i.1⟩ ≫ f T' := by rw [h]
    rw [hf, hf] at heq
    by_cases hiT : i ∈ T <;> by_cases hiT' : i ∈ T' <;> simp_all [hι i, (hι i).symm]
  have : Small.{q} (Set S) := small_of_injective hinj
  exact small_of_injective (f := fun i : S => ({i} : Set S)) Set.singleton_injective

/-! ### Shift compatibility of the comparison map -/

variable (O) in
/-- The derived restriction map of `O` along `a`, as a natural transformation
`RΓ(V, -) ⟶ RΓ(U, -) ⋙ DRestrict a`. -/
private noncomputable abbrev restrictionMapNatTrans {U V : Cᵒᵖ} (a : V ⟶ U) :
    RGamma.{w} O V ⟶ RGamma.{w} O U ⋙ DRestrict.{w} O a :=
  restrictionD.{w} O a ≫ (RGammaRestrictIso.{w} O a).hom

variable (O) in
/-- The derived restriction transformation commutes with the shift. -/
private lemma restrictionD_commShift {U V : Cᵒᵖ} (a : V ⟶ U) :
    NatTrans.CommShift (restrictionD.{w} O a) ℤ := by
  let A := PresheafOfModules O
  let EvV := PresheafOfModules.evaluation.{max u v r w} O V
  let EvU := PresheafOfModules.evaluation.{max u v r w} O U ⋙
    ModuleCat.restrictScalars.{max u v r w} (O.map a).hom
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let α := (PresheafOfModules.restriction O a).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let : NatTrans.CommShift α ℤ := by
    dsimp [α]
    infer_instance
  let : NatTrans.CommShift
      (Functor.whiskerRight α (DerivedCategory.Q (C := ModuleCat (O.obj V)))) ℤ := by
    infer_instance
  let : NatTrans.CommShift
      (Localization.Lifting.iso (DerivedCategory.Q (C := A)) W
        (EvV.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q (C := ModuleCat (O.obj V))) EvV.mapDerivedCategory).hom ℤ := by
    show NatTrans.CommShift EvV.mapDerivedCategoryFactors.hom ℤ
    infer_instance
  let : NatTrans.CommShift
      (Localization.Lifting.iso (DerivedCategory.Q (C := A)) W
        (EvU.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q (C := ModuleCat (O.obj V))) EvU.mapDerivedCategory).hom ℤ := by
    show NatTrans.CommShift EvU.mapDerivedCategoryFactors.hom ℤ
    infer_instance
  unfold restrictionD
  apply localization_liftNatTrans_commShift

variable (O) in
/-- The isomorphism `RGammaRestrictIso` commutes with the shift. -/
private lemma RGammaRestrictIso_hom_commShift {U V : Cᵒᵖ} (a : V ⟶ U) :
    NatTrans.CommShift (RGammaRestrictIso.{w} O a).hom ℤ := by
  let A := PresheafOfModules O
  let Ev := PresheafOfModules.evaluation.{max u v r w} O U
  let EvU := PresheafOfModules.evaluation.{max u v r w} O U ⋙
    ModuleCat.restrictScalars.{max u v r w} (O.map a).hom
  let Res := ModuleCat.restrictScalars.{max u v r w} (O.map a).hom
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let F' := RGammaRestrict.{w} O a
  let G' := RGamma.{w} O U ⋙ DRestrict.{w} O a
  let : (DRestrict.{w} (O := O) (U := U) (V := V) a).CommShift ℤ := by
    dsimp [DRestrict]
    infer_instance
  let : NatTrans.CommShift Ev.mapDerivedCategoryFactors.hom ℤ := by infer_instance
  let : NatTrans.CommShift Res.mapDerivedCategoryFactors.hom ℤ := by infer_instance
  let : NatTrans.CommShift
      (Functor.whiskerRight Ev.mapDerivedCategoryFactors.hom
        (DRestrict.{w} (O := O) (U := U) (V := V) a)) ℤ := by
    infer_instance
  let : NatTrans.CommShift
      (Functor.associator (DerivedCategory.Q (C := A)) Ev.mapDerivedCategory
        (DRestrict.{w} (O := O) (U := U) (V := V) a)).hom ℤ := by
    infer_instance
  let : NatTrans.CommShift
      (Functor.whiskerLeft (Ev.mapHomologicalComplex (ComplexShape.up ℤ))
        Res.mapDerivedCategoryFactors.hom) ℤ := by
    infer_instance
  let : NatTrans.CommShift
      (Functor.associator (Ev.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.Q (C := ModuleCat (O.obj U)))
        (DRestrict.{w} (O := O) (U := U) (V := V) a)).hom ℤ := by
    infer_instance
  let : NatTrans.CommShift
      (Functor.associator (Ev.mapHomologicalComplex (ComplexShape.up ℤ))
        (Res.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.Q (C := ModuleCat (O.obj V)))).hom ℤ := by
    infer_instance
  let : F'.CommShift ℤ := by
    dsimp [F']
    infer_instance
  let : G'.CommShift ℤ := by
    dsimp [G']
    infer_instance
  let : NatTrans.CommShift
      (Localization.Lifting.iso (DerivedCategory.Q (C := A)) W
        (EvU.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q (C := ModuleCat (O.obj V))) EvU.mapDerivedCategory).hom ℤ := by
    show NatTrans.CommShift EvU.mapDerivedCategoryFactors.hom ℤ
    infer_instance
  let : NatTrans.CommShift
      (Localization.Lifting.iso (DerivedCategory.Q (C := A)) W
        (EvU.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q (C := ModuleCat (O.obj V))) G').hom ℤ := by
    show NatTrans.CommShift
      (((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight Ev.mapDerivedCategoryFactors
          (DRestrict.{w} (O := O) (U := U) (V := V) a) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (Ev.mapHomologicalComplex (ComplexShape.up ℤ))
          (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategoryFactors ≪≫
        (Functor.associator _ _ _).symm).hom) ℤ
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom]
    infer_instance
  show NatTrans.CommShift
    (Localization.liftNatTrans (DerivedCategory.Q (C := A)) W
      (EvU.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat (O.obj V)))
      (EvU.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat (O.obj V)))
      F' G' (𝟙 _)) ℤ
  apply localization_liftNatTrans_commShift

variable (O) in
/-- The derived restriction map of `O` commutes with the shift. -/
private lemma restrictionMapNatTrans_commShift {U V : Cᵒᵖ} (a : V ⟶ U) :
    NatTrans.CommShift (restrictionMapNatTrans.{w} O a) ℤ := by
  let : NatTrans.CommShift (restrictionD.{w} O a) ℤ := restrictionD_commShift.{w} O a
  let : NatTrans.CommShift (RGammaRestrictIso.{w} O a).hom ℤ :=
    RGammaRestrictIso_hom_commShift.{w} O a
  exact NatTrans.CommShift.comp (A := ℤ) (restrictionD.{w} O a) (RGammaRestrictIso.{w} O a).hom

/-- Derived restriction of scalars commutes with the shift. -/
private noncomputable abbrev derivedRestrictionCommShift {U V : Cᵒᵖ} (a : V ⟶ U) :
    (DRestrict.{w} O a).CommShift ℤ := by
  dsimp [DRestrict]
  infer_instance

/-- Derived base change commutes with the shift. -/
private noncomputable abbrev derivedBaseChangeCommShift (bc : BaseChangeData.{w} O)
    {U V : Cᵒᵖ} (a : V ⟶ U) : (bc.baseChange a).CommShift ℤ :=
  (bc.baseChangeAdj a).leftAdjointCommShift ℤ

attribute [local instance] derivedRestrictionCommShift derivedBaseChangeCommShift

/-- The comparison transformation commutes with the shift. -/
private lemma comparisonNatTrans_commShift (bc : BaseChangeData.{w} O)
    {U V : Cᵒᵖ} (a : V ⟶ U) :
    NatTrans.CommShift (comparisonNatTrans.{w} bc a) ℤ := by
  let F := bc.baseChange a
  let G := DRestrict.{w} O a
  let H := RGamma.{w} O V
  let K := RGamma.{w} O U
  let adj := bc.baseChangeAdj a
  let τ := restrictionMapNatTrans.{w} O a
  let : G.CommShift ℤ := by
    dsimp [G, DRestrict]
    infer_instance
  let : F.CommShift ℤ := adj.leftAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  let : H.CommShift ℤ := by
    dsimp [H, RGamma]
    infer_instance
  let : K.CommShift ℤ := by
    dsimp [K, RGamma]
    infer_instance
  let : NatTrans.CommShift τ ℤ := restrictionMapNatTrans_commShift.{w} O a
  exact Adjunction.natTrans_commShift_of_homEquiv_symm ℤ adj H K τ _ fun _ ↦ rfl

/-! ### Grothendieck abelianness of the categories in play -/

/-- The localization functor to the derived category of a Grothendieck abelian category
preserves direct sums, for any model of the derived category (Tag 07D9). -/
private lemma derivedCategoryQ_preservesCoproducts
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory A]
    [IsGrothendieckAbelian.{q} A] (I : Type q) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) := by
  let Q := DerivedCategory.Q (C := A)
  let : HasDerivedCategory A := HasDerivedCategory.standard A
  let Qs := DerivedCategory.Q (C := A)
  have : PreservesColimitsOfShape (Discrete I) Qs :=
    Stacks.Injectives.derivedCategoryQ_preservesCoproducts A I
  exact preservesColimitsOfShape_of_natIso
    (Localization.compUniqFunctor Qs Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))

/-- An exact functor which preserves `Discrete J`-colimits induces a functor on derived
categories which preserves them, provided both localization functors preserve them. -/
private theorem mapDerivedCategory_preservesDiscreteColimits
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : Type*) [HasColimitsOfShape (Discrete J) A]
    [HasColimitsOfShape (Discrete J) (DerivedCategory A)]
    [PreservesColimitsOfShape (Discrete J) F]
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A))]
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := B))] :
    PreservesColimitsOfShape (Discrete J) F.mapDerivedCategory := by
  have : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := A) ⋙ F.mapDerivedCategory) :=
    (preservesColimitsOfShape_iff_of_natIso F.mapDerivedCategoryFactors).2 inferInstance
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    (DerivedCategory.Q (C := A)) F.mapDerivedCategory J

/-! ### The four assertions of Stacks 0GYW -/

variable (bc : BaseChangeData.{w} O)

/-- **Stacks 0GYW**, strict fullness: the cartesian objects form a subcategory of `D(O)` closed
under isomorphisms. -/
@[stacks 0GYW "strictly full"]
instance isQC_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsQC.{w} bc) :=
  ⟨by
    intro K K' e hK
    change ∀ {U V : Cᵒᵖ} (a : V ⟶ U), IsIso (comparison.{w} bc a K')
    intro U V a
    have := hK a
    have : IsIso ((bc.baseChange a).map ((RGamma.{w} O V).map e.hom) ≫
        comparison.{w} bc a K') := by
      rw [comparison_naturality.{w} bc a e.hom]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((bc.baseChange a).map ((RGamma.{w} O V).map e.hom)) (comparison.{w} bc a K')⟩

/-- The cartesian objects are stable under retracts. -/
private lemma isQC_stableUnderRetracts :
    CategoryTheory.ObjectProperty.IsStableUnderRetracts (IsQC.{w} bc) := by
  refine ⟨fun {K K'} rt hK' => ?_⟩
  show ∀ {U V : Cᵒᵖ} (a : V ⟶ U), IsIso (comparison.{w} bc a K)
  exact fun a => isIso_app_of_retract (comparisonNatTrans.{w} bc a) rt (hK' a)

/-- **Stacks 0GYW**, saturation: a direct summand of a cartesian object is cartesian. -/
@[stacks 0GYW "saturated"]
instance isQC_isSaturated : ObjectProperty.IsSaturated (IsQC.{w} bc) :=
  letI : CategoryTheory.ObjectProperty.IsStableUnderRetracts (IsQC.{w} bc) :=
    isQC_stableUnderRetracts.{w} bc
  ObjectProperty.IsSaturated.of_isStableUnderRetracts (IsQC.{w} bc)

/-- For each `a`, the objects at which the comparison map at `a` is invertible form a triangulated
subcategory of `D(O)`. -/
private lemma isIso_comparisonNatTrans_isTriangulated {U V : Cᵒᵖ} (a : V ⟶ U) :
    ObjectProperty.IsTriangulated (fun K => IsIso ((comparisonNatTrans.{w} bc a).app K)) := by
  let F := RGamma.{w} O V ⋙ bc.baseChange a
  let G := RGamma.{w} O U
  let : F.CommShift ℤ := by dsimp [F]; infer_instance
  let : G.CommShift ℤ := by dsimp [G, RGamma]; infer_instance
  let : (bc.baseChangeAdj a).CommShift ℤ := (bc.baseChangeAdj a).commShift_of_rightAdjoint ℤ
  let : NatTrans.CommShift (comparisonNatTrans.{w} bc a) ℤ := comparisonNatTrans_commShift.{w} bc a
  let : (bc.baseChangeAdj a).IsTriangulated :=
    CategoryTheory.Adjunction.IsTriangulated.mk'' (bc.baseChangeAdj a)
  exact isIso_app_isTriangulated F G (comparisonNatTrans.{w} bc a)

/-- **Stacks 0GYW**, triangulatedness: the cartesian objects form a triangulated subcategory of
`D(O)`. -/
@[stacks 0GYW "triangulated"]
instance isQC_isTriangulated : ObjectProperty.IsTriangulated (IsQC.{w} bc) := by
  let P : ObjectProperty (DMod.{w} O) :=
    fun K => ∀ {U V : Cᵒᵖ} (a : V ⟶ U), IsIso (comparison.{w} bc a K)
  change ObjectProperty.IsTriangulated P
  refine {
    exists_zero := ⟨0, isZero_zero _, fun a => ?_⟩
    isStableUnderShiftBy := fun n => ⟨fun K hK _ _ a => ?_⟩
    ext₂' := fun T hT h₁ h₃ => ⟨T.obj₂, fun a => ?_, ⟨Iso.refl _⟩⟩ }
  all_goals
    have := isIso_comparisonNatTrans_isTriangulated.{w} bc a
    have := isIso_app_isClosedUnderIsomorphisms (comparisonNatTrans.{w} bc a)
  · simpa [comparisonNatTrans] using
      ObjectProperty.prop_of_isZero (fun K => IsIso ((comparisonNatTrans.{w} bc a).app K))
        (isZero_zero _)
  · exact ObjectProperty.le_shift (P := fun K => IsIso ((comparisonNatTrans.{w} bc a).app K)) n K
      (hK a)
  · exact ObjectProperty.ext_of_isTriangulatedClosed₂
      (fun K => IsIso ((comparisonNatTrans.{w} bc a).app K)) T hT (h₁ a) (h₃ a)

/-- **Stacks 0GYW**, direct sums: a direct sum of cartesian objects, indexed by an arbitrary
type, is cartesian. -/
@[stacks 0GYW "arbitrary direct sums"]
instance isQC_isClosedUnderColimitsOfShape (J : Type j) :
    ObjectProperty.IsClosedUnderColimitsOfShape (IsQC.{w} bc) (Discrete J) := by
  classical
  let P : ObjectProperty (DMod.{w} O) :=
    fun K => ∀ {U V : Cᵒᵖ} (a : V ⟶ U), IsIso (comparison.{w} bc a K)
  change ObjectProperty.IsClosedUnderColimitsOfShape P (Discrete J)
  refine ⟨?_⟩
  intro X hX
  obtain ⟨p⟩ := hX
  let K := p.diag
  let s : Cocone K := Cocone.mk X p.ι
  let : HasColimit K := ⟨s, p.isColimit⟩
  let S := {i : J // ¬ IsZero (K.obj (Discrete.mk i))}
  let KS : Discrete S ⥤ DMod.{w} O :=
    Discrete.functor (fun i => K.obj (Discrete.mk i.1))
  let cS : Cocone KS := {
    pt := X
    ι := Discrete.natTrans (fun i => p.ι.app (Discrete.mk i.as.1))
  }
  let extendCocone (t : Cocone KS) : Cocone K := {
    pt := t.pt
    ι := Discrete.natTrans (fun i => if hi : ¬ IsZero (K.obj i) then
      t.ι.app (Discrete.mk ⟨i.as, hi⟩) else 0)
  }
  have hcS : IsColimit cS := by
    refine ⟨(fun t => p.isColimit.desc (extendCocone t)), ?_, ?_⟩
    · intro t i
      have hfac := p.isColimit.fac (extendCocone t) (Discrete.mk i.as.1)
      simpa [cS, extendCocone, i.as.2] using hfac
    · intro t m hm
      apply p.isColimit.hom_ext
      intro i
      by_cases hi : ¬ IsZero (K.obj i)
      · have hmi := hm (Discrete.mk ⟨i.as, hi⟩)
        change p.ι.app i ≫ m = p.ι.app i ≫ p.isColimit.desc (extendCocone t)
        rw [p.isColimit.fac]
        simpa [extendCocone, cS, hi] using hmi
      · exact (not_not.mp hi).eq_of_src _ _
  let : LocallySmall.{max u v r w} (DMod.{w} O) := inferInstance
  let : Small.{max u v r w} S :=
    small_nonzero_support_of_isColimit (K := K) s p.isColimit
  let I := Shrink.{max u v r w} S
  let e : Discrete I ≌ Discrete S := Discrete.equivalence ((equivShrink S).symm)
  let KI := e.functor ⋙ KS
  let cI := cS.whisker e.functor
  have hcI : IsColimit cI := hcS.whiskerEquivalence e
  let : HasColimit KI := ⟨cI, hcI⟩
  change ∀ {U V : Cᵒᵖ} (a : V ⟶ U), IsIso (comparison.{w} bc a X)
  intro U V a
  let η := comparisonNatTrans.{w} bc a
  let F := RGamma.{w} O V ⋙ bc.baseChange a
  let G := RGamma.{w} O U
  have hmod (W : Cᵒᵖ) :
      IsGrothendieckAbelian.{max u v r w} (ModuleCat.{max u v r w} (O.obj W)) :=
    Stacks.EtaleCohomology.moduleCat_isGrothendieckAbelian.{r, max u v r w} (O.obj W)
  let := hmod U
  let := hmod V
  let : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q.{max u v r w} (C := PresheafOfModules.{max u v r w} O)) :=
    derivedCategoryQ_preservesCoproducts _ I
  let : PreservesColimitsOfShape (Discrete I) (RGamma.{w} O V) := by
    dsimp [RGamma]
    exact mapDerivedCategory_preservesDiscreteColimits
      (PresheafOfModules.evaluation.{max u v r w} O V) I
  let : PreservesColimitsOfShape (Discrete I) (RGamma.{w} O U) := by
    dsimp [RGamma]
    exact mapDerivedCategory_preservesDiscreteColimits
      (PresheafOfModules.evaluation.{max u v r w} O U) I
  let : (bc.baseChange a).IsLeftAdjoint := (bc.baseChangeAdj a).isLeftAdjoint
  let : PreservesColimit KI F := by dsimp [F]; infer_instance
  let : PreservesColimit KI G := by dsimp [G]; infer_instance
  have hcol : IsIso (η.app (colimit KI)) :=
    Stacks.DerivedCategoryComparisons.isIso_app_colimit_of_preserves F G η KI
      (fun i => (p.prop_diag_obj (Discrete.mk (e.functor.obj i).as.1)) a)
  let eX : colimit KI ≅ X := hcI.coconePointUniqueUpToIso (colimit.isColimit KI) |>.symm
  have : IsIso (F.map eX.hom ≫ η.app X) := by
    rw [η.naturality eX.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map eX.hom) (η.app X)

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
