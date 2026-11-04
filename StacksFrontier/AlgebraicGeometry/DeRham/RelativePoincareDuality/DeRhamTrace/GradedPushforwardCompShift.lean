module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnitCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.PushforwardFirstDifferentialDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward

/-!
# The derived direct image and its comparisons commute with the shift

For morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` the composition isomorphism
`Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of [Stacks, Tag 0D5T] is the uniqueness isomorphism of right adjoints
of `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. The commutations of the derived pushforwards with the shift are
transported from those of the derived pullbacks along the derived adjunctions, and the
comparison of [Stacks, Tag 0D5S] commutes with the shift, so the composition isomorphism commutes
with the shift: this is an instance of the general fact that the uniqueness isomorphism of right
adjoints of shift-compatible left adjoints is shift-compatible.

The commutation of `Rf_*` with the shift transported along `Lf^* ⊣ Rf_*` is moreover the one of
`Rf_*` as a total right derived functor, since the derived adjunction is compatible with the
derived-functor commutations; so the comparison `Q(f_*K) ⟶ Rf_*(QK)` of the degreewise direct
image of a complex with the derived one commutes with the shift.

## Main results

* `CategoryTheory.Adjunction.commShift_rightAdjointUniq_ofNatIsoLeft`
* `CategoryTheory.Adjunction.rightAdjointCommShift_eq`
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.commShift_derivedPushforwardCompIso_hom`
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift_eq`
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardComparisonQ_commShift`

## References

* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction

open Category CategoryTheory.Functor

variable {A : Type*} [AddMonoid A] {C D : Type*} [Category* C] [Category* D]
  [HasShift C A] [HasShift D A] {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C}
  [F₁.CommShift A] [F₂.CommShift A] [G₁.CommShift A] [G₂.CommShift A]

/-- **The uniqueness isomorphism of right adjoints of shift-compatible left adjoints is
shift-compatible.** For shift-compatible adjunctions `F₁ ⊣ G₁` and `F₂ ⊣ G₂` and a
shift-compatible isomorphism `F₁ ≅ F₂`, the isomorphism `G₁ ≅ G₂` of right adjoints of `F₂`
commutes with the shift. -/
theorem commShift_rightAdjointUniq_ofNatIsoLeft (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
    [adj₁.CommShift A] [adj₂.CommShift A] (e : F₁ ≅ F₂) [NatTrans.CommShift e.hom A] :
    NatTrans.CommShift (rightAdjointUniq (adj₁.ofNatIsoLeft e) adj₂).hom A := by
  let τ : G₁ ⟶ G₂ := (Functor.rightUnitor G₁).inv ≫ Functor.whiskerLeft G₁ adj₂.unit ≫
    Functor.whiskerLeft G₁ (Functor.whiskerRight e.inv G₂) ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight adj₁.counit G₂ ≫ (Functor.leftUnitor G₂).hom
  have : (rightAdjointUniq (adj₁.ofNatIsoLeft e) adj₂).hom = τ := by
    ext x
    simp [τ, rightAdjointUniq, ofNatIsoLeft]
  rw [this]
  dsimp only [τ]
  infer_instance

/-- **The commutation of a right adjoint with the shift is the one transported from the left
adjoint**, as soon as the adjunction is compatible with it. -/
theorem rightAdjointCommShift_eq {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : Type*) [AddGroup A]
    [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A] [adj.CommShift A] :
    adj.rightAdjointCommShift A = ‹G.CommShift A› := by
  refine Functor.CommShift.ext_of_commShiftIso_hom_app fun a X ↦ ?_
  have h : Adjunction.CommShift.CompatibilityUnit adj (F.commShiftIso a) (G.commShiftIso a) :=
    fun Y ↦ by
      simpa [Functor.commShiftIso_comp_hom_app] using
        (adj.unit_app_commShiftIso_hom_app A a Y).symm
  exact congr_app (congrArg Iso.hom (Adjunction.CommShift.compatibilityUnit_unique_right adj _ _ _
    (Adjunction.RightAdjointCommShift.compatibilityUnit_iso adj a) h)) X

end CategoryTheory.Adjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

open CategoryTheory
open scoped Stacks.StandardDerivedModel

universe u

variable {X Y Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` commutes with the shift**
([Stacks, Tag 0D5T]), for the commutations of the derived pushforwards with the shift
transported along the derived adjunctions. -/
theorem commShift_derivedPushforwardCompIso_hom :
    letI := derivedPushforwardCommShift f
    letI := derivedPushforwardCommShift g
    letI := derivedPushforwardCommShift (f ≫ g)
    NatTrans.CommShift (derivedPushforwardCompIso f g).hom ℤ := by
  let := derivedPushforwardCommShift f
  let := derivedPushforwardCommShift g
  let := derivedPushforwardCommShift (f ≫ g)
  have := (derivedAdjunction f).commShift_of_leftAdjoint ℤ
  have := (derivedAdjunction g).commShift_of_leftAdjoint ℤ
  have := (derivedAdjunction (f ≫ g)).commShift_of_leftAdjoint ℤ
  exact Adjunction.commShift_rightAdjointUniq_ofNatIsoLeft
    ((derivedAdjunction g).comp (derivedAdjunction f)) (derivedAdjunction (f ≫ g))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g)

/-- The composition isomorphism followed by the identification of `R(f ≫ g)_*` with `Rh_*` for
`f ≫ g = h` commutes with the shift. -/
theorem commShift_derivedPushforwardCompIso_trans_eqToIso_hom (h : X ⟶ Z) (hfg : f ≫ g = h) :
    letI := derivedPushforwardCommShift f
    letI := derivedPushforwardCommShift g
    letI := derivedPushforwardCommShift h
    NatTrans.CommShift (derivedPushforwardCompIso f g ≪≫
      eqToIso (show derivedPushforward (f ≫ g) = derivedPushforward h by rw [hfg])).hom ℤ := by
  subst hfg
  let := derivedPushforwardCommShift f
  let := derivedPushforwardCommShift g
  let := derivedPushforwardCommShift (f ≫ g)
  have := commShift_derivedPushforwardCompIso_hom f g
  simp only [eqToIso_refl, Iso.trans_refl]
  infer_instance

/-- **The commutation of `Rf_*` with the shift transported along `Lf^* ⊣ Rf_*` is the one of a
total right derived functor.** -/
theorem derivedPushforwardCommShift_eq :
    derivedPushforwardCommShift f =
      Functor.IsRightDerivedFunctor.commShift (derivedPushforward f) (derivedPushforwardUnit f)
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)) ℤ := by
  let := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ℤ
  have : (derivedAdjunction f).CommShift ℤ := derivedAdjunction_commShift f
  exact Adjunction.rightAdjointCommShift_eq (derivedAdjunction f) ℤ

section Comparison

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- The comparison `Q(f_*K) ⟶ Rf_*(QK)`, as a morphism of functors of the complex `K`. -/
def pushforwardComparisonNatTrans :
    Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex f ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedPushforward f :=
  Functor.whiskerLeft (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex f)
      (DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((StacksDraft.KFlat.modulePushforward f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) (ComplexShape.up ℤ))
      (derivedPushforwardUnit f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom (derivedPushforward f)

/-- The comparison `Q(f_*K) ⟶ Rf_*(QK)` commutes with the shift, for the commutation of `Rf_*`
with the shift as a total right derived functor. -/
instance : NatTrans.CommShift (pushforwardComparisonNatTrans f) ℤ := by
  dsimp only [pushforwardComparisonNatTrans]
  infer_instance

/-- The components of `pushforwardComparisonNatTrans` are the comparisons
`Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ`. -/
theorem pushforwardComparisonNatTrans_app
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (pushforwardComparisonNatTrans f).app K =
      Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ f K :=
    by
  have e₀ : DerivedCategory.Qh.map (((StacksDraft.KFlat.modulePushforward f
      ).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  simp only [pushforwardComparisonNatTrans,
    Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, e₀]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

/-- **The comparison `Q(f_*K) ⟶ Rf_*(QK)` commutes with the shift**, for the commutation of
`Rf_*` with the shift transported along the derived adjunction. -/
theorem pushforwardComparisonQ_commShift
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (m : ℤ) :
    letI := derivedPushforwardCommShift f
    Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ f
        (K⟦m⟧) ≫
      (derivedPushforward f).map ((DerivedCategory.Q.commShiftIso m).hom.app K) ≫
      ((derivedPushforward f).commShiftIso m).hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map
        (((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex f).commShiftIso
          m).hom.app K) ≫
      (DerivedCategory.Q.commShiftIso m).hom.app
        ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex f).obj K) ≫
      (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ f
        K)⟦m⟧' := by
  rw [derivedPushforwardCommShift_eq]
  have h := NatTrans.shift_app_comm (pushforwardComparisonNatTrans f) m K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc,
    pushforwardComparisonNatTrans_app] at h
  exact h.symm

end Comparison

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
