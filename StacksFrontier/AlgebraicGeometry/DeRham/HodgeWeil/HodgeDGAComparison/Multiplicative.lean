module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGAComparison.Equiv

/-!
# The identification of the Hodge complex cohomology with Hodge cohomology is multiplicative

The multiplication of the Hodge complex restricts to the wedge product of its summands
`Ω^p[-p]`, and the identification `hodgeDgaEquiv : H^n(X, ℋ) ≅ H^n_{Hodge}(X/S)` carries the cup
product of Section 0FKU followed by the multiplication of `ℋ` to the cup product of Hodge
cohomology, and the unit to the unit.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafOfModules.baseRingedSpace

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry ComplexShape
open AlgebraicGeometry.SheafOfModules
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped TensorProduct DirectSum Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

attribute [local instance] AlgebraicGeometry.SheafOfModules.preservesZeroMorphisms_sheafTensor
  AlgebraicGeometry.SheafOfModules.preservesZeroMorphisms_sheafTensor_obj

/-! ### The multiplication of the summands -/

section SummandWedge


/-- **The action of the Hodge complex on itself is the wedge product on the summands of pure
degree**: on the summand `Ω^p ⊗_A Ω^q` of `Tot(ℋ ⊗_A ℋ)` in degree `p + q` the action is wedge
multiplication, up to identifications of objects. -/
theorem isEqToHomSandwich_dgActionComponent (p q : ℕ) (k : ℤ) (h : (p : ℤ) + (q : ℤ) = k) :
    IsEqToHomSandwich (exteriorProductComponent B p q)
      (dgActionComponent (_root_.SheafOfModules.DifferentialGradedModule.regularModule
        (hodgeDGA B)) p q ≫ ((hodgeDGA B).complex.XIsoOfEq h).hom) := by
  obtain rfl : k = ((p + q : ℕ) : ℤ) := by push_cast; omega
  let D := deRhamDifferential B
  let K := deRhamComplex B D
  have e1 := ι_dgActionDesc (_root_.SheafOfModules.DifferentialGradedModule.regularModule
    (deRhamDifferentialGradedAlgebra B D)) p q _ h
  have e3 := ι_multiplicationInt_f (wedgeProduct B D) (p + q) p q h
  have e4 := ι_wedgeProductDesc B D p q (p + q) rfl
  have hchain : dgActionComponent (_root_.SheafOfModules.DifferentialGradedModule.regularModule
        (hodgeDGA B)) p q ≫ ((hodgeDGA B).complex.XIsoOfEq h).hom =
      ((sheafTensor A).map (K.extendXIso embeddingUpNat (i' := (p : ℤ)) (i := p)
          (by simp)).hom).app _ ≫
        ((sheafTensor A).obj (K.X p)).map (K.extendXIso embeddingUpNat (i' := (q : ℤ)) (i := q)
          (by simp)).hom ≫
        exteriorProductComponent B p q ≫ (K.XIsoOfEq (rfl : p + q = p + q)).hom ≫
        (K.extendXIso embeddingUpNat (i' := ((p + q : ℕ) : ℤ)) (i := p + q) (by simp)).inv := by
    refine e1.symm.trans ?_
    rw [← dgAction_f, dgAction_regular_deRham]
    refine e3.trans ?_
    rw [wedgeProduct_f, reassoc_of% e4]
    exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.assoc _ _ _))
  refine IsEqToHomSandwich.of_eq hchain ?_
  refine IsEqToHomSandwich.pre (exists_eqToHom_app (exists_eqToHom_map _
    (exists_eqToHom_extendXIso_hom _ _ _)) _) ?_
  refine IsEqToHomSandwich.pre (exists_eqToHom_map _ (exists_eqToHom_extendXIso_hom _ _ _)) ?_
  refine IsEqToHomSandwich.assoc ?_
  refine IsEqToHomSandwich.post ?_ (exists_eqToHom_extendXIso_inv _ _ _)
  exact IsEqToHomSandwich.post (IsEqToHomSandwich.self _) ⟨rfl, rfl⟩

/-- **`Ω^p[-p]` is the bottom graded piece of the Hodge filtration**, the sheaf `Ω^p` placed in
degree `p` of the `ℕ`-indexed complexes, extended by zero. -/
def hodgeSummandGradedPieceIso (p : ℕ) :
    hodgeSummand B p ≅
      (deRhamGradedPiece B (deRhamDifferential B) p).extend embeddingUpNat :=
  (HomologicalComplex.single
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) (up ℤ)
      (p : ℤ)).mapIso (hodgeComplexIntXIso B p) ≪≫
    (HomologicalComplex.extendSingleIso embeddingUpNat
      ((deRhamComplex B (deRhamDifferential B)).X p) p (p : ℤ) rfl).symm

/-- The identification `ℋ^p = Ω^p` is an identification of objects. -/
theorem exists_eqToHom_hodgeComplexIntXIso_hom (p : ℕ) :
    ∃ h, (hodgeComplexIntXIso B p).hom = eqToHom h := by
  unfold hodgeComplexIntXIso
  exact exists_eqToHom_extendXIso_hom (deRhamComplex B (deRhamDifferential B)) embeddingUpNat _

/-- The inverse of the identification `ℋ^p = Ω^p` is an identification of objects. -/
theorem exists_eqToHom_hodgeComplexIntXIso_inv (p : ℕ) :
    ∃ h, (hodgeComplexIntXIso B p).inv = eqToHom h := by
  unfold hodgeComplexIntXIso
  exact exists_eqToHom_extendXIso_inv (deRhamComplex B (deRhamDifferential B)) embeddingUpNat _

/-- In degree `p` the identification of `Ω^p[-p]` with the graded piece is an identification
of objects. -/
theorem exists_eqToHom_hodgeSummandGradedPieceIso_hom_f (p : ℕ) :
    ∃ h, (hodgeSummandGradedPieceIso B p).hom.f (p : ℤ) = eqToHom h := by
  refine exists_eqToHom_of_eq (HomologicalComplex.comp_f _ _ _) (exists_eqToHom_comp ?_ ?_)
  · exact exists_eqToHom_of_eq (HomologicalComplex.single_map_f_self _ _ _)
      (exists_eqToHom_comp (exists_eqToHom_singleObjXSelf_hom _ _)
        (exists_eqToHom_comp (exists_eqToHom_hodgeComplexIntXIso_hom B p)
          (exists_eqToHom_singleObjXSelf_inv _ _)))
  · exact exists_eqToHom_of_eq (HomologicalComplex.extendSingleIso_inv_f _ _ _ _ _)
      (exists_eqToHom_comp (exists_eqToHom_singleObjXSelf_hom _ _)
        (exists_eqToHom_comp (exists_eqToHom_singleObjXSelf_inv _ _)
          (exists_eqToHom_extendXIso_inv _ _ _)))

/-- In degree `p` the inverse identification of `Ω^p[-p]` with the graded piece is an
identification of objects. -/
theorem exists_eqToHom_hodgeSummandGradedPieceIso_inv_f (p : ℕ) :
    ∃ h, (hodgeSummandGradedPieceIso B p).inv.f (p : ℤ) = eqToHom h := by
  refine exists_eqToHom_of_eq (HomologicalComplex.comp_f _ _ _) (exists_eqToHom_comp ?_ ?_)
  · exact exists_eqToHom_of_eq (HomologicalComplex.extendSingleIso_hom_f _ _ _ _ _)
      (exists_eqToHom_comp (exists_eqToHom_extendXIso_hom _ _ _)
        (exists_eqToHom_comp (exists_eqToHom_singleObjXSelf_hom _ _)
          (exists_eqToHom_singleObjXSelf_inv _ _)))
  · exact exists_eqToHom_of_eq (HomologicalComplex.single_map_f_self _ _ _)
      (exists_eqToHom_comp (exists_eqToHom_singleObjXSelf_hom _ _)
        (exists_eqToHom_comp (exists_eqToHom_hodgeComplexIntXIso_inv B p)
          (exists_eqToHom_singleObjXSelf_inv _ _)))

/-- In degree `p` the inclusion `Ω^p[-p] ⟶ ℋ` is an identification of objects. -/
theorem exists_eqToHom_hodgeSummandι_f (p : ℕ) :
    ∃ h, (hodgeSummandι B p).f (p : ℤ) = eqToHom h := by
  rw [hodgeSummandι, HomologicalComplex.mkHomFromSingle_f, Category.comp_id]
  exact exists_eqToHom_singleObjXSelf_hom _ _

/-- **The wedge product `Tot(Ω^p[-p] ⊗_A Ω^q[-q]) ⟶ Ω^{p + q}[-(p + q)]`** of two summands of
the Hodge complex: the multiplication of the bottom graded pieces of the Hodge filtration,
`AlgebraicGeometry.SheafOfModules.gradedPieceWedge`, read through
`hodgeSummandGradedPieceIso`. -/
def hodgeSummandWedge (p q : ℕ) :
    HomologicalComplex.mapBifunctor (hodgeSummand B p) (hodgeSummand B q) (sheafTensor A) (up ℤ) ⟶
      hodgeSummand B (p + q) :=
  HomologicalComplex.mapBifunctorMap (hodgeSummandGradedPieceIso B p).hom
      (hodgeSummandGradedPieceIso B q).hom (sheafTensor A) (up ℤ) ≫
    multiplicationInt (gradedPieceWedge B (deRhamDifferential B) p q) ≫
      (hodgeSummandGradedPieceIso B (p + q)).inv

/-- Reassociating a composite around a factorisation of its first two morphisms. -/
theorem sandwich_paste {V : Type*} [Category* V] {a b c d e f g h : V} (ι : a ⟶ b)
    (desc : b ⟶ c) (s : c ⟶ d) (x : d ⟶ e) (y : e ⟶ f) (m : a ⟶ g) (n : g ⟶ h) (w : h ⟶ c)
    (hL : ι ≫ desc = m ≫ n ≫ w) :
    ι ≫ ((desc ≫ s) ≫ x) ≫ y = m ≫ n ≫ w ≫ s ≫ x ≫ y := by
  simp only [← Category.assoc] at hL ⊢
  rw [hL]

/-- On its summand of bidegree `(p, q)` the wedge product of two summands of the Hodge complex
is wedge multiplication of forms, up to identifications of objects. -/
theorem isEqToHomSandwich_ι_hodgeSummandWedge_f (p q : ℕ)
    (h : (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ)) :
    IsEqToHomSandwich (exteriorProductComponent B p q)
      (HomologicalComplex.ιMapBifunctor (hodgeSummand B p) (hodgeSummand B q) (sheafTensor A)
        (up ℤ) p q _ h ≫ (hodgeSummandWedge B p q).f ((p + q : ℕ) : ℤ)) := by
  rw [hodgeSummandWedge, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, ι_multiplicationInt_f_assoc _ (p + q) p q h,
    gradedPieceWedge_f]
  have hL := ι_gradedPieceWedgeDesc B (deRhamDifferential B) p q p q rfl
  rw [gradedPieceWedgeSummand_self] at hL
  refine IsEqToHomSandwich.pre (exists_eqToHom_app (exists_eqToHom_map _
    (exists_eqToHom_hodgeSummandGradedPieceIso_hom_f B p)) _) ?_
  refine IsEqToHomSandwich.pre (exists_eqToHom_map _
    (exists_eqToHom_hodgeSummandGradedPieceIso_hom_f B q)) ?_
  refine IsEqToHomSandwich.pre (exists_eqToHom_app (exists_eqToHom_map _
    (exists_eqToHom_extendXIso_hom _ _ _)) _) ?_
  refine IsEqToHomSandwich.pre (exists_eqToHom_map _ (exists_eqToHom_extendXIso_hom _ _ _)) ?_
  refine IsEqToHomSandwich.of_eq (sandwich_paste _ _ _ _ _ _ _ _ hL) ?_
  refine IsEqToHomSandwich.pre (exists_eqToHom_map _ (exists_eqToHom_singleObjXSelf_hom
    (c := up ℕ) q ((deRhamComplex B (deRhamDifferential B)).X q))) ?_
  refine IsEqToHomSandwich.pre (exists_eqToHom_app (exists_eqToHom_map _
    (exists_eqToHom_singleObjXSelf_hom (c := up ℕ) p
      ((deRhamComplex B (deRhamDifferential B)).X p))) _) ?_
  exact IsEqToHomSandwich.post (IsEqToHomSandwich.self _)
    (exists_eqToHom_comp (exists_eqToHom_singleObjXSelf_inv _ _)
      (exists_eqToHom_comp (exists_eqToHom_extendXIso_inv _ _ _)
        (exists_eqToHom_hodgeSummandGradedPieceIso_inv_f B (p + q))))

/-- **The multiplication of the Hodge complex restricts to the wedge product on its summands**:
`Tot(Ω^p[-p] ⊗_A Ω^q[-q]) ⟶ Tot(ℋ ⊗_A ℋ) ⟶ ℋ` is
`Tot(Ω^p[-p] ⊗_A Ω^q[-q]) ⟶ Ω^{p + q}[-(p + q)] ⟶ ℋ`. -/
theorem mapBifunctorMap_hodgeSummandι_dgAction (p q : ℕ) :
    HomologicalComplex.mapBifunctorMap (hodgeSummandι B p) (hodgeSummandι B q) (sheafTensor A)
        (up ℤ) ≫
      dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule (hodgeDGA B)) =
      hodgeSummandWedge B p q ≫ hodgeSummandι B (p + q) := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  by_cases ha : a = (p : ℤ)
  swap
  · exact (isZero_tensorFunctor_obj_obj_of_left
      (HomologicalComplex.isZero_single_obj_X (up ℤ) (p : ℤ) _ a ha) _).eq_of_src _ _
  by_cases hb : b = (q : ℤ)
  swap
  · exact (isZero_tensorFunctor_obj_obj_of_right _
      (HomologicalComplex.isZero_single_obj_X (up ℤ) (q : ℤ) _ b hb)).eq_of_src _ _
  subst ha hb
  obtain rfl : k = ((p + q : ℕ) : ℤ) := by
    have : (p : ℤ) + (q : ℤ) = k := hab
    push_cast
    exact this.symm
  refine IsEqToHomSandwich.eq (f := exteriorProductComponent B p q) ?_ ?_
  · have h1 := HomologicalComplex.ι_mapBifunctorMap_assoc (hodgeSummandι B p) (hodgeSummandι B q)
      (sheafTensor A) (up ℤ) (p : ℤ) (q : ℤ) _ hab
      ((dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule
        (hodgeDGA B))).f ((p + q : ℕ) : ℤ))
    have h2 := ι_dgActionDesc (_root_.SheafOfModules.DifferentialGradedModule.regularModule
      (hodgeDGA B)) p q _ hab
    refine IsEqToHomSandwich.of_eq ((congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)).trans
      (h1.trans (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) h2)))) ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_app (exists_eqToHom_map _
      (exists_eqToHom_hodgeSummandι_f B p)) _) ?_
    refine IsEqToHomSandwich.pre (exists_eqToHom_map _ (exists_eqToHom_hodgeSummandι_f B q)) ?_
    exact isEqToHomSandwich_dgActionComponent B p q _ hab
  · refine IsEqToHomSandwich.of_eq ((congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)).trans
      (Category.assoc _ _ _).symm) ?_
    exact IsEqToHomSandwich.post (isEqToHomSandwich_ι_hodgeSummandWedge_f B p q hab)
      (exists_eqToHom_hodgeSummandι_f B (p + q))

end SummandWedge

/-- Cancelling an isomorphism and its inverse in the middle of a composite. -/
theorem iso_cancel_paste {V : Type*} [Category* V] {a b c d e : V} (x : a ⟶ b) (i : c ≅ b)
    (y : b ⟶ d) (j : d ≅ e) : (x ≫ i.inv) ≫ (i.hom ≫ y ≫ j.hom) ≫ j.inv = x ≫ y := by
  simp

/-- Moving a naturality square past two composites. -/
theorem naturality_paste {V : Type*} [Category* V] {P Q R S U W : V} (e : P ⟶ Q) (g : Q ⟶ R)
    (s : R ⟶ U) (c : U ⟶ W) (t : R ⟶ S) (s' : S ⟶ W) (n : t ≫ s' = s ≫ c) :
    e ≫ (g ≫ s) ≫ c = (e ≫ g ≫ t) ≫ s' := by
  simp only [Category.assoc, n]

/-- **The identification `H^n(X, Ω^p[-p]) ≅ H^q(X, Ω^p)` through the graded pieces of the Hodge
filtration**: it is `gradedPieceModuleShiftIso` followed by `hodgeComponentIso`. -/
theorem hodgeSummandCohomologyIso_hom_eq (p : ℕ) (n q : ℤ) (h : -(p : ℤ) + n = q) :
    (hodgeSummandCohomologyIso B p n q h).hom =
      cohomologyMap (S := baseRingedSpace A) (hodgeSummandGradedPieceIso B p).hom n ≫
        (gradedPieceModuleShiftIso B (deRhamDifferential B) p n q h).hom ≫
          (hodgeComponentIso B p q).hom := by
  have hc : (hodgeSummandGradedPieceIso B p).hom ≫
      (gradedPieceShiftIso B (deRhamDifferential B) p).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(p : ℤ))).map
          (HomologicalComplex.extendSingleIso embeddingUpNat (deRhamTerm B p) 0 0 rfl).hom =
      (hodgeSummandShiftIso B p).hom :=
    iso_cancel_paste _ _ _ _
  have n1 := shiftCohomologyIsoR_naturality (S := baseRingedSpace A)
    (HomologicalComplex.extendSingleIso embeddingUpNat (deRhamTerm B p) 0 0 rfl).hom
    (-(p : ℤ)) n q h
  rw [gradedPieceModuleShiftIso_hom]
  refine Eq.trans ?_ (naturality_paste _ _ _ _ _ _ n1).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) ((cohomologyMap_comp (S := baseRingedSpace A) _ _ n).trans
    (congrArg (_ ≫ ·) (cohomologyMap_comp (S := baseRingedSpace A) _ _ n))))
  refine Eq.trans ?_ (congrArg (fun f => cohomologyMap (S := baseRingedSpace A) f n ≫ _) hc.symm)
  rfl

/-- An isomorphism which factors through another one, inverted. -/
theorem inv_paste {V : Type*} [Category* V] {P Q R S : V} (t : P ≅ S) (a : P ⟶ Q) (b : Q ⟶ R)
    (c : R ≅ S) (hT : t.hom = a ≫ b ≫ c.hom) : t.inv ≫ a ≫ b = c.inv := by
  have : a ≫ b = t.hom ≫ c.inv := by
    rw [hT]
    simp
  rw [this, Iso.inv_hom_id_assoc]

/-- Cancelling an isomorphism after its inverse at the end of a composite. -/
theorem comp_inv_hom_paste {V : Type*} [Category* V] {a b c d : V} (x : a ⟶ b) (y : b ⟶ c)
    (i : d ≅ c) : (x ≫ y ≫ i.inv) ≫ i.hom = x ≫ y := by
  simp

/-- `hodgeSummandCohomologyIso` read in an equal target degree. -/
theorem hodgeSummandCohomologyIso_congr (p : ℕ) {n q q' : ℤ} (h : -(p : ℤ) + n = q)
    (hq : q = q') (z : cohomologyModule (S := baseRingedSpace A)
      (DerivedCategory.Q.obj (hodgeSummand (A := A) B p)) n) :
    (hodgeSummandCohomologyIso B p n q' (h.trans hq)).hom.hom z =
      reindexHodgeDeg B hq ((hodgeSummandCohomologyIso B p n q h).hom.hom z) := by
  subst hq
  rfl

/-- The inverse of `hodgeSummandCohomologyIso` through the graded pieces of the Hodge
filtration. -/
theorem gradedPieceModuleShiftIso_hodgeSummandCohomologyIso_inv (p : ℕ) (n q : ℤ)
    (h : -(p : ℤ) + n = q) (ξ : hodgeComponentBase B p q) :
    (gradedPieceModuleShiftIso B (deRhamDifferential B) p n q h).hom.hom
        ((cohomologyMap (S := baseRingedSpace A) (hodgeSummandGradedPieceIso B p).hom n).hom
          ((hodgeSummandCohomologyIso B p n q h).inv.hom ξ)) =
      (hodgeComponentIso B p q).inv.hom ξ :=
  ConcreteCategory.congr_hom
    (inv_paste _ _ _ _ (hodgeSummandCohomologyIso_hom_eq B p n q h)) ξ

/-- `H^n(X, -)` of the wedge product of two summands, read on the bottom graded pieces of the
Hodge filtration. -/
theorem cohomologyMap_hodgeSummandWedge_comp (p q : ℕ) (n : ℤ) :
    cohomologyMap (S := baseRingedSpace A) (hodgeSummandWedge B p q) n ≫
        cohomologyMap (S := baseRingedSpace A) (hodgeSummandGradedPieceIso B (p + q)).hom n =
      cohomologyMap (S := baseRingedSpace A) (HomologicalComplex.mapBifunctorMap
        (hodgeSummandGradedPieceIso B p).hom (hodgeSummandGradedPieceIso B q).hom
          (sheafTensor A) (up ℤ)) n ≫
        cohomologyMap (S := baseRingedSpace A)
          (multiplicationInt (gradedPieceWedge B (deRhamDifferential B) p q)) n := by
  refine (cohomologyMap_comp (S := baseRingedSpace A) _ _ n).symm.trans
    (Eq.trans ?_ (cohomologyMap_comp (S := baseRingedSpace A) _ _ n))
  exact congrArg (fun f => cohomologyMap (S := baseRingedSpace A) f n)
    (comp_inv_hom_paste _ _ _)

/-- **The cup product of two classes of pure bidegree, through the summands of the Hodge
complex, is the cup product on Hodge cohomology** `hodgeCohomologyCup`, with its Koszul sign
`(-1)^{q p'}`: the cup product of Section 0FKU of `H^n(X, Ω^p[-p])` and `H^m(X, Ω^{p'}[-p'])`
followed by the wedge product of the summands, read in `H^{q + q'}(X, Ω^{p + p'})`. -/
theorem hodgeSummandCohomologyIso_wedge_cup (p p' : ℕ) (n m q q' : ℤ) (h : -(p : ℤ) + n = q)
    (h' : -(p' : ℤ) + m = q') (ξ : hodgeCohomologyComponent B p q)
    (ζ : hodgeCohomologyComponent B p' q') :
    (hodgeSummandCohomologyIso B (p + p') (n + m) (q + q') (by push_cast; omega)).hom.hom
        ((cohomologyMap (S := baseRingedSpace A) (hodgeSummandWedge B p p') (n + m)).hom
          ((totalCupPairing (S := baseRingedSpace A) (hodgeSummand (A := A) B p)
            (hodgeSummand (A := A) B p') n m).hom
              ((hodgeSummandCohomologyIso B p n q h).inv.hom ξ ⊗ₜ
              (hodgeSummandCohomologyIso B p' m q' h').inv.hom ζ))) =
      hodgeCohomologyCup B p p' q q' ξ ζ := by
  let D := deRhamDifferential B
  let a := (hodgeSummandCohomologyIso B p n q h).inv.hom ξ
  let b := (hodgeSummandCohomologyIso B p' m q' h').inv.hom ζ
  let E := fun k : ℕ => (hodgeSummandGradedPieceIso B k).hom
  let G := fun (k : ℕ) (r s : ℤ) (hk : -(k : ℤ) + r = s) =>
    (gradedPieceModuleShiftIso B D k r s hk).hom.hom
  let c := (totalCupPairing (S := baseRingedSpace A) (hodgeSummand (A := A) B p)
    (hodgeSummand (A := A) B p') n m).hom (a ⊗ₜ b)
  have hpq : -((p + p' : ℕ) : ℤ) + (n + m) = q + q' := by push_cast; omega
  have e1 := ConcreteCategory.congr_hom (hodgeSummandCohomologyIso_hom_eq B (p + p') (n + m)
    (q + q') hpq) ((cohomologyMap (S := baseRingedSpace A) (hodgeSummandWedge B p p')
      (n + m)).hom c)
  have e2 := ConcreteCategory.congr_hom (cohomologyMap_hodgeSummandWedge_comp B p p' (n + m)) c
  have e3 := totalCupPairing_naturality_apply (S := baseRingedSpace A) (E p) (E p') n m a b
  have e4 := ConcreteCategory.congr_hom
    (canonicalPairingModule_eq (gradedPieceWedge B D p p') n m)
    ((cohomologyMap (S := baseRingedSpace A) (E p) n).hom a ⊗ₜ
      (cohomologyMap (S := baseRingedSpace A) (E p') m).hom b)
  have e5 := canonicalPairingModule_gradedPieceWedge_apply B D p p' n m q q' h h'
    ((cohomologyMap (S := baseRingedSpace A) (E p) n).hom a)
    ((cohomologyMap (S := baseRingedSpace A) (E p') m).hom b)
  have e6 := gradedPieceModuleShiftIso_hodgeSummandCohomologyIso_inv B p n q h ξ
  have e7 := gradedPieceModuleShiftIso_hodgeSummandCohomologyIso_inv B p' m q' h' ζ
  refine e1.trans ?_
  refine (congrArg (fun z => (hodgeComponentIso B (p + p') (q + q')).hom.hom
    (G (p + p') (n + m) (q + q') hpq z)) e2).trans ?_
  refine (congrArg (fun z => (hodgeComponentIso B (p + p') (q + q')).hom.hom
    (G (p + p') (n + m) (q + q') hpq ((cohomologyMap (S := baseRingedSpace A)
      (multiplicationInt (gradedPieceWedge B D p p')) (n + m)).hom z))) e3.symm).trans ?_
  refine (congrArg (fun z => (hodgeComponentIso B (p + p') (q + q')).hom.hom
    (G (p + p') (n + m) (q + q') hpq z)) e4.symm).trans ?_
  refine (congrArg (fun z => (hodgeComponentIso B (p + p') (q + q')).hom.hom z) e5).trans ?_
  rw [e6, e7, Units.smul_def]
  refine ((hodgeComponentIso B (p + p') (q + q')).hom.hom.toAddMonoidHom.map_zsmul _ _).trans ?_
  rw [mul_neg, Int.negOnePow_neg]
  change _ = ((q * (p' : ℤ)).negOnePow : ℤ) •
    hodgeComponentCup B (exteriorProductComponent B p p') q q' ξ ζ
  refine congrArg (((q * (p' : ℤ)).negOnePow : ℤ) • ·) ?_
  rw [hodgeComponentCup, singleMultiplication_exteriorProductComponent B D]
  rfl

/-- The bidegree of a cup product of two classes of pure bidegree. -/
abbrev HodgeBidegreeInt.add {n m : ℤ} (i : HodgeBidegreeInt n) (j : HodgeBidegreeInt m) :
    HodgeBidegreeInt (n + m) :=
  ⟨(i.1.1 + j.1.1, i.1.2 + j.1.2), hodgeBidegreeInt_add i j⟩

/-- **The cup product of the Hodge complex on two classes of pure bidegree** is the cup product
on Hodge cohomology: `ι(ξ) ∪ ι(ζ) = ι(ξ ∪ ζ)` for `ξ ∈ H^q(X, Ω^p)` and `ζ ∈ H^{q'}(X, Ω^{p'})`,
the cup product on the right being `hodgeCohomologyCup`, with its Koszul sign `(-1)^{q p'}`. -/
theorem hodgeDgaCup_hodgeIncl {n m : ℤ} (i : HodgeBidegreeInt n) (j : HodgeBidegreeInt m)
    (ξ : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ))
    (ζ : hodgeCohomologyComponent B j.1.1 (j.1.2 : ℤ)) :
    hodgeDgaCup B n m (hodgeIncl B i ξ) (hodgeIncl B j ζ) =
      hodgeIncl B (i.add j) (reindexHodgeDeg B (Nat.cast_add i.1.2 j.1.2).symm
        (hodgeCohomologyCup B i.1.1 j.1.1 (i.1.2 : ℤ) (j.1.2 : ℤ) ξ ζ)) := by
  let a := (hodgeSummandCohomologyIso B i.1.1 n i.1.2 i.neg_add_eq).inv.hom ξ
  let b := (hodgeSummandCohomologyIso B j.1.1 m j.1.2 j.neg_add_eq).inv.hom ζ
  let c := (totalCupPairing (S := baseRingedSpace A) (hodgeSummand (A := A) B i.1.1)
    (hodgeSummand (A := A) B j.1.1) n m).hom (a ⊗ₜ b)
  have e1 := totalCupPairing_naturality_apply (S := baseRingedSpace A) (hodgeSummandι B i.1.1)
    (hodgeSummandι B j.1.1) n m a b
  have e2 := cohomologyMap_comp_apply (S := baseRingedSpace A)
    (HomologicalComplex.mapBifunctorMap (hodgeSummandι B i.1.1) (hodgeSummandι B j.1.1)
      (sheafTensor A) (up ℤ))
    (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule (hodgeDGA B)))
    (n + m) c
  have e3 := congrArg (fun f => (cohomologyMap (S := baseRingedSpace A) f (n + m)).hom c)
    (mapBifunctorMap_hodgeSummandι_dgAction B i.1.1 j.1.1)
  have e4 := (cohomologyMap_comp_apply (S := baseRingedSpace A) (hodgeSummandWedge B i.1.1 j.1.1)
    (hodgeSummandι B (i.1.1 + j.1.1)) (n + m) c).symm
  have hq : (i.1.2 : ℤ) + (j.1.2 : ℤ) = ((i.1.2 + j.1.2 : ℕ) : ℤ) := (Nat.cast_add _ _).symm
  have e5 := hodgeSummandCohomologyIso_congr B (i.1.1 + j.1.1)
    (show -((i.1.1 + j.1.1 : ℕ) : ℤ) + (n + m) = (i.1.2 : ℤ) + (j.1.2 : ℤ) by
      have := i.neg_add_eq
      have := j.neg_add_eq
      push_cast at *
      omega) hq
    ((cohomologyMap (S := baseRingedSpace A) (hodgeSummandWedge B i.1.1 j.1.1) (n + m)).hom c)
  have e6 := hodgeSummandCohomologyIso_wedge_cup B i.1.1 j.1.1 n m i.1.2 j.1.2 i.neg_add_eq
    j.neg_add_eq ξ ζ
  rw [e6] at e5
  refine (congrArg (fun z => (cohomologyMap (S := baseRingedSpace A)
    (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule (hodgeDGA B)))
      (n + m)).hom z) e1).trans (e2.trans (e3.trans (e4.trans ?_)))
  refine congrArg (fun z => (cohomologyMap (S := baseRingedSpace A)
    (hodgeSummandι B (i.1.1 + j.1.1)) (n + m)).hom z) ?_
  refine Eq.trans ?_ (congrArg (fun z => ((hodgeSummandCohomologyIso B (i.1.1 + j.1.1) (n + m)
    (i.1.2 + j.1.2 : ℕ) (i.add j).neg_add_eq).inv.hom z)) e5)
  exact (ModuleCat.inv_hom_apply _ _).symm

section CupAdditivity

variable (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A))

/-- The cup product on the cohomology of a sheaf of differential graded algebras is additive in
its first variable. -/
theorem dgaCohomologyCup_add_left (n m : ℤ) (x x' : dgaCohomology 𝒜 n) (y : dgaCohomology 𝒜 m) :
    dgaCohomologyCup 𝒜 n m (x + x') y =
      dgaCohomologyCup 𝒜 n m x y + dgaCohomologyCup 𝒜 n m x' y := by
  unfold dgaCohomologyCup
  exact (congrArg _ (TensorProduct.add_tmul _ _ _)).trans (map_add _ _ _)

/-- The cup product on the cohomology of a sheaf of differential graded algebras is additive in
its second variable. -/
theorem dgaCohomologyCup_add_right (n m : ℤ) (x : dgaCohomology 𝒜 n) (y y' : dgaCohomology 𝒜 m) :
    dgaCohomologyCup 𝒜 n m x (y + y') =
      dgaCohomologyCup 𝒜 n m x y + dgaCohomologyCup 𝒜 n m x y' := by
  unfold dgaCohomologyCup
  exact (congrArg _ (TensorProduct.tmul_add _ _ _)).trans (map_add _ _ _)

/-- The cup product with zero on the left vanishes. -/
theorem dgaCohomologyCup_zero_left (n m : ℤ) (y : dgaCohomology 𝒜 m) :
    dgaCohomologyCup 𝒜 n m 0 y = 0 := by
  unfold dgaCohomologyCup
  exact (congrArg _ (TensorProduct.zero_tmul _ _)).trans (map_zero _)

/-- The cup product with zero on the right vanishes. -/
theorem dgaCohomologyCup_zero_right (n m : ℤ) (x : dgaCohomology 𝒜 n) :
    dgaCohomologyCup 𝒜 n m x 0 = 0 := by
  unfold dgaCohomologyCup
  exact (congrArg _ (TensorProduct.tmul_zero _ _)).trans (map_zero _)

end CupAdditivity

/-- The multiplicativity of `hodgeDgaEquiv`, on the images of classes of Hodge cohomology. -/
theorem hodgeDgaEquiv_cup_symm (n m : ℤ) (X : hodgePiece B n) (Y : hodgePiece B m) :
    hodgeDgaEquiv B (n + m) (hodgeDgaCup B n m ((hodgeDgaEquiv B n).symm X)
      ((hodgeDgaEquiv B m).symm Y)) = hodgePieceMul B n m X Y := by
  induction X using DirectSum.induction_on with
  | zero => simp [dgaCohomologyCup_zero_left]
  | add X X' hX hX' => simp [dgaCohomologyCup_add_left, hX, hX']
  | of i ξ =>
  induction Y using DirectSum.induction_on with
  | zero => simp [dgaCohomologyCup_zero_right]
  | add Y Y' hY hY' => simp [dgaCohomologyCup_add_right, hY, hY']
  | of j ζ =>
    rw [hodgeDgaEquiv_symm_of, hodgeDgaEquiv_symm_of, hodgeDgaCup_hodgeIncl,
      hodgeDgaEquiv_hodgeIncl, hodgePieceMul_of]

/-- **The identification `H^*(X, ℋ) ≅ H^*_{Hodge}(X/S)` is multiplicative.** The cup product on the
cohomology of the Hodge complex, the global cup product of Section 0FKU followed by the
multiplication of `ℋ`, is carried by `hodgeDgaEquiv` to the cup product `hodgePieceMul` on Hodge
cohomology, with its Koszul sign `(-1)^{q p'}` on `H^q(X, Ω^p) × H^{q'}(X, Ω^{p'})`. -/
theorem hodgeDgaEquiv_cup (n m : ℤ) (x : dgaCohomology (hodgeDGA B) n)
    (y : dgaCohomology (hodgeDGA B) m) :
    hodgeDgaEquiv B (n + m) (hodgeDgaCup B n m x y) =
      hodgePieceMul B n m (hodgeDgaEquiv B n x) (hodgeDgaEquiv B m y) := by
  have h := hodgeDgaEquiv_cup_symm B n m (hodgeDgaEquiv B n x) (hodgeDgaEquiv B m y)
  rwa [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h

/-! ### The unit -/

section Unit

/-- An identification of modules does not move elements, up to transport. -/
theorem moduleCat_eqToHom_hom_heq {R : Type*} [Ring R] {M N : ModuleCat.{u} R} (h : M = N)
    (x : M) : HEq ((eqToHom h).hom x) x := by
  subst h
  rfl

/-- In degree `p` the shift identification `Ω^p[-p] ≅ Ω^p[0][-p]` is an identification of
objects. -/
theorem exists_eqToHom_hodgeSummandShiftIso_hom_f (p : ℕ) :
    ∃ h, (hodgeSummandShiftIso B p).hom.f (p : ℤ) = eqToHom h := by
  have e : ((HomologicalComplex.single
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) (up ℤ)
        (p : ℤ)).obj (deRhamTerm B p)).X (p : ℤ) =
      ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(p : ℤ))).obj ((HomologicalComplex.single _ (up ℤ) 0).obj (deRhamTerm B p))).X
            (p : ℤ) := by
    rw [HomologicalComplex.single_obj_X_self]
    change deRhamTerm B p = ((HomologicalComplex.single _ (up ℤ) 0).obj (deRhamTerm B p)).X
      ((p : ℤ) + -(p : ℤ))
    rw [add_neg_cancel, HomologicalComplex.single_obj_X_self]
  refine exists_eqToHom_of_eq (HomologicalComplex.comp_f _ _ _) (exists_eqToHom_comp ?_
    ⟨e, singleFunctors_shiftIso_inv_app_f (-(p : ℤ)) (p : ℤ) 0 (by omega) (deRhamTerm B p)
      (p : ℤ) e⟩)
  exact exists_eqToHom_of_eq (HomologicalComplex.single_map_f_self _ _ _)
    (exists_eqToHom_comp (exists_eqToHom_singleObjXSelf_hom _ _)
      (exists_eqToHom_comp (exists_eqToHom_hodgeComplexIntXIso_hom B p)
        (exists_eqToHom_singleObjXSelf_inv _ _)))

/-- **`hodgeSummandCohomologyIso` on the class of a global cocycle**, in the degree `p` of the
summand `Ω^p[-p]`: a global cocycle of `Ω^p[-p]` in degree `p` goes to the class of the same
global section of `Ω^p`, placed in degree `0`. -/
theorem hodgeSummandCohomologyIso_globalClass (p : ℕ) (h : -(p : ℤ) + p = 0)
    (s : (sectionsComplex (baseRingedSpace A) (hodgeSummand (A := A) B p)).cycles (p : ℤ))
    (t : (sectionsComplex (baseRingedSpace A) (singleInt (A := A) (deRhamTerm B p))).cycles 0)
    (hst : HEq (((sectionsComplex (baseRingedSpace A) (hodgeSummand (A := A) B p)).iCycles
      (p : ℤ)).hom s) (((sectionsComplex (baseRingedSpace A)
        (singleInt (A := A) (deRhamTerm B p))).iCycles 0).hom t)) :
    (hodgeSummandCohomologyIso B p p 0 h).hom.hom
        (globalClass (X := baseRingedSpace A) (hodgeSummand (A := A) B p) (p : ℤ) s) =
      globalClass (X := baseRingedSpace A) (singleInt (X := X) (A := A) (@deRhamTerm X A φ B p)) 0
        t := by
  let N := singleInt (X := X) (A := A) (@deRhamTerm X A φ B p)
  let Γc := (globalSections (baseRingedSpace A)).mapHomologicalComplex (up ℤ)
  let s₂ := (HomologicalComplex.cyclesMap (Γc.map (hodgeSummandShiftIso B p).hom) p).hom s
  have g2 := globalClass_map (X := baseRingedSpace A) (hodgeSummandShiftIso B p).hom (p : ℤ) s
  let z := ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing (baseRingedSpace A)) _ s₂)
  have g3 := congrArg (fun f => f.hom (1 : baseRing (baseRingedSpace A)))
    (globalCycleClass_shiftCohomologyIsoR (S := baseRingedSpace A) N (-(p : ℤ)) p 0 h z)
  have hz : z.hom 1 = s₂ := one_smul _ _
  refine (congrArg (fun x => (shiftCohomologyIsoR (S := baseRingedSpace A) N (-(p : ℤ)) p 0
    h).hom.hom x) g2).trans ?_
  refine (congrArg (fun x => (shiftCohomologyIsoR (S := baseRingedSpace A) N (-(p : ℤ)) p 0
    h).hom.hom (globalClass (X := baseRingedSpace A) (shiftR (S := baseRingedSpace A) N
      (-(p : ℤ))) p x)) hz.symm).trans ?_
  refine g3.trans ?_
  refine congrArg (globalClass (X := baseRingedSpace A) N 0) ?_
  apply (ModuleCat.mono_iff_injective ((sectionsComplex (baseRingedSpace A) N).iCycles 0)).1
    inferInstance
  have i1 := congrArg (fun f => f.hom (1 : baseRing (baseRingedSpace A)))
    (shiftCycles_iCycles (sectionsComplex (baseRingedSpace A) N) 0 h (z ≫
      HomologicalComplex.cyclesMap ((((_root_.SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (baseRingedSpace A).sheaf)
          (op ⊤)).mapHomologicalComplex (up ℤ)).commShiftIso (-(p : ℤ))).hom.app N) p))
  refine i1.trans (eq_of_heq (HEq.trans ?_ hst))
  obtain ⟨e₁, he₁⟩ := exists_eqToHom_hodgeSummandShiftIso_hom_f B p
  have st2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    ((((_root_.SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (baseRingedSpace A).sheaf)
          (op ⊤)).mapHomologicalComplex (up ℤ)).commShiftIso (-(p : ℤ))).hom.app N) (p : ℤ))
    (z.hom 1)
  have st4 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (Γc.map (hodgeSummandShiftIso B p).hom) (p : ℤ)) s
  have st5 : HEq (((Γc.map (hodgeSummandShiftIso B p).hom).f p).hom
      (((sectionsComplex (baseRingedSpace A) (hodgeSummand (A := A) B p)).iCycles p).hom s))
      (((sectionsComplex (baseRingedSpace A) (hodgeSummand (A := A) B p)).iCycles p).hom s) := by
    change HEq (((globalSections (baseRingedSpace A)).map
      ((hodgeSummandShiftIso B p).hom.f p)).hom _) _
    rw [he₁, eqToHom_map]
    exact moduleCat_eqToHom_hom_heq _ _
  let Cm := HomologicalComplex.cyclesMap ((((_root_.SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (baseRingedSpace A).sheaf)
      (op ⊤)).mapHomologicalComplex (up ℤ)).commShiftIso (-(p : ℤ))).hom.app N) (p : ℤ)
  let Im := HomologicalComplex.iCycles ((CategoryTheory.shiftFunctor
    (CochainComplex (ModuleCat.{u} (baseRing (baseRingedSpace A))) ℤ) (-(p : ℤ))).obj
      (sectionsComplex (baseRingedSpace A) N)) (p : ℤ)
  let Sm := ((sectionsComplex (baseRingedSpace A) N).shiftFunctorObjXIso (-(p : ℤ)) p 0
    (by omega)).hom
  change HEq (Sm.hom (Im.hom (Cm.hom (z.hom 1)))) _
  refine (moduleCat_eqToHom_hom_heq (congrArg (sectionsComplex (baseRingedSpace A) N).X
    (show (p : ℤ) + -(p : ℤ) = 0 by omega)) (Im.hom (Cm.hom (z.hom 1)))).trans ?_
  refine (heq_of_eq (st2.trans (congrArg _ hz))).trans ?_
  exact (heq_of_eq st4).trans st5

/-- The bidegree `(0, 0)`. -/
abbrev hodgeBidegreeZero : HodgeBidegreeInt 0 := ⟨(0, 0), rfl⟩

/-- **The projection of the unit of `H^*(X, ℋ)` to `H^0(X, Ω^0)` is the unit class.** -/
theorem hodgeProj_dgaOneClass :
    hodgeProj B hodgeBidegreeZero (dgaOneClass (hodgeDGA B)) = hodgeOne B := by
  let c := dgaOneCycle (hodgeDGA B)
  let Γc := (globalSections (baseRingedSpace A)).mapHomologicalComplex (up ℤ)
  let c' := (HomologicalComplex.cyclesMap (Γc.map (hodgeSummandπ B 0)) 0).hom c
  have g1 := globalClass_map (X := baseRingedSpace A) (hodgeSummandπ B 0) 0 c
  have st := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (Γc.map (hodgeSummandπ B 0)) 0) c
  obtain ⟨e₀, he₀'⟩ : ∃ e, (hodgeSummandπ B 0).f ((0 : ℕ) : ℤ) = eqToHom e := by
    rw [hodgeSummandπ, HomologicalComplex.mkHomToSingle_f, Category.id_comp]
    exact exists_eqToHom_singleObjXSelf_inv _ _
  have he₀ : (hodgeSummandπ B 0).f 0 = eqToHom e₀ := he₀'
  have hst : HEq (((sectionsComplex (baseRingedSpace A) (hodgeSummand (A := A) B 0)).iCycles
      ((0 : ℕ) : ℤ)).hom c') (((sectionsComplex (baseRingedSpace A)
        (singleInt (A := A) (deRhamTerm B 0))).iCycles 0).hom (formsOneCycle B)) := by
    refine (heq_of_eq st).trans ?_
    change HEq (((globalSections (baseRingedSpace A)).map ((hodgeSummandπ B 0).f 0)).hom _) _
    rw [he₀, eqToHom_map]
    refine (moduleCat_eqToHom_hom_heq _ _).trans ?_
    refine (heq_of_eq (iCycles_dgaOneCycle (hodgeDGA B))).trans ?_
    refine (hodgeDGA_one B (op ⊤)).trans ?_
    refine HEq.trans ?_ (heq_of_eq (iCycles_formsOneCycle B).symm)
    exact (Stacks.DeRhamSmooth.eqToHom_val_app_heq_of_eq
      (HomologicalComplex.single_obj_X_self (up ℤ) 0 (deRhamTerm B 0)).symm (op ⊤)
        ((formsOne B).val (op ⊤))).symm
  have g2 := hodgeSummandCohomologyIso_globalClass B 0 (by simp) c' (formsOneCycle B) hst
  refine (congrArg (fun x =>
    (hodgeSummandCohomologyIso B 0 0 0 hodgeBidegreeZero.neg_add_eq).hom.hom x)
      ((congrArg (fun x => (cohomologyMap (S := baseRingedSpace A) (hodgeSummandπ B 0) 0).hom x)
        (dgaOneClass_eq_globalClass_one (hodgeDGA B))).trans g1)).trans ?_
  exact g2.trans (hodgeOne_eq_globalClass B).symm

/-- **The identification `H^*(X, ℋ) ≅ H^*_{Hodge}(X/S)` is unital.** The unit `1 ∈ H^0(X, ℋ)`, the
class of the global section `1` of `Ω^0`, goes to the unit `1 ∈ H^0(X, Ω^0)` of Hodge
cohomology. -/
theorem hodgeDgaEquiv_one :
    hodgeDgaEquiv B 0 (dgaOneClass (hodgeDGA B)) = hodgePieceOne B := by
  change (∑ j ∈ hodgeBidegrees 0, (DirectSum.lof _ _ (fun i : HodgeBidegreeInt 0 =>
      (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) j).comp (hodgeProj B j))
    (dgaOneClass (hodgeDGA B)) = _
  rw [LinearMap.sum_apply, Finset.sum_eq_single hodgeBidegreeZero, LinearMap.comp_apply,
    hodgeProj_dgaOneClass]
  · rfl
  · intro j _ hj
    exfalso
    refine hj (Subtype.ext ?_)
    have h2 : j.1.1 + j.1.2 = 0 := by exact_mod_cast j.2
    exact Prod.ext (show j.1.1 = 0 by omega) (show j.1.2 = 0 by omega)
  · exact fun h => absurd (mem_hodgeBidegrees _) h

end Unit

end Stacks.HodgeWeil

end
