module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.CategoryTheory.Shift.AdjunctionMateCommShift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# The derived adjunction `Lf^* ⊣ Rf_*` commutes with the shift

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The derived pullback `Lf^*` is a
total left derived functor and the derived pushforward `Rf_*` a total right derived functor, so
each carries its own commutation with the shift: the left derived one
`StacksDraft.PseudoCoherence.leftDerivedCommShift` and the right derived one
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift`. This file proves that the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 079W] is compatible with these two structures, at an arbitrary
model of the two derived categories, and draws the consequence on the quasi-coherent derived
categories of schemes.

## Main results

* `CategoryTheory.Adjunction.commShift_of_isLeftDerivedFunctor`: an adjunction `LF ⊣ RG`
  between localized categories whose unit is related, through the counit `α` of the left derived
  functor `LF` and a shift-compatible transformation `β` towards `RG`, to the unit of a
  shift-compatible adjunction `F ⊣ G`, is compatible with the shift for the left derived
  commutation on `LF`.
* `CategoryTheory.Adjunction.commShift_restrictFullyFaithful`: the restriction of a
  shift-compatible adjunction along fully faithful shift-compatible functors is
  shift-compatible for the induced commutations `Functor.CommShift.ofComp`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_commShift`: **`Lf^* ⊣ Rf_*`
  commutes with the shift**, for the derived-functor shifts on both sides.
* `Stacks.Duality.commShift_quasiCoherentDerivedPullback_eq`: on the quasi-coherent derived
  categories of schemes, the commutation of the restricted `Lf^*` with the shift obtained from the
  restricted adjunction is the one induced from the left derived commutation of `Lf^*`.

## Implementation notes

*The route.* The left derived commutation of `LF` is characterised by the compatibility of the
counit `α : L₁ ⋙ LF ⟶ F ⋙ L₂` with the shift
(`CategoryTheory.Functor.IsLeftDerivedFunctor.commShift_ext`): two commutations of `LF` with the
shift making `α` compatible agree, because `LF ⋙ shiftFunctor _ a` is again a left derived functor
and maps into a left derived functor are detected after composing with its counit. So it suffices
to check that the commutation `adj.leftAdjointCommShift` transported from `RG` along the
adjunction makes `α` compatible. Under the adjunction, `α` is the transpose of
`L₁(η^K) ≫ β`, which is the unit factorisation of Tag 079W; that transformation commutes with the
shift because `η^K`, `β` and `L₁` do, and the transpose of a shift-compatible transformation is
shift-compatible (`CategoryTheory.Adjunction.natTrans_commShift_of_homEquiv_symm`). No
cancellation of `α` — which is not invertible — is needed anywhere.

*The adjunction on homotopy categories.* The degreewise adjunction `f^* ⊣ f_*` induces
adjunctions on cochain complexes and on homotopy categories, and both commute with the shift for
Mathlib's commutations of `Functor.mapHomologicalComplex` and `Functor.mapHomotopyCategory`:
on complexes this is a degreewise identity, and on homotopy categories it is detected on the image
of the quotient functor.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory Category Functor
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

noncomputable section

namespace CategoryTheory

/-! ### Commutations with the shift with the same isomorphisms -/

/-- Two commutations of a functor with the shift whose isomorphisms have the same components are
equal: the two other fields of `Functor.CommShift` are propositions. -/
theorem Functor.CommShift.ext_of_commShiftIso_hom_app {C D : Type*} [Category* C] [Category* D]
    {G : C ⥤ D} {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]
    {h₁ h₂ : G.CommShift A}
    (e : ∀ (a : A) (X : C),
      (letI := h₁; G.commShiftIso a).hom.app X = (letI := h₂; G.commShiftIso a).hom.app X) :
    h₁ = h₂ := by
  cases h₁ with
  | mk i₁ _ _ =>
    cases h₂ with
    | mk i₂ _ _ =>
      obtain rfl : i₁ = i₂ := funext fun a ↦ Iso.ext (NatTrans.ext (funext (e a)))
      rfl

/-! ### Uniqueness of the commutation of a left derived functor with the shift -/

/-- **A left derived functor carries at most one commutation with the shift compatible with its
counit.** If `α : L ⋙ LF ⟶ F` makes `LF` a left derived functor of `F`, two commutations of `LF`
with the shift for which `α` commutes with the shift agree: `LF ⋙ shiftFunctor D a` is a left
derived functor of `F ⋙ shiftFunctor D a`, so a transformation into it is determined by its
composite with the counit, and both commutation isomorphisms have the same such composite. -/
theorem Functor.IsLeftDerivedFunctor.commShift_ext {C D H : Type*} [Category* C] [Category* D]
    [Category* H] (LF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H} (α : L ⋙ LF ⟶ F)
    (W : MorphismProperty C) [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]
    (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
    [F.CommShift A] [L.CommShift A] (h₁ h₂ : LF.CommShift A)
    (hα₁ : letI := h₁; NatTrans.CommShift α A) (hα₂ : letI := h₂; NatTrans.CommShift α A) :
    h₁ = h₂ := by
  have key : ∀ (h : LF.CommShift A) (_ : let := h; NatTrans.CommShift α A) (a : A) (X : C),
      (let := h; LF.commShiftIso a).hom.app (L.obj X) ≫ (α.app X)⟦a⟧' =
        LF.map ((L.commShiftIso a).inv.app X) ≫ α.app (X⟦a⟧) ≫
          (F.commShiftIso a).hom.app X := by
    intro h hα a X
    let := h
    have : NatTrans.CommShift α A := hα
    have hc := NatTrans.shift_app_comm α a X
    rw [Functor.commShiftIso_comp_hom_app, assoc] at hc
    rw [← hc, ← LF.map_comp_assoc, Iso.inv_hom_id_app, LF.map_id, id_comp]
  refine Functor.CommShift.ext_of_commShiftIso_hom_app fun a ↦ ?_
  have : (let := h₁; LF.commShiftIso a).hom = (let := h₂; LF.commShiftIso a).hom :=
    leftDerived_ext (LF ⋙ shiftFunctor D a)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α (shiftFunctor D a)) W _ _ _ (by
        ext X
        simpa using (key h₁ hα₁ a X).trans (key h₂ hα₂ a X).symm)
  exact fun X ↦ congr_app this X

/-! ### Uniqueness of the commutation of a left adjoint with the shift -/

/-- **The commutation of a left adjoint with the shift is the one transported from the right
adjoint**, as soon as the adjunction is compatible with it: the commutation isomorphisms of a left
adjoint compatible with the unit are determined by those of the right adjoint. -/
theorem Adjunction.leftAdjointCommShift_eq {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : Type*) [AddGroup A] [HasShift C A]
    [HasShift D A] [F.CommShift A] [G.CommShift A] [adj.CommShift A] :
    adj.leftAdjointCommShift A = ‹F.CommShift A› := by
  refine Functor.CommShift.ext_of_commShiftIso_hom_app fun a X ↦ ?_
  have h : Adjunction.CommShift.CompatibilityUnit adj (F.commShiftIso a) (G.commShiftIso a) :=
    fun Y ↦ by
      simpa [Functor.commShiftIso_comp_hom_app] using
        (adj.unit_app_commShiftIso_hom_app A a Y).symm
  exact congr_app (congrArg Iso.hom (Adjunction.CommShift.compatibilityUnit_unique_left adj _ _ _
    (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj a) h)) X

/-! ### Restriction of a shift-compatible adjunction along fully faithful functors -/

/-- **The restriction of a shift-compatible adjunction is shift-compatible.** Let `adj : L' ⊣ R'`
be compatible with the shift, and let `L`, `R` be restrictions of `L'`, `R'` along fully faithful
functors `iC`, `iD` commuting with the shift, through isomorphisms `e₁ : L ⋙ iD ≅ iC ⋙ L'` and
`e₂ : R ⋙ iC ≅ iD ⋙ R'`. With the commutations of `L` and `R` with the shift induced by `e₁` and
`e₂`, the restricted adjunction `Adjunction.restrictFullyFaithful` is compatible with the shift.
The unit is tested after applying the faithful functor `iC`, where it is the conjugate of the
unit of `adj` by `e₁` and `e₂`. -/
theorem Adjunction.commShift_restrictFullyFaithful {C D C' D' : Type*} [Category* C]
    [Category* D] [Category* C'] [Category* D'] {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'}
    {R' : D' ⥤ C'} (adj : L' ⊣ R') (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
    [iC.Full] [iC.Faithful] [iD.Full] [iD.Faithful] {L : C ⥤ D} {R : D ⥤ C}
    (e₁ : L ⋙ iD ≅ iC ⋙ L') (e₂ : R ⋙ iC ≅ iD ⋙ R') (A : Type*) [AddMonoid A]
    [HasShift C A] [HasShift D A] [HasShift C' A] [HasShift D' A] [iC.CommShift A]
    [iD.CommShift A] [L'.CommShift A] [R'.CommShift A] [adj.CommShift A] :
    letI := Functor.CommShift.ofComp e₁ A
    letI := Functor.CommShift.ofComp e₂ A
    (adj.restrictFullyFaithful hiC hiD e₁.symm e₂.symm).CommShift A := by
  let := Functor.CommShift.ofComp e₁ A
  let := Functor.CommShift.ofComp e₂ A
  have := Functor.CommShift.ofComp_compatibility e₁ A
  have := Functor.CommShift.ofComp_compatibility e₂ A
  refine Adjunction.CommShift.mk' _ _ ?_
  refine NatTrans.commShift_of_whiskerRight _ iC ?_
  refine NatTrans.commShift_of_eq (θ := iC.leftUnitor.hom ≫ iC.rightUnitor.inv ≫
    whiskerLeft iC adj.unit ≫ (Functor.associator iC L' R').inv ≫ whiskerRight e₁.inv R' ≫
    (Functor.associator L iD R').hom ≫ whiskerLeft L e₂.inv ≫ (Functor.associator L R iC).inv) ?_
  ext X
  simp

/-! ### The induced adjunctions on complexes and on homotopy categories -/

section MapHomotopyCategory

variable {A : Type*} [Category* A] [Preadditive A] {B : Type*} [Category* B] [Preadditive B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : G ⊣ F)

/-- The adjunction induced degreewise on cochain complexes commutes with the shift: in each
degree its unit is the unit of `adj`, and the commutations of both functors with the shift are
degreewise identities. -/
instance Adjunction.mapHomologicalComplexAdjunction_commShift :
    (Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).CommShift ℤ := by
  refine Adjunction.CommShift.mk' _ _ ⟨fun a ↦ ?_⟩
  ext K n
  simp [Adjunction.mapHomologicalComplexAdjunction_unit_app_f, Functor.commShiftIso_comp_hom_app]

/-- **The adjunction induced on homotopy categories commutes with the shift.** Its unit is tested
on the image of the quotient functor, where it is the class of the unit on complexes. -/
instance Adjunction.mapHomotopyCategoryAdjunction_commShift :
    (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).CommShift ℤ := by
  refine Adjunction.CommShift.mk' _ _ ?_
  refine NatTrans.commShift_of_whiskerLeft (HomotopyCategory.quotient B (ComplexShape.up ℤ)) _ ?_
  refine NatTrans.commShift_of_eq
    (θ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).rightUnitor.hom ≫
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).leftUnitor.inv ≫
      whiskerRight (Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).unit
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
        (F.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
      (Functor.associator _ _ _).hom) ?_
  ext K
  simp only [comp_obj, id_obj, whiskerLeft_app, mapHomotopyCategoryAdjunction_unit_app_quotient,
    mapHomotopyCategoryFactors, NatTrans.comp_app, rightUnitor_hom_app, leftUnitor_inv_app,
    whiskerRight_app, associator_hom_app, Quotient.lift.isLift_inv, associator_inv_app, comp_id,
    id_comp]
  exact (comp_id _).symm.trans (congrArg (CategoryStruct.comp
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).unit.app K)))
    ((id_comp _).trans ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map_id
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))).symm)

end MapHomotopyCategory

/-! ### An adjunction between derived functors commutes with the shift -/

section DerivedAdjunction

variable {C₁ C₂ H₁ H₂ : Type*} [Category* C₁] [Category* C₂] [Category* H₁] [Category* H₂]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adjK : F ⊣ G)
  {L₁ : C₁ ⥤ H₁} {L₂ : C₂ ⥤ H₂} {LF : H₁ ⥤ H₂} {RG : H₂ ⥤ H₁} (adj : LF ⊣ RG)
  (α : L₁ ⋙ LF ⟶ F ⋙ L₂) (β : G ⋙ L₁ ⟶ L₂ ⋙ RG)
  (hunit : ∀ M : C₁, adj.unit.app (L₁.obj M) ≫ RG.map (α.app M) =
    L₁.map (adjK.unit.app M) ≫ β.app (F.obj M))
  (A : Type*) [AddGroup A] [HasShift C₁ A] [HasShift C₂ A] [HasShift H₁ A] [HasShift H₂ A]
  [F.CommShift A] [G.CommShift A] [L₁.CommShift A] [L₂.CommShift A] [RG.CommShift A]
  [adjK.CommShift A] [NatTrans.CommShift β A]

include hunit in
/-- For the commutation of `LF` with the shift transported from `RG` along `adj`, the
transformation `α` commutes with the shift. Under the adjunction `α` is the transpose of
`L₁(η^K) ≫ β`, by the unit factorisation `hunit`, and that transformation commutes with the
shift. -/
theorem Adjunction.natTrans_commShift_of_unit_fac :
    letI := adj.leftAdjointCommShift A
    NatTrans.CommShift α A := by
  let := adj.leftAdjointCommShift A
  have := adj.commShift_of_rightAdjoint A
  refine Adjunction.natTrans_commShift_of_homEquiv_symm A adj L₁ (F ⋙ L₂)
    (L₁.leftUnitor.inv ≫ whiskerRight adjK.unit L₁ ≫ (Functor.associator F G L₁).hom ≫
      whiskerLeft F β ≫ (Functor.associator F L₂ RG).inv) α fun M ↦ ?_
  rw [Equiv.eq_symm_apply, adj.homEquiv_unit]
  simpa using hunit M

include hunit in
/-- **An adjunction between a left and a right derived functor commutes with the shift.** Let
`adjK : F ⊣ G` be compatible with the shift, `LF` a left derived functor of `F ⋙ L₂` with counit
`α`, equipped with a commutation with the shift for which `α` commutes with the shift, and `RG`
a functor commuting with the shift with a shift-compatible `β : G ⋙ L₁ ⟶ L₂ ⋙ RG`. An
adjunction `LF ⊣ RG` whose unit factors as `hunit` through those of `adjK` is compatible with the
shift.

The commutation of `LF` transported from `RG` along the adjunction makes `α` compatible
(`Adjunction.natTrans_commShift_of_unit_fac`), so it is the given one by
`Functor.IsLeftDerivedFunctor.commShift_ext`. -/
theorem Adjunction.commShift_of_isLeftDerivedFunctor (W₁ : MorphismProperty C₁)
    [L₁.IsLocalization W₁] [LF.IsLeftDerivedFunctor α W₁] [hLF : LF.CommShift A]
    (hα : NatTrans.CommShift α A) : adj.CommShift A := by
  have h : hLF = adj.leftAdjointCommShift A :=
    Functor.IsLeftDerivedFunctor.commShift_ext LF α W₁ A hLF _ hα
      (Adjunction.natTrans_commShift_of_unit_fac adjK adj α β hunit A)
  subst h
  exact adj.commShift_of_rightAdjoint A

end DerivedAdjunction

end CategoryTheory

/-! ### The derived adjunction on a ringed space -/

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u w₁ w₂

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

/-- The commutation of the derived pullback `Lf^*` with the shift as a total left derived functor,
`StacksDraft.PseudoCoherence.leftDerivedCommShift`, at arbitrary models of the derived
categories. Not an instance: it is a datum, and a consumer seats it with `letI`. -/
@[instance_reducible]
def derivedPullbackLeftDerivedCommShift : (derivedPullback f).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift (derivedPullback f)
    (derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) ℤ

/-- **The derived adjunction `Lf^* ⊣ Rf_*` commutes with the shift**, for an arbitrary morphism of
ringed spaces and arbitrary models of the derived categories. The commutation of `Lf^*` with the
shift is the one of a total left derived functor and that of `Rf_*` the one of a total right
derived functor.

The unit factorisation `derivedAdjunction_unit_fac` relates the derived unit to the unit of the
adjunction `K(f^*) ⊣ K(f_*)` on homotopy categories, which commutes with the shift, through the
counit of `Lf^*` and the unit of `Rf_*`, which commute with the shift for their derived
commutations; `CategoryTheory.Adjunction.commShift_of_isLeftDerivedFunctor` concludes. -/
theorem derivedAdjunction_commShift :
    letI := StacksDraft.PseudoCoherence.leftDerivedCommShift (derivedPullback f)
      (derivedPullbackComparison f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) ℤ
    letI := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
      (derivedPushforwardUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ℤ
    (derivedAdjunction f).CommShift ℤ :=
  by
  let := derivedPullbackLeftDerivedCommShift f
  let := Functor.IsRightDerivedFunctor.commShift _ (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso _ _) ℤ
  have := Functor.IsRightDerivedFunctor.natTrans_commShift _ (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso _ _) ℤ
  exact Adjunction.commShift_of_isLeftDerivedFunctor (homotopyPullbackPushforwardAdjunction f)
    (derivedAdjunction f) (derivedPullbackComparison f) (derivedPushforwardUnit f)
    (derivedAdjunction_unit_fac f) ℤ
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility _ _ _ ℤ)

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-! ### The quasi-coherent derived categories of a scheme -/

namespace Stacks.Duality

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On the unbounded derived categories of a morphism of schemes, the commutation of `Lf^*` with
the shift transported from `Rf_*` along the adjunction `Lf^* ⊣ Rf_*` is the left derived one. -/
theorem derivedAdjunction_leftAdjointCommShift_eq :
    (derivedAdjunction f).leftAdjointCommShift ℤ =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift
        f.toLRSHom.toShHom : (derivedPullback f).CommShift ℤ) := by
  let : (derivedPullback f).CommShift ℤ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift
      f.toLRSHom.toShHom
  have : (derivedAdjunction f).CommShift ℤ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_commShift
      f.toLRSHom.toShHom
  exact Adjunction.leftAdjointCommShift_eq _ ℤ

variable (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj K.obj)).IsQuasicoherent)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The commutation of the restricted `Lf^*` with the shift is induced by the left derived
one.** `commShift_quasiCoherentDerivedPullback` is obtained from the restricted adjunction
`Lf^* ⊣ Rf_*` on `D_QCoh`; it agrees with the commutation induced, through the fully faithful
inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, by the left derived commutation of the ambient `Lf^*`. The
ambient adjunction is compatible with the derived-functor shifts by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_commShift`, so its
restriction is compatible with the induced ones, and a left adjoint carries a unique commutation
with the shift compatible with a given adjunction. -/
theorem commShift_quasiCoherentDerivedPullback_eq :
    letI : (derivedPullback f).CommShift ℤ :=
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift
        f.toLRSHom.toShHom
    commShift_quasiCoherentDerivedPullback f hpull hpush =
      Functor.CommShift.ofComp (quasiCoherentDerivedPullbackCompιIso f hpull) ℤ := by
  let : (derivedPullback f).CommShift ℤ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift
      f.toLRSHom.toShHom
  have : (derivedAdjunction f).CommShift ℤ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_commShift
      f.toLRSHom.toShHom
  let := Functor.CommShift.ofComp (quasiCoherentDerivedPullbackCompιIso f hpull) ℤ
  have : (quasiCoherentDerivedAdjunction f hpull hpush).CommShift ℤ :=
    Adjunction.commShift_restrictFullyFaithful (derivedAdjunction f)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (quasiCoherentDerivedPullbackCompιIso f hpull)
      (DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush) ℤ
  exact Adjunction.leftAdjointCommShift_eq _ ℤ

end Stacks.Duality

end
