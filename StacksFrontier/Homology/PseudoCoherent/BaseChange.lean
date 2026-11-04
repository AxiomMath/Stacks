module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Shift.Opposite
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksFrontier.Homology.TorAmplitude.Comparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence under derived base change

Derived extension of scalars along a homomorphism `f : R → A` of commutative rings preserves
both `m`-pseudo-coherent and pseudo-coherent objects of the derived category (Stacks 0650). This
holds for the canonical functor `derivedExtensionScalars f`, with the source ring, the target
ring and the module carrier in three independent universes.

The same holds for any triangulated functor `baseChange : D(A) ⥤ D(B)` equipped with a
comparison map to termwise extension of scalars that makes it a total left derived functor of
extension of scalars.

## Main definitions

* `StacksDraft.PseudoCoherence.extendScalarsDerived`: the total left derived functor of
  extension of scalars, together with its counit `extendScalarsDerivedCounit` and its
  commutation with the shift `commShift_extendScalarsDerived`.
* `StacksDraft.PseudoCoherence.leftDerivedCommShift`: a total left derived functor commutes with
  the shift, and `StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility`: its counit is
  compatible with that commutation.
* `StacksDraft.PseudoCoherence.derivedExtensionScalars`: derived extension of scalars, for a
  source ring, a target ring and a module carrier in independent universes.

## Main results

* `StacksDraft.PseudoCoherence.isIso_baseChangeComparison_app_of_isKProjective`: the comparison
  map of a total left derived functor of extension of scalars is invertible at a K-projective
  complex.
* `StacksDraft.PseudoCoherence.isLE_baseChange_obj`: such a functor is right t-exact.
* `StacksDraft.PseudoCoherence.baseChange_preserves_pseudoCoherent`: such a functor, if it is
  triangulated, preserves pseudo-coherence.
* `StacksDraft.PseudoCoherence.extendScalarsDerived_preserves_pseudoCoherent`: the same for
  `extendScalarsDerived f`, assuming that it is triangulated.
* `StacksDraft.PseudoCoherence.ulift_preserves_pseudoCoherent`: raising the module universe
  preserves both forms of pseudo-coherence.
* `StacksDraft.PseudoCoherence.totalDerivedExtensionScalars_preserves_pseudoCoherent`:
  preservation by the unbounded derived extension-of-scalars functor of Stacks 064H, in the
  common module universe that the two rings force.
* `StacksDraft.PseudoCoherence.derivedExtensionScalars_preserves_pseudoCoherent`: preservation
  by `derivedExtensionScalars f`, for independent ring and carrier universes.

## Implementation notes

Both alternatives of the source's "respectively" statement are combined into a conjunction.

`derivedExtensionScalars f` is the exact universe lift followed by the unbounded derived
extension-of-scalars functor of Stacks 064H. Exact universe lifting preserves finite free
approximations, so no size hypothesis on the rings is needed.

Extension of scalars is only right exact, so `Functor.mapDerivedCategory`, which needs an exact
functor, does not apply, and a total left derived functor is used instead.

## References

* [Stacks Project, Tag 0650](https://stacks.math.columbia.edu/tag/0650)
* [Stacks Project, Tag 064H](https://stacks.math.columbia.edu/tag/064H)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.Pretriangulated HomologicalComplex

namespace StacksDraft.PseudoCoherence

universe u v w uR uA wR wA

-- This file is not yet migrated to `[HasDerivedCategory _]` arguments (pending a later batch of
-- that migration): its declarations about derived categories, among them `extendScalarsDerived`
-- with its counit and the statements about `IsPseudoCoherent` and `IsPseudoCoherentFrom`, are
-- made at the standard model that this local instance supplies. The exception is
-- `derivedExtensionScalars`, which takes its models as instance arguments.
attribute [local instance] HasDerivedCategory.standard

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-! ### Passing a right Kan universal property to the opposite categories -/

section Op

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]



attribute [local simp] opCounit_app



end Op

/-! ### A total left derived functor commutes with the shift -/

section Shift

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : L ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W]
  [LF.IsLeftDerivedFunctor α W]
  (M : Type*) [AddGroup M] [HasShift C M] [HasShift D M] [HasShift H M]
  [W.IsCompatibleWithShift M] [F.CommShift M] [L.CommShift M]

/-- The commutation with the shift of a total left derived functor, obtained from
`Functor.IsRightDerivedFunctor.commShift` in the opposite categories. -/
@[instance_reducible]
public noncomputable def leftDerivedCommShift : LF.CommShift M := by
  let Wo : MorphismProperty (OppositeShift C M) := W.op
  let Lo := OppositeShift.functor M L
  let Fo := OppositeShift.functor M F
  let LFo := OppositeShift.functor M LF
  let αo : Fo ⟶ Lo ⋙ LFo := NatTrans.op α
  have : Lo.IsLocalization Wo := inferInstanceAs (L.op.IsLocalization W.op)
  have : Wo.IsCompatibleWithShift M := ⟨fun b => by
    ext X Y f
    exact MorphismProperty.IsCompatibleWithShift.iff W f.unop b⟩
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α W
  have : LFo.IsRightDerivedFunctor αo Wo := ⟨isLeftKanExtension_op LF α⟩
  let : LFo.CommShift M := Functor.IsRightDerivedFunctor.commShift LFo αo Wo M
  exact Functor.commShiftUnop M LF

/-- The counit of a total left derived functor is compatible with `leftDerivedCommShift`. -/
public lemma leftDerivedCommShift_compatibility :
    let := leftDerivedCommShift LF α W M
    NatTrans.CommShift α M := by
  let Wo : MorphismProperty (OppositeShift C M) := W.op
  let Lo := OppositeShift.functor M L
  let Fo := OppositeShift.functor M F
  let LFo := OppositeShift.functor M LF
  let αo : Fo ⟶ Lo ⋙ LFo := NatTrans.op α
  have : Lo.IsLocalization Wo := inferInstanceAs (L.op.IsLocalization W.op)
  have : Wo.IsCompatibleWithShift M := ⟨fun b => by
    ext X Y f
    exact MorphismProperty.IsCompatibleWithShift.iff W f.unop b⟩
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α W
  have : LFo.IsRightDerivedFunctor αo Wo := ⟨isLeftKanExtension_op LF α⟩
  let : LFo.CommShift M := Functor.IsRightDerivedFunctor.commShift LFo αo Wo M
  let := leftDerivedCommShift LF α W M
  constructor
  intro b
  ext X
  have h : ((LF.commShiftIso b).inv.app (L.obj X) ≫
        LF.map ((L.commShiftIso b).inv.app X)) ≫ α.app (X⟦b⟧) =
      (α.app X)⟦b⟧' ≫ (F.commShiftIso b).inv.app X :=
    congrArg Quiver.Hom.unop
      (Functor.IsRightDerivedFunctor.comp_map_commShiftIso_hom_app LFo αo Wo M b
        (Opposite.op X))
  dsimp
  rw [Functor.commShiftIso_comp_hom_app]
  rw [← cancel_epi (LF.map ((L.commShiftIso b).inv.app X)),
    ← cancel_epi ((LF.commShiftIso b).inv.app (L.obj X))]
  simp only [Category.assoc, ← LF.map_comp_assoc, Iso.inv_hom_id_app,
    LF.map_id, Category.id_comp]
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Functor.comp_obj,
    Category.comp_id] using
    (h =≫ (F.commShiftIso b).hom.app X).symm

end Shift

/-! ### Projective covers of modules -/

variable {A : Type u} [CommRing A]

private instance hasExactColimitsOfShapeNat :
    HasExactColimitsOfShape ℕ (ModuleCat.{u} A) :=
  letI : AB5OfSize.{0, 0, u, u + 1} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{0, 0, u, u} AddCommGrpCat.{u}
  HasExactColimitsOfShape.domain_of_functor ℕ
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})

/-- The projective modules, as a class of objects of `ModuleCat A`. -/
private abbrev projectiveObjects (A : Type u) [CommRing A] :
    ObjectProperty (ModuleCat.{u} A) :=
  fun X => Projective X

private instance : (projectiveObjects A).ContainsZero :=
  ⟨ModuleCat.of A (Fin 0 → A), ModuleCat.isZero_of_subsingleton _, inferInstance⟩

set_option maxHeartbeats 2000000 in
-- Instance search for `Projective (X ⊞ Y)` unfolds the `ModuleCat` biproduct, which is slow.
/-- The class of projective modules is closed under binary biproducts. -/
private lemma projectiveObjects_biprod (X Y : ModuleCat.{u} A)
    (hX : projectiveObjects A X) (hY : projectiveObjects A Y) :
    projectiveObjects A (X ⊞ Y) := by
  have := hX
  have := hY
  exact inferInstanceAs (Projective (X ⊞ Y))

/-- Every module is a quotient of a projective module. -/
private lemma projectiveObjects_cover (X : ModuleCat.{u} A) :
    ∃ (Y : ModuleCat.{u} A) (_ : projectiveObjects A Y) (p : Y ⟶ X), Epi p :=
  ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩

/-- An object of `D^{≤ a}(A)` is represented by a complex of projective modules vanishing in
degrees above `a`: this is Stacks 05T7 for the class of projective modules. -/
private lemma exists_projective_representative
    (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ) [K.IsLE a] :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ i, Projective (P.X i)) ∧ P.IsStrictlyLE a ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨L, e, hL⟩ := ‹K.IsLE a›
  obtain ⟨P, g, hq, hP, hPa⟩ := (CochainComplex.exists_quasiIso_prop
    (projectiveObjects A) projectiveObjects_cover a).2 L
  have := hq
  exact ⟨P, hP, hPa, ⟨e ≪≫ (asIso (DerivedCategory.Q.map g)).symm⟩⟩

/-! ### The total left derived functor of extension of scalars -/

variable {B : Type u} [CommRing B]

private noncomputable instance isLeftAdjoint_extendScalars (f : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint

/-- Extension of scalars along a ring homomorphism is an additive functor. -/
public instance additive_extendScalars (f : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- Extension of scalars turns a bounded above acyclic complex of projective modules into an
acyclic complex. -/
private lemma acyclic_extendScalars_of_projective (f : A →+* B) (a : ℤ)
    (L : CochainComplex (ModuleCat.{u} A) ℤ) (hLE : L.IsStrictlyLE a)
    (hproj : ∀ n : ℤ, Projective (L.X n)) (hac : L.Acyclic) :
    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  have := hLE
  have := hproj
  have : L.IsKProjective := CochainComplex.isKProjective_of_projective L a
  have hz : IsZero ((HomotopyCategory.quotient (ModuleCat.{u} A)
      (ComplexShape.up ℤ)).obj L) := by
    rw [IsZero.iff_id_eq_zero]
    exact CochainComplex.IsKProjective.leftOrthogonal L (𝟙 _)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hac)
  have hz2 := ((ModuleCat.extendScalars.{u, u, u} f).mapHomotopyCategory
    (ComplexShape.up ℤ)).map_isZero hz
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} B)).prop_of_isZero hz2

/-- Extension of scalars read on the homotopy category, followed by the localization to the
derived category. -/
private noncomputable abbrev extendScalarsHomotopy (f : A →+* B) :
    HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  (ModuleCat.extendScalars.{u, u, u} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The left derived functor of extension of scalars along `Qh : K(A) ⥤ D(A)` is defined at every
object (Stacks 0794). -/
private instance hasPointwiseLeftDerivedFunctor_extendScalars (f : A →+* B) :
    (extendScalarsHomotopy f).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
  CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    _ (projectiveObjects A) projectiveObjects_biprod projectiveObjects_cover
    (fun a L hLE hP hac => acyclic_extendScalars_of_projective f a L hLE hP hac)

/-- The total left derived functor of extension of scalars, on the derived category. -/
public noncomputable def extendScalarsDerived (f : A →+* B) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  (extendScalarsHomotopy f).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))

/-- Its counit, on the homotopy category. -/
private noncomputable def extendScalarsDerivedCounitHomotopy (f : A →+* B) :
    DerivedCategory.Qh ⋙ extendScalarsDerived f ⟶ extendScalarsHomotopy f :=
  (extendScalarsHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))

private instance isLeftDerivedFunctor_extendScalarsDerivedCounitHomotopy (f : A →+* B) :
    (extendScalarsDerived f).IsLeftDerivedFunctor (extendScalarsDerivedCounitHomotopy f)
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := by
  dsimp only [extendScalarsDerived, extendScalarsDerivedCounitHomotopy]
  infer_instance

/-- Extension of scalars read on the homotopy category, precomposed with the homotopy quotient,
is termwise extension of scalars followed by the localization. -/
private noncomputable def quotientCompExtendScalarsIso (f : A →+* B) :
    HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ) ⋙
        extendScalarsHomotopy f ≅
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerRight
      ((ModuleCat.extendScalars.{u, u, u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator
      ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (ModuleCat.{u} B) (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B))

/-- The counit of `extendScalarsDerived f`, on complexes. -/
public noncomputable def extendScalarsDerivedCounit (f : A →+* B) :
    DerivedCategory.Q ⋙ extendScalarsDerived f ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv
      (extendScalarsDerived f) ≫
    whiskerLeft (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (extendScalarsDerivedCounitHomotopy f) ≫ (quotientCompExtendScalarsIso f).hom

/-- `extendScalarsDerived f`, with the counit `extendScalarsDerivedCounit f`, is a total left
derived functor of termwise extension of scalars with respect to quasi-isomorphisms. -/
public instance isLeftDerivedFunctor_extendScalarsDerivedCounit (f : A →+* B) :
    (extendScalarsDerived f).IsLeftDerivedFunctor (extendScalarsDerivedCounit f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
  StacksDraft.TorAmplitude.isLeftDerivedFunctor_of_homotopyCategory _
    (extendScalarsHomotopy f)
    (quotientCompExtendScalarsIso f) (extendScalarsDerived f)
    (extendScalarsDerivedCounitHomotopy f) (extendScalarsDerivedCounit f) (by
      ext X
      dsimp only [extendScalarsDerivedCounit, NatTrans.comp_app, whiskerRight_app,
        whiskerLeft_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      simp)

/-- The total left derived functor of extension of scalars commutes with the shift: this is
`leftDerivedCommShift` applied to its counit. -/
public noncomputable instance commShift_extendScalarsDerived (f : A →+* B) :
    (extendScalarsDerived f).CommShift ℤ :=
  leftDerivedCommShift (extendScalarsDerived f) (extendScalarsDerivedCounit f)
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) ℤ

/-- The counit of the total left derived functor of extension of scalars, on the homotopy
category, is invertible at a K-projective complex. -/
private lemma isIso_extendScalarsDerivedCounitHomotopy_app (f : A →+* B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKProjective] :
    IsIso ((extendScalarsDerivedCounitHomotopy f).app
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj P)) := by
  have hpt := hasPointwiseLeftDerivedFunctor_extendScalars f
  have hptw : (RightExtension.mk (extendScalarsDerived f)
      (extendScalarsDerivedCounitHomotopy f)).IsPointwiseRightKanExtension :=
    Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
      (extendScalarsDerived f) (extendScalarsDerivedCounitHomotopy f)
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
  have hat := hptw (DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj P))
  have h := hat.isIso_π_app_of_isInitial _
    (StacksDraft.TorAmplitude.isInitialStructuredArrowMkId P)
  simpa using h

/-- The counit `extendScalarsDerivedCounit f` is invertible at a K-projective complex. -/
private lemma isIso_extendScalarsDerivedCounit_app (f : A →+* B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKProjective] :
    IsIso ((extendScalarsDerivedCounit f).app P) := by
  have := isIso_extendScalarsDerivedCounitHomotopy_app f P
  dsimp only [extendScalarsDerivedCounit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  infer_instance

/-! ### An arbitrary derived base change -/

variable {baseChange : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B)}

/-- The comparison map of a total left derived functor of extension of scalars is invertible at a
K-projective complex. -/
public theorem isIso_baseChangeComparison_app_of_isKProjective (f : A →+* B)
    (comparison : DerivedCategory.Q ⋙ baseChange ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (isLeftDerived : baseChange.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKProjective] :
    IsIso (comparison.app P) := by
  have := isLeftDerived
  have hβ : IsIso ((extendScalarsDerivedCounit f).app P) :=
    isIso_extendScalarsDerivedCounit_app f P
  have hiso : IsIso ((Functor.leftDerivedNatTrans (extendScalarsDerived f) baseChange
      (extendScalarsDerivedCounit f) comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (𝟙 _)).app (DerivedCategory.Q.obj P)) := by
    have h : IsIso ((Functor.leftDerivedNatIso (extendScalarsDerived f) baseChange
        (extendScalarsDerivedCounit f) comparison
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
        (Iso.refl _)).hom.app (DerivedCategory.Q.obj P)) := inferInstance
    simpa using h
  have hkey : IsIso ((Functor.leftDerivedNatTrans (extendScalarsDerived f) baseChange
      (extendScalarsDerivedCounit f) comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (𝟙 _)).app (DerivedCategory.Q.obj P) ≫ comparison.app P) := by
    rw [Functor.leftDerivedNatTrans_app]
    simpa using hβ
  exact IsIso.of_isIso_comp_left
    ((Functor.leftDerivedNatTrans (extendScalarsDerived f) baseChange
      (extendScalarsDerivedCounit f) comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (𝟙 _)).app (DerivedCategory.Q.obj P)) (comparison.app P)

/-- Termwise extension of scalars preserves the property of vanishing above a given degree. -/
private instance isStrictlyLE_mapHomologicalComplex (f : A →+* B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [P.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} f)
    (P.isZero_of_isStrictlyLE b i hi)

/-- A total left derived functor of extension of scalars is right t-exact: it maps `D^{≤ b}(A)`
into `D^{≤ b}(B)`. -/
public theorem isLE_baseChange_obj (f : A →+* B)
    (comparison : DerivedCategory.Q ⋙ baseChange ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (isLeftDerived : baseChange.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} A)) (b : ℤ) [K.IsLE b] :
    (baseChange.obj K).IsLE b := by
  obtain ⟨P, hproj, hPLE, ⟨e⟩⟩ := exists_projective_representative K b
  have := hPLE
  have := hproj
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  have hc : IsIso (comparison.app P) :=
    isIso_baseChangeComparison_app_of_isKProjective f comparison isLeftDerived P
  have hSLE := isStrictlyLE_mapHomologicalComplex f P b
  have := hSLE
  have hQLE : (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).IsLE b := inferInstance
  have e₂ : baseChange.obj K ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
    baseChange.mapIso e ≪≫ asIso (comparison.app P)
  have := hQLE
  exact DerivedCategory.TStructure.t.isLE_of_iso e₂.symm b

/-! ### The cone of an approximation -/

/-- The cone of a morphism which is an isomorphism on cohomology above `m` and surjective in
degree `m` lies in `D^{≤ m - 1}`. -/
private lemma cone_isLE_of_approximation {R : Type uR} [CommRing R]
    {E K : DerivedCategory (ModuleCat.{v} R)} {m : ℤ} (α : E ⟶ K)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map α)) :
    ∃ (C : DerivedCategory (ModuleCat.{v} R)) (β : K ⟶ C) (γ : C ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang _ ∧ C.IsLE (m - 1) := by
  obtain ⟨C, β, γ, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α β γ
  refine ⟨C, β, γ, hT, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hi' : m ≤ i := by omega
  have hαepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α) := by
    rcases hi'.eq_or_lt with rfl | hlt
    · exact hepi
    · exact @IsIso.epi_of_iso _ _ _ _ _ (hiso i hlt)
  have hβ : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂ = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hαepi
  have hδα : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT i (i + 1) rfl).1
    exact @IsIso.mono_of_iso _ _ _ _ _ (hiso (i + 1) (by omega))
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_of_both_zeros
    hβ hδα

/-- Conversely, the first map of a distinguished triangle whose third object lies in
`D^{≤ m - 1}` is an isomorphism on cohomology above `m` and surjective in degree `m`. -/
private lemma approximation_of_triangle_isLE {R : Type uR} [CommRing R]
    {T : Triangle (DerivedCategory (ModuleCat.{v} R))}
    (hT : T ∈ distTriang _) {m : ℤ} [T.obj₃.IsLE (m - 1)] :
    (∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁)) ∧
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map T.mor₁) := by
  constructor
  · intro i hi
    have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁) := by
      rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) i (by omega)).eq_of_tgt _ _
    have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁) := by
      rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT (i - 1) i (by omega)]
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) (i - 1) (by omega)).eq_of_src _ _
    have := hmono
    have := hepi
    exact isIso_of_mono_of_epi _
  · rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT m]
    exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) m (by omega)).eq_of_tgt _ _

/-! ### Preservation of pseudo-coherence -/

/-- Termwise extension of scalars of a bounded complex of finite free modules is a bounded
complex of finite free modules. -/
private lemma isBoundedFiniteFree_mapHomologicalComplex {R : Type uR} {S : Type uA}
    [CommRing R] [CommRing S] (f : R →+* S)
    [(ModuleCat.extendScalars.{uR, uA, w} f).IsLeftAdjoint]
    {E : CochainComplex (ModuleCat.{w} R) ℤ} (hE : IsBoundedFiniteFree E) :
    IsBoundedFiniteFree
      (((ModuleCat.extendScalars.{uR, uA, w} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E) := by
  let : Algebra R S := ((algebraMap S S).comp f).toAlgebra
  obtain ⟨a, ha⟩ := hE.lowerBound
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩, fun i => ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero (ModuleCat.extendScalars.{uR, uA, w} f)
      (E.isZero_of_isStrictlyGE a i hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (ModuleCat.extendScalars.{uR, uA, w} f)
      (E.isZero_of_isStrictlyLE b i hi)
  · have := (hE.finiteFree i).1
    have := (hE.finiteFree i).2
    constructor
    · change Module.Finite S (TensorProduct R S (E.X i))
      infer_instance
    · change Module.Free S (TensorProduct R S (E.X i))
      infer_instance

/-- The terms of a bounded complex of finite free modules are projective. -/
private lemma projective_X_of_isBoundedFiniteFree {R : Type uR} [Ring R]
    {E : CochainComplex (ModuleCat.{w} R) ℤ} (hE : IsBoundedFiniteFree E) (i : ℤ) :
    Projective (E.X i) := by
  have := (hE.finiteFree i).2
  infer_instance

/-- A triangulated right t-exact functor `D(R) ⥤ D(S)` that carries each bounded complex of
finite free modules to such a complex up to isomorphism preserves `m`-pseudo-coherent objects for
every integer `m`, and it preserves pseudo-coherent objects. -/
private lemma preserves_pseudoCoherent_of_model {R : Type uR} {S : Type uA} [CommRing R]
    [CommRing S] (F : DerivedCategory (ModuleCat.{w} R) ⥤ DerivedCategory (ModuleCat.{v} S))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hLE : ∀ (C : DerivedCategory (ModuleCat.{w} R)) (b : ℤ), C.IsLE b → (F.obj C).IsLE b)
    (hmodel : ∀ E : CochainComplex (ModuleCat.{w} R) ℤ, IsBoundedFiniteFree E →
      ∃ E' : CochainComplex (ModuleCat.{v} S) ℤ, IsBoundedFiniteFree E' ∧
        Nonempty (DerivedCategory.Q.obj E' ≅ F.obj (DerivedCategory.Q.obj E)))
    (K : DerivedCategory (ModuleCat.{w} R)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m → IsPseudoCoherentFrom (F.obj K) m) ∧
      (IsPseudoCoherent K → IsPseudoCoherent (F.obj K)) := by
  have hfrom : ∀ m : ℤ, IsPseudoCoherentFrom K m → IsPseudoCoherentFrom (F.obj K) m := by
    intro m hK
    obtain ⟨E, hE, α, hiso, hepi⟩ := hK
    obtain ⟨C, β, γ, hT, hcone⟩ := cone_isLE_of_approximation α hiso hepi
    obtain ⟨E', hE', ⟨e⟩⟩ := hmodel E hE
    have := hcone
    have : (F.mapTriangle.obj (Triangle.mk α β γ)).obj₃.IsLE (m - 1) := hLE C (m - 1) hcone
    obtain ⟨hiso', hepi'⟩ :=
      approximation_of_triangle_isLE (F.map_distinguished _ hT) (m := m)
    refine ⟨E', hE', e.hom ≫ F.map α, fun i hi => ?_, ?_⟩
    · have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).map (F.map α)) :=
        hiso' i hi
      rw [Functor.map_comp]
      infer_instance
    · have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) m).map (F.map α)) := hepi'
      rw [Functor.map_comp]
      infer_instance
  exact ⟨hfrom, fun hK => (pseudoCoherent_iff_all (F.obj K)).2 fun m =>
    hfrom m ((pseudoCoherent_iff_all K).1 hK m)⟩

/-- Let `f : A → B` be a homomorphism of commutative rings and let `baseChange` be a triangulated
functor `D(A) ⥤ D(B)` with a comparison map to termwise extension of scalars that makes it a
total left derived functor of extension of scalars. Then `baseChange` preserves `m`-pseudo-coherent
objects for every integer `m`, and it preserves pseudo-coherent objects. -/
public theorem baseChange_preserves_pseudoCoherent (f : A →+* B)
    (comparison : DerivedCategory.Q ⋙ baseChange ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (isLeftDerived : baseChange.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    [baseChange.CommShift ℤ] [baseChange.IsTriangulated]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m →
        IsPseudoCoherentFrom (baseChange.obj K) m) ∧
      (IsPseudoCoherent K → IsPseudoCoherent (baseChange.obj K)) := by
  refine preserves_pseudoCoherent_of_model baseChange
    (fun C b _ => isLE_baseChange_obj f comparison isLeftDerived C b) (fun E hE => ?_) K
  obtain ⟨b, hb⟩ := hE.upperBound
  have := hb
  have := projective_X_of_isBoundedFiniteFree hE
  have : E.IsKProjective := CochainComplex.isKProjective_of_projective E b
  have := isIso_baseChangeComparison_app_of_isKProjective f comparison isLeftDerived E
  exact ⟨_, isBoundedFiniteFree_mapHomologicalComplex f hE, ⟨(asIso (comparison.app E)).symm⟩⟩

/-- Let `f : A → B` be a homomorphism of commutative rings. If the total left derived functor
`extendScalarsDerived f` of extension of scalars is triangulated, then it preserves
`m`-pseudo-coherent objects for every integer `m`, and it preserves pseudo-coherent objects. -/
public theorem extendScalarsDerived_preserves_pseudoCoherent (f : A →+* B)
    [(extendScalarsDerived f).IsTriangulated] (K : DerivedCategory (ModuleCat.{u} A)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m →
        IsPseudoCoherentFrom ((extendScalarsDerived f).obj K) m) ∧
      (IsPseudoCoherent K → IsPseudoCoherent ((extendScalarsDerived f).obj K)) :=
  baseChange_preserves_pseudoCoherent f (extendScalarsDerivedCounit f)
    (isLeftDerivedFunctor_extendScalarsDerivedCounit f) K

/-! ### Stacks 0650 at the canonical derived extension of scalars -/

/-- Raising the module universe preserves both forms of pseudo-coherence: `ULift` is exact and
carries finite free modules to finite free modules. -/
public theorem ulift_preserves_pseudoCoherent {R : Type uR} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m →
      IsPseudoCoherentFrom ((ModuleCat.uliftFunctor.{w} R).mapDerivedCategory.obj K) m) ∧
      (IsPseudoCoherent K →
        IsPseudoCoherent ((ModuleCat.uliftFunctor.{w} R).mapDerivedCategory.obj K)) := by
  apply exactFunctor_preserves_pseudoCoherent
  intro M hfinite hfree
  have := hfinite
  have := hfree
  show Module.Finite R (ULift M) ∧ Module.Free R (ULift M)
  exact ⟨inferInstance, inferInstance⟩

open CochainComplex.DerivedExtensionScalars in
/-- The unbounded derived extension-of-scalars functor `- ⊗ᴸ_R A` of Stacks 064H, in the common
module universe `max uA uR v`, preserves `m`-pseudo-coherent objects for every integer `m`, and
it preserves pseudo-coherent objects. -/
public theorem totalDerivedExtensionScalars_preserves_pseudoCoherent
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (K : DerivedCategory (ModuleCat.{max uA (max uR v)} R)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m →
      IsPseudoCoherentFrom ((totalDerivedExtensionScalars.{uR, uA, v} f).functor.obj K) m) ∧
      (IsPseudoCoherent K →
        IsPseudoCoherent ((totalDerivedExtensionScalars.{uR, uA, v} f).functor.obj K)) := by
  let : Algebra R A := ((algebraMap A A).comp f).toAlgebra
  have : (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} f).isLeftAdjoint
  let D := totalDerivedExtensionScalars.{uR, uA, v} f
  refine preserves_pseudoCoherent_of_model D.functor (fun C b _ => D.maps_t_le C b)
    (fun E hE => ?_) K
  obtain ⟨n, hn⟩ := hE.upperBound
  have hQE : DerivedCategory.TStructure.t.minus (DerivedCategory.Q.obj E) :=
    ⟨n, E, Iso.refl _, hn⟩
  obtain ⟨e⟩ := derivedExtensionScalars_projective_model f E hQE
    ⟨n, (CochainComplex.isStrictlyLE_iff E n).1 hn⟩ (projective_X_of_isBoundedFiniteFree hE)
  let e' : D.functor.obj (DerivedCategory.Q.obj E) ≅ (extensionOfScalarsComplex f).obj E :=
    (D.extendsBounded.app ⟨DerivedCategory.Q.obj E, hQE⟩).symm ≪≫ e
  exact ⟨_, isBoundedFiniteFree_mapHomologicalComplex f hE,
    ⟨(Iso.refl ((extensionOfScalarsComplex f).obj E) : _ ≅ _) ≪≫ e'.symm⟩⟩

open CochainComplex.DerivedExtensionScalars in
/-- Derived extension of scalars along `f : R →+* A` for a source ring, a target ring and a
module carrier in three independent universes. The exact universe lift raising the carrier above
both ring universes is performed inside the construction, so no size hypothesis is needed.

The derived categories of `R`-modules and of `A`-modules are taken at arbitrary models, given as
instance arguments; the intermediate derived category `DerivedCategory (ModuleCat.{max uA uR v} R)`
of the universe lift uses the standard model. -/
@[expose, sga "6 I 2.16.1" "a), special case"] public noncomputable def derivedExtensionScalars
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{v} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uA uR v} A)] :
    DerivedCategory (ModuleCat.{v} R) ⥤
      DerivedCategory (ModuleCat.{max uA uR v} A) :=
  letI : HasDerivedCategory (ModuleCat.{max uA uR v} R) := HasDerivedCategory.standard _
  -- The universes of the lift are pinned: with the intermediate model a local instance, instance
  -- search would otherwise solve the lift's source universe against it and lift the wrong side.
  (ModuleCat.uliftFunctor.{max uA uR, v, uR} R).mapDerivedCategory ⋙
    (totalDerivedExtensionScalars.{uR, uA, v} f).functor

/-- Derived extension of scalars along a homomorphism `f : R →+* A` of commutative rings
preserves `m`-pseudo-coherent objects of the derived category for every integer `m`, and it
preserves pseudo-coherent objects. The source ring, the target ring and the module carrier live
in three independent universes. -/
@[stacks 0650, sga "6 I 2.13" "special case"]
public theorem derivedExtensionScalars_preserves_pseudoCoherent
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (K : DerivedCategory (ModuleCat.{v} R)) :
    (∀ m : ℤ, IsPseudoCoherentFrom K m →
      IsPseudoCoherentFrom ((derivedExtensionScalars f).obj K) m) ∧
      (IsPseudoCoherent K → IsPseudoCoherent ((derivedExtensionScalars f).obj K)) := by
  have hL : (∀ m : ℤ, IsPseudoCoherentFrom K m →
        IsPseudoCoherentFrom
          ((ModuleCat.uliftFunctor.{max uA uR} R).mapDerivedCategory.obj K) m) ∧
      (IsPseudoCoherent K →
        IsPseudoCoherent
          ((ModuleCat.uliftFunctor.{max uA uR} R).mapDerivedCategory.obj K)) :=
    ulift_preserves_pseudoCoherent K
  have hD := totalDerivedExtensionScalars_preserves_pseudoCoherent f
    ((ModuleCat.uliftFunctor.{max uA uR} R).mapDerivedCategory.obj K)
  exact ⟨fun m h ↦ hD.1 m (hL.1 m h), fun h ↦ hD.2 (hL.2 h)⟩

end StacksDraft.PseudoCoherence
