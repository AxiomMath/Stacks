module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Deriving an adjunction whose left adjoint is exact

Let `G ⊣ F` be an adjunction of additive functors between abelian categories with `G` exact and
the source of `F` Grothendieck abelian. Then the induced functors on unbounded derived
categories are again adjoint: `G` needs no deriving, because an exact functor inverts
quasi-isomorphisms, and `F` is replaced by any right derived functor of it.

The adjunction is produced by [Stacks, Tag 09T5] in the form
`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`,
which asks for the derived functors to be given pointwise by essentially constant ind- and
pro-systems. For the right derived functor that is supplied by a K-injective resolution, which
is terminal among quasi-isomorphisms out of a complex; for the exact left adjoint the system is
constant, every morphism in it being inverted.

Because [Stacks, Tag 09T5] localizes the *homotopy* category rather than the category of cochain
complexes, a right derived functor given on cochain complexes is first transported to one given
on the homotopy category; that is
`Stacks.DerivedAdjunction.rightDerived_transfer_homotopy`.

## Main definitions

* `Stacks.DerivedAdjunction.derivedLocalizationHomotopy`: a localization of the homotopy category
  at the quasi-isomorphisms with values in a prescribed model of the derived category.
* `Stacks.DerivedAdjunction.rightDerivedUnitOnHomotopy`: the derivation unit of a right derived
  functor, transported from cochain complexes to the homotopy category.
* `Stacks.DerivedAdjunction.exactDerivedLeftFunctor`: the functor on derived categories induced
  by an exact functor, with values in a prescribed model.
* `Stacks.DerivedAdjunction.derivedAdjunctionOfExactLeft`: the derived adjunction.

## Main results

* `Stacks.DerivedAdjunction.rightDerived_transfer_homotopy`: a right derived functor along the
  localization of cochain complexes is one along the localization of the homotopy category.
* `Stacks.DerivedAdjunction.derivedAdjunctionOfExactLeft`: **the derived functors of an adjoint
  pair with exact left adjoint are adjoint.**

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.DerivedAdjunction

/-! ### Transporting a right derived functor to the homotopy category -/

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]

/-- The localization of the homotopy category at the quasi-isomorphisms, with values in a
prescribed model `Q` of the derived category: `DerivedCategory.Qh` followed by the canonical
equivalence between the two models. -/
public noncomputable def derivedLocalizationHomotopy
    (Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    [Q.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  DerivedCategory.Qh ⋙
    (Localization.uniq (DerivedCategory.Q (C := A)) Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor

/-- `derivedLocalizationHomotopy Q` is a localization of the homotopy category at the
quasi-isomorphisms, being `DerivedCategory.Qh` followed by an equivalence. -/
public instance derivedLocalizationHomotopy_isLocalization
    (Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    [Q.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    (derivedLocalizationHomotopy Q).IsLocalization
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.IsLocalization.of_equivalence_target
    (DerivedCategory.Qh (C := A))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (derivedLocalizationHomotopy Q)
    (Localization.uniq (DerivedCategory.Q (C := A)) Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))) (Iso.refl _)

/-- Degreewise application of an additive functor, followed by the localization of the homotopy
category, agrees on cochain complexes with degreewise application followed by the localization
of complexes. -/
public noncomputable def rightDerivedSourceIso
    [CategoryWithHomology A] [CategoryWithHomology B] (F : A ⥤ B) [F.Additive] :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)

/-- `derivedLocalizationHomotopy Q` restricted to cochain complexes is `Q`. -/
public noncomputable def derivedLocalizationHomotopyQuotientIso
    (Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    [Q.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy Q ≅ Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      (Localization.uniq (DerivedCategory.Q (C := A)) Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor ≪≫
    Localization.compUniqFunctor (DerivedCategory.Q (C := A)) Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- Degreewise application of an additive functor, followed by a prescribed localization of the
target homotopy category, agrees on cochain complexes with the corresponding composite of
localizations of complexes. -/
public noncomputable def rightDerivedSourceModelIso
    [CategoryWithHomology A] [CategoryWithHomology B] (F : A ⥤ B) [F.Additive]
    (Q : CochainComplex B ℤ ⥤ DerivedCategory B)
    [Q.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))] :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy Q ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedSourceIso F)
      (Localization.uniq (DerivedCategory.Q (C := B)) Q
        (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Localization.compUniqFunctor
      (DerivedCategory.Q (C := B)) Q
      (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)))

/-- The derivation unit of a right derived functor, transported from the localization of cochain
complexes to the localization of the homotopy category. -/
public noncomputable def rightDerivedUnitOnHomotopy
    [CategoryWithHomology A] [CategoryWithHomology B] (F : A ⥤ B) [F.Additive]
    (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
    [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
    [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QTarget ⟶
      derivedLocalizationHomotopy QSource ⋙ R :=
  Quotient.natTransLift _
    ((rightDerivedSourceModelIso F QTarget).hom ≫ α ≫
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (derivedLocalizationHomotopyQuotientIso QSource) R).inv)

/-! ### The transfer of a right derived functor to the homotopy category -/

section Transfer

variable [CategoryWithHomology A] [CategoryWithHomology B] (F : A ⥤ B) [F.Additive]
  (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
  [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R)

/-- The comparison `K(A) ⋙ (L ⋙ T) ≅ QSource ⋙ T` for a functor `T` out of the derived
category, coming from the identification of `derivedLocalizationHomotopy QSource` on cochain
complexes with `QSource`. -/
private noncomputable def transferTargetIso (T : DerivedCategory A ⥤ DerivedCategory B) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (derivedLocalizationHomotopy QSource ⋙ T) ≅ QSource ⋙ T :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedLocalizationHomotopyQuotientIso QSource) T

omit [CategoryWithHomology B] in
private lemma transferTargetIso_hom_app (T : DerivedCategory A ⥤ DerivedCategory B)
    (K : CochainComplex A ℤ) :
    (transferTargetIso QSource T).hom.app K =
      T.map ((derivedLocalizationHomotopyQuotientIso QSource).hom.app K) := by
  simp [transferTargetIso]

omit [CategoryWithHomology B] in
private lemma transferTargetIso_inv_app (T : DerivedCategory A ⥤ DerivedCategory B)
    (K : CochainComplex A ℤ) :
    (transferTargetIso QSource T).inv.app K =
      T.map ((derivedLocalizationHomotopyQuotientIso QSource).inv.app K) := by
  simp [transferTargetIso]

/-- A left extension of degreewise `F` along the localization of the homotopy category, read as
a left extension along the localization of cochain complexes. -/
private noncomputable def transferExtension
    (e : LeftExtension (derivedLocalizationHomotopy QSource)
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QTarget)) :
    LeftExtension QSource (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget) :=
  LeftExtension.mk e.right ((rightDerivedSourceModelIso F QTarget).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ)) e.hom ≫
    (transferTargetIso QSource e.right).hom)

/-- The structure map of `transferExtension`, read on a cochain complex. -/
private lemma transferExtension_hom_app
    (e : LeftExtension (derivedLocalizationHomotopy QSource)
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QTarget))
    (K : CochainComplex A ℤ) :
    (transferExtension F QSource QTarget e).hom.app K =
      (rightDerivedSourceModelIso F QTarget).inv.app K ≫
        e.hom.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        e.right.map ((derivedLocalizationHomotopyQuotientIso QSource).hom.app K) := by
  have h : (transferExtension F QSource QTarget e).hom.app K =
      (rightDerivedSourceModelIso F QTarget).inv.app K ≫
        e.hom.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        (transferTargetIso QSource e.right).hom.app K := rfl
  rw [h, transferTargetIso_hom_app]

/-- The transported derivation unit, read on a cochain complex. -/
private lemma rightDerivedUnitOnHomotopy_app (K : CochainComplex A ℤ) :
    (rightDerivedUnitOnHomotopy F QSource QTarget R α).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (rightDerivedSourceModelIso F QTarget).hom.app K ≫ α.app K ≫
        R.map ((derivedLocalizationHomotopyQuotientIso QSource).inv.app K) := by
  have h : (rightDerivedUnitOnHomotopy F QSource QTarget R α).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (rightDerivedSourceModelIso F QTarget).hom.app K ≫ α.app K ≫
        (transferTargetIso QSource R).inv.app K := rfl
  rw [h, transferTargetIso_inv_app QSource R K]

variable [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- `R` with its derivation unit is initial among left extensions of degreewise `F` along
`QSource`. -/
private noncomputable def transferInitial : (LeftExtension.mk R α).IsUniversal :=
  have : R.IsLeftKanExtension α :=
    (Functor.isRightDerivedFunctor_iff_isLeftKanExtension R α
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).mp inferInstance
  R.isUniversalOfIsLeftKanExtension α

/-- The map out of `R` induced by a left extension along the localization of the homotopy
category. -/
private noncomputable def transferDesc
    (e : LeftExtension (derivedLocalizationHomotopy QSource)
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QTarget)) :
    R ⟶ e.right :=
  (transferInitial F QSource QTarget R α).desc (transferExtension F QSource QTarget e)

omit [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] in
/-- A map out of `R` factors the transported derivation unit through `e` on a cochain complex
exactly when it factors `α` through `transferExtension e` there. -/
private lemma transfer_unit_comp_iff
    (e : LeftExtension (derivedLocalizationHomotopy QSource)
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QTarget))
    (δ : R ⟶ e.right) (K : CochainComplex A ℤ) :
    (rightDerivedUnitOnHomotopy F QSource QTarget R α).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
            δ.app ((derivedLocalizationHomotopy QSource).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
        e.hom.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ↔
      α.app K ≫ δ.app (QSource.obj K) = (transferExtension F QSource QTarget e).hom.app K := by
  have hn : R.map ((derivedLocalizationHomotopyQuotientIso QSource).inv.app K) ≫
      δ.app ((derivedLocalizationHomotopy QSource).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      δ.app (QSource.obj K) ≫
        e.right.map ((derivedLocalizationHomotopyQuotientIso QSource).inv.app K) :=
    δ.naturality _
  rw [rightDerivedUnitOnHomotopy_app, transferExtension_hom_app, Category.assoc, Category.assoc,
    hn]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [reassoc_of% h]
    simp

/-- `transferDesc` factors the transported derivation unit through the given left extension. -/
private lemma transferDesc_fac
    (e : LeftExtension (derivedLocalizationHomotopy QSource)
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QTarget)) :
    rightDerivedUnitOnHomotopy F QSource QTarget R α ≫
        Functor.whiskerLeft (derivedLocalizationHomotopy QSource)
          (transferDesc F QSource QTarget R α e) = e.hom := by
  apply Quotient.natTrans_ext
  ext K
  exact (transfer_unit_comp_iff F QSource QTarget R α e _ K).2
    (congr_app ((transferInitial F QSource QTarget R α).fac
      (transferExtension F QSource QTarget e)) K)

/-- **A right derived functor along the localization of cochain complexes is a right derived
functor along the localization of the homotopy category.** The two localizations differ by the
quotient functor `CochainComplex A ℤ ⥤ K(A)`, through which left extensions correspond. -/
public theorem rightDerived_transfer_homotopy :
    R.IsRightDerivedFunctor (rightDerivedUnitOnHomotopy F QSource QTarget R α)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension R
    (rightDerivedUnitOnHomotopy F QSource QTarget R α)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).2
  refine ⟨⟨IsInitial.ofUniqueHom
    (fun e => StructuredArrow.homMk (transferDesc F QSource QTarget R α e)
      (transferDesc_fac F QSource QTarget R α e)) (fun e δ => ?_)⟩⟩
  have hδ : α ≫ Functor.whiskerLeft QSource δ.right =
      (transferExtension F QSource QTarget e).hom := by
    ext K
    exact (transfer_unit_comp_iff F QSource QTarget R α e _ K).1
      (congr_app δ.w ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
  have hfactor : α ≫ Functor.whiskerLeft QSource δ.right =
      α ≫ Functor.whiskerLeft QSource (transferDesc F QSource QTarget R α e) :=
    hδ.trans ((transferInitial F QSource QTarget R α).fac
      (transferExtension F QSource QTarget e)).symm
  exact StructuredArrow.hom_ext δ _
    ((transferInitial F QSource QTarget R α).hom_ext hfactor)

end Transfer

/-! ### Pointwise derived values -/

/-- A cocone over the diagram of quasi-isomorphisms out of `X` with a terminal index computes the
right derived value there. -/
private lemma coconeOfTerminalUnder_isRightDerivedValueAt
    {C : Type*} {D : Type*} [Category C] [Category D]
    (Φ : C ⥤ D) (W : MorphismProperty C) [W.ContainsIdentities]
    (X : C) (t₀ : W.Under ⊤ X) (ht : Limits.IsTerminal t₀) :
    Φ.IsRightDerivedValueAt W X
      (Limits.coconeOfDiagramTerminal ht
        (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ Φ)) := by
  refine ⟨t₀, 𝟙 _, (Category.id_comp _).trans (by simp), fun s => ?_⟩
  refine ⟨t₀, ht.from s, ht.from t₀, ?_⟩
  change Φ.map (ht.from s).right =
    Φ.map (ht.from s).right ≫ 𝟙 _ ≫ Φ.map (ht.from t₀).right
  simp

/-- A quasi-isomorphism into a K-injective complex is terminal among quasi-isomorphisms out of
its source. -/
private noncomputable def isTerminalUnderKInjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K : HomotopyCategory C (ComplexShape.up ℤ)} (I : CochainComplex C ℤ)
    [I.IsKInjective] (q : K ⟶ (HomotopyCategory.quotient C (.up ℤ)).obj I)
    (hq : HomotopyCategory.quasiIso C (.up ℤ) q) :
    Limits.IsTerminal (MorphismProperty.Under.mk ⊤ q hq) := by
  have hI : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).isLocal
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, ObjectProperty.isLocal_trW]
    exact (CochainComplex.isKInjective_iff_rightOrthogonal I).1 inferInstance
  exact Limits.IsTerminal.ofUniqueHom
    (fun s ↦ MorphismProperty.Under.homMk _ ((hI s.hom s.prop).2 q).choose_spec)
    (fun s a ↦ MorphismProperty.Under.Hom.ext
      ((hI s.hom s.prop).1 ((MorphismProperty.Under.w a).trans
        ((hI s.hom s.prop).2 q).choose_spec.symm)))

section Values

variable [CategoryWithHomology A] [CategoryWithHomology B] [IsGrothendieckAbelian A]
  (F : A ⥤ B) [F.Additive]
  (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
  [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R)
  [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- **The right derived functor is computed pointwise by K-injective resolutions.** For every
object of the homotopy category the system of quasi-isomorphisms out of it has a terminal
member, a K-injective resolution, and the induced cocone is the right derived value. -/
public theorem rightDerivedValues_of_isKInjective :
    ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (c : Limits.Cocone (MorphismProperty.Under.forget
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ K ⋙
            Under.forget K ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              derivedLocalizationHomotopy QTarget)),
        ∃ (_ : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          derivedLocalizationHomotopy QTarget).IsRightDerivedValueAt
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c),
      ∃ (e : c.pt ≅ R.obj ((derivedLocalizationHomotopy QSource).obj K)),
          ∀ s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ K,
            c.ι.app s ≫ e.hom ≫ R.map
              ((derivedLocalizationHomotopy QSource).map s.hom) =
                (rightDerivedUnitOnHomotopy F QSource QTarget R α).app s.right := by
  let c := ComplexShape.up ℤ
  let W := HomotopyCategory.quasiIso A c
  let Qs := derivedLocalizationHomotopy QSource
  let Qt := derivedLocalizationHomotopy QTarget
  let Fh := F.mapHomotopyCategory c
  let β := rightDerivedUnitOnHomotopy F QSource QTarget R α
  let : R.IsRightDerivedFunctor β W := rightDerived_transfer_homotopy F QSource QTarget R α
  let hPoint :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (Fh ⋙ Qt) Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso
  intro K
  obtain ⟨Kc, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, q, hI, hq⟩ := Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso Kc
  let : I.IsKInjective := hI
  let : QuasiIso q := hq
  let qh := (HomotopyCategory.quotient A c).map q
  have hqh : W qh := (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
  let t₀ : W.Under ⊤ ((HomotopyCategory.quotient A c).obj Kc) :=
    MorphismProperty.Under.mk ⊤ qh hqh
  let ht := isTerminalUnderKInjective I qh hqh
  let coc := Limits.coconeOfDiagramTerminal ht
    (MorphismProperty.Under.forget W ⊤ ((HomotopyCategory.quotient A c).obj Kc) ⋙
      Under.forget ((HomotopyCategory.quotient A c).obj Kc) ⋙ Fh ⋙ Qt)
  have hc := coconeOfTerminalUnder_isRightDerivedValueAt (Fh ⋙ Qt) W
    ((HomotopyCategory.quotient A c).obj Kc) t₀ ht
  have hβ : IsIso (β.app t₀.right) := hPoint.2 Qs R β I hI
  let eβ : _ ≅ _ := asIso (β.app t₀.right)
  let : IsIso (Qs.map t₀.hom) := (Localization.inverts Qs W) t₀.hom t₀.prop
  let : IsIso (R.map (Qs.map t₀.hom)) := by infer_instance
  let eR : _ ≅ _ := asIso (R.map (Qs.map t₀.hom))
  let e : coc.pt ≅ R.obj (Qs.obj ((HomotopyCategory.quotient A c).obj Kc)) := eβ ≪≫ eR.symm
  refine ⟨coc, hc, e, ?_⟩
  intro s
  have hcomp : s.hom ≫ (ht.from s).right = t₀.hom := MorphismProperty.Under.w (ht.from s)
  have hmap : R.map (Qs.map t₀.hom) =
      R.map (Qs.map s.hom) ≫ R.map (Qs.map ((ht.from s).right)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomp]
  have hnat : (Fh ⋙ Qt).map ((ht.from s).right) ≫ β.app t₀.right =
      β.app s.right ≫ R.map (Qs.map ((ht.from s).right)) := by
    simpa only [Functor.comp_map] using β.naturality ((ht.from s).right)
  let : IsIso (Qs.map s.hom) := (Localization.inverts Qs W) s.hom s.prop
  let : IsIso (R.map (Qs.map s.hom)) := by infer_instance
  have he : e.hom = β.app t₀.right ≫ eR.inv := rfl
  have hcompR : R.map (Qs.map s.hom) ≫ R.map (Qs.map ((ht.from s).right)) = eR.hom := by
    simpa only [eR, asIso_hom] using hmap.symm
  have hcancel : R.map (Qs.map ((ht.from s).right)) ≫ eR.inv ≫ R.map (Qs.map s.hom) = 𝟙 _ := by
    have hEq : R.map (Qs.map s.hom) ≫
        (R.map (Qs.map ((ht.from s).right)) ≫ eR.inv ≫ R.map (Qs.map s.hom)) =
          R.map (Qs.map s.hom) := by
      simp only [← Category.assoc, hcompR]
      exact (Category.assoc eR.hom eR.inv (R.map (Qs.map s.hom))).trans
        (eR.hom_inv_id_assoc _)
    exact (cancel_epi (R.map (Qs.map s.hom))).mp (hEq.trans (Category.comp_id _).symm)
  dsimp only [coc, Limits.coconeOfDiagramTerminal]
  rw [he]
  calc
    _ = ((Fh ⋙ Qt).map ((ht.from s).right) ≫ (β.app t₀.right ≫ eR.inv)) ≫
          R.map (Qs.map s.hom) :=
      (Category.assoc ((Fh ⋙ Qt).map ((ht.from s).right))
        (β.app t₀.right ≫ eR.inv) (R.map (Qs.map s.hom))).symm
    _ = (((Fh ⋙ Qt).map ((ht.from s).right) ≫ β.app t₀.right) ≫ eR.inv) ≫
          R.map (Qs.map s.hom) :=
      congrArg (fun k => k ≫ R.map (Qs.map s.hom))
        (Category.assoc ((Fh ⋙ Qt).map ((ht.from s).right))
          (β.app t₀.right) eR.inv).symm
    _ = ((β.app s.right ≫ R.map (Qs.map ((ht.from s).right))) ≫ eR.inv) ≫
          R.map (Qs.map s.hom) :=
      congrArg (fun k => (k ≫ eR.inv) ≫ R.map (Qs.map s.hom)) hnat
    _ = β.app s.right ≫
          (R.map (Qs.map ((ht.from s).right)) ≫ eR.inv ≫ R.map (Qs.map s.hom)) :=
      (Category.assoc _ _ _).trans (Category.assoc _ _ _)
    _ = β.app s.right := by rw [hcancel]; exact Category.comp_id _

end Values

/-! ### The exact left adjoint, and the derived adjunction -/

/-- The constant cone on `Φ(X)` over the diagram of morphisms into `X` inverted by `Φ`. -/
public noncomputable def coneOfInvertedMorphisms
    {C : Type*} {D : Type*} [Category C] [Category D]
    (Φ : C ⥤ D) (W : MorphismProperty C) (hΦ : W.IsInvertedBy Φ) (X : C) :
    Limits.Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ Φ) where
  pt := Φ.obj X
  π :=
    { app := fun s => by
        letI : IsIso (Φ.map s.hom) := hΦ s.hom s.prop
        exact (asIso (Φ.map s.hom)).inv
      naturality := fun s t u => by
        let : IsIso (Φ.map s.hom) := hΦ s.hom s.prop
        let : IsIso (Φ.map t.hom) := hΦ t.hom t.prop
        dsimp
        apply (cancel_mono (Φ.map t.hom)).1
        simp only [Category.id_comp]
        rw [Category.assoc, ← Φ.map_comp, MorphismProperty.Over.w u,
          IsIso.inv_hom_id, IsIso.inv_hom_id] }

/-- A functor inverting a class of morphisms has that constant cone as its left derived value. -/
public lemma coneOfInvertedMorphisms_isLeftDerivedValueAt
    {C : Type*} {D : Type*} [Category C] [Category D]
    (Φ : C ⥤ D) (W : MorphismProperty C) [W.ContainsIdentities]
    (hΦ : W.IsInvertedBy Φ) (X : C) :
    Φ.IsLeftDerivedValueAt W X (coneOfInvertedMorphisms Φ W hΦ X) := by
  let s₀ : W.Over ⊤ X := MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)
  let v : ∀ s : W.Over ⊤ X, s ⟶ s₀ := fun s =>
    MorphismProperty.Over.homMk (A := s) (B := s₀) s.hom (by
      change s.hom ≫ 𝟙 X = s.hom
      simp)
  refine ⟨s₀, Φ.map s₀.hom, ?_, fun s => ?_⟩
  · dsimp [coneOfInvertedMorphisms]
    let : IsIso (Φ.map s₀.hom) := hΦ s₀.hom s₀.prop
    simp
  · refine ⟨s, 𝟙 s, v s, ?_⟩
    let : IsIso (Φ.map s.hom) := hΦ s.hom s.prop
    dsimp [coneOfInvertedMorphisms]
    calc
      Φ.map (𝟙 s.left) = 𝟙 (Φ.obj s.left) := by simp
      _ = Φ.map ((v s).left ≫ s₀.hom) ≫ inv (Φ.map s.hom) := by
        rw [MorphismProperty.Over.w (v s)]
        simp
      _ = Φ.map (v s).left ≫ Φ.map s₀.hom ≫ inv (Φ.map s.hom) := by
        simp only [Functor.map_comp, Category.assoc]

section ExactLeft

variable [CategoryWithHomology A] [CategoryWithHomology B]
  (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
  [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]

omit [CategoryWithHomology A] in
/-- An exact functor inverts the quasi-isomorphisms of the homotopy category: it induces a
functor of derived categories, which is the composite with `DerivedCategory.Qh` up to
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`. -/
public lemma isInvertedBy_mapHomotopyCategory_comp_qh :
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
  rw [← MorphismProperty.IsInvertedBy.iff_of_iso _ G.mapDerivedCategoryFactorsh]
  exact MorphismProperty.IsInvertedBy.of_comp _ _
    (Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))) G.mapDerivedCategory

/-- An exact functor inverts the quasi-isomorphisms of the homotopy category, with values in a
prescribed model of the derived category. -/
public lemma isInvertedBy_exact :
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QSource) :=
  MorphismProperty.IsInvertedBy.of_comp _ _ (isInvertedBy_mapHomotopyCategory_comp_qh G)
    (Localization.uniq (DerivedCategory.Q (C := A)) QSource
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor

/-- The functor on derived categories induced by an exact functor, with source and target the
prescribed models: an exact functor inverts quasi-isomorphisms, so no deriving is needed. -/
public noncomputable def exactDerivedLeftFunctor :
    DerivedCategory B ⥤ DerivedCategory A :=
  Localization.lift
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QSource)
    (isInvertedBy_exact G QSource) (derivedLocalizationHomotopy QTarget)

/-- `exactDerivedLeftFunctor` is, on the homotopy category, the degreewise functor. -/
public noncomputable def exactDerivedLeftFunctor_fac :
    derivedLocalizationHomotopy QTarget ⋙ exactDerivedLeftFunctor G QSource QTarget ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QSource :=
  Localization.fac
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ derivedLocalizationHomotopy QSource)
    (isInvertedBy_exact G QSource) (derivedLocalizationHomotopy QTarget)

/-- **The derived functors of an adjoint pair whose left adjoint is exact are adjoint.**
`G` is exact, so it descends to the derived categories without deriving, and `R` is any right
derived functor of `F`; the adjunction is [Stacks, Tag 09T5], whose pointwise hypotheses are
K-injective resolutions on the right and the constant system on the left. -/
public noncomputable def derivedAdjunctionOfExactLeft
    [IsGrothendieckAbelian A]
    {F : A ⥤ B} [F.Additive] (adj : G ⊣ F)
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R)
    [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    exactDerivedLeftFunctor G QSource QTarget ⊣ R := by
  let c := ComplexShape.up ℤ
  let Qs := derivedLocalizationHomotopy QSource
  let Qt := derivedLocalizationHomotopy QTarget
  let W := HomotopyCategory.quasiIso A c
  let W' := HomotopyCategory.quasiIso B c
  let Gc := G.mapHomotopyCategory c
  let Rβ := rightDerivedUnitOnHomotopy F QSource QTarget R α
  let : R.IsRightDerivedFunctor Rβ W := rightDerived_transfer_homotopy F QSource QTarget R α
  let LG := exactDerivedLeftFunctor G QSource QTarget
  let αL : Qt ⋙ LG ⟶ Gc ⋙ Qs := (exactDerivedLeftFunctor_fac G QSource QTarget).hom
  have hInv : W'.IsInvertedBy (Gc ⋙ Qs) := isInvertedBy_exact G QSource
  have hRF := rightDerivedValues_of_isKInjective F QSource QTarget R α
  have hLG : ∀ M : HomotopyCategory B c,
      ∃ (d : Limits.Cone (MorphismProperty.Over.forget W' ⊤ M ⋙
        Over.forget M ⋙ Gc ⋙ Qs)),
        ∃ (_ : (Gc ⋙ Qs).IsLeftDerivedValueAt W' M d),
        ∃ (e : LG.obj (Qt.obj M) ≅ d.pt),
          ∀ t : W'.Over ⊤ M,
            LG.map (Qt.map t.hom) ≫ e.hom ≫ d.π.app t = αL.app t.left := by
    intro M
    let H := Gc ⋙ Qs
    let d := coneOfInvertedMorphisms H W' hInv M
    have hd := coneOfInvertedMorphisms_isLeftDerivedValueAt H W' hInv M
    let e : LG.obj (Qt.obj M) ≅ d.pt :=
      (Localization.fac H hInv Qt).app M
    refine ⟨d, hd, e, ?_⟩
    intro t
    let : IsIso (H.map t.hom) := hInv t.hom t.prop
    have hn : LG.map (Qt.map t.hom) ≫ αL.app M = αL.app t.left ≫ H.map t.hom := by
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj,
        Functor.const_obj_obj, H] using αL.naturality t.hom
    dsimp [d, coneOfInvertedMorphisms]
    change LG.map (Qt.map t.hom) ≫ αL.app M ≫ inv (H.map t.hom) = αL.app t.left
    rw [reassoc_of% hn]
    simp
  exact Classical.choose
    (CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      (CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction adj c) W W' Qs Qt R Rβ LG αL
      hRF hLG)

end ExactLeft

/-! ### From a cochain-level derivation unit to a homotopy-level one -/

/-- For a functor out of the derived category, the identification of its restriction along the
quotient `CochainComplex A ℤ ⥤ K(A)`. -/
public noncomputable def quotientFactorIso {D : Type*} [Category* D]
    (RF : DerivedCategory A ⥤ D) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh ⋙ RF) ≅
      DerivedCategory.Q ⋙ RF :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) RF

section HomotopyUnit

variable [CategoryWithHomology A] [CategoryWithHomology B] (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)

/-- A derivation unit given on cochain complexes, read on the homotopy category: the quotient
functor `CochainComplex A ℤ ⥤ K(A)` is a localization at the homotopy equivalences, so
restriction along it is fully faithful on natural transformations out of `K(A)`. -/
public noncomputable def homotopyUnitOfComplex :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF :=
  ((Functor.whiskeringLeft _ _ (DerivedCategory B)).obj
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))).preimage
    ((rightDerivedSourceIso F).hom ≫ α ≫ (quotientFactorIso RF).inv)

/-- **A right derived functor along the localization of cochain complexes is one along the
localization of the homotopy category at `DerivedCategory.Qh`.** -/
public lemma homotopyUnitOfComplex_isRightDerivedFunctor
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    RF.IsRightDerivedFunctor (homotopyUnitOfComplex F RF α)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have h₀ : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).IsLeftKanExtension
        (𝟙 (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
          (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))) :=
    ⟨⟨StructuredArrow.mkIdInitial⟩⟩
  have h₁ : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).IsLeftKanExtension (rightDerivedSourceIso F).inv :=
    (Functor.isLeftKanExtension_iff_of_iso₂ _ (rightDerivedSourceIso F).inv
      (rightDerivedSourceIso F) (Iso.refl _) (by simp)).1 h₀
  have h₂ : RF.IsLeftKanExtension α :=
    (Functor.isRightDerivedFunctor_iff_isLeftKanExtension RF α
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).1 inferInstance
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension RF _
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).2
  refine (Functor.isLeftKanExtension_iff_postcompose (rightDerivedSourceIso F).inv
    DerivedCategory.Q (DerivedCategory.quotientCompQhIso A)
    (homotopyUnitOfComplex F RF α) α ?_).2 h₂
  change (rightDerivedSourceIso F).inv ≫
    ((Functor.whiskeringLeft _ _ (DerivedCategory B)).obj
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))).map
        (homotopyUnitOfComplex F RF α) ≫ (quotientFactorIso RF).hom = α
  dsimp only [homotopyUnitOfComplex]
  rw [Functor.map_preimage]
  simp

end HomotopyUnit

end Stacks.DerivedAdjunction

end
