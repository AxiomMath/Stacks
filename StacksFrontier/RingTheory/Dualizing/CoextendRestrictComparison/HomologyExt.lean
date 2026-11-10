module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedHomAnyModel
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext

/-!
# The cohomology of derived Hom is Ext

Let `f : A →+* B` be a homomorphism of commutative rings and let `RF : D(A) ⥤ D(B)` be a right
derived functor of coextension of scalars `Hom_A(B, -)`, presented by its structural
transformation `α`.  This file proves the second half of Tag 0A71: for every object `K` of `D(A)`
and every `q`, restricting scalars along `f` identifies `H^q(RF(K))` with `Ext^q_A(B, K)`,
naturally in `K` and normalized by the derived unit.  Together with
`Dualizing.derivedCoextendScalarsCompDerivedRestrictScalarsIso` this is Tag 0A71.

The identification is produced by the derived adjunction rather than by a choice of K-injective
resolution.  Three ingredients combine.  First, the derived restriction/coextension adjunction
`Dualizing.derivedAdjunctionData`: any right derived functor of coextension of scalars is right
adjoint to the functor induced by restriction of scalars — it is isomorphic to the canonical one
of Tag 0A70 — and the derived adjunction may therefore be produced by Mathlib's
`CategoryTheory.Adjunction.derived`, which normalizes its unit by the Kan-extension property.
Second, the free rank one `B`-module `ULift B` is projective, so `B[q]` corepresents `H^q` on the
whole of `D(B)` (`DerivedCategory.homologyFromSingle`).  Composing the two gives a bijection
`Hom_{D(A)}(B[q], K) ≅ Hom_B(ULift B, H^q(RF(K))) ≅ H^q(RF(K))`, and shifting turns the source
into `Ext^q_A(B, K)` (`Dualizing.extFromSingleEquiv`).  Third, the comparison so obtained is the
one normalized by `Dualizing.coextendSingleUnit`: this is
`Dualizing.homologyFromSingle_derivedUnit_eq`, proved from the Kan-extension normalization of the
derived unit and the degreewise description of the unit on a single complex.

Everything is stated for arbitrary models of the two derived categories, with independent
morphism universes, and for an arbitrary right derived functor presented by its universal
property, exactly as in `StacksFrontier/RingTheory/Dualizing/CoextendRestrictComparison.lean`.

## Main definitions

* `Dualizing.derivedAdjunctionData` — the derived restriction/coextension adjunction attached to
  `(RF, α)`, together with the normalization of its unit.
* `Dualizing.extFromSingleEquiv` — morphisms `M[q] ⟶ K` are the degree `q` extension classes of
  `K` by `M[0]`.
* `Dualizing.derivedUnitClass` — the class of the identity of `B` in `H^q(RF(B[q]))`.
* `Dualizing.homologyOfDerivedCoextendEquiv` — the comparison `Hom(B[q], K) ≅ H^q(RF(K))`, out
  of which `Dualizing.derivedCoextendScalarsHomologyLinearEquivExt` of
  `StacksFrontier/RingTheory/Dualizing/TrivialDualityRing/Ext.lean` — Tag 0A71 — is assembled.

## Main results

* `Dualizing.homologyFromSingle_derivedUnit_eq` — the comparison is the one normalized by
  `Dualizing.coextendSingleUnit`.
* `Dualizing.additive_of_isRightDerivedFunctor` — a right derived functor of coextension of
  scalars is additive.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u v wA wB

namespace Dualizing

noncomputable section

section Generic

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {G : C ⥤ D} {F : D ⥤ C} [G.Additive] [F.Additive] (adj : G ⊣ F) (q : ℤ) (N : C)

/-- **The unit of an adjunction on a complex concentrated in one degree.** For an adjunction
`G ⊣ F` of additive functors between abelian categories, the unit of the induced adjunction on
cochain complexes, evaluated at the complex `N[q]` with `N` in degree `q`, is the unit of `G ⊣ F`
at `N` read through the two identifications of `F`, resp. `G`, with their degreewise action on
single complexes. -/
lemma unit_app_single_mapHomologicalComplex :
    (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) q).obj N) ≫
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) q).app N).hom =
    (HomologicalComplex.single C (ComplexShape.up ℤ) q).map (adj.unit.app N) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).app
        (G.obj N)).inv := by
  ext n
  by_cases h : n = q
  · subst h
    simp [Adjunction.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
      HomologicalComplex.single_map_f_self]
  · have hz : IsZero (F.obj (((HomologicalComplex.single D (ComplexShape.up ℤ) q).obj
        (G.obj N)).X n)) := by
      rw [IsZero.iff_id_eq_zero, ← F.map_id,
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q (G.obj N) n h).eq_of_src
          (𝟙 _) 0, F.map_zero]
    exact hz.eq_of_tgt _ _

/-- `Dualizing.unit_app_single_mapHomologicalComplex` in the homotopy category: the unit of the
induced adjunction on homotopy categories, evaluated at the class of `N[q]`, is the class of the
degreewise unit. -/
lemma unit_app_single_mapHomotopyCategory :
    (homotopyAdjunction adj (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C (ComplexShape.up ℤ) q).obj N)) ≫
      (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
            ((HomologicalComplex.single C (ComplexShape.up ℤ) q).obj N) ≫
          (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) q).app N).hom) =
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single C (ComplexShape.up ℤ) q).map (adj.unit.app N) ≫
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) q).app
            (G.obj N)).inv) ≫
      (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        ((HomologicalComplex.single D (ComplexShape.up ℤ) q).obj (G.obj N)) := by
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [Category.id_comp, Category.comp_id]
  exact ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (congrArg (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (unit_app_single_mapHomologicalComplex adj q N))

end Generic

section DeltaIdentity

variable (C : Type*) [Category C] [Abelian C] [HasDerivedCategory.{wB} C] (q : ℤ)

/-- The canonical identification of the degree-`q` cohomology of a complex concentrated in
degree `q`, read in the derived category, is the one computed on complexes. -/
lemma singleFunctorCompHomologyFunctorIso_hom_app (N : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).hom.app N =
      (DerivedCategory.homologyFunctorFactors C q).hom.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) q).obj N) ≫
        (HomologicalComplex.homologyFunctorSingleIso C (ComplexShape.up ℤ) q).hom.app N := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorsPostcompQIso]

variable {C}

/-- The unit of an adjunction, read through the identification of the cohomology of
single complexes. -/
lemma homologyFromSingle_single_unit {D : Type*} [Category D] [Abelian D]
    {Gr : C ⥤ D} {Fc : D ⥤ C} [Gr.Additive] [Fc.Additive] (adj : Gr ⊣ Fc) (N : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app N ≫
        (DerivedCategory.homologyFunctor C q).map (DerivedCategory.Q.map
          ((HomologicalComplex.single C (ComplexShape.up ℤ) q).map (adj.unit.app N) ≫
            ((HomologicalComplex.singleMapHomologicalComplex Fc (ComplexShape.up ℤ) q).app
              (Gr.obj N)).inv)) =
      adj.unit.app N ≫
        (HomologicalComplex.homologyFunctorSingleIso C (ComplexShape.up ℤ) q).inv.app
          (Fc.obj (Gr.obj N)) ≫
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).map
          ((HomologicalComplex.singleMapHomologicalComplex Fc (ComplexShape.up ℤ) q).app
            (Gr.obj N)).inv ≫
        (DerivedCategory.homologyFunctorFactors C q).inv.app
          ((Fc.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single D (ComplexShape.up ℤ) q).obj (Gr.obj N))) := by
  have hnat1 : (HomologicalComplex.homologyFunctorSingleIso C (ComplexShape.up ℤ) q).hom.app N ≫
      adj.unit.app N =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).map
        ((HomologicalComplex.single C (ComplexShape.up ℤ) q).map (adj.unit.app N)) ≫
      (HomologicalComplex.homologyFunctorSingleIso C (ComplexShape.up ℤ) q).hom.app
        (Fc.obj (Gr.obj N)) := by
    simpa using
      ((HomologicalComplex.homologyFunctorSingleIso C (ComplexShape.up ℤ) q).hom.naturality
        (adj.unit.app N)).symm
  have hnat2 : ∀ {X Y : CochainComplex C ℤ} (g : X ⟶ Y),
      (DerivedCategory.homologyFunctorFactors C q).hom.app X ≫
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).map g =
      (DerivedCategory.homologyFunctor C q).map (DerivedCategory.Q.map g) ≫
        (DerivedCategory.homologyFunctorFactors C q).hom.app Y := by
    intro X Y g
    simpa using ((DerivedCategory.homologyFunctorFactors C q).hom.naturality g).symm
  rw [← cancel_epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso C q).hom.app N),
    Iso.hom_inv_id_app_assoc, singleFunctorCompHomologyFunctorIso_hom_app]
  simp only [Category.assoc]
  rw [reassoc_of% hnat1, Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, ← Category.assoc, hnat2]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end DeltaIdentity



section SecondHalf

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)]
  (f : A →+* B)
  (RF : DerivedCategory (ModuleCat.{max v u} A) ⥤ DerivedCategory (ModuleCat.{max v u} B))
  (α : coextendScalarsToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))]

/-- Any right derived functor of coextension of scalars is right adjoint to the functor induced
by restriction of scalars: by uniqueness of right derived functors it is isomorphic to the
canonical one, which Tag 0A70 exhibits as a right adjoint. -/
lemma isLeftAdjoint_mapDerivedCategory_and_isRightAdjoint
    (β : coextendScalarsToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))] :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.IsLeftAdjoint ∧ RF.IsRightAdjoint :=
      by
  obtain ⟨a⟩ := Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom.{u, v, u, wA, wB} f
  have hpt := Dualizing.AnyModel.coextendScalars_hasPointwiseRightDerivedFunctor.{u, v, u, wB} f
  set β₀ :=
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))) with hβ₀
  have hird : (Dualizing.AnyModel.derivedHom.{u, v, u, wA, wB} f).IsRightDerivedFunctor β₀
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ)) := by
    rw [hβ₀]
    dsimp [Dualizing.AnyModel.derivedHom]
    infer_instance
  have hiso : RF ≅ Dualizing.AnyModel.derivedHom.{u, v, u, wA, wB} f :=
    Functor.rightDerivedUnique RF _ β β₀
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))
  exact ⟨a.isLeftAdjoint, (a.ofNatIsoRight hiso.symm).isRightAdjoint⟩

/-- The derived restriction/coextension adjunction attached to the chosen right derived functor,
together with the normalization of its unit supplied by the Kan-extension property: at the image
of a homotopy class the unit is the localization of the ordinary unit, followed by the structural
transformation `α`. -/
def derivedAdjunctionData :
    { adjD : (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory ⊣ RF //
      ∀ X : HomotopyCategory (ModuleCat.{max v u} B) (ComplexShape.up ℤ),
        adjD.unit.app (DerivedCategory.Qh.obj X) ≫
            RF.map ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactorsh.hom.app X) =
          DerivedCategory.Qh.map
            ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
            (ComplexShape.up ℤ)).unit.app X) ≫
            α.app
              (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              X) } := by
  obtain ⟨h₁, h₂⟩ := isLeftAdjoint_mapDerivedCategory_and_isRightAdjoint f RF α
  haveI := h₁
  haveI := h₂
  haveI : (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.IsLeftDerivedFunctor
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  exact
    ⟨(homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
    (ComplexShape.up ℤ)).derived
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactorsh.hom α,
    fun X =>
      (homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
      (ComplexShape.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactorsh.hom α X⟩

omit [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))] in
/-- The defining composite of `Dualizing.coextendSingleUnit`. -/
lemma coextendSingleUnit_eq (M : (ModuleCat.{max v u} A)) (q : ℤ) :
    coextendSingleUnit f RF α M q =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) q
      ((ModuleCat.coextendScalars.{u, u, max v u} f).obj M)).inv ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.coextendScalars.{u, u, max v u} f) (ComplexShape.up ℤ) q).app M).inv ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app _ ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).inv.app _ ≫
          DerivedCategory.Qh.map
            (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).inv.app
              ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj M))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map
        (α.app
          ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj M))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map
        (RF.map ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
          ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj M))) := rfl

/-- The derived unit on a single complex, computed through the Kan-extension normalization of
the derived adjunction. -/
lemma derivedUnit_single_eq (q : ℤ) (N : (ModuleCat.{max v u} B)) :
    (derivedAdjunctionData f RF α).1.unit.app
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj N) ≫ RF.map
      (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app N) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
        ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.coextendScalars.{u, u, max v u} f) (ComplexShape.up ℤ) q).app
        ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).inv.app
        (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj N))) ≫ DerivedCategory.Qh.map
        (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app
        ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫
        (α.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫ RF.map
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj N))) := by
  have hstep1 :
    (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app N) =
    ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
    (ComplexShape.up ℤ) q).app N).hom := by
    simp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ,
      CochainComplex.singleFunctor]
  have h2 :
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    (derivedAdjunctionData f RF α).1.unit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj N) =
    (derivedAdjunctionData f RF α).1.unit.app
    (DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫ RF.map
    ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) :=
    (derivedAdjunctionData f RF α).1.unit.naturality
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
      ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))
  have hE :
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    (derivedAdjunctionData f RF α).1.unit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj N) ≫ RF.map
    (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).inv.app
    (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
    (DerivedCategory.Qh.map
    (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).inv.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)))) =
      DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        (α.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)))) := by
    have h1 := (derivedAdjunctionData f RF α).2
      ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))
    rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h1
    rw [← Category.assoc, h2, Category.assoc, ← CategoryTheory.Functor.map_comp]
    exact h1
  have hA :
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    DerivedCategory.Q.map
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
    ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.coextendScalars.{u, u, max v u} f)
    (ComplexShape.up ℤ) q).app ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).inv.app
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N))) ≫ DerivedCategory.Qh.map
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).inv.app
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N)))) =
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
        ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.coextendScalars.{u, u, max v u} f) (ComplexShape.up ℤ) q).app
        ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
        (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app
          ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
          ((ModuleCat.restrictScalars.{max v u} f).obj N)))) := by
    simp [CategoryTheory.Functor.map_comp, - DerivedCategory.Q_map_single_map]
  have hB : (HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).map
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
    ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.coextendScalars.{u, u, max v u} f)
    (ComplexShape.up ℤ) q).app ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).inv.app
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N))) =
      ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        ((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
        (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom) :=
        (unit_app_single_mapHomotopyCategory (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f) q
        N).symm
  have hC : DerivedCategory.Qh.map
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).map
    ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
    (ComplexShape.up ℤ) q).app N).hom)) ≫
    (α.app
    ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N)))) =
      (α.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)))) ≫
        RF.map
        (DerivedCategory.Qh.map
        ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
        (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom)) := by
    simpa using α.naturality
      ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom.app
      ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
      (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
      (ComplexShape.up ℤ) q).app N).hom)
  have hD : DerivedCategory.Qh.map
    ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
    (ComplexShape.up ℤ) q).app N).hom) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N))) =
      (DerivedCategory.Qh.map
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg
      (fun z =>
      (DerivedCategory.Qh.map
      (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom.app
      ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫ z)
      (DerivedCategory.quotientCompQhIso_hom_naturality
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom)
  have hcancel :
    ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
    (ComplexShape.up ℤ) q).app N).hom =
      (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).inv.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        (DerivedCategory.Qh.map
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)))) ≫
        ((DerivedCategory.Qh.map
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom) := by
    simp
  have hR :
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
    (DerivedCategory.Q.map
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
    ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.coextendScalars.{u, u, max v u} f)
    (ComplexShape.up ℤ) q).app ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).inv.app
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N))) ≫ DerivedCategory.Qh.map
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).inv.app
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫
    (α.app
    ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫ RF.map
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj N)))) =
      (DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        (α.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))))) ≫
        RF.map
          ((DerivedCategory.Qh.map
          (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app
          ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
          (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
          DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
          (ComplexShape.up ℤ) q).app N).hom) :=
    calc
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
      ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
      (DerivedCategory.Q.map
      ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
      ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.coextendScalars.{u, u, max v u} f)
      (ComplexShape.up ℤ) q).app ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).inv.app
      (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj N))) ≫ DerivedCategory.Qh.map
      (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv.app
      ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫
      (α.app
      ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫ RF.map
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
      ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj N))))
        =
          (((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
          ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
          DerivedCategory.Q.map
          ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
          ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.coextendScalars.{u, u, max v u} f) (ComplexShape.up ℤ) q).app
          ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).inv.app
          (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
          ((ModuleCat.restrictScalars.{max v u} f).obj N))) ≫ DerivedCategory.Qh.map
          (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app
          ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
          ((ModuleCat.restrictScalars.{max v u} f).obj N))))) ≫
          ((α.app
          ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
          ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫ RF.map
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
          ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
          ((ModuleCat.restrictScalars.{max v u} f).obj N)))) := by
          simp only [Category.assoc]
      _ = DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).map
        ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.coextendScalars.{u, u, max v u} f) (ComplexShape.up ℤ) q).app
        ((ModuleCat.restrictScalars.{max v u} f).obj N)).inv) ≫
            (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).inv.app
              ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
              ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫
            ((α.app
              ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
              ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫ RF.map
              ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
              ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
              ((ModuleCat.restrictScalars.{max v u} f).obj N)))) := by rw [hA]
      _ = DerivedCategory.Qh.map
        (((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        ((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
        (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom)) ≫
        ((α.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj N)))) ≫ RF.map
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj N)))) := by rw [hB]
      _ = DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
            (DerivedCategory.Qh.map
              (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory
              (ComplexShape.up ℤ)).map
              ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app
              ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
              (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex
              (ModuleCat.restrictScalars.{max v u} f) (ComplexShape.up ℤ) q).app N).hom)) ≫
              (α.app
              ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
              ((ModuleCat.restrictScalars.{max v u} f).obj N))))) ≫ RF.map
              ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
              ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
              ((ModuleCat.restrictScalars.{max v u} f).obj N))) := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        ((α.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)))) ≫
        RF.map
        (DerivedCategory.Qh.map
        ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
        (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom))) ≫
            RF.map
              ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
              ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
              ((ModuleCat.restrictScalars.{max v u} f).obj N))) := by rw [hC]
      _ =
        (DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        (α.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))))) ≫
        RF.map
        (DerivedCategory.Qh.map
        ((((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)) ≫
        (HomotopyCategory.quotient (ModuleCat.{max v u} A) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{max v u} f)
        (ComplexShape.up ℤ) q).app N).hom) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
        ((HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj N)))) := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ =
        (DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
        (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
        (α.app
        (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))))) ≫
            RF.map
              ((DerivedCategory.Qh.map
              (((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app
              ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
              ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).hom.app
              (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N))) ≫
              DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex
              (ModuleCat.restrictScalars.{max v u} f) (ComplexShape.up ℤ) q).app N).hom) := by rw
              [hD]
  simp only [Category.assoc] at hR
  rw
    [← cancel_epi
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).hom.app
    ((HomologicalComplex.single (ModuleCat.{max v u} B) (ComplexShape.up ℤ) q).obj N)), hstep1,
    hcancel, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hE, hR]

/-- The normalization: the derived unit of the adjunction, read on the single complex `N[q]`
through cohomology, is the structural map `Dualizing.coextendSingleUnit`. -/
lemma homologyFromSingle_derivedUnit_eq (q : ℤ) (N : (ModuleCat.{max v u} B)) :
    DerivedCategory.homologyFromSingle N
        (RF.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
          ((ModuleCat.restrictScalars.{max v u} f).obj N))) q
        ((derivedAdjunctionData f RF α).1.unit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj N) ≫ RF.map
          (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app N)) =
      (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app N ≫ coextendSingleUnit f RF α
        ((ModuleCat.restrictScalars.{max v u} f).obj N) q := by
  have hd := homologyFromSingle_single_unit (C := (ModuleCat.{max v u} B)) q
    (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f) N
  rw [DerivedCategory.homologyFromSingle_apply, derivedUnit_single_eq, coextendSingleUnit_eq]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hd ⊢
  rw [reassoc_of% hd]
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctorSingleIso_inv_app]
  rfl

end SecondHalf

/-! ### Shifting morphisms out of a single complex into `Ext` -/

section ExtFromSingle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{wA} C]
  (R : Type*) [Ring R] [Linear R C] (q : ℤ) (M : C) (K : DerivedCategory C)

/-- Morphisms `M[q] ⟶ K` in the derived category are the degree-`q` extension classes of `K` by
`M[0]`: shift by `q` and use the structural identification `M[q]⟦q⟧ ≅ M[0]`.  It is `R`-linear
when the category is `R`-linear. -/
def extFromSingleEquiv :
    ((DerivedCategory.singleFunctor C q).obj M ⟶ K) ≃ₗ[R]
      DerivedCategory.Ext ((DerivedCategory.singleFunctor C 0).obj M) K q :=
  LinearEquiv.ofBijective
    { toFun := fun g => ((DerivedCategory.singleFunctors C).shiftIso q 0 q (by simp)).inv.app M ≫
        (shiftFunctor (DerivedCategory C) q).map g
      map_add' := fun g h => by
        simp only [CategoryTheory.Functor.map_add, Preadditive.comp_add]
      map_smul' := fun r g => by
        simp only [Functor.map_smul, Linear.comp_smul, RingHom.id_apply] }
    (Function.Bijective.comp
      (f := fun g => (shiftFunctor (DerivedCategory C) q).map g)
      (g := fun h => ((DerivedCategory.singleFunctors C).shiftIso q 0 q (by simp)).inv.app M ≫ h)
      (Iso.homFromEquiv
        (((DerivedCategory.singleFunctors C).shiftIso q 0 q (by simp)).app M)).bijective
      ⟨Functor.map_injective _, Functor.map_surjective _⟩)

/-- `extFromSingleEquiv` sends `g` to the inverse of the shift isomorphism `M[q]⟦q⟧ ≅ M[0]`
followed by the shift of `g`. -/
@[simp]
lemma extFromSingleEquiv_apply (g : (DerivedCategory.singleFunctor C q).obj M ⟶ K) :
    extFromSingleEquiv R q M K g =
      ((DerivedCategory.singleFunctors C).shiftIso q 0 q (by simp)).inv.app M ≫
        (shiftFunctor (DerivedCategory C) q).map g :=
  rfl

end ExtFromSingle

section Comparison

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)]
  (f : A →+* B)
  (RF : DerivedCategory (ModuleCat.{max v u} A) ⥤ DerivedCategory (ModuleCat.{max v u} B))
  (α : coextendScalarsToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))]

include α in
/-- A right derived functor of coextension of scalars is additive: it is a right adjoint
(`Dualizing.isLeftAdjoint_mapDerivedCategory_and_isRightAdjoint`), hence preserves products. -/
lemma additive_of_isRightDerivedFunctor : RF.Additive := by
  obtain ⟨-, h₂⟩ := isLeftAdjoint_mapDerivedCategory_and_isRightAdjoint f RF α
  have := h₂
  exact Functor.additive_of_preserves_binary_products RF

/-- The canonical class in `H^q(RHom_A(B, B[q]))`: the image of the identity of `B` under the
derived unit. It is the element normalizing the comparison with `Ext`. -/
def derivedUnitClass (q : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj
      (RF.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B))))) :=
  coextendSingleUnit f RF α
    ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B))) q
    ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app (ModuleCat.of B (ULift.{v} B))
    (ULift.up 1))

/-- The canonical class is the image of the identity under the derived adjunction. -/
lemma derivedUnitClass_eq (q : ℤ) :
    derivedUnitClass f RF α q =
      DerivedCategory.homologyFromSingle (ModuleCat.of B (ULift.{v} B))
        (RF.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B))))) q
        ((derivedAdjunctionData f RF α).1.unit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
          (ModuleCat.of B (ULift.{v} B))) ≫ RF.map
          (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
          (ModuleCat.of B (ULift.{v} B)))) (ULift.up 1) := by
  rw [homologyFromSingle_derivedUnit_eq]
  rfl

/-- The comparison map: send a morphism `B[q] ⟶ K` to the image of the canonical class. -/
lemma homologyFunctor_map_derivedUnitClass (q : ℤ) (K : DerivedCategory (ModuleCat.{max v u} A))
    (g :
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)
      (derivedUnitClass f RF α q) =
      DerivedCategory.homologyFromSingle (ModuleCat.of B (ULift.{v} B)) (RF.obj K) q
        ((derivedAdjunctionData f RF α).1.unit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
          (ModuleCat.of B (ULift.{v} B))) ≫ RF.map
          ((((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
          (ModuleCat.of B (ULift.{v} B))) ≫ g)) (ULift.up 1) := by
  rw [derivedUnitClass_eq]
  have h := DerivedCategory.homologyFromSingle_comp (ModuleCat.of B (ULift.{v} B))
    (RF.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B))))) q
    ((derivedAdjunctionData f RF α).1.unit.app
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj (ModuleCat.of B (ULift.{v} B)))
      ≫ RF.map
      (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
      (ModuleCat.of B (ULift.{v} B)))) (RF.map g)
  rw
    [show
    ((derivedAdjunctionData f RF α).1.unit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj (ModuleCat.of B (ULift.{v} B))) ≫
    RF.map
    (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
    (ModuleCat.of B (ULift.{v} B)))) ≫ RF.map g =
      (derivedAdjunctionData f RF α).1.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
        (ModuleCat.of B (ULift.{v} B))) ≫ RF.map
        ((((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
        (ModuleCat.of B (ULift.{v} B))) ≫ g) from by
    rw [CategoryTheory.Functor.map_comp, Category.assoc]] at h
  rw [h]
  rfl

/-- The comparison map is bijective: it is the derived adjunction followed by the corepresentation
of cohomology by the free rank one module (`DerivedCategory.homologyFromSingle`). -/
lemma bijective_homologyFunctor_map_derivedUnitClass (q : ℤ)
  (K : DerivedCategory (ModuleCat.{max v u} A)) :
    Function.Bijective
      (fun g :
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)
        (derivedUnitClass f RF α q)) := by
  have hrw :
    (fun g :
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
    ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)
        (derivedUnitClass f RF α q)) =
      (fun φ : (ModuleCat.of B (ULift.{v} B)) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K) => φ
        (ULift.up 1)) ∘
        (fun h => DerivedCategory.homologyFromSingle (ModuleCat.of B (ULift.{v} B)) (RF.obj K) q h)
          ∘
        (fun k => (derivedAdjunctionData f RF α).1.homEquiv
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
          (ModuleCat.of B (ULift.{v} B))) K k) ∘
        (fun g :
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
          ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K =>
          (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
          (ModuleCat.of B (ULift.{v} B))) ≫ g) := by
    funext g
    rw [homologyFunctor_map_derivedUnitClass]
    rfl
  rw [hrw]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (Function.Bijective.comp ?_ ?_))
  · refine ⟨fun φ ψ h => ?_, fun z => ⟨ModuleCat.ofHom
      ((LinearMap.toSpanSingleton B _ z).comp (ULift.moduleEquiv.toLinearMap)), by simp⟩⟩
    ext x
    have hx : x = (x.down : B) • (ULift.up (1 : B) : ULift.{v} B) := by ext; simp
    rw [hx, _root_.map_smul, _root_.map_smul]
    exact congrArg (fun z => (x.down : B) • z) h
  · exact DerivedCategory.bijective_homologyFromSingle_of_projective _ _ _
  · exact
    ((derivedAdjunctionData f RF α).1.homEquiv
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj (ModuleCat.of B (ULift.{v} B)))
    K).bijective
  · exact
    (Iso.homFromEquiv
    (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).app
    (ModuleCat.of B (ULift.{v} B))).symm).bijective

/-- The comparison map is `A`-linear, where the target carries the `A`-action obtained by
restricting scalars along `f`. -/
lemma homologyFunctor_map_derivedUnitClass_smul (q : ℤ)
  (K : DerivedCategory (ModuleCat.{max v u} A)) (a : A)
    (g :
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map (a • g))
      (derivedUnitClass f RF α q) =
      f a • (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)
        (derivedUnitClass f RF α q) := by
  have hGr : (ModuleCat.restrictScalars.{max v u} f).map (f a • 𝟙 (ModuleCat.of B (ULift.{v} B))) =
    a • 𝟙 ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B))) := by
    ext x
    rfl
  have hnatσ : (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).map
        (f a • 𝟙 (ModuleCat.of B (ULift.{v} B)))) ≫
          (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
          (ModuleCat.of B (ULift.{v} B))) =
      (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
        (ModuleCat.of B (ULift.{v} B))) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).map
        ((ModuleCat.restrictScalars.{max v u} f).map (f a • 𝟙 (ModuleCat.of B (ULift.{v} B)))) :=
    ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.naturality
      (f a • 𝟙 (ModuleCat.of B (ULift.{v} B)))
  have hσ :
    (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
    (ModuleCat.of B (ULift.{v} B))) ≫ (a • g) =
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
        (f a • 𝟙
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
        (ModuleCat.of B (ULift.{v} B)))) ≫
        (((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
        (ModuleCat.of B (ULift.{v} B))) ≫ g := by
    rw
      [show
      (f a • 𝟙
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
      (ModuleCat.of B (ULift.{v} B)))) =
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).map
          (f a • 𝟙 (ModuleCat.of B (ULift.{v} B))) from by
          rw [Functor.map_smul, CategoryTheory.Functor.map_id],
      ← Category.assoc, hnatσ, hGr]
    simp [Linear.comp_smul, Linear.smul_comp]
  have hunit : (derivedAdjunctionData f RF α).1.unit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj (ModuleCat.of B (ULift.{v} B))) ≫
    RF.map
    ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
    (f a • 𝟙
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj (ModuleCat.of B (ULift.{v} B)))))
    =
      (f a • 𝟙
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
        (ModuleCat.of B (ULift.{v} B)))) ≫ (derivedAdjunctionData f RF α).1.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
        (ModuleCat.of B (ULift.{v} B))) :=
    ((derivedAdjunctionData f RF α).1.unit.naturality
      (f a • 𝟙
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
      (ModuleCat.of B (ULift.{v} B))))).symm
  rw [homologyFunctor_map_derivedUnitClass, homologyFunctor_map_derivedUnitClass, hσ,
    CategoryTheory.Functor.map_comp, ← Category.assoc, hunit, Linear.smul_comp, Category.id_comp,
    Linear.smul_comp,
    show DerivedCategory.homologyFromSingle (ModuleCat.of B (ULift.{v} B)) (RF.obj K) q
        (f a •
          ((derivedAdjunctionData f RF α).1.unit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
          (ModuleCat.of B (ULift.{v} B))) ≫ RF.map
          ((((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
          (ModuleCat.of B (ULift.{v} B))) ≫ g))) =
      f a • DerivedCategory.homologyFromSingle (ModuleCat.of B (ULift.{v} B)) (RF.obj K) q
        ((derivedAdjunctionData f RF α).1.unit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
          (ModuleCat.of B (ULift.{v} B))) ≫ RF.map
          ((((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).hom.app
          (ModuleCat.of B (ULift.{v} B))) ≫ g)) from
      (DerivedCategory.homologyFromSingleLinearMap (ModuleCat.of B (ULift.{v} B)) (RF.obj K) q
        B).map_smul (f a) _]
  rfl

/-- The comparison map, as an `A`-linear map. -/
def homologyOfDerivedCoextendMap (q : ℤ) (K : DerivedCategory (ModuleCat.{max v u} A)) :
    (((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K) →ₗ[A]
      (((ModuleCat.restrictScalars.{max v u} f).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K))) : Type
      (max v u)) where
  toFun g := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)
    (derivedUnitClass f RF α q)
  map_add' g h := by
    have := additive_of_isRightDerivedFunctor f RF α
    simp only [CategoryTheory.Functor.map_add]
    rfl
  map_smul' a g := homologyFunctor_map_derivedUnitClass_smul f RF α q K a g

/-- The comparison map, as an isomorphism of `A`-modules. -/
def homologyOfDerivedCoextendEquiv (q : ℤ) (K : DerivedCategory (ModuleCat.{max v u} A)) :
    (((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K) ≃ₗ[A]
      (((ModuleCat.restrictScalars.{max v u} f).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K))) : Type
      (max v u)) :=
  LinearEquiv.ofBijective (homologyOfDerivedCoextendMap f RF α q K)
    (bijective_homologyFunctor_map_derivedUnitClass f RF α q K)

/-- `homologyOfDerivedCoextendEquiv` sends `g` to the image of `derivedUnitClass f RF α q` under
the map induced by `RF.map g` on `q`-th homology. -/
@[simp]
lemma homologyOfDerivedCoextendEquiv_apply (q : ℤ) (K : DerivedCategory (ModuleCat.{max v u} A))
    (g :
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶ K) :
    homologyOfDerivedCoextendEquiv f RF α q K g =
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)
        (derivedUnitClass f RF α q) :=
  rfl

end Comparison



end

end Dualizing
