module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMateModel
public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorProjection

/-!
# The left-hand side of the first residue of [stacks 0E2H], valued at chain level

`Dualizing.ProjectionFormula.projCounitCompat_of_mate_model` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMateModel` reduces
`Dualizing.ProjectionFormula.ProjCounitCompat` -- the first of the three things the module
documentation of `StacksFrontier.RingTheory.Dualizing.RelativeCompositionTag` records [stacks 0E2H]
as owing -- to one mate identity at the class of a K-flat complex `P` of `A`-modules, the scalar
transport of the class of a K-injective complex `I` of `ULift B`-modules, and **any** presentation
`t : Z ≅ RHom_B(Ext Q(P), transport Q(I))` of the internal Hom.  This file makes that choice and
values the left-hand side.

## The choice of presentation

`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaComponentInverse` asks for the
inverse projection formula at a *localized complex*, so `Z` must be one.  It can be:
`StacksDraft.DerivedHom.derivedScalarEquivalence` is definitionally
`(StacksDraft.DerivedHom.uliftModuleEquivalence R).functor.mapDerivedCategory`, so
`CategoryTheory.Functor.mapDerivedCategoryFactors` presents the scalar transport of a localized
complex as a localized complex.  That is
`Dualizing.ProjectionFormula.scalarTransportQIso`, and composing it with the K-injective Hom model
`StacksDraft.DerivedHom.derivedHomModelIso` and a comparison `g` of `Ext Q(P)` with the transport
of a localized K-flat complex -- one exists, by `StacksDraft.DerivedHom.exists_kFlat_model` --
gives `Dualizing.ProjectionFormula.homModelQIso`, a presentation with
`Z = DerivedCategory.Q.obj (Dualizing.ProjectionFormula.homModelComplex B X I)`.

## Main results

* `CategoryTheory.Functor.comp_eight_map_comp`, `…_congr`, `…_last` -- abstract-category
  bookkeeping for an eight-fold composite whose last leg is a functor image.  They exist because
  the goals below are not type-correct at `implicit` transparency, so `rw` and
  `simp only [Category.assoc]` both fail on them while `exact` goes through.
* `Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q_comp` -- **the left-side value**: the
  inverse projection formula at `(Q P, Q L)` followed by derived restriction of any morphism, as
  the eight legs of `derivedProjNatIso_inv_app_Q` with the morphism absorbed into the last.  Its
  only non-bookkeeping factor is `DerivedCategory.Q.map (baseChange_tensor_iso φ P L).inv`, the
  chain-level projection formula.
* `Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q_comp_laxTensor` -- the same with that
  factor rewritten by `CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq` as the unit
  whiskered into the second variable followed by
  `CochainComplex.ExtendScalars.restrictScalarsLaxTensor`.  Only at the equal-universe
  `ModuleCat.{u}`, which is where that identity is stated.
* `Dualizing.ProjectionFormula.scalarTransportQIso`, `…homModelComplex`, `…homModelQIso`,
  `…homModelQIso_hom` -- the presentation.
* `Dualizing.ProjectionFormula.modelEvaluation` and
  `Dualizing.ProjectionFormula.homEquiv_homModelQIso_hom` -- the [stacks 0A63] transpose of that
  presentation, valued: it is the chain-level evaluation
  `StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor` read through the two models.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q` -- `ProjCounitCompat` at every object
  of `D(A)` from the mate identity at that presentation.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_legs` and
  `…_evaluationMor` -- **the sharpest forms**: the same with the left-hand side expanded into the
  eight legs, and then with the [stacks 0A63] transpose on the left replaced by the chain-level
  evaluation.  After the second, the first residue of [stacks 0E2H] is one equation in which the
  tensor--Hom adjunction of [stacks 0A63] occurs only through its two model comparisons.

No `@[stacks]` attribute is placed here: nothing in this file is unconditional about a tag.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

universe w₁ w₂ w₃ w₄

/-- A composite of eight morphisms whose last leg is the image of a functor, postcomposed with
the image of another morphism of the source category. -/
theorem comp_eight_map_comp {C : Type w₁} [Category.{w₂} C] {D : Type w₃} [Category.{w₄} D]
    (F : C ⥤ D) {X₁ X₂ X₃ X₄ X₅ X₆ X₇ : D} {Y Z W : C}
    (f : X₁ ⟶ F.obj Z)
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅) (g : X₅ ⟶ X₆) (m : X₆ ⟶ X₇)
    (p : X₇ ⟶ F.obj Y) (n : Y ⟶ Z) (k : Z ⟶ W)
    (h : f = a ≫ b ≫ c ≫ d ≫ g ≫ m ≫ p ≫ F.map n) :
    f ≫ F.map k = a ≫ b ≫ c ≫ d ≫ g ≫ m ≫ p ≫ F.map (n ≫ k) := by
  subst h
  simp

/-- `CategoryTheory.Functor.comp_eight_map_comp` with the fourth leg replaced along an
equality. -/
theorem comp_eight_map_comp_congr {C : Type w₁} [Category.{w₂} C] {D : Type w₃} [Category.{w₄} D]
    (F : C ⥤ D) {X₁ X₂ X₃ X₄ X₅ X₆ X₇ : D} {Y Z W : C}
    (f : X₁ ⟶ F.obj Z)
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) {d d' : X₄ ⟶ X₅} (g : X₅ ⟶ X₆) (m : X₆ ⟶ X₇)
    (p : X₇ ⟶ F.obj Y) (n : Y ⟶ Z) (k : Z ⟶ W) (hd : d = d')
    (h : f = a ≫ b ≫ c ≫ d ≫ g ≫ m ≫ p ≫ F.map n) :
    f ≫ F.map k = a ≫ b ≫ c ≫ d' ≫ g ≫ m ≫ p ≫ F.map (n ≫ k) := by
  subst hd h
  simp

/-- An eight-fold composite whose last leg is the image of a composite, with the second factor
of that composite replaced along an equality. -/
theorem comp_eight_map_comp_last {C : Type w₁} [Category.{w₂} C] {D : Type w₃} [Category.{w₄} D]
    (F : C ⥤ D) {X₁ X₂ X₃ X₄ X₅ X₆ X₇ : D} {Y Z W : C}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅) (g : X₅ ⟶ X₆) (m : X₆ ⟶ X₇)
    (p : X₇ ⟶ F.obj Y) (n : Y ⟶ Z) {k k' : Z ⟶ W} (hk : k = k') :
    a ≫ b ≫ c ≫ d ≫ g ≫ m ≫ p ≫ F.map (n ≫ k) =
      a ≫ b ≫ c ≫ d ≫ g ≫ m ≫ p ≫ F.map (n ≫ k') := by
  subst hk
  rfl

end CategoryTheory.Functor

open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

namespace Dualizing.ProjectionFormula

open CochainComplex CochainComplex.DerivedTensor CochainComplex.KFlat.ScalarBaseChange
open CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe u v

variable {A B : Type u} [CommRing A] [CommRing B]

/-! ### The value of the left-hand side -/

/-- **The inverse projection formula at a K-flat representative, followed by derived restriction
of a morphism.** -/
theorem derivedProjNatIso_inv_app_Q_comp (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, max u v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, max u v} P)
    (L : CochainComplex (ModuleCat.{max u v} B) ℤ)
    {T : DerivedCategory (ModuleCat.{max u v} B)}
    (k : (tensorRightDerived.{u, max u v} B
      (E.functor.obj (DerivedCategory.Q.obj P))).obj (DerivedCategory.Q.obj L) ⟶ T) :
    (derivedProjNatIso.{u, max u v} φ E iStar adj (DerivedCategory.Q.obj P)).inv.app
          (DerivedCategory.Q.obj L) ≫ iStar.map k =
      (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ iStar adj).hom.app
            (DerivedCategory.Q.obj L)) ≫
        (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app L) ≫
          (derivedTensor_comparison.{u, max u v} A
              ((restrictScalarsLarge.{max u v, u, u} φ).obj L) P hP).hom ≫
            DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, max u v} φ P L).inv ≫
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, max u v}
                    ((extendScalarsLarge.{max u v, u, u} φ).obj P)).obj L) ≫
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                    (derivedTensor_comparison.{u, max u v} B L
                      ((extendScalarsLarge.{max u v, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, max u v} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ iStar adj).inv.app
                      ((tensorRightDerived.{u, max u v} B
                        (DerivedCategory.Q.obj
                          ((extendScalarsLarge.{max u v, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj L)) ≫
                    iStar.map
                      ((((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, max u v,
                              max u v + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, max u v} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj L)) ≫ k) :=
  Functor.comp_eight_map_comp iStar _ _ _ _ _ _ _ _ _ k
    (derivedProjNatIso_inv_app_Q.{u, max u v} φ E iStar adj P hP L)

/-- **The same at equal universes, with the chain-level projection formula replaced by the lax
tensor map of restriction of scalars.** -/
theorem derivedProjNatIso_inv_app_Q_comp_laxTensor (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, u, u} φ)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : IsKFlat.{u, u} P)
    (L : CochainComplex (ModuleCat.{u} B) ℤ)
    {T : DerivedCategory (ModuleCat.{u} B)}
    (k : (tensorRightDerived.{u, u} B
      (E.functor.obj (DerivedCategory.Q.obj P))).obj (DerivedCategory.Q.obj L) ⟶ T) :
    (derivedProjNatIso.{u, u} φ E iStar adj (DerivedCategory.Q.obj P)).inv.app
          (DerivedCategory.Q.obj L) ≫ iStar.map k =
      (tensorRightDerived.{u, u} A (DerivedCategory.Q.obj P)).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, u} φ iStar adj).hom.app
            (DerivedCategory.Q.obj L)) ≫
        (tensorRightDerived.{u, u} A (DerivedCategory.Q.obj P)).map
            ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.hom.app L) ≫
          (derivedTensor_comparison.{u, u} A
              ((restrictScalarsLarge.{u, u, u} φ).obj L) P hP).hom ≫
            DerivedCategory.Q.map
                ((𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) ⊗ₘ
                    (CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj φ).unit.app P) ≫
                  CochainComplex.ExtendScalars.restrictScalarsLaxTensor φ L
                    ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj P)) ≫
              (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, u}
                    ((extendScalarsLarge.{u, u, u} φ).obj P)).obj L) ≫
                (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map
                    (derivedTensor_comparison.{u, u} B L
                      ((extendScalarsLarge.{u, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, u} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, u} φ iStar adj).inv.app
                      ((tensorRightDerived.{u, u} B
                        (DerivedCategory.Q.obj
                          ((extendScalarsLarge.{u, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj L)) ≫
                    iStar.map
                      ((((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, u} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj L)) ≫ k) :=
  Functor.comp_eight_map_comp_congr iStar _ _ _ _ _ _ _ _ k
    (congrArg DerivedCategory.Q.map
      (CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq φ P L))
    (derivedProjNatIso_inv_app_Q.{u, u} φ E iStar adj P hP L)

/-! ### The choice of a localized presentation of the internal Hom -/

/-- The complex of `B`-modules presenting the scalar transport of a complex of
`ULift B`-modules. -/
abbrev scalarTransportComplex (B : Type u) [CommRing B]
    (Y : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ) :
    CochainComplex (ModuleCat.{max u v} B) ℤ :=
  ((uliftModuleEquivalence.{u, max u v, max u v} B).functor.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj Y

/-- Localization commutes with the scalar transport of cochain complexes. -/
def scalarTransportQIso (B : Type u) [CommRing B]
    (Y : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ) :
    (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj Y) ≅
      DerivedCategory.Q.obj (scalarTransportComplex.{u, v} B Y) :=
  (uliftModuleEquivalence.{u, max u v, max u v} B).functor.mapDerivedCategoryFactors.app Y

/-- The complex of `B`-modules presenting the K-injective Hom model. -/
abbrev homModelComplex (B : Type u) [CommRing B]
    (X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ) :
    CochainComplex (ModuleCat.{max u v} B) ℤ :=
  scalarTransportComplex.{u, v} B (CochainComplex.HomComplexR (ULift.{max u v} B) X I)

/-- **A localized presentation of the internal Hom of [stacks 0A63].**  The K-injective Hom model
`StacksDraft.DerivedHom.derivedHomModelIso`, conjugated by a comparison `g` of the model `E` at
`P` with the scalar transport of a K-flat complex, and read through
`Dualizing.ProjectionFormula.scalarTransportQIso`: so the source is the class of a cochain complex
of `B`-modules, which is what
`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q` asks for. -/
def homModelQIso (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ) [I.IsKInjective]
    (g : E.functor.obj (DerivedCategory.Q.obj P) ≅
      (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj X)) :
    DerivedCategory.Q.obj (homModelComplex.{u, v} B X I) ≅
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
        (Opposite.op (E.functor.obj (DerivedCategory.Q.obj P)),
          (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
            (DerivedCategory.Q.obj I)) :=
  (scalarTransportQIso.{u, v} B
        (CochainComplex.HomComplexR (ULift.{max u v} B) X I)).symm ≪≫
    (derivedHomModelIso.{u, max u v, max u v + 1} B X I).symm ≪≫
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.mapIso
        (g.op.prod (Iso.refl
          ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
            (DerivedCategory.Q.obj I))))

/-- `Dualizing.ProjectionFormula.homModelQIso` as the composite it is. -/
theorem homModelQIso_hom (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ) [I.IsKInjective]
    (g : E.functor.obj (DerivedCategory.Q.obj P) ≅
      (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj X)) :
    (homModelQIso.{u, v} φ E P X I g).hom =
      (scalarTransportQIso.{u, v} B
          (CochainComplex.HomComplexR (ULift.{max u v} B) X I)).inv ≫
        (derivedHomModelIso.{u, max u v, max u v + 1} B X I).inv ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.map
            (show (Opposite.op ((derivedScalarEquivalence.{u, max u v,
                    max u v + 1} B).functor.obj (DerivedCategory.Q.obj X)),
                (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I)) ⟶
              (Opposite.op (E.functor.obj (DerivedCategory.Q.obj P)),
                (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I)) from
              (g.hom.op, 𝟙 ((derivedScalarEquivalence.{u, max u v,
                max u v + 1} B).functor.obj (DerivedCategory.Q.obj I)))) :=
  rfl

/-- **The chain-level transpose of the chosen presentation.**  The comparison `g` whiskered into
the second variable, the K-flat tensor model
`StacksDraft.DerivedHom.derivedTensorModelIso`, and the localized chain-level evaluation
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`. -/
def modelEvaluation (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ) (hX : X.KFlat)
    (g : E.functor.obj (DerivedCategory.Q.obj P) ≅
      (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj X)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
        (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I),
          E.functor.obj (DerivedCategory.Q.obj P)) ⟶
      (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj I) :=
  (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
      (X := (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I),
        E.functor.obj (DerivedCategory.Q.obj P)))
      (Y := ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{max u v} B) X I)),
        E.functor.obj (DerivedCategory.Q.obj P)))
      ((scalarTransportQIso.{u, v} B
          (CochainComplex.HomComplexR (ULift.{max u v} B) X I)).inv,
        𝟙 (E.functor.obj (DerivedCategory.Q.obj P))) ≫
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
        (X := ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
            (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{max u v} B) X I)),
          E.functor.obj (DerivedCategory.Q.obj P)))
        (Y := ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
            (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{max u v} B) X I)),
          (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
            (DerivedCategory.Q.obj X)))
        (𝟙 ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{max u v} B) X I))),
          g.hom) ≫
      (derivedTensorModelIso.{u, max u v, max u v + 1} B
          (CochainComplex.HomComplexR (ULift.{max u v} B) X I) X hX).hom ≫
        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.map
          (DerivedCategory.Q.map (DerivedInternalHom.Model.evaluationMor X I))

/-- **The [stacks 0A63] transpose of the chosen presentation is the chain-level evaluation.**
`StacksDraft.DerivedHom.homEquiv_derivedHomModelIso_inv_comp` after naturality of the transpose
in its first variable. -/
theorem homEquiv_homModelQIso_hom (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ)
    (hX : X.KFlat) [I.IsKInjective]
    (g : E.functor.obj (DerivedCategory.Q.obj P) ≅
      (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj X)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homEquiv
        (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))
        (E.functor.obj (DerivedCategory.Q.obj P))
        ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj I))
        (homModelQIso.{u, v} φ E P X I g).hom =
      modelEvaluation.{u, v} φ E P X I hX g := by
  rw [modelEvaluation, homModelQIso_hom.{u, v} φ E P X I g,
    DerivedHomAdjunction.homEquiv_naturality_left,
    homEquiv_derivedHomModelIso_inv_comp.{u, max u v, max u v + 1} B X I hX
      (E.functor.obj (DerivedCategory.Q.obj P)) g.hom]

/-! ### The first residue of [stacks 0E2H] at a localized presentation -/

/-- **The first residue of [stacks 0E2H] at a localized presentation of the internal Hom.**
`Dualizing.ProjectionFormula.projCounitCompat_of_mate_model` with the existential witness taken to
be the class of the cochain complex `Dualizing.ProjectionFormula.homModelComplex` of `B`-modules
and the presentation taken to be `Dualizing.ProjectionFormula.homModelQIso`.  The K-flat complex
`X` and the comparison `g` are supplied by `StacksDraft.DerivedHom.exists_kFlat_model`. -/
theorem projCounitCompat_of_mate_Q (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P →
      ∀ X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ,
      X.KFlat → ∀ _hI : I.IsKInjective,
      ∀ g : E.functor.obj (DerivedCategory.Q.obj P) ≅
        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj X),
        (derivedProjNatIso.{u, max u v} φ E _ adj (DerivedCategory.Q.obj P)).inv.app
              (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I)) ≫
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homEquiv
                (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))
                (E.functor.obj (DerivedCategory.Q.obj P))
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I))
                (homModelQIso.{u, v} φ E P X I g).hom) =
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I)))
            (DerivedCategory.Q.obj P)
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                (DerivedCategory.Q.obj I)))
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                (homModelQIso.{u, v} φ E P X I g).hom ≫
              homRestrictComponent.{u, v} φ E (DerivedCategory.Q.obj P)
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I))))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  refine projCounitCompat_of_mate_model.{u, v} φ E adj (fun P hP I hI => ?_) N
  have := hI
  obtain ⟨X, hX, ⟨gx⟩⟩ := exists_kFlat_model.{u, max u v, max u v + 1} (R := B)
    (E.functor.obj (DerivedCategory.Q.obj P))
  exact ⟨_, _, h P hP X I hX hI gx.symm⟩

/-- **The first residue of [stacks 0E2H] with the inverse projection formula expanded leg by
leg.**  `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q` with its left-hand side valued by
`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q_comp`: the eight legs of
`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q`, whose only non-bookkeeping factor is
the chain-level projection formula
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso`, followed by derived restriction of
the [stacks 0A63] transpose of the presentation. -/
theorem projCounitCompat_of_mate_Q_legs (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P,
      ∀ X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ,
      X.KFlat → ∀ _hI : I.IsKInjective,
      ∀ g : E.functor.obj (DerivedCategory.Q.obj P) ≅
        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj X),
        (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
            ((leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).hom.app
              (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
          (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
                (homModelComplex.{u, v} B X I)) ≫
            (derivedTensor_comparison.{u, max u v} A
                ((restrictScalarsLarge.{max u v, u, u} φ).obj
                  (homModelComplex.{u, v} B X I)) P hP).hom ≫
              DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, max u v} φ P
                (homModelComplex.{u, v} B X I)).inv ≫
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app
                    ((tensorRightLarge.{u, max u v}
                      ((extendScalarsLarge.{max u v, u, u} φ).obj P)).obj
                      (homModelComplex.{u, v} B X I)) ≫
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                      (derivedTensor_comparison.{u, max u v} B
                        (homModelComplex.{u, v} B X I)
                        ((extendScalarsLarge.{max u v, u, u} φ).obj P)
                        (isKFlat_extendScalarsLarge.{u, max u v} φ P hP)).inv ≫
                    (leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).inv.app
                        ((tensorRightDerived.{u, max u v} B
                          (DerivedCategory.Q.obj
                            ((extendScalarsLarge.{max u v, u, u} φ).obj P))).obj
                          (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                        ((((Functor.curry.obj
                              (derivedHomAdjunctionOverRing.{u, max u v,
                                max u v + 1} B).tensor).flip.mapIso
                          (@asIso _ _ _ _ (E.comparison.app P)
                            (E.comparison_isIso_of_kFlat P
                              ((isKFlat_iff_kFlat.{u, max u v} P).mp hP)))).inv.app
                          (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homEquiv
                            (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))
                            (E.functor.obj (DerivedCategory.Q.obj P))
                            ((derivedScalarEquivalence.{u, max u v,
                              max u v + 1} B).functor.obj (DerivedCategory.Q.obj I))
                            (homModelQIso.{u, v} φ E P X I g).hom) =
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I)))
            (DerivedCategory.Q.obj P)
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                (DerivedCategory.Q.obj I)))
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                (homModelQIso.{u, v} φ E P X I g).hom ≫
              homRestrictComponent.{u, v} φ E (DerivedCategory.Q.obj P)
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I))))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N :=
  projCounitCompat_of_mate_Q.{u, v} φ E adj
    (fun P hP X I hX hI g =>
      (derivedProjNatIso_inv_app_Q_comp.{u, v} φ E _ adj P hP
        (homModelComplex.{u, v} B X I) _).trans (h P hP X I hX hI g)) N

/-- **The first residue of [stacks 0E2H] with the whole left-hand side at chain level.**
`Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_legs` with the [stacks 0A63] transpose of
the presentation replaced by `Dualizing.ProjectionFormula.modelEvaluation`, which it is by
`Dualizing.ProjectionFormula.homEquiv_homModelQIso_hom`.

So the whole of `Dualizing.ProjectionFormula.ProjCounitCompat`, at every object of `D(A)`, follows
from one equation whose left-hand side mentions no derived internal Hom and no evaluation of
[stacks 0A63]: only the eight legs of
`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q`, the K-flat tensor model and the
localized chain-level evaluation
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`. -/
theorem projCounitCompat_of_mate_Q_evaluationMor (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P,
      ∀ X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ,
      ∀ hX : X.KFlat, ∀ _hI : I.IsKInjective,
      ∀ g : E.functor.obj (DerivedCategory.Q.obj P) ≅
        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj X),
        (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
            ((leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).hom.app
              (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
          (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
                (homModelComplex.{u, v} B X I)) ≫
            (derivedTensor_comparison.{u, max u v} A
                ((restrictScalarsLarge.{max u v, u, u} φ).obj
                  (homModelComplex.{u, v} B X I)) P hP).hom ≫
              DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, max u v} φ P
                (homModelComplex.{u, v} B X I)).inv ≫
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app
                    ((tensorRightLarge.{u, max u v}
                      ((extendScalarsLarge.{max u v, u, u} φ).obj P)).obj
                      (homModelComplex.{u, v} B X I)) ≫
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                      (derivedTensor_comparison.{u, max u v} B
                        (homModelComplex.{u, v} B X I)
                        ((extendScalarsLarge.{max u v, u, u} φ).obj P)
                        (isKFlat_extendScalarsLarge.{u, max u v} φ P hP)).inv ≫
                    (leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).inv.app
                        ((tensorRightDerived.{u, max u v} B
                          (DerivedCategory.Q.obj
                            ((extendScalarsLarge.{max u v, u, u} φ).obj P))).obj
                          (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                        ((((Functor.curry.obj
                              (derivedHomAdjunctionOverRing.{u, max u v,
                                max u v + 1} B).tensor).flip.mapIso
                          (@asIso _ _ _ _ (E.comparison.app P)
                            (E.comparison_isIso_of_kFlat P
                              ((isKFlat_iff_kFlat.{u, max u v} P).mp hP)))).inv.app
                          (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                          modelEvaluation.{u, v} φ E P X I hX g) =
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I)))
            (DerivedCategory.Q.obj P)
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                (DerivedCategory.Q.obj I)))
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                (homModelQIso.{u, v} φ E P X I g).hom ≫
              homRestrictComponent.{u, v} φ E (DerivedCategory.Q.obj P)
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I))))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N :=
  projCounitCompat_of_mate_Q_legs.{u, v} φ E adj
    (fun P hP X I hX hI g =>
      (Functor.comp_eight_map_comp_last
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory _ _ _ _ _ _ _ _
          (homEquiv_homModelQIso_hom.{u, v} φ E P X I hX g)).trans
        (h P hP X I hX hI g)) N

end Dualizing.ProjectionFormula

end
