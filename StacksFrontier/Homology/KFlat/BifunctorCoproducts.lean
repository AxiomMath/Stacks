module

public import StacksFrontier.Homology.KFlat.BifunctorOneSidedLeft
public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts

/-!
# The derived bifunctor commutes with direct sums in its second variable

Let `F : A ⥤ B ⥤ D` be a bifunctor of abelian categories such that each `F(X, -)` commutes with
coproducts of a given shape `Discrete J`, and suppose that the localization functors
`C(B) ⥤ D(B)` and `C(D) ⥤ D(D)` preserve those coproducts.  Then for every `K ∈ D(A)` the functor
`K ⊗^L - := (derivedBifunctor F).obj K` commutes with them.

Represent `K` by a complex `P` which is K-flat in the left variable.  On complexes the functor
`K ⊗^L -` is then `Q ∘ Tot(F(P, -))` (`CochainComplex.KFlatBifunctor.derivedBifunctorLeftIso`,
the one-sided comparison, which places no hypothesis on the second variable), and
`Tot(F(P, -))` commutes with coproducts because `F(Pᵖ, -)` does in each degree.  Since the
localization functor `Q` is essentially surjective and preserves the coproducts, the descended
functor does too (`preservesColimitsOfShape_discrete_of_essSurj_comp`).

## Main results

* `CochainComplex.KFlatBifunctor.derivedBifunctor_obj_preservesColimitsOfShape_discrete`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

omit [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- **The derived bifunctor commutes with direct sums in its second variable**: for every
`K ∈ D(A)`, the functor `(derivedBifunctor F).obj K` preserves coproducts of shape `Discrete J`
as soon as every `F(X, -)` does and the localization functors of `B` and `D` do. -/
theorem derivedBifunctor_obj_preservesColimitsOfShape_discrete (J : Type*)
    [HasColimitsOfShape (Discrete J) B] [HasColimitsOfShape (Discrete J) D]
    (hF : ∀ X : A, PreservesColimitsOfShape (Discrete J) (F.obj X))
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := B))]
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := D))]
    (K : DerivedCategory A) :
    PreservesColimitsOfShape (Discrete J) ((derivedBifunctor F).obj K) := by
  have := Localization.essSurj (kFlatQLeft F) (kFlatQuasiIsoLeft F)
  let P := (kFlatQLeft F).objPreimage K
  let G : DerivedCategory B ⥤ DerivedCategory D :=
    derivedToDerivedLeft F ⋙ (evaluation _ _).obj P
  let e₀ : (derivedBifunctor F).obj ((kFlatQLeft F).obj P) ≅ G :=
    NatIso.ofComponents (fun L ↦ ((derivedBifunctorLeftIso F).app L).app P)
      (fun g ↦ NatTrans.congr_app ((derivedBifunctorLeftIso F).hom.naturality g) P)
  let e : (derivedBifunctor F).obj K ≅ G :=
    (derivedBifunctor F).mapIso ((kFlatQLeft F).objObjPreimageIso K).symm ≪≫ e₀
  let T := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj P.obj.as
  have hT : PreservesColimitsOfShape (Discrete J) T := by
    have := preservesColimitsOfShape_mapBifunctorObj (J := Discrete J) F P.obj.as hF
    have := preservesColimitsOfShape_totalFunctor (D := D) (J := Discrete J)
    have : PreservesColimitsOfShape (Discrete J) (totFunctor F P.obj.as) :=
      comp_preservesColimitsOfShape (J := Discrete J) _ _
    exact preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
        dsimp only [totFunctor, T, Functor.comp_map, Iso.refl_hom]
        refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
        simp only [Functor.comp_obj, HomologicalComplex₂.totalFunctor_map,
          Functor.map₂HomologicalComplex_obj_map, HomologicalComplex.mapBifunctorMap,
          CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
        congr 1) : totFunctor F P.obj.as ≅ T)
  let e₁ : DerivedCategory.Q ⋙ G ≅ T ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedToDerivedLeftFac F) _ ≪≫
      Functor.isoWhiskerRight ((homotopyBifunctorLiftingIso F).app P.obj.as)
        DerivedCategory.Qh ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  have : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q ⋙ G) :=
    preservesColimitsOfShape_of_natIso e₁.symm
  have : PreservesColimitsOfShape (Discrete J) G :=
    preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q G J
  exact preservesColimitsOfShape_of_natIso e.symm

end CochainComplex.KFlatBifunctor

end
