module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules

/-!
# Higher direct images of unbounded complexes on the small étale site

Let `f : X ⟶ Y` be a morphism in a big étale site. The unbounded clause of Stacks 03Q8 says
that `Rf_*` is computed by the presheaf `V ↦ RΓ(X ×_Y V, -)` on the small étale site of `Y`.
The vocabulary is set up in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage`; what is proved
here is the assertion `DerivedPushforwardComparison`: the canonical comparison
`derivedSheafificationComparison` is invertible, evaluating the derived presheaf of sections at
`V` is the total right derived functor of sections over `X ×_Y V`, and the restriction maps of
the hypercohomology presheaf are the derived restriction maps of sections.

The first two assertions say that K-injective complexes compute all the derived functors
involved. At a K-injective complex of sheaves on `X` the units of `Rf_*`, of the derived
presheaf of sections and of derived sections over `X ×_Y V` are all invertible, and a
transformation of functors on the unbounded derived category which is invertible on the images
of K-injective complexes is invertible. This is where the Grothendieck abelian hypothesis on
the sheaves on `X` enters: it provides the functorial K-injective resolutions.

The third assertion is proved by a universal property rather than by computing the comparison.
Evaluation at `V` and at `U` are both right derived functors of sections, so the derived
transformation between them is the *unique* one compatible with the two units. The
transformation that postcomposition with the restriction `ev_V ⟶ ev_U` of evaluation functors
induces on unbounded derived categories is compatible with those units, hence equals it; and
that induced transformation commutes with taking homology because postcomposition with an
exact functor does.

## Main results

* `Stacks.HigherDirectImage.derivedPushforwardComparison` — the unbounded clause of Stacks
  03Q8: the canonical comparison of `Rf_*` with the sheafified derived presheaf of sections
  over the étale base changes is invertible, evaluation at `V` is derived sections over
  `X ×_Y V`, and the restriction maps are the derived restriction maps.

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)

Tags covered: 03Q8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.HigherDirectImage

open Stacks.DerivedFunctor

attribute [local instance] HasDerivedCategory.standard

/-! ### Naturality in the exact functor

The comparisons of `Comparison.DerivedFunctor` are attached to a single exact functor. The
transformation `Stacks.DerivedFunctor.mapDerivedNatTrans τ` of the functors induced on unbounded
derived categories by a transformation `τ : T ⟶ S` of exact functors, and the naturality in `τ`
of the comparison with homology, are
`StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans`; what is added here is
the naturality of the comparison with localization. -/

section General

variable {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory D]
  {T S : A ⥤ D} [T.Additive] [S.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

variable {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]

/-- For the identity comparison, `Stacks.DerivedFunctor.postcompHomotopyIso` is the
factorization of the postcomposed functor through the homotopy category. -/
private lemma postcompHomotopyIso_refl_hom_app
    (P : A ⥤ D) [P.Additive] (T : D ⥤ E) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (X : HomotopyCategory A (.up ℤ)) :
    (Stacks.DerivedFunctor.postcompHomotopyIso P T (P ⋙ T) (Iso.refl _)).hom.app X =
      T.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj X) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  dsimp only [Stacks.DerivedFunctor.postcompHomotopyIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app]
  change _ ≫ _ ≫ _ ≫ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (𝟙 _)) = _
  simp only [CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans
    (((Category.assoc _ _ _).symm.trans (Category.comp_id _)).trans (Category.comp_id _))

/-- `Stacks.DerivedFunctor.postcompHomotopyIso` for the identity comparison is natural in the
exact functor that is postcomposed. -/
private lemma postcompHomotopyIso_refl_naturality
    (P : A ⥤ D) [P.Additive] {T S : D ⥤ E} [T.Additive] [S.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (τ : T ⟶ S) :
    Functor.whiskerLeft (P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
        (mapDerivedNatTrans τ) ≫
        (Stacks.DerivedFunctor.postcompHomotopyIso P S (P ⋙ S) (Iso.refl _)).hom =
      (Stacks.DerivedFunctor.postcompHomotopyIso P T (P ⋙ T) (Iso.refl _)).hom ≫
        Functor.whiskerRight ((Functor.whiskerLeft P τ).mapHomotopyCategory (.up ℤ))
          DerivedCategory.Qh := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    postcompHomotopyIso_refl_hom_app]
  exact NatTrans.congr_app (mapDerivedNatTrans_homotopy_fac τ)
    ((P.mapHomotopyCategory (.up ℤ)).obj K)

/-- A commuting square with two isomorphic sides stays commuting after inverting them. -/
private lemma inv_comp_eq_comp_inv_of_comp_hom_eq {C : Type*} [Category C] {A B P Q : C}
    (e : A ≅ B) (e' : P ≅ Q) {a : A ⟶ P} {b : B ⟶ Q} (h : a ≫ e'.hom = e.hom ≫ b) :
    e.inv ≫ a = b ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at *
  simpa using h

end General

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [HasSheafify (JX B (X := X)) AddCommGrpCat.{w}]
  [(homotopyPreimageSectionsPresheaf.{u, w} B f).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))]

/-! ### The restriction maps of the hypercohomology presheaf -/

/-- The unit exhibiting evaluation at `V` as derived sections over `X ×_Y V` is natural in `V`:
restriction of sections on the homotopy category is carried to the transformation that
restriction of evaluation functors induces on derived categories. -/
private lemma evaluatedDerivedSectionsUnit_naturality
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    evaluatedDerivedSectionsUnit.{u, w} B f V ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (derivedPreimageSectionsPresheaf B f)
            (mapDerivedNatTrans ((evaluation _ AddCommGrpCat.{w}).map g.op))) =
      Functor.whiskerRight ((sectionsRestriction B f g).mapHomotopyCategory (.up ℤ))
          DerivedCategory.Qh ≫ evaluatedDerivedSectionsUnit B f U := by
  let P := preimageSectionsPresheaf.{u, w} B f
  let T := (evaluation _ AddCommGrpCat.{w}).obj (Opposite.op V)
  let S := (evaluation _ AddCommGrpCat.{w}).obj (Opposite.op U)
  let τ : T ⟶ S := (evaluation _ AddCommGrpCat.{w}).map g.op
  let β := (homotopyPreimageSectionsPresheaf B f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))
  let eT := Stacks.DerivedFunctor.postcompHomotopyIso P T (P ⋙ T) (Iso.refl _)
  let eS := Stacks.DerivedFunctor.postcompHomotopyIso P S (P ⋙ S) (Iso.refl _)
  ext K
  have he' := inv_comp_eq_comp_inv_of_comp_hom_eq (eT.app K) (eS.app K)
    (NatTrans.congr_app (postcompHomotopyIso_refl_naturality P τ) K)
  simp only [Iso.app_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he'
  simp only [evaluatedDerivedSectionsUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id]
  change (eT.inv.app K ≫ T.mapDerivedCategory.map (β.app K)) ≫
      (mapDerivedNatTrans τ).app
        ((DerivedCategory.Qh ⋙ derivedPreimageSectionsPresheaf B f).obj K) =
    DerivedCategory.Qh.map (((sectionsRestriction B f g).mapHomotopyCategory (.up ℤ)).app K) ≫
      eS.inv.app K ≫ S.mapDerivedCategory.map (β.app K)
  rw [Category.assoc, (mapDerivedNatTrans τ).naturality, ← Category.assoc, he', Category.assoc]
  rfl

/-- The derived restriction map between evaluations at `V` and at `U` is the transformation
that restriction of evaluation functors induces on derived categories: both are compatible with
the two units, and the derived transformation is the unique such. -/
private lemma evaluatedDerivedSections_rightDerivedNatTrans
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    (hV : (evaluatedDerivedSections.{u, w} B f V).IsRightDerivedFunctor
      (evaluatedDerivedSectionsUnit B f V)
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))) :
    letI := hV
    (evaluatedDerivedSections B f V).rightDerivedNatTrans
        (evaluatedDerivedSections B f U)
        (evaluatedDerivedSectionsUnit B f V) (evaluatedDerivedSectionsUnit B f U)
        (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))
        (Functor.whiskerRight ((sectionsRestriction B f g).mapHomotopyCategory (.up ℤ))
          DerivedCategory.Qh) =
      Functor.whiskerLeft (derivedPreimageSectionsPresheaf B f)
        (mapDerivedNatTrans ((evaluation _ AddCommGrpCat.{w}).map g.op)) := by
  let _ := hV
  apply Functor.rightDerived_ext _ (evaluatedDerivedSectionsUnit B f V)
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))
  rw [Functor.rightDerivedNatTrans_fac]
  exact (evaluatedDerivedSectionsUnit_naturality B f g).symm

/-- The restriction maps of the hypercohomology presheaf are the derived restriction maps of
sections: under the identification of evaluation of the hypercohomology presheaf with homology
of the evaluated derived sections, restriction along `g : U ⟶ V` becomes
`hypercohomologyRestriction`. -/
private lemma preimageHypercohomologyPresheafEvaluationIso_naturality
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V)
    (hV : (evaluatedDerivedSections.{u, w} B f V).IsRightDerivedFunctor
      (evaluatedDerivedSectionsUnit B f V)
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ)))
    (i : ℤ) (K : DerivedCategory (Sheaf (JX B (X := X)) AddCommGrpCat.{w})) :
    (preimageHypercohomologyPresheaf B f K i).map g.op ≫
        (preimageHypercohomologyPresheafEvaluationIso B f U i).hom.app K =
      (preimageHypercohomologyPresheafEvaluationIso B f V i).hom.app K ≫
        (hypercohomologyRestriction B f g hV i).app K := by
  let T := (evaluation _ AddCommGrpCat.{w}).obj (Opposite.op V)
  let S := (evaluation _ AddCommGrpCat.{w}).obj (Opposite.op U)
  let K' := (derivedPreimageSectionsPresheaf B f).obj K
  have h := NatTrans.congr_app
    (derivedHomologyIso_naturality ((evaluation _ AddCommGrpCat.{w}).map g.op) i) K'
  have h' := inv_comp_eq_comp_inv_of_comp_hom_eq
    ((Stacks.DerivedFunctor.derivedHomologyIso T i).app K')
    ((Stacks.DerivedFunctor.derivedHomologyIso S i).app K') h
  simp only [hypercohomologyRestriction, evaluatedDerivedSections_rightDerivedNatTrans,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [preimageHypercohomologyPresheafEvaluationIso,
    preimageHypercohomologyPresheaf, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id]
  convert h'.symm using 1 <;> rfl

/-! ### Invertibility and the universal property of evaluation -/

variable [IsGrothendieckAbelian.{w} (Sheaf (JX B (X := X)) AddCommGrpCat.{w})]

/-- Evaluation at `V` is the total right derived functor of sections over `X ×_Y V`: its unit
is invertible at every K-injective complex, because the unit of the derived presheaf of sections
is and evaluation is exact. -/
private lemma evaluatedDerivedSections_isRightDerivedFunctor_of_grothendieck
    (V : SmallEtale B Y.obj Y.property) :
    (evaluatedDerivedSections.{u, w} B f V).IsRightDerivedFunctor
      (evaluatedDerivedSectionsUnit B f V)
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (homotopyPreimageSectionsPresheaf.{u, w} B f) (derivedPreimageSectionsPresheaf B f)
    ((homotopyPreimageSectionsPresheaf B f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))) I
  dsimp [evaluatedDerivedSectionsUnit]
  infer_instance

variable [HasSheafify (JY B (Y := Y)) AddCommGrpCat.{w}]
  [(homotopyPushforward.{u, w} B f).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ))]

/-- The canonical comparison is invertible: it is so on the image of a K-injective complex,
where both units are invertible, and such a transformation of functors on the unbounded derived
category is invertible. -/
private lemma derivedSheafificationComparison_isIso_of_grothendieck :
    IsIso (derivedSheafificationComparison.{u, w} B f) := by
  apply Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives
  intro I hI
  let qI := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let P := homotopyPushforward.{u, w} B f
  let Q := homotopyPreimageSectionsPresheaf.{u, w} B f
  let W := HomotopyCategory.quasiIso (Sheaf (JX B (X := X)) AddCommGrpCat.{w}) (.up ℤ)
  let α := P.totalRightDerivedUnit DerivedCategory.Qh W
  let β := Q.totalRightDerivedUnit DerivedCategory.Qh W
  have hα : IsIso (α.app qI) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective P _ α I
  have hβ : IsIso (β.app qI) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective Q _ β I
  unfold derivedSheafificationComparison
  apply (isIso_comp_left_iff (α.app qI) _).mp
  rw [Functor.rightDerived_fac_app]
  dsimp
  infer_instance

/-- **Stacks 03Q8, unbounded complexes.** The canonical comparison of `Rf_*` with the sheafified
derived presheaf of sections over the étale base changes is invertible, evaluating the derived
presheaf of sections at `V` is the total right derived functor of sections over `X ×_Y V`, and
the restriction maps of the hypercohomology presheaf are the derived restriction maps of
sections. -/
@[stacks 03Q8 "unbounded complexes"]
public theorem derivedPushforwardComparison : DerivedPushforwardComparison.{u, w} B f := by
  have he := evaluatedDerivedSections_isRightDerivedFunctor_of_grothendieck.{u, w} B f
  exact
    { isIso := derivedSheafificationComparison_isIso_of_grothendieck B f
      evaluation := he
      restriction := fun g i K ↦
        preimageHypercohomologyPresheafEvaluationIso_naturality B f g (he _) i K }

end Stacks.HigherDirectImage
