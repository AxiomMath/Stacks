module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsEquivBaseChange

/-!
# The bijection of Tag 0B3V and base change, along an arbitrary identification `ℰ' ≅ g^*ℰ`

Let `g : X ⟶ Y` be a morphism of schemes, `ℰ` a quasi-coherent `𝒪_Y`-module and `ℰ'` a
quasi-coherent `𝒪_X`-module with an identification `ℰ' ≅ g^*ℰ`.  If a section `σ'` of
`𝐏(ℰ') ⟶ X` lies over a section `σ` of `𝐏(ℰ) ⟶ Y` along the base-change morphism
`𝐏(ℰ') ⟶ 𝐏(ℰ)`, then the invertible quotient of `ℰ'` classified by `σ'` is the base change of the
one classified by `σ`, read along the identification.

## Main results

* `Stacks.RelativeProj.classifies_of_comp_projectiveBundleBaseChange`: the classification
  statement for an arbitrary tautological datum on `𝐏(ℰ)` and its base change.
* `Stacks.RelativeProj.projectiveBundleSectionsEquiv_baseChange_of_iso`: the statement for the
  canonical bijections.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- The identification of `ℰ'` with `σ'^*b^*π^*ℰ`, through the base-change identification of
the pulled-back modules and a section `σ'` lying over `σ`, is `ℰ' ≅ g^*ℰ` followed by the pullback
along `g` of the identification of `ℰ` with `σ^*π^*ℰ`. -/
@[reassoc] theorem key_coherence_of_iso (σ : Y ⟶ projectiveBundle Y E)
    (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) (σ' : X ⟶ projectiveBundle X E')
    (hσ' : σ' ≫ projectiveBundleToBase X E' = 𝟙 X)
    (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ) :
    (Scheme.Modules.pullbackId X).inv.app E' ≫
        (Scheme.Modules.pullbackCongr hσ').inv.app E' ≫
        (Scheme.Modules.pullbackComp σ' (projectiveBundleToBase X E')).inv.app E' ≫
        (Scheme.Modules.pullback σ').map (tautologicalBaseChangeIso g E E' hE).inv ≫
        (Stacks.Modules.pullbackSquareIso σ σ' (projectiveBundleBaseChange g E E' hE) g
            comm.symm).hom.app ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).obj E) =
      hE.hom ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).inv.app E) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackCongr hσ).inv.app E) ≫
        (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackComp σ (projectiveBundleToBase Y E)).inv.app E) := by
  have hnat₁ := (Scheme.Modules.pullbackId X).inv.naturality hE.hom
  have hnat₂ := (Scheme.Modules.pullbackCongr hσ').inv.naturality hE.hom
  have hnat₃ := (Scheme.Modules.pullbackComp σ' (projectiveBundleToBase X E')).inv.naturality
    hE.hom
  simp only [Functor.id_map, Functor.comp_map] at hnat₁ hnat₂ hnat₃
  simp only [Stacks.Modules.pullbackSquareIso, tautologicalBaseChangeIso, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnat₃, ← reassoc_of% hnat₂, ← reassoc_of% hnat₁]
  congr 1
  exact Stacks.Modules.sectionSquare_coherence_inv g σ (projectiveBundleToBase Y E) σ'
    (projectiveBundleToBase X E') (projectiveBundleBaseChange g E E' hE) hσ hσ'
    (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE) comm E

/-- **A section lying over a section classifies the base change of the quotient it lies over**,
for the base change of an arbitrary tautological datum along `ℰ' ≅ g^*ℰ`. -/
theorem classifies_of_comp_projectiveBundleBaseChange (D : TautologicalDatum Y E)
    (σ : Y ⟶ projectiveBundle Y E) (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y)
    (σ' : X ⟶ projectiveBundle X E') (hσ' : σ' ≫ projectiveBundleToBase X E' = 𝟙 X)
    (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ) :
    (D.baseChange g E E' hE).Classifies σ' hσ'
      (Stacks.ProjectiveBundleQuotients.InvertibleQuotient.baseChange g hE
        (D.pullbackQuotient σ hσ)) := by
  refine ⟨(Stacks.Modules.pullbackSquareIso σ σ' (projectiveBundleBaseChange g E E' hE) g
      comm.symm).app D.twist, ?_⟩
  have hnat := (Stacks.Modules.pullbackSquareIso σ σ' (projectiveBundleBaseChange g E E' hE) g
      comm.symm).hom.naturality D.univ
  simp only [TautologicalDatum.pullbackQuotient_q, TautologicalDatum.pullbackQuotientMap,
    Stacks.ProjectiveBundleQuotients.InvertibleQuotient.baseChange_q, Iso.app_hom]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (Category.assoc _ _ _))) ?_
  rw [TautologicalDatum.baseChange_univ]
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
    (Functor.map_comp_assoc _ _ _ _)))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ hnat)))) ?_
  refine Eq.trans (key_coherence_of_iso_assoc g E E' hE σ hσ σ' hσ' comm _) ?_
  simp only [Functor.comp_map]
  exact whisker_eq _ (((Scheme.Modules.pullback g).map_comp _ _).trans
    ((whisker_eq _ ((Scheme.Modules.pullback g).map_comp _ _)).trans
      (whisker_eq _ (whisker_eq _ ((Scheme.Modules.pullback g).map_comp _ _))))).symm

/-- The classification statement on isomorphism classes. -/
theorem sectionsMap_of_comp_projectiveBundleBaseChange (D : TautologicalDatum Y E)
    (σ : Y ⟶ projectiveBundle Y E) (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y)
    (σ' : X ⟶ projectiveBundle X E') (hσ' : σ' ≫ projectiveBundleToBase X E' = 𝟙 X)
    (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ) :
    (D.baseChange g E E' hE).sectionsMap ⟨σ', hσ'⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass g hE (D.sectionsMap ⟨σ, hσ⟩) :=
  ((D.baseChange g E E' hE).sectionsMap_eq_iff _ _).2
    (classifies_of_comp_projectiveBundleBaseChange g E E' hE D σ hσ σ' hσ' comm)

/-- **The bijection of Tag 0B3V is compatible with base change along an arbitrary
identification `ℰ' ≅ g^*ℰ`**: a section of `𝐏(ℰ') ⟶ X` lying over a section `σ` of
`𝐏(ℰ) ⟶ Y` goes to the base change of the class `σ` goes to. -/
theorem projectiveBundleSectionsEquiv_baseChange_of_iso (σ : Y ⟶ projectiveBundle Y E)
    (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y)
    (σ' : X ⟶ projectiveBundle X E') (hσ' : σ' ≫ projectiveBundleToBase X E' = 𝟙 X)
    (comm : σ' ≫ projectiveBundleBaseChange g E E' hE = g ≫ σ) :
    projectiveBundleSectionsEquiv ⟨σ', hσ'⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass g hE
        (projectiveBundleSectionsEquiv ⟨σ, hσ⟩) := by
  have h : ((tautologicalDatum E).baseChange g E E' hE).sectionsMap =
      (tautologicalDatum E').sectionsMap :=
    TautologicalDatum.sectionsMap_eq_of_univ_comp _ _
      (tautologicalDatumTwistBaseChangeIso g E E' hE)
      (tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom g E E' hE)
  have h' := sectionsMap_of_comp_projectiveBundleBaseChange g E E' hE (tautologicalDatum E) σ hσ
    σ' hσ' comm
  rw [h] at h'
  exact h'

end Stacks.RelativeProj

end
