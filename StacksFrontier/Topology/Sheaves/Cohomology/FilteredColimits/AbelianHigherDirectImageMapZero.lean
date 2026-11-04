module

public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.AbelianHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyViaSectionComplex

/-!
# A morphism of higher direct images vanishing over a basis

Let `f : X ⟶ Y` be a continuous map and `φ : F ⟶ G` a morphism of abelian sheaves on `X`. The
higher direct image `R^p f_*` is the sheafification of the presheaf `V ↦ H^p(f⁻¹(V), -)`
([Stacks, Tag 072W]), so `R^p f_* φ = 0` as soon as the maps `H^p(f⁻¹(V), F) ⟶ H^p(f⁻¹(V), G)`
induced by `φ` vanish for all `V` in a basis of `Y`.

## Main results

* `Stacks.Cohomology.AbelianSheaf.presheafToSheaf_map_eq_zero_of_isBasis`: a morphism of
  presheaves of abelian groups on a space vanishing on the opens of a basis has zero
  sheafification.
* `Stacks.Cohomology.AbelianSheaf.higherDirectImage_map_eq_zero_of_isBasis`: `R^p f_* φ = 0`
  when `φ` induces zero on `H^p(f⁻¹(V), -)` for all `V` in a basis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

namespace Stacks.Cohomology.AbelianSheaf

variable {X Y : TopCat.{v}}

/-- **A morphism of presheaves vanishing on a basis has zero sheafification.** If
`ψ : P ⟶ Q` is a morphism of presheaves of abelian groups on `Y` with `ψ(V) = 0` for every `V`
in a basis of `Y`, then the induced morphism of associated sheaves is zero: every section of the
sheafification of `P` is locally the image of a section of `P`, and restricting further into
the basis kills its image. -/
theorem presheafToSheaf_map_eq_zero_of_isBasis {P Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    (ψ : P ⟶ Q) (h : Opens.IsBasis {V : Opens Y | ψ.app (op V) = 0}) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v}).map ψ = 0 := by
  let J := Opens.grothendieckTopology Y
  have key : ∀ (U : Opens Y) (y : (sheafify J P).obj (op U)),
      (sheafifyMap J ψ).app (op U) y = 0 := by
    intro U y
    have hmem : Presheaf.equalizerSieve (F := sheafify J Q) (X := op U)
        ((sheafifyMap J ψ).app (op U) y) 0 ∈ J U := by
      refine J.transitive (Presheaf.imageSieve_mem J (toSheafify J P) y) _ ?_
      rintro W g ⟨t, ht⟩ x hx
      obtain ⟨V, hVB, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp h hx
      refine ⟨V, homOfLE hVW, ?_, hxV⟩
      have hV : ψ.app (op V) = 0 := hVB
      show (sheafify J Q).map (homOfLE hVW ≫ g).op ((sheafifyMap J ψ).app (op U) y) =
        (sheafify J Q).map (homOfLE hVW ≫ g).op 0
      rw [map_zero, ← NatTrans.naturality_apply (sheafifyMap J ψ), op_comp,
        (sheafify J P).map_comp, ConcreteCategory.comp_apply, ← ht,
        ← NatTrans.naturality_apply (toSheafify J P), ← ConcreteCategory.comp_apply,
        ← NatTrans.comp_app, ← toSheafify_naturality, NatTrans.comp_app,
        ConcreteCategory.comp_apply, hV]
      simp
    exact Stacks.Cohomology.Locality.section_eq_zero_of_cover J _
      ((presheafToSheaf J AddCommGrpCat.{v}).obj Q).property ⟨_, hmem⟩ _ fun g => by
        simpa [Presheaf.equalizerSieve] using g.hf
  ext U y
  exact key U.unop y

/-- A morphism is sent to zero by one of two naturally isomorphic functors iff by the other. -/
private theorem map_eq_zero_iff_of_iso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {F G : C ⥤ D} (e : F ≅ G) {A B : C} (φ : A ⟶ B) :
    F.map φ = 0 ↔ G.map φ = 0 := by
  rw [← cancel_mono (e.hom.app B), zero_comp, e.hom.naturality, ← comp_zero (f := e.hom.app A),
    cancel_epi]

open Stacks.Cohomology.SheafifiedHigherDirectImage in
/-- **A morphism of higher direct images vanishing over a basis**, at the site-theoretic
spelling of `R^p f_*` as the right derived functor of `sheafPushforwardContinuous` along
`Opens.map f`: if `φ` induces zero on `H^p(f⁻¹(V), -)` for all `V` in a basis of `Y`, then
`R^p f_* φ = 0`. -/
theorem sheafPushforwardContinuous_rightDerived_map_eq_zero_of_isBasis (f : X ⟶ Y)
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}} (φ : F ⟶ G) (p : ℕ)
    (h : Opens.IsBasis {V : Opens Y |
      ((pushforwardCohomologyPresheaf AddCommGrpCat.{v} (Opens.map f)
        (K := Opens.grothendieckTopology X) ⋙ (evaluation _ _).obj (op V)).rightDerived p).map φ
          = 0}) :
    (((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{v}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).rightDerived p).map φ = 0 := by
  let e := rightDerivedPushforwardIso AddCommGrpCat.{v} (Opens.map f)
    (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X) p
  let Ψ := ((pushforwardCohomologyPresheaf AddCommGrpCat.{v} (Opens.map f)
    (K := Opens.grothendieckTopology X)).rightDerived p).map φ
  have hΨ : (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v}).map Ψ = 0 := by
    refine presheafToSheaf_map_eq_zero_of_isBasis Ψ (Opens.isBasis_iff_nbhd.mpr fun {U x} hx => ?_)
    obtain ⟨V, hVB, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp h hx
    refine ⟨V, ?_, hxV, hVU⟩
    exact (map_eq_zero_iff_of_iso (pushforwardCohomologyPresheafEvaluationIso AddCommGrpCat.{v}
      (Opens.map f) (K := Opens.grothendieckTopology X) p V) φ).1 hVB
  exact (map_eq_zero_iff_of_iso e φ).2 hΨ

/-- **A morphism of higher direct images vanishing over a basis.** Let `f : X ⟶ Y` be continuous
and `φ : F ⟶ G` a morphism of abelian sheaves on `X`. If `φ` induces zero on
`H^p(f⁻¹(V), -)` for all `V` in a basis of `Y`, then `R^p f_* φ = 0`. -/
theorem higherDirectImage_map_eq_zero_of_isBasis (f : X ⟶ Y) {F G : X.Sheaf AddCommGrpCat.{v}}
    (φ : F ⟶ G) (p : ℕ)
    (h : Opens.IsBasis {V : Opens Y | (cohomologyOver ((Opens.map f).obj V) p).map φ = 0}) :
    (higherDirectImage f p).map φ = 0 := by
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) := by
    show EnoughInjectives (X.Sheaf AddCommGrpCat.{v})
    infer_instance
  exact sheafPushforwardContinuous_rightDerived_map_eq_zero_of_isBasis f φ p h

end Stacks.Cohomology.AbelianSheaf
