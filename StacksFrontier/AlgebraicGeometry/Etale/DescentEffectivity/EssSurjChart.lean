module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.BaseChangeDescended
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.ChartShrinkFlat
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.EffectivityTransport
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Flat

/-!
# Descent over the reduced complement of a chart

Let `g : Y ⟶ T` be a finite surjection, `D` a quasi-compact separated étale descent datum along
`g`, `U₀` an open of `T`, and `W` an affine open of `T` containing a point `ξ ∉ U₀` whose closure
contains `(W : Set T) ∩ (U₀ : Set T)ᶜ`. Then `W` can be shrunk to an affine open `W'` containing
`ξ` such that the datum base changed to the reduced induced scheme on
`(W' : Set T) ∩ (U₀ : Set T)ᶜ` is descended by a scheme finite and étale over it.

The chart is first shrunk until the base change of `g` to the reduced complement is flat, so that
the datum is effective there ([Stacks, Tag 02W8]), with descended scheme `U_Z` étale over the
reduced complement; it is then shrunk once more until `U_Z` is finite over the reduced complement
([Stacks, Tag 02NW]).

## Main results

* `AlgebraicGeometry.DescentDatum.Descended.ofPullbackSquareReverse`: a scheme descending the
  pullback of a datum along a morphism of the source over the base, which admits a reverse,
  descends the datum itself.
* `AlgebraicGeometry.DescentDatum.Descended.exists_etale_isFinite_of_pullbackSquareReverse`: that
  transport preserves étaleness and finiteness of the structure morphism.
* `AlgebraicGeometry.DescentDatum.Descended.exists_changeDatum_of_eq`: the transport of a descended
  scheme, étale and finite, along an equality of morphisms of the base.
* `AlgebraicGeometry.exists_isAffineOpen_descended_isFinite_etale_reducedInducedInclusion`: the
  chart can be shrunk around `ξ` so that the datum base changed to the reduced complement is
  descended by a scheme finite and étale over it.

## References

* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

namespace DescentDatum.Descended

/-! ### Carrying a descended scheme backwards along a pullback of data over the base -/

/-- A scheme descending the pullback of a datum along a morphism of the source over the base
descends the datum itself, as soon as that morphism admits a reverse morphism over the base. -/
def ofPullbackSquareReverse {S X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S) (p : X' ⟶ X)
    (q : X ⟶ X') (hp : p ≫ a = a' ≫ 𝟙 S) (hq : q ≫ a' = a ≫ 𝟙 S) (E : DescentDatum a')
    (Q : (pullbackSquareDatum (DescentData.pullbackFunctor a' a (𝟙 S) q hq) E).Descended) :
    E.Descended :=
  have hcomp : (p ≫ q) ≫ a' = a' ≫ 𝟙 S := by
    rw [Category.assoc, hq, Category.comp_id, hp, Category.comp_id]
  have hself : (p ≫ q) ≫ a' = a' := by rw [hcomp, Category.comp_id]
  have hε : (DescentData.pullbackFunctor a' a (𝟙 S) q hq).functor ⋙
      (DescentData.pullbackFunctor a a' (𝟙 S) p hp).functor ≅ 𝟭 _ :=
    (DescentData.pullbackFactorizationIso
      (DescentData.pullbackFunctor a' a' (𝟙 S) (p ≫ q) hcomp)
      (DescentData.pullbackFunctor a' a (𝟙 S) q hq)
      (DescentData.pullbackFunctor a a' (𝟙 S) p hp)).symm ≪≫
    DescentData.selfPullbackFunctorIso a' (p ≫ q) hself
  (pullbackSquare (DescentData.pullbackFunctor a a' (𝟙 S) p hp) Q).ofDatumIso (hε.app E).symm

/-- The backwards transport of a descended scheme keeps its base pulled back along the identity,
hence keeps étaleness and finiteness of the structure morphism. -/
theorem exists_etale_isFinite_of_pullbackSquareReverse {S X X' : Scheme.{u}} (a : X ⟶ S)
    (a' : X' ⟶ S) (p : X' ⟶ X) (q : X ⟶ X') (hp : p ≫ a = a' ≫ 𝟙 S) (hq : q ≫ a' = a ≫ 𝟙 S)
    (E : DescentDatum a')
    (Q : (pullbackSquareDatum (DescentData.pullbackFunctor a' a (𝟙 S) q hq) E).Descended)
    (hE : Etale Q.base.hom) (hF : IsFinite Q.base.hom) :
    ∃ R : E.Descended, Etale R.base.hom ∧ IsFinite R.base.hom := by
  refine ⟨ofPullbackSquareReverse a a' p q hp hq E Q, ?_, ?_⟩
  · have := hE
    show Etale (pullback.snd Q.base.hom (𝟙 S))
    infer_instance
  · have := hF
    show IsFinite (pullback.snd Q.base.hom (𝟙 S))
    infer_instance

/-- Transport of a descended scheme, with étaleness and finiteness of its structure morphism,
along an equality of the morphism of the base being base changed along. -/
theorem exists_changeDatum_of_eq {S X T : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)
    {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) (Q : (D.changeDatum g₁).Descended) (hE : Etale Q.base.hom)
    (hF : IsFinite Q.base.hom) :
    ∃ R : (D.changeDatum g₂).Descended, Etale R.base.hom ∧ IsFinite R.base.hom := by
  subst h
  exact ⟨Q, hE, hF⟩

end DescentDatum.Descended

/-! ### Descent over the reduced complement of a chart -/

/-- Over an affine open chart `W` of the base through a point `ξ` outside `U₀` whose closure
contains the complement of `U₀` in `W`, that complement being irreducible, the chart can be
shrunk to an affine open `W' ≤ W` still containing `ξ` so that the descent datum base changed to
the reduced induced scheme on `(W' : Set T) ∩ (U₀ : Set T)ᶜ` is descended by a scheme which is
finite and étale over it. -/
theorem exists_isAffineOpen_descended_isFinite_etale_reducedInducedInclusion {T Y : Scheme.{u}}
    (g : Y ⟶ T) [IsFinite g] [Surjective g] (D : DescentDatum g) [Etale D.over.hom]
    (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom) (U₀ W : T.Opens) (ξ : T)
    (hξW : ξ ∈ W) (hξU₀ : ξ ∉ U₀) (_hirr : IsIrreducible ((W : Set T) ∩ (U₀ : Set T)ᶜ))
    (hclos : (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ}) :
    ∃ (W' : T.Opens) (_ : (W' : Set T) ⊆ (W : Set T)), ξ ∈ W' ∧ IsAffineOpen W' ∧
      ∃ Q : (D.changeDatum (reducedInducedInclusion ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
          (isLocallyClosed_inter_compl W' U₀))).Descended,
        Etale Q.base.hom ∧ IsFinite Q.base.hom := by
  obtain ⟨W₁, hW₁W, hξW₁, hW₁aff, hflat⟩ :=
    exists_isAffineOpen_flat_pullback_snd_reducedInducedInclusion g U₀ W ξ hξW hξU₀ hclos
  have hclos₁ : (W₁ : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ} :=
    fun y hy ↦ hclos ⟨hW₁W hy.1, hy.2⟩
  have hirr₁ : IsIrreducible ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ) :=
    Topology.isIrreducible_of_mem_of_subset_closure_singleton ⟨hξW₁, hξU₀⟩ hclos₁
  have hflat' : Flat (pullback.snd g (reducedInducedInclusion
    ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W₁ U₀))) := hflat
  obtain ⟨Q₁, hQ₁⟩ := qcSepEtaleEffective_of_flat
    (pullback.snd g (reducedInducedInclusion ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ)
      (isLocallyClosed_inter_compl W₁ U₀)))
    (D.changeDatum (reducedInducedInclusion ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ)
      (isLocallyClosed_inter_compl W₁ U₀))) inferInstance
    (DescentDatum.quasiCompact_changeDatum_over_hom D _ hqc)
    (DescentDatum.isSeparated_changeDatum_over_hom D _ hsep)
  have : Etale Q₁.base.hom := hQ₁
  have : QuasiCompact Q₁.base.hom :=
    Q₁.quasiCompact_base_hom (DescentDatum.quasiCompact_changeDatum_over_hom D _ hqc)
  have : IsSeparated Q₁.base.hom :=
    Q₁.isSeparated_base_hom (DescentDatum.isSeparated_changeDatum_over_hom D _ hsep)
  have : QuasiSeparated Q₁.base.hom := inferInstance
  obtain ⟨W₂, hW₂W₁, hξW₂, hW₂aff, hfin⟩ :=
    exists_isAffineOpen_isFinite_pullback_snd_reducedInducedComparison U₀ W₁ ξ hξW₁ hirr₁ hclos₁
      Q₁.base.hom
  refine ⟨W₂, fun y hy ↦ hW₁W (hW₂W₁ hy), hξW₂, hW₂aff, ?_⟩
  obtain ⟨R, hRE, hRF⟩ :=
    DescentDatum.Descended.exists_etale_isFinite_of_pullbackSquareReverse _ _
      (DescentDatum.changeCompIso g (reducedInducedInclusion ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ)
        (isLocallyClosed_inter_compl W₁ U₀))
        (reducedInducedComparison ((W₂ : Set T) ∩ (U₀ : Set T)ᶜ)
          ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W₂ U₀)
          (isLocallyClosed_inter_compl W₁ U₀) (Set.inter_subset_inter_left _ hW₂W₁))).inv
      _
      (DescentDatum.changeCompIso_inv_comp_snd g _ _)
      (DescentDatum.changeCompIso_hom_comp_snd g _ _) _
      (Q₁.changeDatum (reducedInducedComparison ((W₂ : Set T) ∩ (U₀ : Set T)ᶜ)
        ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W₂ U₀)
        (isLocallyClosed_inter_compl W₁ U₀) (Set.inter_subset_inter_left _ hW₂W₁))
        |>.ofDatumIso (DescentDatum.changeCompDatumIso _ _ D))
      (by
        show Etale (pullback.snd Q₁.base.hom _)
        infer_instance)
      hfin
  exact DescentDatum.Descended.exists_changeDatum_of_eq D
    (reducedInducedComparison_inclusion ((W₂ : Set T) ∩ (U₀ : Set T)ᶜ)
      ((W₁ : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W₂ U₀)
      (isLocallyClosed_inter_compl W₁ U₀) (Set.inter_subset_inter_left _ hW₂W₁))
    R hRE hRF

end AlgebraicGeometry

end
