module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The chart a closed subspace inherits, and the drop of its fibre degree

Let `X` be an algebraic space with an affine surjective étale chart `c : h_W ⟶ X`, and let `G` be
a closed subspace of `X`. The base change `G ×_X W ⟶ G` of `c` is an affine surjective étale chart
of `G`, and if the points of `G` lie off the open on which the fibre degree of `c` is `d`, then
every fibre of this chart at a field-valued point of `G` has degree strictly less than `d`.

## Main results

* `AlgebraicGeometry.Space.presheaf_isFiniteLocallyFreeOfRank_yoneda_map`: a morphism of the site
  whose underlying morphism of schemes is finite locally free of rank `r` is relatively finite
  locally free of rank `r` as a morphism of presheaves.
* `AlgebraicGeometry.Space.exists_chart_of_isClosedSubspace`: a closed subspace inherits an
  affine surjective étale chart, presented as a base change of the given chart.
* `AlgebraicGeometry.Space.exists_lt_of_chart_of_isClosedSubspace`: if the point set of the
  closed subspace misses the minimal-degree open, every representable presentation of a fibre of
  the inherited chart at a field-valued point is finite locally free of degree strictly less
  than `d`.

## References

* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The relative form of a fibre degree -/

/-- A morphism of the site which is finite locally free of rank `r` on underlying schemes is
relatively finite locally free of rank `r` as a morphism of presheaves. -/
theorem presheaf_isFiniteLocallyFreeOfRank_yoneda_map {A T : BigFppfOver B S hS} (q : A ⟶ T)
    {r : ℕ} (hq : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) :
    (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
  have _ := inverseImage_isStableUnderBaseChange B S hS
    (inferInstance : (IsFiniteLocallyFreeOfRank.property.{u} r).IsStableUnderBaseChange)
  MorphismProperty.relative_map hq

/-! ### The chart inherited by a closed subspace -/

/-- A closed subspace `G` of an algebraic space `X` inherits an affine surjective étale chart from
an affine surjective étale chart `c : h_W ⟶ X`: there is an affine surjective étale chart
`cT : h_{W_T} ⟶ G` and a morphism `W_T ⟶ W` making `cT` the base change of `c` along the
inclusion of `G`. -/
theorem exists_chart_of_isClosedSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (G : Subfunctor X) (hGι : IsClosedImmersion B S hS G.ι)
    (Wch : BigFppfOver B S hS) (c : yoneda.obj Wch ⟶ X) (hc : IsEtale B S hS c)
    (hcs : IsSurjective B S hS c)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj Wch)) :
    ∃ (WT : BigFppfOver B S hS) (cT : yoneda.obj WT ⟶ G.toFunctor) (pW : WT ⟶ Wch),
      IsAffine ((BigFppfOver.toScheme B S hS).obj WT) ∧ IsEtale B S hS cT ∧
        IsSurjective B S hS cT ∧ IsPullback cT (yoneda.map pW) G.ι c := by
  have hsq : IsPullback (hGι.rep.fst c) (yoneda.map (hGι.rep.snd c)) G.ι c :=
    hGι.rep.isPullback c
  refine ⟨hGι.rep.pullback c, hGι.rep.fst c, hGι.rep.snd c, ?_, ?_, ?_, hsq⟩
  · have hci : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hGι.rep.snd c)) :=
      hGι.property c (hGι.rep.fst c) (hGι.rep.snd c) hsq
    exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hGι.rep.snd c))
  · have _ := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (F := yoneda)
    exact (isEtale_iff_presheaf_of_yoneda B S hS (hGι.rep.fst c)).2
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
        ((isEtale_iff_presheaf_of_yoneda B S hS c).1 hc))
  · have _ := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (F := yoneda)
    exact isSurjective_of_presheafSurjective B S hS (hGι.rep.fst c)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
        ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX Wch c).2 hcs))

/-! ### The drop of the fibre degree on a closed subspace off the minimal-degree open -/

/-- Let `G` be a closed subspace of `X` whose point set lies outside the open `U` on which the
fibre degree of the chart `c` of `X` is `d`, and let `c_T : h_{W_T} ⟶ G` be a base change of `c`
along the inclusion. Then every representable presentation of the fibre of `c_T` at a
field-valued point of `G` is finite locally free of degree strictly less than `d`. -/
theorem exists_lt_of_chart_of_isClosedSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor X)
    (Wch : BigFppfOver B S hS) (c : yoneda.obj Wch ⟶ X)
    (WT : BigFppfOver B S hS) (cT : yoneda.obj WT ⟶ G.toFunctor) (pW : WT ⟶ Wch)
    (hsq : IsPullback cT (yoneda.map pW) G.ι c)
    (U : Set (points B S hS X)) (d : ℕ)
    (hU2 : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X)
      (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj Wch) (pr₂ : Pp ⟶ T),
        IsPullback pr₁ pr₂ c hm → points B S hS T →
          Set.range (pointsMap B S hS T hm) ⊆ Uᶜ →
            ∀ r : ℕ,
              (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                (BigFppfOver.toScheme B S hS)).presheaf pr₂ → r < d)
    (hU3 : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
      (i : yoneda.obj Vf ⟶ yoneda.obj Wch),
      IsPullback i (yoneda.map q) c ξ →
        ∃ r : ℕ, r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r)
    (hGrange : Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆ Uᶜ) :
    ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ G.toFunctor) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
      (i : yoneda.obj Vf ⟶ yoneda.obj WT),
      IsPullback i (yoneda.map q) cT ξ →
        ∃ r : ℕ, r < d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r := by
  intro K hK T eT ξ Vf q i hsqi
  have hpaste : IsPullback (i ≫ yoneda.map pW) (yoneda.map q) c (ξ ≫ G.ι) :=
    hsqi.paste_horiz hsq.flip
  obtain ⟨r, -, hrank⟩ := hU3 K hK T eT (ξ ≫ G.ι) Vf q (i ≫ yoneda.map pW) hpaste
  obtain ⟨t⟩ := nonempty_points_yoneda_of_isoSpec_toScheme B S hS T eT
  refine ⟨r, ?_, hrank⟩
  refine hU2 (yoneda.obj T) (ξ ≫ G.ι) (yoneda.obj Vf) (i ≫ yoneda.map pW) (yoneda.map q)
    hpaste t ?_ r (presheaf_isFiniteLocallyFreeOfRank_yoneda_map B S hS q hrank)
  rintro y ⟨z, rfl⟩
  refine hGrange ⟨pointsMap B S hS (yoneda.obj T) ξ z, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS G.toFunctor G.ι),
    ← pointsMap_comp B S hS (yoneda.obj T) ξ G.ι]

end AlgebraicGeometry.Space

end
