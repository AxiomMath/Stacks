module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionEtale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiniteRegularSliceOverField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Immersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# An unramified local complete intersection point of an algebraic space over a field

Let `T` be a scheme isomorphic to the spectrum of a field and let `X` be an algebraic space over
`T` which is flat and locally of finite presentation over `T` and has a section over some
nonempty scheme. Then there is a scheme `Z` over `T`, finite locally free of some positive degree
`d`, together with a morphism `Z ⟶ X` of algebraic spaces which is unramified and a local
complete intersection morphism.

This is steps 2 to 8 of the proof of Stacks 06DA. Choose an étale atlas `W ⟶ X`; it is nonempty
because `X` has a point. The scheme `W` is flat and locally of finite presentation over `T`
(Stacks 03XP), so it carries a regular immersion `Z ⟶ W` with `Z` finite locally free of positive
degree over `T` (Stacks 045U, 0570, 00PJ). The composite `Z ⟶ W ⟶ X` is unramified as an
immersion followed by an étale morphism (Stacks 03ZI, 06CR, 06CQ), and a local complete
intersection morphism as a regular immersion followed by an étale morphism (Stacks 069L, 04XX,
06CP, 06C9, 06C8).

## Main results

* `AlgebraicGeometry.Space.exists_isUnramified_isLocalCompleteIntersection_of_field`: the
  unramified local complete intersection point.

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03ZI](https://stacks.math.columbia.edu/tag/03ZI)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 069L](https://stacks.math.columbia.edu/tag/069L)
* [Stacks Project, Tag 06C8](https://stacks.math.columbia.edu/tag/06C8)
* [Stacks Project, Tag 06C9](https://stacks.math.columbia.edu/tag/06C9)
* [Stacks Project, Tag 06CP](https://stacks.math.columbia.edu/tag/06CP)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
-/

@[expose] public section

open CategoryTheory Opposite Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)

/-- **An unramified local complete intersection point of an algebraic space over a field.** An
algebraic space `X` over a scheme `T ≅ Spec k`, flat and locally of finite presentation over `T`
and with a section over a nonempty scheme, receives an unramified local complete intersection
morphism from a scheme `Z` over `T` which is finite locally free of positive degree over `T`. -/
theorem exists_isUnramified_isLocalCompleteIntersection_of_field {k : Type u} [Field k]
    (eT : T ≅ Spec (.of k)) {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B T hT X)
    (hflat : HoldsOnEveryEtaleChart B T hT (@Flat : MorphismProperty Scheme.{u})
      (toYonedaId B T hT X))
    (hlfp : HoldsOnEveryEtaleChart B T hT
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) (toYonedaId B T hT X))
    (V : BigFppfOver B T hT) [Nonempty ((BigFppfOver.toScheme B T hT).obj V)]
    (s : X.obj (op V)) :
    ∃ (Z : BigFppfOver B T hT) (d : ℕ), 0 < d ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map Z.hom) d ∧
      ∃ f : yoneda.obj Z ⟶ X, IsUnramified B T hT f ∧ IsLocalCompleteIntersection B T hT f := by
  let τ := BigFppfOver.toScheme B T hT
  obtain ⟨W, a, ha_surj, ha_et⟩ := hX.exists_atlas
  -- the atlas is nonempty, since `X` has a section over a nonempty scheme
  have hWne : Nonempty (τ.obj W) := by
    let t : yoneda.obj V ⟶ X := yonedaEquiv.symm s
    have hsnd : Surjective (τ.map (ha_surj.rep.snd t)) := ha_surj.property_snd t
    obtain ⟨v⟩ := ‹Nonempty (τ.obj V)›
    obtain ⟨p, -⟩ := (τ.map (ha_surj.rep.snd t)).surjective v
    exact ⟨τ.map (ha_surj.rep.fst' t) p⟩
  -- the atlas is flat and locally of finite presentation over `T`
  let hW : W ⟶ Over.mk (𝟙 (B.obj hT)) := Over.homMk W.hom (by simp)
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) τ).presheaf
      (𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hT))))) :=
    presheaf_id_of_iso B T hT _ (fun _ _ f _ => inferInstanceAs (Etale (τ.map f))) _
  have hsq : yoneda.map hW ≫ 𝟙 _ = a ≫ toYonedaId B T hT X := by
    ext _ x
    exact Over.OverMorphism.ext (Over.w x)
  have hlfpW : LocallyOfFinitePresentation (τ.map hW) := hlfp W _ a (𝟙 _) hW ha_et hb hsq
  have hflatW : Flat (τ.map hW) := hflat W _ a (𝟙 _) hW ha_et hb hsq
  let g : τ.obj W ⟶ Spec (.of k) := τ.map hW ≫ eT.hom
  obtain ⟨Z, i, hi, hreg, d, hd, hfl⟩ :=
    exists_regularImmersion_isFiniteLocallyFreeOfRank_of_field g
  have hZ : B.Contains Z := BigFppfSite.contains_of_mono B i W.left.2
  let Zo : BigFppfOver B T hT := Over.mk (⟨i ≫ τ.map hW⟩ : B.obj hZ ⟶ B.obj hT)
  let ι : Zo ⟶ W := Over.homMk (⟨i⟩ : B.obj hZ ⟶ W.left) rfl
  have hι : τ.map ι = i := rfl
  have ha : IsEtale B T hT a := (isEtale_iff_presheaf_of_yoneda B T hT a).2 ha_et
  have hZs := isAlgebraicSpace_yoneda B T hT Zo
  have hWs := isAlgebraicSpace_yoneda B T hT W
  refine ⟨Zo, d, hd, ?_, yoneda.map ι ≫ a, ?_, ?_⟩
  · rw [← Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff] at hfl ⊢
    rwa [show i ≫ g = (i ≫ τ.map hW) ≫ eT.hom by simp [g],
      MorphismProperty.cancel_right_of_respectsIso
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d)] at hfl
  · have h1 : IsUnramified B T hT (yoneda.map ι) :=
      holdsOnEveryEtaleChart_yoneda_map B T hT unramified_isEtaleLocalOnSourceAndTarget ι
        (by rw [hι]; exact unramified_of_isImmersion i)
    exact isUnramified_comp B T hT hZs hWs hX _ _ h1 (isUnramified_of_isEtale B T hT ha)
  · have l1 : IsLocalCompleteIntersection B T hT (yoneda.map ι) :=
      holdsOnEveryEtaleChart_yoneda_map B T hT
        (isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
          isLocalCompleteIntersectionMorphism_isLocalAtSource_etale) ι
        (by rw [hι]; exact isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg)
    have l2 : IsLocalCompleteIntersection B T hT a :=
      ((isSyntomic_iff_isFlat_and_isLocalCompleteIntersection B T hT a).1
        (isSyntomic_of_isSmooth B T hT a (isSmooth_of_isEtale B T hT hX ha))).2
    exact isLocalCompleteIntersection_comp B T hT hZs hWs hX _ _ l1 l2

end AlgebraicGeometry.Space

end
