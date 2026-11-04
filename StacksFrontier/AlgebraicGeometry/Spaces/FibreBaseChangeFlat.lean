module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFactorisationLargeField
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat

/-!
# Enlarging the field of a fibre is a flat base change

Let `F` be an algebraic space over the spectrum of a field `k` in the big fppf site of `S`, and let
`c : T' ⟶ Spec k` be any morphism of the site into that field spectrum. Then the projection
`F ×_{Spec k} T' ⟶ F` is flat, and flat at every point.

## Main results

* `AlgebraicGeometry.Space.flat_map_of_field_target`: every morphism of the big fppf site of `S`
  whose target is the spectrum of a field is flat as a morphism of schemes.
* `AlgebraicGeometry.Space.isFlat_pullback_fst_yoneda_map_of_field`: the projection
  `F ×_{Spec k} T' ⟶ F` is flat.
* `AlgebraicGeometry.Space.isFlatAt_pullback_fst_yoneda_map_of_field`: it is flat at every point
  of its source.

## References

* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf site whose target is the spectrum of a field is flat as a morphism
of schemes. -/
theorem flat_map_of_field_target {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S) {T' : BigFppfOver B S hS}
    (c : T' ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) :
    _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map c) := by
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj
      (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  infer_instance

/-- Let `F` be an algebraic space over the spectrum of a field `k` in the site, by a morphism `π`,
and let `c : T' ⟶ Spec k` be any morphism of the site. Then the projection
`F ×_{Spec k} T' ⟶ F` is flat. -/
theorem isFlat_pullback_fst_yoneda_map_of_field
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (π : F ⟶ yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))
    {T' : BigFppfOver B S hS}
    (c : T' ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) :
    IsFlat B S hS (pullback.fst π (yoneda.map c)) := by
  have hc : IsFlat B S hS (yoneda.map c) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget c).mpr
      (flat_map_of_field_target B S hS hk b c)
  let Fs : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let Ts : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)), isAlgebraicSpace_yoneda B S hS _⟩
  let T's : AlgebraicSpaces B S hS := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS _⟩
  have := isFlat_isStableUnderBaseChange B S hS
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFlat B S hS f.hom)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk π : Fs ⟶ Ts)
      (ObjectProperty.homMk (yoneda.map c) : T's ⟶ Ts)).flip hc

/-- Let `F` be an algebraic space over the spectrum of a field `k` in the site, by a morphism `π`,
and let `c : T' ⟶ Spec k` be any morphism of the site. Then the projection
`F ×_{Spec k} T' ⟶ F` is flat at every point of its source. -/
theorem isFlatAt_pullback_fst_yoneda_map_of_field
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (π : F ⟶ yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))
    {T' : BigFppfOver B S hS}
    (c : T' ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS))
    (w : points B S hS (pullback π (yoneda.map c))) :
    IsFlatAt B S hS (pullback.fst π (yoneda.map c)) w :=
  (isFlat_iff_forall_isFlatAt B S hS (pullback.fst π (yoneda.map c))).mp
    (isFlat_pullback_fst_yoneda_map_of_field B S hS hF hk b π c) w

end AlgebraicGeometry.Space

end
