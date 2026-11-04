module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat

/-!
# Flatness of a closed subspace over the target, read off one surjective étale chart

Let `X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site and
let `Z ⊆ X` be a closed subspace.  Let `U` be an étale chart of `X` which is surjective, let `V`
be an étale chart of `Y`, and let `b : U ⟶ V` be a morphism of the site making the square over
`X ⟶ Y` commute.  Then `Z ⟶ Y` is flat as soon as the morphism of schemes `Z ×_X U ⟶ V` is
flat.

For `Z = V(f₁, …, f_r)` and an affine chart `U`, the base change `Z ×_X U` is the zero scheme of
the restrictions of the `fᵢ` to `U`, so the hypothesis may be stated in that form.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeToSubspace`: the chart `Z ×_X U ⟶ Z` of a closed
  subspace base changed from an étale chart of the ambient space.

## Main results

* `AlgebraicGeometry.Space.isEtale_chartBaseChangeToSubspace` and
  `AlgebraicGeometry.Space.isSurjective_chartBaseChangeToSubspace`: it is étale, and surjective
  as soon as the chart it comes from is.
* `AlgebraicGeometry.Space.isFlat_ι_comp_of_surjective_chart`: a closed subspace is flat over
  the target when its base change to one surjective étale chart is flat over a chart of the
  target.
* `AlgebraicGeometry.Space.isFlat_ι_vanishingSubfunctor_comp_of_zeroScheme`: the same for
  `V(f₁, …, f_r)`, with the hypothesis in the zero-scheme form.

## References

* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The étale chart of a closed subspace base changed from one of the ambient space -/

/-- The chart `Z ×_X U ⟶ Z` of a closed subspace `Z ⊆ X` obtained by base changing an étale
chart `U` of `X` along the closed immersion. -/
abbrev chartBaseChangeToSubspace (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (U : SmallEtale B S hS X.1) :
    yoneda.obj (Z.2.2.rep.pullback U.1.hom) ⟶ Z.1.toFunctor :=
  Z.2.2.rep.fst U.1.hom

/-- The base change of an étale chart to a closed subspace is étale. -/
theorem isEtale_chartBaseChangeToSubspace (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1) :
    IsEtale B S hS (chartBaseChangeToSubspace B S hS X Z U) :=
  isEtale_of_isPullback_yoneda B S hS (Z.2.2.rep.isPullback U.1.hom).flip
    ((isEtale_iff_presheaf_of_yoneda B S hS U.1.hom).2 U.2)

/-- The base change of a surjective étale chart to a closed subspace is surjective. -/
theorem isSurjective_chartBaseChangeToSubspace (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1)
    (hU : IsSurjective B S hS U.1.hom) :
    IsSurjective B S hS (chartBaseChangeToSubspace B S hS X Z U) := by
  have sq : IsPullback
      (ObjectProperty.homMk (yoneda.map (Z.2.2.rep.snd U.1.hom)) :
        (⟨yoneda.obj (Z.2.2.rep.pullback U.1.hom),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U),
            isAlgebraicSpace_yoneda B S hS _⟩)
      (ObjectProperty.homMk (Z.2.2.rep.fst U.1.hom) :
        (⟨yoneda.obj (Z.2.2.rep.pullback U.1.hom),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨Z.1.toFunctor, Z.2.1⟩)
      (ObjectProperty.homMk U.1.hom :
        (⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (ObjectProperty.homMk Z.1.ι : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (Z.2.2.rep.isPullback U.1.hom).flip
  exact isSurjective_of_isPullback B S hS sq hU

/-! ### Flatness over the target read off one surjective étale chart -/

/-- A closed subspace is flat over the target as soon as its base change to one surjective
étale chart is flat over a chart of the target.

Let `g : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `Z ⊆ X` be a closed subspace,
let `U` be a surjective étale chart of `X`, let `V` be an étale chart of `Y` and let
`b : U ⟶ V` be a morphism of the site with `U ⟶ X ⟶ Y` equal to `U ⟶ V ⟶ Y`.  If the morphism
of schemes `Z ×_X U ⟶ V` is flat, then `Z ⟶ Y` is flat. -/
theorem isFlat_ι_comp_of_surjective_chart (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1)
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1)
    (hU : IsSurjective B S hS U.1.hom) (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
    (hq : IsEtale B S hS q) (b : (SmallEtale.toOver B S hS X.1).obj U ⟶ V)
    (hcomm : U.1.hom ≫ g = yoneda.map b ≫ q)
    (hflat : AlgebraicGeometry.Flat
      (chartBaseChangeHom B S hS X Z U ≫ (BigFppfOver.toScheme B S hS).map b)) :
    IsFlat B S hS (Z.1.ι ≫ g) := by
  refine ((isFlat_tfae B S hS Z.2.1 Y.2 (Z.1.ι ≫ g)).out 8 1).1 ?_
  refine ⟨Z.2.2.rep.pullback U.1.hom, V, chartBaseChangeToSubspace B S hS X Z U, q,
    Z.2.2.rep.snd U.1.hom ≫ b, isEtale_chartBaseChangeToSubspace B S hS X Z U, hq,
    isSurjective_chartBaseChangeToSubspace B S hS X Z U hU, ?_, ?_⟩
  · rw [← Category.assoc, (Z.2.2.rep.isPullback U.1.hom).w, Category.assoc, hcomm,
      Functor.map_comp, Category.assoc]
  · exact isFlat_yoneda_map B S hS _ (by rwa [Functor.map_comp])

/-- The zero locus `V(f₁, …, f_r)` is flat over the target as soon as the zero scheme of the
restricted functions on one surjective affine étale chart is flat over a chart of the target. -/
theorem isFlat_ι_vanishingSubfunctor_comp_of_zeroScheme (X Y : AlgebraicSpaces B S hS)
    (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1)
    (hUaff : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hU : IsSurjective B S hS U.1.hom) (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
    (hq : IsEtale B S hS q) (b : (SmallEtale.toOver B S hS X.1).obj U ⟶ V)
    (hcomm : U.1.hom ≫ g = yoneda.map b ≫ q)
    (hflat : AlgebraicGeometry.Flat
      ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => (f i).eval (op U)))).subschemeι ≫
        (BigFppfOver.toScheme B S hS).map b)) :
    IsFlat B S hS ((vanishingSubfunctor B S hS X f).ι ≫ g) := by
  let : MorphismProperty.RespectsIso (@AlgebraicGeometry.Flat.{u}) :=
    AlgebraicGeometry.Flat.isStableUnderBaseChange.respectsIso
  obtain ⟨Z, hZeq, hzero⟩ := exists_closedSubspace_iso_zeroScheme_chartBaseChange B S hS X f
  have hZ : Z = vanishingSubspace B S hS X f := Subtype.ext hZeq.symm
  subst hZ
  obtain ⟨e, he⟩ := hzero U hUaff
  refine isFlat_ι_comp_of_surjective_chart B S hS X Y g (vanishingSubspace B S hS X f) U hU
    V q hq b hcomm ?_
  rw [← he, Category.assoc]
  exact MorphismProperty.RespectsIso.precomp _ e.hom _ hflat

end AlgebraicGeometry.Space

end
