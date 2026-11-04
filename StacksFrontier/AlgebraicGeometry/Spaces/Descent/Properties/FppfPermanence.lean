module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Permanence along a surjective flat morphism locally of finite presentation

Let `p = f ≫ q` be a commuting triangle of morphisms of algebraic spaces over `S` with `f`
surjective, flat and locally of finite presentation. If `p` is smooth, resp. étale, then so
is `q`.

## Main results

* `AlgebraicGeometry.Space.exists_surjective_chart_over_etale_chart` lifts an étale chart of
  the target of a surjective morphism to a commuting square whose morphism of schemes is
  surjective.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_of_fppf` reduces the permanence of a
  chart-tested property along such an `f` to the corresponding statement for schemes.
* `AlgebraicGeometry.Space.isSmooth_of_comp_of_fppf` and
  `AlgebraicGeometry.Space.isEtale_of_comp_of_fppf` are **Stacks 0AHE**, the smooth and étale
  cases.

## Implementation notes

Given an étale chart `a` of the target `Y` of `f`, the fibre product of `f` with `a` is an
algebraic space whose projection to `yoneda.obj U` is surjective and whose projection to `X`
is étale. An atlas `W` of that fibre product therefore yields a morphism `W ⟶ U` of the site
which is surjective as a morphism of schemes, together with an étale chart of `X` over it.
Flatness and local finite presentation of `f` are by definition the corresponding properties
of the morphism of schemes underlying *every* commuting square of étale charts, so they apply
to the square so obtained; the property of `p` applies to the square over the given chart of
the base. The scheme-level descent of Stacks 05B5 then gives the property of the morphism of
schemes underlying the chart square of `q`, in the form
`Stacks.Smooth.smooth_of_comp_of_fppf` and `Stacks.Etale.etale_of_comp_of_fppf`.

Étaleness of a morphism of algebraic spaces is not by definition a chart condition, so the
étale case passes through `AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`.

The commuting triangle is given as a separate morphism `p` together with the equality
`p = f ≫ q`, exactly as in the source and as in the neighbouring Stacks 0AHD.

## References

* [Stacks Project, Tag 05B5](https://stacks.math.columbia.edu/tag/05B5)
* [Stacks Project, Tag 0AHE](https://stacks.math.columbia.edu/tag/0AHE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Over an étale chart `a` of the target of a surjective morphism `f : X ⟶ Y` of algebraic
spaces over `S` there is an étale chart `e` of the source and a morphism `δ` of the site
making a commuting square with `a` and `f`, whose morphism of schemes is surjective. -/
theorem exists_surjective_chart_over_etale_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hfs : IsSurjective B S hS f)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ Y)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ (W : BigFppfOver B S hS) (e : yoneda.obj W ⟶ X) (δ : W ⟶ U),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf e ∧
        Surjective ((BigFppfOver.toScheme B S hS).map δ) ∧
          yoneda.map δ ≫ a = e ≫ f := by
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let Xo : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Yo : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Uo : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hU⟩
  let fo : Xo ⟶ Yo := ObjectProperty.homMk f
  let ao : Uo ⟶ Yo := ObjectProperty.homMk a
  let Po : AlgebraicSpaces B S hS :=
    ⟨pullback f a, isAlgebraicSpace_pullback B S hS f a hX hU hY⟩
  let fstP : Po ⟶ Xo := ObjectProperty.homMk (pullback.fst f a)
  let sndP : Po ⟶ Uo := ObjectProperty.homMk (pullback.snd f a)
  have hpb : IsPullback fstP sndP fo ao :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ pullback.condition)
      (IsPullback.of_hasPullback f a)
  have hpullComm : fstP.hom ≫ f = sndP.hom ≫ a := by
    simpa [fo, ao] using congrArg (fun g : Po ⟶ Yo => g.hom) hpb.w
  have hprojSurj : IsSurjective B S hS sndP.hom :=
    isSurjective_of_isPullback B S hS hpb hfs
  have haSpace : IsEtale B S hS ao.hom := (isEtale_iff_presheaf_of_yoneda B S hS a).mpr ha
  have hprojEtale : IsEtale B S hS fstP.hom :=
    isEtale_of_isPullback B S hS sndP fstP ao fo hpb.flip haSpace
  obtain ⟨W, c, hcSurj, hcEtale⟩ := Po.property.exists_atlas
  have hcPoints : IsSurjective B S hS c :=
    (surjective_iff_surjective_pointsMap B S hS Po.obj Po.property W c).mp hcSurj
  have hδ : yoneda.map (yoneda.preimage (c ≫ sndP.hom)) = c ≫ sndP.hom :=
    yoneda.map_preimage _
  refine ⟨W, c ≫ fstP.hom, yoneda.preimage (c ≫ sndP.hom), ?_, ?_, ?_⟩
  · exact (isEtale_iff_presheaf_of_yoneda B S hS (c ≫ fstP.hom)).mp
      (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS c).mpr hcEtale) hprojEtale)
  · refine (presheaf_yoneda_map_iff B S hS (P := @Surjective.{u}) inferInstance
      (yoneda.preimage (c ≫ sndP.hom))).mp ?_
    refine (surjective_iff_surjective_pointsMap B S hS (yoneda.obj U) hU W
      (yoneda.map (yoneda.preimage (c ≫ sndP.hom)))).mpr ?_
    rw [hδ]
    exact isSurjective_comp B S hS hcPoints hprojSurj
  · rw [hδ]
    simpa only [Category.assoc] using congrArg (fun g => c ≫ g) hpullComm.symm

/-- A property of morphisms of schemes which passes from a composite `g ≫ r` with `g`
surjective, flat and locally of finite presentation to `r` passes, in the chart sense of
Stacks 03MJ, from a composite `f ≫ q` of morphisms of algebraic spaces with `f` surjective,
flat and locally of finite presentation to `q`. -/
theorem holdsOnEveryEtaleChart_of_comp_of_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (scheme_case : ∀ {A C D : Scheme.{u}} (g : A ⟶ C) (r : C ⟶ D), Surjective g → Flat g →
      LocallyOfFinitePresentation g → P (g ≫ r) → P r)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hcomm : p = f ≫ q)
    (hfs : IsSurjective B S hS f) (hff : IsFlat B S hS f)
    (hfp : IsLocallyOfFinitePresentation B S hS f)
    (hp : HoldsOnEveryEtaleChart B S hS P p) :
    HoldsOnEveryEtaleChart B S hS P q := by
  intro U V a b α ha hb hab
  obtain ⟨W, e, δ, he, hδSurj, hsq⟩ :=
    exists_surjective_chart_over_etale_chart B S hS hX hY f hfs U a ha
  have hδαP : P ((BigFppfOver.toScheme B S hS).map (δ ≫ α)) := by
    refine hp W V e b (δ ≫ α) he hb ?_
    calc
      yoneda.map (δ ≫ α) ≫ b = yoneda.map δ ≫ yoneda.map α ≫ b := by
        simp [Functor.map_comp, Category.assoc]
      _ = (yoneda.map δ ≫ a) ≫ q := by rw [hab, Category.assoc]
      _ = e ≫ p := by rw [hcomm, hsq, Category.assoc]
  exact scheme_case _ ((BigFppfOver.toScheme B S hS).map α) hδSurj
    (hff W U e a δ he ha hsq) (hfp W U e a δ he ha hsq) (by simpa using hδαP)

/-- **Stacks 0AHE**, smooth case. In a commuting triangle `p = f ≫ q` of morphisms of
algebraic spaces over `S` with `f` surjective, flat and locally of finite presentation,
smoothness of `p` implies smoothness of `q`. -/
@[stacks 0AHE "smooth case"]
theorem isSmooth_of_comp_of_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hcomm : p = f ≫ q) (hfs : IsSurjective B S hS f) (hff : IsFlat B S hS f)
    (hfp : IsLocallyOfFinitePresentation B S hS f) (hp : IsSmooth B S hS p) :
    IsSmooth B S hS q :=
  holdsOnEveryEtaleChart_of_comp_of_fppf B S hS
    (@Smooth.{u} : MorphismProperty Scheme.{u})
    (fun g r _ _ _ _ => Stacks.Smooth.smooth_of_comp_of_fppf g r) hX hY f p q hcomm hfs hff hfp hp

/-- **Stacks 0AHE**, étale case. In a commuting triangle `p = f ≫ q` of morphisms of
algebraic spaces over `S` with `f` surjective, flat and locally of finite presentation,
étaleness of `p` implies étaleness of `q`. -/
@[stacks 0AHE "étale case"]
theorem isEtale_of_comp_of_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hcomm : p = f ≫ q) (hfs : IsSurjective B S hS f) (hff : IsFlat B S hS f)
    (hfp : IsLocallyOfFinitePresentation B S hS f) (hp : IsEtale B S hS p) :
    IsEtale B S hS q := by
  refine (isEtale_iff_holdsOnEveryEtaleChart B S hS hY hZ q).2 ?_
  exact holdsOnEveryEtaleChart_of_comp_of_fppf B S hS
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (fun g r _ _ _ _ => Stacks.Etale.etale_of_comp_of_fppf g r) hX hY f p q hcomm hfs hff hfp
    ((isEtale_iff_holdsOnEveryEtaleChart B S hS hX hZ p).1 hp)

end AlgebraicGeometry.Space

end
