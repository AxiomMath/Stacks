module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Permanence along a surjective morphism of algebraic spaces

Let `p = f ≫ q` be a commuting triangle of morphisms of algebraic spaces over `S` with `f`
surjective. If `f` and `p` both have one of the chart-tested properties of Stacks 03MJ, then so
does `q`, provided the corresponding property of morphisms of schemes has that permanence.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_surjective` is the reduction of the
  statement for algebraic spaces to the statement for schemes.
* `AlgebraicGeometry.Space.isSmooth_of_comp_surjective_isSmooth` and
  `AlgebraicGeometry.Space.isEtale_of_comp_surjective_isEtale` are the smooth and étale cases.

## Implementation notes

Given a square of étale charts `a` of `Y` and `b` of `Z` over `α`, the fibre product of `f`
with `a` is an algebraic space whose projection to `Y` is surjective and whose projection to
`X` is étale. An atlas `W` of that fibre product therefore yields a chart `W ⟶ U` of the site
which is surjective as a morphism of schemes, together with an étale chart of `X` over it, and
the hypotheses on `f` and on `p` apply to the two squares so obtained. The scheme-level
permanence statement then gives the property of the morphism of schemes underlying `α`.

Étaleness of a morphism of algebraic spaces is not by definition a chart condition, so the
étale case passes through `AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`.

## References

* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A property of morphisms of schemes which passes from a composite `g ≫ r` with `g`
surjective to `r` passes, in the chart sense of Stacks 03MJ, from a composite `f ≫ q` of
morphisms of algebraic spaces with `f` surjective to `q`. -/
theorem holdsOnEveryEtaleChart_of_comp_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (scheme_case : ∀ {A C D : Scheme.{u}} (g : A ⟶ C) (r : C ⟶ D),
      Surjective g → P g → P (g ≫ r) → P r)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hcomm : p = f ≫ q)
    (hfs : IsSurjective B S hS f)
    (hf : HoldsOnEveryEtaleChart B S hS P f)
    (hp : HoldsOnEveryEtaleChart B S hS P p) :
    HoldsOnEveryEtaleChart B S hS P q := by
  intro U V a b α ha hb hab
  let T := BigFppfOver.toScheme B S hS
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
  have hprojEtale : IsEtale B S hS fstP.hom :=
    isEtale_of_isPullback B S hS sndP fstP ao fo hpb.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr ha)
  obtain ⟨W, c, hcSurj, hcEtale⟩ := Po.property.exists_atlas
  have hcPoints : IsSurjective B S hS c :=
    (surjective_iff_surjective_pointsMap B S hS Po.obj Po.property W c).mp hcSurj
  let δ : W ⟶ U := yoneda.preimage (c ≫ sndP.hom)
  have hδ : yoneda.map δ = c ≫ sndP.hom := yoneda.map_preimage _
  have hδSurj : Surjective (T.map δ) := by
    refine (presheaf_yoneda_map_iff B S hS (P := @Surjective.{u}) inferInstance δ).mp ?_
    refine (surjective_iff_surjective_pointsMap B S hS (yoneda.obj U) hU W (yoneda.map δ)).mpr ?_
    rw [hδ]
    exact isSurjective_comp B S hS hcPoints hprojSurj
  have hdEtalePres : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf (c ≫ fstP.hom) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (c ≫ fstP.hom)).mp
      (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS c).mpr hcEtale) hprojEtale)
  have hδP : P (T.map δ) := by
    refine hf W U (c ≫ fstP.hom) a δ hdEtalePres ha ?_
    rw [hδ]
    simp only [Category.assoc, hpullComm]
  have hδαP : P (T.map (δ ≫ α)) := by
    refine hp W V (c ≫ fstP.hom) b (δ ≫ α) hdEtalePres hb ?_
    rw [Functor.map_comp, Category.assoc, hab, hδ, hcomm]
    simp only [Category.assoc, reassoc_of% hpullComm]
  exact scheme_case (T.map δ) (T.map α) hδSurj hδP (by simpa using hδαP)

/-- **Stacks 0AHD**, smooth case. In a commuting triangle `p = f ≫ q` of morphisms of
algebraic spaces over `S` with `f` surjective and smooth, smoothness of `p` implies smoothness
of `q`. -/
@[stacks 0AHD "smooth case"]
theorem isSmooth_of_comp_surjective_isSmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hcomm : p = f ≫ q) (hfs : IsSurjective B S hS f)
    (hf : IsSmooth B S hS f) (hp : IsSmooth B S hS p) :
    IsSmooth B S hS q := by
  refine holdsOnEveryEtaleChart_of_comp_surjective B S hS
    (@Smooth.{u} : MorphismProperty Scheme.{u}) 
    (fun g r (_ : Surjective g) (_ : Smooth g) (_ : Smooth (g ≫ r)) =>
      Stacks.Smooth.smooth_of_comp_surjective_smooth g r)
    hX hY f p q hcomm hfs hf hp

/-- **Stacks 0AHD**, étale case. In a commuting triangle `p = f ≫ q` of morphisms of algebraic
spaces over `S` with `f` surjective and étale, étaleness of `p` implies étaleness of `q`. -/
@[stacks 0AHD "étale case"]
theorem isEtale_of_comp_surjective_isEtale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hcomm : p = f ≫ q) (hfs : IsSurjective B S hS f)
    (hf : IsEtale B S hS f) (hp : IsEtale B S hS p) :
    IsEtale B S hS q := by
  refine (isEtale_iff_holdsOnEveryEtaleChart B S hS hY hZ q).2 ?_
  refine holdsOnEveryEtaleChart_of_comp_surjective B S hS
    (@Etale.{u} : MorphismProperty Scheme.{u}) 
    (fun g r (_ : Surjective g) (_ : Etale g) (_ : Etale (g ≫ r)) =>
      Stacks.Etale.etale_of_comp_surjective_etale g r)
    hX hY f p q hcomm hfs
    ((isEtale_iff_holdsOnEveryEtaleChart B S hS hX hY f).1 hf)
    ((isEtale_iff_holdsOnEveryEtaleChart B S hS hX hZ p).1 hp)

end AlgebraicGeometry.Space

end
