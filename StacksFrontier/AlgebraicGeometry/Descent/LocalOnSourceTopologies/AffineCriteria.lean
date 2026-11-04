module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme

/-!
# Affine criteria for source locality in the fpqc, fppf and smooth topologies

A property of morphisms of schemes is local on the source for the fpqc (respectively fppf,
respectively smooth) topology as soon as it is Zariski local on the source and on the target, is
preserved by precomposition with flat morphisms (respectively with flat morphisms locally of
finite presentation, respectively with smooth morphisms), and descends along a surjective flat
morphism (respectively a surjective flat morphism locally of finite presentation, respectively a
surjective smooth morphism) of affine schemes.

The syntomic and étale cases are `AlgebraicGeometry.isLocalAtSource_syntomic_of_affine_descent`
and `AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`.

## Main results

* `AlgebraicGeometry.Scheme.jointlySurjective_precoverage`: a covering family for the
  precoverage attached to a morphism property is jointly surjective.
* `AlgebraicGeometry.affine_descent_of_quasiCompactCover`: a property Zariski local on the
  source, which descends along surjective `Q`-morphisms of affine schemes, can be checked on a
  quasi-compact `Q`-covering of an affine scheme.
* `AlgebraicGeometry.isLocalAtSource_fpqc_of_affine_descent`: the affine criterion for fpqc
  locality on the source.
* `AlgebraicGeometry.isLocalAtSource_fppf_of_affine_descent`: the affine criterion for fppf
  locality on the source.
* `AlgebraicGeometry.isLocalAtSource_smooth_of_affine_descent`: the affine criterion for smooth
  locality on the source.

## References

* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- A covering family for the precoverage attached to a morphism property is jointly
surjective. -/
theorem Scheme.jointlySurjective_precoverage (Q : MorphismProperty Scheme.{u}) :
    Scheme.JointlySurjective (Scheme.precoverage Q) where
  exists_eq {X} R hR x := by
    obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
    obtain ⟨i, hi⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).mp hR).1 x
    exact ⟨Y i, f i, ⟨i⟩, hi⟩

/-- Being flat and locally of finite presentation is Zariski local on the source. -/
theorem isZariskiLocalAtSource_flat_inf_locallyOfFinitePresentation :
    IsZariskiLocalAtSource (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  MorphismProperty.IsLocalAtSource.inf _ _

/-- Being flat and locally of finite presentation is preserved by precomposition with an open
immersion. -/
theorem respectsLeft_isOpenImmersion_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.RespectsLeft
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (@IsOpenImmersion.{u}) :=
  let := isZariskiLocalAtSource_flat_inf_locallyOfFinitePresentation.{u}
  ⟨fun i _ _ hf ↦ IsZariskiLocalAtSource.comp
    (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) hf i⟩

variable {Q : MorphismProperty Scheme.{u}}

/-- A property that is Zariski local on the source descends along a quasi-compact `Q`-covering
of an affine scheme, provided it descends along surjective `Q`-morphisms of affine schemes. -/
theorem affine_descent_of_quasiCompactCover (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] [Q.RespectsLeft (@IsOpenImmersion.{u})]
    [IsZariskiLocalAtSource Q]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (U : Scheme.Cover.{v} (Scheme.precoverage Q) X)
    [QuasiCompactCover U.toPreZeroHypercover] (hU : ∀ i, P (U.f i ≫ f))
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Q g → P (g ≫ f) → P f) : P f := by
  obtain ⟨V, r, hfinite, hopen⟩ := QuasiCompactCover.exists_hom U
  have : Finite V.I₀ := hfinite
  exact affine_descent_of_refinement P f U V r hopen hU hAffine
    (IsZariskiLocalAtSource.sigmaDesc (P := Q) V.map_prop)

/-- A property that is Zariski local on the source descends along a covering for the precoverage
of a morphism property `Q` consisting of open morphisms, provided it descends along surjective
`Q`-morphisms of affine schemes. -/
private theorem affine_descent_of_isOpenMap_cover (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] [Q.RespectsLeft (@IsOpenImmersion.{u})]
    [IsZariskiLocalAtSource Q] (hQ : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), Q g → IsOpenMap g)
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (U : (Scheme.precoverage Q).ZeroHypercover.{u + 1} X) (hU : ∀ i, P (U.f i ≫ f))
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Q g → P (g ≫ f) → P f) : P f :=
  have : QuasiCompactCover U.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun i ↦ hQ _ (Scheme.Cover.map_prop U i)
  affine_descent_of_quasiCompactCover P f U hU hAffine

/-- A property of morphisms of schemes which is Zariski local on the source and on the target,
which is preserved by precomposition with flat morphisms, and which descends along surjective
flat morphisms of affine schemes, is fpqc local on the source. -/
@[stacks 036H "fpqc case"]
theorem isLocalAtSource_fpqc_of_affine_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Flat.{u})] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Flat g → P (g ≫ f) → P f) :
    P.IsLocalAtSource Scheme.fpqcPrecoverage := by
  have := Scheme.jointlySurjective_precoverage (@Flat.{u})
  have hzls : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have := @IsZariskiLocalAtSource.respectsLeft_isOpenImmersion _ hzls
  refine isLocalAtSource_of_affineCriterion (P := P) (Q := @Flat.{u})
    (K := Scheme.fpqcPrecoverage) (fun U i ↦ ?_) (fun {X Y} _ _ f U hU ↦ ?_)
  · exact Scheme.Cover.map_prop
      (P := @Flat.{u}) ({ __ := U.toPreZeroHypercover, mem₀ := U.mem₀.2 } :
        Scheme.Cover.{u + 1} _ _) i
  · let U' : Scheme.Cover.{u + 1} (Scheme.precoverage (@Flat.{u})) X :=
      { __ := U.toPreZeroHypercover, mem₀ := U.mem₀.2 }
    have : QuasiCompactCover U'.toPreZeroHypercover :=
      Scheme.presieve₀_mem_qcPrecoverage_iff.mp U.mem₀.1
    exact affine_descent_of_quasiCompactCover P f U' hU hAffine

/-- A property of morphisms of schemes which is Zariski local on the source and on the target,
which is preserved by precomposition with flat morphisms locally of finite presentation, and
which descends along surjective flat morphisms locally of finite presentation of affine schemes,
is fppf local on the source. -/
@[stacks 036H "fppf case"]
theorem isLocalAtSource_fppf_of_affine_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})]
    [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Flat g → LocallyOfFinitePresentation g →
        P (g ≫ f) → P f) :
    P.IsLocalAtSource Scheme.fppfPrecoverage := by
  have := Scheme.jointlySurjective_precoverage
    (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
  have := isZariskiLocalAtSource_flat_inf_locallyOfFinitePresentation.{u}
  have := respectsLeft_isOpenImmersion_flat_inf_locallyOfFinitePresentation.{u}
  refine isLocalAtSource_of_affineCriterion (P := P)
    (Q := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
    (K := Scheme.fppfPrecoverage) (fun U i ↦ ?_) (fun {X Y} _ _ f U hU ↦ ?_)
  · exact Scheme.Cover.map_prop U i
  · exact affine_descent_of_isOpenMap_cover P (fun g hg ↦ by
      have : Flat g := hg.1
      have : LocallyOfFinitePresentation g := hg.2
      exact Scheme.Hom.isOpenMap g) f U hU
      fun g f hg hQg hcomp ↦ hAffine g f hg hQg.1 hQg.2 hcomp

/-- A property of morphisms of schemes which is Zariski local on the source and on the target,
which is preserved by precomposition with smooth morphisms, and which descends along surjective
smooth morphisms of affine schemes, is smooth local on the source. -/
@[stacks 036H "smooth case"]
theorem isLocalAtSource_smooth_of_affine_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Smooth.{u})] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Smooth g → P (g ≫ f) → P f) :
    P.IsLocalAtSource (Scheme.precoverage (@Smooth.{u})) := by
  have := precoverage_isStableUnderBaseChange (@Smooth.{u})
  have := Scheme.jointlySurjective_precoverage (@Smooth.{u})
  have hzls : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  have := @IsZariskiLocalAtSource.respectsLeft_isOpenImmersion _ hzls
  refine isLocalAtSource_of_affineCriterion (P := P) (Q := @Smooth.{u})
    (K := Scheme.precoverage (@Smooth.{u})) (fun U i ↦ ?_) (fun {X Y} _ _ f U hU ↦ ?_)
  · exact Scheme.Cover.map_prop U i
  · exact affine_descent_of_isOpenMap_cover P (fun g hg ↦ by
      have : Smooth g := hg
      exact Scheme.Hom.isOpenMap g) f U hU hAffine

end AlgebraicGeometry

end
