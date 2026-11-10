module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductFundamentalClassBivariant

/-!
# Proper pushforward commutes with the exterior product by a fundamental class

Let `(S, δ)` be a base situation whose base is the spectrum of a field, so that the exterior
product of Stacks 0FBV is available, let `X` be an **integral** scheme locally of finite type and
flat over `S` of relative dimension `d`, and let `h : Y' ⟶ Y` be a proper morphism of schemes
locally of finite type over `S`. Then

  `[X] × h_*γ = (1_X × h)_*([X] × γ)`

in `CH_{d+m}(X ×_S Y)` for every `γ ∈ CH_m(Y')`, where `[X] ∈ CH_d(X)` is the fundamental class
of `X` and `1_X × h : X ×_S Y' ⟶ X ×_S Y` is the base change of `h`.

This is condition (1) of Stacks 0B76 — proper naturality — for the operation `γ ↦ [X] × γ`, and it
is the proper-pushforward half of the presentation of the exterior product by a bivariant class
that the proof of Stacks 0FBW uses. Its flat-pullback counterpart, for an arbitrary class in the
first variable, is
`Stacks.Chow.flatPullbackChow_chowExteriorProduct_tmul` of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductFlatPullback`.

## Main results

* `Stacks.Chow.isProper_exteriorProductSndMap` — the base change `1_X × h` of a proper morphism is
  proper, so Chow classes may be pushed forward along it.
* `Stacks.Chow.chowExteriorProduct_properChowPushforward_fundamentalChowClass` — the identity
  above, on Chow groups.

## Implementation notes

### Why this is Stacks 02RG and nothing more

The square

      X ×_S Y' --1×h--> X ×_S Y
         |                 |
       pr_{Y'}           pr_Y
         v                 v
         Y' -----h------>  Y

is cartesian, its horizontal legs are proper and its vertical legs are flat of the common
relative dimension `d`, namely the relative dimension of `X` over the base, both being base
changes of the structure morphism of `X`. So Stacks 02RG applies to it and gives

  `pr_Y^*(h_*γ) = (1 × h)_*(pr_{Y'}^* γ)`.

Each side is then rewritten by clause (1) of **Stacks 0B0R**, which identifies the flat pullback
along the projection `pr_Y : X ×_S Y ⟶ Y` of an integral `X` with the exterior product `[X] × -`;
on Chow groups that is
`Stacks.Chow.chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct`. Nothing else
enters: in particular no multiplicity computation is performed here, the whole content sitting in
Stacks 02RG and in Stacks 0B0R.

### What is not proved, and why

The first variable is a fundamental class and not an arbitrary Chow class. The reason is that
clause (1) of Stacks 0B0R is the only statement in this repository relating the exterior product
to a flat pullback along a product projection, and it requires the factor it replaces to be the
fundamental class of an **integral** scheme. For an arbitrary `α ∈ CH_n(X)` the source argues
coefficientwise: the exterior product `α × γ` is a locally finite sum over the support of `α` of
pushforwards, along the closed immersions `closure {x} ×_S Y ↪ X ×_S Y`, of flat pullbacks along
`closure {x} ×_S Y ⟶ Y`, and the identity above has to be summed over that support after being
applied to each reduced point closure. That decomposition of the exterior product over the
support of one of its factors has no carrier in this repository, and it is what separates the
statement below from the general one.

No `@[stacks 0B0R]` attribute is carried. Stacks 0B0R is a statement about product projections on
nonsingular varieties, registered on
`Stacks.Intersection.ExteriorProductProjections.exteriorProduct_projections`, whose clause (1) in
general form is `Stacks.Chow.flatPullbackSnd_eq_fundamentalCycle_exteriorProduct`; the identity
below is not a clause of it, so tagging it would record coverage the tag does not assert.

### The hypotheses carried

* `hfp : Stacks.Chow.FlatPullbackDescends C` is **Stacks 02S1** and
  `hpp : Stacks.Chow.ProperPushforwardDescends C` is **Stacks 02S2**. Without them neither
  `Stacks.Chow.flatPullbackChow` nor `Stacks.Chow.properChowPushforward` nor
  `Stacks.Chow.chowExteriorProduct` exists, so they are prerequisites of writing the statement
  down at all.
* `hRG : Stacks.Chow.ProperPushforwardFlatPullbackBaseChange C` is **Stacks 02RG on Chow groups**,
  in the four-corner form of the source. It is the bundled hypothesis of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass`, already carried by Stacks
  0B78, by the surjectivity half of Stacks 0FBW and by Stacks 0FBX in this repository; this module
  introduces no new stand-in for it.

### Degrees

The exterior product with a class of degree `d` sends degree `m` to `d + m`, while flat pullback
of relative dimension `d` sends it to `m + d`. These are the same integer and not the same term,
and `Stacks.Chow.chowGroupDegreeEquiv` mediates; the two statements of Stacks 02RG that are
compared are therefore matched through `Stacks.Chow.properChowPushforward_heq_congr`, which says
that proper pushforward depends on its degree and its argument only up to heterogeneous equality.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The base change of a proper morphism in the second factor -/

/-- The morphism `1_X × h : X ×_S Y' ⟶ X ×_S Y` is proper when `h` is, being a base change of
`h`. This is the instance that lets Chow classes be pushed forward along `1_X × h`. -/
instance isProper_exteriorProductSndMap {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) [IsProper h] (hh : h ≫ g = g') :
    IsProper (exteriorProductSndMap f g g' h hh) :=
  MorphismProperty.of_isPullback (isPullback_exteriorProductSndMap f g g' h hh).flip
    inferInstance

/-! ### Proper naturality of the exterior product by a fundamental class -/

/-- **Proper pushforward commutes with the exterior product by a fundamental class.** Let the base
be the spectrum of a field, let `X` be integral and flat over it of relative dimension `d`, let
`h : Y' ⟶ Y` be proper over the base and let `γ ∈ CH_m(Y')`. Then

  `[X] × h_*γ = (1_X × h)_*([X] × γ)`

in `CH_{d+m}(X ×_S Y)`.

This is condition (1) of Stacks 0B76 — proper naturality — for the operation `γ ↦ [X] × γ`. Both
sides are produced in degree `d + m`, so no transport is needed at the outside; the two
intermediate flat pullbacks live in degree `m + d` and are matched through
`Stacks.Chow.chowGroupDegreeEquiv`.

The proof is Stacks 02RG, carried as `hRG`, for the cartesian square whose horizontal legs are
`h` and `1_X × h` and whose vertical legs are the two projections to `Y'` and to `Y`, followed on
each side by clause (1) of Stacks 0B0R in the form
`Stacks.Chow.chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct`. -/
theorem chowExteriorProduct_properChowPushforward_fundamentalChowClass (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX] [IsIntegral X]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [IsProper h] (hh : h ≫ sY = sY') (d : ℕ)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    (hfp : FlatPullbackDescends C) (hpp : ProperPushforwardDescends C)
    (hRG : ProperPushforwardFlatPullbackBaseChange C) (m : ℤ)
    (γ : chowGroup C sY' m) :
    chowExteriorProduct C hδ sX sY (d : ℤ) m
        (TensorProduct.tmul ℤ (fundamentalChowClass C sX (d : ℤ))
          (properChowPushforward C sY' sY h hh m (hpp sY' sY h hh m) γ)) =
      properChowPushforward C (pullback.fst sX sY' ≫ sX) (pullback.fst sX sY ≫ sX)
        (exteriorProductSndMap sX sY sY' h hh)
        (exteriorProductSndMap_comp_structureMorphism sX sY sY' h hh) ((d : ℤ) + m)
        (hpp (pullback.fst sX sY' ≫ sX) (pullback.fst sX sY ≫ sX)
          (exteriorProductSndMap sX sY sY' h hh)
          (exteriorProductSndMap_comp_structureMorphism sX sY sY' h hh) ((d : ℤ) + m))
        (chowExteriorProduct C hδ sX sY' (d : ℤ) m
          (TensorProduct.tmul ℤ (fundamentalChowClass C sX (d : ℤ)) γ)) := by
  have hrel (Z : Scheme.{u}) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] :
      AlgebraicGeometry.RelativeDimension (pullback.snd sX sZ) d :=
    relativeDimension_pullbackSnd sX hfr sZ
  have hfac (Z : Scheme.{u}) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] :
      FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst sX sZ ≫ sX) sZ
        (pullback.snd sX sZ) pullback.condition.symm d (hrel Z sZ) m :=
    hfp _ sZ _ _ d (hrel Z sZ) m
  have hbase := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct C hδ sX sY d
    (hrel Y sY) hd m (hfac Y sY)
    (properChowPushforward C sY' sY h hh m (hpp sY' sY h hh m) γ)
  have hbase' := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct C hδ sX sY' d
    (hrel Y' sY') hd m (hfac Y' sY') γ
  have hppmd (n : ℤ) := hpp (pullback.fst sX sY' ≫ sX) (pullback.fst sX sY ≫ sX)
    (exteriorProductSndMap sX sY sY' h hh)
    (exteriorProductSndMap_comp_structureMorphism sX sY sY' h hh) n
  have hsq := hRG sY' (pullback.fst sX sY' ≫ sX) sY (pullback.fst sX sY ≫ sX) h hh
    (exteriorProductSndMap sX sY sY' h hh)
    (exteriorProductSndMap_comp_structureMorphism sX sY sY' h hh) (pullback.snd sX sY')
    pullback.condition.symm (pullback.snd sX sY) pullback.condition.symm
    (isPullback_exteriorProductSndMap sX sY sY' h hh).flip d (hrel Y' sY')
    (hrel Y sY) m (hfac Y' sY') (hfac Y sY)
    (hpp sY' sY h hh m) (hppmd _) γ
  refine eq_of_heq (HEq.trans ?_ (properChowPushforward_heq_congr C
    (pullback.fst sX sY' ≫ sX) (pullback.fst sX sY ≫ sX) (exteriorProductSndMap sX sY sY' h hh)
    (exteriorProductSndMap_comp_structureMorphism sX sY sY' h hh) (add_comm m (d : ℤ)) (hppmd _)
    (hppmd _) _ _
    (hbase' ▸ chowGroupDegreeEquiv_heq C (pullback.fst sX sY' ≫ sX)
      (add_comm m (d : ℤ)) _).symm))
  rw [← hbase, hsq]
  exact chowGroupDegreeEquiv_heq C (pullback.fst sX sY ≫ sX) (add_comm m (d : ℤ)) _

end Stacks.Chow

end
