module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback

/-!
# Flat pullback commutes with the exterior product

Let `(S, δ)` be a base situation whose base is the spectrum of a field, so that the exterior
product of Stacks 0FBV is available, let `X`, `Y` and `Y'` be schemes locally of finite type
over `S` and let `h : Y' ⟶ Y` be a flat morphism over `S` of relative dimension `r`. Then
`1_X × h : X ×_S Y' ⟶ X ×_S Y` is flat of relative dimension `r` as well, and

  `α × h^*γ = (1_X × h)^*(α × γ)`

for `α ∈ CH_n(X)` and `γ ∈ CH_m(Y)`.

This is condition (2) of Stacks 0B76 — flat naturality — for the operation `γ ↦ α × γ`, and it
is one of the two inputs the proof of Stacks 0FBW needs in order to present the exterior product
with `α` as the cap product of a bivariant class `c_α ∈ A^{-n}(X ⟶ S)`. Before this module the
exterior product had no naturality lemma of any kind; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductBivariant`.

## Main definitions

* `Stacks.Chow.exteriorProductSndMap` — the morphism `1_X × h : X ×_S Y' ⟶ X ×_S Y`, pinned down
  by its two projections.

## Main results

* `Stacks.Chow.isPullback_exteriorProductSndMap` — `1_X × h` is the base change of `h` along the
  second projection of `X ×_S Y`. Flatness and local finite type of `1_X × h` are read off from
  that square and registered as instances, and its relative dimension is
  `Stacks.Chow.relativeDimension_exteriorProductSndMap`.
* `Stacks.Chow.closedSubschemeCycleCoeff_comap_exteriorProductSndMap` — the multiplicity
  identity where the mathematics sits, for a pair of ideal sheaves.
* `Stacks.Chow.exteriorProductWeight_mul_flatPullbackWeight_sndMap` — the same identity for the
  reduced point closures, which is the form the coefficient formula for the exterior product
  needs.
* `Stacks.Chow.flatPullback_exteriorProduct_sndMap` — the identity on cycles.
* `Stacks.Chow.flatPullbackChow_chowExteriorProduct_tmul` — the identity on **Chow groups**,
  which is the form the bivariant-class conditions of Stacks 0B76 are stated in.
* `Stacks.Chow.flatPullbackChow_chowExteriorProduct_tmul_field` — the same over
  `Stacks.Chow.fieldChowSituation`, where the hypotheses on reduced point closures are
  discharged and only Stacks 02S1 remains assumed.

## Implementation notes

### Why the multiplicity identity is the whole content

Both sides of the cycle identity have a three-factor coefficient formula, and after the two
cycle coefficients `α(pr_X w)` and `γ(h(pr_{Y'} w))` are cancelled what is left is an identity
between two products of two multiplicities. Each of the four multiplicities is a
`Stacks.Chow.closedSubschemeCycleCoeff`, and the identity is obtained by writing both products
as the single multiplicity of the closed subscheme

  `closure {pr_X w} ×_S h^{-1}(closure {h (pr_{Y'} w)})`

of `X ×_S Y'`, in two ways:

* along `1_X × h`, by `Stacks.Chow.closedSubschemeCycleCoeff_comap` — the coefficientwise form
  of Stacks 02RE, part (1) — applied to the ideal sheaf of the product of the two reduced point
  closures downstairs, whose delta-dimension bound is
  `Stacks.Chow.schemeDeltaDimension_product_le`;
* along the projection `closure {pr_X w} ×_S Y' ⟶ Y'`, by
  `Stacks.Chow.closedSubschemeCycleCoeff_product_left` — multiplicativity of the multiplicity in
  a product — applied to the inverse image ideal sheaf `h^{-1}(closure {h (pr_{Y'} w)})`, whose
  delta-dimension bound is `Stacks.Chow.schemeDeltaDimension_comap_le_of_relativeDimension`.

The two readings are compared through the identity of ideal sheaves

  `(I ×_S J).comap (1_X × h) = I.comap pr_X ⊔ (J.comap h).comap pr_{Y'}`,

which is `Scheme.IdealSheafData.comap_sup` together with the two projection formulas for
`1_X × h`. No new commutative algebra enters: the length computations are the ones already
carried by Stacks 02RE and by the multiplicativity lemmas of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity`.

The degrees of the two readings are `(n + m) + r` and `n + (m + r)`, which is why the cycle
identity below is stated between the underlying algebraic cycles and the Chow-group identity
through `Stacks.Chow.chowGroupDegreeEquiv`, exactly as for associativity in
`Stacks.Chow.chowExteriorProduct_assoc`.

### The two flatness hypotheses on reduced point closures

Multiplicativity of the multiplicity in a product requires one of the two factors to be flat
over the base of a fixed relative dimension. Over a field base every morphism is flat, and the
reduced closure of a point of relative dimension `d` has constant fibre dimension `d`, so both
requirements hold; but this repository derives the second only for
`Stacks.Chow.fieldChowSituation`, by
`Stacks.Chow.pointClosure_relativeDimension`, and not for
an abstract base situation with a one-point integral base. The statements over an abstract base
therefore carry the two hypotheses `hXclosure` and `hYclosure`, quantified over the points of
relative dimension `n` of `X` and of relative dimension `m` of `Y` — exactly the points at which
`α` and `γ` can have a nonzero coefficient — and
`Stacks.Chow.flatPullbackChow_chowExteriorProduct_tmul_field` discharges both over a field. This
matches the existing clause (1) of Stacks 0B0R,
`Stacks.Chow.flatPullbackFst_eq_exteriorProduct_fundamentalCycle`, which carries the relative
dimension of the projection it uses as a hypothesis for the same reason.

The natural numbers `nn` and `mm` with `(nn : ℤ) = n` and `(mm : ℤ) = m` are needed because
`AlgebraicGeometry.RelativeDimension` is indexed by a natural number while delta-dimensions are
integers. The equalities are part of `hXclosure` and `hYclosure` rather than separate
hypotheses, because over a field the delta-dimension of a point is non-negative only when such
a point exists, and that is exactly the situation those hypotheses are quantified over.

### Why no tag is carried

The Stacks Project has no tagged statement asserting that the exterior product commutes with
flat pullback. The exterior product is introduced in the running prose of section 0B09 and in
the proof of Stacks 0FBV, and its compatibility with flat pullback is used inside the proofs of
Stacks 0FBV and 0FBW rather than stated. The one tagged statement in that neighbourhood,
Stacks 0B0R, is a statement about nonsingular varieties whose clause (1) compares a flat
pullback along a *product projection* with an exterior product with a *fundamental cycle*; that
is the special case `h = pr_Y` and `α = [X]`, and it is already formalized as
`Stacks.Chow.flatPullbackSnd_eq_fundamentalCycle_exteriorProduct`. The general statement below
is not a clause of it, so it is left untagged.

## References

* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The base change of a morphism in the second factor -/

/-- The morphism `1_X × h : X ×_S Y' ⟶ X ×_S Y` induced by `h : Y' ⟶ Y` over `S`: the unique
morphism whose first projection is the first projection of `X ×_S Y'` and whose second
projection is `h` after the second projection of `X ×_S Y'`. -/
def exteriorProductSndMap {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S)
    (h : Y' ⟶ Y) (hh : h ≫ g = g') :
    (pullback f g' : Scheme.{u}) ⟶ (pullback f g : Scheme.{u}) :=
  pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ h)
    (by rw [Category.assoc, hh]; exact pullback.condition)

/-- The first projection of `1_X × h` is the first projection of `X ×_S Y'`. -/
@[simp]
theorem exteriorProductSndMap_comp_fst {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) (hh : h ≫ g = g') :
    exteriorProductSndMap f g g' h hh ≫ pullback.fst f g = pullback.fst f g' :=
  pullback.lift_fst _ _ _

/-- The second projection of `1_X × h` is `h` after the second projection of `X ×_S Y'`. -/
@[simp]
theorem exteriorProductSndMap_comp_snd {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) (hh : h ≫ g = g') :
    exteriorProductSndMap f g g' h hh ≫ pullback.snd f g = pullback.snd f g' ≫ h :=
  pullback.lift_snd _ _ _

/-- On points, the first projection of the image of `w` under `1_X × h` is the first projection
of `w`. -/
@[simp]
theorem exteriorProductSndMap_base_fst {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) (hh : h ≫ g = g') (w : (pullback f g' : Scheme.{u})) :
    (pullback.fst f g).base ((exteriorProductSndMap f g g' h hh).base w) =
      (pullback.fst f g').base w := by
  rw [← Scheme.Hom.comp_apply, exteriorProductSndMap_comp_fst]

/-- On points, the second projection of the image of `w` under `1_X × h` is `h` of the second
projection of `w`. -/
@[simp]
theorem exteriorProductSndMap_base_snd {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) (hh : h ≫ g = g') (w : (pullback f g' : Scheme.{u})) :
    (pullback.snd f g).base ((exteriorProductSndMap f g g' h hh).base w) =
      h.base ((pullback.snd f g').base w) := by
  rw [← Scheme.Hom.comp_apply, exteriorProductSndMap_comp_snd, Scheme.Hom.comp_apply]

/-- `1_X × h` is a morphism over `S`: composing it with the structure morphism of `X ×_S Y`
gives the structure morphism of `X ×_S Y'`. -/
theorem exteriorProductSndMap_comp_structureMorphism {S X Y Y' : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (g' : Y' ⟶ S) (h : Y' ⟶ Y) (hh : h ≫ g = g') :
    exteriorProductSndMap f g g' h hh ≫ (pullback.fst f g ≫ f) = pullback.fst f g' ≫ f := by
  rw [← Category.assoc, exteriorProductSndMap_comp_fst]

/-- `1_X × h` is the base change of `h` along the second projection of `X ×_S Y`: the square
whose vertical arrows are the two second projections and whose horizontal arrows are `1_X × h`
and `h` is cartesian. -/
theorem isPullback_exteriorProductSndMap {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) (hh : h ≫ g = g') :
    IsPullback (exteriorProductSndMap f g g' h hh) (pullback.snd f g')
      (pullback.snd f g) h := by
  refine IsPullback.of_right ?_ (exteriorProductSndMap_comp_snd f g g' h hh)
    (IsPullback.of_hasPullback f g)
  rw [exteriorProductSndMap_comp_fst, hh]
  exact IsPullback.of_hasPullback f g'

/-- `1_X × h` is flat when `h` is flat. -/
instance flat_exteriorProductSndMap {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) [Flat h] (hh : h ≫ g = g') :
    Flat (exteriorProductSndMap f g g' h hh) :=
  MorphismProperty.of_isPullback (isPullback_exteriorProductSndMap f g g' h hh).flip
    inferInstance

/-- `1_X × h` is locally of finite type when `h` is locally of finite type. -/
instance locallyOfFiniteType_exteriorProductSndMap {S X Y Y' : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (g' : Y' ⟶ S) (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hh : h ≫ g = g') :
    LocallyOfFiniteType (exteriorProductSndMap f g g' h hh) :=
  MorphismProperty.of_isPullback (isPullback_exteriorProductSndMap f g g' h hh).flip
    inferInstance

/-- `1_X × h` has the relative dimension of `h`, being a base change of it. -/
theorem relativeDimension_exteriorProductSndMap {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hh : h ≫ g = g') (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) :
    AlgebraicGeometry.RelativeDimension (exteriorProductSndMap f g g' h hh) r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    (isPullback_exteriorProductSndMap f g g' h hh).flip hr

/-! ### Two facts about reduced point closures -/

/-- The reduced closure of a point of relative dimension `d` has delta-dimension at most `d`. -/
theorem schemeDeltaDimension_vanishingIdeal_closure_le (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (x : X) (d : ℤ)
    (hd : relativeDimension C.dimensionFunction p x = d) :
    schemeDeltaDimension C
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ p) ≤ (d : EInt) :=
  le_of_eq ((schemeDeltaDimension_integralComponentAt C p x).trans
    (congrArg WithBotTop.coe hd))

/-! ### The multiplicity identity -/

/-- **The multiplicity identity behind flat naturality of the exterior product.** Let `I` be an
ideal sheaf on `X` whose closed subscheme is flat of relative dimension `nn` over the base and
has delta-dimension at most `n`, let `J` be an ideal sheaf on `Y` whose closed subscheme is flat
of relative dimension `mm` and has delta-dimension at most `m`, and let `h : Y' ⟶ Y` be flat of
relative dimension `r`. For a point `w` of `X ×_S Y'` whose first projection lies in the support
of `I`,

  `mult_{(1 × h)(w)}(I ×_S J) · mult_w(1 × h) = mult_{pr_{Y'} w}(h^{-1}J) · mult_w(I ×_S [pt])`,

where the last factor is the multiplicity of `w` in the product of the closed subscheme of `I`
with the reduced closure of the second projection of `w`.

Both sides are the multiplicity of `w` in the inverse image of `I ×_S J` along `1 × h`, which is
`I ×_S h^{-1}J`: the left-hand side reads it along `1 × h`, by the coefficientwise flat pullback
identity of Stacks 02RE; the right-hand side factors it in the product along the projection to
`Y'`, by multiplicativity of the multiplicity in a product. -/
theorem closedSubschemeCycleCoeff_comap_exteriorProductSndMap (C : ChowSituation.{u})
    {X Y Y' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (g' : Y' ⟶ C.S) [LocallyOfFiniteType g'] (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] [Flat h] (hh : h ≫ g = g') (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (I : X.IdealSheafData)
    (J : Y.IdealSheafData) [Flat (I.subschemeι ≫ f)] [Flat (J.subschemeι ≫ g)] (n m : ℤ)
    (nn mm : ℕ) (hn : (nn : ℤ) = n) (hm : (mm : ℤ) = m)
    (hI : AlgebraicGeometry.RelativeDimension (I.subschemeι ≫ f) nn)
    (hIle : schemeDeltaDimension C (I.subschemeι ≫ f) ≤ (n : EInt))
    (hJ : AlgebraicGeometry.RelativeDimension (J.subschemeι ≫ g) mm)
    (hJle : schemeDeltaDimension C (J.subschemeι ≫ g) ≤ (m : EInt))
    (w : (pullback f g' : Scheme.{u})) (hw : (pullback.fst f g').base w ∈ I.support) :
    closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
          (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).subschemeι (n + m)
          ((exteriorProductSndMap f g g' h hh).base w) *
        flatPullbackWeight C (pullback.fst f g' ≫ f) (exteriorProductSndMap f g g' h hh)
          (n + m + (r : ℤ)) w =
      closedSubschemeCycleCoeff C g' (J.comap h).subschemeι (m + (r : ℤ))
          ((pullback.snd f g').base w) *
        closedSubschemeCycleCoeff C (pullback.fst f g' ≫ f)
          (I.comap (pullback.fst f g') ⊔
            (Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({(pullback.snd f g').base w} : Set Y'))).comap
                (pullback.snd f g')).subschemeι (n + (m + (r : ℤ))) w := by
  have hprodle : schemeDeltaDimension C
      ((I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).subschemeι ≫
        pullback.fst f g ≫ f) ≤ ((n + m : ℤ) : EInt) := by
    have H := schemeDeltaDimension_product_le C f g I J mm hJ n hIle
    rwa [hm] at H
  have hKle : schemeDeltaDimension C ((J.comap h).subschemeι ≫ g') ≤
      ((m + (r : ℤ) : ℤ) : EInt) :=
    schemeDeltaDimension_comap_le_of_relativeDimension C g' g h hh r hr J m hJle
  have hideal : (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).comap
        (exteriorProductSndMap f g g' h hh) =
      I.comap (pullback.fst f g') ⊔ (J.comap h).comap (pullback.snd f g') := by
    simp only [Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp,
      exteriorProductSndMap_comp_fst, exteriorProductSndMap_comp_snd]
  have hleft := closedSubschemeCycleCoeff_comap C (pullback.fst f g' ≫ f)
    (pullback.fst f g ≫ f) (exteriorProductSndMap f g g' h hh)
    (exteriorProductSndMap_comp_structureMorphism f g g' h hh) r
    (relativeDimension_exteriorProductSndMap f g g' h hh r hr)
    (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)) (n + m) hprodle w
  have hright := closedSubschemeCycleCoeff_product_left C f g' I (J.comap h) nn hI
    (m + (r : ℤ)) hKle w hw
  rw [hideal] at hleft
  rw [hn] at hright
  rw [← hleft, add_assoc, hright]

/-- **The multiplicity identity for reduced point closures.** The specialisation of
`Stacks.Chow.closedSubschemeCycleCoeff_comap_exteriorProductSndMap` to the reduced closures of
the two projections of `w`, which is the shape in which the coefficient formula for the exterior
product consumes it: the exterior product multiplicity of `(1 × h)(w)` times the flat pullback
multiplicity of `1 × h` at `w` equals the flat pullback multiplicity of `h` at the second
projection of `w` times the exterior product multiplicity of `w` itself. -/
theorem exteriorProductWeight_mul_flatPullbackWeight_sndMap (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] {X Y Y' : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (g' : Y' ⟶ C.S)
    [LocallyOfFiniteType g'] (h : Y' ⟶ Y) [LocallyOfFiniteType h] [Flat h] (hh : h ≫ g = g')
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r) (n m : ℤ) (nn mm : ℕ)
    (hn : (nn : ℤ) = n) (hm : (mm : ℤ) = m) (w : (pullback f g' : Scheme.{u}))
    (hx : AlgebraicGeometry.RelativeDimension
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(pullback.fst f g').base w} : Set X))).subschemeι ≫ f) nn)
    (hdx : relativeDimension C.dimensionFunction f ((pullback.fst f g').base w) = n)
    (hy : AlgebraicGeometry.RelativeDimension
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure
          ({h.base ((pullback.snd f g').base w)} : Set Y))).subschemeι ≫ g) mm)
    (hdy : relativeDimension C.dimensionFunction g
      (h.base ((pullback.snd f g').base w)) = m) :
    exteriorProductWeight C f g (n + m) ((pullback.fst f g').base w)
            (h.base ((pullback.snd f g').base w))
            ((exteriorProductSndMap f g g' h hh).base w) *
          flatPullbackWeight C (pullback.fst f g' ≫ f) (exteriorProductSndMap f g g' h hh)
            (n + m + (r : ℤ)) w =
      flatPullbackWeight C g' h (m + (r : ℤ)) ((pullback.snd f g').base w) *
        exteriorProductWeight C f g' (n + (m + (r : ℤ))) ((pullback.fst f g').base w)
          ((pullback.snd f g').base w) w :=
  closedSubschemeCycleCoeff_comap_exteriorProductSndMap C f g g' h hh r hr _ _ n m nn mm hn hm
    hx (schemeDeltaDimension_vanishingIdeal_closure_le C f _ n hdx) hy
    (schemeDeltaDimension_vanishingIdeal_closure_le C g _ m hdy) w
    (mem_support_vanishingIdeal_closure_self _)

/-! ### Flat naturality of the exterior product of cycles -/

/-- **Flat pullback commutes with the exterior product, on cycles.** Let the base be the
spectrum of a field, let `h : Y' ⟶ Y` be flat over it of relative dimension `r`, let
`α ∈ Z_n(X)` and `γ ∈ Z_m(Y)`. Then

  `(1_X × h)^*(α × γ) = α × h^*γ`.

The two sides live in the cycle groups of delta-dimensions `(n + m) + r` and `n + (m + r)`,
equal integers but not syntactically equal ones, so the identity is stated between the
underlying algebraic cycles.

Both coefficients at a point `w` of `X ×_S Y'` are `α(pr_X w)` times `γ(h (pr_{Y'} w))` times a
product of two multiplicities, and the two products of multiplicities agree by
`Stacks.Chow.exteriorProductWeight_mul_flatPullbackWeight_sndMap`. The two flatness hypotheses
on reduced point closures are only used at points where the two cycle coefficients are nonzero,
which forces the relative dimensions to be `n` and `m`. -/
theorem flatPullback_exteriorProduct_sndMap (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] {X Y Y' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (g : Y ⟶ C.S) [LocallyOfFiniteType g] (g' : Y' ⟶ C.S) [LocallyOfFiniteType g']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] [Flat h] (hh : h ≫ g = g') (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (n m : ℤ) (nn mm : ℕ)
    (hXclosure : ∀ x : X, relativeDimension C.dimensionFunction f x = n →
      (nn : ℤ) = n ∧ AlgebraicGeometry.RelativeDimension
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ f) nn)
    (hYclosure : ∀ y : Y, relativeDimension C.dimensionFunction g y = m →
      (mm : ℤ) = m ∧ AlgebraicGeometry.RelativeDimension
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).subschemeι ≫ g) mm)
    (α : CycleGroup C f n) (γ : CycleGroup C g m) :
    (flatPullback C (pullback.fst f g' ≫ f) (pullback.fst f g ≫ f)
          (exteriorProductSndMap f g g' h hh)
          (exteriorProductSndMap_comp_structureMorphism f g g' h hh) r
          (relativeDimension_exteriorProductSndMap f g g' h hh r hr) (n + m)
          (exteriorProduct C f g n m α γ)).1 =
      (exteriorProduct C f g' n (m + (r : ℤ)) α (flatPullback C g' g h hh r hr m γ)).1 := by
  ext w
  simp only [flatPullback_apply, exteriorProduct_apply, exteriorProductSndMap_base_fst,
    exteriorProductSndMap_base_snd]
  by_cases hα : α.1 ((pullback.fst f g').base w) = 0
  · rw [hα]; ring
  by_cases hγ : γ.1 (h.base ((pullback.snd f g').base w)) = 0
  · rw [hγ]; ring
  have hdx : relativeDimension C.dimensionFunction f ((pullback.fst f g').base w) = n :=
    (mem_cyclesOfDimension_iff_forall_point C f n α.1).mp α.2 _ hα
  have hdy : relativeDimension C.dimensionFunction g
      (h.base ((pullback.snd f g').base w)) = m :=
    (mem_cyclesOfDimension_iff_forall_point C g m γ.1).mp γ.2 _ hγ
  obtain ⟨hn, hx⟩ := hXclosure _ hdx
  obtain ⟨hm, hy⟩ := hYclosure _ hdy
  rw [mul_assoc, exteriorProductWeight_mul_flatPullbackWeight_sndMap C f g g' h hh r hr n m
    nn mm hn hm w hx hdx hy hdy]
  ring

/-! ### Flat naturality of the exterior product on Chow groups -/

/-- **Flat pullback commutes with the exterior product, on Chow groups.** Let the base be the
spectrum of a field, let `h : Y' ⟶ Y` be flat over it of relative dimension `r`, let
`a ∈ CH_n(X)` and `c ∈ CH_m(Y)`. Then

  `(1_X × h)^*(a × c) = a × h^*c`

in `CH_{n + (m + r)}(X ×_S Y')`.

This is condition (2) of Stacks 0B76 — flat naturality — for the operation `c ↦ a × c`, and it
is the Chow-group statement the proof of Stacks 0FBW requires of the class `c_a` it attaches to
`a`. The left-hand side is produced in degree `(n + m) + r` and the right-hand side in degree
`n + (m + r)`, so the two are compared through `Stacks.Chow.chowGroupDegreeEquiv`, which is the
identity on cycle coefficients.

On classes of cycles it is `Stacks.Chow.flatPullback_exteriorProduct_sndMap`, read modulo
rational equivalence. The three instances of Stacks 02S1 it needs are the two that make the
exterior product on Chow groups exist in each of the two products, and the one that makes flat
pullback along `h` and along `1_X × h` descend. -/
theorem flatPullbackChow_chowExteriorProduct_tmul (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y Y' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (g' : Y' ⟶ C.S) [LocallyOfFiniteType g'] (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] [Flat h] (hh : h ≫ g = g') (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (n m : ℤ) (nn mm : ℕ)
    (hXclosure : ∀ x : X, relativeDimension C.dimensionFunction f x = n →
      (nn : ℤ) = n ∧ AlgebraicGeometry.RelativeDimension
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ f) nn)
    (hYclosure : ∀ y : Y, relativeDimension C.dimensionFunction g y = m →
      (mm : ℤ) = m ∧ AlgebraicGeometry.RelativeDimension
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).subschemeι ≫ g) mm)
    (_hright : FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C f g m)
    (_hleft : FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C g f n)
    (_hright' : FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C f g'
      (m + (r : ℤ)))
    (_hleft' : FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C g' f n)
    (hfach : FlatPullbackFactorsThroughRationalEquivalence C g' g h hh r hr m)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst f g' ≫ f)
      (pullback.fst f g ≫ f) (exteriorProductSndMap f g g' h hh)
      (exteriorProductSndMap_comp_structureMorphism f g g' h hh) r
      (relativeDimension_exteriorProductSndMap f g g' h hh r hr) (n + m))
    (a : chowGroup C f n) (c : chowGroup C g m) :
    chowGroupDegreeEquiv C (pullback.fst f g' ≫ f) (add_assoc n m (r : ℤ))
        (flatPullbackChow C (pullback.fst f g' ≫ f) (pullback.fst f g ≫ f)
          (exteriorProductSndMap f g g' h hh)
          (exteriorProductSndMap_comp_structureMorphism f g g' h hh) r
          (relativeDimension_exteriorProductSndMap f g g' h hh r hr) (n + m) hfac
          (chowExteriorProduct C hδ f g n m (TensorProduct.tmul ℤ a c))) =
      chowExteriorProduct C hδ f g' n (m + (r : ℤ))
        (TensorProduct.tmul ℤ a (flatPullbackChow C g' g h hh r hr m hfach c)) := by
  induction a using QuotientAddGroup.induction_on with
  | H α =>
    induction c using QuotientAddGroup.induction_on with
    | H γ =>
      rw [chowExteriorProduct_tmul_mk]
      exact chowGroupDegreeEquiv_mk_eq_mk_of_val C (pullback.fst f g' ≫ f)
        (add_assoc n m (r : ℤ)) _ _
        (flatPullback_exteriorProduct_sndMap C f g g' h hh r hr n m nn mm hXclosure
          hYclosure α γ)

/-! ### The field case, with no hypothesis on reduced point closures -/

/-- **Flat pullback commutes with the exterior product over a field, on Chow groups.** Let `k` be
a field, let `X`, `Y` and `Y'` be schemes locally of finite type over `k`, let `h : Y' ⟶ Y` be
flat over `k` of relative dimension `r`, and let `a ∈ CH_n(X)` and `c ∈ CH_m(Y)`. Then

  `(1_X × h)^*(a × c) = a × h^*c`

in `CH_{n + (m + r)}(X ×_k Y')`.

This is `Stacks.Chow.flatPullbackChow_chowExteriorProduct_tmul` with the two hypotheses on
reduced point closures discharged: over a field the reduced closure of a point of relative
dimension `d` is flat of constant fibre dimension `d` and `d` is non-negative, which is
`Stacks.Chow.pointClosure_relativeDimension`. Stacks 02S1 is assumed, in the
bundled form `Stacks.Chow.FlatPullbackDescends`; it is what makes the exterior product on Chow
groups and the two flat pullbacks exist at all, exactly as in
`Stacks.Chow.chowExteriorProduct_assoc`. -/
theorem flatPullbackChow_chowExteriorProduct_tmul_field (k : Type u) [Field k]
    (hfp : FlatPullbackDescends (fieldChowSituation k)) {X Y Y' : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (g' : Y' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g'] (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] [Flat h] (hh : h ≫ g = g') (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (n m : ℤ)
    (a : chowGroup (fieldChowSituation k) f n) (c : chowGroup (fieldChowSituation k) g m) :
    chowGroupDegreeEquiv (fieldChowSituation k) (pullback.fst f g' ≫ f)
        (add_assoc n m (r : ℤ))
        (flatPullbackChow (fieldChowSituation k) (pullback.fst f g' ≫ f)
          (pullback.fst f g ≫ f) (exteriorProductSndMap f g g' h hh)
          (exteriorProductSndMap_comp_structureMorphism f g g' h hh) r
          (relativeDimension_exteriorProductSndMap f g g' h hh r hr) (n + m)
          (hfp (pullback.fst f g' ≫ f) (pullback.fst f g ≫ f)
            (exteriorProductSndMap f g g' h hh)
            (exteriorProductSndMap_comp_structureMorphism f g g' h hh) r
            (relativeDimension_exteriorProductSndMap f g g' h hh r hr) (n + m))
          (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) f g n m
            (TensorProduct.tmul ℤ a c))) =
      chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) f g' n (m + (r : ℤ))
        (TensorProduct.tmul ℤ a
          (flatPullbackChow (fieldChowSituation k) g' g h hh r hr m (hfp g' g h hh r hr m) c)) :=
  flatPullbackChow_chowExteriorProduct_tmul (fieldChowSituation k) (fun _ _ ↦ rfl) f g g' h hh r
    hr n m n.toNat m.toNat
    (fun x hx ↦ pointClosure_relativeDimension k f x n hx)
    (fun y hy ↦ pointClosure_relativeDimension k g y m hy)
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds
      (fieldChowSituation k) f g m)
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds
      (fieldChowSituation k) g f n)
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds
      (fieldChowSituation k) f g' (m + (r : ℤ)))
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds
      (fieldChowSituation k) g' f n) _ _ a c

end Stacks.Chow

end
