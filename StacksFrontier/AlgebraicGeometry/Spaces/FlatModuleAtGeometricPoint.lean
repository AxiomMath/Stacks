module

public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.FlatHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing

/-!
# Flatness of a module over the target at a point of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `F`
be an `𝒪_X`-module and let `x` be a point of `X`.  Stacks 05VU states two equivalent conditions
on that data:

1. for some commuting square of étale scheme charts `U ⟶ V` over `f` and some point `u` of `U`
   above `x`, the restriction of `F` to `U` is flat over `V` at `u`;
2. the geometric stalk `F_{x̄}` is flat over the étale local ring `𝒪_{Y, ȳ}`, where `x̄` is any
   geometric point above `x` and `ȳ = f ∘ x̄`.

This file states both conditions against the library's objects and proves the last step of the
source's proof — the passage from the local ring of a chart of `Y` to the étale local ring of
`Y`.  The equivalence itself is
`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAtGeometricPointEquiv.lean`, which is where
`@[stacks 05VU]` sits.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatOverAtOnChartDiagram`: condition (1) of Stacks 05VU at one
  point of one commuting square of étale scheme charts.
* `AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`: condition (2) of Stacks 05VU, flatness
  of the geometric stalk of `F` over the étale local ring of `Y` at the image geometric point.

## Main results

* `AlgebraicGeometry.Space.isFlatOverOnChartDiagram_iff_forall_isFlatOverAtOnChartDiagram` and
  `AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtOnChartDiagram`: the pointwise
  chart condition assembles to the chartwise flatness of `AlgebraicGeometry.Space.IsFlatOver`,
  which is the definition of Stacks 05VV.
* `AlgebraicGeometry.Space.etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ`: the
  commuting square of local rings drawn in the proof of Stacks 05VU, read on germs of regular
  functions on the target chart.  Going round it either way sends the germ at `v` of a regular
  function on the chart of `Y` to the germ at `x̄` of its pullback to the chart of `X`.
* `AlgebraicGeometry.Space.flat_chartLocalRing_geometricModuleStalk_iff`: flatness of the
  geometric stalk `F_{x̄}` over the ordinary local ring `𝒪_{V, v}` of a scheme chart of `Y`
  carrying `ȳ` is flatness of `F_{x̄}` over the étale local ring `𝒪_{Y, ȳ}`.  This is the final
  step of the proof of Stacks 05VU: the étale local ring of `Y` at `ȳ` is the strict
  henselization of `𝒪_{V, v}` (Stacks 04KF) and flatness over a local ring and over any of its
  henselizations agree (Stacks 05VL).

## Implementation notes

The source deduces the equivalence from the base-change formula
`F_{x̄} = (a^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of Stacks 05VP, applied to the faithfully flat map
`𝒪_{U, u} → 𝒪_{X, x̄}` through Stacks 0584 (2): that formula is what turns flatness of the
ordinary stalk `(a^* F)_u` over `𝒪_{V, v}` into flatness of the geometric stalk `F_{x̄}` over
`𝒪_{V, v}`, after which the result below finishes the proof.  All three of those inputs are now
available — `AlgebraicGeometry.Space.isIso_chartStalkTensorComparison` is Stacks 05VP,
`AlgebraicGeometry.Space.faithfullyFlat_chartLocalRingToEtaleLocalRing` the faithful flatness,
and `Module.Flat.tensorProduct_iff_of_faithfullyFlat` Stacks 0584 (2).

The difference of shape between condition (1) and Stacks 05VP is resolved in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartZariskiStalkOrdinary.lean`: condition (1) is the
ringed-space predicate `AlgebraicGeometry.IsFlatOverAt`, whose module is
`TopCat.Presheaf.stalk` of the underlying presheaf of abelian groups, whereas Stacks 05VP is
stated for `AlgebraicGeometry.Space.chartZariskiModuleStalk`, the stalk at the point of the
Zariski *site*; `AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv` identifies the two
with their scalars, and
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk` reads
condition (1), at the point under a chosen lift of a geometric point, as flatness of the
Zariski stalk over the local ring of the target chart.

The equivalence itself is
`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAtGeometricPointEquiv.lean`, which carries
`@[stacks 05VU]`; neither of the two conditions below is on its own a claim, and their
equivalence is what the tag asserts.  The remaining input it needs beyond the result below is
the commuting square of local rings as an identity of ring homomorphisms rather than only on
germs of global sections:
`AlgebraicGeometry.Space.etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartLocalRingSquare.lean` proves it, by checking both
composites on the germ of a function on a Zariski open of the chart of `Y` after refining the
square by that open and its preimage.

Condition (1) is phrased on `AlgebraicGeometry.Space.ChartDiagram`, the commuting square of
étale scheme charts with an arbitrary vertical morphism of schemes already used by
`AlgebraicGeometry.Space.IsFlatOverOnChartDiagram`, and the flatness of the restriction at one
point is the ringed-space predicate `AlgebraicGeometry.IsFlatOverAt` of Stacks 08KT.  The
source quantifies existentially over the square and over the point above `x`; that existential
is formed where the equivalence is, since the pointwise predicate is the form from which both
the existential of Stacks 05VU and the universal quantification of Stacks 05VV are built.  As
in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModule.lean`, the module universe of condition (1)
is the universe of the structure rings, since that is where
`AlgebraicGeometry.Space.restrictToChart` lands in the modules of a scheme.  Condition (2)
carries an independent module universe.

The scalars of condition (2) are restricted along the canonical homomorphism of étale local
rings `𝒪_{Y, ȳ} → 𝒪_{X, x̄}` of Stacks 04NG, which is
`AlgebraicGeometry.Space.etaleLocalRingMap`; the geometric stalk itself is the module over
`𝒪_{X, x̄}` of Stacks 05VQ.  In the result below the scalars are restricted one step further,
along the canonical map `𝒪_{V, v} → 𝒪_{Y, ȳ}` of Stacks 05VP, so that the two flatness
conditions compared are conditions on one fixed additive group, as in
`flat_tfae_henselization`.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VL](https://stacks.math.columbia.edu/tag/05VL)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u m

/-- Flatness of a module over a ring is unchanged by transporting the ring along a ring
isomorphism: the isomorphism exhibits the target as the localization of the source at the
trivial submonoid. -/
private theorem flat_compHom_ringEquiv_iff
    {R T M : Type*} [CommRing R] [CommRing T] [AddCommGroup M] [Module T M]
    (e : R ≃+* T) :
    letI : Module R M := Module.compHom M e.toRingHom
    (Module.Flat R M ↔ Module.Flat T M) := by
  let : Algebra R T := e.toRingHom.toAlgebra
  let : Module R M := Module.compHom M e.toRingHom
  let : IsScalarTower R T M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalization (⊥ : Submonoid R) T :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rintro x ⟨r, hr, rfl⟩
      have hr' : r = 1 := hr
      simp [hr']) e.bijective
  exact (Module.flat_iff_of_isLocalization T (⊥ : Submonoid R) M).symm

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (1) of Stacks 05VU: flatness at a point of a chart diagram -/

/-- **Condition (1) of Stacks 05VU at one point.** Flatness of a module on an algebraic space
over the target at one point of the source chart of one commuting square of étale scheme
charts: the restriction of `F` to that chart is flat over the target chart at the point,
relative to the vertical morphism of schemes of the square. -/
noncomputable abbrev IsFlatOverAtOnChartDiagram {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f)
    (u : chartScheme d.U) : Prop :=
  AlgebraicGeometry.IsFlatOverAt
    (LocallyRingedSpace.forgetToSheafedSpace.map
      ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom)
    (restrictToChart B S hS hX F d.U) u

/-- Flatness of the restriction of `F` to the source chart of a commuting square of étale
scheme charts, over the target chart, is flatness at every point of that chart. -/
theorem isFlatOverOnChartDiagram_iff_forall_isFlatOverAtOnChartDiagram
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f) :
    IsFlatOverOnChartDiagram B S hS hX F d ↔
      ∀ u : chartScheme d.U, IsFlatOverAtOnChartDiagram B S hS hX F d u :=
  Iff.rfl

/-- **Stacks 05VV through condition (1) of Stacks 05VU.** An `𝒪_X`-module is flat over `Y` when
condition (1) of Stacks 05VU holds at every point of every commuting square of étale scheme
charts of `f`. -/
theorem isFlatOver_iff_forall_isFlatOverAtOnChartDiagram
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) :
    IsFlatOver B S hS hX f F ↔
      ∀ (d : ChartDiagram B S hS X Y f) (u : chartScheme d.U),
        IsFlatOverAtOnChartDiagram B S hS hX F d u :=
  Iff.rfl

/-! ### Condition (2) of Stacks 05VU: flatness of the geometric stalk -/

/-- **Condition (2) of Stacks 05VU.** Flatness of the geometric stalk `F_{x̄}` of an
`𝒪_X`-module at a geometric point `x̄` of `X` over the étale local ring `𝒪_{Y, ȳ}` of the target
at the image geometric point `ȳ = f ∘ x̄`, the scalars being restricted along the canonical
homomorphism of étale local rings of Stacks 04NG. -/
noncomputable def IsFlatOverAtGeometricPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1) : Prop :=
  letI : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  Module.Flat (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
    (geometricModuleStalk B S hS X xbar F)

/-- **A module whose geometric stalk vanishes at a point is flat over the target there.**
Condition (2) of Stacks 05VU is flatness of `F_{x̄}` as a module over an étale local ring, and a
module with at most one element is flat, being a retract of the ring.

This is what makes the points outside the support of a module cost nothing when relative
flatness is assembled point by point: at such a point the condition holds for every target and
every morphism, with no hypothesis on `F` at all.

The flatness of a subsingleton module is inlined as `Module.Flat.of_retract` at the zero maps
rather than cited: the general statement is `Module.Flat.of_subsingleton'`, which this
development has, but only inside
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeNilpotentSmooth.lean` — a
crystalline-site file that none of the flatness-of-spaces files imports, and whose import
here would be a large one for a two-line fact. -/
theorem isFlatOverAtGeometricPoint_of_subsingleton_geometricModuleStalk
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, m} B S hS X.1 X.2)
    (xbar : GeometricPoint B S hS X.1)
    (h : Subsingleton (geometricModuleStalk B S hS X xbar F)) :
    IsFlatOverAtGeometricPoint B S hS f F xbar := by
  let : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  have := h
  exact Module.Flat.of_retract
    (M := etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
    0 0 (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)

/-! ### The commuting square of local rings -/

/-- **The commuting square of local rings of Stacks 05VU, on germs.** In a commuting square of
pointed étale scheme charts over `f : X ⟶ Y`, the two composites
`𝒪_{V, v} → 𝒪_{Y, ȳ} → 𝒪_{X, x̄}` and `𝒪_{V, v} → 𝒪_{U, u} → 𝒪_{X, x̄}` agree on the germ at `v`
of a regular function on the chart of `Y`: both send it to the germ at `x̄` of its pullback to
the chart of `X`.  The vertical maps are those of Stacks 05VP and the horizontal one of
Stacks 04NG.

Agreement on germs of global sections is what determines the square when the chart of `Y` is
affine, since then the germs of its global sections generate `𝒪_{V, v}`. -/
theorem etaleLocalRingMap_chartLocalRingToEtaleLocalRing_germ {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (xbar : GeometricPoint B S hS X.1) (U : SmallEtaleNeighborhood xbar)
    (V : SmallEtaleNeighborhood (geometricPointMap f.hom xbar))
    (g : U.chart.obj.left ⟶ V.chart.obj.left)
    (hcomm : U.chart.obj.hom ≫ f.hom = yoneda.map g ≫ V.chart.obj.hom)
    (hpoint : U.point ≫ g = V.point) (a : Γ(chartScheme V.chart, ⊤)) :
    etaleLocalRingMap X.2 f.hom xbar
        (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2 V
          ((chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS Y.1 V) trivial a)) =
      chartLocalRingToEtaleLocalRing B S hS X.1 X.2 U
        ((chartScheme U.chart).presheaf.germ ⊤ (chartPoint B S hS X.1 U) trivial
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom a)) := by
  calc etaleLocalRingMap X.2 f.hom xbar
        (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2 V
          ((chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS Y.1 V) trivial a))
      = etaleLocalRingMap X.2 f.hom xbar
          (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom xbar) (Opposite.op V) a) :=
        congrArg _ (chartLocalRingToEtaleLocalRing_germ B S hS Y.1 Y.2 V a)
    _ = etaleLocalRingGerm B S hS X.1 xbar (Opposite.op U)
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom a) :=
        (congrArg (fun k => k a)
          (etaleLocalRingMap_isEtaleLocalRingMap X.2 f.hom xbar U V g hcomm hpoint)).symm
    _ = _ := (chartLocalRingToEtaleLocalRing_germ B S hS X.1 X.2 U _).symm

/-! ### The final step of the proof of Stacks 05VU -/

/-- **The last step of the proof of Stacks 05VU.** The geometric stalk `F_{x̄}` is flat over the
ordinary local ring `𝒪_{V, v}` of a scheme chart of `Y` carrying the image geometric point
`ȳ = f ∘ x̄` exactly when it is flat over the étale local ring `𝒪_{Y, ȳ}`, that is exactly when
condition (2) of Stacks 05VU holds.

The étale local ring `𝒪_{Y, ȳ}` is the strict henselization of `𝒪_{V, v}` by Stacks 04KF, and
flatness of a module over a local ring agrees with flatness over any of its henselizations by
Stacks 05VL. -/
theorem flat_chartLocalRing_geometricModuleStalk_iff {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1)
    (V : SmallEtaleNeighborhood (geometricPointMap f.hom xbar)) :
    letI : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
        (geometricModuleStalk B S hS X xbar F) :=
      Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
    letI : Module (chartLocalRing B S hS Y.1 V) (geometricModuleStalk B S hS X xbar F) :=
      Module.compHom _ ((etaleLocalRingMap X.2 f.hom xbar).comp
        (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2 V))
    (Module.Flat (chartLocalRing B S hS Y.1 V) (geometricModuleStalk B S hS X xbar F) ↔
      IsFlatOverAtGeometricPoint B S hS f F xbar) := by
  let T := chartHenselizationTower B S hS Y.1 V
  let e := chartStrictHenselizationEquiv B S hS Y.1 Y.2 V
  let N := geometricModuleStalk B S hS X xbar F
  let : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar)) N :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  let : Module T.strictHenselization N := Module.compHom _ e.toRingHom
  let : Module T.henselization N :=
    Module.compHom _ (algebraMap T.henselization T.strictHenselization)
  let : Module (chartLocalRing B S hS Y.1 V) N :=
    Module.compHom _ (algebraMap _ T.strictHenselization)
  have h1 : List.TFAE [Module.Flat (chartLocalRing B S hS Y.1 V) N,
      Module.Flat T.henselization N, Module.Flat T.strictHenselization N] :=
    flat_tfae_henselization (R := (chartLocalRing B S hS Y.1 V))
      (Rh := T.henselization) (Rsh := T.strictHenselization)
      (K := separableClosure (ResidueField (chartLocalRing B S hS Y.1 V))
        (chartGeometricPoint V).residueField) (Msh := N)
  have h2 := flat_compHom_ringEquiv_iff (M := N) e
  exact (h1.out 1 3).trans h2

end AlgebraicGeometry.Space

end
