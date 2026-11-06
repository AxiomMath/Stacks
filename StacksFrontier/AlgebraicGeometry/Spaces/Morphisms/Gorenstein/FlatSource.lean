module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.EtaleLocalRings
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphismOfFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.EtaleCharts

/-!
# Flat morphisms of algebraic spaces with Gorenstein source

A flat morphism `f : X ⟶ Y` of locally Noetherian algebraic spaces over a scheme `S` whose
source is a Gorenstein algebraic space is a Gorenstein morphism, and the étale local ring of
`Y` at the image of any geometric point of `X` is Gorenstein.

## Main results

* `AlgebraicGeometry.Space.isGorenstein_of_isGorenstein_source`: **Stacks 0E17**, the morphism
  is Gorenstein.
* `AlgebraicGeometry.Space.isGorensteinLocalRing_etaleLocalRing_target`: **Stacks 0E17**, the
  étale local rings of the target at image points are Gorenstein.

## Implementation notes

Both halves are read off a commuting square of étale scheme charts and reduced to the
corresponding statement for morphisms of schemes, Tag 0C12. This is the Gorenstein counterpart
of the Cohen–Macaulay case, Tag 0E0Y, and everything generic there is reused rather than
repeated: the chart of the base change over a chart of the target
(`AlgebraicGeometry.Space.exists_surjective_etale_atlas_over_chart`), the comparison of the
fibre over a chart point with the scheme-theoretic fibre of the chart square
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_fiberAt_iff`), the pointed chart square with
affine target chart (`AlgebraicGeometry.Space.exists_compatible_affine_chart_square`), and the
Noetherian and local-ring structures on the étale local rings.

For the morphism this is the chart criterion of Tag 0E15: over an étale scheme chart
`g : h_V ⟶ Y` of the target there is a surjective étale scheme chart `a` of the base change,
presented by a morphism `h : U ⟶ V` of the site, and the fibre conditions on `f` over the
residue-field points of `V` are the corresponding conditions on the scheme-theoretic fibres of
`h`. The source chart `a ≫ pullback.fst f g` of `X` is étale, so `U` is a locally Noetherian
Gorenstein scheme, and `h` is flat because `f` is; hence the fibres of `h` are Gorenstein
schemes by Tag 0C12 together with Tag 0C05.

For the target local ring the square is a *pointed* one, with affine target chart. The étale
local rings are the strict henselizations of the ordinary local rings of the two chart schemes
at the selected points (Tag 04KF), the local ring of the target chart at the selected point is
Gorenstein by the base half of Tag 0C12, and Gorensteinness passes to a strict henselization
because the structure map is flat and local with closed fibre the residue field of the strict
henselization, which is regular, hence Gorenstein: Tag 0BJL then applies.

The locally Noetherian hypotheses are the étale-local property of Tag 03E6 for local
Noetherianity of schemes, which is weaker than Noetherianity of the algebraic space, so the
Noetherian structure on the étale local rings comes from
`AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian` rather than
from Tag 08AH.

## References

* [Stacks Project, Tag 0E17](https://stacks.math.columbia.edu/tag/0E17)
* [Stacks Project, Tag 0C12](https://stacks.math.columbia.edu/tag/0C12)
* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
* [Stacks Project, Tag 0E15](https://stacks.math.columbia.edu/tag/0E15)
* [Stacks Project, Tag 0E0Y](https://stacks.math.columbia.edu/tag/0E0Y)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-! ### Gorensteinness of the two Gorenstein-scheme classes -/

/-- Gorensteinness of a Noetherian local ring passes to the strict henselization in a
henselization tower: the structure map is flat and local, and its closed fibre is the residue
field of the strict henselization, which is regular and hence Gorenstein, so the criterion of
Tag 0BJL identifies Gorensteinness of the strict henselization with Gorensteinness of the
ring. -/
private theorem isGorensteinLocalRing_strictHenselization {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {K : Type u} [Field K]
    [Algebra (ResidueField R) K] [IsSepClosure (ResidueField R) K] (T : HenselizationTower R K)
    (hT : IsNoetherianRing T.strictHenselization)
    (hR : Dualizing.IsGorensteinLocalRing R) :
    Dualizing.IsGorensteinLocalRing T.strictHenselization := by
  have : IsLocalHom (algebraMap R T.strictHenselization) :=
    IsHenselization.isLocalHom (L := K)
  have : Module.Flat R T.strictHenselization :=
    IsHenselization.flat (R := R) (L := K) (Rh := T.strictHenselization)
  have hI : (maximalIdeal R).map (algebraMap R T.strictHenselization) =
      maximalIdeal T.strictHenselization :=
    IsHenselization.map_maximalIdeal (R := R) (L := K) (Rh := T.strictHenselization)
  set I : Ideal T.strictHenselization :=
    (maximalIdeal R).map (algebraMap R T.strictHenselization)
  have : Nontrivial (T.strictHenselization ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R T.strictHenselization)).ne
  have hNq : IsNoetherianRing (T.strictHenselization ⧸ I) := inferInstance
  have hLq : IsLocalRing (T.strictHenselization ⧸ I) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hGq : @Dualizing.IsGorensteinLocalRing (T.strictHenselization ⧸ I) _ hNq hLq := by
    have e : (T.strictHenselization ⧸ I) ≃+* ResidueField T.strictHenselization :=
      Ideal.quotEquivOfEq hI
    exact Dualizing.isGorensteinLocalRing_of_ringEquiv e
      (Dualizing.IsRegularLocalRing.isGorensteinLocalRing _)
  have hcrit' : Dualizing.IsGorensteinLocalRing T.strictHenselization ↔
      (Dualizing.IsGorensteinLocalRing R ∧
        @Dualizing.IsGorensteinLocalRing (T.strictHenselization ⧸ I) _ hNq hLq) := by
    simpa [I] using Dualizing.isGorensteinLocalRing_iff_of_flat R T.strictHenselization
  exact hcrit'.mpr ⟨hR, hGq⟩

/-! ### The scheme-level input -/

/-- A flat morphism of locally Noetherian schemes with Gorenstein source has Gorenstein
fibres: it is a Gorenstein morphism by Tag 0C12, and the fibres of a Gorenstein morphism are
Gorenstein schemes by Tag 0C05. -/
private theorem isGorenstein_fiber_of_flat_of_isGorenstein_source {Z W : Scheme.{u}} (q : Z ⟶ W)
    (hZ : _root_.AlgebraicGeometry.IsGorenstein Z) [IsLocallyNoetherian W] [Flat q] (w : W) :
    _root_.AlgebraicGeometry.IsGorenstein (q.fiber w) := by
  obtain ⟨hfib, hmor⟩ := Stacks.Duality.isGorenstein_of_flat q
  exact Scheme.Hom.isGorenstein_fiber_of_isGorenstein q hfib hmor w

/-- The base half of Tag 0C12 for the local ring of the target at a prescribed image point. -/
private theorem isGorensteinLocalRing_stalk_of_map_eq {Z W : Scheme.{u}} (q : Z ⟶ W)
    [IsLocallyNoetherian W] [Flat q] (hZ : _root_.AlgebraicGeometry.IsGorenstein Z) (z : Z)
    (w : W) (hzw : q z = w) :
    Dualizing.IsGorensteinLocalRing (W.presheaf.stalk w) := by
  subst hzw
  exact Stacks.Duality.isGorensteinLocalRing_stalk_of_flat q z

/-! ### The morphism -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_GorensteinFlatSource :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_GorensteinFlatSource
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_GorensteinFlatSource B S hS).has_limit _

/-- An étale-local property of an algebraic space holds on every étale scheme chart. -/
private theorem property_of_etale_chart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {P : ObjectProperty Scheme.{u}} [P.IsLocal Scheme.etalePrecoverage]
    (hF : IsAlgebraicSpace B S hS F) (hP : HasEtaleLocalProperty B S hS F P)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ F)
    (hg : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) g) :
    P ((BigFppfOver.toScheme B S hS).obj V) :=
  (exists_atlas_iff_forall_etale B S hS F P hF).mp hP V g hg

/-- **Stacks 0E17.** A flat morphism of locally Noetherian algebraic spaces over `S` whose
source is a Gorenstein algebraic space is a Gorenstein morphism. -/
@[stacks 0E17 "the morphism is Gorenstein"]
theorem isGorenstein_of_isGorenstein_source (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hG : HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T))
    (f : X ⟶ Y) (hf : IsFlat B S hS f) :
    IsGorenstein B S hS f := by
  have key := (isGorenstein_tfae_etaleCharts B S hS hX hY f
    (hasLocallyNoetherianFibers_of_source B S hS hX hY f hNX)).out 3 1
  refine key.mp ⟨hf, ?_⟩
  intro V g hg v hv
  obtain ⟨U, a, h, comm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_atlas_over_chart B S hS hX hY f V g
  have hgEtale := (isEtale_iff_presheaf_of_yoneda B S hS g).mp hg
  have hpEtale := chartSource_property B S hS (@Etale.{u})
    Etale.etale_isStableUnderBaseChange.{u} etale_isStableUnderComposition.{u} f V g hgEtale
    U a haEtale
  have hVnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    property_of_etale_chart B S hS hY hNY V g hgEtale
  have hUgor : _root_.AlgebraicGeometry.IsGorenstein
      ((BigFppfOver.toScheme B S hS).obj U) :=
    property_of_etale_chart B S hS hX hG U (a ≫ pullback.fst f g) hpEtale
  have hpcomm : (a ≫ pullback.fst f g) ≫ f = yoneda.map h ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, comm]
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map h) :=
    hf U V (a ≫ pullback.fst f g) g h hpEtale hgEtale hpcomm.symm
  exact (hasEtaleLocalProperty_fiberAt_iff B S hS hX hY f V g U a h comm haSurjective haEtale
    (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T) v hv).mpr
    (isGorenstein_fiber_of_flat_of_isGorenstein_source
      ((BigFppfOver.toScheme B S hS).map h) hUgor v)

/-! ### The target local rings -/

/-- **Stacks 0E17.** For a flat morphism of locally Noetherian algebraic spaces over `S` whose
source is a Gorenstein algebraic space, the étale local ring of the target at the image of any
geometric point of the source is Gorenstein. -/
@[stacks 0E17 "the target étale local rings are Gorenstein"]
theorem isGorensteinLocalRing_etaleLocalRing_target (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hG : HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T))
    (f : X ⟶ Y) (hf : IsFlat B S hS f) (x : GeometricPoint B S hS X) :
    letI : IsLocalRing (etaleLocalRing B S hS Y (geometricPointMap f x)) :=
      isLocalRing_etaleLocalRing B S hS Y hY (geometricPointMap f x)
    letI : IsNoetherianRing (etaleLocalRing B S hS Y (geometricPointMap f x)) :=
      isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Y hY hNY
        (geometricPointMap f x)
    Dualizing.IsGorensteinLocalRing (etaleLocalRing B S hS Y (geometricPointMap f x)) := by
  have : IsLocalRing (etaleLocalRing B S hS Y (geometricPointMap f x)) :=
    isLocalRing_etaleLocalRing B S hS Y hY (geometricPointMap f x)
  have : IsNoetherianRing (etaleLocalRing B S hS Y (geometricPointMap f x)) :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Y hY hNY
      (geometricPointMap f x)
  obtain ⟨U, V, g, hcomm, hpoint, -⟩ :=
    exists_compatible_affine_chart_square B S hS hX hY f x
  have hUgor : _root_.AlgebraicGeometry.IsGorenstein (chartScheme U.chart) :=
    property_of_etale_chart B S hS hX hG _ U.chart.obj.hom U.chart.property
  have hUnoeth : IsLocallyNoetherian (chartScheme U.chart) :=
    property_of_etale_chart B S hS hX hNX _ U.chart.obj.hom U.chart.property
  have hVnoeth : IsLocallyNoetherian (chartScheme V.chart) :=
    property_of_etale_chart B S hS hY hNY _ V.chart.obj.hom V.chart.property
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V.chart.obj.left) := hVnoeth
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map g) :=
    hf U.chart.obj.left V.chart.obj.left U.chart.obj.hom V.chart.obj.hom g
      U.chart.property V.chart.property hcomm.symm
  have huv : ((BigFppfOver.toScheme B S hS).map g)
        ((chartGeometricPoint U).hom (closedPoint (chartGeometricPoint U).residueField)) =
      (chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField) :=
    congrArg (fun k ↦ ((BigFppfOver.toScheme B S hS).map k)
      (show (BigFppfOver.toScheme B S hS).obj x.val.siteObject from
        closedPoint x.val.carrier)) hpoint
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  have hRgor : Dualizing.IsGorensteinLocalRing R :=
    isGorensteinLocalRing_stalk_of_map_eq ((BigFppfOver.toScheme B S hS).map g) hUgor _ _ huv
  let T := henselizationTower R
    (separableClosure (ResidueField R) (chartGeometricPoint V).residueField)
  have hT : IsNoetherianRing T.strictHenselization :=
    (isNoetherianRing_iff_henselizations R T.henselization T.strictHenselization
      (separableClosure (ResidueField R) (chartGeometricPoint V).residueField)).2.mp inferInstance
  exact Dualizing.isGorensteinLocalRing_of_ringEquiv
    (strictHenselizationEquivEtaleLocalRing hY V (bigEtaleSiteOfFppfSite B)
      V.chart.obj.left.left.property T).symm
    (isGorensteinLocalRing_strictHenselization T hT hRgor)

end AlgebraicGeometry.Space

end
