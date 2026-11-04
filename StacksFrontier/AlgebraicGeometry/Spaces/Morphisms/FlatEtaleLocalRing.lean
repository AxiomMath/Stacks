module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.FlatHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra

/-!
# Flatness at a point and the étale local rings

Let `f : F ⟶ G` be a morphism of algebraic spaces over a scheme `S` and let `x` be a
geometric point of `F`, with image geometric point `f ∘ x` of `G`. There is a unique
homomorphism of étale local rings

`𝒪_{G, f ∘ x} ⟶ 𝒪_{F, x}`

compatible with the germ maps in every commuting diagram of pointed étale scheme charts, and
`f` is flat at the image point of `x` exactly when that homomorphism is flat.

## Main definitions

* `AlgebraicGeometry.Space.etaleLocalRingMap` is the canonical homomorphism of étale local
  rings induced by a morphism of algebraic spaces at a geometric point.

## Main results

* `AlgebraicGeometry.Space.existsUnique_etaleLocalRingMap`: **Stacks 04NG**, the canonical
  homomorphism exists and is uniquely determined by its action on germs of chart sections.
* `AlgebraicGeometry.Space.isFlatAt_iff_etaleLocalRingMap_flat`: **Stacks 04NG**, flatness of
  `f` at the image of `x` is flatness of that homomorphism.
* `AlgebraicGeometry.MorphismOfGerms.isFlat_ofSchemeHom_iff`: flatness of the germ morphism of
  a morphism of schemes at a point of its source is flatness of its map on local rings.
* `AlgebraicGeometry.Space.exists_affine_smallEtaleNeighborhood`: every small étale
  neighbourhood of a geometric point is refined by one whose chart is affine.

## Implementation notes

The characterisation of the canonical homomorphism by germs is
`AlgebraicGeometry.Space.IsEtaleLocalRingMap`. Its existence is the construction of a cocone
on the diagram computing `𝒪_{G, f ∘ x}`: a small étale neighbourhood `V` of the image point is
pulled back along the chart of one fixed small étale neighbourhood of `x`, which produces a
neighbourhood of `x` mapping to `V` over `f`, and the germ map of that neighbourhood composed
with pullback of sections is the component of the cocone at `V`. Independence of the choice of
pullback — hence the cocone condition and the uniqueness — comes from comparing any two such
diagrams inside a third one, which is again a pullback of charts.

For the flatness statement the two étale local rings are read off a *single* commuting square
of pointed étale charts, by Stacks 04KF: they are the strict henselizations of the ordinary
local rings of the two chart schemes at the selected points. The chart of the target is taken
affine, which is what makes the germs of its global sections generate the local ring of the
target chart, so that the comparison of the two vertical maps in that square is determined by
what the canonical homomorphism does to germs. Flatness over a strict henselization is then
flatness over the original local ring by Stacks 05VL, and the remaining horizontal
identification is `AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing`.

Flatness at a point of an algebraic space is a condition on every pointed étale chart
(Stacks 03ML, part (2)); it is read off the one chosen square with Stacks 04NC, since flatness
of a germ morphism is étale local on source and target (Stacks 04ND).

The statement is about the image point of the geometric point; for a point `x` of `F` with
`x̄.LiesOver x` the corresponding statement follows by rewriting along that equality.

## References

* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Germ flatness and flatness of a stalk map -/

/-- Flatness of the stalk map of a composite with an open immersion on the left is flatness of
the stalk map of the second factor: the stalk map of an open immersion is an isomorphism. -/
private theorem flat_stalkMap_comp_isOpenImmersion_iff {W X Y : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ Y) (w : W) :
    ((j ≫ f).stalkMap w).hom.Flat ↔ (f.stalkMap (j w)).hom.Flat := by
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.Flat.comp_iff_of_bijective_left
    (ConcreteCategory.bijective_of_isIso (j.stalkMap w))

/-- The germ morphism induced by a morphism of schemes at a point of its source is flat, in
the sense of [Stacks Project, Tag 04ND], exactly when the induced homomorphism of local rings
at that point is flat. -/
theorem MorphismOfGerms.isFlat_ofSchemeHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    MorphismOfGerms.IsFlat (MorphismOfGerms.ofSchemeHom f x) ↔ (f.stalkMap x).hom.Flat := by
  refine ⟨fun h => Space.flatAt_of_isFlat_germ f x h, fun h => ?_⟩
  refine ⟨⟨⊤, by simp, X.topIso.hom ≫ f, by change f x = f x; rfl⟩, rfl, ?_⟩
  exact (flat_stalkMap_comp_isOpenImmersion_iff X.topIso.hom f _).mpr h

/-! ### Flatness over a strict henselization -/

/-- Flatness of a composite `R → S → T` whose second factor is a flat local homomorphism of
local rings is flatness of its first factor: a flat local homomorphism of local rings is
faithfully flat, and flatness descends along a faithfully flat change of algebra. -/
@[ega "0 6.6.4" "special case", ega "IV 2.2.13" "(iii), special case"]
private theorem flat_comp_iff_of_flat_isLocalHom {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [IsLocalRing S] [IsLocalRing T] (f : R →+* S) (g : S →+* T) (hg : g.Flat)
    [IsLocalHom g] : (g.comp f).Flat ↔ f.Flat := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Flat S T := hg
  let : IsLocalHom (algebraMap S T) := ‹IsLocalHom g›
  let : Module.FaithfullyFlat S T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  change Module.Flat R T ↔ Module.Flat R S
  exact (Module.Flat.equiv_iff
      ((TensorProduct.AlgebraTensorModule.rid S T T).restrictScalars R)).symm.trans
    (Module.Flat.tensorProduct_iff_of_faithfullyFlat (R := R) (S := S) (S' := T) (M := S))

/-- Flatness of a module over a henselization with extended residue field, read over the
original local ring, is flatness over that henselization. This is Stacks 05VL, conditions (1)
and (3), stated for ring maps. -/
@[sga "4 VIII 4.1" "more general"]
private theorem flat_comp_isHenselization_iff {R Rh Rsh A : Type*} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rh]
    [Algebra Rh Rsh] [Algebra R Rsh] [IsScalarTower R Rh Rsh]
    [IsHenselization R (ResidueField R) Rh] {K : Type*} [Field K]
    [Algebra (ResidueField R) K] [IsHenselization R K Rsh] [CommRing A] (g : Rsh →+* A) :
    (g.comp (algebraMap R Rsh)).Flat ↔ g.Flat := by
  let : Module Rsh A := g.toAlgebra.toModule
  exact (flat_tfae_henselization (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) (Msh := A)).out 1 3

/-- A commuting square of local rings whose horizontal arrows are the structure maps to chosen
strict henselizations identifies flatness of its two vertical arrows. -/
private theorem flat_iff_of_henselizationTower_square {R A K L : Type*} [CommRing R]
    [IsLocalRing R] [CommRing A] [IsLocalRing A] [Field K] [Algebra (ResidueField R) K]
    [IsSepClosure (ResidueField R) K] [Field L] [Algebra (ResidueField A) L]
    [IsSepClosure (ResidueField A) L] (T : HenselizationTower R K) (U : HenselizationTower A L)
    (f : R →+* A) (g : T.strictHenselization →+* U.strictHenselization)
    (h : g.comp (algebraMap R T.strictHenselization) =
      (algebraMap A U.strictHenselization).comp f) : f.Flat ↔ g.Flat := by
  let : Module.Flat A U.strictHenselization :=
    Module.Flat.trans A U.henselization U.strictHenselization
  have : IsLocalHom (algebraMap A U.strictHenselization) := by
    rw [IsScalarTower.algebraMap_eq A U.henselization U.strictHenselization]
    exact RingHom.isLocalHom_comp _ _
  have hb := flat_comp_iff_of_flat_isLocalHom f (algebraMap A U.strictHenselization)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  rw [← h] at hb
  exact hb.symm.trans (flat_comp_isHenselization_iff (Rh := T.henselization) (K := K) g)

/-- Flatness of the stalk map of a morphism of schemes with affine target at a point, read
through chosen strict henselizations of the two local rings and chosen identifications of
those with two further rings: it is flatness of any homomorphism matching the germs of global
sections of the target. Affineness of the target is what makes the germs of its global
sections generate the local ring, so the matching condition pins the homomorphism down. -/
private theorem flat_stalkMap_iff_of_strictHenselization_germs {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) {K L : Type*} [Field K]
    [Algebra (ResidueField (Y.presheaf.stalk y)) K]
    [IsSepClosure (ResidueField (Y.presheaf.stalk y)) K] [Field L]
    [Algebra (ResidueField (X.presheaf.stalk x)) L]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) L]
    (T : HenselizationTower (Y.presheaf.stalk y) K)
    (U : HenselizationTower (X.presheaf.stalk x) L) {C D : Type*} [CommRing C] [CommRing D]
    (eY : T.strictHenselization ≃+* C) (eX : U.strictHenselization ≃+* D) (φ : C →+* D)
    (hc : ∀ a : Γ(Y, ⊤),
      φ (eY (algebraMap _ T.strictHenselization (Y.presheaf.germ ⊤ y trivial a))) =
        eX (algebraMap _ U.strictHenselization
          (X.presheaf.germ ⊤ x trivial ((Scheme.Γ.map f.op).hom a)))) :
    (f.stalkMap x).hom.Flat ↔ φ.Flat := by
  subst hxy
  let g := eX.symm.toRingHom.comp (φ.comp eY.toRingHom)
  have hs : g.comp (algebraMap _ T.strictHenselization) =
      (algebraMap _ U.strictHenselization).comp (f.stalkMap x).hom := by
    let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk (f x)) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨f x, trivial⟩ : (⊤ : Y.Opens))
    have := (isAffineOpen_top Y).isLocalization_stalk (⟨f x, trivial⟩ : (⊤ : Y.Opens))
    apply IsLocalization.ringHom_ext
      ((isAffineOpen_top Y).primeIdealOf ⟨f x, trivial⟩).asIdeal.primeCompl
    ext a
    change eX.symm (φ (eY (algebraMap _ T.strictHenselization
      (Y.presheaf.germ ⊤ (f x) trivial a)))) = _
    rw [hc, RingEquiv.symm_apply_apply]
    exact congrArg (algebraMap _ U.strictHenselization)
      (f.germ_stalkMap_apply ⊤ x trivial a).symm
  exact (flat_iff_of_henselizationTower_square T U (f.stalkMap x).hom g hs).trans
    ((RingHom.Flat.comp_iff_of_bijective_left eX.symm.bijective).trans
      (RingHom.Flat.comp_iff_of_bijective_right eY.bijective))

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Small étale neighbourhoods: existence and affine refinement -/

/-- A geometric point of an algebraic space has a small étale neighbourhood in the sense of
[Stacks Project, Tag 04JY]: a surjective étale scheme atlas is the chart of one. -/
theorem nonempty_smallEtaleNeighborhood (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) : Nonempty (SmallEtaleNeighborhood x) := by
  obtain ⟨U, p, hSurj, hEtale⟩ := hF.exists_atlas
  obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF x p hSurj hEtale
  exact ⟨V⟩

/-- Every small étale neighbourhood of a geometric point is refined by one whose chart scheme
is affine: the lift of the geometric point factors through an affine open of the chart, and an
open immersion is étale. This is what makes the comparison of
[Stacks Project, Tag 04KF] usable on germs of global chart sections. -/
theorem exists_affine_smallEtaleNeighborhood {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) :
    ∃ W : SmallEtaleNeighborhood x, IsAffine (chartScheme W.chart) := by
  obtain ⟨R, j, hj, q, hq⟩ :=
    exists_affine_point_refinement (chartGeometricPoint V) (chartGeometricPoint V).hom
  have := hj
  have hB : B.Contains (Spec R) :=
    Scheme.size_lt_of_isOpenImmersion j V.chart.obj.left.left.property
  exact ⟨(chartRefinement V hB j inferInstance q hq).left,
    inferInstanceAs (IsAffine (Spec R))⟩

/-! ### The canonical homomorphism of étale local rings -/

/-- A morphism of small étale neighbourhoods of a geometric point, from a morphism of their
charts carrying the chosen lift to the chosen lift. -/
def smallEtaleNeighborhoodHom {x : GeometricPoint B S hS F}
    {U V : SmallEtaleNeighborhood x} (g : U.chart.obj.left ⟶ V.chart.obj.left)
    (hc : yoneda.map g ≫ V.chart.obj.hom = U.chart.obj.hom)
    (hp : U.point ≫ g = V.point) : U ⟶ V :=
  ⟨ObjectProperty.homMk (CostructuredArrow.homMk g hc), hp⟩

/-- Germs in a small étale neighbourhood are germs in any neighbourhood it refines, after
pullback of sections. -/
private theorem etaleLocalRingGerm_comp_map {x : GeometricPoint B S hS F}
    {U V : SmallEtaleNeighborhood x} (m : U ⟶ V) :
    (etaleLocalRingGerm B S hS F x (Opposite.op U)).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map m.hom)).op).hom =
      etaleLocalRingGerm B S hS F x (Opposite.op V) := by
  have h := colimit.w (SmallEtaleNeighborhood.sections
    (liftedStructurePresheaf B S hS F)) m.op
  ext a
  exact congrArg (fun q => q.hom (ULift.up a)) h

/-- Pulling back chart sections along a composite is pulling back along the two factors. -/
private theorem toScheme_gammaMap_comp {X Y Z : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (a ≫ b)).op).hom =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map a).op).hom.comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map b).op).hom := by
  rw [Functor.map_comp, CategoryTheory.op_comp, Functor.map_comp, CommRingCat.hom_comp]

/-- Maps into the two legs of a cartesian square of representables, agreeing over the base,
factor through the corner. -/
private theorem exists_comp_eq_of_isPullback_yoneda {C : Type*} [Category C] {P X Y T : C}
    {Z : Cᵒᵖ ⥤ Type _} {a : P ⟶ X} {b : P ⟶ Y} {f : yoneda.obj X ⟶ Z} {g : yoneda.obj Y ⟶ Z}
    (sq : IsPullback (yoneda.map a) (yoneda.map b) f g) (u : T ⟶ X) (v : T ⟶ Y)
    (h : yoneda.map u ≫ f = yoneda.map v ≫ g) : ∃ e : T ⟶ P, e ≫ a = u ∧ e ≫ b = v :=
  ⟨yoneda.preimage (sq.lift _ _ h), yoneda.map_injective (by simp), yoneda.map_injective (by simp)⟩

/-- A lift of a small étale neighbourhood `V` of the image of a geometric point `x` through a
fixed small étale neighbourhood `N` of `x`: the base change of the chart of `V` along the
chart of `N`, read as a small étale neighbourhood of `x` with its two chart projections and
the induced lift of `x`. -/
private structure EtaleChartLift (f : F ⟶ G) {x : GeometricPoint B S hS F}
    (N : SmallEtaleNeighborhood x)
    (V : SmallEtaleNeighborhood (geometricPointMap f x)) where
  /-- The small étale neighbourhood of `x` carrying the lift. -/
  U : SmallEtaleNeighborhood x
  /-- The projection of charts to the fixed neighbourhood. -/
  toBase : U.chart.obj.left ⟶ N.chart.obj.left
  /-- The projection of charts to the neighbourhood of the image point. -/
  toImage : U.chart.obj.left ⟶ V.chart.obj.left
  /-- The chart is the chart of the fixed neighbourhood precomposed with the projection. -/
  chart_hom : U.chart.obj.hom = yoneda.map toBase ≫ N.chart.obj.hom
  /-- The square of charts is cartesian. -/
  isPullback : IsPullback (yoneda.map toImage) (yoneda.map toBase) V.chart.obj.hom
    (N.chart.obj.hom ≫ f)
  /-- The lift of `x` projects to the lift chosen in the fixed neighbourhood. -/
  point_comp_toBase : U.point ≫ toBase = N.point
  /-- The lift of `x` projects to the lift chosen in the neighbourhood of the image point. -/
  point_comp_toImage : U.point ≫ toImage = V.point

/-- A small étale neighbourhood of the image of a geometric point lifts through any small
étale neighbourhood of that point: the chart of the former is relatively representable and
étale, so its base change along the latter is again an étale chart, and the two lifts of the
point induce a lift to the base change. -/
private theorem nonempty_etaleChartLift (f : F ⟶ G) {x : GeometricPoint B S hS F}
    (N : SmallEtaleNeighborhood x)
    (V : SmallEtaleNeighborhood (geometricPointMap f x)) :
    Nonempty (EtaleChartLift f N V) := by
  set q : yoneda.obj N.chart.obj.left ⟶ G := N.chart.obj.hom ≫ f with hq
  set s : V.chart.property.rep.pullback q ⟶ N.chart.obj.left := V.chart.property.rep.snd q
    with hsdef
  have sq : IsPullback (V.chart.property.rep.fst q) (yoneda.map s) V.chart.obj.hom q :=
    V.chart.property.rep.isPullback q
  set g : V.chart.property.rep.pullback q ⟶ V.chart.obj.left :=
    yoneda.preimage (V.chart.property.rep.fst q) with hgdef
  have hg : yoneda.map g = V.chart.property.rep.fst q := yoneda.map_preimage _
  have hchart : IsEtaleChart B S hS F
      (CostructuredArrow.mk (yoneda.map s ≫ N.chart.obj.hom)) :=
    etale_comp_of_scheme B S hS s N.chart.obj.hom
      (V.chart.property.property_snd q) N.chart.property
  -- the chosen lift of `x` into the chart of `V`, through the identification of the two
  -- site objects of a geometric point and its image
  set pointV : x.val.siteObject ⟶ V.chart.obj.left := V.point with hpointV
  have hbase : yoneda.map pointV ≫ V.chart.obj.hom = yoneda.map N.point ≫ q := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    change V.chart.obj.hom.app (Opposite.op x.val.siteObject) V.point =
      f.app (Opposite.op x.val.siteObject)
        (N.chart.obj.hom.app (Opposite.op x.val.siteObject) N.point)
    rw [N.point_comp]
    exact V.point_comp
  have sq' : IsPullback (yoneda.map g) (yoneda.map s) V.chart.obj.hom q := hg ▸ sq
  obtain ⟨pointR, hrg, hrs⟩ :=
    exists_comp_eq_of_isPullback_yoneda sq' pointV N.point hbase
  have hpc : (yoneda.map s ≫ N.chart.obj.hom).app (Opposite.op x.val.siteObject) pointR =
      x.val.value := by
    have happ : (yoneda.map s ≫ N.chart.obj.hom).app (Opposite.op x.val.siteObject) pointR =
        N.chart.obj.hom.app (Opposite.op x.val.siteObject) (pointR ≫ s) := by
      simp
    rw [happ, hrs]
    exact N.point_comp
  exact ⟨{ U := { chart := ⟨CostructuredArrow.mk (yoneda.map s ≫ N.chart.obj.hom), hchart⟩
                  point := pointR
                  point_comp := hpc }
           toBase := s
           toImage := g
           chart_hom := rfl
           isPullback := sq'
           point_comp_toBase := hrs
           point_comp_toImage := hrg }⟩

/-- Any commuting diagram of pointed charts over `f` with source a small étale neighbourhood
of `x` factors through the chosen lift, by the universal property of the cartesian square. -/
private theorem EtaleChartLift.factor {f : F ⟶ G} {x : GeometricPoint B S hS F}
    {N : SmallEtaleNeighborhood x} {V : SmallEtaleNeighborhood (geometricPointMap f x)}
    (L : EtaleChartLift f N V) (Z : SmallEtaleNeighborhood x)
    (s : Z.chart.obj.left ⟶ N.chart.obj.left) (g : Z.chart.obj.left ⟶ V.chart.obj.left)
    (hs : yoneda.map s ≫ N.chart.obj.hom = Z.chart.obj.hom)
    (hg : yoneda.map g ≫ V.chart.obj.hom = Z.chart.obj.hom ≫ f)
    (hps : Z.point ≫ s = N.point) (hpg : Z.point ≫ g = V.point) :
    ∃ m : Z ⟶ L.U, (SmallEtale.toOver B S hS F).map m.hom ≫ L.toImage = g := by
  have hcomm : yoneda.map g ≫ V.chart.obj.hom =
      yoneda.map s ≫ (N.chart.obj.hom ≫ f) := by rw [← Category.assoc, hs, hg]
  obtain ⟨e, heg, hes⟩ := exists_comp_eq_of_isPullback_yoneda L.isPullback g s hcomm
  have hec : yoneda.map e ≫ L.U.chart.obj.hom = Z.chart.obj.hom := by
    rw [L.chart_hom, ← Category.assoc, ← Functor.map_comp, hes, hs]
  have hep : Z.point ≫ e = L.U.point := by
    apply yoneda.map_injective
    apply L.isPullback.hom_ext
    · rw [← Functor.map_comp, Category.assoc, heg, hpg, ← Functor.map_comp,
        L.point_comp_toImage]
    · rw [← Functor.map_comp, Category.assoc, hes, hps, ← Functor.map_comp,
        L.point_comp_toBase]
  exact ⟨smallEtaleNeighborhoodHom e hec hep, heg⟩

/-- The germ of a chart section computed through any compatible diagram of pointed charts over
`f` is the germ computed through the chosen lift: both diagrams are dominated by a third one,
obtained by base changing the chart of the fixed neighbourhood along the chart of the given
one. -/
private theorem EtaleChartLift.germ_eq {f : F ⟶ G} {x : GeometricPoint B S hS F}
    {N : SmallEtaleNeighborhood x} {V : SmallEtaleNeighborhood (geometricPointMap f x)}
    (L : EtaleChartLift f N V) (Z : SmallEtaleNeighborhood x)
    (g : Z.chart.obj.left ⟶ V.chart.obj.left)
    (hg : Z.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom)
    (hpg : Z.point ≫ g = V.point) :
    (etaleLocalRingGerm B S hS F x (Opposite.op Z)).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom =
      (etaleLocalRingGerm B S hS F x (Opposite.op L.U)).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map L.toImage).op).hom := by
  obtain ⟨Q⟩ := nonempty_etaleChartLift (𝟙 F) Z
    (show SmallEtaleNeighborhood (geometricPointMap (𝟙 F) x) from N)
  have hqz : yoneda.map Q.toBase ≫ Z.chart.obj.hom = Q.U.chart.obj.hom := Q.chart_hom.symm
  set m : Q.U ⟶ Z := smallEtaleNeighborhoodHom Q.toBase hqz Q.point_comp_toBase with hm
  have hqn : yoneda.map Q.toImage ≫ N.chart.obj.hom = Q.U.chart.obj.hom := by
    rw [Q.isPullback.w, Category.comp_id, hqz]
  have hqg : yoneda.map (Q.toBase ≫ g) ≫ V.chart.obj.hom = Q.U.chart.obj.hom ≫ f := by
    rw [Functor.map_comp, Category.assoc, ← hg, ← Category.assoc, hqz]
  obtain ⟨n, hn⟩ := L.factor Q.U Q.toImage (Q.toBase ≫ g) hqn hqg Q.point_comp_toImage
    (by rw [← Category.assoc, Q.point_comp_toBase]; exact hpg)
  rw [← etaleLocalRingGerm_comp_map m, ← etaleLocalRingGerm_comp_map n]
  have he : (SmallEtale.toOver B S hS F).map m.hom ≫ g =
      (SmallEtale.toOver B S hS F).map n.hom ≫ L.toImage := hn.symm
  have he' := congrArg
    (fun k => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom) he
  simp only [toScheme_gammaMap_comp] at he'
  exact congrArg
    (fun k => (etaleLocalRingGerm B S hS F x (Opposite.op Q.U)).comp k) he'

/-- Every small étale neighbourhood of the image of a geometric point is the target of a
compatible diagram of pointed charts over `f`. -/
private theorem exists_compatible_chart_lift (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    {x : GeometricPoint B S hS F} (V : SmallEtaleNeighborhood (geometricPointMap f x)) :
    ∃ (U : SmallEtaleNeighborhood x) (g : U.chart.obj.left ⟶ V.chart.obj.left),
      U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom ∧ U.point ≫ g = V.point := by
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood hF x
  obtain ⟨L⟩ := nonempty_etaleChartLift f N V
  refine ⟨L.U, L.toImage, ?_, L.point_comp_toImage⟩
  rw [L.isPullback.w, L.chart_hom, Category.assoc]

/-- **Stacks 04NG.** A morphism `f` of algebraic spaces over `S` induces at a geometric point
`x` of its source a unique homomorphism of étale local rings
`𝒪_{G, f ∘ x} ⟶ 𝒪_{F, x}` compatible with the germ maps in every commuting diagram of pointed
étale scheme charts over `f`. -/
@[stacks 04NG "the canonical homomorphism of étale local rings"]
theorem existsUnique_etaleLocalRingMap (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    (x : GeometricPoint B S hS F) :
    ∃! φ : etaleLocalRing B S hS G (geometricPointMap f x) →+* etaleLocalRing B S hS F x,
      IsEtaleLocalRingMap f x φ := by
  classical
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood hF x
  set L : ∀ V : SmallEtaleNeighborhood (geometricPointMap f x), EtaleChartLift f N V :=
    fun V => Classical.choice (nonempty_etaleChartLift f N V) with hL
  set D := SmallEtaleNeighborhood.sections (x := geometricPointMap f x)
    (liftedStructurePresheaf B S hS G) with hD
  set γ : ∀ V : SmallEtaleNeighborhood (geometricPointMap f x),
      (structurePresheaf B S hS G).obj (Opposite.op V.chart) →+* etaleLocalRing B S hS F x :=
    fun V => (etaleLocalRingGerm B S hS F x (Opposite.op (L V).U)).comp
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (L V).toImage).op).hom with hγ
  have hgerm : ∀ (V : SmallEtaleNeighborhood (geometricPointMap f x))
      (U : SmallEtaleNeighborhood x) (g : U.chart.obj.left ⟶ V.chart.obj.left),
      U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom → U.point ≫ g = V.point →
      (etaleLocalRingGerm B S hS F x (Opposite.op U)).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom = γ V :=
    fun V U g hc hp => (L V).germ_eq U g hc hp
  set c : Cocone D :=
    { pt := etaleLocalRing B S hS F x
      ι :=
        { app := fun V => CommRingCat.ofHom ((γ V.unop).comp ULift.ringEquiv.toRingHom)
          naturality := by
            intro V V' m
            set a := (SmallEtale.toOver B S hS G).map m.unop.hom with ha'
            have ha : yoneda.map a ≫ V.unop.chart.obj.hom = V'.unop.chart.obj.hom :=
              m.unop.hom.hom.w
            have hc : (L V'.unop).U.chart.obj.hom ≫ f =
                yoneda.map ((L V'.unop).toImage ≫ a) ≫ V.unop.chart.obj.hom := by
              rw [Functor.map_comp, Category.assoc, ha, (L V'.unop).isPullback.w,
                (L V'.unop).chart_hom, Category.assoc]
            have hp : (L V'.unop).U.point ≫ ((L V'.unop).toImage ≫ a) = V.unop.point := by
              rw [← Category.assoc, (L V'.unop).point_comp_toImage]
              exact m.unop.point_comp
            have h := hgerm V.unop (L V'.unop).U ((L V'.unop).toImage ≫ a) hc hp
            apply ConcreteCategory.hom_ext
            intro z
            have hz := congrArg (fun k => k (ULift.down z)) h
            change γ V'.unop
              ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map a).op).hom
                (ULift.down z)) = γ V.unop (ULift.down z)
            simp only [hγ, toScheme_gammaMap_comp] at hz
            exact hz } } with hcdef
  have hdesc : ∀ V : SmallEtaleNeighborhood (geometricPointMap f x), γ V =
      ((colimit.desc D c).hom).comp
        (etaleLocalRingGerm B S hS G (geometricPointMap f x) (Opposite.op V)) := by
    intro V
    have h := colimit.ι_desc c (Opposite.op V)
    ext a
    exact (congrArg (fun q => q.hom (ULift.up a)) h).symm
  refine ⟨(colimit.desc D c).hom, ?_, ?_⟩
  · intro U V g hc hp
    rw [hgerm V U g hc hp]
    exact hdesc V
  · intro ψ hψ
    apply RingHom.ext
    intro z
    have heq : CommRingCat.ofHom ψ = CommRingCat.ofHom (colimit.desc D c).hom := by
      apply colimit.hom_ext
      intro V
      obtain ⟨U, g, hcomm, hpoint⟩ := exists_compatible_chart_lift hF f V.unop
      have hψV := hψ U V.unop g hcomm hpoint
      have hφV := (hgerm V.unop U g hcomm hpoint).trans (hdesc V.unop)
      apply ConcreteCategory.hom_ext
      intro a
      exact congrArg (fun k => k (ULift.down a)) (hψV.symm.trans hφV)
    change (CommRingCat.ofHom ψ).hom z = (CommRingCat.ofHom (colimit.desc D c).hom).hom z
    rw [heq]

/-- The canonical homomorphism of étale local rings induced by a morphism of algebraic spaces
at a geometric point of its source, characterised by `Stacks 04NG` as the unique one
compatible with the germ maps in every commuting diagram of pointed étale charts. -/
def etaleLocalRingMap (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    (x : GeometricPoint B S hS F) :
    etaleLocalRing B S hS G (geometricPointMap f x) →+* etaleLocalRing B S hS F x :=
  (existsUnique_etaleLocalRingMap hF f x).choose

/-- The canonical homomorphism of étale local rings pulls germs of chart sections back along
the chart morphisms, in every commuting diagram of pointed étale charts over `f`. -/
theorem etaleLocalRingMap_isEtaleLocalRingMap (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    (x : GeometricPoint B S hS F) :
    IsEtaleLocalRingMap f x (etaleLocalRingMap hF f x) :=
  (existsUnique_etaleLocalRingMap hF f x).choose_spec.1

/-- A homomorphism of étale local rings compatible with the germ maps over `f` is the
canonical one. -/
theorem eq_etaleLocalRingMap (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    (x : GeometricPoint B S hS F)
    {φ : etaleLocalRing B S hS G (geometricPointMap f x) →+* etaleLocalRing B S hS F x}
    (hφ : IsEtaleLocalRingMap f x φ) : φ = etaleLocalRingMap hF f x :=
  (existsUnique_etaleLocalRingMap hF f x).unique hφ
    (etaleLocalRingMap_isEtaleLocalRingMap hF f x)

/-- Two commuting diagrams of pointed étale charts over the same morphism, with the same
neighbourhood of the image point, compute the same germ map: each is computed by the lift of
that neighbourhood through a fixed neighbourhood of the source point. -/
private theorem etaleLocalRingGerm_comp_eq_of_comm (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ G) {x : GeometricPoint B S hS F}
    {V : SmallEtaleNeighborhood (geometricPointMap f x)}
    (Z Z' : SmallEtaleNeighborhood x)
    (g : Z.chart.obj.left ⟶ V.chart.obj.left) (g' : Z'.chart.obj.left ⟶ V.chart.obj.left)
    (hg : Z.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom)
    (hpg : Z.point ≫ g = V.point)
    (hg' : Z'.chart.obj.hom ≫ f = yoneda.map g' ≫ V.chart.obj.hom)
    (hpg' : Z'.point ≫ g' = V.point) :
    (etaleLocalRingGerm B S hS F x (Opposite.op Z)).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom =
      (etaleLocalRingGerm B S hS F x (Opposite.op Z')).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g').op).hom := by
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood hF x
  obtain ⟨L⟩ := nonempty_etaleChartLift f N V
  rw [L.germ_eq Z g hg hpg, L.germ_eq Z' g' hg' hpg']

/-- Compatibility with the germ maps is stable under composition: a homomorphism of étale
local rings induced by `f` precomposed with one induced by `g` is induced by `f ≫ g`.  Hence
the canonical homomorphisms of Stacks 04NG compose, which is
`AlgebraicGeometry.Space.etaleLocalRingMap_comp`. -/
theorem isEtaleLocalRingMap_comp {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (g : G ⟶ H) (x : GeometricPoint B S hS F)
    {φ : etaleLocalRing B S hS G (geometricPointMap f x) →+* etaleLocalRing B S hS F x}
    {ψ : etaleLocalRing B S hS H (geometricPointMap g (geometricPointMap f x)) →+*
      etaleLocalRing B S hS G (geometricPointMap f x)}
    (hφ : IsEtaleLocalRingMap f x φ)
    (hψ : IsEtaleLocalRingMap g (geometricPointMap f x) ψ) :
    IsEtaleLocalRingMap (f ≫ g) x (φ.comp ψ) := by
  intro N P h hcomm hpoint
  obtain ⟨V, k, hk, hpk⟩ :=
    exists_compatible_chart_lift (x := geometricPointMap f x) hG g P
  obtain ⟨Z, l, hl, hpl⟩ := exists_compatible_chart_lift hF f V
  have hcomm' : Z.chart.obj.hom ≫ (f ≫ g) = yoneda.map (l ≫ k) ≫ P.chart.obj.hom :=
    calc Z.chart.obj.hom ≫ (f ≫ g)
        = (Z.chart.obj.hom ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (yoneda.map l ≫ V.chart.obj.hom) ≫ g := by rw [hl]
      _ = yoneda.map l ≫ (V.chart.obj.hom ≫ g) := Category.assoc _ _ _
      _ = yoneda.map l ≫ (yoneda.map k ≫ P.chart.obj.hom) := by rw [hk]
      _ = (yoneda.map l ≫ yoneda.map k) ≫ P.chart.obj.hom := (Category.assoc _ _ _).symm
      _ = yoneda.map (l ≫ k) ≫ P.chart.obj.hom := by rw [Functor.map_comp]
  have hpoint' : Z.point ≫ (l ≫ k) = P.point := by
    rw [← Category.assoc, hpl]; exact hpk
  rw [etaleLocalRingGerm_comp_eq_of_comm hF (f ≫ g) N Z h (l ≫ k) hcomm hpoint hcomm' hpoint']
  have target : (etaleLocalRingGerm B S hS F x (Opposite.op Z)).comp
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (l ≫ k)).op).hom =
      (φ.comp ψ).comp (etaleLocalRingGerm B S hS H
        (geometricPointMap g (geometricPointMap f x)) (Opposite.op P)) := by
    refine RingHom.ext fun a => ?_
    have h2 := DFunLike.congr_fun (hψ V P k hk hpk) a
    have h1 := DFunLike.congr_fun (hφ Z V l hl hpl)
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom a)
    have hga := DFunLike.congr_fun (toScheme_gammaMap_comp (B := B) (S := S) (hS := hS) l k) a
    exact ((congrArg (fun t => etaleLocalRingGerm B S hS F x (Opposite.op Z) t) hga).trans
      h1).trans (congrArg (fun t => φ t) h2)
  exact target

/-- The canonical homomorphisms of étale local rings of Stacks 04NG compose. -/
theorem etaleLocalRingMap_comp {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (g : G ⟶ H) (x : GeometricPoint B S hS F) :
    (etaleLocalRingMap hF f x).comp (etaleLocalRingMap hG g (geometricPointMap f x)) =
      etaleLocalRingMap hF (f ≫ g) x :=
  eq_etaleLocalRingMap hF (f ≫ g) x
    (isEtaleLocalRingMap_comp hF hG f g x (etaleLocalRingMap_isEtaleLocalRingMap hF f x)
      (etaleLocalRingMap_isEtaleLocalRingMap hG g (geometricPointMap f x)))

/-! ### Flatness at a point -/

/-- **Stacks 04NG.** A morphism `f` of algebraic spaces over `S` is flat at the image of a
geometric point `x` of its source exactly when the canonical homomorphism of étale local rings
`𝒪_{G, f ∘ x} ⟶ 𝒪_{F, x}` is flat.

For a point `x₀` of `F` with `x.LiesOver x₀` the statement for `x₀` follows by rewriting along
that equality. -/
@[stacks 04NG "the flatness criterion"]
theorem isFlatAt_iff_etaleLocalRingMap_flat (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : GeometricPoint B S hS F) :
    IsFlatAt B S hS f x.image ↔ (etaleLocalRingMap hF f x).Flat := by
  classical
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood hG (geometricPointMap f x)
  obtain ⟨V, hVaffine⟩ := exists_affine_smallEtaleNeighborhood N
  obtain ⟨U, g, hc, hp⟩ := exists_compatible_chart_lift hF f V
  set T := BigFppfOver.toScheme B S hS with hT
  -- the comparison of étale local rings is read off the chart schemes, so the morphism of
  -- charts is named at that spelling of its source and target
  set q : chartScheme U.chart ⟶ chartScheme V.chart := T.map g with hqdef
  set u := (chartGeometricPoint U).hom (closedPoint (chartGeometricPoint U).residueField)
    with hu
  set v := (chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)
    with hv
  have huv : q u = v := congrArg
    (fun k => (T.map k) (show T.obj x.val.siteObject from closedPoint x.val.carrier)) hp
  set p : FieldValuedPoint B S hS (yoneda.obj U.chart.obj.left) :=
    { carrier := x.val.carrier
      contained := x.val.contained
      toBase := x.val.toBase
      value := U.point } with hp'
  have hmap : FieldValuedPoint.map B S hS _ U.chart.obj.hom p = x.val :=
    congrArg (fun a : F.obj (Opposite.op x.val.siteObject) => { x.val with value := a })
      U.point_comp
  set c : EtaleChartAtPoint B S hS f x.image :=
    { U := U.chart.obj.left
      V := V.chart.obj.left
      a := U.chart.obj.hom
      b := V.chart.obj.hom
      h := g
      a_etale := U.chart.property
      b_etale := V.chart.property
      comm := hc.symm
      representative := p
      point := closedPoint p.carrier
      maps_to := congrArg (FieldValuedPoint.class B S hS F) hmap } with hcdef
  have hflat : IsFlatAt B S hS f x.image ↔ (q.stalkMap u).hom.Flat := by
    refine ⟨fun h => (MorphismOfGerms.isFlat_ofSchemeHom_iff q u).mp (h c), fun h => ?_⟩
    refine (holdsOnEveryEtaleChartAtPoint_iff_some B S hS (@MorphismOfGerms.IsFlat.{u})
      MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat hF hG f x.image).mpr ?_
    exact ⟨c, (MorphismOfGerms.isFlat_ofSchemeHom_iff q u).mpr h⟩
  set E := bigEtaleSiteOfFppfSite B with hE
  set TU := henselizationTower ((chartScheme U.chart).presheaf.stalk u)
    (separableClosure (ResidueField ((chartScheme U.chart).presheaf.stalk u))
      (chartGeometricPoint U).residueField) with hTU
  set TV := henselizationTower ((chartScheme V.chart).presheaf.stalk v)
    (separableClosure (ResidueField ((chartScheme V.chart).presheaf.stalk v))
      (chartGeometricPoint V).residueField) with hTV
  refine hflat.trans (flat_stalkMap_iff_of_strictHenselization_germs q u v huv TV TU
    (strictHenselizationEquivEtaleLocalRing hG V E V.chart.obj.left.left.property TV)
    (strictHenselizationEquivEtaleLocalRing hF U E U.chart.obj.left.left.property TU)
    (etaleLocalRingMap hF f x) ?_)
  intro a
  calc
    _ = (etaleLocalRingMap hF f x)
        (etaleLocalRingGerm B S hS G (geometricPointMap f x) (Opposite.op V) a) :=
      congrArg _ (strictHenselizationEquivEtaleLocalRing_germ hG V E
        V.chart.obj.left.left.property TV a)
    _ = etaleLocalRingGerm B S hS F x (Opposite.op U) ((Scheme.Γ.map q.op).hom a) :=
      (congrArg (fun k => k a)
        (etaleLocalRingMap_isEtaleLocalRingMap hF f x U V g hc hp)).symm
    _ = _ := (strictHenselizationEquivEtaleLocalRing_germ hF U E
      U.chart.obj.left.left.property TU ((Scheme.Γ.map q.op).hom a)).symm

end Space

end AlgebraicGeometry

end
