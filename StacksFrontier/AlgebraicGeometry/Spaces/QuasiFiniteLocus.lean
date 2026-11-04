module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts

/-!
# The quasi-finite locus of a morphism of algebraic spaces

Part (1) of Tag 0ABM says that the set of points of the source at which a morphism of
algebraic spaces is quasi-finite is an open subset of the point space of Tag 03BU, and
likewise for any base change of the morphism; part (2) says that for a morphism locally of
finite type the locus of a base change is the inverse image of the locus, so that forming the
quasi-finite locus commutes with base change. This file proves both: openness as a single
statement about an arbitrary morphism, of which the two clauses of part (1) are instances, and
the base-change comparison for an arbitrary cartesian square of algebraic spaces.

Along the way it records the germ form of quasi-finiteness of a morphism of schemes at a
point, which is what makes the two sides of part (2) comparable through étale charts.

Tag 0ABN is the finiteness statement which that comparison makes available: a finite-type
morphism of algebraic spaces is quasi-finite at only finitely many points of any one fibre.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.quasiFiniteAt_iff_hasRepresentativeWithProperty`: for a morphism of
  schemes locally of finite type, quasi-finiteness at a point is the germ property of
  Stacks 04R6 induced by local quasi-finiteness.
* `AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_iUnion` writes the locus as the union of
  the point sets of the locally quasi-finite open subspaces of the source.
* `AlgebraicGeometry.Space.isOpen_setOf_isQuasiFiniteAt` is part (1) of Tag 0ABM.
* `AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback` is part (2) of
  Tag 0ABM.
* `AlgebraicGeometry.Space.finite_setOf_mapsTo_and_isQuasiFiniteAt` is Tag 0ABN.

## Implementation notes

Quasi-finiteness at a point is `AlgebraicGeometry.Space.IsQuasiFiniteAt`, part (2) of Tag
03XJ: some open subspace of the source containing the point is locally quasi-finite over the
target. The locus is therefore, verbatim, the union over the locally quasi-finite open
subspaces of the images of their point sets, and each such image is open because an open
immersion is open on points — `AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion`,
part (1) of Tag 03BZ. The source argument instead transports openness from an étale chart,
through Tags 04NC and 04RF and the scheme-level openness of Tag 01TI; none of that is needed
here, because the definition of quasi-finiteness at a point already quantifies over open
neighbourhoods rather than over germs.

Two hypotheses of the source statement are consequently absent from the openness result. The
morphism need not be locally of finite type, and neither the source nor the target need be an
algebraic space: openness of the point set of an open subspace is tested on the represented
base changes of its inclusion, not on an atlas. The topology is
`AlgebraicGeometry.Space.pointTopology`, installed as a local instance as elsewhere in this
library.

Part (2) does use the chart machinery, and both of its hypotheses. Compatible surjective étale
charts of the cartesian square (`AlgebraicGeometry.Space.exists_compatible_etale_charts`) put
the two morphisms into a cartesian square of morphisms of schemes, and a field-valued point of
the chart of the fibre product makes both squares into pointed charts whose selected scheme
points correspond. Since local quasi-finiteness of morphisms of schemes is étale local on the
source and target
(`AlgebraicGeometry.locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget`,
Stacks 04R3), quasi-finiteness at a point may be read off any one pointed chart (Stacks 04NC),
which reduces the statement to Tag 01TM for schemes.

Parts (3) and (4) of Tag 0ABM are the base-change statements for local quasi-finiteness and
quasi-finiteness. They are Tag 03XL, and are proved — without the hypothesis of local finite
type — in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/QuasiFinite.lean`, where the étale
locality input of this file's part (2) also lives.

Tag 0ABN is reduced to its scheme-level counterpart, Tag 0AAY, by base changing twice: once
along a field-valued representative of the given point of the target, and once more along the
identity of its field spectrum, which makes the source quasi-compact and hence gives it an
*affine* surjective étale chart (Tag 03H6). Part (2) is what carries quasi-finiteness of the
original morphism at a point of `|X|` over to the two base changes, and the comparison of the
points of a represented presheaf with the points of the representing scheme
(`AlgebraicGeometry.Space.pointsEquivScheme`) is what turns the finite set of quasi-finite
points of the chart into a finite set covering the fibre.

## References

* [Stacks Project, Tag 01TM](https://stacks.math.columbia.edu/tag/01TM)
* [Stacks Project, Tag 0AAY](https://stacks.math.columbia.edu/tag/0AAY)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ABN](https://stacks.math.columbia.edu/tag/0ABN)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04R6](https://stacks.math.columbia.edu/tag/04R6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The germ form of quasi-finiteness at a point of a scheme -/

/-- A morphism of schemes locally of finite type is quasi-finite at a point exactly when the
germ it defines there has a representative which is locally quasi-finite in the sense of
Stacks 03XJ.

Both directions are the quasi-finite locus of Stacks 01TI: it is an open neighbourhood of
every point of quasi-finiteness over which the morphism is locally quasi-finite, and
conversely a representative with that property restricts to one on a common open
neighbourhood, where local quasi-finiteness is quasi-finiteness at each point. -/
@[sga "3 VIB 1.3" "(6), special case"]
theorem quasiFiniteAt_iff_hasRepresentativeWithProperty {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    quasiFiniteAt f x ↔
      MorphismOfGerms.HasRepresentativeWithProperty
        ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
          (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
        (MorphismOfGerms.ofSchemeHom f x) := by
  constructor
  · intro hq
    have hxW : x ∈ quasiFiniteLocus f := (mem_quasiFiniteLocus_iff f x).2 hq
    refine ⟨{ source := quasiFiniteLocus f
              mem_source := hxW
              hom := (quasiFiniteLocus f).ι ≫ f
              map_point := rfl }, ?_, ⟨inferInstance, inferInstance⟩⟩
    exact MorphismOfGerms.mk_eq_mk_iff.mpr ⟨quasiFiniteLocus f, hxW, le_rfl, le_top, by simp⟩
  · rintro ⟨r, hr, hP⟩
    have hagree : r.AgreeNear
        ({ source := ⊤, mem_source := by simp, hom := X.topIso.hom ≫ f,
            map_point := rfl } : MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩) :=
      MorphismOfGerms.mk_eq_mk_iff.mp hr
    obtain ⟨W, hxW, hWr, hWtop, heq⟩ := hagree
    have _ : LocallyOfFiniteType r.hom := hP.1
    have _ : LocallyQuasiFinite r.hom := hP.2
    have hrestrict : W.ι ≫ f = X.homOfLE hWr ≫ r.hom := by
      rw [heq, ← Category.assoc]
      exact (congrArg (fun k => k ≫ f) (by simp : X.homOfLE hWtop ≫ X.topIso.hom = W.ι)).symm
    have hW : LocallyOfFiniteType (W.ι ≫ f) ∧ LocallyQuasiFinite (W.ι ≫ f) := by
      rw [hrestrict]; exact ⟨inferInstance, inferInstance⟩
    refine ⟨finiteTypeAt_of_locallyOfFiniteType f x, ?_⟩
    have hqW := (forall_quasiFiniteAt_iff (W.ι ≫ f)).mpr hW ⟨x, hxW⟩
    exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
      (f := W.ι) (g := f) (x := ⟨x, hxW⟩)).mp hqW.2

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The set of points at which a morphism of algebraic spaces over `S` is quasi-finite is the
union of the point sets of those open subspaces of the source which are locally quasi-finite
over the target. -/
theorem setOf_isQuasiFiniteAt_eq_iUnion (f : X ⟶ Y) :
    {x | IsQuasiFiniteAt B S hS f x} =
      ⋃ U : {U : Subfunctor X // IsOpenSubspace B S hS U ∧
          IsLocallyQuasiFinite B S hS (U.ι ≫ f)},
        Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) := by
  ext x
  constructor
  · rintro ⟨U, hU, x', hx', hqf⟩
    exact Set.mem_iUnion.2 ⟨⟨U, hU, hqf⟩, x', hx'⟩
  · intro hx
    obtain ⟨U, x', hx'⟩ := Set.mem_iUnion.1 hx
    exact ⟨U.1, U.2.1, x', hx', U.2.2⟩

/-- **Stacks 0ABM, part (1).** The set of points at which a morphism of algebraic spaces over
`S` is quasi-finite is open in the point space of Tag 03BU. Applied to a base change `f'` of
`f` this is the second clause of part (1), that the quasi-finite locus of `f'` is open.

The source assumes `f` locally of finite type; that is not needed. -/
@[stacks 0ABM "part (1): the quasi-finite locus is open"]
theorem isOpen_setOf_isQuasiFiniteAt (f : X ⟶ Y) :
    IsOpen {x | IsQuasiFiniteAt B S hS f x} := by
  rw [setOf_isQuasiFiniteAt_eq_iUnion]
  exact isOpen_iUnion fun U ↦
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.1.ι U.2.1.2

/-! ### The locus commutes with base change -/

/-- Quasi-finiteness of a morphism of algebraic spaces at a point is read off any one pointed
étale chart, when the chart morphism is locally of finite type. -/
private theorem isQuasiFiniteAt_iff_quasiFiniteAt_of_chart {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (x : points B S hS F) (c : EtaleChartAtPoint B S hS f x)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h)] :
    IsQuasiFiniteAt B S hS f x ↔
      quasiFiniteAt ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) := by
  have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (MorphismOfGerms.HasRepresentativeWithProperty
        ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
          (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))) :=
    MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
      locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
  exact ⟨fun h => (quasiFiniteAt_iff_hasRepresentativeWithProperty _ _).mpr
      ((isQuasiFiniteAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hF hG f x).mp h c),
    fun h => (isQuasiFiniteAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hF hG f x).mpr
      ((holdsOnEveryEtaleChartAtPoint_iff_some B S hS _ hQ hF hG f x).mpr
        ⟨c, (quasiFiniteAt_iff_hasRepresentativeWithProperty _ _).mp h⟩)⟩

/-- **Stacks 0ABM, part (2).** For a morphism of algebraic spaces over `S` which is locally of
finite type, the locus of quasi-finiteness of a base change is the inverse image of the locus
of quasi-finiteness of the morphism.

Compatible surjective étale charts of the cartesian square
(`AlgebraicGeometry.Space.exists_compatible_etale_charts`) give a chart `V` of the target, a
chart `U ⟶ V` of `f`, a chart `V' ⟶ V` of `g` and the induced chart `U' = U ×_V V' ⟶ V'` of
the base change, with `U'` an atlas of the fibre product. A field-valued point of `U'` lying
over the given point of `|X'|` turns the two squares into pointed étale charts of `f'` at that
point and of `f` at its image, whose selected scheme points correspond under `U' ⟶ U`. Local
quasi-finiteness of morphisms of schemes being étale local on the source and target
(Stacks 04R3), quasi-finiteness at a point is the induced germ condition read in any one
pointed chart (Stacks 04NC), so each side becomes quasi-finiteness of a morphism of schemes at
corresponding points of a cartesian square of schemes, which is **Stacks 01TM**. -/
@[stacks 0ABM "part (2): the locus commutes with base change", sga "3 V 7.4" "more general"]
theorem setOf_isQuasiFiniteAt_eq_preimage_of_isPullback
    {X₁ X₀ Y₁ Y₀ : AlgebraicSpaces B S hS} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀}
    {g : Y₁ ⟶ Y₀} (sq : IsPullback g' f' f g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    {x' | IsQuasiFiniteAt B S hS f'.hom x'} =
      pointsMap B S hS X₁.1 g'.hom ⁻¹' {x | IsQuasiFiniteAt B S hS f.hom x} := by
  let T := BigFppfOver.toScheme B S hS
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have hQbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) (F := yoneda)
  have hQcomp := MorphismProperty.relative_isStableUnderComposition
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) (F := yoneda)
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hcharts, hap, hbq, hcX, hcY,
      hvSurj, hvEtale, haSurj, haEtale, hbSurj, hbEtale, hcSurj, hcEtale⟩ :=
    exists_compatible_etale_charts B S hS f g
  -- the comparison of the given cartesian square with the chosen fibre product
  let eAs : X₁ ≅ AlgebraicSpaces.fiberProduct B S hS f g :=
    sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)
  let e : X₁.1 ≅ pullback f.hom g.hom :=
    { hom := eAs.hom.hom
      inv := eAs.inv.hom
      hom_inv_id := congrArg (fun k => k.hom) eAs.hom_inv_id
      inv_hom_id := congrArg (fun k => k.hom) eAs.inv_hom_id }
  have heFst : e.hom ≫ pullback.fst f.hom g.hom = g'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_fst _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heSnd : e.hom ≫ pullback.snd f.hom g.hom = f'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_snd _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heInvSnd : e.inv ≫ f'.hom = pullback.snd f.hom g.hom := by
    rw [← heSnd, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  -- étaleness of the two chart maps into the source algebraic spaces
  have hSndFEtale := hQbc.of_isPullback (IsPullback.of_hasPullback v f.hom) hvEtale
  have hSndGEtale := hQbc.of_isPullback (IsPullback.of_hasPullback v g.hom) hvEtale
  have hAEtale := MorphismProperty.comp_mem _ a (pullback.snd v f.hom) haEtale hSndFEtale
  have hBEtale := MorphismProperty.comp_mem _ b (pullback.snd v g.hom) hbEtale hSndGEtale
  have hcXEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf (c ≫ e.inv) :=
    have _ : IsIso e.inv := ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩
    MorphismProperty.RespectsIso.postcomp _ e.inv c hcEtale
  have hcommF : yoneda.map p ≫ v = (a ≫ pullback.snd v f.hom) ≫ f.hom := by
    calc yoneda.map p ≫ v = (a ≫ pullback.fst v f.hom) ≫ v := by rw [← hap]
      _ = (a ≫ pullback.snd v f.hom) ≫ f.hom := by
          simp only [Category.assoc, pullback.condition]
  have hcommF' : yoneda.map pV' ≫ (b ≫ pullback.snd v g.hom) = (c ≫ e.inv) ≫ f'.hom := by
    calc yoneda.map pV' ≫ (b ≫ pullback.snd v g.hom) = c ≫ pullback.snd f.hom g.hom := by
          simpa only [Category.assoc] using hcY.symm
      _ = (c ≫ e.inv) ≫ f'.hom := by rw [← heInvSnd]; simp only [Category.assoc]
  -- local finite type of the two chart morphisms of schemes
  have hpLFT : LocallyOfFiniteType (T.map p) :=
    hf U V (a ≫ pullback.snd v f.hom) v p hAEtale hvEtale hcommF
  have _ : LocallyOfFiniteType (T.map pV') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcharts hpLFT
  have hscheme : ∀ w : T.obj U',
      quasiFiniteAt (T.map pV') w ↔ quasiFiniteAt (T.map p) (T.map pU w) := fun w => by
    rw [← mem_quasiFiniteLocus_iff, ← mem_quasiFiniteLocus_iff,
      quasiFiniteLocus_eq_preimage_of_isPullback hcharts]
    rfl
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  -- a field-valued representative of `x'` on the chart `U'` of the fibre product
  have hPull : IsAlgebraicSpace B S hS (pullback f.hom g.hom) :=
    isAlgebraicSpace_pullback B S hS f.hom g.hom X₀.property Y₁.property Y₀.property
  obtain ⟨z, hz⟩ :=
    (surjective_iff_surjective_pointsMap B S hS (pullback f.hom g.hom) hPull U' c).mp hcSurj
      (pointsMap B S hS X₁.1 e.hom x')
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hz' : pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U')) =
      pointsMap B S hS X₁.1 e.hom x' := hz
  -- the two pointed charts
  let chartF : EtaleChartAtPoint B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x') :=
    { U := U
      V := V
      a := a ≫ pullback.snd v f.hom
      b := v
      h := p
      a_etale := hAEtale
      b_etale := hvEtale
      comm := hcommF
      representative := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U) (a ≫ pullback.snd v f.hom)
            ((FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r).class B S hS
              (yoneda.obj U)) =
            pointsMap B S hS (yoneda.obj U') (yoneda.map pU ≫ a ≫ pullback.snd v f.hom)
              (r.class B S hS (yoneda.obj U')) := rfl
        have h₂ : pointsMap B S hS (yoneda.obj U') (c ≫ pullback.fst f.hom g.hom)
            (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
              (pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U'))) := rfl
        have h₃ : pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
            (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ pullback.fst f.hom g.hom) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom (pullback.fst f.hom g.hom)) x').symm
        rw [h₁, ← hcX, h₂, hz', h₃, heFst] }
  let chartF' : EtaleChartAtPoint B S hS f'.hom x' :=
    { U := U'
      V := V'
      a := c ≫ e.inv
      b := b ≫ pullback.snd v g.hom
      h := pV'
      a_etale := hcXEtale
      b_etale := hBEtale
      comm := hcommF'
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U') (c ≫ e.inv)
            (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (pullback f.hom g.hom) e.inv
              (pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U'))) := rfl
        have h₂ : pointsMap B S hS (pullback f.hom g.hom) e.inv
            (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ e.inv) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom e.inv) x').symm
        rw [h₁, hz', h₂, e.hom_inv_id, pointsMap_id, id_eq] }
  have hsource : chartF.sourcePoint B S hS = T.map pU (chartF'.sourcePoint B S hS) := by
    show (T.map (r.value ≫ pU)) (IsLocalRing.closedPoint r.carrier) =
      T.map pU ((T.map r.value) (IsLocalRing.closedPoint r.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  rw [isQuasiFiniteAt_iff_quasiFiniteAt_of_chart B S hS X₁.property Y₁.property f'.hom x' chartF',
    isQuasiFiniteAt_iff_quasiFiniteAt_of_chart B S hS X₀.property Y₀.property f.hom _ chartF,
    hsource]
  exact hscheme _

/-! ### Finitely many quasi-finite points in one fibre -/

/-- A point of the source of a base change of a morphism locally of finite type is a point of
quasi-finiteness as soon as its image in the source of the morphism is. -/
private theorem isQuasiFiniteAt_of_isPullback {X₁ X₀ Y₁ Y₀ : AlgebraicSpaces B S hS}
    {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀} {g : Y₁ ⟶ Y₀} (sq : IsPullback g' f' f g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (v : points B S hS X₁.1)
    (hv : IsQuasiFiniteAt B S hS f.hom (pointsMap B S hS X₁.1 g'.hom v)) :
    IsQuasiFiniteAt B S hS f'.hom v := by
  exact (Set.ext_iff.1 (setOf_isQuasiFiniteAt_eq_preimage_of_isPullback B S hS sq hf) v).2 hv

/-- **Stacks 0ABN.** For a morphism of algebraic spaces over `S` of finite type, only finitely
many points of the source lying over a fixed point of the target are points at which the
morphism is quasi-finite.

Represent the point of the target by a field-valued point `Spec k ⟶ Y` and base change twice:
once along it, and once more along the identity of `Spec k`. The second base change is a
finite-type morphism out of an algebraic space with quasi-compact source, so it has an
*affine* surjective étale chart `U` (Stacks 03H6), and the morphism of schemes `U ⟶ Spec k`
it induces is of finite type with compact source, hence quasi-compact: Stacks 0AAY bounds the
set of its quasi-finite points over the closed point of `Spec k`, and that is all of `U`
because `Spec k` is a one-point space.

A point of `|X|` over the given point at which `f` is quasi-finite lifts through both
cartesian squares (Stacks 03H4), and quasi-finiteness travels with it because forming the
quasi-finite locus commutes with base change
(`AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback`). A field-valued
representative of the lift on the chart then exhibits the point as the image of a member of
that finite set. -/
@[stacks 0ABN]
theorem finite_setOf_mapsTo_and_isQuasiFiniteAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsFiniteType B S hS f) (y : points B S hS Y) :
    {x : points B S hS X |
      pointsMap B S hS X f x = y ∧ IsQuasiFiniteAt B S hS f x}.Finite := by
  classical
  obtain ⟨py, hpy⟩ := Quot.exists_rep y
  let K : BigFppfOver B S hS := py.siteObject B S hS Y
  let α : yoneda.obj K ⟶ Y := yonedaEquiv.symm py.value
  let zrep : FieldValuedPoint B S hS (yoneda.obj K) :=
    { carrier := py.carrier
      field := py.field
      contained := py.contained
      toBase := py.toBase
      value := 𝟙 K }
  have hα : FieldValuedPoint.map B S hS (yoneda.obj K) α zrep = py := by
    cases py
    simp [FieldValuedPoint.map, zrep, α, K, FieldValuedPoint.siteObject]
  let z : points B S hS (yoneda.obj K) := zrep.class B S hS (yoneda.obj K)
  have hzy : pointsMap B S hS (yoneda.obj K) α z = y :=
    (congrArg (FieldValuedPoint.class B S hS Y) hα).trans hpy
  -- the spectrum of a field is a one-point, hence compact, space
  have hKsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj K) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of py.carrier)))
  have hKcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj K) := inferInstance
  -- the first base change, along the field-valued point
  let AX : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let AY : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let AK : AlgebraicSpaces B S hS := ⟨yoneda.obj K, isAlgebraicSpace_yoneda B S hS K⟩
  let fsp : AX ⟶ AY := ObjectProperty.homMk f
  let gsp : AK ⟶ AY := ObjectProperty.homMk α
  let F : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS fsp gsp
  let pF : F ⟶ AX := ObjectProperty.homMk (pullback.fst fsp.hom gsp.hom)
  let qF : F ⟶ AK := ObjectProperty.homMk (pullback.snd fsp.hom gsp.hom)
  have hsqF : IsPullback pF qF fsp gsp := AlgebraicSpaces.isPullback_fiberProduct B S hS fsp gsp
  have hqFft : IsFiniteType B S hS qF.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A C : AlgebraicSpaces B S hS⦄ (k : A ⟶ C) => IsFiniteType B S hS k.hom)
      hsqF hf
  -- the second base change, along the identity, which has quasi-compact source
  let idAK : AK ⟶ AK := ObjectProperty.homMk (𝟙 AK.1)
  let P : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS idAK qF
  let pP : P ⟶ AK := ObjectProperty.homMk (pullback.fst idAK.hom qF.hom)
  let qP : P ⟶ F := ObjectProperty.homMk (pullback.snd idAK.hom qF.hom)
  have hsqP : IsPullback pP qP idAK qF := AlgebraicSpaces.isPullback_fiberProduct B S hS idAK qF
  have hPqc : IsQuasiCompactSpace B S hS P.1 := by
    have h := hqFft.2 AK.1 AK.property (isQuasiCompactSpace_yoneda_obj B S hS hKcpt) (𝟙 AK.1)
    simpa [P, idAK, AlgebraicSpaces.fiberProduct] using h
  have hqPft : IsFiniteType B S hS pP.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A C : AlgebraicSpaces B S hS⦄ (k : A ⟶ C) => IsFiniteType B S hS k.hom)
      hsqP.flip hqFft
  -- an affine surjective étale chart of the fibre
  obtain ⟨U, a, hUaff, hAsurj, hAetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P.1 P.property).mp hPqc
  have hAsurjPts : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (surjective_iff_surjective_pointsMap B S hS P.1 P.property U a).mp hAsurj
  have haEtale := (isEtale_iff_presheaf_of_yoneda B S hS a).1 hAetale
  have hidK : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj K)) :=
    presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj K))
  have hidU : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U)) :=
    presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj U))
  let m : U ⟶ K := yoneda.preimage (a ≫ pP.hom)
  have hm : yoneda.map m = a ≫ pP.hom := yoneda.map_preimage _
  have hcompChart : IsLocallyOfFiniteType B S hS (a ≫ pP.hom) :=
    isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS U) P.property
      AK.property a pP.hom (isLocallyOfFiniteType_of_isEtale B S hS P.property hAetale)
      hqPft.1
  have hmLFT : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m) :=
    hcompChart U K (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj K)) m hidU hidK (by rw [hm]; simp)
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := by
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
    infer_instance
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map m) :=
    quasiCompact_of_compactSpace _
  have hfinite := finite_setOf_mapsTo_and_quasiFiniteAt ((BigFppfOver.toScheme B S hS).map m)
    (IsLocalRing.closedPoint py.carrier : (BigFppfOver.toScheme B S hS).obj K)
  refine (hfinite.image fun w => pointsMap B S hS (yoneda.obj U) (a ≫ qP.hom ≫ pF.hom)
    ((pointsEquivScheme B S hS U).symm w)).subset ?_
  rintro x ⟨hxy, hxf⟩
  -- lift `x` through the two cartesian squares
  have hcomm : pointsMap B S hS AX.1 fsp.hom x = pointsMap B S hS AK.1 gsp.hom z := by
    show pointsMap B S hS X f x = pointsMap B S hS (yoneda.obj K) α z
    rw [hzy]; exact hxy
  obtain ⟨v, hvX, hvK⟩ := exists_point_of_isPullback B S hS hsqF x z hcomm
  have hqFqf : IsQuasiFiniteAt B S hS qF.hom v :=
    isQuasiFiniteAt_of_isPullback B S hS hsqF hf.1 v (by rw [hvX]; exact hxf)
  obtain ⟨w, -, hwF⟩ := exists_point_of_isPullback B S hS hsqP z v hvK.symm
  have hqPqf : IsQuasiFiniteAt B S hS pP.hom w :=
    isQuasiFiniteAt_of_isPullback B S hS hsqP.flip hqFft.1 w (by rw [hwF]; exact hqFqf)
  -- read quasi-finiteness off the chart
  obtain ⟨wU, hwU⟩ := hAsurjPts w
  obtain ⟨ru, hru⟩ := Quot.exists_rep wU
  have hru' : ru.class B S hS (yoneda.obj U) = wU := hru
  let chart : EtaleChartAtPoint B S hS pP.hom w :=
    { U := U
      V := K
      a := a
      b := 𝟙 (yoneda.obj K)
      h := m
      a_etale := haEtale
      b_etale := hidK
      comm := by rw [hm]; simp
      representative := ru
      point := IsLocalRing.closedPoint ru.carrier
      maps_to := by rw [hru']; exact hwU }
  refine ⟨schemePoint B S hS U ru, ⟨@Subsingleton.elim _ hKsub _ _,
    (isQuasiFiniteAt_iff_quasiFiniteAt_of_chart B S hS P.property AK.property pP.hom w
      chart).mp hqPqf⟩, ?_⟩
  have hclass : (pointsEquivScheme B S hS U).symm (schemePoint B S hS U ru) =
      ru.class B S hS (yoneda.obj U) :=
    (pointsEquivScheme B S hS U).injective (by rw [Equiv.apply_symm_apply]; rfl)
  have hsplit : pointsMap B S hS (yoneda.obj U) (a ≫ qP.hom ≫ pF.hom) wU =
      pointsMap B S hS F.1 pF.hom
        (pointsMap B S hS P.1 qP.hom (pointsMap B S hS (yoneda.obj U) a wU)) :=
    (congrFun (pointsMap_comp B S hS (yoneda.obj U) a (qP.hom ≫ pF.hom)) wU).trans
      (congrFun (pointsMap_comp B S hS P.1 qP.hom pF.hom) _)
  show pointsMap B S hS (yoneda.obj U) (a ≫ qP.hom ≫ pF.hom)
    ((pointsEquivScheme B S hS U).symm (schemePoint B S hS U ru)) = x
  rw [hclass, hru', hsplit, hwU, hwF, hvX]

end Space

end AlgebraicGeometry

end
