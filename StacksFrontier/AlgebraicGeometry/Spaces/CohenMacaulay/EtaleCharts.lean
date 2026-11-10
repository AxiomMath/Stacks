module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohen–Macaulay morphisms of algebraic spaces and étale charts of the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose fibres are locally
Noetherian. Then `f` is Cohen–Macaulay exactly when it is flat and the fibres of its base
change to one, equivalently to every, étale scheme chart of `Y` are Cohen–Macaulay algebraic
spaces.

## Main definitions

* `AlgebraicGeometry.Space.fiberAt` is the fibre of a morphism at a field-valued point of its
  target.
* `AlgebraicGeometry.Space.chartResidueFieldPoint` is the field-valued point of the target
  determined by a point of an étale scheme chart of it.
* `AlgebraicGeometry.Space.HasLocallyNoetherianFibers` is local Noetherianity of all fibres.
* `AlgebraicGeometry.Space.HasCohenMacaulayFibersOnChart` is Cohen–Macaulayness of the fibres
  over the points of one étale scheme chart of the target.
* `AlgebraicGeometry.Space.etaleLocalFiberIdeal` is the ideal of the étale local ring of the
  source cutting out the local ring of the fibre.

## Main results

* `AlgebraicGeometry.Space.isCohenMacaulay_isLocal_etale`: Cohen–Macaulayness of schemes is
  local for the étale topology.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_fiberAt_iff`: an étale-local property of
  schemes holds on the fibre of `f` over a residue-field point of a chart exactly when it
  holds on the corresponding scheme-theoretic fibre of a chart square.
* `AlgebraicGeometry.Space.isCohenMacaulay_yoneda_map_iff`: for a flat morphism of represented
  presheaves with locally Noetherian fibres, Cohen–Macaulayness is Cohen–Macaulayness of all
  scheme-theoretic fibres.
* `AlgebraicGeometry.Space.isCohenMacaulay_tfae_etaleCharts`: **Stacks 0E0W**, the three
  equivalent conditions.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_iff_etaleLocalRingMap`: **Stacks 0E0W**, the
  equivalence of conditions (a) and (b) at a geometric point.

## Implementation notes

The fibre of `f` over a field-valued point `p` of `Y` is the presheaf fibre product of `f`
with the morphism `h_{Spec κ} ⟶ Y` carried by `p`, and the Cohen–Macaulay and locally
Noetherian conditions on it are `AlgebraicGeometry.Space.HasEtaleLocalProperty` of Tag 03E6
for the corresponding property of schemes. Cohen–Macaulayness of schemes is local for the
étale topology because it is local for the syntomic topology, Tag 036B, and an étale
morphism is syntomic, Tag 02GQ.

`AlgebraicGeometry.Space.HasLocallyNoetherianFibers` is local Noetherianity of the fibre over
every residue-field point of every étale scheme chart of `Y`. This is the every-chart reading
of the standing hypothesis of the source, which that source states by naming the equivalent
chart and field-valued-point conditions of Tag 0CUW. It is the reading the proof below
consumes, and no case of the equivalence is used.

The fibre condition over a chart point is compared with the ordinary scheme-theoretic fibre
of the chart square by `AlgebraicGeometry.Space.hasEtaleLocalProperty_fiberAt_iff`: given a
surjective étale scheme atlas `a : h_U ⟶ X ×_Y h_V` of the base change, presented over `V` by
a morphism `h : U ⟶ V` of the site, the base change of `a` along the residue field of `v`
is again a surjective étale scheme atlas, of the fibre, and its source is the scheme-theoretic
fibre of `h` at `v` because the canonical functor to schemes preserves fibre products. With
that comparison the three conditions reduce to Tag 045S for the morphism of schemes `h`,
through the chart descriptions of Cohen–Macaulayness of Tag 0E0V already available for a
morphism of represented presheaves.

The criterion at a geometric point is the same chart square read on strict henselizations. The
Stacks text states it under the standing hypothesis that the fibres are locally Noetherian,
but that hypothesis is not used: Noetherianity of the fibre local ring is part of the germ
predicate `AlgebraicGeometry.HasCohenMacaulayFiberLocalRing` of Tag 0E0U rather than an
assumption, so the criterion is stated here without it. The identification of the étale local
rings with the strict henselizations of the chart local rings is Tag 04KF, that the quotient
of a strict henselization by an extended ideal is a strict henselization of the quotient is
Tag 05WS, and that Cohen–Macaulayness of a Noetherian local ring passes to and from its strict
henselization is Tag 06LM. Affineness of the chart of the target is what makes the germs of its
global sections generate its local ring, which is what pins the square of henselizations down;
that is why the chart square is refined to one with affine target chart.

## References

* [Stacks Project, Tag 0E0W](https://stacks.math.columbia.edu/tag/0E0W)
* [Stacks Project, Tag 045S](https://stacks.math.columbia.edu/tag/045S)
* [Stacks Project, Tag 0CUW](https://stacks.math.columbia.edu/tag/0CUW)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05WS](https://stacks.math.columbia.edu/tag/05WS)
* [Stacks Project, Tag 06LM](https://stacks.math.columbia.edu/tag/06LM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Cohen–Macaulayness of schemes is local for the étale topology: it is local for the
syntomic topology by Tag 036B, and an étale morphism is syntomic by Tag 02GQ. -/
instance isCohenMacaulay_isLocal_etale :
    ObjectProperty.IsLocal (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsCohenMacaulay T)
      Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le (Scheme.precoverage_mono
    (fun _ _ f hf => have := hf; syntomic_of_etale f))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for pullbacks of presheaves on the big fppf site is expensive
/-- Pullbacks of presheaves on the big fppf site of `S`, found once so that later searches
do not repeat the expensive instance search. -/
theorem hasLimit_cospan_presheaf_etaleCharts {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  inferInstance

attribute [local instance high] hasLimit_cospan_presheaf_etaleCharts

/-! ### Fibres at field-valued points of the target -/

/-- The fibre of a morphism of presheaves on the big fppf site of `S` at a field-valued point
of its target: the presheaf fibre product with the morphism out of the spectrum of the field
carried by the point. -/
abbrev fiberAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback f (yonedaEquiv.symm p.value)

/-- An étale-local property of schemes holds on the fibre of `f` at a field-valued point of
its target. -/
abbrev FiberHasEtaleLocalProperty {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (p : FieldValuedPoint B S hS Y) : Prop :=
  HasEtaleLocalProperty B S hS (fiberAt B S hS f p) P

/-- The field-valued point of `Y` carried by the residue field of a point `v` of a scheme
chart `g : h_V ⟶ Y` of `Y`. -/
def chartResidueFieldPoint {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) (v : V.left.1)
    (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) : FieldValuedPoint B S hS Y :=
  FieldValuedPoint.map B S hS (yoneda.obj V) g
    ⟨V.left.1.residueField v, hv, V.left.1.fromSpecResidueField v ≫ V.hom.1,
      residueFieldMap B S hS V v hv⟩

/-- The morphism out of the spectrum of the field of `chartResidueFieldPoint` is the
residue-field point of the chart followed by the chart. -/
theorem yonedaEquiv_symm_value_chartResidueFieldPoint
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (v : V.left.1) (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) :
    yonedaEquiv.symm (chartResidueFieldPoint B S hS V g v hv).value =
      yoneda.map (residueFieldMap B S hS V v hv) ≫ g := by
  have h1 : yoneda.map (residueFieldMap B S hS V v hv) =
      yonedaEquiv.symm (residueFieldMap B S hS V v hv) :=
    yonedaEquiv.eq_symm_apply.2 (yonedaEquiv_yoneda_map _)
  rw [h1]
  exact (yonedaEquiv_symm_naturality_right (residueFieldObject B S hS V v hv) g
    (residueFieldMap B S hS V v hv)).symm

/-- The fibres of `f` are locally Noetherian: the fibre over the residue field of every point
of every étale scheme chart of the target is a locally Noetherian algebraic space.

This is the every-chart reading of the standing hypothesis of Tag 0E0W, one of the equivalent
conditions of Tag 0CUW which the definition of a locally Noetherian fibre names. -/
abbrev HasLocallyNoetherianFibers {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsEtale B S hS g →
    ∀ (v : V.left.1) (hv : B.Contains (Spec (.of (V.left.1.residueField v)))),
      FiberHasEtaleLocalProperty B S hS f
        (fun T : Scheme.{u} => IsLocallyNoetherian T) (chartResidueFieldPoint B S hS V g v hv)

/-- **Stacks 0E0W.** The fibres of `f` over the points of the étale scheme chart
`g : h_V ⟶ Y` are Cohen–Macaulay algebraic spaces. -/
@[stacks 0E0W "the fibre condition on an étale scheme chart of the target"]
abbrev HasCohenMacaulayFibersOnChart {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) : Prop :=
  ∀ (v : V.left.1) (hv : B.Contains (Spec (.of (V.left.1.residueField v)))),
    FiberHasEtaleLocalProperty B S hS f
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsCohenMacaulay T)
      (chartResidueFieldPoint B S hS V g v hv)

/-! ### Comparison of the fibre of a chart square with the scheme-theoretic fibre -/

private theorem presheafEtale_isStableUnderBaseChange :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

private theorem presheafSurjective_isStableUnderBaseChange :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- An étale-local property of an algebraic space may be read off any one surjective étale
scheme chart of it. -/
private theorem hasEtaleLocalProperty_iff_of_atlas
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F)
    (hpSurjective : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    HasEtaleLocalProperty B S hS F P ↔ P ((BigFppfOver.toScheme B S hS).obj U) :=
  ⟨fun h => (exists_atlas_iff_forall_etale B S hS F P hF).mp h U p hpEtale,
    fun hU => ⟨U, p, hpSurjective, hpEtale, hU⟩⟩

/-- An étale-local property of algebraic spaces is invariant under isomorphism of
presheaves. -/
private theorem hasEtaleLocalProperty_iff_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (e : F ≅ G) :
    HasEtaleLocalProperty B S hS F P ↔ HasEtaleLocalProperty B S hS G P := by
  have hsurj := (presheafSurjective_isStableUnderBaseChange B S hS).respectsIso
  have hetale := (presheafEtale_isStableUnderBaseChange B S hS).respectsIso
  have forward {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
      HasEtaleLocalProperty B S hS F P → HasEtaleLocalProperty B S hS G P := by
    rintro ⟨U, a, haSurjective, haEtale, hP⟩
    exact ⟨U, a ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom a haSurjective,
      MorphismProperty.RespectsIso.postcomp _ e.hom a haEtale, hP⟩
  exact ⟨forward e, forward e.symm⟩

/-- The square expressing a base change of `A ⟶ S` along `T ⟶ S` as a base change of
`X ⟶ S` along `T ⟶ S`, for a factorisation `A ⟶ X ⟶ S`. -/
private lemma isPullback_lift_fst {C : Type*} [Category C] [HasPullbacks C]
    {A X Z T : C} (a : A ⟶ X) (b : X ⟶ Z) (bA : A ⟶ Z) (f : T ⟶ Z) (h : a ≫ b = bA) :
    IsPullback
      (pullback.lift (pullback.fst bA f ≫ a) (pullback.snd bA f)
        (by rw [Category.assoc, h]; exact pullback.condition))
      (pullback.fst bA f) (pullback.fst b f) a := by
  refine ⟨⟨pullback.lift_fst _ _ _⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd (c.fst ≫ pullback.snd b f) ?_
    calc
      c.snd ≫ bA = c.snd ≫ a ≫ b := by rw [← h]
      _ = c.fst ≫ pullback.fst b f ≫ b := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ b) c.condition.symm
      _ = c.fst ≫ pullback.snd b f ≫ f := by rw [pullback.condition]
    all_goals simp only [Category.assoc]
  · intro c
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst] using
        c.condition.symm
    · simp only [Category.assoc, pullback.lift_snd]
  · intro c
    exact pullback.lift_fst _ _ _
  · intro c m hm₁ hm₂
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using hm₂
    · simpa only [Category.assoc, pullback.lift_snd] using
        congrArg (fun k => k ≫ pullback.snd b f) hm₁

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The scheme atlas of the fibre of a chart square over a residue-field point of the target
chart, obtained by base change of the atlas of the whole square. -/
private def chartFiberAtlasMap (f : X ⟶ Y) (V : BigFppfOver B S hS)
    (g : yoneda.obj V ⟶ Y) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g)
    (h : U ⟶ V) (comm : a ≫ pullback.snd f g = yoneda.map h) (v : V.left.1)
    (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) :
    yoneda.obj (pullback h (residueFieldMap B S hS V v hv)) ⟶
      pullback (pullback.snd f g) (yoneda.map (residueFieldMap B S hS V v hv)) :=
  (PreservesPullback.iso yoneda h (residueFieldMap B S hS V v hv)).hom ≫
    pullback.lift
      (pullback.fst (yoneda.map h) (yoneda.map (residueFieldMap B S hS V v hv)) ≫ a)
      (pullback.snd (yoneda.map h) (yoneda.map (residueFieldMap B S hS V v hv)))
      (by rw [Category.assoc, comm]; exact pullback.condition)

private theorem chartFiberAtlas_isPullback (f : X ⟶ Y) (V : BigFppfOver B S hS)
    (g : yoneda.obj V ⟶ Y) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g)
    (h : U ⟶ V) (comm : a ≫ pullback.snd f g = yoneda.map h) (v : V.left.1)
    (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) :
    IsPullback (chartFiberAtlasMap B S hS f V g U a h comm v hv)
      (yoneda.map (pullback.fst h (residueFieldMap B S hS V v hv)))
      (pullback.fst (pullback.snd f g)
        (yoneda.map (residueFieldMap B S hS V v hv))) a := by
  set r := residueFieldMap B S hS V v hv with hrdef
  set e := PreservesPullback.iso yoneda h r with hedef
  set k := pullback.lift (pullback.fst (yoneda.map h) (yoneda.map r) ≫ a)
    (pullback.snd (yoneda.map h) (yoneda.map r))
    (by rw [Category.assoc, comm]; exact pullback.condition) with hkdef
  refine (isPullback_lift_fst a (pullback.snd f g) (yoneda.map h) (yoneda.map r) comm).of_iso
    e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ rfl rfl
  · change k = e.inv ≫ (e.hom ≫ k)
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · exact (PreservesPullback.iso_inv_fst yoneda h r).symm

private theorem chartFiberAtlas_properties (f : X ⟶ Y) (V : BigFppfOver B S hS)
    (g : yoneda.obj V ⟶ Y) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g)
    (h : U ⟶ V) (comm : a ≫ pullback.snd f g = yoneda.map h)
    (haSurjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (haEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (v : V.left.1) (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (chartFiberAtlasMap B S hS f V g U a h comm v hv) ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (chartFiberAtlasMap B S hS f V g U a h comm v hv) := by
  have _ := presheafSurjective_isStableUnderBaseChange B S hS
  have _ := presheafEtale_isStableUnderBaseChange B S hS
  have hpb := chartFiberAtlas_isPullback B S hS f V g U a h comm v hv
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip haSurjective,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip haEtale⟩

/-- **The fibre comparison.** For a commuting square of étale charts of `f` over a scheme
chart `g : h_V ⟶ Y`, presented by `h : U ⟶ V`, an étale-local property of schemes holds on
the fibre of `f` over the residue field of `v : V` exactly when it holds on the
scheme-theoretic fibre of `h` at `v`. -/
theorem hasEtaleLocalProperty_fiberAt_iff
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ pullback f g) (h : U ⟶ V)
    (comm : a ≫ pullback.snd f g = yoneda.map h)
    (haSurjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (haEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage] (v : V.left.1)
    (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) :
    FiberHasEtaleLocalProperty B S hS f P (chartResidueFieldPoint B S hS V g v hv) ↔
      P (((BigFppfOver.toScheme B S hS).map h).fiber v) := by
  set T := BigFppfOver.toScheme B S hS with hTdef
  set r := residueFieldMap B S hS V v hv with hrdef
  obtain ⟨havSurjective, havEtale⟩ :=
    chartFiberAtlas_properties B S hS f V g U a h comm haSurjective haEtale v hv
  have hFv : IsAlgebraicSpace B S hS (pullback (pullback.snd f g) (yoneda.map r)) :=
    isAlgebraicSpace_pullback B S hS (pullback.snd f g) (yoneda.map r)
      (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY)
      (isAlgebraicSpace_yoneda B S hS (residueFieldObject B S hS V v hv))
      (isAlgebraicSpace_yoneda B S hS V)
  have hAtlas := hasEtaleLocalProperty_iff_of_atlas B S hS
    (pullback (pullback.snd f g) (yoneda.map r)) P hFv (pullback h r)
    (chartFiberAtlasMap B S hS f V g U a h comm v hv) havSurjective havEtale
  have hIso := hasEtaleLocalProperty_iff_of_iso B S hS (F := pullback f (yoneda.map r ≫ g))
    (G := pullback (pullback.snd f g) (yoneda.map r)) P
    (pullbackLeftPullbackSndIso f g (yoneda.map r)).symm
  have hvalue : FiberHasEtaleLocalProperty B S hS f P (chartResidueFieldPoint B S hS V g v hv) ↔
      HasEtaleLocalProperty B S hS (pullback f (yoneda.map r ≫ g)) P :=
    hasEtaleLocalProperty_iff_of_iso B S hS P
      (pullback.congrHom (f₁ := f) rfl
        (yonedaEquiv_symm_value_chartResidueFieldPoint B S hS V g v hv))
  have eScheme : T.obj (pullback h r) ≅ (T.map h).fiber v := by
    change T.obj (pullback h r) ≅ pullback (T.map h) (V.left.1.fromSpecResidueField v)
    have hr : T.map r = V.left.1.fromSpecResidueField v := rfl
    rw [← hr]
    exact PreservesPullback.iso T h r
  refine hvalue.trans (hIso.trans (hAtlas.trans ⟨?_, ?_⟩))
  · exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso eScheme
  · exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso eScheme.symm

/-- Over any scheme chart of the target there is a surjective étale scheme chart of the base
change, presented over the target chart by a morphism of the site. -/
theorem exists_surjective_etale_atlas_over_chart
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g) (h : U ⟶ V),
      a ≫ pullback.snd f g = yoneda.map h ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a := by
  obtain ⟨U, a, haSurjective, haEtale⟩ :=
    (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY).exists_atlas
  exact ⟨U, a, yoneda.preimage (a ≫ pullback.snd f g), by simp, haSurjective, haEtale⟩

/-- The composite of a surjective étale scheme chart of the base change with the first
projection is a surjective étale scheme chart of the source. -/
theorem chartSource_property (Q : MorphismProperty Scheme.{u})
    (hQ : Q.IsStableUnderBaseChange) (hQ' : Q.IsStableUnderComposition) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS))) g)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS))) a) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS))) (a ≫ pullback.fst f g) := by
  have _ := inverseImage_isStableUnderBaseChange B S hS hQ
  have _ := inverseImage_isStableUnderComposition B S hS hQ'
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS))).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  exact MorphismProperty.comp_mem _ a (pullback.fst f g) ha
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g).flip hg)

/-! ### The equivalent conditions -/

/-- A Cohen–Macaulay morphism of algebraic spaces is flat. -/
theorem isFlat_of_isCohenMacaulay (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hcm : IsCohenMacaulay B S hS f) :
    IsFlat B S hS f :=
  ((isFlat_tfae B S hS hX hY f).out 2 1).mp fun x => (hcm x).1

/-- For a flat morphism of represented presheaves with locally Noetherian fibres,
Cohen–Macaulayness is Cohen–Macaulayness of all scheme-theoretic fibres of the underlying
morphism of schemes. -/
theorem isCohenMacaulay_yoneda_map_iff (U V : BigFppfOver B S hS) (h : U ⟶ V)
    [Flat ((BigFppfOver.toScheme B S hS).map h)]
    (hfib : ∀ v : (BigFppfOver.toScheme B S hS).obj V,
      IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber v)) :
    IsCohenMacaulay B S hS (yoneda.map h) ↔
      ∀ v : (BigFppfOver.toScheme B S hS).obj V,
        _root_.AlgebraicGeometry.IsCohenMacaulay
          (((BigFppfOver.toScheme B S hS).map h).fiber v) := by
  have key (x : (BigFppfOver.toScheme B S hS).obj U) :
      IsCohenMacaulayAt B S hS (yoneda.map h)
        ((schemePointRepresentative B S hS U x).class B S hS (yoneda.obj U)) ↔
      ((BigFppfOver.toScheme B S hS).map h).IsCohenMacaulayAt hfib x := by
    have hiff := isCohenMacaulayAt_yoneda_iff B S hS U V h hfib
      (schemePointRepresentative B S hS U x)
    rwa [schemePointRepresentative_point B S hS U x] at hiff
  constructor
  · intro hcm v
    exact ((_root_.AlgebraicGeometry.isCohenMacaulay_iff_flat_and_fibers
      ((BigFppfOver.toScheme B S hS).map h) hfib).mp fun x => (key x).mp (hcm _)).2 v
  · intro hcm
    have hcm' := (_root_.AlgebraicGeometry.isCohenMacaulay_iff_flat_and_fibers
      ((BigFppfOver.toScheme B S hS).map h) hfib).mpr ⟨inferInstance, hcm⟩
    refine fun z => Quot.inductionOn z fun p => ?_
    have h1 := (key ((BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier))).mpr (hcm' _)
    rwa [schemePointRepresentative_class B S hS U p] at h1

/-- Flatness of the morphism of schemes presenting a flat morphism of algebraic spaces over a
commuting square of étale charts. -/
theorem flat_chart_of_isFlat (f : X ⟶ Y) (hflat : IsFlat B S hS f)
    (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (hp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hq : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (comm : yoneda.map h ≫ q = p ≫ f) :
    Flat ((BigFppfOver.toScheme B S hS).map h) :=
  hflat U V p q h hp hq comm

/-- **Stacks 0E0W.** For a morphism of algebraic spaces over `S` with locally Noetherian
fibres, Cohen–Macaulayness is equivalent to flatness together with Cohen–Macaulayness of the
fibres after some, equivalently after every, étale scheme chart of the target. -/
@[stacks 0E0W "equivalence of conditions (1), (2) and (3)"]
theorem isCohenMacaulay_tfae_etaleCharts (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : HasLocallyNoetherianFibers B S hS f) :
    List.TFAE [
      IsCohenMacaulay B S hS f,
      IsFlat B S hS f ∧
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) g ∧
          IsEtale B S hS g ∧ HasCohenMacaulayFibersOnChart B S hS f V g,
      IsFlat B S hS f ∧
        ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsEtale B S hS g → HasCohenMacaulayFibersOnChart B S hS f V g] := by
  -- The data attached to one étale scheme chart `g` of the target.
  have chart (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) (hg : IsEtale B S hS g) :
      ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g) (h : U ⟶ V),
        a ≫ pullback.snd f g = yoneda.map h ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) a ∧
        (∀ v : (BigFppfOver.toScheme B S hS).obj V,
          IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber v)) ∧
        (HasCohenMacaulayFibersOnChart B S hS f V g ↔
          ∀ v : (BigFppfOver.toScheme B S hS).obj V,
            _root_.AlgebraicGeometry.IsCohenMacaulay
              (((BigFppfOver.toScheme B S hS).map h).fiber v)) := by
    obtain ⟨U, a, h, comm, haSurjective, haEtale⟩ :=
      exists_surjective_etale_atlas_over_chart B S hS hX hY f V g
    have fiber_iff (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
        (v : V.left.1) (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) :=
      hasEtaleLocalProperty_fiberAt_iff B S hS hX hY f V g U a h comm haSurjective haEtale P v hv
    refine ⟨U, a, h, comm, haSurjective, haEtale, fun v => ?_, ?_, ?_⟩
    · exact (fiber_iff (fun W : Scheme.{u} => IsLocallyNoetherian W) v
        (B.residueField_spec_contains V.left.2 v)).mp
        (hf V g hg v (B.residueField_spec_contains V.left.2 v))
    · intro hchart v
      exact (fiber_iff (fun W : Scheme.{u} => _root_.AlgebraicGeometry.IsCohenMacaulay W) v
        (B.residueField_spec_contains V.left.2 v)).mp
        (hchart v (B.residueField_spec_contains V.left.2 v))
    · intro hscheme v hv
      exact (fiber_iff (fun W : Scheme.{u} => _root_.AlgebraicGeometry.IsCohenMacaulay W) v
        hv).mpr (hscheme v)
  -- Flatness of the chart morphism, and its Cohen–Macaulayness at a point against that of `f`.
  have square (hflat : IsFlat B S hS f) (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
      (hg : IsEtale B S hS g) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g)
      (h : U ⟶ V) (comm : a ≫ pullback.snd f g = yoneda.map h)
      (haEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a) :
      Flat ((BigFppfOver.toScheme B S hS).map h) ∧
        ∀ t : FieldValuedPoint B S hS (yoneda.obj U),
          IsCohenMacaulayAt B S hS (yoneda.map h) (t.class B S hS (yoneda.obj U)) ↔
            IsCohenMacaulayAt B S hS f (pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f g)
              (t.class B S hS (yoneda.obj U))) := by
    have hgEtale := (isEtale_iff_presheaf_of_yoneda B S hS g).mp hg
    have hpEtale := chartSource_property B S hS (@Etale.{u})
      Etale.etale_isStableUnderBaseChange.{u} etale_isStableUnderComposition.{u}
      f V g hgEtale U a haEtale
    have hpcomm : (a ≫ pullback.fst f g) ≫ f = yoneda.map h ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, comm]
    exact ⟨flat_chart_of_isFlat B S hS f hflat U V (a ≫ pullback.fst f g) g h hpEtale hgEtale
        hpcomm.symm,
      fun t => isCohenMacaulayAt_chart_iff B S hS f U V (a ≫ pullback.fst f g) g h hpEtale
        hgEtale hpcomm t (IsLocalRing.closedPoint t.carrier)⟩
  tfae_have 1 → 3 := by
    intro hcm
    have hflat := isFlat_of_isCohenMacaulay B S hS hX hY f hcm
    refine ⟨hflat, fun V g hg => ?_⟩
    obtain ⟨U, a, h, comm, haSurjective, haEtale, hfib, hequiv⟩ := chart V g hg
    obtain ⟨hflatChart, hsquare⟩ := square hflat V g hg U a h comm haEtale
    refine hequiv.mpr ((isCohenMacaulay_yoneda_map_iff B S hS U V h hfib).mp ?_)
    exact fun z => Quot.inductionOn z fun t => (hsquare t).mpr (hcm _)
  tfae_have 3 → 2 := by
    rintro ⟨hflat, hcharts⟩
    obtain ⟨V, g, hgSurjective, hgEtale⟩ := hY.exists_atlas
    have hg : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).mpr hgEtale
    exact ⟨hflat, V, g, hgSurjective, hg, hcharts V g hg⟩
  tfae_have 2 → 1 := by
    rintro ⟨hflat, V, g, hgSurjective, hg, hchart⟩
    obtain ⟨U, a, h, comm, haSurjective, haEtale, hfib, hequiv⟩ := chart V g hg
    obtain ⟨hflatChart, hsquare⟩ := square hflat V g hg U a h comm haEtale
    have hpSurjective := chartSource_property B S hS (@Surjective.{u}) inferInstance
      surjective_isStableUnderComposition.{u} f V g hgSurjective U a haSurjective
    have hcmChart : IsCohenMacaulay B S hS (yoneda.map h) :=
      (isCohenMacaulay_yoneda_map_iff B S hS U V h hfib).mpr (hequiv.mp hchart)
    intro x
    obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U
      (a ≫ pullback.fst f g)).mp hpSurjective x
    rw [← hz]
    exact Quot.inductionOn z fun t => (hsquare t).mp (hcmChart _)
  tfae_finish

/-! ### Cohen–Macaulayness at a point through the étale local rings

The second half of Tag 0E0W: at a geometric point of the source, Cohen–Macaulayness is
flatness of the homomorphism of étale local rings together with Cohen–Macaulayness of its
local fibre ring. -/

section EtaleLocalRings

open IsLocalRing

/-- Being Noetherian, local and Cohen–Macaulay transports along a ring isomorphism. -/
private theorem exists_isCohenMacaulayLocalRing_iff_of_ringEquiv {A C : Type*} [CommRing A]
    [CommRing C] (e : A ≃+* C) :
    (∃ (hN : IsNoetherianRing A) (hL : IsLocalRing A), @IsCohenMacaulayLocalRing A _ hN hL) ↔
      (∃ (hN : IsNoetherianRing C) (hL : IsLocalRing C),
        @IsCohenMacaulayLocalRing C _ hN hL) := by
  constructor
  · rintro ⟨hN, hL, hCM⟩
    have := isNoetherianRing_of_ringEquiv A e
    have := RingEquiv.isLocalRing e
    exact ⟨inferInstance, inferInstance, (isCohenMacaulayLocalRing_iff_of_ringEquiv e).mp hCM⟩
  · rintro ⟨hN, hL, hCM⟩
    have := isNoetherianRing_of_ringEquiv C e.symm
    have := RingEquiv.isLocalRing e.symm
    exact ⟨inferInstance, inferInstance, (isCohenMacaulayLocalRing_iff_of_ringEquiv e).mpr hCM⟩

/-- Being Noetherian, local and Cohen–Macaulay for the quotient of a local ring by an ideal
inside its maximal ideal is unchanged on passing to a strict henselization: by Stacks 05WS the
quotient of the strict henselization is a strict henselization of the quotient, and by
Stacks 06LM maximal Cohen–Macaulayness ascends and descends along a strict henselization. -/
@[ega "IV 18.8.13" "more general"]
private theorem exists_isCohenMacaulayLocalRing_quotient_strictHenselization_iff
    {R : Type u} [CommRing R] [IsLocalRing R] (L : Type u) [Field L] [Algebra (ResidueField R) L]
    [IsSepClosure (ResidueField R) L] (T : HenselizationTower R L) (I : Ideal R)
    (hI : I ≤ maximalIdeal R) :
    (∃ (hN : IsNoetherianRing (R ⧸ I)) (hL : IsLocalRing (R ⧸ I)),
      @IsCohenMacaulayLocalRing (R ⧸ I) _ hN hL) ↔
    (∃ (hN : IsNoetherianRing
          (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization)))
        (hL : IsLocalRing (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization))),
      @IsCohenMacaulayLocalRing
        (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization)) _ hN hL) := by
  have : IsLocalHom (algebraMap R T.strictHenselization) := IsHenselization.isLocalHom (L := L)
  have : HenselianLocalRing T.strictHenselization := IsHenselization.henselian (R := R) (L := L)
  obtain ⟨a, _, hsep, hres⟩ :=
    IsHenselization.exists_residueFieldAlgebra (R := R) (L := L) (Rh := T.strictHenselization)
  have halg : a = ResidueField.instAlgebra (R := R) (S := T.strictHenselization) := by
    refine Algebra.algebra_ext _ _ fun z => ?_
    obtain ⟨r, rfl⟩ := residue_surjective z
    exact (hres r).trans (ResidueField.algebraMap_residue (S := T.strictHenselization) r).symm
  subst halg
  have : IsSepClosure (ResidueField R) (ResidueField T.strictHenselization) := hsep inferInstance
  obtain ⟨hQ, hAQ, _, hhens, hind, _, hsepQ⟩ :=
    IsLocalRing.strictHenselization_quotient (R := R) (Rsh := T.strictHenselization)
      (IsHenselization.ind_etale_of_universe_le.{u, u, u} L)
      (IsHenselization.map_maximalIdeal (R := R) (L := L) (Rh := T.strictHenselization)) I hI
  have hH : IsHenselization (R ⧸ I)
      (ResidueField (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization)))
      (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization)) :=
    IsHenselization.of_ind_etale hhens hind
      ⟨RingEquiv.refl _, ResidueField.algebraMap_residue⟩
  have hnoeth := (isNoetherianRing_iff_henselizations (R ⧸ I)
    (henselizationTower (R ⧸ I)
        (ResidueField (T.strictHenselization ⧸
          I.map (algebraMap R T.strictHenselization)))).henselization
    (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization))
    (ResidueField (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization)))).2
  have hmcm [IsNoetherianRing (R ⧸ I)] := (isMaximalCohenMacaulay_iff_henselizations (R ⧸ I)
    (henselizationTower (R ⧸ I)
        (ResidueField (T.strictHenselization ⧸
          I.map (algebraMap R T.strictHenselization)))).henselization
    (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization))
    (ResidueField (T.strictHenselization ⧸ I.map (algebraMap R T.strictHenselization)))).2
  constructor
  · rintro ⟨hN, _, hCM⟩
    have := hN
    have := hnoeth.mp hN
    exact ⟨inferInstance, inferInstance, (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mpr
      (hmcm.mp ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mp hCM))⟩
  · rintro ⟨hN, _, hCM⟩
    have := hN
    have := hnoeth.mpr hN
    exact ⟨inferInstance, inferInstance, (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mpr
      (hmcm.mpr ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mp hCM))⟩

/-- A commuting square of local rings whose horizontal arrows are the structure maps to chosen
strict henselizations, followed by chosen identifications of those, identifies the quotient of
the strict henselization of the source by the extended maximal ideal of the target with the
corresponding quotient on the right-hand side. -/
theorem nonempty_quotient_maximalIdeal_map_ringEquiv {R A : Type u} [CommRing R]
    [IsLocalRing R] [CommRing A] [IsLocalRing A] (LR LA : Type u) [Field LR] [Field LA]
    [Algebra (ResidueField R) LR] [IsSepClosure (ResidueField R) LR]
    [Algebra (ResidueField A) LA] [IsSepClosure (ResidueField A) LA]
    (TR : HenselizationTower R LR) (TA : HenselizationTower A LA)
    {R' A' : Type*} [CommRing R'] [IsLocalRing R'] [CommRing A']
    (eR : TR.strictHenselization ≃+* R') (eA : TA.strictHenselization ≃+* A')
    (g : R →+* A) (φ : R' →+* A')
    (hcomm : φ.comp (eR.toRingHom.comp (algebraMap R TR.strictHenselization)) =
      eA.toRingHom.comp ((algebraMap A TA.strictHenselization).comp g)) :
    Nonempty ((TA.strictHenselization ⧸
      ((maximalIdeal R).map g).map (algebraMap A TA.strictHenselization)) ≃+*
        (A' ⧸ (maximalIdeal R').map φ)) := by
  have hmax : (maximalIdeal R').map φ =
      (((maximalIdeal R).map g).map (algebraMap A TA.strictHenselization)).map eA := by
    rw [← map_ringEquiv_maximalIdeal eR,
      ← IsHenselization.map_maximalIdeal (R := R) (L := LR) (Rh := TR.strictHenselization)]
    change (((maximalIdeal R).map (algebraMap R TR.strictHenselization)).map
        eR.toRingHom).map φ =
      (((maximalIdeal R).map g).map (algebraMap A TA.strictHenselization)).map eA.toRingHom
    simp only [Ideal.map_map]
    rw [hcomm]
  exact ⟨Ideal.quotientEquiv _ _ eA hmax⟩

/-- The commuting square of a stalk map of a morphism of schemes with affine target against
chosen strict henselizations of the two local rings and chosen identifications of those: it is
pinned down by the germs of global sections of the target, since those generate its local
ring. -/
theorem apply_algebraMap_strictHenselization_eq {Z W : Scheme.{u}} [IsAffine W]
    (q : Z ⟶ W) (z : Z) {K L : Type u} [Field K]
    [Algebra (ResidueField (W.presheaf.stalk (q z))) K]
    [IsSepClosure (ResidueField (W.presheaf.stalk (q z))) K] [Field L]
    [Algebra (ResidueField (Z.presheaf.stalk z)) L]
    [IsSepClosure (ResidueField (Z.presheaf.stalk z)) L]
    (T : HenselizationTower (W.presheaf.stalk (q z)) K)
    (U : HenselizationTower (Z.presheaf.stalk z) L) {C D : Type*} [CommRing C] [CommRing D]
    (eW : T.strictHenselization ≃+* C) (eZ : U.strictHenselization ≃+* D) (φ : C →+* D)
    (hc : ∀ a : Γ(W, ⊤),
      φ (eW (algebraMap _ T.strictHenselization (W.presheaf.germ ⊤ (q z) trivial a))) =
        eZ (algebraMap _ U.strictHenselization
          (Z.presheaf.germ ⊤ z trivial ((Scheme.Γ.map q.op).hom a)))) :
    ∀ b : W.presheaf.stalk (q z), φ (eW (algebraMap _ T.strictHenselization b)) =
      eZ (algebraMap _ U.strictHenselization ((q.stalkMap z).hom b)) := by
  have hs : (eZ.symm.toRingHom.comp (φ.comp eW.toRingHom)).comp
      (algebraMap _ T.strictHenselization) =
      (algebraMap _ U.strictHenselization).comp (q.stalkMap z).hom := by
    let _ : Algebra Γ(W, ⊤) (W.presheaf.stalk (q z)) :=
      TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨q z, trivial⟩ : (⊤ : W.Opens))
    have := (isAffineOpen_top W).isLocalization_stalk (⟨q z, trivial⟩ : (⊤ : W.Opens))
    apply IsLocalization.ringHom_ext
      ((isAffineOpen_top W).primeIdealOf ⟨q z, trivial⟩).asIdeal.primeCompl
    ext a
    change eZ.symm (φ (eW (algebraMap _ T.strictHenselization
      (W.presheaf.germ ⊤ (q z) trivial a)))) = _
    rw [hc, RingEquiv.symm_apply_apply]
    exact congrArg (algebraMap _ U.strictHenselization)
      (q.germ_stalkMap_apply ⊤ z trivial a).symm
  intro b
  have h := congrArg
    (fun k : (W.presheaf.stalk (q z)) →+* U.strictHenselization => k b) hs
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  exact eZ.symm.injective (by simpa using h)

/-- Cohen–Macaulayness of the fibre local ring of a morphism of schemes with affine target at a
point of its source, read through chosen strict henselizations of the two local rings and
chosen identifications of those: it is Cohen–Macaulayness of the quotient of the right-hand
identification of the source by the extended maximal ideal of the target. -/
private theorem exists_isCohenMacaulayLocalRing_fiberStalk_iff {Z W : Scheme.{u}} [IsAffine W]
    (q : Z ⟶ W) (z : Z) (w : W) (hzw : q z = w) {K L : Type u} [Field K]
    [Algebra (ResidueField (W.presheaf.stalk w)) K]
    [IsSepClosure (ResidueField (W.presheaf.stalk w)) K] [Field L]
    [Algebra (ResidueField (Z.presheaf.stalk z)) L]
    [IsSepClosure (ResidueField (Z.presheaf.stalk z)) L]
    (T : HenselizationTower (W.presheaf.stalk w) K)
    (U : HenselizationTower (Z.presheaf.stalk z) L) {C D : Type*} [CommRing C] [IsLocalRing C]
    [CommRing D] (eW : T.strictHenselization ≃+* C) (eZ : U.strictHenselization ≃+* D)
    (φ : C →+* D)
    (hc : ∀ a : Γ(W, ⊤),
      φ (eW (algebraMap _ T.strictHenselization (W.presheaf.germ ⊤ w trivial a))) =
        eZ (algebraMap _ U.strictHenselization
          (Z.presheaf.germ ⊤ z trivial ((Scheme.Γ.map q.op).hom a)))) :
    (∃ hN : IsNoetherianRing ((q.fiber (q z)).presheaf.stalk (q.asFiber z)),
      @IsCohenMacaulayLocalRing ((q.fiber (q z)).presheaf.stalk (q.asFiber z)) _ hN _) ↔
    (∃ (hN : IsNoetherianRing (D ⧸ (maximalIdeal C).map φ))
        (hL : IsLocalRing (D ⧸ (maximalIdeal C).map φ)),
      @IsCohenMacaulayLocalRing (D ⧸ (maximalIdeal C).map φ) _ hN hL) := by
  subst hzw
  obtain ⟨e⟩ := nonempty_quotient_maximalIdeal_map_ringEquiv K L T U eW eZ
    (q.stalkMap z).hom φ
    (RingHom.ext (apply_algebraMap_strictHenselization_eq q z T U eW eZ φ hc))
  have hlocal : IsLocalHom (q.stalkMap z).hom := q.toLRSHom.prop z
  have hI : (maximalIdeal (W.presheaf.stalk (q z))).map (q.stalkMap z).hom ≤
      maximalIdeal (Z.presheaf.stalk z) := map_maximalIdeal_le (q.stalkMap z).hom
  refine Iff.trans ?_
    ((exists_isCohenMacaulayLocalRing_iff_of_ringEquiv
      (quotientStalkEquivFiberStalk q z)).symm.trans
      ((exists_isCohenMacaulayLocalRing_quotient_strictHenselization_iff L U _ hI).trans
        (exists_isCohenMacaulayLocalRing_iff_of_ringEquiv e)))
  exact ⟨fun h => ⟨h.1, inferInstance, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-! ### Compatible pointed étale charts over a morphism -/

/-- Transport of the value of a field-valued point along the equality of site objects induced
by an equality of its images. -/
theorem fieldValuedPoint_map_value_eq
    {A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : A ⟶ C) (p : FieldValuedPoint B S hS A)
    (q : FieldValuedPoint B S hS C)
    (hsite : Opposite.op p.siteObject = Opposite.op q.siteObject)
    (h : FieldValuedPoint.map B S hS A α p = q) :
    hsite ▸ α.app (Opposite.op p.siteObject) p.value = q.value := by
  have hv : HEq (α.app (Opposite.op p.siteObject) p.value) q.value := by
    cases h
    rfl
  exact eq_of_heq ((eqRec_heq hsite _).trans hv)

/-- The action of a presheaf on an `eqToHom` is transport along the underlying equality. -/
theorem map_eqToHom_eq_cast {C : Type*} [Category C] {A : Cᵒᵖ ⥤ Type u}
    {D E : Cᵒᵖ} (h : D = E) (a : A.obj D) : A.map (eqToHom h) a = h ▸ a := by
  rw [eqToHom_map]
  cases h
  rfl

/-- A geometric point lifts along a surjective étale scheme chart without extending its
field: the lift of the underlying point of Tag 05VN already has the same field of
definition. -/
theorem exists_point_lift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F)
    (haSurjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (haEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a) :
    ∃ p : x.val.siteObject ⟶ U, a.app (Opposite.op x.val.siteObject) p = x.val.value := by
  obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U a).mp haSurjective x.image
  obtain ⟨xU, -, hxU⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hF a
    ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr haEtale) x z hz
  have hsite : Opposite.op xU.val.siteObject = Opposite.op x.val.siteObject :=
    congrArg Opposite.op
      (congrArg (fun w : FieldValuedPoint B S hS F => w.siteObject) hxU)
  refine ⟨(yoneda.obj U).map (eqToHom hsite) xU.val.value, ?_⟩
  calc
    a.app (Opposite.op x.val.siteObject)
          ((yoneda.obj U).map (eqToHom hsite) xU.val.value) =
        F.map (eqToHom hsite) (a.app (Opposite.op xU.val.siteObject) xU.val.value) := by
      simpa only [types_comp_apply] using
        congrArg (fun k => k xU.val.value) (a.naturality (eqToHom hsite))
    _ = x.val.value := (map_eqToHom_eq_cast hsite _).trans
      (fieldValuedPoint_map_value_eq B S hS a xU.val x.val hsite hxU)

/-- A point of a chart of the source, sent to a point of the source, goes to the point of the
target obtained by following the commuting square of charts. -/
private theorem app_comp_eq_of_square {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    {U V W : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (g : U ⟶ V)
    (hcomm : a ≫ f = yoneda.map g ≫ b) (p : W ⟶ U) (z : F.obj (Opposite.op W))
    (hp : a.app (Opposite.op W) p = z) :
    b.app (Opposite.op W) (p ≫ g) = f.app (Opposite.op W) z := by
  have hc := congrArg (fun k : yoneda.obj U ⟶ G => k.app _ p) hcomm
  change f.app _ (a.app _ p) = b.app _ (p ≫ g) at hc
  exact hc.symm.trans (congrArg (f.app _) hp)

/-- Over a morphism of algebraic spaces there is a commuting square of pointed étale scheme
charts at any prescribed geometric point of the source: a surjective étale chart of the target
lifts, by Tag 02X1, to one of the source, and the geometric point lifts to the latter. -/
public theorem exists_compatible_chart_square (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : GeometricPoint B S hS X) :
    ∃ (U : SmallEtaleNeighborhood x) (V : SmallEtaleNeighborhood (geometricPointMap f x))
      (g : U.chart.obj.left ⟶ V.chart.obj.left),
      U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom ∧ U.point ≫ g = V.point := by
  obtain ⟨V, b, hbSurjective, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, g, hcomm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurjective hbEtale
  obtain ⟨p, hp⟩ := exists_point_lift B S hS X hX x a haSurjective haEtale
  refine ⟨⟨⟨CostructuredArrow.mk a, haEtale⟩, p, hp⟩,
    ⟨⟨CostructuredArrow.mk b, hbEtale⟩, p ≫ g, ?_⟩, g, hcomm, rfl⟩
  exact app_comp_eq_of_square B S hS f a b g hcomm p _ hp

/-- The square of pointed étale scheme charts can in addition be taken with affine chart of
the target: restrict the chart of the target to an affine open around the image point and the
chart of the source to its preimage. Both restrictions are open immersions, hence étale, so
the restricted charts are again étale charts, and the lift of the geometric point factors
through the restricted chart of the source. -/
theorem exists_compatible_affine_chart_square (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : GeometricPoint B S hS X) :
    ∃ (U : SmallEtaleNeighborhood x) (V : SmallEtaleNeighborhood (geometricPointMap f x))
      (g : U.chart.obj.left ⟶ V.chart.obj.left),
      U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom ∧ U.point ≫ g = V.point ∧
      IsAffine (chartScheme V.chart) := by
  obtain ⟨U, V, g, hcomm, hpoint⟩ := exists_compatible_chart_square B S hS hX hY f x
  set C := BigFppfOver.toScheme B S hS with hC
  obtain ⟨W, hW, hv, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := chartScheme V.chart) (x := (C.map V.point) (IsLocalRing.closedPoint x.val.carrier))
    (U := ⊤) trivial
  set Z := (C.map g) ⁻¹ᵁ W with hZ
  set UW : BigFppfOver B S hS :=
    Over.mk (show B.obj (Scheme.size_lt_of_isOpenImmersion Z.ι
      U.chart.obj.left.left.property) ⟶ B.obj hS from ⟨Z.ι ≫ U.chart.obj.left.hom.1⟩) with hUW
  set VW : BigFppfOver B S hS :=
    Over.mk (show B.obj (Scheme.size_lt_of_isOpenImmersion W.ι
      V.chart.obj.left.left.property) ⟶ B.obj hS from ⟨W.ι ≫ V.chart.obj.left.hom.1⟩) with hVW
  set iU : UW ⟶ U.chart.obj.left := Over.homMk ⟨Z.ι⟩ with hiU
  set iV : VW ⟶ V.chart.obj.left := Over.homMk ⟨W.ι⟩ with hiV
  set gW : UW ⟶ VW := Over.homMk ⟨(C.map g) ∣_ W⟩ (by
    apply B.inclusion.map_injective
    change (C.map g ∣_ W) ≫ (W.ι ≫ V.chart.obj.left.hom.1) = Z.ι ≫ U.chart.obj.left.hom.1
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    congr 1
    exact congrArg B.inclusion.map g.w) with hgW
  have hsquare : gW ≫ iV = iU ≫ g :=
    Over.OverMorphism.ext (B.inclusion.map_injective (morphismRestrict_ι (C.map g) W))
  have hrange : Set.range (C.map U.point) ⊆ Set.range Z.ι := by
    rintro _ ⟨t, rfl⟩
    refine ⟨⟨C.map U.point t, ?_⟩, rfl⟩
    change C.map g (C.map U.point t) ∈ W
    rw [← Scheme.Hom.comp_apply, ← C.map_comp, hpoint]
    have ht : t = IsLocalRing.closedPoint x.val.carrier := by
      change (_ : Spec (.of x.val.carrier)) = _
      exact Subsingleton.elim _ _
    rw [ht]
    exact hv
  set q' : x.val.siteObject ⟶ UW :=
    Over.homMk ⟨IsOpenImmersion.lift Z.ι (C.map U.point) hrange⟩ (by
      apply B.inclusion.map_injective
      change IsOpenImmersion.lift Z.ι (C.map U.point) hrange ≫
        (Z.ι ≫ U.chart.obj.left.hom.1) = x.val.toBase
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact congrArg B.inclusion.map U.point.w) with hq'
  have hq : q' ≫ iU = U.point :=
    Over.OverMorphism.ext (B.inclusion.map_injective (IsOpenImmersion.lift_fac _ _ _))
  have haW : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      C).presheaf (yoneda.map iU ≫ U.chart.obj.hom) :=
    etale_comp_of_scheme B S hS iU U.chart.obj.hom (show Etale Z.ι from inferInstance)
      U.chart.property
  have hbW : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      C).presheaf (yoneda.map iV ≫ V.chart.obj.hom) :=
    etale_comp_of_scheme B S hS iV V.chart.obj.hom (show Etale W.ι from inferInstance)
      V.chart.property
  have hcommW : (yoneda.map iU ≫ U.chart.obj.hom) ≫ f =
      yoneda.map gW ≫ (yoneda.map iV ≫ V.chart.obj.hom) := by
    rw [Category.assoc, hcomm, ← Category.assoc, ← yoneda.map_comp, ← hsquare,
      yoneda.map_comp, Category.assoc]
  have hqa : (yoneda.map iU ≫ U.chart.obj.hom).app (Opposite.op x.val.siteObject) q' =
      x.val.value := by
    change U.chart.obj.hom.app _ (q' ≫ iU) = x.val.value
    rw [hq]
    exact U.point_comp
  refine ⟨⟨⟨CostructuredArrow.mk (yoneda.map iU ≫ U.chart.obj.hom), haW⟩, q', hqa⟩,
    ⟨⟨CostructuredArrow.mk (yoneda.map iV ≫ V.chart.obj.hom), hbW⟩, q' ≫ gW, ?_⟩,
    gW, hcommW, rfl, hW⟩
  exact app_comp_eq_of_square B S hS f _ _ gW hcommW q' _ hqa

/-! ### The criterion on étale local rings -/

/-- The ideal of the étale local ring of the source at a geometric point generated by the
maximal ideal of the étale local ring of the target at its image. The quotient by it is the
local ring of the fibre. -/
def etaleLocalFiberIdeal (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : GeometricPoint B S hS X) :
    Ideal (etaleLocalRing B S hS X x) :=
  letI : IsLocalRing (etaleLocalRing B S hS Y (geometricPointMap f x)) :=
    isLocalRing_etaleLocalRing B S hS Y hY (geometricPointMap f x)
  (maximalIdeal (etaleLocalRing B S hS Y (geometricPointMap f x))).map
    (etaleLocalRingMap hX f x)

/-- **Stacks 0E0W.** A morphism of algebraic spaces over `S` is Cohen–Macaulay at the image of
a geometric point `x` of its source exactly when the canonical homomorphism of étale local
rings at `x` is flat and its local fibre ring is Noetherian, local and Cohen–Macaulay. -/
@[stacks 0E0W "equivalence of conditions (a) and (b)"]
theorem isCohenMacaulayAt_iff_etaleLocalRingMap (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : GeometricPoint B S hS X) :
    IsCohenMacaulayAt B S hS f x.image ↔
      ((etaleLocalRingMap hX f x).Flat ∧
        ∃ (hN : IsNoetherianRing
            (etaleLocalRing B S hS X x ⧸ etaleLocalFiberIdeal B S hS hX hY f x))
          (hL : IsLocalRing
            (etaleLocalRing B S hS X x ⧸ etaleLocalFiberIdeal B S hS hX hY f x)),
          @IsCohenMacaulayLocalRing
            (etaleLocalRing B S hS X x ⧸ etaleLocalFiberIdeal B S hS hX hY f x) _ hN hL) := by
  refine and_congr (isFlatAt_iff_etaleLocalRingMap_flat hX hY f x) ?_
  obtain ⟨U, V, g, hcomm, hpoint, hVaffine⟩ :=
    exists_compatible_affine_chart_square B S hS hX hY f x
  have _ : IsAffine (chartScheme V.chart) := hVaffine
  set q : chartScheme U.chart ⟶ chartScheme V.chart := (BigFppfOver.toScheme B S hS).map g
    with hq
  set u := (chartGeometricPoint U).hom (IsLocalRing.closedPoint
    (chartGeometricPoint U).residueField) with hu
  set v := (chartGeometricPoint V).hom (IsLocalRing.closedPoint
    (chartGeometricPoint V).residueField) with hv
  have huv : q u = v := congrArg
    (fun k => ((BigFppfOver.toScheme B S hS).map k)
      (show (BigFppfOver.toScheme B S hS).obj x.val.siteObject from
        IsLocalRing.closedPoint x.val.carrier)) hpoint
  set p : FieldValuedPoint B S hS (yoneda.obj U.chart.obj.left) :=
    { carrier := x.val.carrier
      contained := x.val.contained
      toBase := x.val.toBase
      value := U.point } with hp
  have hmap : FieldValuedPoint.map B S hS _ U.chart.obj.hom p = x.val :=
    congrArg (fun z : X.obj (Opposite.op x.val.siteObject) => { x.val with value := z })
      U.point_comp
  set c : EtaleChartAtPoint B S hS f x.image :=
    { U := U.chart.obj.left
      V := V.chart.obj.left
      a := U.chart.obj.hom
      b := V.chart.obj.hom
      h := g
      a_etale := U.chart.property
      b_etale := V.chart.property
      comm := hcomm.symm
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := congrArg (FieldValuedPoint.class B S hS X) hmap } with hc
  have hchart : HoldsOnEveryEtaleChartAtPoint B S hS
      (@_root_.AlgebraicGeometry.HasCohenMacaulayFiberLocalRing.{u}) f x.image ↔
      _root_.AlgebraicGeometry.HasCohenMacaulayFiberLocalRing
        (MorphismOfGerms.ofSchemeHom q u) := by
    refine ⟨fun h => h c, fun h => ?_⟩
    refine (holdsOnEveryEtaleChartAtPoint_iff_some B S hS
      (@_root_.AlgebraicGeometry.HasCohenMacaulayFiberLocalRing.{u})
      _root_.AlgebraicGeometry.hasCohenMacaulayFiberLocalRing_isEtaleLocalOnSourceAndTarget
      hX hY f x.image).mpr ⟨c, h⟩
  rw [hchart, _root_.AlgebraicGeometry.hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff]
  have _ : IsLocalRing (etaleLocalRing B S hS Y (geometricPointMap f x)) :=
    isLocalRing_etaleLocalRing B S hS Y hY (geometricPointMap f x)
  set E := bigEtaleSiteOfFppfSite B with hE
  set TU := henselizationTower ((chartScheme U.chart).presheaf.stalk u)
    (separableClosure (ResidueField ((chartScheme U.chart).presheaf.stalk u))
      (chartGeometricPoint U).residueField) with hTU
  set TV := henselizationTower ((chartScheme V.chart).presheaf.stalk v)
    (separableClosure (ResidueField ((chartScheme V.chart).presheaf.stalk v))
      (chartGeometricPoint V).residueField) with hTV
  refine exists_isCohenMacaulayLocalRing_fiberStalk_iff q u v huv TV TU
    (strictHenselizationEquivEtaleLocalRing hY V E V.chart.obj.left.left.property TV)
    (strictHenselizationEquivEtaleLocalRing hX U E U.chart.obj.left.left.property TU)
    (etaleLocalRingMap hX f x) ?_
  intro a
  calc
    _ = (etaleLocalRingMap hX f x)
        (etaleLocalRingGerm B S hS Y (geometricPointMap f x) (Opposite.op V) a) :=
      congrArg _ (strictHenselizationEquivEtaleLocalRing_germ hY V E
        V.chart.obj.left.left.property TV a)
    _ = etaleLocalRingGerm B S hS X x (Opposite.op U) ((Scheme.Γ.map q.op).hom a) :=
      (congrArg (fun k => k a)
        (etaleLocalRingMap_isEtaleLocalRingMap hX f x U V g hcomm hpoint)).symm
    _ = _ := (strictHenselizationEquivEtaleLocalRing_germ hX U E
      U.chart.obj.left.left.property TU ((Scheme.Γ.map q.op).hom a)).symm

end EtaleLocalRings

end AlgebraicGeometry.Space

end
