module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SingletonChartFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints

/-!
# The fibre of a morphism of algebraic spaces over a field-valued point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `p` be a
field-valued point of `Y`, presenting a point `y` of `|Y|` by a morphism `Spec k ⟶ Y` which
is a quasi-compact monomorphism. Stacks 0AC8 says that the fibre `X_k = X ×_Y Spec k` has
point space the set-theoretic fibre `|f|^{-1}(\{y\})` with its subspace topology.

The set-theoretic halves of that statement — that `|X_k| → |X|` has image the fibre and is
injective — are
`AlgebraicGeometry.Space.range_pointsMap_fibre_fieldMorphism` and
`AlgebraicGeometry.Space.injective_pointsMap_fibre_fieldMorphism`. This file supplies the
topological half and assembles the homeomorphism.

## Main results

* `AlgebraicGeometry.Space.exists_fieldValuedPoint_presheafPreimmersion`: every point of a
  represented presheaf is presented by a field-valued point whose presenting morphism is a
  preimmersion after every represented base change, namely by the residue field there.
* `AlgebraicGeometry.Space.isInducing_pointsMap_of_isInducing_snd`: the map on points of a
  relatively representable morphism into an algebraic space is topologically inducing as soon
  as its represented base changes are.
* `AlgebraicGeometry.Space.isInducing_pointsMap_fibre_fieldMorphism` and
  `AlgebraicGeometry.Space.isEmbedding_pointsMap_fibre_fieldMorphism`: the map
  `|X_k| → |X|` is inducing, hence a topological embedding.
* `AlgebraicGeometry.Space.fibreHomeomorph`: the resulting homeomorphism of `|X_k|` onto the
  set-theoretic fibre of `|f|` above the point presented by `p`.

## Implementation notes

The point topology `AlgebraicGeometry.Space.pointTopology` is installed as a local instance,
as elsewhere in this directory.

`AlgebraicGeometry.Space.isInducing_of_isInducing_of_isOpenMap_comm` is the point-set topology
the argument runs on. In a commuting square whose left-hand map is inducing, whose bottom map
is open, whose top map is a continuous surjection and whose right-hand map is a continuous
injection, the right-hand map is inducing as soon as the image of the left-hand map is the
preimage along the bottom map of the image of the right-hand one. Every open set of the source
is then transported across the square and pushed forward along the open map.

The square the source's argument supplies is the one attached to an étale chart `V ⟶ Y` with
*exactly one* point `v` above `y`, which is
`AlgebraicGeometry.Space.exists_etale_chart_singleton_fibre_of_isQuasiCompact_fieldMorphism`.
Its bottom map is `|X ×_Y V| → |X|`, open because a base change of an étale morphism is étale;
its left-hand map is `|X ×_Y Spec κ(v)| → |X ×_Y V|`, inducing because `Spec κ(v) ⟶ V` is a
preimmersion and preimmersions are stable under base change; and the image of the left-hand map
is the set of points above `v`, which is the preimage of the fibre above `y` *because `v` is
the only point of the chart there*. The top map `X ×_Y Spec κ(v) ⟶ X ×_Y Spec k` exists because
a field-valued point of `Y` carried to `y` factors through the monomorphism presenting `y`,
which is Stacks 0H2X; it is surjective on points by Stacks 03H4 together with injectivity of
`|X_k| → |X|`.

Only `AlgebraicGeometry.Space.isInducing_pointsMap_of_isInducing_snd` uses an étale atlas of
the target, and it is the sole descent step: the remaining comparisons are between a presheaf
and a representable one, where the point topology is the Zariski topology of the representing
scheme by Stacks 03BX.

## References

* [Stacks Project, Tag 01K1](https://stacks.math.columbia.edu/tag/01K1)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The point-set topology of the argument -/

/-- A map `c` is inducing if it is covered by a continuous surjection `t` and an inducing map `r`
through an open map `g`, with every point `g a' = c w` lifting to a pair `r a = a'`, `t a = w`. -/
private theorem isInducing_of_isOpenMap_of_forall_lift {A A' C D : Type*} [TopologicalSpace A]
    [TopologicalSpace A'] [TopologicalSpace C] [TopologicalSpace D] {c : C → D} {g : A' → D}
    {r : A → A'} {t : A → C} (hc : Continuous c) (ht : Continuous t)
    (htsurj : Function.Surjective t) (hg : IsOpenMap g) (hr : Topology.IsInducing r)
    (hcomm : ∀ a, c (t a) = g (r a))
    (hlift : ∀ a' w, g a' = c w → ∃ a, r a = a' ∧ t a = w) : Topology.IsInducing c := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp hc) fun O hO ↦ ?_⟩
  rw [isOpen_induced_iff]
  obtain ⟨O', hO', hO'eq⟩ := hr.isOpen_iff.mp (hO.preimage ht)
  refine ⟨g '' O', hg _ hO', ?_⟩
  ext w
  constructor
  · rintro ⟨z, hzO', hz⟩
    obtain ⟨a, rfl, rfl⟩ := hlift z w hz
    exact hO'eq.subset hzO'
  · intro hwO
    obtain ⟨a, rfl⟩ := htsurj w
    exact ⟨r a, hO'eq.symm.subset hwO, (hcomm a).symm⟩

/-- A continuous injection is inducing as soon as it is covered by an inducing map through an
open map.

Precisely: in a commuting square `c ∘ t = g ∘ r` with `r` inducing, `g` open, `t` a continuous
surjection and `c` a continuous injection whose image pulls back along `g` to the image of `r`,
the map `c` is inducing. -/
theorem isInducing_of_isInducing_of_isOpenMap_comm {A A' C D : Type*} [TopologicalSpace A]
    [TopologicalSpace A'] [TopologicalSpace C] [TopologicalSpace D] {c : C → D} {g : A' → D}
    {r : A → A'} {t : A → C} (hc : Continuous c) (hcinj : Function.Injective c)
    (ht : Continuous t) (htsurj : Function.Surjective t) (hg : IsOpenMap g)
    (hr : Topology.IsInducing r)
    (hrange : Set.range r = g ⁻¹' Set.range c) (hcomm : ∀ a, c (t a) = g (r a)) :
    Topology.IsInducing c := by
  refine isInducing_of_isOpenMap_of_forall_lift hc ht htsurj hg hr hcomm fun a' w h ↦ ?_
  obtain ⟨a, rfl⟩ : a' ∈ Set.range r := by
    rw [hrange]
    exact ⟨w, h.symm⟩
  exact ⟨a, rfl, hcinj ((hcomm a).trans h)⟩

/-! ### The residue field at a point as an object of the site -/

variable (B : BigFppfSite.{u})

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- Every point of a represented presheaf on the big fppf site of `S` is presented by a
field-valued point whose presenting morphism is a preimmersion after every represented base
change, namely by the residue field at the corresponding point of the representing scheme. -/
theorem exists_fieldValuedPoint_presheafPreimmersion (V : BigFppfOver B S hS)
    (v : points B S hS (yoneda.obj V)) :
    ∃ q : FieldValuedPoint B S hS (yoneda.obj V),
      q.class B S hS (yoneda.obj V) = v ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsPreimmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
          (fieldMorphism B S hS (yoneda.obj V) q) := by
  have hκ : B.Contains (Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj V).residueField
      (pointsToScheme B S hS V v)))) :=
    B.residueField_spec_contains V.left.2 (pointsToScheme B S hS V v)
  let fr : Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj V).residueField
      (pointsToScheme B S hS V v))) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    ((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField (pointsToScheme B S hS V v)
  let m : (Over.mk (⟨fr ≫ V.hom.hom⟩ : B.obj hκ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V :=
    Over.homMk (⟨fr⟩ : B.obj hκ ⟶ V.left) (by ext; rfl)
  have hm : (BigFppfOver.toScheme B S hS).map m = fr := rfl
  refine ⟨{ carrier := ↥(((BigFppfOver.toScheme B S hS).obj V).residueField
              (pointsToScheme B S hS V v))
            contained := hκ
            toBase := fr ≫ V.hom.hom
            value := m }, ?_, ?_⟩
  · exact injective_pointsToScheme B S hS V
      (((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField_apply
        (pointsToScheme B S hS V v) _)
  · rw [fieldMorphism_yoneda]
    refine presheaf_yoneda_map_of_inverseImage B S hS ?_ m ?_
    · infer_instance
    · rw [hm]
      infer_instance

/-! ### Descent of the inducing property to the point space -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site times out otherwise
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_fibreOverFieldPoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_fibreOverFieldPoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of the big fppf site of `S` whose underlying map of schemes is topologically
inducing induces an inducing map on points. -/
theorem isInducing_pointsMap_yoneda {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : Topology.IsInducing ⇑((BigFppfOver.toScheme B S hS).map h)) :
    Topology.IsInducing (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) := by
  rw [pointsMap_yoneda_eq_conj]
  exact (schemePointsHomeomorph B S hS V).symm.isEmbedding.isInducing.comp
    (hh.comp (schemePointsHomeomorph B S hS U).isEmbedding.isInducing)

/-- The map on points of a relatively representable morphism into an algebraic space over `S`
is topologically inducing as soon as each of its represented base changes is an inducing map
of schemes.

This is the argument of Stacks 0ABJ for the inducing half, with the immersion hypothesis there
weakened to what that half uses: an open set of the source pulls back to an open set of the
base change to an étale atlas, which is the preimage of an open set of the atlas because the
base change is inducing; the image of that open set in the target is open because the atlas is
open on points, and its preimage in the source is the original open set, one inclusion by
Stacks 03H4 and the other by surjectivity on points of the base change. -/
theorem isInducing_pointsMap_of_isInducing_snd (hX : IsAlgebraicSpace B S hS X) {i : Z ⟶ X}
    (hrep : yoneda.relativelyRepresentable i)
    (hind : ∀ (A : BigFppfOver B S hS) (g : yoneda.obj A ⟶ X),
      Topology.IsInducing ⇑((BigFppfOver.toScheme B S hS).map (hrep.snd g))) :
    Topology.IsInducing (pointsMap B S hS Z i) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  have hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj
  have haopen := isOpenMap_pointsMap_of_presheafEtale B S hS a haEtale
  have hfsurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj (hrep.pullback a)) (hrep.fst a)) :=
    surjective_pointsMap_of_isPullback B S hS (hrep.isPullback a).flip hasurj
  have hjind := isInducing_pointsMap_yoneda B S hS (hrep.snd a) (hind U a)
  refine isInducing_of_isOpenMap_of_forall_lift (continuous_pointsMap B S hS i)
    (continuous_pointsMap B S hS (hrep.fst a)) hfsurj haopen hjind
    (fun pt ↦ pointsMap_apply_comm B S hS (hrep.isPullback a).w pt) fun a' w h ↦ ?_
  obtain ⟨pt, hptf, hptj⟩ := exists_points_of_isPullback B S hS (hrep.isPullback a) w a' h.symm
  exact ⟨pt, hptj, hptf⟩

/-- The base change of a preimmersion of presheaves into an algebraic space over `S` induces an
inducing map on points. -/
private theorem isInducing_pointsMap_of_presheaf_isPreimmersion (hX : IsAlgebraicSpace B S hS X)
    {i : Z ⟶ X} (hi : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsPreimmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i) :
    Topology.IsInducing (pointsMap B S hS Z i) := by
  refine isInducing_pointsMap_of_isInducing_snd B S hS hX hi.rep fun _ h ↦ ?_
  have : _root_.AlgebraicGeometry.IsPreimmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd h)) := hi.property_snd h
  exact ((BigFppfOver.toScheme B S hS).map (hi.rep.snd h)).isEmbedding.isInducing

/-! ### The topology of the fibre over a field-valued point -/

/-- If `v` is the only point of `Z` above `y` along `ψ : Z ⟶ Y`, then the points of
`X ×_Y Z` above the fibre of `|f|` over `y` are exactly the points above `v`. -/
private theorem preimage_pointsMap_fst_eq_of_preimage_eq_singleton (f : X ⟶ Y) (ψ : Z ⟶ Y)
    {y : points B S hS Y} {v : points B S hS Z} (hψ : pointsMap B S hS Z ψ ⁻¹' {y} = {v}) :
    pointsMap B S hS (pullback f ψ) (pullback.fst f ψ) ⁻¹' {x | pointsMap B S hS X f x = y} =
      {z | pointsMap B S hS (pullback f ψ) (pullback.snd f ψ) z = v} := by
  ext z
  have hz := pointsMap_apply_comm B S hS (pullback.condition (f := f) (g := ψ)) z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hz]
  exact Set.ext_iff.mp hψ _

/-- A field-valued point `q` of `Z` carried by `φ : Z ⟶ Y` to the point presented by a
field-valued point `p` of an algebraic space `Y`, with `Spec k ⟶ Y` a monomorphism, factors
through `Spec k ⟶ Y`; this is Stacks 0H2X. -/
private theorem exists_hom_siteObject_comp_fieldMorphism (hY : IsAlgebraicSpace B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hmono : Mono (fieldMorphism B S hS Y p)) (φ : Z ⟶ Y)
    (q : FieldValuedPoint B S hS Z)
    (h : pointsMap B S hS Z φ (q.class B S hS Z) = p.class B S hS Y) :
    ∃ w : q.siteObject B S hS Z ⟶ p.siteObject B S hS Y,
      yoneda.map w ≫ fieldMorphism B S hS Y p = fieldMorphism B S hS Z q ≫ φ := by
  have : Mono (yonedaEquiv.symm p.value) := hmono
  obtain ⟨w, hw, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Y hY p
    (FieldValuedPoint.map B S hS Z φ q) (by rw [← pointsMap_class, h])
  refine ⟨w, ?_⟩
  rw [← fieldMorphism_map B S hS Z φ q]
  change yoneda.map w ≫ yonedaEquiv.symm p.value = yonedaEquiv.symm _
  rw [yonedaEquiv_symm_naturality_left, hw]

/-- Let `p` be a field-valued point of an algebraic space `Y` with `Spec k ⟶ Y` a
monomorphism, and `q` a field-valued point of `Z` carried by `ψ : Z ⟶ Y` to the point of `p`.
Then for `f : X ⟶ Y` there is a morphism `(X ×_Y Z) ×_Z Spec κ ⟶ X ×_Y Spec k` over `X`
which is surjective on points. -/
private theorem exists_surjective_pointsMap_fibre_hom (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hmono : Mono (fieldMorphism B S hS Y p)) (ψ : Z ⟶ Y)
    (q : FieldValuedPoint B S hS Z)
    (h : pointsMap B S hS Z ψ (q.class B S hS Z) = p.class B S hS Y) :
    ∃ t : pullback (pullback.snd f ψ) (fieldMorphism B S hS Z q) ⟶
        pullback f (fieldMorphism B S hS Y p),
      Function.Surjective (pointsMap B S hS _ t) ∧
        t ≫ pullback.fst f (fieldMorphism B S hS Y p) =
          pullback.fst (pullback.snd f ψ) (fieldMorphism B S hS Z q) ≫ pullback.fst f ψ := by
  obtain ⟨w, hw⟩ := exists_hom_siteObject_comp_fieldMorphism B S hS hY p hmono ψ q h
  have hcond : (pullback.fst (pullback.snd f ψ) (fieldMorphism B S hS Z q) ≫
        pullback.fst f ψ) ≫ f =
      (pullback.snd (pullback.snd f ψ) (fieldMorphism B S hS Z q) ≫
        yoneda.map w) ≫ fieldMorphism B S hS Y p := by
    rw [Category.assoc, Category.assoc, pullback.condition (f := f) (g := ψ),
      ← Category.assoc, pullback.condition (f := pullback.snd f ψ)
        (g := fieldMorphism B S hS Z q), Category.assoc, hw]
  have hfst := pullback.lift_fst _ _ hcond
  refine ⟨pullback.lift _ _ hcond, fun x ↦ ?_, hfst⟩
  have hx : pointsMap B S hS X f (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
      (pullback.fst f (fieldMorphism B S hS Y p)) x) = p.class B S hS Y :=
    (Set.ext_iff.mp (range_pointsMap_fibre_fieldMorphism B S hS f p) _).mp ⟨x, rfl⟩
  obtain ⟨z, hz₁, hz₂⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback f ψ) _ _ (hx.trans h.symm)
  obtain ⟨u, rfl⟩ : z ∈ Set.range (pointsMap B S hS
      (pullback (pullback.snd f ψ) (fieldMorphism B S hS Z q))
      (pullback.fst (pullback.snd f ψ) (fieldMorphism B S hS Z q))) := by
    rw [range_pointsMap_fibre_fieldMorphism B S hS (pullback.snd f ψ) q]
    exact hz₂
  refine ⟨u, injective_pointsMap_fibre_fieldMorphism B S hS f p hmono ?_⟩
  rw [← pointsMap_comp_apply, hfst, pointsMap_comp_apply]
  exact hz₁

/-- **Stacks 0AC8, the topology of the fibre.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` and let `p` be a field-valued point of `Y` whose presenting morphism
`Spec k ⟶ Y` is a quasi-compact monomorphism. Then the map on points induced by the
projection `X ×_Y Spec k ⟶ X` is topologically inducing. -/
@[stacks 0AC8 "the topology of the fibre"]
theorem isInducing_pointsMap_fibre_fieldMorphism (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hmono : Mono (fieldMorphism B S hS Y p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    Topology.IsInducing (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
      (pullback.fst f (fieldMorphism B S hS Y p))) := by
  classical
  -- An étale chart of `Y` with exactly one point `v` above the point presented by `p`.
  obtain ⟨V, ψ, v, hψ, hfibre⟩ :=
    exists_etale_chart_singleton_fibre_of_isQuasiCompact_fieldMorphism B S hS hY p hqc
  have hψv : pointsMap B S hS (yoneda.obj V) ψ v = p.class B S hS Y :=
    (Set.ext_iff.mp hfibre v).mpr rfl
  -- The base change of the chart is open on points.
  have hetaleBC : MorphismProperty.IsStableUnderBaseChange
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hgopen : IsOpenMap (pointsMap B S hS (pullback f ψ) (pullback.fst f ψ)) :=
    isOpenMap_pointsMap_of_presheafEtale B S hS (pullback.fst f ψ)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f ψ).flip hψ)
  have hXV : IsAlgebraicSpace B S hS (pullback f ψ) :=
    isAlgebraicSpace_pullback B S hS f ψ hX (isAlgebraicSpace_yoneda B S hS V) hY
  -- The residue field at `v`, and the fibre of the base change over it.
  obtain ⟨q, hqv, hqpre⟩ := exists_fieldValuedPoint_presheafPreimmersion B S hS V v
  have hpreBC : MorphismProperty.IsStableUnderBaseChange
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsPreimmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hrpre := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (pullback.snd f ψ)
      (fieldMorphism B S hS (yoneda.obj V) q)).flip hqpre
  -- The residue field point of the chart factors through the monomorphism presenting `p`.
  -- The resulting morphism from the fibre over the residue field to the fibre over `k`.
  -- It is surjective on points, because its image in `|X|` is the whole fibre.
  obtain ⟨t, htsurj, ht⟩ := exists_surjective_pointsMap_fibre_hom B S hS hY f p hmono ψ q
    (by rw [hqv, hψv])
  -- The two set-theoretic halves of Stacks 0AC8.
  refine isInducing_of_isInducing_of_isOpenMap_comm
    (continuous_pointsMap B S hS (pullback.fst f (fieldMorphism B S hS Y p)))
    (injective_pointsMap_fibre_fieldMorphism B S hS f p hmono)
    (continuous_pointsMap B S hS t) htsurj hgopen
    (isInducing_pointsMap_of_presheaf_isPreimmersion B S hS hXV hrpre) ?_ fun a ↦ ?_
  -- Points of the base change above the fibre are exactly the points above `v`: this is
  -- where it is used that `v` is the only point of the chart above the point of `p`.
  · rw [range_pointsMap_fibre_fieldMorphism B S hS (pullback.snd f ψ) q, hqv,
      range_pointsMap_fibre_fieldMorphism B S hS f p,
      preimage_pointsMap_fst_eq_of_preimage_eq_singleton B S hS f ψ hfibre]
  · rw [← pointsMap_comp_apply, ht, pointsMap_comp_apply]

/-- **Stacks 0AC8, the topology of the fibre.** The map on points induced by the projection
`X ×_Y Spec k ⟶ X` is a topological embedding when the morphism `Spec k ⟶ Y` presenting the
field-valued point `p` is a quasi-compact monomorphism. -/
@[stacks 0AC8 "the fibre is embedded"]
theorem isEmbedding_pointsMap_fibre_fieldMorphism (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hmono : Mono (fieldMorphism B S hS Y p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    Topology.IsEmbedding (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
      (pullback.fst f (fieldMorphism B S hS Y p))) :=
  ⟨isInducing_pointsMap_fibre_fieldMorphism B S hS hX hY f p hmono hqc,
    injective_pointsMap_fibre_fieldMorphism B S hS f p hmono⟩

/-- **Stacks 0AC8.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` and a
field-valued point `p` of `Y` whose presenting morphism `Spec k ⟶ Y` is a quasi-compact
monomorphism, the point space of the fibre `X ×_Y Spec k` is homeomorphic to the
set-theoretic fibre of `|f|` above the point presented by `p`, with its subspace topology. -/
@[stacks 0AC8 "homeomorphism onto the fibre"]
noncomputable def fibreHomeomorph (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hmono : Mono (fieldMorphism B S hS Y p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y p)) :
    points B S hS (pullback f (fieldMorphism B S hS Y p)) ≃ₜ
      (pointsMap B S hS X f ⁻¹' {p.class B S hS Y}) :=
  (isEmbedding_pointsMap_fibre_fieldMorphism B S hS hX hY f p hmono hqc).toHomeomorph.trans
    (Homeomorph.setCongr (range_pointsMap_fibre_fieldMorphism B S hS f p))

end AlgebraicGeometry.Space

end
