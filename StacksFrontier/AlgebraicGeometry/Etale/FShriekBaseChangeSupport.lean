module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm

/-!
# Base change of supports and of supported sections along a cartesian square

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, and let `F` be an abelian
sheaf on the small étale site of `X`. For an étale test object `V` of `Y` with base change
`V' = V ×_Y Y'`, transitivity of fibre products identifies `X'_{V'}` with the base change of
`X_V` along `V' ⟶ V`. The inverse image along that comparison of a support finite over `V` is
a support finite over `V'`, and a section of `F` supported on the first is carried, by the unit
of the inverse image along `p`, to a section of `p⁻¹F` supported on the second. These pullback
maps are compatible with the transitions of the colimit `f_{p!}F(V) = colim_Z H_Z(F)` and
functorial in `F`, so they assemble into a map `f_{p!}F(V) ⟶ f'_{p!}(p⁻¹F)(V')`, natural in
`F`. This is the construction of the map `c` in the proof of Stacks 0F5J, over a single test
object.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fiberBaseChangeMap` — the comparison `X'_{V'} ⟶ X_V` of the two
  étale base changes of a test object, with `fiberBaseChangeScheme` the underlying morphism of
  schemes.
* `AlgebraicGeometry.SmallEtale.baseChangeObjProjection` and
  `AlgebraicGeometry.SmallEtale.baseChangeObjLift` — the projection of the étale base change of
  an object of the small étale site of `X` to that object, and a morphism into that base change
  given by its two coordinates.
* `AlgebraicGeometry.SmallEtale.abPullbackUnit` — the map from the sections of `F` over `W` to
  the sections of `p⁻¹F` over the base change of `W`.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangeSupport` — the base change of a support finite
  over `V`, with `fiberBaseChangeSupportOpen` the inverse image of its canonical open and
  `fiberBaseChangeSupportArrow` the resulting comparison of étale test objects.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangeSectionsMap` — the pullback map
  `H_Z(F) ⟶ H_{Z'}(p⁻¹F)` on supported sections, with
  `AlgebraicGeometry.SmallEtale.fiberBaseChangeDiagramMap` the same map read between the
  diagrams of supported sections.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangeCocone` and
  `AlgebraicGeometry.SmallEtale.fiberBaseChangeColimitMap` — the resulting map
  `f_{p!}F(V) ⟶ f'_{p!}(p⁻¹F)(V')` on finite-support sections, pinned down on the colimit
  generators by `AlgebraicGeometry.SmallEtale.fiberBaseChangeColimitMap_ι`.

## Main results

* `AlgebraicGeometry.SmallEtale.isPullback_fiberBaseChangeMap` — `X'_{V'}` is the base change of
  `X_V` along `V' ⟶ V`, which is the transitivity of fibre products the source appeals to.
* `AlgebraicGeometry.SmallEtale.isFiniteSupport_fiberBaseChange_preimage` — the inverse image of
  a support finite over `V` is a support finite over `V'`.
* `AlgebraicGeometry.SmallEtale.supportSection_abPullbackUnit_subset` and
  `AlgebraicGeometry.SmallEtale.supportSection_pullbackSectionAlongHom_subset` — pulling a
  section back along the unit of the inverse image does not enlarge its support.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangeSectionsMap_val` and
  `AlgebraicGeometry.SmallEtale.fiberBaseChangeSectionsMap_restrict` — the pullback map on
  supported sections is, on the inverse image of the canonical open of the support, the pullback
  of the section along the unit; this determines it, by
  `AlgebraicGeometry.SmallEtale.supportedSections_ext`.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangeSectionsMap_transition` and
  `AlgebraicGeometry.SmallEtale.fiberBaseChangeSectionsMap_sheafMap` — the pullback map on
  supported sections commutes with the transitions of Stacks 0F6H and with a morphism of
  abelian sheaves, which is what makes it a map out of the colimit, natural in the sheaf;
  `AlgebraicGeometry.SmallEtale.fiberBaseChangeColimitMap_natural` is that naturality.

## Implementation notes

The comparison `X'_{V'} ⟶ X_V` is built from the universal property of `X_V` rather than
transported along a comparison of the two composite base-change functors, so that its two
coordinates, and hence the cartesian square it sits in, are available by `IsPullback.lift_fst`
and `IsPullback.lift_snd`.

The morphism `p` of the square is arbitrary, so the comparison `X'_{V'} ⟶ X_V` need not be an
open map and the canonical open `coborder Z'` of the base-changed support need not lie in the
inverse image of `coborder Z`. The pullback of a supported section is therefore produced on the
inverse image of `coborder Z`, which is an admissible open for `Z'` because `Z` is closed in
`coborder Z`, and then transported to `coborder Z'` by
`AlgebraicGeometry.SmallEtale.supportedSectionsOpenEquiv`.

## References

* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6F](https://stacks.math.columbia.edu/tag/0F6F)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Pullbacks

/-- In a cartesian square of schemes the image of one projection is the inverse image of the
image of the opposite arrow. -/
private theorem range_eq_preimage_range_of_isPullback {P Q R S : Scheme.{u}}
    {a : P ⟶ Q} {b : P ⟶ R} {c : Q ⟶ S} {d : R ⟶ S} (h : IsPullback a b c d) :
    Set.range b.base = d.base ⁻¹' Set.range c.base := by
  have hsurj : Function.Surjective h.isoPullback.hom.base := fun x =>
    ⟨h.isoPullback.inv.base x,
      congrArg (fun m : pullback c d ⟶ pullback c d => m.base x) h.isoPullback.inv_hom_id⟩
  rw [← Scheme.Pullback.range_snd c d,
    ← congrArg (fun k : P ⟶ R => Set.range k.base) h.isoPullback_hom_snd,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- The inverse image of the largest open in which a subset is closed is contained in the
largest open in which its inverse image is closed. -/
private theorem preimage_coborder_subset {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {h : α → β} (hc : Continuous h) (Z : Set β) :
    h ⁻¹' coborder Z ⊆ coborder (h ⁻¹' Z) := by
  intro x hx
  have hx' : h x ∈ coborder Z := hx
  rw [mem_coborder_iff_imp] at hx'
  rw [mem_coborder_iff_imp]
  exact fun hxc => hx' (hc.closure_preimage_subset Z hxc)

end Pullbacks

section Projection

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The projection of the étale base change `X_V = V ×_Y X` to the test object `V`. -/
public def fiberProjection (V : SmallEtale B Y.obj Y.property) :
    (baseChange B f V).obj.left ⟶ V.obj.left :=
  pullback.fst V.obj.hom f

/-- The étale base change of `X` along a test object `V` of `Y` is the fibre product of `V`
and `X` over `Y`. -/
public theorem isPullback_fiberProjection (V : SmallEtale B Y.obj Y.property) :
    IsPullback (fiberProjection B f V) (baseChange B f V).obj.hom V.obj.hom f :=
  IsPullback.of_hasPullback _ _

end Projection

section OpenObject

/-- The structure morphism of a Zariski open of an object of the small étale site, as a
morphism of schemes. -/
public theorem openObject_hom_map (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : SmallEtale B S hS) (W : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    B.inclusion.map (openObject B S hS U W).obj.hom = W.ι ≫ B.inclusion.map U.obj.hom := by
  have h := congrArg B.inclusion.map (Over.w (openObjectι B S hS U W).hom)
  rw [Functor.map_comp] at h
  rw [← h]
  exact congrArg (fun k => k ≫ B.inclusion.map U.obj.hom) (openObjectι_map B S hS U W)

end OpenObject

section SupportedSectionsExt

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- A section supported on a locally closed subset is determined by its restriction to any
admissible open contained in the canonical one. -/
public theorem supportedSections_ext (W : SmallEtale B S hS)
    (Z : Set ((SmallEtale.toScheme B S hS).obj W)) (hZ : IsLocallyClosed Z)
    (U : ((SmallEtale.toScheme B S hS).obj W).Opens) (hZU : Z ⊆ U)
    (hUc : IsClosed (U.ι.base ⁻¹' Z)) (h : U ≤ supportOpen B S hS W Z hZ)
    {x y : supportedSections B S hS F W Z hZ}
    (he : F.obj.map (openObjectHomOfLE B S hS W h).op x.val =
      F.obj.map (openObjectHomOfLE B S hS W h).op y.val) : x = y := by
  have hx := locallyClosedSupportEquiv_restrict B S hS F W Z (supportOpen B S hS W Z hZ) U
    (subset_supportOpen B S hS W Z hZ) hZU (isClosed_supportOpen_preimage B S hS W Z hZ) hUc h x
  have hy := locallyClosedSupportEquiv_restrict B S hS F W Z (supportOpen B S hS W Z hZ) U
    (subset_supportOpen B S hS W Z hZ) hZU (isClosed_supportOpen_preimage B S hS W Z hZ) hUc h y
  exact (supportedSectionsOpenEquiv B S hS F W Z hZ U hZU hUc).injective
    (Subtype.ext (hx.trans (he.trans hy.symm)))

end SupportedSectionsExt

section BaseChangeObject

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} (p : X' ⟶ X)

/-- The projection of the étale base change of an object of the small étale site of `X` to that
object. -/
public def baseChangeObjProjection (W : SmallEtale B X.obj X.property) :
    ((smallEtaleBaseChange B p).obj W).obj.left ⟶ W.obj.left :=
  pullback.fst W.obj.hom p

/-- The étale base change of an object of the small étale site of `X` is its fibre product
with `X'`. -/
public theorem isPullback_baseChangeObjProjection (W : SmallEtale B X.obj X.property) :
    IsPullback (baseChangeObjProjection B p W)
      ((smallEtaleBaseChange B p).obj W).obj.hom W.obj.hom p :=
  IsPullback.of_hasPullback _ _

/-- A morphism of the small étale site of `X'` into the base change of `W`, given by a morphism
to `W` lying over `p`. -/
public def baseChangeObjLift (T : SmallEtale B X'.obj X'.property)
    (W : SmallEtale B X.obj X.property) (m : T.obj.left ⟶ W.obj.left)
    (hm : m ≫ W.obj.hom = T.obj.hom ≫ p) : T ⟶ (smallEtaleBaseChange B p).obj W :=
  ObjectProperty.homMk (Over.homMk
    ((isPullback_baseChangeObjProjection B p W).lift m T.obj.hom hm)
    ((isPullback_baseChangeObjProjection B p W).lift_snd m T.obj.hom hm))

/-- The morphism `baseChangeObjLift` followed by the projection to `W` is the given morphism
`m`. -/
@[simp]
public theorem baseChangeObjLift_proj (T : SmallEtale B X'.obj X'.property)
    (W : SmallEtale B X.obj X.property) (m : T.obj.left ⟶ W.obj.left)
    (hm : m ≫ W.obj.hom = T.obj.hom ≫ p) :
    (baseChangeObjLift B p T W m hm).hom.left ≫ baseChangeObjProjection B p W = m :=
  (isPullback_baseChangeObjProjection B p W).lift_fst m T.obj.hom hm

/-- Two morphisms into an étale base change agreeing after the projection are equal. -/
public theorem baseChangeObj_hom_ext {T : SmallEtale B X'.obj X'.property}
    {W : SmallEtale B X.obj X.property} {a b : T ⟶ (smallEtaleBaseChange B p).obj W}
    (h : a.hom.left ≫ baseChangeObjProjection B p W =
      b.hom.left ≫ baseChangeObjProjection B p W) : a = b :=
  (SmallEtale.inclusion B X'.obj X'.property).map_injective <| Over.OverMorphism.ext <|
    (isPullback_baseChangeObjProjection B p W).hom_ext h
      ((Over.w a.hom).trans (Over.w b.hom).symm)

/-- The projection of the étale base change is natural in the object. -/
public theorem baseChangeObjProjection_naturality {W₁ W : SmallEtale B X.obj X.property}
    (i : W₁ ⟶ W) :
    ((smallEtaleBaseChange B p).map i).hom.left ≫ baseChangeObjProjection B p W =
      baseChangeObjProjection B p W₁ ≫ i.hom.left :=
  pullback.lift_fst _ _ _

/-- The étale base change of a morphism of the small étale site of `X` sits in a cartesian
square over that morphism. -/
public theorem isPullback_baseChangeObjMap {W₁ W : SmallEtale B X.obj X.property}
    (i : W₁ ⟶ W) :
    IsPullback ((smallEtaleBaseChange B p).map i).hom.left
      (baseChangeObjProjection B p W₁) (baseChangeObjProjection B p W) i.hom.left := by
  have hs := (isPullback_baseChangeObjProjection B p W₁).flip
  rw [← Over.w ((smallEtaleBaseChange B p).map i).hom, ← Over.w i.hom] at hs
  exact IsPullback.of_right hs (baseChangeObjProjection_naturality B p i)
    (isPullback_baseChangeObjProjection B p W).flip

/-- The image of the étale base change of a morphism of the small étale site of `X` is the
inverse image of its image. -/
public theorem range_baseChangeObjMap {W₁ W : SmallEtale B X.obj X.property} (i : W₁ ⟶ W) :
    Set.range ((SmallEtale.toScheme B X'.obj X'.property).map
        ((smallEtaleBaseChange B p).map i)).base =
      (B.inclusion.map (baseChangeObjProjection B p W)).base ⁻¹'
        Set.range ((SmallEtale.toScheme B X.obj X.property).map i).base :=
  range_eq_preimage_range_of_isPullback
    ((isPullback_baseChangeObjMap B p i).flip.map B.inclusion)

end BaseChangeObject

section UnitSupport

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} (p : X' ⟶ X)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The canonical map from the sections of `F` over an object `W` of the small étale site of `X`
to the sections of `p⁻¹F` over the base change of `W`: the unit of the inverse-image
adjunction. -/
public abbrev abPullbackUnit (W : SmallEtale B X.obj X.property) :
    F.obj.obj (op W) ⟶
      ((abPullback.{u, v} B p).obj F).obj.obj (op ((smallEtaleBaseChange B p).obj W)) :=
  (((smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W)

/-- The unit of the inverse-image adjunction is natural in the object of the small étale site. -/
private theorem abPullbackUnit_map {W₁ W : SmallEtale B X.obj X.property} (i : W₁ ⟶ W)
    (s : F.obj.obj (op W)) :
    abPullbackUnit.{u, v} B p F W₁ (F.obj.map i.op s) =
      ((abPullback.{u, v} B p).obj F).obj.map ((smallEtaleBaseChange B p).map i).op
        (abPullbackUnit.{u, v} B p F W s) :=
  ConcreteCategory.congr_hom
    ((((smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.naturality i.op) s

/-- Pulling a section back along an arrow is restricting its pullback along the unit. -/
private theorem pullbackSectionAlongHom_eq_map_unit (W : SmallEtale B X.obj X.property)
    (T : SmallEtale B X'.obj X'.property) (a : T ⟶ (smallEtaleBaseChange B p).obj W)
    (s : F.obj.obj (op W)) :
    pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F W T a s =
      ((abPullback.{u, v} B p).obj F).obj.map a.op (abPullbackUnit.{u, v} B p F W s) :=
  ConcreteCategory.comp_apply _ _ _

/-- Pulling a section back along the unit does not enlarge its support: the support of the
pulled-back section lies in the inverse image of the support. -/
public theorem supportSection_abPullbackUnit_subset (W : SmallEtale B X.obj X.property)
    (s : F.obj.obj (op W)) :
    supportSection B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
        ((smallEtaleBaseChange B p).obj W) (abPullbackUnit.{u, v} B p F W s) ⊆
      (B.inclusion.map (baseChangeObjProjection B p W)).base ⁻¹'
        supportSection B X.obj X.property F W s := by
  set U₀ := zeroOpen B X.obj X.property F W s with hU₀
  set W₀ := openObject B X.obj X.property W U₀ with hW₀
  set i₀ := openObjectι B X.obj X.property W U₀ with hi₀
  have hs0 : F.obj.map i₀.op s = 0 :=
    (map_eq_zero_iff_range_subset_zeroOpen B X.obj X.property F W s W₀ i₀).2
      (by rw [hi₀, openObjectι_range])
  have hmapzero : ((abPullback.{u, v} B p).obj F).obj.map
      ((smallEtaleBaseChange B p).map i₀).op (abPullbackUnit.{u, v} B p F W s) = 0 := by
    rw [← abPullbackUnit_map, hs0, map_zero]
  have hrange := (map_eq_zero_iff_range_subset_zeroOpen B X'.obj X'.property
    ((abPullback.{u, v} B p).obj F) ((smallEtaleBaseChange B p).obj W)
    (abPullbackUnit.{u, v} B p F W s) ((smallEtaleBaseChange B p).obj W₀)
    ((smallEtaleBaseChange B p).map i₀)).1 hmapzero
  rw [range_baseChangeObjMap, hi₀, openObjectι_range] at hrange
  intro x hx hxn
  exact hx (hrange hxn)

/-- Pulling a section back along the unit and restricting it to an étale neighbourhood over the
base change does not enlarge its support. -/
public theorem supportSection_pullbackSectionAlongHom_subset
    (W : SmallEtale B X.obj X.property) (T : SmallEtale B X'.obj X'.property)
    (a : T ⟶ (smallEtaleBaseChange B p).obj W) (s : F.obj.obj (op W)) :
    supportSection B X'.obj X'.property ((abPullback.{u, v} B p).obj F) T
        (pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F W T a s) ⊆
      ((SmallEtale.toScheme B X'.obj X'.property).map a ≫
          B.inclusion.map (baseChangeObjProjection B p W)).base ⁻¹'
        supportSection B X.obj X.property F W s := by
  rw [pullbackSectionAlongHom_eq_map_unit, Scheme.Hom.comp_base]
  refine (supportSection_restrict_subset_preimage B X'.obj X'.property
    ((abPullback.{u, v} B p).obj F) _ T a _).trans ?_
  rw [TopCat.coe_comp, Set.preimage_comp]
  exact Set.preimage_mono (supportSection_abPullbackUnit_subset.{u, v} B p F W s)

/-- Pulling a section back along the unit and restricting it is pulling it back along the
composite arrow. -/
public theorem pullbackSectionAlongHom_restrict (W : SmallEtale B X.obj X.property)
    {T T' : SmallEtale B X'.obj X'.property} (a : T ⟶ (smallEtaleBaseChange B p).obj W)
    (b : T' ⟶ T) (s : F.obj.obj (op W)) :
    ((abPullback.{u, v} B p).obj F).obj.map b.op
        (pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F W T a s) =
      pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F W T' (b ≫ a) s := by
  rw [pullbackSectionAlongHom_eq_map_unit, pullbackSectionAlongHom_eq_map_unit, op_comp,
    Functor.map_comp, ConcreteCategory.comp_apply]

/-- Restricting a section and then pulling it back along the unit is pulling it back along the
composite arrow. -/
public theorem pullbackSectionAlongHom_map {W₁ W : SmallEtale B X.obj X.property} (i : W₁ ⟶ W)
    (T : SmallEtale B X'.obj X'.property) (a : T ⟶ (smallEtaleBaseChange B p).obj W₁)
    (s : F.obj.obj (op W)) :
    pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F W₁ T a (F.obj.map i.op s) =
      pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F W T
        (a ≫ (smallEtaleBaseChange B p).map i) s := by
  rw [pullbackSectionAlongHom_eq_map_unit, pullbackSectionAlongHom_eq_map_unit,
    abPullbackUnit_map, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Pulling a section back along the unit is natural in the abelian sheaf. -/
public theorem pullbackSectionAlongHom_sheafMap
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) (W : SmallEtale B X.obj X.property)
    (T : SmallEtale B X'.obj X'.property) (a : T ⟶ (smallEtaleBaseChange B p).obj W)
    (s : F.obj.obj (op W)) :
    pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} G W T a (φ.hom.app (op W) s) =
      ((abPullback.{u, v} B p).map φ).hom.app (op T)
        (pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F W T a s) := by
  have hunit : abPullbackUnit.{u, v} B p G W (φ.hom.app (op W) s) =
      ((abPullback.{u, v} B p).map φ).hom.app (op ((smallEtaleBaseChange B p).obj W))
        (abPullbackUnit.{u, v} B p F W s) := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun ψ => ψ.hom)
        (((smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.naturality φ)) (op W)) s
    exact h
  rw [pullbackSectionAlongHom_eq_map_unit, pullbackSectionAlongHom_eq_map_unit, hunit]
  exact (ConcreteCategory.congr_hom (((abPullback.{u, v} B p).map φ).hom.naturality a.op)
    (abPullbackUnit.{u, v} B p F W s)).symm

end UnitSupport

section Square

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- For a cartesian square, the comparison `X'_{V'} ⟶ X_V` of the étale base changes of a test
object `V` of `Y` and of its base change `V' = V ×_Y Y'`: the first coordinate is the projection
to `V`, the second is the projection to `X'` followed by `p`. -/
public def fiberBaseChangeMap (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) :
    (baseChange B f' (baseChange B g V)).obj.left ⟶ (baseChange B f V).obj.left :=
  (isPullback_fiberProjection B f V).lift
    (fiberProjection B f' (baseChange B g V) ≫ fiberProjection B g V)
    ((baseChange B f' (baseChange B g V)).obj.hom ≫ p)
    (by
      have h1 := (isPullback_fiberProjection B g V).w
      have h2 := (isPullback_fiberProjection B f' (baseChange B g V)).w
      rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc, Category.assoc, sq.w])

/-- The comparison `fiberBaseChangeMap` followed by the projection to `V` is the composite of
the projections `X'_{V'} ⟶ V'` and `V' ⟶ V`. -/
@[simp]
public theorem fiberBaseChangeMap_fst (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) :
    fiberBaseChangeMap B p f' f g sq V ≫ fiberProjection B f V =
      fiberProjection B f' (baseChange B g V) ≫ fiberProjection B g V :=
  IsPullback.lift_fst _ _ _ _

/-- The comparison `fiberBaseChangeMap` followed by the structure morphism `X_V ⟶ X` is the
structure morphism `X'_{V'} ⟶ X'` followed by `p`. -/
@[simp]
public theorem fiberBaseChangeMap_snd (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) :
    fiberBaseChangeMap B p f' f g sq V ≫ (baseChange B f V).obj.hom =
      (baseChange B f' (baseChange B g V)).obj.hom ≫ p :=
  IsPullback.lift_snd _ _ _ _

/-- For a cartesian square, `X'_{V'}` is the base change of `X_V` along `V' ⟶ V`. -/
public theorem isPullback_fiberBaseChangeMap (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) :
    IsPullback (fiberBaseChangeMap B p f' f g sq V)
      (fiberProjection B f' (baseChange B g V))
      (fiberProjection B f V) (fiberProjection B g V) := by
  have hpaste := (isPullback_fiberProjection B f' (baseChange B g V)).flip.paste_horiz sq
  rw [(isPullback_fiberProjection B g V).w.symm,
    ← fiberBaseChangeMap_snd B p f' f g sq V] at hpaste
  exact IsPullback.of_right hpaste (fiberBaseChangeMap_fst B p f' f g sq V)
    (isPullback_fiberProjection B f V).flip

/-- The comparison of the two étale base changes, as a morphism of schemes. -/
public abbrev fiberBaseChangeScheme (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) :
    (SmallEtale.toScheme B X'.obj X'.property).obj (baseChange B f' (baseChange B g V)) ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) :=
  B.inclusion.map (fiberBaseChangeMap B p f' f g sq V)

/-- The inverse image along the comparison of a support finite over `V` is a support finite
over `V'`: it is the base change of the given one along `V' ⟶ V`. -/
public theorem isFiniteSupport_fiberBaseChange_preimage (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    IsFiniteSupport B f' (baseChange B g V)
      ((fiberBaseChangeScheme B p f' f g sq V).base ⁻¹' E.1) := by
  obtain ⟨Z, i, hi, hfin, hrange⟩ := E.property
  let _ : IsImmersion i := hi
  have houter : IsPullback (fiberBaseChangeScheme B p f' f g sq V)
      (B.inclusion.map (fiberProjection B f' (baseChange B g V)))
      (B.inclusion.map (fiberProjection B f V))
      (B.inclusion.map (fiberProjection B g V)) :=
    (isPullback_fiberBaseChangeMap B p f' f g sq V).map B.inclusion
  have hbig : IsPullback (pullback.fst i (fiberBaseChangeScheme B p f' f g sq V))
      (pullback.snd i (fiberBaseChangeScheme B p f' f g sq V) ≫
        B.inclusion.map (fiberProjection B f' (baseChange B g V)))
      (i ≫ B.inclusion.map (fiberProjection B f V))
      (B.inclusion.map (fiberProjection B g V)) :=
    (IsPullback.of_hasPullback i _).paste_vert houter
  refine ⟨pullback i (fiberBaseChangeScheme B p f' f g sq V),
    pullback.snd i (fiberBaseChangeScheme B p f' f g sq V), inferInstance,
    MorphismProperty.of_isPullback hbig hfin, ?_⟩
  rw [Scheme.Pullback.range_snd, hrange]

/-- The comparison of the two étale base changes lies over `p`. -/
public theorem fiberBaseChangeScheme_comp_hom (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) :
    fiberBaseChangeScheme B p f' f g sq V ≫ B.inclusion.map (baseChange B f V).obj.hom =
      B.inclusion.map (baseChange B f' (baseChange B g V)).obj.hom ≫ B.inclusion.map p := by
  rw [← Functor.map_comp, ← Functor.map_comp, fiberBaseChangeMap_snd]

/-- **Stacks 0F5J.** The base change of a support finite over `V` along the cartesian square:
the inverse image of the support under the comparison of the two étale base changes. It is
again a support finite over `V'`. -/
@[stacks 0F5J "the base change of a support finite over the test object"]
public def fiberBaseChangeSupport (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    FiniteSupport B f' (baseChange B g V) :=
  ⟨(fiberBaseChangeScheme B p f' f g sq V).base ⁻¹' E.1,
    isFiniteSupport_fiberBaseChange_preimage B p f' f g sq V E⟩

/-- The open of `X'_{V'}` on which the base change of a section supported on `E` lives: the
inverse image of the canonical open of `E`. -/
public abbrev fiberBaseChangeSupportOpen (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    ((SmallEtale.toScheme B X'.obj X'.property).obj
      (baseChange B f' (baseChange B g V))).Opens :=
  fiberBaseChangeScheme B p f' f g sq V ⁻¹ᵁ
    supportOpen B X.obj X.property (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)

/-- The base-changed support lies in the inverse image of the canonical open of the support. -/
public theorem fiberBaseChangeSupport_subset_open (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    (fiberBaseChangeSupport B p f' f g sq V E).1 ⊆
      (fiberBaseChangeSupportOpen B p f' f g sq V E :
        Set ((SmallEtale.toScheme B X'.obj X'.property).obj
          (baseChange B f' (baseChange B g V)))) :=
  Set.preimage_mono (subset_supportOpen B X.obj X.property (baseChange B f V) E.1
    (finiteSupport_isLocallyClosed B f V E))

/-- The base-changed support is the inverse image of the support. -/
public theorem fiberBaseChangeSupport_coe (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    (fiberBaseChangeSupport B p f' f g sq V E).1 =
      (fiberBaseChangeScheme B p f' f g sq V).base ⁻¹' E.1 :=
  rfl

/-- The inclusion of the open on which the base change of a supported section lives, followed
by the comparison of the two étale base changes, is the restriction of that comparison. -/
public theorem fiberBaseChangeSupportOpen_ι_comp (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    (fiberBaseChangeSupportOpen B p f' f g sq V E).ι ≫
        fiberBaseChangeScheme B p f' f g sq V =
      (fiberBaseChangeScheme B p f' f g sq V ∣_
          supportOpen B X.obj X.property (baseChange B f V) E.1
            (finiteSupport_isLocallyClosed B f V E)) ≫
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)).ι :=
  (morphismRestrict_ι _ _).symm

/-- The inverse image of the canonical open of the support is an admissible open for the
base-changed support: the latter is closed in it. -/
public theorem isClosed_fiberBaseChangeSupport_preimage (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    IsClosed ((fiberBaseChangeSupportOpen B p f' f g sq V E).ι.base ⁻¹'
      (fiberBaseChangeSupport B p f' f g sq V E).1) := by
  have hpre : (fiberBaseChangeSupportOpen B p f' f g sq V E).ι.base ⁻¹'
      (fiberBaseChangeSupport B p f' f g sq V E).1 =
      (fiberBaseChangeScheme B p f' f g sq V ∣_
        supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)).base ⁻¹'
        ((supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)).ι.base ⁻¹' E.1) := by
    rw [fiberBaseChangeSupport_coe, ← Set.preimage_comp, ← Set.preimage_comp]
    exact congrArg (fun k : (fiberBaseChangeSupportOpen B p f' f g sq V E).toScheme ⟶
        (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) => k.base ⁻¹' E.1)
      (fiberBaseChangeSupportOpen_ι_comp B p f' f g sq V E)
  rw [hpre]
  exact (isClosed_supportOpen_preimage B X.obj X.property (baseChange B f V) E.1
    (finiteSupport_isLocallyClosed B f V E)).preimage (Scheme.Hom.continuous _)

/-- The restriction of the comparison of the two étale base changes to the canonical open of
the support and its inverse image. -/
public def fiberBaseChangeOpenMap (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    (openObject B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupportOpen B p f' f g sq V E)).obj.left ⟶
      (openObject B X.obj X.property (baseChange B f V)
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E))).obj.left :=
  B.inclusion.preimage (fiberBaseChangeScheme B p f' f g sq V ∣_
    supportOpen B X.obj X.property (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E))

/-- The underlying morphism of schemes of `fiberBaseChangeOpenMap` is the restriction of
`fiberBaseChangeScheme` to the canonical open of the support. -/
@[simp]
public theorem fiberBaseChangeOpenMap_map (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    B.inclusion.map (fiberBaseChangeOpenMap B p f' f g sq V E) =
      fiberBaseChangeScheme B p f' f g sq V ∣_
        supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E) :=
  B.inclusion.map_preimage _

/-- The morphism of the small étale site of `X'` comparing the canonical open of the
base-changed support with the étale base change along `p` of the canonical open of the
support. -/
public def fiberBaseChangeSupportArrow (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    openObject B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupportOpen B p f' f g sq V E) ⟶
      (smallEtaleBaseChange B p).obj (openObject B X.obj X.property (baseChange B f V)
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E))) :=
  baseChangeObjLift B p _ _ (fiberBaseChangeOpenMap B p f' f g sq V E)
    (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_comp, fiberBaseChangeOpenMap_map,
        openObject_hom_map, openObject_hom_map, ← Category.assoc, morphismRestrict_ι,
        Category.assoc, Category.assoc, fiberBaseChangeScheme_comp_hom])

/-- The comparison arrow lies over the restriction of the comparison of the two étale base
changes. -/
public theorem fiberBaseChangeSupportArrow_proj (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    (fiberBaseChangeSupportArrow B p f' f g sq V E).hom.left ≫
        baseChangeObjProjection B p (openObject B X.obj X.property (baseChange B f V)
          (supportOpen B X.obj X.property (baseChange B f V) E.1
            (finiteSupport_isLocallyClosed B f V E))) =
      fiberBaseChangeOpenMap B p f' f g sq V E :=
  baseChangeObjLift_proj B p _ _ _ _

/-- The comparison arrow, followed by the projection of the base change and the inclusion of
the canonical open of the support, is the inclusion of the inverse-image open followed by the
comparison of the two étale base changes. -/
public theorem fiberBaseChangeSupportArrow_comp (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    ((SmallEtale.toScheme B X'.obj X'.property).map
          (fiberBaseChangeSupportArrow B p f' f g sq V E) ≫
        B.inclusion.map (baseChangeObjProjection B p
          (openObject B X.obj X.property (baseChange B f V)
            (supportOpen B X.obj X.property (baseChange B f V) E.1
              (finiteSupport_isLocallyClosed B f V E))))) ≫
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)).ι =
      (fiberBaseChangeSupportOpen B p f' f g sq V E).ι ≫
        fiberBaseChangeScheme B p f' f g sq V := by
  have h1 : (SmallEtale.toScheme B X'.obj X'.property).map
        (fiberBaseChangeSupportArrow B p f' f g sq V E) ≫
      B.inclusion.map (baseChangeObjProjection B p
        (openObject B X.obj X.property (baseChange B f V)
          (supportOpen B X.obj X.property (baseChange B f V) E.1
            (finiteSupport_isLocallyClosed B f V E)))) =
      fiberBaseChangeScheme B p f' f g sq V ∣_
        supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E) := by
    show B.inclusion.map ((fiberBaseChangeSupportArrow B p f' f g sq V E).hom.left) ≫
      B.inclusion.map _ = _
    rw [← Functor.map_comp, fiberBaseChangeSupportArrow_proj, fiberBaseChangeOpenMap_map]
  rw [h1]
  exact morphismRestrict_ι _ _

/-- **Stacks 0F5J.** The pullback map on supported sections: a section of `F` supported on a
support `E` finite over `V` is carried by the unit of the inverse-image adjunction to a section
of `p⁻¹F` supported on the base change of `E`. -/
@[stacks 0F5J "the pullback map H_Z(F) ⟶ H_{Z'}(p⁻¹F) on supported sections"]
public def fiberBaseChangeSectionsMap (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    supportedSections B X.obj X.property F (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E) →+
      supportedSections B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
        (baseChange B f' (baseChange B g V)) (fiberBaseChangeSupport B p f' f g sq V E).1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V)
          (fiberBaseChangeSupport B p f' f g sq V E)) :=
  (supportedSectionsOpenEquiv B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
      (baseChange B f' (baseChange B g V)) (fiberBaseChangeSupport B p f' f g sq V E).1
      (finiteSupport_isLocallyClosed B f' (baseChange B g V)
        (fiberBaseChangeSupport B p f' f g sq V E))
      (fiberBaseChangeSupportOpen B p f' f g sq V E)
      (fiberBaseChangeSupport_subset_open B p f' f g sq V E)
      (isClosed_fiberBaseChangeSupport_preimage B p f' f g sq V
        E)).symm.toAddMonoidHom.comp
    { toFun := fun s => ⟨pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F _ _
        (fiberBaseChangeSupportArrow B p f' f g sq V E) s.val, by
          refine (supportSection_pullbackSectionAlongHom_subset.{u, v} B p F _ _ _ s.val).trans
            ((Set.preimage_mono s.property).trans (Eq.subset ?_))
          rw [fiberBaseChangeSupport_coe, ← Set.preimage_comp, ← Set.preimage_comp]
          exact congrArg (fun k : (fiberBaseChangeSupportOpen B p f' f g sq V E).toScheme ⟶
              (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) =>
            k.base ⁻¹' E.1) (fiberBaseChangeSupportArrow_comp B p f' f g sq V E)⟩
      map_zero' := Subtype.ext (pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F _ _
        (fiberBaseChangeSupportArrow B p f' f g sq V E)).hom.map_zero
      map_add' := fun s t => Subtype.ext
        ((pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F _ _
          (fiberBaseChangeSupportArrow B p f' f g sq V E)).hom.map_add s.val t.val) }

/-- The inverse image of the canonical open of the support lies in the canonical open of the
base-changed support. -/
public theorem fiberBaseChangeSupportOpen_le (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V) :
    fiberBaseChangeSupportOpen B p f' f g sq V E ≤
      supportOpen B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupport B p f' f g sq V E).1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V)
          (fiberBaseChangeSupport B p f' f g sq V E)) :=
  preimage_coborder_subset (Scheme.Hom.continuous _) E.1

/-- The pullback map on supported sections is, on the inverse image of the canonical open of
the support, the pullback of the section along the unit of the inverse-image adjunction. -/
public theorem fiberBaseChangeSectionsMap_val (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    ((supportedSectionsOpenEquiv B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
        (baseChange B f' (baseChange B g V)) (fiberBaseChangeSupport B p f' f g sq V E).1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V)
          (fiberBaseChangeSupport B p f' f g sq V E))
        (fiberBaseChangeSupportOpen B p f' f g sq V E)
        (fiberBaseChangeSupport_subset_open B p f' f g sq V E)
        (isClosed_fiberBaseChangeSupport_preimage B p f' f g sq V E))
      (fiberBaseChangeSectionsMap B p f' f g sq V E F s)).val =
      pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F _ _
        (fiberBaseChangeSupportArrow B p f' f g sq V E) s.val :=
  congrArg Subtype.val (AddEquiv.apply_symm_apply _ _)

/-- The pullback map on supported sections restricts, on the inverse image of the canonical open
of the support, to the pullback of the section along the unit: this determines it, the
restriction being injective. -/
public theorem fiberBaseChangeSectionsMap_restrict (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (s : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) :
    ((abPullback.{u, v} B p).obj F).obj.map (openObjectHomOfLE B X'.obj X'.property
          (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupportOpen_le B p f' f g sq V E)).op
        (fiberBaseChangeSectionsMap B p f' f g sq V E F s).val =
      pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F _ _
        (fiberBaseChangeSupportArrow B p f' f g sq V E) s.val :=
  (locallyClosedSupportEquiv_restrict B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
      (baseChange B f' (baseChange B g V)) (fiberBaseChangeSupport B p f' f g sq V E).1
      (supportOpen B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupport B p f' f g sq V E).1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V)
          (fiberBaseChangeSupport B p f' f g sq V E)))
      (fiberBaseChangeSupportOpen B p f' f g sq V E)
      (subset_supportOpen B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupport B p f' f g sq V E).1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V)
          (fiberBaseChangeSupport B p f' f g sq V E)))
      (fiberBaseChangeSupport_subset_open B p f' f g sq V E)
      (isClosed_supportOpen_preimage B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupport B p f' f g sq V E).1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V)
          (fiberBaseChangeSupport B p f' f g sq V E)))
      (isClosed_fiberBaseChangeSupport_preimage B p f' f g sq V E)
      (fiberBaseChangeSupportOpen_le B p f' f g sq V E)
      (fiberBaseChangeSectionsMap B p f' f g sq V E F s)).symm.trans
    (fiberBaseChangeSectionsMap_val B p f' f g sq V E F s)

/-- Enlarging the support shrinks the inverse image of its canonical open. -/
public theorem fiberBaseChangeSupportOpen_antitone (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) {E E₁ : FiniteSupport B f V} (hle : E ≤ E₁) :
    fiberBaseChangeSupportOpen B p f' f g sq V E₁ ≤
      fiberBaseChangeSupportOpen B p f' f g sq V E := by
  intro x hx
  exact supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E₁.1
    (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E₁) hle
    (finiteSupport_closedWithin B f V E E₁ hle) hx

/-- The restrictions of the comparison of the two étale base changes to the canonical opens of
a support and of a larger one are compatible with the inclusions of those opens. -/
public theorem fiberBaseChangeOpenMap_transition (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) {E E₁ : FiniteSupport B f V} (hle : E ≤ E₁) :
    (openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupportOpen_antitone B p f' f g sq V hle)).hom.left ≫
        fiberBaseChangeOpenMap B p f' f g sq V E =
      fiberBaseChangeOpenMap B p f' f g sq V E₁ ≫
        (openObjectHomOfLE B X.obj X.property (baseChange B f V)
          (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E₁.1
            (finiteSupport_isLocallyClosed B f V E)
            (finiteSupport_isLocallyClosed B f V E₁) hle
            (finiteSupport_closedWithin B f V E E₁ hle))).hom.left := by
  apply B.inclusion.map_injective
  rw [Functor.map_comp, Functor.map_comp, fiberBaseChangeOpenMap_map,
    fiberBaseChangeOpenMap_map,
    show B.inclusion.map (openObjectHomOfLE B X'.obj X'.property
        (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupportOpen_antitone B p f' f g sq V hle)).hom.left =
      Scheme.homOfLE _ (fiberBaseChangeSupportOpen_antitone B p f' f g sq V hle) from
      openObjectHomOfLE_map B X'.obj X'.property (baseChange B f' (baseChange B g V)) _,
    show B.inclusion.map (openObjectHomOfLE B X.obj X.property (baseChange B f V)
        (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E₁.1
          (finiteSupport_isLocallyClosed B f V E)
          (finiteSupport_isLocallyClosed B f V E₁) hle
          (finiteSupport_closedWithin B f V E E₁ hle))).hom.left =
      Scheme.homOfLE _ (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E₁.1
        (finiteSupport_isLocallyClosed B f V E)
        (finiteSupport_isLocallyClosed B f V E₁) hle
        (finiteSupport_closedWithin B f V E E₁ hle)) from
      openObjectHomOfLE_map B X.obj X.property (baseChange B f V) _,
    ← cancel_mono (supportOpen B X.obj X.property (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)).ι,
    Category.assoc, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι,
    ← Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]

/-- The comparison arrows of a support and of a larger one are compatible with the inclusion of
the inverse images of the canonical opens and with the base change of the inclusion of the
canonical opens. -/
public theorem fiberBaseChangeSupportArrow_transition (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) {E E₁ : FiniteSupport B f V} (hle : E ≤ E₁) :
    openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupportOpen_antitone B p f' f g sq V hle) ≫
        fiberBaseChangeSupportArrow B p f' f g sq V E =
      fiberBaseChangeSupportArrow B p f' f g sq V E₁ ≫
        (smallEtaleBaseChange B p).map (openObjectHomOfLE B X.obj X.property
          (baseChange B f V)
          (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E₁.1
            (finiteSupport_isLocallyClosed B f V E)
            (finiteSupport_isLocallyClosed B f V E₁) hle
            (finiteSupport_closedWithin B f V E E₁ hle))) := by
  refine baseChangeObj_hom_ext B p ?_
  show ((openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupportOpen_antitone B p f' f g sq V hle)).hom.left ≫
        (fiberBaseChangeSupportArrow B p f' f g sq V E).hom.left) ≫ _ =
      ((fiberBaseChangeSupportArrow B p f' f g sq V E₁).hom.left ≫
        ((smallEtaleBaseChange B p).map (openObjectHomOfLE B X.obj X.property
          (baseChange B f V)
          (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E₁.1
            (finiteSupport_isLocallyClosed B f V E)
            (finiteSupport_isLocallyClosed B f V E₁) hle
            (finiteSupport_closedWithin B f V E E₁ hle)))).hom.left) ≫ _
  rw [Category.assoc, fiberBaseChangeSupportArrow_proj, Category.assoc,
    baseChangeObjProjection_naturality, ← Category.assoc,
    fiberBaseChangeSupportArrow_proj, fiberBaseChangeOpenMap_transition B p f' f g sq V hle]

/-- Base change of supports is monotone. -/
public theorem fiberBaseChangeSupport_mono (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) {E E₁ : FiniteSupport B f V} (hle : E ≤ E₁) :
    fiberBaseChangeSupport B p f' f g sq V E ≤ fiberBaseChangeSupport B p f' f g sq V E₁ :=
  Set.preimage_mono hle

/-- **Stacks 0F5J.** The pullback map on supported sections is compatible with the transition
maps of Stacks 0F6H: enlarging the support commutes with base change. This is what makes the
pullback maps a map out of the colimit defining `f_{p!}F`. -/
@[stacks 0F5J "compatibility of the pullback map with the transitions of the colimit"]
public theorem fiberBaseChangeSectionsMap_transition (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) {E E₁ : FiniteSupport B f V} (hle : E ≤ E₁)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (fiberBaseChangeSectionsMap B p f' f g sq V E₁ F).comp
        (supportedSectionsMap B X.obj X.property F (baseChange B f V) E.1 E₁.1
          (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E₁) hle
          (finiteSupport_closedWithin B f V E E₁ hle)) =
      (supportedSectionsMap B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
          (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupport B p f' f g sq V E).1
          (fiberBaseChangeSupport B p f' f g sq V E₁).1
          (finiteSupport_isLocallyClosed B f' (baseChange B g V)
            (fiberBaseChangeSupport B p f' f g sq V E))
          (finiteSupport_isLocallyClosed B f' (baseChange B g V)
            (fiberBaseChangeSupport B p f' f g sq V E₁))
          (fiberBaseChangeSupport_mono B p f' f g sq V hle)
          (finiteSupport_closedWithin B f' (baseChange B g V)
            (fiberBaseChangeSupport B p f' f g sq V E)
            (fiberBaseChangeSupport B p f' f g sq V E₁)
            (fiberBaseChangeSupport_mono B p f' f g sq V hle))).comp
        (fiberBaseChangeSectionsMap B p f' f g sq V E F) := by
  refine AddMonoidHom.ext fun s => ?_
  refine supportedSections_ext B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
    (baseChange B f' (baseChange B g V)) (fiberBaseChangeSupport B p f' f g sq V E₁).1
    (finiteSupport_isLocallyClosed B f' (baseChange B g V)
      (fiberBaseChangeSupport B p f' f g sq V E₁))
    (fiberBaseChangeSupportOpen B p f' f g sq V E₁)
    (fiberBaseChangeSupport_subset_open B p f' f g sq V E₁)
    (isClosed_fiberBaseChangeSupport_preimage B p f' f g sq V E₁)
    (fiberBaseChangeSupportOpen_le B p f' f g sq V E₁) ?_
  rw [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    fiberBaseChangeSectionsMap_restrict, supportedSectionsMap_apply, supportedSectionsMap_apply,
    pullbackSectionAlongHom_map, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    openObjectHomOfLE_comp,
    ← openObjectHomOfLE_comp B X'.obj X'.property (baseChange B f' (baseChange B g V))
      (fiberBaseChangeSupportOpen_antitone B p f' f g sq V hle)
      (fiberBaseChangeSupportOpen_le B p f' f g sq V E),
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    fiberBaseChangeSectionsMap_restrict, pullbackSectionAlongHom_restrict,
    fiberBaseChangeSupportArrow_transition B p f' f g sq V hle]

/-- The pullback map on supported sections, read as a morphism from the value of the diagram of
supported sections at a support to its value at the base change of that support. -/
public def fiberBaseChangeDiagramMap (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (E : FiniteSupport B f V) :
    (finiteSupportDiagram B f F V).obj E ⟶
      (finiteSupportDiagram B f' ((abPullback.{u, v} B p).obj F) (baseChange B g V)).obj
        (fiberBaseChangeSupport B p f' f g sq V E) :=
  AddCommGrpCat.ofHom (fiberBaseChangeSectionsMap B p f' f g sq V E F)

/-- **Stacks 0F5J.** The pullback map on supported sections is functorial in the abelian
sheaf: a morphism of sheaves on `X` acts on the pullbacks through its inverse image. -/
@[stacks 0F5J "functoriality in the sheaf of the pullback map on supported sections"]
public theorem fiberBaseChangeSectionsMap_sheafMap (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) :
    (fiberBaseChangeSectionsMap B p f' f g sq V E G).comp
        (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)) =
      (supportedSectionsSheafMap B X'.obj X'.property ((abPullback.{u, v} B p).map φ)
          (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupport B p f' f g sq V E).1
          (finiteSupport_isLocallyClosed B f' (baseChange B g V)
            (fiberBaseChangeSupport B p f' f g sq V E))).comp
        (fiberBaseChangeSectionsMap B p f' f g sq V E F) := by
  refine AddMonoidHom.ext fun s => ?_
  refine supportedSections_ext B X'.obj X'.property ((abPullback.{u, v} B p).obj G)
    (baseChange B f' (baseChange B g V)) (fiberBaseChangeSupport B p f' f g sq V E).1
    (finiteSupport_isLocallyClosed B f' (baseChange B g V)
      (fiberBaseChangeSupport B p f' f g sq V E))
    (fiberBaseChangeSupportOpen B p f' f g sq V E)
    (fiberBaseChangeSupport_subset_open B p f' f g sq V E)
    (isClosed_fiberBaseChangeSupport_preimage B p f' f g sq V E)
    (fiberBaseChangeSupportOpen_le B p f' f g sq V E) ?_
  have hval : (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E) s).val =
      φ.hom.app (op (openObject B X.obj X.property (baseChange B f V)
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E)))) s.val := rfl
  rw [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    fiberBaseChangeSectionsMap_restrict, hval]
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    (((abPullback.{u, v} B p).map φ).hom.naturality
      (openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupportOpen_le B p f' f g sq V E)).op)
    (fiberBaseChangeSectionsMap B p f' f g sq V E F s).val)
  rw [ConcreteCategory.comp_apply, fiberBaseChangeSectionsMap_restrict]
  exact pullbackSectionAlongHom_sheafMap.{u, v} B p φ _ _
    (fiberBaseChangeSupportArrow B p f' f g sq V E) s.val

/-- The cocone on the diagram of supported sections over `V` whose vertex is the group of
finite-support sections of `p⁻¹F` over `V'`: a support goes to its base change and a supported
section to its pullback. -/
public def fiberBaseChangeCocone (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    Cocone (finiteSupportDiagram B f F V) where
  pt := finiteSupportSections B f' ((abPullback.{u, v} B p).obj F) (baseChange B g V)
  ι :=
  { app := fun E => fiberBaseChangeDiagramMap B p f' f g sq V F E ≫
      colimit.ι (finiteSupportDiagram B f' ((abPullback.{u, v} B p).obj F) (baseChange B g V))
        (fiberBaseChangeSupport B p f' f g sq V E)
    naturality := by
      intro E E₁ h
      have h1 : (finiteSupportDiagram B f F V).map h ≫
          fiberBaseChangeDiagramMap B p f' f g sq V F E₁ =
          fiberBaseChangeDiagramMap B p f' f g sq V F E ≫
            (finiteSupportDiagram B f' ((abPullback.{u, v} B p).obj F)
              (baseChange B g V)).map
              (homOfLE (fiberBaseChangeSupport_mono B p f' f g sq V (leOfHom h))) :=
        AddCommGrpCat.hom_ext <| fiberBaseChangeSectionsMap_transition B p f' f g sq V (leOfHom h) F
      refine Eq.trans ?_ (Category.comp_id _).symm
      rw [← Category.assoc, h1, Category.assoc, colimit.w] }

/-- **Stacks 0F5J.** The base-change map on finite-support sections over an étale test object
`V` of `Y`: the generator of a support `Z` carrying a section `s` goes to the generator of the
base change of `Z` carrying the pullback of `s`. This is the map `c` of the source, over `V`. -/
@[stacks 0F5J "the map c on finite-support sections over a test object"]
public def fiberBaseChangeColimitMap (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    finiteSupportSections B f F V ⟶
      finiteSupportSections B f' ((abPullback.{u, v} B p).obj F) (baseChange B g V) :=
  colimit.desc (finiteSupportDiagram B f F V) (fiberBaseChangeCocone B p f' f g sq V F)

/-- The base-change map on finite-support sections, on a colimit generator. -/
@[simp]
public theorem fiberBaseChangeColimitMap_ι (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (E : FiniteSupport B f V) :
    colimit.ι (finiteSupportDiagram B f F V) E ≫
        fiberBaseChangeColimitMap B p f' f g sq V F =
      fiberBaseChangeDiagramMap B p f' f g sq V F E ≫
        colimit.ι (finiteSupportDiagram B f' ((abPullback.{u, v} B p).obj F)
          (baseChange B g V)) (fiberBaseChangeSupport B p f' f g sq V E) :=
  colimit.ι_desc _ _

/-- **Stacks 0F5J.** The base-change map on finite-support sections over an étale test object
is functorial in the abelian sheaf. -/
@[stacks 0F5J "functoriality in the sheaf of the map c over a test object"]
public theorem fiberBaseChangeColimitMap_natural (sq : IsPullback p f' f g)
    (V : SmallEtale B Y.obj Y.property)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) :
    colim.map (finiteSupportDiagramMap B f φ V) ≫
        fiberBaseChangeColimitMap B p f' f g sq V G =
      fiberBaseChangeColimitMap B p f' f g sq V F ≫
        colim.map (finiteSupportDiagramMap B f' ((abPullback.{u, v} B p).map φ)
          (baseChange B g V)) := by
  refine colimit.hom_ext fun E => ?_
  have hsq : (finiteSupportDiagramMap B f φ V).app E ≫
      fiberBaseChangeDiagramMap B p f' f g sq V G E =
      fiberBaseChangeDiagramMap B p f' f g sq V F E ≫
        (finiteSupportDiagramMap B f' ((abPullback.{u, v} B p).map φ)
          (baseChange B g V)).app (fiberBaseChangeSupport B p f' f g sq V E) :=
    AddCommGrpCat.hom_ext <| fiberBaseChangeSectionsMap_sheafMap B p f' f g sq V E φ
  rw [← Category.assoc, colimit.ι_map, Category.assoc, fiberBaseChangeColimitMap_ι,
    ← Category.assoc, hsq, Category.assoc]
  conv_rhs => rw [← Category.assoc, fiberBaseChangeColimitMap_ι, Category.assoc, colimit.ι_map]

end Square

end AlgebraicGeometry.SmallEtale

end
