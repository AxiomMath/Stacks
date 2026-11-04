module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# Étale neighbourhoods of a geometric point of an algebraic space

An *étale neighbourhood* of a geometric point `x` of an algebraic space `F` over `S` is an
algebraic space `U` over `S` which is étale over `F`, together with a lift of `x` to `U`
(`AlgebraicGeometry.Space.EtaleNeighborhood`); a morphism of étale neighbourhoods
(`AlgebraicGeometry.Space.EtaleNeighborhood.Hom`) is a morphism over `F` preserving the lift.
Unlike the *small* étale neighbourhoods of `AlgebraicGeometry.Space.SmallEtaleNeighborhood`,
which are the objects of the small étale site and hence scheme charts, `U` here is an arbitrary
algebraic space étale over `F`.

## Main definitions

* `AlgebraicGeometry.Space.EtaleNeighborhood.self` is `F` itself, étale over itself by the
  identity; `AlgebraicGeometry.Space.EtaleNeighborhood.isTerminalSelf` says it is terminal.
* `AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is the comparison functor from
  the small étale neighbourhoods.
* `AlgebraicGeometry.Space.etaleSiteObjectOfNeighborhood` reads an étale neighbourhood as an
  object of the spaces-étale site, and
  `AlgebraicGeometry.Space.etaleNeighborhoodOfSitePoint` reads a pointed object of the
  spaces-étale site as an étale neighbourhood.

## Main results

* `AlgebraicGeometry.Space.EtaleNeighborhood.exists_common_refinement`: two étale
  neighbourhoods have a common refinement, and
  `AlgebraicGeometry.Space.EtaleNeighborhood.exists_equalizing_refinement`: two parallel
  morphisms of étale neighbourhoods are equalized by a refinement.
* `AlgebraicGeometry.Space.EtaleNeighborhood.instIsCofiltered`: the category of étale
  neighbourhoods of a geometric point is cofiltered, and
  `AlgebraicGeometry.Space.EtaleNeighborhood.instInitialOfSmallEtale`: the comparison from
  the small étale neighbourhoods is initial.
* `AlgebraicGeometry.Space.exists_lift_to_etaleCovering`: a covering of an étale
  neighbourhood in the spaces-étale site has a member which is again an étale neighbourhood,
  with the covering arrow a morphism of étale neighbourhoods.
* `AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is fully faithful, and
  `AlgebraicGeometry.Space.EtaleNeighborhood.exists_smallEtaleNeighborhood_refinement` says
  every étale neighbourhood is refined by one in its image.

## Implementation notes

The lift of the geometric point is a section of `U` over the field spectrum underlying `x`,
so it has the same source as the section defining `x`, and the compatibility condition
`point_comp` is the commuting triangle of the definition. In
`AlgebraicGeometry.Space.SmallEtaleNeighborhood` the lift is instead a morphism of the site,
the neighbourhood being representable there; under Yoneda the two agree.

## References

* [Stacks Project, Tag 04JV](https://stacks.math.columbia.edu/tag/04JV)
* [Stacks Project, Tag 04JW](https://stacks.math.columbia.edu/tag/04JW)
* [Stacks Project, Tag 04JX](https://stacks.math.columbia.edu/tag/04JX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace EtaleNeighborhood

variable {B S hS F}
variable {hF : IsAlgebraicSpace B S hS F} {x : GeometricPoint B S hS F}

/-- The algebraic space `F` is an étale neighbourhood of any of its geometric points, by the
identity morphism. -/
def self (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    EtaleNeighborhood B S hS F hF x where
  space := F
  isAlgebraicSpace := hF
  toBase := 𝟙 F
  etale_toBase := isEtale_of_isIso B S hS (𝟙 F)
  point := x.val.value
  point_comp := by simp

/-- The category of étale neighbourhoods of a geometric point is inhabited by
`AlgebraicGeometry.Space.EtaleNeighborhood.self`. -/
instance : Inhabited (EtaleNeighborhood B S hS F hF x) := ⟨self hF x⟩

/-- The category of étale neighbourhoods of a geometric point is nonempty. -/
instance : Nonempty (EtaleNeighborhood B S hS F hF x) := ⟨self hF x⟩

/-- `AlgebraicGeometry.Space.EtaleNeighborhood.self` is a terminal étale neighbourhood: the unique
morphism to it from `U` is the structure morphism of `U`. -/
def isTerminalSelf (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    IsTerminal (self hF x) :=
  IsTerminal.ofUniqueHom
    (fun U =>
      { hom := (U.toBase : U.space ⟶ F)
        over := Category.comp_id _
        point_comp := U.point_comp })
    (fun _ f => Hom.ext ((Category.comp_id f.hom).symm.trans f.over))

/-! ### Comparison with the small étale neighbourhoods -/

/-- A small étale neighbourhood of a geometric point — an object of the small étale site of
`F` with a lift of the point, as in Stacks 04JY — is an étale neighbourhood in the sense of
Stacks 04JV. The underlying data is unchanged: the neighbourhood is the presheaf represented
by the chart, and the lift of the point is the same morphism, read through Yoneda. -/
noncomputable def ofSmallEtale (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    SmallEtaleNeighborhood x ⥤ EtaleNeighborhood B S hS F hF x where
  obj U :=
    { space := yoneda.obj U.chart.obj.left
      isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS _
      toBase := U.chart.obj.hom
      etale_toBase := isEtale_of_presheaf_etale B S hS U.chart.property
      point := U.point
      point_comp := U.point_comp }
  map {U V} f :=
    { hom := yoneda.map f.hom.hom.left
      over := CostructuredArrow.w f.hom.hom
      point_comp := f.point_comp }
  map_id U := Hom.ext (by simp)
  map_comp f g := Hom.ext (by simp)

/-- The space of the étale neighbourhood `ofSmallEtale` attaches to a small étale neighbourhood
is the presheaf represented by its chart. -/
@[simp]
theorem ofSmallEtale_obj_space (U : SmallEtaleNeighborhood x) :
    ((ofSmallEtale hF x).obj U).space = yoneda.obj U.chart.obj.left := rfl

/-- The structure morphism of the étale neighbourhood `ofSmallEtale` attaches to a small étale
neighbourhood is the structure morphism of its chart. -/
@[simp]
theorem ofSmallEtale_obj_toBase (U : SmallEtaleNeighborhood x) :
    ((ofSmallEtale hF x).obj U).toBase = U.chart.obj.hom := rfl

/-- The lift of the point in the étale neighbourhood `ofSmallEtale` attaches to a small étale
neighbourhood is the lift of the small one. -/
@[simp]
theorem ofSmallEtale_obj_point (U : SmallEtaleNeighborhood x) :
    ((ofSmallEtale hF x).obj U).point = U.point := rfl

/-- `ofSmallEtale` sends a morphism of small étale neighbourhoods to the image under Yoneda of
the underlying morphism of charts. -/
@[simp]
theorem ofSmallEtale_map_hom {U V : SmallEtaleNeighborhood x} (f : U ⟶ V) :
    ((ofSmallEtale hF x).map f).hom = yoneda.map f.hom.hom.left := rfl

/-- `AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is faithful. -/
instance : (ofSmallEtale hF x).Faithful where
  map_injective {U V} f g h := by
    have h' : yoneda.map f.hom.hom.left = yoneda.map g.hom.hom.left := congrArg Hom.hom h
    exact SmallEtaleNeighborhood.Hom.ext (ObjectProperty.hom_ext _
      (CostructuredArrow.hom_ext _ _ (yoneda.map_injective h')))

/-- `AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is full. -/
instance : (ofSmallEtale hF x).Full where
  map_surjective {U V} h := by
    let k : yoneda.obj U.chart.obj.left ⟶ yoneda.obj V.chart.obj.left := h.hom
    have hk : yoneda.map (yoneda.preimage k) = k := yoneda.map_preimage k
    have hover : k ≫ V.chart.obj.hom = U.chart.obj.hom := h.over
    have hpoint : k.app (Opposite.op x.val.siteObject) U.point = V.point := h.point_comp
    refine ⟨⟨ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage k) ?_), ?_⟩, ?_⟩
    · rwa [hk]
    · change U.point ≫ yoneda.preimage k = V.point
      exact (congrArg (fun k' => k'.app (Opposite.op x.val.siteObject) U.point) hk).trans hpoint
    · exact Hom.ext hk

/-! ### Refinements -/

/-- Two étale neighbourhoods of a geometric point have a common refinement. -/
@[stacks 04JW "common_refinement"]
theorem exists_common_refinement (U V : EtaleNeighborhood B S hS F hF x) :
    ∃ W : EtaleNeighborhood B S hS F hF x, Nonempty ((W ⟶ U) × (W ⟶ V)) := by
  let U' : AlgebraicSpaces B S hS := ⟨U.space, U.isAlgebraicSpace⟩
  let V' : AlgebraicSpaces B S hS := ⟨V.space, V.isAlgebraicSpace⟩
  let F' : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let f : U' ⟶ F' := ObjectProperty.homMk U.toBase
  let g : V' ⟶ F' := ObjectProperty.homMk V.toBase
  let P := AlgebraicSpaces.fiberProduct B S hS f g
  let pU : P ⟶ U' := ObjectProperty.homMk (pullback.fst U.toBase V.toBase)
  let pV : P ⟶ V' := ObjectProperty.homMk (pullback.snd U.toBase V.toBase)
  have hpb : IsPullback pU pV f g := by
    simpa [P, pU, pV, f, g] using AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  let point := (pullbackObjIso U.toBase V.toBase (Opposite.op x.val.siteObject)).inv
    ((Types.pullbackIsoPullback (U.toBase.app (Opposite.op x.val.siteObject))
        (V.toBase.app (Opposite.op x.val.siteObject))).inv
      ⟨⟨U.point, V.point⟩, by rw [U.point_comp, V.point_comp]⟩)
  have hpU_point : pU.hom.app (Opposite.op x.val.siteObject) point = U.point := by
    show (pullback.fst U.toBase V.toBase).app (Opposite.op x.val.siteObject) point = _
    dsimp only [point]
    rw [← CategoryTheory.comp_apply, pullbackObjIso_inv_comp_fst]
    simp
  have hpV_point : pV.hom.app (Opposite.op x.val.siteObject) point = V.point := by
    show (pullback.snd U.toBase V.toBase).app (Opposite.op x.val.siteObject) point = _
    dsimp only [point]
    rw [← CategoryTheory.comp_apply, pullbackObjIso_inv_comp_snd]
    simp
  let W : EtaleNeighborhood B S hS F hF x :=
    { space := P.obj
      isAlgebraicSpace := P.property
      toBase := pV.hom ≫ V.toBase
      etale_toBase := isEtale_comp B S hS
        (isEtale_of_isPullback B S hS pU pV f g hpb U.etale_toBase) V.etale_toBase
      point := point
      point_comp := by
        show V.toBase.app (Opposite.op x.val.siteObject)
          (pV.hom.app (Opposite.op x.val.siteObject) point) = x.val.value
        rw [hpV_point, V.point_comp] }
  refine ⟨W, ⟨⟨pU.hom, ?_, ?_⟩, ⟨pV.hom, rfl, ?_⟩⟩⟩
  · simpa [f, g] using congrArg (fun k => k.hom) hpb.w
  · simpa [W] using hpU_point
  · simpa [W] using hpV_point

/-- Two parallel morphisms of étale neighbourhoods of a geometric point are equalized by a
further étale neighbourhood. -/
@[stacks 04JW "equalizing_refinement"]
theorem exists_equalizing_refinement {U V : EtaleNeighborhood B S hS F hF x} (h₁ h₂ : U ⟶ V) :
    ∃ (W : EtaleNeighborhood B S hS F hF x) (h : W ⟶ U), h ≫ h₁ = h ≫ h₂ := by
  let X : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let U₀ : AlgebraicSpaces B S hS := ⟨U.space, U.isAlgebraicSpace⟩
  let V₀ : AlgebraicSpaces B S hS := ⟨V.space, V.isAlgebraicSpace⟩
  let v₀ : V₀ ⟶ X := ObjectProperty.homMk V.toBase
  let T : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS v₀ v₀
  let t₁ : T ⟶ V₀ := ObjectProperty.homMk (pullback.fst v₀.hom v₀.hom)
  let t₂ : T ⟶ V₀ := ObjectProperty.homMk (pullback.snd v₀.hom v₀.hom)
  let m : U₀ ⟶ T := ObjectProperty.homMk
    (pullback.lift h₁.hom h₂.hom (h₁.over.trans h₂.over.symm))
  let δ : V₀ ⟶ T := ObjectProperty.homMk (pullback.lift (𝟙 V.space) (𝟙 V.space) (by simp))
  let W₀ : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS m δ
  let w₁ : W₀ ⟶ U₀ := ObjectProperty.homMk (pullback.fst m.hom δ.hom)
  let w₂ : W₀ ⟶ V₀ := ObjectProperty.homMk (pullback.snd m.hom δ.hom)
  have hTpb : IsPullback t₁ t₂ v₀ v₀ := by
    simpa only [t₁, t₂] using AlgebraicSpaces.isPullback_fiberProduct B S hS v₀ v₀
  have ht₁ : IsEtale B S hS t₁.hom :=
    isEtale_of_isPullback B S hS t₂ t₁ v₀ v₀ hTpb.flip V.etale_toBase
  have hTbaseEt : IsEtale B S hS (t₁.hom ≫ V.toBase) :=
    isEtale_comp B S hS ht₁ V.etale_toBase
  have hmt₁ : m.hom ≫ t₁.hom = h₁.hom := pullback.lift_fst _ _ _
  have hmt₂ : m.hom ≫ t₂.hom = h₂.hom := pullback.lift_snd _ _ _
  have hmover : m.hom ≫ (t₁.hom ≫ V.toBase) = U.toBase := by
    rw [← Category.assoc, hmt₁, h₁.over]
  have hm : IsEtale B S hS m.hom :=
    isEtale_of_isEtale_over B S hS U.isAlgebraicSpace T.property hF m.hom U.toBase
      (t₁.hom ≫ V.toBase) U.etale_toBase hTbaseEt hmover
  have hWpb : IsPullback w₁ w₂ m δ := by
    simpa [w₁, w₂, W₀, AlgebraicSpaces.fiberProduct] using
      AlgebraicSpaces.isPullback_fiberProduct B S hS m δ
  have hw₂ : IsEtale B S hS w₂.hom :=
    isEtale_of_isPullback B S hS w₁ w₂ m δ hWpb hm
  have hw₂base : IsEtale B S hS (w₂.hom ≫ V.toBase) :=
    isEtale_comp B S hS hw₂ V.etale_toBase
  let A := x.val.siteObject
  let pU : yoneda.obj A ⟶ U.space := yonedaEquiv.symm U.point
  let pV : yoneda.obj A ⟶ V.space := yonedaEquiv.symm V.point
  have hpU : ∀ k : U ⟶ V, pU ≫ k.hom = pV := fun k => by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    simpa [A, pV] using k.point_comp
  have hδ₁ : δ.hom ≫ t₁.hom = 𝟙 V.space := pullback.lift_fst _ _ _
  have hδ₂ : δ.hom ≫ t₂.hom = 𝟙 V.space := pullback.lift_snd _ _ _
  have hpointCone : pU ≫ m.hom = pV ≫ δ.hom := by
    apply pullback.hom_ext
    · show pU ≫ m.hom ≫ t₁.hom = pV ≫ δ.hom ≫ t₁.hom
      simp only [hmt₁, hδ₁, Category.comp_id, hpU]
    · show pU ≫ m.hom ≫ t₂.hom = pV ≫ δ.hom ≫ t₂.hom
      simp only [hmt₂, hδ₂, Category.comp_id, hpU]
  let pW : yoneda.obj A ⟶ W₀.obj := pullback.lift pU pV hpointCone
  have hpW₁ : pW ≫ w₁.hom = pU := pullback.lift_fst _ _ _
  have hpW₂ : pW ≫ w₂.hom = pV := pullback.lift_snd _ _ _
  have hw : ∀ (t : T ⟶ V₀) (k : U ⟶ V), m.hom ≫ t.hom = k.hom → δ.hom ≫ t.hom = 𝟙 V.space →
      w₁.hom ≫ k.hom = w₂.hom := by
    intro t k hmt hδt
    have hpair := congrArg (fun k : W₀ ⟶ T => (k ≫ t).hom) hWpb.w
    change (w₁.hom ≫ m.hom) ≫ t.hom = (w₂.hom ≫ δ.hom) ≫ t.hom at hpair
    rwa [Category.assoc, hmt, Category.assoc, hδt, Category.comp_id] at hpair
  have hw₁h₁ := hw t₁ h₁ hmt₁ hδ₁
  have hw₁h₂ := hw t₂ h₂ hmt₂ hδ₂
  let W : EtaleNeighborhood B S hS F hF x :=
    { space := W₀.obj
      isAlgebraicSpace := W₀.property
      toBase := w₂.hom ≫ V.toBase
      etale_toBase := hw₂base
      point := yonedaEquiv (X := A) (F := W₀.obj) pW
      point_comp := by
        show (w₂.hom ≫ V.toBase).app (Opposite.op A)
          (yonedaEquiv (X := A) (F := W₀.obj) pW) = x.val.value
        calc
          (w₂.hom ≫ V.toBase).app (Opposite.op A)
              (yonedaEquiv (X := A) (F := W₀.obj) pW) =
              yonedaEquiv (pW ≫ (w₂.hom ≫ V.toBase)) :=
            (yonedaEquiv_comp pW (w₂.hom ≫ V.toBase)).symm
          _ = yonedaEquiv (pV ≫ V.toBase) := by rw [← Category.assoc, hpW₂]
          _ = V.toBase.app (Opposite.op A) V.point := by
            rw [yonedaEquiv_comp]; simp [pV]
          _ = x.val.value := V.point_comp }
  refine ⟨W, ⟨w₁.hom, ?_, ?_⟩, ?_⟩
  · calc
      w₁.hom ≫ U.toBase = w₁.hom ≫ (h₁.hom ≫ V.toBase) := by rw [← h₁.over]
      _ = w₂.hom ≫ V.toBase := by rw [← Category.assoc, hw₁h₁]
  · show w₁.hom.app (Opposite.op A) (yonedaEquiv (X := A) (F := W₀.obj) pW) = U.point
    rw [← yonedaEquiv_comp pW w₁.hom, hpW₁]
    exact Equiv.apply_symm_apply _ _
  · exact Hom.ext (hw₁h₁.trans hw₁h₂.symm)

/-- Every étale neighbourhood of a geometric point is refined by one coming from the small étale
site, i.e. by one in the image of `AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale`. -/
@[stacks 04JW "scheme_refinement, in the small étale site"]
theorem exists_smallEtaleNeighborhood_refinement (U : EtaleNeighborhood B S hS F hF x) :
    ∃ V : SmallEtaleNeighborhood x, Nonempty ((ofSmallEtale hF x).obj V ⟶ U) := by
  obtain ⟨V, atlas, hatlas_surjective, hatlas_etale⟩ := U.isAlgebraicSpace.exists_atlas
  let P := x.val.siteObject
  let g : yoneda.obj P ⟶ U.space := yonedaEquiv.symm U.point
  let hrep := hatlas_surjective.1
  let W := hrep.pullback g
  let snd := hrep.snd g
  let fst := hrep.fst g
  have hpb : IsPullback fst (yoneda.map snd) atlas g := hrep.isPullback g
  have : Surjective ((BigFppfOver.toScheme B S hS).map snd) :=
    hatlas_surjective.property_snd g
  have : Etale ((BigFppfOver.toScheme B S hS).map snd) :=
    hatlas_etale.property g fst snd hpb
  have : IsAlgClosed x.val.carrier := x.property
  obtain ⟨sec, hsec⟩ := exists_section_of_surjective_etale_spec x.val.carrier
    ((BigFppfOver.toScheme B S hS).map snd)
  let secInclusion : B.inclusion.obj P.left ⟶ B.inclusion.obj W.left := sec
  change secInclusion ≫ B.inclusion.map snd.left = 𝟙 _ at hsec
  have hleft : B.inclusion.preimage secInclusion ≫ snd.left = 𝟙 P.left := by
    apply B.inclusion.map_injective
    simpa only [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_id] using hsec
  let secOver : P ⟶ W := Over.homMk (B.inclusion.preimage secInclusion) (by
    rw [← Over.w snd, ← Category.assoc, hleft, Category.id_comp])
  have hsecOver : secOver ≫ snd = 𝟙 P := by
    apply Over.OverMorphism.ext
    simpa [secOver] using hleft
  let toV : P ⟶ V := secOver ≫ yoneda.preimage fst
  let pointV : (yoneda.obj V).obj (Opposite.op P) := yonedaEquiv (yoneda.map toV)
  have hpointV : atlas.app (Opposite.op P) pointV = U.point := by
    have hcomp : yoneda.map toV ≫ atlas = g := by
      calc
        yoneda.map toV ≫ atlas = yoneda.map secOver ≫ fst ≫ atlas := by
          simp [toV, Category.assoc]
        _ = yoneda.map secOver ≫ yoneda.map snd ≫ g := by rw [hpb.w]
        _ = yoneda.map (secOver ≫ snd) ≫ g := by simp [Functor.map_comp, Category.assoc]
        _ = g := by simp [hsecOver]
    rw [← yonedaEquiv_comp, hcomp]
    simp [g]
  refine ⟨{ chart := ⟨CostructuredArrow.mk (atlas ≫ U.toBase),
              U.etale_toBase V atlas hatlas_etale⟩
            point := pointV
            point_comp := ?_ }, ⟨{ hom := atlas, over := rfl, point_comp := hpointV }⟩⟩
  show U.toBase.app (Opposite.op P) (atlas.app (Opposite.op P) pointV) = x.val.value
  rw [hpointV]
  exact U.point_comp

/-- The category of étale neighbourhoods of a geometric point is cofiltered. -/
instance instIsCofiltered : IsCofiltered (EtaleNeighborhood B S hS F hF x) where
  cone_objs U V := by
    obtain ⟨W, ⟨f, g⟩⟩ := exists_common_refinement U V
    exact ⟨W, f, g, trivial⟩
  cone_maps _ _ h₁ h₂ := exists_equalizing_refinement h₁ h₂
  nonempty := ⟨self hF x⟩

/-- `AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is initial. -/
instance instInitialOfSmallEtale : (ofSmallEtale hF x).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    exists_smallEtaleNeighborhood_refinement

end EtaleNeighborhood

/-! ### Coverings of an étale neighbourhood in the spaces-étale site -/

/-- Transport of a section of a presheaf along an equality of field-valued points: if a
morphism of presheaves carries `p` to `q`, then it carries the section of `p`, cast into the
site object of `q`, to the section of `q`. -/
private theorem fieldValue_map_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (p : FieldValuedPoint B S hS F) (q : FieldValuedPoint B S hS G)
    (h : FieldValuedPoint.map B S hS F f p = q) :
    f.app (Opposite.op q.siteObject)
      (cast (congrArg (fun z ↦ F.obj z)
        (congrArg (fun r : FieldValuedPoint B S hS G ↦ Opposite.op r.siteObject) h))
        p.value) = q.value := by
  cases h
  rfl

/-- The object of the spaces-étale site of `X` underlying an étale neighbourhood of a
geometric point of `X`: the neighbourhood's algebraic space, with its étale structure
morphism to `X`. -/
def etaleSiteObjectOfNeighborhood (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (U : EtaleNeighborhood B S hS X.1 X.2 x) :
    SpacesEtale B S hS X :=
  ⟨Over.mk (ObjectProperty.homMk U.toBase :
    (⟨U.space, U.isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ X),
    U.etale_toBase⟩

/-- An object `V` of the spaces-étale site of `X` together with a lift `v` of the geometric
point `x`, regarded as an étale neighbourhood of `x`. This is inverse to
`AlgebraicGeometry.Space.etaleSiteObjectOfNeighborhood` on the data. -/
def etaleNeighborhoodOfSitePoint (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (V : SpacesEtale B S hS X)
    (v : ((SpacesEtale.toSpaces B S hS X).obj V).1.obj (Opposite.op x.val.siteObject))
    (hv : (((SpacesEtale.inclusion B S hS X).obj V).hom.hom).app
      (Opposite.op x.val.siteObject) v = x.val.value) :
    EtaleNeighborhood B S hS X.1 X.2 x where
  space := ((SpacesEtale.toSpaces B S hS X).obj V).1
  isAlgebraicSpace := ((SpacesEtale.toSpaces B S hS X).obj V).2
  toBase := (((SpacesEtale.inclusion B S hS X).obj V).hom).hom
  etale_toBase := V.property
  point := v
  point_comp := hv

/-- A covering of an étale neighbourhood `U` of a geometric point `x` of an algebraic space `X`,
taken in the spaces-étale site of `X`, has a member to which `x` lifts; that member, with the
lift, is again an étale neighbourhood of `x`, and the covering arrow is a morphism of étale
neighbourhoods. -/
@[stacks 04JX]
theorem exists_lift_to_etaleCovering (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (U : EtaleNeighborhood B S hS X.1 X.2 x)
    (E : PreZeroHypercover.{u + 1} (etaleSiteObjectOfNeighborhood B S hS X x U))
    (hE : SpacesEtale.IsCovering B S hS X
      ⟨etaleSiteObjectOfNeighborhood B S hS X x U, E⟩) :
    ∃ i : E.I₀,
      ∃ uiBar : ((SpacesEtale.toSpaces B S hS X).obj (E.X i)).1.obj
        (Opposite.op x.val.siteObject),
      ∃ huiBar : (((SpacesEtale.inclusion B S hS X).obj (E.X i)).hom.hom).app
          (Opposite.op x.val.siteObject) uiBar = x.val.value,
      ∃ φ : etaleNeighborhoodOfSitePoint B S hS X x (E.X i) uiBar huiBar ⟶ U,
        EtaleNeighborhood.Hom.hom φ =
          ((SpacesEtale.toSpaces B S hS X).map (E.f i)).hom := by
  let uval : FieldValuedPoint B S hS U.space :=
    { carrier := x.val.carrier
      contained := x.val.contained
      toBase := x.val.toBase
      value := U.point }
  let xbarU : GeometricPoint B S hS U.space := ⟨uval, x.property⟩
  let p := uval.class B S hS U.space
  obtain ⟨i, y, hy⟩ := hE p
  let f := (E.f i).hom.left.hom
  let ui := ((SpacesEtale.toSpaces B S hS X).obj (E.X i)).obj
  let uiToX := (((SpacesEtale.inclusion B S hS X).obj (E.X i)).hom.hom)
  have hpoint : pointsMap B S hS ui f y = p := by
    simpa [p, ui, f] using hy
  have hfg : f ≫ U.toBase = uiToX := by
    simpa [f, uiToX, etaleSiteObjectOfNeighborhood] using
      congrArg (fun g ↦ g.hom) (E.f i).hom.w
  have hf : IsEtale B S hS f :=
    isEtale_of_isEtale_over B S hS (E.X i).obj.left.property U.isAlgebraicSpace X.property
      f uiToX U.toBase (E.X i).property U.etale_toBase hfg
  obtain ⟨ubar, _, hmap⟩ :=
    exists_geometricPoint_lift_of_isEtale B S hS
      ((SpacesEtale.toSpaces B S hS X).obj (E.X i)).2
      ((SpacesEtale.toSpaces B S hS X).obj
        (etaleSiteObjectOfNeighborhood B S hS X x U)).2
      f hf xbarU y hpoint
  let hmapSite :=
    congrArg (fun q : FieldValuedPoint B S hS U.space ↦ Opposite.op q.siteObject) hmap
  let uiBar : ui.obj (Opposite.op xbarU.val.siteObject) :=
    cast (congrArg (fun z ↦ ui.obj z) hmapSite) ubar.val.value
  have hvalue : f.app (Opposite.op xbarU.val.siteObject) uiBar = U.point :=
    fieldValue_map_eq f ubar.val xbarU.val hmap
  have hvalueAtX : f.app (Opposite.op x.val.siteObject) uiBar = U.point := by
    simpa [xbarU, uval, FieldValuedPoint.siteObject] using hvalue
  have hUiToXPoint : uiToX.app (Opposite.op x.val.siteObject) uiBar = x.val.value := by
    rw [← hfg]
    show U.toBase.app (Opposite.op x.val.siteObject)
      (f.app (Opposite.op x.val.siteObject) uiBar) = x.val.value
    exact hvalueAtX ▸ U.point_comp
  exact ⟨i, uiBar, hUiToXPoint, ⟨f, hfg, hvalueAtX⟩, rfl⟩

end AlgebraicGeometry.Space

end
