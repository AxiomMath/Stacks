module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Separation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation

/-!
# Testing a group algebraic space at its identity

Let `G ⟶ B` be a group algebraic space over an algebraic space `B`, locally of finite type.
Then `G ⟶ B` is locally quasi-finite, respectively unramified, exactly when it is quasi-finite,
respectively unramified, at the identity point over every point of `B`.

## Main results

* `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_at_identity`: **Stacks 0DSI**, the
  locally-quasi-finite characterization.
* `AlgebraicGeometry.Space.isUnramified_iff_at_identity`: **Stacks 0DSI**, the unramified
  characterization.

## Implementation notes

The identity point over a point `b` of `B` is the image of `b` under the map on point sets of
Tag 03BU induced by the morphism underlying the unit of the group object.

For local quasi-finiteness, one direction is the pointwise criterion, Stacks 040Z. For the
other, a point of `|G|` is represented by a field-valued point `Spec k ⟶ G` of Tag 03BU;
base changing `G` along the induced `Spec k ⟶ B` (Tag 043I) turns that representative into a
*global section* of the base-changed group algebraic space, whose identity point is the base
change of an identity point of `G`. Translation by a section
(`AlgebraicGeometry.Space.isQuasiFiniteAt_one_iff_at_section`) moves quasi-finiteness from the
identity to that section, and the quasi-finite locus commutes with base change
(`AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback`, Stacks 0ABM), so
both transfers are available.

Unramifiedness is proved without any pointwise base change, because the unramified locus is not
known here to commute with base change. Instead the identity section is pushed into the open
unramified locus `W` of Stacks 05W2, part (1): by hypothesis its image on points lies in `|W|`,
so it factors through `W` by Stacks 03IE. The restriction `W ⟶ B` of the structure morphism is
unramified — that is `isUnramified_ι_of_range_eq_setOf_isUnramifiedAt` below, which checks the
pointwise criterion of Stacks 03ZK on `W` by transporting, again through Stacks 03IE, an open
subspace of `G` on which the morphism is unramified into an open subspace of `W`. The induced
section of `W ⟶ B` is then a base change of the relative diagonal of `W ⟶ B`, which is an open
immersion by part (1) of Stacks 05W1; so the identity section of `G` is an open immersion, hence
so is the relative diagonal of `G ⟶ B`, of which it is a base change along `(g, g') ↦ g⁻¹ g'`,
and part (2) of Stacks 05W1 concludes.

## References

* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03ZK](https://stacks.math.columbia.edu/tag/03ZK)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
* [Stacks Project, Tag 0DSI](https://stacks.math.columbia.edu/tag/0DSI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hBs : IsAlgebraicSpace B S hS Bs}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
set_option maxHeartbeats 1000000 in
-- elaborating the `Over.pullback` lax-monoidal unit and its `pullback.fst` composites
/-- The unit of a base-changed group algebraic space projects to the unit of the original
one. -/
theorem one_baseChange_left_comp_fst (G : GroupAlgebraicSpace B S hS Bs hBs)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs) :
    (MonObj.one (X := (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)).left ≫
        pullback.fst G.obj.X.hom f =
      f ≫ (MonObj.one (X := G.obj.X)).left := by
  have hnat : ∀ {Z W : Over Bs} (k : Z ⟶ W),
      ((Over.pullback f).map k).left ≫ pullback.fst W.hom f =
        pullback.fst Z.hom f ≫ k.left := fun _ => pullback.lift_fst _ _ _
  have hcond : pullback.fst (𝟙_ (Over Bs)).hom f =
      pullback.snd (𝟙_ (Over Bs)).hom f ≫ f :=
    (Category.comp_id _).symm.trans pullback.condition
  have hw : (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over Bs)).hom f = 𝟙 Bt :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have hε : (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.fst (𝟙_ (Over Bs)).hom f = f := by
    rw [hcond, ← Category.assoc, hw]
    exact Category.id_comp f
  calc _ = (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
          (((Over.pullback f).map (MonObj.one (X := G.obj.X))).left ≫
            pullback.fst G.obj.X.hom f) := Category.assoc _ _ _
    _ = f ≫ (MonObj.one (X := G.obj.X)).left := by
          rw [hnat (MonObj.one (X := G.obj.X)), ← Category.assoc, hε]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- Quasi-finiteness at the identity over every point of the base is inherited by the point
of the source determined by a global section of a base change. -/
private theorem isQuasiFiniteAt_pointsMap_fst_of_forall_at_one
    (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    (h : ∀ b : points B S hS Bs,
      IsQuasiFiniteAt B S hS G.obj.X.hom
        (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b))
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs)
    (g : Over.mk (𝟙 Bt) ⟶ (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)
    (b : points B S hS Bt) :
    IsQuasiFiniteAt B S hS G.obj.X.hom
      (pointsMap B S hS (pullback G.obj.X.hom f) (pullback.fst G.obj.X.hom f)
        (pointsMap B S hS Bt g.left b)) := by
  have hiff : ∀ x : points B S hS (pullback G.obj.X.hom f),
      IsQuasiFiniteAt B S hS (pullback.snd G.obj.X.hom f) x ↔
        IsQuasiFiniteAt B S hS G.obj.X.hom
          (pointsMap B S hS (pullback G.obj.X.hom f) (pullback.fst G.obj.X.hom f) x) :=
    Set.ext_iff.mp (setOf_isQuasiFiniteAt_eq_preimage_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk G.obj.X.hom :
          (⟨G.obj.X.left, G.property⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)
        (ObjectProperty.homMk f : (⟨Bt, hBt⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)) hG)
  have hpoint : pointsMap B S hS (pullback G.obj.X.hom f) (pullback.fst G.obj.X.hom f)
        (pointsMap B S hS Bt
          (MonObj.one
            (X := (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)).left b) =
      pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left (pointsMap B S hS Bt f b) :=
    calc pointsMap B S hS (pullback G.obj.X.hom f) (pullback.fst G.obj.X.hom f)
          (pointsMap B S hS Bt
            (MonObj.one
              (X := (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)).left b)
        = pointsMap B S hS Bt
            ((MonObj.one
                (X := (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)).left ≫
              pullback.fst G.obj.X.hom f) b :=
          (pointsMap_comp_apply B S hS _ _ b).symm
      _ = pointsMap B S hS Bt (f ≫ (MonObj.one (X := G.obj.X)).left) b :=
          congrArg (fun k => pointsMap B S hS Bt k b)
            (one_baseChange_left_comp_fst B S hS G hBt f)
      _ = pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left
            (pointsMap B S hS Bt f b) := pointsMap_comp_apply B S hS f _ b
  exact (hiff _).mp ((isQuasiFiniteAt_one_iff_at_section B S hS
    (GroupAlgebraicSpace.baseChange B S hS hBt f G) g b).mp ((hiff _).mpr (hpoint ▸ h _)))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- The point of the base cut out by a field-valued point of a group algebraic space: the
morphism from the representing object of the site to the base determined by the structure
morphism. -/
private noncomputable def baseOfFieldValuedPoint (G : GroupAlgebraicSpace B S hS Bs hBs)
    (p : FieldValuedPoint B S hS G.obj.X.left) :
    (yoneda.obj (p.siteObject B S hS G.obj.X.left) :
      (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ Bs :=
  yonedaEquiv.symm
    (G.obj.X.hom.app (Opposite.op (p.siteObject B S hS G.obj.X.left)) p.value)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- The morphism of presheaves underlying the global section of the base change of a group
algebraic space determined by a field-valued point of it. -/
private noncomputable def sectionMapOfFieldValuedPoint
    (G : GroupAlgebraicSpace B S hS Bs hBs) (p : FieldValuedPoint B S hS G.obj.X.left) :
    (yoneda.obj (p.siteObject B S hS G.obj.X.left) :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶
      pullback G.obj.X.hom (baseOfFieldValuedPoint B S hS G p) :=
  pullback.lift (yonedaEquiv.symm p.value) (𝟙 _) (by
    apply yonedaEquiv.injective
    simp [baseOfFieldValuedPoint, yonedaEquiv_comp])

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- The global section of the base change of a group algebraic space along the base point of a
field-valued point of it, determined by that field-valued point. -/
private noncomputable def sectionOfFieldValuedPoint (G : GroupAlgebraicSpace B S hS Bs hBs)
    (p : FieldValuedPoint B S hS G.obj.X.left) :
    Over.mk (𝟙 (yoneda.obj (p.siteObject B S hS G.obj.X.left) :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
      (GroupAlgebraicSpace.baseChange B S hS
        (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS G.obj.X.left))
        (baseOfFieldValuedPoint B S hS G p) G).obj.X :=
  Over.homMk (sectionMapOfFieldValuedPoint B S hS G p) (pullback.lift_snd _ _ _)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- The section of the base change determined by a field-valued point projects back to the
class of that point. -/
private theorem pointsMap_fst_sectionMapOfFieldValuedPoint
    (G : GroupAlgebraicSpace B S hS Bs hBs) (p : FieldValuedPoint B S hS G.obj.X.left) :
    pointsMap B S hS
        (pullback G.obj.X.hom (baseOfFieldValuedPoint B S hS G p))
        (pullback.fst G.obj.X.hom (baseOfFieldValuedPoint B S hS G p))
        (pointsMap B S hS
          (yoneda.obj (p.siteObject B S hS G.obj.X.left) :
            (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (sectionMapOfFieldValuedPoint B S hS G p)
          ((fieldPointOfYoneda B S hS p).class B S hS _)) =
      p.class B S hS G.obj.X.left := by
  have hfst : sectionMapOfFieldValuedPoint B S hS G p ≫
      pullback.fst G.obj.X.hom (baseOfFieldValuedPoint B S hS G p) =
        yonedaEquiv.symm p.value := pullback.lift_fst _ _ _
  rw [← pointsMap_comp_apply, hfst, pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
    ⟨p, ⟨𝟙 _, ?_⟩, FieldValuedPoint.dominates_refl B S hS _ p⟩
  exact (G.obj.X.left.map_id_apply _ _).trans (G.obj.X.left.map_id_apply _ _)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- **Stacks 0DSI.** A group algebraic space locally of finite type over its base is locally
quasi-finite exactly when it is quasi-finite at the identity point over every point of the
base. -/
@[stacks 0DSI "the locally quasi-finite characterization"]
theorem isLocallyQuasiFinite_iff_at_identity (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) :
    IsLocallyQuasiFinite B S hS G.obj.X.hom ↔
      ∀ b : points B S hS Bs,
        IsQuasiFiniteAt B S hS G.obj.X.hom
          (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b) := by
  rw [isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS G.property hBs G.obj.X.hom]
  refine ⟨fun hqf b => hqf _, fun h x => ?_⟩
  induction x using Quot.ind with
  | _ p =>
    change IsQuasiFiniteAt B S hS G.obj.X.hom (p.class B S hS G.obj.X.left)
    rw [← pointsMap_fst_sectionMapOfFieldValuedPoint B S hS G p]
    exact isQuasiFiniteAt_pointsMap_fst_of_forall_at_one B S hS G hG h
      (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS G.obj.X.left))
      (baseOfFieldValuedPoint B S hS G p) (sectionOfFieldValuedPoint B S hS G p)
      ((fieldPointOfYoneda B S hS p).class B S hS _)

/-! ### The unramified characterization -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- The property of being an open immersion, as a relative property of morphisms of presheaves
on the big fppf site of `S`. -/
private abbrev openImmersions : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- The relative diagonal of a monomorphism of presheaves is an open immersion: it is an
isomorphism. -/
private theorem isOpenImmersion_pullbackDiagonal_of_mono
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ Y) [Mono g] :
    IsOpenImmersion B S hS (pullback.diagonal g) := by
  have : (openImmersions B S hS).ContainsIdentities :=
    (inferInstance : (openImmersions B S hS).IsMultiplicative).toContainsIdentities
  have : (openImmersions B S hS).RespectsIso := inferInstance
  exact (openImmersions B S hS).of_isIso (pullback.diagonal g)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- If a composite of morphisms of presheaves is an open immersion and the relative diagonal of
its second factor is an open immersion, then its first factor is an open immersion.

This is the open-immersion case of the cancellation pattern of
`AlgebraicGeometry.Space.isClosedImmersion_of_comp_of_isSeparated`: being an open immersion is
a relative property, so it is multiplicative and stable under base change, and the cancellation
statement is then the tautology that the diagonal condition implies itself. -/
private theorem isOpenImmersion_of_comp_of_isOpenImmersion_pullbackDiagonal
    {Z Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Y) (f : Y ⟶ X)
    (hgf : IsOpenImmersion B S hS (g ≫ f))
    (hf : IsOpenImmersion B S hS (pullback.diagonal f)) :
    IsOpenImmersion B S hS g := by
  let R : MorphismProperty Scheme.{u} := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}
  have _ : R.ContainsIdentities := (inferInstance : R.IsMultiplicative).toContainsIdentities
  have _ : R.IsStableUnderComposition := ⟨(inferInstance : R.IsMultiplicative).comp_mem⟩
  let Q : MorphismProperty (BigFppfOver B S hS) := R.inverseImage (BigFppfOver.toScheme B S hS)
  have _ : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have _ : Q.ContainsIdentities := MorphismProperty.ContainsIdentities.inverseImage _
  have _ : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : Q.IsMultiplicative := MorphismProperty.IsMultiplicative.mk
  have _ : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  have _ : Q.presheaf.IsMultiplicative := MorphismProperty.relative_isMultiplicative Q
  exact ((MorphismProperty.hasOfPostcompProperty_iff_le_diagonal
    (P := Q.presheaf) (Q := Q.presheaf.diagonal)).2 le_rfl).of_postcomp g f hf hgf

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- The restriction of a morphism of algebraic spaces over `S` to an open subspace whose set of
points is exactly the set of points at which the morphism is unramified is unramified.

By the pointwise criterion of Stacks 03ZK it suffices to see that the restriction is unramified
at every point `w` of the open subspace `W`. The image of `w` in the source is a point at which
the morphism is unramified, so some open subspace `U` of the source carries it and has
unramified restriction; every point of `U` is then a point of unramifiedness, so `U` factors
through `W` by Stacks 03IE, by a morphism `j` which is an open immersion because `W` is a
monomorphism. The range of `j` is the open subspace of `W` witnessing unramifiedness at `w`. -/
private theorem isUnramified_ι_of_range_eq_setOf_isUnramifiedAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (W : Subfunctor X)
    (hW : IsOpenSubspace B S hS W)
    (hWrange : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      {x : points B S hS X | IsUnramifiedAt B S hS f x}) :
    IsUnramified B S hS (W.ι ≫ f) := by
  refine ((isUnramified_tfae B S hS hW.1 hY (W.ι ≫ f)).out 2 1).mp fun w => ?_
  obtain ⟨U, hU, x', hx', hUf⟩ := hWrange.subset ⟨w, rfl⟩
  have hsub : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hWrange]
    rintro z ⟨u, rfl⟩
    exact ⟨U, hU, u, rfl, hUf⟩
  obtain ⟨j, hj⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS hX hU.1 W hW U.ι).mpr hsub
  have hmonoj : Mono j := by
    have : Mono (j ≫ W.ι) := by
      rw [hj]
      infer_instance
    exact mono_of_mono j W.ι
  have hjOpen : IsOpenImmersion B S hS j :=
    isOpenImmersion_of_comp_of_isOpenImmersion_pullbackDiagonal B S hS j W.ι
      (hj ▸ hU.2) (isOpenImmersion_pullbackDiagonal_of_mono B S hS W.ι)
  let V : Subfunctor W.toFunctor := Subfunctor.range j
  let β : U.toFunctor ⟶ V.toFunctor := Subfunctor.toRange j
  have : IsIso β := inferInstance
  have hβ : β ≫ V.ι = j := Subfunctor.toRange_ι j
  have hVι : (asIso β).inv ≫ j = V.ι := by
    rw [← hβ]
    simp
  have hVopen : IsOpenImmersion B S hS V.ι := by
    rw [← hVι]
    exact MorphismProperty.RespectsIso.precomp (openImmersions B S hS) (asIso β).inv j hjOpen
  refine ⟨V, ⟨isAlgebraicSpace_of_iso B S hS (asIso β) hU.1, hVopen⟩,
    pointsMap B S hS U.toFunctor β x', ?_, ?_⟩
  · refine pointsMap_injective_of_mono B S hS W.ι ?_
    rwa [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← Category.assoc, hβ, hj]
  · have hfac : V.ι ≫ W.ι ≫ f = (asIso β).inv ≫ U.ι ≫ f := by
      rw [← hVι, ← hj]
      simp only [Category.assoc]
    rw [hfac]
    exact (holdsOnEveryEtaleChart_precomp_iso B S hS
      (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
      (asIso β).symm (U.ι ≫ f)).mp hUf

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site exceeds the default budget
/-- **Stacks 0DSI.** A group algebraic space locally of finite type over its base is unramified
exactly when it is unramified at the identity point over every point of the base. -/
@[stacks 0DSI "the unramified characterization"]
theorem isUnramified_iff_at_identity (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) :
    IsUnramified B S hS G.obj.X.hom ↔
      ∀ b : points B S hS Bs,
        IsUnramifiedAt B S hS G.obj.X.hom
          (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b) := by
  constructor
  · intro hf b
    have hpointwise := ((isUnramified_tfae B S hS G.property hBs G.obj.X.hom).out 1 2).mp hf
    exact hpointwise _
  intro h
  let W := unramifiedLocus B S hS G.property G.obj.X.hom
  have hWrange : Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
      {x : points B S hS G.obj.X.left | IsUnramifiedAt B S hS G.obj.X.hom x} :=
    range_pointsMap_unramifiedLocus B S hS G.property G.obj.X.hom
  obtain ⟨e, he⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS G.property hBs W.1 W.2
      (MonObj.one (X := G.obj.X)).left).mpr (by
        rw [hWrange]
        rintro z ⟨b, rfl⟩
        exact h b)
  have hdiagW : IsOpenImmersion B S hS (pullback.diagonal (W.1.ι ≫ G.obj.X.hom)) :=
    isOpenImmersion_diagonal_of_isUnramified B S hS W.2.1 hBs _
      (isUnramified_ι_of_range_eq_setOf_isUnramifiedAt B S hS G.property hBs G.obj.X.hom
        W.1 W.2 hWrange)
  have hsection : e ≫ W.1.ι ≫ G.obj.X.hom = 𝟙 Bs := by
    rw [← Category.assoc, he]
    simp
  have heOpen : IsOpenImmersion B S hS e :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_section_diagonal (W.1.ι ≫ G.obj.X.hom) e hsection) hdiagW
  have honeOpen : IsOpenImmersion B S hS (MonObj.one (X := G.obj.X)).left := by
    rw [← he]
    exact (openImmersions B S hS).comp_mem e W.1.ι heOpen W.2.2
  exact isUnramified_of_isOpenImmersion_pullbackDiagonal B S hS G.property hBs G.obj.X.hom hG
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_diagonal_identity B S hS G.obj.X).flip honeOpen)

end AlgebraicGeometry.Space

end
