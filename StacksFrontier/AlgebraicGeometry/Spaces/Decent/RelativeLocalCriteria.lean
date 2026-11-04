module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyBetaDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableZariskiLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
import StacksFrontier.AlgebraicGeometry.Spaces.Representability
import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverPoints
import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# Zariski-local criteria for the relative conditions of Stacks 03KZ

Stacks 03L3 says that each of the conditions property `(β)`, decent, reasonable and very
reasonable on a *morphism* `f : X ⟶ Y` of algebraic spaces over `S` — the relative conditions
of Stacks 03KZ — can be tested on the base changes of `f` along morphisms from *affine*
objects of the site, or on a Zariski covering of `Y`, and (for the first three) after one
surjective étale chart of `Y` by a scheme.

The criteria hold for any absolute condition `P` on algebraic spaces which passes to the source
of a representable morphism (Stacks 03KF) and is Zariski local (Stacks 03KE); condition (5)
holds when moreover `P` descends along surjective quasi-compact étale morphisms (Stacks 03L2).
The entries of each `List.TFAE` follow the numbering of the source. The restriction of `f` to a
member `Yᵢ` of a Zariski covering of the target is the first projection of `Yᵢ ×_Y X`, and the
base change of `f` along `g : h_Z ⟶ Y` is `pullback.fst g f`.

## Main definitions

* `AlgebraicGeometry.Space.ZariskiLocalProperty`: a property of algebraic spaces over `S`
  which satisfies the case of Stacks 03KF and the case of Stacks 03KE for it.
* `AlgebraicGeometry.Space.RelativeProperty`: the relative condition of Stacks 03KZ attached
  to a property of algebraic spaces — every base change along a morphism from a representable
  presheaf has the property.
* `AlgebraicGeometry.Space.openSubobject`: an open subscheme of the scheme underlying an
  object of the big fppf category over `S`, regarded as an object of that category.

## Main results

* `AlgebraicGeometry.Space.ZariskiLocalProperty.tfae`: conditions (1) to (4) of Stacks 03L3
  for any Zariski-local property.
* `AlgebraicGeometry.Space.ZariskiLocalProperty.tfae_etale`: the same together with condition
  (5), given descent of the property along a surjective quasi-compact étale morphism.
* `AlgebraicGeometry.Space.hasPropertyBeta_tfae`: **Stacks 03L3 for property `(β)`**, all five
  conditions.
* `AlgebraicGeometry.Space.isVeryReasonable_tfae`: **Stacks 03L3 for very reasonableness**, all
  four conditions.
* `AlgebraicGeometry.Space.isReasonable_tfae`: **Stacks 03L3 for reasonableness**, all five
  conditions.
* `AlgebraicGeometry.Space.isDecent_tfae_etale`: **Stacks 03L3 for decency**, all five
  conditions; `AlgebraicGeometry.Space.isDecent_tfae` is its restriction to conditions (1)
  to (4).

## References

* [Stacks Project, Tag 02YY](https://stacks.math.columbia.edu/tag/02YY)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03L2](https://stacks.math.columbia.edu/tag/03L2)
* [Stacks Project, Tag 03L3](https://stacks.math.columbia.edu/tag/03L3)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open subschemes of an object of the site -/

/-- An open subscheme of the scheme underlying an object `T` of the big fppf category over
`S`, presented as an open immersion `j` of schemes, regarded as an object of that category. -/
noncomputable def openSubobject (T : BigFppfOver B S hS) {A : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage
    (show B.inclusion.obj
        (B.obj (@Scheme.size_lt_of_isOpenImmersion _ _ _ j hj T.left.property)) ⟶
      B.inclusion.obj T.left from j) ≫ T.hom)

/-- The inclusion of `AlgebraicGeometry.Space.openSubobject` into the ambient object of the
site. -/
noncomputable def openSubobjectHom (T : BigFppfOver B S hS) {A : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) : openSubobject B S hS T j hj ⟶ T :=
  Over.homMk (B.inclusion.preimage
    (show B.inclusion.obj
        (B.obj (@Scheme.size_lt_of_isOpenImmersion _ _ _ j hj T.left.property)) ⟶
      B.inclusion.obj T.left from j))

/-- The scheme underlying `AlgebraicGeometry.Space.openSubobject` is the given open
subscheme. -/
theorem toScheme_obj_openSubobject (T : BigFppfOver B S hS) {A : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) :
    (BigFppfOver.toScheme B S hS).obj (openSubobject B S hS T j hj) = A := rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openSubobjectHom` is the
given open immersion. -/
theorem toScheme_map_openSubobjectHom (T : BigFppfOver B S hS) {A : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) :
    (BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS T j hj) = j :=
  B.inclusion.map_preimage _

/-- A morphism of the big fppf category over `S` whose underlying morphism of schemes is an
open immersion represents an open immersion of algebraic spaces in the sense of
Stacks 02YU. -/
theorem isOpenImmersion_yoneda_map {A D : BigFppfOver B S hS} (j : A ⟶ D)
    (hj : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    IsOpenImmersion B S hS (yoneda.map j) :=
  have := inverseImage_isStableUnderBaseChange B S hS
    (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance
  MorphismProperty.relative_map (F := yoneda) hj

/-- The inclusion of an open subscheme of the scheme of a site object is an open immersion of
algebraic spaces. -/
theorem isOpenImmersion_yoneda_map_openSubobjectHom (T : BigFppfOver B S hS) {A : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) :
    IsOpenImmersion B S hS (yoneda.map (openSubobjectHom B S hS T j hj)) :=
  isOpenImmersion_yoneda_map B S hS _
    (by rw [toScheme_map_openSubobjectHom]; exact hj)

/-- A family of open immersions covering the scheme of a site object covers the points of the
presheaf it represents. -/
theorem exists_pointsMap_openSubobjectHom_eq (T : BigFppfOver B S hS) {I : Type u}
    {A : I → Scheme.{u}} (j : ∀ i, A i ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : ∀ i, AlgebraicGeometry.IsOpenImmersion (j i))
    (hcover : ∀ x : (BigFppfOver.toScheme B S hS).obj T, ∃ i, x ∈ Set.range (j i))
    (z : points B S hS (yoneda.obj T)) :
    ∃ i w, pointsMap B S hS (yoneda.obj (openSubobject B S hS T (j i) (hj i)))
      (yoneda.map (openSubobjectHom B S hS T (j i) (hj i))) w = z := by
  obtain ⟨i, a, ha⟩ := hcover (pointsToScheme B S hS T z)
  refine ⟨i, (pointsEquivScheme B S hS (openSubobject B S hS T (j i) (hj i))).symm a,
    (injective_pointsToScheme B S hS T) ?_⟩
  rw [pointsToScheme_pointsMap_yoneda, toScheme_map_openSubobjectHom,
    show pointsToScheme B S hS (openSubobject B S hS T (j i) (hj i))
        ((pointsEquivScheme B S hS (openSubobject B S hS T (j i) (hj i))).symm a) = a from
      (pointsEquivScheme B S hS (openSubobject B S hS T (j i) (hj i))).apply_symm_apply a]
  exact ha

/-- **A quasi-compact étale refinement.** A surjective étale morphism of the site onto an
affine object restricts to an open subscheme of its source which is quasi-compact and still
surjects onto that object. -/
theorem exists_quasiCompact_isEtale_isSurjective_openSubobject {V T : BigFppfOver B S hS}
    (p : V ⟶ T) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hp : Etale ((BigFppfOver.toScheme B S hS).map p))
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map p)) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ V),
      IsQuasiCompact B S hS (yoneda.map (j ≫ p)) ∧
      IsEtale B S hS (yoneda.map (j ≫ p)) ∧
      IsSurjective B S hS (yoneda.map (j ≫ p)) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  have _ : Etale ((BigFppfOver.toScheme B S hS).map p) := hp
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map p) := hs
  obtain ⟨U, hUcompact, hUimage⟩ :
      ∃ U : ((BigFppfOver.toScheme B S hS).obj V).Opens, IsCompact U.carrier ∧
        ⇑((BigFppfOver.toScheme B S hS).map p) '' (U : Set _) = Set.univ :=
    ((BigFppfOver.toScheme B S hS).map p).isOpenMap.exists_opens_image_eq_of_prespectralSpace
      ((BigFppfOver.toScheme B S hS).map p).continuous
      (by rw [Set.range_eq_univ.2 (Surjective.surj
        (f := (BigFppfOver.toScheme B S hS).map p))])
      isOpen_univ isCompact_univ
  have hU₀ : AlgebraicGeometry.IsOpenImmersion U.ι := inferInstance
  have hcomp : (BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V U.ι hU₀ ≫ p) =
      U.ι ≫ (BigFppfOver.toScheme B S hS).map p := by
    rw [Functor.map_comp, toScheme_map_openSubobjectHom]
    rfl
  have _ : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj (openSubobject B S hS V U.ι hU₀)) :=
    isCompact_iff_compactSpace.1 hUcompact
  have hsurj : Surjective
      ((BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V U.ι hU₀ ≫ p)) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, hcomp]
    show Set.range ((BigFppfOver.toScheme B S hS).map p ∘ U.ι) = Set.univ
    rw [Set.range_comp, Scheme.Opens.range_ι]
    exact hUimage
  have hqcm : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V U.ι hU₀ ≫ p)) :=
    inferInstance
  have hetm : Etale
      ((BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V U.ι hU₀ ≫ p)) := by
    rw [hcomp]
    exact (inferInstance : Etale (U.ι ≫ (BigFppfOver.toScheme B S hS).map p))
  refine ⟨openSubobject B S hS V U.ι hU₀, openSubobjectHom B S hS V U.ι hU₀, ?_, ?_, ?_⟩
  · refine isQuasiCompact_of_presheaf_quasiCompact B S hS ?_
    have := inverseImage_isStableUnderBaseChange B S hS
      (P := @AlgebraicGeometry.QuasiCompact.{u}) inferInstance
    exact MorphismProperty.relative_map (F := yoneda) hqcm
  · exact (isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS _).2 hetm)
  · exact (surjective_pointsMap_yoneda_iff B S hS _).2 hsurj.surj

/-! ### Zariski-local properties of algebraic spaces -/

/-- A property `P` of presheaves on the big fppf site of `S` is a *Zariski-local property* of
algebraic spaces when it satisfies two permanence statements: the case of Stacks 03KF for `P`,
that `P` passes from the target of a representable morphism of algebraic spaces to its source;
and the case of Stacks 03KE for `P`, that an algebraic space with a Zariski covering by open
subspaces having `P` has `P`. -/
structure ZariskiLocalProperty
    (P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop) : Prop where
  /-- `P` passes from the target of a representable morphism of algebraic spaces to its
  source. -/
  of_relativelyRepresentable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y → ∀ f : X ⟶ Y,
      yoneda.relativelyRepresentable f → P Y → P X
  /-- An algebraic space with a Zariski covering by open subspaces having `P` has `P`. -/
  of_isZariskiCover {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    IsAlgebraicSpace B S hS X → ∀ (I : Type u) (Xᵢ : I → Subfunctor X),
      IsZariskiCover B S hS I Xᵢ → (∀ i, P (Xᵢ i).toFunctor) → P X

/-- **Stacks 03KZ for a property of algebraic spaces.** The relative condition attached to a
property `P` of presheaves on the big fppf site of `S`: a morphism satisfies it when every
base change of it along a morphism from a representable presheaf into its target satisfies
`P`.

The relative conditions `AlgebraicGeometry.Space.HasPropertyBeta`,
`AlgebraicGeometry.Space.IsDecent`, `AlgebraicGeometry.Space.IsReasonable` and
`AlgebraicGeometry.Space.IsVeryReasonable` of Stacks 03KZ are `RelativeProperty` of
`AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint`,
`AlgebraicGeometry.Space.IsDecentSpace`, `AlgebraicGeometry.Space.IsReasonableSpace` and
`AlgebraicGeometry.Space.IsVeryReasonableSpace` respectively. -/
abbrev RelativeProperty (P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y), P (pullback g f)

variable {B S hS}
variable {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}

/-- Open immersions of algebraic spaces are stable under base change. -/
private theorem isOpenImmersion_snd_of_isPullback {W A C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : W ⟶ A} {snd : W ⟶ C} {f : A ⟶ D} {g : C ⟶ D} (h : IsPullback fst snd f g)
    (hf : IsOpenImmersion B S hS f) : IsOpenImmersion B S hS snd :=
  (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback h hf

namespace ZariskiLocalProperty

variable (hP : ZariskiLocalProperty B S hS P)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

include hP

/-- A Zariski-local property of algebraic spaces is invariant under isomorphism. -/
theorem of_iso (hX : IsAlgebraicSpace B S hS X) (e : X ≅ Y) (h : P X) : P Y :=
  hP.of_relativelyRepresentable (hX.of_iso e) hX e.inv
    (Functor.relativelyRepresentable.of_isIso yoneda e.inv) h

/-- For a Zariski-local property, `P` of the base change of `f` along `b = a ≫ g` is equivalent
to `P` of the base change of `pullback.fst g f` along `a`. -/
private theorem iff_pullback_pullback_fst {T Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : T ⟶ Y) (a : Z ⟶ T) (b : Z ⟶ Y) (hab : a ≫ g = b) :
    P (pullback b f) ↔ P (pullback a (pullback.fst g f)) := by
  subst hab
  exact ⟨hP.of_iso (isAlgebraicSpace_pullback B S hS _ f hZ hX hY)
      (pullbackRightPullbackFstIso g f a).symm,
    hP.of_iso (isAlgebraicSpace_pullback B S hS a (pullback.fst g f) hZ
      (isAlgebraicSpace_pullback B S hS g f hT hX hY) hT) (pullbackRightPullbackFstIso g f a)⟩

/-- **Stacks 03L0 for a Zariski-local property.** The relative condition attached to a
Zariski-local property is stable under arbitrary base change. -/
theorem relativeProperty_pullback_fst (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : Z ⟶ Y) (h : RelativeProperty B S hS P f) :
    RelativeProperty B S hS P (pullback.fst k f) := fun T g =>
  hP.of_iso
    (isAlgebraicSpace_pullback B S hS (g ≫ k) f (isAlgebraicSpace_yoneda B S hS T) hX hY)
    (pullbackRightPullbackFstIso k f g).symm (h T (g ≫ k))

/-- The source of a morphism into a representable presheaf satisfying the relative condition
attached to a Zariski-local property satisfies the property itself. -/
theorem of_relativeProperty_yoneda (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (f : X ⟶ yoneda.obj T) (h : RelativeProperty B S hS P f) : P X :=
  have hT := isAlgebraicSpace_yoneda B S hS T
  have : IsIso (pullback.snd (𝟙 (yoneda.obj T)) f) :=
    (IsPullback.of_hasPullback (𝟙 (yoneda.obj T)) f).isIso_snd_of_isIso
  hP.of_iso (isAlgebraicSpace_pullback B S hS (𝟙 (yoneda.obj T)) f hT hX hT)
    (asIso (pullback.snd (𝟙 (yoneda.obj T)) f)) (h T (𝟙 (yoneda.obj T)))

/-- A family of open immersions into an algebraic space whose images cover its points
transfers a Zariski-local property to the target. -/
theorem of_isOpenImmersion_family (hX : IsAlgebraicSpace B S hS X) {I : Type u}
    (Z : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : ∀ i, IsAlgebraicSpace B S hS (Z i)) (m : ∀ i, Z i ⟶ X)
    (hm : ∀ i, IsOpenImmersion B S hS (m i))
    (hcover : ∀ x : points B S hS X, ∃ i w, pointsMap B S hS (Z i) (m i) w = x)
    (h : ∀ i, P (Z i)) : P X := by
  have hmono : ∀ i, Mono (m i) := fun i => mono_of_presheaf_isOpenImmersion (hm i)
  refine hP.of_isZariskiCover hX I (fun i => Subfunctor.range (m i)) ?_ fun i =>
    hP.of_iso (hZ i) (asIso (Subfunctor.toRange (m i))) (h i)
  refine (isZariskiCover_iff_iUnion_points B S hS X hX I _ fun i =>
    isOpenSubspace_range_of_isAlgebraicSpace B S hS (hZ i) (m i) (hm i)).2 ?_
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨i, w, hw⟩ := hcover x
  refine Set.mem_iUnion.2 ⟨i, pointsMap B S hS (Z i) (Subfunctor.toRange (m i)) w, ?_⟩
  rw [← Function.comp_apply
      (f := pointsMap B S hS (Subfunctor.range (m i)).toFunctor (Subfunctor.range (m i)).ι),
    ← pointsMap_comp, Subfunctor.toRange_ι]
  exact hw

/-- A family of open immersions into the target of a morphism of algebraic spaces whose images
cover the points of that target transfers a Zariski-local property from the base changes of the
morphism to its source. -/
theorem of_pullback_isOpenImmersion_family (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {I : Type u}
    (Z : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : ∀ i, IsAlgebraicSpace B S hS (Z i)) (m : ∀ i, Z i ⟶ Y)
    (hm : ∀ i, IsOpenImmersion B S hS (m i))
    (hcover : ∀ y : points B S hS Y, ∃ i w, pointsMap B S hS (Z i) (m i) w = y)
    (h : ∀ i, P (pullback (m i) f)) : P X := by
  refine hP.of_isOpenImmersion_family hX (fun i => pullback (m i) f)
    (fun i => isAlgebraicSpace_pullback B S hS (m i) f (hZ i) hX hY)
    (fun i => pullback.snd (m i) f)
    (fun i => isOpenImmersion_snd_of_isPullback (IsPullback.of_hasPullback (m i) f) (hm i)) ?_ h
  intro x
  obtain ⟨i, w, hw⟩ := hcover (pointsMap B S hS X f x)
  obtain ⟨z, -, hz⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback (m i) f) w x hw
  exact ⟨i, z, hz⟩

/-! ### Conditions (1) to (4) of Stacks 03L3 -/

/-- **Stacks 03L3, (3) ⇒ (1).** If every base change of `f` along a morphism from an affine
object of the site satisfies a Zariski-local property, then so does every base change of `f`
along a morphism from an arbitrary object of the site. -/
theorem of_affine_tests (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) → P (pullback g f)) :
    RelativeProperty B S hS P f := by
  intro T g
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hK := isAlgebraicSpace_pullback B S hS g f hT hX hY
  have hopen : ∀ i, AlgebraicGeometry.IsOpenImmersion
      (((BigFppfOver.toScheme B S hS).obj T).affineOpenCover.openCover.f i) :=
    fun i => ((BigFppfOver.toScheme B S hS).obj T).affineOpenCover.openCover.map_prop i
  refine hP.of_pullback_isOpenImmersion_family hK hT (pullback.fst g f)
    (fun i => yoneda.obj (openSubobject B S hS T
      (((BigFppfOver.toScheme B S hS).obj T).affineOpenCover.openCover.f i) (hopen i)))
    (fun i => isAlgebraicSpace_yoneda B S hS _)
    (fun i => yoneda.map (openSubobjectHom B S hS T
      (((BigFppfOver.toScheme B S hS).obj T).affineOpenCover.openCover.f i) (hopen i)))
    (fun i => isOpenImmersion_yoneda_map_openSubobjectHom B S hS T _ (hopen i))
    (exists_pointsMap_openSubobjectHom_eq B S hS T _ hopen fun x =>
      ⟨((BigFppfOver.toScheme B S hS).obj T).affineOpenCover.openCover.idx x,
        (((BigFppfOver.toScheme B S hS).obj T).affineOpenCover.openCover.covers x).imp
          fun _ hy => hy⟩)
    fun i => ?_
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (openSubobject B S hS T
      (((BigFppfOver.toScheme B S hS).obj T).affineOpenCover.openCover.f i) (hopen i))) :=
    Scheme.isAffine_affineOpenCover _
      ((BigFppfOver.toScheme B S hS).obj T).affineOpenCover i
  exact (hP.iff_pullback_pullback_fst hX hY hT (isAlgebraicSpace_yoneda B S hS _) f g _ _
    rfl).1 (h _ (yoneda.map (openSubobjectHom B S hS T _ (hopen i)) ≫ g) haff)

/-- **Stacks 03L3, (4) ⇒ (1).** If the restriction of `f` to every member of a Zariski
covering of its target satisfies the relative condition attached to a Zariski-local property,
then so does `f`. -/
theorem of_isZariskiCover_target (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {I : Type u} (Yᵢ : I → Subfunctor Y)
    (hcover : IsZariskiCover B S hS I Yᵢ)
    (h : ∀ i, RelativeProperty B S hS P (pullback.fst (Yᵢ i).ι f)) :
    RelativeProperty B S hS P f := by
  intro T g
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hK := isAlgebraicSpace_pullback B S hS g f hT hX hY
  have r : ∀ i, yoneda.relativelyRepresentable (Yᵢ i).ι := fun i => (hcover.1 i).2.rep
  refine hP.of_pullback_isOpenImmersion_family hK hT (pullback.fst g f)
    (fun i => yoneda.obj ((r i).pullback g))
    (fun i => isAlgebraicSpace_yoneda B S hS ((r i).pullback g))
    (fun i => yoneda.map ((r i).snd g))
    (fun i => isOpenImmersion_snd_of_isPullback ((r i).isPullback g) (hcover.1 i).2) ?_ ?_
  · intro z
    have hpts := (isZariskiCover_iff_iUnion_points B S hS Y hY I Yᵢ hcover.1).1 hcover
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 (hpts ▸
      Set.mem_univ (pointsMap B S hS (yoneda.obj T) g z))
    obtain ⟨c, -, hc⟩ := exists_points_of_isPullback B S hS ((r i).isPullback g) y z hy
    exact ⟨i, c, hc⟩
  · intro i
    have hVi := isAlgebraicSpace_yoneda B S hS ((r i).pullback g)
    have hYi := (hcover.1 i).1
    exact (hP.iff_pullback_pullback_fst hX hY hT hVi f g _ _ ((r i).w g).symm).1
      ((hP.iff_pullback_pullback_fst hX hY hYi hVi f (Yᵢ i).ι _ _ rfl).2
        (h i ((r i).pullback g) ((r i).fst g)))

/-- **Stacks 03L3, conditions (1) to (4), for a Zariski-local property.** For a morphism
`f : X ⟶ Y` of algebraic spaces over `S` and a Zariski-local property `P` of algebraic
spaces, the following are equivalent:
`(1)` `f` satisfies the relative condition attached to `P`;
`(2)` for every affine object `Z` of the site and every `Z ⟶ Y`, the base change
`Z ×_Y X ⟶ Z` satisfies it;
`(3)` for every such `Z ⟶ Y` the algebraic space `Z ×_Y X` satisfies `P`;
`(4)` there is a Zariski covering of `Y` by open subspaces `Yᵢ` such that every restriction
`Yᵢ ×_Y X ⟶ Yᵢ` satisfies the relative condition. -/
theorem tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [RelativeProperty B S hS P f,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            RelativeProperty B S hS P (pullback.fst g f),
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) → P (pullback g f),
        ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, RelativeProperty B S hS P (pullback.fst (Yᵢ i).ι f)] := by
  tfae_have 1 → 2 := fun h T g _ => hP.relativeProperty_pullback_fst hX hY f g h
  tfae_have 2 → 3 := fun h T g ha =>
    hP.of_relativeProperty_yoneda
      (isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY)
      T (pullback.fst g f) (h T g ha)
  tfae_have 3 → 1 := hP.of_affine_tests hX hY f
  tfae_have 1 → 4 := fun h =>
    ⟨PUnit.{u + 1}, fun _ => ⊤, isZariskiCover_top hY,
      fun _ => hP.relativeProperty_pullback_fst hX hY f (⊤ : Subfunctor Y).ι h⟩
  tfae_have 4 → 1 := fun ⟨_, Yᵢ, hcover, h⟩ =>
    hP.of_isZariskiCover_target hX hY f Yᵢ hcover h
  tfae_finish

/-! ### Condition (5) of Stacks 03L3 -/

/-- **Stacks 03L3, (5) ⇒ (1).** If the base change of `f` along one surjective étale chart of
its target by a scheme satisfies the relative condition attached to a Zariski-local property
which descends along surjective quasi-compact étale morphisms, then `f` satisfies it. -/
theorem of_etale_cover
    (hdescent : ∀ {A D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS A →
      IsAlgebraicSpace B S hS D → ∀ a : A ⟶ D, IsQuasiCompact B S hS a →
      IsEtale B S hS a → IsSurjective B S hS a → P A → P D)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) (hs : IsSurjective B S hS g)
    (he : IsEtale B S hS g) (h : RelativeProperty B S hS P (pullback.fst g f)) :
    RelativeProperty B S hS P f := by
  refine hP.of_affine_tests hX hY f fun T k hTaff => ?_
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hgE := (isEtale_iff_presheaf_of_yoneda B S hS g).1 he
  have hgS := (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V g).2 hs
  obtain ⟨W, j, hqc, het, hsur⟩ :=
    exists_quasiCompact_isEtale_isSurjective_openSubobject B S hS (hgE.rep.snd k) hTaff
      (hgE.property_snd k)
      (hgS.property k (hgE.rep.fst k) (hgE.rep.snd k) (hgE.rep.isPullback k))
  have hW := isAlgebraicSpace_yoneda B S hS W
  have ha : (yoneda.map j ≫ hgE.rep.fst k) ≫ g = yoneda.map (j ≫ hgE.rep.snd k) ≫ k := by
    rw [Functor.map_comp, Category.assoc, Category.assoc, hgE.rep.w k]
  have hK := isAlgebraicSpace_pullback B S hS k f hT hX hY
  have hL := isAlgebraicSpace_pullback B S hS (yoneda.map (j ≫ hgE.rep.snd k))
    (pullback.fst k f) hW hK hT
  have hLprop : P (pullback (yoneda.map (j ≫ hgE.rep.snd k)) (pullback.fst k f)) := by
    exact (hP.iff_pullback_pullback_fst hX hY hT hW f k _ _ ha.symm).1
      ((hP.iff_pullback_pullback_fst hX hY hV hW f g _ _ rfl).2
        (h W (yoneda.map j ≫ hgE.rep.fst k)))
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk (yoneda.map (j ≫ hgE.rep.snd k)) :
      (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj T, hT⟩)
    (ObjectProperty.homMk (pullback.fst k f) :
      (⟨pullback k f, hK⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj T, hT⟩)
  refine hdescent hL hK
    (pullback.snd (yoneda.map (j ≫ hgE.rep.snd k)) (pullback.fst k f)) ?_ ?_ ?_ hLprop
  · exact isQuasiCompact_of_isPullback B S hS
      (IsPullback.of_hasPullback (yoneda.map (j ≫ hgE.rep.snd k)) (pullback.fst k f)) hqc
  · exact isEtale_of_isPullback B S hS _ _ _ _ hpb het
  · exact isSurjective_of_isPullback B S hS hpb hsur

/-- **Stacks 03L3, all five conditions, for a Zariski-local property which descends along a
surjective quasi-compact étale morphism.** Conditions (1) to (4) are those of
`AlgebraicGeometry.Space.ZariskiLocalProperty.tfae`, and condition `(5)` is that there is a
scheme of the site with a surjective étale morphism to `Y` along which the base change of `f`
satisfies the relative condition. -/
theorem tfae_etale
    (hdescent : ∀ {A D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS A →
      IsAlgebraicSpace B S hS D → ∀ a : A ⟶ D, IsQuasiCompact B S hS a →
      IsEtale B S hS a → IsSurjective B S hS a → P A → P D)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [RelativeProperty B S hS P f,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            RelativeProperty B S hS P (pullback.fst g f),
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) → P (pullback g f),
        ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, RelativeProperty B S hS P (pullback.fst (Yᵢ i).ι f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsSurjective B S hS g ∧
          IsEtale B S hS g ∧ RelativeProperty B S hS P (pullback.fst g f)] := by
  tfae_have 1 ↔ 2 := (hP.tfae hX hY f).out 1 2
  tfae_have 1 ↔ 3 := (hP.tfae hX hY f).out 1 3
  tfae_have 1 ↔ 4 := (hP.tfae hX hY f).out 1 4
  tfae_have 1 → 5 := by
    intro h
    obtain ⟨V, g, hgs, hge⟩ := hY.exists_atlas
    exact ⟨V, g, (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V g).1 hgs,
      (isEtale_iff_presheaf_of_yoneda B S hS g).2 hge,
      hP.relativeProperty_pullback_fst hX hY f g h⟩
  tfae_have 5 → 1 := fun ⟨V, g, hgs, hge, h⟩ =>
    hP.of_etale_cover hdescent hX hY f V g hgs hge h
  tfae_finish

end ZariskiLocalProperty

/-! ### The four cases of Stacks 03L3 -/

variable (B S hS)

/-- Property `(β)` of Stacks 03JX, finiteness of the relation fibres at every point, is a
Zariski-local property. -/
theorem zariskiLocalProperty_hasFiniteRelationFibersAtEveryPoint :
    ZariskiLocalProperty B S hS (HasFiniteRelationFibersAtEveryPoint B S hS) where
  of_relativelyRepresentable hX hY f hf hβ :=
    hasFiniteRelationFibersAtEveryPoint_of_relativelyRepresentable B S hS hX f hf
      fun y =>
        (hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative
            B S hS hY y).1
          ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
              B S hS _ hY y).1
            ((hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS _ hY y).1 (hβ y)))
  of_isZariskiCover hX I Xᵢ hcover hβ :=
    hasFiniteRelationFibersAtEveryPoint_of_isZariskiCover B S hS _ hX I Xᵢ hcover hβ

/-- Decency of algebraic spaces is a Zariski-local property. -/
theorem zariskiLocalProperty_isDecentSpace :
    ZariskiLocalProperty B S hS (IsDecentSpace B S hS) where
  of_relativelyRepresentable hX _ f hf hdec :=
    isDecentSpace_of_relativelyRepresentable B S hS hX f hf hdec
  of_isZariskiCover hX I Xᵢ hcover hdec :=
    (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS _ hX).2
      (hasFiniteChartAndRelationFibersAtEveryPoint_of_isZariskiCover B S hS _ hX I Xᵢ hcover
        fun i => (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS _
          (hcover.1 i).1).1 (hdec i))

/-- Reasonableness of algebraic spaces is a Zariski-local property. -/
theorem zariskiLocalProperty_isReasonableSpace :
    ZariskiLocalProperty B S hS (IsReasonableSpace B S hS) where
  of_relativelyRepresentable hX hY f hf hr :=
    isReasonableSpace_of_relativelyRepresentable B S hS hX hY f hf hr
  of_isZariskiCover hX I Xᵢ hcover hr :=
    isReasonableSpace_of_isZariskiCover B S hS _ hX I Xᵢ hcover hr

/-- Very reasonableness of algebraic spaces is a Zariski-local property. -/
theorem zariskiLocalProperty_isVeryReasonableSpace :
    ZariskiLocalProperty B S hS (IsVeryReasonableSpace B S hS) where
  of_relativelyRepresentable _ _ f hf hvr :=
    isVeryReasonableSpace_of_relativelyRepresentable B S hS f hf hvr
  of_isZariskiCover _ I Xᵢ hcover hvr :=
    isVeryReasonableSpace_of_isZariskiCover B S hS _ I Xᵢ hcover hvr

variable {B S hS}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are equivalent:
`(1)` `f` has property `(β)` in the sense of Stacks 03KZ;
`(2)` for every affine object `Z` of the site and every `Z ⟶ Y`, the base change
`Z ×_Y X ⟶ Z` has property `(β)`;
`(3)` for every such `Z ⟶ Y` the algebraic space `Z ×_Y X` has property `(β)`;
`(4)` there is a Zariski covering of `Y` by open subspaces `Yᵢ` with every restriction
`Yᵢ ×_Y X ⟶ Yᵢ` having property `(β)`;
`(5)` there is a scheme of the site with a surjective étale morphism `V ⟶ Y` such that
`V ×_Y X ⟶ V` has property `(β)`. -/
@[stacks 03L3 "property beta"]
theorem hasPropertyBeta_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [HasPropertyBeta B S hS f,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            HasPropertyBeta B S hS (pullback.fst g f),
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            HasFiniteRelationFibersAtEveryPoint B S hS (pullback g f),
        ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, HasPropertyBeta B S hS (pullback.fst (Yᵢ i).ι f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsSurjective B S hS g ∧
          IsEtale B S hS g ∧ HasPropertyBeta B S hS (pullback.fst g f)] :=
  (zariskiLocalProperty_hasFiniteRelationFibersAtEveryPoint B S hS).tfae_etale
    (fun hA hD a hqc het hsur hβ =>
      hasFiniteRelationFibersAtEveryPoint_of_surjective_isEtale B S hS hA hD a hqc het hsur hβ)
    hX hY f

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are equivalent:
`(1)` `f` is very reasonable in the sense of Stacks 03KZ;
`(2)` for every affine object `Z` of the site and every `Z ⟶ Y`, the base change
`Z ×_Y X ⟶ Z` is very reasonable;
`(3)` for every such `Z ⟶ Y` the algebraic space `Z ×_Y X` is very reasonable;
`(4)` there is a Zariski covering of `Y` by open subspaces `Yᵢ` with every restriction
`Yᵢ ×_Y X ⟶ Yᵢ` very reasonable. -/
@[stacks 03L3 "very reasonable"]
theorem isVeryReasonable_tfae (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [IsVeryReasonable B S hS f,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsVeryReasonable B S hS (pullback.fst g f),
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsVeryReasonableSpace B S hS (pullback g f),
        ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, IsVeryReasonable B S hS (pullback.fst (Yᵢ i).ι f)] :=
  (zariskiLocalProperty_isVeryReasonableSpace B S hS).tfae hX hY f

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are equivalent:
`(1)` `f` is decent in the sense of Stacks 03KZ;
`(2)` for every affine object `Z` of the site and every `Z ⟶ Y`, the base change
`Z ×_Y X ⟶ Z` is decent;
`(3)` for every such `Z ⟶ Y` the algebraic space `Z ×_Y X` is decent;
`(4)` there is a Zariski covering of `Y` by open subspaces `Yᵢ` with every restriction
`Yᵢ ×_Y X ⟶ Yᵢ` decent. -/
@[stacks 03L3 "decent, conditions (1) to (4)"]
theorem isDecent_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [IsDecent B S hS f,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsDecent B S hS (pullback.fst g f),
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsDecentSpace B S hS (pullback g f),
        ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, IsDecent B S hS (pullback.fst (Yᵢ i).ι f)] :=
  (zariskiLocalProperty_isDecentSpace B S hS).tfae hX hY f

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the four conditions of
`AlgebraicGeometry.Space.isDecent_tfae` are also equivalent to
`(5)` there is a scheme of the site with a surjective étale morphism `V ⟶ Y` such that
`V ×_Y X ⟶ V` is decent. -/
@[stacks 03L3 "decent"]
theorem isDecent_tfae_etale (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [IsDecent B S hS f,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsDecent B S hS (pullback.fst g f),
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsDecentSpace B S hS (pullback g f),
        ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, IsDecent B S hS (pullback.fst (Yᵢ i).ι f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsSurjective B S hS g ∧
          IsEtale B S hS g ∧ IsDecent B S hS (pullback.fst g f)] :=
  (zariskiLocalProperty_isDecentSpace B S hS).tfae_etale
    (fun hA hD a hqc _ hsur hdec =>
      isDecentSpace_of_surjective_isQuasiCompact B S hS hA hD a hqc hsur hdec)
    hX hY f

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are equivalent:
`(1)` `f` is reasonable in the sense of Stacks 03KZ;
`(2)` for every affine object `Z` of the site and every `Z ⟶ Y`, the base change
`Z ×_Y X ⟶ Z` is reasonable;
`(3)` for every such `Z ⟶ Y` the algebraic space `Z ×_Y X` is reasonable;
`(4)` there is a Zariski covering of `Y` by open subspaces `Yᵢ` with every restriction
`Yᵢ ×_Y X ⟶ Yᵢ` reasonable;
`(5)` there is a scheme of the site with a surjective étale morphism `V ⟶ Y` such that
`V ×_Y X ⟶ V` is reasonable. -/
@[stacks 03L3 "reasonable"]
theorem isReasonable_tfae (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [IsReasonable B S hS f,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsReasonable B S hS (pullback.fst g f),
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
            IsReasonableSpace B S hS (pullback g f),
        ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, IsReasonable B S hS (pullback.fst (Yᵢ i).ι f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsSurjective B S hS g ∧
          IsEtale B S hS g ∧ IsReasonable B S hS (pullback.fst g f)] :=
  (zariskiLocalProperty_isReasonableSpace B S hS).tfae_etale
    (fun hA hD a hqc _ hsur hr =>
      isReasonableSpace_of_surjective_isQuasiCompact B S hS hA hD a hqc hsur hr)
    hX hY f

end AlgebraicGeometry.Space

/-! ### Remark 68.17.10

Stacks 03L4 states no proposition of its own. Its one mathematical sentence, that a morphism
has property `(β)`, is decent, reasonable or very reasonable when, "(very) loosely speaking",
the fibres of the morphism do, is made precise by Stacks 03L3, whose four cases are the
theorems above. -/

add_to_stacks 03L4 "Remark 68.17.10, which states no proposition of its own: its one
  mathematical sentence, that a morphism has one of the conditions of Stacks 03KZ when, in the
  source's words '(very) loosely speaking', the fibres of the morphism do, is disclaimed there
  as loose and is sharp only as Stacks 03L3 — here the case of property `(β)`."
  AlgebraicGeometry.Space.hasPropertyBeta_tfae

add_to_stacks 03L4 "Remark 68.17.10, which states no proposition of its own: its one
  mathematical sentence, that a morphism has one of the conditions of Stacks 03KZ when, in the
  source's words '(very) loosely speaking', the fibres of the morphism do, is disclaimed there
  as loose and is sharp only as Stacks 03L3 — here the case of very reasonableness."
  AlgebraicGeometry.Space.isVeryReasonable_tfae

add_to_stacks 03L4 "Remark 68.17.10, which states no proposition of its own: its one
  mathematical sentence, that a morphism has one of the conditions of Stacks 03KZ when, in the
  source's words '(very) loosely speaking', the fibres of the morphism do, is disclaimed there
  as loose and is sharp only as Stacks 03L3 — here the case of decency."
  AlgebraicGeometry.Space.isDecent_tfae_etale

add_to_stacks 03L4 "Remark 68.17.10, which states no proposition of its own: its one
  mathematical sentence, that a morphism has one of the conditions of Stacks 03KZ when, in the
  source's words '(very) loosely speaking', the fibres of the morphism do, is disclaimed there
  as loose and is sharp only as Stacks 03L3 — here the case of reasonableness."
  AlgebraicGeometry.Space.isReasonable_tfae

end
