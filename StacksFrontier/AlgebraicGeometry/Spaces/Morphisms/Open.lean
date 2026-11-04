module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversallyOpen.Criteria
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.UniversallyClosedCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas

/-!
# Open and universally open morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *open* when the map it induces on points
is an open map, and *universally open* when its base change along every morphism from an
algebraic space is open. Universal openness implies openness, is stable under base change and
composition, and is local on the target; a morphism to the spectrum of a field is universally
open; and a representable morphism is universally open exactly when its represented base
changes are universally open morphisms of schemes.

## Main definitions

* `AlgebraicGeometry.Space.IsOpenMorphism`: a morphism of algebraic spaces whose map on points
  is open.
* `AlgebraicGeometry.Space.UniversallyOpen`: a morphism of algebraic spaces whose base change
  along every morphism from an algebraic space is open.

## Main results

* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_comp_isIso`: a morphism which becomes one
  with open map on points after precomposition with an isomorphism has open map on points.
* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_pullback_fst_id`: if the base change of `f`
  along the identity of its target has open map on points, so does `f`.
* `AlgebraicGeometry.Space.isOpenMap_pointsMap_pullback_fst_pullback_fst` and
  `AlgebraicGeometry.Space.isOpenMap_pointsMap_pullback_fst_comp`: the base change of
  `f : X ⟶ Y` along `w ≫ g` has open map on points exactly when the base change along `w` of
  the base change along `g` does.
* `AlgebraicGeometry.Space.isOpen_of_universallyOpen`: a universally open morphism of
  algebraic spaces is open.
* `AlgebraicGeometry.Space.IsOpenMorphism.comp` and
  `AlgebraicGeometry.Space.universallyOpen_comp`: compositions of open, respectively
  universally open, morphisms are open, respectively universally open.
* `AlgebraicGeometry.Space.universallyOpen_pullback`: a base change of a universally open
  morphism is universally open.
* `AlgebraicGeometry.Space.universallyOpen_tfae`: five equivalent criteria for universal
  openness, with the implications
  `AlgebraicGeometry.Space.universallyOpen_of_isOpenMorphism_affine`,
  `AlgebraicGeometry.Space.universallyOpen_of_universallyOpen_etaleChart` and
  `AlgebraicGeometry.Space.universallyOpen_of_zariskiCover`.
* `AlgebraicGeometry.Space.universallyOpen_to_field`: a morphism to the spectrum of a field is
  universally open.
* `AlgebraicGeometry.Space.presheaf_universallyOpen_iff`: a representable morphism is
  universally open exactly when each of its represented base changes is a universally open
  morphism of schemes, with the two implications
  `AlgebraicGeometry.Space.universallyOpen_of_presheaf_universallyOpen` and
  `AlgebraicGeometry.Space.presheaf_universallyOpen_of_universallyOpen`.

## Implementation notes

The point set is `AlgebraicGeometry.Space.points` of Stacks 03BU and the induced map is
`AlgebraicGeometry.Space.pointsMap`. The topology is `AlgebraicGeometry.Space.pointTopology`,
the topology detected by scheme-valued points, which is the topology every family satisfying
the three clauses of Stacks 03BX assigns to an algebraic space
(`AlgebraicGeometry.Space.PointTopologyFamily.topology_eq`).

The predicates are stated for arbitrary morphisms of presheaves on the big fppf site of `S`,
algebraicity of the source and target being imposed by hypotheses, and they are abbreviations,
so that the `IsOpenMap` API applies to them directly. Algebraicity of the covering object `Z`
is a hypothesis of the quantifier defining universal openness.

`AlgebraicGeometry.Space.pointTopology` is a `def`, not an instance. The definitions supply
it with `letI`; the results install it as a local instance, so that `IsOpenMap` and
`Continuous` elaborate without explicit topology arguments.

The schemes occurring in the criteria of Stacks 03Z5 are the objects of the big fppf site over
`S`. Universal openness in the sense of `AlgebraicGeometry.UniversallyOpen` quantifies over all
schemes; base changes inside the site suffice by the affine-space criterion
`AlgebraicGeometry.universallyOpen_iff_forall_isOpenMap_affineSpaceMap` of Stacks 0F31, since
affine `n`-space over a scheme in the site is again in the site.

## References

* [Stacks Project, Tag 03Z1](https://stacks.math.columbia.edu/tag/03Z1)
* [Stacks Project, Tag 03Z2](https://stacks.math.columbia.edu/tag/03Z2)
* [Stacks Project, Tag 03Z3](https://stacks.math.columbia.edu/tag/03Z3)
* [Stacks Project, Tag 03Z4](https://stacks.math.columbia.edu/tag/03Z4)
* [Stacks Project, Tag 03Z5](https://stacks.math.columbia.edu/tag/03Z5)
* [Stacks Project, Tag 06DN](https://stacks.math.columbia.edu/tag/06DN)
* [Stacks Project, Tag 0F31](https://stacks.math.columbia.edu/tag/0F31)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Open and universally open morphisms -/

section Defs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of algebraic spaces over `S` is *open* when the map it induces on points is an
open map for the topology detected by scheme-valued points. -/
@[stacks 03Z2 "part (1): open"]
abbrev IsOpenMorphism (f : F ⟶ G) : Prop :=
  letI := pointTopology B S hS F
  letI := pointTopology B S hS G
  IsOpenMap (pointsMap B S hS F f)

/-- A morphism of algebraic spaces over `S` is *universally open* when its base change along
every morphism to its target from an algebraic space over `S` is open. -/
@[stacks 03Z2 "part (2): universally open"]
abbrev UniversallyOpen (f : F ⟶ G) : Prop :=
  ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
    ∀ g : Z ⟶ G, IsOpenMorphism B S hS (pullback.fst g f)

end Defs

/-! ### Openness on points of a base change -/

section Comparisons

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a morphism of presheaves on the big fppf site of `S` becomes, after precomposition
with an isomorphism, a morphism whose map on points is open, then its own map on points is
open. -/
theorem isOpenMap_pointsMap_of_comp_isIso {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ F') [IsIso e] {g : F' ⟶ G} {f : F ⟶ G} (hfg : e ≫ g = f)
    (hg : IsOpenMap (pointsMap B S hS F' g)) :
    IsOpenMap (pointsMap B S hS F f) := by
  subst hfg
  rw [pointsMap_comp]
  exact hg.comp (pointsHomeomorphOfIso B S hS (asIso e)).isOpenMap

/-- If the base change of `f : X ⟶ Y` along the identity of `Y` has open map on points, then so
does `f`. -/
theorem isOpenMap_pointsMap_of_pullback_fst_id {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)
    (h : IsOpenMap (pointsMap B S hS (pullback (𝟙 Y) f) (pullback.fst (𝟙 Y) f))) :
    IsOpenMap (pointsMap B S hS X f) := by
  refine isOpenMap_pointsMap_of_comp_isIso B S hS (inv (pullback.snd (𝟙 Y) f)) ?_ h
  have hc : pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f := by
    simpa using pullback.condition (f := 𝟙 Y) (g := f)
  rw [hc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- If the base change of `f : X ⟶ Y` along a composite `w ≫ g` has open map on points, then so
does the base change along `w` of the base change along `g`. -/
theorem isOpenMap_pointsMap_pullback_fst_pullback_fst
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y) (w : W ⟶ Z)
    (h : IsOpenMap (pointsMap B S hS (pullback (w ≫ g) f) (pullback.fst (w ≫ g) f))) :
    IsOpenMap (pointsMap B S hS (pullback w (pullback.fst g f))
      (pullback.fst w (pullback.fst g f))) :=
  isOpenMap_pointsMap_of_comp_isIso B S hS (pullbackRightPullbackFstIso g f w).hom
    (pullbackRightPullbackFstIso_hom_fst g f w) h

/-- If the base change along `w` of the base change of `f : X ⟶ Y` along `g` has open map on
points, then so does the base change of `f` along the composite `w ≫ g`. -/
theorem isOpenMap_pointsMap_pullback_fst_comp
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y) (w : W ⟶ Z)
    (h : IsOpenMap (pointsMap B S hS (pullback w (pullback.fst g f))
      (pullback.fst w (pullback.fst g f)))) :
    IsOpenMap (pointsMap B S hS (pullback (w ≫ g) f) (pullback.fst (w ≫ g) f)) :=
  isOpenMap_pointsMap_of_comp_isIso B S hS (pullbackRightPullbackFstIso g f w).inv
    (by rw [← pullbackRightPullbackFstIso_hom_fst g f w, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]) h

end Comparisons

/-! ### Permanence properties of openness and universal openness -/

section Permanence

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A universally open morphism of algebraic spaces over `S` is open. -/
theorem isOpen_of_universallyOpen (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : UniversallyOpen B S hS f) :
    IsOpenMorphism B S hS f :=
  isOpenMap_pointsMap_of_pullback_fst_id B S hS f (hf G hG (𝟙 G))

/-- A composition of open morphisms of algebraic spaces over `S` is open. -/
@[stacks 03Z4 "open"]
theorem IsOpenMorphism.comp {f : F ⟶ G} {g : G ⟶ H} (hg : IsOpenMorphism B S hS g)
    (hf : IsOpenMorphism B S hS f) :
    IsOpenMorphism B S hS (f ≫ g) := by
  intro W hW
  rw [pointsMap_comp, Set.image_comp]
  exact hg _ (hf _ hW)

/-- A base change of a universally open morphism of algebraic spaces over `S` is universally
open. -/
@[stacks 03Z3]
theorem universallyOpen_pullback {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : UniversallyOpen B S hS f) :
    UniversallyOpen B S hS (pullback.fst g f) := fun W hW k ↦
  isOpenMap_pointsMap_pullback_fst_pullback_fst B S hS f g k (hf W hW (k ≫ g))

/-- A composition of universally open morphisms of algebraic spaces over `S` is universally
open. -/
@[stacks 03Z4 "universally open"]
theorem universallyOpen_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : UniversallyOpen B S hS f) (hg : UniversallyOpen B S hS g) :
    UniversallyOpen B S hS (f ≫ g) := by
  intro W hW k
  have hP : IsAlgebraicSpace B S hS (pullback k g) :=
    isAlgebraicSpace_pullback B S hS k g hW hY hZ
  exact isOpenMap_pointsMap_of_comp_isIso B S hS (pullbackLeftPullbackSndIso k g f).inv
    (pullbackLeftPullbackSndIso_inv_fst k g f)
    (IsOpenMorphism.comp B S hS (hg W hW k) (hf (pullback k g) hP (pullback.snd k g)))

end Permanence

/-! ### Universal openness is local on the target -/

section Local

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `m i : α i → β` be continuous maps whose ranges cover `β`. If each composite
`q ∘ m i` is an open map, then so is `q`. -/
theorem isOpenMap_of_iUnion_range {ι : Type*} {α : ι → Type*} {β γ : Type*}
    [∀ i, TopologicalSpace (α i)] [TopologicalSpace β] [TopologicalSpace γ]
    (m : ∀ i, α i → β) (q : β → γ)
    (hcover : (⋃ i, Set.range (m i)) = Set.univ)
    (hcont : ∀ i, Continuous (m i))
    (hopen : ∀ i, IsOpenMap (q ∘ m i)) : IsOpenMap q := by
  intro W hW
  have hdecomp : (⋃ i, m i '' (m i ⁻¹' W)) = W := by
    simp_rw [Set.image_preimage_eq_inter_range]
    rw [← Set.inter_iUnion, hcover, Set.inter_univ]
  rw [← hdecomp]
  simp_rw [Set.image_iUnion, ← Set.image_comp]
  exact isOpen_iUnion fun i ↦ hopen i _ ((hcont i).isOpen_preimage W hW)

/-- Openness on points of the base change of `f` along `g` transports along an equality
`g = g'`. -/
private theorem isOpenMap_pointsMap_pullback_fst_of_eq
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) {g g' : Z ⟶ Y} (hgg : g = g')
    (h : IsOpenMap (pointsMap B S hS (pullback g' f) (pullback.fst g' f))) :
    IsOpenMap (pointsMap B S hS (pullback g f) (pullback.fst g f)) := by
  subst hgg; exact h

/-- The base change of a presheaf-étale morphism along any morphism is presheaf-étale. -/
private theorem presheaf_etale_pullback_fst {Z V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ Y) (v : V ⟶ Y)
    (hv : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst g v) := by
  have := inverseImage_isStableUnderBaseChange B S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.pullback_fst g v hv

/-- If the base change of `f` along `v` becomes open on points after pulling back along `snd g v`,
then the base change of `f` along `fst g v ≫ g` is open on points. -/
private theorem isOpenMap_pointsMap_pullback_fst_fst_comp {Z V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Z ⟶ Y) (v : V ⟶ Y)
    (h : IsOpenMap (pointsMap B S hS (pullback (pullback.snd g v) (pullback.fst v f))
      (pullback.fst (pullback.snd g v) (pullback.fst v f)))) :
    IsOpenMap (pointsMap B S hS (pullback (pullback.fst g v ≫ g) f)
      (pullback.fst (pullback.fst g v ≫ g) f)) :=
  isOpenMap_pointsMap_pullback_fst_of_eq B S hS f
    (show pullback.fst g v ≫ g = pullback.snd g v ≫ v from pullback.condition)
    (isOpenMap_pointsMap_pullback_fst_comp B S hS f v (pullback.snd g v) h)

/-- If `w i : W i ⟶ Z` are open on points with ranges covering the points of `Z`, and the base
changes of `fst g f` along each `w i` are open on points, then the base change of `f` along `g`
is open on points. -/
private theorem isOpenMap_pointsMap_pullback_fst_of_cover {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {ι : Type*} {W : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    (w : ∀ i, W i ⟶ Z) (hw : ∀ i, IsOpenMap (pointsMap B S hS (W i) (w i)))
    (hcover : (⋃ i, Set.range (pointsMap B S hS (W i) (w i))) = Set.univ)
    (hfst : ∀ i, IsOpenMap (pointsMap B S hS (pullback (w i) (pullback.fst g f))
      (pullback.fst (w i) (pullback.fst g f)))) :
    IsOpenMap (pointsMap B S hS (pullback g f) (pullback.fst g f)) := by
  refine isOpenMap_of_iUnion_range
    (fun i ↦ pointsMap B S hS (pullback (w i) (pullback.fst g f))
      (pullback.snd (w i) (pullback.fst g f)))
    (pointsMap B S hS (pullback g f) (pullback.fst g f)) ?_
    (fun i ↦ continuous_pointsMap B S hS _) ?_
  · refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp
      (hcover ▸ Set.mem_univ (pointsMap B S hS (pullback g f) (pullback.fst g f) x))
    obtain ⟨v, -, hv⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback (w i) (pullback.fst g f)) y x hy
    exact Set.mem_iUnion.mpr ⟨i, ⟨v, hv⟩⟩
  · intro i
    rw [← pointsMap_comp, ← pullback.condition, pointsMap_comp]
    exact (hw i).comp (hfst i)

/-- If every base change of `f : X ⟶ Y` along a morphism from an affine scheme in the site is
open on points, then `f` is universally open. -/
theorem universallyOpen_of_isOpenMorphism_affine (f : X ⟶ Y)
    (h : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ g : yoneda.obj V ⟶ Y, IsOpenMorphism B S hS (pullback.fst g f)) :
    UniversallyOpen B S hS f := by
  classical
  intro Z hZ g
  obtain ⟨I, U, hcov, hcharts⟩ := exists_zariski_cover_affine_etale_atlas B S hS Z hZ
  choose V a W hVaff haSurj haEtale _ _ using hcharts
  set w : ∀ i, yoneda.obj (V i) ⟶ Z := fun i ↦ a i ≫ (U i).ι with hw
  have hwOpen : ∀ i, IsOpenMap (pointsMap B S hS (yoneda.obj (V i)) (w i)) := by
    intro i
    rw [hw, pointsMap_comp]
    exact (isOpenMap_pointsMap_of_presheafEtale B S hS (U i).ι
      (presheaf_etale_of_isOpenImmersion B S hS (hcov.1 i).2)).comp
        (isOpenMap_pointsMap_of_presheafEtale B S hS (a i) (haEtale i))
  have haPointsSurj : ∀ i, Function.Surjective
      (pointsMap B S hS (yoneda.obj (V i)) (a i)) := fun i ↦
    (surjective_iff_surjective_pointsMap B S hS (U i).toFunctor (hcov.1 i).1 (V i)
      (a i)).mp (haSurj i)
  have hwRange : ∀ i, Set.range (pointsMap B S hS (yoneda.obj (V i)) (w i)) =
      Set.range (pointsMap B S hS (U i).toFunctor (U i).ι) := by
    intro i
    rw [hw, pointsMap_comp, Set.range_comp, (haPointsSurj i).range_eq, Set.image_univ]
  have hwCover : (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (V i)) (w i))) = Set.univ := by
    simp_rw [hwRange]
    exact (isZariskiCover_iff_iUnion_points B S hS Z hZ I U hcov.1).mp hcov
  have hfstOpen : ∀ i, IsOpenMap (pointsMap B S hS (pullback (w i) (pullback.fst g f))
      (pullback.fst (w i) (pullback.fst g f))) := fun i ↦
    isOpenMap_pointsMap_pullback_fst_pullback_fst B S hS f g (w i)
      (h (V i) (hVaff i) (w i ≫ g))
  exact isOpenMap_pointsMap_pullback_fst_of_cover B S hS f g w hwOpen hwCover hfstOpen

/-- If `f : X ⟶ Y` becomes universally open after base change along one surjective étale
morphism to `Y` from a scheme in the site, then `f` is universally open. -/
theorem universallyOpen_of_universallyOpen_etaleChart
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y) (hvSurj : IsSurjective B S hS v)
    (hvEtale : IsEtale B S hS v) (hv : UniversallyOpen B S hS (pullback.fst v f)) :
    UniversallyOpen B S hS f := by
  intro Z hZ g
  have hR : IsAlgebraicSpace B S hS (pullback g v) :=
    isAlgebraicSpace_pullback B S hS g v hZ (isAlgebraicSpace_yoneda B S hS V) hY
  have hrEtale := presheaf_etale_pullback_fst B S hS g v
    ((isEtale_iff_presheaf_of_yoneda B S hS v).mp hvEtale)
  have hrSurj : Function.Surjective (pointsMap B S hS (pullback g v) (pullback.fst g v)) :=
    surjective_pointsMap_of_isPullback B S hS
      (IsPullback.of_hasPullback g v).flip hvSurj
  have hq := isQuotientMap_pointsMap_of_presheafEtale B S hS (pullback.fst g v) hrEtale hrSurj
  refine isOpenMap_pointsMap_pullback_fst_of_comp B S hS f g (pullback.fst g v)
    (fun C hC ↦ hq.isOpen_preimage.mp hC) ?_
  exact isOpenMap_pointsMap_pullback_fst_fst_comp B S hS f g v
    (hv (pullback g v) hR (pullback.snd g v))

/-- If `f : X ⟶ Y` becomes universally open after base change along each member of a Zariski
covering of `Y`, then `f` is universally open. -/
theorem universallyOpen_of_zariskiCover (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} {U : I → Subfunctor Y} (hcov : IsZariskiCover B S hS I U)
    (hlocal : ∀ i, UniversallyOpen B S hS (pullback.fst (U i).ι f)) :
    UniversallyOpen B S hS f := by
  intro Z hZ g
  have hUalg : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor := fun i ↦ (hcov.1 i).1
  have hZi : ∀ i, IsAlgebraicSpace B S hS (pullback g (U i).ι) := fun i ↦
    isAlgebraicSpace_pullback B S hS g (U i).ι hZ (hUalg i) hY
  have hrOpen : ∀ i, IsOpenMap (pointsMap B S hS (pullback g (U i).ι)
      (pullback.fst g (U i).ι)) := by
    exact fun i ↦ isOpenMap_pointsMap_of_presheafEtale B S hS _
      (presheaf_etale_pullback_fst B S hS g (U i).ι
        (presheaf_etale_of_isOpenImmersion B S hS (hcov.1 i).2))
  have hrCover : (⋃ i, Set.range (pointsMap B S hS (pullback g (U i).ι)
      (pullback.fst g (U i).ι))) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun z ↦ ?_
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp
      (((isZariskiCover_iff_iUnion_points B S hS Y hY I U hcov.1).mp hcov) ▸
        Set.mem_univ (pointsMap B S hS Z g z))
    obtain ⟨p, hp, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback g (U i).ι) z y hy.symm
    exact Set.mem_iUnion.mpr ⟨i, ⟨p, hp⟩⟩
  have hfstOpen : ∀ i, IsOpenMap (pointsMap B S hS
      (pullback (pullback.fst g (U i).ι) (pullback.fst g f))
      (pullback.fst (pullback.fst g (U i).ι) (pullback.fst g f))) := by
    intro i
    exact isOpenMap_pointsMap_pullback_fst_pullback_fst B S hS f g _
      (isOpenMap_pointsMap_pullback_fst_fst_comp B S hS f g (U i).ι
        (hlocal i _ (hZi i) (pullback.snd g (U i).ι)))
  exact isOpenMap_pointsMap_pullback_fst_of_cover B S hS f g (fun i ↦ pullback.fst g (U i).ι)
    hrOpen hrCover hfstOpen

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are equivalent:

1. `f` is universally open;
2. for every scheme `Z` in the site and every `Z ⟶ Y` the projection `|Z ×_Y X| → |Z|` is
   open;
3. the same for every affine scheme `Z` in the site;
4. there is a scheme `V` in the site and a surjective étale `V ⟶ Y` with `V ×_Y X ⟶ V`
   universally open;
5. there is a Zariski covering of `Y` by open subspaces `Y_i` with each
   `f⁻¹(Y_i) ⟶ Y_i` universally open. -/
@[stacks 03Z5]
theorem universallyOpen_tfae (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [UniversallyOpen B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsOpenMorphism B S hS (pullback.fst g f),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ g : yoneda.obj Z ⟶ Y, IsOpenMorphism B S hS (pullback.fst g f),
        ∃ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y),
          IsSurjective B S hS v ∧ IsEtale B S hS v ∧
            UniversallyOpen B S hS (pullback.fst v f),
        ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
          ∀ i, UniversallyOpen B S hS (pullback.fst (U i).ι f)] := by
  have h12 : UniversallyOpen B S hS f →
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsOpenMorphism B S hS (pullback.fst g f) :=
    fun h Z g ↦ h _ (isAlgebraicSpace_yoneda B S hS Z) g
  have h14 : UniversallyOpen B S hS f →
      ∃ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y),
        IsSurjective B S hS v ∧ IsEtale B S hS v ∧
          UniversallyOpen B S hS (pullback.fst v f) := by
    intro h
    obtain ⟨V, v, hvSurj, hvEtale⟩ := hY.exists_atlas
    exact ⟨V, v, (surjective_iff_surjective_pointsMap B S hS Y hY V v).mp hvSurj,
      isEtale_of_presheaf_etale B S hS hvEtale,
      universallyOpen_pullback B S hS hX hY (isAlgebraicSpace_yoneda B S hS V) f v h⟩
  have h15 : UniversallyOpen B S hS f →
      ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
        ∀ i, UniversallyOpen B S hS (pullback.fst (U i).ι f) := by
    intro h
    set U : Subfunctor Y := openSubspaceOfPoints B S hS Y Set.univ with hU
    have hUopen : IsOpenSubspace B S hS U :=
      isOpenSubspace_openSubspaceOfPoints B S hS hY Set.univ isOpen_univ
    refine ⟨PUnit.{u + 1}, fun _ ↦ U, ⟨fun _ ↦ hUopen, ?_⟩, fun _ ↦
      universallyOpen_pullback B S hS hX hY hUopen.1 f U.ι h⟩
    refine ((isZariskiCover_iff_iUnion_points B S hS Y hY PUnit.{u + 1} (fun _ ↦ U)
      (fun _ ↦ hUopen)).mpr ?_).2
    rw [Set.iUnion_const, hU, range_pointsMap_ι_openSubspaceOfPoints]
  refine List.tfae_of_forall (b := UniversallyOpen B S hS f) ?_
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact ⟨fun h ↦ universallyOpen_of_isOpenMorphism_affine B S hS f (fun Z _ ↦ h Z), h12⟩
  · exact ⟨universallyOpen_of_isOpenMorphism_affine B S hS f, fun h Z _ ↦ h12 h Z⟩
  · exact ⟨fun ⟨V, v, hs, he, hvo⟩ ↦
      universallyOpen_of_universallyOpen_etaleChart B S hS hY f v hs he hvo, h14⟩
  · exact ⟨fun ⟨_, U, hcov, hlocal⟩ ↦
      universallyOpen_of_zariskiCover B S hS hY f hcov hlocal, h15⟩

end Local

/-! ### Algebraic spaces over a field -/

section OverField

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism from an algebraic space over `S` to a representable presheaf whose representing
scheme receives only universally open morphisms of schemes is universally open. -/
theorem universallyOpen_of_universallyOpen_scheme_hom (hX : IsAlgebraicSpace B S hS X)
    {K : BigFppfOver B S hS}
    (hK : ∀ (W : Scheme.{u}) (q : W ⟶ (BigFppfOver.toScheme B S hS).obj K),
      AlgebraicGeometry.UniversallyOpen q)
    (p : X ⟶ yoneda.obj K) :
    UniversallyOpen B S hS p := by
  refine ((universallyOpen_tfae B S hS hX (isAlgebraicSpace_yoneda B S hS K) p).out 1 2).mpr ?_
  intro Z g
  obtain ⟨z, rfl⟩ : ∃ z : Z ⟶ K, yoneda.map z = g := ⟨yoneda.preimage g, by simp⟩
  obtain ⟨U, a, haSurj, -⟩ := hX.exists_atlas
  have hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (surjective_iff_surjective_pointsMap B S hS X hX U a).mp haSurj
  obtain ⟨uK, hum⟩ : ∃ w : U ⟶ K, yoneda.map w = a ≫ p :=
    ⟨yoneda.preimage (a ≫ p), by simp⟩
  have hsq : IsPullback (yoneda.map (pullback.fst uK z)) (yoneda.map (pullback.snd uK z))
      (a ≫ p) (yoneda.map z) := by
    rw [← hum]
    exact (IsPullback.of_hasPullback uK z).map yoneda
  have hWopen : IsOpenMap ((BigFppfOver.toScheme B S hS).map (pullback.snd uK z)) := by
    have : AlgebraicGeometry.UniversallyOpen
        ((BigFppfOver.toScheme B S hS).map (pullback.snd uK z)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.UniversallyOpen)
        ((IsPullback.of_hasPullback uK z).map (BigFppfOver.toScheme B S hS)) (hK _ _)
    exact Scheme.Hom.isOpenMap _
  refine IsOpenMap.of_comp
    (continuous_pointsMap B S hS ((IsPullback.of_hasPullback (yoneda.map z) p).lift
      (yoneda.map (pullback.snd uK z)) (yoneda.map (pullback.fst uK z) ≫ a)
      (by rw [Category.assoc]; exact hsq.w.symm))) ?_ ?_
  · exact surjective_pointsMap_of_isPullback B S hS
      (IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hsq.flip)
        (IsPullback.lift_snd _ _ _ _) (IsPullback.of_hasPullback (yoneda.map z) p)).flip hasurj
  · rw [← pointsMap_comp, IsPullback.lift_fst]
    exact (isOpenMap_pointsMap_yoneda_iff B S hS (pullback.snd uK z)).mpr hWopen

/-- A morphism from an algebraic space over `S` to a representable presheaf whose representing
scheme is the spectrum of a field is universally open. -/
@[stacks 06DN, ega "IV 2.4.10", ega "IV 2.4.9" "Y = Spec k", sga "4 VIII 9.4.4" "more general"]
theorem universallyOpen_to_field (hX : IsAlgebraicSpace B S hS X)
    {K : BigFppfOver B S hS} {k : Type u} [Field k]
    (e : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (CommRingCat.of k))
    (p : X ⟶ yoneda.obj K) :
    UniversallyOpen B S hS p :=
  universallyOpen_of_universallyOpen_scheme_hom B S hS hX
    (fun _ q ↦ (MorphismProperty.cancel_right_of_respectsIso
      (@AlgebraicGeometry.UniversallyOpen.{u}) q e.hom).mp inferInstance) p

end OverField

/-! ### The size cutoff and universal openness of morphisms of schemes -/

section Cutoff

/-- A morphism of schemes whose target lies inside a big fppf site is universally open as soon
as its base changes along morphisms from schemes inside that site are open maps. -/
private theorem universallyOpen_of_bounded_isOpenMap_baseChanges (B : BigFppfSite.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : B.Contains Y)
    (hopen : ∀ (Z : Scheme.{u}), B.Contains Z → ∀ g : Z ⟶ Y,
      IsOpenMap (pullback.snd f g)) :
    AlgebraicGeometry.UniversallyOpen f := by
  rw [universallyOpen_iff_forall_isOpenMap_affineSpaceMap]
  intro n
  let proj : AffineSpace (ULift.{u} (Fin n)) Y ⟶ Y := AffineSpace (ULift.{u} (Fin n)) Y ↘ Y
  let sq := (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) f).flip
  let e := sq.isoIsPullback _ _ (IsPullback.of_hasPullback f proj)
  have hEq : ⇑(pullback.snd f proj) ∘ ⇑e.hom =
      ⇑(AffineSpace.map (ULift.{u} (Fin n)) f) := by
    funext x
    exact congrFun (congrArg (fun k : AffineSpace (ULift.{u} (Fin n)) X ⟶
      AffineSpace (ULift.{u} (Fin n)) Y => (k : _ → _))
        (sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f proj))) x
  simpa [hEq] using (hopen _ (B.contains_affineSpace hY n) proj).comp
    (Scheme.Hom.isOpenMap e.hom)

end Cutoff

/-! ### Representable morphisms -/

section Representable

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of the big fppf site whose underlying morphism of schemes is universally open
has underlying map of schemes an open map. -/
theorem inverseImage_universallyOpen_le_inverseImage_isOpenMap :
    MorphismProperty.inverseImage
        (@AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage
        (topologically @IsOpenMap : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := by
  intro U V i hi
  have : AlgebraicGeometry.UniversallyOpen ((BigFppfOver.toScheme B S hS).map i) := hi
  exact Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map i)

/-- If `f` is representable and every represented base change of `f` is a universally open
morphism of schemes, then every base change of `f` by an algebraic space over `S` is open on
points. -/
theorem universallyOpen_of_presheaf_universallyOpen (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    UniversallyOpen B S hS f := fun _ _ g ↦
  isOpenMap_pointsMap_pullback_fst_of_presheafIsOpenMap B S hS f
    (MorphismProperty.relative_monotone
      (inverseImage_universallyOpen_le_inverseImage_isOpenMap B S hS) _ hf) g

/-- Openness on the points of the presheaf fibre product `h_U ×_Y X` gives openness of the
morphism of schemes representing that base change. -/
private theorem isOpenMap_map_relativelyRepresentable_snd {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {U : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ Y)
    (hopen : IsOpenMap (pointsMap B S hS (pullback g f) (pullback.fst g f))) :
    IsOpenMap ((BigFppfOver.toScheme B S hS).map (hf.snd g)) := by
  let e : yoneda.obj (hf.pullback g) ≅ pullback g f :=
    (hf.isPullback g).isoPullback ≪≫ pullbackSymmetry f g
  have he : e.hom ≫ pullback.fst g f = yoneda.map (hf.snd g) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
      IsPullback.isoPullback_hom_snd]
  refine (isOpenMap_pointsMap_yoneda_iff B S hS (hf.snd g)).1 ?_
  rw [← he, pointsMap_comp]
  exact hopen.comp (pointsHomeomorphOfIso B S hS e).isOpenMap

/-- If every base change of a representable morphism `f` of presheaves by an algebraic space
over `S` is open on points, then every represented base change of `f` is a universally open
morphism of schemes. -/
theorem presheaf_universallyOpen_of_universallyOpen {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversallyOpen B S hS f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine ⟨hf, ?_⟩
  intro U V g fst snd sq
  let T := BigFppfOver.toScheme B S hS
  have hrepresented : ∀ (W : BigFppfOver B S hS) (k : yoneda.obj W ⟶ Y),
      IsOpenMap (T.map (hf.snd k)) := fun W k ↦
    isOpenMap_map_relativelyRepresentable_snd B S hS hf k
      (h (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) k)
  have hopenBounded : ∀ (W : Scheme.{u}), B.Contains W → ∀ k : W ⟶ T.obj U,
      IsOpenMap (pullback.snd (T.map snd) k) := by
    intro W hW k
    let k' : B.inclusion.obj (B.obj hW) ⟶ B.inclusion.obj U.left := k
    let kSite : B.obj hW ⟶ U.left := B.inclusion.preimage k'
    let Wov : BigFppfOver B S hS := Over.mk (kSite ≫ U.hom)
    let kOver : Wov ⟶ U := Over.homMk kSite
    have hk : T.map kOver = k := B.inclusion.map_preimage k'
    rw [← hk]
    let lNat : yoneda.obj (hf.pullback (yoneda.map kOver ≫ g)) ⟶ yoneda.obj V :=
      sq.lift (hf.fst (yoneda.map kOver ≫ g))
        (yoneda.map (hf.snd (yoneda.map kOver ≫ g)) ≫ yoneda.map kOver)
        (by simpa [Category.assoc] using (hf.isPullback (yoneda.map kOver ≫ g)).w)
    have hpaste : IsPullback (lNat ≫ fst)
        (yoneda.map (hf.snd (yoneda.map kOver ≫ g))) f (yoneda.map kOver ≫ g) := by
      rw [show lNat ≫ fst = hf.fst (yoneda.map kOver ≫ g) from by simp [lNat]]
      exact hf.isPullback (yoneda.map kOver ≫ g)
    have hpbNat : IsPullback lNat (yoneda.map (hf.snd (yoneda.map kOver ≫ g)))
        (yoneda.map snd) (yoneda.map kOver) :=
      (IsPullback.paste_horiz_iff sq (by simp [lNat])).mp hpaste
    have hpbOver : IsPullback (yoneda.preimage lNat)
        (hf.snd (yoneda.map kOver ≫ g)) snd kOver := by
      apply IsPullback.of_map_of_faithful (F := yoneda)
      simpa using hpbNat
    have hpbScheme : IsPullback (T.map (yoneda.preimage lNat))
        (T.map (hf.snd (yoneda.map kOver ≫ g))) (T.map snd) (T.map kOver) := hpbOver.map T
    let eScheme := hpbScheme.isoIsPullback _ _
      (IsPullback.of_hasPullback (T.map snd) (T.map kOver))
    have hfun : ⇑(T.map (hf.snd (yoneda.map kOver ≫ g))) ∘ ⇑eScheme.inv =
        ⇑(pullback.snd (T.map snd) (T.map kOver)) := by
      funext z
      exact congrFun (congrArg (fun m : pullback (T.map snd) (T.map kOver) ⟶ T.obj Wov =>
        (m : _ → _)) (hpbScheme.isoIsPullback_inv_snd _ _
          (IsPullback.of_hasPullback (T.map snd) (T.map kOver)))) z
    rw [← hfun]
    exact (hrepresented Wov (yoneda.map kOver ≫ g)).comp (Scheme.Hom.isOpenMap eScheme.inv)
  exact universallyOpen_of_bounded_isOpenMap_baseChanges B (T.map snd)
    U.left.property hopenBounded

/-- A representable morphism of algebraic spaces over `S` is universally open, that is, every
base change of it by an algebraic space over `S` is open on points, exactly when each of its
represented base changes is a universally open morphism of schemes. -/
@[stacks 03Z1]
theorem presheaf_universallyOpen_iff {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔ UniversallyOpen B S hS f :=
  ⟨universallyOpen_of_presheaf_universallyOpen B S hS f,
    presheaf_universallyOpen_of_universallyOpen B S hS hf⟩

end Representable

end AlgebraicGeometry.Space

end
