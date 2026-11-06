module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.UniversallyClosedSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Testing universal closedness on finitely presented bases and on affine spaces

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S`. Tag 0CM9
says that universal closedness of `f` is detected by two much smaller families of base
changes: those along the morphisms `Z ⟶ Y` which are locally of finite presentation, and
those along the projections `𝐀ⁿ × V ⟶ Y` attached to one surjective étale scheme atlas
`V ⟶ Y` of the target.

## Main results

* `AlgebraicGeometry.Space.isClosedMorphism_pullback_fst_of_universallyClosed`: a universally
  closed morphism has closed base changes along the morphisms locally of finite presentation.
* `AlgebraicGeometry.Space.exists_affineSpaceTest_of_universallyClosed`: a universally closed
  morphism passes the affine-space test over any surjective étale scheme atlas of the target.
* `AlgebraicGeometry.Space.isClosedMorphism_pullback_fst_of_affineSpaceTest`: conversely, the
  affine-space test over one surjective étale scheme atlas forces every base change along a
  morphism locally of finite presentation to be closed.
* `AlgebraicGeometry.Space.universallyClosed_of_isClosedMorphism_of_isLocallyOfFinitePresentation`:
  closedness of the base changes along the morphisms locally of finite presentation forces
  universal closedness.
* `AlgebraicGeometry.Space.universallyClosed_tfae_of_isQuasiCompact`: the three equivalent
  conditions of Tag 0CM9.

## Implementation notes

An affine-space test over a scheme `V` is indexed by an object `W` of the chosen big fppf
site together with an identification of its underlying scheme with affine `n`-space over the
scheme underlying `V`, compatible with the projections; this is
`AlgebraicGeometry.Space.IsAffineSpaceOver`. Carrying the identification as data is what makes
the condition say something: the site is closed under the construction, by
`AlgebraicGeometry.Space.exists_isAffineSpaceOver`, so requiring only the existence of some
object over `V` would be vacuous. The base change of `f` tested at such a `W` is the first
projection of `W ×_Y X`, which is `𝐀ⁿ × (X ×_Y V) ⟶ 𝐀ⁿ × V`.

The implication from the affine-space test to closedness over a base locally of finite
presentation is the argument of the source, read on point spaces. A test morphism `h : Z ⟶ Y`
locally of finite presentation is first replaced by a representable one: the composite of an
étale atlas of `Z ×_Y V` with the projection to `Z` is open and surjective on points, hence
detects closed sets, so closedness may be checked after that base change, and the base change
is tested by a morphism of the site into `V` which is locally of finite presentation. Such a
morphism is then restricted to the affine opens of its source, which form a family of étale
charts covering the points; over an affine open the source is quasi-affine and of finite type
over `V`, so Tag 04II provides an immersion into a finite-dimensional affine space over `V`,
and the hypothesis at that affine space transfers to the immersed base change because the map
on points of an immersion is a topological embedding, by Tag 0ABJ.

The reverse implication, from closedness over all bases locally of finite presentation to
universal closedness, is where the quasi-compactness of `f` enters, through the separation
statement of Tag 0CM8,
`AlgebraicGeometry.Space.exists_affine_etale_isLocallyOfFinitePresentation_separation`. That
statement is phrased with the fibre product written source first, so the subset of `|X ×_Y Z|`
at hand and the closedness supplied by the hypothesis are both carried across the symmetry
isomorphism of the fibre product.

## References

* [Stacks Project, Tag 0CM9](https://stacks.math.columbia.edu/tag/0CM9)
* [Stacks Project, Tag 0CM8](https://stacks.math.columbia.edu/tag/0CM8)
* [Stacks Project, Tag 03IT](https://stacks.math.columbia.edu/tag/03IT)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_universallyClosedAffineSpaceTest
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two auxiliary statements of point-set topology -/

/-- A continuous open surjection detects closed sets: a subset of the target whose preimage is
closed is itself closed, because its complement is the image of the open complement of that
preimage. -/
private theorem isClosed_of_isOpenMap_of_surjective {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {p : α → β} (hopen : IsOpenMap p) (hsurj : Function.Surjective p)
    {C : Set β} (hC : IsClosed (p ⁻¹' C)) : IsClosed C := by
  rw [← isOpen_compl_iff] at hC ⊢
  have h := hopen _ hC
  rwa [← Set.preimage_compl, Set.image_preimage_eq _ hsurj] at h

/-! ### Affine space over an object of the site -/

/-- An object `W` of the big fppf site of `S` over an object `V`, through a morphism `a`,
*is affine `n`-space over* `V` when its underlying scheme is identified with affine `n`-space
over the scheme underlying `V` in such a way that `a` becomes the projection. -/
def IsAffineSpaceOver (V W : BigFppfOver B S hS) (n : ℕ) (a : W ⟶ V) : Prop :=
  ∃ e : (BigFppfOver.toScheme B S hS).obj W ≅
      AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj V),
    (BigFppfOver.toScheme B S hS).map a =
      e.hom ≫ (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V)

/-- Affine `n`-space over an object of the big fppf site of `S` is again an object of that
site: its projection is of finite type, so the size bound of Stacks 000R applies. -/
theorem exists_isAffineSpaceOver (V : BigFppfOver B S hS) (n : ℕ) :
    ∃ (W : BigFppfOver B S hS) (a : W ⟶ V), IsAffineSpaceOver B S hS V W n a := by
  have hsize : (AffineSpace (ULift.{u} (Fin n))
      ((BigFppfOver.toScheme B S hS).obj V)).size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V) V.left.property
  refine ⟨Over.mk (B.inclusion.preimage (X := B.obj hsize) (Y := V.left)
      (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V) ≫ V.hom),
    Over.homMk (B.inclusion.preimage (X := B.obj hsize) (Y := V.left) _) rfl, Iso.refl _, ?_⟩
  rw [Iso.refl_hom, Category.id_comp]
  exact B.inclusion.map_preimage _

/-! ### Transfer of closedness along an immersion of the base -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Closedness of a base change transfers along an immersion of the base.

If `b : W ⟶ Y` has closed base change `|W ×_Y X| → |W|` and `j : Z ⟶ W` is an immersion, then
the base change along `j ≫ b` is closed: the comparison morphism `Z ×_Y X ⟶ W ×_Y X` is a base
change of `j`, hence an immersion, hence a topological embedding on points by Tag 0ABJ, so a
closed subset of `|Z ×_Y X|` is cut out by a closed subset of `|W ×_Y X|`; its image in `|Z|`
is then the preimage along `j` of a closed subset of `|W|`, by Tag 03H4. -/
theorem isClosedMorphism_pullback_fst_of_isImmersion
    {Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hW : IsAlgebraicSpace B S hS W)
    (f : X ⟶ Y) (b : W ⟶ Y) (j : Z ⟶ W) (hj : IsImmersion B S hS j)
    (hb : IsClosedMorphism B S hS (pullback.fst b f)) :
    IsClosedMorphism B S hS (pullback.fst (j ≫ b) f) := by
  obtain ⟨m, sq⟩ := exists_isPullback_pullback_fst_comp B S hS f b j
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hm : IsImmersion B S hS m := hbc.of_isPullback sq.flip hj
  have hemb := isEmbedding_pointsMap_of_isImmersion B S hS
    (isAlgebraicSpace_pullback B S hS b f hW hX hY) m hm
  intro T hT
  obtain ⟨C, hC, rfl⟩ := hemb.isInducing.isClosed_iff.mp hT
  rw [← preimage_image_pointsMap_of_isPullback B S hS sq C]
  exact (hb C hC).preimage (continuous_pointsMap B S hS j)

/-- Closedness of the base change of `f` along a morphism depends only on that morphism, so it
may be transported along an equality of morphisms. The fibre product carries its existence
hypothesis as an argument, so such an equality cannot be rewritten in place. -/
private theorem isClosedMorphism_pullback_fst_congr
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {b b' : Z ⟶ Y} (f : X ⟶ Y) (hb : b = b')
    (h : IsClosedMorphism B S hS (pullback.fst b' f)) :
    IsClosedMorphism B S hS (pullback.fst b f) :=
  hb ▸ h

/-! ### From the affine-space test to closedness over a finitely presented base -/

/-- The affine-space test over a scheme `V` gives closedness of the base change of `f` along
any morphism to `Y` which factors through `V` by a morphism of the site with affine source and
locally finitely presented underlying morphism of schemes.

An affine scheme is quasi-affine and the morphism is of finite type, so Tag 04II immerses the
source into a finite-dimensional affine space over the scheme underlying `V`; the hypothesis at
that affine space then transfers along the immersion. -/
theorem isClosedMorphism_pullback_fst_of_isAffine_of_locallyOfFinitePresentation
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (htest : ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V), IsAffineSpaceOver B S hS V W n a ∧
      IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f))
    (Z : BigFppfOver B S hS) (χ : Z ⟶ V)
    (hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (hχ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map χ)) :
    IsClosedMorphism B S hS (pullback.fst (yoneda.map χ ≫ g) f) := by
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map χ) := inferInstance
  obtain ⟨n, i, hi, hiχ⟩ := exists_immersion_affineSpace ((BigFppfOver.toScheme B S hS).map χ)
  obtain ⟨W, a, ⟨e, hae⟩, hclosed⟩ := htest n
  -- the immersion into affine `n`-space, read as a morphism of the site into `W`
  let j₀ : Z.left ⟶ W.left := B.inclusion.preimage (X := Z.left) (Y := W.left) (i ≫ e.inv)
  have hj₀ : B.inclusion.map j₀ = i ≫ e.inv :=
    B.inclusion.map_preimage (X := Z.left) (Y := W.left) (i ≫ e.inv)
  have hja : j₀ ≫ a.left = χ.left := by
    refine B.inclusion.map_injective ?_
    rw [CategoryTheory.Functor.map_comp, hj₀]
    show (i ≫ e.inv) ≫ (BigFppfOver.toScheme B S hS).map a = (BigFppfOver.toScheme B S hS).map χ
    rw [hae, ← hiχ, Category.assoc, e.inv_hom_id_assoc]
  let j : Z ⟶ W := Over.homMk j₀ (by rw [← a.w, ← Category.assoc, hja, χ.w])
  have hjimm : IsImmersion B S hS (yoneda.map j) := by
    refine (presheaf_yoneda_map_iff B S hS
      AlgebraicGeometry.IsImmersion.isStableUnderBaseChange j).2 ?_
    show AlgebraicGeometry.IsImmersion (B.inclusion.map j₀)
    rw [hj₀]
    infer_instance
  have hcomp : j ≫ a = χ := Over.OverMorphism.ext hja
  have hfac : yoneda.map χ ≫ g = yoneda.map j ≫ yoneda.map a ≫ g := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hcomp]
  exact isClosedMorphism_pullback_fst_congr B S hS f hfac
    (isClosedMorphism_pullback_fst_of_isImmersion B S hS hX hY
      (isAlgebraicSpace_yoneda B S hS W) f (yoneda.map a ≫ g) (yoneda.map j) hjimm hclosed)

/-- The affine-space test over a scheme `V` gives closedness of the base change of `f` along
any morphism to `Y` which factors through `V` by a morphism of the site whose underlying
morphism of schemes is locally of finite presentation.

The affine opens of the source form a family of étale charts covering its points, and
closedness descends along such a family; over an affine open the previous statement applies. -/
theorem isClosedMorphism_pullback_fst_of_yonedaMap_locallyOfFinitePresentation
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (htest : ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V), IsAffineSpaceOver B S hS V W n a ∧
      IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f))
    (U : BigFppfOver B S hS) (ψ : U ⟶ V)
    (hψ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map ψ)) :
    IsClosedMorphism B S hS (pullback.fst (yoneda.map ψ ≫ g) f) := by
  refine isClosedMap_of_isOpenMap_family_cartesian
    (pointsMap B S hS (pullback (yoneda.map ψ ≫ g) f) (pullback.fst (yoneda.map ψ ≫ g) f))
    (fun O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens ↦ pointsMap B S hS
      (pullback (yoneda.map (openSiteObjectHom B S hS U O.1)) (pullback.fst (yoneda.map ψ ≫ g) f))
      (pullback.snd (yoneda.map (openSiteObjectHom B S hS U O.1))
        (pullback.fst (yoneda.map ψ ≫ g) f)))
    (fun O ↦ pointsMap B S hS
      (pullback (yoneda.map (openSiteObjectHom B S hS U O.1)) (pullback.fst (yoneda.map ψ ≫ g) f))
      (pullback.fst (yoneda.map (openSiteObjectHom B S hS U O.1))
        (pullback.fst (yoneda.map ψ ≫ g) f)))
    (fun O ↦ pointsMap B S hS (yoneda.obj (openSiteObject B S hS U O.1))
      (yoneda.map (openSiteObjectHom B S hS U O.1)))
    (fun _ x ↦ pointsMap_apply_comm B S hS pullback.condition.symm x)
    (fun O c w hcw ↦ exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback (yoneda.map (openSiteObjectHom B S hS U O.1))
        (pullback.fst (yoneda.map ψ ≫ g) f)).flip c w hcw)
    (fun _ ↦ continuous_pointsMap B S hS _)
    (fun O ↦ isOpenMap_pointsMap_of_etale B S hS (isAlgebraicSpace_yoneda B S hS U)
      (openSiteObject B S hS U O.1) (yoneda.map (openSiteObjectHom B S hS U O.1))
      (presheaf_etale_yonedaMap_openSiteObjectHom B S hS U O.1))
    (fun z ↦ exists_affineOpen_pointsMap_yonedaMap_eq B S hS U z)
    (fun O ↦ ?_)
  refine isClosedMap_pointsMap_pullback_fst_pullback_fst B S hS f (yoneda.map ψ ≫ g)
    (yoneda.map (openSiteObjectHom B S hS U O.1)) ?_
  have hmap : yoneda.map (openSiteObjectHom B S hS U O.1) ≫ yoneda.map ψ ≫ g =
      yoneda.map (openSiteObjectHom B S hS U O.1 ≫ ψ) ≫ g := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
  refine isClosedMorphism_pullback_fst_congr B S hS f hmap ?_
  refine isClosedMorphism_pullback_fst_of_isAffine_of_locallyOfFinitePresentation B S hS hX hY f
    V g htest (openSiteObject B S hS U O.1) (openSiteObjectHom B S hS U O.1 ≫ ψ) O.2 ?_
  have hopen : LocallyOfFinitePresentation (O.1).ι := inferInstance
  rw [CategoryTheory.Functor.map_comp, map_openSiteObjectHom]
  exact MorphismProperty.comp_mem _ _ _ hopen hψ

/-- The second projection of a fibre product of algebraic spaces is locally of finite
presentation when the first factor is, by stability under base change. -/
theorem isLocallyOfFinitePresentation_pullback_snd {Z V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y) (h : Z ⟶ Y) (g : V ⟶ Y)
    (hh : IsLocallyOfFinitePresentation B S hS h) :
    IsLocallyOfFinitePresentation B S hS (pullback.snd h g) := by
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let Vs : AlgebraicSpaces B S hS := ⟨V, hV⟩
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  exact (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk h : Zs ⟶ Ys) (ObjectProperty.homMk g : Vs ⟶ Ys)) hh

/-- **Stacks 0CM9, (3) implies (2).** If `f : X ⟶ Y` passes the affine-space test over one
surjective étale scheme atlas `V ⟶ Y` of the target, then the base change of `f` along every
morphism to `Y` which is locally of finite presentation is closed.

Closedness of `|Z ×_Y X| → |Z|` may be checked after the base change along the composite of an
étale atlas of `Z ×_Y V` with the projection to `Z`, which is open and surjective on points;
that composite exhibits the test object as a morphism of the site into `V` locally of finite
presentation, where the previous statement applies.

Quasi-compactness of `f` is not needed: it enters Tag 0CM9 only through the implication from
the finitely presented tests back to universal closedness. -/
@[stacks 0CM9 "(3) implies (2)"]
theorem isClosedMorphism_pullback_fst_of_affineSpaceTest
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (hgsurj : IsSurjective B S hS g) (hgetale : IsEtale B S hS g)
    (htest : ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V), IsAffineSpaceOver B S hS V W n a ∧
      IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f))
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z) (h : Z ⟶ Y)
    (hh : IsLocallyOfFinitePresentation B S hS h) :
    IsClosedMorphism B S hS (pullback.fst h f) := by
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hZv : IsAlgebraicSpace B S hS (pullback h g) :=
    isAlgebraicSpace_pullback B S hS h g hZ hV hY
  have hbcEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  -- the projection `Z ×_Y V ⟶ Z` is a base change of `g`, hence étale and surjective on points
  have hq₁et : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst h g) :=
    hbcEt.of_isPullback (IsPullback.of_hasPullback h g).flip
      (presheaf_etale_of_isEtale B S hS hgetale)
  have hq₁surj : Function.Surjective (pointsMap B S hS (pullback h g) (pullback.fst h g)) :=
    surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback h g).flip hgsurj
  -- an étale atlas of `Z ×_Y V`, composed with that projection
  obtain ⟨U, c, hcsurj₀, hcet⟩ := hZv.exists_atlas
  have hcsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) c) :=
    (surjective_iff_surjective_pointsMap B S hS _ hZv U c).mp hcsurj₀
  refine isClosedMap_pointsMap_pullback_fst_of_comp B S hS f h (c ≫ pullback.fst h g)
    (fun C hC ↦ isClosed_of_isOpenMap_of_surjective
      ((isOpenMap_pointsMap_of_presheafEtale B S hS _ hq₁et).comp
        (isOpenMap_pointsMap_of_presheafEtale B S hS c hcet))
      (hq₁surj.comp hcsurj) (by rwa [pointsMap_comp] at hC)) ?_
  -- the resulting test object is a morphism of the site into `V`
  let ψ : U ⟶ V := yoneda.preimage (c ≫ pullback.snd h g)
  have hψmap : yoneda.map ψ = c ≫ pullback.snd h g := yoneda.map_preimage _
  have hfac : (c ≫ pullback.fst h g) ≫ h = yoneda.map ψ ≫ g := by
    rw [hψmap, Category.assoc, Category.assoc, pullback.condition]
  refine isClosedMorphism_pullback_fst_congr B S hS f hfac ?_
  -- it is locally of finite presentation, being an étale atlas followed by a base change of `h`
  have hψlfp : IsLocallyOfFinitePresentation B S hS (yoneda.map ψ) := by
    rw [hψmap]
    exact isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hZv hV
      c (pullback.snd h g)
      (isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_of_presheaf_etale B S hS hcet))
        (isLocallyOfFinitePresentation_pullback_snd B S hS hZ hV hY h g hh)
  have hψsch : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map ψ) := by
    have := isMultiplicative_presheaf_etale B S hS
    exact hψlfp U V (𝟙 _) (𝟙 _) ψ (MorphismProperty.id_mem _ _) (MorphismProperty.id_mem _ _)
      (by simp)
  exact isClosedMorphism_pullback_fst_of_yonedaMap_locallyOfFinitePresentation B S hS hX hY f
    V g htest U ψ hψsch

/-! ### The two implications out of universal closedness -/

/-- **Stacks 0CM9, (1) implies (2).** The base change of a universally closed morphism of
algebraic spaces over `S` along a morphism which is locally of finite presentation is
closed. -/
@[stacks 0CM9 "(1) implies (2)"]
theorem isClosedMorphism_pullback_fst_of_universallyClosed (f : X ⟶ Y)
    (hf : UniversallyClosed B S hS f) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (h : Z ⟶ Y)
    (_hh : IsLocallyOfFinitePresentation B S hS h) :
    IsClosedMorphism B S hS (pullback.fst h f) :=
  hf Z hZ h

/-- **Stacks 0CM9, (1) implies (3).** A universally closed morphism of algebraic spaces over
`S` passes the affine-space test over every surjective étale scheme atlas of its target: each
affine space over the atlas is an object of the site mapping to the target, so the base change
of `f` along it is closed. -/
@[stacks 0CM9 "(1) implies (3)"]
theorem exists_affineSpaceTest_of_universallyClosed (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : UniversallyClosed B S hS f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      IsSurjective B S hS g ∧ IsEtale B S hS g ∧
        ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V), IsAffineSpaceOver B S hS V W n a ∧
          IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f) := by
  obtain ⟨V, g, hgsurj, hgetale⟩ := hY.exists_atlas
  refine ⟨V, g, (surjective_iff_surjective_pointsMap B S hS Y hY V g).mp hgsurj,
    isEtale_of_presheaf_etale B S hS hgetale, fun n ↦ ?_⟩
  obtain ⟨W, a, ha⟩ := exists_isAffineSpaceOver B S hS V n
  exact ⟨W, a, ha, hf _ (isAlgebraicSpace_yoneda B S hS W) (yoneda.map a ≫ g)⟩

/-! ### The remaining implication -/

/-- Closedness of `|Z ×_Y X| → |Z|`, read on the fibre product written with the source first.
The two spellings of the fibre product are exchanged by its symmetry isomorphism, which is a
homeomorphism on points carrying one projection to the other. -/
private theorem isClosed_image_pointsMap_pullback_snd
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (h : Z ⟶ Y)
    (hc : IsClosedMorphism B S hS (pullback.fst h f))
    (C : Set (points B S hS (pullback f h))) (hC : IsClosed C) :
    IsClosed (pointsMap B S hS (pullback f h) (pullback.snd f h) '' C) := by
  have himg : pointsMap B S hS (pullback f h) (pullback.snd f h) '' C =
      pointsMap B S hS (pullback h f) (pullback.fst h f) ''
        (pointsMap B S hS (pullback f h) (pullbackSymmetry f h).hom '' C) := by
    rw [← Set.image_comp, ← pointsMap_comp, pullbackSymmetry_hom_comp_fst]
  rw [himg]
  exact hc _ (isClosedMap_pointsMap_of_isIso B S hS (pullbackSymmetry f h).hom _ hC)

/-- **Stacks 0CM9, (2) implies (1).** A quasi-compact morphism of algebraic spaces over `S`
whose base changes along the morphisms locally of finite presentation are closed is
universally closed.

Let `T ⊆ |X ×_Y Z|` be closed and let `z` be a point of `|Z|` outside the image of `T`. The
separation statement of Tag 0CM8 produces an étale neighbourhood `(V, v)` of `z`, a
factorization `V ⟶ Z' ⟶ Y` with `Z' ⟶ Y` locally of finite presentation, and a closed
`T' ⊆ |X ×_Y Z'|` receiving the inverse image of `T` and missing the image of `v`. Since
`|V| → |Z|` is open, `v` lies in the closure of the inverse image of the image of `T`, which
by Tag 03H4 is the image of the inverse image of `T` in `|X ×_Y V|`; that image lands in the
inverse image along `V ⟶ Z'` of the image of `T'`, a closed set by hypothesis. Hence the image
of `v` lies in the image of `T'` after all, so `z` is not in the closure of the image of
`T`. -/
@[stacks 0CM9 "(2) implies (1)"]
theorem universallyClosed_of_isClosedMorphism_of_isLocallyOfFinitePresentation
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f)
    (htest : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
      ∀ h : Z ⟶ Y, IsLocallyOfFinitePresentation B S hS h →
        IsClosedMorphism B S hS (pullback.fst h f)) :
    UniversallyClosed B S hS f := by
  intro Z hZ g T hT
  have himg : pointsMap B S hS (pullback g f) (pullback.fst g f) '' T =
      pointsMap B S hS (pullback f g) (pullback.snd f g) ''
        (pointsMap B S hS (pullback g f) (pullbackSymmetry g f).hom '' T) := by
    rw [← Set.image_comp, ← pointsMap_comp, pullbackSymmetry_hom_comp_snd]
  rw [himg]
  have hTsclosed : IsClosed (pointsMap B S hS (pullback g f) (pullbackSymmetry g f).hom '' T) :=
    isClosedMap_pointsMap_of_isIso B S hS (pullbackSymmetry g f).hom _ hT
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  by_contra hzT
  obtain ⟨V, Z', p, v, a, b, T', r, q, _, _, hp, hpv, _, hb, hT'closed, hav,
    _, _, sqr, _, hq₂, hsub⟩ :=
    exists_affine_etale_isLocallyOfFinitePresentation_separation B S hS hX hY hZ f g hf z _
      hTsclosed hzT
  have hvclosure : v ∈ closure (pointsMap B S hS _ (pullback.snd f (p ≫ g)) ''
      (pointsMap B S hS _ r ⁻¹'
        (pointsMap B S hS (pullback g f) (pullbackSymmetry g f).hom '' T))) := by
    rw [← preimage_image_pointsMap_of_isPullback B S hS sqr _]
    refine (isOpenMap_pointsMap_of_isEtale B S hS p (isAlgebraicSpace_yoneda B S hS V) hZ
      hp).preimage_closure_subset_closure_preimage ?_
    show pointsMap B S hS (yoneda.obj V) p v ∈ closure _
    rwa [hpv]
  have hinc : pointsMap B S hS _ (pullback.snd f (p ≫ g)) ''
      (pointsMap B S hS _ r ⁻¹'
        (pointsMap B S hS (pullback g f) (pullbackSymmetry g f).hom '' T)) ⊆
      pointsMap B S hS (yoneda.obj V) a ⁻¹'
        (pointsMap B S hS (pullback f b) (pullback.snd f b) '' T') := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨pointsMap B S hS _ q s, hsub ⟨s, hs, rfl⟩, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hq₂]
  exact hav (closure_minimal hinc
    ((isClosed_image_pointsMap_pullback_snd B S hS f b
        (htest _ (isAlgebraicSpace_yoneda B S hS Z') b hb) T' hT'closed).preimage
      (continuous_pointsMap B S hS a)) hvclosure)

/-! ### Stacks 0CM9 -/

/-- **Stacks 0CM9.** For a quasi-compact morphism `f : X ⟶ Y` of algebraic spaces over `S` the
following are equivalent: `f` is universally closed; the base change of `f` along every
morphism to `Y` which is locally of finite presentation is closed; and there is a surjective
étale morphism to `Y` from a presheaf represented by an object `V` of the site such that for
every `n` the base change of `f` along affine `n`-space over `V` is closed.

The implication from the second condition to the first is the one using quasi-compactness of
`f`, through the separation statement of Tag 0CM8. -/
@[stacks 0CM9]
theorem universallyClosed_tfae_of_isQuasiCompact (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f) :
    List.TFAE
      [UniversallyClosed B S hS f,
        ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
          ∀ h : Z ⟶ Y, IsLocallyOfFinitePresentation B S hS h →
            IsClosedMorphism B S hS (pullback.fst h f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
              IsAffineSpaceOver B S hS V W n a ∧
                IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f)] := by
  tfae_have 1 → 2 := fun h Z hZ k hk ↦
    isClosedMorphism_pullback_fst_of_universallyClosed B S hS f h hZ k hk
  tfae_have 2 → 1 := fun h ↦
    universallyClosed_of_isClosedMorphism_of_isLocallyOfFinitePresentation B S hS hX hY f hf h
  tfae_have 1 → 3 := fun h ↦ exists_affineSpaceTest_of_universallyClosed B S hS hY f h
  tfae_have 3 → 2 := by
    rintro ⟨V, g, hgsurj, hgetale, htest⟩ Z hZ k hk
    exact isClosedMorphism_pullback_fst_of_affineSpaceTest B S hS hX hY f V g hgsurj hgetale
      htest hZ k hk
  tfae_finish

end AlgebraicGeometry.Space

end
