module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSpectrum
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-!
# Base change of an affine groupoid scheme along an extension of its invariant ring

Let `G` be a groupoid scheme with affine object and arrow schemes and with finite locally free
source and target. Its object and arrow schemes are then schemes over the spectrum of the ring
`C` of invariant functions, and the whole groupoid is a groupoid scheme over `Spec C`. Base
changing it along `Spec C' ⟶ Spec C` for an extension `C ⟶ C'` therefore produces a groupoid
scheme over `Spec C'` whose object and arrow rings are `A ⊗[C] C'` and `B ⊗[C] C'`, and whose
source and target maps are the scalar extensions of those of `G`.

`AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange`, defined in
`StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSpectrum`, packages that groupoid together
with the identifications of its coordinate rings, the cartesian squares exhibiting it as a base
change, and the compatibility of every structure map with the projection to `G`. This file
constructs one.

## Main results

* `AlgebraicGeometry.GroupoidScheme.source_comp_objectsToInvariantSpectrum`: the structure
  morphism to the invariant spectrum coequalizes the source and the target map.
* `AlgebraicGeometry.GroupoidScheme.mapObjects_comp_objectsToInvariantSpectrum`: a morphism of
  groupoid schemes is compatible with the structure morphisms to the invariant spectra.
* `AlgebraicGeometry.GroupoidScheme.exists_affineInvariantBaseChange`: the base change exists.

## Implementation notes

The groupoid over `Spec C` is built by hand rather than by transporting `G` along a functor:
its object and arrow schemes are those of `G`, re-read as schemes over `Spec C`, and all its
structure maps are those of `G`. The base change along `Spec C' ⟶ Spec C` is then supplied by
`AlgebraicGeometry.GroupoidScheme.exists_baseChange`, and the affine comparison identifies the
resulting fibre products with the spectra of the two tensor products.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### The groupoid over the spectrum of the invariant ring -/

/-- The canonical morphisms to the invariant spectra intertwine the map on object schemes of a
morphism of groupoid schemes with the induced map on invariant rings. -/
@[reassoc]
theorem mapObjects_comp_objectsToInvariantSpectrum {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : GroupoidScheme.Hom G' G) :
    F.mapObjects.left ≫ objectsToInvariantSpectrum G =
      objectsToInvariantSpectrum G' ≫ Spec.map (CommRingCat.ofHom (invariantRingMap F)) := by
  have hcomm : CommRingCat.ofHom (invariantRingMap F) ≫
      CommRingCat.ofHom (invariantRing G').subtype =
      CommRingCat.ofHom (invariantRing G).subtype ≫ F.mapObjects.left.appTop := rfl
  calc F.mapObjects.left ≫ objectsToInvariantSpectrum G
      = G'.objects.left.toSpecΓ ≫ Spec.map F.mapObjects.left.appTop ≫
          Spec.map (CommRingCat.ofHom (invariantRing G).subtype) := by
        rw [objectsToInvariantSpectrum, Scheme.toSpecΓ_naturality_assoc]
    _ = G'.objects.left.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (invariantRing G).subtype ≫
            F.mapObjects.left.appTop) := by rw [← Spec.map_comp]
    _ = G'.objects.left.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (invariantRingMap F) ≫
            CommRingCat.ofHom (invariantRing G').subtype) := by rw [hcomm]
    _ = objectsToInvariantSpectrum G' ≫ Spec.map (CommRingCat.ofHom (invariantRingMap F)) := by
        rw [objectsToInvariantSpectrum, Spec.map_comp, Category.assoc]

/-! ### Compatibility of the structure maps with the invariant spectrum -/

/-- The morphism to the spectrum of the invariant ring coequalizes the source and the target
map. -/
theorem source_comp_objectsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] :
    G.source.left ≫ objectsToInvariantSpectrum G =
      G.target.left ≫ objectsToInvariantSpectrum G := by
  apply AlgebraicGeometry.ext_of_isAffine
  apply CommRingCat.hom_ext
  ext c
  simp only [Scheme.Hom.comp_appTop, objectsToInvariantSpectrum, Scheme.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality]
  show (sourceMap G) ((Scheme.ΓSpecIso (.of (invariantRing G))).hom c).val =
    (targetMap G) ((Scheme.ΓSpecIso (.of (invariantRing G))).hom c).val
  exact ((Scheme.ΓSpecIso (.of (invariantRing G))).hom c).property

private theorem identity_comp_arrowsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.identity.left ≫ arrowsToInvariantSpectrum G = objectsToInvariantSpectrum G := by
  show (G.identity ≫ G.source).left ≫ objectsToInvariantSpectrum G = _
  rw [G.source_identity]
  simp

private theorem inverse_comp_arrowsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] :
    G.inverse.left ≫ arrowsToInvariantSpectrum G = arrowsToInvariantSpectrum G := by
  show (G.inverse ≫ G.source).left ≫ objectsToInvariantSpectrum G = _
  rw [G.source_inverse]
  exact (source_comp_objectsToInvariantSpectrum G).symm

private theorem comp_comp_arrowsToInvariantSpectrum {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.comp.left ≫ arrowsToInvariantSpectrum G =
      (pullback.snd G.source G.target).left ≫ arrowsToInvariantSpectrum G := by
  show (G.comp ≫ G.source).left ≫ objectsToInvariantSpectrum G = _
  rw [G.source_comp, Over.comp_left]
  rfl

/-! ### The groupoid structure over the invariant spectrum -/

section InvariantBase

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The source map, read in schemes over the spectrum of the invariant ring. -/
private def invariantBaseSource :
    Over.mk (arrowsToInvariantSpectrum G) ⟶ Over.mk (objectsToInvariantSpectrum G) :=
  Over.homMk G.source.left rfl

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]

/-- The target map, read in schemes over the spectrum of the invariant ring. -/
private def invariantBaseTarget :
    Over.mk (arrowsToInvariantSpectrum G) ⟶ Over.mk (objectsToInvariantSpectrum G) :=
  Over.homMk G.target.left (source_comp_objectsToInvariantSpectrum G).symm

private theorem invariantBaseComposables_condition :
    (pullback.fst (invariantBaseSource G) (invariantBaseTarget G)).left ≫ G.source.left =
      (pullback.snd (invariantBaseSource G) (invariantBaseTarget G)).left ≫ G.target.left := by
  show (pullback.fst (invariantBaseSource G) (invariantBaseTarget G) ≫
      invariantBaseSource G).left =
    (pullback.snd (invariantBaseSource G) (invariantBaseTarget G) ≫
      invariantBaseTarget G).left
  exact congrArg Over.Hom.left (pullback.condition :
    pullback.fst (invariantBaseSource G) (invariantBaseTarget G) ≫ invariantBaseSource G =
      pullback.snd (invariantBaseSource G) (invariantBaseTarget G) ≫ invariantBaseTarget G)

/-- The comparison from the composable arrows over the invariant spectrum to the composable
arrows over `S`. -/
private def invariantBaseComposables :
    (pullback (invariantBaseSource G) (invariantBaseTarget G)).left ⟶
      (pullback G.source G.target).left :=
  (overFibreProduct_isPullback G.source G.target).lift
    (pullback.fst (invariantBaseSource G) (invariantBaseTarget G)).left
    (pullback.snd (invariantBaseSource G) (invariantBaseTarget G)).left
    (invariantBaseComposables_condition G)

@[reassoc]
private theorem invariantBaseComposables_fst :
    invariantBaseComposables G ≫ (pullback.fst G.source G.target).left =
      (pullback.fst (invariantBaseSource G) (invariantBaseTarget G)).left :=
  (overFibreProduct_isPullback G.source G.target).lift_fst _ _
    (invariantBaseComposables_condition G)

@[reassoc]
private theorem invariantBaseComposables_snd :
    invariantBaseComposables G ≫ (pullback.snd G.source G.target).left =
      (pullback.snd (invariantBaseSource G) (invariantBaseTarget G)).left :=
  (overFibreProduct_isPullback G.source G.target).lift_snd _ _
    (invariantBaseComposables_condition G)

/-- Composition, read on underlying schemes. -/
private def invariantBaseCompMap :
    (pullback (invariantBaseSource G) (invariantBaseTarget G)).left ⟶ G.arrows.left :=
  invariantBaseComposables G ≫ G.comp.left

private theorem invariantBaseCompMap_over :
    invariantBaseCompMap G ≫ arrowsToInvariantSpectrum G =
      (pullback (invariantBaseSource G) (invariantBaseTarget G)).hom := by
  calc
    invariantBaseCompMap G ≫ arrowsToInvariantSpectrum G =
        invariantBaseComposables G ≫ G.comp.left ≫ arrowsToInvariantSpectrum G := by
      rw [invariantBaseCompMap, Category.assoc]
    _ = invariantBaseComposables G ≫
          (pullback.snd G.source G.target).left ≫ arrowsToInvariantSpectrum G := by
      rw [comp_comp_arrowsToInvariantSpectrum]
    _ = (pullback.snd (invariantBaseSource G) (invariantBaseTarget G)).left ≫
          arrowsToInvariantSpectrum G := by
      rw [← Category.assoc, invariantBaseComposables_snd G]
    _ = (pullback (invariantBaseSource G) (invariantBaseTarget G)).hom :=
      Over.w (pullback.snd (invariantBaseSource G) (invariantBaseTarget G))

/-- A test object over the invariant spectrum, re-read as a test object over `S`. -/
private abbrev invariantBaseTestObject {G : GroupoidScheme S}
    {T : Over (Spec (.of (invariantRing G)))}
    (f : T ⟶ Over.mk (arrowsToInvariantSpectrum G)) : Over S :=
  Over.mk (f.left ≫ G.arrows.hom)

/-- A generalized arrow over the invariant spectrum, re-read as a generalized arrow over `S`. -/
private def invariantBaseTestArrow {G : GroupoidScheme S}
    {T : Over (Spec (.of (invariantRing G)))}
    (f : T ⟶ Over.mk (arrowsToInvariantSpectrum G)) : invariantBaseTestObject f ⟶ G.arrows :=
  Over.homMk f.left rfl

private theorem invariantBaseTestArrow_left {G : GroupoidScheme S}
    {T : Over (Spec (.of (invariantRing G)))}
    (f : T ⟶ Over.mk (arrowsToInvariantSpectrum G)) :
    (invariantBaseTestArrow f).left = f.left := rfl

variable {G}

private theorem invariantBaseCompatibleArrow_over {T : Over (Spec (.of (invariantRing G)))}
    (f g : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (w : f ≫ invariantBaseSource G = g ≫ invariantBaseTarget G) :
    g.left ≫ G.arrows.hom = f.left ≫ G.arrows.hom := by
  have hw : f.left ≫ G.source.left = g.left ≫ G.target.left := by
    show (f ≫ invariantBaseSource G).left = (g ≫ invariantBaseTarget G).left
    exact congrArg Over.Hom.left w
  simpa using (hw =≫ G.objects.hom).symm

/-- The second of two composable generalized arrows over the invariant spectrum, re-read as a
generalized arrow over `S` with the same test object as the first. -/
private def invariantBaseCompatibleArrow {T : Over (Spec (.of (invariantRing G)))}
    (f g : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (w : f ≫ invariantBaseSource G = g ≫ invariantBaseTarget G) :
    invariantBaseTestObject f ⟶ G.arrows :=
  Over.homMk g.left (invariantBaseCompatibleArrow_over f g w)

private theorem invariantBaseTestArrows_composable {T : Over (Spec (.of (invariantRing G)))}
    (f g : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (w : f ≫ invariantBaseSource G = g ≫ invariantBaseTarget G) :
    f.left ≫ G.source.left = g.left ≫ G.target.left :=
  congrArg Over.Hom.left w

private theorem invariantBaseCompatibleArrow_source_target
    {T : Over (Spec (.of (invariantRing G)))}
    (f g : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (w : f ≫ invariantBaseSource G = g ≫ invariantBaseTarget G) :
    invariantBaseTestArrow f ≫ G.source = invariantBaseCompatibleArrow f g w ≫ G.target :=
  Over.OverMorphism.ext (invariantBaseTestArrows_composable f g w)

private theorem invariantBaseLift_comp_composables {T : Over (Spec (.of (invariantRing G)))}
    (f g : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (w : f ≫ invariantBaseSource G = g ≫ invariantBaseTarget G) :
    (pullback.lift f g w).left ≫ invariantBaseComposables G =
      (overFibreProduct_isPullback G.source G.target).lift f.left g.left
        (invariantBaseTestArrows_composable f g w) := by
  refine (overFibreProduct_isPullback G.source G.target).hom_ext ?_ ?_
  · calc
      (pullback.lift f g w).left ≫ invariantBaseComposables G ≫
            (pullback.fst G.source G.target).left =
          (pullback.lift f g w).left ≫
            (pullback.fst (invariantBaseSource G) (invariantBaseTarget G)).left := by
        rw [invariantBaseComposables_fst G]
      _ = f.left := by
        simpa only [Over.comp_left] using congrArg Over.Hom.left (pullback.lift_fst f g w)
      _ = _ := ((overFibreProduct_isPullback G.source G.target).lift_fst _ _ _).symm
  · calc
      (pullback.lift f g w).left ≫ invariantBaseComposables G ≫
            (pullback.snd G.source G.target).left =
          (pullback.lift f g w).left ≫
            (pullback.snd (invariantBaseSource G) (invariantBaseTarget G)).left := by
        rw [invariantBaseComposables_snd G]
      _ = g.left := by
        simpa only [Over.comp_left] using congrArg Over.Hom.left (pullback.lift_snd f g w)
      _ = _ := ((overFibreProduct_isPullback G.source G.target).lift_snd _ _ _).symm

/-- Composition over the invariant spectrum is computed by composition over `S`. -/
private theorem invariantBaseLift_comp_compMap {T : Over (Spec (.of (invariantRing G)))}
    (a b r : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (w : a ≫ invariantBaseSource G = b ≫ invariantBaseTarget G)
    (p q : invariantBaseTestObject r ⟶ G.arrows) (hp : p.left = a.left) (hq : q.left = b.left)
    (hw : p ≫ G.source = q ≫ G.target) :
    (pullback.lift a b w).left ≫ invariantBaseCompMap G =
      (pullback.lift p q hw).left ≫ G.comp.left := by
  rw [invariantBaseCompMap, ← Category.assoc, invariantBaseLift_comp_composables]
  simpa [hp, hq] using
    congrArg (fun k => k ≫ G.comp.left) (overFibreProduct_lift_left G.source G.target p q hw).symm

/-- Composition over the invariant spectrum, computed through any equation satisfied by
composition over `S`. -/
private theorem invariantBaseLift_comp_compMap_eq {T : Over (Spec (.of (invariantRing G)))}
    (a b r : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (w : a ≫ invariantBaseSource G = b ≫ invariantBaseTarget G)
    (p q : invariantBaseTestObject r ⟶ G.arrows) (hp : p.left = a.left) (hq : q.left = b.left)
    (hw : p ≫ G.source = q ≫ G.target) {x : invariantBaseTestObject r ⟶ G.arrows}
    (hx : pullback.lift p q hw ≫ G.comp = x) :
    (pullback.lift a b w).left ≫ invariantBaseCompMap G = x.left :=
  (invariantBaseLift_comp_compMap a b r w p q hp hq hw).trans (congrArg Over.Hom.left hx)

variable (G)

/-- The identity section, read in schemes over the spectrum of the invariant ring. -/
private def invariantBaseIdentity :
    Over.mk (objectsToInvariantSpectrum G) ⟶ Over.mk (arrowsToInvariantSpectrum G) :=
  Over.homMk G.identity.left (identity_comp_arrowsToInvariantSpectrum G)

/-- The inverse, read in schemes over the spectrum of the invariant ring. -/
private def invariantBaseInverse :
    Over.mk (arrowsToInvariantSpectrum G) ⟶ Over.mk (arrowsToInvariantSpectrum G) :=
  Over.homMk G.inverse.left (inverse_comp_arrowsToInvariantSpectrum G)

/-- Composition, read in schemes over the spectrum of the invariant ring. -/
private def invariantBaseComp :
    pullback (invariantBaseSource G) (invariantBaseTarget G) ⟶
      Over.mk (arrowsToInvariantSpectrum G) :=
  Over.homMk (invariantBaseCompMap G) (invariantBaseCompMap_over G)

private theorem invariantBaseGroupoid_assoc {T : Over (Spec (.of (invariantRing G)))}
    (f g h : T ⟶ Over.mk (arrowsToInvariantSpectrum G))
    (wfg : f ≫ invariantBaseSource G = g ≫ invariantBaseTarget G)
    (wgh : g ≫ invariantBaseSource G = h ≫ invariantBaseTarget G)
    (w₁ : (pullback.lift f g wfg ≫ invariantBaseComp G) ≫ invariantBaseSource G =
      h ≫ invariantBaseTarget G)
    (w₂ : f ≫ invariantBaseSource G =
      (pullback.lift g h wgh ≫ invariantBaseComp G) ≫ invariantBaseTarget G) :
    pullback.lift (pullback.lift f g wfg ≫ invariantBaseComp G) h w₁ ≫ invariantBaseComp G =
      pullback.lift f (pullback.lift g h wgh ≫ invariantBaseComp G) w₂ ≫ invariantBaseComp G := by
  let T₀ := invariantBaseTestObject f
  let f₀ := invariantBaseTestArrow f
  let g₀ := invariantBaseCompatibleArrow f g wfg
  have hBase : f.left ≫ G.arrows.hom = h.left ≫ G.arrows.hom :=
    (invariantBaseCompatibleArrow_over f g wfg).symm.trans
      (invariantBaseCompatibleArrow_over g h wgh).symm
  let h₀ : T₀ ⟶ G.arrows := Over.homMk h.left hBase.symm
  have wfg₀ : f₀ ≫ G.source = g₀ ≫ G.target :=
    invariantBaseCompatibleArrow_source_target f g wfg
  have wgh₀ : g₀ ≫ G.source = h₀ ≫ G.target :=
    Over.OverMorphism.ext (invariantBaseTestArrows_composable g h wgh)
  have w₁₀ : (pullback.lift f₀ g₀ wfg₀ ≫ G.comp) ≫ G.source = h₀ ≫ G.target := by
    simp only [Category.assoc, G.source_comp, pullback.lift_snd_assoc]
    exact wgh₀
  have w₂₀ : f₀ ≫ G.source = (pullback.lift g₀ h₀ wgh₀ ≫ G.comp) ≫ G.target := by
    simp only [Category.assoc, G.target_comp, pullback.lift_fst_assoc]
    exact wfg₀
  let c₁ := pullback.lift f₀ g₀ wfg₀ ≫ G.comp
  let c₂ := pullback.lift g₀ h₀ wgh₀ ≫ G.comp
  let n₁ := pullback.lift f g wfg ≫ invariantBaseComp G
  let n₂ := pullback.lift g h wgh ≫ invariantBaseComp G
  have hn₁ : n₁.left = c₁.left := by
    dsimp only [n₁, c₁]
    exact invariantBaseLift_comp_compMap f g f wfg f₀ g₀ rfl rfl wfg₀
  have hn₂ : n₂.left = c₂.left := by
    dsimp only [n₂, c₂]
    exact invariantBaseLift_comp_compMap g h f wgh g₀ h₀ rfl rfl wgh₀
  have hOld := G.assoc T₀ f₀ g₀ h₀ wfg₀ wgh₀ w₁₀ w₂₀
  have hLeft : (pullback.lift n₁ h w₁).left ≫ invariantBaseCompMap G =
      (pullback.lift c₁ h₀ w₁₀).left ≫ G.comp.left :=
    invariantBaseLift_comp_compMap n₁ h f w₁ c₁ h₀ hn₁.symm rfl w₁₀
  have hRight : (pullback.lift f n₂ w₂).left ≫ invariantBaseCompMap G =
      (pullback.lift f₀ c₂ w₂₀).left ≫ G.comp.left :=
    invariantBaseLift_comp_compMap f n₂ f w₂ f₀ c₂ rfl hn₂.symm w₂₀
  have hOldAssoc : (pullback.lift c₁ h₀ w₁₀).left ≫ G.comp.left =
      (pullback.lift f₀ c₂ w₂₀).left ≫ G.comp.left := by
    simpa [c₁, c₂] using congrArg Over.Hom.left hOld
  exact (Over.forget (Spec (.of (invariantRing G)))).map_injective
    (hLeft.trans (hOldAssoc.trans hRight.symm))

/-- The object and arrow schemes of an affine groupoid scheme, read as schemes over the spectrum
of the invariant ring, form a groupoid scheme with the same structure maps. -/
private def invariantBaseGroupoid : GroupoidScheme (Spec (.of (invariantRing G))) where
  objects := Over.mk (objectsToInvariantSpectrum G)
  arrows := Over.mk (arrowsToInvariantSpectrum G)
  source := invariantBaseSource G
  target := invariantBaseTarget G
  comp := invariantBaseComp G
  identity := invariantBaseIdentity G
  inverse := invariantBaseInverse G
  source_identity := by
    apply Over.OverMorphism.ext
    change (G.identity ≫ G.source).left = 𝟙 G.objects.left
    exact congrArg Over.Hom.left G.source_identity
  target_identity := by
    apply Over.OverMorphism.ext
    change (G.identity ≫ G.target).left = 𝟙 G.objects.left
    exact congrArg Over.Hom.left G.target_identity
  source_inverse := by
    apply Over.OverMorphism.ext
    change (G.inverse ≫ G.source).left = G.target.left
    exact congrArg Over.Hom.left G.source_inverse
  target_inverse := by
    apply Over.OverMorphism.ext
    change (G.inverse ≫ G.target).left = G.source.left
    exact congrArg Over.Hom.left G.target_inverse
  source_comp := by
    apply Over.OverMorphism.ext
    change invariantBaseCompMap G ≫ G.source.left =
      (pullback.snd (invariantBaseSource G) (invariantBaseTarget G)).left ≫ G.source.left
    calc
      invariantBaseCompMap G ≫ G.source.left =
          invariantBaseComposables G ≫
            ((pullback.snd G.source G.target).left ≫ G.source.left) := by
        rw [invariantBaseCompMap, Category.assoc]
        exact congrArg (invariantBaseComposables G ≫ ·)
          (congrArg Over.Hom.left G.source_comp)
      _ = (pullback.snd (invariantBaseSource G) (invariantBaseTarget G)).left ≫
            G.source.left := by
        rw [← Category.assoc, invariantBaseComposables_snd G]
  target_comp := by
    apply Over.OverMorphism.ext
    change invariantBaseCompMap G ≫ G.target.left =
      (pullback.fst (invariantBaseSource G) (invariantBaseTarget G)).left ≫ G.target.left
    calc
      invariantBaseCompMap G ≫ G.target.left =
          invariantBaseComposables G ≫
            ((pullback.fst G.source G.target).left ≫ G.target.left) := by
        rw [invariantBaseCompMap, Category.assoc]
        exact congrArg (invariantBaseComposables G ≫ ·)
          (congrArg Over.Hom.left G.target_comp)
      _ = (pullback.fst (invariantBaseSource G) (invariantBaseTarget G)).left ≫
            G.target.left := by
        rw [← Category.assoc, invariantBaseComposables_fst G]
  left_identity := by
    intro T f w
    apply Over.OverMorphism.ext
    let q := invariantBaseTestArrow f
    let p := q ≫ G.target ≫ G.identity
    have wOld : p ≫ G.source = q ≫ G.target := by simp [p, G.source_identity]
    exact invariantBaseLift_comp_compMap_eq _ f f w p q rfl rfl wOld (G.left_identity _ q wOld)
  right_identity := by
    intro T f w
    apply Over.OverMorphism.ext
    let p := invariantBaseTestArrow f
    let q := p ≫ G.source ≫ G.identity
    have wOld : p ≫ G.source = q ≫ G.target := by simp [q, G.target_identity]
    exact invariantBaseLift_comp_compMap_eq f _ f w p q rfl rfl wOld (G.right_identity _ p wOld)
  left_inverse := by
    intro T f w
    apply Over.OverMorphism.ext
    let q := invariantBaseTestArrow f
    let p := q ≫ G.inverse
    have wOld : p ≫ G.source = q ≫ G.target := by simp [p, G.source_inverse]
    exact invariantBaseLift_comp_compMap_eq _ f f w p q rfl rfl wOld (G.left_inverse _ q wOld)
  right_inverse := by
    intro T f w
    apply Over.OverMorphism.ext
    let p := invariantBaseTestArrow f
    let q := p ≫ G.inverse
    have wOld : p ≫ G.source = q ≫ G.target := by simp [q, G.target_inverse]
    exact invariantBaseLift_comp_compMap_eq f _ f w p q rfl rfl wOld (G.right_inverse _ p wOld)
  assoc := fun _ f g h wfg wgh w₁ w₂ => invariantBaseGroupoid_assoc G f g h wfg wgh w₁ w₂

end InvariantBase

/-! ### The affine comparison -/

section Comparison

/-- The inclusion of the left tensor factor, as a ring homomorphism. -/
private theorem includeLeft_toRingHom {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom =
      Algebra.TensorProduct.includeLeftRingHom := rfl

/-- The arrow scheme, read over the spectrum of the invariant ring, is the spectrum of the arrow
ring viewed as an algebra over the invariant ring through the source map. -/
private theorem arrowsToInvariantSpectrum_eq_specMap {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.arrows.left] :
    arrowsToInvariantSpectrum G =
      G.arrows.left.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (RingHom.comp (sourceMap G) (invariantRing G).subtype)) := by
  show G.source.left ≫ G.objects.left.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (invariantRing G).subtype) = _
  rw [Scheme.toSpecΓ_naturality_assoc G.source.left, ← Spec.map_comp]
  rfl

/-- The fibre product of the object scheme with `Spec C'` over the invariant spectrum is the
spectrum of `A ⊗[C] C'`. -/
private def objectsPullbackTensorIso {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    pullback (objectsToInvariantSpectrum G) (invariantSpectrumMap G C') ≅
      Spec (.of (objectRingBaseChange G C')) :=
  asIso (pullback.map (objectsToInvariantSpectrum G) (invariantSpectrumMap G C')
    (Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G) Γ(G.objects.left, ⊤))))
    (Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G) C')))
    G.objects.left.isoSpec.hom (𝟙 _) (𝟙 _) (by rfl) (by rfl)) ≪≫
    pullbackSpecIso (invariantRing G) Γ(G.objects.left, ⊤) C'

/-- The fibre product of the arrow scheme with `Spec C'` over the invariant spectrum is the
spectrum of `B ⊗[C] C'`. -/
private def arrowsPullbackTensorIso {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.arrows.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    pullback (arrowsToInvariantSpectrum G) (invariantSpectrumMap G C') ≅
      Spec (.of (arrowRingBaseChange G C')) :=
  letI := invariantRingAlgebraArrow G
  asIso (pullback.map (arrowsToInvariantSpectrum G) (invariantSpectrumMap G C')
    (Spec.map (CommRingCat.ofHom
      (RingHom.comp (sourceMap G) (invariantRing G).subtype)))
    (Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G) C')))
    G.arrows.left.isoSpec.hom (𝟙 _) (𝟙 _)
    (by rw [arrowsToInvariantSpectrum_eq_specMap]; simp) (by rfl)) ≪≫
    pullbackSpecIso (invariantRing G) Γ(G.arrows.left, ⊤) C'

/-- The projection from `Spec (A ⊗[C] C')` to the object scheme. -/
private def objectsTensorProjection {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    Spec (.of (objectRingBaseChange G C')) ⟶ G.objects.left :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
    Γ(G.objects.left, ⊤) →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom) ≫
    G.objects.left.isoSpec.inv

/-- The projection from `Spec (B ⊗[C] C')` to the arrow scheme. -/
private def arrowsTensorProjection {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.arrows.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    Spec (.of (arrowRingBaseChange G C')) ⟶ G.arrows.left :=
  letI := invariantRingAlgebraArrow G
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
    Γ(G.arrows.left, ⊤) →ₐ[invariantRing G] arrowRingBaseChange G C').toRingHom) ≫
    G.arrows.left.isoSpec.inv

private theorem objectsPullbackTensorIso_projection {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    (objectsPullbackTensorIso G C').hom ≫ objectsTensorProjection G C' =
      pullback.fst (objectsToInvariantSpectrum G) (invariantSpectrumMap G C') := by
  have h : (pullbackSpecIso (invariantRing G) Γ(G.objects.left, ⊤) C').hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        Γ(G.objects.left, ⊤) →ₐ[invariantRing G] objectRingBaseChange G C').toRingHom) =
      pullback.fst _ _ := pullbackSpecIso_hom_fst _ _ _
  dsimp only [objectsPullbackTensorIso, objectsTensorProjection, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, ← Category.assoc _ _ G.objects.left.isoSpec.inv, h]
  dsimp only [pullback.map]
  rw [pullback.lift_fst_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem arrowsPullbackTensorIso_projection {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.arrows.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    (arrowsPullbackTensorIso G C').hom ≫ arrowsTensorProjection G C' =
      pullback.fst (arrowsToInvariantSpectrum G) (invariantSpectrumMap G C') := by
  let : Algebra (invariantRing G) Γ(G.arrows.left, ⊤) := invariantRingAlgebraArrow G
  have h : (pullbackSpecIso (invariantRing G) Γ(G.arrows.left, ⊤) C').hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        Γ(G.arrows.left, ⊤) →ₐ[invariantRing G] arrowRingBaseChange G C').toRingHom) =
      pullback.fst _ _ := pullbackSpecIso_hom_fst _ _ _
  dsimp only [arrowsPullbackTensorIso, arrowsTensorProjection, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, ← Category.assoc _ _ G.arrows.left.isoSpec.inv, h]
  dsimp only [pullback.map]
  rw [pullback.lift_fst_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem objectsPullbackTensorIso_over {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    (objectsPullbackTensorIso G C').hom ≫ (objectSchemeBaseChange G C').hom =
      pullback.snd (objectsToInvariantSpectrum G) (invariantSpectrumMap G C') := by
  have h : (pullbackSpecIso (invariantRing G) Γ(G.objects.left, ⊤) C').hom ≫
      (objectSchemeBaseChange G C').hom = pullback.snd _ _ := pullbackSpecIso_hom_snd _ _ _
  dsimp only [objectsPullbackTensorIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, h]
  dsimp only [pullback.map]
  rw [pullback.lift_snd, Category.comp_id]

private theorem arrowsPullbackTensorIso_over {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.arrows.left] (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    (arrowsPullbackTensorIso G C').hom ≫ (arrowSchemeBaseChange G C').hom =
      pullback.snd (arrowsToInvariantSpectrum G) (invariantSpectrumMap G C') := by
  let : Algebra (invariantRing G) Γ(G.arrows.left, ⊤) := invariantRingAlgebraArrow G
  have h : (pullbackSpecIso (invariantRing G) Γ(G.arrows.left, ⊤) C').hom ≫
      (arrowSchemeBaseChange G C').hom = pullback.snd _ _ := pullbackSpecIso_hom_snd _ _ _
  dsimp only [arrowsPullbackTensorIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, h]
  dsimp only [pullback.map]
  rw [pullback.lift_snd, Category.comp_id]

end Comparison

/-! ### Existence of the base change -/

/-- **Stacks Project, Tag 03BK.** Extending the coordinate rings of an affine groupoid scheme
from its invariant ring produces the indicated groupoid scheme, with finite locally free source
and target. -/
@[stacks 03BK "base_changed_groupoid"]
theorem exists_affineInvariantBaseChange {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (C' : Type u) [CommRing C'] [Algebra (invariantRing G) C'] :
    Nonempty (AffineInvariantBaseChange G C') := by
  let : Algebra (invariantRing G) Γ(G.arrows.left, ⊤) := invariantRingAlgebraArrow G
  obtain ⟨bc⟩ := exists_baseChange (invariantSpectrumMap G C') (invariantBaseGroupoid G)
  let pO : bc.groupoid.objects.left ⟶ G.objects.left := bc.projection.mapObjects.left
  let pA : bc.groupoid.arrows.left ⟶ G.arrows.left := bc.projection.mapArrows.left
  have hpbO : IsPullback pO bc.groupoid.objects.hom (objectsToInvariantSpectrum G)
      (invariantSpectrumMap G C') := bc.isPullback_objects
  have hpbA : IsPullback pA bc.groupoid.arrows.hom (arrowsToInvariantSpectrum G)
      (invariantSpectrumMap G C') := bc.isPullback_arrows
  set eO : bc.groupoid.objects.left ≅ Spec (.of (objectRingBaseChange G C')) :=
    hpbO.isoPullback ≪≫ objectsPullbackTensorIso G C' with heO
  set eA : bc.groupoid.arrows.left ≅ Spec (.of (arrowRingBaseChange G C')) :=
    hpbA.isoPullback ≪≫ arrowsPullbackTensorIso G C' with heA
  have hOproj : eO.hom ≫ objectsTensorProjection G C' = pO := by
    rw [heO, Iso.trans_hom, Category.assoc, objectsPullbackTensorIso_projection]
    exact hpbO.isoPullback_hom_fst
  have hAproj : eA.hom ≫ arrowsTensorProjection G C' = pA := by
    rw [heA, Iso.trans_hom, Category.assoc, arrowsPullbackTensorIso_projection]
    exact hpbA.isoPullback_hom_fst
  have hOover : eO.hom ≫ (objectSchemeBaseChange G C').hom = bc.groupoid.objects.hom := by
    rw [heO, Iso.trans_hom, Category.assoc, objectsPullbackTensorIso_over]
    exact hpbO.isoPullback_hom_snd
  have hAover : eA.hom ≫ (arrowSchemeBaseChange G C').hom = bc.groupoid.arrows.hom := by
    rw [heA, Iso.trans_hom, Category.assoc, arrowsPullbackTensorIso_over]
    exact hpbA.isoPullback_hom_snd
  have hOinvproj : eO.inv ≫ pO = objectsTensorProjection G C' := by rw [← hOproj]; simp
  have hOinvBase : eO.inv ≫ bc.groupoid.objects.hom = (objectSchemeBaseChange G C').hom := by
    rw [← hOover]; simp
  have tensorFormula (k' : bc.groupoid.arrows ⟶ bc.groupoid.objects) (k : G.arrows ⟶ G.objects)
      (φ : Γ(G.objects.left, ⊤) →ₐ[invariantRing G] Γ(G.arrows.left, ⊤))
      (hφ : φ.toRingHom = k.left.appTop.hom)
      (hk : pA ≫ k.left = k'.left ≫ pO) :
      k'.left = eA.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id (invariantRing G) C')).toRingHom) ≫ eO.inv := by
    set m : Spec (.of (arrowRingBaseChange G C')) ⟶ Spec (.of (objectRingBaseChange G C')) :=
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id (invariantRing G) C')).toRingHom) with hm
    have hmBase : m ≫ (objectSchemeBaseChange G C').hom =
        (arrowSchemeBaseChange G C').hom := by
      rw [hm]
      dsimp only [objectSchemeBaseChange, arrowSchemeBaseChange, Over.mk_hom]
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
    have hmLeft : m ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : Γ(G.objects.left, ⊤) →ₐ[invariantRing G]
            objectRingBaseChange G C').toRingHom) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : Γ(G.arrows.left, ⊤) →ₐ[invariantRing G]
            arrowRingBaseChange G C').toRingHom) ≫ Spec.map k.left.appTop := by
      rw [hm, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      simp [← hφ]
    have hmProj : m ≫ objectsTensorProjection G C' =
        arrowsTensorProjection G C' ≫ k.left := by
      dsimp only [objectsTensorProjection, arrowsTensorProjection]
      rw [← Category.assoc m, hmLeft]
      simp only [Category.assoc, Scheme.isoSpec_inv_naturality]
    refine hpbO.hom_ext ?_ ?_
    · calc
        k'.left ≫ pO = pA ≫ k.left := hk.symm
        _ = (eA.hom ≫ arrowsTensorProjection G C') ≫ k.left :=
          congrArg (fun z => z ≫ k.left) hAproj.symm
        _ = (eA.hom ≫ m ≫ eO.inv) ≫ pO := by
          simp only [Category.assoc, hOinvproj, hmProj]
    · calc
        k'.left ≫ bc.groupoid.objects.hom = bc.groupoid.arrows.hom := Over.w k'
        _ = (eA.hom ≫ m ≫ eO.inv) ≫ bc.groupoid.objects.hom := by
          simp only [Category.assoc, hOinvBase, hmBase, hAover]
  exact ⟨{
    groupoid := bc.groupoid
    objectsIso := eO
    arrowsIso := eA
    objectsIso_over := hOover
    arrowsIso_over := hAover
    objectsProjection := pO
    arrowsProjection := pA
    objects_isPullback := hpbO
    arrows_isPullback := hpbA
    projection_source := congrArg Over.Hom.left bc.projection.map_source
    projection_target := congrArg Over.Hom.left bc.projection.map_target
    projection_identity := congrArg Over.Hom.left bc.projection.map_identity
    projection_inverse := (congrArg Over.Hom.left bc.projection.map_inverse).symm
    composableProjection := bc.projection.composablesMap ≫ invariantBaseComposables G
    composableProjection_fst :=
      (Category.assoc _ _ _).trans
        ((congrArg (bc.projection.composablesMap ≫ ·) (invariantBaseComposables_fst G)).trans
          bc.projection.composablesMap_fst)
    composableProjection_snd :=
      (Category.assoc _ _ _).trans
        ((congrArg (bc.projection.composablesMap ≫ ·) (invariantBaseComposables_snd G)).trans
          bc.projection.composablesMap_snd)
    projection_comp := bc.projection.comp_left.trans (Category.assoc _ _ _).symm
    baseRingMap_invariant := fun x =>
      congrArg (fun k => k.hom x) (congrArg
        (fun k => (Scheme.ΓSpecIso (.of C')).inv ≫ Scheme.Hom.appTop k)
        ((Over.w bc.groupoid.source).trans (Over.w bc.groupoid.target).symm))
    source_eq := tensorFormula bc.groupoid.source G.source (sourceAlgHom G) rfl
      (congrArg Over.Hom.left bc.projection.map_source)
    target_eq := tensorFormula bc.groupoid.target G.target (targetAlgHom G) rfl
      (congrArg Over.Hom.left bc.projection.map_target)
    source_isFiniteLocallyFree :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback bc.source_isPullback
        (show IsFiniteLocallyFree G.source.left from inferInstance)
    target_isFiniteLocallyFree :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback bc.target_isPullback
        (show IsFiniteLocallyFree G.target.left from inferInstance)
  }⟩

end AlgebraicGeometry.GroupoidScheme

end

end
