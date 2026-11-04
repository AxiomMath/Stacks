module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongRefinement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical descent datum of a scheme over the base along a refinement

Let `𝒱 = {V j ⟶ S}` be a family of morphisms of schemes with fixed target and let
`𝒰 = {U i ⟶ S}` refine it along `α`. Pulling the canonical descent datum of a scheme `W` over
`S` relative to `𝒱` back along `α` gives the canonical descent datum of `W` relative to `𝒰`:
the component of the pullback at `i` is `(W ×_S V (α i)) ×_{V (α i)} U i`, the composite of the
two projections identifies it with `W ×_S U i`, and that identification is compatible with all
the gluing isomorphisms.

## Main definitions

* `AlgebraicGeometry.pullbackCompObjSchemeIso` and
  `AlgebraicGeometry.pullbackCompObjIso`: the identification of `(W ×_S Y) ×_Y X` with `W ×_S X`,
  as schemes and as schemes over `X`, for a factorization `X ⟶ Y ⟶ S` of the structure map
  of `X`.
* `AlgebraicGeometry.DescentData.toCanonicalDatum`: a morphism of descent data from `D` to the
  canonical descent datum of `W`, built from an identification of the components of `D` with the
  fibre products `W ×_S X i` which is compatible with the gluing isomorphisms.
* `AlgebraicGeometry.DescentData.isoCanonicalDatum`: the same when the identifications are
  isomorphisms.
* `AlgebraicGeometry.pulledBackCanonicalDatumIso`: the pullback along a refinement of the
  canonical descent datum of `W` is the canonical descent datum of `W`.
* `AlgebraicGeometry.pullbackFunctorCanonicalObjIso`: the same isomorphism phrased for the
  pullback functor on descent data.

## Main results

* `AlgebraicGeometry.DescentData.gluing_comm_inv`: the componentwise inverses of a morphism of
  descent data with isomorphism components are again compatible with the gluing isomorphisms.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_pullback_of_refinement`: a descent datum
  whose pullback along a refinement is effective is effective, assuming only that pullback along
  the refinement is fully faithful.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_fpqcRefinement`: the same with full
  faithfulness replaced by the fibrewise fpqc hypothesis which implies it.

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02VZ](https://stacks.math.columbia.edu/tag/02VZ)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

section Canonicity

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- Pushing a morphism of schemes over `X` forward to `S` and following it with the structure
map recovers the structure map. -/
private lemma map_comp_structureMap {X' S' : Scheme.{u}} (g : X' ⟶ S') {A B : Over X'}
    (m : A ⟶ B) : (Over.map g).map m ≫ structureMap g B = structureMap g A :=
  Over.OverMorphism.ext (Over.w m)

/-- The projection of the component at `i` of the canonical descent datum of `W` to `W`. -/
private abbrev datumProj (f : ∀ i, X i ⟶ S) (W : Over S) (i : ι) :
    ((CanonicalDatum.datum f W).obj i).left ⟶ W.left :=
  pullback.fst W.hom (f i)

/-- The gluing isomorphisms of the canonical descent datum of `W` preserve the projection
to `W`. -/
private lemma datum_gluingPullback_proj (f : ∀ i, X i ⟶ S) (W : Over S) (i j : ι) :
    ((CanonicalDatum.datum f W).gluingPullbackIso i j).hom ≫
        pullback.snd (f i) (pullback.snd W.hom (f j) ≫ f j) ≫ pullback.fst W.hom (f j) =
      pullback.fst (pullback.snd W.hom (f i) ≫ f i) (f j) ≫ pullback.fst W.hom (f i) := by
  simp only [DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Over.forget_map, Category.assoc]
  dsimp only [CanonicalDatum.datum]
  show _ ≫ _ ≫ (Over.prodLeftIsoPullback (Over.mk (f i))
      (CanonicalDatum.component W (f j))).hom ≫
    pullback.snd (Over.mk (f i)).hom (CanonicalDatum.component W (f j)).hom ≫ _ = _
  rw [Over.prodLeftIsoPullback_hom_snd_assoc]
  have h := congrArg Over.Hom.left (CanonicalDatum.transition_original W (f i) (f j))
  simp only [Over.comp_left] at h
  show _ ≫ (CanonicalDatum.transition W (f i) (f j)).left ≫
    (prod.snd : Over.mk (f i) ⨯ CanonicalDatum.component W (f j) ⟶ _).left ≫
    (CanonicalDatum.originalProjection W (f j)).left = _
  rw [h]
  exact Over.prodLeftIsoPullback_inv_fst_assoc _ _ _

/-- The gluing isomorphisms of the canonical descent datum of `W` preserve the projection
`datumProj` to `W`. -/
private lemma datum_gluingPullback_projComponent (f : ∀ i, X i ⟶ S) (W : Over S) (i j : ι) :
    ((CanonicalDatum.datum f W).gluingPullbackIso i j).hom ≫
        pullback.snd (f i) (((CanonicalDatum.datum f W).obj j).hom ≫ f j) ≫
        datumProj f W j =
      pullback.fst (((CanonicalDatum.datum f W).obj i).hom ≫ f i) (f j) ≫ datumProj f W i :=
  datum_gluingPullback_proj f W i j

/-- Compatibility of an identification of the components of a descent datum with the fibre
products `W ×_S X i`, read on products in `Over S` rather than on the literal fibre
products. -/
private lemma gluing_comp_originalProjection (D : DescentData f) (W : Over S)
    (e : ∀ i, D.obj i ⟶ (Over.pullback (f i)).obj W) (i j : ι)
    (he : (D.gluingPullbackIso i j).hom ≫
        pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ (e j).left ≫ pullback.fst W.hom (f j) =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ (e i).left ≫ pullback.fst W.hom (f i)) :
    (D.gluing i j).hom.left ≫ prod.snd ≫ (Over.map (f j)).map (e j) ≫
        CanonicalDatum.originalProjection W (f j) =
      prod.fst ≫ (Over.map (f i)).map (e i) ≫ CanonicalDatum.originalProjection W (f i) := by
  apply Over.OverMorphism.ext
  have hsnd := Over.prodLeftIsoPullback_hom_snd (Over.mk (f i))
    ((Over.map (f j)).obj (D.obj j))
  change (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.snd (f i) ((D.obj j).hom ≫ f j) =
    (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left at hsnd
  have hfst := Over.prodLeftIsoPullback_hom_fst ((Over.map (f i)).obj (D.obj i))
    (Over.mk (f j))
  change (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).hom ≫
      pullback.fst ((D.obj i).hom ≫ f i) (f j) =
    (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left at hfst
  have key := congrArg (fun q ↦ (Over.prodLeftIsoPullback
    ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).hom ≫ q) he
  simp only [DescentData.gluingPullbackIso, DescentData.gluingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map, Category.assoc, Iso.hom_inv_id_assoc] at key
  rw [reassoc_of% hsnd, reassoc_of% hfst] at key
  simpa only [Over.comp_left, Over.map_map_left, CanonicalDatum.originalProjection,
    Over.homMk_left] using key

/-- A descent datum whose components are identified with the fibre products `W ×_S X i`
compatibly with the gluing isomorphisms maps to the canonical descent datum of `W`. The
compatibility hypothesis says that the gluing isomorphisms preserve the projection to `W`. -/
def DescentData.toCanonicalDatum (D : DescentData f) (W : Over S)
    (e : ∀ i, D.obj i ⟶ (Over.pullback (f i)).obj W)
    (he : ∀ i j, (D.gluingPullbackIso i j).hom ≫
        pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ (e j).left ≫ pullback.fst W.hom (f j) =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ (e i).left ≫ pullback.fst W.hom (f i)) :
    D ⟶ CanonicalDatum.datum f W where
  hom := e
  comm i j := by
    change prod.map ((Over.map (f i)).map (e i)) (𝟙 (Over.mk (f j))) ≫
        CanonicalDatum.transition W (f i) (f j) =
      (D.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j))
    apply prod.hom_ext
    · simp only [Category.assoc, CanonicalDatum.transition_fst, prod.map_fst_assoc,
        prod.map_fst, Category.comp_id]
      rw [DescentData.gluing_hom_fst, map_comp_structureMap]
    · apply CanonicalDatum.component_hom_ext
      · simp only [Category.assoc, CanonicalDatum.transition_original, prod.map_fst_assoc,
          prod.map_snd_assoc]
        exact (gluing_comp_originalProjection D W e i j (he i j)).symm
      · simp only [Category.assoc, CanonicalDatum.transition_structure, prod.map_snd,
          Category.comp_id]
        rw [map_comp_structureMap, DescentData.gluing_hom_snd_structureMap]

/-- The componentwise inverses of a morphism of descent data whose components are isomorphisms
are again compatible with the gluing isomorphisms. -/
@[sga "3 IV 2.4" "(a), special case"]
lemma DescentData.gluing_comm_inv {D E : DescentData f} (φ : D ⟶ E)
    (e : ∀ i, D.obj i ≅ E.obj i) (hφ : ∀ i, φ.hom i = (e i).hom) (i j : ι) :
    prod.map ((Over.map (f i)).map (e i).inv) (𝟙 (Over.mk (f j))) ≫
        (D.gluing i j).hom.left =
      (E.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j).inv) := by
  have hcomm := φ.comm i j
  simp only [hφ] at hcomm
  rw [← cancel_mono (prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j).hom)),
    Category.assoc, Category.assoc, ← hcomm]
  simp
 
/-- A descent datum whose components are isomorphic to the fibre products `W ×_S X i`
compatibly with the gluing isomorphisms *is* the canonical descent datum of `W`. -/
def DescentData.isoCanonicalDatum (D : DescentData f) (W : Over S)
    (e : ∀ i, D.obj i ≅ (Over.pullback (f i)).obj W)
    (he : ∀ i j, (D.gluingPullbackIso i j).hom ≫
        pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ (e j).hom.left ≫
          pullback.fst W.hom (f j) =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ (e i).hom.left ≫
        pullback.fst W.hom (f i)) :
    D ≅ CanonicalDatum.datum f W where
  hom := D.toCanonicalDatum W (fun i ↦ (e i).hom) he
  inv :=
    { hom := fun i ↦ (e i).inv
      comm := DescentData.gluing_comm_inv (D.toCanonicalDatum W (fun i ↦ (e i).hom) he) e
        fun _ ↦ rfl }
  hom_inv_id := DescentData.hom_ext fun i ↦ (e i).hom_inv_id
  inv_hom_id := DescentData.hom_ext fun i ↦ (e i).inv_hom_id

end Canonicity

section PullbackComp

variable {S : Scheme.{u}}

/-- `(W ×_S Y) ×_Y X` is `W ×_S X` when `a ≫ g = b` factors the structure map of `X`. -/
def pullbackCompObjSchemeIso (W : Over S) {X Y : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S)
    (b : X ⟶ S) (hw : a ≫ g = b) :
    pullback (pullback.snd W.hom g) a ≅ pullback W.hom b :=
  pullbackLeftPullbackSndIso W.hom g a ≪≫ pullback.congrHom rfl hw

/-- The identification of `(W ×_S Y) ×_Y X` with `W ×_S X` sends the composite of the two
projections to `W` to the projection to `W`. -/
lemma pullbackCompObjSchemeIso_hom_fst (W : Over S) {X Y : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S)
    (b : X ⟶ S) (hw : a ≫ g = b) :
    (pullbackCompObjSchemeIso W a g b hw).hom ≫ pullback.fst W.hom b =
      pullback.fst (pullback.snd W.hom g) a ≫ pullback.fst W.hom g := by
  simp [pullbackCompObjSchemeIso, pullback.congrHom, pullback.lift_fst]

/-- The identification of `(W ×_S Y) ×_Y X` with `W ×_S X` preserves the projection to `X`. -/
lemma pullbackCompObjSchemeIso_hom_snd (W : Over S) {X Y : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S)
    (b : X ⟶ S) (hw : a ≫ g = b) :
    (pullbackCompObjSchemeIso W a g b hw).hom ≫ pullback.snd W.hom b =
      pullback.snd (pullback.snd W.hom g) a := by
  simp [pullbackCompObjSchemeIso, pullback.congrHom, pullback.lift_snd]

/-- The identification of `(W ×_S Y) ×_Y X` with `W ×_S X` as schemes over `X`. -/
def pullbackCompObjIso (W : Over S) {X Y : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S)
    (b : X ⟶ S) (hw : a ≫ g = b) :
    (Over.pullback a).obj ((Over.pullback g).obj W) ≅ (Over.pullback b).obj W :=
  Over.isoMk (pullbackCompObjSchemeIso W a g b hw) (pullbackCompObjSchemeIso_hom_snd W a g b hw)

/-- The identification of `(W ×_S Y) ×_Y X` with `W ×_S X` preserves the projection to `W`. -/
lemma pullbackCompObjIso_hom_left_fst (W : Over S) {X Y : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S)
    (b : X ⟶ S) (hw : a ≫ g = b) :
    (pullbackCompObjIso W a g b hw).hom.left ≫ pullback.fst W.hom b =
      pullback.fst (pullback.snd W.hom g) a ≫ pullback.fst W.hom g :=
  pullbackCompObjSchemeIso_hom_fst W a g b hw

end PullbackComp

section Refinement

open MorphismOfSchemeFamilies

variable {S : Scheme.{u}} {U V : PreZeroHypercover.{u} S}

/-- The component at `i` of the pullback along a refinement `α` of the canonical descent datum
of `W`, identified with the fibre product `W ×_S U i`. -/
def refinementCanonicalObjIso (α : U.HomOver V (𝟙 S)) (W : Over S) (i : U.I₀) :
    (pulledBackDatum (ofRefinement α) (CanonicalDatum.datum V.f W)).obj i ≅
      (Over.pullback (U.f i)).obj W :=
  pullbackCompObjIso W (α.h₀ i) (V.f (α.s₀ i)) (U.f i) ((α.w₀ i).trans (Category.comp_id _))

/-- The identification of the components preserves the projection to `W`. -/
private lemma refinementCanonicalObjIso_hom_left_fst (α : U.HomOver V (𝟙 S)) (W : Over S)
    (i : U.I₀) :
    (refinementCanonicalObjIso α W i).hom.left ≫ pullback.fst W.hom (U.f i) =
      (pulledBackDatumObjIso (ofRefinement α) (CanonicalDatum.datum V.f W) i).hom.left ≫
        pullback.fst ((CanonicalDatum.datum V.f W).obj (α.s₀ i)).hom (α.h₀ i) ≫
        datumProj V.f W (α.s₀ i) :=
  (pullbackCompObjIso_hom_left_fst W (α.h₀ i) (V.f (α.s₀ i)) (U.f i)
    ((α.w₀ i).trans (Category.comp_id _))).trans (Category.id_comp _).symm

/-- The characterization of the gluing isomorphisms of a pulled-back descent datum, with the
index map of a refinement spelled out. -/
private lemma pulledBackDatum_gluing_refinement (α : U.HomOver V (𝟙 S)) (D : DescentData V.f)
    (i j : U.I₀) :
    ((pulledBackDatum (ofRefinement α) D).gluingPullbackIso i j).hom ≫
        pulledBackDatumTargetMap (ofRefinement α) D i j =
      pulledBackDatumSourceMap (ofRefinement α) D i j ≫
        (D.gluingPullbackIso (α.s₀ i) (α.s₀ j)).hom :=
  pulledBackDatum_gluing (ofRefinement α) D i j

/-- The second projection of the comparison map on the targets of the gluing isomorphisms of a
pulled-back descent datum along a refinement. -/
private lemma targetMap_snd_refinement (α : U.HomOver V (𝟙 S)) (D : DescentData V.f)
    (i j : U.I₀) :
    pulledBackDatumTargetMap (ofRefinement α) D i j ≫
        pullback.snd (V.f (α.s₀ i)) ((D.obj (α.s₀ j)).hom ≫ V.f (α.s₀ j)) =
      pullback.snd (U.f i) (((pulledBackDatum (ofRefinement α) D).obj j).hom ≫ U.f j) ≫
        (pulledBackDatumObjIso (ofRefinement α) D j).hom.left ≫
        pullback.fst (D.obj (α.s₀ j)).hom (α.h₀ j) :=
  pullback.lift_snd _ _ _

/-- The first projection of the comparison map on the sources of the gluing isomorphisms of a
pulled-back descent datum along a refinement. -/
private lemma sourceMap_fst_refinement (α : U.HomOver V (𝟙 S)) (D : DescentData V.f)
    (i j : U.I₀) :
    pulledBackDatumSourceMap (ofRefinement α) D i j ≫
        pullback.fst ((D.obj (α.s₀ i)).hom ≫ V.f (α.s₀ i)) (V.f (α.s₀ j)) =
      pullback.fst (((pulledBackDatum (ofRefinement α) D).obj i).hom ≫ U.f i) (U.f j) ≫
        (pulledBackDatumObjIso (ofRefinement α) D i).hom.left ≫
        pullback.fst (D.obj (α.s₀ i)).hom (α.h₀ i) :=
  pullback.lift_fst _ _ _

/-- The gluing isomorphisms of the pullback along a refinement of the canonical descent datum of
`W` preserve the projection to `W`. -/
lemma refinementCanonicalObjIso_gluing (α : U.HomOver V (𝟙 S)) (W : Over S) (i j : U.I₀) :
    ((pulledBackDatum (ofRefinement α)
          (CanonicalDatum.datum V.f W)).gluingPullbackIso i j).hom ≫
        pullback.snd (U.f i)
          (((pulledBackDatum (ofRefinement α)
            (CanonicalDatum.datum V.f W)).obj j).hom ≫ U.f j) ≫
        (refinementCanonicalObjIso α W j).hom.left ≫ pullback.fst W.hom (U.f j) =
      pullback.fst (((pulledBackDatum (ofRefinement α)
          (CanonicalDatum.datum V.f W)).obj i).hom ≫ U.f i) (U.f j) ≫
        (refinementCanonicalObjIso α W i).hom.left ≫ pullback.fst W.hom (U.f i) := by
  have key := congrArg (fun q ↦ q ≫
      pullback.snd (V.f (α.s₀ i))
        (((CanonicalDatum.datum V.f W).obj (α.s₀ j)).hom ≫ V.f (α.s₀ j)) ≫
      datumProj V.f W (α.s₀ j))
    (pulledBackDatum_gluing_refinement α (CanonicalDatum.datum V.f W) i j)
  simp only [Category.assoc,
    reassoc_of% (targetMap_snd_refinement α (CanonicalDatum.datum V.f W) i j),
    datum_gluingPullback_projComponent V.f W (α.s₀ i) (α.s₀ j),
    reassoc_of% (sourceMap_fst_refinement α (CanonicalDatum.datum V.f W) i j)] at key
  simpa only [refinementCanonicalObjIso_hom_left_fst, Category.assoc] using key

/-- **The canonical descent datum pulls back to the canonical descent datum.** The pullback
along a refinement `α` of `𝒱` by `𝒰` of the canonical descent datum of `W` relative to `𝒱` is
the canonical descent datum of `W` relative to `𝒰`. -/
def pulledBackCanonicalDatumIso (α : U.HomOver V (𝟙 S)) (W : Over S) :
    pulledBackDatum (ofRefinement α)
        ((canonicalFamilyDescentFunctor V.f).functor.obj W) ≅
      (canonicalFamilyDescentFunctor U.f).functor.obj W :=
  DescentData.isoCanonicalDatum _ W (refinementCanonicalObjIso α W)
    (refinementCanonicalObjIso_gluing α W)

/-- The pullback functor on descent data along a refinement `α` carries the canonical descent
datum of `W` to the canonical descent datum of `W`. -/
def pullbackFunctorCanonicalObjIso (α : U.HomOver V (𝟙 S)) (W : Over S) :
    (pullbackFunctor (ofRefinement α)).functor.obj
        ((canonicalFamilyDescentFunctor V.f).functor.obj W) ≅
      (canonicalFamilyDescentFunctor U.f).functor.obj W :=
  eqToIso ((pullbackFunctor (ofRefinement α)).obj_eq _) ≪≫ pulledBackCanonicalDatumIso α W

namespace DescentData

/-- **Effectivity descends along a refinement.** Let the family `U` refine the family `V` by
`α` and suppose that pulling descent data back along `α` is fully faithful. Then a descent datum
relative to `V` whose pullback along `α` is effective is itself effective. -/
theorem isFamilyEffective_of_pullback_of_refinement (α : U.HomOver V (𝟙 S))
    (hff : (MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRefinement α)).functor.FullyFaithful)
    {D : DescentData V.f}
    (h : ((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRefinement α)).functor.obj D).IsFamilyEffective) :
    D.IsFamilyEffective := by
  obtain ⟨W, ⟨e⟩⟩ := h
  exact ⟨W, ⟨hff.preimageIso (pullbackFunctorCanonicalObjIso α W ≪≫ e)⟩⟩

/-- **Effectivity descends along an fpqc refinement.** Let the family `U` refine the family `V`
by `α` so that the members of `U` lying above each member of `V` form an fpqc covering of it.
Then a descent datum relative to `V` whose pullback along `α` is effective is itself
effective. -/
theorem isFamilyEffective_of_fpqcRefinement (α : U.HomOver V (𝟙 S))
    (hfpqc : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.fpqcPrecoverage (V.X j))
    {D : DescentData V.f}
    (h : ((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRefinement α)).functor.obj D).IsFamilyEffective) :
    D.IsFamilyEffective :=
  have ⟨hff⟩ := pullbackFunctor_fullyFaithful_of_fpqcRefinement U V α hfpqc
  isFamilyEffective_of_pullback_of_refinement α hff h

end DescentData

end Refinement

end AlgebraicGeometry

end

end
