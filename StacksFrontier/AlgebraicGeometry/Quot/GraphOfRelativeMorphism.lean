module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

/-!
# Relative morphisms as points of a Hilbert functor (Stacks 0D1A)

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site. A relative morphism from `Z` to `X` over `Q` at a test scheme `T` is a pair `(a, b)`
consisting of a morphism `a : T ⟶ Q` and a morphism `b : Z_T ⟶ X` over `Q` (Stacks 05Y1). Such a
pair has a *graph*: the subspace of `(Z ×_Q X)_T` cut out by the map `Z_T ⟶ (Z ×_Q X)_T` with
components the projection and `b`.

When `x` is separated the graph is a closed subspace, and when `z` is of finite presentation, flat
and proper the graph is of finite presentation, flat and proper over `T`, so the graph is a point
of the Hilbert functor of `Z ×_Q X` over `Q`. The graph of a restriction of `(a, b)` along a
morphism `T' ⟶ T` is the inverse image of the graph of `(a, b)`, so these points assemble into a
transformation of presheaves

```text
Mor_Q(Z, X) ⟶ Hilb_{Z ×_Q X / Q},
```

and that transformation is injective at every test scheme. That is Stacks 0D1A.

## Main definitions

* `AlgebraicGeometry.Space.graphAmbient` is the algebraic space `Z ×_Q X` and
  `AlgebraicGeometry.Space.graphAmbientMap` its structure morphism to `Q`.
* `AlgebraicGeometry.Space.graphMap` is the graph of a relative morphism, as a map from the base
  change of `Z` into the base change of `Z ×_Q X`.
* `AlgebraicGeometry.Space.graphHilbertFamily` is the graph read as a point of the Hilbert functor
  of `AlgebraicGeometry.Space.hilbertFunctor`.
* `AlgebraicGeometry.Space.graphTransformation`: **Stacks 0D1A**, the graph transformation itself.

## Main results

* `AlgebraicGeometry.Space.graphMap_mono`: the graph is a monomorphism.
* `AlgebraicGeometry.Space.graphMap_isClosedImmersion`: the graph of a relative morphism is a
  closed immersion when `x` is separated.
* `AlgebraicGeometry.Space.isClosedSubspace_range_graphMap`: its range is therefore a closed
  subspace of the base change of `Z ×_Q X`.
* `AlgebraicGeometry.Space.property_range_graphMap_comp_snd`: any property of morphisms of
  algebraic spaces which is stable under base change and holds for `z` holds for the projection of
  that range to the test scheme.
* `AlgebraicGeometry.Space.isPullback_graphMap_restrict` and
  `AlgebraicGeometry.Space.range_graphMap_restrict`: the graph of a restriction is the base change,
  equivalently the inverse image, of the graph. This is the naturality of the graph.
* `AlgebraicGeometry.Space.graphTransformation_app_family_Z`: **Stacks 0D1A**, the transformation
  carries a relative morphism to its graph.
* `AlgebraicGeometry.Space.graphTransformation_injective`: **Stacks 0D1A**, the transformation is
  injective at every test scheme.
* `AlgebraicGeometry.Space.relativeMorphism_eq_of_range_graphMap_eq`: what injectivity rests on, a
  relative morphism is determined by its base and its graph.

## Implementation notes

The graph of `(a, b)` is the map `Z_T ⟶ (Z ×_Q X)_T = (Z ×_Q X) ×_Q T` whose first component is
`(pr, b) : Z_T ⟶ Z ×_Q X` and whose second is the projection `Z_T ⟶ T`. Everything below is
written with the structure morphism of `Z ×_Q X` spelled out as `pr_Z ≫ z` rather than through the
projection of `AlgebraicGeometry.Space.graphAmbientMap`, so that no definitional unfolding of the
full-subcategory morphism is needed anywhere; the two are the same morphism, which is
`AlgebraicGeometry.Space.graphAmbientMap_hom`.

Closedness of the graph is the usual factorization through a diagonal: the graph is the composite
of the isomorphism `Z_T ≅ Z_T ×_X X` with the base change
`CategoryTheory.Limits.pullback.mapDesc` of `b` and `𝟙 X` along `x`, which is a closed immersion
exactly when `x` is separated (Stacks 03KN), followed by the canonical rebracketing of iterated
fibre products.

Naturality is proved as the *cartesianness* of the square comparing the two graph maps, rather
than by computing the two subspaces separately: `Z_{T'}` is the base change of `Z_T` and
`(Z ×_Q X)_{T'}` is the base change of `(Z ×_Q X)_T`, and both graph maps commute with the
projections to the test schemes, so the comparison square is the left half of the first cartesian
square cut by the second. The equality of the graph with the inverse image of the graph is then
`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback`. Because the inverse image of
`CategoryTheory.Subfunctor.preimage` is what the Hilbert functor restricts along *on the nose*,
this makes `AlgebraicGeometry.Space.graphTransformation` an honest natural transformation rather
than one that exists only up to a bijection.

Injectivity uses that every graph map is a *section* of one retraction of `(Z ×_Q X)_T` onto `Z_T`,
namely the projection to `Z` of the ambient fibre product paired with the projection to `T`. The
retraction does not depend on the relative morphism, so two graph maps over the same base with the
same range agree pointwise by
`CategoryTheory.Subfunctor.eq_of_range_eq_of_comp_eq_id`, and reading off the component in `X`
identifies the two morphisms.

## References

* [Stacks Project, Tag 0D1A](https://stacks.math.columbia.edu/tag/0D1A)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- The base `Q` of the graph construction, as an object of the category of algebraic spaces over
`S`. -/
abbrev graphBase : AlgebraicSpaces B S hS := ⟨Q, hQ⟩

/-- The ambient algebraic space `Z ×_Q X` of the graph construction. -/
abbrev graphAmbient : AlgebraicSpaces B S hS :=
  ⟨pullback z x, isAlgebraicSpace_pullback B S hS z x hZ hX hQ⟩

/-- The structure morphism `Z ×_Q X ⟶ Q` of the ambient space of the graph construction, as a
morphism of algebraic spaces over `S`. -/
def graphAmbientMap : graphAmbient B S hS z x hZ hX hQ ⟶ graphBase B S hS hQ :=
  ObjectProperty.homMk (pullback.fst z x ≫ z)

/-- The underlying morphism of `AlgebraicGeometry.Space.graphAmbientMap` is `pr_Z ≫ z`. -/
@[simp]
theorem graphAmbientMap_hom :
    (graphAmbientMap B S hS z x hZ hX hQ).hom = pullback.fst z x ≫ z := rfl

variable {B S hS z x}

/-- The *graph* of a relative morphism `(a, b)` at a test scheme `T`: the map from the base change
`Z_T` into the base change of `Z ×_Q X` whose first component is `(pr, b)` and whose second is the
projection to `T`. -/
def graphMap {T : BigFppfOver B S hS} (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    pullback p.base z ⟶ pullback (pullback.fst z x ≫ z) p.base :=
  pullback.lift (pullback.lift (pullback.snd p.base z) p.morphism p.commutes.symm)
    (pullback.fst p.base z) (by
      rw [← Category.assoc, pullback.lift_fst]
      exact (pullback.condition (f := p.base) (g := z)).symm)

/-- The second component of the graph map is the projection `Z_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem graphMap_snd {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    graphMap p ≫ pullback.snd (pullback.fst z x ≫ z) p.base = pullback.fst p.base z :=
  pullback.lift_snd _ _ _

/-- The component in `Z` of the graph map is the projection `Z_T ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem graphMap_fst_fst {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    graphMap p ≫ pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.fst z x =
      pullback.snd p.base z := by
  rw [graphMap, pullback.lift_fst_assoc, pullback.lift_fst]

/-- The component in `X` of the graph map is the morphism `b : Z_T ⟶ X` of the relative
morphism. -/
@[reassoc (attr := simp)]
theorem graphMap_fst_snd {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    graphMap p ≫ pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.snd z x = p.morphism := by
  rw [graphMap, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The graph of a relative morphism is a monomorphism: it is a section of the projection to the
base change of `Z`. -/
instance graphMap_mono {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) : Mono (graphMap p) := by
  refine ⟨fun {W} a b hab => ?_⟩
  apply pullback.hom_ext
  · calc a ≫ pullback.fst p.base z
        = (a ≫ graphMap p) ≫ pullback.snd (pullback.fst z x ≫ z) p.base := by simp
      _ = (b ≫ graphMap p) ≫ pullback.snd (pullback.fst z x ≫ z) p.base := by rw [hab]
      _ = b ≫ pullback.fst p.base z := by simp
  · calc a ≫ pullback.snd p.base z
        = (a ≫ graphMap p) ≫
            pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.fst z x := by simp
      _ = (b ≫ graphMap p) ≫
            pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.fst z x := by rw [hab]
      _ = b ≫ pullback.snd p.base z := by simp

/-- The graph of a relative morphism is a closed immersion as soon as `x` is
separated: it factors as an isomorphism followed by the base change along `x` of the pair
`(b, 𝟙 X)`, which is a closed immersion by Stacks 03KN, followed by the canonical rebracketing of
iterated fibre products. -/
theorem graphMap_isClosedImmersion {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) (hsep : IsSeparated B S hS x) :
    IsClosedImmersion B S hS (graphMap p) := by
  let α : pullback p.base z ⟶ pullback p.morphism (𝟙 X) :=
    pullback.lift (𝟙 _) p.morphism (by simp)
  let eSource : pullback p.base z ≅ pullback p.morphism (𝟙 X) :=
    Iso.mk α (pullback.fst p.morphism (𝟙 X)) (by simp [α]) (by
      apply pullback.hom_ext
      · simp [α]
      · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
        exact pullback.condition)
  let eTarget : pullback (p.morphism ≫ x) (𝟙 X ≫ x) ≅ pullback (pullback.fst z x ≫ z) p.base :=
    pullback.congrHom p.commutes (Category.id_comp x) ≪≫ pullbackAssoc p.base z z x ≪≫
      pullbackSymmetry p.base (pullback.fst z x ≫ z)
  let d := pullback.mapDesc p.morphism (𝟙 X) x
  have hfactor : α ≫ d ≫ eTarget.hom = graphMap p := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · conv_rhs => rw [Category.assoc, graphMap_fst_fst p]
        simp [α, d, eTarget, pullbackAssoc_hom_snd_fst]
      · conv_rhs => rw [Category.assoc, graphMap_fst_snd p]
        simp [α, d, eTarget, pullbackAssoc_hom_snd_snd]
    · rw [graphMap_snd p]
      simp [α, d, eTarget]
  have hd : IsClosedImmersion B S hS d := isClosedImmersion_mapDesc B S hS p.morphism (𝟙 X) x hsep
  have hde : IsClosedImmersion B S hS (d ≫ eTarget.hom) :=
    MorphismProperty.RespectsIso.postcomp _ eTarget.hom d hd
  have hα : IsIso α := eSource.isIso_hom
  rw [← hfactor]
  exact MorphismProperty.RespectsIso.precomp _ α (d ≫ eTarget.hom) hde

/-- The base change `Z_T` of `z` along the base of a relative morphism is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_base {T : BigFppfOver B S hS}
    (hZ : IsAlgebraicSpace B S hS Z) (hQ : IsAlgebraicSpace B S hS Q)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    IsAlgebraicSpace B S hS (pullback p.base z) :=
  isAlgebraicSpace_pullback B S hS p.base z (isAlgebraicSpace_yoneda B S hS T) hZ hQ

/-- The range of the graph map of a relative morphism is an algebraic space: the graph map is a
monomorphism, so its range is isomorphic to the base change `Z_T`. -/
theorem isAlgebraicSpace_range_graphMap {T : BigFppfOver B S hS}
    (hZ : IsAlgebraicSpace B S hS Z) (hQ : IsAlgebraicSpace B S hS Q)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    IsAlgebraicSpace B S hS (Subfunctor.range (graphMap p)).toFunctor :=
  isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange (graphMap p)))
    (isAlgebraicSpace_pullback_base hZ hQ p)

/-- The range of the graph map of a relative morphism is a closed subspace of the
base change of `Z ×_Q X`, as soon as `x` is separated. -/
theorem isClosedSubspace_range_graphMap {T : BigFppfOver B S hS}
    (hZ : IsAlgebraicSpace B S hS Z) (hQ : IsAlgebraicSpace B S hS Q)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) (hsep : IsSeparated B S hS x) :
    IsClosedSubspace B S hS (Subfunctor.range (graphMap p)) := by
  refine ⟨isAlgebraicSpace_range_graphMap hZ hQ p, ?_⟩
  have hPci : MorphismProperty.RespectsIso
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) := inferInstance
  have h := MorphismProperty.RespectsIso.precomp _
    (asIso (Subfunctor.toRange (graphMap p))).inv (graphMap p)
    (graphMap_isClosedImmersion p hsep)
  rwa [inv_toRange_comp (graphMap p)] at h

/-- Any property of morphisms of algebraic spaces stable under base change which holds for `z`
holds for the projection of the range of a graph map to its test scheme: that projection is, up to
the isomorphism onto the range, the base change `Z_T ⟶ T` of `z`. -/
theorem property_range_graphMap_comp_snd {T : BigFppfOver B S hS}
    (hZ : IsAlgebraicSpace B S hS Z) (hQ : IsAlgebraicSpace B S hS Q)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T))
    {P : MorphismProperty (AlgebraicSpaces B S hS)} (hP : P.IsStableUnderBaseChange)
    (hz : P (ObjectProperty.homMk z :
      (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ graphBase B S hS hQ)) :
    P (ObjectProperty.homMk
        ((Subfunctor.range (graphMap p)).ι ≫ pullback.snd (pullback.fst z x ≫ z) p.base) :
      (⟨_, isAlgebraicSpace_range_graphMap hZ hQ p⟩ : AlgebraicSpaces B S hS) ⟶
        schemeSpace T) := by
  let Psp : AlgebraicSpaces B S hS := ⟨pullback p.base z, isAlgebraicSpace_pullback_base hZ hQ p⟩
  let Rsp : AlgebraicSpaces B S hS := ⟨_, isAlgebraicSpace_range_graphMap hZ hQ p⟩
  let Tsp : AlgebraicSpaces B S hS := schemeSpace T
  let eSp : Psp ≅ Rsp := ObjectProperty.isoMk _ (asIso (Subfunctor.toRange (graphMap p)))
  let rToT : Rsp ⟶ Tsp := ObjectProperty.homMk
    ((Subfunctor.range (graphMap p)).ι ≫ pullback.snd (pullback.fst z x ≫ z) p.base)
  have hcomp : eSp.hom ≫ rToT = (ObjectProperty.homMk (pullback.fst p.base z) : Psp ⟶ Tsp) := by
    apply ObjectProperty.hom_ext
    change Subfunctor.toRange (graphMap p) ≫ (Subfunctor.range (graphMap p)).ι ≫
      pullback.snd (pullback.fst z x ≫ z) p.base = pullback.fst p.base z
    rw [← Category.assoc, Subfunctor.toRange_ι, graphMap_snd]
  have sq : IsPullback (ObjectProperty.homMk (pullback.snd p.base z) :
        Psp ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (pullback.fst p.base z) : Psp ⟶ Tsp)
      (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ graphBase B S hS hQ)
      (ObjectProperty.homMk p.base : Tsp ⟶ graphBase B S hS hQ) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (IsPullback.of_hasPullback p.base z).flip
  have h : P (eSp.hom ≫ rToT) := by
    rw [hcomp]
    exact hP.of_isPullback sq hz
  simpa using MorphismProperty.RespectsIso.precomp P eSp.inv (eSp.hom ≫ rToT) h

/-- The graph of a relative morphism `(a, b)` at a test scheme `T`, as a point of
the Hilbert functor of `Z ×_Q X` over `Q`: the range of the graph map is a closed subspace of
`(Z ×_Q X)_T` which is of finite presentation, flat and proper over `T`, because it is isomorphic
over `T` to the base change `Z_T` of `z`. -/
def graphHilbertFamily {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z) :
    HilbertFamily (graphAmbientMap B S hS z x hZ hX hQ) (CostructuredArrow.mk p.base) where
  Z := Subfunctor.range (graphMap p)
  closed := isClosedSubspace_range_graphMap hZ hQ p hsep
  finitePresentation := property_range_graphMap_comp_snd hZ hQ p
    (isFinitePresentation_isStableUnderBaseChange B S hS) hfp
  flat := property_range_graphMap_comp_snd hZ hQ p (isFlat_isStableUnderBaseChange B S hS) hflat
  proper := property_range_graphMap_comp_snd hZ hQ p (isProper_isStableUnderBaseChange B S hS)
    hproper

/-- The closed subspace underlying the graph of a relative morphism is the range of its graph
map. -/
@[simp]
theorem graphHilbertFamily_Z {T : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z) :
    (graphHilbertFamily hZ hX hQ p hsep hfp hflat hproper).Z = Subfunctor.range (graphMap p) :=
  rfl

/-- The comparison of the two base changes of the ambient space `Z ×_Q X` along `T' ⟶ T` is the
canonical comparison map of fibre products. -/
theorem schemeBaseChangeMap_graphAmbientMap {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (a : yoneda.obj T ⟶ Q) :
    schemeBaseChangeMap (graphAmbientMap B S hS z x hZ hX hQ) (HilbertFamilyOver.restrict g a) =
      pullback.mapSnd (yoneda.map g) (pullback.fst z x ≫ z) a :=
  pullback.hom_ext ((schemeBaseChangeMap_fst _ _).trans (pullback.mapSnd_fst _ _ _).symm)
    ((schemeBaseChangeMap_snd _ _).trans (pullback.mapSnd_snd _ _ _).symm)

/-- The graph of a relative morphism whose base is presented as a composite `T' ⟶ T ⟶ Q`, and
whose morphism is the base change of the morphism of a pair over `T`, is the base change of the
graph of that pair: the comparison square is cartesian. Both graph maps commute with the
projections to the test schemes, so this is the left half of the cartesian square exhibiting
`Z_{T'}` as the base change of `Z_T`, cut by the cartesian square exhibiting `(Z ×_Q X)_{T'}` as
the base change of `(Z ×_Q X)_T`. -/
theorem isPullback_graphMap_comp_base {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T))
    (m : pullback (yoneda.map g ≫ p.base) z ⟶ X)
    (hm : m ≫ x = pullback.snd (yoneda.map g ≫ p.base) z ≫ z)
    (hmor : m = pullback.mapFst (yoneda.map g) p.base z ≫ p.morphism) :
    IsPullback (graphMap (⟨yoneda.map g ≫ p.base, m, hm⟩ :
          RelativeMorphism B S hS Z X Q z x (yoneda.obj T')))
      (pullback.mapFst (yoneda.map g) p.base z)
      (pullback.mapSnd (yoneda.map g) (pullback.fst z x ≫ z) p.base)
      (graphMap p) := by
  refine IsPullback.of_right ?_ ?_
    (pullback.isPullback_mapSnd (yoneda.map g) (pullback.fst z x ≫ z) p.base)
  · rw [graphMap_snd, graphMap_snd]
    exact pullback.isPullback_mapFst (yoneda.map g) p.base z
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.mapSnd_fst, graphMap_fst_fst, pullback.mapFst_snd]
        exact graphMap_fst_fst _
      · simp only [Category.assoc, pullback.mapSnd_fst, graphMap_fst_snd]
        rw [graphMap_fst_snd]
        exact hmor
    · simp only [Category.assoc, pullback.mapSnd_snd, graphMap_snd, pullback.mapFst_fst]
      rw [← Category.assoc, graphMap_snd]

/-- The square comparing the graph of a relative morphism with the graph of its restriction along
`T' ⟶ T` is cartesian. -/
theorem isPullback_graphMap_restrict {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    IsPullback (graphMap (RelativeMorphism.restrict (yoneda.map g) p))
      (pullback.mapFst (yoneda.map g) p.base z)
      (pullback.mapSnd (yoneda.map g) (pullback.fst z x ≫ z) p.base)
      (graphMap p) :=
  isPullback_graphMap_comp_base g p (RelativeMorphism.restrict (yoneda.map g) p).morphism
    (RelativeMorphism.restrict (yoneda.map g) p).commutes
    (by simp [pullback.map_id_eq_mapFst])

/-- **Stacks 0D1A.** The graph of the restriction of a relative morphism along `T' ⟶ T` is the
inverse image of its graph along the comparison of the two base changes of `Z ×_Q X`. This is the
naturality of the graph construction, in exactly the form the Hilbert functor restricts along. -/
theorem range_graphMap_restrict {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    Subfunctor.range (graphMap (RelativeMorphism.restrict (yoneda.map g) p)) =
      (Subfunctor.range (graphMap p)).preimage
        (schemeBaseChangeMap (graphAmbientMap B S hS z x hZ hX hQ)
          (HilbertFamilyOver.restrict g p.base)) := by
  rw [schemeBaseChangeMap_graphAmbientMap]
  exact Subfunctor.range_eq_preimage_of_isPullback (isPullback_graphMap_restrict g p)

/-- A relative morphism is determined by its base and its graph. The two graph maps are sections of
one retraction of `(Z ×_Q X)_T` onto `Z_T` — the projection to `Z` of the ambient fibre product
paired with the projection to `T`, which does not mention the relative morphism — so equal ranges
force the graph maps to agree, and the component in `X` of a graph map is the morphism. -/
theorem relativeMorphism_eq_of_range_graphMap_eq {T : BigFppfOver B S hS}
    {p q : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)} (hbase : p.base = q.base)
    (hrange : Subfunctor.range (graphMap p) ≍ Subfunctor.range (graphMap q)) : p = q := by
  obtain ⟨pb, pm, pc⟩ := p
  obtain ⟨qb, qm, qc⟩ := q
  dsimp only at hbase
  subst hbase
  have hsec : ∀ (m : pullback pb z ⟶ X) (hm : m ≫ x = pullback.snd pb z ≫ z),
      graphMap (⟨pb, m, hm⟩ : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) ≫
          pullback.lift (pullback.snd (pullback.fst z x ≫ z) pb)
            (pullback.fst (pullback.fst z x ≫ z) pb ≫ pullback.fst z x)
            (by rw [Category.assoc]; exact pullback.condition.symm) =
        𝟙 (pullback pb z) := by
    intro m hm
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact graphMap_snd _
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact graphMap_fst_fst _
  have hgraph : graphMap (⟨pb, pm, pc⟩ : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) =
      graphMap ⟨pb, qm, qc⟩ :=
    Subfunctor.eq_of_range_eq_of_comp_eq_id _ (hsec pm pc) (hsec qm qc) (eq_of_heq hrange)
  have hm : pm = qm := by
    have := congrArg (· ≫ pullback.fst (pullback.fst z x ≫ z) pb ≫ pullback.snd z x) hgraph
    rwa [graphMap_fst_snd, graphMap_fst_snd] at this
  subst hm
  rfl

/-- **Stacks 0D1A.** The *graph transformation* `Mor_Q(Z, X) ⟶ Hilb_{Z ×_Q X / Q}`: it carries a
relative morphism `(a, b)` at a test scheme `T` to the graph of `b`, a closed subspace of
`(Z ×_Q X)_T` which is of finite presentation, flat and proper over `T` because `z` is. It is
natural because the graph of a restriction is the inverse image of the graph
(`AlgebraicGeometry.Space.range_graphMap_restrict`). The source is composed with the universe lift,
the Hilbert presheaf taking values one universe up. -/
@[stacks 0D1A "the graph transformation"]
def graphTransformation (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z) :
    relativeHom B S hS Z X Q z x hZ hX hQ ⋙ uliftFunctor.{u + 1, u} ⟶
      hilbertPresheaf (graphAmbientMap B S hS z x hZ hX hQ) where
  app T := TypeCat.ofHom fun p =>
    { toBase := (relativeHomSections B S hS Z X Q z x hZ hX hQ T.unop p.down).base
      family := graphHilbertFamily hZ hX hQ
        (relativeHomSections B S hS Z X Q z x hZ hX hQ T.unop p.down) hsep hfp hflat hproper }
  naturality T T' g := by
    ext p
    have hsec : relativeHomSections B S hS Z X Q z x hZ hX hQ T'.unop
          ((relativeHom B S hS Z X Q z x hZ hX hQ).map g p.down) =
        RelativeMorphism.restrict (yoneda.map g.unop)
          (relativeHomSections B S hS Z X Q z x hZ hX hQ T.unop p.down) :=
      relativeHomSections_map B S hS Z X Q z x hZ hX hQ g.unop p.down
    exact Eq.trans (congrArg
      (fun q : RelativeMorphism B S hS Z X Q z x (yoneda.obj T'.unop) =>
        (⟨q.base, graphHilbertFamily hZ hX hQ q hsep hfp hflat hproper⟩ :
          HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T'.unop)) hsec)
      (HilbertFamilyOver.ext rfl (heq_of_eq (range_graphMap_restrict hZ hX hQ g.unop _)))

/-- The family the graph transformation produces lies over the first component of the relative
morphism. -/
@[simp]
theorem graphTransformation_app_toBase (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (T : BigFppfOver B S hS) (p : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op T)) :
    ((graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T)
        (ULift.up p)).toBase =
      (relativeHomSections B S hS Z X Q z x hZ hX hQ T p).base :=
  rfl

/-- **Stacks 0D1A.** The graph transformation maps a relative morphism to its graph: the closed
subspace of the family it produces is the range of the graph map. -/
@[stacks 0D1A "the transformation is the graph", simp]
theorem graphTransformation_app_family_Z (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (T : BigFppfOver B S hS) (p : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op T)) :
    ((graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T)
        (ULift.up p)).family.Z =
      Subfunctor.range (graphMap (relativeHomSections B S hS Z X Q z x hZ hX hQ T p)) :=
  rfl

/-- **Stacks 0D1A.** The graph transformation is injective at every test scheme: two relative
morphisms with the same graph have the same first component, and then
`AlgebraicGeometry.Space.relativeMorphism_eq_of_range_graphMap_eq` identifies them. -/
@[stacks 0D1A "injectivity"]
theorem graphTransformation_injective (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (T : BigFppfOver B S hS) :
    Function.Injective
      ((graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T)) := by
  intro a b hab
  apply ULift.ext
  apply (relativeHomSections B S hS Z X Q z x hZ hX hQ T).injective
  exact relativeMorphism_eq_of_range_graphMap_eq (congrArg HilbertFamilyOver.toBase hab)
    (HilbertFamilyOver.family_Z_heq hab)

end AlgebraicGeometry.Space

end
