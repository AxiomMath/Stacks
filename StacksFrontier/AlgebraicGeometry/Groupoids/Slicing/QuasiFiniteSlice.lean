module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RelativeDimensionLocus
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.MaximalSlice
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionStabilizer
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChange

/-!
# Quasi-finite slices of Cohen-Macaulay groupoid schemes

Let `(U, R, s, t, c, e, i)` be a groupoid scheme whose source and target maps are
Cohen-Macaulay and locally of finite presentation, let `u` be a finite type point of `U`, and
assume the stabilizer group scheme `G ⟶ U` is locally quasi-finite.  Then `u` admits an affine
slice `g : U' ⟶ U` which is an immersion locally of finite presentation and for which the
morphism `h : U' ×_{g, U, t} R ⟶ U` and the two structure maps of the restricted groupoid are
flat, locally of finite presentation and locally quasi-finite.

Starting from a slice whose source fibre has the same dimension as the restricted stabilizer
fibre, local quasi-finiteness of the stabilizer forces that common dimension to be zero, so `h`
has relative dimension zero at the identity arrow over `u`.  The relative-dimension-zero locus
of `h` is the inverse image of an open of `U'`, so shrinking `U'` to an affine open inside that
open makes `h` have relative dimension zero everywhere, hence locally quasi-finite; it stays
Cohen-Macaulay, hence flat, and locally of finite presentation.  The structure maps of the
restricted groupoid are base changes of `h`, so they inherit all three properties.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint` constructs the
  slice.

## Implementation notes

The slice is produced as a scheme over the base together with a morphism to the object scheme
and a point lying over `u`; these assemble into an `AlgebraicGeometry.SliceSituation`, whose
`sourceMap` is the morphism `h` of the source and whose `restrictedGroupoid` carries the
structure maps `s'` and `t'`.  Local Noetherianity of the fibres, which the Cohen-Macaulay
predicate for a morphism takes as an argument, is bundled existentially, as elsewhere in the
development.

The slice to be shrunk is the maximal Cohen-Macaulay slice of
`AlgebraicGeometry.exists_affine_slice_dim_eq_stabilizer`; of its conclusions only the
affineness of `U'`, the immersion and finite presentation of `g`, the Cohen-Macaulayness and
finite presentation of `h`, and the equality of the restricted source fibre dimension with the
restricted stabilizer fibre dimension are used.

## References

* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Precomposing with an open immersion does not change the local dimension of a fibre. -/
private lemma fiberDimensionAt_openImmersion_comp {U X S : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ S) (x : U) :
    topologicalKrullDimAt ((j ≫ f).fiber ((j ≫ f) x)) ((j ≫ f).asFiber x) =
      topologicalKrullDimAt (f.fiber (f (j x))) (f.asFiber (j x)) := by
  let B : Set X := f ⁻¹' {f (j x)}
  let A : Set U := j ⁻¹' B
  let C : Set U := (j ≫ f) ⁻¹' {(j ≫ f) x}
  rw [topologicalKrullDimAt_eq_of_homeomorph ((j ≫ f).fiberHomeo _) ((j ≫ f).asFiber x),
    topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo _) (f.asFiber (j x))]
  let e : C ≃ₜ A := Homeomorph.setCongr (by ext z; simp [C, A, B])
  have hpC : ((j ≫ f).fiberHomeo _) ((j ≫ f).asFiber x) = (⟨x, by simp [C]⟩ : C) :=
    Subtype.ext ((j ≫ f).fiberι_asFiber x)
  have hpB : (f.fiberHomeo _) (f.asFiber (j x)) = (⟨j x, by simp [B]⟩ : B) :=
    Subtype.ext (f.fiberι_asFiber (j x))
  rw [hpC, hpB, topologicalKrullDimAt_eq_of_homeomorph e]
  exact ((j.isOpenEmbedding.restrictPreimage B).topologicalKrullDimAt_eq ⟨x, by simp [B]⟩).symm

/-- A property of morphisms respecting isomorphisms holds for a morphism exactly when it holds
after precomposition with an isomorphism onto its source. -/
private lemma morphismProperty_isoDomain {P : MorphismProperty Scheme}
    [MorphismProperty.RespectsIso P] {X X' Y : Scheme.{u}} (e : X ≅ X')
    (f : X' ⟶ Y) (g : X ⟶ Y) (hfg : e.hom ≫ f = g) : P f ↔ P g :=
  MorphismProperty.arrow_mk_iso_iff P
    (Arrow.isoMk e.symm (Iso.refl _) (by rw [← hfg]; simp))

/-- Local quasi-finiteness is unchanged by postcomposition with an isomorphism. -/
private lemma locallyQuasiFinite_postcomp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) :
    LocallyQuasiFinite f ↔ LocallyQuasiFinite (f ≫ e.hom) := by
  have : MorphismProperty.RespectsIso (@LocallyQuasiFinite) :=
    AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite.respectsIso
  exact MorphismProperty.arrow_mk_iso_iff (@LocallyQuasiFinite)
    (Arrow.isoMk (Iso.refl X) e)

/-- A morphism locally of finite type is locally quasi-finite exactly when it has relative
dimension at most zero. -/
private theorem locallyQuasiFinite_iff_relativeDimensionLE_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] : LocallyQuasiFinite f ↔ RelativeDimensionLE f 0 := by
  refine ⟨fun hf x => ?_, fun h => ?_⟩
  · rw [relativeDimensionLEAt_iff]
    exact le_of_eq ((quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mp
      (((forall_quasiFiniteAt_iff f).mpr ⟨inferInstance, hf⟩) x))
  · exact ((forall_quasiFiniteAt_iff f).mp (fun x =>
      (quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mpr
        (le_antisymm ((relativeDimensionLEAt_iff f 0 x).mp (h x))
          (topologicalKrullDimAt_nonneg (f.asFiber x))))).2

/-- Local quasi-finiteness passes from an open subscheme to a smaller one. -/
private lemma locallyQuasiFinite_restrictOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V W : X.Opens} (hVW : V ≤ W) (hW : LocallyQuasiFinite (W.ι ≫ f)) :
    LocallyQuasiFinite (V.ι ≫ f) := by
  rw [← X.homOfLE_ι hVW]
  exact MorphismProperty.comp_mem (@LocallyQuasiFinite) (X.homOfLE hVW) (W.ι ≫ f)
    inferInstance hW

/-- The stabilizer of a restriction, viewed over the domain of the restricting morphism, is the
base change of the original stabilizer along it. -/
private noncomputable def restrictStabilizerIsoOver {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) :
    Over.mk ((stabilizer (GroupoidScheme.restrict G g).groupoid).hom ≫
      eqToHom (congrArg Over.left (GroupoidScheme.restrict G g).objects_eq)) ≅
      Over.mk (pullback.fst g.left (stabilizer G).hom) := by
  classical
  let ep := CartesianMonoidalCategory.lift (restrictionTarget G g) (restrictionSource G g)
  let d := CartesianMonoidalCategory.lift (𝟙 U') (𝟙 U')
  let R := GroupoidScheme.restrict G g
  change Over.mk ((stabilizer R.groupoid).hom ≫
      eqToHom (congrArg Over.left R.objects_eq)) ≅ _
  cases R with
  | mk H oe ae se te hom moe mae ev =>
    cases H with
    | mk objects arrows source target comp identity inverse source_identity target_identity
        source_inverse target_inverse left_identity right_identity left_inverse right_inverse
        assoc =>
      have hObj : objects = U' := oe
      cases hObj
      have hArr : arrows = restrictionArrows G g := ae
      cases hArr
      have hSrc : source = restrictionSource G g := by simpa using se
      cases hSrc
      have hTgt : target = restrictionTarget G g := by simpa using te
      cases hTgt
      let e₁ := overPullbackLeftIso g (pullback.snd (sourceTarget G) (diagonal G))
      refine Over.isoMk (((Over.forget S).mapIso (restrictedStabilizerOverIso G g)).trans e₁) ?_
      change (Over.Hom.left (restrictedStabilizerOverIso G g).hom ≫ e₁.hom) ≫
          pullback.fst g.left (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G))) =
        (pullback.snd ep d).left
      calc
        (Over.Hom.left (restrictedStabilizerOverIso G g).hom ≫ e₁.hom) ≫
            pullback.fst g.left (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G))) =
            Over.Hom.left (restrictedStabilizerOverIso G g).hom ≫
              (e₁.hom ≫ pullback.fst g.left
                (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G)))) :=
          Category.assoc _ _ _
        _ = Over.Hom.left (restrictedStabilizerOverIso G g).hom ≫
              (pullback.fst g (pullback.snd (sourceTarget G) (diagonal G))).left :=
          congrArg (fun k => Over.Hom.left (restrictedStabilizerOverIso G g).hom ≫ k)
            (overPullbackLeftIso_hom_fst g (pullback.snd (sourceTarget G) (diagonal G)))
        _ = (pullback.snd ep d).left := by
          simpa only [Over.comp_left] using
            congrArg Over.Hom.left (restrictedStabilizerOverIso_hom_fst G g)

/-- The stabilizer of a restriction of a groupoid with locally quasi-finite stabilizer is again
locally quasi-finite over the new object scheme. -/
private theorem locallyQuasiFinite_restrict_stabilizer {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    [LocallyQuasiFinite (stabilizer G).hom] :
    LocallyQuasiFinite (stabilizer (GroupoidScheme.restrict G g).groupoid).hom := by
  have : MorphismProperty.IsStableUnderBaseChange (@LocallyQuasiFinite) :=
    AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite
  have : MorphismProperty.RespectsIso (@LocallyQuasiFinite) := this.respectsIso
  have hbase : LocallyQuasiFinite (pullback.fst g.left (stabilizer G).hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g.left (stabilizer G).hom).flip inferInstance
  have hcomp : LocallyQuasiFinite (Over.mk
      ((stabilizer (GroupoidScheme.restrict G g).groupoid).hom ≫
        eqToHom (congrArg Over.left (GroupoidScheme.restrict G g).objects_eq))).hom :=
    (morphismProperty_isoDomain (P := @LocallyQuasiFinite)
      ((Over.forget _).mapIso (restrictStabilizerIsoOver G g))
      (pullback.fst g.left (stabilizer G).hom) _
      (Over.w (restrictStabilizerIsoOver G g).hom)).mp hbase
  exact (locallyQuasiFinite_postcomp_iso
    (stabilizer (GroupoidScheme.restrict G g).groupoid).hom
    (eqToIso (congrArg Over.left (GroupoidScheme.restrict G g).objects_eq))).mpr hcomp

/-- A nonempty stabilizer fibre of a groupoid scheme with locally quasi-finite stabilizer and
source map locally of finite type has dimension zero. -/
private lemma stabilizerFiber_topologicalKrullDim_eq_zero {S : Scheme.{u}}
    (G : GroupoidScheme S) [LocallyOfFiniteType G.source.left]
    [LocallyQuasiFinite (stabilizer G).hom] (u : G.objects.left)
    (hne : Nonempty ((stabilizer G).hom.fiber u)) :
    topologicalKrullDim ((stabilizer G).hom.fiber u) = 0 := by
  have : IsImmersion (stabilizerArrow G) := AlgebraicGeometry.stabilizerArrow_isImmersion G
  have heq : stabilizerArrow G ≫ G.source.left = (stabilizer G).hom := by
    simpa [stabilizerArrowHom, Over.comp_left] using
      congrArg Over.Hom.left (stabilizerArrowHom_source G (𝟙 (stabilizer G)))
  have : LocallyOfFiniteType (stabilizer G).hom := by
    rw [← heq]
    infer_instance
  exact ((locallyQuasiFinite_iff_relativeDimension_zero (stabilizer G).hom).mp
    inferInstance u hne).2

/-- The local dimension of a fibre at a point is computed by any point of the chosen fibre
mapping to it. -/
private lemma fiberDimensionAt_of_fiberι_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (z : f.fiber y) (hxy : f x = y) (hz : f.fiberι y z = x) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber y) z := by
  subst hxy
  obtain rfl : z = f.asFiber x :=
    (f.fiberι _).isEmbedding.injective (hz.trans (f.fiberι_asFiber x).symm)
  rfl

/-- The local dimension of a fibre is unchanged by an isomorphism of the source. -/
private lemma fiberDimensionAt_isoDomain {X X' Y : Scheme.{u}} (e : X ≅ X')
    (f : X' ⟶ Y) (g : X ⟶ Y) (hfg : e.hom ≫ f = g) (x : X) :
    topologicalKrullDimAt (f.fiber (f (e.hom x))) (f.asFiber (e.hom x)) =
      topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) := by
  subst hfg
  exact (fiberDimensionAt_openImmersion_comp e.hom f x).symm

/-- In the locally finite type groupoid situation, a point at which `h` has fibre dimension zero
lies over an open of `U'` whose inverse image restricts `h` to a locally quasi-finite
morphism. -/
private lemma exists_open_with_locallyQuasiFinite
    (D : LocallyOfFiniteTypeGroupoidSituation.{u}) (x : D.fiberProduct)
    (hx : topologicalKrullDimAt (D.h.fiber (D.h x)) (D.h.asFiber x) = 0) :
    ∃ W : D.U'.Opens, (pullback.fst D.g D.groupoid.target.left x ∈ W) ∧
      LocallyQuasiFinite ((pullback.fst D.g D.groupoid.target.left ⁻¹ᵁ W).ι ≫ D.h) := by
  have hDh : LocallyOfFiniteType D.h := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left))
  let V : D.fiberProduct.Opens :=
    ⟨{z | topologicalKrullDimAt (D.h.fiber (D.h z)) (D.h.asFiber z) ≤ 0},
      isOpen_setOf_fiberDimensionAt_le D.h 0⟩
  have hV : RelativeDimensionLE (V.ι ≫ D.h) 0 := by
    intro z
    rw [relativeDimensionLEAt_iff, fiberDimensionAt_openImmersion_comp V.ι D.h z]
    exact z.2
  have hxV : x ∈ V := by
    show topologicalKrullDimAt (D.h.fiber (D.h x)) (D.h.asFiber x) ≤ 0
    rw [hx]
  obtain ⟨W, hW⟩ := exists_open_with_preimage_maximal_relativeDimensionLE D 0
  refine ⟨W, hW.2 hV hxV, ?_⟩
  have hcomp : LocallyOfFiniteType
      ((pullback.fst D.g D.groupoid.target.left ⁻¹ᵁ W).ι ≫ D.h) :=
    MorphismProperty.comp_mem (@LocallyOfFiniteType)
      (pullback.fst D.g D.groupoid.target.left ⁻¹ᵁ W).ι D.h inferInstance hDh
  exact (@locallyQuasiFinite_iff_relativeDimensionLE_zero _ _ _ hcomp).mpr hW.1

/-- In the slice situation, if the source fibre of the restriction at the identity arrow has the
same dimension as the restricted stabilizer fibre, and the stabilizer of the groupoid is locally
quasi-finite, then `h` has fibre dimension zero at the identity arrow. -/
private lemma sourceMap_fiberDimensionAt_restrictedIdentity_eq_zero (D : SliceSituation.{u})
    [LocallyOfFiniteType D.groupoid.source.left] [LocallyOfFiniteType D.groupoid.target.left]
    [LocallyOfFiniteType D.g.left] [LocallyQuasiFinite (stabilizer D.groupoid).hom]
    (hsm : LocallyOfFiniteType D.sourceMap.left)
    (hdim : topologicalKrullDimAt D.restrictedSourceFiber
        D.sliceIdentityPoints.restrictedSourceIdentity =
      topologicalKrullDim D.restrictedStabilizerFiber) :
    topologicalKrullDimAt (D.sourceMap.left.fiber (D.sourceMap.left
        ((pullback.fst (pullback.snd D.g D.groupoid.target)
          (pullback.fst D.groupoid.source D.g)).left
            D.sliceIdentityPoints.restrictedIdentity)))
      (D.sourceMap.left.asFiber
        ((pullback.fst (pullback.snd D.g D.groupoid.target)
          (pullback.fst D.groupoid.source D.g)).left
            D.sliceIdentityPoints.restrictedIdentity)) = 0 := by
  let x := D.sliceIdentityPoints.restrictedIdentity
  have hpb : IsPullback
      (pullback.fst (pullback.snd D.g D.groupoid.target)
        (pullback.fst D.groupoid.source D.g)).left
      D.restrictedSource D.sourceMap.left D.g.left :=
    ((IsPullback.of_hasPullback
      (pullback.snd D.g D.groupoid.target) (pullback.fst D.groupoid.source D.g)).paste_vert
      (IsPullback.of_hasPullback D.groupoid.source D.g)).map (Over.forget D.S)
  have hdimPB := @topologicalKrullDimAt_fiber_eq_of_isPullback _ _ _ _ _ _ _ _ hpb hsm x
  have hdimRest := fiberDimensionAt_of_fiberι_eq D.restrictedSource x D.u'
    D.sliceIdentityPoints.restrictedSourceIdentity
    D.sliceIdentityPoints.restrictedIdentity_source
    D.sliceIdentityPoints.restrictedSourceIdentity_fiberι
  have : LocallyQuasiFinite (stabilizer D.restrictedGroupoid).hom :=
    locallyQuasiFinite_restrict_stabilizer D.groupoid D.g
  have : LocallyOfFiniteType D.restrictedGroupoid.source.left :=
    restriction_source_mem D.groupoid D.g D.restriction (@LocallyOfFiniteType) hsm
  exact hdimPB.symm.trans <| hdimRest.trans <| hdim.trans <|
    stabilizerFiber_topologicalKrullDim_eq_zero D.restrictedGroupoid
      D.restrictedObjectPoint ⟨D.sliceIdentityPoints.restrictedStabilizerFiberIdentity⟩

/-- **Stacks Project, Tag 04N0.** Let `(U, R, s, t, c, e, i)` be a groupoid scheme with `s` and
`t` Cohen-Macaulay and locally of finite presentation, let `u` be a finite type point of `U`,
and assume the stabilizer group scheme is locally quasi-finite.  Then there are an affine scheme
`U'` and a morphism `g : U' ⟶ U` such that `g` is an immersion, `u` lies in `U'`, `g` is locally
of finite presentation, the morphism `h : U' ×_{g, U, t} R ⟶ U` is flat, locally of finite
presentation and locally quasi-finite, and the structure maps `s', t' : R' ⟶ U'` of the
restricted groupoid are flat, locally of finite presentation and locally quasi-finite. -/
@[stacks 04N0 "conclusions (1)-(5): an affine immersion locally of finite presentation whose \
`h`, `s'` and `t'` are flat, locally of finite presentation and locally quasi-finite"]
public theorem exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (hu : AlgebraicGeometry.IsFiniteTypePoint u)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    (hs : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf)
    (ht : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf)
    [LocallyQuasiFinite (stabilizer G).hom] :
    ∃ (U' : Over S) (g : U' ⟶ G.objects) (u' : U'.left) (hgu : g.left u' = u),
      let D : SliceSituation :=
        { S := S, groupoid := G, U' := U', g := g, u := u, u' := u', mapsTo := hgu }
      IsAffine U'.left ∧ IsImmersion g.left ∧ LocallyOfFinitePresentation g.left ∧
        (Flat D.sourceMap.left ∧ LocallyOfFinitePresentation D.sourceMap.left ∧
          LocallyQuasiFinite D.sourceMap.left) ∧
        (Flat D.restrictedGroupoid.source.left ∧
          LocallyOfFinitePresentation D.restrictedGroupoid.source.left ∧
          LocallyQuasiFinite D.restrictedGroupoid.source.left) ∧
        (Flat D.restrictedGroupoid.target.left ∧
          LocallyOfFinitePresentation D.restrictedGroupoid.target.left ∧
          LocallyQuasiFinite D.restrictedGroupoid.target.left) := by
  classical
  obtain ⟨U', g, u', hgu, hAffine, hImm, hgLFP, hhLFP, hhCM, -, -, -, -, hdim⟩ :=
    exists_affine_slice_dim_eq_stabilizer G u hu hs ht
  let D : SliceSituation :=
    { S := S, groupoid := G, U' := U', g := g, u := u, u' := u', mapsTo := hgu }
  have : LocallyOfFinitePresentation g.left := hgLFP
  have : IsImmersion g.left := hImm
  have : LocallyOfFinitePresentation D.sourceMap.left := hhLFP
  -- The groupoid situation on underlying schemes, in which the maximal
  -- relative-dimension locus of `h` descends to an open of `U'`.
  let A : LocallyOfFiniteTypeGroupoidSituation :=
    { S := S, groupoid := G, U' := U'.left, g := g.left }
  let e₀ := overPullbackLeftIso D.g D.groupoid.target
  let x₀ := (pullback.fst (pullback.snd D.g D.groupoid.target)
    (pullback.fst D.groupoid.source D.g)).left D.sliceIdentityPoints.restrictedIdentity
  let x : A.fiberProduct := e₀.hom x₀
  have hmap : e₀.hom ≫ A.h = D.sourceMap.left := by
    show e₀.hom ≫ pullback.snd g.left G.target.left ≫ G.source.left =
      (pullback.snd D.g D.groupoid.target ≫ D.groupoid.source).left
    rw [← Category.assoc, overPullbackLeftIso_hom_snd, Over.comp_left]
  have hsmD : LocallyOfFiniteType D.sourceMap.left := inferInstance
  have hxzero := sourceMap_fiberDimensionAt_restrictedIdentity_eq_zero D hsmD hdim
  have hx : topologicalKrullDimAt (A.h.fiber (A.h x)) (A.h.asFiber x) = 0 :=
    (fiberDimensionAt_isoDomain e₀ A.h D.sourceMap.left hmap x₀).trans hxzero
  obtain ⟨W, hxW, hW⟩ := exists_open_with_locallyQuasiFinite A x hx
  obtain ⟨V, hV, hxV, hVW⟩ :
      ∃ V : U'.left.Opens, V ∈ U'.left.affineOpens ∧
        pullback.fst g.left G.target.left x ∈ V ∧ (V : Set U'.left) ⊆ (W : Set U'.left) := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      U'.left.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    exact ⟨V, hV, hxV, hVW⟩
  -- Flatness and local finite presentation of `h`, transported to the underlying schemes.
  obtain ⟨hfOld, hcmOld⟩ := hhCM
  have hflatOld : Flat D.sourceMap.left := flat_of_isCohenMacaulay _ hfOld hcmOld
  have : MorphismProperty.RespectsIso (@Flat) := Flat.isStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation) :=
    AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@LocallyQuasiFinite) :=
    AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite.respectsIso
  have hisoA {P : MorphismProperty Scheme} [P.RespectsIso] : P A.h ↔ P D.sourceMap.left :=
    morphismProperty_isoDomain e₀ A.h D.sourceMap.left hmap
  have hflatA : Flat A.h := hisoA.mpr hflatOld
  have hlfpA : LocallyOfFinitePresentation A.h := hisoA.mpr hhLFP
  -- The shrunken slice.
  let π : pullback g.left G.target.left ⟶ U'.left := pullback.fst g.left G.target.left
  let Vpre := π ⁻¹ᵁ V
  have hle : Vpre ≤ π ⁻¹ᵁ W := fun z hz => hVW hz
  have hqfV : LocallyQuasiFinite (Vpre.ι ≫ A.h) :=
    locallyQuasiFinite_restrictOpen A.h hle hW
  have hflatV : Flat (Vpre.ι ≫ A.h) :=
    MorphismProperty.comp_mem (@Flat) Vpre.ι A.h inferInstance hflatA
  have hlfpV : LocallyOfFinitePresentation (Vpre.ι ≫ A.h) :=
    MorphismProperty.comp_mem (@LocallyOfFinitePresentation) Vpre.ι A.h inferInstance hlfpA
  let U2 : Over S := Over.mk (V.ι ≫ U'.hom)
  let j : U2 ⟶ U' := Over.homMk V.ι (by simp [U2])
  have hj : j.left = V.ι := rfl
  let g2 : U2 ⟶ G.objects := j ≫ g
  let h2 := (pullback.snd g2 G.target ≫ G.source).left
  -- Identification of `U2 ×_{g2, U, t} R` with the open `Vpre` of `U' ×_{g, U, t} R`.
  let πOver := (pullback.fst g G.target).left
  let Vo := πOver ⁻¹ᵁ V
  have he₀fst : e₀.hom ≫ π = πOver := overPullbackLeftIso_hom_fst g G.target
  have he₀fstInv : e₀.inv ≫ πOver = π := by rw [← he₀fst]; simp
  have hRange : Set.range (Vo.ι ≫ e₀.hom) = Set.range Vpre.ι := by
    refine Set.ext fun y => ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (e₀.hom ≫ π) (Vo.ι z) ∈ V
      rw [congrArg (fun k => k (Vo.ι z)) he₀fst]
      exact z.2
    · rw [Scheme.Opens.range_ι]
      intro hy
      change π y ∈ V at hy
      refine ⟨⟨e₀.inv y, by change (e₀.inv ≫ πOver) y ∈ V; rw [he₀fstInv]; exact hy⟩, ?_⟩
      show e₀.hom (e₀.inv y) = y
      simp
  have : IsOpenImmersion (Vo.ι ≫ e₀.hom) := inferInstance
  let e₁ := pullbackRightPullbackFstIso g G.target j
  let e₂ := overPullbackLeftIso j (pullback.fst g G.target)
  let e₃ := pullbackSymmetry j.left πOver
  let e₃₄ := pullback.congrHom (show πOver = πOver from rfl) hj
  let e₄ := pullbackRestrictIsoRestrict πOver V
  let e₅ := IsOpenImmersion.isoOfRangeEq (Vo.ι ≫ e₀.hom) Vpre.ι hRange
  let e₂₃₄₅ := e₂.trans (e₃.trans (e₃₄.trans (e₄.trans e₅)))
  let eV : (pullback g2 G.target).left ≅ Vpre :=
    ((Over.forget S).mapIso e₁.symm).trans e₂₃₄₅
  let q := pullback.snd j (pullback.fst g G.target)
  have he₃₄ : e₃₄.hom ≫ e₄.hom ≫ Vo.ι = pullback.fst πOver j.left := by
    dsimp [e₃₄, e₄, Vo]
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst,
      pullbackRestrictIsoRestrict_hom_ι, Category.comp_id]
  have hq : e₂₃₄₅.hom ≫ Vpre.ι = q.left ≫ e₀.hom := by
    have htrans : e₂₃₄₅.hom = e₂.hom ≫ e₃.hom ≫ e₃₄.hom ≫ e₄.hom ≫ e₅.hom := by
      simp only [e₂₃₄₅, Iso.trans_hom]
    rw [htrans]
    calc
      e₂.hom ≫ e₃.hom ≫ e₃₄.hom ≫ e₄.hom ≫ e₅.hom ≫ Vpre.ι =
          e₂.hom ≫ e₃.hom ≫ (e₃₄.hom ≫ e₄.hom ≫ Vo.ι) ≫ e₀.hom := by
            dsimp only [e₅]
            rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
            simp only [Category.assoc]
      _ = e₂.hom ≫ (e₃.hom ≫ pullback.fst πOver j.left) ≫ e₀.hom := by
            rw [he₃₄]; simp only [Category.assoc]
      _ = e₂.hom ≫ pullback.snd j.left πOver ≫ e₀.hom := by
            rw [show e₃.hom ≫ pullback.fst πOver j.left = pullback.snd j.left πOver from by
              simp [e₃]]
      _ = q.left ≫ e₀.hom := by
            dsimp only [e₂, q]
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ e₀.hom)
                (overPullbackLeftIso_hom_snd j (pullback.fst g G.target))
  have hpb2 : e₁.inv ≫ q ≫ pullback.snd g G.target = pullback.snd g2 G.target := by
    calc
      e₁.inv ≫ q ≫ pullback.snd g G.target =
          e₁.inv ≫ (e₁.hom ≫ pullback.snd g2 G.target) := by
            rw [pullbackRightPullbackFstIso_hom_snd]
      _ = pullback.snd g2 G.target := by simp [e₁]
  have heV : eV.hom = e₁.inv.left ≫ e₂₃₄₅.hom := rfl
  have hmap2 : eV.hom ≫ (Vpre.ι ≫ A.h) = h2 := by
    calc
      eV.hom ≫ (Vpre.ι ≫ A.h) = e₁.inv.left ≫ (e₂₃₄₅.hom ≫ Vpre.ι) ≫ A.h :=
            (congrArg (fun k => k ≫ Vpre.ι ≫ A.h) heV).trans
              ((Category.assoc e₁.inv.left e₂₃₄₅.hom (Vpre.ι ≫ A.h)).trans
                (congrArg (fun k => e₁.inv.left ≫ k)
                  (Category.assoc e₂₃₄₅.hom Vpre.ι A.h).symm))
      _ = e₁.inv.left ≫ q.left ≫ (e₀.hom ≫ A.h) :=
            congrArg (fun k => e₁.inv.left ≫ k)
              ((congrArg (fun k => k ≫ A.h) hq).trans (Category.assoc q.left e₀.hom A.h))
      _ = (e₁.inv ≫ q ≫ pullback.snd g G.target ≫ G.source).left := by
            rw [hmap]
            show e₁.inv.left ≫ q.left ≫
              (pullback.snd g G.target ≫ G.source).left = _
            simp only [Over.comp_left]
      _ = h2 := by
            simpa [h2, Over.comp_left] using
              congrArg Over.Hom.left (congrArg (fun k => k ≫ G.source) hpb2)
  have hisoV {P : MorphismProperty Scheme} [P.RespectsIso] : P (Vpre.ι ≫ A.h) ↔ P h2 :=
    morphismProperty_isoDomain eV (Vpre.ι ≫ A.h) h2 hmap2
  have hqf2 : LocallyQuasiFinite h2 := hisoV.mp hqfV
  have hflat2 : Flat h2 := hisoV.mp hflatV
  have hlfp2 : LocallyOfFinitePresentation h2 := hisoV.mp hlfpV
  -- The chosen point of the shrunken slice lies over `u`.
  have hpull : g.left (πOver x₀) = G.target.left ((pullback.snd g G.target).left x₀) :=
    congrArg (fun k => k x₀) (congrArg Over.Hom.left (pullback.condition (f := g) (g := G.target)))
  have harrow : (pullback.snd g G.target).left x₀ = G.identity.left u := by
    show ((pullback.fst (pullback.snd D.g D.groupoid.target)
      (pullback.fst D.groupoid.source D.g) ≫
      pullback.snd D.g D.groupoid.target).left D.sliceIdentityPoints.restrictedIdentity) = _
    exact D.sliceIdentityPoints.restrictedIdentity_arrow
  have htid : G.target.left (G.identity.left u) = u := by
    simpa using congrArg (fun k => k u) (congrArg Over.Hom.left G.target_identity)
  have hcoordOver : πOver x₀ = u' := by
    refine g.left.isEmbedding.injective ?_
    rw [hpull, harrow, htid, hgu]
  have hcoord : π x = u' := by
    show π (e₀.hom x₀) = u'
    simpa using (congrArg (fun k => k x₀) he₀fst).trans hcoordOver
  let u2 : V.toScheme := ⟨π x, hxV⟩
  have hpoint : g2.left u2 = u := by
    show g.left (V.ι u2) = u
    simpa [u2] using (congrArg g.left hcoord).trans hgu
  refine ⟨U2, g2, u2, hpoint, hV, ?_, ?_, ⟨hflat2, hlfp2, hqf2⟩, ?_, ?_⟩
  · show IsImmersion (V.ι ≫ g.left)
    infer_instance
  · show LocallyOfFinitePresentation (V.ι ≫ g.left)
    infer_instance
  · exact ⟨restriction_source_mem G g2 (GroupoidScheme.restrict G g2) _ hflat2,
      restriction_source_mem G g2 (GroupoidScheme.restrict G g2) _ hlfp2,
      restriction_source_mem G g2 (GroupoidScheme.restrict G g2) _ hqf2⟩
  · exact ⟨restriction_target_mem G g2 (GroupoidScheme.restrict G g2) _ hflat2,
      restriction_target_mem G g2 (GroupoidScheme.restrict G g2) _ hlfp2,
      restriction_target_mem G g2 (GroupoidScheme.restrict G g2) _ hqf2⟩

end AlgebraicGeometry
