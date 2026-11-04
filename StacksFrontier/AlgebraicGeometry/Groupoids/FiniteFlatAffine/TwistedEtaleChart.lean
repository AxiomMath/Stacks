module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.TwistedBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleInvariantRingMapAssembly
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantQuotientSchemes
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# Étale charts of the invariant spectrum from a twisted base change

Let `G = (U, R, s, t, c)` be a groupoid scheme with `U` and `R` affine and `s, t` finite locally
free, let `C` be its ring of invariant functions and `φ : U ⟶ M = Spec C` the canonical morphism.
Let `U' ⟶ U` be a separated étale twisted base change of `G` (see
`AlgebraicGeometry.GroupoidScheme.TwistedBaseChange`) with auxiliary morphism `q : U' ⟶ V`. This
file shows that every point `u'` of `U'` lies in an `R'`-invariant affine open `U''` of `U'` whose
invariant spectrum `M''` is étale over `M`, with `U'' = M'' ×_M U`, and through which `q`
restricted to `U''` factors. This is the heart of the existence half of the proof of Stacks 0DUR.

The argument is the source's: the class of `u'` is finite because `s'` is finite, so it lies in an
affine open of `U'` (Stacks 07S0, since `U' ⟶ U` is separated and quasi-finite and `U` is affine),
hence `u'` has an invariant affine open neighbourhood `U''` (Stacks 03JE). The morphism from the
restriction of the twisted groupoid to `U''` into `G` has cartesian source, target and stabilizer
squares, so Stacks 0DT9 makes `M'' ⟶ M` étale and `U'' = M'' ×_M U`. The restriction of `q` to
`U''` is invariant, so it factors through `U'' ⟶ M''` because the invariant spectrum is a
categorical quotient in the category of schemes.

## Main results

* `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.exists_etale_chart`: the étale chart.

## References

* [Stacks Project, Tag 0DUR](https://stacks.math.columbia.edu/tag/0DUR)
* [Stacks Project, Tag 07S0](https://stacks.math.columbia.edu/tag/07S0)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- Finite local freeness of morphisms of schemes is stable under base change. -/
theorem isFiniteLocallyFree_of_isPullback {X Y Z W : Scheme.{u}} {f' : X ⟶ Y} {g' : X ⟶ Z}
    {g : Y ⟶ W} {f : Z ⟶ W} (h : IsPullback f' g' g f) [IsFiniteLocallyFree g] :
    IsFiniteLocallyFree g' := by
  exact MorphismProperty.of_isPullback h ‹IsFiniteLocallyFree g›

namespace TwistedBaseChange

variable {G : GroupoidScheme S} [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (D : TwistedBaseChange G) [Etale D.proj.left] [IsSeparated D.proj.left]

/-- **An étale chart of the invariant spectrum through a point of a twisted base change.** Every
point `u'` of the object scheme `U'` of a separated étale twisted base change of `G` lies in an
invariant affine open `U''`, carrying the restricted groupoid `G''`, such that the invariant
spectrum `W = Spec C''` of `G''` is étale over `M = Spec C` with `U'' = W ×_M U`, and such that the
morphism `U'' ⟶ U' ⟶ V` factors through `U'' ⟶ W`; the factorization is compatible with any
descent `M ⟶ S` of the structure morphism of `U`. -/
theorem exists_etale_chart (σ : Spec (.of (invariantRing G)) ⟶ S)
    (hσ : objectsToInvariantSpectrum G ≫ σ = G.objects.hom) (u' : D.groupoid.objects.left) :
    ∃ (G'' : GroupoidScheme S) (ι : GroupoidScheme.Hom G'' D.groupoid)
      (e : Spec (.of (invariantRing G'')) ⟶ Spec (.of (invariantRing G)))
      (k : Spec (.of (invariantRing G'')) ⟶ D.aux.left),
      IsAffine G''.objects.left ∧ IsAffine G''.arrows.left ∧
        IsFiniteLocallyFree G''.source.left ∧ IsFiniteLocallyFree G''.target.left ∧
        IsOpenImmersion ι.mapObjects.left ∧ IsOpenImmersion ι.mapArrows.left ∧ Etale e ∧
        IsPullback (ι.mapObjects.left ≫ D.hom.mapObjects.left) (objectsToInvariantSpectrum G'')
          (objectsToInvariantSpectrum G) e ∧
        objectsToInvariantSpectrum G'' ≫ k = ι.mapObjects.left ≫ D.toAuxG.left ∧
        k ≫ D.aux.hom = e ≫ σ ∧ u' ∈ Set.range ι.mapObjects.left.base := by
  classical
  have : Etale D.hom.mapObjects.left := ‹Etale D.proj.left›
  have : IsSeparated D.hom.mapObjects.left := ‹IsSeparated D.proj.left›
  have : Unramified D.hom.mapObjects.left := unramified_of_etale _
  have : IsFiniteLocallyFree D.groupoid.source.left :=
    isFiniteLocallyFree_of_isPullback D.isPullback_source
  have : IsFiniteLocallyFree D.groupoid.target.left :=
    isFiniteLocallyFree_of_isPullback D.isPullback_target
  -- the class of `u'` is finite, so it lies in an affine open (Stacks 07S0)
  have hsfin : IsFinite D.groupoid.source.left := IsFiniteLocallyFree.isFinite _
  have hE : (D.groupoid.target.left.base '' (D.groupoid.source.left.base ⁻¹' {u'})).Finite :=
    (D.groupoid.source.left.finite_preimage_singleton u').image _
  obtain ⟨W₀, hW₀, hEW⟩ := exists_isAffineOpen_containing_finite_of_locallyQuasiFinite
    D.hom.mapObjects.left hE
  -- an invariant affine open neighbourhood of `u'` (Stacks 03JE)
  obtain ⟨V, hVinv, hVaff, hu'V⟩ :=
    exists_isInvariantOpen_isAffineOpen_mem D.groupoid u' ⟨W₀, hW₀, hEW⟩
  let ι := restrictInvariantOpenHom D.groupoid V hVinv
  let F := GroupoidScheme.Hom.comp ι D.hom
  have hιs := isPullback_restrictInvariantOpenHom_source D.groupoid V hVinv
  have hιt := isPullback_restrictInvariantOpenHom_target D.groupoid V hVinv
  have : IsAffine (restrictInvariantOpen D.groupoid V hVinv).objects.left := hVaff
  have : IsFiniteLocallyFree (restrictInvariantOpen D.groupoid V hVinv).source.left :=
    isFiniteLocallyFree_of_isPullback hιs
  have : IsFiniteLocallyFree (restrictInvariantOpen D.groupoid V hVinv).target.left :=
    isFiniteLocallyFree_of_isPullback hιt
  have : IsAffine (restrictInvariantOpen D.groupoid V hVinv).arrows.left :=
    isAffine_of_isAffineHom (restrictInvariantOpen D.groupoid V hVinv).source.left
  have : Etale F.mapObjects.left := by
    show Etale (ι.mapObjects.left ≫ D.hom.mapObjects.left)
    infer_instance
  -- the three cartesian squares of Stacks 0DT9
  have hsource : IsPullback F.mapArrows.left
      (restrictInvariantOpen D.groupoid V hVinv).source.left G.source.left F.mapObjects.left :=
    hιs.paste_horiz D.isPullback_source
  have htarget : IsPullback F.mapArrows.left
      (restrictInvariantOpen D.groupoid V hVinv).target.left G.target.left F.mapObjects.left :=
    hιt.paste_horiz D.isPullback_target
  have hsrc : ∀ {T : Scheme.{u}} (r : T ⟶ (restrictInvariantOpen D.groupoid V hVinv).arrows.left),
      (r ≫ F.mapArrows.left) ≫ G.source.left = (r ≫ F.mapArrows.left) ≫ G.target.left →
        r ≫ (restrictInvariantOpen D.groupoid V hVinv).source.left =
          r ≫ (restrictInvariantOpen D.groupoid V hVinv).target.left := by
    intro T r hr
    have h₀ : F.mapArrows.left = ι.mapArrows.left ≫ D.hom.mapArrows.left := rfl
    rw [h₀] at hr
    have h₁ := D.source_eq_target (r ≫ ι.mapArrows.left) (by simpa only [Category.assoc] using hr)
    rw [← cancel_mono ι.mapObjects.left, Category.assoc, Category.assoc,
      ← ι.map_source_left, ← ι.map_target_left]
    simpa only [Category.assoc] using h₁
  have hstab := isPullback_stabilizerMap F htarget hsrc
  have hetale := etale_invariantRingMap F hsource htarget hstab
  have hpb := isPullback_mapObjects F hsource htarget hstab
  -- the restriction of the auxiliary morphism is invariant, so it factors
  have hst := congrArg Over.Hom.left D.source_toAux
  simp only [Over.comp_left] at hst
  have hinv : (restrictInvariantOpen D.groupoid V hVinv).target.left ≫
        (ι.mapObjects.left ≫ D.toAuxG.left) =
      (restrictInvariantOpen D.groupoid V hVinv).source.left ≫
        (ι.mapObjects.left ≫ D.toAuxG.left) := by
    rw [← Category.assoc, ← Category.assoc, ← ι.map_target_left, ← ι.map_source_left,
      Category.assoc, Category.assoc]
    exact congrArg (fun z => ι.mapArrows.left ≫ z) hst.symm
  obtain ⟨k, hk, -⟩ := existsUnique_comp_objectsToInvariantSpectrum_scheme
    (restrictInvariantOpen D.groupoid V hVinv) _ hinv
  refine ⟨restrictInvariantOpen D.groupoid V hVinv, ι,
    Spec.map (CommRingCat.ofHom (invariantRingMap F)), k, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    HasRingHomProperty.Spec_iff.mpr hetale, hpb, hk, ?_, ⟨⟨u', hu'V⟩, rfl⟩⟩
  -- compatibility with the structure morphisms to `S`
  refine ext_of_comp_objectsToInvariantSpectrum (restrictInvariantOpen D.groupoid V hVinv) _ _ ?_
  rw [← Category.assoc, hk, ← Category.assoc, hpb.w.symm, Category.assoc, Category.assoc, hσ,
    Over.w D.toAuxG]
  show ι.mapObjects.left ≫ D.groupoid.objects.hom =
    (ι.mapObjects.left ≫ D.hom.mapObjects.left) ≫ G.objects.hom
  rw [Category.assoc, Over.w D.hom.mapObjects]

end TwistedBaseChange

end AlgebraicGeometry.GroupoidScheme

end

end
