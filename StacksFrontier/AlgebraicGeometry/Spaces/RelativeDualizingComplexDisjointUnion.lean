module

public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.RelativeDualizingPair
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexAffinePerfect

/-!
# Relative dualizing complexes over a disjoint union of affines

Let `V = ⨆ i, Y i` be a disjoint union of affine algebraic spaces and `f : Z ⟶ V` proper, flat
and of finite presentation. The pairs `(a_i(𝒪_{Y i}), Tr)` on the base changes `Z ×_V Y i ⟶ Y i`
glue to a pair on `Z/V` which is a relative dualizing complex, by Stacks 0E60 applied to the
étale covering `{Y i ⟶ V}`. This is the degree-zero step of the proof of Stacks 0E61.

## Main results

* `AlgebraicGeometry.Space.nonempty_relativeDualizingComplex_of_isColimit_cofan`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  sheafTensor_additive_inverseImageRingedSite_over
  sheafTensor_obj_additive_inverseImageRingedSite_over
  hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A relative dualizing complex over a disjoint union of affines.** Let `V` be the disjoint
union, in the fppf sheaves of sets, of affine algebraic spaces `Y i`, and let `f : Z ⟶ V` be
proper, flat and of finite presentation. Then `f` has a relative dualizing complex: the pairs
`(a_i(𝒪_{Y i}), Tr)` of the base changes of `f` to the `Y i` glue to it. -/
theorem nonempty_relativeDualizingComplex_of_isColimit_cofan
    {ι : Type u} {Yi : ι → AlgebraicSpaces B S hS} {V : AlgebraicSpaces B S hS}
    {b : ∀ i, Yi i ⟶ V}
    (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj V)
      fun i => (algebraicSpacesToSheaf B S hS).map (b i)))
    (hYi : ∀ i, IsAffineSpace B S hS (Yi i).1)
    {Z : AlgebraicSpaces B S hS} (f : Z ⟶ V) (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom) :
    Nonempty (RelativeDualizingComplex hZ f hf hfl hfp) := by
  let A := algebraicSpacesToSheaf B S hS
  have sqi : ∀ i, IsPullback (pullback.snd (b i) f) (pullback.fst (b i) f) f (b i) :=
    fun i => (IsPullback.of_hasPullback (b i) f).flip
  have hcZ : IsColimit (Cofan.mk (A.obj Z) fun i => A.map (pullback.snd (b i) f)) :=
    (nonempty_isColimit_cofanMk_of_isPullback B S hS _ hc (A.map f)
      (fun i => A.map (pullback.snd (b i) f)) (fun i => A.map (pullback.fst (b i) f))
      fun i => (sqi i).map A).some
  have hfi : ∀ i, IsProper B S hS (pullback.fst (b i) f).hom := fun i =>
    (isProper_isStableUnderBaseChange B S hS).of_isPullback (sqi i) hf
  have hfli : ∀ i, IsFlat B S hS (pullback.fst (b i) f).hom := fun i =>
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback (sqi i) hfl
  have hfpi : ∀ i, IsFinitePresentation B S hS (pullback.fst (b i) f).hom := fun i =>
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback (sqi i) hfp
  let P : ∀ i, RelativeDualizingPair (pullback.fst (b i) f) (hfli i) (hfpi i) := fun i =>
    (RelativeDualizingComplex.ofIsAffine hZ (pullback.fst (b i) f) (hfi i) (hfli i) (hfpi i)
      (hYi i)).toRelativeDualizingPair
  obtain ⟨Q, e, he⟩ := exists_relativeDualizingPair_of_isColimit_cofan hcZ hc f hfl hfp
    (fun i => pullback.fst (b i) f) hfli hfpi (fun i => (sqi i).w) P
  exact ⟨{ Q with
    isAffineBaseChangePair := fun _ _ f' g g' sq hY' =>
      Q.isAffineBaseChangePair_of_isEtaleCovering_of_isProper hf sqi hYi
        (isEtaleCovering_cofanInj_of_isColimit hc) (fun i => ⟨e i, he i⟩) f' g g' sq hY' }⟩

end AlgebraicGeometry.Space

end
