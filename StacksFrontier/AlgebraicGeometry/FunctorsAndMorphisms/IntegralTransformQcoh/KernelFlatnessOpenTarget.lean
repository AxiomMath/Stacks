module

public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness

/-!
# Flatness of the kernel of an exact integral transform over an affine source

Let `R` be a commutative ring, let `X` be an affine scheme over `R` and let `Y` be an arbitrary
scheme over `R`.  A quasi-coherent module `K` on `X ×_R Y` has an integral transform
`F ↦ pr_{2,*}(pr_1^*F ⊗ K)` from quasi-coherent modules on `X` to quasi-coherent modules on
`Y`, and by Tag 0FZD every `R`-linear right exact functor commuting with arbitrary direct sums
arises this way.  If such a functor is exact, its kernel is flat over `X`.

Flatness over `X` is a local condition on `X ×_R Y`, so it suffices to check it on the open
cover of `X ×_R Y` by the `X ×_R V` for `V` an affine open of `Y`.  By the change-of-target
isomorphism of Tag 0FZF the integral transform of the restricted kernel is the integral
transform of `K` followed by the inverse image along `V ⟶ Y`, which is exact because an open
immersion is flat; so the case of an affine target applies to it and makes the restricted
kernel flat over `X`.  The inverse image along the open immersion `X ×_R V ⟶ X ×_R Y` is the
restricted kernel, so flatness at a point of `X ×_R V` is flatness of `K` at its image, and
every point of `X ×_R Y` is such an image.

## Main results

* `AlgebraicGeometry.exactFunctor_comp_quasicoherentPullback`: the composite of an exact functor
  with the inverse image along a flat morphism is exact on quasi-coherent modules.
* `AlgebraicGeometry.isFlatOver_of_exactFunctor`: Tag 0FZG in the case of Tag 0FZD, for an
  arbitrary target `Y`.

## References

* [Stacks Project, Tag 0FZG](https://stacks.math.columbia.edu/tag/0FZG)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The composite of an exact functor with the inverse image along a flat morphism is exact.
Inverse image along a flat morphism is left exact, and right exact because it is a left
adjoint. -/
theorem exactFunctor_comp_quasicoherentPullback {X V Y : Scheme.{u}}
    (F : Scheme.QuasicoherentModules X ⥤ Scheme.QuasicoherentModules Y) (j : V ⟶ Y) [Flat j]
    (hF : exactFunctor _ _ F) :
    exactFunctor _ _ (F ⋙ quasicoherentPullback j) := by
  have : PreservesFiniteLimits F := ((exactFunctor_iff F).mp hF).1
  have : PreservesFiniteColimits F := ((exactFunctor_iff F).mp hF).2
  have : PreservesFiniteLimits (quasicoherentPullback j) :=
    quasicoherentPullback_preservesFiniteLimits j
  have : PreservesFiniteColimits (quasicoherentPullback j) :=
    quasicoherentPullback_preservesFiniteColimits j
  rw [exactFunctor_iff]
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

/-- **The case of Tag 0FZG with `X` affine.**  In the situation of Tag 0FZD, so with `X`
affine and `Y` arbitrary, if the `R`-linear right exact direct-sum-preserving functor `F` is
exact, then the quasi-coherent module `K` on `X ×_R Y` corresponding to it is flat over `X`.

The correspondence between `F` and `K` is the isomorphism `hFK`.  Flatness over `X` is checked
on the cover of `X ×_R Y` by the open subschemes `X ×_R V` with `V` an affine open of `Y`: on
such a piece the kernel is the inverse image of `K`, and by Tag 0FZF it is the kernel of `F`
followed by the inverse image along `V ⟶ Y`, which is exact, so the case of an affine target
applies. -/
theorem isFlatOver_of_exactFunctor (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (F : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory)
    (hFK : F ≅ quasicoherentIntegralTransform R X Y K)
    (hF : exactFunctor _ _ F) :
    IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : Y.left.Opens))
      (x := (pullback.snd X.hom Y.hom).base x) (by simp)
  have : IsAffine V.toScheme := hV
  set V' : Over (Spec (.of R)) := Over.mk (V.ι ≫ Y.hom) with hV'
  set g : V' ⟶ Y := Over.homMk V.ι rfl with hg
  have : IsAffine V'.left := hV
  have : Flat g.left := inferInstanceAs (Flat V.ι)
  set q : pullback X.hom V'.hom ⟶ pullback X.hom Y.hom := targetChangeMap R X Y V' g with hq
  have : IsOpenImmersion q := by
    rw [hq]
    exact isOpenImmersion_openTargetChangeMap R X Y V.ι
  have haff : IsFlatOver (pullback.fst X.hom V'.hom).toLRSHom.toShHom
      (targetChangeKernel R X Y V' g K).obj :=
    isFlatOver_of_exactFunctor_affine R X V' (targetChangeKernel R X Y V' g K)
      (F ⋙ quasicoherentPullback g.left)
      (Functor.isoWhiskerRight hFK (quasicoherentPullback g.left) ≪≫
        quasicoherentIntegralTransformTargetChangeIso R X Y V' g K)
      (exactFunctor_comp_quasicoherentPullback F g.left hF)
  have hqp : q ≫ pullback.fst X.hom Y.hom = pullback.fst X.hom V'.hom :=
    targetChangeMap_comp_fst R X Y V' g
  have hx : x ∈ Set.range (pullback.fst (pullback.snd X.hom Y.hom) V.ι) := by
    rw [IsOpenImmersion.range_pullbackFst V.ι (pullback.snd X.hom Y.hom)]
    change (pullback.snd X.hom Y.hom).base x ∈ V.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    exact hxV
  obtain ⟨w, hw⟩ := hx
  have hpb := isPullback_targetChangeMap R X Y V' g
  have hxz : q (hpb.isoPullback.inv w) = x := by
    change (hpb.isoPullback.inv ≫ q) w = x
    rw [hpb.isoPullback_inv_fst]
    exact hw
  rw [← hxz]
  refine (isFlatOverAt_iff_modulePullback_isFlatOverAt q (pullback.fst X.hom Y.hom) K.obj
    (hpb.isoPullback.inv w) (Flat.stalkMap q _)).mpr ?_
  rw [hqp]
  exact haff _

end AlgebraicGeometry

end
