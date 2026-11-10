module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.BaseChangeAcyclicity
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelFlatnessOpenTarget
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelOfFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffinePushforwardExact

/-!
# Flatness of the kernel of an exact functor on quasi-coherent modules

Let `R` be a ring and let `X` and `Y` be schemes over `R`.  This file proves [Stacks, Tag 0FZG]:
in the situation of Tag 0FZD (`X` affine) or of Tag 0GPA (`X` quasi-compact with affine
diagonal), if the functor `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` is exact, then the quasi-coherent module
`K` on `X ×_R Y` corresponding to it is flat over `X`.

## Main results

* `AlgebraicGeometry.isFlatOver_of_exactFunctor_of_isIso_whiskerLeft`: the case of Tag 0GPA, for
  every kernel `K` and transformation `t : F ⟶ F_K` that is an isomorphism on direct images from
  affine schemes.
* `AlgebraicGeometry.isFlatOver_integralTransformQcohEquivalence_inverse_obj`: the kernel
  attached to `F` by the equivalence of Tag 0FZD is flat over `X` when `F` is exact.
* `AlgebraicGeometry.isFlatOver_glued_of_exactFunctor`: the kernel constructed in Tag 0GPA is
  flat over `X` when `F` is exact.
* `AlgebraicGeometry.isFlatOver_kernel_of_exactFunctor`: [Stacks, Tag 0FZG], in both situations.

## References

* [Stacks Project, Tag 0FZG](https://stacks.math.columbia.edu/tag/0FZG)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The direct image along an affine morphism followed by an exact functor is exact. -/
theorem exactFunctor_quasicoherentPushforward_comp {X' X Y : Scheme.{u}} (f : X' ⟶ X)
    [IsAffineHom f] (F : Scheme.QuasicoherentModules X ⥤ Scheme.QuasicoherentModules Y)
    (hF : exactFunctor _ _ F) :
    exactFunctor _ _ (quasicoherentPushforward f ⋙ F) := by
  have : PreservesFiniteLimits F := ((exactFunctor_iff F).mp hF).1
  have : PreservesFiniteColimits F := ((exactFunctor_iff F).mp hF).2
  have : PreservesFiniteColimits (quasicoherentPushforward f) :=
    preservesFiniteColimits_quasicoherentPushforward f
  rw [exactFunctor_iff]
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

/-- **The kernel of an exact functor in the situation of Tag 0GPA is flat over `X`.**  Let `X`
be quasi-compact with affine diagonal, let `K` be a quasi-coherent module on `X ×_R Y` and let
`t : F ⟶ F_K` be a natural transformation such that `t ∘ f_*` is an isomorphism for every
morphism `f : X' ⟶ X` with `X'` affine.  If `F` is exact, then `K` is flat over `X`. -/
theorem isFlatOver_of_exactFunctor_of_isIso_whiskerLeft (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [CompactSpace X.left]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (t : F ⟶ quasicoherentIntegralTransform R X Y K)
    (ht : ∀ (X' : Scheme.{u}) [IsAffine X'] (f : X' ⟶ X.left),
      letI : IsAffineHom f :=
        Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source f
      IsIso (Functor.whiskerLeft (quasicoherentPushforward f) t))
    (hF : exactFunctor _ _ F) :
    IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj := by
  have : QuasiSeparated (terminal.from X.left) := ⟨inferInstance⟩
  have : QuasiSeparatedSpace X.left :=
    quasiSeparatedSpace_of_quasiSeparated (terminal.from X.left)
  intro x
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.left.Opens))
      (x := (pullback.fst X.hom Y.hom).base x) (by simp)
  have : IsAffine U.toScheme := hU
  have : IsAffine (openSubOver R X U).left := hU
  let : IsAffineHom (openSubOverHom R X U).left :=
    Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source U.ι
  have hiso := ht U.toScheme U.ι
  set q := sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U) with hq
  have hflat : IsFlatOver (pullback.fst (openSubOver R X U).hom Y.hom).toLRSHom.toShHom
      (sourceChangeKernel R X (openSubOver R X U) Y (openSubOverHom R X U) K).obj :=
    isFlatOver_of_exactFunctor R (openSubOver R X U) Y
      (sourceChangeKernel R X (openSubOver R X U) Y (openSubOverHom R X U) K)
      (quasicoherentPushforward (openSubOverHom R X U).left ⋙ F)
      (@asIso _ _ _ _ (Functor.whiskerLeft (quasicoherentPushforward U.ι) t) hiso ≪≫
        quasicoherentIntegralTransformSourceChangeIso' R X (openSubOver R X U) Y
          (openSubOverHom R X U) K)
      (exactFunctor_quasicoherentPushforward_comp _ F hF)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst X.hom Y.hom)
    (g := U.ι) x ⟨(pullback.fst X.hom Y.hom).base x, hxU⟩ (by simp)
  have hpb := (isPullback_sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U)).flip
  set w := hpb.isoPullback.inv z with hw
  have hqw : q w = x := by
    rw [← hz, hw, hq]
    change (hpb.isoPullback.inv ≫ _) z = _
    rw [hpb.isoPullback_inv_fst]
    rfl
  rw [← hqw]
  refine (isFlatOverAt_iff_modulePullback_isFlatOverAt q (pullback.fst X.hom Y.hom) K.obj w
    (Flat.stalkMap q _)).mpr ?_
  rw [sourceChangeMap_comp_fst R X (openSubOver R X U) Y (openSubOverHom R X U)]
  exact (show (pullback.fst (openSubOver R X U).hom Y.hom ≫ U.ι).toLRSHom.toShHom =
      (pullback.fst (openSubOver R X U).hom Y.hom).toLRSHom.toShHom ≫ U.ι.toLRSHom.toShHom
    from rfl) ▸ IsFlatOverAt.comp _ _ _ w (hflat w) (Flat.stalkMap U.ι _)

/-- **The kernel corresponding to an exact functor under the equivalence of Tag 0FZD is flat over
`X`.**  For `X` affine and `F` an `R`-linear right exact functor commuting with arbitrary direct
sums, the kernel `K` attached to `F` by the inverse of the equivalence
`AlgebraicGeometry.integralTransformQcohEquivalence` is flat over `X` as soon as `F` is exact. -/
theorem isFlatOver_integralTransformQcohEquivalence_inverse_obj (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left]
    (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory)
    (hF : exactFunctor _ _ F.obj) :
    IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom
      ((integralTransformQcohEquivalence R X Y).inverse.obj F).obj :=
  isFlatOver_of_exactFunctor R X Y _ F.obj
    ((ObjectProperty.ι _).mapIso ((integralTransformQcohEquivalence R X Y).counitIso.app F).symm)
    hF

/-- **The kernel constructed in Tag 0GPA is flat over `X` when the functor is exact.**  For `X`
quasi-compact with affine diagonal and `F` an `R`-linear right exact functor commuting with
arbitrary direct sums, the glued kernel `AlgebraicGeometry.AffineChartKernels.glued` of
`AlgebraicGeometry.openKernelSystem`, which comes with the transformation
`AlgebraicGeometry.kernelTransform`, is flat over `X` as soon as `F` is exact. -/
theorem isFlatOver_glued_of_exactFunctor (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [CompactSpace X.left]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
    (hF : rightExactLinearCoproductFunctor R X Y F) (hE : exactFunctor _ _ F) :
    IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom
      (openKernelSystem R X Y F
        (affineOpenRightExactLinearCoproductFunctor_of_rightExact R X Y F hF)).glued.obj := by
  refine isFlatOver_of_exactFunctor_of_isIso_whiskerLeft R X Y F _
    (kernelTransform R X Y F (affineOpenRightExactLinearCoproductFunctor_of_rightExact R X Y F hF))
    (fun X' hX' f => ?_) hE
  have : IsAffine (Over.mk (f ≫ X.hom)).left := hX'
  exact isIso_whiskerLeft_kernelTransform R X Y F hF (X' := Over.mk (f ≫ X.hom))
    (Over.homMk f rfl)

/-- **The kernel of an exact functor is flat.** In the situation of Tag 0FZD or of Tag 0GPA, if
`F` is an exact functor, then the corresponding object `K` of `QCoh(𝒪_{X ×_R Y})` is flat over
`X`.

The four conjuncts are:
1. the situation of Tag 0FZD (`X` affine, `Y` arbitrary), for every kernel `K` whose integral
   transform is isomorphic to `F`;
2. the same, for the kernel attached to `F` by the inverse of the equivalence of Tag 0FZD;
3. the situation of Tag 0GPA (`X` quasi-compact with affine diagonal), for every kernel `K` with
   a natural transformation `t : F ⟶ F_K` such that `t ∘ f_*` is an isomorphism for every
   morphism `f : X' ⟶ X` with `X'` affine;
4. the same, for the glued kernel constructed in Tag 0GPA from an `R`-linear right exact functor
   commuting with arbitrary direct sums. -/
@[stacks 0FZG "the kernel corresponding to an exact functor is flat over X, both for X affine \
and for X quasi-compact with affine diagonal"]
theorem isFlatOver_kernel_of_exactFunctor (R : Type u) [CommRing R] :
    (∀ (X Y : Over (Spec (.of R))) [IsAffine X.left]
      (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
      (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left),
      (F ≅ quasicoherentIntegralTransform R X Y K) → exactFunctor _ _ F →
        IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj) ∧
    (∀ (X Y : Over (Spec (.of R))) [IsAffine X.left]
      (F : (rightExactLinearCoproductFunctor R X Y).FullSubcategory),
      exactFunctor _ _ F.obj →
        IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          ((integralTransformQcohEquivalence R X Y).inverse.obj F).obj) ∧
    (∀ (X Y : Over (Spec (.of R))) [CompactSpace X.left]
      [IsAffineHom (pullback.diagonal (terminal.from X.left))]
      (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
      (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
      (t : F ⟶ quasicoherentIntegralTransform R X Y K),
      (∀ (X' : Scheme.{u}) [IsAffine X'] (f : X' ⟶ X.left),
        letI : IsAffineHom f :=
          Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source f
        IsIso (Functor.whiskerLeft (quasicoherentPushforward f) t)) →
      exactFunctor _ _ F →
        IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj) ∧
    (∀ (X Y : Over (Spec (.of R))) [CompactSpace X.left]
      [IsAffineHom (pullback.diagonal (terminal.from X.left))]
      (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
      (hF : rightExactLinearCoproductFunctor R X Y F),
      exactFunctor _ _ F →
        IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom
          (openKernelSystem R X Y F
            (affineOpenRightExactLinearCoproductFunctor_of_rightExact R X Y F hF)).glued.obj) :=
  ⟨fun X Y _ K F hFK hF => isFlatOver_of_exactFunctor R X Y K F hFK hF,
    fun X Y _ F hF => isFlatOver_integralTransformQcohEquivalence_inverse_obj R X Y F hF,
    fun X Y _ _ F K t ht hF => isFlatOver_of_exactFunctor_of_isIso_whiskerLeft R X Y F K t ht hF,
    fun X Y _ _ F hF hE => isFlatOver_glued_of_exactFunctor R X Y F hF hE⟩

end AlgebraicGeometry

end
