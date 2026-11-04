module

public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSourceCocycle
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.CharacterizingProperties

/-!
# Pseudo-functoriality of affine change of source with a quasi-separated source

`AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated` identifies, for
an affine morphism `f : X' ⟶ X` of schemes over `R` with `X` and `X'` quasi-compact and
quasi-separated, the integral transform of a quasi-coherent kernel on `X ×_R Y` precomposed with
the direct image along `f` with the integral transform of `(f × id_Y)^*K` on `X' ×_R Y`.  This is
Tag 0FZF with affineness of `X` relaxed to quasi-compactness and quasi-separatedness.

This file proves that this identification is compatible with composition of the morphism, in the
shape `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_comp` has it for an affine
source.

## Main results

* `whiskerRight_quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom`: the
  identification, after forgetting quasi-coherence of the values, is affine change of source for
  the pullback--tensor--pushforward formula of Tag 0FZB conjugated by the two comparison
  isomorphisms.
* `quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom_eq`: when `X` and `X'` are
  affine, the identification agrees with Tag 0FZF's own
  `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso`.
* `quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_comp`:
  **pseudo-functoriality of affine change of source with a quasi-separated source.**
* `quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_naturality`: the identification
  is natural in the kernel.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0GPB](https://stacks.math.columbia.edu/tag/0GPB)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

section QuasiSeparated

variable (R : Type u) [CommRing R] (X X' X'' Y : Over (Spec (.of R)))
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace X'.left] [QuasiSeparatedSpace X'.left]
  [CompactSpace X''.left] [QuasiSeparatedSpace X''.left]
  (f' : X' ⟶ X) (f'' : X'' ⟶ X') [IsAffineHom f'.left] [IsAffineHom f''.left]
  (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))

omit [CompactSpace X''.left] [QuasiSeparatedSpace X''.left] [IsAffineHom f''.left] in
/-- **Affine change of source with a quasi-separated source, after forgetting quasi-coherence of
the values**, is affine change of source for the pullback--tensor--pushforward formula of Tag
0FZB, conjugated by the two comparison isomorphisms. -/
theorem whiskerRight_quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom :
    Functor.whiskerRight
        (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f' K).hom
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι =
      Functor.whiskerLeft (quasicoherentPushforward f'.left)
          (quasicoherentIntegralTransformData R X Y K).comparison.hom ≫
        (integralTransformFormulaSourceChangeIso R X X' Y f' K).hom ≫
        (quasicoherentIntegralTransformData R X' Y
          (sourceChangeKernel R X X' Y f' K)).comparison.inv :=
  ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
    (Scheme.QuasicoherentModules X'.left)).map_preimage _

omit [CompactSpace X''.left] [QuasiSeparatedSpace X''.left] [IsAffineHom f''.left] in
/-- **On affine schemes the two affine-change-of-source isomorphisms agree.**  When `X` and `X'`
are affine, `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated` is
Tag 0FZF's `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso`. -/
theorem quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom_eq
    [IsAffine X.left] [IsAffine X'.left] :
    (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f' K).hom =
      (quasicoherentIntegralTransformSourceChangeIso R X X' Y f' K).hom := by
  refine whiskerRight_isQuasicoherentι_injective R Y X' ?_
  rw [whiskerRight_quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom,
    whiskerRight_quasicoherentIntegralTransformSourceChangeIso_hom]

/-- **Pseudo-functoriality of affine change of source with a quasi-separated source**:  change of
source along a composite `X'' ⟶ X' ⟶ X` of affine morphisms between quasi-compact quasi-separated
schemes over `R` is the composite of the two changes of source, up to the identification of the
two iterated inverse images of the kernel.  This is
`AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_comp` with affineness of the
target relaxed to quasi-compactness and quasi-separatedness. -/
theorem quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_comp :
    (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X'' Y (f'' ≫ f') K).hom =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
          (quasicoherentIntegralTransform R X Y K) ≫
        ((quasicoherentPushforward (Over.Hom.left f'')).associator
              (quasicoherentPushforward (Over.Hom.left f'))
              (quasicoherentIntegralTransform R X Y K)).hom ≫
          (quasicoherentPushforward (Over.Hom.left f'')).whiskerLeft
              (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f' K).hom ≫
            (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X' X'' Y f''
                (sourceChangeKernel R X X' Y f' K)).hom ≫
              (integralTransformQcohFunctor R X'' Y).map
                (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv := by
  refine whiskerRight_isQuasicoherentι_injective R Y X'' ?_
  rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerRight_comp,
    Functor.whiskerRight_comp]
  have hL := whiskerRight_quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom
    R X X'' Y (f'' ≫ f') K
  have h3 := whiskerRight_whiskerLeft_comp₃ (quasicoherentPushforward f''.left)
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
    (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f' K).hom _ _ _
    (whiskerRight_quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom R X X' Y f' K)
  have h4 := whiskerRight_quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_hom
    R X' X'' Y f'' (sourceChangeKernel R X X' Y f' K)
  have h5 := whiskerRight_integralTransformQcohFunctor_map R Y X'' _ _
    (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv
  have hex := whisker_exchange_pair (quasicoherentPushforward f''.left)
    (quasicoherentPushforward f'.left)
    (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
    (quasicoherentIntegralTransform R X Y K)
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
    (quasicoherentIntegralTransformData R X Y K).comparison.hom
  refine five_chain hL h3 h4 h5 ?_ ?_ hex
    (integralTransformFormulaSourceChangeIso_comp R X X' X'' Y f' f'' K)
  · exact NatTrans.ext (funext fun _ =>
      (quasicoherentIntegralTransformData R X' Y
        (sourceChangeKernel R X X' Y f' K)).comparison.inv_hom_id_app _)
  · exact Iso.inv_hom_id _

omit [CompactSpace X''.left] [QuasiSeparatedSpace X''.left] [IsAffineHom f''.left] in
/-- **Affine change of source with a quasi-separated source is natural in the kernel.**  For a
morphism `φ : K ⟶ L` of quasi-coherent kernels on `X ×_R Y`, the integral transform of `φ`
precomposed with the direct image along `f'` corresponds, through the two change-of-source
identifications, to the integral transform of the inverse image of `φ` on `X' ×_R Y`. -/
theorem quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_naturality
    {L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)} (φ : K ⟶ L) :
    Functor.whiskerLeft (quasicoherentPushforward f'.left)
          ((integralTransformQcohFunctor R X Y).map φ) ≫
        (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f' L).hom =
      (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f' K).hom ≫
        (integralTransformQcohFunctor R X' Y).map
          ((sourceChangeKernelFunctor R X X' Y f').map φ) :=
  preimageIso_sourceChange_naturality R X X' Y f' K L φ

end QuasiSeparated

end AlgebraicGeometry

end
