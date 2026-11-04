module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSource

/-!
# The geometry of the gluing of the kernels with affine source

Let `R` be a commutative ring and let `X`, `X'` and `Y` be schemes over `R`.  The kernel of
Tag 0GPA is glued from the kernels attached to the inclusions of the members of an affine open
cover of `X`, which live on the products `U ×_R Y` and have to be read as modules on the open
subschemes of `X ×_R Y` that those products are.  This file supplies the two inputs that reading
needs:

* affine change of source for the integral transform with *no* affineness hypothesis on `X`.
  `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso` asks for `X` affine only
  because it is stated alongside the equivalence of Tag 0FZD, while the underlying
  identification `AlgebraicGeometry.integralTransformFormulaSourceChangeIso` of the
  pullback--tensor--pushforward formulas needs nothing of the kind.  The gluing compares the
  glued kernel with the kernels of the members of the cover over the *whole* of `X`, so this is
  exactly the shape it needs.
* the identification of `U ×_R Y` with the open subscheme `pr_1^{-1}(U)` of `X ×_R Y` for an
  open `U` of `X`, compatibly with the inclusion into `X ×_R Y` and with the projection to `Y`,
  and the fact that these open subschemes cover `X ×_R Y` as soon as the `U` cover `X`.

## Main definitions

* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso'`: affine change of source
  for the integral transform, for `X` quasi-compact and quasi-separated rather than affine.
* `AlgebraicGeometry.productOpen`: the open subscheme `pr_1^{-1}(U)` of `X ×_R Y`.
* `AlgebraicGeometry.productOpenIso`: the identification of `U ×_R Y` with `pr_1^{-1}(U)`.

## Main results

* `AlgebraicGeometry.opensRange_sourceChangeMap_ι`: the range of `U ×_R Y ⟶ X ×_R Y` is
  `pr_1^{-1}(U)`.
* `AlgebraicGeometry.productOpenIso_hom_ι` and `AlgebraicGeometry.productOpenIso_hom_snd`: the
  identification is compatible with the inclusion into `X ×_R Y` and with the projection to `Y`.
* `AlgebraicGeometry.iSup_productOpen`: the open subschemes `pr_1^{-1}(U i)` cover `X ×_R Y`
  when the `U i` cover `X`.

## Implementation notes

The source of the inclusion is written `sourceOver R X U.ι`, the open subscheme regarded as a
scheme over `R` through its inclusion, so that the morphism `U ×_R Y ⟶ X ×_R Y` is the
`AlgebraicGeometry.sourceChangeMap` already used for the kernels; this keeps the identification
in the vocabulary of `IntegralTransformQcoh.ChangeOfSpaces` rather than introducing a second
spelling of the same product.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Affine change of source for an integral transform, for a quasi-compact and
quasi-separated source.**  For an affine morphism `f : X' ⟶ X` of schemes over `R` and a
quasi-coherent kernel `K` on `X ×_R Y`, the integral transform of `K` precomposed with the
direct image along `f` is the integral transform of `(f × id_Y)^*K`.

This is `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso` with the hypothesis
that `X` be affine removed; the proof is the same, since the affineness is used nowhere. -/
def quasicoherentIntegralTransformSourceChangeIso' (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y K ≅
      quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f K) :=
  ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).preimageIso
    (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
        (quasicoherentIntegralTransformData R X Y K).comparison ≪≫
      integralTransformFormulaSourceChangeIso R X X' Y f K ≪≫
      (quasicoherentIntegralTransformData R X' Y
        (sourceChangeKernel R X X' Y f K)).comparison.symm)

/-! ### The open subschemes of `X ×_R Y` lying over the opens of `X` -/

section ProductOpen

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- The open subscheme `pr_1^{-1}(U)` of `X ×_R Y` lying over an open `U` of `X`. -/
abbrev productOpen (U : X.left.Opens) : (pullback X.hom Y.hom).Opens :=
  pullback.fst X.hom Y.hom ⁻¹ᵁ U

/-- The morphism `U ×_R Y ⟶ X ×_R Y` induced by the inclusion of an open `U` of `X` is an open
immersion, being a base change of that inclusion. -/
instance isOpenImmersion_sourceChangeMap_ι (U : X.left.Opens) :
    IsOpenImmersion (sourceChangeMap R X (sourceOver R X U.ι) Y (sourceOverHom R X U.ι)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_sourceChangeMap R X (sourceOver R X U.ι) Y (sourceOverHom R X U.ι))
    (inferInstanceAs (IsOpenImmersion U.ι))

/-- **`U ×_R Y` is the open subscheme `pr_1^{-1}(U)` of `X ×_R Y`.**  Both are pullbacks of the
inclusion of `U` along the first projection: the left-hand one by
`AlgebraicGeometry.isPullback_sourceChangeMap`, the right-hand one by
`AlgebraicGeometry.isPullback_morphismRestrict`. -/
def productOpenIso (U : X.left.Opens) :
    pullback (sourceOver R X U.ι).hom Y.hom ≅ (productOpen R X Y U).toScheme :=
  IsPullback.isoIsPullback _ _
    (isPullback_sourceChangeMap R X (sourceOver R X U.ι) Y (sourceOverHom R X U.ι))
    (isPullback_morphismRestrict (pullback.fst X.hom Y.hom) U)

/-- The identification of `U ×_R Y` with `pr_1^{-1}(U)`, followed by the inclusion of
`pr_1^{-1}(U)` into `X ×_R Y`, is the morphism `U ×_R Y ⟶ X ×_R Y` induced by `U ⟶ X`. -/
@[simp]
theorem productOpenIso_hom_ι (U : X.left.Opens) :
    (productOpenIso R X Y U).hom ≫ (productOpen R X Y U).ι =
      sourceChangeMap R X (sourceOver R X U.ι) Y (sourceOverHom R X U.ι) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The identification of `U ×_R Y` with `pr_1^{-1}(U)` is compatible with the first
projection. -/
theorem productOpenIso_hom_restrict (U : X.left.Opens) :
    (productOpenIso R X Y U).hom ≫ pullback.fst X.hom Y.hom ∣_ U =
      pullback.fst (sourceOver R X U.ι).hom Y.hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The identification of `U ×_R Y` with `pr_1^{-1}(U)` is compatible with the projection to
`Y`. -/
theorem productOpenIso_hom_snd (U : X.left.Opens) :
    (productOpenIso R X Y U).hom ≫ (productOpen R X Y U).ι ≫ pullback.snd X.hom Y.hom =
      pullback.snd (sourceOver R X U.ι).hom Y.hom := by
  rw [← Category.assoc, productOpenIso_hom_ι, sourceChangeMap_comp_snd]

/-- **The open subschemes lying over a cover of `X` cover `X ×_R Y`.** -/
theorem iSup_productOpen {ι : Type*} (U : ι → X.left.Opens) (hU : ⨆ i, U i = ⊤) :
    ⨆ i, productOpen R X Y (U i) = ⊤ := by
  simpa [productOpen, Scheme.Hom.preimage_iSup] using
    congrArg (fun V : X.left.Opens => pullback.fst X.hom Y.hom ⁻¹ᵁ V) hU

end ProductOpen

/-! ### Reading an identity of kernels off the integral transforms -/

section KernelIsoExt

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [IsAffine X.left]

/-- **The isomorphism of kernels attached to an isomorphism of integral transforms induces that
isomorphism.**  On an affine source the functor of Tag 0FZD is fully faithful, so
`AlgebraicGeometry.kernelIsoOfIntegralTransformIso` is a two-sided inverse to taking integral
transforms; this is the direction that computes the induced natural transformation.

It is what reduces an identity between two isomorphisms of kernels — a cocycle condition, say —
to the corresponding identity between natural transformations of integral transforms, which is
where the composition laws of Tag 0FZF live. -/
theorem integralTransformQcohFunctor_map_kernelIsoOfIntegralTransformIso
    {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}
    (e : quasicoherentIntegralTransform R X Y K ≅ quasicoherentIntegralTransform R X Y L) :
    (integralTransformQcohFunctor R X Y).map (kernelIsoOfIntegralTransformIso R X Y e).hom =
      e.hom :=
  have : (integralTransformQcohFunctorLift R X Y).Full :=
    full_integralTransformQcohFunctorLift R X Y
  have : (integralTransformQcohFunctorLift R X Y).Faithful :=
    faithful_integralTransformQcohFunctorLift R X Y
  congrArg (fun φ : (integralTransformQcohFunctorLift R X Y).obj K ⟶
      (integralTransformQcohFunctorLift R X Y).obj L => φ.hom)
    ((Functor.FullyFaithful.ofFullyFaithful
      (integralTransformQcohFunctorLift R X Y)).map_preimage _)

/-- **Two isomorphisms of kernels on an affine source which induce the same isomorphism of
integral transforms are equal.** -/
theorem kernelIso_ext {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}
    (e₁ e₂ : K ≅ L)
    (h : (integralTransformQcohFunctor R X Y).map e₁.hom =
      (integralTransformQcohFunctor R X Y).map e₂.hom) :
    e₁ = e₂ :=
  have : (integralTransformQcohFunctorLift R X Y).Faithful :=
    faithful_integralTransformQcohFunctorLift R X Y
  Iso.ext ((integralTransformQcohFunctorLift R X Y).map_injective (ObjectProperty.hom_ext _ h))

end KernelIsoExt

/-! ### The chart modules of the gluing -/

section ChartKernel

attribute [local instance] isOpenImmersion_sourceOverHom_left

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- **The chart module of the gluing of Tag 0GPA at an affine open `U` of `X`.**  The kernel
attached by `AlgebraicGeometry.affineSourceKernel` to the inclusion of `U`, which lives on
`U ×_R Y`, read through `AlgebraicGeometry.productOpenIso` as a quasi-coherent module on the
open subscheme `pr_1^{-1}(U)` of `X ×_R Y`.  These are the modules the glued kernel is to
restrict to. -/
def productOpenKernel (hF : affineOpenRightExactLinearCoproductFunctor R X Y F) (U : X.left.Opens)
    [IsAffine U.toScheme] :
    Scheme.QuasicoherentModules (productOpen R X Y U).toScheme :=
  letI : IsAffine (sourceOver R X U.ι).left := inferInstanceAs (IsAffine U.toScheme)
  ⟨(Scheme.Modules.pullback (productOpenIso R X Y U).inv).obj
      (affineSourceKernel R X Y F hF (sourceOverHom R X U.ι)).obj,
    have : (affineSourceKernel R X Y F hF (sourceOverHom R X U.ι)).obj.IsQuasicoherent :=
      (affineSourceKernel R X Y F hF (sourceOverHom R X U.ι)).property
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (productOpenIso R X Y U).inv.toLRSHom.toShHom _ (by assumption)⟩

/-- The chart module at `U` is the kernel of `U ×_R Y` transported along the identification of
`U ×_R Y` with `pr_1^{-1}(U)`. -/
theorem productOpenKernel_obj (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    (U : X.left.Opens) [IsAffine U.toScheme] :
    letI : IsAffine (sourceOver R X U.ι).left := inferInstanceAs (IsAffine U.toScheme)
    (productOpenKernel R X Y F hF U).obj =
      (Scheme.Modules.pullback (productOpenIso R X Y U).inv).obj
        (affineSourceKernel R X Y F hF (sourceOverHom R X U.ι)).obj := rfl

end ChartKernel

end AlgebraicGeometry

end
