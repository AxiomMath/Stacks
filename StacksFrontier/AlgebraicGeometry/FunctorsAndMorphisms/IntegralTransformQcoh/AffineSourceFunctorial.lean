module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSource
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence

/-!
# The triangle and pseudo-functoriality for kernels with affine source

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with `X` of affine diagonal,
and let `F : QCoh(O_X) ⥤ QCoh(O_Y)` be `R`-linear, right exact and commuting with arbitrary
direct sums. `AlgebraicGeometry.affineSourceKernelSourceChangeIso` compares, for `f : X₁ ⟶ X`
and `g : X₂ ⟶ X₁` with `X₁` and `X₂` affine, the inverse image along `g × id_Y` of the kernel of
`f` with the kernel of `g ≫ f`. This file evaluates the integral transform of that comparison at
a quasi-coherent module, and reads the pseudo-functoriality of the source-change isomorphism of
[Stacks, Tag 0FZF] at a quasi-coherent module.

## Main results

* `AlgebraicGeometry.affineSourceKernelSourceChangeIso_triangle_app`: the source-change
  isomorphism followed by the integral transform of `affineSourceKernelSourceChangeIso` is the
  comparison for `f` at the direct image along `g`, inverted, followed by the comparison for
  `g ≫ f`.
* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_comp_app`: the source-change
  isomorphism of a composite `h ≫ g`, at a quasi-coherent module, is the composite of the
  source-change isomorphisms of `g` and `h` and the inverse comparison of the two iterated
  inverse images of the kernel.
* `AlgebraicGeometry.sourceChangeKernelFunctor_naturality`: the naturality of the source-change
  isomorphism in the kernel, with change of source given by
  `AlgebraicGeometry.sourceChangeKernelFunctor`.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] isOpenImmersion_over_comp_left

attribute [local implicit_reducible] CategoryTheory.instCategoryOver
  CategoryTheory.commaCategory AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

section Triangle

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)

/-- The comparison of the direct images along a composite, on quasi-coherent modules, has
identity components. -/
private theorem quasicoherentPushforwardComp_hom_app {Z Z' Z'' : Scheme.{u}} (f : Z'' ⟶ Z')
    (g : Z' ⟶ Z) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)] (M : Scheme.QuasicoherentModules Z'') :
    (quasicoherentPushforwardComp f g).hom.app M = 𝟙 _ := rfl

omit [IsAffineHom (pullback.diagonal (terminal.from X.left))] in
/-- **Two morphisms of quasi-coherent kernels on an affine source with the same integral
transform are equal.** -/
private theorem kernel_hom_ext [IsAffine X.left]
    {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)} {φ ψ : K ⟶ L}
    (h : (integralTransformQcohFunctor R X Y).map φ =
      (integralTransformQcohFunctor R X Y).map ψ) : φ = ψ :=
  have := faithful_integralTransformQcohFunctorLift R X Y
  (integralTransformQcohFunctorLift R X Y).map_injective (ObjectProperty.hom_ext _ h)

omit [IsAffineHom (pullback.diagonal (terminal.from X.left))] in
/-- **The integral transform of the isomorphism of kernels produced by an isomorphism of
integral transforms is that isomorphism.** -/
private theorem map_kernelIsoOfIntegralTransformIso [IsAffine X.left]
    {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}
    (e : quasicoherentIntegralTransform R X Y K ≅ quasicoherentIntegralTransform R X Y L) :
    (integralTransformQcohFunctor R X Y).map
      (kernelIsoOfIntegralTransformIso R X Y e).hom = e.hom :=
  have := full_integralTransformQcohFunctorLift R X Y
  have := faithful_integralTransformQcohFunctorLift R X Y
  congrArg (fun t : (integralTransformQcohFunctorLift R X Y).obj K ⟶
      (integralTransformQcohFunctorLift R X Y).obj L ↦ t.hom)
    ((Functor.FullyFaithful.ofFullyFaithful
      (integralTransformQcohFunctorLift R X Y)).map_preimage _)

variable {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left]
  [IsAffine X₃.left]

/-- The comparison of the direct images along a composite, whiskered by `F`, has identity
components. -/
theorem whiskerRight_quasicoherentPushforwardComp_app (f : X₁ ⟶ X) (g : X₂ ⟶ X₁)
    (M : Scheme.QuasicoherentModules X₂.left) :
    letI : IsAffineHom (Over.Hom.left f) := isAffineHom_left_of_isAffine_left R X f
    F.map ((quasicoherentPushforwardComp (Over.Hom.left g)
      (Over.Hom.left f)).hom.app M) = 𝟙 (F.obj ((quasicoherentPushforward
        (Over.Hom.left f)).obj ((quasicoherentPushforward (Over.Hom.left g)).obj M))) := by
  let : IsAffineHom (Over.Hom.left f) := isAffineHom_left_of_isAffine_left R X f
  exact F.map_id _

/-- The integral transform of `AlgebraicGeometry.affineSourceKernelSourceChangeIso` is the
isomorphism of integral transforms it was produced from. -/
private theorem map_affineSourceKernelSourceChangeIso (f : X₁ ⟶ X) (g : X₂ ⟶ X₁)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)] :
    letI : IsAffineHom (Over.Hom.left f) := isAffineHom_left_of_isAffine_left R X f
    letI : IsAffineHom (Over.Hom.left (g ≫ f)) :=
      isAffineHom_left_of_isAffine_left R X (g ≫ f)
    (integralTransformQcohFunctor R X₂ Y).map
        (affineSourceKernelSourceChangeIso R X Y F hF f g).hom =
      ((quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
            (affineSourceKernel R X Y F hF f)).symm ≪≫
          Functor.isoWhiskerLeft (quasicoherentPushforward (Over.Hom.left g))
            (affineSourceKernelIso R X Y F hF f).symm ≪≫
          Functor.isoWhiskerRight
            (quasicoherentPushforwardComp (Over.Hom.left g) (Over.Hom.left f)) F ≪≫
          affineSourceKernelIso R X Y F hF (g ≫ f)).hom :=
  map_kernelIsoOfIntegralTransformIso R X₂ Y _

/-- **The triangle of the comparison of the kernels with affine source**, at a quasi-coherent
module:  the source-change isomorphism of Tag 0FZF, followed by the integral transform of
`AlgebraicGeometry.affineSourceKernelSourceChangeIso`, is the comparison of `F ∘ f_*` with the
integral transform of the kernel of `f`, read at the direct image along `g`, followed by the
comparison at `g ≫ f`. -/
theorem affineSourceKernelSourceChangeIso_triangle_app (f : X₁ ⟶ X) (g : X₂ ⟶ X₁)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)]
    (M : Scheme.QuasicoherentModules X₂.left) :
    letI : IsAffineHom (Over.Hom.left f) := isAffineHom_left_of_isAffine_left R X f
    letI : IsAffineHom (Over.Hom.left (g ≫ f)) :=
      isAffineHom_left_of_isAffine_left R X (g ≫ f)
    (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
          (affineSourceKernel R X Y F hF f)).hom.app M ≫
        ((integralTransformQcohFunctor R X₂ Y).map
          (affineSourceKernelSourceChangeIso R X Y F hF f g).hom).app M =
      (affineSourceKernelIso R X Y F hF f).inv.app
          ((quasicoherentPushforward (Over.Hom.left g)).obj M) ≫
        (affineSourceKernelIso R X Y F hF (g ≫ f)).hom.app M := by
  let : IsAffineHom (Over.Hom.left f) := isAffineHom_left_of_isAffine_left R X f
  let : IsAffineHom (Over.Hom.left (g ≫ f)) :=
    isAffineHom_left_of_isAffine_left R X (g ≫ f)
  rw [map_affineSourceKernelSourceChangeIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.hom_inv_id_app_assoc]
  refine congrArg ((affineSourceKernelIso R X Y F hF f).inv.app
    ((quasicoherentPushforward (Over.Hom.left g)).obj M) ≫ ·) ?_
  exact (congrArg (· ≫ (affineSourceKernelIso R X Y F hF (g ≫ f)).hom.app M)
    (whiskerRight_quasicoherentPushforwardComp_app R X Y F f g M)).trans (Category.id_comp _)

end Triangle

/-! ### Pseudo-functoriality -/

section PseudoFunctorial

variable (R : Type u) [CommRing R] (Y : Over (Spec (.of R)))
  {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]

/-- **The identification of the direct image along a composite with the composite of the direct
images has identity components.** -/
theorem eqToIso_quasicoherentPushforward_hom_app (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (M : Scheme.QuasicoherentModules X₃.left) :
    (eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom.app M =
      𝟙 ((quasicoherentPushforward (Over.Hom.left (h ≫ g))).obj M) := by
  rw [eqToIso.hom, eqToHom_app]
  rfl

/-- The transport of the integral transform along the identification of the direct image along a
composite with the composite of the direct images is the identity. -/
private theorem map_eqToIso_quasicoherentPushforward_hom_app (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (K : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom))
    (M : Scheme.QuasicoherentModules X₃.left) :
    (quasicoherentIntegralTransform R X₁ Y K).map
        ((eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom.app M) =
      𝟙 ((quasicoherentPushforward (Over.Hom.left g) ⋙
            quasicoherentIntegralTransform R X₁ Y K).obj
        ((quasicoherentPushforward (Over.Hom.left h)).obj M)) := by
  rw [eqToIso_quasicoherentPushforward_hom_app R g h M]
  exact (quasicoherentIntegralTransform R X₁ Y K).map_id _

omit [IsAffine X₁.left] [IsAffine X₂.left] in
/-- The integral transform of the comparison of the two iterated inverse images of a kernel is
an isomorphism, at a quasi-coherent module. -/
theorem map_sourceChangeKernelCompIso_inv_hom_app (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (K : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom))
    (M : Scheme.QuasicoherentModules X₃.left) :
    ((integralTransformQcohFunctor R X₃ Y).map
          (sourceChangeKernelCompIso R X₁ X₂ X₃ Y g h K).inv).app M ≫
        ((integralTransformQcohFunctor R X₃ Y).map
          (sourceChangeKernelCompIso R X₁ X₂ X₃ Y g h K).hom).app M = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id]
  exact congrArg (fun α ↦ NatTrans.app α M) ((integralTransformQcohFunctor R X₃ Y).map_id _)

/-- **Pseudo-functoriality of the source-change isomorphism of Tag 0FZF at a quasi-coherent
module**: the source-change isomorphism of `h ≫ g` at `M` is that of `g` at the direct image of
`M` along `h`, followed by that of `h` at `M`, followed by the integral transform of the inverse
comparison of the two iterated inverse images of the kernel. -/
theorem quasicoherentIntegralTransformSourceChangeIso_comp_app
    (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (K : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom))
    (M : Scheme.QuasicoherentModules X₃.left) :
    (quasicoherentIntegralTransformSourceChangeIso R X₁ X₃ Y (h ≫ g) K).hom.app M =
      (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g K).hom.app
          ((quasicoherentPushforward (Over.Hom.left h)).obj M) ≫
        (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h
            (sourceChangeKernel R X₁ X₂ Y g K)).hom.app M ≫
          ((integralTransformQcohFunctor R X₃ Y).map
            (sourceChangeKernelCompIso R X₁ X₂ X₃ Y g h K).inv).app M := by
  have h1 := congrArg (fun α ↦ NatTrans.app α M)
    (quasicoherentIntegralTransformSourceChangeIso_comp R X₁ X₂ X₃ Y g h K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, map_eqToIso_quasicoherentPushforward_hom_app R Y g h K M] at h1
  exact h1.trans (Category.id_comp _)

/-- The naturality of the source-change isomorphism of Tag 0FZF in the kernel, in the form in
which change of source is `AlgebraicGeometry.sourceChangeKernelFunctor`. -/
theorem sourceChangeKernelFunctor_naturality (h : X₃ ⟶ X₂)
    (K L : Scheme.QuasicoherentModules (pullback X₂.hom Y.hom)) (φ : K ⟶ L) :
    (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h K).hom ≫
        (integralTransformQcohFunctor R X₃ Y).map
          ((sourceChangeKernelFunctor R X₂ X₃ Y h).map φ) =
      Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left h))
          ((integralTransformQcohFunctor R X₂ Y).map φ) ≫
        (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h L).hom :=
  (quasicoherentIntegralTransformSourceChangeIso_naturality R X₂ X₃ Y h K L φ).symm

end PseudoFunctorial


/-! ### The two spellings of a triple composite -/

section Cocycle

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
  {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]

omit [IsAffine X₁.left] [IsAffine X₂.left] in
/-- The two spellings of a triple composite give the same kernel, and the transport between
them is the identity. -/
theorem map_eqToHom_affineSourceKernel (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)]
    [IsOpenImmersion (Over.Hom.left h)] :
    (integralTransformQcohFunctor R X₃ Y).map
        (eqToHom (affineSourceKernel_congr R X Y F hF (Category.assoc h g f))) =
      𝟙 ((integralTransformQcohFunctor R X₃ Y).obj
        (affineSourceKernel R X Y F hF ((h ≫ g) ≫ f))) := by
  rw [show eqToHom (affineSourceKernel_congr R X Y F hF (Category.assoc h g f)) =
    𝟙 (affineSourceKernel R X Y F hF ((h ≫ g) ≫ f)) from rfl]
  exact (integralTransformQcohFunctor R X₃ Y).map_id _


end Cocycle

end AlgebraicGeometry

end
