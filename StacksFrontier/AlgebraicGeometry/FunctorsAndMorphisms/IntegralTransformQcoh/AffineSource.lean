module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine
import all StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# Integral-transform kernels along a morphism with affine source

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` and assume the diagonal of
`X` over `R` is affine.  Every morphism `f : X' ⟶ X` whose source is an affine scheme is then an
affine morphism, so direct image along `f` is `R`-linear, right exact on quasi-coherent modules
and commutes with arbitrary direct sums.  Consequently, if `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` is
`R`-linear, right exact and commutes with arbitrary direct sums, so is `F ∘ f_*`, and the
equivalence of Tag 0FZD attaches to it a quasi-coherent kernel on `X' ×_R Y`.

## Main definitions

* `AlgebraicGeometry.sourceOver` regards the source of a morphism to `X` as a scheme over `R`,
  and `AlgebraicGeometry.sourceOverHom` regards the morphism itself as a morphism over `R`.
* `AlgebraicGeometry.affineOpenRightExactLinearCoproductFunctor` is the property of being
  `R`-linear, commuting with arbitrary direct sums, and right exact after direct image along
  every open immersion with affine source.
* `AlgebraicGeometry.affineSourceKernel` is the quasi-coherent module on `X' ×_R Y` whose
  integral transform is `F ∘ f_*`, for `f` an open immersion with affine source.
* `AlgebraicGeometry.quasicoherentPushforwardComp` is the composition isomorphism for direct
  image on quasi-coherent modules.

## Main results

* `AlgebraicGeometry.quasicoherentPushforward_linear`,
  `AlgebraicGeometry.preservesColimitsOfShape_discrete_quasicoherentPushforward` and
  `AlgebraicGeometry.preservesFiniteColimits_quasicoherentPushforward`: direct image on
  quasi-coherent modules is `R`-linear, commutes with arbitrary direct sums, and is right exact
  along an affine morphism.
* `AlgebraicGeometry.rightExactLinearCoproductFunctor_comp_quasicoherentPushforward`: for `f`
  with affine source, `F ∘ f_*` is again `R`-linear, right exact and commutes with arbitrary
  direct sums.
* `AlgebraicGeometry.affineSourceKernelIso`: `F ∘ f_*` is the integral transform of
  `AlgebraicGeometry.affineSourceKernel`.
* `AlgebraicGeometry.kernelIsoOfIntegralTransformIso`: on an affine source, an isomorphism of
  integral transforms comes from an isomorphism of kernels.
* `AlgebraicGeometry.affineSourceKernelSourceChangeIso`: for a further morphism `g : X'' ⟶ X'`
  with `X''` affine, the inverse image along `g × id_Y` of the kernel attached to `f` is the
  kernel attached to `g ≫ f`.

## Implementation notes

Right exactness of `f_*` on quasi-coherent modules is genuinely a property of affine `f`, and is
assembled from coequalizers and finite coproducts exactly as for the integral transform: the
coequalizer half has to be proved one diagram at a time, since the direct image preserves only
those coequalizers whose two objects are quasi-coherent.

The source of `f` is taken to be a scheme over `R` and `f` a morphism over `R`.  This is no
restriction, and in particular does not weaken the quantifier over morphisms with affine source:
an arbitrary morphism `f : X' ⟶ X` of schemes makes its source a scheme over `R` through `f`
itself, and `AlgebraicGeometry.sourceOver`, `AlgebraicGeometry.sourceOverHom` and
`AlgebraicGeometry.sourceOverHom_left` record that passage.  Writing the binders this way rather
than inserting the base structure with a `let` keeps the source of `f` a free variable, which is
what lets instance search match the affineness of `f` against the hypotheses of the direct image.

Affineness of `f` is not a hypothesis:  it follows from affineness of the source and of the
diagonal of `X`, and is inserted into the statements as a `letI` so that the direct image on
quasi-coherent modules is available in them.

The kernel and the identification of `F ∘ f_*` with its integral transform are data, taken from
the inverse and the counit of the equivalence of Tag 0FZD, not from an existence statement.

The declarations here are the affine-source steps of [Stacks, Tag 0GPA]: a kernel for each
morphism with affine source, the comparison with its integral transform at such a morphism, and
the compatibility of those kernels under a further affine change of source.  The tag itself, with
the kernels glued into a single quasi-coherent module on `X ×_R Y` and the natural transformation
on all of `QCoh(𝒪_X)`, is
`AlgebraicGeometry.exists_kernel_natTrans_isIso_whiskerLeft_pushforward` in
`StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelOfFunctor`.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Direct image on quasi-coherent modules -/

section Pushforward

variable (R : Type u) [CommRing R]

/-- Direct image along a morphism of schemes over `R`, on quasi-coherent modules, is linear over
the base ring. -/
theorem quasicoherentPushforward_linear {X' X : Over (Spec (.of R))} (f : X' ⟶ X)
    [QuasiCompact f.left] [QuasiSeparated f.left] :
    letI : Linear R (SheafOfModules.{u} X'.left.ringCatSheaf) := modulesLinear R X'
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    (quasicoherentPushforward f.left).Linear R := by
  let : Linear R (SheafOfModules.{u} X'.left.ringCatSheaf) := modulesLinear R X'
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R X'.left.Modules := modulesLinear R X'
  let : Linear R X.left.Modules := modulesLinear R X
  let ι' : Scheme.QuasicoherentModules X'.left ⥤ X'.left.Modules :=
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X'.left.ringCatSheaf)
  let pf : X'.left.Modules ⥤ X.left.Modules := Scheme.Modules.pushforward f.left
  have : ι'.Linear R :=
    inferInstanceAs (Functor.Linear R
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X'.left.ringCatSheaf)))
  have : pf.Linear R := over_pushforward_linear R f
  have : (quasicoherentPushforward f.left ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf)).Linear R :=
    inferInstanceAs ((ι' ⋙ pf).Linear R)
  exact linear_of_faithful_comp R (quasicoherentPushforward f.left)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf))

variable {X' X : Scheme.{u}}

/-- Direct image along a quasi-compact and quasi-separated morphism of schemes, on quasi-coherent
modules, commutes with arbitrary direct sums. -/
theorem preservesColimitsOfShape_discrete_quasicoherentPushforward (f : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (quasicoherentPushforward f) := by
  let P₁ := SheafOfModules.isQuasicoherent X'.ringCatSheaf
  let P₂ := SheafOfModules.isQuasicoherent X.ringCatSheaf
  have : P₁.IsClosedUnderColimitsOfShape (Discrete I) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := Discrete I) X'
  have : P₂.IsClosedUnderColimitsOfShape (Discrete I) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := Discrete I) X
  let : CreatesColimitsOfShape (Discrete I) (ObjectProperty.ι P₂) := inferInstance
  have : PreservesColimitsOfShape (Discrete I)
      (quasicoherentPushforward f ⋙ ObjectProperty.ι P₂) := by
    let ι₁ : P₁.FullSubcategory ⥤ X'.Modules := ObjectProperty.ι P₁
    let pf : X'.Modules ⥤ X.Modules := Scheme.Modules.pushforward f
    let : CreatesColimitsOfShape (Discrete I) (ObjectProperty.ι P₁) := inferInstance
    have : PreservesColimitsOfShape (Discrete I) ι₁ :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete I) (ObjectProperty.ι P₁))
    have : PreservesColimitsOfShape (Discrete I) pf :=
      schemePushforward_preservesCoproducts f I
    exact inferInstanceAs (PreservesColimitsOfShape (Discrete I) (ι₁ ⋙ pf))
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (quasicoherentPushforward f) (ObjectProperty.ι P₂)

/-- Quasi-coherent modules on a scheme have finite coproducts, built from the ones indexed by
`Type u`. -/
private theorem hasFiniteCoproducts_quasicoherentModules (Z : Scheme.{u}) :
    HasFiniteCoproducts (Scheme.QuasicoherentModules Z) := by
  refine ⟨fun n => ?_⟩
  have : HasColimitsOfShape (Discrete (ULift.{u} (Fin n)))
      (Scheme.QuasicoherentModules Z) := inferInstance
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{u})

/-- Along an affine morphism, the inclusion of quasi-coherent modules followed by the direct
image preserves the colimit of every parallel pair:  the inclusion preserves it, and the direct
image preserves it because the two modules in the diagram are quasi-coherent. -/
private theorem preservesColimitsOfShape_walkingParallelPair_iota_pushforward
    (f : X' ⟶ X) [IsAffineHom f] :
    PreservesColimitsOfShape WalkingParallelPair
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X'.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f) := by
  refine ⟨fun {D} => ?_⟩
  let P := SheafOfModules.isQuasicoherent X'.ringCatSheaf
  let ι' : P.FullSubcategory ⥤ X'.Modules := ObjectProperty.ι P
  have : P.IsClosedUnderColimitsOfShape WalkingParallelPair :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := WalkingParallelPair) X'
  let : CreatesColimitsOfShape WalkingParallelPair (ObjectProperty.ι P) := inferInstance
  have : PreservesColimitsOfShape WalkingParallelPair ι' :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (ObjectProperty.ι P))
  have : PreservesColimit (D ⋙ ι') (Scheme.Modules.pushforward f) :=
    Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_walkingParallelPair f
      (D ⋙ ι') (D.obj WalkingParallelPair.zero).property
      (D.obj WalkingParallelPair.one).property
  exact inferInstanceAs (PreservesColimit D (ι' ⋙ Scheme.Modules.pushforward f))

/-- **Right exactness of the direct image along an affine morphism, on quasi-coherent modules.**
Finite colimits are assembled from coequalizers and finite coproducts; the coproduct half is the
direct-sum statement at a finite index type. -/
theorem preservesFiniteColimits_quasicoherentPushforward (f : X' ⟶ X) [IsAffineHom f] :
    PreservesFiniteColimits (quasicoherentPushforward f) := by
  let P₁ := SheafOfModules.isQuasicoherent X'.ringCatSheaf
  let P₂ := SheafOfModules.isQuasicoherent X.ringCatSheaf
  have : HasFiniteCoproducts P₁.FullSubcategory := hasFiniteCoproducts_quasicoherentModules X'
  have : PreservesColimitsOfShape WalkingParallelPair (quasicoherentPushforward f) := by
    have : P₂.IsClosedUnderColimitsOfShape WalkingParallelPair :=
      Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
        (K := WalkingParallelPair) X
    let : CreatesColimitsOfShape WalkingParallelPair (ObjectProperty.ι P₂) := inferInstance
    have : PreservesColimitsOfShape WalkingParallelPair
        (quasicoherentPushforward f ⋙ ObjectProperty.ι P₂) :=
      preservesColimitsOfShape_walkingParallelPair_iota_pushforward f
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (quasicoherentPushforward f) (ObjectProperty.ι P₂)
  have : PreservesFiniteCoproducts (quasicoherentPushforward f) := by
    refine ⟨fun n => ?_⟩
    have : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin n)))
        (quasicoherentPushforward f) :=
      preservesColimitsOfShape_discrete_quasicoherentPushforward f (ULift.{u} (Fin n))
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  exact preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    (quasicoherentPushforward f)

end Pushforward

/-! ### Morphisms with affine source -/

section Source

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))

/-- The source of a morphism to `X`, regarded as a scheme over `R` through that morphism. -/
def sourceOver {X' : Scheme.{u}} (f : X' ⟶ X.left) : Over (Spec (.of R)) :=
  Over.mk (f ≫ X.hom)

/-- A morphism to `X`, regarded as a morphism of schemes over `R`. -/
def sourceOverHom {X' : Scheme.{u}} (f : X' ⟶ X.left) : sourceOver R X f ⟶ X :=
  Over.homMk f

/-- The underlying morphism of schemes of `sourceOverHom R X f` is `f`. -/
@[simp]
theorem sourceOverHom_left {X' : Scheme.{u}} (f : X' ⟶ X.left) :
    (sourceOverHom R X f).left = f := rfl

/-- The underlying scheme of `sourceOver R X f` is the source `X'` of `f`. -/
@[simp]
theorem sourceOver_left {X' : Scheme.{u}} (f : X' ⟶ X.left) :
    (sourceOver R X f).left = X' := rfl

/-- An open immersion, regarded as a morphism of schemes over `R`, is an open immersion. -/
theorem isOpenImmersion_sourceOverHom_left {X' : Scheme.{u}} (f : X' ⟶ X.left)
    [IsOpenImmersion f] : IsOpenImmersion (sourceOverHom R X f).left :=
  inferInstanceAs (IsOpenImmersion f)

/-- A morphism of schemes over `R` with affine source into a scheme with affine diagonal is an
affine morphism. -/
theorem isAffineHom_left_of_isAffine_left {X' : Over (Spec (.of R))} [IsAffine X'.left]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))] (f : X' ⟶ X) :
    IsAffineHom f.left :=
  Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source f.left

end Source

/-! ### The kernel attached to a morphism with affine source -/

section AffineSource

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- Additivity, linearity and preservation of direct sums by `F`, together with right exactness of
`F ∘ f_*`, give the properties of `F ∘ f_*` for a morphism `f` with affine source. -/
private theorem rightExactLinearCoproductFunctor_comp_quasicoherentPushforward_aux
    (hF : letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
      letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
      F.Additive ∧ F.Linear R)
    (hFsum : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F)
    {X' : Over (Spec (.of R))} [IsAffine X'.left] (f : X' ⟶ X)
    (hrex : letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
      PreservesFiniteColimits (quasicoherentPushforward f.left ⋙ F)) :
    letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
    rightExactLinearCoproductFunctor R X' Y (quasicoherentPushforward f.left ⋙ F) := by
  have : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  have := hrex
  let : Linear R (SheafOfModules.{u} X'.left.ringCatSheaf) := modulesLinear R X'
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
  let : Linear R X'.left.Modules := modulesLinear R X'
  let : Linear R X.left.Modules := modulesLinear R X
  let : Linear R Y.left.Modules := modulesLinear R Y
  obtain ⟨hFadd, hFlin⟩ := hF
  have : (quasicoherentPushforward f.left).Linear R :=
    quasicoherentPushforward_linear R f
  refine ⟨⟨inferInstance, inferInstance⟩, inferInstance, fun I => ?_⟩
  have := hFsum I
  have : PreservesColimitsOfShape (Discrete I) (quasicoherentPushforward f.left) :=
    preservesColimitsOfShape_discrete_quasicoherentPushforward f.left I
  exact inferInstanceAs
    (PreservesColimitsOfShape (Discrete I) (quasicoherentPushforward f.left ⋙ F))

/-- **`F ∘ f_*` is again `R`-linear, right exact and commuting with arbitrary direct sums**, for
every morphism `f` to `X` whose source is an affine scheme. -/
theorem rightExactLinearCoproductFunctor_comp_quasicoherentPushforward
    (hF : rightExactLinearCoproductFunctor R X Y F) {X' : Over (Spec (.of R))}
    [IsAffine X'.left] (f : X' ⟶ X) :
    letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
    rightExactLinearCoproductFunctor R X' Y (quasicoherentPushforward f.left ⋙ F) := by
  have : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  have := hF.2.1
  have : PreservesFiniteColimits (quasicoherentPushforward f.left) :=
    preservesFiniteColimits_quasicoherentPushforward f.left
  exact rightExactLinearCoproductFunctor_comp_quasicoherentPushforward_aux R X Y F hF.1 hF.2.2 f
    inferInstance

/-- The property of a functor between quasi-coherent module categories of being `R`-linear,
commuting with arbitrary direct sums, and right exact after direct image along every open
immersion of schemes over `R` whose source is affine.  This is all the construction of the
kernel of Tag 0GPA uses: it only ever evaluates the functor on direct images from affine opens.
A right exact functor has the property
(`AlgebraicGeometry.affineOpenRightExactLinearCoproductFunctor_of_rightExact`). -/
def affineOpenRightExactLinearCoproductFunctor :
    ObjectProperty
      ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory) :=
  fun F =>
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
    (F.Additive ∧ F.Linear R) ∧
      (∀ ⦃X' : Over (Spec (.of R))⦄ [IsAffine X'.left] (f : X' ⟶ X) [IsOpenImmersion f.left],
        letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
        PreservesFiniteColimits (quasicoherentPushforward f.left ⋙ F)) ∧
      ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F

/-- A right exact functor is right exact after direct image along a morphism with affine
source. -/
theorem affineOpenRightExactLinearCoproductFunctor_of_rightExact
    (hF : rightExactLinearCoproductFunctor R X Y F) :
    affineOpenRightExactLinearCoproductFunctor R X Y F :=
  ⟨hF.1, fun _ _ f _ =>
    (rightExactLinearCoproductFunctor_comp_quasicoherentPushforward R X Y F hF f).2.1, hF.2.2⟩

/-- **`F ∘ f_*` is `R`-linear, right exact and commuting with arbitrary direct sums** for an
open immersion `f` with affine source, as soon as `F` has the property
`AlgebraicGeometry.affineOpenRightExactLinearCoproductFunctor`. -/
theorem rightExactLinearCoproductFunctor_comp_quasicoherentPushforward_of_isOpenImmersion
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F) {X' : Over (Spec (.of R))}
    [IsAffine X'.left] (f : X' ⟶ X) [IsOpenImmersion f.left] :
    letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
    rightExactLinearCoproductFunctor R X' Y (quasicoherentPushforward f.left ⋙ F) := by
  have : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  exact rightExactLinearCoproductFunctor_comp_quasicoherentPushforward_aux R X Y F hF.1 hF.2.2 f
    (hF.2.1 f)

/-- A composite of open immersions over a base is an open immersion.  Not a global instance:
it matches the underlying morphism of every composite in an over category. -/
theorem isOpenImmersion_over_comp_left {S : Scheme.{u}} {A B C : Over S} (f : A ⟶ B)
    (g : B ⟶ C) [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion (f ≫ g).left :=
  IsOpenImmersion.comp f.left g.left

attribute [local instance] isOpenImmersion_over_comp_left

/-- **The kernel of `F ∘ f_*`.**  For an open immersion `f : X' ⟶ X` of schemes over `R` with
`X'` affine, the quasi-coherent module on `X' ×_R Y` whose integral transform is `F ∘ f_*`,
taken from the inverse of the equivalence of Tag 0FZD. -/
def affineSourceKernel (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X' : Over (Spec (.of R))} [IsAffine X'.left] (f : X' ⟶ X) [IsOpenImmersion f.left] :
    Scheme.QuasicoherentModules (pullback X'.hom Y.hom) :=
  letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  (integralTransformQcohEquivalence R X' Y).inverse.obj
    ⟨quasicoherentPushforward f.left ⋙ F,
      rightExactLinearCoproductFunctor_comp_quasicoherentPushforward_of_isOpenImmersion
        R X Y F hF f⟩

/-- **`F ∘ f_*` is the integral transform of `AlgebraicGeometry.affineSourceKernel`.**  This is
the counit of the equivalence of Tag 0FZD at `F ∘ f_*`, read through the inclusion of the
`R`-linear right exact direct-sum-preserving functors. -/
def affineSourceKernelIso (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X' : Over (Spec (.of R))} [IsAffine X'.left] (f : X' ⟶ X) [IsOpenImmersion f.left] :
    letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
    quasicoherentPushforward f.left ⋙ F ≅
      quasicoherentIntegralTransform R X' Y (affineSourceKernel R X Y F hF f) :=
  letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  ((ObjectProperty.ι (rightExactLinearCoproductFunctor R X' Y)).mapIso
    ((integralTransformQcohEquivalence R X' Y).counitIso.app
      ⟨quasicoherentPushforward f.left ⋙ F,
        rightExactLinearCoproductFunctor_comp_quasicoherentPushforward_of_isOpenImmersion
          R X Y F hF f⟩)).symm

/-- **A kernel with affine source is determined by its integral transform.**  The functor of
Tag 0FZD is fully faithful, so an isomorphism of integral transforms on an affine source comes
from an isomorphism of kernels. -/
def kernelIsoOfIntegralTransformIso [IsAffine X.left]
    {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}
    (e : quasicoherentIntegralTransform R X Y K ≅ quasicoherentIntegralTransform R X Y L) :
    K ≅ L :=
  haveI : (integralTransformQcohFunctorLift R X Y).Full :=
    full_integralTransformQcohFunctorLift R X Y
  haveI : (integralTransformQcohFunctorLift R X Y).Faithful :=
    faithful_integralTransformQcohFunctorLift R X Y
  (Functor.FullyFaithful.ofFullyFaithful (integralTransformQcohFunctorLift R X Y)).preimageIso
    (ObjectProperty.isoMk _ e)

end AffineSource

/-! ### Compatibility of the kernels under a further affine change of source -/

section Compatibility

attribute [local instance] isOpenImmersion_over_comp_left

variable (R : Type u) [CommRing R]

/-- Direct image on quasi-coherent modules composes. -/
def quasicoherentPushforwardComp {Z Z' Z'' : Scheme.{u}} (f : Z'' ⟶ Z') (g : Z' ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)] :
    quasicoherentPushforward f ⋙ quasicoherentPushforward g ≅
      quasicoherentPushforward (f ≫ g) :=
  ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent Z''.ringCatSheaf).ι
      (Scheme.Modules.pushforwardComp f g))

variable (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- **The kernel of `F ∘ (g ≫ f)_*` is the inverse image of the kernel of `F ∘ f_*`.**  For
morphisms `g : X'' ⟶ X'` and `f : X' ⟶ X` of schemes over `R` with `X'` and `X''` affine,
`(g × id_Y)^*` carries the kernel attached to `f` to the kernel attached to `g ≫ f`.  This is
the compatibility of Tag 0FZF, read through the kernels of
`AlgebraicGeometry.affineSourceKernel`. -/
def affineSourceKernelSourceChangeIso (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X' X'' : Over (Spec (.of R))} [IsAffine X'.left] [IsAffine X''.left] (f : X' ⟶ X)
    (g : X'' ⟶ X') [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    sourceChangeKernel R X' X'' Y g (affineSourceKernel R X Y F hF f) ≅
      affineSourceKernel R X Y F hF (g ≫ f) :=
  letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  letI : IsAffineHom (g ≫ f).left := isAffineHom_left_of_isAffine_left R X (g ≫ f)
  kernelIsoOfIntegralTransformIso R X'' Y
    ((quasicoherentIntegralTransformSourceChangeIso R X' X'' Y g
          (affineSourceKernel R X Y F hF f)).symm ≪≫
      Functor.isoWhiskerLeft (quasicoherentPushforward g.left)
        (affineSourceKernelIso R X Y F hF f).symm ≪≫
      Functor.isoWhiskerRight
        (quasicoherentPushforwardComp g.left f.left) F ≪≫
      affineSourceKernelIso R X Y F hF (g ≫ f))

/-- **Equal open immersions have the same kernel.**  The open-immersion instance is part of
the data of `AlgebraicGeometry.affineSourceKernel`, so a transport along an equality of
morphisms has to carry it along. -/
theorem affineSourceKernel_congr (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X' : Over (Spec (.of R))} [IsAffine X'.left] {f f' : X' ⟶ X} [IsOpenImmersion f.left]
    [IsOpenImmersion f'.left] (h : f = f') :
    affineSourceKernel R X Y F hF f = affineSourceKernel R X Y F hF f' := by
  subst h
  rfl

end Compatibility

end AlgebraicGeometry

end
