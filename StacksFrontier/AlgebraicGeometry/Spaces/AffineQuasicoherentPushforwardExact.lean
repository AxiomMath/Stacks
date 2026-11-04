module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections

/-!
# Direct image along an affine morphism of algebraic spaces is exact on quasi-coherent modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`.
Granted that the direct image preserves quasi-coherence it restricts to
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` (`AlgebraicGeometry.Space.quasicoherentPushforward`), and this
file proves that restriction exact and reads the induced functor of unbounded derived categories
as a total right derived functor of it.

Left exactness is free and carries no hypothesis: the inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is
exact and reflects isomorphisms, and `f_*` on all modules is a right adjoint.  Right exactness is
the geometric half.  It is reduced here to one input, right acyclicity of the quasi-coherent
modules for the direct image of all modules: with that, the short exact sequence
`0 ⟶ ker φ ⟶ A ⟶ C ⟶ 0` attached to an epimorphism `φ` of `QCoh(𝒪_X)` has quasi-coherent kernel
— quasi-coherence on an algebraic space is closed under kernels, unconditionally — so
[Stacks, Tag 015D] in the form
`CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact` makes its image under
`f_*` short exact, which is the epimorphy wanted.  An exact functor induces a functor of
unbounded derived categories with no derivation, and a lift through the localization of a functor
inverting the quasi-isomorphisms is a total right derived functor.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentPushforward` — direct image on
  quasi-coherent modules is left exact, unconditionally.
* `AlgebraicGeometry.Space.preservesEpimorphisms_quasicoherentPushforward_of_rightAcyclic` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentPushforward_of_rightAcyclic` —
  right exactness, granted the acyclicity input.
* `AlgebraicGeometry.Space.isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory` —
  the induced functor `D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` *is* a total right derived functor of `f_*`.
* `AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentPushforward_of_isAffineHom` and
  its derived-functor companion
  `isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory_of_isAffineHom` — the same
  for an affine morphism, where the preservation of quasi-coherence is supplied by
  `AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_isAffineHom`.

## Implementation notes

**No `stacks` attribute here.**  Tag 08GY is the assertion for an affine morphism of algebraic
spaces, and the acyclicity hypothesis `hac` of the statements below is still an open input of
this file; a separate file registers Tag 08GY once that input is discharged.

**The acyclicity hypothesis is not a restatement of the conclusion.**  It is the vanishing
`R^p f_* 𝓕 = 0` for `p > 0` and `𝓕` quasi-coherent, a statement about the direct image of *all*
modules, which for an affine morphism is the algebraic-spaces form of [Stacks, Tag 01XC]; the
conclusion is right exactness of the restriction to the quasi-coherent modules.

**Local priority raises.**  As in the neighbouring files on the small étale modules of an
algebraic space, `SheafOfModules.instAbelian` is raised and the two universe-pinned instances
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules` and
`AlgebraicGeometry.Space.enoughInjectives_modules` are made local, so that the homological
instances on the modules are found at module universe `u` rather than at the
`max u v r w` spelling of the general site machinery.  `HasDerivedCategory.standard` is local for
the same reason it is in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedComparison.lean`: a free
`HasDerivedCategory` binder on the quasi-coherent modules does not elaborate against the `Abelian`
instance that is itself derived from the closure properties.

## References

* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules

/-! ### Left exactness -/

/-- **Direct image is left exact on quasi-coherent modules.**  The inclusion
`ι : QCoh(𝒪_Y) ⥤ Mod(𝒪_Y)` is left exact and reflects isomorphisms, so left exactness of the
restriction is inherited from the direct image of all modules, which is a right adjoint
(`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`) and hence preserves every limit it
can.

No hypothesis beyond the preservation of quasi-coherence that makes the restriction exist is
needed. -/
instance preservesFiniteLimits_quasicoherentPushforward (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    PreservesFiniteLimits (quasicoherentPushforward B S hS f hpush) := by
  have : PreservesLimitsOfSize.{0, 0} (modulePushforward B S hS f) :=
    (modulePullbackAdjunction B S hS f).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (modulePushforward B S hS f) := inferInstance
  have : PreservesFiniteLimits
      (quasicoherentPushforward B S hS f hpush ⋙ quasicoherentSheavesι B S hS Y) :=
    preservesFiniteLimits_of_natIso
      (quasicoherentPushforwardCompιIso B S hS f hpush).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS Y)

/-! ### Right exactness -/

/-- **Direct image carries an epimorphism of quasi-coherent modules to an epimorphism**, granted
`hac`: that every quasi-coherent `𝒪_X`-module is right acyclic for the direct image of all
`𝒪_X`-modules.

The inclusion of the quasi-coherent modules is exact and fully faithful, so an epimorphism of
`QCoh(𝒪_X)` is an epimorphism of `Mod(𝒪_X)` between quasi-coherent modules and conversely.  In
between, the kernel of that epimorphism is quasi-coherent by the kernel clause of
[Stacks, Tag 03M1], part (3), on an algebraic space
(`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_algebraicSpace`), so `hac`
makes both the kernel and the source right acyclic, and [Stacks, Tag 015D] in the form
`CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact` makes the image of the
short exact sequence short exact. -/
theorem preservesEpimorphisms_quasicoherentPushforward_of_rightAcyclic (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f)
    (hac : ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
      (modulePushforward B S hS f).rightAcyclic M) :
    (quasicoherentPushforward B S hS f hpush).PreservesEpimorphisms := by
  constructor
  intro A C φ _
  have : Epi φ.hom := (quasicoherentSheavesι B S hS X).map_epi φ
  have hK : (kernel φ.hom).IsQuasicoherentOnSite :=
    ObjectProperty.prop_kernel (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      φ.hom A.property C.property
  have hT : (ShortComplex.mk (kernel.ι φ.hom) φ.hom (by simp)).ShortExact :=
    { exact := ShortComplex.exact_kernel φ.hom }
  have h := (Functor.rightAcyclic_and_shortExact_map_of_shortExact
    (modulePushforward B S hS f) _ hT).2.1 (hac _ hK) (hac _ A.property)
  exact (quasicoherentSheavesι B S hS Y).epi_of_epi_map
    (f := (quasicoherentPushforward B S hS f hpush).map φ) h.2.epi_g

/-- **Direct image is right exact on quasi-coherent modules**, granted the acyclicity input
`hac`.  It is left exact by
`AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentPushforward` and preserves
epimorphisms by
`AlgebraicGeometry.Space.preservesEpimorphisms_quasicoherentPushforward_of_rightAcyclic`, hence
preserves homology, hence preserves finite colimits. -/
theorem preservesFiniteColimits_quasicoherentPushforward_of_rightAcyclic (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f)
    (hac : ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
      (modulePushforward B S hS f).rightAcyclic M) :
    PreservesFiniteColimits (quasicoherentPushforward B S hS f hpush) := by
  have := preservesEpimorphisms_quasicoherentPushforward_of_rightAcyclic B S hS f hpush hac
  have : (quasicoherentPushforward B S hS f hpush).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-! ### The induced functor on unbounded derived categories -/

/-- **Direct image on quasi-coherent modules defines a derived functor
`D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`**, granted the acyclicity input `hac`: the functor induced on
unbounded derived categories by the exact functor
`AlgebraicGeometry.Space.quasicoherentPushforward`, namely
`CategoryTheory.Functor.mapDerivedCategory`, is a total right derived functor of it, so no
resolutions are involved and the derived functor is computed by applying `f_*` to a representative
complex.

The structure map is `CategoryTheory.Functor.mapDerivedCategoryFactorsh.inv`, which exhibits the
induced functor as a lift through the localization `DerivedCategory.Qh`; a lift of a functor that
inverts the quasi-isomorphisms is a right derived functor for the inverse of the lifting
isomorphism. -/
theorem isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f)
    (hac : ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
      (modulePushforward B S hS f).rightAcyclic M) :
    letI := preservesFiniteColimits_quasicoherentPushforward_of_rightAcyclic B S hS f hpush hac
    (quasicoherentPushforward B S hS f hpush).mapDerivedCategory.IsRightDerivedFunctor
      (quasicoherentPushforward B S hS f hpush).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)) :=
  let := preservesFiniteColimits_quasicoherentPushforward_of_rightAcyclic B S hS f hpush hac
  Functor.isRightDerivedFunctor_of_inverts _ _
    (quasicoherentPushforward B S hS f hpush).mapDerivedCategoryFactorsh

/-! ### An affine morphism -/

/-- **Direct image along an affine morphism of algebraic spaces is right exact on quasi-coherent
modules**, granted the acyclicity input `hac`.

This is `AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentPushforward_of_rightAcyclic`
with its preservation of quasi-coherence supplied by the quasi-coherence assertion of
[Stacks, Tag 07U8],
`AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_isAffineHom`. -/
theorem preservesFiniteColimits_quasicoherentPushforward_of_isAffineHom (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom)
    (hac : ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
      (modulePushforward B S hS f).rightAcyclic M) :
    PreservesFiniteColimits (quasicoherentPushforward B S hS f
      (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf)) :=
  preservesFiniteColimits_quasicoherentPushforward_of_rightAcyclic B S hS f
    (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf) hac

/-- **Direct image along an affine morphism of algebraic spaces defines a derived functor
`D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`**, granted the acyclicity input `hac`.

This is
`AlgebraicGeometry.Space.isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory` with
its preservation of quasi-coherence supplied by the quasi-coherence assertion of
[Stacks, Tag 07U8],
`AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_isAffineHom`. -/
theorem isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory_of_isAffineHom
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hac : ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
      (modulePushforward B S hS f).rightAcyclic M) :
    letI := preservesFiniteColimits_quasicoherentPushforward_of_isAffineHom B S hS f hf hac
    Functor.IsRightDerivedFunctor
      (quasicoherentPushforward B S hS f
        (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf)).mapDerivedCategory
      (quasicoherentPushforward B S hS f
          (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f
            hf)).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory B S hS f
    (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf) hac

end AlgebraicGeometry.Space

end
