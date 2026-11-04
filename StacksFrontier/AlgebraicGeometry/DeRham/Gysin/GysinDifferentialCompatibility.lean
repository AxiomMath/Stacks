module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two spellings of `i_*ℋ ᶜ_Z` and functoriality of the class map in them

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = d + 1`, let `T ⊆ X` be a closed
subset containing their common zero locus, and let `ℱ` be a quasi-coherent `𝒪_X`-module. The
direct image on `X` of the degree-`c` local cohomology sheaf of `ℱ` along `T` can be formed in two
ways:

* `Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT ℱ c`, the degree-`c` cohomology
  sheaf of `i_* R𝓗_T(ℱ[0])`, with the cohomology taken after the direct image;
* `AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f ℱ`, the direct image of the
  degree-`c` cohomology sheaf of `R𝓗_Z(ℱ[0])`, with the cohomology taken before the direct image;
  this is the target of the Gysin map `AlgebraicGeometry.Scheme.Hom.gysinMap`.

This file identifies the two, naturally in the coefficient module, using the exactness of the
direct image along the inclusion of a closed subset ([Stacks, Tag 08KS]), and expresses the
functoriality of the class map of [Stacks, Tag 0G7T] in the second form.

## Main definitions

* `Stacks.Perfect.GysinLocalCohomology.localCohomologyPushforwardFunctor`: the functor
  `ℱ ↦ i_*ℋ ᶜ_T(ℱ)`, with the cohomology sheaf taken before the direct image.
* `Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`: the natural isomorphism
  between the two forms.
* `Stacks.Perfect.GysinLocalCohomology.gysinTargetIso`: the same isomorphism at a single module,
  with source `AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology`.
* `Stacks.Perfect.GysinLocalCohomology.supportedFractionSourcePush`: the class map
  `ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` of [Stacks, Tag 0G7Q] with its target in the second form.
* `Stacks.Perfect.GysinLocalCohomology.fractionClassPushTrans`: the natural transformation of
  [Stacks, Tag 0G7Q] with its target in the second form, so that the target functor is `i_*`
  composed with `ℱ ↦ ℋ ᶜ_Z(ℱ)`.
* `Stacks.Perfect.GysinLocalCohomology.fractionClassOnClosed`: the canonical `𝒪_X|_Z`-linear map
  `c_{f₁, …, f_c} : i^*ℱ ⟶ ℋ ᶜ_Z(ℱ)` on `Z`, as a natural transformation of functors of the
  `𝒪_X`-module `ℱ` into `𝒪_X|_Z`-modules.

## Main results

* `Stacks.Perfect.GysinLocalCohomology.localCohomologyPushforwardFunctor_obj` and
  `localCohomologyPushforwardFunctor_obj_gysin`: the values of the functor, in particular
  `AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology`.
* `Stacks.Perfect.GysinLocalCohomology.supportedFractionSourcePush_natural`: the functoriality in
  `ℱ` of the class map of [Stacks, Tag 0G7T], with its target in the second form.
* `Stacks.Perfect.GysinLocalCohomology.homEquiv_fractionClassOnClosed_app`: the transpose of the
  component of `fractionClassOnClosed` is the component of `fractionClassPushTrans`.

## References

* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Perfect.GysinLocalCohomology

attribute [local instance 10000] HasDerivedCategory.standard

/-- Sheaves of modules on a ringed space form an abelian category, in the spelling that unfolds
`structureSheafRing`. -/
local instance abelian_sheafOfModules_ringSheaf (Y : RingedSpace.{u, u}) :
    Abelian (_root_.SheafOfModules.{u} (structureSheafRing Y)) :=
  _root_.SheafOfModules.instAbelian _

/-- The direct image of modules along a morphism of ringed spaces is additive, in the spelling
that unfolds `structureSheafRing`. -/
local instance additive_modulePushforward {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z) :
    (modulePushforward g).Additive :=
  RingedSpaceModuleAdjunction.modulePushforward_additive g

variable {X : Scheme.{u}}

/-! ### The Gysin map's spelling of the local cohomology sheaf, as a functor -/

/-- The functor `ℱ ↦ i_*ℋ ᵖ_T(ℱ)` of the coefficient module, with the cohomology sheaf taken
before the direct image: the module placed in degree `0`, its derived sections supported on the
closed subset `T`, the degree-`p` cohomology sheaf of the result, and the direct image from `T`
to `X`. -/
@[sga "4 V 6.3" "special case"]
public def localCohomologyPushforwardFunctor {T : Set X} (hT : IsClosed T) (p : ℤ) :
    X.Modules ⥤ X.Modules :=
  DerivedCategory.singleFunctor X.Modules 0 ⋙
    derivedSupportedSectionsOnClosed X.toRingedSpace T hT ⋙
      DerivedCategory.homologyFunctor _ p ⋙
        modulePushforward (closedSubsetInclusion X.toRingedSpace T)

/-- The functor evaluates to the direct image of the degree-`p` local cohomology sheaf of the
module placed in degree `0`. -/
public theorem localCohomologyPushforwardFunctor_obj {T : Set X} (hT : IsClosed T) (p : ℤ)
    (F : X.Modules) :
    (localCohomologyPushforwardFunctor hT p).obj F =
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).obj
        (localCohomologySheafOfComplex X.toRingedSpace T hT p
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := rfl

/-- At the common zero locus of a nonempty family of equations and in the degree equal to their
number, the functor evaluates to the target of the Gysin map,
`AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology`. -/
public theorem localCohomologyPushforwardFunctor_obj_gysin {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) :
    (localCohomologyPushforwardFunctor (isClosed_equationsClosedSet f)
        ((d + 1 : ℕ) : ℤ)).obj F =
      AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f F := rfl

/-! ### The two spellings agree -/

/-- The natural isomorphism, in the coefficient module `ℱ`, between pushing forward from `T` the
degree-`p` cohomology sheaf of `R𝓗_T(ℱ[0])` and taking the degree-`p` cohomology sheaf on `X` of
its direct image. -/
public def supportCohomologySheafFunctorIso {T : Set X} (hT : IsClosed T) (p : ℤ) :
    supportCohomologySheafFunctor hT p ≅ localCohomologyPushforwardFunctor hT p :=
  letI := pushforward_preservesFiniteLimits X.toRingedSpace T
  letI := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  Functor.isoWhiskerLeft
    (DerivedCategory.singleFunctor X.Modules 0 ⋙
      derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
    (exactFunctorDerivedHomologyIso
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T)) p)

/-- The isomorphism between the target of the Gysin map and the target of the class map of
[Stacks, Tag 0G7Q], at the common zero locus of the equations and in the degree equal to their
number: the component of `supportCohomologySheafFunctorIso` at a single module. -/
public def gysinTargetIso {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) :
    AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f F ≅
      supportCohomologySheaf (isClosed_equationsClosedSet f) F ((d + 1 : ℕ) : ℤ) :=
  ((supportCohomologySheafFunctorIso (isClosed_equationsClosedSet f)
    ((d + 1 : ℕ) : ℤ)).app F).symm

/-! ### Functoriality of the class map in the Gysin map's spelling -/

/-- The class map `c_{f₁,…,f_c} : ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` of [Stacks, Tag 0G7Q], with the cohomology
sheaf of its target taken before the direct image: `supportedFractionSource` followed by
`supportCohomologySheafFunctorIso`. -/
public def supportedFractionSourcePush {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)
    [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    F ⟶ (localCohomologyPushforwardFunctor hT ((d + 1 : ℕ) : ℤ)).obj F :=
  supportedFractionSource f F hT hTf ≫
    (supportCohomologySheafFunctorIso hT ((d + 1 : ℕ) : ℤ)).hom.app F

/-- The class map `supportedFractionSourcePush` into `i_*ℋ ᶜ_T(ℱ)` is natural in morphisms
`φ : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules ([Stacks, Tag 0G7T]). -/
public theorem supportedFractionSourcePush_natural {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    φ ≫ supportedFractionSourcePush f G hT hTf =
      supportedFractionSourcePush f F hT hTf ≫
        (localCohomologyPushforwardFunctor hT ((d + 1 : ℕ) : ℤ)).map φ := by
  rw [supportedFractionSourcePush, supportedFractionSourcePush]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫
      (supportCohomologySheafFunctorIso hT ((d + 1 : ℕ) : ℤ)).hom.app G)
    (supportedFractionSource_natural f φ hT hTf)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun ψ => supportedFractionSource f F hT hTf ≫ ψ)
    ((supportCohomologySheafFunctorIso hT ((d + 1 : ℕ) : ℤ)).hom.naturality φ)) ?_
  exact (Category.assoc _ _ _).symm

/-! ### The class map on the closed subscheme -/

/-- The natural transformation `Stacks.Perfect.SupportedFraction.fractionClassTrans` of
[Stacks, Tag 0G7Q] followed by `supportCohomologySheafFunctorIso`, so that its target functor is
`i_*` composed with `ℱ ↦ ℋ^c_Z(ℱ)`. -/
public def fractionClassPushTrans {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) :
    equationsQuotientFunctor f ⟶
      localCohomologyPushforwardFunctor (isClosed_equationsClosedSet f) ((d + 1 : ℕ) : ℤ) :=
  fractionClassTrans f ≫
    (supportCohomologySheafFunctorIso (isClosed_equationsClosedSet f) ((d + 1 : ℕ) : ℤ)).hom

/-- With `X` a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `Z ⊆ X` the closed subscheme they cut out,
the canonical map `c_{f₁, …, f_c} : i^*ℱ ⟶ ℋ^c_Z(ℱ)` of `𝒪_X|_Z`-modules on `Z`, as a natural
transformation of functors of the `𝒪_X`-module `ℱ`: from `ℱ ↦ i^*(ℱ/(f₁, …, f_c)ℱ)`, the inverse
image along the inclusion of `Z` of the cokernel of `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, to
`ℱ ↦ ℋ^c_Z(ℱ)`. Its component at `ℱ` is the transpose under `i^* ⊣ i_*` of the component of
`fractionClassPushTrans`. -/
@[stacks 0G7Q "the remark's conclusion: the canonical O_X|_Z-linear map c_{f₁,…,f_c} : i^*ℱ ⟶ \
ℋ^c_Z(ℱ) on Z, together with its functoriality in the 𝒪_X-module ℱ, as a natural transformation \
of the two functors of ℱ into 𝒪_X|_Z-modules; obtained from the transformation on X by the \
remark's last step, the transposition along i^* ⊣ i_* that full faithfulness of i_* provides"]
public def fractionClassOnClosed {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) :
    equationsQuotientFunctor f ⋙
        modulePullback (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)) ⟶
      DerivedCategory.singleFunctor X.Modules 0 ⋙
        derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
            (isClosed_equationsClosedSet f) ⋙
          DerivedCategory.homologyFunctor _ ((d + 1 : ℕ) : ℤ) where
  app F := (homEquiv (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)) _ _).symm
    ((fractionClassPushTrans f).app F)
  naturality F G φ := by
    refine Eq.trans (Adjunction.homEquiv_naturality_left_symm
      (modulePullbackPushforwardAdjunction
        (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)))
      ((equationsQuotientFunctor f).map φ) ((fractionClassPushTrans f).app G)).symm ?_
    refine Eq.trans (congrArg (homEquiv (closedSubsetInclusion X.toRingedSpace
      (equationsClosedSet f)) _ _).symm ((fractionClassPushTrans f).naturality φ)) ?_
    exact Adjunction.homEquiv_naturality_right_symm _ _ _

/-- The transpose under `i^* ⊣ i_*` of the component of `fractionClassOnClosed` at `ℱ` is the
component of `fractionClassPushTrans` at `ℱ`, with source and target written as in
`Stacks.Perfect.FractionClass.fractionClass f ℱ`. -/
public theorem homEquiv_fractionClassOnClosed_app {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) :
    homEquiv (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))
        (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f) ((d + 1 : ℕ) : ℤ)
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))
        (Stacks.Perfect.FractionClass.equationsQuotient f F)
        ((fractionClassOnClosed f).app F) =
      (fractionClassPushTrans f).app F :=
  Equiv.apply_symm_apply _ _

end Stacks.Perfect.GysinLocalCohomology

end
