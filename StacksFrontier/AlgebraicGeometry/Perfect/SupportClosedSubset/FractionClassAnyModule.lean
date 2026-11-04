module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinClassMapToSupportLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetDegreewise

/-!
# The class map of Tag 0G7Q for an arbitrary `𝒪_X`-module

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, let `Z` be their common zero locus and let
`T ⊆ X` be a closed subset containing `Z`.  [Stacks, Tag 0G7Q] gives, for **every** `𝒪_X`-module
`ℱ`, a canonical `𝒪_X|_T`-linear map

`c_{f₁, …, f_c} : i^*(ℱ/(f₁, …, f_c)ℱ) ⟶ ℋ ᶜ_T(ℱ)`

functorial in `ℱ`.  The remark needs only the comparison `ℱ^• ⟶ i_* R𝓗_T(ℱ)` of
[Stacks, Tag 0G7L], which holds for an arbitrary `𝒪_X`-module; quasi-coherence enters the source
only one tag later, at [Stacks, Tag 0G7M], where that comparison is shown to be *invertible*.
The map itself needs no such thing.

`Stacks.Perfect.FractionClass.fractionClass` builds the same map through [Stacks, Tag 0G7M] and
therefore carries `[ℱ.IsQuasicoherent]`.  This file builds it through [Stacks, Tag 0G7L] alone,
for an arbitrary `X.Modules`, and `fractionClassAnyModule_eq` records that on a quasi-coherent
module the two agree, so the earlier construction is the present one specialised.

## Main definitions

* `Stacks.Perfect.FractionClass.classMapToPushforward`: the class map read on the coefficient
  module, with values in `i_*ℋ ᶜ_T(ℱ)` taken in the spelling with the direct image outside.
* `Stacks.Perfect.FractionClass.equationsQuotientMap`: the map `ℱ/(f)ℱ ⟶ 𝒢/(f)𝒢` induced by a
  morphism `ℱ ⟶ 𝒢`, making the source of the class map a functor of the coefficient module.
* `Stacks.Perfect.FractionClass.quotientClassMapToPushforward`: **the `𝒪_X`-module map
  `i_*i^*ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` of [Stacks, Tag 0G7Q]**, for an arbitrary `𝒪_X`-module.
* `Stacks.Perfect.FractionClass.fractionClassAnyModule`: **the map `c_{f₁, …, f_c}` itself**, its
  transpose along `i^* ⊣ i_*`, for an arbitrary `𝒪_X`-module.

## Main results

* `Stacks.Perfect.FractionClass.fracTermTop_naturality`: the fraction `s / (f₁ ⋯ f_c)` in the top
  term of the extended alternating Čech complex is natural in the coefficient module, for **any**
  number of equations.  This discharges, at every `c`, the hypothesis that
  `Stacks.Gysin.classMap_naturality` and `Stacks.Gysin.classMapToSupport_naturality` carry.
* `Stacks.Perfect.FractionClass.classMapToSupport_natural`: **[Stacks, Tag 0G7T] for an arbitrary
  `𝒪_X`-module** — `Stacks.Gysin.classMapToSupport_naturality` with the quasi-coherence of the two
  coefficient modules removed, which that statement names and its proof does not use.
* `Stacks.Perfect.FractionClass.classMapToPushforward_natural`,
  `quotientClassMapToPushforward_natural` and `fractionClassAnyModule_natural`: **the
  functoriality in `ℱ` asserted by [Stacks, Tag 0G7Q]**, on the coefficient module, on the
  quotient by the equations, and on `c_{f₁, …, f_c}` itself.
* `Stacks.Perfect.FractionClass.quotientClassMapToPushforward_eq` and
  `fractionClassAnyModule_eq`: on a quasi-coherent module the maps built here are the maps
  `pushforwardFractionClass` and `fractionClass` built through [Stacks, Tag 0G7M].

## Implementation notes

**No hypothesis beyond the remark's.**  Every declaration below takes an arbitrary `X.Modules`,
an arbitrary number of equations, zero included, and an arbitrary closed subset containing their
zero locus — the only exceptions being the last two, which compare the construction with the
quasi-coherent one and so name quasi-coherence in order to speak about it.  The ingredients were
already general:

* `Stacks.Perfect.FractionClass.classMapToSupport` — the fraction class in the degree-`c`
  cohomology sheaf of the extended alternating Čech complex, carried into `i_*ℋ ᶜ_T(ℱ)` by the
  comparison of [Stacks, Tag 0G7L];
* `Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso` — the two places at
  which the degree-`c` cohomology sheaf may be taken agree, the direct image from a closed subset
  being exact;
* `Stacks.Perfect.FractionClass.equationsMap_comp_classMap` — the fraction class kills the image
  of `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, which is what makes it descend to the quotient.

What was missing was the naturality of the numerator at a *nonempty* family of equations, and
with it the hypothesis-free form of `Stacks.Gysin.classMapToSupport_naturality`: `fracTermTop` is
defined by cases on the number of equations, so its naturality has two cases with nothing in
common.  For `c = 0` the fraction is the identity of the coefficient module and the case was
already available as `Stacks.Gysin.fracTermTop_naturality_zero`; for `c = n + 1` it is
`Stacks.Perfect.SupportedFraction.fractionHom_naturality` transported along
`Stacks.Perfect.GysinFractionDeRham.fracTerm_eq_fractionHom`, which is
`fracTermTop_naturality_succ` below.

The second thing missing was the naturality of the class map at an arbitrary coefficient module:
`Stacks.Gysin.classMapToSupport_naturality` names `[ℱ.IsQuasicoherent]` and `[𝒢.IsQuasicoherent]`
without using either, and restating it is not an option — that declaration is depended upon as it
stands.  `classMapToSupport_natural` below is the same statement with the two instances removed,
proved the same way.

**Why the agreement with the quasi-coherent construction is available.**  Both
`quotientClassMapToPushforward` and `pushforwardFractionClass` are maps out of the cokernel of
`equationsMap`, so they are equal as soon as they agree after the projection onto it, and
`Stacks.Perfect.FractionClass.classMapToSupport_comp_supportCohomologyToPushforward` is exactly
that agreement — with the comparison of the two spellings of the target written as
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward`.  That comparison is the
component of `supportCohomologySheafFunctorIso` used here, by
`Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafFunctorIso_hom_app_eq`, which
closes the triangle between the library's three copies of "an exact functor commutes with `Hⁿ`";
nothing about those copies is reproved here.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.GysinLocalCohomology (localCohomologyPushforwardFunctor
  supportCohomologySheafFunctorIso)

universe u

namespace Stacks.Perfect.FractionClass

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The numerator is natural in the coefficient module -/

/-- **For a nonempty family of equations the fraction in the top term is natural in the
coefficient module.**  The fraction in the top term is then the fraction with the product of all
the equations as denominator, which is
`Stacks.Perfect.SupportedFraction.fractionHom` by
`Stacks.Perfect.GysinFractionDeRham.fracTerm_eq_fractionHom`, and the top-degree component of the
induced map of Čech complexes is `Stacks.Perfect.SupportedFraction.prodMap`. -/
public theorem fracTermTop_naturality_succ {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) :
    fracTermTop f F ≫ (cplxMap f φ).f (n + 1) = φ ≫ fracTermTop f G := by
  show fracTerm f F ≫ prodMap f φ n = φ ≫ fracTerm f G
  rw [GysinFractionDeRham.fracTerm_eq_fractionHom, GysinFractionDeRham.fracTerm_eq_fractionHom]
  exact SupportedFraction.fractionHom_naturality f φ n

/-- **The fraction in the top term of the extended alternating Čech complex is natural in the
coefficient module, for every number of equations.**

This is the hypothesis that `Stacks.Gysin.classMap_naturality` and
`Stacks.Gysin.classMapToSupport_naturality` carry, discharged at every `c`.  The two cases have
nothing in common: for `c = 0` the denominator is the empty product `1`, so the fraction is the
identity of the coefficient module and the statement is
`Stacks.Gysin.fracTermTop_naturality_zero`; for `c = n + 1` it is
`fracTermTop_naturality_succ`. -/
public theorem fracTermTop_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}
    (φ : F ⟶ G) :
    fracTermTop f F ≫ (cplxMap f φ).f c = φ ≫ fracTermTop f G := by
  cases c with
  | zero => exact Stacks.Gysin.fracTermTop_naturality_zero f φ
  | succ n => exact fracTermTop_naturality_succ f φ

/-! ### The class map on the coefficient module is natural, for an arbitrary module -/

/-- **Stacks Project, Tag 0G7T for an arbitrary `𝒪_X`-module and any number of equations: the
class map of [Stacks, Tag 0G7Q] read on the coefficient module is natural in it**, in the
spelling of `i_*ℋ ᶜ_T(ℱ)` with the cohomology sheaf taken after the direct image.

This is `Stacks.Gysin.classMapToSupport_naturality` with the quasi-coherence of the two
coefficient modules removed, which that statement names and does not use.  Its proof is the
naturality `Stacks.Gysin.classMap_naturality` of the fraction class in the degree-`c` cohomology
of the extended alternating Čech complex followed by the naturality
`Stacks.Perfect.SupportedFraction.homologyMap_cplxMap_comp_cechHomologyToSupport` of the
comparison of [Stacks, Tag 0G7L], and neither needs it: that comparison is a map of complexes of
arbitrary `𝒪_X`-modules, quasi-coherence entering only at [Stacks, Tag 0G7M], where it is shown
to be invertible.  The proof below is therefore the quasi-coherent one verbatim. -/
public theorem classMapToSupport_natural {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}
    (φ : F ⟶ G) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (hfrac : fracTermTop f F ≫ (cplxMap f φ).f c = φ ≫ fracTermTop f G) :
    φ ≫ classMapToSupport f G hT hTf =
      classMapToSupport f F hT hTf ≫
        (SupportedFraction.supportCohomologySheafFunctor hT (c : ℤ)).map φ := by
  rw [classMapToSupport, classMapToSupport, ← Category.assoc,
    Stacks.Gysin.classMap_naturality f φ hfrac, Category.assoc]
  exact congrArg (classMap f F ≫ ·)
    (SupportedFraction.homologyMap_cplxMap_comp_cechHomologyToSupport f φ hT hTf c)

/-! ### The class map on the coefficient module, with the direct image outside -/

/-- **The class map of [Stacks, Tag 0G7Q] read on the coefficient module and in the spelling of
`i_*ℋ ᶜ_T(ℱ)` with the direct image taken outside the cohomology sheaf.**  It is
`Stacks.Perfect.FractionClass.classMapToSupport`, which takes the cohomology sheaf after the
direct image, followed by the comparison of the two spellings; the comparison needs no hypothesis,
the direct image from a closed subset being exact. -/
public def classMapToPushforward {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    F ⟶ (localCohomologyPushforwardFunctor hT (c : ℤ)).obj F :=
  classMapToSupport f F hT hTf ≫ (supportCohomologySheafFunctorIso hT (c : ℤ)).hom.app F

/-- **Stacks Project, Tag 0G7Q, functoriality in `ℱ`**, in the spelling of `i_*ℋ ᶜ_T(ℱ)` with the
direct image outside: `classMapToSupport_natural`, with its carried numerator hypothesis
discharged by `fracTermTop_naturality`, carried across the comparison of the two spellings, which
is natural. -/
@[stacks 0G7Q "functoriality in the 𝒪_X-module ℱ, with the direct image taken outside the
cohomology sheaf, for an arbitrary 𝒪_X-module and any number of equations"]
public theorem classMapToPushforward_natural {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}
    (φ : F ⟶ G) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    φ ≫ classMapToPushforward f G hT hTf =
      classMapToPushforward f F hT hTf ≫ (localCohomologyPushforwardFunctor hT (c : ℤ)).map φ := by
  rw [classMapToPushforward, classMapToPushforward]
  erw [← Category.assoc, classMapToSupport_natural f φ hT hTf (fracTermTop_naturality f φ),
    Category.assoc, (supportCohomologySheafFunctorIso hT (c : ℤ)).hom.naturality φ,
    Category.assoc]

/-! ### The quotient by the equations, as a functor of the coefficient module -/

/-- The coprojection followed by `equationsMap` is multiplication by the corresponding equation. -/
private theorem sigmaι_comp_equationsMap {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    (i : Fin c) : Sigma.ι (fun _ : Fin c => F) i ≫ equationsMap f F = smulHom (f i) F :=
  Limits.Sigma.ι_desc _ _

/-- Multiplication by one of the equations is killed by the projection onto the quotient by the
equations: it is the corresponding coprojection followed by
`Stacks.Perfect.FractionClass.equationsMap`. -/
public theorem smulHom_comp_cokernelπ_equationsMap {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) (i : Fin c) :
    smulHom (f i) F ≫ cokernel.π (equationsMap f F) = 0 := by
  rw [← sigmaι_comp_equationsMap, Category.assoc, cokernel.condition, comp_zero]

/-- A morphism of coefficient modules followed by the projection onto the quotient by the
equations kills `Stacks.Perfect.FractionClass.equationsMap`, because multiplication by a global
function commutes with every morphism of modules. -/
public theorem equationsMap_comp_comp_cokernelπ {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) :
    equationsMap f F ≫ φ ≫ cokernel.π (equationsMap f G) = 0 := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [comp_zero, ← Category.assoc, sigmaι_comp_equationsMap, ← Category.assoc,
    smulHom_naturality, Category.assoc, smulHom_comp_cokernelπ_equationsMap, comp_zero]

/-- **The map `ℱ/(f₁, …, f_c)ℱ ⟶ 𝒢/(f₁, …, f_c)𝒢` induced by a morphism of coefficient
modules.**  This is `i_*i^*φ` read on the presentation of `i_*i^*ℱ` as the cokernel of
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` that [Stacks, Tag 0G7Q] uses; it exists because multiplication by a
global function commutes with every morphism of modules. -/
public def equationsQuotientMap {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G) :
    equationsQuotient f F ⟶ equationsQuotient f G :=
  cokernel.desc (equationsMap f F) (φ ≫ cokernel.π (equationsMap f G))
    (equationsMap_comp_comp_cokernelπ f φ)

/-- The induced map on the quotient by the equations carries the class of a local section to the
class of its image. -/
public theorem cokernelπ_comp_equationsQuotientMap {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) :
    cokernel.π (equationsMap f F) ≫ equationsQuotientMap f φ =
      φ ≫ cokernel.π (equationsMap f G) :=
  cokernel.π_desc _ _ _

/-! ### The map of the remark, for an arbitrary `𝒪_X`-module -/

/-- The fraction class with values in `i_*ℋ ᶜ_T(ℱ)` kills the image of
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, so it descends to the quotient by the equations.  This is the step
of [Stacks, Tag 0G7Q] which says that the class of `s / (f₁ ⋯ f_c)` "depends only on `s` modulo
the image of `(f₁, …, f_c)`", and it is already available for an arbitrary `𝒪_X`-module as
`equationsMap_comp_classMap`. -/
public theorem equationsMap_comp_classMapToPushforward {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    equationsMap f F ≫ classMapToPushforward f F hT hTf = 0 := by
  rw [classMapToPushforward, classMapToSupport]
  erw [← Category.assoc, ← Category.assoc, equationsMap_comp_classMap, zero_comp, zero_comp]

/-- **Stacks Project, Tag 0G7Q, for an arbitrary `𝒪_X`-module.**  The `𝒪_X`-module map

`i_*i^*ℱ = ℱ/(f₁, …, f_c)ℱ ⟶ i_*ℋ ᶜ_T(ℱ)`

carrying the class of a local section `s` of `ℱ` to the class of the fraction `s / (f₁ ⋯ f_c)`.
The remark builds exactly this map and then descends it along the fully faithful `i_*`; here the
descent is `fractionClassAnyModule`.

No quasi-coherence and no hypothesis on the number of equations: the class of the fraction lands
in the degree-`c` cohomology sheaf of the extended alternating Čech complex, which the comparison
of [Stacks, Tag 0G7L] carries into `i_*ℋ ᶜ_T(ℱ)` for every `𝒪_X`-module `ℱ`. -/
@[stacks 0G7Q "i_* of the remark's map c_{f₁,…,f_c}, between its two presentations, for an
arbitrary 𝒪_X-module ℱ and any number of equations"]
public def quotientClassMapToPushforward {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    equationsQuotient f F ⟶ (localCohomologyPushforwardFunctor hT (c : ℤ)).obj F :=
  cokernel.desc (equationsMap f F) (classMapToPushforward f F hT hTf)
    (equationsMap_comp_classMapToPushforward f F hT hTf)

/-- **Stacks Project, Tag 0G7Q.**  The map out of the quotient sends the class of a local section
`s` of `ℱ` to the class of the fraction `s / (f₁ ⋯ f_c)`. -/
@[stacks 0G7Q "the value on the class of a local section is the class of its fraction, for an
arbitrary 𝒪_X-module ℱ"]
public theorem cokernelπ_comp_quotientClassMapToPushforward {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    cokernel.π (equationsMap f F) ≫ quotientClassMapToPushforward f F hT hTf =
      classMapToPushforward f F hT hTf :=
  cokernel.π_desc _ _ _

/-- **Stacks Project, Tag 0G7Q, functoriality in `ℱ` of the map out of the quotient.**  The
square commutes for every morphism `φ : ℱ ⟶ 𝒢` of `𝒪_X`-modules, the left vertical arrow being
`i_*i^*φ` in the presentation `equationsQuotientMap`.

The projection onto the quotient is an epimorphism, so this is
`classMapToPushforward_natural`. -/
@[stacks 0G7Q "functoriality in the 𝒪_X-module ℱ of i_* of the remark's map, for an arbitrary
𝒪_X-module ℱ and any number of equations"]
public theorem quotientClassMapToPushforward_natural {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {F G : X.Modules} (φ : F ⟶ G) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) :
    equationsQuotientMap f φ ≫ quotientClassMapToPushforward f G hT hTf =
      quotientClassMapToPushforward f F hT hTf ≫
        (localCohomologyPushforwardFunctor hT (c : ℤ)).map φ := by
  refine (cancel_epi (cokernel.π (equationsMap f F))).mp ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ quotientClassMapToPushforward f G hT hTf)
    (cokernelπ_comp_equationsQuotientMap f φ)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun ψ => φ ≫ ψ)
    (cokernelπ_comp_quotientClassMapToPushforward f G hT hTf)) ?_
  refine Eq.trans (classMapToPushforward_natural f φ hT hTf) ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ (localCohomologyPushforwardFunctor hT (c : ℤ)).map φ)
    (cokernelπ_comp_quotientClassMapToPushforward f F hT hTf).symm) ?_
  exact Category.assoc _ _ _

/-- **Stacks Project, Tag 0G7Q, for every `𝒪_X`-module.**  The canonical `𝒪_X|_T`-linear map

`c_{f₁, …, f_c} : i^*(ℱ/(f₁, …, f_c)ℱ) ⟶ ℋ ᶜ_T(ℱ)`

on a closed subset `T` containing the common zero locus of `f₁, …, f_c`, for an **arbitrary**
`𝒪_X`-module `ℱ` and an arbitrary number of equations.  It is the transpose, under the adjunction
`i^* ⊣ i_*` between inverse image and direct image along the inclusion of `T`, of the map
`quotientClassMapToPushforward` carrying the class of a local section `s` of `ℱ` to the class of
the fraction `s / (f₁ ⋯ f_c)`.

This is the remark's own construction: the `𝒪_X`-module map `i_*i^*ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` followed by
the descent along `i_*`.  Only the comparison of [Stacks, Tag 0G7L] is used, and that holds for
every `𝒪_X`-module; `Stacks.Perfect.FractionClass.fractionClass` is this map on a quasi-coherent
module, by `fractionClassAnyModule_eq`. -/
@[stacks 0G7Q "the canonical map c_{f_1, …, f_c}, for an arbitrary 𝒪_X-module ℱ and any number of
equations"]
public def fractionClassAnyModule {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    (modulePullback (closedSubsetInclusion X.toRingedSpace T)).obj (equationsQuotient f F) ⟶
      localCohomologySheafOfComplex X.toRingedSpace T hT (c : ℤ)
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  (homEquiv (closedSubsetInclusion X.toRingedSpace T) _
    (equationsQuotient f F)).symm (quotientClassMapToPushforward f F hT hTf)

/-- **Stacks Project, Tag 0G7Q.**  The map `c_{f₁, …, f_c}` is the transpose of the map
`i_*i^*ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` out of the quotient by the equations. -/
@[stacks 0G7Q "c_{f_1, …, f_c} is the transpose of the map out of the quotient, for an arbitrary
𝒪_X-module ℱ"]
public theorem homEquiv_fractionClassAnyModule {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    homEquiv (closedSubsetInclusion X.toRingedSpace T) _ (equationsQuotient f F)
        (fractionClassAnyModule f F hT hTf) =
      quotientClassMapToPushforward f F hT hTf :=
  Equiv.apply_symm_apply _ _

/-- **Stacks Project, Tag 0G7Q, functoriality in `ℱ` of `c_{f₁, …, f_c}` itself.**  For every
morphism `φ : ℱ ⟶ 𝒢` of `𝒪_X`-modules the square

`i^*(ℱ/(f)ℱ) ⟶ ℋ ᶜ_T(ℱ)`, `i^*(𝒢/(f)𝒢) ⟶ ℋ ᶜ_T(𝒢)`

commutes, the vertical arrows being `i^*` of `equationsQuotientMap` and `ℋ ᶜ_T(φ)`.  This is the
functoriality the remark asserts, read on `c_{f₁, …, f_c}` rather than on its direct image.

It is `quotientClassMapToPushforward_natural` transposed: both sides become maps out of
`ℱ/(f)ℱ` under the bijection of the adjunction `i^* ⊣ i_*`, by its naturality in each variable,
and there the square is the one already proved. -/
@[stacks 0G7Q "functoriality in the 𝒪_X-module ℱ of c_{f_1, …, f_c} itself, for an arbitrary
𝒪_X-module ℱ and any number of equations"]
public theorem fractionClassAnyModule_natural {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}
    (φ : F ⟶ G) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    (modulePullback (closedSubsetInclusion X.toRingedSpace T)).map (equationsQuotientMap f φ) ≫
        fractionClassAnyModule f G hT hTf =
      fractionClassAnyModule f F hT hTf ≫
        (localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (c : ℤ)).map φ := by
  refine (homEquiv (closedSubsetInclusion X.toRingedSpace T) _
    (equationsQuotient f F)).injective ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_left
      (modulePullbackPushforwardAdjunction (closedSubsetInclusion X.toRingedSpace T))
      (equationsQuotientMap f φ) (fractionClassAnyModule f G hT hTf)) ?_
  refine Eq.trans (congrArg (fun ψ => equationsQuotientMap f φ ≫ ψ)
    (homEquiv_fractionClassAnyModule f G hT hTf)) ?_
  refine Eq.trans (quotientClassMapToPushforward_natural f φ hT hTf) ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).map
        ((localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (c : ℤ)).map φ))
    (homEquiv_fractionClassAnyModule f F hT hTf).symm) ?_
  exact (Adjunction.homEquiv_naturality_right
    (modulePullbackPushforwardAdjunction (closedSubsetInclusion X.toRingedSpace T))
    (fractionClassAnyModule f F hT hTf)
    ((localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (c : ℤ)).map φ)).symm

/-! ### The quasi-coherent construction is this one specialised -/

/-- **On a quasi-coherent module the map built here is the map built through
[Stacks, Tag 0G7M].**  Both are maps out of the cokernel of
`Stacks.Perfect.FractionClass.equationsMap`, so they agree as soon as they agree after the
projection onto it, where the statement is
`Stacks.Perfect.FractionClass.classMapToSupport_comp_supportCohomologyToPushforward`.

The comparison of the two places at which the degree-`c` cohomology sheaf may be taken appears on
the two sides in its two spellings, and
`Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafFunctorIso_hom_app_eq`
identifies them: they come from two of the library's three copies of "an exact functor commutes
with `Hᶜ`". -/
public theorem quotientClassMapToPushforward_eq {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    [F.IsQuasicoherent] :
    quotientClassMapToPushforward f F (isClosed_equationsClosedSet f) subset_rfl =
      pushforwardFractionClass f F := by
  refine (cancel_epi (cokernel.π (equationsMap f F))).mp ?_
  refine Eq.trans (cokernelπ_comp_quotientClassMapToPushforward f F
    (isClosed_equationsClosedSet f) subset_rfl) ?_
  refine Eq.trans (congrArg (fun ψ => classMapToSupport f F (isClosed_equationsClosedSet f)
      subset_rfl ≫ ψ) (SupportedEndoForgetDegreewise.supportCohomologySheafFunctorIso_hom_app_eq
        (isClosed_equationsClosedSet f) c F)) ?_
  exact classMapToSupport_comp_supportCohomologyToPushforward f F

/-- **Stacks Project, Tag 0G7Q: the quasi-coherent construction is this one specialised.**  On a
quasi-coherent `𝒪_X`-module the map `c_{f₁, …, f_c}` built here through [Stacks, Tag 0G7L] alone
is `Stacks.Perfect.FractionClass.fractionClass`, which is built through [Stacks, Tag 0G7M].  Both
are transposes along `i^* ⊣ i_*`, and their transposes agree by
`quotientClassMapToPushforward_eq`. -/
@[stacks 0G7Q "the quasi-coherent construction of c_{f_1, …, f_c} is the arbitrary-module one
specialised"]
public theorem fractionClassAnyModule_eq {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    [F.IsQuasicoherent] :
    fractionClassAnyModule f F (isClosed_equationsClosedSet f) subset_rfl = fractionClass f F :=
  congrArg (homEquiv (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)) _
    (equationsQuotient f F)).symm (quotientClassMapToPushforward_eq f F)

end Stacks.Perfect.FractionClass

end
