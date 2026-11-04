module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType

/-!
# The Quot functor

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module. For a scheme `T` over `B`
write `X_T = X ×_B T` and write `F_T` for the pullback of `F` along the projection `X_T ⟶ X`.
The set

`Quot_{F/X/B}(T) = {quotients F_T ⟶ Q with Q quasi-coherent of finite presentation, flat
over T, with support proper over T}`

is the subset of the set `Q^{fp}_{F/X/B}(T)` of finitely presented quotients cut out by the
condition that the support of the quotient be proper over `T`. That condition is stable under
base change. A quotient of `F_T` is recorded by its kernel.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation`: a quotient situation whose morphism is moreover of
  finite presentation.
* `AlgebraicGeometry.Space.QuotSituation.IsProperlySupportedOver`: the condition that the
  support of an `𝒪_{X_T}`-module be proper over the test scheme `T`.
* `AlgebraicGeometry.Space.QuotSituation.properlySupportedQuotients`: the set
  `Quot_{F/X/B}(T)`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isProperlySupportedOver_modulePullback_quotientModule`:
  the inverse image along `X_U ⟶ X_T` of the quotient of a member of `Quot_{F/X/B}(T)` again has
  support proper over the test scheme.
* `AlgebraicGeometry.Space.QuotSituation.isProperlySupportedOver_modulePullback`: the same for an
  arbitrary finite type, quasi-coherent module.
* `AlgebraicGeometry.Space.QuotSituation.properlySupportedQuotients_subset_finitePresentation`:
  the inclusion `Quot_{F/X/B}(T) ⊆ Q^{fp}_{F/X/B}(T)`.
* `AlgebraicGeometry.Space.QuotSituation.isLocallyOfFiniteType_projection`: the projection
  `X_T ⟶ T` is locally of finite type.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

/-! ### The standing data -/

/-- A quotient situation — a morphism `f : X ⟶ B` of algebraic spaces over `S` together with a
quasi-coherent `𝒪_X`-module `F` — whose morphism is moreover of finite presentation. -/
@[stacks 09TR "the standing data"]
structure QuotSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    extends QuotientSituation B S hS where
  /-- The morphism is of finite presentation (Stacks 03XP). -/
  finitePresentation : IsFinitePresentation B S hS f.hom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- The support of an `𝒪_{X_T}`-module, as a subset of the points of `X_T` (Stacks 04KA). -/
abbrev support (T : SchemesOver D.Y)
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    Set (points B S hS (D.space T).1) :=
  supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G)

/-- The projection `X_T ⟶ T` is locally of finite type. -/
theorem isLocallyOfFiniteType_projection (T : SchemesOver D.Y) :
    IsLocallyOfFiniteType B S hS (D.projection T).hom :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom)
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS D.finitePresentation.1)

/-! ### The proper-support condition -/

/-- An `𝒪_{X_T}`-module has *support proper over the test scheme* `T` when its support is a
closed subset of the points of `X_T` proper over `T`. -/
abbrev IsProperlySupportedOver (T : SchemesOver D.Y)
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) : Prop :=
  HasProperSupport B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
    (D.projection T).hom (D.isLocallyOfFiniteType_projection T)
    ((SheafOfModules.toSheaf _).obj G)

/-- The proper-support condition is inherited by the inverse image of a finite type,
quasi-coherent module along the morphism `X_U ⟶ X_T` of base changes induced by a morphism
`U ⟶ T` of test schemes. -/
theorem isProperlySupportedOver_modulePullback {U T : SchemesOver D.Y} (h : U ⟶ T)
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hqc : SheafOfModules.IsQuasicoherentOnSite G)
    (hft : SheafOfModules.IsFiniteTypeOnSite G)
    (hG : D.IsProperlySupportedOver T G) :
    D.IsProperlySupportedOver U ((modulePullback B S hS (D.relativeMap h)).obj G) :=
  ⟨isClosed_supportOfSheaf_modulePullback B S hS (D.relativeMap h) G hft,
    isProperOver_supportOfSheaf_modulePullback B S hS (isPullback_baseChangeMap D.f h)
      (D.isLocallyOfFiniteType_projection T) G hqc hft hG.2⟩

/-! ### The Quot functor -/

/-- The set `Quot_{F/X/B}(T)` of quotients of `F_T` which are quasi-coherent, of finite
presentation, flat over the test scheme `T` and with support proper over `T`, each recorded by
its kernel `K`, the quotient being `F_T / K`. -/
@[stacks 09TR "the set of quotients"]
def properlySupportedQuotients (T : SchemesOver D.Y) :
    Set (Subobject (D.baseChangeModule T)) :=
  {K | K ∈ D.finitePresentationQuotients T ∧
    D.IsProperlySupportedOver T (D.quotientModule T K)}

/-- The quotients with proper support form a subset of `Q^{fp}_{F/X/B}(T)`. -/
theorem properlySupportedQuotients_subset_finitePresentation
    (T : SchemesOver D.Y) :
    D.properlySupportedQuotients T ⊆ D.finitePresentationQuotients T :=
  fun _ hK => hK.1

/-- The support of a quotient in `Q^{fp}_{F/X/B}(T)` is closed. -/
theorem isClosed_support_of_mem {T : SchemesOver D.Y} {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.finitePresentationQuotients T) :
    IsClosed (D.support T (D.quotientModule T K)) :=
  have := hK.2
  isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS (D.space T).1 (D.space T).2
    (D.quotientModule T K)

/-- For a quotient in `Quot_{F/X/B}(T)` and a morphism `U ⟶ T` of test schemes, the inverse
image of that quotient along `X_U ⟶ X_T` again has support proper over the test scheme. -/
@[stacks 09TR "the subfunctor of the finitely presented quotients"]
theorem isProperlySupportedOver_modulePullback_quotientModule {U T : SchemesOver D.Y}
    (h : U ⟶ T) {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) :
    D.IsProperlySupportedOver U
      ((modulePullback B S hS (D.relativeMap h)).obj (D.quotientModule T K)) :=
  have := hK.1.2
  D.isProperlySupportedOver_modulePullback h (D.quotientModule T K) hK.1.1.1 inferInstance hK.2

end QuotSituation

end AlgebraicGeometry.Space

end
