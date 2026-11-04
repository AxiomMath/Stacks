module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperMorphismSupport

/-!
# Proper support over the test scheme when the morphism is proper

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of finite presentation and
let `T` be a scheme over `Y`.  Both `Coh_{X/Y}` (Stacks 08KB) and `Quot_{F/X/Y}` (Stacks 09TR)
ask of a module on the base change `X_T = X ×_Y T` that its support be a closed subset of
`|X_T|` proper over `T` in the sense of Stacks 0CZD.

When `f` is proper this condition is automatic for a module of finite type.  The projection
`X_T ⟶ T` is proper, being a base change of `f` (Stacks 04WP); the support of a module of finite
type is closed (Stacks 07TZ); and every closed subset of the points of the source of a proper
morphism is proper over its target.  So for `f` proper the objects of `Coh_{X/Y}` over `T` are
the finitely presented quasi-coherent `𝒪_{X_T}`-modules flat over `T`, and `Quot_{F/X/Y}(T)` is
the set `Q^{fp}_{F/X/Y}(T)` of Stacks 082M.  This is the form of the proper-support condition used
in the existence part of the valuative criterion for `Coh_{X/Y} → Y` and `Quot_{F/X/Y} → Y`
(Stacks 0DM0, 0DM4).

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.objectOfIsProper`: for `f` proper, the object of
  `Coh_{X/Y}` over `T` given by a finitely presented quasi-coherent module on `X_T` flat over `T`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_isProperOver_support_of_isProper`: for `f`
  proper, a module of finite type on `X_T` satisfies the proper-support condition of an object of
  `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.isProper_schemeTheoreticSupport_of_isProper`: for
  `f` proper, the scheme-theoretic support of a finite type quasi-coherent module on `X_T` is
  proper over `T`.
* `AlgebraicGeometry.Space.QuotSituation.isProper_projection`: for `f` proper, the projection
  `X_T ⟶ T` is proper.
* `AlgebraicGeometry.Space.QuotSituation.isProperlySupportedOver_of_isProper` and
  `AlgebraicGeometry.Space.QuotSituation.properlySupportedQuotients_eq_of_isProper`: for `f`
  proper, every module of finite type on `X_T` has support proper over `T`, so
  `Quot_{F/X/Y}(T) = Q^{fp}_{F/X/Y}(T)`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0DM4](https://stacks.math.columbia.edu/tag/0DM4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- **For `f` proper, a module of finite type on `X_T` has support proper over `T`**, in exactly
the form of the proper-support condition on an object of `Coh_{X/Y}` (Stacks 08KB): the
projection `X_T ⟶ T` is locally of finite type, the support is closed, and it is proper over `T`
in the sense of Stacks 0CZD. -/
theorem exists_isProperOver_support_of_isProper (hf : IsProper B S hS D.f.hom)
    (T : SchemesOver D.Y) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    [SheafOfModules.IsFiniteTypeOnSite F] :
    ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T F)),
      IsProperOver B S hS (D.space T).2
        ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom hp (D.support T F) hU :=
  ⟨Space.isLocallyOfFiniteType_projection D T,
    hasProperSupport_toSheaf_of_isProper B S hS (D.space T).2
      ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom
      (Space.isLocallyOfFiniteType_projection D T) (Space.isProper_projection D hf T) F⟩

/-- **For `f` proper, the scheme-theoretic support of a finite type quasi-coherent module on
`X_T` is proper over `T`.** -/
theorem isProper_schemeTheoreticSupport_of_isProper (hf : IsProper B S hS D.f.hom)
    (T : SchemesOver D.Y) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    IsProper B S hS ((schemeTheoreticSupport B S hS (D.space T) F).ι ≫ (D.projection T).hom) :=
  Space.isProper_schemeTheoreticSupport_of_isProper B S hS (D.space T)
    ((schemeSpaceFunctor B S hS).obj T.left) (D.projection T).hom
    (Space.isProper_projection D hf T) F hF hFft

/-- **For `f` proper, an object of `Coh_{X/Y}` is a finitely presented quasi-coherent module on
`X_T` flat over `T`**: the proper-support condition of Stacks 08KB holds automatically. -/
@[simps T F]
def objectOfIsProper (hf : IsProper B S hS D.f.hom) (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (hqc : F.IsQuasicoherentOnSite)
    (hfp : F.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F) : CoherentObject D where
  T := T
  F := F
  quasicoherent := hqc
  finitePresentation := hfp
  flat := hflat
  properSupport :=
    letI := hfp
    D.exists_isProperOver_support_of_isProper hf T F

end CoherentSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **For `f` proper, the projection `X_T ⟶ T` is proper**, being a base change of `f`
(Stacks 04WP). -/
theorem isProper_projection (hf : IsProper B S hS D.f.hom) (T : SchemesOver D.Y) :
    IsProper B S hS (D.projection T).hom :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) hf

/-- **For `f` proper, a module of finite type on `X_T` has support proper over `T`.** -/
theorem isProperlySupportedOver_of_isProper (hf : IsProper B S hS D.f.hom)
    (T : SchemesOver D.Y) (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    [SheafOfModules.IsFiniteTypeOnSite G] :
    D.IsProperlySupportedOver T G :=
  hasProperSupport_toSheaf_of_isProper B S hS (D.space T).2
    ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom
    (D.isLocallyOfFiniteType_projection T) (D.isProper_projection hf T) G

/-- **For `f` proper, `Quot_{F/X/Y}(T) = Q^{fp}_{F/X/Y}(T)`**: a finitely presented quotient
of `F_T` is of finite type, so its support is proper over `T`. -/
theorem properlySupportedQuotients_eq_of_isProper (hf : IsProper B S hS D.f.hom)
    (T : SchemesOver D.Y) :
    D.properlySupportedQuotients T = D.finitePresentationQuotients T := by
  refine subset_antisymm (D.properlySupportedQuotients_subset_finitePresentation T) ?_
  intro K hK
  let := hK.2
  exact ⟨hK, D.isProperlySupportedOver_of_isProper hf T _⟩

end QuotSituation

end AlgebraicGeometry.Space

end
