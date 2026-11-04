module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpecIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFiniteOverAffine

/-!
# The normalization in a proper algebraic space over a locally Noetherian base is finite

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian.
The direct image `f_* 𝒪_X` has finite sections over every affine étale chart `V` of `Y`: they
embed into the global functions of the algebraic space `X ×_Y V`, proper over `V`, and those form
a finite `Γ(V, 𝒪_V)`-module (the degree-zero case of Stacks 08AR for the structure sheaf,
`AlgebraicGeometry.Space.isNoetherian_globalFunctions_of_isProper`).  Hence the integral closure
`𝒪'` of `𝒪_Y` in `f_* 𝒪_X` is a finite `𝒪_Y`-algebra, and its relative spectrum, the
normalization `ν : Y' ⟶ Y` of `Y` in `X` (Stacks 0822), is a finite morphism.  This is
clause (2) of Stacks 0A1B.

## Main results

* `Stacks.RelativeSpec.isFinite_toBase_of_finite_app`: the relative spectrum of a quasi-coherent
  algebra on a scheme whose sections are finite over the base is finite over the base.
* `AlgebraicGeometry.Space.isFinite_chartRelativeSpecQuotientHom`: the relative spectrum of a
  finite quasi-coherent algebra on an algebraic space is a finite morphism of algebraic spaces.
* `AlgebraicGeometry.Space.finite_pushforwardAlgebra_algebraMap_of_isProper`: for proper `f` over
  a locally Noetherian `Y`, the sections of `f_* 𝒪_X` over an affine étale chart form a finite
  module.
* `AlgebraicGeometry.Space.isFinite_normalizationInQcqsHom_of_isProper`: the normalization of `Y`
  in `X` is finite over `Y`.

## References

* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.RelativeSpec

open _root_.AlgebraicGeometry

variable (s : RelativeSpecSituation.{u})

/-- **The relative spectrum of a quasi-coherent algebra whose sections are finite over the base
is finite over the base.**  It is affine over the base, and over an affine open its sections are
those of the algebra followed by an isomorphism. -/
theorem isFinite_toBase_of_finite_app
    (h : ∀ U : s.base.Opens, IsAffineOpen U → (s.algebra.hom.hom.app (.op U)).hom.Finite) :
    IsFinite (gluedSpectrum s).toBase := by
  have : IsAffineHom (gluedSpectrum s).toBase :=
    AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase s.algebra
  have : (RingHom.toMorphismProperty RingHom.Finite).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.finite_respectsIso
  refine ⟨fun U hU => ?_⟩
  have _ := isIso_universalAlgebraMap_app s ⟨U, hU⟩
  rw [toBase_app]
  exact MorphismProperty.RespectsIso.postcomp
    (RingHom.toMorphismProperty RingHom.Finite) _ _ (h U hU)

end Stacks.RelativeSpec

namespace AlgebraicGeometry.Space

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (hAfin : A.IsFinite) (V : SmallEtale B S hS X.1)

include hAfin

/-- **The relative spectrum over a chart of a finite quasi-coherent algebra is a finite morphism
of schemes.**  Over an affine open `O` of the chart's scheme its sections are restriction of
regular functions to `O`, an isomorphism, followed by the structure-algebra map of `A` over the
étale chart `O` cuts out, which is finite by hypothesis. -/
theorem isFinite_chartRelativeSpecToChart :
    _root_.AlgebraicGeometry.IsFinite (chartRelativeSpecToChart B S hS X A hA V) := by
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  have : (RingHom.toMorphismProperty RingHom.Finite).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.finite_respectsIso
  refine Stacks.RelativeSpec.isFinite_toBase_of_finite_app
    (Stacks.AffineAlgebraEquivalence.situation (chartSchemeAlgebra B S hS X A V))
    fun O hO => ?_
  exact MorphismProperty.RespectsIso.precomp
    (RingHom.toMorphismProperty RingHom.Finite)
    ((Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op O)) _
    (hAfin (openChart B S hS X.1 V O) hO)

/-- **The relative spectrum over a chart, read in the site, is a finite morphism of algebraic
spaces.** -/
theorem isFinite_yoneda_map_chartRelativeSpecSiteToChart
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    IsFinite B S hS
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V hV)) :=
  (isFinite_iff_holdsOnAffineBaseChange _).2 <| HoldsOnAffineBaseChange.of_presheaf
    (fun p hp hZ => isAffine_of_isFinite p hp hZ)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsFinite.{u})
      (chartRelativeSpecSiteToChart B S hS X A hA V hV)).2
      (isFinite_chartRelativeSpecToChart B S hS X A hA hAfin V))

end Chart

section Quotient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (hAfin : A.IsFinite)
    {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))

include hAfin hsq hsurj hV'' in
/-- **The structure morphism `ν : \underline{Spec}_X(A) ⟶ X` of the relative spectrum of a
finite quasi-coherent algebra is a finite morphism of algebraic spaces.**  Its base change along
the surjective étale chart `V₂` is the structure morphism of the relative spectrum over the
chart (`AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom`), which is finite, and
finiteness is étale local on the target (Stacks 03ZQ). -/
theorem isFinite_chartRelativeSpecQuotientHom :
    IsFinite B S hS
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom := by
  have hsqr := isPullback_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
    hV' hV₂ hV''
  have : IsIso (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) := inferInstance
  have hiso : IsPullback hsqr.isoPullback.inv
      (pullback.snd (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom
        V₂.obj.hom)
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))
      (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) :=
    IsPullback.of_horiz_isIso ⟨hsqr.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  exact isFinite_of_surjectiveEtaleChart B S hS
    (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').property X.property _
    (isSurjective_of_presheafSurjective B S hS V₂.obj.hom hsurj)
    (isEtale_of_presheaf_etale B S hS V₂.property)
    (isFinite_of_isPullback B S hS hiso
      (isFinite_yoneda_map_chartRelativeSpecSiteToChart B S hS X A hA hAfin V₂ hV₂))

end Quotient

section Proper

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The sections of `f_* 𝒪_X` over an affine étale chart of a locally Noetherian `Y` form a
finite module, for `f` proper.**  They embed `Γ(V, 𝒪_V)`-linearly into the global functions of
the algebraic space `X ×_Y V` (`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`),
which is proper over the Noetherian affine scheme `V`, so that its global functions form a
Noetherian `Γ(V, 𝒪_V)`-module (`AlgebraicGeometry.Space.isNoetherian_globalFunctions_of_isProper`,
the degree-zero case of Stacks 08AR for the structure sheaf). -/
theorem finite_pushforwardAlgebra_algebraMap_of_isProper (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    RingHom.Finite ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V)) := by
  let T : BigFppfOver B S hS := (SmallEtale.toOver B S hS Y.1).obj V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hV
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) :=
    isLocallyNoetherian_chartScheme B S hS Y hY V
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let W := chartBaseChangeSpace B S hS f V
  let g : W ⟶ schemeSpace T := chartBaseChangeProjection B S hS f V
  have hg : IsProper B S hS g.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      ((spacesBaseChange B S hS f).isPullback ((comparisonFunctor B S hS Y).obj V)).flip hf
  let R₀ := (structureSheaf B S hS Y.1 Y.2).obj.obj (op V)
  let : Module R₀ (globalFunctions B S hS W.obj) := globalFunctionsModuleOfHom B S hS W T g
  have : _root_.IsNoetherian R₀ (globalFunctions B S hS W.obj) :=
    isNoetherian_globalFunctions_of_isProper B S hS g hg
  let := ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V)).toAlgebra
  have hcomm : ∀ r, directImageSectionsToGlobalFunctions B S hS f V
      ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V) r) =
      pullbackToGlobalFunctions B S hS W T g r := fun r =>
    Subtype.ext (funext fun c =>
      directImageSectionsToGlobalFunctions_algebraMap B S hS f V c.unop r)
  let L : (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V) →ₗ[R₀]
      globalFunctions B S hS W.obj :=
    { toFun := directImageSectionsToGlobalFunctions B S hS f V
      map_add' := map_add _
      map_smul' := fun r x => by
        change directImageSectionsToGlobalFunctions B S hS f V
            ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V) r * x) =
          pullbackToGlobalFunctions B S hS W T g r *
            directImageSectionsToGlobalFunctions B S hS f V x
        rw [map_mul, hcomm] }
  have : _root_.IsNoetherian R₀
      ((pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V)) :=
    isNoetherian_of_injective L (injective_directImageSectionsToGlobalFunctions B S hS f V)
  exact (inferInstance : Module.Finite R₀
    ((pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V)))

/-- **The integral closure of `𝒪_Y` in `f_* 𝒪_X` is a finite `𝒪_Y`-algebra**, for `f` proper
and `Y` locally Noetherian: its sections over an affine étale chart are a submodule of those of
`f_* 𝒪_X`, which are finite over the Noetherian ring of the chart. -/
theorem isFinite_integralClosureSheaf_pushforwardAlgebra_of_isProper (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))).IsFinite := by
  intro V hV
  have : IsLocallyNoetherian (unop ((SmallEtale.toOver B S hS Y.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op V))) :=
    isLocallyNoetherian_chartScheme B S hS Y hY V
  have : IsAffine (unop ((SmallEtale.toOver B S hS Y.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op V))) := hV
  have : IsNoetherianRing ((structureSheaf B S hS Y.1 Y.2).obj.obj (op V)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let A := pushforwardAlgebra B S hS (Over.mk f)
  let := (A.algebraMap (op V)).toAlgebra
  let := ((AlgebraSheaf.integralClosureSheaf A).algebraMap (op V)).toAlgebra
  have : Module.Finite ((structureSheaf B S hS Y.1 Y.2).obj.obj (op V))
      (A.right.obj.obj (op V)) :=
    finite_pushforwardAlgebra_algebraMap_of_isProper B S hS f hf hY V hV
  have : _root_.IsNoetherian ((structureSheaf B S hS Y.1 Y.2).obj.obj (op V))
      (A.right.obj.obj (op V)) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let L : (AlgebraSheaf.integralClosureSheaf A).right.obj.obj (op V) →ₗ[
      (structureSheaf B S hS Y.1 Y.2).obj.obj (op V)] A.right.obj.obj (op V) :=
    { toFun := ((AlgebraSheaf.integralClosureInclusion A).right.hom.app (op V)).hom
      map_add' := map_add _
      map_smul' := fun _ _ => rfl }
  have : _root_.IsNoetherian ((structureSheaf B S hS Y.1 Y.2).obj.obj (op V))
      ((AlgebraSheaf.integralClosureSheaf A).right.obj.obj (op V)) :=
    isNoetherian_of_injective L (AlgebraSheaf.integralClosureInclusion_app_injective A (op V))
  exact (inferInstance : Module.Finite ((structureSheaf B S hS Y.1 Y.2).obj.obj (op V))
    ((AlgebraSheaf.integralClosureSheaf A).right.obj.obj (op V)))

/-- **Stacks 0A1B, clause (2): `π : Y' ⟶ Y` is finite.**  For a proper morphism `f : X ⟶ Y` of
algebraic spaces with `Y` locally Noetherian, the normalization `ν : Y' ⟶ Y` of `Y` in `X`
(Stacks 0822) is a finite morphism: it is the relative spectrum of the integral closure `𝒪'` of
`𝒪_Y` in `f_* 𝒪_X`, which is a finite `𝒪_Y`-algebra. -/
@[stacks 0A1B "part (2): for f proper with Y locally Noetherian, the morphism pi : Y' -> Y \
from the normalization of Y in X (Stacks 0822), through which f factors as X -> Y' -> Y, is \
finite"]
theorem isFinite_normalizationInQcqsHom_of_isProper (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsFinite B S hS (normalizationInQcqsHom B S hS f hf.2.1.2
      (isQuasiSeparated_of_isSeparated B S hS hf.1)).hom :=
  isFinite_chartRelativeSpecQuotientHom B S hS Y _ _
    (isFinite_integralClosureSheaf_pushforwardAlgebra_of_isProper B S hS f hf hY) _ _
    (isPullback_chosenAtlasPair B S hS Y) (surjective_chosenAtlasPairTarget B S hS Y) _ _ _

end Proper

end AlgebraicGeometry.Space

end
