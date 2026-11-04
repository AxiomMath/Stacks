module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareFlat
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareIdeal
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareStrict
public import StacksFrontier.Deformation.ToposThickening.QuotientLiftObstructionCriterion
public import StacksFrontier.Deformation.ToposThickening.BaseIdealTensorShortExact
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseFlatness
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientLiftBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientLiftQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation

/-!
# Obstructions for quotients

Stacks Remark 0CZU. In Situation 082M (`AlgebraicGeometry.Space.QuotientSituation`), assume that
`F` is flat over the base `Y`, and let `h : T ⟶ T'` be a first order thickening of schemes over
`Y` with ideal sheaf `𝒥`. Write `i : X_T ⟶ X_{T'}`, `p : X_T ⟶ T`, `f' : X_{T'} ⟶ T'` and
`t : T ⟶ T'`. The remark asserts:

1. `X_T ⊂ X_{T'}` is a first order thickening whose ideal `I` is a quotient of `f_T^*𝒥`:
   `AlgebraicGeometry.Space.QuotientSituation.isFirstOrderThickening_range_relativeMap` and
   `AlgebraicGeometry.Space.QuotientSituation.isStrict_relativeSquare`.
2. `0 ⟶ f_T^*𝒥 ⊗ F_T ⟶ F_{T'} ⟶ F_T ⟶ 0` is exact:
   `AlgebraicGeometry.Space.QuotientSituation.reductionShortComplex_relativeSquare_shortExact`.
3. `f_T^*𝒥 ⊗ F_T = I ⊗ F_T` (Stacks 08MQ):
   `AlgebraicGeometry.Space.QuotientSituation.isIso_baseIdealTensorToIdealTensor_relativeSquare`.
4. For `x ∈ Q(T)` given by `0 ⟶ K ⟶ F_T ⟶ Q ⟶ 0`, the sequence
   `0 ⟶ K ⊗ 𝒥 ⟶ F_T ⊗ 𝒥 ⟶ Q ⊗ 𝒥 ⟶ 0` is exact:
   `AlgebraicGeometry.Space.QuotientSituation.obstructionKernel_baseIdealTensor_shortExact`.
5. The canonical extension `0 ⟶ Q ⊗ 𝒥 ⟶ π⁻¹(K)/i(K ⊗ 𝒥) ⟶ K ⟶ 0` is short exact
   (`AlgebraicGeometry.Space.QuotientSituation.quotientObstructionExtension_shortExact`) and
   defines `o_x(T') ∈ Ext¹(K, Q ⊗ 𝒥)`
   (`AlgebraicGeometry.Space.QuotientSituation.quotientObstruction`).
6. `o_x(T') = 0` if and only if `x` lifts to `x' ∈ Q(T')`:
   `AlgebraicGeometry.Space.QuotientSituation.quotientObstruction_eq_zero_iff`.
7. If `x ∈ Q^{fp}(T)` then every such lift lies in `Q^{fp}(T')` (Stacks 08VU):
   `QuotientSituation.mem_finitePresentationQuotients_of_quotientPullback_eq`.

## Implementation notes

The morphisms of small étale ringed topoi of Stacks 03G8 are pseudo-functorial only, so the
square `f' ∘ i ≅ t ∘ p` of ringed topoi does not commute on the nose. The remark is therefore
read through the relative square of
`AlgebraicGeometry.Space.QuotientSituation.relativeSquare_comm`, whose base is the small étale
topos of `X_{T'}` with the sheaves of rings `f'⁻¹𝒪_{T'}` and `f'⁻¹t_*𝒪_T`. There, `f_T^*𝒥` is
the pullback along `f̃ : X_T ⟶ (X_{T'}, f'⁻¹t_*𝒪_T)` of the ideal `f'⁻¹𝒥`, and
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso` identifies it
with `p^*𝒥`. Following the remark, modules on `X_{T'}` and `X_T` are compared through
`F_{T'}|_{X_T} ≅ F_T`: `K` is read on `F_{T'}|_{X_T}` as
`AlgebraicGeometry.Space.QuotientSituation.obstructionKernel`.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
-- The import closure carries sheafification instances at a free module universe, on which the
-- search for `Mono` of an isomorphism stalls.
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
-- The `Ext` universe is the one the caller supplies; Mathlib's instance deriving `HasExt` from
-- `IsGrothendieckAbelian` meets instances at a free module universe and stalls.
attribute [-instance] CategoryTheory.IsGrothendieckAbelian.hasExt

universe e u

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) (hF : IsFlatOver B S hS D.X.2 D.f.hom D.F)
  {T T' : SchemesOver D.Y} (h : T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- The small étale site of `X_{T'}`, read as the site of the base `(X_{T'}, f'⁻¹𝒪_{T'})` of the
relative square, has sheaf composition with the forgetful functor of abelian groups. -/
instance (priority := 10000) relBaseTop_hasSheafCompose_forget :
    (relBaseTop (smallEtaleRingedToposHom B S hS (D.projection T'))).J.HasSheafCompose
      (forget AddCommGrpCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS (D.space T').1).HasSheafCompose
    (forget AddCommGrpCat.{u}))

/-- Sheafification of abelian presheaves on the site of the base `(X_{T'}, f'⁻¹𝒪_{T'})` of the
relative square; see
`AlgebraicGeometry.Space.QuotientSituation.relBaseTop_hasSheafCompose_forget`. -/
instance (priority := 10000) relBaseTop_hasWeakSheafify : HasWeakSheafify
    (relBaseTop (smallEtaleRingedToposHom B S hS (D.projection T'))).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS (D.space T').1) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences of abelian presheaves on the site of the base
`(X_{T'}, f'⁻¹𝒪_{T'})` of the relative square; see
`AlgebraicGeometry.Space.QuotientSituation.relBaseTop_hasSheafCompose_forget`. -/
instance (priority := 10000) relBaseTop_wEqualsLocallyBijective :
    (relBaseTop (smallEtaleRingedToposHom B S hS (D.projection T'))).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B S hS (D.space T').1).WEqualsLocallyBijective
    AddCommGrpCat.{u})

include hF in
/-- `F_{T'}` is flat over the base of the relative square: it is flat over `T'` (Stacks 05VW),
read through the structure map of `X_{T'} ⟶ T'`. -/
theorem isFlat_baseChangeModule_relBaseRight (T' : SchemesOver D.Y) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose (smallEtaleRingedTopos B S hS (D.space T')).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
          (relBaseRight
            (smallEtaleRingedToposHom B S hS (D.projection T'))).fSharpInverseImage)).obj
        (D.baseChangeModule T')) := by
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.sourceProjection T') D.F D.quasicoherent
  exact (isFlat_restrictScalars_relBaseRight_iff
    (smallEtaleRingedToposHom B S hS (D.projection T')) (D.baseChangeModule T')).2
    ((isFlatOver_iff_isFlat_restrictScalars B S hS (D.projection T') (D.baseChangeModule T')).1
      (D.isFlatOver_baseChangeModule hF T'))

/-- **The quotient `F_T ⟶ Q` read on `F_{T'}|_{X_T}`**: the image of `K ⊂ F_T` under the
identification `F_T ≅ F_{T'}|_{X_T}` of Stacks 082N. -/
abbrev obstructionKernel (K : Subobject (D.baseChangeModule T)) :
    Subobject ((modulePullback B S hS (D.relativeMap h)).obj (D.baseChangeModule T')) :=
  (Subobject.map (D.restrictBaseChangeModuleIso h).inv).obj K

/-- `Q`, read on `F_{T'}|_{X_T}`, is flat over `𝒪_T` as a sheaf of modules. -/
private theorem isFlat_restrictScalars_cokernel {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose (smallEtaleRingedTopos B S hS (D.space T)).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
          (smallEtaleRingedToposHom B S hS (D.projection T)).fSharpInverseImage)).obj
        (cokernel (D.obstructionKernel h K).arrow)) := by
  have := hK.1
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
    ((SheafOfModules.restrictScalars _).mapIso
      (Subobject.cokernelArrowMapIso (D.restrictBaseChangeModuleIso h).symm K).symm)
    ((isFlatOver_iff_isFlat_restrictScalars B S hS (D.projection T) _).1 hK.2)

variable [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))]

/-- **The obstruction class `o_x(T') ∈ Ext¹_{𝒪_{X_T}}(K, Q ⊗_{𝒪_T} 𝒥)` of Remark 0CZU**, for the
quotient `x = (F_T ⟶ F_T/K)`: the class of the canonical extension
`0 ⟶ Q ⊗_{𝒪_T} 𝒥 ⟶ π⁻¹(K)/i(K ⊗_{𝒪_T} 𝒥) ⟶ K ⟶ 0`
(`AlgebraicGeometry.Space.QuotientSituation.quotientObstructionExtension_shortExact`). It lives in
`Ext¹(K, Q ⊗ f_T^*𝒥)`, with `K` read on `F_{T'}|_{X_T}`
(`AlgebraicGeometry.Space.QuotientSituation.obstructionKernel`) and `f_T^*𝒥` presented through
the relative square
(`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`). -/
def quotientObstruction (K : Subobject (D.baseChangeModule T)) :=
  quotientLiftObstruction.{_, _, _, _, _, _, _, _, _, _, _, e}
    (smallEtaleRingedToposHom B S hS (D.relativeMap h)) (D.relativeSquareThickening h)
    (D.relativeSquareLeft h) (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
    (D.isFlat_baseChangeModule_relBaseRight hF T') (D.obstructionKernel h K)

/-- The quotient of `F_{T'}|_{X_T}` by the transported kernel is the quotient `Q = F_T/K`. -/
def obstructionKernelCokernelIso (K : Subobject (D.baseChangeModule T)) :
    cokernel (D.obstructionKernel h K).arrow ≅ D.quotientModule T K :=
  Subobject.cokernelArrowMapIso (D.restrictBaseChangeModuleIso h).symm K

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
/-- The quotient `Q` of `x ∈ Q(T)`, read on `F_{T'}|_{X_T}`, is quasi-coherent. -/
theorem isQuasicoherentOnSite_cokernel_obstructionKernel {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) : (cokernel (D.obstructionKernel h K).arrow).IsQuasicoherentOnSite :=
  hK.1.of_iso (D.obstructionKernelCokernelIso h K).symm

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
include hh in
/-- **`Q` is flat over `𝒪_T`, in the form Remark 0CZU uses on the relative square**: its direct
image to `X_{T'}` is flat over the base along `f̃`. -/
theorem isFlatOverBase_obstructionKernel {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) :
    IsFlatOverBase.{u, u + 1, u, u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (D.relativeMap h)) (D.relativeSquareLeft h)
      ((pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS (D.relativeMap h)).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O)).obj
          (cokernel (D.obstructionKernel h K).arrow)) := by
  have := D.isQuasicoherentOnSite_cokernel_obstructionKernel h hK
  have := hK.1
  refine (D.isFlatOver_iff_isFlatOverBase_relativeSquareLeft h hh
    (cokernel (D.obstructionKernel h K).arrow)).1 ?_
  exact (isFlatOver_iff_isFlat_restrictScalars B S hS (D.projection T)
    (cokernel (D.obstructionKernel h K).arrow)).2 (D.isFlat_restrictScalars_cokernel h hK)

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
include hh in
/-- `X_T ⟶ X_{T'}` is affine, being a closed immersion (Stacks 07U2). -/
theorem isAffineHom_relativeMap : IsAffineHom B S hS (D.relativeMap h).hom := by
  have := D.mono_relativeMap h hh
  exact isAffineHom_of_isClosedImmersion B S hS _
    (IsThickeningHom.isClosedImmersion (i := D.relativeMap h)
      ⟨inferInstance, (D.isFirstOrderThickening_range_relativeMap h hh).1⟩)

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
include hF hh in
/-- **A lift of the quotient in the sense of ringed topoi is a lift in the functor of quotients**:
for `K ∈ Q(T)` and `K' ⊂ F_{T'}`, `F_{T'}/K'` is flat over the base of the relative square and
restricts to `Q` exactly when `K' ∈ Q(T')` and `K'` pulls back to `K` along `T ⟶ T'`
(Stacks 082N). -/
theorem isQuotientLift_obstructionKernel_iff {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) (K' : Subobject (D.baseChangeModule T')) :
    IsQuotientLift.{u, u + 1, u, u, u + 1, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (D.relativeMap h))
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
        (D.baseChangeModule T') (D.obstructionKernel h K) K' ↔
      K' ∈ D.quotients T' ∧ D.quotientPullback h K' = K := by
  constructor
  · intro hK'
    have hqc : (cokernel K'.arrow).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_cokernel_of_isQuotientLift (D.relativeMap h)
        (D.relativeSquareThickening h) (D.relativeSquareLeft h)
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
        (D.relativeMapFirstOrderThickening h hh)
        (D.relativeSquareThickeningFirstOrderThickening h hh) (D.relativeSquare_comm h)
        (D.isAffineHom_relativeMap h hh) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
        (D.isFlat_baseChangeModule_relBaseRight hF T') (D.obstructionKernel h K)
        (D.isQuasicoherentOnSite_cokernel_obstructionKernel h hK)
        (by
          have := D.isQuasicoherentOnSite_cokernel_obstructionKernel h hK
          exact D.isQuasicoherentOnSite_baseIdealTensor_relativeSquare h hh
            (cokernel (D.obstructionKernel h K).arrow)) hK'
    have := hqc
    exact ⟨⟨hqc, (isFlatOver_iff_isFlat_restrictScalars B S hS (D.projection T')
      (cokernel K'.arrow)).2 ((isFlat_restrictScalars_relBaseRight_iff
        (smallEtaleRingedToposHom B S hS (D.projection T')) (cokernel K'.arrow)).1 hK'.1)⟩,
      (D.quotientPullback_eq_iff h K' K).2 hK'.2⟩
  · rintro ⟨⟨hqc, hfl⟩, hpb⟩
    have := hqc
    exact ⟨(isFlat_restrictScalars_relBaseRight_iff
      (smallEtaleRingedToposHom B S hS (D.projection T')) (cokernel K'.arrow)).2
      ((isFlatOver_iff_isFlat_restrictScalars B S hS (D.projection T') (cokernel K'.arrow)).1 hfl),
      (D.quotientPullback_eq_iff h K' K).1 hpb⟩

/-- **Remark 0CZU: the obstruction vanishes exactly when the quotient lifts.** For `x ∈ Q(T)`
given by `K ⊂ F_T`, `o_x(T') = 0` if and only if there is `x' ∈ Q(T')` restricting to `x`. -/
@[stacks 0CZU]
theorem quotientObstruction_eq_zero_iff {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) :
    D.quotientObstruction hF h hh K = 0 ↔ ∃ K' ∈ D.quotients T', D.quotientPullback h K' = K :=
  (quotientLiftObstruction_eq_zero_iff (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
    (D.isFlat_baseChangeModule_relBaseRight hF T') (D.obstructionKernel h K)
    (D.isFlatOverBase_obstructionKernel h hh hK)).trans
    ⟨fun ⟨K', hK'⟩ => ⟨K', (D.isQuotientLift_obstructionKernel_iff hF h hh hK K').1 hK'⟩,
      fun ⟨K', hm, hp⟩ => ⟨K', (D.isQuotientLift_obstructionKernel_iff hF h hh hK K').2 ⟨hm, hp⟩⟩⟩

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
include hF hh in
/-- **Remark 0CZU, finite presentation (Stacks 08VU).** If `x ∈ Q^{fp}(T)`, every lift
`x' ∈ Q(T')` of `x` lies in `Q^{fp}(T')`. -/
@[stacks 0CZU]
theorem mem_finitePresentationQuotients_of_quotientPullback_eq
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.finitePresentationQuotients T)
    {K' : Subobject (D.baseChangeModule T')} (hK' : K' ∈ D.quotients T')
    (hpb : D.quotientPullback h K' = K) :
    K' ∈ D.finitePresentationQuotients T' := by
  refine ⟨hK', ?_⟩
  have : (D.quotientModule T' K').IsFinitePresentation :=
    isFinitePresentation_cokernel_of_isQuotientLift
    (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h) (D.baseChangeModule T') (D.obstructionKernel h K)
    (D.isStrict_relativeSquare h hh)
    ((D.isQuotientLift_obstructionKernel_iff hF h hh hK.1 K').2 ⟨hK', hpb⟩)
    (Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (D.obstructionKernelCokernelIso h K).symm
      (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _ hK.2))
  exact SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation _

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
include hh in
/-- `Q` is flat over the base of the relative square: `Q` is flat over `T`, and the structure map
of `f̃` differs from that of `X_T ⟶ T` by the isomorphism `i⁻¹f'⁻¹t_*𝒪_T ≅ p⁻¹𝒪_T`. -/
theorem isFlat_relativeSquareLeft_cokernel_obstructionKernel {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose (smallEtaleRingedTopos B S hS (D.space T)).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (D.relativeSquareLeft h).fSharpInverseImage)).obj
        (cokernel (D.obstructionKernel h K).arrow)) := by
  have := D.isQuasicoherentOnSite_cokernel_obstructionKernel h hK
  have := hK.1
  refine (isFlat_restrictScalars_relBaseLeft_iff (θ := D.relativeSquareIso h)
    (squareRingNatIso B S hS (D.relativeMap h) (D.projection T') (D.projection T)
      ((schemeSpaceFunctor B S hS).map h.left) (D.relativeMap_comp_projection h))
    (D.testSchemeFirstOrderThickening h hh) rfl _).2 ?_
  exact D.isFlat_restrictScalars_cokernel h hK

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
/-- **Remark 0CZU: `0 ⟶ f_T^*𝒥 ⊗ F_T ⟶ F_{T'} ⟶ F_T ⟶ 0` is exact.** Since `F_{T'}` is flat
over `T'`, the reduction `π : F_{T'} ⟶ F_T` (read on `X_{T'}`) has kernel `f_T^*𝒥 ⊗ F_T`, embedded
by `i`. -/
@[stacks 0CZU]
theorem reductionShortComplex_relativeSquare_shortExact :
    (reductionShortComplex (smallEtaleRingedToposHom B S hS (D.relativeMap h))
      (D.relativeSquareThickening h) (D.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
      (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquare_comm h) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
      (D.isFlat_baseChangeModule_relBaseRight hF T')).ShortExact :=
  reductionShortComplex_shortExact (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
    (D.isFlat_baseChangeModule_relBaseRight hF T')

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
include hF in
/-- **Remark 0CZU: `f_T^*𝒥 ⊗ F_T = I ⊗ F_T` (Stacks 08MQ).** The canonical comparison of
`f_T^*𝒥 ⊗ F_T` with `I ⊗ F_T`, for `F_T = F_{T'}|_{X_T}`, is an isomorphism. -/
@[stacks 0CZU]
theorem isIso_baseIdealTensorToIdealTensor_relativeSquare :
    IsIso (baseIdealTensorToIdealTensor (smallEtaleRingedToposHom B S hS (D.relativeMap h))
      (D.relativeSquareThickening h) (D.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
      (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquare_comm h)
      ((modulePullback B S hS (D.relativeMap h)).obj (D.baseChangeModule T'))) :=
  isIso_baseIdealTensorToIdealTensor (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
    (D.isFlat_baseChangeModule_relBaseRight hF T')

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
/-- **Remark 0CZU: `0 ⟶ K ⊗_{𝒪_T} 𝒥 ⟶ F_T ⊗_{𝒪_T} 𝒥 ⟶ Q ⊗_{𝒪_T} 𝒥 ⟶ 0` is exact**, `Q` being
flat over `T`. Here `G ⊗_{𝒪_T} 𝒥 = f_T^*𝒥 ⊗ G`. -/
@[stacks 0CZU]
theorem obstructionKernel_baseIdealTensor_shortExact {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) :
    ((ShortComplex.mk (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.space T)).O)) (D.obstructionKernel h K).arrow
        (cokernel.π (D.obstructionKernel h K).arrow)
      (cokernel.condition _)).map (baseIdealTensor.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (D.relativeSquareThickening h) (D.relativeSquareLeft h)
        (D.relativeSquareThickeningFirstOrderThickening h hh))).ShortExact :=
  shortExact_map_baseIdealTensor_of_isFlat_cokernel (D.relativeSquareThickening h)
    (D.relativeSquareLeft h) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.obstructionKernel h K) (D.isFlat_relativeSquareLeft_cokernel_obstructionKernel h hh hK)

omit [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))] in
/-- **Remark 0CZU: the canonical extension
`0 ⟶ Q ⊗_{𝒪_T} 𝒥 ⟶ π⁻¹(K)/i(K ⊗_{𝒪_T} 𝒥) ⟶ K ⟶ 0` of `𝒪_{X_T}`-modules is short exact.** Its
class is `AlgebraicGeometry.Space.QuotientSituation.quotientObstruction`. -/
@[stacks 0CZU]
theorem quotientObstructionExtension_shortExact (K : Subobject (D.baseChangeModule T)) :
    (quotientLiftExtension (smallEtaleRingedToposHom B S hS (D.relativeMap h))
      (D.relativeSquareThickening h) (D.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
      (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquare_comm h) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
      (D.isFlat_baseChangeModule_relBaseRight hF T') (D.obstructionKernel h K)).ShortExact :=
  quotientLiftExtension_shortExact (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h) (D.baseChangeModule T') (D.isStrict_relativeSquare h hh)
    (D.isFlat_baseChangeModule_relBaseRight hF T') (D.obstructionKernel h K)

end AlgebraicGeometry.Space.QuotientSituation
