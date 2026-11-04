module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.BaseChangeWitness
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PullbackSquareIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RestrictPhi
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PullbackTensorSupport

/-!
# Base change of the representing object of the relative `Ext`, on all of `X'`

For a cartesian square `X' → X` over `S' → S` and `L` the pseudo-coherent object of a witness
`W : PartBWitness f E G hG`, there is an identification on all of `X'`. Since `(g')^*𝒢^•` is
supported on `(g')^{-1}Z ⊆ V' = (g')^{-1}V` for a closed `Z ⊇ Supp 𝒢^•` inside `V`, restriction to
`V'` is bijective on morphisms into `Φ'(N)`, so the identification over `V'` extends to `X'`:

`Hom(Lg^*L, N) ≃ Hom(L(g')^*E, Φ'(N))`, `Φ' = L(f')^*(-) ⊗^L (g')^*𝒢^•`,

naturally in `N ∈ D^+_{QCoh}(𝒪_{S'})`.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.baseChangeHomEquiv`: the natural identification
  `Hom(Lg^*L, N) ≃ Hom(L(g')^*E, Φ'(N))` for `N ∈ D^+_{QCoh}(𝒪_{S'})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] hasSheafifyOpensSpace wEqualsLocallyBijectiveOpensSpace

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} [IsNoetherian S] [LocallyOfFiniteType f]
  {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g)
  {E : DStd X} {G : CochainComplex (TModules X.toRingedSpace) ℤ}
  {hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G}
  (W : PartBWitness f E G hG)

variable (hG) in
include hG in
omit [AlgebraicGeometry.IsNoetherian S] in
/-- The terms of `𝒢` are quasi-coherent. -/
theorem isQuasicoherent_G_X (i : ℤ) : (G.X i).IsQuasicoherent := by
  have : (G.X i).IsCoherent := hG.isCoherent i
  exact isQuasicoherent_of_isCoherent _

variable (hG) in
include hsq hG in
omit [AlgebraicGeometry.IsNoetherian S] in
/-- `(g')^*𝒢^•` is bounded and flat over `S'`. -/
theorem isBoundedFlatOver_total_pullback :
    IsBoundedFlatOver f'.toLRSHom.toShHom
      ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj G) :=
  isBoundedFlatOver_pullbackComplex hsq G (isQuasicoherent_G_X hG)
    (isBoundedFlatOver_of_flatProperSupportComplex hG)

section Total

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `Φ'(N)` is supported on `(g')^{-1}Z`. -/
theorem cohomologySupportedOn_total (N : DStd S') :
    @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _
      (structureSheafRing X'.toRingedSpace) (HasDerivedCategory.standard _) (g'.base ⁻¹' W.Z)
      ((pullbackTensorDerivedFunctor (isBoundedFlatOver_total_pullback hsq hG)).obj N) :=
  cohomologySupportedOn_pullbackTensorDerivedFunctor_obj f'.toLRSHom.toShHom _
    (isBoundedFlatOver_total_pullback hsq hG) (g'.base ⁻¹' W.Z)
    (fun q x hx ↦ isZero_stalk_modulePullback g'.toLRSHom.toShHom (G.X q) x (W.supportZ q _ hx)) N

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Restriction to `V'` is bijective on morphisms into `Φ'(N)`. -/
theorem bijective_restrict_total (N : DStd S') :
    Function.Bijective (fun φ : (stdPullback g'.toLRSHom.toShHom).obj E ⟶
        (pullbackTensorDerivedFunctor (isBoundedFlatOver_total_pullback hsq hG)).obj N ↦
      (stdPullback (g' ⁻¹ᵁ W.V).ι.toLRSHom.toShHom).map φ) :=
  bijective_derivedPullback_map_of_supportedOn (g' ⁻¹ᵁ W.V).ι (g'.base ⁻¹' W.Z)
    (W.isClosed.preimage g'.base.hom.continuous)
    (fun x hx ↦ by rw [Scheme.Opens.range_ι]; exact W.hZV hx) _ _
    (cohomologySupportedOn_total hsq W N)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The square `V' → V` over `X' → X` at the level of ringed spaces. -/
theorem restrict_toShHom_comm :
    (g' ⁻¹ᵁ W.V).ι.toLRSHom.toShHom ≫ g'.toLRSHom.toShHom =
      (g' ∣_ W.V).toLRSHom.toShHom ≫ W.V.ι.toLRSHom.toShHom :=
  (congrArg (fun k : (g' ⁻¹ᵁ W.V : Scheme.{u}) ⟶ X ↦ k.toLRSHom.toShHom)
    (morphismRestrict_ι g' W.V)).symm

/-- `L(j')^*L(g')^*E ≅ L(h)^*(E|_V)`. -/
def restrictPullbackIso :
    (stdPullback (g' ⁻¹ᵁ W.V).ι.toLRSHom.toShHom).obj ((stdPullback g'.toLRSHom.toShHom).obj E) ≅
      (stdPullback (g' ∣_ W.V).toLRSHom.toShHom).obj ((restrictDerived W.V.ι).obj E) :=
  (stdPullbackSquareIso _ _ _ _ (restrict_toShHom_comm W)).app E ≪≫
    (stdPullback (g' ∣_ W.V).toLRSHom.toShHom).mapIso
      ((restrictDerivedIsoStdPullback W.V.ι).app E).symm

/-- `Φ'_{V'}`, computed with `h^*(𝒢|_V)`, is `Φ'` followed by restriction to `V'`. -/
def restrictPhiIso :
    pullbackTensorDerivedFunctor (isBoundedFlatOver_witness_pullback hsq W) ≅
      pullbackTensorDerivedFunctor (isBoundedFlatOver_total_pullback hsq hG) ⋙
        stdPullback (g' ⁻¹ᵁ W.V).ι.toLRSHom.toShHom :=
  (pullbackTensorDerivedFunctorIsoOfIso ((g' ⁻¹ᵁ W.V).ι ≫ f').toLRSHom.toShHom
      (isBoundedFlatOver_restrictComplex (f := f') (j := (g' ⁻¹ᵁ W.V).ι)
        (isBoundedFlatOver_total_pullback hsq hG))
      (isBoundedFlatOver_witness_pullback hsq W)
      (pullbackComplexSquareIso _ _ _ _ (restrict_toShHom_comm W) G)).symm ≪≫
    pullbackTensorDerivedPullbackIso f' (g' ⁻¹ᵁ W.V).ι (isBoundedFlatOver_total_pullback hsq hG)

/-- **The base-changed identification on `X'`**: `Hom(Lg^*L, N) ≃ Hom(L(g')^*E, Φ'(N))`,
naturally in `N ∈ D^+_{QCoh}(𝒪_{S'})`. -/
def baseChangeHomEquiv :
    ShiftedHom.NaturalHomEquiv (𝟭 (DStd S'))
      (pullbackTensorDerivedFunctor (isBoundedFlatOver_total_pullback hsq hG))
      ((stdPullback g.toLRSHom.toShHom).obj W.L) ((stdPullback g'.toLRSHom.toShHom).obj E)
      (plusQCohDerived S') :=
  (naturalHomEquivOfUnit _ (plusQCohDerived S')
      (exists_isRepresentingUnit_baseChange_witness hsq W).choose
      (fun N hN ↦ (exists_isRepresentingUnit_baseChange_witness hsq W).choose_spec N hN.1
        hN.2.choose hN.2.choose_spec)).trans
    ((ShiftedHom.NaturalHomEquiv.ofIso (restrictPhiIso hsq W)).trans
      ((ShiftedHom.NaturalHomEquiv.ofIsoSource (restrictPullbackIso W)).trans
        (naturalHomEquivOfBijectiveMap _ _ (plusQCohDerived S') _
          (fun N _ ↦ bijective_restrict_total hsq W N))))

end Total

end Stacks.Cohomology.RelativeExtCanonical

end
