module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartB
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PartBBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.StageDataSquare

/-!
# Base change of the representing object of [Stacks, Tag 08IF] (B), over the chosen open

Let `f : X ⟶ S`, `E`, `𝒢` be as in [Stacks, Tag 08IF], with the witness
`Stacks.Cohomology.RelativeExt.PartBWitness` of the construction of
`L = Stacks.Cohomology.RelativeExt.pseudoCoherentRepresentative`: an open `V ⊇ Supp 𝒢`, the
approximation of `E|_V`, and `L = hocolim Lₙ`. For a cartesian square `X' → X` over `S' → S`, put
`V' = (g')^{-1}V` with `h : V' ⟶ V`. Then there is

`η' : L(h)^*(E|_V) ⟶ Φ'(Lg^*L)`, `Φ' = L(f'|_{V'})^*(-) ⊗^L (h^*(𝒢|_V))`,

identifying `Hom(Lg^*L, N)` with `Hom(L(h)^*(E|_V), Φ' N)` for every `N ∈ D^+_{QCoh}(𝒪_{S'})`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.isPullback_restrict_comp`
* `Stacks.Cohomology.RelativeExtCanonical.exists_isRepresentingUnit_baseChange_witness`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] hasSheafifyOpensSpace wEqualsLocallyBijectiveOpensSpace

/-- The restriction of a cartesian square to an open of the upper right corner and its preimage is
cartesian. -/
theorem isPullback_restrict_comp {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g) (V : X.Opens) :
    IsPullback (g' ∣_ V) ((g' ⁻¹ᵁ V).ι ≫ f') (V.ι ≫ f) g :=
  IsPullback.paste_vert (isPullback_morphismRestrict g' V) hsq

section Witness

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} [IsNoetherian S] [LocallyOfFiniteType f]
  {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g)
  {E : DStd X} {G : CochainComplex (TModules X.toRingedSpace) ℤ}
  {hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G}
  (W : PartBWitness f E G hG)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The terms of `𝒢|_V` are quasi-coherent. -/
theorem isQuasicoherent_restrictComplex_X (i : ℤ) :
    ((restrictComplex W.V.ι G).X i).IsQuasicoherent := by
  have : (G.X i).IsCoherent := hG.isCoherent i
  have hq : (G.X i).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    W.V.ι.toLRSHom.toShHom (G.X i) hq

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `𝒢|_V` is bounded and flat over `S`. -/
theorem isBoundedFlatOver_witness :
    IsBoundedFlatOver (W.V.ι ≫ f).toLRSHom.toShHom (restrictComplex W.V.ι G) :=
  isBoundedFlatOver_restrictComplex (isBoundedFlatOver_of_flatProperSupportComplex hG)

omit [AlgebraicGeometry.IsNoetherian S] in
include hsq in
/-- `h^*(𝒢|_V)` is bounded and flat over `S'`. -/
theorem isBoundedFlatOver_witness_pullback :
    IsBoundedFlatOver ((g' ⁻¹ᵁ W.V).ι ≫ f').toLRSHom.toShHom
      ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex (g' ∣_ W.V).toLRSHom.toShHom).obj
        (restrictComplex W.V.ι G)) :=
  isBoundedFlatOver_pullbackComplex (isPullback_restrict_comp hsq W.V) _
    (isQuasicoherent_restrictComplex_X W) (isBoundedFlatOver_witness W)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `h^*(𝒢|_V)` vanishes in degrees below the bound of `𝒢`. -/
theorem isStrictlyGE_witness_pullback :
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex (g' ∣_ W.V).toLRSHom.toShHom).obj
      (restrictComplex W.V.ι G)).IsStrictlyGE W.b := by
  have := RingedSpaceModuleAdjunction.modulePullback_additive (g' ∣_ W.V).toLRSHom.toShHom
  have hb := isStrictlyGE_restrictComplex (j := W.V.ι) W.b W.hb
  exact (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦
    Functor.map_isZero (RingedSpaceModuleAdjunction.modulePullback (g' ∣_ W.V).toLRSHom.toShHom)
      ((CochainComplex.isStrictlyGE_iff _ W.b).1 hb i hi)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **Base change of the representing object over the chosen open**: there is
`η' : L(h)^*(E|_V) ⟶ Φ'(Lg^*L)` representing `N ↦ Hom(L(h)^*(E|_V), Φ' N)` on
`D^+_{QCoh}(𝒪_{S'})`. -/
theorem exists_isRepresentingUnit_baseChange_witness :
    ∃ η' : (stdPullback (g' ∣_ W.V).toLRSHom.toShHom).obj ((restrictDerived W.V.ι).obj E) ⟶
        (pullbackTensorDerivedFunctor (isBoundedFlatOver_witness_pullback hsq W)).obj
          ((stdPullback g.toLRSHom.toShHom).obj W.L),
      IsRepresentingUnit (pullbackTensorDerivedFunctor (isBoundedFlatOver_witness_pullback hsq W))
        η' := by
  have := W.quasiCompact
  have := W.quasiSeparated
  let := W.hasCoproduct
  let := W.hasColimit
  have hsqV := isPullback_restrict_comp hsq W.V
  have : ∀ Y : Scheme.{u}, HasColimitsOfShape (Discrete ℕ) (DStd Y) := fun Y ↦
    @Stacks.PseudoCoherentHocolim.hasColimitsOfShape_discrete_nat_derivedCategory _
      (HasDerivedCategory.standard _)
  exact exists_baseChange_partBHocolimUnit (isBoundedFlatOver_witness W)
    (isBoundedFlatOver_witness_pullback hsq W) W.D (squareBaseChangeMap_isNatural hsqV) W.b
    (isStrictlyGE_restrictComplex W.b W.hb) (isStrictlyGE_witness_pullback W) W.hocolim
    W.homologyColimit (fun n ↦ stageData_of_isPullback hsqV (isBoundedFlatOver_witness W)
      (isQuasicoherent_restrictComplex_X W) (W.D.sys.obj n) (W.D.perfect n) (W.D.stageKPerfect n))

end Witness

end Stacks.Cohomology.RelativeExtCanonical

end
