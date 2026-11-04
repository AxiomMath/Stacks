module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartBHocolim
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.BaseChangeUnits
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PullbackHocolim
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.HocolimUnit

/-!
# Base change of the representing object of [Stacks, Tag 08IF] (B), over the open `U`

Let `g : U ⟶ S`, `𝒢` and `E = hocolim Eₙ` be as in
`Stacks.Cohomology.RelativeExt.PartBApproxSystem`, with `L = hocolim Lₙ` the representing object
of [Stacks, Tag 08IF] (B) built from the perfect stages `Lₙ = Rg_*(Eₙ^∨ ⊗^L 𝒢)^∨`. Let
`h : U' ⟶ U`, `g' : U' ⟶ S'`, `g_S : S' ⟶ S` be such that the perfect stages base change
(`Stacks.Cohomology.RelativeExtCanonical.StageData`, with a natural family of base-change maps
`bc`; for a cartesian square of schemes this is [Stacks, Tag 0A1D]). Then there is

`η' : L(h)^*E ⟶ Φ'(L(g_S)^*L)`, `Φ' = L(g')^*(-) ⊗^L 𝒢'`,

such that composing with `η'` identifies `Hom(L(g_S)^*L, N)` with `Hom(L(h)^*E, Φ' N)` for every
`N` in `D^+_{QCoh}(𝒪_{S'})`: the formation of `L` commutes with base change, which is
[Stacks, Tag 0DJS] over `U`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.exists_baseChange_partBHocolimUnit`: there is a map
  `η' : L(h)^*E ⟶ Φ'(L(g_S)^*L)` composing with which identifies `Hom(L(g_S)^*L, N)` with
  `Hom(L(h)^*E, Φ' N)` for every `N` in `D^+_{QCoh}(𝒪_{S'})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

variable {U S S' U' : Scheme.{u}} {g : U ⟶ S} {gS : S' ⟶ S} {g' : U' ⟶ S'} {h : U' ⟶ U}
  {G : CochainComplex (TModules U.toRingedSpace) ℤ}
  {G' : CochainComplex (TModules U'.toRingedSpace) ℤ}
  (hG : IsBoundedFlatOver g.toLRSHom.toShHom G) (hG' : IsBoundedFlatOver g'.toLRSHom.toShHom G')
  {bc : BaseChangeFamily g.toLRSHom.toShHom gS.toLRSHom.toShHom g'.toLRSHom.toShHom
    h.toLRSHom.toShHom G G'}
  {E : DStd U} (D : PartBApproxSystem g G E)
  [HasCoproduct (partBSystem D).obj] {L : DStd S} {d : ∀ n, (partBSystem D).obj n ⟶ L}

/-- The derived pullback `L(φ)^*` at the standard model of both derived categories. -/
local notation "derivedPullbackStd " φ:max =>
  @derivedPullback _ _ φ (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _

/-- **`η : E ⟶ Φ(L)` represents `N ↦ Hom(E, Φ N)` on `D^+_{QCoh}(𝒪_S)`**: composing with `η`
identifies `Hom(L, N)` with `Hom(E, Φ N)` for every bounded below `N` with quasi-coherent
cohomology. -/
def IsRepresentingUnit {S U : Scheme.{u}} (Φ : DStd S ⥤ DStd U) {E : DStd U} {L : DStd S}
    (η : E ⟶ Φ.obj L) : Prop :=
  ∀ (N : DStd S) (_ : qcohDerived S N) (m : ℤ)
    (_ : @DerivedCategory.IsGE _ _ _ (HasDerivedCategory.standard _) N m),
    Function.Bijective (fun ψ : L ⟶ N ↦ η ≫ Φ.map ψ)

include hG in
/-- There is a map `η' : L(h)^*E ⟶ Φ'(L(g_S)^*L)`, `Φ' = L(g')^*(-) ⊗^L 𝒢'`, composing with which
identifies `Hom(L(g_S)^*L, N)` with `Hom(L(h)^*E, Φ' N)` for every `N` in `D^+_{QCoh}(𝒪_{S'})`. -/
theorem exists_baseChange_partBHocolimUnit (hbc : bc.IsNatural) (b : ℤ)
    (hb : G.IsStrictlyGE b) (hb' : G'.IsStrictlyGE b)
    (hL : IsHomotopyColimitWith (partBSystem D) L d)
    [∀ i : ℤ, HasColimit (partBSystem D ⋙ @DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) _ _ (HasDerivedCategory.standard _) i)]
    (hcolim : PartBHomologyColimit D L d)
    (hdata : ∀ n, StageData g.toLRSHom.toShHom gS.toLRSHom.toShHom g'.toLRSHom.toShHom
      h.toLRSHom.toShHom bc (qcohDerived S') (D.sys.obj n))
    [HasCoproduct (D.sys ⋙ derivedPullbackStd h.toLRSHom.toShHom).obj]
    [HasCoproduct (partBSystem D ⋙ derivedPullbackStd gS.toLRSHom.toShHom).obj] :
    ∃ η' : (derivedPullbackStd h.toLRSHom.toShHom).obj E ⟶
        (pullbackTensorDerivedFunctor hG').obj ((derivedPullbackStd gS.toLRSHom.toShHom).obj L),
      IsRepresentingUnit (pullbackTensorDerivedFunctor hG') η' := by
  have := D.hasCoproduct
  have hE' := isHomotopyColimitWith_derivedPullback h.toLRSHom.toShHom D.hocolim
  have hL' := isHomotopyColimitWith_derivedPullback gS.toLRSHom.toShHom hL
  let u' : ∀ n, (D.sys ⋙ derivedPullbackStd h.toLRSHom.toShHom).obj n ⟶
      (pullbackTensorDerivedFunctor hG').obj
        ((partBSystem D ⋙ derivedPullbackStd gS.toLRSHom.toShHom).obj n) :=
    fun n ↦ baseChangeStageUnit hG' (hdata n)
  have hu' : ∀ n, (D.sys ⋙ derivedPullbackStd h.toLRSHom.toShHom).map (homOfLE (Nat.le_succ n)) ≫
      u' (n + 1) = u' n ≫ (pullbackTensorDerivedFunctor hG').map
        ((partBSystem D ⋙ derivedPullbackStd gS.toLRSHom.toShHom).map
          (homOfLE (Nat.le_succ n))) := by
    intro n
    simp only [Functor.comp_map, partBSystem_map_succ]
    exact baseChangeStageUnit_comp hG' hbc (hdata n) (hdata (n + 1))
      (D.sys.map (homOfLE (Nat.le_succ n)))
  obtain ⟨η', hη'⟩ := exists_unit_of_isHomotopyColimitWith
    (pullbackTensorDerivedFunctor hG') hE' hL' u' hu'
  refine ⟨η', fun N hN m hm ↦ ?_⟩
  have := hb'
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing U'.toSheafedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S'.toSheafedSpace))
  refine bijective_unit_comp_map (pullbackTensorDerivedFunctor hG') b
    (fun N m hm ↦ isGE_pullbackTensorDerivedFunctor_obj g'.toLRSHom.toShHom hG' b N m hm)
    u' η' hη' (qcohDerived S')
    (fun n N hN ↦ bijective_baseChangeStageUnit_comp hG' (hdata n) N hN) (fun k ↦ ?_) N hN m hm
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 - k ≤ (n : ℤ) ∧ 1 - k - b ≤ (n : ℤ) :=
    ⟨(max (1 - k) (1 - k - b)).toNat, by lia, by lia⟩
  refine ⟨n, ?_, ?_⟩
  · exact isIso_truncGE_map_of_isIso_homologyFunctor_map _ k fun i hi ↦
      isIso_homologyFunctor_map_of_isIso_truncGE_map _ _
        (isIso_truncGE_map_derivedPullback h.toLRSHom.toShHom (D.c n) (-(n : ℤ)) (D.trunc n)) i
        (by lia)
  · have h1 := isIso_truncGE_map_derivedPullback gS.toLRSHom.toShHom (d n) (k - 1)
      (isIso_truncGE_partBCoprojection D hG b hb hcolim n (k - 1) (by lia))
    rwa [sub_add_cancel] at h1

end Stacks.Cohomology.RelativeExtCanonical

end
