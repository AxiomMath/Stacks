module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PerfectStageBaseChangeCore

/-!
# The units of the perfect stages after base change

Let `f`, `g`, `f'`, `g'`, `𝒢`, `𝒢'` and `bc_E` be as for
`Stacks.Cohomology.RelativeExtCanonical.stageLBaseChangeIso`, and let `P₀ ⟶ P₁ ⟶ ⋯` be a system of
perfect objects on `X`. The units `L(g')^*Pₙ ⟶ Φ'(L'(L(g')^*Pₙ))` of the perfect stage on `X'`,
read through `Lg^*L(Pₙ) ≅ L'(L(g')^*Pₙ)`, are maps

`u'ₙ : L(g')^*Pₙ ⟶ Φ'(Lg^*L(Pₙ))`

compatible with the pulled back transition maps `L(g')^*Pₙ ⟶ L(g')^*Pₙ₊₁` and
`Lg^*L(Pₙ) ⟶ Lg^*L(Pₙ₊₁)`, and each of them identifies `Hom(Lg^*L(Pₙ), N)` with
`Hom(L(g')^*Pₙ, Φ' N)`.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.StageData`: the conditions at a perfect object under
  which the base-changed unit is defined.
* `Stacks.Cohomology.RelativeExtCanonical.baseChangeStageUnit`: the base-changed unit
  `L(g')^*P ⟶ Φ'(Lg^*L(P))`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.baseChangeStageUnit_comp`: the base-changed units are
  compatible with the transition maps.
* `Stacks.Cohomology.RelativeExtCanonical.bijective_baseChangeStageUnit_comp`: the base-changed
  unit identifies `Hom(Lg^*L(P), N)` with `Hom(L(g')^*P, Φ' N)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

variable {X S S' X' : RingedSpace.{u, u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology S'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
  {G' : CochainComplex (SheafOfModules.{u} (structureSheafRing X')) ℤ}
  (hG' : IsBoundedFlatOver f' G')
  (bc : BaseChangeFamily f g f' g' G G')
  (Q' : ObjectProperty (DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))))

/-- Conditions at a perfect object `P`: perfectness of `P`, of `L(g')^*P`, of `K(P)`,
`Lg^*K(P)` and `K'(L(g')^*P)`, invertibility of the base-change map at `P^∨`, the projection
formula on `Q'` for `L(g')^*P`, and `L'(L(g')^*P) ∈ Q'`. -/
structure StageData (P : StdDerivedModules X.sheaf) : Prop where
  hP : IsPerfectStd P
  hP' : IsPerfectStd ((stdPullback g').obj P)
  hK : IsPerfectStd (stageK f (G := G) P)
  hgK : IsPerfectStd ((stdPullback g).obj (stageK f (G := G) P))
  hK' : IsPerfectStd (stageK f' (G := G') ((stdPullback g').obj P))
  isIso_bc : IsIso (bc (Stacks.SheafOfModules.derivedDual X.sheaf P))
  hQ : ∀ N, Q' N → IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f'
    (stageSource (G := G') ((stdPullback g').obj P)) N)
  hL : Q' (stageL f' (G := G') ((stdPullback g').obj P))

variable {f g f' g' bc Q'}

/-- The isomorphism `Lg^*L(P) ≅ L'(L(g')^*P)` under the conditions `StageData` at `P`. -/
def StageData.iso {P : StdDerivedModules X.sheaf} (h : StageData f g f' g' bc Q' P) :
    (derivedPullback g).obj (stageL f (G := G) P) ≅
      stageL f' (G := G') ((derivedPullback g').obj P) :=
  haveI := h.isIso_bc
  stageLBaseChangeIso f g f' g' bc P h.hP h.hP' h.hK h.hgK h.hK'

/-- **The base-changed unit** `L(g')^*P ⟶ Φ'(Lg^*L(P))`: the unit of the perfect stage on `X'` at
`L(g')^*P`, followed by `Φ'` of `L'(L(g')^*P) ≅ Lg^*L(P)`. -/
def baseChangeStageUnit {P : StdDerivedModules X.sheaf} (h : StageData f g f' g' bc Q' P) :
    (derivedPullback g').obj P ⟶
      (pullbackTensorDerivedFunctor hG').obj ((derivedPullback g).obj (stageL f (G := G) P)) :=
  perfectStageUnit f' hG' ((derivedPullback g').obj P) h.hP' Q' h.hQ h.hK' h.hL ≫
    (pullbackTensorDerivedFunctor hG').map h.iso.inv

/-- **The base-changed unit identifies `Hom(Lg^*L(P), N)` with `Hom(L(g')^*P, Φ' N)`**, for `N`
in `Q'`. -/
theorem bijective_baseChangeStageUnit_comp {P : StdDerivedModules X.sheaf}
    (h : StageData f g f' g' bc Q' P)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))) (hN : Q' N) :
    Function.Bijective (fun ψ : (derivedPullback g).obj (stageL f (G := G) P) ⟶ N ↦
      baseChangeStageUnit hG' h ≫ (pullbackTensorDerivedFunctor hG').map ψ) := by
  have e : (fun ψ : (derivedPullback g).obj (stageL f (G := G) P) ⟶ N ↦
      baseChangeStageUnit hG' h ≫ (pullbackTensorDerivedFunctor hG').map ψ) =
      ((perfectStageDualEquiv f' hG' ((derivedPullback g').obj P) h.hP' Q' h.hQ h.hK').equiv N
        hN) ∘ (fun ψ ↦ h.iso.inv ≫ ψ) := by
    funext ψ
    simp only [Function.comp_apply, baseChangeStageUnit, Category.assoc, ← Functor.map_comp]
    rw [perfectStageDualEquiv_apply f' hG' ((derivedPullback g').obj P) h.hP' Q' h.hQ h.hK' h.hL]
  rw [e]
  exact (Equiv.bijective _).comp ⟨fun a b hab ↦ by simpa using congrArg (h.iso.hom ≫ ·) hab,
    fun y ↦ ⟨h.iso.hom ≫ y, by simp⟩⟩

/-- **The base-changed units are compatible with the transition maps**: for `p : P₁ ⟶ P₂`,
`L(g')^*p ≫ u'(P₂) = u'(P₁) ≫ Φ'(Lg^*L(p))`. -/
theorem baseChangeStageUnit_comp {P₁ P₂ : StdDerivedModules X.sheaf}
    (hbc : bc.IsNatural) (h₁ : StageData f g f' g' bc Q' P₁) (h₂ : StageData f g f' g' bc Q' P₂)
    (p : P₁ ⟶ P₂) :
    (derivedPullback g').map p ≫ baseChangeStageUnit hG' h₂ =
      baseChangeStageUnit hG' h₁ ≫ (pullbackTensorDerivedFunctor hG').map
        ((derivedPullback g).map (stageLMap f (G := G) h₁.hP h₂.hP p h₁.hK h₂.hK)) := by
  have := h₁.isIso_bc
  have := h₂.isIso_bc
  have hnat : (derivedPullback g).map (stageLMap f (G := G) h₁.hP h₂.hP p h₁.hK h₂.hK) ≫
      h₂.iso.hom = h₁.iso.hom ≫
        stageLMap f' (G := G') h₁.hP' h₂.hP' ((derivedPullback g').map p) h₁.hK' h₂.hK' :=
    stageLBaseChangeIso_naturality f g f' g' bc hbc h₁.hP h₂.hP h₁.hP' h₂.hP' h₁.hK h₂.hK h₁.hgK
      h₂.hgK h₁.hK' h₂.hK' p
  have hnat' : stageLMap f' (G := G') h₁.hP' h₂.hP' ((derivedPullback g').map p) h₁.hK' h₂.hK' ≫
      h₂.iso.inv = h₁.iso.inv ≫ (derivedPullback g).map (stageLMap f (G := G) h₁.hP h₂.hP p
        h₁.hK h₂.hK) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hu := comp_perfectStageUnit f' hG' h₁.hP' h₂.hP' ((derivedPullback g').map p) Q' h₁.hQ
    h₂.hQ h₁.hK' h₂.hK' h₁.hL h₂.hL
  simp only [baseChangeStageUnit, ← Category.assoc]
  rw [hu, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hnat']

end Stacks.Cohomology.RelativeExtCanonical

end
