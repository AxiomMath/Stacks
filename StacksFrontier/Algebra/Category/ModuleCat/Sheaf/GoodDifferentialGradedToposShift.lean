module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImageShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftByFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback

/-!
# The shift of a good differential graded module is good

Let `Y` be a ringed topos and let `A` be a sheaf of differential graded `O_Y`-algebras. For every
integer `k`, a right differential graded `A`-module `P` is good in the sense of
`SheafOfModules.IsGoodToposBaseChange` — conditions (1), (2) and (3) of Tag 0FSA, the last over
the morphisms of ringed topoi — if and only if its shift `P[k]` is.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.shiftByCorepresentableBy`: **the shift of a base
  change is a base change of the shift**: if `T` corepresents `Q ↦ Hom_A(P, f_{*,ψ}Q)`, then
  `T[k]` corepresents `Q ↦ Hom_A(P[k], f_{*,ψ}Q)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.leftAdjointObjIsDefined_shiftBy`: a base change of
  `P[k]` exists as soon as one of `P` does.
* `SheafOfModules.IsGoodToposBaseChange.shiftBy` and
  `SheafOfModules.isGoodToposBaseChange_of_shiftBy`: `P` is good if and only if `P[k]` is.

## Implementation notes

The corepresentability is the composite of four bijections natural in `Q`:
`Hom(T[k], Q) ≃ Hom(T, Q[-k])` (`shiftByHomEquiv`), the base change of `P` at `Q[-k]`, the
identification `f_{*,ψ}(Q[-k]) ≅ (f_{*,ψ}Q)[-k]` of `toposPushforwardShiftByIso`, and
`shiftByHomEquiv` again, backwards, over the other ringed topos. Conditions (1) and (2) for the
shift are `isGradedFlat_shiftBy` and `isKFlat_shiftBy`, at both ringed topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section ToposPullback

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)

omit [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}] in
/-- `shiftByHomEquiv` is natural in the target, backwards. -/
theorem shiftByHomEquiv_symm_comp (k : ℤ) {T Q Q' : DifferentialGradedModule.{w, w, w} A}
    (φ : T ⟶ shiftBy Q (-k)) (g : Q ⟶ Q') :
    (shiftByHomEquiv k T Q').symm (φ ≫ shiftByMap (-k) g) =
      (shiftByHomEquiv k T Q).symm φ ≫ g := by
  apply (shiftByHomEquiv k T Q').injective
  rw [Equiv.apply_symm_apply, shiftByHomEquiv_comp, Equiv.apply_symm_apply]

/-- Postcomposition with an isomorphism of right differential graded modules, as a bijection of
morphisms. -/
def compIsoEquiv {X Y Y' : DifferentialGradedModule.{w, w, w} A} (i : Y ≅ Y') :
    (X ⟶ Y) ≃ (X ⟶ Y') where
  toFun φ := φ ≫ i.hom
  invFun φ := φ ≫ i.inv
  left_inv φ := by simp
  right_inv φ := by simp

/-- **The shift of a base change is a base change of the shift.** -/
noncomputable def shiftByCorepresentableBy {P : DifferentialGradedModule.{w, w, w} A}
    {T : DifferentialGradedModule.{w, w, w} B}
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (k : ℤ) :
    (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op (shiftBy P k))).CorepresentableBy
      (shiftBy T k) where
  homEquiv {Q} := (shiftByHomEquiv k T Q).trans (e.homEquiv.trans
    ((compIsoEquiv (toposPushforwardShiftByIso G ψ hψ Q (-k))).trans
      (shiftByHomEquiv k P ((toposPushforward G ψ hψ).obj Q)).symm))
  homEquiv_comp {Q Q'} g φ := by
    change (shiftByHomEquiv k P ((toposPushforward G ψ hψ).obj Q')).symm
        (e.homEquiv (shiftByHomEquiv k T Q' (φ ≫ g)) ≫
          (toposPushforwardShiftByIso G ψ hψ Q' (-k)).hom) =
      (shiftByHomEquiv k P ((toposPushforward G ψ hψ).obj Q)).symm
        (e.homEquiv (shiftByHomEquiv k T Q φ) ≫ (toposPushforwardShiftByIso G ψ hψ Q (-k)).hom) ≫
          (toposPushforward G ψ hψ).map g
    rw [shiftByHomEquiv_comp]
    have h1 : e.homEquiv (shiftByHomEquiv k T Q φ ≫ shiftByMap (-k) g) =
        e.homEquiv (shiftByHomEquiv k T Q φ) ≫
          (toposPushforward G ψ hψ).map (shiftByMap (-k) g) :=
      e.homEquiv_comp _ _
    rw [h1, Category.assoc, toposPushforwardShiftByIso_hom_naturality, ← Category.assoc,
      shiftByHomEquiv_symm_comp]

/-- A base change of `P[k]` exists as soon as one of `P` does. -/
theorem leftAdjointObjIsDefined_shiftBy {P : DifferentialGradedModule.{w, w, w} A}
    (h : (toposPushforward G ψ hψ).leftAdjointObjIsDefined P) (k : ℤ) :
    (toposPushforward G ψ hψ).leftAdjointObjIsDefined (shiftBy P k) := by
  have : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).IsCorepresentable := h
  exact (shiftByCorepresentableBy G ψ hψ
    (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).corepresentableBy k).isCorepresentable

end ToposPullback

end SheafOfModules.DifferentialGradedModule

namespace SheafOfModules

open DifferentialGradedModule

section Predicate

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

omit [HasSheafify Y.J (Type w)] in
/-- **The shift of a good right differential graded module is good**, goodness being
`SheafOfModules.IsGoodToposBaseChange`. Conditions (1) and (2) are the flatness and K-flatness of
a shift; at a base change the shift of the base change corepresents the base change of the shift,
and every other corepresenting object is isomorphic to it. -/
theorem IsGoodToposBaseChange.shiftBy {P : DifferentialGradedModule.{w, w, w} A}
    (hP : IsGoodToposBaseChange.{w, v₁, u₁} P) (k : ℤ) :
    IsGoodToposBaseChange.{w, v₁, u₁} (DifferentialGradedModule.shiftBy P k) := by
  refine ⟨isGradedFlat_shiftBy P k hP.isGradedFlat, isKFlat_shiftBy P k hP.isKFlat, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  obtain ⟨T, ⟨e⟩⟩ := (hP.baseChange f B ψ hψ).1
  have hT := (hP.baseChange f B ψ hψ).2 T e
  refine ⟨⟨_, ⟨shiftByCorepresentableBy (toposDirectImageModules f) ψ hψ e k⟩⟩, ?_⟩
  intro T' e'
  have i := e'.uniqueUpToIso (shiftByCorepresentableBy (toposDirectImageModules f) ψ hψ e k)
  exact ⟨RelativeTensor.IsGradedFlat.of_iso (GradedModule.ofDifferentialGradedIso i).symm
      (isGradedFlat_shiftBy T k hT.1),
    RelativeTensor.IsKFlat.of_iso i.symm (isKFlat_shiftBy T k hT.2)⟩

omit [HasSheafify Y.J (Type w)] in
/-- **A right differential graded module whose shift is good is good.** -/
theorem isGoodToposBaseChange_of_shiftBy {P : DifferentialGradedModule.{w, w, w} A} (k : ℤ)
    (hP : IsGoodToposBaseChange.{w, v₁, u₁} (DifferentialGradedModule.shiftBy P k)) :
    IsGoodToposBaseChange.{w, v₁, u₁} P := by
  have h := hP.shiftBy (-k)
  rwa [shiftBy_shiftBy_neg] at h

end Predicate

end SheafOfModules

end
