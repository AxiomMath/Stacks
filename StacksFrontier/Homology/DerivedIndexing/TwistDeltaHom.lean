module

public import StacksFrontier.Homology.DerivedIndexing.BaseChangeDelta
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp

/-!
# The endomorphism of a derived δ-functor attached to a twist

Let `F : 𝒜 ⥤ ℬ` be an additive functor, `𝒜` with enough injectives, `G : 𝒜 ⥤ 𝒜` an additive
functor and `Θ : RG ⋙ RF ⟶ RF` a transformation of right derived functors commuting with the
shift. For an exact functor `P : 𝒜' ⥤ 𝒜` and a *twist* `τ : P ⟶ P ⋙ G`, the maps

`R ⁿF(P X) ⟶ R ⁿF(G(P X)) ⟶ R ⁿF(RG(P X)) ⟶ R ⁿF(P X)`

(`τ`, the unit of `RG`, then `Θ`) form an endomorphism of the cohomological δ-functor
`X ↦ R ⁿF(P X)`: they commute with the connecting morphisms.

## Main definitions

* `Stacks.DerivedIndexing.twistDerivedEndo`: the endomorphism of `R ⁿF(P X)` attached to `τ`.
* `Stacks.DerivedIndexing.twistDeltaHom`: the endomorphism of the δ-functor `R ⁿF ∘ P`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B] [Abelian A] [Abelian A']
  [Abelian B] [EnoughInjectives A] (G : A ⥤ A) (F : A ⥤ B) [G.Additive] [F.Additive]
  (Θ : G.rightDerivedFunctorPlus ⋙ F.rightDerivedFunctorPlus ⟶ F.rightDerivedFunctorPlus)
  (P : A' ⥤ A) [P.Additive] (τ : P ⟶ P ⋙ G)

/-- **The endomorphism of `R ⁿF(P X)` attached to the twist `τ`**: `R ⁿF(τ_X)`, the unit of `RG`
and `Θ`. -/
def twistDerivedEndo (n : ℤ) (X : A') :
    (F.rightDerivedPlus n).obj (P.obj X) ⟶ (F.rightDerivedPlus n).obj (P.obj X) :=
  (DerivedCategory.Plus.homologyFunctor B n).map (derivedPairMap G F F Θ (τ.app X))

omit [Abelian A'] [P.Additive] in
/-- `Stacks.DerivedIndexing.twistDerivedEndo` unfolded: `R ⁿF(τ_X)` followed by the unit of `RG`
and `Θ`. -/
lemma twistDerivedEndo_eq (n : ℤ) (X : A') :
    twistDerivedEndo G F Θ P τ n X =
      (DerivedCategory.Plus.homologyFunctor B n).map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map (τ.app X)) ≫
          F.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle G).app (P.obj X)) ≫
          Θ.app ((DerivedCategory.Plus.singleFunctor A 0).obj (P.obj X))) := by
  dsimp only [twistDerivedEndo, derivedPairMap]
  rw [F.rightDerivedFunctorPlus.map_comp, Category.assoc]

omit [Abelian A'] [P.Additive] in
/-- `Stacks.DerivedIndexing.twistDerivedEndo` is natural. -/
lemma twistDerivedEndo_naturality (n : ℤ) {X Y : A'} (f : X ⟶ Y) :
    (F.rightDerivedPlus n).map (P.map f) ≫ twistDerivedEndo G F Θ P τ n Y =
      twistDerivedEndo G F Θ P τ n X ≫ (F.rightDerivedPlus n).map (P.map f) := by
  change (DerivedCategory.Plus.homologyFunctor B n).map (F.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor A 0).map (P.map f))) ≫
      (DerivedCategory.Plus.homologyFunctor B n).map (derivedPairMap G F F Θ (τ.app Y)) =
    (DerivedCategory.Plus.homologyFunctor B n).map (derivedPairMap G F F Θ (τ.app X)) ≫
      (DerivedCategory.Plus.homologyFunctor B n).map (F.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor A 0).map (P.map f)))
  rw [← Functor.map_comp, ← Functor.map_comp, derivedPairMap_naturality G F F Θ (τ.app X)
    (τ.app Y) (P.map f) (P.map f) (τ.naturality f)]

variable [NatTrans.CommShift Θ ℤ] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- **The endomorphism of the δ-functor `X ↦ R ⁿF(P X)` attached to a twist `τ : P ⟶ P ⋙ G`**:
in degree `n` it is `Stacks.DerivedIndexing.twistDerivedEndo`, read through the comparison
`R ⁿF ≅ H ⁿ ∘ RF` of the two indexings, and it commutes with the connecting morphisms. -/
def twistDeltaHom :
    (rightDerivedDeltaFunctorOfEnoughInjectives F).precomp P ⟶
      (rightDerivedDeltaFunctorOfEnoughInjectives F).precomp P where
  app n :=
    { app X := (rightDerivedIso F n).hom.app (P.obj X) ≫ twistDerivedEndo G F Θ P τ n X ≫
        (rightDerivedIso F n).inv.app (P.obj X)
      naturality X Y f := by
        change (F.rightDerived n).map (P.map f) ≫ (rightDerivedIso F n).hom.app (P.obj Y) ≫
            twistDerivedEndo G F Θ P τ n Y ≫ (rightDerivedIso F n).inv.app (P.obj Y) =
          ((rightDerivedIso F n).hom.app (P.obj X) ≫ twistDerivedEndo G F Θ P τ n X ≫
            (rightDerivedIso F n).inv.app (P.obj X)) ≫ (F.rightDerived n).map (P.map f)
        rw [(rightDerivedIso F n).hom.naturality_assoc, reassoc_of% (twistDerivedEndo_naturality
          G F Θ P τ n f), assoc, assoc, ← (rightDerivedIso F n).inv.naturality] }
  comm {S} hS n := by
    have hS' := hS.map_of_exact P
    let μ : S.map P ⟶ (S.map P).map G :=
      { τ₁ := τ.app S.X₁
        τ₂ := τ.app S.X₂
        τ₃ := τ.app S.X₃
        comm₁₂ := (τ.naturality S.f).symm
        comm₂₃ := (τ.naturality S.g).symm }
    have key := canonicalδ_comp_derivedPairMap G F F Θ hS' hS' μ n
    change ((rightDerivedIso F n).hom.app (P.obj S.X₃) ≫ twistDerivedEndo G F Θ P τ n S.X₃ ≫
        (rightDerivedIso F n).inv.app (P.obj S.X₃)) ≫
        ((rightDerivedIso F n).hom.app (P.obj S.X₃) ≫ canonicalδ F hS' n ≫
          (rightDerivedIso F (n + 1)).inv.app (P.obj S.X₁)) =
      ((rightDerivedIso F n).hom.app (P.obj S.X₃) ≫ canonicalδ F hS' n ≫
          (rightDerivedIso F (n + 1)).inv.app (P.obj S.X₁)) ≫
        ((rightDerivedIso F (n + 1)).hom.app (P.obj S.X₁) ≫
          twistDerivedEndo G F Θ P τ ((n + 1 : ℕ) : ℤ) S.X₁ ≫
          (rightDerivedIso F (n + 1)).inv.app (P.obj S.X₁))
    simp only [assoc, Iso.inv_hom_id_app_assoc]
    congr 1
    rw [← assoc, ← assoc]
    congr 1
    exact key.symm

/-- The component of `Stacks.DerivedIndexing.twistDeltaHom` in degree `n` at `X` is
`Stacks.DerivedIndexing.twistDerivedEndo` conjugated by the comparison `R ⁿF ≅ H ⁿ ∘ RF`. -/
@[simp]
lemma twistDeltaHom_app_app (n : ℕ) (X : A') :
    ((twistDeltaHom G F Θ P τ).app n).app X =
      (rightDerivedIso F n).hom.app (P.obj X) ≫ twistDerivedEndo G F Θ P τ n X ≫
        (rightDerivedIso F n).inv.app (P.obj X) :=
  rfl

end Stacks.DerivedIndexing

end
