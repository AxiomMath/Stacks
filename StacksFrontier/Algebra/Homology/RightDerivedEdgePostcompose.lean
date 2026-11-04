module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompIsoSpellings
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonSourceNaturality
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The edge morphism under postcomposition with an exact functor, and in the `ℤ`-indexing

Let `P : 𝒜 ⥤ 𝒜` preserve injective objects, `Γ : 𝒜 ⥤ ℬ` be additive and `U : ℬ ⥤ 𝒞` be exact.
The edge morphism `Stacks.Cohomology.RightDerivedEdge.edge P Γ n : RⁿΓ ∘ P ⟶ Rⁿ(P ⋙ Γ)` commutes
with pulling `U` out of the right derived functors (`map_edge_comp_rightDerivedCompIso_inv`):
both are read on the chosen injective resolutions, where the comparison is the natural
`mapComplexHomologyIso`.

Combined with the identification of the `ℕ`- and `ℤ`-indexed edge morphisms
(`Stacks.DerivedIndexing.edge_comp_rightDerivedIso`) and the naturality of the comparison of the
two indexings (`Stacks.DerivedIndexing.rightDerivedIso_hom_naturality`), this moves a statement
about the `ℤ`-indexed degreewise comparison `Stacks.DerivedIndexing.rightDerivedPlusEdge P Γ i`
followed by the map induced by `σ : P ⋙ Γ ⟶ Γ` to the `ℕ`-indexed edge morphism of `(P, Γ ⋙ U)`
followed by the map induced by `σ ▷ U` (`rightDerivedCompIso_inv_map_rightDerivedIso_edgePlus`).
For `Γ` global sections with values in modules and `U` the forgetful functor to abelian groups,
this is how the canonical geometric Frobenius on `Hⁱ_c` reaches `Ext` in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedEdge

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D] [EnoughInjectives A]
  (P : A ⥤ A) [P.Additive] [P.PreservesInjectiveObjects] (Γ : A ⥤ B) [Γ.Additive]
  (U : B ⥤ D) [U.Additive] [U.PreservesHomology]

/-- The algebra of `map_edge_comp_moduleComparison_rightDerivedCompIso_hom`, abstract in the
objects. -/
private lemma postcomp_aux {B' D' : Type*} [Category* B'] [Category* D'] (U' : B' ⥤ D')
    {X₀ X₁ X₂ X₃ : B'} {Y₁ Y₂ Y₃ Y₄ : D'} {a : X₀ ⟶ X₁} {h : X₁ ⟶ X₂} {ci : X₂ ⟶ X₃}
    {c : X₃ ⟶ X₂} {m : U'.obj X₂ ⟶ Y₂} {d : Y₂ ⟶ Y₃} {mJ : U'.obj X₁ ⟶ Y₁} {jinv : Y₁ ⟶ Y₄}
    {jhom : Y₄ ⟶ Y₁} {h' : Y₁ ⟶ Y₂} (hci : ci ≫ c = 𝟙 X₂) (hj : jinv ≫ jhom = 𝟙 Y₁)
    (hnat : U'.map h ≫ m = mJ ≫ h') :
    U'.map (a ≫ h ≫ ci) ≫ U'.map c ≫ m ≫ d = (U'.map a ≫ mJ ≫ jinv) ≫ jhom ≫ h' ≫ d := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← U'.map_comp_assoc ci c, hci, U'.map_id, Category.id_comp, reassoc_of% hnat,
    reassoc_of% hj]

/-- **The edge morphism commutes with pulling an exact functor out of the right derived
functors**, in the spelling of `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`. -/
theorem map_edge_comp_moduleComparison_rightDerivedCompIso_hom (n : ℕ) (M : A) :
    U.map ((edge P Γ n).app M) ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (P ⋙ Γ) U ((P ⋙ Γ) ⋙ U)
          (Iso.refl _) n).hom.app M =
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso Γ U (Γ ⋙ U)
          (Iso.refl _) n).hom.app (P.obj M) ≫ (edge P (Γ ⋙ U) n).app M := by
  rw [Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app,
    Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app]
  have hnat := (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso Γ U (Γ ⋙ U)
    (Iso.refl _) n).hom.naturality (resolutionComparison P M)
  dsimp only [edge]
  exact postcomp_aux U (Iso.inv_hom_id _) (Iso.inv_hom_id _) hnat

/-- **The edge morphism commutes with pulling an exact functor out of the right derived
functors.** -/
theorem rightDerivedCompIso_hom_comp_map_edge (n : ℕ) (M : A) :
    (Γ.rightDerivedCompIso U n).hom.app (P.obj M) ≫ U.map ((edge P Γ n).app M) =
      (edge P (Γ ⋙ U) n).app M ≫ ((P ⋙ Γ).rightDerivedCompIso U n).hom.app M := by
  have h := map_edge_comp_moduleComparison_rightDerivedCompIso_hom P Γ U n M
  rw [Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_refl_app,
    Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_refl_app] at h
  rw [← cancel_mono (((P ⋙ Γ).rightDerivedCompIso U n).inv.app M), Category.assoc, h,
    Iso.hom_inv_id_app_assoc, Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- The algebra of `rightDerivedCompIso_hom_map_rightDerivedIso_edgePlus`, abstract in the
objects. -/
private lemma pasting_aux {B' D' : Type*} [Category* B'] [Category* D'] (U' : B' ⥤ D')
    {X₀ X₁ X₂ X₃ X₄ X₅ : B'} {Y₀ Y₁ Y₂ : D'} {e : X₀ ⟶ X₁} {r' : X₁ ⟶ X₂} {r : X₀ ⟶ X₃}
    {ep : X₃ ⟶ X₂} {nσ : X₁ ⟶ X₄} {r₀ : X₄ ⟶ X₅} {np : X₂ ⟶ X₅} {s : Y₀ ⟶ U'.obj X₀}
    {e' : Y₀ ⟶ Y₁} {s' : Y₁ ⟶ U'.obj X₁} {nU : Y₁ ⟶ Y₂} {s₀ : Y₂ ⟶ U'.obj X₄}
    (E1 : e ≫ r' = r ≫ ep) (E2 : nσ ≫ r₀ = r' ≫ np) (E3 : s ≫ U'.map e = e' ≫ s')
    (E4 : nU ≫ s₀ = s' ≫ U'.map nσ) :
    s ≫ U'.map r ≫ U'.map (ep ≫ np) = e' ≫ nU ≫ s₀ ≫ U'.map r₀ := by
  rw [← U'.map_comp, ← Category.assoc r, ← E1, Category.assoc, ← E2, U'.map_comp,
    reassoc_of% E3, reassoc_of% E4, U'.map_comp]

variable [HasDerivedCategory A] [HasDerivedCategory B]

/-- **The `ℤ`-indexed degreewise comparison followed by the map induced by `σ`, moved to the
`ℕ`-indexing and through an exact functor `U`.** Under `RⁿΓ ≅ RⁿΓ` (`ℕ` against `ℤ`) and
`Rⁿ(Γ ⋙ U) ≅ RⁿΓ ⋙ U`, `U` of `Stacks.DerivedIndexing.rightDerivedPlusEdge P Γ n` followed by the
map induced by `σ : P ⋙ Γ ⟶ Γ` is the edge morphism of `(P, Γ ⋙ U)` followed by the map induced
by `σ ▷ U`. -/
theorem rightDerivedCompIso_hom_map_rightDerivedIso_edgePlus (σ : P ⋙ Γ ⟶ Γ) (n : ℕ) (M : A) :
    (Γ.rightDerivedCompIso U n).hom.app (P.obj M) ≫
        U.map ((Stacks.DerivedIndexing.rightDerivedIso Γ n).hom.app (P.obj M)) ≫
        U.map ((Stacks.DerivedIndexing.rightDerivedPlusEdge P Γ (n : ℤ)).app M ≫
          (Stacks.DerivedIndexing.rightDerivedPlusNatTrans σ (n : ℤ)).app M) =
      (edge P (Γ ⋙ U) n).app M ≫ (NatTrans.rightDerived (Functor.whiskerRight σ U) n).app M ≫
        (Γ.rightDerivedCompIso U n).hom.app M ≫
        U.map ((Stacks.DerivedIndexing.rightDerivedIso Γ n).hom.app M) :=
  pasting_aux U (Stacks.DerivedIndexing.edge_comp_rightDerivedIso P Γ n M)
    (NatTrans.congr_app (Stacks.DerivedIndexing.rightDerivedIso_hom_naturality σ n) M)
    (rightDerivedCompIso_hom_comp_map_edge P Γ U n M)
    (Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_natTrans_source
      (P ⋙ Γ) Γ σ U n M)

end Stacks.Cohomology.RightDerivedEdge

end
