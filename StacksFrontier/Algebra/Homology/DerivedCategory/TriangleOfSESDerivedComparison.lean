module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Connecting morphisms of short exact sequences under a comparison into a derived functor

Let `Ψ` be an additive functor between categories of cochain complexes which commutes with the
shift, let `G` be a functor between the derived categories which commutes with the shift, and
let `σ : Ψ ⋙ Q ⟶ Q ⋙ G` be a natural transformation compatible with the shifts. This is the
direction of the unit of a right derived functor `G` of `Ψ`. Let `S` be a short exact sequence of
cochain complexes whose image under `Ψ` is again short exact, and suppose that `Ψ` carries the
mapping cone of `S.f` isomorphically to the mapping cone of `Ψ S.f`, compatibly with the third
morphism of the mapping cone triangle and with the canonical map from the mapping cone to
`S.X₃`. Then the connecting morphism of `Ψ S` in the derived category is carried by `σ` to `G`
of the connecting morphism of `S`.

(`DerivedCategory.map_triangleOfSESδ_comp_natTrans` is the statement for a comparison in the
other direction, `Q ⋙ G ⟶ Ψ ⋙ Q`.)

## Main results

* `DerivedCategory.triangleOfSESδ_comp_natTrans_map`: the square formed by the two connecting
  morphisms and the components of `σ` commutes.
* `DerivedCategory.triangleOfSESδ_comp_natTrans_map_of_mapHomologicalComplex`: the same when `Ψ`
  is an additive functor applied degreewise, the mapping cone comparison being Mathlib's
  `CochainComplex.mappingCone.mapHomologicalComplexIso`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (Ψ : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [Ψ.Additive] [Ψ.CommShift ℤ]
  (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ]
  (σ : Ψ ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ G) [NatTrans.CommShift σ ℤ]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (hΨS : (S.map Ψ).ShortExact)
  (e : Ψ.obj (CochainComplex.mappingCone S.f) ≅ CochainComplex.mappingCone (Ψ.map S.f))
  (he₃ : Ψ.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (Ψ.commShiftIso (1 : ℤ)).hom.app S.X₁ =
    e.hom ≫ (CochainComplex.mappingCone.triangle (Ψ.map S.f)).mor₃)
  (hed : Ψ.map (CochainComplex.mappingCone.descShortComplex S) =
    e.hom ≫ CochainComplex.mappingCone.descShortComplex (S.map Ψ))

include hed he₃ in
/-- **The connecting morphism of `Ψ S` is carried by `σ` to `G` of that of `S`**:
`δ(Ψ S) ≫ σ_{S.X₁}[1] = σ_{S.X₃} ≫ G(δ S)`, read through the shift isomorphism of `G`. -/
theorem triangleOfSESδ_comp_natTrans_map :
    triangleOfSESδ hΨS ≫ (σ.app S.X₁)⟦(1 : ℤ)⟧' =
      σ.app S.X₃ ≫ G.map (triangleOfSESδ hS) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hΨS
  have hiso : IsIso (Q.map (Ψ.map (CochainComplex.mappingCone.descShortComplex S))) := by
    rw [hed, Q.map_comp]
    infer_instance
  refine (cancel_epi (Q.map (Ψ.map (CochainComplex.mappingCone.descShortComplex S)))).1 ?_
  have hnat₃ := σ.naturality (CochainComplex.mappingCone.descShortComplex S)
  have hnat₁ := σ.naturality (CochainComplex.mappingCone.triangle S.f).mor₃
  have e₁ := Functor.commShiftIso_comp_hom_app Q G (1 : ℤ) S.X₁
  have e₂ := Functor.commShiftIso_comp_hom_app Ψ Q (1 : ℤ) S.X₁
  simp only [Functor.comp_map, Functor.comp_obj] at hnat₃ hnat₁ e₁ e₂
  have hL : Q.map (Ψ.map (CochainComplex.mappingCone.descShortComplex S)) ≫
        triangleOfSESδ hΨS ≫ (σ.app S.X₁)⟦(1 : ℤ)⟧' =
      Q.map (Ψ.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
        ((Ψ ⋙ Q).commShiftIso (1 : ℤ)).hom.app S.X₁ ≫ (σ.app S.X₁)⟦(1 : ℤ)⟧' := by
    have h₃ : Q.map e.hom ≫ Q.map (CochainComplex.mappingCone.triangle (Ψ.map S.f)).mor₃ =
        Q.map (Ψ.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
          Q.map ((Ψ.commShiftIso (1 : ℤ)).hom.app S.X₁) :=
      (Q.map_comp _ _).symm.trans ((congrArg Q.map he₃).symm.trans (Q.map_comp _ _))
    rw [hed, Q.map_comp, Category.assoc, reassoc_of% (descShortComplex_triangleOfSESδ hΨS), e₂]
    exact ((reassoc_of% h₃) _).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm))
  have hR : Q.map (Ψ.map (CochainComplex.mappingCone.descShortComplex S)) ≫ σ.app S.X₃ ≫
        G.map (triangleOfSESδ hS) ≫ (G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) =
      σ.app (CochainComplex.mappingCone S.f) ≫
        G.map (Q.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
          ((Q ⋙ G).commShiftIso (1 : ℤ)).hom.app S.X₁ := by
    rw [reassoc_of% hnat₃, ← G.map_comp_assoc, descShortComplex_triangleOfSESδ hS, e₁,
      G.map_comp_assoc]
    rfl
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine (congrArg (Q.map (Ψ.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫ ·)
    (NatTrans.shift_app_comm σ (1 : ℤ) S.X₁)).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat₁).trans (Category.assoc _ _ _))

omit [Ψ.Additive] [Ψ.CommShift ℤ] [NatTrans.CommShift σ ℤ] in
/-- **`triangleOfSESδ_comp_natTrans_map` for an additive functor applied degreewise.** -/
theorem triangleOfSESδ_comp_natTrans_map_of_mapHomologicalComplex (H : C ⥤ D) [H.Additive]
    (σ : H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G) [NatTrans.CommShift σ ℤ]
    (hΨS : (S.map (H.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact) :
    triangleOfSESδ hΨS ≫ (σ.app S.X₁)⟦(1 : ℤ)⟧' =
      σ.app S.X₃ ≫ G.map (triangleOfSESδ hS) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) :=
  triangleOfSESδ_comp_natTrans_map (H.mapHomologicalComplex (ComplexShape.up ℤ)) G σ hS hΨS
    (CochainComplex.mappingCone.mapHomologicalComplexIso S.f H)
    (CochainComplex.mappingCone.map_δ S.f H)
    (CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex H S).symm

end DerivedCategory
