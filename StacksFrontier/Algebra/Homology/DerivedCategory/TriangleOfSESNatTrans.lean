module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Triangles of short exact sequences under a comparison of functors

Let `Ψ` be an additive functor between categories of cochain complexes which commutes with the
shift, let `G` be a functor between the derived categories which commutes with the shift, and
let `τ : Q ⋙ G ⟶ Ψ ⋙ Q` be a natural transformation compatible with the shifts. Let `S` be a
short exact sequence of cochain complexes whose image under `Ψ` is again short exact, and
suppose that `Ψ` carries the mapping cone of `S.f` to the mapping cone of `Ψ S.f` through a
morphism `e` compatible with the third morphism of the mapping cone triangle and with the
canonical map from the mapping cone to `S.X₃`. Then the components of `τ` form a morphism from
the image under `G` of the distinguished triangle of `S` to the distinguished triangle of `Ψ S`.

## Main results

* `DerivedCategory.map_triangleOfSESδ_comp_natTrans`: the square formed by the two connecting
  morphisms and the components of `τ` commutes.
* `DerivedCategory.triangleOfSESNatTrans`: the morphism of triangles
  `G.mapTriangle (triangleOfSES S) ⟶ triangleOfSES (Ψ S)` whose components are those of `τ`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (Ψ : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [Ψ.Additive] [Ψ.CommShift ℤ]
  (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ]
  (τ : DerivedCategory.Q ⋙ G ⟶ Ψ ⋙ DerivedCategory.Q) [NatTrans.CommShift τ ℤ]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (hΨS : (S.map Ψ).ShortExact)
  (e : Ψ.obj (CochainComplex.mappingCone S.f) ⟶ CochainComplex.mappingCone (Ψ.map S.f))
  (he₃ : Ψ.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (Ψ.commShiftIso (1 : ℤ)).hom.app S.X₁ =
    e ≫ (CochainComplex.mappingCone.triangle (Ψ.map S.f)).mor₃)
  (hed : Ψ.map (CochainComplex.mappingCone.descShortComplex S) =
    e ≫ CochainComplex.mappingCone.descShortComplex (S.map Ψ))

include hed he₃ in
/-- **The connecting morphisms of the two distinguished triangles are compatible with `τ`.** -/
theorem map_triangleOfSESδ_comp_natTrans :
    G.map (triangleOfSESδ hS) ≫ (G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) ≫
        (τ.app S.X₁)⟦(1 : ℤ)⟧' =
      τ.app S.X₃ ≫ triangleOfSESδ hΨS := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hiso : IsIso (G.map (Q.map (CochainComplex.mappingCone.descShortComplex S))) :=
    inferInstance
  refine (cancel_epi (G.map (Q.map (CochainComplex.mappingCone.descShortComplex S)))).1 ?_
  have hnat₃ := τ.naturality (CochainComplex.mappingCone.descShortComplex S)
  have hnat₁ := τ.naturality (CochainComplex.mappingCone.triangle S.f).mor₃
  simp only [Functor.comp_map, Functor.comp_obj] at hnat₃ hnat₁
  have h₁ : G.map (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
        G.map (triangleOfSESδ hS) =
      G.map (Q.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
        G.map ((Q.commShiftIso (1 : ℤ)).hom.app S.X₁) :=
    (G.map_comp _ _).symm.trans
      ((congrArg G.map (descShortComplex_triangleOfSESδ hS)).trans (G.map_comp _ _))
  have h₂ : G.map ((Q.commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) ≫ (τ.app S.X₁)⟦(1 : ℤ)⟧' =
      τ.app (S.X₁⟦(1 : ℤ)⟧) ≫ Q.map ((Ψ.commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
        (Q.commShiftIso (1 : ℤ)).hom.app (Ψ.obj S.X₁) := by
    rw [← Category.assoc, ← Functor.commShiftIso_comp_hom_app Q G (1 : ℤ) S.X₁,
      NatTrans.shift_app_comm τ (1 : ℤ) S.X₁, Functor.commShiftIso_comp_hom_app Ψ Q (1 : ℤ) S.X₁]
  have h₃ : Q.map (Ψ.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
        Q.map ((Ψ.commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app (Ψ.obj S.X₁) =
      Q.map e ≫ Q.map (CochainComplex.mappingCone.descShortComplex (S.map Ψ)) ≫
        triangleOfSESδ hΨS :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (Q.commShiftIso (1 : ℤ)).hom.app (Ψ.obj S.X₁))
        ((Q.map_comp _ _).symm.trans ((congrArg Q.map he₃).trans (Q.map_comp _ _)))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (Q.map e ≫ ·) (descShortComplex_triangleOfSESδ hΨS).symm)))
  have h₄ : τ.app (CochainComplex.mappingCone S.f) ≫ Q.map e ≫
        Q.map (CochainComplex.mappingCone.descShortComplex (S.map Ψ)) =
      G.map (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫ τ.app S.X₃ :=
    (congrArg (τ.app (CochainComplex.mappingCone S.f) ≫ ·)
      ((Q.map_comp _ _).symm.trans (congrArg Q.map hed.symm))).trans hnat₃.symm
  have k₁ := (Category.assoc (G.map (Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (G.map (triangleOfSESδ hS)) ((G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) ≫
          (τ.app S.X₁)⟦(1 : ℤ)⟧')).symm
  have k₂ := (congrArg (· ≫ (G.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) ≫
          (τ.app S.X₁)⟦(1 : ℤ)⟧') h₁).trans (Category.assoc _ _ _)
  have k₃ := congrArg (G.map (Q.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫ ·) h₂
  have k₄ := (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ Q.map ((Ψ.commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
            (Q.commShiftIso (1 : ℤ)).hom.app (Ψ.obj S.X₁)) hnat₁).trans (Category.assoc _ _ _))
  have k₅ := congrArg (τ.app (CochainComplex.mappingCone S.f) ≫ ·) h₃
  have k₆ : τ.app (CochainComplex.mappingCone S.f) ≫ Q.map e ≫
          Q.map (CochainComplex.mappingCone.descShortComplex (S.map Ψ)) ≫ triangleOfSESδ hΨS =
      G.map (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫ τ.app S.X₃ ≫
          triangleOfSESδ hΨS := by
    refine Eq.trans ?_ ((congrArg (· ≫ triangleOfSESδ hΨS) h₄).trans (Category.assoc _ _ _))
    simp only [Category.assoc]
  exact k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆))))

/-- **The morphism of triangles induced by `τ`.** Its three components are those of `τ`, from
the image under `G` of the distinguished triangle of `S` to the distinguished triangle of the
short exact sequence `Ψ S`. -/
noncomputable def triangleOfSESNatTrans :
    G.mapTriangle.obj (triangleOfSES hS) ⟶ triangleOfSES hΨS :=
  Triangle.homMk _ _ (τ.app S.X₁) (τ.app S.X₂) (τ.app S.X₃)
    (τ.naturality S.f) (τ.naturality S.g)
    ((Category.assoc _ _ _).trans (map_triangleOfSESδ_comp_natTrans Ψ G τ hS hΨS e he₃ hed))

/-- The first component of `triangleOfSESNatTrans` is `τ.app S.X₁`. -/
@[simp] theorem triangleOfSESNatTrans_hom₁ :
    (triangleOfSESNatTrans Ψ G τ hS hΨS e he₃ hed).hom₁ = τ.app S.X₁ := rfl

/-- The second component of `triangleOfSESNatTrans` is `τ.app S.X₂`. -/
@[simp] theorem triangleOfSESNatTrans_hom₂ :
    (triangleOfSESNatTrans Ψ G τ hS hΨS e he₃ hed).hom₂ = τ.app S.X₂ := rfl

/-- The third component of `triangleOfSESNatTrans` is `τ.app S.X₃`. -/
@[simp] theorem triangleOfSESNatTrans_hom₃ :
    (triangleOfSESNatTrans Ψ G τ hS hΨS e he₃ hed).hom₃ = τ.app S.X₃ := rfl

end DerivedCategory
