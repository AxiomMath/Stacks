module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESNatTrans

/-!
# The cone-commutation isomorphism of `Tot(F(G, -))` and short exact sequences

Let `F : A ⥤ B ⥤ D` be a bifunctor additive in each variable and `G` a complex of objects of `A`.
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso` identifies
`Tot(F(G, cone φ))` with `cone(Tot(F(G, φ)))`.  This file records its compatibility with the
third morphism of the mapping cone triangle and with the canonical morphism
`cone(S.f) ⟶ S.X₃` of a short complex `S`, and the same for the composite of `Tot(F(G, -))`
with a degreewise additive functor `Φ`.  These are the inputs of
`DerivedCategory.map_triangleOfSESδ_comp_natTrans`.

## Main results

* `Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso_hom_triangle_mor₃`
* `Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso_hom_descShortComplex`
* `Stacks.SheafOfModules.Tensor.Reduction.compBifunctorMappingConeIso`, with
  `compBifunctorMappingConeIso_hom_triangle_mor₃` and
  `compBifunctorMappingConeIso_hom_descShortComplex`
* `Stacks.SheafOfModules.Tensor.Reduction.compBifunctor_map_triangleOfSESδ_comp_natTrans`: the
  resulting compatibility of a comparison `Q ⋙ G' ⟶ Tot(F(G, Φ(-))) ⋙ Q` with the connecting
  morphisms of the triangles of short exact sequences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.Tensor.Reduction

attribute [local implicit_reducible] Functor.map₂HomologicalComplex

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (G : HomologicalComplex A (ComplexShape.up ℤ))

/-- `Tot(F(G, -))`, read as a functor of cochain complexes. -/
abbrev bifunctorTotLeft : CochainComplex B ℤ ⥤ CochainComplex D ℤ :=
  (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G

/-- The transport of the zero cochain is zero. -/
lemma Ψcoch_zero {X Y : CochainComplex B ℤ} {n : ℤ} :
    Ψcoch F G (0 : CochainComplex.HomComplex.Cochain X Y n) = 0 := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a a' h
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [Ψcoch_v F G (0 : CochainComplex.HomComplex.Cochain X Y n) a a' h p q hpq]
  simp

/-- The cone-commutation isomorphism is compatible with the third morphisms of the two mapping
cone triangles. -/
lemma bifunctorMappingConeIso_hom_triangle_mor₃ {K L : CochainComplex B ℤ} (φ : K ⟶ L) :
    letI := map₂HomologicalComplex_obj_additive F G
    (bifunctorTotLeft F G).map (CochainComplex.mappingCone.triangle φ).mor₃ ≫
      ((bifunctorTotLeft F G).commShiftIso (1 : ℤ)).hom.app K =
    (bifunctorMappingConeIso F G φ).hom ≫
      (CochainComplex.mappingCone.triangle
        ((bifunctorTotLeft F G).map φ)).mor₃ := by
  have h := (bifunctorMapTriangleIso F G φ).hom.comm₃
  have e : (shiftFunctor (HomologicalComplex D (ComplexShape.up ℤ)) (1 : ℤ)).map
      (bifunctorMapTriangleIso F G φ).hom.hom₁ = 𝟙 _ := by
    rw [show (bifunctorMapTriangleIso F G φ).hom.hom₁ = 𝟙 _ from rfl]
    exact CategoryTheory.Functor.map_id _ _
  rw [e] at h
  exact (Category.comp_id _).symm.trans h

/-- The inverse of the cone-commutation isomorphism on the summand `K[1]` of the cone. -/
lemma inl_v_bifunctorMappingConeIso_inv_f {K L : CochainComplex B ℤ} (φ : K ⟶ L) (n : ℤ) :
    (CochainComplex.mappingCone.inl ((bifunctorTotLeft F G).map φ)).v (n + 1) n (by omega) ≫
      (bifunctorMappingConeIso F G φ).inv.f n =
        (Ψcoch F G (CochainComplex.mappingCone.inl φ)).v (n + 1) n (by omega) := by
  dsimp only [bifunctorMappingConeIso]
  rw [CochainComplex.mappingCone.inl_v_desc_f]

/-- The inverse of the cone-commutation isomorphism on the summand `L` of the cone. -/
lemma inr_bifunctorMappingConeIso_inv {K L : CochainComplex B ℤ} (φ : K ⟶ L) :
    CochainComplex.mappingCone.inr ((bifunctorTotLeft F G).map φ) ≫
      (bifunctorMappingConeIso F G φ).inv =
        (bifunctorTotLeft F G).map (CochainComplex.mappingCone.inr φ) := by
  dsimp only [bifunctorMappingConeIso]
  rw [CochainComplex.mappingCone.inr_desc]

/-- The inverse of the cone-commutation isomorphism, followed by `Tot(F(G, cone S.f ⟶ S.X₃))`,
is the canonical morphism of the mapping cone of `Tot(F(G, S.f))`. -/
lemma bifunctorMappingConeIso_inv_map_descShortComplex (S : ShortComplex (CochainComplex B ℤ)) :
    letI := map₂HomologicalComplex_obj_additive F G
    (bifunctorMappingConeIso F G S.f).inv ≫
      (bifunctorTotLeft F G).map (CochainComplex.mappingCone.descShortComplex S) =
      CochainComplex.mappingCone.descShortComplex (S.map
          (bifunctorTotLeft F G)) := by
  let := map₂HomologicalComplex_obj_additive F G
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
  · refine ((Category.assoc _ _ _).symm.trans ?_).trans
      (CochainComplex.mappingCone.inl_v_descShortComplex_f (S.map (bifunctorTotLeft F G))
        (n + 1) n (by omega)).symm
    rw [inl_v_bifunctorMappingConeIso_inv_f, ← CochainComplex.HomComplex.Cochain.ofHom_v
        ((bifunctorTotLeft F G).map (CochainComplex.mappingCone.descShortComplex S)),
      ← Ψcoch_ofHom, ← CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero (-1 : ℤ))
        (n + 1) n n (by omega) (by omega), ← Ψcoch_comp,
      CochainComplex.mappingCone.descShortComplex, CochainComplex.mappingCone.inl_desc,
      Ψcoch_zero, CochainComplex.HomComplex.Cochain.zero_v]
  · refine Eq.trans ?_
      (CochainComplex.mappingCone.inr_f_descShortComplex_f (S.map (bifunctorTotLeft F G)) n).symm
    rw [← Category.assoc, ← HomologicalComplex.comp_f, inr_bifunctorMappingConeIso_inv,
      ← HomologicalComplex.comp_f,
      ← Functor.map_comp, CochainComplex.mappingCone.inr_descShortComplex]
    rfl

/-- The cone-commutation isomorphism is compatible with the canonical morphisms from the mapping
cone of `S.f` to `S.X₃`. -/
lemma bifunctorMappingConeIso_hom_descShortComplex (S : ShortComplex (CochainComplex B ℤ)) :
    letI := map₂HomologicalComplex_obj_additive F G
    (bifunctorMappingConeIso F G S.f).hom ≫
        CochainComplex.mappingCone.descShortComplex (S.map
          (bifunctorTotLeft F G)) =
      (bifunctorTotLeft F G).map (CochainComplex.mappingCone.descShortComplex S) :=
  (Iso.eq_inv_comp (bifunctorMappingConeIso F G S.f)).1
    (bifunctorMappingConeIso_inv_map_descShortComplex F G S).symm

section Comp

variable {C : Type*} [Category C] [Abelian C]
  (Φ : C ⥤ B) [Φ.Additive]

/-- The cone-commutation isomorphism of the composite `Tot(F(G, Φ(-)))`. -/
def compBifunctorMappingConeIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
        (bifunctorTotLeft F G)).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone
        (((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
          (bifunctorTotLeft F G)).map φ) :=
  (bifunctorTotLeft F G).mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso φ Φ) ≪≫
    bifunctorMappingConeIso F G _

/-- The cone-commutation isomorphism of the composite is compatible with the third morphisms of
the mapping cone triangles. -/
lemma compBifunctorMappingConeIso_hom_triangle_mor₃
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    letI := map₂HomologicalComplex_obj_additive F G
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
        (bifunctorTotLeft F G)).map (CochainComplex.mappingCone.triangle φ).mor₃ ≫
      (((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
        (bifunctorTotLeft F G)).commShiftIso (1 : ℤ)).hom.app K =
    (compBifunctorMappingConeIso F G Φ φ).hom ≫
      (CochainComplex.mappingCone.triangle
        (((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
          (bifunctorTotLeft F G)).map φ)).mor₃ := by
  let := map₂HomologicalComplex_obj_additive F G
  have h2 := bifunctorMappingConeIso_hom_triangle_mor₃ F G
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).map φ)
  have key : (bifunctorTotLeft F G).map
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).map (CochainComplex.mappingCone.triangle φ).mor₃ ≫
          ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).commShiftIso (1 : ℤ)).hom.app K) ≫
      ((bifunctorTotLeft F G).commShiftIso (1 : ℤ)).hom.app
          ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).obj K) =
      ((bifunctorTotLeft F G).map (CochainComplex.mappingCone.mapHomologicalComplexIso φ Φ).hom ≫
        (bifunctorMappingConeIso F G ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).map φ)).hom) ≫
      (CochainComplex.mappingCone.triangle
        ((bifunctorTotLeft F G).map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).map φ))).mor₃ := by
    rw [CochainComplex.mappingCone.map_δ φ Φ]
    exact (Functor.map_comp_assoc _ _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)
  rw [Functor.commShiftIso_comp_hom_app]
  exact (Functor.map_comp_assoc (bifunctorTotLeft F G) _ _ _).symm.trans key

/-- The cone-commutation isomorphism of the composite is compatible with the canonical morphisms
from the mapping cone of `S.f` to `S.X₃`. -/
lemma compBifunctorMappingConeIso_hom_descShortComplex
    (S : ShortComplex (CochainComplex C ℤ)) :
    letI := map₂HomologicalComplex_obj_additive F G
    (compBifunctorMappingConeIso F G Φ S.f).hom ≫
        CochainComplex.mappingCone.descShortComplex (S.map
          ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
            (bifunctorTotLeft F G))) =
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
        (bifunctorTotLeft F G)).map (CochainComplex.mappingCone.descShortComplex S) := by
  let := map₂HomologicalComplex_obj_additive F G
  have h0 := CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex Φ S
  have h := bifunctorMappingConeIso_hom_descShortComplex F G
    (S.map (Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ))
  have key : ((bifunctorTotLeft F G).map
        (CochainComplex.mappingCone.mapHomologicalComplexIso S.f Φ).hom ≫
        (bifunctorMappingConeIso F G ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).map S.f)).hom) ≫
      CochainComplex.mappingCone.descShortComplex
        ((S.map (Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ)).map
          (bifunctorTotLeft F G)) =
      (bifunctorTotLeft F G).map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ).map
          (CochainComplex.mappingCone.descShortComplex S)) :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ h0)))
  exact key

/-- **The connecting morphisms and a comparison with `Tot(F(G, Φ(-)))`.**  For a functor
`G'` between the derived categories commuting with the shifts and a comparison
`τ : Q ⋙ G' ⟶ Tot(F(G, Φ(-))) ⋙ Q` compatible with the shifts, the components of `τ` carry the
connecting morphism of the image under `G'` of the triangle of a short exact sequence `S` to the
connecting morphism of the triangle of `Tot(F(G, Φ(S)))`, when the latter is short exact. -/
theorem compBifunctor_map_triangleOfSESδ_comp_natTrans
    [HasDerivedCategory C] [HasDerivedCategory D]
    [((Φ.mapHomologicalComplex (ComplexShape.up ℤ) : CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
      (bifunctorTotLeft F G)).Additive]
    (G' : DerivedCategory C ⥤ DerivedCategory D) [G'.CommShift ℤ]
    (τ : DerivedCategory.Q ⋙ G' ⟶
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) : CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙
        (bifunctorTotLeft F G)) ⋙ DerivedCategory.Q) [NatTrans.CommShift τ ℤ]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (hΨS : (S.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex C ℤ ⥤ CochainComplex B ℤ) ⋙ (bifunctorTotLeft F G))).ShortExact) :
    G'.map (DerivedCategory.triangleOfSESδ hS) ≫
        (G'.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj S.X₁) ≫
        (τ.app S.X₁)⟦(1 : ℤ)⟧' =
      τ.app S.X₃ ≫ DerivedCategory.triangleOfSESδ hΨS :=
  DerivedCategory.map_triangleOfSESδ_comp_natTrans _ G' τ hS hΨS
    (compBifunctorMappingConeIso F G Φ S.f).hom
    (compBifunctorMappingConeIso_hom_triangle_mor₃ F G Φ S.f)
    (compBifunctorMappingConeIso_hom_descShortComplex F G Φ S).symm

end Comp

end Stacks.SheafOfModules.Tensor.Reduction

end
