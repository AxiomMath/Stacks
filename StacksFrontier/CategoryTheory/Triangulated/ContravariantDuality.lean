module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Representability through a contravariant duality

Let `C` be a category and `D : Cᵒᵖ ⥤ C` a contravariant functor which is an anti-self-equivalence
through a natural isomorphism `η : 𝟭 C ≅ D ∘ D`, as the dual `E ↦ E^∨` is on perfect complexes
([Stacks, Tag 08DQ]). This file records the two formal steps of the proof of [Stacks, Tag 0H4A]
which only use this structure.

## Main results

* `CategoryTheory.Functor.isHomological_comp_of_exists_distinguished`: if `D` turns each
  distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]` into a distinguished triangle
  `D Z ⟶ D Y ⟶ D X ⟶ (D Z)[1]`, then `D ⋙ G` is homological on `Cᵒᵖ` for every homological `G`,
  i.e. `E ↦ G(E^∨)` is cohomological.
* `CategoryTheory.exists_iso_linearCoyoneda_of_comp_iso_linearYoneda`: if moreover `D` is
  `k`-linear and `E ↦ G(D E)` is represented, `G(D E) ≅ Hom(E, K)`, then `G` is corepresented,
  `G ≅ Hom(D K, -)`.

## References

* [Stacks Project, Tag 0H4A](https://stacks.math.columbia.edu/tag/0H4A)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Pretriangulated Pretriangulated.Opposite

universe w v u

namespace CategoryTheory

section Homological

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type*} [Category A] [Abelian A]

/-- **A contravariant exact functor followed by a homological functor is homological on the
opposite category.** If `D : Cᵒᵖ ⥤ C` carries every distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]` of
`C` to a distinguished triangle `D Z ⟶ D Y ⟶ D X ⟶ (D Z)[1]`, then `D ⋙ G` is homological for
every homological functor `G : C ⥤ A`. -/
theorem Functor.isHomological_comp_of_exists_distinguished (D : Cᵒᵖ ⥤ C)
    [D.PreservesZeroMorphisms]
    (hD : ∀ T ∈ distTriang C, ∃ δ : D.obj (op T.obj₁) ⟶ (D.obj (op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk (D.map T.mor₂.op) (D.map T.mor₁.op) δ ∈ distTriang C)
    (G : C ⥤ A) [G.IsHomological] : (D ⋙ G).IsHomological where
  exact T hT := by
    obtain ⟨δ, hδ⟩ := hD _ (unop_distinguished T hT)
    exact G.map_distinguished_exact _ hδ

section Transport

variable {C' : Type*} [Category C'] [HasZeroObject C'] [HasShift C' ℤ] [Preadditive C']
  [∀ n : ℤ, (shiftFunctor C' n).Additive] [Pretriangulated C']

/-- The contravariant functor `D` read through an equivalence `e : C ≌ C'`. -/
abbrev Equivalence.transportDual (e : C ≌ C') (D : Cᵒᵖ ⥤ C) : C'ᵒᵖ ⥤ C' :=
  e.inverse.op ⋙ D ⋙ e.functor

/-- Reversal of distinguished triangles is carried along a triangulated equivalence. -/
theorem Equivalence.exists_distinguished_transportDual (e : C ≌ C')
    [e.functor.CommShift ℤ] [e.functor.IsTriangulated] [e.inverse.CommShift ℤ]
    [e.inverse.IsTriangulated] (D : Cᵒᵖ ⥤ C)
    (hD : ∀ T ∈ distTriang C, ∃ δ : D.obj (Opposite.op T.obj₁) ⟶
        (D.obj (Opposite.op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk (D.map T.mor₂.op) (D.map T.mor₁.op) δ ∈ distTriang C) :
    ∀ T ∈ distTriang C', ∃ δ : (e.transportDual D).obj (Opposite.op T.obj₁) ⟶
        ((e.transportDual D).obj (Opposite.op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk ((e.transportDual D).map T.mor₂.op) ((e.transportDual D).map T.mor₁.op) δ ∈
        distTriang C' := by
  intro T hT
  obtain ⟨δ, hδ⟩ := hD _ (e.inverse.map_distinguished T hT)
  exact ⟨_, e.functor.map_distinguished _ hδ⟩

/-- A natural transformation `𝟭 ⟶ D ∘ D` carried along an equivalence `e : C ≌ C'`. -/
def Equivalence.transportBidual (e : C ≌ C') (D : Cᵒᵖ ⥤ C) (η : 𝟭 C ⟶ D.rightOp ⋙ D) :
    𝟭 C' ⟶ (e.transportDual D).rightOp ⋙ e.transportDual D :=
  e.counitInv ≫ Functor.whiskerRight (Functor.whiskerLeft e.inverse η) e.functor ≫
    Functor.whiskerRight (Functor.whiskerLeft (e.inverse ⋙ D.rightOp)
      (Functor.whiskerRight (NatTrans.op e.unitInv) D)) e.functor

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject C'] [HasShift C' ℤ] [Preadditive C']
  [∀ (n : ℤ), (shiftFunctor C' n).Additive] [Pretriangulated C'] in
/-- The components of the transported natural transformation are invertible wherever those of
the original one are. -/
theorem Equivalence.isIso_transportBidual_app (e : C ≌ C') (D : Cᵒᵖ ⥤ C)
    (η : 𝟭 C ⟶ D.rightOp ⋙ D) (Y : C') (h : IsIso (η.app (e.inverse.obj Y))) :
    IsIso ((e.transportBidual D η).app Y) := by
  dsimp [Equivalence.transportBidual]
  infer_instance

end Transport

section Restriction

variable (P : ObjectProperty C) [P.IsTriangulated] (D : Cᵒᵖ ⥤ C)
  (hP : ∀ X, P X → P (D.obj (Opposite.op X)))

/-- The restriction of a contravariant functor `D` preserving `P` to the full subcategory of
`P`. -/
abbrev ObjectProperty.restrictDual : P.FullSubcategoryᵒᵖ ⥤ P.FullSubcategory :=
  P.lift (P.ι.op ⋙ D) (fun X => hP _ X.unop.property)

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [P.IsTriangulated] in
private lemma comm₃_aux (S : C ⥤ C) {X W Y' : C} (δ : X ⟶ S.obj W) (i : S.obj W ⟶ Y')
    (j : Y' ⟶ S.obj W) (hij : i ≫ j = 𝟙 _) :
    ((δ ≫ i) ≫ j) ≫ S.map (𝟙 W) = 𝟙 X ≫ δ := by
  simp [hij]

/-- Reversal of distinguished triangles restricts to a triangulated subcategory. -/
theorem ObjectProperty.exists_distinguished_restrictDual
    (hD : ∀ T ∈ distTriang C, ∃ δ : D.obj (Opposite.op T.obj₁) ⟶
        (D.obj (Opposite.op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk (D.map T.mor₂.op) (D.map T.mor₁.op) δ ∈ distTriang C) :
    ∀ T ∈ distTriang P.FullSubcategory, ∃ δ : (P.restrictDual D hP).obj (Opposite.op T.obj₁) ⟶
        ((P.restrictDual D hP).obj (Opposite.op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk ((P.restrictDual D hP).map T.mor₂.op) ((P.restrictDual D hP).map T.mor₁.op) δ ∈
        distTriang P.FullSubcategory := by
  intro T hT
  obtain ⟨δ, hδ⟩ : ∃ δ : D.obj (Opposite.op T.obj₁.obj) ⟶ (D.obj (Opposite.op T.obj₃.obj))⟦(1 : ℤ)⟧,
      Triangle.mk (D.map T.mor₂.hom.op) (D.map T.mor₁.hom.op) δ ∈ distTriang C := hD _ hT
  refine ⟨P.fullyFaithfulι.preimage (δ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app
    ((P.restrictDual D hP).obj (Opposite.op T.obj₃))), ?_⟩
  refine isomorphic_distinguished _ hδ _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    (Category.comp_id _ |>.trans (Category.id_comp _).symm) ?_)
  exact comm₃_aux (shiftFunctor C (1 : ℤ)) δ _ _ (Iso.inv_hom_id_app _ _)

/-- A natural transformation `𝟭 ⟶ D ∘ D` which is invertible on `P` restricts to a natural
isomorphism on the full subcategory of `P`. -/
noncomputable def ObjectProperty.restrictBidualIso (η : 𝟭 C ⟶ D.rightOp ⋙ D)
    (hη : ∀ X, P X → IsIso (η.app X)) :
    𝟭 P.FullSubcategory ≅ (P.restrictDual D hP).rightOp ⋙ P.restrictDual D hP :=
  NatIso.ofComponents (fun X => P.isoMk (@asIso _ _ _ _ (η.app X.obj) (hη _ X.property)))
    (fun f => by
      ext
      exact η.naturality f.hom)

end Restriction

end Homological

section Representability

variable (k : Type w) [CommRing k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- **Corepresentability from representability through a duality.** Let `D : Cᵒᵖ ⥤ C` be an
additive, `k`-linear contravariant functor with a natural isomorphism `η : 𝟭 C ≅ D ∘ D`, and let
`G : C ⥤ Vect_k`. If `E ↦ G(D E)` is represented by `K`, i.e. `G(D E) ≅ Hom(E, K)` naturally and
`k`-linearly, then `G ≅ Hom(D K, -)`. -/
theorem exists_iso_linearCoyoneda_of_comp_iso_linearYoneda (D : Cᵒᵖ ⥤ C) [D.Additive]
    (hD : ∀ {X Y : C} (f : X ⟶ Y) (r : k), D.map (r • f).op = r • D.map f.op)
    (η : 𝟭 C ≅ D.rightOp ⋙ D) (G : C ⥤ ModuleCat.{v} k) (K : C)
    (e : D ⋙ G ≅ (linearYoneda k C).obj K) :
    Nonempty (G ≅ (linearCoyoneda k C).obj (op (D.obj (op K)))) := by
  let ε : D ⋙ D.rightOp ≅ 𝟭 Cᵒᵖ := NatIso.ofComponents (fun Y => (η.app Y.unop).op) (by
    intro Y Y' f
    apply Quiver.Hom.unop_inj
    simpa using (η.hom.naturality f.unop).symm)
  let E : C ≌ Cᵒᵖ := Equivalence.mk D.rightOp D η ε
  let adj : D ⊣ D.rightOp := E.symm.toAdjunction
  have hφ : ∀ (X : C) (f : D.obj (op K) ⟶ X),
      (adj.homEquiv (op K) X f).unop = D.map f.op ≫ (adj.unit.app (op K)).unop := by
    intro X f
    rw [Adjunction.homEquiv_unit]
    rfl
  let φ : ∀ X : C, (D.obj (op K) ⟶ X) ≃ₗ[k] (D.obj (op X) ⟶ K) := fun X =>
    { toFun := fun f => (adj.homEquiv (op K) X f).unop
      invFun := fun g => (adj.homEquiv (op K) X).symm g.op
      left_inv := fun f => by simp
      right_inv := fun g => by simp
      map_add' := fun f g => by
        simp only [hφ, op_add, Functor.map_add, Preadditive.add_comp]
      map_smul' := fun r f => by
        simp only [hφ, hD, Linear.smul_comp, RingHom.id_apply] }
  have hnat : ∀ {X X' : C} (f : X ⟶ X') (h : D.obj (op K) ⟶ X),
      φ X' (h ≫ f) = D.map f.op ≫ φ X h := by
    intro X X' f h
    change (adj.homEquiv (op K) X' (h ≫ f)).unop = _
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  refine ⟨(Functor.leftUnitor G).symm ≪≫ Functor.isoWhiskerRight E.unitIso G ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.functor e ≪≫
    NatIso.ofComponents (fun X => (φ X).symm.toModuleIso) ?_⟩
  intro X X' f
  ext g
  apply (φ X').injective
  change φ X' ((φ X').symm (D.map f.op ≫ g)) = φ X' ((φ X).symm g ≫ f)
  rw [hnat, LinearEquiv.apply_symm_apply]
  exact (congrArg (D.map f.op ≫ ·) ((φ X).apply_symm_apply g)).symm

end Representability

end CategoryTheory
