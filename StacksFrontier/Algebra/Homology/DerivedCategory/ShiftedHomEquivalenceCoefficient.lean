module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Equivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence

/-!
# `Hom(E, 𝔽(M)[i])` along an equivalence, for a coefficient complex concentrated in degree `0`

Let `G : 𝒳 ⥤ 𝒴` be an additive equivalence of abelian categories, `𝔽 : 𝒞 ⥤ C(𝒳)` a functor whose
values are isomorphic to complexes concentrated in degree `0`, `θ : 𝔽 ≅ P(−)[0]`, and
`ε : G ∘ P ≅ Q`. For `E ∈ D(𝒳)` and an isomorphism `ι : G(E) ≅ L` in `D(𝒴)` this file builds the
additive equivalences

`Hom_{D(𝒳)}(E, 𝔽(M)[i]) ≃ Hom_{D(𝒴)}(L, Q(M)[0][i])`,

applying `G` on derived categories (`CategoryTheory.ShiftedHom.mapAddEquiv`) and moving along
`ι`, `θ` and `ε`, and proves that they are natural in `M` and carry the boundary map of a short
exact sequence `0 → 𝔽(M₁) → 𝔽(M₂) → 𝔽(M₃) → 0` of complexes to the boundary map
`CategoryTheory.ShortComplex.ShortExact.singleδ` of `0 → Q(M₁) → Q(M₂) → Q(M₃) → 0`.

## Main definitions

* `CategoryTheory.ShiftedHom.coefficientAddEquiv`: the additive equivalence.

## Main results

* `CategoryTheory.ShiftedHom.coefficientAddEquiv_naturality`.
* `CategoryTheory.ShiftedHom.coefficientAddEquiv_comp_triangleOfSESδ`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShiftedHom

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]

omit [Preadditive C] in
/-- Postcomposing a composite of shifted morphisms with a shifted morphism. -/
theorem comp_comp_shift {W A B B' : C} {a c : ℤ} (x : ShiftedHom W A a) (b : ShiftedHom A B 1)
    (κ : B ⟶ B') (h : 1 + a = c) :
    ShiftedHom.comp x b h ≫ κ⟦c⟧' = ShiftedHom.comp x (b ≫ κ⟦(1 : ℤ)⟧') h := by
  simp only [comp, Category.assoc, Functor.map_comp]
  congr 2
  exact ((shiftFunctorAdd' C 1 a c h).inv.naturality κ).symm

omit [Preadditive C] in
/-- Precomposing a shifted morphism after a shifted morphism. -/
theorem shift_comp_comp {W A A' B : C} {a c : ℤ} (x : ShiftedHom W A a) (κ : A ⟶ A')
    (b : ShiftedHom A' B 1) (h : 1 + a = c) :
    ShiftedHom.comp (x ≫ κ⟦a⟧') b h = ShiftedHom.comp x (κ ≫ b) h := by
  simp only [comp, Category.assoc, Functor.map_comp]

omit [Preadditive C] in
/-- Precomposing a composite of shifted morphisms with a morphism. -/
theorem comp_comp_assoc {V W A B : C} {a c : ℤ} (f : V ⟶ W) (x : ShiftedHom W A a)
    (b : ShiftedHom A B 1) (h : 1 + a = c) :
    f ≫ ShiftedHom.comp x b h = ShiftedHom.comp (f ≫ x) b h := by
  simp only [comp, Category.assoc]

variable {𝒳 𝒴 𝒞 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒞] [Abelian 𝒳] [Abelian 𝒴]
  [HasDerivedCategory 𝒳] [HasDerivedCategory 𝒴] (G : 𝒳 ⥤ 𝒴) [G.Additive] [G.IsEquivalence]
  {𝔽 : 𝒞 ⥤ CochainComplex 𝒳 ℤ} {P : 𝒞 ⥤ 𝒳}
  (θ : 𝔽 ≅ P ⋙ HomologicalComplex.single 𝒳 (ComplexShape.up ℤ) 0) {Q : 𝒞 ⥤ 𝒴} (ε : P ⋙ G ≅ Q)
  {E : DerivedCategory 𝒳} {L : DerivedCategory 𝒴} (ι : G.mapDerivedCategory.obj E ≅ L)

/-- **The coefficient comparison** `G(𝔽(M)) ≅ Q(M)[0]` in `D(𝒴)`: `θ`, the comparison of `G` with
the degree-`0` functors, and `ε`. -/
def coefficientIso (M : 𝒞) :
    G.mapDerivedCategory.obj (DerivedCategory.Q.obj (𝔽.obj M)) ≅
      (DerivedCategory.singleFunctor 𝒴 0).obj (Q.obj M) :=
  G.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso (θ.app M)) ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app (P.obj M) ≪≫
    (DerivedCategory.singleFunctor 𝒴 0).mapIso (ε.app M)

/-- The isomorphisms `coefficientIso G θ ε M` are natural in `M`. -/
theorem coefficientIso_hom_naturality {M N : 𝒞} (g : M ⟶ N) :
    G.mapDerivedCategory.map (DerivedCategory.Q.map (𝔽.map g)) ≫
        (coefficientIso G θ ε N).hom =
      (coefficientIso G θ ε M).hom ≫ (DerivedCategory.singleFunctor 𝒴 0).map (Q.map g) := by
  have h₁ := congrArg (fun k => G.mapDerivedCategory.map (DerivedCategory.Q.map k))
    (θ.hom.naturality g)
  have h₂ := (G.mapDerivedCategorySingleFunctor 0).hom.naturality (P.map g)
  have h₃ := congrArg (fun k => (DerivedCategory.singleFunctor 𝒴 0).map k) (ε.hom.naturality g)
  simp only [Functor.map_comp, Functor.comp_map] at h₁ h₂ h₃
  simp only [coefficientIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  have h₂' : G.mapDerivedCategory.map (DerivedCategory.Q.map
        ((HomologicalComplex.single 𝒳 (ComplexShape.up ℤ) 0).map (P.map g))) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (P.obj N) =
      (G.mapDerivedCategorySingleFunctor 0).hom.app (P.obj M) ≫
        (DerivedCategory.singleFunctor 𝒴 0).map (G.map (P.map g)) := h₂
  rw [reassoc_of% h₁, reassoc_of% h₂', h₃]

/-- **`Hom(E, 𝔽(M)[i]) ≃ Hom(L, Q(M)[0][i])`**: apply `G` on derived categories, then move along
`ι` and `coefficientIso`. -/
def coefficientAddEquiv (M : 𝒞) (i : ℤ) :
    ShiftedHom E (DerivedCategory.Q.obj (𝔽.obj M)) i ≃+
      ShiftedHom L ((DerivedCategory.singleFunctor 𝒴 0).obj (Q.obj M)) i :=
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence G
  (ShiftedHom.mapAddEquiv G.mapDerivedCategory E _ i).trans
    (ShiftedHom.congrAddEquiv ι (coefficientIso G θ ε M) i)

/-- `coefficientAddEquiv G θ ε ι M i y` is `ι⁻¹ ≫ G(y) ≫ (coefficientIso G θ ε M)[i]`. -/
theorem coefficientAddEquiv_apply (M : 𝒞) (i : ℤ)
    (y : ShiftedHom E (DerivedCategory.Q.obj (𝔽.obj M)) i) :
    coefficientAddEquiv G θ ε ι M i y =
      ι.inv ≫ ShiftedHom.map y G.mapDerivedCategory ≫ (coefficientIso G θ ε M).hom⟦i⟧' :=
  rfl

/-- **`coefficientAddEquiv` is natural in `M`.** -/
theorem coefficientAddEquiv_naturality {M N : 𝒞} (g : M ⟶ N) (i : ℤ)
    (y : ShiftedHom E (DerivedCategory.Q.obj (𝔽.obj M)) i) :
    coefficientAddEquiv G θ ε ι N i (y ≫ (DerivedCategory.Q.map (𝔽.map g))⟦i⟧') =
      coefficientAddEquiv G θ ε ι M i y ≫
        ((DerivedCategory.singleFunctor 𝒴 0).map (Q.map g))⟦i⟧' := by
  rw [coefficientAddEquiv_apply, coefficientAddEquiv_apply]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality_assoc]
  congr 3
  rw [← Functor.map_comp, ← Functor.map_comp, coefficientIso_hom_naturality]

/-- **`coefficientAddEquiv` carries the boundary map to the boundary map.** For a short exact
sequence `0 → M₁ → M₂ → M₃ → 0` in `𝒞` whose images under `𝔽` and `P` are short exact, the
composition with the boundary map of `𝔽(M₁) → 𝔽(M₂) → 𝔽(M₃)` is carried to the composition with
`singleδ` of `Q(M₁) → Q(M₂) → Q(M₃)`. -/
theorem coefficientAddEquiv_comp_triangleOfSESδ [HasZeroMorphisms 𝒞] [𝔽.PreservesZeroMorphisms]
    [P.PreservesZeroMorphisms] [Q.PreservesZeroMorphisms] {Sq : ShortComplex 𝒞}
    (hS₁ : (Sq.map 𝔽).ShortExact) (hQ : (Sq.map Q).ShortExact)
    (i j : ℤ) (h : 1 + i = j) (y : ShiftedHom E (DerivedCategory.Q.obj (𝔽.obj Sq.X₃)) i) :
    coefficientAddEquiv G θ ε ι Sq.X₁ j (ShiftedHom.comp y (DerivedCategory.triangleOfSESδ hS₁) h) =
      ShiftedHom.comp (coefficientAddEquiv G θ ε ι Sq.X₃ i y) hQ.singleδ h := by
  have : G.inv.Additive := Functor.additive_of_isEquivalence _
  have hP : (Sq.map P).ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso Sq
      (Functor.isoWhiskerRight ε.symm G.inv ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft P G.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor P))
      (hQ.map_of_exact G.inv)
  have hθ := DerivedCategory.triangleOfSESδ_naturality hS₁ (hP.map_of_exact
    (HomologicalComplex.single 𝒳 (ComplexShape.up ℤ) 0))
    ((ShortComplex.mapNatIso Sq θ).hom)
  have hG := hP.mapShiftedHom_singleδ G
  have hε := (ShortComplex.ShortExact.singleTriangle.map (hP.map_of_exact G) hQ
    ((ShortComplex.mapNatIso Sq ε).hom)).comm₃
  have key : ShiftedHom.map (DerivedCategory.triangleOfSESδ hS₁) G.mapDerivedCategory ≫
      ((coefficientIso G θ ε Sq.X₁).hom)⟦(1 : ℤ)⟧' =
      (coefficientIso G θ ε Sq.X₃).hom ≫ hQ.singleδ := by
    have hθ' : DerivedCategory.triangleOfSESδ hS₁ ≫
        (DerivedCategory.Q.map (θ.hom.app Sq.X₁))⟦(1 : ℤ)⟧' =
        DerivedCategory.Q.map (θ.hom.app Sq.X₃) ≫ hP.singleδ := hθ
    have hG' : G.mapDerivedCategory.map hP.singleδ ≫
        (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((P ⋙ HomologicalComplex.single 𝒳 (ComplexShape.up ℤ) 0).obj
            Sq.X₁)) =
        (G.mapDerivedCategorySingleFunctor 0).hom.app (P.obj Sq.X₃) ≫
          (hP.map_of_exact G).singleδ ≫
            ((G.mapDerivedCategorySingleFunctor 0).inv.app (P.obj Sq.X₁))⟦(1 : ℤ)⟧' := hG
    have hε' : (DerivedCategory.singleFunctor 𝒴 0).map (ε.hom.app Sq.X₃) ≫ hQ.singleδ =
        (hP.map_of_exact G).singleδ ≫
          ((DerivedCategory.singleFunctor 𝒴 0).map (ε.hom.app Sq.X₁))⟦(1 : ℤ)⟧' := hε.symm
    simp only [coefficientIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, ShiftedHom.map,
      Category.assoc, Functor.map_comp]
    rw [← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc, hθ',
      Functor.map_comp, Category.assoc]
    simp only [Functor.comp_obj] at hG' ⊢
    rw [reassoc_of% hG']
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [hε']
    simp
  rw [coefficientAddEquiv_apply, coefficientAddEquiv_apply, ShiftedHom.map_comp,
    comp_comp_shift, key, ← shift_comp_comp, comp_comp_assoc]

end CategoryTheory.ShiftedHom

end
