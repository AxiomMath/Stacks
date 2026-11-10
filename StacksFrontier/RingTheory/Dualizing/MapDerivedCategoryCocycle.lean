module

public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategoryJunction

/-!
# The cocycle and unit laws for the comparison of composite derived functors

`Dualizing.mapDerivedCategoryCompNatIso` turns an isomorphism `e : F ⋙ G ≅ H` of exact functors
between abelian categories into an isomorphism
`F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`. This file proves that the
construction respects composition and units, as soon as the chain-level isomorphisms do:

* for three composable exact functors, the two ways of comparing `F₃ ∘ F₂ ∘ F₁` with a fourth
  functor `G` through the intermediate composites agree on derived categories when they agree on
  objects;
* an isomorphism `ε : F ≅ 𝟭` lifts to `F.mapDerivedCategory ≅ 𝟭`, and the comparison built from
  `ε` whiskered by a second functor is that lift whiskered.

## Main results

* `Dualizing.mapDerivedCategoryCompNatIso_cocycle`: the cocycle law.
* `Dualizing.mapDerivedCategoryIdNatIso`: the lift of `ε : F ≅ 𝟭`.
* `Dualizing.mapDerivedCategoryCompNatIso_hom_app_of_unit`: the unit law.

## Implementation notes

Both laws are equalities of natural transformations out of a derived category, so by
`CategoryTheory.Localization.natTrans_ext` it suffices to compare them at the class `Q(A)` of a
cochain complex, where `Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q` computes every
comparison through the factorisations `CategoryTheory.Functor.mapDerivedCategoryFactors`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace Dualizing

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

section Cocycle

variable (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₃ : C₃ ⥤ C₄) (G₁₂ : C₁ ⥤ C₃) (G₂₃ : C₂ ⥤ C₄)
  (G : C₁ ⥤ C₄)
  [F₁.Additive] [F₂.Additive] [F₃.Additive] [G₁₂.Additive] [G₂₃.Additive] [G.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₂₃] [PreservesFiniteColimits G₂₃]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The cocycle law for `Dualizing.mapDerivedCategoryCompNatIso`.** Let `F₁, F₂, F₃` be
composable exact functors and let `e₁₂ : F₁ ⋙ F₂ ≅ G₁₂`, `e₂₃ : F₂ ⋙ F₃ ≅ G₂₃`,
`e : G₁₂ ⋙ F₃ ≅ G` and `e' : F₁ ⋙ G₂₃ ≅ G` be isomorphisms of exact functors whose two composites
`F₃ ∘ F₂ ∘ F₁ ⟶ G` agree. Then the two composites of the induced comparisons on derived
categories agree. -/
theorem mapDerivedCategoryCompNatIso_cocycle (e₁₂ : F₁ ⋙ F₂ ≅ G₁₂) (e₂₃ : F₂ ⋙ F₃ ≅ G₂₃)
    (e : G₁₂ ⋙ F₃ ≅ G) (e' : F₁ ⋙ G₂₃ ≅ G)
    (h : ∀ M : C₁, F₃.map (e₁₂.hom.app M) ≫ e.hom.app M =
      e₂₃.hom.app (F₁.obj M) ≫ e'.hom.app M)
    (K : DerivedCategory C₁) :
    F₃.mapDerivedCategory.map ((mapDerivedCategoryCompNatIso F₁ F₂ G₁₂ e₁₂).hom.app K) ≫
        (mapDerivedCategoryCompNatIso G₁₂ F₃ G e).hom.app K =
      (mapDerivedCategoryCompNatIso F₂ F₃ G₂₃ e₂₃).hom.app (F₁.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryCompNatIso F₁ G₂₃ G e').hom.app K := by
  let τ₁ : F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⋙ F₃.mapDerivedCategory ⟶
      G.mapDerivedCategory :=
    Functor.whiskerRight (mapDerivedCategoryCompNatIso F₁ F₂ G₁₂ e₁₂).hom
        F₃.mapDerivedCategory ≫ (mapDerivedCategoryCompNatIso G₁₂ F₃ G e).hom
  let τ₂ : F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⋙ F₃.mapDerivedCategory ⟶
      G.mapDerivedCategory :=
    Functor.whiskerLeft F₁.mapDerivedCategory (mapDerivedCategoryCompNatIso F₂ F₃ G₂₃ e₂₃).hom ≫
      (mapDerivedCategoryCompNatIso F₁ G₂₃ G e').hom
  suffices hτ : τ₁ = τ₂ from congrArg (fun τ => τ.app K) hτ
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
  intro A
  have hdeg : DerivedCategory.Q.map ((Functor.mapHomologicalComplex F₃ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e₁₂ (ComplexShape.up ℤ)).hom.app A)) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app A) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e₂₃ (ComplexShape.up ℤ)).hom.app
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj A)) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e' (ComplexShape.up ℤ)).hom.app A) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n
    simpa using h (A.X n)
  have hnat' : F₃.mapDerivedCategory.map (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e₁₂ (ComplexShape.up ℤ)).hom.app A)) ≫
      F₃.mapDerivedCategoryFactors.hom.app ((G₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) =
      F₃.mapDerivedCategoryFactors.hom.app ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj A)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplex F₃ (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso e₁₂ (ComplexShape.up ℤ)).hom.app A)) :=
    (F₃.mapDerivedCategoryFactors.hom.naturality
      ((Functor.mapHomologicalComplexCompIso e₁₂ (ComplexShape.up ℤ)).hom.app A))
  change F₃.mapDerivedCategory.map ((mapDerivedCategoryCompNatIso F₁ F₂ G₁₂ e₁₂).hom.app
        (DerivedCategory.Q.obj A)) ≫
      (mapDerivedCategoryCompNatIso G₁₂ F₃ G e).hom.app (DerivedCategory.Q.obj A) =
    (mapDerivedCategoryCompNatIso F₂ F₃ G₂₃ e₂₃).hom.app
        (F₁.mapDerivedCategory.obj (DerivedCategory.Q.obj A)) ≫
      (mapDerivedCategoryCompNatIso F₁ G₂₃ G e').hom.app (DerivedCategory.Q.obj A)
  have conj : ∀ {Xo Yo : DerivedCategory C₂} (φ : Xo ≅ Yo),
      (mapDerivedCategoryCompNatIso F₂ F₃ G₂₃ e₂₃).hom.app Xo =
        (F₂.mapDerivedCategory ⋙ F₃.mapDerivedCategory).map φ.hom ≫
          (mapDerivedCategoryCompNatIso F₂ F₃ G₂₃ e₂₃).hom.app Yo ≫
            G₂₃.mapDerivedCategory.map φ.inv := fun φ => by
    simpa using ((mapDerivedCategoryCompNatIso F₂ F₃ G₂₃ e₂₃).hom.naturality φ.hom =≫
      G₂₃.mapDerivedCategory.map φ.inv).symm
  have mih : ∀ {Zo : DerivedCategory C₄}
      (k : F₃.mapDerivedCategory.obj
        ((G₁₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj A) ⟶ Zo),
      F₃.mapDerivedCategory.map (G₁₂.mapDerivedCategoryFactors.inv.app A) ≫
        F₃.mapDerivedCategory.map (G₁₂.mapDerivedCategoryFactors.hom.app A) ≫ k = k :=
    fun k => by
      rw [← F₃.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
  have mih' : ∀ {Zo : DerivedCategory C₄}
      (k : G₂₃.mapDerivedCategory.obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj A) ⟶ Zo),
      G₂₃.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app A) ≫
        G₂₃.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app A) ≫ k = k :=
    fun k => by
      rw [← G₂₃.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
  rw [conj (Xo := F₁.mapDerivedCategory.obj (DerivedCategory.Q.obj A))
    (Yo := DerivedCategory.Q.obj ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj A))
    (F₁.mapDerivedCategoryFactors.app A)]
  rw [mapDerivedCategoryCompNatIso_hom_app_Q F₁ F₂ G₁₂ e₁₂,
    mapDerivedCategoryCompNatIso_hom_app_Q G₁₂ F₃ G e,
    mapDerivedCategoryCompNatIso_hom_app_Q F₂ F₃ G₂₃ e₂₃,
    mapDerivedCategoryCompNatIso_hom_app_Q F₁ G₂₃ G e']
  simp only [Functor.comp_map, Iso.app_hom, Iso.app_inv, Category.assoc, Functor.map_comp,
    Iso.inv_hom_id_app_assoc, mih, mih', ← reassoc_of% hnat',
    ← reassoc_of% hdeg]

end Cocycle

section Unit

variable (F : C₁ ⥤ C₁) (G : C₂ ⥤ C₁)
  [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An isomorphism `ε : F ≅ 𝟭` of an exact endofunctor with the identity lifts to an isomorphism
`F.mapDerivedCategory ≅ 𝟭` on the derived category: the lift along the localisation of the
factorisation of `F` followed by `ε` read degreewise. -/
def mapDerivedCategoryIdNatIso (ε : F ≅ 𝟭 C₁) : F.mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory) DerivedCategory.Q
    F.mapDerivedCategory (𝟭 _)
    (F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      Functor.leftUnitor _)

/-- At the image `Q A` of a cochain complex `A`, the component of `mapDerivedCategoryIdNatIso F ε`
is the factorisation isomorphism of `F` at `A` followed by `Q` applied to `ε` read degreewise
on `A`. -/
theorem mapDerivedCategoryIdNatIso_hom_app_Q (ε : F ≅ 𝟭 C₁) (A : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIdNatIso F ε).hom.app (DerivedCategory.Q.obj A) =
      F.mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app A) := by
  simp [mapDerivedCategoryIdNatIso, Localization.liftNatIso, Localization.liftNatTrans_app]

/-- **The unit law for `Dualizing.mapDerivedCategoryCompNatIso`.** If `e : G ⋙ F ≅ G` is `ε`
whiskered by `G` for an isomorphism `ε : F ≅ 𝟭`, then the comparison induced by `e` at an
object `K` is the lift of `ε` at `G K`. -/
theorem mapDerivedCategoryCompNatIso_hom_app_of_unit (ε : F ≅ 𝟭 C₁) (e : G ⋙ F ≅ G)
    (h : ∀ M : C₂, e.hom.app M = ε.hom.app (G.obj M)) (K : DerivedCategory C₂) :
    (mapDerivedCategoryCompNatIso G F G e).hom.app K =
      (mapDerivedCategoryIdNatIso F ε).hom.app (G.mapDerivedCategory.obj K) := by
  let τ₁ : G.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
    (mapDerivedCategoryCompNatIso G F G e).hom
  let τ₂ : G.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
    Functor.whiskerLeft G.mapDerivedCategory (mapDerivedCategoryIdNatIso F ε).hom
  suffices hτ : τ₁ = τ₂ from congrArg (fun τ => τ.app K) hτ
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ))
  intro A
  have hdeg : (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app A =
      (NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) := by
    ext n
    simpa using h (A.X n)
  change (mapDerivedCategoryCompNatIso G F G e).hom.app (DerivedCategory.Q.obj A) =
    (mapDerivedCategoryIdNatIso F ε).hom.app (G.mapDerivedCategory.obj (DerivedCategory.Q.obj A))
  have conj : ∀ {Xo Yo : DerivedCategory C₁} (φ : Xo ≅ Yo),
      (mapDerivedCategoryIdNatIso F ε).hom.app Xo =
        F.mapDerivedCategory.map φ.hom ≫ (mapDerivedCategoryIdNatIso F ε).hom.app Yo ≫ φ.inv :=
    fun φ => by simp
  rw [conj (Xo := G.mapDerivedCategory.obj (DerivedCategory.Q.obj A))
    (Yo := DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj A))
    (G.mapDerivedCategoryFactors.app A), mapDerivedCategoryCompNatIso_hom_app_Q G F G e,
    mapDerivedCategoryIdNatIso_hom_app_Q F ε, hdeg]
  simp only [Iso.app_hom, Iso.app_inv, Category.assoc]

end Unit

section UnitRight

variable (F : C₁ ⥤ C₁) (G : C₁ ⥤ C₂)
  [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The unit law for `Dualizing.mapDerivedCategoryCompNatIso`, on the right.** If
`e : F ⋙ G ≅ G` is the image under `G` of an isomorphism `ε : F ≅ 𝟭`, then the comparison
induced by `e` at an object `K` is the image under the derived functor of `G` of the lift of `ε`
at `K`. -/
theorem mapDerivedCategoryCompNatIso_hom_app_of_unit' (ε : F ≅ 𝟭 C₁) (e : F ⋙ G ≅ G)
    (h : ∀ M : C₁, e.hom.app M = G.map (ε.hom.app M)) (K : DerivedCategory C₁) :
    (mapDerivedCategoryCompNatIso F G G e).hom.app K =
      G.mapDerivedCategory.map ((mapDerivedCategoryIdNatIso F ε).hom.app K) := by
  let τ₁ : F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶ G.mapDerivedCategory :=
    (mapDerivedCategoryCompNatIso F G G e).hom
  let τ₂ : F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶ G.mapDerivedCategory :=
    Functor.whiskerRight (mapDerivedCategoryIdNatIso F ε).hom G.mapDerivedCategory
  suffices hτ : τ₁ = τ₂ from congrArg (fun τ => τ.app K) hτ
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
  intro A
  let εA := (NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app A
  have hdeg : (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app A =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map εA := by
    ext n
    simpa [εA] using h (A.X n)
  have hnat : G.mapDerivedCategory.map (DerivedCategory.Q.map εA) ≫
      G.mapDerivedCategoryFactors.hom.app A =
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map εA) :=
    G.mapDerivedCategoryFactors.hom.naturality εA
  change (mapDerivedCategoryCompNatIso F G G e).hom.app (DerivedCategory.Q.obj A) =
    G.mapDerivedCategory.map ((mapDerivedCategoryIdNatIso F ε).hom.app (DerivedCategory.Q.obj A))
  rw [mapDerivedCategoryCompNatIso_hom_app_Q F G G e, mapDerivedCategoryIdNatIso_hom_app_Q F ε,
    hdeg, Functor.map_comp, ← reassoc_of% hnat, Iso.hom_inv_id_app]
  exact congrArg (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app A) ≫ ·)
    (Category.comp_id _)

end UnitRight

end Dualizing

end
