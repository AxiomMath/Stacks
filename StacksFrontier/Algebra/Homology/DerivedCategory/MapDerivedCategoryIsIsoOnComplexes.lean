module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Invertibility of derived maps from invertibility on modules

Let `F, G : C₁ ⥤ C₂` and `H : C₂ ⥤ C₃` be exact additive functors of abelian categories.  This
file records how invertibility statements about natural transformations and adjunctions on the
abelian categories pass to the unbounded derived categories, by evaluation on the image of the
localization `DerivedCategory.Q`, where every derived transformation is the degreewise one
conjugated by canonical comparisons.

## Main results

* `CategoryTheory.isIso_app_of_isIso_app_Q`: a natural transformation of functors out of a
  derived category is invertible at every object as soon as it is at every object `Q(K)`.
* `CategoryTheory.Functor.isIso_mapDerivedCategory_map_Q_map`: the image under `H` of a map of
  complexes which `H` inverts degreewise is inverted by the derived functor of `H`.
* `CategoryTheory.NatTrans.isIso_mapDerivedCategory_map_app`: if `H` inverts every component of
  a natural transformation `η : F ⟶ G`, then the derived functor of `H` inverts every component of
  its derived transformation.
* `CategoryTheory.Adjunction.isIso_mapDerivedCategory_unit_app`: the unit of the derived
  adjunction of an adjunction with invertible unit is invertible.
* `CategoryTheory.Adjunction.isIso_map_mapDerivedCategory_counit_app`: if `H` inverts every
  component of the counit of an adjunction, its derived functor inverts every component of the
  counit of the derived adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- A natural transformation of functors out of the derived category is invertible at every
object as soon as it is invertible at every object in the image of the localization. -/
theorem isIso_app_of_isIso_app_Q {E : Type u₄} [Category.{v₄} E]
    {Φ Ψ : DerivedCategory C₁ ⥤ E} (τ : Φ ⟶ Ψ)
    (h : ∀ K : CochainComplex C₁ ℤ, IsIso (τ.app (DerivedCategory.Q.obj K)))
    (X : DerivedCategory C₁) : IsIso (τ.app X) := by
  let e := DerivedCategory.Q.objObjPreimageIso X
  have := h (DerivedCategory.Q.objPreimage X)
  have hnat : τ.app X = Φ.map e.inv ≫ τ.app _ ≫ Ψ.map e.hom := by
    rw [τ.naturality_assoc, ← Ψ.map_comp, e.inv_hom_id, Ψ.map_id, Category.comp_id]
  rw [hnat]
  infer_instance

/-- A natural transformation which is invertible on objects is invertible on every complex. -/
private theorem isIso_mapHomologicalComplex_app_of_isIso_app {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] [Preadditive A] [Preadditive B] {F G : A ⥤ B}
    [F.Additive] [G.Additive] (η : F ⟶ G) (hη : ∀ M : A, IsIso (η.app M))
    (K : CochainComplex A ℤ) :
    IsIso ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) :=
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K).f n) :=
    fun n => hη (K.X n)
  HomologicalComplex.Hom.isIso_of_components _

variable (H : C₂ ⥤ C₃) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **The derived functor of `H` inverts a map of complexes which `H` inverts degreewise.** -/
theorem Functor.isIso_mapDerivedCategory_map_Q_map {K L : CochainComplex C₂ ℤ} (f : K ⟶ L)
    (hf : ∀ n : ℤ, IsIso (H.map (f.f n))) :
    IsIso (H.mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  have : ∀ n, IsIso (((H.mapHomologicalComplex (ComplexShape.up ℤ)).map f).f n) := hf
  have : IsIso ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (H.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
      H.mapDerivedCategoryFactors.hom.app L) := by
    rw [H.mapDerivedCategoryFactors_hom_naturality f]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.mapDerivedCategoryFactors.hom.app L)

variable {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **If `H` inverts every component of `η : F ⟶ G`, then the derived functor of `H` inverts
every component of the derived transformation of `η`.** -/
theorem NatTrans.isIso_mapDerivedCategory_map_app (η : F ⟶ G)
    (hη : ∀ M : C₁, IsIso (H.map (η.app M))) (X : DerivedCategory C₁) :
    IsIso (H.mapDerivedCategory.map ((NatTrans.mapDerivedCategory η).app X)) := by
  refine isIso_app_of_isIso_app_Q
    (Functor.whiskerRight (NatTrans.mapDerivedCategory η) H.mapDerivedCategory) (fun K => ?_) X
  rw [Functor.whiskerRight_app, NatTrans.mapDerivedCategory_app_Q, Functor.map_comp,
    Functor.map_comp]
  have := H.isIso_mapDerivedCategory_map_Q_map
    ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) (fun n => hη (K.X n))
  infer_instance

/-- **The derived transformation of a natural isomorphism is invertible.** -/
theorem NatTrans.isIso_mapDerivedCategory_app (η : F ⟶ G) (hη : ∀ M : C₁, IsIso (η.app M))
    (X : DerivedCategory C₁) : IsIso ((NatTrans.mapDerivedCategory η).app X) := by
  refine isIso_app_of_isIso_app_Q (NatTrans.mapDerivedCategory η) (fun K => ?_) X
  rw [NatTrans.mapDerivedCategory_app_Q]
  have := isIso_mapHomologicalComplex_app_of_isIso_app η hη K
  infer_instance

section Adjunction

variable {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- **The unit of the derived adjunction of an adjunction with invertible unit is invertible.**
-/
theorem Adjunction.isIso_mapDerivedCategory_unit_app (adj : L ⊣ R)
    (hη : ∀ M : C₁, IsIso (adj.unit.app M)) (X : DerivedCategory C₁) :
    IsIso ((Adjunction.mapDerivedCategory adj).unit.app X) := by
  refine isIso_app_of_isIso_app_Q (Adjunction.mapDerivedCategory adj).unit (fun K => ?_) X
  rw [mapDerivedCategoryAdjunction_unit_app_Q]
  have := isIso_mapHomologicalComplex_app_of_isIso_app adj.unit hη K
  infer_instance

/-- **If `H` inverts every component of the counit of `F ⊣ G`, its derived functor inverts every
component of the counit of the derived adjunction.** -/
theorem Adjunction.isIso_map_mapDerivedCategory_counit_app (adj : L ⊣ R)
    (hε : ∀ M : C₂, IsIso (H.map (adj.counit.app M))) (X : DerivedCategory C₂) :
    IsIso (H.mapDerivedCategory.map ((Adjunction.mapDerivedCategory adj).counit.app X)) := by
  rw [← Adjunction.derivedCounit_app adj X, Functor.map_comp, Functor.map_comp]
  have := NatTrans.isIso_mapDerivedCategory_map_app H adj.counit hε X
  infer_instance

end Adjunction

end CategoryTheory
