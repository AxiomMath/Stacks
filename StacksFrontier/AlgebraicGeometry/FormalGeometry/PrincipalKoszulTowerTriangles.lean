module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalKoszulTowerDerivedSections

/-!
# Derived sections of the Koszul tower, compatibly with the cone triangles

Let `(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative
ring `A`, let `f ∈ A` and let `E ∈ D(𝒪_X)`. The `n`-th term `E_n = E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)`
of the `f`-power Koszul tower sits in the distinguished triangle `E ⟶ E ⟶ E_n ⟶ E[1]` whose first
map is multiplication by `f^(n+1)`. This file proves that derived sections over the base ring carry
the tower `n ↦ E_n` to the `f`-power Koszul tower of `K = RΓ(X, E)` over `A` by an isomorphism of
inverse systems which is, at every level, the third component of a morphism of triangles

`RΓ(X, E) ⟶ RΓ(X, E) ⟶ RΓ(X, E_n) ⟶ RΓ(X, E)[1]`
`   K     ⟶    K     ⟶ K ⊗ᴸ_A (A --f^(n+1)--> A) ⟶ K[1]`

whose first two components are the identity of `K`. In particular the identification carries the
map `Hᵖ(X, E) ⟶ Hᵖ(X, E_n)` and the boundary `Hᵖ(X, E_n) ⟶ Hᵖ⁺¹(X, E)` of the geometric triangle to
those of the algebraic one.

## Main results

* `Stacks.Cohomology.KoszulTowerSections.sectionsDerivedUnit_commShift` — the comparison
  `Q(Γ(X, C)) ⟶ RΓ(X, Q C)` commutes with the shifts.
* `Stacks.Cohomology.KoszulTowerSections.exists_triangle_koszulTower_derivedSections` — the
  comparison for a cochain complex of sheaves of modules.
* `Stacks.Cohomology.KoszulTowerSections.exists_triangle_principalDerivedTensorSystem_of_iso` —
  the algebraic Koszul tower depends on its argument only up to isomorphism, compatibly with the
  cone triangles.
* `Stacks.Cohomology.KoszulTowerSections.exists_triangle_principalKoszulTower_derivedSections` —
  the comparison for an object of `D(𝒪_X)`.
* `Stacks.Cohomology.KoszulTowerSections.exists_iso_principalKoszulTower_derivedSections_cone` —
  the comparison carries the cone inclusions and the cohomology boundaries of the geometric
  triangles to those of the algebraic ones.
* `Stacks.Cohomology.KoszulTowerSections.exists_triangleMorphism_map_derivedLimit` — a
  triangulated functor preserving countable products carries a derived-limit triangle to any
  distinguished triangle on the difference map of an isomorphic tower.

## References

* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.KoszulTowerSections

open Stacks.Cohomology.DerivedSectionsOverBase

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))

/-- The comparison `Q(Γ(X, C)) ⟶ RΓ(X, Q C)` from termwise sections to derived sections commutes
with the shifts: it is assembled from the unit of the right derived functor and from the canonical
identifications of the homotopy category, each of which does. -/
instance sectionsDerivedUnit_commShift : NatTrans.CommShift (sectionsDerivedUnit X ρ) ℤ := by
  let G := (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)
  let e := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((sectionsOver X ρ).mapHomotopyCategoryFactors (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))
  have h1 : NatTrans.CommShift e.hom ℤ := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom]
    infer_instance
  have h2 : NatTrans.CommShift (Functor.whiskerLeft
      (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
      (derivedSectionsOverUnit X ρ)) ℤ := inferInstance
  have h3 : NatTrans.CommShift (Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom
      (derivedSectionsOver X ρ)) ℤ := inferInstance
  have h4 : NatTrans.CommShift (Functor.associator
      (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
      DerivedCategory.Qh (derivedSectionsOver X ρ)).inv ℤ := inferInstance
  have h0 : NatTrans.CommShift e.inv ℤ := inferInstance
  exact (inferInstance : NatTrans.CommShift (e.inv ≫ Functor.whiskerLeft
      (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
      (derivedSectionsOverUnit X ρ) ≫ (Functor.associator
      (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
      DerivedCategory.Qh (derivedSectionsOver X ρ)).inv ≫ Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom
      (derivedSectionsOver X ρ)) ℤ)

end Stacks.Cohomology.KoszulTowerSections

namespace Stacks.Cohomology.KoszulTowerSections

open Stacks.Cohomology.DerivedSectionsOverBase

attribute [local instance] HasDerivedCategory.standard

section Tri

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [HasShift C ℤ]
  [HasShift D ℤ]
  [Preadditive C] [Preadditive D] {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ]

/-- A natural transformation compatible with the shifts induces a morphism between the images of
a triangle. -/
def triangleMapOfNatTrans (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C) :
    F₁.mapTriangle.obj T ⟶ F₂.mapTriangle.obj T where
  hom₁ := τ.app T.obj₁
  hom₂ := τ.app T.obj₂
  hom₃ := τ.app T.obj₃
  comm₁ := τ.naturality T.mor₁
  comm₂ := τ.naturality T.mor₂
  comm₃ := by
    have key : (F₁.map T.mor₃ ≫ (F₁.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (τ.app T.obj₁)⟦(1 : ℤ)⟧' =
          τ.app T.obj₃ ≫ F₂.map T.mor₃ ≫ (F₂.commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
      rw [Category.assoc, NatTrans.shift_app_comm, NatTrans.naturality_assoc]
    exact key

omit [Preadditive C] [Preadditive D] in
/-- The first component of `triangleMapOfNatTrans τ T` is `τ.app T.obj₁`. -/
@[simp] lemma triangleMapOfNatTrans_hom₁ (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C) :
    (triangleMapOfNatTrans τ T).hom₁ = τ.app T.obj₁ := rfl

omit [Preadditive C] [Preadditive D] in
/-- The second component of `triangleMapOfNatTrans τ T` is `τ.app T.obj₂`. -/
@[simp] lemma triangleMapOfNatTrans_hom₂ (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C) :
    (triangleMapOfNatTrans τ T).hom₂ = τ.app T.obj₂ := rfl

omit [Preadditive C] [Preadditive D] in
/-- The third component of `triangleMapOfNatTrans τ T` is `τ.app T.obj₃`. -/
@[simp] lemma triangleMapOfNatTrans_hom₃ (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C) :
    (triangleMapOfNatTrans τ T).hom₃ = τ.app T.obj₃ := rfl

/-- The isomorphism of image triangles induced by a natural transformation compatible with the
shifts which is invertible at the three objects of the triangle. -/
def triangleIsoOfNatTrans (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C)
    [h₁ : IsIso (τ.app T.obj₁)] [h₂ : IsIso (τ.app T.obj₂)] [h₃ : IsIso (τ.app T.obj₃)] :
    F₁.mapTriangle.obj T ≅ F₂.mapTriangle.obj T :=
  @asIso _ _ _ _ (triangleMapOfNatTrans τ T) (Triangle.isIso_of_isIsos _
    (inferInstanceAs (IsIso (τ.app T.obj₁))) (inferInstanceAs (IsIso (τ.app T.obj₂)))
    (inferInstanceAs (IsIso (τ.app T.obj₃))))

omit [Preadditive C] [Preadditive D] in
/-- The first component of the inverse of `triangleIsoOfNatTrans τ T` is `inv (τ.app T.obj₁)`. -/
lemma triangleIsoOfNatTrans_inv_hom₁ (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C)
    [h₁ : IsIso (τ.app T.obj₁)] [h₂ : IsIso (τ.app T.obj₂)] [h₃ : IsIso (τ.app T.obj₃)] :
    (triangleIsoOfNatTrans τ T).inv.hom₁ = @inv _ _ _ _ (τ.app T.obj₁) h₁ :=
  @IsIso.eq_inv_of_hom_inv_id _ _ _ _ _ h₁ _
    (congrArg TriangleMorphism.hom₁ (triangleIsoOfNatTrans τ T).hom_inv_id)

omit [Preadditive C] [Preadditive D] in
/-- The second component of the inverse of `triangleIsoOfNatTrans τ T` is `inv (τ.app T.obj₂)`. -/
lemma triangleIsoOfNatTrans_inv_hom₂ (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C)
    [h₁ : IsIso (τ.app T.obj₁)] [h₂ : IsIso (τ.app T.obj₂)] [h₃ : IsIso (τ.app T.obj₃)] :
    (triangleIsoOfNatTrans τ T).inv.hom₂ = @inv _ _ _ _ (τ.app T.obj₂) h₂ :=
  @IsIso.eq_inv_of_hom_inv_id _ _ _ _ _ h₂ _
    (congrArg TriangleMorphism.hom₂ (triangleIsoOfNatTrans τ T).hom_inv_id)

omit [Preadditive C] [Preadditive D] in
/-- The third component of the inverse of `triangleIsoOfNatTrans τ T` is `inv (τ.app T.obj₃)`. -/
lemma triangleIsoOfNatTrans_inv_hom₃ (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C)
    [h₁ : IsIso (τ.app T.obj₁)] [h₂ : IsIso (τ.app T.obj₂)] [h₃ : IsIso (τ.app T.obj₃)] :
    (triangleIsoOfNatTrans τ T).inv.hom₃ = @inv _ _ _ _ (τ.app T.obj₃) h₃ :=
  @IsIso.eq_inv_of_hom_inv_id _ _ _ _ _ h₃ _
    (congrArg TriangleMorphism.hom₃ (triangleIsoOfNatTrans τ T).hom_inv_id)

/-- The image under a functor of a morphism of triangles, inverted, when the functor makes its
three components invertible. -/
def mapTriangleIsoOfIsIso (F : C ⥤ D) [F.CommShift ℤ] {T T' : Triangle C} (φ : T ⟶ T')
    [IsIso (F.map φ.hom₁)] [IsIso (F.map φ.hom₂)] [IsIso (F.map φ.hom₃)] :
    F.mapTriangle.obj T ≅ F.mapTriangle.obj T' :=
  @asIso _ _ _ _ (F.mapTriangle.map φ) (Triangle.isIso_of_isIsos _
    (inferInstanceAs (IsIso (F.map φ.hom₁))) (inferInstanceAs (IsIso (F.map φ.hom₂)))
    (inferInstanceAs (IsIso (F.map φ.hom₃))))

omit [Preadditive C] [Preadditive D] in
/-- The first component of the inverse of `mapTriangleIsoOfIsIso F φ` is `inv (F.map φ.hom₁)`. -/
lemma mapTriangleIsoOfIsIso_inv_hom₁ (F : C ⥤ D) [F.CommShift ℤ] {T T' : Triangle C}
    (φ : T ⟶ T') [h₁ : IsIso (F.map φ.hom₁)] [h₂ : IsIso (F.map φ.hom₂)]
    [h₃ : IsIso (F.map φ.hom₃)] :
    (mapTriangleIsoOfIsIso F φ).inv.hom₁ = @inv _ _ _ _ (F.map φ.hom₁) h₁ :=
  @IsIso.eq_inv_of_hom_inv_id _ _ _ _ _ h₁ _
    (congrArg TriangleMorphism.hom₁ (mapTriangleIsoOfIsIso F φ).hom_inv_id)

omit [Preadditive C] [Preadditive D] in
/-- The second component of the inverse of `mapTriangleIsoOfIsIso F φ` is `inv (F.map φ.hom₂)`. -/
lemma mapTriangleIsoOfIsIso_inv_hom₂ (F : C ⥤ D) [F.CommShift ℤ] {T T' : Triangle C}
    (φ : T ⟶ T') [h₁ : IsIso (F.map φ.hom₁)] [h₂ : IsIso (F.map φ.hom₂)]
    [h₃ : IsIso (F.map φ.hom₃)] :
    (mapTriangleIsoOfIsIso F φ).inv.hom₂ = @inv _ _ _ _ (F.map φ.hom₂) h₂ :=
  @IsIso.eq_inv_of_hom_inv_id _ _ _ _ _ h₂ _
    (congrArg TriangleMorphism.hom₂ (mapTriangleIsoOfIsIso F φ).hom_inv_id)

omit [Preadditive C] [Preadditive D] in
/-- The third component of the inverse of `mapTriangleIsoOfIsIso F φ` is `inv (F.map φ.hom₃)`. -/
lemma mapTriangleIsoOfIsIso_inv_hom₃ (F : C ⥤ D) [F.CommShift ℤ] {T T' : Triangle C}
    (φ : T ⟶ T') [h₁ : IsIso (F.map φ.hom₁)] [h₂ : IsIso (F.map φ.hom₂)]
    [h₃ : IsIso (F.map φ.hom₃)] :
    (mapTriangleIsoOfIsIso F φ).inv.hom₃ = @inv _ _ _ _ (F.map φ.hom₃) h₃ :=
  @IsIso.eq_inv_of_hom_inv_id _ _ _ _ _ h₃ _
    (congrArg TriangleMorphism.hom₃ (mapTriangleIsoOfIsIso F φ).hom_inv_id)

omit [HasShift C ℤ] [Preadditive C] in
/-- If `a ≫ b = 𝟙 W`, then `a ≫ ((b ≫ e) ≫ m) = e ≫ m`. -/
lemma comp_comp_cancel_left {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ W) (h : a ≫ b = 𝟙 W)
    (e : W ⟶ Y) (m : Y ⟶ Z) : a ≫ ((b ≫ e) ≫ m) = e ≫ m := by
  rw [Category.assoc, reassoc_of% h]

omit [HasShift C ℤ] [Preadditive C] in
/-- If `a ≫ d = d' ≫ b`, `a = a'` and `b ≫ e = b'`, then `a' ≫ d ≫ e = d' ≫ b'`. -/
lemma comp_comp_eq_of_comp_eq {x y z w v : C} {a a' : x ⟶ y} {d : y ⟶ z} {d' : x ⟶ w}
    {b : w ⟶ z} (hk : a ≫ d = d' ≫ b) (ha : a = a') {e : z ⟶ v} {b' : w ⟶ v}
    (hb : b ≫ e = b') : a' ≫ d ≫ e = d' ≫ b' := by
  rw [← ha, ← Category.assoc, hk, Category.assoc, hb]

omit [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D] in
/-- For an isomorphism `i : z ≅ y`, `F.map (a ≫ i.inv) ≫ F.map i.hom = F.map a`. -/
lemma map_comp_inv_map_hom (F : C ⥤ D) {x y z : C} (a : x ⟶ y) (i : z ≅ y) :
    F.map (a ≫ i.inv) ≫ F.map i.hom = F.map a := by
  rw [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Tri

section ConeMap

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
  (G : C ⥤ D) [G.Additive]

/-- The first component of `(CochainComplex.mappingCone.mapTriangleIso φ G).hom` is the
identity. -/
lemma mappingCone_mapTriangleIso_hom_hom₁ :
    (CochainComplex.mappingCone.mapTriangleIso φ G).hom.hom₁ = 𝟙 _ := rfl

/-- The second component of `(CochainComplex.mappingCone.mapTriangleIso φ G).hom` is the
identity. -/
lemma mappingCone_mapTriangleIso_hom_hom₂ :
    (CochainComplex.mappingCone.mapTriangleIso φ G).hom.hom₂ = 𝟙 _ := rfl

/-- The third component of `(CochainComplex.mappingCone.mapTriangleIso φ G).hom` is
`(CochainComplex.mappingCone.mapHomologicalComplexIso φ G).hom`. -/
lemma mappingCone_mapTriangleIso_hom_hom₃ :
    (CochainComplex.mappingCone.mapTriangleIso φ G).hom.hom₃ =
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ G).hom := rfl

end ConeMap

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) (f : A)

/-- A quasi-isomorphism of complexes of `A`-modules is levelwise invertible in `D(A)` on the
`f`-power Koszul towers. -/
private theorem isIso_map_principalComplexSystemMap_app {C D : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : C ⟶ D) [IsIso (DerivedCategory.Q.map g)] (n : ℕᵒᵖ) :
    IsIso (DerivedCategory.Q.map ((principalComplexSystemMap f g).app n)) :=
  inferInstanceAs (IsIso ((Functor.whiskerRight (principalComplexSystemMap f g)
    DerivedCategory.Q).app n))

/-- The isomorphism of `f`-power Koszul towers in `D(A)` inverse to the map induced by a map `g`
of complexes of `A`-modules which is invertible in `D(A)`. -/
private def principalComplexSystemInvIso {C D : CochainComplex (ModuleCat.{u} A) ℤ} (g : C ⟶ D)
    [IsIso (DerivedCategory.Q.map g)] :
    PrincipalTorsionTower.principalComplexSystem A f D ⋙ DerivedCategory.Q ≅
      PrincipalTorsionTower.principalComplexSystem A f C ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun n ↦ (@asIso _ _ _ _ (DerivedCategory.Q.map
    ((principalComplexSystemMap f g).app n)) (isIso_map_principalComplexSystemMap_app f g n)).symm)
    (by
      intro m n h
      dsimp only [Functor.comp_obj, Functor.comp_map, Iso.symm_hom, asIso_inv]
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← Functor.map_comp,
        ← Functor.map_comp]
      exact congrArg DerivedCategory.Q.map
        ((principalComplexSystemMap f g).naturality h).symm)

/-- A map `Q C ≅ Q I` in `D(A)` into a K-injective complex lifts to a map of complexes. -/
private theorem exists_map_eq_of_isKInjective {C I : CochainComplex (ModuleCat.{u} A) ℤ}
    [I.IsKInjective] (u : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj I) :
    ∃ ψ : C ⟶ I, DerivedCategory.Q.map ψ = u.hom := by
  let cq := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj C) I).surjective
    (cq.hom.app C ≫ u.hom ≫ cq.inv.app I)
  refine ⟨(HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).preimage h, ?_⟩
  have hnat := cq.hom.naturality
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).preimage h)
  rw [Functor.comp_map, Functor.map_preimage, hh, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] at hnat
  exact ((cancel_epi _).1 hnat).symm

/-- **Derived sections carry the `f`-power Koszul tower of a complex to the `f`-power Koszul tower
of its derived sections, compatibly with the cone triangles.** For a cochain complex `E` of sheaves
of `𝒪_X`-modules and `K = RΓ(X, E)` there is an isomorphism of inverse systems
`c : RΓ(X, E_n) ≅ K ⊗ᴸ_A (A --f^(n+1)--> A)` such that for every `n` the image under `RΓ(X, -)` of
the cone triangle of multiplication by `f^(n+1)` on `E` maps to the cone triangle of
multiplication by `f^(n+1)` on the chosen complex representing `K`, by a morphism of triangles
whose first two components are the identification of `K` with that complex and whose third is
`c`. -/
theorem exists_triangle_koszulTower_derivedSections
    (E : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    let K := (derivedSectionsOver X ρ).obj (DerivedCategory.Q.obj E)
    ∃ c : principalKoszulComplexTower X (baseSmul X ρ f) E ⋙ DerivedCategory.Q ⋙
        derivedSectionsOver X ρ ≅ PrincipalTorsionTower.principalDerivedTensorSystem A f K,
      ∀ n : ℕ, ∃ τ : (derivedSectionsOver X ρ).mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj
          (CochainComplex.mappingCone.triangle (smulComplex X (baseSmul X ρ f) E ^ (n + 1)))) ⟶
          DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
            (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K))),
        τ.hom₁ = (DerivedCategory.Q.objObjPreimageIso K).inv ∧
        τ.hom₂ = (DerivedCategory.Q.objObjPreimageIso K).inv ∧ τ.hom₃ = c.hom.app ⟨n⟩ := by
  intro K
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  let G := (sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (structureSheafRing X))).obj E
  let j : E ⟶ J :=
    (Stacks.Injectives.kInjectiveResolutionInclusion
      (SheafOfModules.{u} (structureSheafRing X))).app E
  have hJ : J.IsKInjective := inferInstance
  have hjQ : IsIso (DerivedCategory.Q.map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ j).2 inferInstance
  let e₁ : principalKoszulComplexTower X (baseSmul X ρ f) E ⋙ DerivedCategory.Q ≅
      principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight (koszulComplexTowerMap X (baseSmul X ρ f) j) DerivedCategory.Q)
  have hcone (n : ℕ) :
      ((principalKoszulComplexTower X (baseSmul X ρ f) J).obj ⟨n⟩).IsKInjective :=
    CochainComplex.isKInjective_mappingCone _
  have hunit (n : ℕ) : IsIso ((sectionsDerivedUnit X ρ).app
      ((principalKoszulComplexTower X (baseSmul X ρ f) J).obj ⟨n⟩)) :=
    isIso_sectionsDerivedUnit_app X ρ _ (hcone n)
  let e₂ : principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ DerivedCategory.Q ⋙
        derivedSectionsOver X ρ ≅
      principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ G ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun n ↦ (@asIso _ _ _ _ ((sectionsDerivedUnit X ρ).app
      ((principalKoszulComplexTower X (baseSmul X ρ f) J).obj n)) (hunit n.unop)).symm) (by
        intro m n g
        dsimp only [Functor.comp_obj, Functor.comp_map, Iso.symm_hom, asIso_inv]
        rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
        exact ((sectionsDerivedUnit X ρ).naturality _).symm)
  let e₃ : principalKoszulComplexTower X (baseSmul X ρ f) J ⋙ G ≅
      PrincipalTorsionTower.principalComplexSystem A f (G.obj J) :=
    sectionsKoszulComplexTowerIso X ρ f J
  let P := DerivedCategory.Q.objPreimage K
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor (ModuleCat.{u} A)).obj P
  let p : P ⟶ I := (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)).app P
  have hI : I.IsKInjective := inferInstance
  have hpQ : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 inferInstance
  have hJunit : IsIso ((sectionsDerivedUnit X ρ).app J) :=
    isIso_sectionsDerivedUnit_app X ρ J hJ
  let u : DerivedCategory.Q.obj (G.obj J) ≅ DerivedCategory.Q.obj I :=
    asIso ((sectionsDerivedUnit X ρ).app J) ≪≫
      (derivedSectionsOver X ρ).mapIso (asIso (DerivedCategory.Q.map j)).symm ≪≫
      (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ asIso (DerivedCategory.Q.map p)
  obtain ⟨ψ, hψu⟩ := exists_map_eq_of_isKInjective u
  have hψ : IsIso (DerivedCategory.Q.map ψ) := by
    rw [hψu]
    infer_instance
  have hpn (n : ℕᵒᵖ) : IsIso (DerivedCategory.Q.map ((principalComplexSystemMap f p).app n)) :=
    isIso_map_principalComplexSystemMap_app f p n
  let e₄ : PrincipalTorsionTower.principalComplexSystem A f (G.obj J) ⋙ DerivedCategory.Q ≅
      PrincipalTorsionTower.principalDerivedTensorSystem A f K :=
    asIso (Functor.whiskerRight (principalComplexSystemMap f ψ) DerivedCategory.Q) ≪≫
      principalComplexSystemInvIso f p
  let c := Functor.isoWhiskerRight e₁ (derivedSectionsOver X ρ) ≪≫ e₂ ≪≫
    Functor.isoWhiskerRight e₃ DerivedCategory.Q ≪≫ e₄
  refine ⟨c, fun n ↦ ?_⟩
  let aE := smulComplex X (baseSmul X ρ f) E
  let aJ := smulComplex X (baseSmul X ρ f) J
  let RΓ := derivedSectionsOver X ρ
  let Q := (DerivedCategory.Q : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ ⥤ _)
  let QA := (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _)
  let t₁ := RΓ.mapTriangle.map (Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap
    ((aE ^ (n + 1) : End E) : E ⟶ E) ((aJ ^ (n + 1) : End J) : J ⟶ J) j j
    (smulComplex_pow_naturality X (baseSmul X ρ f) j (n + 1))))
  let t₂ := (Functor.mapTriangleCompIso Q RΓ).inv.app
    (CochainComplex.mappingCone.triangle ((aJ ^ (n + 1) : End J) : J ⟶ J))
  let TJ := CochainComplex.mappingCone.triangle ((aJ ^ (n + 1) : End J) : J ⟶ J)
  have hu₁ : IsIso ((sectionsDerivedUnit X ρ).app TJ.obj₁) := hJunit
  have hu₂ : IsIso ((sectionsDerivedUnit X ρ).app TJ.obj₂) := hJunit
  have hu₃ : IsIso ((sectionsDerivedUnit X ρ).app TJ.obj₃) := hunit n
  let U₃ := triangleIsoOfNatTrans (sectionsDerivedUnit X ρ)
    (CochainComplex.mappingCone.triangle ((aJ ^ (n + 1) : End J) : J ⟶ J))
  let t₄ := (Functor.mapTriangleCompIso G QA).hom.app
    (CochainComplex.mappingCone.triangle ((aJ ^ (n + 1) : End J) : J ⟶ J))
  let t₅ := QA.mapTriangle.map (CochainComplex.mappingCone.mapTriangleIso
    ((aJ ^ (n + 1) : End J) : J ⟶ J) (sectionsOver X ρ)).hom
  let t₆ := QA.mapTriangle.map (CochainComplex.mappingCone.triangleMap
    (G.map ((aJ ^ (n + 1) : End J) : J ⟶ J)) (f ^ (n + 1) • 𝟙 (G.obj J)) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp,
      mapHomologicalComplex_map_smulComplex_pow X ρ f J (n + 1)]))
  let t₇ := QA.mapTriangle.map (CochainComplex.mappingCone.triangleMap
    (f ^ (n + 1) • 𝟙 (G.obj J)) (f ^ (n + 1) • 𝟙 I) ψ ψ
    (by simp [Linear.smul_comp, Linear.comp_smul]))
  let m₈ := CochainComplex.mappingCone.triangleMap
    (f ^ (n + 1) • 𝟙 P) (f ^ (n + 1) • 𝟙 I) p p (by simp [Linear.smul_comp, Linear.comp_smul])
  have hm₁ : IsIso (QA.map m₈.hom₁) := hpQ
  have hm₂ : IsIso (QA.map m₈.hom₂) := hpQ
  have hm₃ : IsIso (QA.map m₈.hom₃) := hpn ⟨n⟩
  let T₈ := mapTriangleIsoOfIsIso QA m₈
  have L : RΓ.map (Q.map j) ≫ 𝟙 (RΓ.obj (Q.obj J)) ≫ inv ((sectionsDerivedUnit X ρ).app J) ≫
      𝟙 (QA.obj (G.obj J)) ≫ QA.map (𝟙 (G.obj J)) ≫ QA.map (𝟙 (G.obj J)) ≫ QA.map ψ ≫
        inv (QA.map p) = (DerivedCategory.Q.objObjPreimageIso K).inv := by
    simp [hψu, u, Q, QA, RΓ, G]
  refine ⟨t₁ ≫ t₂ ≫ U₃.inv ≫ t₄ ≫ t₅ ≫ t₆ ≫ t₇ ≫ T₈.inv, ?_, ?_, ?_⟩
  · simp only [Pretriangulated.comp_hom₁, t₁, t₂, U₃, t₄, t₅, t₆, t₇, T₈,
      triangleIsoOfNatTrans_inv_hom₁, mapTriangleIsoOfIsIso_inv_hom₁, Functor.mapTriangle_map_hom₁,
      mappingCone_mapTriangleIso_hom_hom₁, CochainComplex.mappingCone.triangleMap_hom₁,
      Functor.mapTriangleCompIso_inv_app_hom₁, Functor.mapTriangleCompIso_hom_app_hom₁]
    exact L
  · simp only [Pretriangulated.comp_hom₂, t₁, t₂, U₃, t₄, t₅, t₆, t₇, T₈,
      triangleIsoOfNatTrans_inv_hom₂, mapTriangleIsoOfIsIso_inv_hom₂, Functor.mapTriangle_map_hom₂,
      mappingCone_mapTriangleIso_hom_hom₂, CochainComplex.mappingCone.triangleMap_hom₂,
      Functor.mapTriangleCompIso_inv_app_hom₂, Functor.mapTriangleCompIso_hom_app_hom₂]
    exact L
  · simp only [Pretriangulated.comp_hom₃, t₁, t₂, U₃, t₄, t₅, t₆, t₇, T₈,
      triangleIsoOfNatTrans_inv_hom₃, mapTriangleIsoOfIsIso_inv_hom₃, Functor.mapTriangle_map_hom₃,
      mappingCone_mapTriangleIso_hom_hom₃, CochainComplex.mappingCone.triangleMap_hom₃,
      Functor.mapTriangleCompIso_inv_app_hom₃, Functor.mapTriangleCompIso_hom_app_hom₃]
    have L₃ : RΓ.map (Q.map (CochainComplex.mappingCone.map _ _ j j
          (smulComplex_pow_naturality X (baseSmul X ρ f) j (n + 1)))) ≫
        𝟙 _ ≫ @inv _ _ _ _ ((sectionsDerivedUnit X ρ).app TJ.obj₃) hu₃ ≫ 𝟙 _ ≫
        QA.map (CochainComplex.mappingCone.mapHomologicalComplexIso
          ((aJ ^ (n + 1) : End J) : J ⟶ J) (sectionsOver X ρ)).hom ≫
        QA.map (CochainComplex.mappingCone.map (G.map ((aJ ^ (n + 1) : End J) : J ⟶ J))
          (f ^ (n + 1) • 𝟙 (G.obj J)) (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Category.id_comp,
            mapHomologicalComplex_map_smulComplex_pow X ρ f J (n + 1)])) ≫
        QA.map (CochainComplex.mappingCone.map (f ^ (n + 1) • 𝟙 (G.obj J)) (f ^ (n + 1) • 𝟙 I) ψ ψ
          (by simp [Linear.smul_comp, Linear.comp_smul])) ≫
        @inv _ _ _ _ (QA.map m₈.hom₃) hm₃ = c.hom.app ⟨n⟩ := by
      have L₃b : RΓ.map (Q.map (CochainComplex.mappingCone.map _ _ j j
            (smulComplex_pow_naturality X (baseSmul X ρ f) j (n + 1)))) ≫
          @inv _ _ _ _ ((sectionsDerivedUnit X ρ).app TJ.obj₃) hu₃ ≫
          QA.map ((CochainComplex.mappingCone.mapHomologicalComplexIso
            ((aJ ^ (n + 1) : End J) : J ⟶ J) (sectionsOver X ρ)).hom ≫
            CochainComplex.mappingCone.map (G.map ((aJ ^ (n + 1) : End J) : J ⟶ J))
            (f ^ (n + 1) • 𝟙 (G.obj J)) (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Category.id_comp,
              mapHomologicalComplex_map_smulComplex_pow X ρ f J (n + 1)])) ≫
          QA.map (CochainComplex.mappingCone.map (f ^ (n + 1) • 𝟙 (G.obj J)) (f ^ (n + 1) • 𝟙 I)
            ψ ψ (by simp [Linear.smul_comp, Linear.comp_smul])) ≫
          @inv _ _ _ _ (QA.map m₈.hom₃) hm₃ = c.hom.app ⟨n⟩ := rfl
      refine Eq.trans ?_ L₃b
      simp only [Category.id_comp]
      congr 2
      exact (QA.map_comp_assoc _ _ _).symm
    exact L₃

/-- **The `f`-power Koszul tower of an object of `D(A)` depends on the object only up to
isomorphism, compatibly with the cone triangles.** An isomorphism `e : K' ≅ K` in `D(A)` induces
an isomorphism of `f`-power Koszul towers whose `n`-th component is the third component of a
morphism between the cone triangles of multiplication by `f^(n+1)` on the chosen complexes
representing `K'` and `K`; its first two components are `e`, read on those representatives. -/
theorem exists_triangle_principalDerivedTensorSystem_of_iso
    {K' K : DerivedCategory (ModuleCat.{u} A)} (e : K' ≅ K) :
    ∃ t : PrincipalTorsionTower.principalDerivedTensorSystem A f K' ≅
        PrincipalTorsionTower.principalDerivedTensorSystem A f K,
      ∀ n : ℕ, ∃ σ : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
            (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K'))) ⟶
          DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
            (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K))),
        σ.hom₁ = (DerivedCategory.Q.objObjPreimageIso K').hom ≫ e.hom ≫
            (DerivedCategory.Q.objObjPreimageIso K).inv ∧
        σ.hom₂ = (DerivedCategory.Q.objObjPreimageIso K').hom ≫ e.hom ≫
            (DerivedCategory.Q.objObjPreimageIso K).inv ∧
        σ.hom₃ = t.hom.app ⟨n⟩ := by
  let QA := (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _)
  let C' := QA.objPreimage K'
  let C := QA.objPreimage K
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor (ModuleCat.{u} A)).obj C
  let p : C ⟶ I := (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)).app C
  have hI : I.IsKInjective := inferInstance
  have hpQ : IsIso (QA.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 inferInstance
  let u : QA.obj C' ≅ QA.obj I := DerivedCategory.Q.objObjPreimageIso K' ≪≫ e ≪≫
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ asIso (QA.map p)
  obtain ⟨ψ, hψu⟩ := exists_map_eq_of_isKInjective u
  have hψ : IsIso (DerivedCategory.Q.map ψ) := by
    rw [hψu]
    infer_instance
  have hpn (n : ℕᵒᵖ) : IsIso (QA.map ((principalComplexSystemMap f p).app n)) :=
    isIso_map_principalComplexSystemMap_app f p n
  let t : PrincipalTorsionTower.principalDerivedTensorSystem A f K' ≅
      PrincipalTorsionTower.principalDerivedTensorSystem A f K :=
    @asIso _ _ _ _ (Functor.whiskerRight (principalComplexSystemMap f ψ) DerivedCategory.Q)
      (@isIso_whiskerRight_principalComplexSystemMap _ _ f _ _ ψ hψ) ≪≫
      principalComplexSystemInvIso f p
  refine ⟨t, fun n ↦ ?_⟩
  let mψ := CochainComplex.mappingCone.triangleMap
    (f ^ (n + 1) • 𝟙 C') (f ^ (n + 1) • 𝟙 I) ψ ψ (by simp [Linear.smul_comp, Linear.comp_smul])
  let mp := CochainComplex.mappingCone.triangleMap
    (f ^ (n + 1) • 𝟙 C) (f ^ (n + 1) • 𝟙 I) p p (by simp [Linear.smul_comp, Linear.comp_smul])
  have hm₁ : IsIso (QA.map mp.hom₁) := hpQ
  have hm₂ : IsIso (QA.map mp.hom₂) := hpQ
  have hm₃ : IsIso (QA.map mp.hom₃) := hpn ⟨n⟩
  have L : QA.map ψ ≫ inv (QA.map p) = (DerivedCategory.Q.objObjPreimageIso K').hom ≫ e.hom ≫
      (DerivedCategory.Q.objObjPreimageIso K).inv := by
    simp [hψu, u, QA]
  refine ⟨QA.mapTriangle.map mψ ≫ (mapTriangleIsoOfIsIso QA mp).inv, ?_, ?_, ?_⟩
  · simp only [Pretriangulated.comp_hom₁, mapTriangleIsoOfIsIso_inv_hom₁,
      Functor.mapTriangle_map_hom₁]
    exact L
  · simp only [Pretriangulated.comp_hom₂, mapTriangleIsoOfIsIso_inv_hom₂,
      Functor.mapTriangle_map_hom₂]
    exact L
  · simp only [Pretriangulated.comp_hom₃, mapTriangleIsoOfIsIso_inv_hom₃,
      Functor.mapTriangle_map_hom₃]
    rfl

/-- **Derived sections carry the `f`-power Koszul tower of `E ∈ D(𝒪_X)` to the `f`-power Koszul
tower of `RΓ(X, E)`, compatibly with the cone triangles.** There is an isomorphism of inverse
systems `c : RΓ(X, E_n) ≅ RΓ(X, E) ⊗ᴸ_A (A --f^(n+1)--> A)` such that for every `n` the image
under `RΓ(X, -)` of the triangle `E ⟶ E ⟶ E_n ⟶ E[1]` maps to the triangle
`K ⟶ K ⟶ K ⊗ᴸ_A (A --f^(n+1)--> A) ⟶ K[1]` of `K = RΓ(X, E)` by a morphism of triangles which is
the identity of `K` on the first two terms (read on the chosen representatives) and `c` on the
third. -/
theorem exists_triangle_principalKoszulTower_derivedSections
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    let K := (derivedSectionsOver X ρ).obj E
    ∃ c : principalKoszulTower X ρ f E ⋙ derivedSectionsOver X ρ ≅
        PrincipalTorsionTower.principalDerivedTensorSystem A f K,
      ∀ n : ℕ, ∃ τ : (derivedSectionsOver X ρ).mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj
          (CochainComplex.mappingCone.triangle
            (smulComplex X (baseSmul X ρ f) (DerivedCategory.Q.objPreimage E) ^ (n + 1)))) ⟶
          DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
            (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K))),
        τ.hom₁ = (derivedSectionsOver X ρ).map (DerivedCategory.Q.objObjPreimageIso E).hom ≫
            (DerivedCategory.Q.objObjPreimageIso K).inv ∧
        τ.hom₂ = (derivedSectionsOver X ρ).map (DerivedCategory.Q.objObjPreimageIso E).hom ≫
            (DerivedCategory.Q.objObjPreimageIso K).inv ∧
        τ.hom₃ = c.hom.app ⟨n⟩ := by
  intro K
  have hcx := exists_triangle_koszulTower_derivedSections X ρ f
    (DerivedCategory.Q.objPreimage E)
  have htx := exists_triangle_principalDerivedTensorSystem_of_iso f
    ((derivedSectionsOver X ρ).mapIso (DerivedCategory.Q.objObjPreimageIso E))
  obtain ⟨c', hc'⟩ := hcx
  obtain ⟨t, ht⟩ := htx
  refine ⟨c' ≪≫ t, fun n ↦ ?_⟩
  obtain ⟨τ', h₁, h₂, h₃⟩ := hc' n
  have hn := ht n
  obtain ⟨σ, hσ⟩ := hn
  have L : (DerivedCategory.Q.objObjPreimageIso
        ((derivedSectionsOver X ρ).obj
          (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)))).inv ≫
      (DerivedCategory.Q.objObjPreimageIso
        ((derivedSectionsOver X ρ).obj
          (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)))).hom ≫
      ((derivedSectionsOver X ρ).mapIso (DerivedCategory.Q.objObjPreimageIso E)).hom ≫
      (DerivedCategory.Q.objObjPreimageIso K).inv =
        (derivedSectionsOver X ρ).map (DerivedCategory.Q.objObjPreimageIso E).hom ≫
          (DerivedCategory.Q.objObjPreimageIso K).inv := by
    simp
  refine ⟨τ' ≫ σ, ?_, ?_, ?_⟩
  · exact (congrArg₂ (CategoryStruct.comp (obj := DerivedCategory (ModuleCat.{u} A))) h₁
      hσ.1).trans L
  · exact (congrArg₂ (CategoryStruct.comp (obj := DerivedCategory (ModuleCat.{u} A))) h₂
      hσ.2.1).trans L
  · exact (congrArg₂ (CategoryStruct.comp (obj := DerivedCategory (ModuleCat.{u} A))) h₃
      hσ.2.2)

/-- **The identification of the two Koszul towers on cohomology.** For `E ∈ D(𝒪_X)` and
`K = RΓ(X, E)` there is an isomorphism of inverse systems
`c : RΓ(X, E_n) ≅ K ⊗ᴸ_A (A --f^(n+1)--> A)` which carries the map `RΓ(X, E) ⟶ RΓ(X, E_n)` induced
by the cone inclusion `E ⟶ E_n` to the cone inclusion `K ⟶ K ⊗ᴸ_A (A --f^(n+1)--> A)`, and the
boundary `Hᵠ(X, E_n) ⟶ Hᵠ⁺¹(X, E)` of the triangle `E ⟶ E ⟶ E_n ⟶ E[1]` to the boundary of the
triangle `K ⟶ K ⟶ K ⊗ᴸ_A (A --f^(n+1)--> A) ⟶ K[1]`, both read on the chosen representatives. -/
theorem exists_iso_principalKoszulTower_derivedSections_cone
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ∃ c : principalKoszulTower X ρ f E ⋙ derivedSectionsOver X ρ ≅
        PrincipalTorsionTower.principalDerivedTensorSystem A f ((derivedSectionsOver X ρ).obj E),
      ∀ n : ℕ,
        (derivedSectionsOver X ρ).map ((DerivedCategory.Q.objObjPreimageIso E).inv ≫
            DerivedCategory.Q.map (CochainComplex.mappingCone.inr
              (smulComplex X (baseSmul X ρ f) (DerivedCategory.Q.objPreimage E) ^ (n + 1)))) ≫
          c.hom.app ⟨n⟩ =
          (DerivedCategory.Q.objObjPreimageIso ((derivedSectionsOver X ρ).obj E)).inv ≫
            DerivedCategory.Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙
              (DerivedCategory.Q.objPreimage ((derivedSectionsOver X ρ).obj E)))) ∧
        ∀ (q q' : ℤ) (hq : q + 1 = q'),
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map (c.hom.app ⟨n⟩) ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ
                (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
                  (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage
                    ((derivedSectionsOver X ρ).obj E))))) q q' hq ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q').map
                (DerivedCategory.Q.objObjPreimageIso ((derivedSectionsOver X ρ).obj E)).hom =
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ
                ((derivedSectionsOver X ρ).mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj
                  (CochainComplex.mappingCone.triangle (smulComplex X (baseSmul X ρ f)
                    (DerivedCategory.Q.objPreimage E) ^ (n + 1))))) q q' hq ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q').map
                ((derivedSectionsOver X ρ).map (DerivedCategory.Q.objObjPreimageIso E).hom) := by
  have hc := exists_triangle_principalKoszulTower_derivedSections X ρ f E
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, fun n ↦ ?_⟩
  have hn := hc n
  obtain ⟨τ, hτ⟩ := hn
  have k₂ : (derivedSectionsOver X ρ).map (DerivedCategory.Q.map (CochainComplex.mappingCone.inr
        (smulComplex X (baseSmul X ρ f) (DerivedCategory.Q.objPreimage E) ^ (n + 1)))) ≫
        c.hom.app ⟨n⟩ =
      ((derivedSectionsOver X ρ).map (DerivedCategory.Q.objObjPreimageIso E).hom ≫
        (DerivedCategory.Q.objObjPreimageIso ((derivedSectionsOver X ρ).obj E)).inv) ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙
          (DerivedCategory.Q.objPreimage ((derivedSectionsOver X ρ).obj E)))) :=
    (congrArg (CategoryStruct.comp _) hτ.2.2.symm).trans
      (τ.comm₂.trans (congrArg (· ≫ _) hτ.2.1))
  refine ⟨?_, fun q q' hq ↦ ?_⟩
  · refine (congrArg (· ≫ c.hom.app ⟨n⟩) ((derivedSectionsOver X ρ).map_comp _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (CategoryStruct.comp _) k₂).trans ?_))
    exact comp_comp_cancel_left _ _
      (by rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id])
      _ _
  · have k := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ_naturality τ
      q q' hq
    simp only [DerivedCategory.shift_homologyFunctor] at k
    refine comp_comp_eq_of_comp_eq k
      (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map hτ.2.2) ?_
    refine (congrArg (fun z ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q').map
      z ≫ _) hτ.1).trans ?_
    exact map_comp_inv_map_hom _ _ _

section DerivedLimit

universe v₃ v₄ u₃ u₄

variable {C : Type u₃} {D : Type u₄} [Category.{v₃} C] [Category.{v₄} D] [HasZeroObject C]
  [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [HasProductsOfShape ℕ D] (G : C ⥤ D) [G.CommShift ℤ]
  [G.IsTriangulated]

/-- **A triangulated functor preserving countable products carries a derived-limit triangle to
any distinguished triangle on the difference map of an isomorphic tower.** Let `L ⟶ ∏ Yₙ ⟶ ∏ Yₙ ⟶
L[1]` be distinguished with middle map `1 - shift`, let `G` preserve the product and let
`c : Y ⋙ G ≅ Z`. If `T₂` is distinguished and its middle map is `1 - shift` on `∏ Zₙ` through
identifications `e`, `e'` of its middle terms with that product, then the image of the first
triangle maps to `T₂` by a morphism of triangles whose middle components are the product of the
components of `c` and whose first component is an isomorphism. -/
theorem exists_triangleMorphism_map_derivedLimit (Y : ℕᵒᵖ ⥤ C) (Z : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ ↦ Y.obj ⟨n⟩]
    [PreservesLimit (Discrete.functor fun n : ℕ ↦ Y.obj ⟨n⟩) G] (c : Y ⋙ G ≅ Z) {L : C}
    (a : L ⟶ ∏ᶜ fun n : ℕ ↦ Y.obj ⟨n⟩) (b : (∏ᶜ fun n : ℕ ↦ Y.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op) b ∈
        distTriang C)
    (T₂ : Triangle D) (hT₂ : T₂ ∈ distTriang D) (e : T₂.obj₂ ≅ ∏ᶜ fun n : ℕ ↦ Z.obj ⟨n⟩)
    (e' : T₂.obj₃ ≅ ∏ᶜ fun n : ℕ ↦ Z.obj ⟨n⟩)
    (he : T₂.mor₂ ≫ e'.hom = e.hom ≫ Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) (n + 1) ≫ Z.map (homOfLE (Nat.le_succ n)).op) :
    ∃ τ : G.mapTriangle.obj (Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op) b) ⟶ T₂,
      IsIso τ.hom₁ ∧ IsIso τ.hom₂ ∧ IsIso τ.hom₃ ∧
      (∀ n : ℕ, τ.hom₂ ≫ e.hom ≫ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n =
        G.map (Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n) ≫ c.hom.app ⟨n⟩) ∧
      (∀ n : ℕ, τ.hom₃ ≫ e'.hom ≫ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n =
        G.map (Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n) ≫ c.hom.app ⟨n⟩) := by
  let P := PreservesProduct.iso G (fun n : ℕ ↦ Y.obj ⟨n⟩)
  let M : (∏ᶜ fun n : ℕ ↦ G.obj (Y.obj ⟨n⟩)) ≅ ∏ᶜ fun n : ℕ ↦ Z.obj ⟨n⟩ :=
    Pi.mapIso (fun n : ℕ ↦ c.app ⟨n⟩)
  let ι₂ : G.obj (∏ᶜ fun n : ℕ ↦ Y.obj ⟨n⟩) ≅ T₂.obj₂ := P ≪≫ M ≪≫ e.symm
  let ι₃ : G.obj (∏ᶜ fun n : ℕ ↦ Y.obj ⟨n⟩) ≅ T₂.obj₃ := P ≪≫ M ≪≫ e'.symm
  have hP (n : ℕ) : P.hom ≫ Pi.π (fun n : ℕ ↦ G.obj (Y.obj ⟨n⟩)) n =
      G.map (Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n) := by
    simp [P, PreservesProduct.iso_hom]
  have hι₂ (n : ℕ) : ι₂.hom ≫ e.hom ≫ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n =
      G.map (Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n) ≫ c.hom.app ⟨n⟩ := by
    simp [ι₂, M, Pi.mapIso_hom_π, reassoc_of% hP]
  have hι₃ (n : ℕ) : ι₃.hom ≫ e'.hom ≫ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n =
      G.map (Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n) ≫ c.hom.app ⟨n⟩ := by
    simp [ι₃, M, Pi.mapIso_hom_π, reassoc_of% hP]
  have hdist := G.map_distinguished _ hT
  have key : G.map (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op) ≫
        ι₃.hom ≫ e'.hom = ι₂.hom ≫ e.hom ≫ Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) (n + 1) ≫ Z.map (homOfLE (Nat.le_succ n)).op := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    have hc := c.hom.naturality (homOfLE (Nat.le_succ n)).op
    dsimp only [Functor.comp_obj, Functor.comp_map] at hc
    simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub, hι₃, hι₂, reassoc_of% hι₂,
      ← G.map_comp_assoc, G.map_sub, Preadditive.sub_comp, G.map_comp, hc]
  have hsq : (G.mapTriangle.obj (Triangle.mk a (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op) b)).mor₂ ≫
      ι₃.hom = ι₂.hom ≫ T₂.mor₂ := by
    apply (cancel_mono e'.hom).1
    have hr : ι₂.hom ≫ e.hom ≫ (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Z.obj ⟨n⟩) (n + 1) ≫ Z.map (homOfLE (Nat.le_succ n)).op) =
          (ι₂.hom ≫ T₂.mor₂) ≫ e'.hom := by
      rw [Category.assoc, he]
    exact (Category.assoc _ _ _).trans (key.trans hr)
  obtain ⟨u, hu₁, hu₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hdist hT₂ ι₂.hom ι₃.hom hsq
  let τ := Triangle.homMk _ _ u ι₂.hom ι₃.hom hu₁ hsq hu₃
  have h₂ : IsIso τ.hom₂ := inferInstanceAs (IsIso ι₂.hom)
  have h₃ : IsIso τ.hom₃ := inferInstanceAs (IsIso ι₃.hom)
  exact ⟨τ, isIso₁_of_isIso₂₃ τ hdist hT₂ h₂ h₃, h₂, h₃, hι₂, hι₃⟩

end DerivedLimit

end Stacks.Cohomology.KoszulTowerSections
