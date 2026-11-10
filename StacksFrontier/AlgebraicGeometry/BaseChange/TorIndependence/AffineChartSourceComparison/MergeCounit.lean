module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.Mates
public import
StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.UnitRestrict

/-!
# Transports, the merge counit, and the restriction model along a composite

Regroupings, cocycle and transport lemmas for derived extension of scalars;
`RingTheory.TorIndependence.map_merge_comp_counit` and
`RingTheory.TorIndependence.inv_comp_map_merge_comp_counit`; the two factors
`AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict_hom_app` and
`AlgebraicGeometry.map_totalDerivedExtensionScalarsCompIsoRestrict_hom_comp_counit`; and the
transports `AlgebraicGeometry.map_eqToHom_comp_comp_hom_extend` and
`AlgebraicGeometry.comp_inv_comp_map_eqToHom_stalk`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp totalDerivedExtensionScalarsComp_comparison
  derivedExtensionScalarsAdjunction)
open scoped TensorProduct ChangeOfRings

universe u w v₁ v₂ v₃ u₁ u₂ u₃

/-! ### The reconciliation at the `Spec 𝒪_X(U)` corner -/

namespace RingTheory.TorIndependence

/-- **A morphism determined by its composite with one half of an inverse pair.** -/
theorem eq_comp_inv_of {𝒞 : Type u₁} [Category.{v₁} 𝒞] {W X Y : 𝒞} (a : W ⟶ X)
    (b : W ⟶ Y) (i : X ⟶ Y) (i' : Y ⟶ X) (hi : i ≫ i' = CategoryStruct.id X)
    (hb : a ≫ i = b) : a = b ≫ i' := by
  rw [← hb, Category.assoc, hi, Category.comp_id]

section Flat

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- Two factors replaced by one, with a tail. -/
theorem comp2_reassoc_one {W₀ W₁ W₂ W₃ : 𝒞} {a : W₀ ⟶ W₁} {b : W₁ ⟶ W₂}
    {z : W₀ ⟶ W₂} (h : a ≫ b = z) (r : W₂ ⟶ W₃) : a ≫ b ≫ r = z ≫ r :=
  calc a ≫ b ≫ r = (a ≫ b) ≫ r := by simp only [Category.assoc]
    _ = z ≫ r := congrArg (fun w => w ≫ r) h

/-- Two factors replaced by two, with a tail. -/
theorem comp2_reassoc_two {W₀ W₁ W₂ W₃ W₄ : 𝒞} {a : W₀ ⟶ W₁} {b : W₁ ⟶ W₂}
    {z₁ : W₀ ⟶ W₃} {z₂ : W₃ ⟶ W₂} (h : a ≫ b = z₁ ≫ z₂) (r : W₂ ⟶ W₄) :
    a ≫ b ≫ r = z₁ ≫ z₂ ≫ r :=
  calc a ≫ b ≫ r = (a ≫ b) ≫ r := by simp only [Category.assoc]
    _ = (z₁ ≫ z₂) ≫ r := congrArg (fun w => w ≫ r) h
    _ = z₁ ≫ z₂ ≫ r := Category.assoc _ _ _

/-- Three factors replaced by one, with a tail. -/
theorem comp3_reassoc_one {W₀ W₁ W₂ W₃ W₄ : 𝒞} {a : W₀ ⟶ W₁} {b : W₁ ⟶ W₂}
    {c : W₂ ⟶ W₃} {z : W₀ ⟶ W₃} (h : a ≫ b ≫ c = z) (r : W₃ ⟶ W₄) :
    a ≫ b ≫ c ≫ r = z ≫ r :=
  calc a ≫ b ≫ c ≫ r = (a ≫ b ≫ c) ≫ r := by simp only [Category.assoc]
    _ = z ≫ r := congrArg (fun w => w ≫ r) h

/-- Five factors replaced by two, with a tail. -/
theorem comp5_reassoc_two {W₀ W₁ W₂ W₃ W₄ W₅ W₆ W₇ : 𝒞} {a : W₀ ⟶ W₁} {b : W₁ ⟶ W₂}
    {c : W₂ ⟶ W₃} {d : W₃ ⟶ W₄} {e : W₄ ⟶ W₅} {z₁ : W₀ ⟶ W₆} {z₂ : W₆ ⟶ W₅}
    (h : a ≫ b ≫ c ≫ d ≫ e = z₁ ≫ z₂) (r : W₅ ⟶ W₇) :
    a ≫ b ≫ c ≫ d ≫ e ≫ r = z₁ ≫ z₂ ≫ r :=
  calc a ≫ b ≫ c ≫ d ≫ e ≫ r = (a ≫ b ≫ c ≫ d ≫ e) ≫ r := by simp only [Category.assoc]
    _ = (z₁ ≫ z₂) ≫ r := congrArg (fun w => w ≫ r) h
    _ = z₁ ≫ z₂ ≫ r := Category.assoc _ _ _

/-- A four-fold composite, grouped to the left. -/
theorem comp3_reassoc_left {W₀ W₁ W₂ W₃ W₄ : 𝒞} (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂)
    (c : W₂ ⟶ W₃) (d : W₃ ⟶ W₄) : a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

/-- One factor replaced by two, with a tail. -/
theorem comp1_reassoc_two {W₀ W₁ W₂ W₃ : 𝒞} {a : W₀ ⟶ W₁} {z₁ : W₀ ⟶ W₂}
    {z₂ : W₂ ⟶ W₁} (h : a = z₁ ≫ z₂) (r : W₁ ⟶ W₃) : a ≫ r = z₁ ≫ z₂ ≫ r := by
  rw [h, Category.assoc]

/-- Two transports merged, with a tail. -/
theorem eqToHom_trans_reassoc {W₀ W₁ W₂ W₃ : 𝒞} (h₁ : W₀ = W₁) (h₂ : W₁ = W₂)
    (r : W₂ ⟶ W₃) : eqToHom h₁ ≫ eqToHom h₂ ≫ r = eqToHom (h₁.trans h₂) ≫ r :=
  comp2_reassoc_one (eqToHom_trans h₁ h₂) r

end Flat

section Cocycle

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [HasDerivedCategory.{u} (ModuleCat.{u} C)] [HasDerivedCategory.{u} (ModuleCat.{u} D)]
  (f : A →+* B) (g : B →+* C) (h : C →+* D) (X : DerivedCategory (ModuleCat.{u} A))

/-- **The cocycle condition with the inner composition isomorphism inverted.**  Derived extension
along `h` of `C_{f,g}` read backwards, then `C_{g,h}`, is `C_{g∘f,h}` then `C_{f,h∘g}` read
backwards. -/
theorem map_comp_inv_comp_comp_hom :
    (totalDerivedExtensionScalars.{u, u, u} h).functor.map
          ((totalDerivedExtensionScalarsComp.{u, u} f g).inv.app X) ≫
        (totalDerivedExtensionScalarsComp.{u, u} g h).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X) =
      (totalDerivedExtensionScalarsComp.{u, u} (g.comp f) h).hom.app X ≫
        (totalDerivedExtensionScalarsComp.{u, u} f (h.comp g)).inv.app X := by
  have ha := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_assoc
    f g h X
  refine eq_comp_inv_of _ _
    ((totalDerivedExtensionScalarsComp.{u, u} f (h.comp g)).hom.app X)
    ((totalDerivedExtensionScalarsComp.{u, u} f (h.comp g)).inv.app X)
    (Iso.hom_inv_id_app _ _) ?_
  rw [Category.assoc, ← ha, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Three factors of the cocycle condition collapse to one.**  `C_{g∘f,h}` read backwards, then
derived extension along `h` of `C_{f,g}` read backwards, then `C_{g,h}`, is `C_{f,h∘g}` read
backwards. -/
theorem comp_inv_comp_map_comp_inv_comp_comp_hom :
    (totalDerivedExtensionScalarsComp.{u, u} (g.comp f) h).inv.app X ≫
        (totalDerivedExtensionScalars.{u, u, u} h).functor.map
            ((totalDerivedExtensionScalarsComp.{u, u} f g).inv.app X) ≫
          (totalDerivedExtensionScalarsComp.{u, u} g h).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X) =
      (totalDerivedExtensionScalarsComp.{u, u} f (h.comp g)).inv.app X := by
  rw [map_comp_inv_comp_comp_hom f g h X, ← Category.assoc, Iso.inv_hom_id_app,
    Category.id_comp]

/-- **The cocycle condition with both outer composition isomorphisms inverted.** -/
theorem comp_inv_comp_comp_inv :
    (totalDerivedExtensionScalarsComp.{u, u} f (h.comp g)).inv.app X ≫
        (totalDerivedExtensionScalarsComp.{u, u} g h).inv.app
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X) =
      (totalDerivedExtensionScalarsComp.{u, u} (g.comp f) h).inv.app X ≫
        (totalDerivedExtensionScalars.{u, u, u} h).functor.map
          ((totalDerivedExtensionScalarsComp.{u, u} f g).inv.app X) := by
  refine (eq_comp_inv_of _ _
    ((totalDerivedExtensionScalarsComp.{u, u} g h).hom.app
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X))
    ((totalDerivedExtensionScalarsComp.{u, u} g h).inv.app
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X))
    (Iso.hom_inv_id_app _ _) ?_).symm
  rw [Category.assoc]
  exact comp_inv_comp_map_comp_inv_comp_comp_hom f g h X

/-- **The cocycle condition with the outer composition isomorphism inverted.** -/
theorem comp_inv_comp_map_comp_hom :
    (totalDerivedExtensionScalarsComp.{u, u} g h).inv.app
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X) ≫
        (totalDerivedExtensionScalars.{u, u, u} h).functor.map
          ((totalDerivedExtensionScalarsComp.{u, u} f g).hom.app X) =
      (totalDerivedExtensionScalarsComp.{u, u} f (h.comp g)).hom.app X ≫
        (totalDerivedExtensionScalarsComp.{u, u} (g.comp f) h).inv.app X := by
  have ha := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_assoc
    f g h X
  refine eq_comp_inv_of _ _
    ((totalDerivedExtensionScalarsComp.{u, u} (g.comp f) h).hom.app X)
    ((totalDerivedExtensionScalarsComp.{u, u} (g.comp f) h).inv.app X)
    (Iso.hom_inv_id_app _ _) ?_
  rw [Category.assoc, ha, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end Cocycle

section Transport

variable {R T Q : Type u} [CommRing R] [CommRing T] [CommRing Q]
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} T)]
  [HasDerivedCategory.{u} (ModuleCat.{u} Q)]

/-- **A transport of the inner ring map crosses the composition isomorphism.** -/
theorem map_eqToHom_comp_comp_hom {k l : Q →+* R} (hkl : k = l) (p : R →+* T)
    (X : DerivedCategory (ModuleCat.{u} Q)) :
    (totalDerivedExtensionScalars.{u, u, u} p).functor.map
          (eqToHom (congrArg
            (fun m : Q →+* R => (totalDerivedExtensionScalars.{u, u, u} m).functor.obj X) hkl)) ≫
        (totalDerivedExtensionScalarsComp.{u, u} l p).hom.app X =
      (totalDerivedExtensionScalarsComp.{u, u} k p).hom.app X ≫
        eqToHom (congrArg
          (fun m : Q →+* R => (totalDerivedExtensionScalars.{u, u, u} (p.comp m)).functor.obj X)
          hkl) := by
  subst hkl
  simp

/-- **A transport of the outer ring map crosses the composition isomorphism, read backwards.** -/
theorem comp_inv_comp_congr_hom {k l : R →+* T} (hkl : k = l) (p : Q →+* R)
    (X : DerivedCategory (ModuleCat.{u} Q)) :
    (totalDerivedExtensionScalarsComp.{u, u} p k).inv.app X ≫
        (totalDerivedExtensionScalarsCongr.{u, u} hkl).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj X) =
      (totalDerivedExtensionScalarsCongr.{u, u}
            (congrArg (fun m : R →+* T => m.comp p) hkl)).hom.app X ≫
        (totalDerivedExtensionScalarsComp.{u, u} p l).inv.app X := by
  subst hkl
  simp [totalDerivedExtensionScalarsCongr_rfl]

/-- **Two transports of the ring map, read at a complex, compose to one.** -/
theorem congr_inv_app_comp_congr_hom_app {k l m : Q →+* T} (hkl : k = l) (hkm : k = m)
    (X : DerivedCategory (ModuleCat.{u} Q)) :
    (totalDerivedExtensionScalarsCongr.{u, u} hkl).inv.app X ≫
        (totalDerivedExtensionScalarsCongr.{u, u} hkm).hom.app X =
      eqToHom (congrArg
        (fun r : Q →+* T => (totalDerivedExtensionScalars.{u, u, u} r).functor.obj X)
        (hkl.symm.trans hkm)) := by
  subst hkl
  subst hkm
  simp [totalDerivedExtensionScalarsCongr_rfl]

/-- **A transport of the inner ring map crosses the composition isomorphism read backwards.** -/
theorem comp_inv_comp_map_eqToHom {k l : Q →+* R} (hkl : k = l) (p : R →+* T)
    (X : DerivedCategory (ModuleCat.{u} Q)) :
    (totalDerivedExtensionScalarsComp.{u, u} k p).inv.app X ≫
        (totalDerivedExtensionScalars.{u, u, u} p).functor.map
          (eqToHom (congrArg
            (fun m : Q →+* R => (totalDerivedExtensionScalars.{u, u, u} m).functor.obj X)
            hkl)) =
      eqToHom (congrArg
          (fun m : Q →+* R =>
            (totalDerivedExtensionScalars.{u, u, u} (p.comp m)).functor.obj X) hkl) ≫
        (totalDerivedExtensionScalarsComp.{u, u} l p).inv.app X := by
  subst hkl
  simp

/-- A transport of the derived extension-of-scalars functor, read backwards at a complex. -/
theorem eqToIso_functor_inv_app {k l : Q →+* R} (hkl : k = l)
    (X : DerivedCategory (ModuleCat.{u} Q)) :
    (eqToIso (congrArg
        (fun ψ : Q →+* R => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
        hkl)).inv.app X =
      eqToHom (congrArg
          (fun m : Q →+* R => (totalDerivedExtensionScalars.{u, u, u} m).functor.obj X)
          hkl).symm := by
  subst hkl
  simp

/-- A transport of the derived extension-of-scalars functor, read at a complex. -/
theorem eqToIso_functor_hom_app {k l : Q →+* R} (hkl : k = l)
    (X : DerivedCategory (ModuleCat.{u} Q)) :
    (eqToIso (congrArg
        (fun ψ : Q →+* R => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
        hkl)).hom.app X =
      eqToHom (congrArg
        (fun m : Q →+* R => (totalDerivedExtensionScalars.{u, u, u} m).functor.obj X) hkl) := by
  subst hkl
  simp

end Transport

section Transport2

variable {R T Q : Type u} [CommRing R] [CommRing T] [CommRing Q]
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} T)]
  [HasDerivedCategory.{u} (ModuleCat.{u} Q)]

/-- **A transport of the outer ring map crosses the composition isomorphism.** -/
theorem congr_hom_app_comp_comp_hom {k l : R →+* T} (hkl : k = l) (p : Q →+* R)
    (X : DerivedCategory (ModuleCat.{u} Q)) :
    (totalDerivedExtensionScalarsCongr.{u, u} hkl).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj X) ≫
        (totalDerivedExtensionScalarsComp.{u, u} p l).hom.app X =
      (totalDerivedExtensionScalarsComp.{u, u} p k).hom.app X ≫
        eqToHom (congrArg
          (fun m : R →+* T => (totalDerivedExtensionScalars.{u, u, u} (m.comp p)).functor.obj X)
          hkl) := by
  subst hkl
  simp

end Transport2

section Merge

variable {A₄ A₅ B₄ : Type u} [CommRing A₄] [CommRing A₅] [CommRing B₄] [Algebra A₄ A₅]
  (S : Submonoid A₄) [IsLocalization S A₅] (g : A₅ →+* B₄)
  [HasDerivedCategory.{u} (ModuleCat.{u} A₄)] [HasDerivedCategory.{u} (ModuleCat.{u} A₅)]
  [HasDerivedCategory.{u} (ModuleCat.{u} B₄)]

include S in
/-- **The passage through a localization absorbs the merge and the counit.** For `A₅` a
localization of `A₄` and `g : A₅ →+* B₄`, the merge `Ψ` of the two restrictions extended along
`g ∘ (A₄ → A₅)`, followed by the counit along it, is
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` followed by the counit along
`g`. -/
public theorem map_merge_comp_counit
    (Ψ : (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} (algebraMap A₄ A₅)).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (g.comp (algebraMap A₄ A₅))).mapDerivedCategory)
    (hΨ : Ψ = mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.restrictScalars.{u} (algebraMap A₄ A₅))
      (ModuleCat.restrictScalars.{u} (g.comp (algebraMap A₄ A₅)))
      (ModuleCat.restrictScalarsComp'.{u} (algebraMap A₄ A₅) g
        (g.comp (algebraMap A₄ A₅)) rfl).symm)
    (N : DerivedCategory (ModuleCat.{u} B₄)) :
    (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).functor.map
          (Ψ.hom.app N) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₄ B₄ _ _
          (g.comp (algebraMap A₄ A₅)) _ _
          (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).functor
          (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).comparison
          (totalDerivedExtensionScalars.{u, u, u}
            (g.comp (algebraMap A₄ A₅))).isLeftDerived).counit.app N =
      (restrictScalarsDerivedExtendCompIso.{u, u} S g).hom.app
          ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj N) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₅ B₄ _ _ g _ _
          (totalDerivedExtensionScalars.{u, u, u} g).functor
          (totalDerivedExtensionScalars.{u, u, u} g).comparison
          (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).counit.app N := by
  have hcount : (derivedExtendRestrictAdjunction (A := A₄) (A₂ := A₅)).counit =
      (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₄ A₅ _ _ (algebraMap A₄ A₅) _ _
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A₄ A₅)).functor
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A₄ A₅)).comparison
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A₄ A₅)).isLeftDerived).counit := rfl
  have hmate := totalDerivedExtensionScalarsComp_hom_app_comp_counit
    (algebraMap A₄ A₅) g Ψ hΨ N
  have hnat := (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A₄ A₅) g).hom.naturality
    (Ψ.hom.app N)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  have key : (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A₄ A₅) g).hom.app
          ((ModuleCat.restrictScalars.{u} (algebraMap A₄ A₅)).mapDerivedCategory.obj
            ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj N)) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).functor.map
            (Ψ.hom.app N) ≫
          (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₄ B₄ _ _
            (g.comp (algebraMap A₄ A₅)) _ _
            (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).functor
            (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).comparison
            (totalDerivedExtensionScalars.{u, u, u}
              (g.comp (algebraMap A₄ A₅))).isLeftDerived).counit.app N =
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₄ A₅ _ _ (algebraMap A₄ A₅) _ _
            (totalDerivedExtensionScalars.{u, u, u} (algebraMap A₄ A₅)).functor
            (totalDerivedExtensionScalars.{u, u, u} (algebraMap A₄ A₅)).comparison
            (totalDerivedExtensionScalars.{u, u, u} (algebraMap A₄ A₅)).isLeftDerived).counit.app
            ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj N)) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₅ B₄ _ _ g _ _
          (totalDerivedExtensionScalars.{u, u, u} g).functor
          (totalDerivedExtensionScalars.{u, u, u} g).comparison
          (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).counit.app N := by
    rw [← Category.assoc, ← hnat, Category.assoc, hmate,
      ← CategoryTheory.Functor.map_comp_assoc, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [restrictScalarsDerivedExtendCompIso_hom_app.{u, u} S g,
    restrictScalarsDerivedExtendIso_hom_eq_counit S, hcount, Category.assoc, ← key,
    ← Category.assoc, Iso.inv_hom_id_app]
  exact (Category.id_comp _).symm

include S in
/-- **The passage through a localization absorbs the merge and the counit, read backwards.** For
`A₅` a localization of `A₄` and `g : A₅ →+* B₄`, the inverse of
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso`, the merge `Ψ` of the two
restrictions extended along `g ∘ (A₄ → A₅)` and the counit along it compose to the counit along
`g`. -/
public theorem inv_comp_map_merge_comp_counit
    (Ψ : (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} (algebraMap A₄ A₅)).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (g.comp (algebraMap A₄ A₅))).mapDerivedCategory)
    (hΨ : Ψ = mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.restrictScalars.{u} (algebraMap A₄ A₅))
      (ModuleCat.restrictScalars.{u} (g.comp (algebraMap A₄ A₅)))
      (ModuleCat.restrictScalarsComp'.{u} (algebraMap A₄ A₅) g
        (g.comp (algebraMap A₄ A₅)) rfl).symm)
    (N : DerivedCategory (ModuleCat.{u} B₄)) :
    (restrictScalarsDerivedExtendCompIso.{u, u} S g).inv.app
          ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj N) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).functor.map
            (Ψ.hom.app N) ≫
          (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₄ B₄ _ _
            (g.comp (algebraMap A₄ A₅)) _ _
            (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).functor
            (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A₄ A₅))).comparison
            (totalDerivedExtensionScalars.{u, u, u}
              (g.comp (algebraMap A₄ A₅))).isLeftDerived).counit.app N =
      (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A₅ B₄ _ _ g _ _
        (totalDerivedExtensionScalars.{u, u, u} g).functor
        (totalDerivedExtensionScalars.{u, u, u} g).comparison
        (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).counit.app N := by
  rw [map_merge_comp_counit S g Ψ hΨ N, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

section Unit

variable {R₃ C₃ : Type u} [CommRing R₃] [CommRing C₃]
  [HasDerivedCategory.{u} (ModuleCat.{u} R₃)] [HasDerivedCategory.{u} (ModuleCat.{u} C₃)]

/-- `AlgebraicGeometry.totalDerivedExtensionScalarsIdOf` read backwards at a complex: the
transport along the hypothesis, then the identification for `RingHom.id`. -/
theorem idOf_inv_app (k : R₃ →+* R₃) (hk : k = RingHom.id R₃)
    (X : DerivedCategory (ModuleCat.{u} R₃)) :
    (AlgebraicGeometry.totalDerivedExtensionScalarsIdOf.{u, u} k hk).inv.app X =
      eqToHom (congrArg
          (fun r : R₃ →+* R₃ => (totalDerivedExtensionScalars.{u, u, u} r).functor.obj X) hk) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, u}
          R₃).inv.app X := by
  subst hk
  simp [AlgebraicGeometry.totalDerivedExtensionScalarsIdOf]

/-- **The left unit law, read backwards.**  Derived extension along `b` of the identification of
the identity functor with extension along `RingHom.id` read backwards is the composition
isomorphism of `RingHom.id` with `b`. -/
theorem map_id_inv_app (b : C₃ →+* R₃) (X : DerivedCategory (ModuleCat.{u} C₃)) :
    (totalDerivedExtensionScalars.{u, u, u} b).functor.map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, u}
          C₃).inv.app X) =
      (totalDerivedExtensionScalarsComp.{u, u} (RingHom.id C₃) b).hom.app X := by
  exact Iso.inv_ext (f := (totalDerivedExtensionScalars.{u, u, u} b).functor.mapIso
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, u} C₃).app X))
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_id_comp b X)

/-- **The right unit law, read backwards.**  For `k` equal to the identity, the composition
isomorphism of `b` with `k` read backwards, followed by
`AlgebraicGeometry.totalDerivedExtensionScalarsIdOf` read backwards, is the transport along
`k ∘ b = b`. -/
theorem comp_inv_comp_idOf_inv (k : R₃ →+* R₃) (hk : k = RingHom.id R₃)
    (b : C₃ →+* R₃) (hkb : k.comp b = b) (X : DerivedCategory (ModuleCat.{u} C₃)) :
    (totalDerivedExtensionScalarsComp.{u, u} b k).inv.app X ≫
        (AlgebraicGeometry.totalDerivedExtensionScalarsIdOf.{u, u} k hk).inv.app
          ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj X) =
      eqToHom (congrArg
        (fun r : C₃ →+* R₃ => (totalDerivedExtensionScalars.{u, u, u} r).functor.obj X) hkb) := by
  subst hk
  have hu := Iso.inv_ext
    (f := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, u} R₃).app
      ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj X))
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comp_id b X)
  rw [idOf_inv_app, eqToHom_refl, Category.id_comp]
  exact (congrArg _ hu).trans (Iso.inv_hom_id_app _ _)

end Unit

end Merge

end RingTheory.TorIndependence

namespace AlgebraicGeometry

/-- The two factors of `AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict`: the
composition isomorphism of derived extension of scalars along `b` and `σ` read backwards,
followed by `AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict` at the extension of `N`
along `b`. -/
public theorem totalDerivedExtensionScalarsCompIsoRestrict_hom_app {C R₁ R₂ : Type u}
    [CommRing C] [CommRing R₁] [CommRing R₂]
    [HasDerivedCategory.{u} (ModuleCat.{u} C)] [HasDerivedCategory.{u} (ModuleCat.{u} R₁)]
    [HasDerivedCategory.{u} (ModuleCat.{u} R₂)]
    (b : C →+* R₁) (σ : R₁ →+* R₂) (ε' : R₂ →+* R₁) (h₁ : ∀ x, ε' (σ x) = x)
    (h₂ : ∀ z, σ (ε' z) = z) (N : DerivedCategory (ModuleCat.{u} C)) :
    (totalDerivedExtensionScalarsCompIsoRestrict b σ ε' h₁ h₂).hom.app N =
      (totalDerivedExtensionScalarsComp.{u, u} b σ).inv.app N ≫
        (totalDerivedExtensionScalarsIsoRestrict σ ε' h₁ h₂).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj N) :=
  rfl

/-- **The restriction model met against the counit.** For `ε` invertible with inverse `ε'`,
derived extension along `ε'` of `AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict`,
followed by the counit along `ε'`, is the composition isomorphism of derived extension of scalars
followed by `AlgebraicGeometry.totalDerivedExtensionScalarsIdOf` read backwards. -/
public theorem map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit_eq {R R₂ : Type u}
    [CommRing R] [CommRing R₂]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R₂)]
    (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ z, ε (ε' z) = z)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
          ((totalDerivedExtensionScalarsIsoRestrict.{u, u} ε ε' h₁ h₂).hom.app M) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R₂ R _ _ ε' _ _
          (totalDerivedExtensionScalars.{u, u, u} ε').functor
          (totalDerivedExtensionScalars.{u, u, u} ε').comparison
          (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived).counit.app M =
      (totalDerivedExtensionScalarsComp.{u, u} ε ε').hom.app M ≫
        (totalDerivedExtensionScalarsIdOf.{u, u} (ε'.comp ε) (RingHom.ext h₁)).inv.app M :=
  Eq.trans
    (map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit ε ε' h₁ h₂ _ rfl
      (restrictScalarsIdDerivedIso.{u, u} (ε'.comp ε) (RingHom.ext h₁)).hom
      (fun W => unit_mapDerivedCategory_adjRestrictScalarsOfInv_app ε ε' h₁ h₂ _ rfl W) M)
    (congrArg (fun z => (totalDerivedExtensionScalarsComp.{u, u} ε ε').hom.app M ≫ z)
      (map_restrictScalarsIdDerivedIso_hom_comp_counit (ε'.comp ε) (RingHom.ext h₁) M))

/-- `AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict` met against the counit along
`ε'`: derived extension along `ε'` of the isomorphism, followed by the counit, is the extension of
the inverse composition isomorphism along `b` and `σ`, followed by the composition isomorphism
along `σ` and `ε'` and `AlgebraicGeometry.totalDerivedExtensionScalarsIdOf` read backwards. -/
public theorem map_totalDerivedExtensionScalarsCompIsoRestrict_hom_comp_counit
    {C R₁ R₂ : Type u} [CommRing C] [CommRing R₁]
    [CommRing R₂] [HasDerivedCategory.{u} (ModuleCat.{u} C)]
    [HasDerivedCategory.{u} (ModuleCat.{u} R₁)] [HasDerivedCategory.{u} (ModuleCat.{u} R₂)]
    (b : C →+* R₁) (σ : R₁ →+* R₂) (ε' : R₂ →+* R₁) (h₁ : ∀ x, ε' (σ x) = x)
    (h₂ : ∀ z, σ (ε' z) = z) (N : DerivedCategory (ModuleCat.{u} C)) :
    (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
          ((totalDerivedExtensionScalarsCompIsoRestrict b σ ε' h₁ h₂).hom.app N) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R₂ R₁ _ _ ε' _ _
          (totalDerivedExtensionScalars.{u, u, u} ε').functor
          (totalDerivedExtensionScalars.{u, u, u} ε').comparison
          (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived).counit.app
          ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj N) =
      (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
          ((totalDerivedExtensionScalarsComp.{u, u} b σ).inv.app N) ≫
        (totalDerivedExtensionScalarsComp.{u, u} σ ε').hom.app
            ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj N) ≫
          (totalDerivedExtensionScalarsIdOf.{u, u} (ε'.comp σ) (RingHom.ext h₁)).inv.app
            ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj N) := by
  rw [totalDerivedExtensionScalarsCompIsoRestrict_hom_app, CategoryTheory.Functor.map_comp,
    Category.assoc, map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit_eq]


/-! ### Two transports that need the point and the morphism substituted -/

section SubstTransport

variable {A : CommRingCat.{u}} {𝒳 : Scheme.{u}}

/-- The stalk map is unchanged by precomposing the stalk congruence of a reflexive equality. -/
private theorem stalkMap_hom_eq_stalkCongr_rfl (i : Spec A ⟶ 𝒳) (w : Spec A) :
    (i.stalkMap w).hom =
      ((𝒳.presheaf.stalkCongr (.of_eq (rfl : i w = i w))).hom ≫ i.stalkMap w).hom := by
  simp

/-- The germ localization of the derived stalk, extended along a further map, read at a point
presented through an equality of points. -/
public theorem derivedStalkAffineSections_extend_comp_obj_eq (i : Spec A ⟶ 𝒳) (w : Spec A)
    (z : 𝒳) (hz : z = i w) (K : DerivedCategory 𝒳.Modules) {T : Type u} [CommRing T]
    [HasDerivedCategory.{u} (ModuleCat.{u} T)]
    (r : ToType ((Spec A).presheaf.stalk w) →+* T) :
    (totalDerivedExtensionScalars.{u, u, u} (r.comp (i.stalkMap w).hom)).functor.obj
        ((derivedStalkFunctor (i w)).obj K) =
      (totalDerivedExtensionScalars.{u, u, u}
          (r.comp ((𝒳.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom)).functor.obj
        ((derivedStalkFunctor z).obj K) := by
  subst hz
  exact congrArg (fun s => (totalDerivedExtensionScalars.{u, u, u} (r.comp s)).functor.obj
      ((derivedStalkFunctor (i w)).obj K))
    (stalkMap_hom_eq_stalkCongr_rfl i w)

/-- The transport of the point crosses the composition isomorphism. -/
public theorem map_eqToHom_comp_comp_hom_extend (i : Spec A ⟶ 𝒳) (w : Spec A) (z : 𝒳)
    (hz : z = i w) (K : DerivedCategory 𝒳.Modules) {T T' : Type u} [CommRing T] [CommRing T']
    [HasDerivedCategory.{u} (ModuleCat.{u} T)] [HasDerivedCategory.{u} (ModuleCat.{u} T')]
    (r : ToType ((Spec A).presheaf.stalk w) →+* T) (p : T →+* T') :
    (totalDerivedExtensionScalars.{u, u, u} p).functor.map
          (eqToHom (derivedStalkAffineSections_extend_comp_obj_eq i w z hz K r)) ≫
        (totalDerivedExtensionScalarsComp.{u, u}
            (r.comp ((𝒳.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom) p).hom.app
          ((derivedStalkFunctor z).obj K) =
      (totalDerivedExtensionScalarsComp.{u, u} (r.comp (i.stalkMap w).hom) p).hom.app
          ((derivedStalkFunctor (i w)).obj K) ≫
        eqToHom (derivedStalkAffineSections_extend_comp_obj_eq i w z hz K (p.comp r)) := by
  subst hz
  exact RingTheory.TorIndependence.map_eqToHom_comp_comp_hom
    (congrArg r.comp (stalkMap_hom_eq_stalkCongr_rfl i w))
    p ((derivedStalkFunctor (i w)).obj K)

/-- The transport of a morphism of schemes crosses the composition isomorphism. -/
public theorem comp_inv_comp_map_eqToHom_stalk {A' : CommRingCat.{u}} (y : Spec A')
    (K : DerivedCategory 𝒳.Modules) {T : Type u} [CommRing T]
    [HasDerivedCategory.{u} (ModuleCat.{u} T)] (t t' : Spec A' ⟶ 𝒳) (hw : t = t')
    (p : ToType ((Spec A').presheaf.stalk y) →+* T) :
    (totalDerivedExtensionScalarsComp.{u, u} (t.stalkMap y).hom p).inv.app
          ((derivedStalkFunctor (t y)).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} p).functor.map
            (eqToHom (congrArg
              (fun s : Spec A' ⟶ 𝒳 =>
                (totalDerivedExtensionScalars.{u, u, u} (s.stalkMap y).hom).functor.obj
                  ((derivedStalkFunctor (s y)).obj K)) hw)) ≫
          (totalDerivedExtensionScalarsComp.{u, u} (t'.stalkMap y).hom p).hom.app
            ((derivedStalkFunctor (t' y)).obj K) =
      eqToHom (congrArg
        (fun s : Spec A' ⟶ 𝒳 =>
          (totalDerivedExtensionScalars.{u, u, u} (p.comp (s.stalkMap y).hom)).functor.obj
            ((derivedStalkFunctor (s y)).obj K)) hw) := by
  subst hw
  simp

end SubstTransport

end AlgebraicGeometry

end
