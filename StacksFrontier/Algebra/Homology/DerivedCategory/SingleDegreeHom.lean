module

/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Cohomology computes the morphisms between objects in a single degree

For objects of `D(𝒜)` concentrated in the degree `a`, the functor `H^a` is a bijection on
morphisms, so such a system of objects is naturally the `singleFunctor` of its cohomology there.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  DerivedCategory.TStructure

universe w v u v' u'

namespace DerivedCategory

variable {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Bijectivity of `F` on a `Hom` group is invariant under isomorphisms of the two objects. -/
public theorem bijective_map_of_iso {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) {Y Y' Z Z' : C} (eY : Y ≅ Y') (eZ : Z ≅ Z')
    (h : Function.Bijective (fun f : Y' ⟶ Z' => F.map f)) :
    Function.Bijective (fun f : Y ⟶ Z => F.map f) := by
  refine ⟨fun f₁ f₂ hf => ?_, fun m => ?_⟩
  · have h' : F.map (eY.inv ≫ f₁ ≫ eZ.hom) = F.map (eY.inv ≫ f₂ ≫ eZ.hom) := by
      simp only [Functor.map_comp]
      rw [show F.map f₁ = F.map f₂ from hf]
    have h'' := h.injective h'
    exact (cancel_mono eZ.hom).mp ((cancel_epi eY.inv).mp h'')
  · obtain ⟨f, hf⟩ := h.surjective (F.map eY.inv ≫ m ≫ F.map eZ.hom)
    dsimp only at hf
    refine ⟨eY.hom ≫ f ≫ eZ.inv, ?_⟩
    dsimp only
    rw [Functor.map_comp, Functor.map_comp, hf]
    simp [← Functor.map_comp]

/-- `H^a` computes the morphisms between two objects concentrated in degree `a`. -/
public theorem bijective_homologyFunctor_map (a : ℤ) (Y Z : DerivedCategory 𝒜)
    (hY : t.IsLE Y a) (hY' : t.IsGE Y a) (hZ : t.IsLE Z a) (hZ' : t.IsGE Z a) :
    Function.Bijective (fun f : Y ⟶ Z => (homologyFunctor 𝒜 a).map f) := by
  have := hY; have := hY'; have := hZ; have := hZ'
  obtain ⟨Y₀, ⟨eY⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE Y a
  obtain ⟨Z₀, ⟨eZ⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE Z a
  refine bijective_map_of_iso _ eY eZ ?_
  set ε := singleFunctorCompHomologyFunctorIso 𝒜 a with hε
  have key : ∀ {P Q : 𝒜} (g : P ⟶ Q), (homologyFunctor 𝒜 a).map ((singleFunctor 𝒜 a).map g) =
      ε.hom.app P ≫ g ≫ ε.inv.app Q := by
    intro P Q g
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv (ε.app Q)).2 (ε.hom.naturality g)
  refine ⟨fun f g hfg => ?_, fun m => ?_⟩
  · obtain ⟨f', rfl⟩ := (singleFunctor 𝒜 a).map_surjective f
    obtain ⟨g', rfl⟩ := (singleFunctor 𝒜 a).map_surjective g
    simp only [key] at hfg
    exact congrArg _ ((cancel_mono (ε.inv.app Z₀)).mp ((cancel_epi (ε.hom.app Y₀)).mp hfg))
  · refine ⟨(singleFunctor 𝒜 a).map (ε.inv.app Y₀ ≫ m ≫ ε.hom.app Z₀), ?_⟩
    dsimp only
    rw [key]
    simp

/-- **The morphism with a prescribed `H^a`.** Between objects concentrated in degree `a`, `H^a`
is bijective on morphisms, so every map of cohomology objects in degree `a` is `H^a` of exactly
one morphism; this is that morphism. -/
public noncomputable def homOfHomologyMap (a : ℤ) {Y Z : DerivedCategory 𝒜}
    (hY : t.IsLE Y a) (hY' : t.IsGE Y a) (hZ : t.IsLE Z a) (hZ' : t.IsGE Z a)
    (m : (homologyFunctor 𝒜 a).obj Y ⟶ (homologyFunctor 𝒜 a).obj Z) : Y ⟶ Z :=
  (Equiv.ofBijective _ (bijective_homologyFunctor_map a Y Z hY hY' hZ hZ')).symm m

/-- The defining property of `DerivedCategory.homOfHomologyMap`. -/
@[simp]
public theorem homologyFunctor_map_homOfHomologyMap (a : ℤ) {Y Z : DerivedCategory 𝒜}
    (hY : t.IsLE Y a) (hY' : t.IsGE Y a) (hZ : t.IsLE Z a) (hZ' : t.IsGE Z a)
    (m : (homologyFunctor 𝒜 a).obj Y ⟶ (homologyFunctor 𝒜 a).obj Z) :
    (homologyFunctor 𝒜 a).map (homOfHomologyMap a hY hY' hZ hZ' m) = m :=
  (Equiv.ofBijective _ (bijective_homologyFunctor_map a Y Z hY hY' hZ hZ')).apply_symm_apply m

/-- A system of objects of `D(𝒜)` concentrated in the single degree `a` is naturally the
`singleFunctor` of its cohomology in that degree.

`H^a` is a bijection on morphisms between objects concentrated in degree `a`
(`bijective_homologyFunctor_map`), so the components of
`DerivedCategory.singleFunctorCompHomologyFunctorIso` have unique preimages, and each of the two
round trips, together with naturality, is an equality of morphisms that `H^a` may be applied to.
`exists_iso_singleFunctor_obj_of_isGE_of_isLE` gives the pointwise statement only. -/
public noncomputable def isoCompSingleFunctorOfIsLEOfIsGE {J : Type u} [Category.{v} J]
    (B : J ⥤ DerivedCategory 𝒜) (a : ℤ)
    (hLE : ∀ j, t.IsLE (B.obj j) a) (hGE : ∀ j, t.IsGE (B.obj j) a) :
    B ≅ (B ⋙ homologyFunctor 𝒜 a) ⋙ singleFunctor 𝒜 a := by
  let ε := singleFunctorCompHomologyFunctorIso 𝒜 a
  have hbij : ∀ (Y Z : DerivedCategory 𝒜), t.IsLE Y a → t.IsGE Y a → t.IsLE Z a → t.IsGE Z a →
      Function.Bijective (fun f : Y ⟶ Z => (homologyFunctor 𝒜 a).map f) :=
    bijective_homologyFunctor_map a
  have hLE' : ∀ j, t.IsLE (((B ⋙ homologyFunctor 𝒜 a) ⋙ singleFunctor 𝒜 a).obj j) a := fun j =>
    inferInstanceAs (t.IsLE ((singleFunctor 𝒜 a).obj ((homologyFunctor 𝒜 a).obj (B.obj j))) a)
  have hGE' : ∀ j, t.IsGE (((B ⋙ homologyFunctor 𝒜 a) ⋙ singleFunctor 𝒜 a).obj j) a := fun j =>
    inferInstanceAs (t.IsGE ((singleFunctor 𝒜 a).obj ((homologyFunctor 𝒜 a).obj (B.obj j))) a)
  let f : ∀ j, B.obj j ⟶ ((B ⋙ homologyFunctor 𝒜 a) ⋙ singleFunctor 𝒜 a).obj j := fun j =>
    homOfHomologyMap a (hLE j) (hGE j) (hLE' j) (hGE' j)
      (ε.inv.app ((homologyFunctor 𝒜 a).obj (B.obj j)))
  let g : ∀ j, ((B ⋙ homologyFunctor 𝒜 a) ⋙ singleFunctor 𝒜 a).obj j ⟶ B.obj j := fun j =>
    homOfHomologyMap a (hLE' j) (hGE' j) (hLE j) (hGE j)
      (ε.hom.app ((homologyFunctor 𝒜 a).obj (B.obj j)))
  have hf : ∀ j, (homologyFunctor 𝒜 a).map (f j) =
      ε.inv.app ((homologyFunctor 𝒜 a).obj (B.obj j)) := fun j =>
    homologyFunctor_map_homOfHomologyMap a (hLE j) (hGE j) (hLE' j) (hGE' j) _
  have hg : ∀ j, (homologyFunctor 𝒜 a).map (g j) =
      ε.hom.app ((homologyFunctor 𝒜 a).obj (B.obj j)) := fun j =>
    homologyFunctor_map_homOfHomologyMap a (hLE' j) (hGE' j) (hLE j) (hGE j) _
  have hfg : ∀ j, f j ≫ g j = 𝟙 (B.obj j) := fun j => by
    refine (hbij (B.obj j) (B.obj j) (hLE j) (hGE j) (hLE j) (hGE j)).injective ?_
    rw [Functor.map_comp, hf, hg, CategoryTheory.Functor.map_id]
    simp
  have hgf : ∀ j, g j ≫ f j = 𝟙 (((B ⋙ homologyFunctor 𝒜 a) ⋙ singleFunctor 𝒜 a).obj j) :=
    fun j => by
      refine (hbij _ _ (hLE' j) (hGE' j) (hLE' j) (hGE' j)).injective ?_
      rw [Functor.map_comp, hf, hg, CategoryTheory.Functor.map_id]
      simp
  have hnat : ∀ {j k : J} (u : j ⟶ k),
      B.map u ≫ f k = f j ≫ ((B ⋙ homologyFunctor 𝒜 a) ⋙ singleFunctor 𝒜 a).map u :=
    fun {j k} u => by
      refine (hbij (B.obj j) _ (hLE j) (hGE j) (hLE' k) (hGE' k)).injective ?_
      rw [Functor.map_comp, Functor.map_comp, hf, hf]
      exact ε.inv.naturality ((homologyFunctor 𝒜 a).map (B.map u))
  exact NatIso.ofComponents (fun j => ⟨f j, g j, hfg j, hgf j⟩) hnat

/-- **The defining property of `DerivedCategory.isoCompSingleFunctorOfIsLEOfIsGE`.** In degree
`a` its components are the components of
`DerivedCategory.singleFunctorCompHomologyFunctorIso`.

Without this the isomorphism is of no use in an equation: its type admits other inhabitants —
negate every component and naturality and both round trips still hold — so nothing about a
composite through it is determined by the statement that it exists. -/
public theorem homologyFunctor_map_isoCompSingleFunctorOfIsLEOfIsGE_hom_app
    {J : Type u} [Category.{v} J] (B : J ⥤ DerivedCategory 𝒜) (a : ℤ)
    (hLE : ∀ j, t.IsLE (B.obj j) a) (hGE : ∀ j, t.IsGE (B.obj j) a) (j : J) :
    (homologyFunctor 𝒜 a).map ((isoCompSingleFunctorOfIsLEOfIsGE B a hLE hGE).hom.app j) =
      (singleFunctorCompHomologyFunctorIso 𝒜 a).inv.app
        ((homologyFunctor 𝒜 a).obj (B.obj j)) :=
  homologyFunctor_map_homOfHomologyMap a (hLE j) (hGE j)
    (inferInstanceAs (t.IsLE ((singleFunctor 𝒜 a).obj ((homologyFunctor 𝒜 a).obj (B.obj j))) a))
    (inferInstanceAs (t.IsGE ((singleFunctor 𝒜 a).obj ((homologyFunctor 𝒜 a).obj (B.obj j))) a)) _

end DerivedCategory

end
