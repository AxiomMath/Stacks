module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom

/-!
# Morphisms from schemes to an algebraic space glue along fppf coverings

An algebraic space `Y` over `S` is an fppf sheaf on the big fppf site of `S`, and a morphism
`U ⟶ Y` from the algebraic space represented by a scheme `U` of the site is a point of `Y` over
`U`.  So morphisms from schemes to `Y` are determined by, and glue from, their restrictions to
the members of a covering family.

## Main results

* `AlgebraicGeometry.Space.schemeSpace_hom_ext_of_mem_topology`: two morphisms which agree on the
  members of a covering family are equal.
* `AlgebraicGeometry.Space.exists_schemeSpace_hom_of_mem_topology`: a family of morphisms on the
  members of a covering family which agree on the fibre products glues.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The point of an algebraic space over a scheme of the site attached to a morphism from the
represented algebraic space. -/
abbrev schemeSpaceSection {Y : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (b : (schemeSpaceFunctor B S hS).obj U ⟶ Y) : Y.obj.obj (op U) :=
  yonedaEquiv b.hom

/-- A morphism from the algebraic space represented by a scheme is determined by its point. -/
theorem schemeSpaceSection_injective {Y : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS} :
    Function.Injective (schemeSpaceSection (Y := Y) (U := U)) :=
  yonedaEquiv.injective.comp (ObjectProperty.ι _).map_injective

/-- The point attached to the composite of a morphism `b` with the map induced by `g : V ⟶ U` is
the restriction along `g` of the point attached to `b`. -/
theorem schemeSpaceSection_map {Y : AlgebraicSpaces B S hS} {U V : BigFppfOver B S hS}
    (g : V ⟶ U) (b : (schemeSpaceFunctor B S hS).obj U ⟶ Y) :
    schemeSpaceSection ((schemeSpaceFunctor B S hS).map g ≫ b) =
      Y.obj.map g.op (schemeSpaceSection b) :=
  (yonedaEquiv_naturality' b.hom g.op).symm

variable {I : Type v} {U : BigFppfOver B S hS} {X : I → BigFppfOver B S hS} (f : ∀ i, X i ⟶ U)

/-- The sheaf condition of an algebraic space for a covering family. -/
theorem isSheafFor_ofArrows_of_mem_topology (Y : AlgebraicSpaces B S hS)
    (hf : Sieve.ofArrows X f ∈ BigFppfOver.topology B S hS U) :
    (Presieve.ofArrows X f).IsSheafFor Y.obj := by
  have h := (isSheaf_iff_isSheaf_of_type _ _).1 Y.property.isSheaf
  exact (Presieve.isSheafFor_iff_generate _).2 (h _ hf)

/-- **Two morphisms from a scheme to an algebraic space agree as soon as they agree on the
members of a covering family.** -/
theorem schemeSpace_hom_ext_of_mem_topology {Y : AlgebraicSpaces B S hS}
    (hf : Sieve.ofArrows X f ∈ BigFppfOver.topology B S hS U)
    (b₁ b₂ : (schemeSpaceFunctor B S hS).obj U ⟶ Y)
    (h : ∀ i, (schemeSpaceFunctor B S hS).map (f i) ≫ b₁ =
      (schemeSpaceFunctor B S hS).map (f i) ≫ b₂) : b₁ = b₂ := by
  refine schemeSpaceSection_injective ?_
  obtain ⟨t, -, ht⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_ofArrows_of_mem_topology f Y hf)
    (fun i => schemeSpaceSection ((schemeSpaceFunctor B S hS).map (f i) ≫ b₁)) (by
      rw [Presieve.Arrows.pullbackCompatible_iff]
      intro i j
      rw [← schemeSpaceSection_map, ← schemeSpaceSection_map, ← Category.assoc, ← Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have h₁ := ht (schemeSpaceSection b₁) fun i => by rw [schemeSpaceSection_map]
  have h₂ := ht (schemeSpaceSection b₂) fun i => by rw [← schemeSpaceSection_map, ← h i]
  exact h₁.trans h₂.symm

/-- **Morphisms from the members of a covering family to an algebraic space which agree on the
fibre products glue** to a morphism from the target of the family. -/
theorem exists_schemeSpace_hom_of_mem_topology {Y : AlgebraicSpaces B S hS}
    (hf : Sieve.ofArrows X f ∈ BigFppfOver.topology B S hS U)
    (b : ∀ i, (schemeSpaceFunctor B S hS).obj (X i) ⟶ Y)
    (hb : ∀ i j, (schemeSpaceFunctor B S hS).map (pullback.fst (f i) (f j)) ≫ b i =
      (schemeSpaceFunctor B S hS).map (pullback.snd (f i) (f j)) ≫ b j) :
    ∃ c : (schemeSpaceFunctor B S hS).obj U ⟶ Y,
      ∀ i, (schemeSpaceFunctor B S hS).map (f i) ≫ c = b i := by
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_ofArrows_of_mem_topology f Y hf) (fun i => schemeSpaceSection (b i)) (by
      rw [Presieve.Arrows.pullbackCompatible_iff]
      intro i j
      rw [← schemeSpaceSection_map, ← schemeSpaceSection_map, hb i j])
  refine ⟨ObjectProperty.homMk (yonedaEquiv.symm t), fun i => schemeSpaceSection_injective ?_⟩
  rw [schemeSpaceSection_map, ← ht i]
  simp only [schemeSpaceSection]
  rw [show (ObjectProperty.homMk (yonedaEquiv.symm t) :
      (schemeSpaceFunctor B S hS).obj U ⟶ Y).hom = yonedaEquiv.symm t from rfl,
    Equiv.apply_symm_apply]

end AlgebraicGeometry.Space

end
