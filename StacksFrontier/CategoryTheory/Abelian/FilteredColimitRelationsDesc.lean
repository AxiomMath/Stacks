module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Morphisms out of a quotient of a filtered colimit, given generators of the relations

Let `C` be an abelian category in which colimits of shape `J` are exact, `J` connected (for
instance filtered), `E : J ⥤ C` a diagram and `π : E ⟶ const F` a cocone whose components are
jointly epimorphic.  Suppose that for every `j` a family of morphisms `κ_{j, r} : P_r ⟶ E_j`
with `κ_{j, r} ≫ π_j = 0` generates the kernel of `π_j`.  Then a compatible family of morphisms
`ψ_j : E_j ⟶ N` killing every `κ_{j, r}` descends uniquely to a morphism `F ⟶ N`.

The kernel of the induced morphism `colim E ⟶ F` is the colimit of the kernels of the `π_j`,
colimits of shape `J` being exact, and that is killed by the induced morphism `colim E ⟶ N`.

## Main results

* `CategoryTheory.Abelian.existsUnique_desc_of_relations`: a compatible family of morphisms
  `ψ_j : E_j ⟶ N` killing every `κ_{j, r}` descends uniquely to a morphism `F ⟶ N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] {J : Type w} [SmallCategory J] [IsConnected J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- **A compatible family killing generators of the relations descends to the quotient.** -/
theorem existsUnique_desc_of_relations (E : J ⥤ C) {F : C} (π : E ⟶ (Functor.const J).obj F)
    (hπ : ∀ {N : C} (g : F ⟶ N), (∀ j, π.app j ≫ g = 0) → g = 0)
    {R : J → Type*} (P : ∀ j, R j → C) (κ : ∀ j r, P j r ⟶ E.obj j)
    (hκπ : ∀ j r, κ j r ≫ π.app j = 0)
    (hκ : ∀ j {N : C} (g : kernel (π.app j) ⟶ N),
      (∀ r, kernel.lift (π.app j) (κ j r) (hκπ j r) ≫ g = 0) → g = 0)
    {N : C} (ψ : E ⟶ (Functor.const J).obj N) (hψ : ∀ j r, κ j r ≫ ψ.app j = 0) :
    ∃! φ : F ⟶ N, ∀ j, π.app j ≫ φ = ψ.app j := by
  have : PreservesFiniteLimits (colim (J := J) (C := C)) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  let eF : colimit ((Functor.const J).obj F) ≅ F :=
    (colimit.isColimit ((Functor.const J).obj F)).coconePointUniqueUpToIso
      (isColimitConstCocone J F)
  let eN : colimit ((Functor.const J).obj N) ≅ N :=
    (colimit.isColimit ((Functor.const J).obj N)).coconePointUniqueUpToIso
      (isColimitConstCocone J N)
  have heF : ∀ j, colimit.ι ((Functor.const J).obj F) j ≫ eF.hom = 𝟙 F := fun j =>
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitConstCocone J F) j
  have heN : ∀ j, colimit.ι ((Functor.const J).obj N) j ≫ eN.hom = 𝟙 N := fun j =>
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitConstCocone J N) j
  have hιF : ∀ j, colimit.ι ((Functor.const J).obj F) j = eF.inv := fun j =>
    (Iso.comp_hom_eq_id eF).1 (heF j)
  have h₁ : ∀ j, π.app j ≫ eF.inv = colimit.ι E j ≫ colim.map π := fun j =>
    (congrArg (π.app j ≫ ·) (hιF j)).symm.trans (colimit.ι_map π j).symm
  have h₂ : ∀ j, colimit.ι E j ≫ colim.map ψ ≫ eN.hom = ψ.app j := fun j => by
    rw [← Category.assoc, colimit.ι_map, Category.assoc]
    exact (congrArg (ψ.app j ≫ ·) (heN j)).trans (Category.comp_id _)
  have hker : ∀ j, kernel.ι (π.app j) ≫ ψ.app j = 0 := fun j =>
    hκ j _ fun r => by rw [kernel.lift_ι_assoc, hψ]
  have hι : kernel.ι π ≫ ψ = 0 := by
    ext j
    have h := PreservesKernel.iso_hom ((evaluation J C).obj j) π
    have h₂ : (kernel.ι π).app j =
        (PreservesKernel.iso ((evaluation J C).obj j) π).hom ≫ kernel.ι (π.app j) := by
      rw [h]
      exact (kernelComparison_comp_ι π ((evaluation J C).obj j)).symm
    rw [NatTrans.comp_app, h₂, Category.assoc, hker, comp_zero]
    rfl
  have hkerColim : kernel.ι (colim.map π) ≫ colim.map ψ = 0 := by
    have h₁ : (PreservesKernel.iso colim π).inv ≫ colim.map (kernel.ι π) =
        kernel.ι (colim.map π) := PreservesKernel.iso_inv_ι colim π
    rw [← h₁, Category.assoc, ← colim.map_comp, hι, colim.map_zero, comp_zero]
  have hepi : Epi (colim.map π) := by
    refine Preadditive.epi_of_cancel_zero _ fun {Z} g hg => ?_
    have h := hπ (eF.inv ≫ g) fun j => by
      rw [← Category.assoc, h₁, Category.assoc, hg, comp_zero]
    simpa only [Iso.hom_inv_id_assoc, comp_zero] using congrArg (eF.hom ≫ ·) h
  let d := Abelian.epiDesc (colim.map π) (colim.map ψ ≫ eN.hom)
    (by rw [← Category.assoc, hkerColim, zero_comp])
  have hd : ∀ j, π.app j ≫ eF.inv ≫ d = ψ.app j := fun j => by
    rw [← Category.assoc, h₁, Category.assoc, Abelian.comp_epiDesc, h₂]
  refine ⟨eF.inv ≫ d, hd, fun φ hφ => sub_eq_zero.1 (hπ _ fun j => ?_)⟩
  rw [Preadditive.comp_sub, hφ, hd, sub_self]

end CategoryTheory.Abelian

end
