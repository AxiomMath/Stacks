module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangle

/-!
# A morphism whose first cohomology factors through a `Φ`-acyclic object

Let `C` be an abelian category and `Φ : D⁺(C) ⥤ D⁺(C)` a triangulated functor. Let `u : X ⟶ Y`
be a morphism of `D⁺(C)` with `X` concentrated in degrees `1` and `2` and `Y` in degrees `≥ 1`,
and suppose `H¹(u)` factors as `H¹(X) ⟶ I ⟶ H¹(Y)` with `H¹(Φ(I[0])) = 0`. If moreover
`H⁰(Φ(H²(X)[0])) = 0`, then `H²(Φ(u)) = 0`:

* on `τ_{≤1} X = H¹(X)[-1]`, `u` factors through `I[-1]` (morphisms between objects
  concentrated in degree `1` are morphisms of `C`), and `H²(Φ(I[-1])) = H¹(Φ(I[0])) = 0`;
* `H²(Φ(τ_{≤1} X)) ⟶ H²(Φ X)` is onto, the next term `H²(Φ(τ_{>1} X)) = H⁰(Φ(H²(X)[0]))`
  being zero.

This is the formal core of the mechanism (c) of the single-level argument for the
irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): for `Φ` the Fourier transform,
`u = ℓᵉ Φ(β)` with the image of `ℓᵉ H¹(Φ β)` punctual, and `H²(X) = H²(Φ G)` lisse.

## Main results

* `Stacks.DerivedCategoryPlus.homology_two_map_eq_zero_of_homology_one_map_eq_comp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C) [Φ.CommShift ℤ] [Φ.IsTriangulated]

/-- **`H²(Φ(u)) = 0` when `H¹(u)` factors through a `Φ`-acyclic object**: for `u : X ⟶ Y`,
`X` concentrated in degrees `1` and `2`, `Y` in degrees `≥ 1`, `H¹(u) = p ≫ m` through `I` with
`H¹(Φ(I[0])) = 0`, and `H⁰(Φ(H²(X)[0])) = 0`. -/
theorem homology_two_map_eq_zero_of_homology_one_map_eq_comp {X Y : DerivedCategory.Plus C}
    [X.IsGE 1] [X.IsLE 2] [Y.IsGE 1] (u : X ⟶ Y) {I : C}
    (p : (DerivedCategory.Plus.homologyFunctor C 1).obj X ⟶ I)
    (m : I ⟶ (DerivedCategory.Plus.homologyFunctor C 1).obj Y)
    (hpm : (DerivedCategory.Plus.homologyFunctor C 1).map u = p ≫ m)
    (hI : IsZero ((DerivedCategory.Plus.homologyFunctor C 1).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj I))))
    (hX : IsZero ((DerivedCategory.Plus.homologyFunctor C 0).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj
        ((DerivedCategory.Plus.homologyFunctor C 2).obj X))))) :
    (DerivedCategory.Plus.homologyFunctor C 2).map (Φ.map u) = 0 := by
  let t := DerivedCategory.Plus.TStructure.t (C := C)
  let T := (t.triangleLEGT 1).obj X
  let ιX := (t.truncLEι 1).app X
  let ιY := (t.truncLEι 1).app Y
  have : t.IsGE ((t.truncGT 1).obj X) (1 + 1) :=
    inferInstanceAs (t.IsGE ((t.truncGT 1).obj X) (1 + 1))
  have : t.IsLE ((t.truncGT 1).obj X) (1 + 1) :=
    inferInstanceAs (t.IsLE ((t.truncGT 1).obj X) 2)
  have := DerivedCategory.Plus.isIso_homologyMap_truncLEι_app X 1 1 le_rfl
  have := DerivedCategory.Plus.isIso_homologyMap_truncLEι_app Y 1 1 le_rfl
  have := DerivedCategory.Plus.isIso_homologyMap_truncGTπ_app X (1 + 1) 1 (by omega)
  obtain ⟨M, ⟨e₁⟩⟩ :=
    DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE ((t.truncLE 1).obj X) 1
  obtain ⟨M', ⟨e₂⟩⟩ :=
    DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE ((t.truncLE 1).obj Y) 1
  obtain ⟨N, ⟨e₃⟩⟩ := DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((t.truncGT 1).obj X) (1 + 1)
  -- `H²(Φ(τ_{>1} X)) = 0`
  obtain ⟨e₄⟩ := nonempty_homology_map_singleFunctor_iso Φ (1 + 1) 2 0 (by omega) N
  let eN : N ≅ (DerivedCategory.Plus.homologyFunctor C 2).obj X :=
    (homologySingleFunctorIso (1 + 1) N).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor C (1 + 1)).mapIso e₃.symm ≪≫
      (asIso ((DerivedCategory.Plus.homologyFunctor C (1 + 1)).map
        ((t.truncGTπ 1).app X))).symm
  have h₃ : IsZero ((DerivedCategory.Plus.homologyFunctor C 2).obj (Φ.obj T.obj₃)) :=
    (hX.of_iso ((DerivedCategory.Plus.homologyFunctor C 0).mapIso
      (Φ.mapIso ((DerivedCategory.Plus.singleFunctor C 0).mapIso eN)))).of_iso
      ((DerivedCategory.Plus.homologyFunctor C 2).mapIso (Φ.mapIso e₃) ≪≫ e₄)
  have : Epi ((DerivedCategory.Plus.homologyFunctor C 2).map (Φ.map ιX)) :=
    ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _
      (Φ.map_distinguished _ (t.triangleLEGT_distinguished 1 X)) 2).2 (h₃.eq_of_tgt _ _)
  -- `u` on `τ_{≤1} X`, as a morphism of `C`
  obtain ⟨φ, hφ⟩ := (DerivedCategory.Plus.singleFunctor C 1).map_surjective
    (e₁.inv ≫ (t.truncLE 1).map u ≫ e₂.hom)
  have hnu : (t.truncLE 1).map u ≫ ιY = ιX ≫ u := (t.truncLEι 1).naturality u
  let a₁ := (homologySingleFunctorIso 1 M).inv ≫
    (DerivedCategory.Plus.homologyFunctor C 1).map e₁.inv ≫
      (DerivedCategory.Plus.homologyFunctor C 1).map ιX
  let a₂ := (homologySingleFunctorIso 1 M').inv ≫
    (DerivedCategory.Plus.homologyFunctor C 1).map e₂.inv ≫
      (DerivedCategory.Plus.homologyFunctor C 1).map ιY
  have : IsIso a₂ := by
    dsimp only [a₂]
    infer_instance
  have hnat : φ ≫ (homologySingleFunctorIso 1 M').inv = (homologySingleFunctorIso 1 M).inv ≫
      (DerivedCategory.Plus.homologyFunctor C 1).map
        ((DerivedCategory.Plus.singleFunctor C 1).map φ) :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 1).inv.naturality φ
  have hφa : φ ≫ a₂ = a₁ ≫ p ≫ m :=
    calc φ ≫ a₂ = (homologySingleFunctorIso 1 M).inv ≫
          (DerivedCategory.Plus.homologyFunctor C 1).map
            ((DerivedCategory.Plus.singleFunctor C 1).map φ ≫ e₂.inv ≫ ιY) := by
          simp only [a₂, ← Category.assoc, hnat]
          simp only [Category.assoc, Functor.map_comp]
      _ = a₁ ≫ p ≫ m := by
          rw [hφ]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          rw [hnu]
          simp only [Functor.map_comp, hpm, a₁, Category.assoc]
  have hφ' : φ = (a₁ ≫ p) ≫ m ≫ inv a₂ := by
    rw [← Category.assoc, IsIso.eq_comp_inv, hφa]
    simp only [Category.assoc]
  -- `H²(Φ(φ[-1])) = 0`, `φ` factoring through `I`
  obtain ⟨e₅⟩ := nonempty_homology_map_singleFunctor_iso Φ 1 2 1 (by omega) I
  have hI' : IsZero ((DerivedCategory.Plus.homologyFunctor C 2).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 1).obj I))) := hI.of_iso e₅
  have hz : (DerivedCategory.Plus.homologyFunctor C 2).map
      (Φ.map ((DerivedCategory.Plus.singleFunctor C 1).map φ)) = 0 := by
    rw [hφ', Functor.map_comp, Functor.map_comp, Functor.map_comp,
      hI'.eq_of_src ((DerivedCategory.Plus.homologyFunctor C 2).map
        (Φ.map ((DerivedCategory.Plus.singleFunctor C 1).map (m ≫ inv a₂)))) 0, comp_zero]
  have hv : ιX ≫ u = e₁.hom ≫ (DerivedCategory.Plus.singleFunctor C 1).map φ ≫ e₂.inv ≫ ιY := by
    rw [hφ, ← hnu]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  refine (cancel_epi ((DerivedCategory.Plus.homologyFunctor C 2).map (Φ.map ιX))).1 ?_
  rw [comp_zero, ← Functor.map_comp, ← Functor.map_comp, hv]
  simp only [Functor.map_comp, hz, zero_comp, comp_zero]

end Stacks.DerivedCategoryPlus

end
