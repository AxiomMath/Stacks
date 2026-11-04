module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleFactorization
public import StacksFrontier.Algebra.DifferentialGraded.DerivedCategory.Octahedron
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated
public import StacksCore.Tactic.StacksAttribute

/-! # The homotopy category of differential graded modules is triangulated

For a differential graded algebra `(A, d)` over a commutative ring `R`, the pretriangulated
structure of Tag 09KH on the homotopy category `K(A, d)` of right differential graded
`A`-modules satisfies the octahedron axiom, so `K(A, d)` is a triangulated category.

## Main results

* `DifferentialGradedModule.instIsTriangulatedHomotopyCategory'`: the octahedron axiom for
  `K(A, d)`, hence its triangulated structure.

## Implementation notes

Mathlib's `CategoryTheory.IsTriangulated.mk'` asks for an octahedron only after replacing the
two given composable morphisms by isomorphic ones. The replacement used here is the one of
Tag 09JX: a pair of composable morphisms of differential graded modules is homotopy equivalent
to a pair of admissible monomorphisms, and for those the octahedron is Tag 09KI. The triangles
produced there are recognised as distinguished through
`DifferentialGradedModule.distinguishedTriangles_eq`.

## References

* [Stacks Project, Tag 09KJ](https://stacks.math.columbia.edu/tag/09KJ)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- A commuting square of isomorphism inverses gives the commuting square of the isomorphisms:
from `e.inv ≫ f = g ≫ e'.inv` one gets `f ≫ e'.hom = e.hom ≫ g`. -/
theorem isoSquare_hom
    {C : Type*} [Category C]
    {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : e.inv ≫ f = g ≫ e'.inv) :
    f ≫ e'.hom = e.hom ≫ g := by
  calc
    f ≫ e'.hom = e.hom ≫ (e.inv ≫ f) ≫ e'.hom := by simp
    _ = e.hom ≫ (g ≫ e'.inv) ≫ e'.hom := by rw [h]
    _ = e.hom ≫ g := by simp

/- The octahedron axiom below is the one for the admissible-sequence structure of Tag 09KH, which
is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] instPretriangulatedHomotopyCategory'

/-- The homotopy category of differential graded modules is triangulated: the pretriangulated
structure of Tag 09KH satisfies the octahedron axiom.

Stated against `DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, whose
distinguished triangles are those of an admissible short exact sequence. The homonymous
instance in `StacksFrontier/Algebra/DGA/Octahedron.lean` is the same axiom for the *other*
pretriangulated structure, `DifferentialGradedModule.instPretriangulatedHomotopyCategory`,
whose distinguished triangles are the cone triangles; the two are distinct statements and
carry distinct names. -/
@[stacks 09KJ, sga "4½ Etat_0 1.2.2" "special case"]
instance instIsTriangulatedHomotopyCategory' (A : DifferentialGradedAlgebra.{u, v} R) :
    IsTriangulated (HomotopyCategory.{u, v, w} A) := by
  refine IsTriangulated.mk' fun X₁ X₂ X₃ u₁₂ u₂₃ => ?_
  induction u₁₂ using Quot.inductionOn with
  | _ f =>
    induction u₂₃ using Quot.inductionOn with
    | _ g =>
      let L : Fin 3 → DifferentialGradedModule.{u, v, w} A := ![X₁.as, X₂.as, X₃.as]
      let arrows : ∀ i : Fin 2, Hom (L i.castSucc) (L i.succ) := by
        intro i
        by_cases h : i.val = 0
        · obtain rfl : i = 0 := Fin.ext h
          simpa [L] using (show Hom X₁.as X₂.as from f)
        · obtain rfl : i = 1 := Fin.ext (by omega)
          simpa [L] using (show Hom X₂.as X₃.as from g)
      obtain ⟨M, m, p, hm, hp, hcomm⟩ :=
        exists_admissibleMono_sequence (A := A) 2 L arrows
      let i₀ : Fin 2 := ⟨0, by decide⟩
      let i₁ : Fin 2 := ⟨1, by decide⟩
      have harrow₀ : arrows i₀ = f := by simp [arrows, i₀, L]
      have harrow₁ : arrows i₁ = g := by simp [arrows, i₁, L]
      obtain ⟨Q₁, Q₂, Q₃, p₁, d₁, p₂, d₂, p₃, d₃, a, b,
        hT₁, hT₂, hT₃, hcomm₁, hcomm₂, hcomm₃, hcomm₄, hT₄⟩ :=
        octahedron_of_isAdmissibleMono (m i₀) (m i₁) (hm i₀) (hm i₁)
      have hIso (i : Fin 3) : IsIso ((toHomotopyCategory A).map (p i)) := by
        obtain ⟨r, h₁, h₂⟩ := hp i
        exact ⟨⟨(toHomotopyCategory A).map r,
          (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).2 h₁,
          (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).2 h₂⟩⟩
      have := hIso 0
      have := hIso 1
      have := hIso 2
      let e₀ : (toHomotopyCategory A).obj X₁.as ≅ (toHomotopyCategory A).obj (M 0) :=
        (asIso ((toHomotopyCategory A).map (p 0))).symm
      let e₁ : (toHomotopyCategory A).obj X₂.as ≅ (toHomotopyCategory A).obj (M 1) :=
        (asIso ((toHomotopyCategory A).map (p 1))).symm
      let e₂ : (toHomotopyCategory A).obj X₃.as ≅ (toHomotopyCategory A).obj (M 2) :=
        (asIso ((toHomotopyCategory A).map (p 2))).symm
      refine ⟨(toHomotopyCategory A).obj (M 0), (toHomotopyCategory A).obj (M 1),
        (toHomotopyCategory A).obj (M 2), Q₁, Q₃, Q₂, (toHomotopyCategory A).map (m i₀),
        (toHomotopyCategory A).map (m i₁), e₀, e₁, e₂,
        ?_, ?_, p₁, d₁, ?_, p₃, d₃, ?_, p₂, d₂, ?_, ?_⟩
      · have h := hcomm i₀
        rw [harrow₀] at h
        exact isoSquare_hom e₀ e₁ _ _ (congrArg (toHomotopyCategory A).map h).symm
      · have h := hcomm i₁
        rw [harrow₁] at h
        exact isoSquare_hom e₁ e₂ _ _ (congrArg (toHomotopyCategory A).map h).symm
      · rwa [distinguishedTriangles_eq]
      · rwa [distinguishedTriangles_eq]
      · rwa [distinguishedTriangles_eq]
      · exact ⟨⟨a, b, hcomm₁, hcomm₂, hcomm₃, hcomm₄, by rwa [distinguishedTriangles_eq]⟩⟩

end DifferentialGradedModule
