module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomFromSingle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIsoAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# The edge map of a class, under base change, and over a separably closed field

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions (inverse and direct image along `f` and along its base
change `f'`), `G`, `H` functors (inverse images along the base change square) and
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` a transformation, so that its mate `β : R₁ ⋙ G ⟶ H ⋙ R₂` is the base change
map. For a class `c : L₁ a ⟶ b`, its *edge* is the adjoint `c♭ = η_a ≫ R₁ c : a ⟶ R₁ b`. The edge
of `c`, moved by `G` and followed by the base change map, is the edge of the moved class
`α_a ≫ H c` (`CategoryTheory.map_homEquiv_comp_mateEquiv_app`). This is the formal half of the
statement that the class `c ∈ H²(X, F)` gives a section of `R² f_* F` whose value at a geometric
point is the restriction of `c` to the geometric fibre.

The other half is the computation over the spectrum of a separably closed field `Ω`: there global
sections are an equivalence onto abelian groups, so the constant sheaf `ℤ_Ω` is projective
(`Stacks.EtaleCohomology.projective_constantSheaf_uliftInt_of_isSepClosed`), and morphisms
`ℤ_Ω[0] ⟶ K` in the derived category are morphisms `ℤ_Ω ⟶ H⁰(K)`, for every complex `K`
(`DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_projective`).

## Main results

* `CategoryTheory.map_homEquiv_comp_mateEquiv_app`: the edge of a class under base change.
* `DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_projective`: `H⁰` is bijective
  on morphisms out of a projective object placed in degree `0`.
* `Stacks.EtaleCohomology.projective_constantSheaf_uliftInt_of_isSepClosed`: the constant sheaf
  `ℤ` is projective over a separably closed field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **The edge of a class under base change.** For `c : L₁ a ⟶ b` with adjoint
`c♭ = η_a ≫ R₁ c`, the image `G c♭` followed by the mate of `α` is the adjoint of the moved
class `α_a ≫ H c`. -/
theorem map_homEquiv_comp_mateEquiv_app (α : TwoSquare G L₁ L₂ H) {a : A} {b : B}
    (c : L₁.obj a ⟶ b) :
    G.map (adj₁.homEquiv a b c) ≫ (mateEquiv adj₁ adj₂ α).app b =
      adj₂.homEquiv (G.obj a) (H.obj b) (α.app a ≫ H.map c) := by
  have hn := (mateEquiv adj₁ adj₂ α).naturality c
  simp only [Functor.comp_map] at hn
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, hn,
    ← Category.assoc, unit_mateEquiv, Category.assoc, ← Functor.map_comp]
  rfl

end CategoryTheory

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **Morphisms out of a projective object in degree `0` are morphisms into `H⁰`**: for `A`
projective and any `E` in `D(C)`, `H⁰` is a bijection `(A[0] ⟶ E) → (H⁰(A[0]) ⟶ H⁰(E))`. -/
theorem bijective_homologyFunctor_map_singleFunctor_of_projective (A : C) [Projective A]
    (E : DerivedCategory C) :
    Function.Bijective
      (fun x : (singleFunctor C 0).obj A ⟶ E => (homologyFunctor C 0).map x) := by
  refine bijective_homologyFunctor_map_singleFunctor A ⊤ (fun _ _ _ => trivial)
    (fun _ _ => trivial) (fun X _ hX f => ?_) E trivial
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE (-1)
  have h0 := from_singleFunctor_obj_eq_zero_of_projective (P := A) (L := K) (i := 0)
    ((singleFunctorIsoCompQ C 0).inv.app A ≫ f ≫ e.hom) (-1) (by omega)
  have : f = (singleFunctorIsoCompQ C 0).hom.app A ≫
      ((singleFunctorIsoCompQ C 0).inv.app A ≫ f ≫ e.hom) ≫ e.inv := by
    simp
  rw [this, h0, zero_comp, comp_zero]

end DerivedCategory

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The constant sheaf `ℤ` on the small étale site of the spectrum of a separably closed field is
projective. -/
theorem projective_constantSheaf_uliftInt_of_isSepClosed :
    Projective ((constantSheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  have := isEquivalence_sheafSections_final_of_isSepClosed Ω AddCommGrpCat.{u + 1}
  have : IsIso (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))).hom :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of Ω))))
  exact (constantSheafAdj (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}
    (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).map_projective _
      Stacks.ChaoticSite.projective_uliftIntAddCommGrp

end Stacks.EtaleCohomology

end
