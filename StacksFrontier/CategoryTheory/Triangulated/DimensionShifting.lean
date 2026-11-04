module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksFrontier.CategoryTheory.Triangulated.MapTriangleHom

/-!
# Dimension shifting for a transformation of triangulated functors into a derived category

Let `τ : Φ ⟶ Ψ` be a natural transformation, compatible with the shift, between two triangulated
functors from a pretriangulated category `C` to the derived category `D(B)` of an abelian
category. Let `P` be a class of objects of `C` with the property that every member `X` of `P`
sits in a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` whose middle vertex `Y` is an object at
which `τ` is invertible and whose third vertex `Z` is again in `P`. If, in addition, `τ` induces
isomorphisms on the cohomology objects `H^q` in negative degrees `q < 0` at every member of `P`,
then `τ` is invertible at every member of `P`.

This is the dimension-shifting argument by which a comparison of two δ-functors is shown to be an
isomorphism from its being one on a class of "effacing" objects: the long exact cohomology
sequences of the two image triangles, compared by `τ`, give by the four lemma first that
`H^n(τ)` is a monomorphism at every member of `P` once all `H^q(τ)` with `q < n` are
isomorphisms there, and then that `H^n(τ)` is an isomorphism; an induction on `n` and the
conservativity of the family of cohomology functors on `D(B)` conclude.

## Main results

* `Stacks.Triangulated.mono_homologyMap_hom₁_of_triangleMorphism`,
  `Stacks.Triangulated.epi_homologyMap_hom₁_of_triangleMorphism` — the two four lemmas for the
  first vertex of a morphism of distinguished triangles of `D(B)`.
* `Stacks.Triangulated.isIso_app_of_dimensionShifting` — the dimension-shifting argument.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Triangulated

section Ladder

variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {S T : Triangle (DerivedCategory B)} (hS : S ∈ distTriang (DerivedCategory B))
  (hT : T ∈ distTriang (DerivedCategory B)) (φ : S ⟶ T)

/-- A functor out of `D(B)` turns the first square of a morphism of triangles into a square. -/
private theorem map_comm₁ (F : DerivedCategory B ⥤ B) :
    F.map S.mor₁ ≫ F.map φ.hom₂ = F.map φ.hom₁ ≫ F.map T.mor₁ := by
  rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁]

/-- A functor out of `D(B)` turns the second square of a morphism of triangles into a square. -/
private theorem map_comm₂ (F : DerivedCategory B ⥤ B) :
    F.map S.mor₂ ≫ F.map φ.hom₃ = F.map φ.hom₂ ≫ F.map T.mor₂ := by
  rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂]

/-- The connecting maps of the long exact homology sequences commute with a morphism of
triangles. -/
private theorem δ_comp_homologyMap_hom₁ (i j : ℤ) (hij : i + 1 = j) :
    DerivedCategory.HomologySequence.δ S i j hij ≫
        (DerivedCategory.homologyFunctor B j).map φ.hom₁ =
      (DerivedCategory.homologyFunctor B i).map φ.hom₃ ≫
        DerivedCategory.HomologySequence.δ T i j hij :=
  ((DerivedCategory.homologyFunctor B 0).homologySequenceδ_naturality φ i j hij).symm

include hS hT

/-- **The four lemma for the first vertex, monomorphism half.** For a morphism `φ` of
distinguished triangles of `D(B)` and `i + 1 = j`, the map `H^j(φ₁)` is a monomorphism when
`H^i(φ₂)` is an epimorphism and `H^i(φ₃)` and `H^j(φ₂)` are monomorphisms: this is the four lemma
on the ladder `H^i(S₂) ⟶ H^i(S₃) ⟶ H^j(S₁) ⟶ H^j(S₂)` of long exact sequences. -/
public theorem mono_homologyMap_hom₁_of_triangleMorphism (i j : ℤ) (hij : i + 1 = j)
    (h₂ : Epi ((DerivedCategory.homologyFunctor B i).map φ.hom₂))
    (h₃ : Mono ((DerivedCategory.homologyFunctor B i).map φ.hom₃))
    (h₂' : Mono ((DerivedCategory.homologyFunctor B j).map φ.hom₂)) :
    Mono ((DerivedCategory.homologyFunctor B j).map φ.hom₁) := by
  let row (U : Triangle (DerivedCategory B)) : ComposableArrows B 3 :=
    ComposableArrows.mk₃ ((DerivedCategory.homologyFunctor B i).map U.mor₂)
      (DerivedCategory.HomologySequence.δ U i j hij)
      ((DerivedCategory.homologyFunctor B j).map U.mor₁)
  have ex {U : Triangle (DerivedCategory B)} (hU : U ∈ distTriang (DerivedCategory B)) :
      (row U).Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₃ _ hU i j hij).exact_toComposableArrows
      (DerivedCategory.HomologySequence.exact₁ _ hU i j hij).exact_toComposableArrows
  let φ' : row S ⟶ row T :=
    ComposableArrows.homMk₃ ((DerivedCategory.homologyFunctor B i).map φ.hom₂)
      ((DerivedCategory.homologyFunctor B i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor B j).map φ.hom₁)
      ((DerivedCategory.homologyFunctor B j).map φ.hom₂)
      (map_comm₂ φ _) (δ_comp_homologyMap_hom₁ φ i j hij) (map_comm₁ φ _)
  exact Abelian.mono_of_epi_of_mono_of_mono φ' (ex hS) (ex hT) h₂ h₃ h₂'

/-- **The four lemma for the first vertex, epimorphism half.** For a morphism `φ` of
distinguished triangles of `D(B)` and `i + 1 = j`, the map `H^j(φ₁)` is an epimorphism when
`H^i(φ₃)` and `H^j(φ₂)` are epimorphisms and `H^j(φ₃)` is a monomorphism: this is the four lemma
on the ladder `H^i(S₃) ⟶ H^j(S₁) ⟶ H^j(S₂) ⟶ H^j(S₃)` of long exact sequences. -/
public theorem epi_homologyMap_hom₁_of_triangleMorphism (i j : ℤ) (hij : i + 1 = j)
    (h₃ : Epi ((DerivedCategory.homologyFunctor B i).map φ.hom₃))
    (h₂' : Epi ((DerivedCategory.homologyFunctor B j).map φ.hom₂))
    (h₃' : Mono ((DerivedCategory.homologyFunctor B j).map φ.hom₃)) :
    Epi ((DerivedCategory.homologyFunctor B j).map φ.hom₁) := by
  let row (U : Triangle (DerivedCategory B)) : ComposableArrows B 3 :=
    ComposableArrows.mk₃ (DerivedCategory.HomologySequence.δ U i j hij)
      ((DerivedCategory.homologyFunctor B j).map U.mor₁)
      ((DerivedCategory.homologyFunctor B j).map U.mor₂)
  have ex {U : Triangle (DerivedCategory B)} (hU : U ∈ distTriang (DerivedCategory B)) :
      (row U).Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₁ _ hU i j hij).exact_toComposableArrows
      (DerivedCategory.HomologySequence.exact₂ _ hU j).exact_toComposableArrows
  let φ' : row S ⟶ row T :=
    ComposableArrows.homMk₃ ((DerivedCategory.homologyFunctor B i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor B j).map φ.hom₁)
      ((DerivedCategory.homologyFunctor B j).map φ.hom₂)
      ((DerivedCategory.homologyFunctor B j).map φ.hom₃)
      (δ_comp_homologyMap_hom₁ φ i j hij) (map_comm₁ φ _) (map_comm₂ φ _)
  exact Abelian.epi_of_epi_of_epi_of_mono φ' (ex hS) (ex hT) h₃ h₂' h₃'

end Ladder

section DimensionShifting

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {Φ Ψ : C ⥤ DerivedCategory B} [Φ.CommShift ℤ] [Ψ.CommShift ℤ]
  [Φ.IsTriangulated] [Ψ.IsTriangulated] (τ : Φ ⟶ Ψ) [NatTrans.CommShift τ ℤ]
  (P : C → Prop)

/-- The property of a class `P` that every member sits as the first vertex of a distinguished
triangle whose second vertex is an object at which `τ` is invertible and whose third vertex is
again in `P`. -/
private abbrev Effacing : Prop :=
  ∀ X, P X → ∃ (Y Z : C) (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk a b c ∈ distTriang C ∧ IsIso (τ.app Y) ∧ P Z

/-- One step of the dimension shift, monomorphism half: if `H^q(τ)` is invertible at every
member of an effacing class `P` for every `q < n`, then `H^n(τ)` is a monomorphism at every
member of `P`. -/
private theorem mono_of_lt (hP : Effacing τ P) (n : ℤ)
    (hlt : ∀ X, P X → ∀ q : ℤ, q < n →
      IsIso ((DerivedCategory.homologyFunctor B q).map (τ.app X)))
    (X : C) (hX : P X) : Mono ((DerivedCategory.homologyFunctor B n).map (τ.app X)) := by
  obtain ⟨Y, Z, a, b, c, hT, hY, hZ⟩ := hP X hX
  have := hY
  have := hlt Z hZ (n - 1) (by omega)
  exact mono_homologyMap_hom₁_of_triangleMorphism (Φ.map_distinguished _ hT)
    (Ψ.map_distinguished _ hT) (StacksDraft.CompactDevissage.mapTriangleHom τ (Triangle.mk a b c))
    (n - 1) n (by omega)
    (inferInstanceAs (Epi ((DerivedCategory.homologyFunctor B (n - 1)).map (τ.app Y))))
    (inferInstanceAs (Mono ((DerivedCategory.homologyFunctor B (n - 1)).map (τ.app Z))))
    (inferInstanceAs (Mono ((DerivedCategory.homologyFunctor B n).map (τ.app Y))))

/-- One step of the dimension shift, isomorphism half: if `H^q(τ)` is invertible at every
member of an effacing class `P` for every `q < n`, then so is `H^n(τ)`. -/
private theorem isIso_of_lt (hP : Effacing τ P) (n : ℤ)
    (hlt : ∀ X, P X → ∀ q : ℤ, q < n →
      IsIso ((DerivedCategory.homologyFunctor B q).map (τ.app X)))
    (X : C) (hX : P X) : IsIso ((DerivedCategory.homologyFunctor B n).map (τ.app X)) := by
  have hmono := mono_of_lt τ P hP n hlt X hX
  obtain ⟨Y, Z, a, b, c, hT, hY, hZ⟩ := hP X hX
  have := hY
  have := hlt Z hZ (n - 1) (by omega)
  have hepi : Epi ((DerivedCategory.homologyFunctor B n).map (τ.app X)) :=
    epi_homologyMap_hom₁_of_triangleMorphism (Φ.map_distinguished _ hT)
      (Ψ.map_distinguished _ hT)
      (StacksDraft.CompactDevissage.mapTriangleHom τ (Triangle.mk a b c)) (n - 1) n (by omega)
      (inferInstanceAs (Epi ((DerivedCategory.homologyFunctor B (n - 1)).map (τ.app Z))))
      (inferInstanceAs (Epi ((DerivedCategory.homologyFunctor B n).map (τ.app Y))))
      (mono_of_lt τ P hP n hlt Z hZ)
  exact isIso_of_mono_of_epi _

/-- **Dimension shifting.** Let `τ : Φ ⟶ Ψ` be a transformation compatible with the shift
between triangulated functors from `C` to `D(B)`, and let `P` be a class of objects of `C` such
that every member `X` sits in a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with `τ` invertible
at `Y` and `Z` again in `P`. If `H^q(τ)` is invertible at every member of `P` in every negative
degree `q`, then `τ` is invertible at every member of `P`. -/
public theorem isIso_app_of_dimensionShifting
    (hP : ∀ X, P X → ∃ (Y Z : C) (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang C ∧ IsIso (τ.app Y) ∧ P Z)
    (hneg : ∀ X, P X → ∀ q : ℤ, q < 0 →
      IsIso ((DerivedCategory.homologyFunctor B q).map (τ.app X)))
    (X : C) (hX : P X) : IsIso (τ.app X) := by
  have key : ∀ m : ℕ, ∀ X, P X → ∀ q : ℤ, q < m →
      IsIso ((DerivedCategory.homologyFunctor B q).map (τ.app X)) := by
    intro m
    induction m with
    | zero => exact fun X hX q hq => hneg X hX q (by exact_mod_cast hq)
    | succ m ih =>
      intro X hX q hq
      have hq' : q ≤ (m : ℤ) := by push_cast at hq; omega
      rcases lt_or_eq_of_le hq' with h | h
      · exact ih X hX q h
      · subst h
        exact isIso_of_lt τ P hP m ih X hX
  rw [DerivedCategory.isIso_iff]
  intro q
  exact key (q.toNat + 1) X hX q (by omega)

end DimensionShifting

end Stacks.Triangulated
