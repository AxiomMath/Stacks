module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Chain maps which are termwise bijective on morphisms into a fixed complex

Let `p : X ⟶ Y` and `Z` be homological complexes in a preadditive category such that, for all
degrees `k` and `l`, precomposition with `p.f k` is a bijection
`Hom(Y.X k, Z.X l) → Hom(X.X k, Z.X l)`. Then precomposition with `p` is a bijection from
morphisms `Y ⟶ Z` to morphisms `X ⟶ Z` in the homotopy category: a chain map `X ⟶ Z` factors
termwise through `p`, and the factorization commutes with the differentials by the injectivity of
precomposition; a homotopy between composites with `p` factors termwise through `p` in the same
way.

## Main definitions

* `HomologicalComplex.descOfBijectiveComp`: the factorization `Y ⟶ Z` of a chain map `X ⟶ Z`
  through `p`.
* `Homotopy.ofBijectiveComp`: a homotopy between `p ≫ a` and `p ≫ b` gives one between `a` and
  `b`.

## Main results

* `HomotopyCategory.bijective_quotient_map_comp`: precomposition with `p` is bijective on
  morphisms to `Z` in the homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {V : Type*} [Category V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}
  {X Y Z : HomologicalComplex V c} (p : X ⟶ Y)
  (hp : ∀ k l, Function.Bijective (fun f : Y.X k ⟶ Z.X l => p.f k ≫ f))

/-- The termwise factorization through `p` of a family of morphisms `X.X k ⟶ Z.X l`, when
precomposition with every `p.f k` is bijective. -/
def precompInv {k l : ι} (g : X.X k ⟶ Z.X l) : Y.X k ⟶ Z.X l :=
  (Equiv.ofBijective _ (hp k l)).symm g

/-- Precomposing `precompInv p hp g` with `p.f k` gives `g`. -/
@[reassoc (attr := simp)]
theorem comp_precompInv {k l : ι} (g : X.X k ⟶ Z.X l) : p.f k ≫ precompInv p hp g = g :=
  (Equiv.ofBijective _ (hp k l)).apply_symm_apply g

/-- The chain map `Y ⟶ Z` through which a chain map `g : X ⟶ Z` factors along `p`, when
precomposition with each `p.f k` is bijective on morphisms into the terms of `Z`. -/
def descOfBijectiveComp (g : X ⟶ Z) : Y ⟶ Z where
  f k := precompInv p hp (g.f k)
  comm' k l _ := (hp k l).1 <| by
    change p.f k ≫ _ ≫ _ = p.f k ≫ _ ≫ _
    rw [comp_precompInv_assoc, p.comm_assoc, comp_precompInv, g.comm]

/-- The composite of `p` with `descOfBijectiveComp p hp g` is `g`. -/
@[reassoc (attr := simp)]
theorem comp_descOfBijectiveComp (g : X ⟶ Z) : p ≫ descOfBijectiveComp p hp g = g := by
  ext k
  exact comp_precompInv p hp (g.f k)

end HomologicalComplex

namespace Homotopy

open HomologicalComplex

variable {V : Type*} [Category V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}
  {X Y Z : HomologicalComplex V c} (p : X ⟶ Y)
  (hp : ∀ k l, Function.Bijective (fun f : Y.X k ⟶ Z.X l => p.f k ≫ f))

/-- The homotopy between `a` and `b` obtained from a homotopy between `p ≫ a` and `p ≫ b`, when
precomposition with each `p.f k` is bijective on morphisms into the terms of `Z`. -/
def ofBijectiveComp {a b : Y ⟶ Z} (H : Homotopy (p ≫ a) (p ≫ b)) : Homotopy a b where
  hom i j := precompInv p hp (H.hom i j)
  zero i j hij := (hp i j).1 <| by
    change p.f i ≫ _ = p.f i ≫ 0
    rw [comp_precompInv, H.zero i j hij, comp_zero]
  comm i := (hp i i).1 <| by
    change p.f i ≫ _ = p.f i ≫ _
    have h₁ := dNext_comp_left p (fun i j => precompInv p hp (H.hom i j)) i
    have h₂ := prevD_comp_left p (fun i j => precompInv p hp (H.hom i j)) i
    simp only [comp_precompInv] at h₁ h₂
    simpa only [Preadditive.comp_add, ← h₁, ← h₂, comp_f] using H.comm i

end Homotopy

namespace HomotopyCategory

open HomologicalComplex

/-- **Precomposition with a termwise precomposition-bijective chain map is bijective in the
homotopy category.** Let `p : X ⟶ Y` be a chain map such that precomposition with each `p.f k` is
a bijection `Hom(Y.X k, Z.X l) → Hom(X.X k, Z.X l)`. Then precomposition with the class of `p` is
a bijection from morphisms `Y ⟶ Z` to morphisms `X ⟶ Z` in the homotopy category. -/
theorem bijective_quotient_map_comp {V : Type*} [Category V] [Preadditive V]
    {ι : Type*} {c : ComplexShape ι} {X Y Z : HomologicalComplex V c} (p : X ⟶ Y)
    (hp : ∀ k l, Function.Bijective (fun f : Y.X k ⟶ Z.X l => p.f k ≫ f)) :
    Function.Bijective (fun φ : (HomotopyCategory.quotient V c).obj Y ⟶
        (HomotopyCategory.quotient V c).obj Z => (HomotopyCategory.quotient V c).map p ≫ φ) := by
  refine ⟨fun φ₁ φ₂ h => ?_, fun ψ => ?_⟩
  · obtain ⟨a, rfl⟩ := (quotient V c).map_surjective φ₁
    obtain ⟨b, rfl⟩ := (quotient V c).map_surjective φ₂
    simp only [← Functor.map_comp] at h
    exact eq_of_homotopy _ _ (Homotopy.ofBijectiveComp p hp (homotopyOfEq _ _ h))
  · obtain ⟨g, rfl⟩ := (quotient V c).map_surjective ψ
    exact ⟨(quotient V c).map (descOfBijectiveComp p hp g), by
      simp only [← Functor.map_comp, comp_descOfBijectiveComp]⟩

end HomotopyCategory
