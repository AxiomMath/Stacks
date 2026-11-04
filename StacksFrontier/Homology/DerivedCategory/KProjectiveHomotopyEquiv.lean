module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Isomorphic K-projective complexes are homotopy equivalent

Two K-projective cochain complexes which become isomorphic in the derived category are
homotopy equivalent: morphisms in the derived category out of a K-projective complex are
morphisms in the homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace CochainComplex.IsKProjective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **An isomorphism in `D(C)` between K-projective complexes is a homotopy equivalence.** -/
public theorem nonempty_homotopyEquiv_of_iso {K L : CochainComplex C ℤ} [K.IsKProjective]
    [L.IsKProjective] (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    Nonempty (HomotopyEquiv K L) := by
  let e' : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj L) :=
    (DerivedCategory.quotientCompQhIso C).app K ≪≫ e ≪≫
      ((DerivedCategory.quotientCompQhIso C).app L).symm
  obtain ⟨f, hf⟩ := (Qh_map_bijective K ((HomotopyCategory.quotient _ _).obj L)).2 e'.hom
  obtain ⟨g, hg⟩ := (Qh_map_bijective L ((HomotopyCategory.quotient _ _).obj K)).2 e'.inv
  have h1 : f ≫ g = 𝟙 _ := (Qh_map_bijective K _).1 (by
    rw [Functor.map_comp, hf, hg, Iso.hom_inv_id, CategoryTheory.Functor.map_id])
  have h2 : g ≫ f = 𝟙 _ := (Qh_map_bijective L _).1 (by
    rw [Functor.map_comp, hf, hg, Iso.inv_hom_id, CategoryTheory.Functor.map_id])
  exact ⟨HomotopyCategory.homotopyEquivOfIso ⟨f, g, h1, h2⟩⟩

end CochainComplex.IsKProjective

end
