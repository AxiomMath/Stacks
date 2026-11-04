module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Realizing an isomorphism of the derived category by a quasi-isomorphism

A bounded above complex of projectives is K-projective, so the localization functor
`DerivedCategory.Qh` is bijective on morphisms out of its image in the homotopy category, and the
homotopy category is a quotient of the category of complexes. Hence every isomorphism
`Q(P) ≅ Q(L)` of the derived category out of such a complex `P` is `Q` applied to an actual
quasi-isomorphism of complexes `P ⟶ L`.

## Main results

* `CochainComplex.exists_quasiIso_of_derived_iso`: an isomorphism `Q(P) ≅ Q(L)`, with `P` bounded
  above with projective terms, comes from a quasi-isomorphism `P ⟶ L`.
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

/-- A morphism out of a bounded above complex of projectives is determined in the derived
category by a morphism of complexes: such a complex is K-projective, so the localization is
bijective on morphisms out of it, and the homotopy category is a quotient of the category of
complexes. Hence an isomorphism `Q(P) ≅ Q(L)` is induced by a quasi-isomorphism `P ⟶ L`. -/
public lemma exists_quasiIso_of_derived_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P L : CochainComplex C ℤ) (d : ℤ) [P.IsStrictlyLE d] [∀ i, Projective (P.X i)]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj L) :
    ∃ π : P ⟶ L, QuasiIso π := by
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  let ι := DerivedCategory.quotientCompQhIso C
  let e' : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj P ≅
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj L :=
    ι.app P ≪≫ e ≪≫ (ι.app L).symm
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).surjective e'.hom
  obtain ⟨π, hπ⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
  refine ⟨π, ?_⟩
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  refine (NatIso.isIso_map_iff ι π).1 ?_
  rw [show (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map π =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map π) from rfl,
    hπ, hf]
  infer_instance

end CochainComplex

end
