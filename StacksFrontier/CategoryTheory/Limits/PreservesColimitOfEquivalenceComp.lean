module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Preservation of one colimit along an equivalence of index categories

If `F` preserves the colimit of `e.functor ⋙ K` for an equivalence `e : J ≌ J'`, then it preserves
the colimit of `K`. This is the single-diagram form of Mathlib's
`CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`.

## Main results

* `CategoryTheory.Limits.preservesColimit_of_equivalence_comp`: preservation of the colimit of `K`
  from that of `e.functor ⋙ K`.
* `CategoryTheory.Limits.preservesColimit_discrete_of_equiv`: the case of a family indexed by a
  type, reindexed along an equivalence of types.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] {J J' : Type*} [Category J] [Category J']

/-- **Preservation of a single colimit along an equivalence of index categories**: if `F` preserves
the colimit of `e.functor ⋙ K` for an equivalence `e : J ≌ J'`, it preserves the colimit of `K`. -/
lemma preservesColimit_of_equivalence_comp (e : J ≌ J') (K : J' ⥤ C) (F : C ⥤ D)
    [PreservesColimit (e.functor ⋙ K) F] : PreservesColimit K F where
  preserves {c} t := ⟨by
    let equ := e.invFunIdAssoc (K ⋙ F)
    have := (isColimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
    apply ((IsColimit.precomposeInvEquiv equ _).symm this).ofIsoColimit
    refine Cocone.ext (Iso.refl _) fun j => ?_
    simp [equ, ← Functor.map_comp]⟩

/-- **Preservation of the direct sum of a family along a reindexing**: if `F` preserves the direct
sum of `Z ∘ σ` for an equivalence of types `σ : I ≃ I'`, it preserves that of `Z`. -/
lemma preservesColimit_discrete_of_equiv {I I' : Type*} (σ : I ≃ I') (Z : I' → C) (F : C ⥤ D)
    [PreservesColimit (Discrete.functor (Z ∘ σ)) F] : PreservesColimit (Discrete.functor Z) F :=
  have : PreservesColimit ((Discrete.equivalence σ).functor ⋙ Discrete.functor Z) F :=
    preservesColimit_of_iso_diagram F (K₁ := Discrete.functor (Z ∘ σ))
      (Discrete.natIso fun _ => Iso.refl _)
  preservesColimit_of_equivalence_comp (Discrete.equivalence σ) (Discrete.functor Z) F

end CategoryTheory.Limits
