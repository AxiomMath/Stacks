module

public import StacksFrontier.Deformation.Smooth.FullVertical
public import StacksFrontier.Deformation.Smooth.Unobstructed

/-!
# Unobstructedness is invariant under equivalence over `𝒞_Λ`

Two categories over `𝒞_Λ` that are equivalent over `𝒞_Λ` are simultaneously unobstructed:
the structure functor of the source is the forward
equivalence followed by the structure functor of the target, the forward equivalence is smooth,
and it is essentially surjective.

## Main results

* `Deformation.isSmooth_baseProjection_iff_of_equivalenceOver`.
-/

@[expose] public section

open CategoryTheory

universe u v w uF vF uG vG

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]

/-- **Unobstructedness is invariant under equivalence over `𝒞_Λ`.** If `p` and `q` are
equivalent over `𝒞_Λ`, then `p` is unobstructed exactly when
`q` is. -/
theorem isSmooth_baseProjection_iff_of_equivalenceOver
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    IsSmooth (baseProjection p) ↔ IsSmooth (baseProjection q) := by
  let φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q) :=
    ⟨e.hom.functor, e.hom.w⟩
  have hcomp : BasedFunctor.comp φ (baseProjection q) = baseProjection p := by
    have h : (BasedFunctor.comp φ (baseProjection q)).toFunctor = (baseProjection p).toFunctor :=
      e.hom.w
    revert h
    generalize BasedFunctor.comp φ (baseProjection q) = a
    generalize baseProjection p = b
    rcases a with ⟨_, _⟩
    rcases b with ⟨_, _⟩
    rintro rfl
    rfl
  have : e.hom.functor.IsEquivalence := e.isEquivalence_hom_functor
  have : φ.toFunctor.EssSurj := inferInstanceAs e.hom.functor.EssSurj
  rw [← hcomp]
  exact ⟨fun h => isSmooth_of_essSurj_comp φ _ h,
    fun h => isSmooth_comp _ _ (isSmooth_of_equivalenceOver e φ rfl) h⟩

end Deformation

end
