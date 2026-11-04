module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.Deformation.GroupoidQuotient.MoritaDimension
public import StacksFrontier.Deformation.GroupoidQuotient.Realization
public import StacksFrontier.Deformation.Presentation

/-!
# `2 dim A - dim B` is an invariant of the presented category

If two smooth groupoids in functors on `𝒞_Λ`, prorepresented by `(A, B)` and `(A', B')`, present
the same category cofibered in groupoids over `𝒞_Λ`, then `2 dim A - dim B = 2 dim A' - dim B'`.
This is the invariance of the right-hand side of Stacks 0DSB under the choice of the cogroupoid
of Remark 0DR3.

## Main results

* `Deformation.GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_presentations`.

## Implementation notes

The two presentations compose to an equivalence over `𝒞_Λ` between the two quotients
(`StacksRepresentableCFG.EquivalenceOver.trans`), which is realized up to isomorphism by a
morphism `F` of groupoids in functors (`Deformation.GroupoidInFunctors.exists_hom_of_morphismOver`,
using prorepresentability of the source and smoothness of the target). The functor `F` induces on
quotients is then full, faithful and essentially surjective, being isomorphic to an equivalence,
and `Deformation.GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_quotientMap` applies.
-/

@[expose] public section

open CategoryTheory

universe u v w uF vF

namespace Deformation

namespace GroupoidInFunctors

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The invariant of a presented category.** Two smooth groupoids in functors on `𝒞_Λ`,
prorepresented by `(A, B)` and `(A', B')` and presenting the same category cofibered in groupoids,
have `2 dim A - dim B = 2 dim A' - dim B'`. -/
public theorem twoMul_ringKrullDim_sub_eq_of_presentations
    (G H : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hG : GroupoidInFunctors.IsSmooth G) (hH : GroupoidInFunctors.IsSmooth H)
    {A B A' B' : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    (eA : G.objects ≅ restrictedCoyoneda A) (eB : G.arrows ≅ restrictedCoyoneda B)
    (eA' : H.objects ≅ restrictedCoyoneda A') (eB' : H.arrows ≅ restrictedCoyoneda B')
    {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (PG : Presentation G p) (PH : Presentation H p) :
    ∃ a b a' b' : ℕ, ringKrullDim A = a ∧ ringKrullDim B = b ∧ ringKrullDim A' = a' ∧
      ringKrullDim B' = b' ∧ 2 * a + b' = 2 * a' + b := by
  have hGpro : GroupoidInFunctors.IsProrepresentable G :=
    (isProrepresentable_iff_objects_arrows G).2 ⟨⟨A, ⟨eA⟩⟩, ⟨B, ⟨eB⟩⟩⟩
  let Φ := PG.trans PH.symm
  obtain ⟨Fm, ⟨i⟩⟩ := exists_hom_of_morphismOver G H hGpro hH Φ.hom
  have : Φ.hom.functor.IsEquivalence := Φ.isEquivalence_hom_functor
  have : (quotientMap Fm).IsEquivalence := Functor.isEquivalence_of_iso i.symm
  exact twoMul_ringKrullDim_sub_eq_of_quotientMap G H hG hH eA eB eA' eB' Fm

end GroupoidInFunctors

end Deformation

end
