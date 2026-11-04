module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Additive functors preserve quasi-isomorphisms between bounded below complexes of injectives

A quasi-isomorphism between bounded below complexes of injective objects of an abelian category
is a homotopy equivalence (both complexes are K-injective), and every additive functor preserves
homotopy equivalences. So every additive functor, exact or not, carries such a
quasi-isomorphism to a quasi-isomorphism.

This is how, in Step 7 of the proof of [Stacks, Tag 03UG], the non-exact functor
`Hom_R(N, -)` over the self-injective ring `R = A[G]` is applied to resolutions: on stalks, a
resolution of a sheaf with injective stalks by an injective sheaf is a quasi-isomorphism between
bounded below complexes of injective modules.

## Main results

* `CochainComplex.quasiIso_map_of_injective`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Preadditive D]
  [CategoryWithHomology D]

attribute [local instance] HasDerivedCategory.standard in
/-- **An additive functor carries a quasi-isomorphism between bounded below complexes of
injectives to a quasi-isomorphism.** -/
theorem quasiIso_map_of_injective (H : C ⥤ D) [H.Additive] {K L : CochainComplex C ℤ}
    (φ : K ⟶ L) [QuasiIso φ] (d : ℤ) [K.IsStrictlyGE d] [L.IsStrictlyGE d]
    [∀ n, Injective (K.X n)] [∀ n, Injective (L.X n)] :
    QuasiIso ((H.mapHomologicalComplex _).map φ) := by
  have := isKInjective_of_injective K d
  have := isKInjective_of_injective L d
  obtain ⟨e, he⟩ := (IsKInjective.quasiIso_iff φ).1 inferInstance
  rw [← he]
  exact homotopyEquivalences_le_quasiIso D _ _ ⟨H.mapHomotopyEquiv e, rfl⟩

end CochainComplex

end
