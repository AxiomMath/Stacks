module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.NatIso

/-!
# A comparison compatible with composition is compatible with identities

Let `P : D ⥤ D` and `Q : E ⥤ E` be endofunctors identified with the identity by `εP`, `εQ`, and
let `R : E ⥤ D`. Suppose `c M : P (R M) ≅ R (Q M)` is natural in `M` and satisfies the
composition law of a comparison of pseudofunctors at two identities,

`P (c M) ≫ c (Q M) ≫ R (εQ (Q M)) = P (εP (R M)) ≫ c M`,

where `εQ (Q M) = Q (εQ M)` (the two unit laws of the pseudofunctor `Q` at an identity). Then
`c M ≫ R (εQ M) = εP (R M)`: the comparison at the identity is the canonical one.

This is the usual "an idempotent isomorphism is an identity" argument. It is how the comparison
of the Zariski restriction of a module on a representable algebraic space with inverse images
(`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`), whose composition law is known,
is shown to be compatible with identities.

## Main results

* `CategoryTheory.comparison_hom_comp_map_eq_of_comp_law`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- **A comparison satisfying the composition law at identities is the canonical one.** -/
theorem comparison_hom_comp_map_eq_of_comp_law (P : D ⥤ D) (Q : E ⥤ E) (R : E ⥤ D)
    (εP : P ≅ 𝟭 D) (εQ : Q ≅ 𝟭 E) (c : ∀ M : E, P.obj (R.obj M) ≅ R.obj (Q.obj M))
    (hc : ∀ {M N : E} (k : M ⟶ N), P.map (R.map k) ≫ (c N).hom = (c M).hom ≫ R.map (Q.map k))
    (hQ : ∀ M : E, εQ.hom.app (Q.obj M) = Q.map (εQ.hom.app M))
    (hlaw : ∀ M : E, P.map (c M).hom ≫ (c (Q.obj M)).hom ≫ R.map (εQ.hom.app (Q.obj M)) =
      P.map (εP.hom.app (R.obj M)) ≫ (c M).hom)
    (M : E) : (c M).hom ≫ R.map (εQ.hom.app M) = εP.hom.app (R.obj M) := by
  have hP : P.Faithful := Functor.Faithful.of_iso εP.symm
  apply P.map_injective
  have h1 := hlaw M
  rw [hQ M, ← hc (εQ.hom.app M), ← Category.assoc, ← P.map_comp] at h1
  rw [P.map_comp]
  exact (cancel_mono (c M).hom).1 (by rw [Category.assoc, ← P.map_comp_assoc]; exact h1)

end CategoryTheory

end
