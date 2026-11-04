module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemExistence

/-!
# Two-out-of-three for Deligne systems on a Noetherian scheme

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` be an
inverse system of distinguished triangles in `D^b_{Coh}(𝒪_X)`. [Stacks, Tag 0G4Q] says that if
`(K_n)` and `(M_n)` are pro-isomorphic to Deligne systems, then so is `(L_n)`.

It is the two-out-of-three `CategoryTheory.DeligneSystemValues.proIsoDeligne_π₂`, for a
triangulated functor with a Deligne-system assignment, at the restriction
`D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)` and the assignment `AlgebraicGeometry.DeligneSystem.values`,
which sends `K` to a Deligne system with value `K` (Stacks 0G4L (2)) and satisfies Stacks 0G2H.

## Main results

* `AlgebraicGeometry.DeligneSystem.proIsoDeligneSystem_π₂`: if the first and third vertices of an
  inverse system of distinguished triangles are pro-isomorphic to Deligne systems, then so is the
  second.

## References

* [Stacks Project, Tag 0G4Q](https://stacks.math.columbia.edu/tag/0G4Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DeligneSystem

variable {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]

/-- Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let
`K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` be an inverse system of distinguished triangles in `D^b_{Coh}(𝒪_X)`. If
`(K_n)` and `(M_n)` are pro-isomorphic to Deligne systems, then so is `(L_n)`. -/
@[stacks 0G4Q]
public theorem proIsoDeligneSystem_π₂ (T : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X))
    (hT : ∀ n, T.obj n ∈ distTriang (BoundedCoherentDerived X))
    (hK : ProIsoDeligneSystem j (T ⋙ Triangle.π₁))
    (hM : ProIsoDeligneSystem j (T ⋙ Triangle.π₃)) :
    ProIsoDeligneSystem j (T ⋙ Triangle.π₂) := by
  rw [proIsoDeligneSystem_iff] at hK hM ⊢
  exact (values j).proIsoDeligne_π₂ T hT hK hM

end AlgebraicGeometry.DeligneSystem

end
