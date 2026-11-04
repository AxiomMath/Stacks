module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# The two composition isomorphisms for inverse image of abelian étale sheaves agree

`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso` is built as a comparison of two left adjoints
of the composite direct image (`CategoryTheory.Adjunction.leftAdjointUniq`), and
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'` as the conjugate of the named-composite
direct image comparison (`CategoryTheory.Adjunction.leftAdjointCompIso`). Both are the conjugate
of the composition isomorphism of direct images, so they coincide.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso_eq` — the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.EtaleCohomology

variable {X Y Z : AlgebraicGeometry.Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- Conjugating the identity from an adjunction with its right adjoint replaced along an
isomorphism, to the original adjunction, gives the inverse of that isomorphism. -/
theorem conjugateEquiv_ofNatIsoRight_id {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D}
    {R R' : D ⥤ C} (adj : L ⊣ R) (e : R ≅ R') :
    conjugateEquiv (adj.ofNatIsoRight e) adj (𝟙 L) = e.inv := by
  ext d
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight]

/-- **The two composition isomorphisms for inverse image agree.** -/
theorem smallEtalePullbackAbCompIso_eq :
    smallEtalePullbackAbCompIso a b = smallEtalePullbackAbCompIso' a b (a ≫ b) rfl := by
  rw [smallEtalePullbackAbCompIso'_rfl]
  apply Iso.ext
  refine (Iso.inv_eq_inv (smallEtalePullbackAbCompIso a b)
    (smallEtalePullbackAbTowerCompIso a b)).mp ?_
  apply (conjugateEquiv ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))
    (smallEtaleAdjunctionAb (a ≫ b))).injective
  let adj' := (smallEtaleAdjunctionAb (a ≫ b)).ofNatIsoRight
    (smallEtalePushforwardAbCompIso a b).symm
  have h := conjugateEquiv_comp ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a)) adj'
    (smallEtaleAdjunctionAb (a ≫ b))
    ((conjugateEquiv ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a)) adj').symm
      (𝟙 _)) (𝟙 _)
  rw [conjugateEquiv_ofNatIsoRight_id, Equiv.apply_symm_apply, Category.id_comp,
    Category.id_comp] at h
  refine (Eq.trans ?_ h.symm).trans ?_
  · rfl
  · simp [smallEtalePullbackAbTowerCompIso]

end Stacks.EtaleCohomology

end
