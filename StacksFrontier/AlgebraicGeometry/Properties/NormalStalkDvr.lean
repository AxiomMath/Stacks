module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE

/-!
# The local rings of a normal scheme at codimension-one points

On a locally Noetherian normal scheme the local ring at a point of codimension one is a discrete
valuation ring: it is a Noetherian local normal domain of Krull dimension one, which is one of the
equivalent characterisations of a discrete valuation ring.

Irreducibility of the ambient scheme plays no role, because normality already makes every local
ring a domain. This matters for schemes that are normal without being integral, such as the
normalization of a reducible scheme.
-/

public noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The local ring of a locally Noetherian normal scheme at a point of codimension one is a
discrete valuation ring.** -/
theorem isDiscreteValuationRing_stalk_of_coheight_eq_one {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]; rfl
  have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal x, hdim⟩
  have h1 : ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
    ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
  exact h1.choose_spec

end AlgebraicGeometry
