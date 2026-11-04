module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothRigFlat

/-!
# Rig-smooth morphisms of formal algebraic spaces are rig-flat

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. **Stacks 0GH3** says that if `f` is
rig-smooth (Stacks 0GCP) then `f` is rig-flat (Stacks 0GGX).

## Main results

* `AlgebraicGeometry.FormalSpace.isRigFlat_of_isRigSmooth`: **Stacks 0GH3**.

## Implementation notes

The proof in the source is "immediate from Lemma 0GH1 and the definitions": rig-smoothness and
rig-flatness of `f` are both conditions on the continuous homomorphism of adic Noetherian
topological rings induced on every affine étale chart diagram over `f`, so the geometric
implication is the chartwise instance of the ring-theoretic one, the rig-flatness conclusion of
Stacks 0GH1 (`Rig.isRigFlat_and_exists_isRegular_of_isRigSmooth`).

The locally Noetherian hypotheses on `X` and `Y` are carried by the class of rings over which
the chart conditions quantify, exactly as for Stacks 0GCP and Stacks 0GGX.

## References

* [Stacks Project, Tag 0GH3](https://stacks.math.columbia.edu/tag/0GH3)
* [Stacks Project, Tag 0GH1](https://stacks.math.columbia.edu/tag/0GH1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0GH3.** A rig-smooth morphism of locally Noetherian formal algebraic spaces over
`S` is rig-flat. -/
@[stacks 0GH3]
theorem isRigFlat_of_isRigSmooth (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hf : IsRigSmooth B S hS f) : IsRigFlat B S hS f := by
  intro U V hU hV a b t ha hb haet hbet hcomm A C _ _ _ _ _ _ _ _ _ _ hAadic hCadic hA D E
    eU eV g hg
  exact (Rig.isRigFlat_and_exists_isRegular_of_isRigSmooth hAadic hCadic g.toRingHom g.continuous
    (hf U V hU hV a b t ha hb haet hbet hcomm A C hAadic hCadic hA D E eU eV g hg)).1

end AlgebraicGeometry.FormalSpace

end
