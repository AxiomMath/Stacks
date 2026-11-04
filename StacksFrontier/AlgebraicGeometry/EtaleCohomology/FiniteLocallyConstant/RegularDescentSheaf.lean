module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent

/-!
# The sheaf `f_* A` of a Galois covering as a sheaf of `A[H]`-modules

Let `f : V ⟶ X` be a Galois covering with group `H` (`AlgebraicGeometry.EtaleGaloisCovering`)
and `A` a commutative ring. The descent sheaf of the group ring `A[H]`, on which `H` acts by
right multiplication by inverses and `A[H]` by left multiplication, is a sheaf of
`A[H]`-modules: the right regular action is `A[H]`-linear for the left module structure. Its
sections over an étale `W ⟶ X` are the locally constant maps `s : W ×_X V → A[H]` with
`s(h · z) = s(z) h⁻¹`, and `s ↦ (z ↦ s(z)(1))` identifies them with all locally constant maps
`W ×_X V → A`, i.e. with the sections of `f_* A`.

This is the sheaf `f_* A` with its deck transformation action, viewed as a sheaf of
`A[H]`-modules, whose compactly supported cohomology is the perfect complex of `A[H]`-modules
in Steps 7 and 8 of the proof of [Stacks, Tag 03UG].

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.rightRegularRep`: the right regular action of `H` on
  `A[H]`, by `A[H]`-linear maps.
* `AlgebraicGeometry.EtaleGaloisCovering.regularDescentSheaf`: the descent sheaf of `A[H]`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.EtaleGaloisCovering

variable (A : Type) [CommRing A] (H : Type) [Group H]

/-- **The right regular action** `h ↦ (y ↦ y h⁻¹)` of `H` on the group ring `A[H]`, by maps
that are linear for the left module structure of `A[H]` over itself. -/
def rightRegularRep : H →* Module.End (MonoidAlgebra A H) (MonoidAlgebra A H) where
  toFun h := LinearMap.mulRight (MonoidAlgebra A H) (MonoidAlgebra.single h⁻¹ (1 : A))
  map_one' := by
    ext y
    simp [MonoidAlgebra.one_def]
  map_mul' h h' := by
    ext y
    simp [MonoidAlgebra.single_mul_single, mul_inv_rev]

/-- The right regular action of `h` sends `y ∈ A[H]` to `y h⁻¹`. -/
lemma rightRegularRep_apply (h : H) (y : MonoidAlgebra A H) :
    rightRegularRep A H h y = y * MonoidAlgebra.single h⁻¹ 1 := rfl

/-- The right regular action on `A[H]`, lifted to the universe `u + 1` of the sections of sheaves
on the small étale site of a scheme in universe `u`. -/
def rightRegularRepULift :
    H →* Module.End (MonoidAlgebra A H) (ULift.{u + 1} (MonoidAlgebra A H)) where
  toFun h := ULift.moduleEquiv.symm.toLinearMap ∘ₗ rightRegularRep A H h ∘ₗ
    ULift.moduleEquiv.toLinearMap
  map_one' := by
    ext y
    simp [map_one]
  map_mul' h h' := by
    ext y
    simp [map_mul]

variable {X : Scheme.{u}} {A H} (G : EtaleGaloisCovering X H)

/-- **The sheaf `f_* A` of a Galois covering, as a sheaf of `A[H]`-modules**: the descent sheaf
of `A[H]` with the right regular action. -/
abbrev regularDescentSheaf :
    Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} (MonoidAlgebra A H)) :=
  G.descentSheaf.{u, 0, 0, u + 1} (MonoidAlgebra A H) (ULift.{u + 1} (MonoidAlgebra A H))
    (rightRegularRepULift.{u} A H)

end AlgebraicGeometry.EtaleGaloisCovering

end
