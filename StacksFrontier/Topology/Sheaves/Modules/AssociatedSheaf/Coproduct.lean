module

public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Free

/-!
# Construction (3) commutes with coproducts

Let `(X, 𝒪_X)` be a ringed space and `α : R → Γ(X, 𝒪_X)` a ring homomorphism. Clause (2) of
Stacks 01BH says that the functor `M ↦ ℱ_M` of construction (3) commutes with arbitrary
colimits, and `Stacks.AssociatedSheaf.preservesColimitsOfSize_associatedSheafFunctor` carries
that statement. This file instantiates it at a coproduct:

```
ℱ_{∐ᵢ Mᵢ} ≅ ∐ᵢ ℱ_{Mᵢ}
```

The `ℕ`-indexed case is the one the determinant of a sheaf of modules needs:
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant` is the coproduct over the degrees
of the degreewise annihilators, so comparing it with construction (3) applied to the determinant
line of a module requires moving the coproduct across the construction. The coproduct is left
categorical rather than rewritten as a `DirectSum`, because that is the shape the sheaf-level
determinant is built at.

## Main definitions

* `Stacks.AssociatedSheaf.coproductIso`: `ℱ_{∐ᵢ Mᵢ} ≅ ∐ᵢ ℱ_{Mᵢ}`.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.AssociatedSheaf

universe w v u

variable {X : AlgebraicGeometry.RingedSpace.{u, u}} {R : Type u} [CommRing R]
  (α : R →+* X.presheaf.obj (op ⊤)) {ι : Type w} (N : ι → ModuleCat.{max u v} R)

/-- **The sheaf associated to a coproduct of modules is the coproduct of the associated
sheaves.** Construction (3) is a left adjoint, by clause (4) of Stacks 01BH, so it preserves
every colimit that exists; this is that statement at a coproduct. -/
def coproductIso [HasCoproduct N]
    [HasCoproduct fun i => (associatedSheafFunctor.{u, max u v} X α).obj (N i)] :
    (associatedSheafFunctor.{u, max u v} X α).obj (∐ N) ≅
      ∐ fun i => (associatedSheafFunctor.{u, max u v} X α).obj (N i) :=
  PreservesCoproduct.iso _ N

end Stacks.AssociatedSheaf

end
