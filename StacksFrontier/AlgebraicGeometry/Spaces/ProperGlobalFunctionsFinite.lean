module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.Finiteness

/-!
# Global functions of a proper algebraic space over a field are finite dimensional

Let `k` be a field and `X` a proper algebraic space over `k`.  This file proves, with nothing
carried, the first three parts of Stacks 0DMY: `A = H⁰(X, 𝒪_X)` is a finite dimensional
`k`-algebra; it is the product, over the finitely many connected components of `|X|`, of Artinian
local `k`-algebras; and when `X` is reduced each factor is a field finite over `k`.

Part (1) is the case of a field of
`AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper`, which shows that the global
functions of an algebraic space proper over any Noetherian ring `A` form a finite `A`-module
(Stacks 08AS in degree zero for the structure sheaf); it is registered for Tag 0DMY below.

The two remaining parts are the corresponding statements of
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions`, there conditional on Stacks 08AS,
now with the finiteness supplied.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper`: **Stacks 0DMY, part (1)**,
  over any Noetherian base ring.
* `AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization_of_isProper_of_field`:
  **Stacks 0DMY, part (2)**, together with the existing
  `AlgebraicGeometry.Space.finite_connectedComponents_points_of_isProper` (finitely many factors).
* `AlgebraicGeometry.Space.exists_componentwiseArtinianFactorization_isField_finite_of_isProper`:
  **Stacks 0DMY, part (3)**, with its finiteness half
  `AlgebraicGeometry.Space.moduleFinite_componentFunctions_of_isProper`.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Tag 0DMY -/

-- Stacks 0DMY, part (1): for `X` proper over a field `k`, `A = H⁰(X, 𝒪_X)` is a finite
-- dimensional `k`-algebra.  The declaration proves it over any Noetherian ring, a field being
-- Noetherian.
add_to_stacks 0DMY "part (1): A is finite over the base, here any Noetherian ring"
  AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper

section Field

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- Part (1) of Tag 0DMY for a proper algebraic space over a field, with the structure morphism
given as an arbitrary morphism `f` to the terminal object. -/
private theorem moduleFinite_globalFunctions_of_isProper_field
    (hf : IsProper B (Spec (.of k)) hS f) :
    Module.Finite k (globalFunctions B (Spec (.of k)) hS X) :=
  moduleFinite_globalFunctions_of_isProper k ⟨X, hX⟩
    (by rwa [(isTerminal_yoneda_obj_base B _ hS).hom_ext f
        ((isTerminal_yoneda_obj_base B _ hS).from X)] at hf)

/-- The ring of global regular functions of a proper algebraic space over a field is Artinian:
it is a finite dimensional `k`-algebra by part (1) of Tag 0DMY,
`AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper` (the structure morphism `f`
being the morphism to the terminal object), hence Artinian as a module over `k`, hence over
itself. -/
theorem isArtinianRing_globalFunctions_of_isProper_of_field
    (hf : IsProper B (Spec (.of k)) hS f) :
    IsArtinianRing (globalFunctions B (Spec (.of k)) hS X) :=
  have := moduleFinite_globalFunctions_of_isProper_field k B hS X hX f hf
  IsArtinianRing.of_finite k (globalFunctions B (Spec (.of k)) hS X)

/-- **Stacks 0DMY, part (2).**  The global regular functions `A` of a proper algebraic space over
a field `k` split as the product, over the connected components of the point space `|X|`, of the
rings of functions on the étale charts lying in each component, each factor an Artinian local
`k`-algebra, the splitting being simultaneous restriction to the components; there are finitely
many components (`AlgebraicGeometry.Space.finite_connectedComponents_points_of_isProper`), so the
product is finite.

This is
`AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace`
with its remaining hypothesis, artinianness of `A`, supplied by part (1):
`AlgebraicGeometry.Space.isArtinianRing_globalFunctions_of_isProper_of_field`.
Quasi-compactness and local Noetherianity of `X` come from properness (Tags 04ZL and 04ZK). -/
@[stacks 0DMY "part (2): A is the product, over the connected components of |X|, of Artinian \
local k-algebras, the splitting being restriction to the components"]
theorem nonempty_componentwiseArtinianFactorization_of_isProper_of_field
    (hf : IsProper B (Spec (.of k)) hS f) :
    Nonempty (ComponentwiseArtinianFactorization k B hS X) :=
  nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace k B hS X hX
    (isQuasiCompactSpace_of_isProper_baseObject k B hS X hX f hf)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hS X hX f hf)
    (isArtinianRing_globalFunctions_of_isProper_of_field k B hS X hX f hf)

/-- **Stacks 0DMY, part (3), finiteness of the factors.**  Each factor of a componentwise
factorization of the global regular functions of a proper algebraic space over a field `k` is
finite dimensional over `k` — so that, `X` being reduced, each factor is a field
(`AlgebraicGeometry.Space.isField_componentFunctions`) finite over `k`.

The global functions are finite dimensional by part (1), the factorization makes the product of
the factors `k`-linearly isomorphic to them, and projection onto a factor is a surjective
`k`-linear map. -/
@[stacks 0DMY "part (3): the factors are finite over the base field"]
theorem moduleFinite_componentFunctions_of_isProper (hf : IsProper B (Spec (.of k)) hS f)
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    @Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) _ _
      (@Algebra.toModule k (componentFunctions B (Spec (.of k)) hS X c) _ _
        (fac.factorAlgebra c)) := by
  let (d : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X d) := fac.factorAlgebra d
  have := moduleFinite_globalFunctions_of_isProper_field k B hS X hX f hf
  have : Module.Finite k
      (∀ d : ConnectedComponents (points B (Spec (.of k)) hS X),
        componentFunctions B (Spec (.of k)) hS X d) :=
    Module.Finite.equiv fac.equivalence.toLinearEquiv
  exact Module.Finite.of_surjective (LinearMap.proj c) (LinearMap.proj_surjective c)

/-- **Stacks 0DMY, part (3).**  Let `X` be a reduced proper algebraic space over a field `k`.
Then `A = H⁰(X, 𝒪_X)` is a product of fields, each a finite extension of `k`: there is a
componentwise factorization of `A` (part (2)), and each of its factors is a field
(`AlgebraicGeometry.Space.isField_componentFunctions`, the factor being reduced by Tag 0BGS and
Artinian local) which is finite dimensional over `k`
(`AlgebraicGeometry.Space.moduleFinite_componentFunctions_of_isProper`). -/
@[stacks 0DMY "part (3)"]
theorem exists_componentwiseArtinianFactorization_isField_finite_of_isProper
    (hf : IsProper B (Spec (.of k)) hS f)
    (hred : HasEtaleLocalProperty B (Spec (.of k)) hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)) :
    ∃ fac : ComponentwiseArtinianFactorization k B hS X,
      ∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
        IsField (componentFunctions B (Spec (.of k)) hS X c) ∧
          @Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) _ _
            (@Algebra.toModule k (componentFunctions B (Spec (.of k)) hS X c) _ _
              (fac.factorAlgebra c)) :=
  let fac := (nonempty_componentwiseArtinianFactorization_of_isProper_of_field k B hS X hX f
    hf).some
  ⟨fac, fun c => ⟨isField_componentFunctions k B hS X hX hred fac c,
    moduleFinite_componentFunctions_of_isProper k B hS X hX f hf fac c⟩⟩

end Field

end AlgebraicGeometry.Space

end
