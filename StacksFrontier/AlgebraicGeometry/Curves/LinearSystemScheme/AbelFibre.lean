module

public import StacksFrontier.AlgebraicGeometry.Curves.ClassicalLinearSystem
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints

/-!
# The fibre of the Abel map over the point of `𝒪_X(D)`

Let `X` be a scheme over a field `k`, let `D ⊆ X` be an effective Cartier divisor and let `d` be
a natural number. For a `k`-scheme `T` write `X_T = X ×_k T`. The Abel map
`γ_d : Hilb^d_{X/k} → Pic_{X/k}` sends a degree-`d` family `Z ⊆ X_T` to the class of `𝒪_{X_T}(Z)`,
and the point of the Picard functor corresponding to `𝒪_X(D)` is the class of its pullback
`pr_X^* 𝒪_X(D)`. A section of the Picard functor is a section of the sheafification of
`T ↦ Pic(X_T)`, so two classes agree when they agree locally on `T`; this file uses the Zariski
topology. The *fibre of `γ_d` over the point of `𝒪_X(D)`* is therefore the subfunctor of the
Hilbert functor of points whose `T`-points are the degree-`d` families `Z ⊆ X_T` for which
`𝒪_{X_T}(Z)` is, locally on `T`, isomorphic to `pr_X^* 𝒪_X(D)`.

## Main definitions

* `Stacks.LinearSystemScheme.curveOver`: `X` as an object of the category of `k`-schemes.
* `Stacks.LinearSystemScheme.IsLocallyLinearlyEquivalent`: the condition on a family `Z ⊆ X_T`
  that `𝒪_{X_T}(Z)` and `pr_X^* 𝒪_X(D)` are isomorphic on the preimage of every member of an
  open cover of `T`.
* `Stacks.LinearSystemScheme.abelFibre`: the `T`-points of the fibre of `γ_d` over the point of
  `𝒪_X(D)`.

## Implementation notes

Affine opens of `T` form a basis, so locality may be tested on them. The restriction of the
family to an open `V ⊆ T` is the pullback along the base change `X_V ⟶ X_T` of the inclusion,
which is `Stacks.Hilbert.familyBaseChangeMap`. Families are the degree-`d` Hilbert families of
`Stacks.Hilbert.HilbertFamily`, closed subschemes of `X_T` finite locally free of rank `d`
over `T`.

## References

* [Stacks Project, Tag 0CCT](https://stacks.math.columbia.edu/tag/0CCT)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.LinearSystemScheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `X`, as an object of the category of `k`-schemes. -/
abbrev curveOver : Over (Spec (.of k)) := Over.mk f

/-- The `k`-scheme `U`, for an open immersion `j : U ⟶ T` into a `k`-scheme `T`. -/
abbrev restrictOver {T : Over (Spec (.of k))} {U : Scheme.{u}} (j : U ⟶ T.left) :
    Over (Spec (.of k)) :=
  Over.mk (j ≫ T.hom)

/-- The morphism of `k`-schemes `U ⟶ T` underlying `j`. -/
abbrev restrictHom {T : Over (Spec (.of k))} {U : Scheme.{u}} (j : U ⟶ T.left) :
    restrictOver j ⟶ T :=
  Over.homMk j

/-- **Local linear equivalence with `pr_X^* 𝒪_X(D)`.** A closed subscheme `Z ⊆ X_T` has this
property when every point of `T` lies in an affine open `V ⊆ T` over which `𝒪_{X_T}(Z)`
restricted to `X_V` is isomorphic to the pullback of `𝒪_X(D)` along the projection `X_V ⟶ X`. -/
def IsLocallyLinearlyEquivalent (D : X.IdealSheafData) {T : Over (Spec (.of k))}
    (Z : ((Over.pullback T.hom).obj (curveOver f)).left.IdealSheafData) : Prop :=
  ∀ t : T.left, ∃ V : T.left.Opens, IsAffineOpen V ∧ t ∈ V ∧
    Nonempty ((Scheme.Modules.pullback
        (Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι))).obj
          (Stacks.Divisors.modulesInvertibleSheaf Z) ≅
      (Scheme.Modules.pullback (pullback.fst f (V.ι ≫ T.hom))).obj
          (Stacks.Divisors.modulesInvertibleSheaf D))

/-- **The fibre of the Abel map `γ_d` over the point of `𝒪_X(D)`, at a `k`-scheme `T`**: the
degree-`d` families `Z ⊆ X_T` whose invertible sheaf `𝒪_{X_T}(Z)` is, locally on `T`, the pullback
of `𝒪_X(D)`. -/
def abelFibre (D : X.IdealSheafData) (d : ℕ) (T : Over (Spec (.of k))) :
    Set (Stacks.Hilbert.HilbertFamily (curveOver f) T d) :=
  {Z | IsLocallyLinearlyEquivalent f D Z.ideal}

end Stacks.LinearSystemScheme

end
