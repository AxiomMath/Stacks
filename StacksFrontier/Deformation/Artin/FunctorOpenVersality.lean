module

public import StacksFrontier.Deformation.Artin.FunctorTangentSpace
public import StacksFrontier.Deformation.Artin.Versality.Openness

/-!
# Openness of versality for a set-valued functor on the locally Noetherian site

Let `S` be a locally Noetherian scheme and `F` a set-valued functor on the category of locally
Noetherian schemes over `S` (Stacks 0GE4). Artin's axiom `[5]` for such a functor (Section 0GE6,
read off Section 07XZ) is *openness of versality*: given a scheme `U` locally of finite type over
`S`, an element `x ∈ F(U)` and a finite type point `u₀ ∈ U` at which `x` is versal, there is an
open neighbourhood of `u₀` in `U` at every finite type point of which `x` is versal.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver.HasOpenVersality`: axiom `[5]`.

## Implementation notes

The category over schemes attached to `F` is
`AlgebraicGeometry.LocallyNoetherianOver.elementsToOver`, the opposite of the category of
elements of `F` over schemes over `S`, and versality is `Deformation.Artin.IsVersalAt` (Stacks
07XF) for it. The predicate is the condition of `Deformation.Artin.IsOpenVersality` (Stacks 07XQ)
for that category, written out: `Deformation.Artin.IsOpenVersality` also takes a proof that the
category is fibred in groupoids over schemes over `S`, which the opposite of the category of
elements of a functor on locally Noetherian schemes is not (a scheme over a locally Noetherian
scheme need not be locally Noetherian), and which the condition itself never uses.

## References

* [Stacks Project, Tag 07XQ](https://stacks.math.columbia.edu/tag/07XQ)
* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianOver

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Artin's axiom `[5]`**, openness of versality, for a set-valued functor `F` on the locally
Noetherian site of `S`: for every scheme `U` locally of finite type over `S`, every element
`x ∈ F(U)` and every finite type point `u₀ ∈ U` at which `x` is versal, there is an open
neighbourhood `V ⊆ U` of `u₀` such that `x` is versal at every finite type point of `V`. -/
def HasOpenVersality (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (U : Over S), LocallyOfFiniteType U.hom →
    ∀ (x : F.Elementsᵒᵖ) (hx : (elementsToOver B S hS F).obj x = U) (u₀ : U.left),
      IsFiniteTypePoint u₀ →
      Deformation.Artin.IsVersalAt U (elementsToOver B S hS F) u₀ x hx →
      ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
        ∀ (u : U.left), u ∈ V.1 →
          IsFiniteTypePoint u →
          Deformation.Artin.IsVersalAt U (elementsToOver B S hS F) u x hx

end AlgebraicGeometry.LocallyNoetherianOver

end
