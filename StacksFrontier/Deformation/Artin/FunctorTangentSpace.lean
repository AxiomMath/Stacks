module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingNoetherian
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.TangentSpace.FiniteDimensional

/-!
# Tangent spaces of a set-valued functor on the locally Noetherian site

Let `S` be a locally Noetherian scheme and `F` a set-valued functor on the category of locally
Noetherian schemes over `S` (Stacks 0GE4). Artin's axiom `[3]` for such a functor (Section 0GE6,
read off Section 07XZ) asks that the tangent spaces `T𝓕_{F,k,x₀}` be finite dimensional, for
every field `k` of finite type over `S` and every `x₀ ∈ F(Spec k)`. This file records that
condition.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver.toOver`: the structure functor of the locally
  Noetherian site to schemes over `S`.
* `AlgebraicGeometry.LocallyNoetherianOver.elementsToOver`: the category fibred in sets
  attached to `F`, that is the opposite of the category of elements of `F`, over schemes over
  `S`.
* `AlgebraicGeometry.LocallyNoetherianOver.HasFiniteDimensionalTangentSpaces`: axiom `[3]`.

## References

* [Stacks Project, Tag 07T2](https://stacks.math.columbia.edu/tag/07T2)
* [Stacks Project, Tag 07T4](https://stacks.math.columbia.edu/tag/07T4)
* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianOver

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure functor of the locally Noetherian site of `S` to schemes over `S`. -/
abbrev toOver : LocallyNoetherianOver B S hS ⥤ Over S :=
  ObjectProperty.ι _ ⋙ Over.post B.inclusion

/-- The category fibred in sets attached to a set-valued functor `F` on the locally Noetherian
site of `S`: the opposite of the category of elements of `F`, over schemes over `S`. An object
over `T` is an element of `F(T)`, and an arrow over `T' ⟶ T` from `ξ' ∈ F(T')` to `ξ ∈ F(T)` is
the statement that `ξ` restricts to `ξ'`. -/
abbrev elementsToOver (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w) :
    F.Elementsᵒᵖ ⥤ Over S :=
  (CategoryOfElements.π F).leftOp ⋙ toOver B S hS

/-- **Artin's axiom `[3]`** for a set-valued functor on the locally Noetherian site of `S`:
for every field `k` of finite type over `S`, every affine open `Spec Λ ⊆ S` through which
`Spec k ⟶ S` factors with `Λ → k` finite, and every `x₀ ∈ F(Spec k)`, the tangent space
`T𝓕_{F,k,x₀}` of the predeformation category of `x₀` is finite dimensional over `k`, for its
canonical vector-space structure of Stacks 06IH. -/
def HasFiniteDimensionalTangentSpaces
    (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (_ : IsOpenImmersion iΛ) (x₀ : F.Elementsᵒᵖ)
    (hx₀ : (elementsToOver B S hS F).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
    let D := Deformation.Artin.predeformationCategory iΛ (elementsToOver B S hS F) x₀ hx₀
    letI : Category D.carrier := D.category
    ∀ (h : Deformation.IsPredeformationCategory (BasedCategory.ofFunctor D.projection).p)
      (hS2 : Deformation.SchlessingerConditionS2 (CategoryOfElements.π
        (Deformation.isomorphismClasses (BasedCategory.ofFunctor D.projection) h.cofibered))),
      letI : Fact (Deformation.IsPredeformationCategory
        (BasedCategory.ofFunctor D.projection).p) := ⟨h⟩
      letI : Fact (Deformation.SchlessingerConditionS2 (CategoryOfElements.π
        (Deformation.isomorphismClasses (BasedCategory.ofFunctor D.projection)
          h.cofibered))) := ⟨hS2⟩
      FiniteDimensional k (Deformation.artinianTangentSpace Λ k
        (Deformation.isomorphismClasses (BasedCategory.ofFunctor D.projection) h.cofibered))

end AlgebraicGeometry.LocallyNoetherianOver

end
