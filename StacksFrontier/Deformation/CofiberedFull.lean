module

public import StacksFrontier.Deformation.Cofibered

/-!
# Fullness of a morphism of categories cofibered in groupoids is a statement about one fibre

Let `p : ℬ ⥤ 𝒞` be cofibered in groupoids and let `F : 𝒜 ⥤ ℬ` be a functor whose composite
`F ⋙ p` is cofibered in groupoids too — so that `F` is a morphism of categories cofibered in
groupoids over `𝒞`.  To prove `F` full one has to lift an arbitrary arrow
`h : F.obj P ⟶ F.obj Q`, which lies over an arbitrary arrow of `𝒞`.  This file reduces that to
lifting the arrows lying over an **identity** of `𝒞`.

The reduction is the universal property of a cocartesian arrow.  Push `P` forward along the
image of `h` in `𝒞`: there is an `R` and an arrow `χ : P ⟶ R` over that image.  In a category
cofibered in groupoids every arrow is strongly cocartesian over its image
(`Deformation.isStronglyCocartesian_of_isCofiberedInGroupoids`), so `F.map χ` is, and `h` —
which lies over the same arrow of `𝒞` — factors uniquely through it as `F.map χ ≫ θ` with `θ`
over the identity.  A lift `ψ` of `θ` then gives `h = F.map (χ ≫ ψ)`.

So all the content of fullness sits in a single fibre, where the two objects have the same
image in `𝒞` and the arrow to be lifted is vertical.  That is the shape in which the
remaining half of [Stacks, Tag 0E3X] is a geometric statement: two deformations of a morphism
of schemes over the *same* Artinian base whose source families are identified must have their
target families identified.

## Main results

* `Deformation.full_of_exists_lift_of_isHomLift_id` — **fullness from the vertical case.**

## Implementation notes

The statement takes the lower functor `p` and forms the upper projection as `F ⋙ p` rather
than taking a second projection together with an equality of functors.  With the equality
present, every use of it has to transport an `eqToHom` through
`CategoryTheory.Functor.IsHomLift`, whose three fields are equalities of objects and of
morphisms; with the composite, `(F ⋙ p).map χ` and `p.map (F.map χ)` are the same term and the
transport disappears.  A caller whose two projections are related by an equality of functors
rewrites with it once, at the statement, instead.

`CategoryTheory.Functor.IsHomLift` is a class, so the hypothesis supplying the vertical lifts
takes it as an explicit argument and the proof reinstates it with `haveI` where Mathlib's
`CategoryTheory.Functor.IsStronglyCocartesian.universal_property'` expects it as an instance.

## References

* [Stacks Project, Tag 06GJ](https://stacks.math.columbia.edu/tag/06GJ)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞]

/-- **Fullness of a morphism of categories cofibered in groupoids from the vertical case.**
Let `p : ℬ ⥤ 𝒞` and `F ⋙ p` be cofibered in groupoids.  If every arrow `F.obj R ⟶ F.obj Q`
lying over an identity of `𝒞` is in the image of `F`, then `F` is full.

An arbitrary arrow `h : F.obj P ⟶ F.obj Q` lies over `p.map h`.  Pushing `P` forward along
`p.map h` in the upper category gives `χ : P ⟶ R` over `p.map h`, and `F.map χ` is strongly
cocartesian over `p.map h` because `p` is cofibered in groupoids; the universal property
factors `h` as `F.map χ ≫ θ` with `θ` over the identity, and a lift `ψ` of `θ` makes
`h = F.map (χ ≫ ψ)`. -/
public theorem full_of_exists_lift_of_isHomLift_id (F : 𝒜 ⥤ ℬ) (p : ℬ ⥤ 𝒞)
    (hA : IsCofiberedInGroupoids (F ⋙ p)) (hB : IsCofiberedInGroupoids p)
    (hlift : ∀ (R Q : 𝒜) (θ : F.obj R ⟶ F.obj Q),
      p.IsHomLift (𝟙 (p.obj (F.obj Q))) θ → ∃ ψ : R ⟶ Q, F.map ψ = θ) :
    F.Full := by
  constructor
  intro P Q h
  obtain ⟨R, χ, hχ⟩ := exists_pushforward hA (p.map h) P rfl
  have hχ' : p.IsHomLift (p.map h) (F.map χ) :=
    IsHomLift.of_fac' p (p.map h) (F.map χ)
      (IsHomLift.domain_eq (F ⋙ p) (p.map h) χ)
      (IsHomLift.codomain_eq (F ⋙ p) (p.map h) χ)
      (IsHomLift.fac' (F ⋙ p) (p.map h) χ)
  have : p.IsStronglyCocartesian (p.map h) (F.map χ) :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hB (p.map h) (F.map χ) hχ'
  have : p.IsHomLift (p.map h ≫ 𝟙 (p.obj (F.obj Q))) h := inferInstance
  obtain ⟨θ, ⟨hθ, hfac⟩, -⟩ :=
    Functor.IsStronglyCocartesian.universal_property' (p := p) (f := p.map h)
      (φ := F.map χ) (𝟙 (p.obj (F.obj Q))) h
  obtain ⟨ψ, hψ⟩ := hlift R Q θ hθ
  exact ⟨χ ≫ ψ, by rw [F.map_comp, hψ, hfac]⟩

end Deformation

end
