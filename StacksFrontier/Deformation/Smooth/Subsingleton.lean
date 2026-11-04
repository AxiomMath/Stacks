module

public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Smoothness over a base with exactly one point everywhere

Let `𝓖` be a category over `𝒞_Λ` and let `R` be a Noetherian complete local `Λ`-algebra
such that every Artinian local `Λ`-algebra carries exactly one `Λ`-algebra map out of `R`,
that is, such that the functor `restrictedCoyoneda R` is a singleton at each object. Then
*any* morphism of categories over `𝒞_Λ` from the cofibered set of `R` to `𝓖` is smooth, as
soon as `𝓖` is thin over `𝒞_Λ` -- a morphism of `𝓖` is determined by its image -- and any
two objects of `𝓖` over the same object of `𝒞_Λ` are joined by a morphism over the
identity.

Indeed the lifting problem asks, for a surjection `B ⟶ A` and an object `x = (A, α)` of the
source over `A`, for an object over `B` mapping to `x`: the hypothesis on `R` supplies the
unique point `α' : R ⟶ B` and forces its restriction along `B ⟶ A` to be `α`, so
`(B, α') ⟶ (A, α)` is a morphism of the source lying over `B ⟶ A`. The remaining datum is a
morphism from the image of `(B, α')` to the prescribed object `y`, and both of those lie
over `B`, so the vertical hypothesis produces one; thinness then makes the required triangle
commute automatically, both of its sides lying over the same arrow of `𝒞_Λ`.

This is the form in which versality of a formal object is checked when the base of the
formal object represents a subsingleton-valued functor: no property of the formal object or
of the chosen pushforwards enters, so the conclusion holds for every choice of them.

## Main results

* `Deformation.isSmooth_of_subsingleton_restrictedCoyoneda`.

## References

* [Stacks Project, Tag 06HG](https://stacks.math.columbia.edu/tag/06HG)
* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u v w u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **A morphism out of the cofibered set of a complete local algebra with exactly one point
at every Artinian local algebra is smooth,** provided the target is thin over `𝒞_Λ` and has
vertical morphisms between any two objects over the same algebra. -/
public theorem isSmooth_of_subsingleton_restrictedCoyoneda
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (hR : ∀ A : ArtinianLocalAlgCat.{u, v, w} Λ k,
      Nonempty (R ⟶ artinianToComplete.obj A) ∧
        Subsingleton (R ⟶ artinianToComplete.obj A))
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (hvert : ∀ (z w : 𝓖.obj) (h : 𝓖.p.obj z = 𝓖.p.obj w),
      ∃ a : z ⟶ w, 𝓖.p.map a = eqToHom h)
    (hthin : ∀ {z w : 𝓖.obj} (s t : z ⟶ w), 𝓖.p.map s = 𝓖.p.map t → s = t)
    (Φ : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R))) 𝓖) :
    IsSmooth Φ := by
  intro B₀ A₀ f hf y x g hg
  let : 𝓖.p.IsHomLift f g := hg
  obtain ⟨A', α⟩ := x
  have hA : A' = A₀ :=
    (BasedFunctor.w_obj Φ _).symm.trans (IsHomLift.codomain_eq 𝓖.p f g)
  subst hA
  obtain ⟨α'⟩ := (hR B₀).1
  have hcompat : (restrictedCoyoneda R).map f α' = α := (hR A').2.elim _ _
  let z₀ : (BasedCategory.ofFunctor
    (CategoryOfElements.π (restrictedCoyoneda R))).obj := ⟨B₀, α'⟩
  let x₁ : (BasedCategory.ofFunctor
    (CategoryOfElements.π (restrictedCoyoneda R))).obj := ⟨A', α⟩
  let hm : z₀ ⟶ x₁ := ⟨f, hcompat⟩
  have hΦz : 𝓖.p.obj (Φ.obj z₀) = B₀ := BasedFunctor.w_obj Φ z₀
  have hy : 𝓖.p.obj y = B₀ := IsHomLift.domain_eq 𝓖.p f g
  obtain ⟨a, ha⟩ := hvert (Φ.obj z₀) y (hΦz.trans hy.symm)
  let hmor : (BasedCategory.ofFunctor
      (CategoryOfElements.π (restrictedCoyoneda R))).p.IsHomLift f hm :=
    IsHomLift.of_fac _ _ _ rfl rfl rfl
  let hverta : 𝓖.p.IsHomLift (𝟙 B₀) a :=
    IsHomLift.of_fac' 𝓖.p (𝟙 B₀) a hΦz hy (by rw [ha]; simp)
  refine ⟨z₀, hm, a, hmor, hverta, ?_⟩
  let h1 : 𝓖.p.IsHomLift f (Φ.map hm) :=
    BasedFunctor.preserves_isHomLift Φ f hm
  have h2 : 𝓖.p.IsHomLift (𝟙 B₀ ≫ f) (a ≫ g) := IsHomLift.comp 𝓖.p _ _ _ _
  rw [Category.id_comp] at h2
  let := h2
  refine hthin _ _ ?_
  rw [IsHomLift.fac' 𝓖.p f (Φ.map hm), IsHomLift.fac' 𝓖.p f (a ≫ g)]

end Deformation

end
