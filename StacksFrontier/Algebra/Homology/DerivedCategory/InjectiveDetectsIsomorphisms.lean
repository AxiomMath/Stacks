module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveRepresents

/-!
# Injective objects placed in one degree detect isomorphisms of the derived category

Let `𝒜` be an abelian category with enough injectives. A morphism `φ : X ⟶ Y` of the unbounded
derived category `D(𝒜)` is an isomorphism as soon as precomposition with `φ` is a bijection
`Hom(Y, E[q]) ⟶ Hom(X, E[q])` for every injective object `E` and every degree `q`.

By `DerivedCategory.homologyToSingleAddEquiv` the groups `Hom(-, E[q])` are the groups
`Hom_𝒜(H^q(-), E)`, naturally, so the hypothesis says that precomposition with `H^q(φ)` is
bijective on morphisms into every injective object; such a morphism of `𝒜` is an isomorphism,
the injectives being enough to see both its kernel and its cokernel.

## Main results

* `CategoryTheory.Abelian.isIso_of_bijective_precomp_injective`: a morphism of an abelian
  category with enough injectives along which precomposition is bijective on morphisms into
  every injective object is an isomorphism.
* `DerivedCategory.isIso_of_bijective_precomp_singleFunctor_injective`: the same for a morphism
  of the derived category, tested on the injective objects placed in every single degree.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- **Injective objects detect isomorphisms.** In an abelian category with enough injectives, a
morphism `g : A ⟶ B` such that precomposition with `g` is a bijection `Hom(B, E) ⟶ Hom(A, E)`
for every injective object `E` is an isomorphism: surjectivity at an injective object containing
`A` makes `g` a monomorphism, and injectivity at an injective object containing the cokernel of
`g` makes that cokernel vanish. -/
theorem isIso_of_bijective_precomp_injective {A B : C} (g : A ⟶ B)
    (h : ∀ (E : C) [Injective E], Function.Bijective (fun a : B ⟶ E => g ≫ a)) :
    IsIso g := by
  have hmono : Mono g := by
    obtain ⟨a, ha⟩ := (h (Injective.under A)).2 (Injective.ι A)
    have ha' : g ≫ a = Injective.ι A := ha
    have : Mono (g ≫ a) := by rw [ha']; infer_instance
    exact mono_of_mono g a
  have hepi : Epi g := by
    have hz : cokernel.π g ≫ Injective.ι (cokernel g) = 0 := by
      apply (h (Injective.under (cokernel g))).1
      simp only [cokernel.condition_assoc, comp_zero, zero_comp]
    have : cokernel.π g = 0 := by
      rw [← cancel_mono (Injective.ι (cokernel g)), hz, zero_comp]
    exact Abelian.epi_of_cokernel_π_eq_zero g this
  exact isIso_of_mono_of_epi g

end CategoryTheory.Abelian

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [EnoughInjectives C]

/-- **Injective objects placed in a single degree detect isomorphisms of the derived category.**
A morphism `φ : X ⟶ Y` of `D(𝒜)`, for `𝒜` abelian with enough injectives, is an isomorphism as
soon as precomposition with it is a bijection `Hom(Y, E[q]) ⟶ Hom(X, E[q])` for every injective
object `E` of `𝒜` and every `q : ℤ`.

Through the natural identification `Hom(-, E[q]) ≅ Hom_𝒜(H^q(-), E)` of
`DerivedCategory.homologyToSingleAddEquiv` the hypothesis is that precomposition with `H^q(φ)`
is bijective on morphisms into every injective object, so each `H^q(φ)` is an isomorphism by
`CategoryTheory.Abelian.isIso_of_bijective_precomp_injective`. -/
theorem isIso_of_bijective_precomp_singleFunctor_injective {X Y : DerivedCategory C}
    (φ : X ⟶ Y)
    (h : ∀ (E : C) [Injective E] (q : ℤ),
      Function.Bijective (fun a : Y ⟶ (singleFunctor C q).obj E => φ ≫ a)) :
    IsIso φ := by
  rw [isIso_iff]
  intro q
  refine Abelian.isIso_of_bijective_precomp_injective _ fun E _ => ?_
  have key : (fun a : (homologyFunctor C q).obj Y ⟶ E => (homologyFunctor C q).map φ ≫ a) =
      homologyToSingleAddEquiv X E q ∘ (fun a : Y ⟶ (singleFunctor C q).obj E => φ ≫ a) ∘
        (homologyToSingleAddEquiv Y E q).symm := by
    funext a
    simp only [Function.comp_apply]
    rw [homologyToSingleAddEquiv_comp, AddEquiv.apply_symm_apply]
  rw [key]
  exact (homologyToSingleAddEquiv X E q).bijective.comp
    ((h E q).comp (homologyToSingleAddEquiv Y E q).symm.bijective)

end DerivedCategory
