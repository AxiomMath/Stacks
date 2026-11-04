module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.ModuleDeformation.CopowerExtension

/-!
# Finite-dimensionality of infinitesimal automorphisms through an extension

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), and `x` an object of
`𝓕` with chosen pushforwards `P`. The vector-space structure of Stacks 06JV on the infinitesimal
automorphisms `Inf_x(𝓕)` of `x` is explicit: addition is composition of automorphisms of the
pushforward of `x` to the dual numbers, and multiplication by `c ∈ k` is transport along the
scaling `ε ↦ c ε` of the dual numbers (`Deformation.naturalLocalizedTangentModule_spec`).

So `Inf_x(𝓕)` is finite-dimensional as soon as it acts faithfully on the middle term of a short
exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of an abelian `k`-linear category, by automorphisms
inducing the identity on `X₁` and `X₃` and with differences from the identity scaling as the
transported automorphisms do, provided `Hom(X₃, X₁)` is finite-dimensional: the coordinates
`a ↦ t` with `a - 𝟙 = g ≫ t ≫ f` then embed `Inf_x(𝓕)` linearly into `Hom(X₃, X₁)`.

This is how the infinitesimal automorphisms of the stack of coherent sheaves of Stacks 08W8 are
bounded by `Ext⁰(𝒢₀, 𝒢₀) = Hom(𝒢₀, 𝒢₀)`.

## Main results

* `Deformation.finiteDimensional_localizedAutomorphismFunctorTangent_of_extension`: the bound for
  the tangent space at the identity of the automorphism functor.
* `Deformation.finiteDimensional_infinitesimalAutomorphismLinearLift_of_extension`: the bound
  for the lifted model `Deformation.IsFiniteDimensionalDeformationCategory` speaks about.
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- **The tangent space at the identity of the automorphism functor is finite-dimensional when the
infinitesimal automorphisms act faithfully on an extension with finite-dimensional
`Hom(X₃, X₁)`**, by automorphisms fixing both outer terms whose differences from the identity
scale as the transported automorphisms do. -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_extension
    (hp : SatisfiesRS p) {x : F} (P : ChosenPushforwardsAt p x)
    {𝒜 : Type u₂} [Category.{v₂} 𝒜] [Abelian 𝒜] [Linear k 𝒜]
    {S : ShortComplex 𝒜} (hS : S.ShortExact) [FiniteDimensional k (S.X₃ ⟶ S.X₁)]
    (ρ : infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)) →* Aut S.X₂)
    (hρ : Function.Injective ρ)
    (hi : ∀ a, S.f ≫ (ρ a).hom = S.f) (hq : ∀ a, (ρ a).hom ≫ S.g = S.g)
    (hscale : ∀ (c : k) (a b : infinitesimalAutomorphismKernel P
        (tangentReduction (p := p) (x := x))),
      b.val = P.transportAutHom (tangentScaling c) a.val →
        (ρ b).hom - 𝟙 S.X₂ = c • ((ρ a).hom - 𝟙 S.X₂)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  let e := localizedTangentEquivKernel P
  let E := ModuleDeformation.extensionAutomorphismCoordinates hS ρ hi hq
  let f : localizedAutomorphismFunctorTangent P →ₗ[k] (S.X₃ ⟶ S.X₁) :=
    { toFun := fun a => Multiplicative.toAdd (E (e a))
      map_add' := fun a b => by
        rw [(naturalLocalizedTangentModule_spec P hp).1, map_mul]
        rfl
      map_smul' := fun c a =>
        ModuleDeformation.extensionAutomorphismCoordinates_smul hS ρ hi hq c (e a) (e (c • a))
          (hscale c (e a) (e (c • a)) ((naturalLocalizedTangentModule_spec P hp).2 c a)) }
  exact FiniteDimensional.of_injective f (fun a b h => e.injective
    (ModuleDeformation.extensionAutomorphismCoordinates_injective hS ρ hi hq hρ h))

/-- **The lifted model of the infinitesimal automorphisms is finite-dimensional** under the
hypotheses of `Deformation.finiteDimensional_localizedAutomorphismFunctorTangent_of_extension`. -/
theorem finiteDimensional_infinitesimalAutomorphismLinearLift_of_extension
    (hp : SatisfiesRS p) {x : F} (P : ChosenPushforwardsAt p x)
    {𝒜 : Type u₂} [Category.{v₂} 𝒜] [Abelian 𝒜] [Linear k 𝒜]
    {S : ShortComplex 𝒜} (hS : S.ShortExact) [FiniteDimensional k (S.X₃ ⟶ S.X₁)]
    (ρ : infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)) →* Aut S.X₂)
    (hρ : Function.Injective ρ)
    (hi : ∀ a, S.f ≫ (ρ a).hom = S.f) (hq : ∀ a, (ρ a).hom ≫ S.g = S.g)
    (hscale : ∀ (c : k) (a b : infinitesimalAutomorphismKernel P
        (tangentReduction (p := p) (x := x))),
      b.val = P.transportAutHom (tangentScaling c) a.val →
        (ρ b).hom - 𝟙 S.X₂ = c • ((ρ a).hom - 𝟙 S.X₂)) :
    FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, v, w} P hp).functor.obj
      (FGModuleCat.of k (ULift.{v} k))) :=
  finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized hp P
    (finiteDimensional_localizedAutomorphismFunctorTangent_of_extension hp P hS ρ hρ hi hq
      hscale)

end Deformation

end
