module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplitting
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.ReesAlgebra.SmulDescend

/-!
# The affine input to the graded splitting: one exponent for the global sections

Let `I = (f₁, …, f_r)` be an ideal of a Noetherian ring `A`, let `φ_j : I ^ c ⟶ A` split the
inclusion against the generators, and let `(F_n)` be a coherent adic system along a
quasi-coherent ideal sheaf on an *affine* Noetherian scheme `X` over `Spec A`. This file
supplies the one step of [Stacks, Tag 0EH6] where [Stacks, Tag 0EIC] is applied: after
enlarging `c` to a `d`, the splitting kills the relations of the global sections
`Γ(F, ⊤) = lim_m Γ(F_m, ⊤)`.

## Main definitions

* `Stacks.Coherent.baseCompletionHom` — the ring map `A ⟶ Γ(X, 𝒪_X)^` through which `A` acts on
  the module of [Stacks, Tag 087W].

## Main results

* `Stacks.Coherent.exists_killsRelationsHom_globalSections` — the enlarged exponent, the
  adjusted splitting, and relation-killing for the global sections of the limit.

## Implementation notes

`Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I fX` is by definition
`Scheme.IdealSheafData.ofIdealTop (baseIdeal A I fX)`, which is the shape the equivalence of
[Stacks, Tag 087W] is stated for, so the statement here is directly applicable to the ideal
sheaf `I · 𝒪_X` of [Stacks, Tag 0EH6]; the ideal of `Γ(X, 𝒪_X)` is left as a parameter because
nothing in the argument needs it to come from `A`.

## References

* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.ReesAlgebra Stacks.Cohomology.FormalFunctions
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

/-- The ring map `A ⟶ Γ(X, 𝒪_X)^` induced by the structure morphism `X ⟶ Spec A` followed by
the completion of the global sections. -/
public def baseCompletionHom (A : Type u) [CommRing A] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (I : Ideal Γ(X, ⊤)) :
    A →+* AdicCompletion I Γ(X, ⊤) :=
  (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤))).comp (baseSectionHom A fX ⊤)

/-- **The affine application of [Stacks, Tag 0EIC] inside [Stacks, Tag 0EH6].**

On an affine Noetherian scheme over `Spec A` the exponent `c` can be enlarged *once*, to a `d`
with an adjusted splitting `ψ`, so that `ψ` kills the relations of the global sections of the
inverse limit of a coherent adic system.

The module is not finite over `Γ(X, 𝒪_X)`; it is a finite module over the `I`-adic completion
of `Γ(X, 𝒪_X)` by [Stacks, Tag 087W], and that ring is Noetherian by [Stacks, Tag 0316], which
is where [Stacks, Tag 0EIC] is applied. -/
public theorem exists_killsRelationsHom_globalSections
    (A : Type u) [CommRing A] (J : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgen : J = Ideal.span (Set.range gen)) (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ g : (J ^ c : Ideal A), (∑ j, gen j * φ j g) = (g : A))
    {X : Scheme.{u}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (fX : X ⟶ Spec (.of A)) (I : Ideal Γ(X, ⊤))
    (F : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting J hcd φ ψ ∧
      (∀ g : (J ^ d : Ideal A), (∑ j, gen j * ψ j g) = (g : A)) ∧
      KillsRelationsHom (baseSectionHom A fX ⊤)
        (limit (globalSectionsSystem F) : ModuleCat.{u} Γ(X, ⊤)) J d ψ := by
  obtain ⟨d, hcd, ψ, hres, hsplit, hkill⟩ :=
    exists_extendLinearMaps_killsRelationsHom A (AdicCompletion I Γ(X, ⊤))
      ((coherentAdicSystemsEquivFGModuleCat X I).functor.obj F)
      (baseCompletionHom A fX I) J gen hgen c hc φ hφ
  refine ⟨d, hcd, ψ, hres, hsplit, ?_⟩
  have hid : ∀ w : (limit (globalSectionsSystem F) : ModuleCat.{u} Γ(X, ⊤)),
      (globalSectionsComparison X I F).hom.hom
        ((globalSectionsComparison X I F).inv.hom w) = w := fun w =>
    congrArg (fun k : (limit (globalSectionsSystem F) : ModuleCat.{u} Γ(X, ⊤)) ⟶ _ => k.hom w)
      (globalSectionsComparison X I F).inv_hom_id
  refine killsRelationsHom_of_injective (baseSectionHom A fX ⊤) (baseCompletionHom A fX I)
    (globalSectionsComparison X I F).inv.hom.toAddMonoidHom ?_ ?_ hkill
  · intro a x
    exact (globalSectionsComparison X I F).inv.hom.map_smul (baseSectionHom A fX ⊤ a) x
  · intro x y hxy
    have hxy' : (globalSectionsComparison X I F).inv.hom x =
        (globalSectionsComparison X I F).inv.hom y := hxy
    have h := congrArg (fun w => (globalSectionsComparison X I F).hom.hom w) hxy'
    rwa [hid x, hid y] at h

/-- **The affine application of [Stacks, Tag 0EIC] inside [Stacks, Tag 0EH6]**, for the ideal
sheaf `I · 𝒪_X` that the tag is stated with. This is
`Stacks.Coherent.exists_killsRelationsHom_globalSections` at the ideal `baseIdeal A J fX`, the
extension `I · 𝒪_X` being by definition the quasi-coherent ideal sheaf that ideal
generates. -/
public theorem exists_killsRelationsHom_globalSections_base
    (A : Type u) [CommRing A] (J : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgen : J = Ideal.span (Set.range gen)) (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ g : (J ^ c : Ideal A), (∑ j, gen j * φ j g) = (g : A))
    {X : Scheme.{u}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (fX : X ⟶ Spec (.of A))
    (F : CoherentAdicSystems (baseIdealSheaf A J fX)) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting J hcd φ ψ ∧
      (∀ g : (J ^ d : Ideal A), (∑ j, gen j * ψ j g) = (g : A)) ∧
      KillsRelationsHom (baseSectionHom A fX ⊤)
        (limit (globalSectionsSystem F) : ModuleCat.{u} Γ(X, ⊤)) J d ψ :=
  exists_killsRelationsHom_globalSections A J gen hgen c hc φ hφ fX (baseIdeal A J fX) F

end Stacks.Coherent

end
