module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback

/-!
# Comparing two quotients of a module on an algebraic space, flat locally

Let `Z` be an algebraic space and `χ : ℳ ⟶ 𝒜`, `χ' : ℳ ⟶ 𝒜'` two surjections of `𝒪_Z`-modules.
An isomorphism `e : 𝒜 ≅ 𝒜'` with `χ ≫ e = χ'` is unique if it exists, both maps being
epimorphisms; and it exists as soon as it exists after the inverse image along a jointly
surjective family of flat morphisms `φ_i : Z_i ⟶ Z`. Indeed, the kernel of `χ` is then killed by
`χ'`, because its inverse image along every `φ_i` is, and an epimorphism of modules is the
cokernel of its kernel; symmetrically for `χ'`, and the two factorizations are inverse to each
other by epimorphism cancellation. No compatibility of the local isomorphisms on overlaps is
needed: the epimorphisms make them unique.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.exists_comp_eq_of_modulePullback`: a factorization
  through an epimorphism exists as soon as it exists flat locally.
* `AlgebraicGeometry.Space.PrivateChern.exists_iso_comp_eq_of_modulePullback`: two quotients
  which are flat locally isomorphic are isomorphic.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : AlgebraicSpaces B S hS} {I : Type*} {Z' : I → AlgebraicSpaces B S hS}
  (φ : ∀ i, Z' i ⟶ Z) (hφ : ∀ i, IsFlat B S hS (φ i).hom)
  (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
  {M A A' : Modules.{u, u} B S hS Z.1 Z.2}

include hφ hsurj in
/-- **A factorization through an epimorphism exists as soon as it exists flat locally.** -/
theorem exists_comp_eq_of_modulePullback (χ : M ⟶ A) [Epi χ] (χ' : M ⟶ A')
    (h : ∀ i, ∃ θ : (modulePullback B S hS (φ i)).obj A ⟶ (modulePullback B S hS (φ i)).obj A',
      (modulePullback B S hS (φ i)).map χ ≫ θ = (modulePullback B S hS (φ i)).map χ') :
    ∃ β : A ⟶ A', χ ≫ β = χ' := by
  have := fun i => preservesZeroMorphisms_modulePullback B S hS (φ i)
  have heff : EffectiveEpi χ := by
    let : Abelian (Modules.{u, u} B S hS Z.1 Z.2) := SheafOfModules.instAbelian _
    have : IsRegularEpi χ := ⟨⟨(normalEpiOfEpi χ).regularEpi⟩⟩
    infer_instance
  refine ⟨EffectiveEpi.desc χ χ' fun {T} g₁ g₂ hg => ?_, EffectiveEpi.fac χ χ' _⟩
  rw [← sub_eq_zero, ← Preadditive.sub_comp]
  rw [← sub_eq_zero, ← Preadditive.sub_comp] at hg
  refine eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat B S hS φ hφ hsurj _ fun i => ?_
  obtain ⟨θ, hθ⟩ := h i
  rw [CategoryTheory.Functor.map_comp, ← hθ, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, hg, Functor.map_zero, zero_comp]

include hφ hsurj in
/-- **Two quotients which are flat locally isomorphic are isomorphic.** -/
theorem exists_iso_comp_eq_of_modulePullback (χ : M ⟶ A) [Epi χ] (χ' : M ⟶ A') [Epi χ']
    (h : ∀ i, ∃ θ : (modulePullback B S hS (φ i)).obj A ≅ (modulePullback B S hS (φ i)).obj A',
      (modulePullback B S hS (φ i)).map χ ≫ θ.hom = (modulePullback B S hS (φ i)).map χ') :
    ∃ e : A ≅ A', χ ≫ e.hom = χ' := by
  obtain ⟨β, hβ⟩ := exists_comp_eq_of_modulePullback φ hφ hsurj χ χ' fun i => by
    obtain ⟨θ, hθ⟩ := h i
    exact ⟨θ.hom, hθ⟩
  obtain ⟨β', hβ'⟩ := exists_comp_eq_of_modulePullback φ hφ hsurj χ' χ fun i => by
    obtain ⟨θ, hθ⟩ := h i
    exact ⟨θ.inv, by rw [← hθ, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  refine ⟨⟨β, β', ?_, ?_⟩, hβ⟩
  · exact (cancel_epi χ).1 (by rw [← Category.assoc, hβ, hβ', Category.comp_id])
  · exact (cancel_epi χ').1 (by rw [← Category.assoc, hβ', hβ, Category.comp_id])

end AlgebraicGeometry.Space.PrivateChern

end
