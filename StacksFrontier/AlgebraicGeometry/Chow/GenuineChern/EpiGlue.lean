module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.EpiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# Factoring one quotient through another, locally on the target

Let `q₁ : F ⟶ L₁` be an epimorphism and `q₂ : F ⟶ L₂` a morphism of sheaves of modules on a
scheme `Y`. If, on each member of a family of open immersions covering `Y`, the pullback of `q₂`
factors through the pullback of `q₁`, then `q₂` factors through `q₁`, uniquely. The local
factorizations need not agree with one another, nor be isomorphisms: the kernel of `q₁` is killed
by `q₂` because it is killed locally, and `q₁` is the cokernel of its kernel.

When `q₂` is also an epimorphism and both targets are invertible, the factorization is an
isomorphism, being a surjection between invertible modules. This is how two invertible quotients
of one module are identified from local identifications: the tautological quotients of two
projective bundles, for instance, which are identified chart by chart.

## Main results

* `Stacks.Chow.GenuineChern.existsUnique_comp_eq_of_pullback`: the factorization, from local
  factorizations of the pullbacks along a covering family of open immersions.
* `Stacks.Chow.GenuineChern.existsUnique_comp_eq_of_restrict`: the same with restrictions.
* `Stacks.Chow.GenuineChern.existsUnique_iso_of_pullback` and
  `Stacks.Chow.GenuineChern.existsUnique_iso_of_restrict`: for two invertible quotients the
  factorization is an isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Chow.GenuineChern

variable {Y : Scheme.{u}} {F L₁ L₂ : Y.Modules} {I : Type v} {Z : I → Scheme.{u}}
  (j : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (j i)] (hj : ⨆ i, (j i).opensRange = ⊤)

include hj in
/-- **A morphism out of `F` factors through an epimorphism out of `F` as soon as it does so
locally.** The local factorizations are arbitrary morphisms, not required to be compatible. -/
theorem existsUnique_comp_eq_of_pullback (q₁ : F ⟶ L₁) [Epi q₁] (q₂ : F ⟶ L₂)
    (h : ∀ i, ∃ ψ : (Scheme.Modules.pullback (j i)).obj L₁ ⟶
        (Scheme.Modules.pullback (j i)).obj L₂,
      (Scheme.Modules.pullback (j i)).map q₁ ≫ ψ = (Scheme.Modules.pullback (j i)).map q₂) :
    ∃! φ : L₁ ⟶ L₂, q₁ ≫ φ = q₂ := by
  have hz : kernel.ι q₁ ≫ q₂ = 0 := by
    refine Stacks.Descent.hom_ext_of_pullback_map_eq j hj fun i => ?_
    obtain ⟨ψ, hψ⟩ := h i
    rw [Functor.map_comp, Functor.map_zero, ← hψ, ← Category.assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, zero_comp]
  exact ⟨Abelian.epiDesc q₁ q₂ hz, Abelian.comp_epiDesc q₁ q₂ hz,
    fun φ hφ => (cancel_epi q₁).1 (hφ.trans (Abelian.comp_epiDesc q₁ q₂ hz).symm)⟩

include hj in
/-- **The factorization, from local factorizations of the restrictions.** -/
theorem existsUnique_comp_eq_of_restrict (q₁ : F ⟶ L₁) [Epi q₁] (q₂ : F ⟶ L₂)
    (h : ∀ i, ∃ ψ : (Scheme.Modules.restrictFunctor (j i)).obj L₁ ⟶
        (Scheme.Modules.restrictFunctor (j i)).obj L₂,
      (Scheme.Modules.restrictFunctor (j i)).map q₁ ≫ ψ =
        (Scheme.Modules.restrictFunctor (j i)).map q₂) :
    ∃! φ : L₁ ⟶ L₂, q₁ ≫ φ = q₂ := by
  refine existsUnique_comp_eq_of_pullback j hj q₁ q₂ fun i => ?_
  obtain ⟨ψ, hψ⟩ := h i
  let e := Scheme.Modules.restrictFunctorIsoPullback (j i)
  refine ⟨e.inv.app L₁ ≫ ψ ≫ e.hom.app L₂, ?_⟩
  rw [e.inv.naturality_assoc, reassoc_of% hψ, ← e.inv.naturality_assoc, Iso.inv_hom_id_app,
    Category.comp_id]

/-- A surjection between two invertible modules on a scheme is an isomorphism. -/
theorem isIso_of_epi_of_isInvertible {M N : Y.Modules} (φ : M ⟶ N) [hφ : Epi φ]
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N) :
    IsIso φ := by
  have hMs : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hM
  have hNs : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hN
  exact @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible Y.toRingedSpace M N φ hφ hMs hNs

/-- A unique factorization of an epimorphism `q₂` through an epimorphism `q₁` between invertible
modules is a unique isomorphism. -/
private theorem existsUnique_iso_of_existsUnique_comp_eq (q₁ : F ⟶ L₁) [Epi q₁] (q₂ : F ⟶ L₂)
    [Epi q₂]
    (h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₂)
    (h : ∃! φ : L₁ ⟶ L₂, q₁ ≫ φ = q₂) : ∃! φ : L₁ ≅ L₂, q₁ ≫ φ.hom = q₂ := by
  obtain ⟨φ, hφ, huniq⟩ := h
  have : Epi φ := by
    have : Epi (q₁ ≫ φ) := by rw [hφ]; infer_instance
    exact epi_of_epi q₁ φ
  have : IsIso φ := isIso_of_epi_of_isInvertible φ h₁ h₂
  exact ⟨asIso φ, hφ, fun ψ hψ => Iso.ext (huniq ψ.hom hψ)⟩

include hj in
/-- **Two invertible quotients of one module that agree locally are isomorphic**, by a unique
isomorphism over the module. The local factorizations are arbitrary morphisms. -/
theorem existsUnique_iso_of_pullback (q₁ : F ⟶ L₁) [Epi q₁] (q₂ : F ⟶ L₂) [Epi q₂]
    (h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₂)
    (h : ∀ i, ∃ ψ : (Scheme.Modules.pullback (j i)).obj L₁ ⟶
        (Scheme.Modules.pullback (j i)).obj L₂,
      (Scheme.Modules.pullback (j i)).map q₁ ≫ ψ = (Scheme.Modules.pullback (j i)).map q₂) :
    ∃! φ : L₁ ≅ L₂, q₁ ≫ φ.hom = q₂ :=
  existsUnique_iso_of_existsUnique_comp_eq q₁ q₂ h₁ h₂
    (existsUnique_comp_eq_of_pullback j hj q₁ q₂ h)

include hj in
/-- **Two invertible quotients of one module that agree locally are isomorphic**, from local
factorizations of the restrictions. -/
theorem existsUnique_iso_of_restrict (q₁ : F ⟶ L₁) [Epi q₁] (q₂ : F ⟶ L₂) [Epi q₂]
    (h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₂)
    (h : ∀ i, ∃ ψ : (Scheme.Modules.restrictFunctor (j i)).obj L₁ ⟶
        (Scheme.Modules.restrictFunctor (j i)).obj L₂,
      (Scheme.Modules.restrictFunctor (j i)).map q₁ ≫ ψ =
        (Scheme.Modules.restrictFunctor (j i)).map q₂) :
    ∃! φ : L₁ ≅ L₂, q₁ ≫ φ.hom = q₂ :=
  existsUnique_iso_of_existsUnique_comp_eq q₁ q₂ h₁ h₂
    (existsUnique_comp_eq_of_restrict j hj q₁ q₂ h)

end Stacks.Chow.GenuineChern

end
