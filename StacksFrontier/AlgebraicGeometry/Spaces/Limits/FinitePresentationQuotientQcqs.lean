module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Main

/-!
# Finite type quasi-coherent modules on qcqs algebraic spaces are quotients of finitely presented
modules

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `M` be a
quasi-coherent `𝒪_X`-module of finite type.  Then there is an `𝒪_X`-module `G` of finite
presentation and an epimorphism `G ⟶ M`.  This is the first step of the source's proof of
Stacks 086Y ("We claim that `𝒢_i → ℱ` is surjective for some `i`").

It combines local generation by modules of finite presentation on a quasi-compact
quasi-separated algebraic space
(`AlgebraicGeometry.Space.isLocallyFpGenerated_of_isQuasiCompactSpace`, by the induction
principle of Stacks 08GP) with
`AlgebraicGeometry.Space.exists_isFinitePresentation_epi_of_isFiniteTypeOnSite`, and renders
finite presentation on the site
(`AlgebraicGeometry.Space.FpAssembly.isFinitePresentationOnSite_of_isFinitePresentation`).

## Main results

* `AlgebraicGeometry.Space.exists_epi_of_isFinitePresentationOnSite_of_isFiniteType`: a finite
  type quasi-coherent module on a quasi-compact quasi-separated algebraic space is a quotient of
  a module of finite presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A finite type quasi-coherent module on a quasi-compact quasi-separated algebraic space is a
quotient of a module of finite presentation.**  Let `X` be a quasi-compact and quasi-separated
algebraic space and `M` a quasi-coherent `𝒪_X`-module of finite type.  Then there are an
`𝒪_X`-module `G` of finite presentation (on the site) and an epimorphism `G ⟶ M`. -/
theorem exists_epi_of_isFinitePresentationOnSite_of_isFiniteType
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (M : Modules.{u, u} B S hS X hX) (hM : M.IsQuasicoherentOnSite) [M.IsFiniteTypeOnSite] :
    ∃ (G : Modules.{u, u} B S hS X hX) (_ : G.IsFinitePresentationOnSite) (p : G ⟶ M), Epi p := by
  obtain ⟨G, hG, p, hp⟩ := exists_isFinitePresentation_epi_of_isFiniteTypeOnSite B S hS hX hqc M
    (isLocallyFpGenerated_of_isQuasiCompactSpace B S hS hZ hX hqc hqs M hM)
  exact ⟨G, FpAssembly.isFinitePresentationOnSite_of_isFinitePresentation G, p, hp⟩

end AlgebraicGeometry.Space

end
