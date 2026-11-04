module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReesModuleOnBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteOverAffine

/-!
# Finiteness of the cohomology of the image module on the base change

For `f : X ⟶ h_T` proper with `T` affine Noetherian, a map `φ : R ⟶ R'` of finitely generated
`A`-algebras and a coherent `F` on `X`, the image module of
`AlgebraicGeometry.Space.algebraImageModule` on `X_R` has cohomology finite over
`Γ(h_{Spec R}, 𝒪) ≅ R`: this is [Stacks, Tag 08AS]
(`AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_of_isProper`) for `X_R ⟶ h_{Spec R}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  (R' : Type u) [CommRing R'] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R')

/-- **The cohomology of the image module is finite over `Γ(h_{Spec R}, 𝒪)`.** -/
theorem hasFiniteGlobalCohomologyOver_algebraImageModule (hZtop : B.Contains (⊤_ Scheme.{u}))
    [IsNoetherianRing R] (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    HasFiniteGlobalCohomologyOver B S hS (algebraBaseChangeStructure B S hS T f R)
      (algebraImageModule B S hS T f R R' φ F) := by
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (algebraSpectrumOver B S hS T R)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of R)))
  have hP := isProper_algebraBaseChangeStructure B S hS T f R hf
  have hN : HasEtaleLocalProperty B S hS (algebraBaseChange B S hS T f R).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (algebraBaseChange B S hS T f R).2
      (schemeSpace (algebraSpectrumOver B S hS T R)).2 _ hP.2.1.1
      (hasEtaleLocalProperty_of_representable B S hS _ _ _ (Iso.refl _) inferInstance)
  exact hasFiniteGlobalCohomologyOver_of_isProper B S hS hZtop
    (algebraBaseChangeStructure B S hS T f R) hP _
    (isCoherent_algebraImageModule B S hS T f R R' φ hN F hF)

end AlgebraicGeometry.Space

end
