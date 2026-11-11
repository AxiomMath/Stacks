module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineFiber

/-!
# The support of a quasi-coherent module whose sections over an affine chart are killed by an ideal

Let `X` be an algebraic space, `A` an étale chart of `X` whose scheme `U` is affine, and `F` a
quasi-coherent `𝒪_X`-module. If an ideal `J ⊆ Γ(U, 𝒪_U)` kills the sections `F(A)`, then the
support of the restriction `F|_U` of `F` to the chart lies in `V(J) ⊆ U`: the global sections of
`F|_U` are `F(A)`, linearly over `Γ(U, 𝒪_U)`, and on an affine scheme the support of a
quasi-coherent module is the support of its module of global sections (Stacks 056I).

## Main results

* `AlgebraicGeometry.Space.isoSpec_mem_zeroLocus_of_mem_supp_restrictToChart`: a point of the
  support of `F|_U` lies in `V(J)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **A quasi-coherent module whose sections over an affine chart are killed by an ideal `J` has
chart restriction supported in `V(J)`.** Let `A` be an étale chart of `X` with affine scheme `U`,
`F` a quasi-coherent `𝒪_X`-module and `J ⊆ Γ(U, 𝒪_U)` an ideal with `r • s = 0` for all `r ∈ J`
and `s ∈ F(A)`. Every point of the support of `F|_U` lies in `V(J)`. -/
theorem isoSpec_mem_zeroLocus_of_mem_supp_restrictToChart (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) [IsAffine (chartScheme A)]
    (J : Ideal Γ(chartScheme A, ⊤)) (hJ : ∀ r ∈ J, ∀ s : M.val.obj (op A), r • s = 0)
    (x : chartScheme A) (hx : x ∈ SheafOfModules.supp (restrictToChart B S hS X.2 M A)) :
    (chartScheme A).isoSpec.hom x ∈ PrimeSpectrum.zeroLocus (J : Set Γ(chartScheme A, ⊤)) := by
  let F : (chartScheme A).Modules := @id (chartScheme A).Modules (restrictToChart B S hS X.2 M A)
  have : F.IsQuasicoherent := isQuasicoherent_restrictToChart B S hS X M hM A
  have hx' : x ∈ SheafOfModules.supp F := hx
  rw [← mem_support_sections_iff_mem_supp_top] at hx'
  replace hx := hx'
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.1 hx
  intro r hr
  apply hm
  rw [Submodule.mem_annihilator_span_singleton]
  -- the global sections of `F|_U` are `F(A)`, linearly over `Γ(U, 𝒪_U)`
  let φ : (Γ(F, ⊤) : Type u) ≃ₗ[Γ(chartScheme A, ⊤)] (M.val.obj (op A) : Type u) :=
    ((moduleGlobalSections (chartScheme A)).mapIso
        (restrictToChartIsoChartRestrictionSheaf B S hS X M A)).toLinearEquiv.trans
      (chartRestrictionSheafTopEquiv B S hS X M A).symm
  apply φ.injective
  simp only [map_smul, hJ r hr, map_zero]

end AlgebraicGeometry.Space

end
