module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiKernelIdeal

/-!
# A closed subspace of the relative Proj is the relative Proj of the quotient by its ideal

Let `S` be a scheme, `X` an algebraic space over `S`, `𝒜` a quasi-coherent graded
`𝒪_X`-algebra, `π : P = Proj_X(𝒜) ⟶ X` its relative Proj, and `i : Z ⟶ P` a closed subspace.
The graded ideal `ℐ ⊆ 𝒜` is the kernel of the canonical map
`𝒜 ⟶ ⨁_{d ≥ 0} π_*((i_*𝒪_Z)(d))`, here in degree `d` the adjoint `𝒜_d ⟶ π_*𝒪_P(d)` of
`ψ_d : π^*𝒜_d ⟶ 𝒪_P(d)` of Stacks 084D followed by `π_*` of `𝒪_P(d) ⟶ i_*i^*𝒪_P(d)`, the twist
`(i_*𝒪_Z)(d)` of `i_*𝒪_Z` (`AlgebraicGeometry.Space.C1359Bridge.psiKernelGradedIdeal`).  If `π`
is quasi-compact, then `Z ≅ Proj_X(𝒜/ℐ)` over `P` (Stacks 085L).

The proof is the source's: on the atlas `U ⟶ X` of a presentation of `X` the base change
`Z ×_X U ⊆ Proj_U(𝒜|_U)` is cut out by the graded ideal of Stacks 0801, whose sections over the
charts `W ⟶ U ⟶ X` are those of `ℐ`
(`AlgebraicGeometry.Space.C1359Bridge.mem_twistKerGradedIdeal_iff_mem_psiKernelGradedIdeal`);
so `Z` and `Proj_X(𝒜/ℐ)` have the same base change to the atlas, and descend to the same closed
subspace of `P`
(`AlgebraicGeometry.Space.RelativeProjSituation.exists_iso_quotientProjHom_of_chart`).

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.exists_iso_quotientProjHom_psiKernelGradedIdeal`:
  **Stacks 085L.**

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space.C1359Bridge

variable (s : RelativeProjSituation.{u, u})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)

/-- **Stacks 085L.**  Let `π : P = Proj_X(𝒜) ⟶ X` be the relative Proj of a quasi-coherent graded
`𝒪_X`-algebra on an algebraic space `X` (twists `𝒪_P(d)` and `ψ` built from a presentation of
`X`), and `i : Z ⟶ P` a closed subspace.  Let `ℐ ⊆ 𝒜` be the kernel of the canonical map
`𝒜 ⟶ ⨁_{d ≥ 0} π_*((i_*𝒪_Z)(d))`: in degree `d ≥ 0` the sections killed by the adjoint
`𝒜_d ⟶ π_*𝒪_P(d)` of `ψ_d` followed by `π_*` of `𝒪_P(d) ⟶ i_*i^*𝒪_P(d) = (i_*𝒪_Z)(d)`, and
`ℐ_n = 𝒜_n = 0` for `n < 0`.  If `π` is quasi-compact, `ℐ` is a quasi-coherent graded ideal and
there is an isomorphism `Z ≅ Proj_X(𝒜/ℐ)` over `P`. -/
@[stacks 085L "Z ≅ Proj_X(𝒜/ℐ) over P for π quasi-compact, ℐ the kernel of \
𝒜 ⟶ ⨁_{d ≥ 0} π_*((i_*𝒪_Z)(d))"]
theorem exists_iso_quotientProjHom_psiKernelGradedIdeal
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom) :
    (∀ (d : ℕ) (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
        (x : (s.algebra.piece (d : ℤ)).val.obj V),
        x ∈ ((psiKernelGradedIdeal s Px i hi hπ).piece (d : ℤ)).obj V ↔
          (psiKernelMap s Px i d (s.psiTwistHom Px d)).val.app V x = 0) ∧
      ∃ e : Z ≅ (psiKernelGradedIdeal s Px i hi hπ).quotientSituation.Proj,
        e.hom ≫ (psiKernelGradedIdeal s Px i hi hπ).quotientProjHom = i := by
  refine ⟨fun d V x => mem_psiKernelPiece_iff s Px i (fun d => s.psiTwistHom Px d) d V x, ?_⟩
  have := RelativeProjSituation.quasiCompact_relativeProj_toBase hπ Px.U Px.toSpace
  have hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) Px.toSpace).hom :=
    isEtale_of_presheaf_etale s.site s.base s.containsBase Px.etale
  exact RelativeProjSituation.exists_iso_quotientProjHom_of_chart
    (psiKernelGradedIdeal s Px i hi hπ) i hi Px.U Px.toSpace Px.etale Px.surjective
    fun n W a => (mem_twistKerGradedIdeal_iff_mem_psiKernelGradedIdeal s Px i hi hπ n hf W a).trans
      ((psiKernelGradedIdeal s Px i hi hπ).quotientHomPoints_app_eq_zero_iff Px.toSpace hf n W
        a).symm

end AlgebraicGeometry.Space.C1359Bridge

end
