module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeDegreeVanishing

/-!
# The corner of a Grothendieck spectral sequence, without a spectral sequence

Let `G : D⁺(𝒞) ⥤ D(𝒟)` be a triangulated functor such that `Hʲ(G(M[-q])) = 0` for every object
`M` of `𝒞` as soon as `j - q > m`, and let `K` be a bounded below complex with no cohomology in
degrees above `b`. The spectral sequence `E₂^{p,q} = Hᵖ(G(H^q(K))) ⟹ H^{p+q}(G K)` then has only
one nonzero term on the antidiagonal `p + q = m + b`, namely `E₂^{m,b}`, and no differential
reaches or leaves it, so `H^{m+b}(G K) ≅ H^{m+b}(G(H^b(K)[-b]))`.

This file proves that directly, from the truncation triangle `τ_{≤ b-1} K → K → τ_{≥ b} K` and
`Stacks.CompositeDegreeVanishing.isZero_homology_map_obj_of_bounded` for its first term, in the
two degrees `m + b` and `m + b + 1`. It is the form in which the Leray spectral sequence of a
family of curves `f : U → S` computes top-degree compactly supported cohomology:
`H^{2e}_c(U) = H^{2e-2}_c(S, R²f_! Λ)` (`m = 2(e - 1)`, `b = 2`).

## Main results

* `Stacks.CompositeDegreeVanishing.isIso_homology_map_truncGEπ_of_isLE`: the map induced by
  `K → τ_{≥ b} K` on `H^{m+b}(G -)` is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.CompositeDegreeVanishing

variable {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  (G : DerivedCategory.Plus C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]

/-- **The corner of the spectral sequence of `G`.** If `Hʲ(G(M[-q])) = 0` whenever `j - q > m`,
and `K` lives in the degrees `[a, b]`, then `K → τ_{≥ b} K` induces an isomorphism
`H^{m+b}(G K) ≅ H^{m+b}(G(τ_{≥ b} K))`: the first term `τ_{≤ b-1} K` of the truncation triangle has
no `H^{m+b}(G -)` and no `H^{m+b+1}(G -)`. -/
theorem isIso_homology_map_truncGEπ_of_isLE (m : ℤ)
    (hG : ∀ (M : C) (q j : ℤ), m < j - q →
      IsZero ((DerivedCategory.homologyFunctor D j).obj
        (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj M))))
    (K : DerivedCategory.Plus C) (a : ℕ) (b : ℤ) (hK : K.IsGE (b - 1 - a)) [K.IsLE b] :
    IsIso ((DerivedCategory.homologyFunctor D (m + b)).map
      (G.map ((DerivedCategory.Plus.TStructure.t.truncGEπ b).app K))) := by
  let t : CategoryTheory.Triangulated.TStructure (DerivedCategory.Plus C) :=
    DerivedCategory.Plus.TStructure.t
  let T₀ := (t.triangleLEGE (b - 1) b (by omega)).obj K
  have hT₀ : T₀ ∈ distTriang (DerivedCategory.Plus C) :=
    t.triangleLEGE_distinguished (b - 1) b (by omega) K
  have hT : G.mapTriangle.obj T₀ ∈ distTriang (DerivedCategory D) := G.map_distinguished T₀ hT₀
  have hτGE : T₀.obj₁.IsGE (b - 1 - a) := by
    let : K.IsGE (b - 1 - a) := hK
    change ((t.truncLE (b - 1)).obj K).IsGE _
    infer_instance
  have hτLE : T₀.obj₁.IsLE (b - 1 - a + (a : ℕ)) :=
    t.isLE_truncLE_obj K (b - 1) _ (by omega)
  have hzero : ∀ j : ℤ, m + b ≤ j →
      IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj T₀.obj₁)) := fun j hj =>
    isZero_homology_map_obj_of_bounded G j (b - 1 - a) a T₀.obj₁ hτGE hτLE
      fun q _ hqb => hG _ q j (by omega)
  have hmono : Mono ((DerivedCategory.homologyFunctor D (m + b)).map (G.mapTriangle.obj T₀).mor₂) :=
    (DerivedCategory.HomologySequence.exact₂ (G.mapTriangle.obj T₀) hT (m + b)).mono_g
      ((hzero (m + b) le_rfl).eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor D (m + b)).map (G.mapTriangle.obj T₀).mor₂) :=
    (DerivedCategory.HomologySequence.exact₃ (G.mapTriangle.obj T₀) hT (m + b) (m + b + 1)).epi_f
      ((hzero (m + b + 1) (by omega)).eq_of_tgt _ _)
  change IsIso ((DerivedCategory.homologyFunctor D (m + b)).map (G.mapTriangle.obj T₀).mor₂)
  exact isIso_of_mono_of_epi _

end Stacks.CompositeDegreeVanishing
