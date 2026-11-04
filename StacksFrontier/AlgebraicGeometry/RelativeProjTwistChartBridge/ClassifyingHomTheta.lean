module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaTagShape
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ClassifyingData

/-!
# The two spellings of `r_{d, ℒ, ψ}` agree

The morphism `T ⟶ U_d` that a class in `F_d(T)` defines is characterised chart by chart over
the affine opens of the base, and each chart-wise morphism factors through the chart
`Proj Γ(U, 𝒜) ⟶ X`. Hence an isomorphism between two relative homogeneous spectra of `𝒜` that is
compatible with the charts carries the morphism a class defines into one of them to the morphism
it defines into the other.

Applied to the canonical isomorphism of [Stacks, Tag 01NZ] from `Proj_S(𝒜)` to the relative
homogeneous spectrum of a `Stacks.RelativeProj.Situation`, this identifies the morphism
`...RelativeProjQuadrupleTilde.classifyingHom` a quadruple classifies with the morphism
`...RelativeProjTwistChartBridge.thetaMorphism` of [Stacks, Tag 01O1], followed by that
isomorphism.

## Main results

* `...RelativeProjTwistChartBridge.homDegreeOpen_ι_comp_iso_hom`: a chart-compatible isomorphism
  of relative homogeneous spectra carries the morphism a class defines to the morphism it defines.
* `...RelativeProjTwistChartBridge.classifyingHom_eq_thetaMorphism_comp`: the classifying morphism
  of a situation is `r_{d, ℒ, ψ}` followed by the canonical isomorphism.
* `...RelativeProjTwistChartBridge.classifyingHom_eq_homEquiv_symm_comp`: it is the morphism the
  representability of `F` gives, followed by the canonical isomorphism.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

section Transport

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) {k : ℕ}

/-- **A chart-compatible isomorphism carries the morphism a class defines to the morphism it
defines.** Let `Q` and `P` be relative homogeneous spectra of `𝒜` and `e : Q ≅ P` an isomorphism
compatible with their charts over the affine opens of `S`. For a class `ξ ∈ F_k(W)`, the morphism
into `U_k ⊆ Q` that `ξ` defines, followed by `e`, is the morphism into `U_k ⊆ P` that `ξ` defines.

Over the preimage of an affine open `U` of the base both are the chart-wise morphism of the
chart-wise class, which factors through the chart of `U` (`...Fd.chartHom_eq_comp`), and `e`
carries the chart of `Q` to the chart of `P`. -/
theorem homDegreeOpen_ι_comp_iso_hom (Q P : RelativeProjData A) (e : Q.scheme ≅ P.scheme)
    (he : ∀ U : S.affineOpens, Q.chart U.1 U.2 ≫ e.hom = P.chart U.1 U.2) (hk : 0 < k)
    {W : Scheme.{u}} (ξ : Fd (situationAlgebra A) (k : ℤ) W) :
    Fd.homDegreeOpen A Q hk ξ ≫ (Q.degreeOpen k).ι ≫ e.hom =
      Fd.homDegreeOpen A P hk ξ ≫ (P.degreeOpen k).ι := by
  classical
  choose η hη using fun U : S.Opens =>
    Fd.exists_chartClassInv_eq A U (Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ) (ξ.1 ∣_ U)
      (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ U)
  obtain ⟨ψ₀, -, huniq⟩ := Scheme.existsUnique_hom_of_opens_cover
    (fun a : {U : S.Opens // IsAffineOpen U} => ξ.1 ⁻¹ᵁ a.1)
    (fun x => exists_mem_preimage_affineOpen ξ.1 x)
    (fun a => (ξ.1 ⁻¹ᵁ a.1).ι ≫ Fd.homDegreeOpen A P hk ξ ≫ (P.degreeOpen k).ι)
    (fun a b => by
      show (W.homOfLE (inf_le_left : (ξ.1 ⁻¹ᵁ a.1) ⊓ (ξ.1 ⁻¹ᵁ b.1) ≤ _)
            ≫ (ξ.1 ⁻¹ᵁ a.1).ι) ≫ Fd.homDegreeOpen A P hk ξ ≫ (P.degreeOpen k).ι
        = (W.homOfLE (inf_le_right : (ξ.1 ⁻¹ᵁ a.1) ⊓ (ξ.1 ⁻¹ᵁ b.1) ≤ _)
            ≫ (ξ.1 ⁻¹ᵁ b.1).ι) ≫ Fd.homDegreeOpen A P hk ξ ≫ (P.degreeOpen k).ι
      rw [W.homOfLE_ι, W.homOfLE_ι])
  refine (huniq _ fun a => ?_).trans (huniq _ fun _ => rfl).symm
  obtain ⟨U, hU⟩ := a
  have key : ∀ R : RelativeProjData A, (ξ.1 ⁻¹ᵁ U).ι ≫ Fd.homDegreeOpen A R hk ξ ≫
      (R.degreeOpen k).ι = Fd.chartHom A U R hU hk _ (η U) := fun R =>
    Fd.ι_homDegreeOpen A R hk ξ U hU (η U) (hη U)
  have h := congrArg (· ≫ e.hom) (key Q)
  simp only [Category.assoc] at h
  rw [h, key P, Fd.chartHom_eq_comp, Fd.chartHom_eq_comp, Category.assoc, Category.assoc,
    he ⟨U, hU⟩]

end Transport

section Situation

variable (s : Stacks.RelativeProj.Situation.{u}) {T : Scheme.{u}} {f : T ⟶ s.base}

open RelativeProjQuadrupleTilde in
/-- **The classifying morphism of a situation is `r_{d, ℒ, ψ}` followed by the canonical
isomorphism.** For a quadruple `(f : T → S, d, ℒ, ψ)` of a `Stacks.RelativeProj.Situation` with
`d ≥ 1`, the morphism `...RelativeProjQuadrupleTilde.classifyingHom` into the situation's relative
homogeneous spectrum is the morphism `thetaMorphism` of [Stacks, Tag 01O1] into `Proj_S(𝒜)`
followed by the canonical isomorphism of [Stacks, Tag 01NZ] from `Proj_S(𝒜)` to the situation's
relative homogeneous spectrum. -/
theorem classifyingHom_eq_thetaMorphism_comp {n : ℕ} (hn : 0 < n)
    (P : Quadruple f s.algebra (n : ℤ)) :
    classifyingHom s (by exact_mod_cast hn) P =
      thetaMorphism (A := sheafGradedAlgebra s) hn P ≫
        (canonicalIso (sheafGradedAlgebra s) (relativeProjData s)).hom := by
  show _ = (Fd.homDegreeOpen (sheafGradedAlgebra s) (relativeProj _) hn (Fd.mk f P) ≫
    ((relativeProj (sheafGradedAlgebra s)).degreeOpen n).ι) ≫ _
  exact (homDegreeOpen_ι_comp_iso_hom (sheafGradedAlgebra s) (relativeProj _)
    (relativeProjData s) (canonicalIso _ _)
    (fun U => chart_comp_canonicalIso_hom _ (relativeProjData s) U) hn (Fd.mk f P)).symm.trans
      (Category.assoc _ _ _).symm

open RelativeProjQuadrupleTilde in
/-- **The classifying morphism of a situation is the morphism the representability of `F` gives,
followed by the canonical isomorphism**: the image of the class of the quadruple under the
representation of the functor `F` of the display 01NX by `Proj_S(𝒜)` of [Stacks, Tag 01NZ], then
the canonical isomorphism from `Proj_S(𝒜)` to the situation's relative homogeneous spectrum. -/
theorem classifyingHom_eq_homEquiv_symm_comp {n : ℕ} (hn : 0 < n)
    (P : Quadruple f s.algebra (n : ℤ)) :
    classifyingHom s (by exact_mod_cast hn) P =
      (relativeProjRepresentableByFunctorUnconditional (sheafGradedAlgebra s)).homEquiv.symm
          (RelativeProjInvertibleMorphism.F.toLim (sheafGradedAlgebra s)
            (F.mk f (by exact_mod_cast hn) P)) ≫
        (canonicalIso (sheafGradedAlgebra s) (relativeProjData s)).hom :=
  (classifyingHom_eq_thetaMorphism_comp s hn P).trans
    (congrArg (· ≫ (canonicalIso (sheafGradedAlgebra s) (relativeProjData s)).hom)
      (thetaMorphism_eq_homEquiv_symm (A := sheafGradedAlgebra s) hn P))

end Situation

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
