module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalDictionary
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageWitness

/-!
# The formal component at a stage from a continuous ring map

In the last part of the proof of Stacks 0GI5 the formal component `x̂ : V_{/Z} ⟶ W` of an element
over the limit `V = lim V_k` factors as `V_{/Z} ⟶ Spf B ⟶ W` through an étale chart, so it is a
continuous ring map `φ : B → A^∧`. This file reduces the construction of an element of `F(V_k)`
restricting to `ξ` to the construction of a continuous ring map `φ_k : B → A_k^∧` over `S` with
`φ = (A_k^∧ → A^∧) ∘ φ_k`, whose morphism `V_{k,/Z_k} ⟶ W` is adic and compatible with the stage
witness: the restriction to the limit is the naturality of the dictionary
(`AlgebraicGeometry.Artin.FormalDictionary.completionSheafRestrict_comp_continuousHomEquiv`).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.StageWitness.exists_mapTriple_eq_of_continuousHom`:
  the reduction.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

/-- The `I`-adic topology on the adic completion `A^∧` of `A` along `I`. -/
local instance instTopologicalSpaceAdicCompletion' {A : Type u} [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)
  {I : Type u} [Category.{u} I] {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D}
  {ξ : Triple c κ.pt.obj} {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat}

open FormalDictionary in
/-- **An element over the limit comes from the stage of a stage witness** as soon as the formal
component `x̂ = ω ∘ e⁻¹ ∘ Spf(φ)` of `ξ`, read through a chart `ω : Spf B ≅ W₀ ⟶ W`, is the
restriction of `ω ∘ e⁻¹ ∘ Spf(φ_k)` for a continuous ring map `φ_k : B → A_k^∧` over `S` with
`φ = (A_k^∧ → A^∧) ∘ φ_k`, whose morphism is adic and compatible with the stage witness. -/
theorem StageWitness.exists_mapTriple_eq_of_continuousHom {k : I} (W : StageWitness c κ ξ w k)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj k).obj)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (D.obj k).obj, ⊤)]
    {Iℓ : Ideal Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)}
    {Ik : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k).obj, ⊤)}
    (hZI : ∀ x, x ∈ ξ.Z ↔ Space.pointsToScheme B S hS κ.pt.obj x ∈
      ((BigFppfOver.toScheme B S hS).obj κ.pt.obj).zeroLocus
        (Iℓ : Set Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))
    (hZIk : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k).obj x ∈
      ((BigFppfOver.toScheme B S hS).obj (D.obj k).obj).zeroLocus
        (Ik : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k).obj, ⊤)))
    (hII : Ik.map ((BigFppfOver.toScheme B S hS).map (κ.π.app k).hom).appTop.hom ≤ Iℓ)
    {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
    [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
    {DB : FormalSpace.QuotientSystem B S hS Bt} {W₀ : FormalSpace.FppfSheaf B S hS}
    (e : W₀ ≅ FormalSpace.formalSpectrum DB) (ω : W₀ ⟶ c.W)
    (x₀ : Space.completionSheaf B S hS (yoneda.obj κ.pt.obj) ξ.Z ⟶ W₀) (hx₀ : x₀ ≫ ω = ξ.xhat)
    (φk : FormalSpace.ContinuousHom DB (completionQuotientSystem (D.obj k).obj Ik))
    (hφ : ((continuousHomEquiv hZI hB).symm (x₀ ≫ e.hom)).toRingHom =
      (completionRingHom ((BigFppfOver.toScheme B S hS).map (κ.π.app k).hom).appTop.hom
        hII).comp φk.toRingHom)
    (hadic : FormalSpace.IsAdicMorphism B S hS (continuousHomEquiv hZIk hB φk ≫ e.inv ≫ ω))
    (hformal : Space.completionSheafRestrict B S hS W.q (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z)
        W.Z (fun _ hz => hz) ≫ continuousHomEquiv hZIk hB φk ≫ e.inv ≫ ω =
      Space.completionSheafRestrict B S hS W.y (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z)
        c.T' W.subset_T' ≫ c.g) :
    ∃ t : Triple c (D.obj k).obj, mapTriple c (κ.π.app k).hom t = ξ := by
  refine W.exists_mapTriple_eq _ hadic hformal ?_
  have hnat := completionSheafRestrict_comp_continuousHomEquiv hZI hZIk (κ.π.app k).hom hII hB
    W.subset_preimage_Z φk ((continuousHomEquiv hZI hB).symm (x₀ ≫ e.hom)) hφ
  rw [Equiv.apply_symm_apply] at hnat
  rw [← Category.assoc, hnat, Category.assoc, Iso.hom_inv_id_assoc, hx₀]

end AlgebraicGeometry.Artin.ContractionSituation

end
