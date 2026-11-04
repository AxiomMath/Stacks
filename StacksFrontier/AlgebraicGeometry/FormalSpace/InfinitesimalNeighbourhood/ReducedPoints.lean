module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.StageCriterion
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal

/-!
# Reduced points of a formal spectrum factor through its reduction

Let `A` be a weakly admissible topological ring with quotient system `D` and let `𝔞` be its ideal
of topologically nilpotent elements. A point of `Spf A` over a reduced affine object of the site
factors through the stage `Spec(A/𝔞)`: it factors through some stage `Spec(A/J)`, and the image of
`𝔞` in `A/J` consists of nilpotent elements, which vanish in a reduced ring.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_factor_nilStage_of_isReduced`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- The weak ideal of definition of topologically nilpotent elements. -/
abbrev nilWeakIdeal (hA : IsWeaklyAdmissible A) :
    { I : Ideal A // IsWeakIdealOfDefinition I } :=
  ⟨topologicalNilradical A, isWeakIdealOfDefinition_topologicalNilradical hA.1⟩

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The kernel of `Spec(A/I) ⟶ Spec A` on global sections, read in `A`. -/
theorem mem_ker_specMap_quotient_appTop_iff (I : Ideal A) (ξ : Γ(Spec (.of A), ⊤)) :
    ξ ∈ RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom ↔
      (Scheme.ΓSpecIso (.of A)).hom ξ ∈ I := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop =
      (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        (Scheme.ΓSpecIso (.of (A ⧸ I))).inv := by
    rw [← Category.assoc, ← h]
    simp
  rw [RingHom.mem_ker, e]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1

/-- **Points of a formal spectrum over a reduced affine object factor through the reduction
stage.** -/
theorem exists_factor_nilStage_of_isReduced (hA : IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (hV : IsReduced ((BigFppfOver.toScheme B S hS).obj V))
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum D) :
    ∃ z : V ⟶ D.stageObj (nilWeakIdeal hA),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map z ≫
        stageIncl D (nilWeakIdeal hA) = x := by
  obtain ⟨J, g, rfl⟩ := exists_stage_hom hA D V x
  obtain ⟨z, hz⟩ := (stage_factor_iff hA D J (nilWeakIdeal hA) g (𝟙 V)).2 (by
    rw [Category.id_comp]
    have : _root_.AlgebraicGeometry.IsClosedImmersion (stageQuotientSpecMap D (nilWeakIdeal hA)) :=
      _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    refine (Scheme.exists_factor_iff_ker_appTop_le _ _).2 fun ξ hξ => ?_
    replace hξ := (mem_ker_specMap_quotient_appTop_iff _ ξ).1 hξ
    obtain ⟨n, hn⟩ := (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hξ
      ).exists_pow_mem_of_mem_nhds (J.2.1.mem_nhds J.1.zero_mem)
    have := hV
    have hnil : IsNilpotent
        (((BigFppfOver.toScheme B S hS).map g ≫ stageQuotientSpecMap D J).appTop ξ) := by
      refine ⟨n, ?_⟩
      rw [← map_pow]
      have : ξ ^ n ∈ RingHom.ker (stageQuotientSpecMap D J).appTop.hom := by
        refine (mem_ker_specMap_quotient_appTop_iff _ _).2 ?_
        rw [map_pow]; exact hn
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      rw [RingHom.mem_ker.mp this, map_zero]
    exact hnil.eq_zero)
  exact ⟨z, hz.trans (congrArg
    (fun k => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫ stageIncl D J)
    (Category.id_comp g))⟩

end AlgebraicGeometry.FormalSpace

end
