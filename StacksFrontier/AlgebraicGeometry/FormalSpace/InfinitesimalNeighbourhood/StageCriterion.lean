module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumHomEquiv
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.ReductionIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.StagePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite

/-!
# Which stages of a formal spectrum a point over an affine scheme factors through

Let `A` be a weakly admissible topological ring with quotient system `D`. A point of `Spf A` over
an affine object `T` of the site comes from a morphism `g` from `T` to a stage `Spec(A/J)`, and
its restriction along `h : T' ⟶ T` factors through the stage `Spec(A/L)` exactly when the
composite `T' ⟶ Spec(A/J) ⟶ Spec A` factors through the closed immersion `Spec(A/L) ⟶ Spec A`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.stageIncl`: the inclusion of a stage into the formal spectrum.
* `AlgebraicGeometry.FormalSpace.stageQuotientSpecMap`: the closed immersion `Spec(A/J) ⟶ Spec A`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_stage_hom`: a point over an affine object comes from a
  morphism to a stage.
* `AlgebraicGeometry.FormalSpace.stage_factor_iff`: the criterion for a restricted point to factor
  through a given stage.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- A point of `Spf A` over an affine object, as a morphism out of the sheafified representable,
comes from a morphism of the site to a stage. -/
theorem exists_stage_hom (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (y : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ formalSpectrum D) :
    ∃ (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (g : T ⟶ D.stageObj J),
      y = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
        formalSpectrumInclusion D (OrderDual.toDual J) := by
  let Jt := BigFppfOver.topology B S hS
  have : Jt.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨J, x', hx'⟩ := exists_factor_formalSpectrumInclusion hA D T
    (uliftYonedaEquiv.symm (Sheaf.sectionEquiv Jt y))
  let e' := uliftYonedaEquiv x'
  obtain ⟨g, hg⟩ : ∃ g : T ⟶ D.stageObj (OrderDual.ofDual J),
      (Sheaf.sheafifiedYoneda Jt).map g = (Sheaf.sectionEquiv Jt).symm e' :=
    ⟨(Sheaf.sheafifiedYoneda Jt).preimage _, (Sheaf.sheafifiedYoneda Jt).map_preimage _⟩
  refine ⟨OrderDual.ofDual J, g, ?_⟩
  apply (Sheaf.sectionEquiv Jt).injective
  have h1 := congrArg uliftYonedaEquiv hx'
  rw [Equiv.apply_symm_apply] at h1
  change Sheaf.sectionEquiv Jt y = (formalSpectrumInclusion D J).hom.app _ e' at h1
  have h2 : Sheaf.sectionEquiv Jt ((Sheaf.sheafifiedYoneda Jt).map g) = e' := by
    rw [hg]
    exact Equiv.apply_symm_apply _ _
  exact (h1.trans (congrArg _ h2.symm)).trans (Sheaf.sectionEquiv_comp Jt _ _).symm

/-- The stage `Spec(A/J) ⟶ Spf A` of a formal spectrum, out of the sheafified representable of
the stage object. -/
abbrev stageIncl (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (D.stageObj J) ⟶
      formalSpectrum D :=
  formalSpectrumInclusion D (OrderDual.toDual J)

/-- The closed immersion `Spec(A/J) ⟶ Spec A` out of the scheme of a stage. -/
abbrev stageQuotientSpecMap (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (BigFppfOver.toScheme B S hS).obj (D.stageObj J) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))

/-- A point of `Spf A` over `T` given by a morphism
`g` to the stage `Spec(A/J)` restricts along `h : T' ⟶ T` to a point factoring through the stage
`Spec(A/L)` exactly when the composite `T' ⟶ Spec(A/J) ⟶ Spec A` factors through
`Spec(A/L) ⟶ Spec A`. -/
theorem stage_factor_iff (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) {T T' : BigFppfOver B S hS}
    (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (g : T ⟶ D.stageObj J) (h : T' ⟶ T) :
    (∃ z : T' ⟶ D.stageObj L,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map z ≫ stageIncl D L =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (h ≫ g) ≫ stageIncl D J) ↔
      ∃ l : (BigFppfOver.toScheme B S hS).obj T' ⟶
          (BigFppfOver.toScheme B S hS).obj (D.stageObj L),
        l ≫ stageQuotientSpecMap D L =
          (BigFppfOver.toScheme B S hS).map (h ≫ g) ≫ stageQuotientSpecMap D J := by
  let Jt := BigFppfOver.topology B S hS
  have : Jt.Subcanonical := bigFppfOver_subcanonical B S hS
  let q := BigFppfOver.toScheme B S hS
  let F := Sheaf.sheafifiedYoneda Jt
  let M : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨J.1 ⊓ L.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 L.2.1⟩
  have hMJ : M.1 ≤ J.1 := inf_le_left
  have hML : M.1 ≤ L.1 := inf_le_right
  have : Mono (stageIncl D M) :=
    mono_formalSpectrumInclusion_of_isWeaklyAdmissible hA D (OrderDual.toDual M)
  have : Mono (stageQuotientSpecMap D M) := by
    have := _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom
      (Ideal.Quotient.mk M.1)) Ideal.Quotient.mk_surjective
    change Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk M.1)))
    infer_instance
  let tJ : D.stageObj J ⟶ D.stageObj M := (BigAffineFppf.inclusion B S hS).map
    (D.transition hMJ)
  let tL : D.stageObj L ⟶ D.stageObj M := (BigAffineFppf.inclusion B S hS).map
    (D.transition hML)
  have hsJ : q.map tJ ≫ stageQuotientSpecMap D M = stageQuotientSpecMap D J := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  have hsL : q.map tL ≫ stageQuotientSpecMap D M = stageQuotientSpecMap D L := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  have hiJ : F.map tJ ≫ stageIncl D M = stageIncl D J := sheafifiedYoneda_map_transition D hMJ
  have hiL : F.map tL ≫ stageIncl D M = stageIncl D L := sheafifiedYoneda_map_transition D hML
  have key : ∀ (a : T' ⟶ D.stageObj J) (b : T' ⟶ D.stageObj L),
      F.map b ≫ stageIncl D L = F.map a ≫ stageIncl D J ↔
        q.map b ≫ stageQuotientSpecMap D L = q.map a ≫ stageQuotientSpecMap D J := by
    intro a b
    rw [← hiJ, ← hiL, ← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp,
      cancel_mono, F.map_injective.eq_iff, ← hsJ, ← hsL, ← Category.assoc, ← Category.assoc,
      ← q.map_comp, ← q.map_comp, cancel_mono, q.map_injective.eq_iff]
  refine ⟨fun ⟨z, hz⟩ ↦ ⟨q.map z, (key (h ≫ g) z).1 hz⟩, fun ⟨l, hl⟩ ↦ ?_⟩
  have hl' : l ≫ q.map tL = q.map (h ≫ g ≫ tJ) := by
    apply (cancel_mono (stageQuotientSpecMap D M)).1
    rw [Category.assoc, hsL, hl, ← Category.assoc h, q.map_comp (h ≫ g) tJ, Category.assoc, hsJ]
  obtain ⟨z, hz⟩ := exists_siteHom_of_toScheme_comp_eq tL (h ≫ g ≫ tJ) l hl'
  refine ⟨z, (key (h ≫ g) z).2 ?_⟩
  rw [← hsL, ← Category.assoc, ← q.map_comp, hz, ← hsJ, ← Category.assoc h, q.map_comp (h ≫ g) tJ,
    Category.assoc]

end AlgebraicGeometry.FormalSpace

end
