module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterionOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimit

/-!
# Global functions on the limit of a system bounded by the cutoff

Stacks 07SI for the structure sheaf says that the ring of global functions of the limit of a
directed inverse system of quasi-compact and quasi-separated algebraic spaces with affine
transition morphisms is the filtered colimit of the rings of global functions of the stages.
The library proves it as `AlgebraicGeometry.Space.isStagesColimit_globalFunctions_of_isLimit`
for an index set smaller than the cofinality of the site's cutoff. This file proves it for a
system bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no
condition on the cofinality.

## Main results

* `AlgebraicGeometry.Space.isStagesColimit_globalFunctions_of_isLimit_of_isCutoffBoundedSystem`:
  Stacks 07SI for the structure sheaf, for a system bounded by the cutoff.
* `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit_of_isCutoffBoundedSystem`:
  the same for a descent situation.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 07SI for the structure sheaf, for a system bounded by the cutoff.** Let `D` be an
inverse system, over a nonempty directed set `I`, of quasi-compact and quasi-separated algebraic
spaces over `S` with affine transition morphisms, bounded by the cutoff, and let `c` be a limit
cone of `D` whose vertex is an algebraic space. Then the ring of global functions of the limit is
the filtered colimit of the rings of global functions of the stages, in the elementwise form
`Stacks.IsStagesColimit`. -/
theorem isStagesColimit_globalFunctions_of_isLimit_of_isCutoffBoundedSystem
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hDc : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hDqc : ∀ i : I, IsQuasiCompactSpace B S hS (D.obj (op i)))
    (hDqs : ∀ i : I, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i)))
    (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hc' : IsAlgebraicSpace B S hS c.pt) :
    Stacks.IsStagesColimit (G := fun i : I => globalFunctions' B S hS (D.obj (op i)))
      (T := globalFunctions' B S hS c.pt)
      (fun i j h x => globalFunctionsMap B S hS (U := ⟨D.obj (op i), hDalg i⟩)
        (V := ⟨D.obj (op j), hDalg j⟩) (ObjectProperty.homMk (D.map (homOfLE h).op)) x)
      (fun i x => globalFunctionsMap B S hS (U := ⟨D.obj (op i), hDalg i⟩)
        (V := ⟨c.pt, hc'⟩) (ObjectProperty.homMk (c.π.app (op i))) x) := by
  have hT := baseTerminal_yonedaIsTerminal B S hS
  have hφ : RelativelyLimitPreserving.{u, u, u, u} B S hS (yoneda.map (affineLineToBase B S hS)) :=
    relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS
      (affineLineSpace B S hS).property (terminalSpace B S hS).property
      (isLocallyOfFinitePresentation_affineLineToBase B S hS)
  refine ⟨fun i j h x => ?_, fun t => ?_, fun i s s' hss => ?_⟩
  · rw [← RingHom.comp_apply, ← globalFunctionsMap_comp]
    congr 2
    exact ObjectProperty.hom_ext _ (c.w (homOfLE h).op)
  · let g := globalFunctionsHomEquiv B S hS ⟨c.pt, hc'⟩ t
    let i₀ : I := Classical.arbitrary I
    obtain ⟨j, -, z, hlim, -⟩ :=
      exists_stage_lift_of_relativelyLimitPreserving_of_isCutoffBoundedSystem B S hS hZ D hDc
        (fun i => hDalg i.unop) (fun i => hDqc i.unop) (fun i => hDqs i.unop) hDaff hc
        (affineLineSpace B S hS).property (terminalSpace B S hS).property hφ (op i₀) g.hom
        (hT.from _) (hT.hom_ext _ _)
    refine ⟨j.unop, (globalFunctionsHomEquiv B S hS ⟨D.obj j, hDalg j.unop⟩).symm
      (ObjectProperty.homMk z), ?_⟩
    apply (globalFunctionsHomEquiv B S hS ⟨c.pt, hc'⟩).injective
    rw [globalFunctionsHomEquiv_natural, Equiv.apply_symm_apply]
    exact ObjectProperty.hom_ext _ hlim
  · have hlim :
        c.π.app (op i) ≫ (globalFunctionsHomEquiv B S hS ⟨D.obj (op i), hDalg i⟩ s).hom =
          c.π.app (op i) ≫ (globalFunctionsHomEquiv B S hS ⟨D.obj (op i), hDalg i⟩ s').hom := by
      have h₁ := globalFunctionsHomEquiv_natural B S hS (U := ⟨D.obj (op i), hDalg i⟩)
        (V := ⟨c.pt, hc'⟩) (ObjectProperty.homMk (c.π.app (op i))) s
      have h₂ := globalFunctionsHomEquiv_natural B S hS (U := ⟨D.obj (op i), hDalg i⟩)
        (V := ⟨c.pt, hc'⟩) (ObjectProperty.homMk (c.π.app (op i))) s'
      exact congrArg (fun f => f.hom)
        (h₁.symm.trans ((congrArg (globalFunctionsHomEquiv B S hS ⟨c.pt, hc'⟩) hss).trans h₂))
    obtain ⟨k, a, hk⟩ :=
      exists_stage_eq_of_relativelyLimitPreserving_of_isCutoffBoundedSystem B S hS hZ D hDc
        (fun i => hDalg i.unop) (fun i => hDqc i.unop) (fun i => hDqs i.unop) hDaff hc
        (affineLineSpace B S hS).property hφ (op i) _ _ hlim (op i) (𝟙 _) (hT.hom_ext _ _)
    refine ⟨k.unop, leOfHom a.unop, ?_⟩
    apply (globalFunctionsHomEquiv B S hS ⟨D.obj k, hDalg k.unop⟩).injective
    rw [globalFunctionsHomEquiv_natural, globalFunctionsHomEquiv_natural]
    refine ObjectProperty.hom_ext _ ?_
    have ha : (homOfLE (leOfHom a.unop)).op = a := Subsingleton.elim _ _
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, ha]
    exact hk

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **Stacks 07SI for the structure sheaf, in a descent situation bounded by the cutoff.** The
ring of global functions of the limit of a descent situation whose system is bounded by the
cutoff is the filtered colimit of the rings of global functions of the stages. -/
theorem isGlobalFunctionsColimit_of_isCutoffBoundedSystem
    (hD : IsCutoffBoundedSystem B S hS D.system) : D.IsGlobalFunctionsColimit :=
  have : Nonempty I := ⟨D.base⟩
  isStagesColimit_globalFunctions_of_isLimit_of_isCutoffBoundedSystem B S hS hZ D.system
    D.limitCone D.isLimit hD D.algebraicSpace D.quasiCompact D.quasiSeparated
    D.transition_affine D.limitAlgebraicSpace

end DescentSituation

end AlgebraicGeometry.Space

end
