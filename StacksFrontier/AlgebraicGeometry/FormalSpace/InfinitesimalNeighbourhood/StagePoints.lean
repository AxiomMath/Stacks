module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitStageFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact

/-!
# Points of a formal spectrum over an affine scheme factor through a stage

Let `A` be a weakly admissible topological ring over `S` with quotient system `D`. A point of the
formal spectrum `Spf A = colim_J Spec(A/J)` over an affine object `T` of the site factors through
one of the stages `Spec(A/J)` (Stacks 0AIA).

## Main definitions

* `AlgebraicGeometry.FormalSpace.liftedFormalSpectrumDiagram`: the diagram of quotient spectra
  with its index lifted by one universe.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_factor_formalSpectrumInclusion`: the factorization.

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

/-- The diagram of quotient spectra of a quotient system, with its index lifted to the universe
in which presentations of affine formal algebraic spaces are indexed. -/
abbrev liftedFormalSpectrumDiagram (D : QuotientSystem B S hS A) :
    ULift.{u + 1} (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) ⥤
      FppfSheaf B S hS :=
  (OrderIso.equivalence
    ({ toEquiv := Equiv.ulift.symm, map_rel_iff' := Iff.rfl } :
      OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } ≃o
        ULift.{u + 1} (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }))
    ).inverse ⋙ formalSpectrumDiagram D

/-- A point of `Spf A` over an affine object of the site factors through a stage `Spec(A/J)`. -/
theorem exists_factor_formalSpectrumInclusion (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (x : uliftYoneda.{u + 1}.obj T ⟶ (formalSpectrum D).obj) :
    ∃ (J : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (x' : uliftYoneda.{u + 1}.obj T ⟶ ((formalSpectrumDiagram D).obj J).obj),
      x = x' ≫ (formalSpectrumInclusion D J).hom := by
  classical
  let I₀ := { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }
  let I := ULift.{u + 1} (OrderDual I₀)
  let eOrder : OrderDual I₀ ≃o I := { toEquiv := Equiv.ulift.symm, map_rel_iff' := Iff.rfl }
  let eI : OrderDual I₀ ≌ I := eOrder.equivalence
  have : Nonempty I := ⟨ULift.up ⟨hA.1.choose, hA.1.choose_spec⟩⟩
  have : IsDirected I (· ≤ ·) := ⟨fun i j => by
    refine ⟨ULift.up ⟨i.down.1 ⊓ j.down.1,
      ⟨i.down.2.1.inter j.down.2.1, fun x hx => i.down.2.2 x hx.1⟩⟩, ?_, ?_⟩
    · exact (inf_le_left : i.down.1 ⊓ j.down.1 ≤ i.down.1)
    · exact (inf_le_right : i.down.1 ⊓ j.down.1 ≤ j.down.1)⟩
  let E : I ⥤ FppfSheaf B S hS := eI.inverse ⋙ formalSpectrumDiagram D
  have hthick : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom := fun i j g =>
    isRepresentableThickeningULift_sheafifiedYoneda_map B S hS _
      (D.isThickening_map_diagram (eI.inverse.map g))
  let p := colimit.pre (formalSpectrumDiagram D) eI.inverse
  obtain ⟨i, ξ', hξ'⟩ := exists_factor_through_stage_of_isQuasiCompactObject B S hS E hthick T
    (isQuasiCompactObject_over_of_compact_scheme B S hS T) (x ≫ (inv p).hom)
  refine ⟨eI.inverse.obj i, ξ', ?_⟩
  have h1 : (inv p).hom ≫ p.hom = 𝟙 _ := by
    show (sheafToPresheaf (BigFppfOver.topology B S hS) _).map (inv p) ≫
      (sheafToPresheaf (BigFppfOver.topology B S hS) _).map p = 𝟙 _
    rw [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  have h2 : (colimit.ι E i).hom ≫ p.hom = (formalSpectrumInclusion D (eI.inverse.obj i)).hom := by
    show (sheafToPresheaf (BigFppfOver.topology B S hS) _).map (colimit.ι E i) ≫
      (sheafToPresheaf (BigFppfOver.topology B S hS) _).map p = _
    rw [← Functor.map_comp, colimit.ι_pre]
    rfl
  have hx : (x ≫ (inv p).hom) ≫ p.hom = x :=
    (Category.assoc x _ _).trans ((congrArg (x ≫ ·) h1).trans (Category.comp_id x))
  exact hx.symm.trans ((congrArg (· ≫ p.hom) hξ').trans
    ((Category.assoc _ _ _).trans (congrArg (ξ' ≫ ·) h2)))

end AlgebraicGeometry.FormalSpace

end
