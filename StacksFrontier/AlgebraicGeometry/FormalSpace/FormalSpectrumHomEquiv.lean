module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum

/-!
# Morphisms out of a formal spectrum are compatible families of sections

The formal spectrum `Spf A = colim_J Spec (A ⧸ J)` of **Stacks 0AIF** is a colimit of
sheafified representables over the weak ideals of definition of `A`. Yoneda's lemma for
sheaves of sets turns a cocone on that diagram into a family of sections, so a morphism
`Spf A ⟶ F` into a sheaf of sets on the big fppf site is the same thing as a family of
sections of `F` over the quotient stages which is compatible with the transition maps.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsCompatibleStageFamily`: compatibility of a family of
  sections over the quotient stages with the transition maps of the system.
* `AlgebraicGeometry.FormalSpace.stageSection`: the restriction of a morphism out of the
  formal spectrum to a quotient stage, read as a section.
* `AlgebraicGeometry.FormalSpace.formalSpectrumHomEquiv`: the bijection between the morphisms
  out of the formal spectrum and the compatible families of sections.

## Main results

* `AlgebraicGeometry.FormalSpace.formalSpectrum_hom_ext`: two morphisms out of a formal
  spectrum which agree on every stage are equal.
* `AlgebraicGeometry.FormalSpace.isCompatibleStageFamily_stageSection`: the family of stage
  restrictions of a morphism is compatible.
* `AlgebraicGeometry.FormalSpace.stageSection_formalSpectrumHomEquiv_symm`: the morphism
  assembled from a compatible family restricts to that family.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The object of the big fppf site underlying the quotient stage of a weak ideal of
definition. -/
public abbrev QuotientSystem.stageObj (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (D.stage J)

/-- A family of sections of `F` over the quotient stages is *compatible* when the section at a
larger weak ideal of definition is the restriction, along the transition map, of the section at
a smaller one. -/
public def IsCompatibleStageFamily (D : QuotientSystem B S hS A)
    (F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (x : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      F.obj.obj (op (D.stageObj J))) : Prop :=
  ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) (h : J.1 ≤ L.1),
    F.obj.map ((BigAffineFppf.inclusion B S hS).map (D.transition h)).op (x J) = x L

variable (D : QuotientSystem B S hS A)
  (F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- Two morphisms out of a formal spectrum which restrict to the same morphism on every
quotient stage are equal. -/
public theorem formalSpectrum_hom_ext {g₁ g₂ : formalSpectrum D ⟶ F}
    (h : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      formalSpectrumInclusion D (OrderDual.toDual J) ≫ g₁ =
        formalSpectrumInclusion D (OrderDual.toDual J) ≫ g₂) :
    g₁ = g₂ :=
  colimit.hom_ext fun J => h J

/-- The restriction of a morphism out of the formal spectrum to the quotient stage of a weak
ideal of definition, read as a section by Yoneda's lemma for sheaves of sets. -/
public def stageSection (g : formalSpectrum D ⟶ F)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    F.obj.obj (op (D.stageObj J)) :=
  Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
    (formalSpectrumInclusion D (OrderDual.toDual J) ≫ g)

/-- The transition map of the system, represented, is the map of the diagram of quotient
stages. -/
public theorem sheafifiedYoneda_map_transition
    {J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }} (h : J.1 ≤ L.1) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.transition h)) ≫
      formalSpectrumInclusion D (OrderDual.toDual J) =
        formalSpectrumInclusion D (OrderDual.toDual L) :=
  colimit.w (formalSpectrumDiagram D) (homOfLE (OrderDual.toDual_le_toDual.mpr h))

/-- The family of stage restrictions of a morphism out of the formal spectrum is
compatible. -/
public theorem isCompatibleStageFamily_stageSection (g : formalSpectrum D ⟶ F) :
    IsCompatibleStageFamily D F (stageSection D F g) := fun J _L h =>
  (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS)
        ((BigAffineFppf.inclusion B S hS).map (D.transition h))
        (formalSpectrumInclusion D (OrderDual.toDual J) ≫ g)).symm.trans
    (congrArg (fun k => Sheaf.sectionEquiv (BigFppfOver.topology B S hS) k)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (sheafifiedYoneda_map_transition D h))))

/-- The cocone on the diagram of quotient stages attached to a compatible family of sections,
by Yoneda's lemma for sheaves of sets. -/
public def stageCocone
    {x : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      F.obj.obj (op (D.stageObj J))}
    (hx : IsCompatibleStageFamily D F x) : Cocone (formalSpectrumDiagram D) where
  pt := F
  ι :=
    { app := fun J ↦ (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm (x J)
      naturality := by
        intro J L f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          Functor.comp_map]
        refine (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective ?_
        rw [Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hx L J (leOfHom f) }

/-- The morphism out of the formal spectrum assembled from a compatible family restricts on
each quotient stage to the member of the family. -/
public theorem stageSection_desc_stageCocone
    {x : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      F.obj.obj (op (D.stageObj J))}
    (hx : IsCompatibleStageFamily D F x)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    stageSection D F (colimit.desc (formalSpectrumDiagram D) (stageCocone D F hx)) J = x J := by
  change Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (formalSpectrumInclusion D (OrderDual.toDual J) ≫
        colimit.desc (formalSpectrumDiagram D) (stageCocone D F hx)) = x J
  rw [colimit.ι_desc]
  exact Equiv.apply_symm_apply _ _

/-- **Morphisms out of a formal spectrum are compatible families of sections.** For a quotient
system of a topological ring `A` over `S` and a sheaf of sets `F` on the big fppf site over
`S`, restriction to the quotient stages is a bijection from the morphisms `Spf A ⟶ F` onto the
families of sections of `F` over the stages that are compatible with the transition maps. -/
public def formalSpectrumHomEquiv :
    (formalSpectrum D ⟶ F) ≃
      { x : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
          F.obj.obj (op (D.stageObj J)) // IsCompatibleStageFamily D F x } where
  toFun g := ⟨stageSection D F g, isCompatibleStageFamily_stageSection D F g⟩
  invFun x := colimit.desc (formalSpectrumDiagram D) (stageCocone D F x.2)
  left_inv g := by
    refine formalSpectrum_hom_ext D F fun J => ?_
    refine (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective ?_
    exact stageSection_desc_stageCocone D F (isCompatibleStageFamily_stageSection D F g) J
  right_inv x := Subtype.ext (funext fun J => stageSection_desc_stageCocone D F x.2 J)

/-- The family attached to a morphism out of the formal spectrum is its family of stage
restrictions. -/
public theorem formalSpectrumHomEquiv_apply (g : formalSpectrum D ⟶ F)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (formalSpectrumHomEquiv D F g).1 J = stageSection D F g J :=
  rfl

/-- The morphism out of the formal spectrum attached to a compatible family restricts on each
quotient stage to the member of the family. -/
public theorem stageSection_formalSpectrumHomEquiv_symm
    (x : { x : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
        F.obj.obj (op (D.stageObj J)) // IsCompatibleStageFamily D F x })
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    stageSection D F ((formalSpectrumHomEquiv D F).symm x) J = x.1 J :=
  stageSection_desc_stageCocone D F x.2 J

end AlgebraicGeometry.FormalSpace

end
