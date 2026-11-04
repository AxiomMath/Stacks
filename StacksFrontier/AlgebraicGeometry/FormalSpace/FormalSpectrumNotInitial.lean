module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# A formal spectrum with a nonzero quotient stage maps to no initial sheaf

Let `S` be a scheme contained in a big fppf site `B` and let `A` be a topological ring with a
quotient system over `S`. If some weak ideal of definition `J` of `A` is a proper ideal, then
`Spf A` is not an initial object of the category of fppf sheaves, and consequently no fppf sheaf
receiving a morphism from `Spf A` is initial.

The category of sheaves of sets is finitary extensive, so its initial objects are strict: a
morphism into an initial sheaf has an initial source. If `Spf A` were initial, so would be the
representable sheaf of its stage `Spec (A ⧸ J)`, which then maps to the representable sheaf of
the empty scheme; the fppf topology being subcanonical, that map comes from a morphism of schemes
`Spec (A ⧸ J) ⟶ ∅`, impossible as `A ⧸ J` is a nonzero ring.

This is the form in which the alternative "`X' = ∅`" of Stacks 0GD9 is excluded in the proof of
Stacks 0GDA: the flat part receives a point out of the formal spectrum of a complete discrete
valuation ring.

## Main results

* `AlgebraicGeometry.FormalSpace.not_isInitial_formalSpectrum`: `Spf A` is not initial.
* `AlgebraicGeometry.FormalSpace.not_isInitial_of_hom_formalSpectrum`: no fppf sheaf receiving a
  morphism from `Spf A` is initial.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The formal spectrum of a topological ring over `S` having a proper weak ideal of definition
`J` is not an initial fppf sheaf: its stage `Spec (A ⧸ J)` is a nonempty scheme, and an initial
sheaf would make that stage map to the empty scheme. -/
theorem not_isInitial_formalSpectrum (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) (hJ : J.1 ≠ ⊤) :
    IsInitial (formalSpectrum D) → False := by
  intro h
  have hstage : IsInitial ((formalSpectrumDiagram D).obj (OrderDual.toDual J)) :=
    IsInitial.ofStrict (formalSpectrumInclusion D (OrderDual.toDual J)) h
  let φ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.stage J)) ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (BigFppfOver.initialObj B S hS) :=
    hstage.to _
  let f := Sheaf.representingHom (J := BigFppfOver.topology B S hS) φ
  have : Nontrivial (A ⧸ J.1) := Ideal.Quotient.nontrivial_iff.mpr hJ
  obtain ⟨x⟩ : Nonempty (Spec (.of (A ⧸ J.1))) := inferInstance
  have hx : (∅ : Scheme.{u}) := ((BigFppfOver.toScheme B S hS).map f).base x
  exact IsEmpty.false hx

/-- No fppf sheaf over `S` receiving a morphism from the formal spectrum of a topological ring
with a proper weak ideal of definition is initial, initial objects of the category of sheaves of
sets being strict. -/
theorem not_isInitial_of_hom_formalSpectrum (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) (hJ : J.1 ≠ ⊤)
    {X : FppfSheaf B S hS} (r : formalSpectrum D ⟶ X) : IsInitial X → False :=
  fun h ↦ not_isInitial_formalSpectrum D J hJ (IsInitial.ofStrict r h)

end AlgebraicGeometry.FormalSpace

end
