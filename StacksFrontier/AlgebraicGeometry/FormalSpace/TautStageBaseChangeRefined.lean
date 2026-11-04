module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
import all StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange

/-!
# Base change of a morphism of formal spectra along a thickening stage: the refined forms

Refined forms of the results on the base change of a morphism of formal spectra along a
thickening stage, complementing `StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe w₂ w₁ v u

section Bridges

end Bridges

section WeakIdealIndex

variable {R : Type u} [CommRing R] [TopologicalSpace R]

end WeakIdealIndex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section StageInclusion

variable {R : Type u} [CommRing R] [TopologicalSpace R]

end StageInclusion

section IdealComparison

variable {R : Type u} [CommRing R] [TopologicalSpace R]

end IdealComparison

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]

variable [IsTopologicalRing C] [IsLinearTopology C C]

end AlgebraicGeometry.FormalSpace

end
