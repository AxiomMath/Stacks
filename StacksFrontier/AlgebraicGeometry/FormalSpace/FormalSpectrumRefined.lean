module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import all StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum

/-!
# The affine formal spectrum (Stacks 0AIF): refined forms

The module for strengthened forms, under primed names, of results of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum`; a result whose statement is
strengthened keeps its original statement in that module. It holds no declarations yet.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Filter

namespace AlgebraicGeometry.FormalSpace

universe u


attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]

variable {C : Type u} [CommRing C] [TopologicalSpace C]

end AlgebraicGeometry.FormalSpace

end
