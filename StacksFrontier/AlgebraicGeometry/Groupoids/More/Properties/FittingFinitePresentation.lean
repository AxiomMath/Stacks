module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteStratification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite

/-!
# Finite presentation of the Fitting stratification of a finite groupoid

Let `G` be a groupoid scheme whose source map is finite and of finite presentation. Then the
direct image of the structure sheaf of the arrow scheme is a finitely presented module on the
object scheme, so each of its Fitting ideals is finitely generated on every affine open, and
each closed subscheme of the Fitting stratification of `G` is of finite presentation over the
object scheme.

## Main results

* `Stacks.Groupoids.isFinitePresentation_pushforwardStructureSheaf_source`: the direct image of
  the structure sheaf along a finite source map of finite presentation is finitely presented.
* `Stacks.Groupoids.finitePresentation_finiteStratification_subschemeι`: each member of the
  Fitting stratification is of finite presentation.

## Implementation notes

Finite presentation of the closed immersion is reduced to finite generation of the defining
ideal on every affine open by `Stacks.Flatness.finitePresentation_subschemeι_iff`, and the
ideal there is the module-theoretic Fitting ideal of the sections by
`Stacks.Fitting.ideal_idealSheaf_pushforward`, which is available because the source map is
finite.

## References

* [Stacks Project, Tag 0ABA](https://stacks.math.columbia.edu/tag/0ABA)
* [Stacks Project, Tag 05P8](https://stacks.math.columbia.edu/tag/05P8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace Stacks.Groupoids

/-- For a finite source map of finite presentation, the direct image of the structure sheaf of
the arrow scheme is a finitely presented module on the object scheme. -/
theorem isFinitePresentation_pushforwardStructureSheaf_source {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left]
    (hG : FinitePresentation G.source.left) :
    (Morphisms.pushforwardStructureSheaf G.source.left).IsFinitePresentation :=
  (isFinitePresentation_iff_pushforward_isFinitePresentation G.source.left hG
    (SheafOfModules.unit G.arrows.left.ringCatSheaf)).mp inferInstance

/-- Each closed subscheme of the Fitting stratification of a groupoid scheme with finite source
map of finite presentation is of finite presentation over the object scheme. -/
theorem finitePresentation_finiteStratification_subschemeι {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left]
    (hG : FinitePresentation G.source.left) (r : ℕ) :
    FinitePresentation (finiteStratification G r).subschemeι := by
  have hF : (Morphisms.pushforwardStructureSheaf G.source.left).IsFinitePresentation :=
    isFinitePresentation_pushforwardStructureSheaf_source G hG
  refine (Stacks.Flatness.finitePresentation_subschemeι_iff _).mpr fun U ↦ ?_
  have hfp : Module.FinitePresentation Γ(G.objects.left, U.1)
      Γ(Morphisms.pushforwardStructureSheaf G.source.left, U.1) :=
    finitePresentation_sections_on_affine _ U
  rw [finiteStratification, Fitting.ideal_idealSheaf_pushforward]
  exact (fittingIdeal_basic_properties.{u, u, u, u}
    (R := Γ(G.objects.left, U.1))
    (M := Γ(Morphisms.pushforwardStructureSheaf G.source.left, U.1))).2.2.2.1 hfp r

end Stacks.Groupoids

end
