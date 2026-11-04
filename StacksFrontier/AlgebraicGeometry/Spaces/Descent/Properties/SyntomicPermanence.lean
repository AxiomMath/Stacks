module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic

/-!
# Permanence of syntomicity along a surjective syntomic morphism of algebraic spaces

Let `p = f ≫ q` be a commuting triangle of morphisms of algebraic spaces over `S` with `f`
surjective and syntomic. If `p` is syntomic, then so is `q`. This is the syntomic case of
Stacks 0AHD; the smooth and étale cases are
`AlgebraicGeometry.Space.isSmooth_of_comp_surjective_isSmooth` and
`AlgebraicGeometry.Space.isEtale_of_comp_surjective_isEtale`.

## Main results

* `AlgebraicGeometry.Space.isSyntomic_of_comp_surjective_isSyntomic`: the syntomic case of
  Stacks 0AHD.

## Implementation notes

Syntomicity of a morphism of algebraic spaces is by definition the every-chart condition of
Stacks 03MJ, so the statement is a direct instance of the reduction
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_surjective` to schemes, where it is the
syntomic case of Stacks 02KM, `AlgebraicGeometry.syntomic_of_comp_surjective_syntomic`.

Inside the namespace `AlgebraicGeometry.Space` the scheme-morphism class
`AlgebraicGeometry.Syntomic` and the scheme-level lemma are written with an explicit `_root_.`,
because the unqualified names would be read in the `Space` namespace.

## References

* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0AHD**, syntomic case. In a commuting triangle `p = f ≫ q` of morphisms of
algebraic spaces over `S` with `f` surjective and syntomic, syntomicity of `p` implies
syntomicity of `q`. -/
@[stacks 0AHD "syntomic case"]
theorem isSyntomic_of_comp_surjective_isSyntomic
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hcomm : p = f ≫ q) (hfs : IsSurjective B S hS f)
    (hf : IsSyntomic B S hS f) (hp : IsSyntomic B S hS p) :
    IsSyntomic B S hS q := by
  refine holdsOnEveryEtaleChart_of_comp_surjective B S hS
    (@_root_.AlgebraicGeometry.Syntomic.{u} : MorphismProperty Scheme.{u})
    (fun g r hs hg hgr => ?_) hX hY f p q hcomm hfs hf hp
  have : Surjective g := hs
  exact _root_.AlgebraicGeometry.syntomic_of_comp_surjective_syntomic g r hg hgr

end AlgebraicGeometry.Space

end
