module

public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesDiagonal

/-!
# The isomorphism locus of a Hilbert family over the graph ambient space

`AlgebraicGeometry.Space.HasIsomorphismLocus` states [Stacks, Tag 05XD] in the shape the proof of
[Stacks, Tag 0D1C] uses it: for two morphisms `z : Z ⟶ Q` and `x : X ⟶ Q` of finite presentation,
flat and proper, and a member `Y` of the Hilbert functor of the ambient space of the graph
construction over a scheme `T`, the locus of `T` over which the graph projection of `Y` becomes an
isomorphism is open. It is proved in
`StacksFrontier/AlgebraicGeometry/Quot/HilbertGraphIsomorphismLocus.lean`.

## Main definitions

* `AlgebraicGeometry.Space.HasIsomorphismLocus`: the openness of that isomorphism locus, for every
  datum.

## References

* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05XD** in the form the proof of Stacks 0D1C consumes it, for every datum: the locus
in the base over which a member of the Hilbert functor of the ambient space of the graph
construction becomes an isomorphism is open, for two morphisms to a common base that are both of
finite presentation, flat and proper — which is the only shape the proof of 0D1C uses it in.

It is proved outright as `AlgebraicGeometry.Space.hasIsomorphismLocus`, in
`StacksFrontier/AlgebraicGeometry/Quot/HilbertGraphIsomorphismLocus.lean`, from the unconditional
form of Stacks 05XD. -/
def HasIsomorphismLocus : Prop :=
  ∀ (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q),
    IsFinitePresentation B S hS z → IsFlat B S hS z → IsProper B S hS z →
    IsFinitePresentation B S hS x → IsFlat B S hS x → IsProper B S hS x →
    ∀ (T : BigFppfOver B S hS)
    (Y : HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T),
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T),
      MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        (BigFppfOver.toScheme B S hS) s ∧
      ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
        (∃ t : T' ⟶ V, t ≫ s = h) ↔
          IsIso (graphProjection z x (Y.baseChange h).toBase (Y.baseChange h).family.Z)

end AlgebraicGeometry.Space

end
