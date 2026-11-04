module

public import StacksFrontier.AlgebraicGeometry.Properties.DimensionZero
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated

/-!
# Separatedness from a discrete representing scheme

A scheme whose underlying topological space is discrete is a separated scheme: its topological
Krull dimension is zero, a discrete space is Hausdorff and hence quasi-separated, and for a
zero-dimensional scheme quasi-separatedness and separatedness coincide — **Stacks 0CKV**, here
`AlgebraicGeometry.separation_tfae_of_topologicalKrullDim_eq_zero`. Concretely such a scheme is
the disjoint union of its points, each of which is a one-point and therefore affine open
subscheme, and a disjoint union of affine schemes is separated; the dimension-zero equivalence
delivers that without decomposing the scheme.

Consequently *every* morphism of algebraic spaces out of an algebraic space represented by such
a scheme is separated, whatever its target: a presheaf represented by an object of the site with
separated underlying scheme is separated over `S`
(`AlgebraicGeometry.Space.isSeparatedOver_yoneda_obj`), and by **Stacks 04ZI** part (4) every
morphism out of a presheaf separated over `S` is separated.

This is the shape in which separatedness of a pre-relation `j = (t, s) : R ⟶ U ×_S U` is
available when the arrow space `R` has a zero-dimensional representing scheme: no condition on
`U`, on the base, or on `j` itself enters.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Scheme.isSeparated_of_discreteTopology`: a scheme with discrete underlying
  space is a separated scheme.
* `AlgebraicGeometry.Space.isSeparatedOver_of_discreteTopology_yoneda_iso`: a presheaf
  isomorphic to one represented by an object of the site with discrete underlying scheme is
  separated over `S`.
* `AlgebraicGeometry.Space.isSeparated_of_discreteTopology_yoneda_iso`: every morphism of
  presheaves out of such a presheaf is separated.

## Implementation notes

The hypothesis is discreteness of the underlying space rather than local Artinianness, which is
strictly stronger: `AlgebraicGeometry.IsLocallyArtinian.discreteTopology` makes a locally
Artinian scheme discrete, and nothing below uses the Noetherian half of local Artinianness.

The empty scheme is treated separately because its topological Krull dimension is `⊥` rather
than `0`, so the dimension-zero equivalence does not apply to it; it is affine, hence separated.

## References

* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 04ZI](https://stacks.math.columbia.edu/tag/04ZI)
* [Stacks Project, Tag 0CKV](https://stacks.math.columbia.edu/tag/0CKV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A scheme with discrete underlying space is a separated scheme.** Its topological Krull
dimension is zero — at most zero because no two distinct irreducible closed subsets of a
discrete space are nested, and at least zero because the space is nonempty — and a discrete
space is Hausdorff, hence quasi-separated, so the equivalence of **Stacks 0CKV** between
quasi-separatedness and separatedness for a zero-dimensional scheme applies.

The empty scheme is affine, and so separated, directly. -/
theorem Scheme.isSeparated_of_discreteTopology (X : Scheme.{u}) [DiscreteTopology X] :
    X.IsSeparated := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty X := hX
    have : IsAffine X := inferInstance
    infer_instance
  · have hne : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨({hX.some} : TopologicalSpace.IrreducibleCloseds X)⟩
    have hdim : topologicalKrullDim X = 0 :=
      le_antisymm (topologicalKrullDim_zero_of_discreteTopology X)
        (show (0 : WithBot ℕ∞) ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds X) from
          Order.krullDim_nonneg)
    have hqs : QuasiSeparatedSpace X := inferInstance
    exact ((separation_tfae_of_topologicalKrullDim_eq_zero X hdim).out 1 2).mp hqs

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A presheaf represented by a scheme with discrete underlying space is separated over the
base.** The representing object of the site has separated underlying scheme by
`AlgebraicGeometry.Scheme.isSeparated_of_discreteTopology`, so
`AlgebraicGeometry.Space.isSeparatedOver_yoneda_obj` applies to it, and separatedness over the
base is insensitive to replacing a presheaf by an isomorphic one: it is separatedness of a
morphism to a terminal presheaf, and the comparison with the representable one is an
isomorphism, hence separated. -/
theorem isSeparatedOver_of_discreteTopology_yoneda_iso (A : BigFppfOver B S hS)
    (e : F ≅ yoneda.obj A)
    (hA : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj A)) :
    IsSeparatedOver B S hS F := by
  have hterminal : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :=
    IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  have hAsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj A) :=
    have := hA
    Scheme.isSeparated_of_discreteTopology _
  refine (isSeparatedOver_iff_isSeparated_of_isTerminal B S hS hterminal
    (e.hom ≫ hterminal.from (yoneda.obj A))).2 ?_
  exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS e.hom)
    (isSeparated_of_isSeparatedOver B S hS
      (isSeparatedOver_yoneda_obj B S hS A hAsep) _)

/-- **Every morphism of presheaves out of one represented by a scheme with discrete underlying
space is separated.** By
`AlgebraicGeometry.Space.isSeparatedOver_of_discreteTopology_yoneda_iso` the source is separated
over `S`, and by **Stacks 04ZI** part (4) every morphism out of a presheaf separated over `S` is
separated. Nothing is asked of the target or of the morphism. -/
theorem isSeparated_of_discreteTopology_yoneda_iso (A : BigFppfOver B S hS)
    (e : F ≅ yoneda.obj A)
    (hA : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj A)) (f : F ⟶ G) :
    IsSeparated B S hS f :=
  isSeparated_of_isSeparatedOver B S hS
    (isSeparatedOver_of_discreteTopology_yoneda_iso B S hS A e hA) f

end Space

end AlgebraicGeometry

end
