module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.RingColimit
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.FiniteDescent
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.ComplexDescent
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.HomComplexBaseChange
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.HomComplexColimit
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.DerivedExtensionPseudofunctor
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.RelativelyPerfectDiagram
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.StrictCocone
public import StacksFrontier.Homology.RelativelyPerfect.Colimit.FilteredColimit

/-!
# Relatively perfect complexes over a filtered colimit of rings

Let `R` be the filtered colimit of a diagram `i ↦ Rᵢ` of `R₀`-algebras, let `R₀ → A₀` be flat of
finite presentation, and put `Aᵢ = Rᵢ ⊗[R₀] A₀` and `A = R ⊗[R₀] A₀`. Every object of `D(A)`
that is perfect relative to `R` is the derived base change of an object of `D(Aᵢ)` perfect
relative to `Rᵢ`, for some stage `i`; and morphisms between the base changes of a
pseudo-coherent complex and of a complex of finite Tor dimension are the filtered colimit of
the morphisms at the finite stages. Consequently the category of objects of `D(A)` perfect
relative to `R` is the categorical colimit of the categories of objects of `D(Aᵢ)` perfect
relative to `Rᵢ`.

## Main definitions

* `PseudoCoherence.stageAlgebra` is the algebra `Rᵢ ⊗[R₀] A₀` at a stage.
* `PseudoCoherence.stageMap`, `PseudoCoherence.baseToStageMap`,
  `PseudoCoherence.stageToLimitMap` and `PseudoCoherence.baseToLimitMap` are its canonical
  structure maps.
* `PseudoCoherence.extensionOfScalarsComplexComp` and
  `PseudoCoherence.derivedExtensionScalarsCongr` are the scalar-tower composition and the
  equality transport for extension of scalars on complexes, at independent module universes.

## Main results

* `PseudoCoherence.relativelyPerfectComplexes_filteredColimit` (Stacks 0DHX): descent of a
  relatively perfect object to a finite stage, the filtered-colimit description of the morphism
  sets, and the colimit cocone identifying the category of relatively perfect objects over the
  colimit ring.

## Implementation notes

The source passes from a distinguished index `0` to the cofinal subsystem of indices above it;
that subsystem is encoded directly as a filtered diagram `F : I ⥤ CommAlgCat R₀`. Derived
extension of scalars is `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`,
and its composition and unit comparisons — produced here by uniqueness of total left derived
functors — are what make the stages into a diagram at all; they are therefore part of the
statement, together with the pseudofunctor coherence laws they satisfy. The derived tensor
product over each ring is supplied as a `PseudoCoherence.DerivedTensoringDatum`.

The index objects and morphisms, the scalar rings, the algebra `A₀` and the module carriers all
have independent universes. Restriction along `ULift A₀ ≃+* A₀` moves the two starting complexes
into the common algebra universe before extension of scalars is applied, and the ring-colimit
hypothesis is stated after lifting to a universe containing the index category: a universal
property tested only against algebras in the smaller carrier universe need not describe the
colimit of a large diagram.

The final assertion is an actual colimit cocone in `Cat`. Its legs are identified with derived
extension of scalars on the full subcategories of relatively perfect objects, and the chosen
identifications satisfy the modification equation with the transition isomorphisms.

## References

* [The Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
-/
