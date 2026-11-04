module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceQuotientMap

/-!
# The line of the Moving Lemma as a scheme, and the products it lives in

Tag 0B1T moves a closed subvariety `C ⊆ 𝐏(V)` in a family `C' ⊆ ℓ × 𝐏(V)` over a line
`ℓ ⊆ 𝐏 = 𝐏((End V)ᵛ)` through `[id_V]`. A line of `𝐏` is
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` of a submodule `L` of corank two, and
that subset is the image of the closed immersion `𝐏((End V)ᵛ ⧸ L) ⟶ 𝐏` induced by the quotient
map. This file takes that projective space of the corank-two quotient as *the line itself*, a
scheme, and builds the two products the family is defined in: the ambient `ℓ ×_k 𝐏(V)` of `C'`
and the triple product `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` carrying the graph of the family.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineSpace`: the corank-two quotient
  `(End V)ᵛ ⧸ L`, whose projective space is the line.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingLine`: the line `ℓ` as a scheme, with
  `AlgebraicGeometry.ProjectiveSpaceOfModule.movingLineι` its closed immersion into the
  parameter space.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingAmbient`: the product `ℓ ×_k 𝐏(V)`, with
  projections `AlgebraicGeometry.ProjectiveSpaceOfModule.ambLine` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.ambPoint`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingProd`: the product
  `𝐏(V) ×_k (ℓ ×_k 𝐏(V))`, with projections
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prSource`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prAmbient`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prLine` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prTarget`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_movingLineι`: the line, read in the parameter
  space, is the linear subspace cut out by `L`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_movingLine`: the line has
  dimension one.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_movingAmbient`: the dimension of
  `ℓ × 𝐏(V)` is `dim 𝐏(V) + 1`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_movingAmbient`: over an
  algebraically closed field that product is irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_prAmbient`: the projection of the triple
  product forgetting the source point is proper, so it carries closed subsets to closed subsets.

## Implementation notes

The line is a scheme rather than a subset, so that the family over it can be a closed subscheme
of an honest product of schemes and its fibres can be taken scheme-theoretically. The passage
between the two descriptions is `range_movingLineι` together with the closed immersion, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosedImmersion_quotientMap`.

Both products are categorical fibre products over `Spec k`, as in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus`: the triple product is
formed as `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` so that the projection forgetting the *source* point of a pair
is a single `CategoryTheory.Limits.pullback.snd`, hence a base change of
`𝐏(V) ⟶ Spec k` and so proper, which is what makes the image of the graph closed.

The corank-two hypothesis enters only through `Nontrivial ((End V)ᵛ ⧸ L)`, which is what the
finite-type and properness instances of the line need; the dimension statement asks for the
corank itself.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

section AbstractLine

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- **The product `𝐏(W) ×_k 𝐏(V)`**, the ambient space of a family of closed subvarieties of
`𝐏(V)` parametrised by the projective space of `W`. Tag 0B1T's statement puts its family in
`𝐏^N × 𝐏^1`, so `W` is taken two-dimensional there; the construction in its proof parametrises
by a line of `𝐏 = 𝐏((End V)ᵛ)`, which is the projective space of a corank-two quotient of
`(End V)ᵛ`, and that is this product at `W = lineSpace k V L`. -/
public abbrev lineProduct : Scheme.{u} :=
  pullback (projectiveSpaceOfModuleToSpec k W) (projectiveSpaceOfModuleToSpec k V)

/-- The projection of `𝐏(W) ×_k 𝐏(V)` to the parameter factor `𝐏(W)`. -/
public abbrev lineProductLine : lineProduct k V W ⟶ projectiveSpaceOfModule k W :=
  pullback.fst _ _

/-- The projection of `𝐏(W) ×_k 𝐏(V)` to `𝐏(V)`. -/
public abbrev lineProductPoint : lineProduct k V W ⟶ projectiveSpaceOfModule k V :=
  pullback.snd _ _

/-- The structure morphism of `𝐏(W) ×_k 𝐏(V)` over `Spec k`. -/
public abbrev lineProductToSpec : lineProduct k V W ⟶ Spec (.of k) :=
  lineProductLine k V W ≫ projectiveSpaceOfModuleToSpec k W

variable [FiniteDimensional k V] [Nontrivial V] [FiniteDimensional k W] [Nontrivial W]

/-- The product `𝐏(W) ×_k 𝐏(V)` is proper over `Spec k`. -/
public instance isProper_lineProductToSpec : IsProper (lineProductToSpec k V W) := by
  have h1 : IsProper (lineProductLine k V W) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
      (isProper_projectiveSpaceOfModuleToSpec k V)
  infer_instance

/-- The product `𝐏(W) ×_k 𝐏(V)` is locally of finite type over `Spec k`. -/
public instance locallyOfFiniteType_lineProductToSpec :
    LocallyOfFiniteType (lineProductToSpec k V W) := by
  have := isProper_lineProductToSpec k V W
  infer_instance

/-- **The dimension of `𝐏(W) × 𝐏(V)`** is the sum of the dimensions of the two factors. -/
public theorem topologicalKrullDim_lineProduct :
    topologicalKrullDim (lineProduct k V W) =
      topologicalKrullDim (projectiveSpaceOfModule k W) +
        topologicalKrullDim (projectiveSpaceOfModule k V) :=
  topologicalKrullDim_pullback k _ _

omit [FiniteDimensional k V] [Nontrivial V] [FiniteDimensional k W] [Nontrivial W] in
/-- **`𝐏(W) × 𝐏(V)` is irreducible** over an algebraically closed field: both factors are
irreducible projective spaces, and a product of geometrically irreducible schemes over a
separably closed field is irreducible. -/
public theorem irreducibleSpace_lineProduct [IsAlgClosed k]
    [IrreducibleSpace (projectiveSpaceOfModule k W)]
    [IrreducibleSpace (projectiveSpaceOfModule k V)] :
    IrreducibleSpace (lineProduct k V W) := by
  have := geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _
    (projectiveSpaceOfModuleToSpec k W)
  have := geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _
    (projectiveSpaceOfModuleToSpec k V)
  infer_instance

end AbstractLine

variable (L : Submodule k (ParameterModule k V))

/-- The corank-two quotient `(End V)ᵛ ⧸ L` of the parameter module, whose projective space is the
line `ℓ ⊆ 𝐏` of Tag 0B1T. -/
public abbrev lineSpace : Type u := ParameterModule k V ⧸ L

/-- **The line `ℓ` of Tag 0B1T as a scheme**: the projective space of the corank-two quotient
`(End V)ᵛ ⧸ L`, which the quotient map embeds in the parameter space as the linear subspace cut
out by `L`. -/
public abbrev movingLine : Scheme.{u} := projectiveSpaceOfModule k (lineSpace k V L)

/-- The closed immersion of the line into the parameter space `𝐏 = 𝐏((End V)ᵛ)`. -/
public abbrev movingLineι : movingLine k V L ⟶ projectiveSpaceOfModule k (ParameterModule k V) :=
  quotientMap k (ParameterModule k V) L

/-- The structure morphism of the line over `Spec k`. -/
public abbrev movingLineToSpec : movingLine k V L ⟶ Spec (.of k) :=
  projectiveSpaceOfModuleToSpec k (lineSpace k V L)

/-- **The line, read in the parameter space, is the linear subspace cut out by `L`.** -/
public theorem range_movingLineι :
    Set.range (movingLineι k V L).base =
      linearSubspace k (ParameterModule k V) L :=
  range_quotientMap k (ParameterModule k V) L

/-- **The line has dimension one** when `L` has corank two. -/
public theorem topologicalKrullDim_movingLine
    (hL : Module.finrank k (lineSpace k V L) = 2) :
    topologicalKrullDim (movingLine k V L) = 1 := by
  have : FiniteDimensional k (lineSpace k V L) := .of_finrank_eq_succ hL
  rw [topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (n := 1) hL]
  rfl

variable [FiniteDimensional k V] [Nontrivial (lineSpace k V L)]

/-- The line is proper over `Spec k`. -/
public instance isProper_movingLineToSpec : IsProper (movingLineToSpec k V L) :=
  isProper_projectiveSpaceOfModuleToSpec k (lineSpace k V L)

/-- The line is locally of finite type over `Spec k`. -/
public instance locallyOfFiniteType_movingLineToSpec :
    LocallyOfFiniteType (movingLineToSpec k V L) := by
  have := isProper_movingLineToSpec k V L
  infer_instance

/-- **The ambient product `ℓ ×_k 𝐏(V)` of the family `C'`**: the product of
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineProduct` at the corank-two quotient. -/
public abbrev movingAmbient : Scheme.{u} := lineProduct k V (lineSpace k V L)

variable [Nontrivial V]

/-- The projection of `ℓ ×_k 𝐏(V)` to the line. -/
public abbrev ambLine : movingAmbient k V L ⟶ movingLine k V L :=
  lineProductLine k V (lineSpace k V L)

/-- The projection of `ℓ ×_k 𝐏(V)` to `𝐏(V)`. -/
public abbrev ambPoint : movingAmbient k V L ⟶ projectiveSpaceOfModule k V :=
  lineProductPoint k V (lineSpace k V L)

/-- The structure morphism of `ℓ ×_k 𝐏(V)` over `Spec k`. -/
public abbrev movingAmbientToSpec : movingAmbient k V L ⟶ Spec (.of k) :=
  lineProductToSpec k V (lineSpace k V L)

/-- The product `ℓ ×_k 𝐏(V)` is proper over `Spec k`. -/
public instance isProper_movingAmbientToSpec : IsProper (movingAmbientToSpec k V L) :=
  isProper_lineProductToSpec k V (lineSpace k V L)

/-- The product `ℓ ×_k 𝐏(V)` is locally of finite type over `Spec k`. -/
public instance locallyOfFiniteType_movingAmbientToSpec :
    LocallyOfFiniteType (movingAmbientToSpec k V L) :=
  locallyOfFiniteType_lineProductToSpec k V (lineSpace k V L)

/-- **The dimension of `ℓ × 𝐏(V)`** is the dimension of the line plus that of `𝐏(V)`. -/
public theorem topologicalKrullDim_movingAmbient :
    topologicalKrullDim (movingAmbient k V L) =
      topologicalKrullDim (movingLine k V L) +
        topologicalKrullDim (projectiveSpaceOfModule k V) :=
  topologicalKrullDim_lineProduct k V (lineSpace k V L)

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **`ℓ × 𝐏(V)` is irreducible** over an algebraically closed field: both factors are
irreducible projective spaces, and a product of geometrically irreducible schemes over a
separably closed field is irreducible. -/
public theorem irreducibleSpace_movingAmbient [IsAlgClosed k]
    [IrreducibleSpace (movingLine k V L)] [IrreducibleSpace (projectiveSpaceOfModule k V)] :
    IrreducibleSpace (movingAmbient k V L) :=
  irreducibleSpace_lineProduct k V (lineSpace k V L)

/-- **The triple product `𝐏(V) ×_k (ℓ ×_k 𝐏(V))`**, whose points are a source point of `𝐏(V)`, a
point of the line and a target point of `𝐏(V)`. -/
public abbrev movingProd : Scheme.{u} :=
  pullback (projectiveSpaceOfModuleToSpec k V) (movingAmbientToSpec k V L)

/-- The projection of the triple product to the source point. -/
public abbrev prSource : movingProd k V L ⟶ projectiveSpaceOfModule k V := pullback.fst _ _

/-- **The projection of the triple product forgetting the source point.** -/
public abbrev prAmbient : movingProd k V L ⟶ movingAmbient k V L := pullback.snd _ _

/-- The projection of the triple product to the line. -/
public abbrev prLine : movingProd k V L ⟶ movingLine k V L :=
  prAmbient k V L ≫ ambLine k V L

/-- The projection of the triple product to the target point. -/
public abbrev prTarget : movingProd k V L ⟶ projectiveSpaceOfModule k V :=
  prAmbient k V L ≫ ambPoint k V L

/-- The structure morphism of the triple product over `Spec k`. -/
public abbrev movingProdToSpec : movingProd k V L ⟶ Spec (.of k) :=
  prAmbient k V L ≫ movingAmbientToSpec k V L

/-- **The projection forgetting the source point is proper**: it is a base change of the
structure morphism of `𝐏(V)`, which is proper. Hence it carries closed subsets of the triple
product to closed subsets of `ℓ × 𝐏(V)`. -/
public instance isProper_prAmbient : IsProper (prAmbient k V L) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _)
    (isProper_projectiveSpaceOfModuleToSpec k V)

/-- The triple product `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` is proper over `Spec k`. -/
public instance isProper_movingProdToSpec : IsProper (movingProdToSpec k V L) := by
  have := isProper_prAmbient k V L
  have := isProper_movingAmbientToSpec k V L
  infer_instance

/-- The triple product `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` is locally of finite type over `Spec k`. -/
public instance locallyOfFiniteType_movingProdToSpec :
    LocallyOfFiniteType (movingProdToSpec k V L) := by
  have := isProper_movingProdToSpec k V L
  infer_instance

omit [Nontrivial (lineSpace k V L)] in
/-- The image of a closed subset of the triple product under the projection forgetting the
source point is closed. -/
public theorem isClosed_image_prAmbient {S : Set (movingProd k V L)} (hS : IsClosed S) :
    IsClosed ((prAmbient k V L).base '' S) :=
  (prAmbient k V L).isClosedMap S hS

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
