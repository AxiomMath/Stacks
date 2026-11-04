module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDiagonal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# The canonical morphism into the internal Hom of a derived tensor product

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of the derived category `D(O_X)`
of sheaves of `O_X`-modules. **Stacks 0A8W** asserts a canonical morphism

`K ⟶ RSheafHom(L, K ⊗^L_{O_X} L)`

in `D(O_X)`, **functorial in both `K` and `L`**. This file constructs the morphism twice.

`Stacks.SheafOfModules.derivedTensorHomUnit` is the short construction, as the unit of the
tensor–internal-Hom bijection of Stacks 08DI: that bijection identifies

`Hom_{D(O_X)}(K, RSheafHom(L, K ⊗^L_{O_X} L))` with
`Hom_{D(O_X)}(K ⊗^L_{O_X} L, K ⊗^L_{O_X} L)`,

and the morphism is the one corresponding to the identity of `K ⊗^L_{O_X} L`.

`Stacks.SheafOfModules.canonicalDerivedTensorHomUnit` is the construction the source gives, and
it is the one that carries the functoriality: a K-flat complex `A` representing `K` and a
K-injective complex `B` representing `L` are chosen, the diagonal morphism of complexes of
Stacks 0A93

`A ⟶ SheafHom(B, Tot(A ⊗_{O_X} B))`

is followed by the augmentation of `Tot(A ⊗_{O_X} B)` into its chosen K-injective resolution
`J`, and the class of the resulting morphism `A ⟶ SheafHom(B, J)` is read through the
comparisons identifying `K` with the class of `A` and `RSheafHom(L, K ⊗^L_{O_X} L)` with the
class of `SheafHom(B, J)`. Both functoriality squares are proved for it.

A ringed space *is* a ringed site, namely the site of its opens with the open-cover topology, so
the second construction is the ringed-site morphism of Stacks 0A99 read off along
`Stacks.SheafOfModules.ringedSite`, exactly as the declarations of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom` read off Stacks 08DI
and the declarations of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonal` read off
Stacks 0BYS. Stacks 0A99 is the statement of Stacks 0A8W verbatim on a ringed site, including
its functoriality clause.

## Main definitions

* `Stacks.SheafOfModules.derivedTensorHomUnit`: the canonical morphism above, as the unit of
  Stacks 08DI.
* `Stacks.SheafOfModules.canonicalDerivedTensorHomUnit`: the canonical morphism above, built the
  way the source builds it, from the complex-level diagonal of Stacks 0A93.

## Main results

* `Stacks.SheafOfModules.derivedTensorHomUnit_eq`: the unit morphism is the image of the identity
  of `K ⊗^L_{O_X} L` under the inverse of the bijection of Stacks 08DI. This is what makes that
  construction content rather than an unconstrained morphism of its type, and the form in which
  to rewrite it.
* `Stacks.SheafOfModules.canonicalDerivedTensorHomUnit_eq`: the morphism built the source's way
  is the class of the complex-level diagonal of Stacks 0A93 followed by the K-injective
  resolution augmentation, read through the comparisons of its source and target with classes of
  complexes. This is what makes *that* construction content.
* `Stacks.SheafOfModules.canonicalDerivedTensorHomUnit_natural_left` and
  `Stacks.SheafOfModules.canonicalDerivedTensorHomUnit_natural_right`: **the functoriality in
  `K` and in `L`**, which is the second assertion of the tag.

## Implementation notes

The two constructions differ in what they need. `derivedTensorHomUnit` goes through the
tensor–internal-Hom bijection of Stacks 08DI,
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`, which is already available as an additive
equivalence of morphism groups: the morphism is then the image of an identity under an
equivalence and needs no choice of representatives at all.
`canonicalDerivedTensorHomUnit` follows the Stacks text and takes the complex-level route,
which does require choosing representatives, replacing `Tot(A ⊗_{O_X} B)` by a K-injective
complex and carrying the comparison isomorphisms of both the derived tensor product and the
derived internal Hom through the localization. That bookkeeping is what buys the
functoriality: the two squares descend from the functoriality of the complex-level diagonal,
`AlgebraicGeometry.RingedSite.diagonalMap_natural` (Stacks 0A93), in the representing
complexes, whereas on the unit construction they would need a naturality of Stacks 08DI that
is not available (see below).

Being defined as the image of `𝟙 (K ⊗^L_{O_X} L)` under a bijection, `derivedTensorHomUnit` is
pinned down by `derivedTensorHomUnit_eq` and is not an arbitrary inhabitant of its type; so is
`canonicalDerivedTensorHomUnit`, by `canonicalDerivedTensorHomUnit_eq`. Neither is the zero
morphism by accident of the construction: the complex-level diagonal they rest on acts on
sections by `k ↦ (l ↦ k ⊗ l)`, which `AlgebraicGeometry.RingedSite.diagonalMap_apply` gives by
`rfl`.

The source assumes nothing of `(X, O_X)` beyond its being a ringed space, and the four
declarations carrying the functorial construction assume nothing either. The five instance
binders such declarations would otherwise carry —
`HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat`, the matching
`WEqualsLocallyBijective`, additivity of `⊗_{O_X}` in each variable, and existence of the total
complexes `Tot(K₁ ⊗_{O_X} K₂)` — hold for *every* ringed space, and are discharged here
rather than demanded of the caller. The first two synthesize unaided. The other three do not,
and the reason is not that they are missing: the general instances are stated at
`CommRingCat.{max u v}` and do not solve against the diagonal `u` of a site of opens while the
universes are still metavariables, so they are supplied by name, exactly as
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback` supplies them for a packaged `RingedSpace`.
They are declared as instances rather than `local` ones so that a consumer of the tag can state
`derivedTensor Rc` without rediscovering the same three lines.

The `derivedTensorHomUnit` pair keeps the five binders, for an elaboration reason and not a
mathematical one: `derivedTensorHomUnit_eq` is proved by `rfl`, and with the three instances
supplied as closed terms instead of opaque binders that `rfl` exhausts the elaborator's
recursion depth — the same hazard recorded below for the forward form of that equation.

That equation is stated in the inverse direction, as the value of the inverse bijection, and
not in the equivalent forward direction asserting that the bijection carries the morphism to
`𝟙 (K ⊗^L_{O_X} L)`. The forward form is unavailable: elaborating an application of the
morphism-group additive equivalence of Stacks 08DI at these arguments exhausts the elaborator's
recursion depth, and raising that limit is a workaround this development does not accept. The
inverse direction is the direction in which the morphism is defined, so it elaborates, and the
two are interderivable by `AddEquiv.apply_symm_apply` once the forward form can be stated at
all.

The functoriality is stated as the two squares, for `k : K ⟶ K'` and `l : L' ⟶ L`,

`k ≫ u_{K',L} = u_{K,L} ≫ RSheafHom(𝟙_L, k ⊗ 𝟙_L)` and
`u_{K,L} ≫ RSheafHom(l, 𝟙) = u_{K,L'} ≫ RSheafHom(𝟙_{L'}, 𝟙_K ⊗ l)`,

and not as a natural transformation of bifunctors. The target is not a bifunctor in `L`: the
second variable occurs covariantly inside the tensor product and contravariantly as the source
of the internal Hom, so the second square is a dinaturality and has no formulation as the
naturality of a transformation between functors of `L`. This is the form the source states and
the form `AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal_natural_left` and
`AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal_natural_right` take.

The functoriality in `L` needs no localization argument, the chosen representative of `L` being
K-injective, so that every morphism `L' ⟶ L` of `D(O_X)` is the class of a morphism of the
chosen representatives. The functoriality in `K` does need one, the chosen representative of
`K` being K-flat and not K-injective: the given morphism is written as a right fraction and the
apex of that fraction is replaced by a K-flat resolution of it (Stacks 06YS), after which the
one-sided K-flat comparison of Stacks 06YU is available at all three vertices of the resulting
roof. Both arguments are carried out once, at the level of ringed sites, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDiagonal`.

## What this file does not contain

The two constructions are **not identified**: there is no declaration below asserting
`derivedTensorHomUnit Rc K L = canonicalDerivedTensorHomUnit Rc K L`. Nothing about the tag
depends on the identification — its two assertions are the existence of a canonical morphism
and its functoriality, and `canonicalDerivedTensorHomUnit` discharges both on its own — but the
gap is a real one and the reason is recorded rather than chosen.

Identifying the two amounts to computing the bijection of Stacks 08DI on a given class. That
bijection is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, the currying isomorphism of
Stacks 08J9 read on degree-zero global hypercohomology with both sides identified with morphism
groups by Stacks 08JA. What is wanted is the compatibility of the identification
`H⁰(X, RSheafHom(L, M)) ≅ Hom_{D(O_X)}(L, M)` with precomposition in `L` and postcomposition
in `M`. The object-level half is available —
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` is the naturality of the currying
isomorphism in all three objects — and so is the **precomposition** half,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsSourceNaturality`,
which carries the tag of Stacks 08JA. Only the **postcomposition** half is missing, and what
it still costs is *not* the naturality of Stacks 0A94: that is proved in both variables, as
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`, from
the compatibility `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap` of
`AlgebraicGeometry.RingedSite.SheafHomComplex.globalSectionsIso` with
`AlgebraicGeometry.RingedSite.homMap`. What remains is the passage from morphisms of complexes
to arbitrary morphisms of `D(O)`, which in the covariant variable needs no
localization-calculus argument at all, the representative of the target being K-injective; see
the section "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects`.

That remaining gap is why the functoriality here is proved for the complex-level construction
and not for the unit construction. On the unit construction the two squares would follow
formally from the naturality of Stacks 08DI in its three variables: the bijection is
injective, so each square reduces to the equality of the two images under it. Of the two
identities that discharges, the first — `Φ(k ≫ f) = (k ⊗ 𝟙_L) ≫ Φ(f)`, compatibility with
precomposition in the source — **is** in the library, as
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` (Stacks 08J8); only the
second, `Φ(f ≫ RSheafHom(𝟙_L, m)) = Φ(f) ≫ m`, compatibility with postcomposition in the
target, is not.

The functoriality clause of Stacks 08JD is **not** absent from
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual`: it is
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality`, proved from the
covariant naturality of Stacks 0A98 in its target rather than through Stacks 08JA, with
`AlgebraicGeometry.RingedSite.derivedTensorDualSections_naturality` its reading on degree-zero
global hypercohomology. What the missing postcomposition half still leaves out is only the
naturality of `derivedTensorDualGlobalSectionsMap`, that reading composed with Stacks 08JA.

## References

* [Stacks Project, Tag 0A8W](https://stacks.math.columbia.edu/tag/0A8W)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A99](https://stacks.math.columbia.edu/tag/0A99)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

section Unit

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Stacks 0A8W.** For objects `K`, `L` of `D(O_X)` on a ringed space, the canonical morphism

`K ⟶ RSheafHom(L, K ⊗^L_{O_X} L)`

in `D(O_X)`: the morphism corresponding to the identity of `K ⊗^L_{O_X} L` under the
tensor–internal-Hom bijection of Stacks 08DI. -/
@[stacks 0A8W "the canonical morphism, as the unit of Stacks 08DI"]
def derivedTensorHomUnit (K L : DerivedCategory (StructureSheafModules Rc)) :
    K ⟶ ((derivedSheafHom Rc).obj (op L)).obj (((derivedTensor Rc).obj K).obj L) :=
  (derivedSheafHomTensorEquiv Rc K L (((derivedTensor Rc).obj K).obj L)).symm (𝟙 _)

/-- The canonical morphism of Stacks 0A8W is the image of the identity of `K ⊗^L_{O_X} L` under
the inverse of the tensor–internal-Hom bijection of Stacks 08DI. This is the equation that
pins the morphism down, and the form in which to rewrite it. -/
theorem derivedTensorHomUnit_eq (K L : DerivedCategory (StructureSheafModules Rc)) :
    derivedTensorHomUnit Rc K L =
      (derivedSheafHomTensorEquiv Rc K L (((derivedTensor Rc).obj K).obj L)).symm (𝟙 _) :=
  rfl

end Unit

/-! ### The construction of the source, and its functoriality

The four declarations below carry no hypothesis beyond the ringed space itself, which is all the
source assumes: the three instances that follow discharge what the section above keeps as
binders, and the remaining two synthesize unaided. -/

attribute [instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **Stacks 0A8W.** For objects `K`, `L` of `D(O_X)` on a ringed space, the canonical morphism

`K ⟶ RSheafHom(L, K ⊗^L_{O_X} L)`

in `D(O_X)`, built the way the source builds it: on the chosen K-flat representative `A` of `K`
and the chosen K-injective representative `B` of `L` it is the diagonal morphism of complexes of
Stacks 0A93, `A ⟶ SheafHom(B, Tot(A ⊗_{O_X} B))`, followed by the augmentation of
`Tot(A ⊗_{O_X} B)` into its chosen K-injective resolution, read through the comparisons
identifying source and target with classes of complexes.

A ringed space is a ringed site, so this is the morphism of Stacks 0A99 read off along
`Stacks.SheafOfModules.ringedSite`. It is the construction that carries the functoriality of the
tag, in `canonicalDerivedTensorHomUnit_natural_left` and
`canonicalDerivedTensorHomUnit_natural_right` below. -/
@[stacks 0A8W "the canonical morphism, built as the source builds it"]
def canonicalDerivedTensorHomUnit (K L : DerivedCategory (StructureSheafModules Rc)) :
    K ⟶ ((derivedSheafHom Rc).obj (op L)).obj (((derivedTensor Rc).obj K).obj L) :=
  RingedSite.canonicalDerivedDiagonal (ringedSite Rc) K L

/-- **Stacks 0A8W.** The canonical morphism built the source's way is the class of the diagonal
morphism of complexes of Stacks 0A93 followed by the K-injective resolution augmentation, read
through the comparisons of its source and target with classes of complexes. This is the equation
that pins the morphism down; in particular it is not an arbitrary morphism between the two
objects. -/
@[stacks 0A8W "the characterisation on representatives"]
theorem canonicalDerivedTensorHomUnit_eq (K L : DerivedCategory (StructureSheafModules Rc)) :
    (RingedSite.kFlatModelIso (ringedSite Rc) K).hom ≫
        canonicalDerivedTensorHomUnit Rc K L ≫
        (RingedSite.diagonalTargetIso (ringedSite Rc) K L L).hom =
      DerivedCategory.Q.map (RingedSite.diagonalComplexMap (ringedSite Rc)
        (RingedSite.kFlatModel (ringedSite Rc) K)
        (RingedSite.kInjectiveModel (ringedSite Rc) L)) :=
  RingedSite.canonicalDerivedDiagonal_eq (ringedSite Rc) K L

/-- **Stacks 0A8W: the canonical morphism is functorial in `K`.** For a morphism `k : K ⟶ K'` of
`D(O_X)` the square

`k ≫ u_{K',L} = u_{K,L} ≫ RSheafHom(𝟙_L, k ⊗ 𝟙_L)`

commutes in `D(O_X)`: the first variable of the morphism acts covariantly, both on the source
and inside the derived tensor product. -/
@[stacks 0A8W "functoriality in K"]
theorem canonicalDerivedTensorHomUnit_natural_left
    (L : DerivedCategory (StructureSheafModules Rc))
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K ⟶ K') :
    k ≫ canonicalDerivedTensorHomUnit Rc K' L =
      canonicalDerivedTensorHomUnit Rc K L ≫
        ((derivedSheafHom Rc).obj (op L)).map (((derivedTensor Rc).map k).app L) :=
  RingedSite.canonicalDerivedDiagonal_natural_left (ringedSite Rc) L k

/-- **Stacks 0A8W: the canonical morphism is functorial in `L`.** For a morphism `l : L' ⟶ L` of
`D(O_X)` the square

`u_{K,L} ≫ RSheafHom(l, 𝟙) = u_{K,L'} ≫ RSheafHom(𝟙_{L'}, 𝟙_K ⊗ l)`

commutes in `D(O_X)`: the second variable acts contravariantly in the source of the internal Hom
and covariantly inside the derived tensor product, which is the dinaturality that the statement
of the tag asserts. -/
@[stacks 0A8W "functoriality in L"]
theorem canonicalDerivedTensorHomUnit_natural_right
    (K : DerivedCategory (StructureSheafModules Rc))
    {L L' : DerivedCategory (StructureSheafModules Rc)} (l : L' ⟶ L) :
    canonicalDerivedTensorHomUnit Rc K L ≫
        ((derivedSheafHom Rc).map l.op).app (((derivedTensor Rc).obj K).obj L) =
      canonicalDerivedTensorHomUnit Rc K L' ≫
        ((derivedSheafHom Rc).obj (op L')).map (((derivedTensor Rc).obj K).map l) :=
  RingedSite.canonicalDerivedDiagonal_natural_right (ringedSite Rc) K l

end Stacks.SheafOfModules

end
