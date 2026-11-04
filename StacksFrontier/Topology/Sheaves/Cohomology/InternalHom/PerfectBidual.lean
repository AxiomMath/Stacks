module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.PerfectEvaluation
import StacksCore.Tactic.StacksAttribute

/-!
# Biduality for a perfect object on a ringed space

Let `(X, O_X)` be a ringed space and let `K` be a **perfect** object of `D(O_X)`. The second
assertion of **Stacks 08DQ** is that `K` is reflexive for the dual
`K^∨ = RSheafHom(K, O_X)` of `Stacks.SheafOfModules.derivedDual`:

`(K^∨)^∨ ≅ K`.

This file states and proves it, in the strong form the source's proof actually gives: there is a
**canonical** map `K ⟶ (K^∨)^∨`, defined for every object of `D(O_X)` with no hypothesis, and it
is an isomorphism as soon as `K` is perfect.

## Main definitions

* `Stacks.SheafOfModules.derivedDualStructureSheafIso`: the trivialisation
  `O_X^∨ = RSheafHom(O_X, O_X) ≅ O_X`.
* `Stacks.SheafOfModules.derivedBidualMap`: the canonical map `K ⟶ (K^∨)^∨`.

## Main results

* `Stacks.SheafOfModules.isIso_derivedBidualMap`: **Stacks 08DQ, second assertion** — the
  canonical map is an isomorphism for a perfect `K`.
* `Stacks.SheafOfModules.derivedBidualIso`: **Stacks 08DQ, second assertion** — the resulting
  isomorphism `K ≅ (K^∨)^∨`. Its `.symm` is the source's orientation `(K^∨)^∨ ≅ K`.

## How it is proved

Exactly the route of the source's proof, which is three morphisms long.

The source writes the canonical map as

`K = RSheafHom(O_X, O_X) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, O_X), O_X) = (K^∨)^∨`,

the arrow being the derived evaluation morphism of **Stacks 0A8U**
(`Stacks.SheafOfModules.derivedSheafHomEvaluation`) at `L = M = O_X`, whose target is then
literally `(K^∨)^∨`: both `derivedDual` and the evaluation morphism spell the structure sheaf as
`AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSite Rc)`, so no bridge is needed and
the type of the composite below is `K ⟶ derivedDual Rc (derivedDual Rc K)` on the nose.

The leading equality `K = RSheafHom(O_X, O_X) ⊗^L_{O_X} K` of the display is not an equality but
two isomorphisms, and both are already in the library:

* `RSheafHom(O_X, O_X) ≅ O_X`, the instance at `Z = O_X` of
  `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` — the derived internal Hom out of
  the structure sheaf is the identity functor. This is the Stacks 0A99/0A98 unitality input; it
  is carried here as `derivedDualStructureSheafIso`, the dual of the structure sheaf being the
  structure sheaf.
* `O_X ⊗^L_{O_X} K ≅ K`, the left unitor `λ_ K` of the monoidal structure
  `Stacks.SheafOfModules.derivedMonoidalStructure` on `D(O_X)`. That structure is *reseated*, so
  its tensor product is `Stacks.SheafOfModules.derivedTensor` and its unit is
  `AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSite Rc)`, both by `rfl`
  (`Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure` and
  `Stacks.SheafOfModules.tensorUnit_derivedMonoidalStructure`); the unitor therefore needs no
  transport, exactly as in
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CupProductAndDualityPairing`.

Invertibility is then the whole content of **Stacks 0G40**,
`Stacks.SheafOfModules.derivedSheafHomEvaluation_isIso_of_isPerfect`, whose only hypothesis is
perfectness of `K` — nothing is assumed of the two remaining variables, so taking both of them to
be the structure sheaf is free. The other two factors of the composite are isomorphisms by
construction.

In particular the restriction compatibility of internal hom (Stacks 08DL), which the source uses
"without further mention" for this part of the argument, is not needed here: it is consumed inside
the proof of Stacks 0G40, which is run on complexes rather than in the derived category, and this
file only composes that result with two trivialisations.

## Universes

This statement is universe polymorphic: Stacks 0G40 and the two trivialisations are all
available at a general `X : TopCat.{u}`. So is the first assertion of the tag,
`Stacks.SheafOfModules.isPerfect_derivedDual` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual`, which this section used to
record as pinned to `Type 0`: that file is stated at `{X : TopCat.{u}}` for a free `u`, and the
instance hypotheses it carries are discharged at every `u` — for a ringed space by the scoped
instances of `StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens`, the open-cover site
being essentially small. The diagonal of `RingedSite.{u, u, u}` is forced, its value is not;
see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
* [Stacks Project, Tag 0G40](https://stacks.math.columbia.edu/tag/0G40)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The dual of the structure sheaf is the structure sheaf**: the trivialisation
`O_X^∨ = RSheafHom(O_X, O_X) ≅ O_X`.

It is the instance at `Z = O_X` of the identification of `RSheafHom(O_X, Z)` with `Z`, the
derived internal Hom out of the structure sheaf being the identity functor. This is the
unitality input to the biduality map of Stacks 08DQ. -/
abbrev derivedDualStructureSheafIso :
    derivedDual Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) ≅
      RingedSite.derivedStructureSheaf (ringedSite Rc) :=
  RingedSite.derivedStructureSheafHomIso (ringedSite Rc)
    (RingedSite.derivedStructureSheaf (ringedSite Rc))

/-- **The canonical biduality map `K ⟶ (K^∨)^∨`** on a ringed space, for an arbitrary object `K`
of `D(O_X)`.

It is the composite the proof of Stacks 08DQ writes down: the left unitor read backwards,
`K ≅ O_X ⊗^L_{O_X} K`; the trivialisation `O_X ≅ RSheafHom(O_X, O_X)` of
`derivedDualStructureSheafIso` in the left tensor factor; and the derived evaluation morphism of
Stacks 0A8U

`RSheafHom(O_X, O_X) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, O_X), O_X) = (K^∨)^∨`

at `L = M = O_X`. No hypothesis on `K` is needed to define it; perfectness enters only in
`isIso_derivedBidualMap`. -/
def derivedBidualMap (K : DerivedCategory (StructureSheafModules Rc)) :
    K ⟶ derivedDual Rc (derivedDual Rc K) :=
  (λ_ K).inv ≫
    (((derivedTensor Rc).mapIso (derivedDualStructureSheafIso Rc).symm).app K).hom ≫
      derivedSheafHomEvaluation Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc))
        (RingedSite.derivedStructureSheaf (ringedSite Rc))

/-- The biduality map is the left unitor, the trivialisation of `RSheafHom(O_X, O_X)` and the
derived evaluation morphism of Stacks 0A8U, in that order. This pins the map down and is the
form in which to rewrite it. -/
theorem derivedBidualMap_eq (K : DerivedCategory (StructureSheafModules Rc)) :
    derivedBidualMap Rc K =
      (λ_ K).inv ≫
        (((derivedTensor Rc).mapIso (derivedDualStructureSheafIso Rc).symm).app K).hom ≫
          derivedSheafHomEvaluation Rc K (RingedSite.derivedStructureSheaf (ringedSite Rc))
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  rfl

variable [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

/-- **Stacks 08DQ, second assertion.** Let `(X, O_X)` be a ringed space and let `K` be a perfect
object of `D(O_X)`. Then `K` is reflexive: the canonical map `K ⟶ (K^∨)^∨` of
`derivedBidualMap` is an isomorphism, so `(K^∨)^∨ ≅ K`.

This is the isomorphism form of `isIso_derivedBidualMap`; its `.symm` is the orientation
`(K^∨)^∨ ≅ K` in which the source states the assertion. The three factors are the left unitor,
the trivialisation `O_X ≅ RSheafHom(O_X, O_X)` and the derived evaluation morphism of
Stacks 0A8U, the last being invertible by Stacks 0G40.

Perfectness is the site-level notion of Stacks 08G5 read at the site of opens of the space, as in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.PerfectEvaluation`, whose section
"Perfectness model" records why that notion and not the ringed-space one of Stacks 08CM. -/
@[stacks 08DQ "the second assertion: `(K^∨)^∨ ≅ K` for a perfect `K`"]
def derivedBidualIso (K : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    K ≅ derivedDual Rc (derivedDual Rc K) :=
  -- Stacks 0G40 states invertibility with the target of the evaluation morphism written
  -- `RSheafHom(RSheafHom(K, O_X), O_X)`, while the composite below has it at the `derivedDual`
  -- spelling the conclusion asks for; the two are the same object only after `derivedDual` and
  -- `RingedSite.derivedInternalHomOfBifunctor` are unfolded, which instance search does not do.
  -- So the instance is handed to `asIso` rather than searched for.
  haveI h := derivedSheafHomEvaluation_isIso_of_isPerfect Rc K
    (RingedSite.derivedStructureSheaf (ringedSite Rc))
    (RingedSite.derivedStructureSheaf (ringedSite Rc)) hK
  (λ_ K).symm ≪≫ ((derivedTensor Rc).mapIso (derivedDualStructureSheafIso Rc).symm).app K ≪≫
    @asIso _ _ _ _ (derivedSheafHomEvaluation Rc K
      (RingedSite.derivedStructureSheaf (ringedSite Rc))
      (RingedSite.derivedStructureSheaf (ringedSite Rc))) h

/-- The isomorphism `derivedBidualIso` is carried by the canonical map `derivedBidualMap`. -/
@[sga "6 I 7.2" "special case"]
theorem derivedBidualIso_hom (K : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    (derivedBidualIso Rc K hK).hom = derivedBidualMap Rc K :=
  rfl

/-- **Stacks 08DQ, second assertion.** Let `(X, O_X)` be a ringed space and let `K` be a perfect
object of `D(O_X)`. The canonical map

`K = RSheafHom(O_X, O_X) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, O_X), O_X) = (K^∨)^∨`

of `derivedBidualMap` is an isomorphism; equivalently `(K^∨)^∨ ≅ K`, which is
`derivedBidualIso`.

Perfectness of `K` is the only hypothesis. Its two outer factors are isomorphisms by
construction, and its middle factor — the derived evaluation morphism of Stacks 0A8U at
`L = M = O_X` — is an isomorphism by Stacks 0G40, which holds for every value of the two
variables specialised here. -/
@[stacks 08DQ "the second assertion: the canonical map \
`K = RSheafHom(O_X, O_X) ⊗^L K ⟶ (K^∨)^∨` of Stacks 0A8U is an isomorphism for a perfect `K`",
  sga "6 I 7.2" "special case"]
theorem isIso_derivedBidualMap (K : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    IsIso (derivedBidualMap Rc K) := by
  -- As at `derivedBidualIso`, the two ring-sheaf spellings make the category instance recorded
  -- in the goal's `IsIso` differ from the one in the type of `derivedBidualIso`, so the
  -- invertibility of an isomorphism's `hom` is supplied by name rather than searched for.
  rw [← derivedBidualIso_hom Rc K hK]
  exact Iso.isIso_hom (derivedBidualIso Rc K hK)

end Stacks.SheafOfModules

end
