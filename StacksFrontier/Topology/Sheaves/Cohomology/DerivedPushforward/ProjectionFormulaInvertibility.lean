module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.CategoryTheory.Category.CompositionChains

/-!
# Invertibility of the derived projection-formula map

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`.
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap` ([Stacks, Tag 0B53]) is the
canonical morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`.

[Stacks, Tag 08EU] asserts that it is an *isomorphism* when `f` is a quasi-compact and
quasi-separated morphism of schemes and `E`, `K` lie in `D_QCoh(𝒪_X)`, `D_QCoh(𝒪_Y)`.  This file
proves two things about that assertion: that it is invariant under isomorphism in each variable,
unconditionally; and that it holds at `K = 𝒪_Y[0]` — the case the source's proof calls
immediate — for an arbitrary morphism of ringed spaces and an arbitrary `E`, from the
right-unitor coherence of the comparison of [Stacks, Tag 079U], which is carried.

## Main results

* `isIso_projectionFormulaMap_of_iso_right` and `isIso_projectionFormulaMap_congr_right`:
  invertibility of the projection-formula map depends on `K` only through its isomorphism class.
* `isIso_projectionFormulaMap_of_iso_left` and `isIso_projectionFormulaMap_congr_left`: the same
  in the source complex `E`.
* `isIso_projectionFormulaMap_unitObject`: **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`**, for an
  arbitrary morphism of ringed spaces and an arbitrary `E ∈ D(𝒪_X)`, carrying the right unitors
  of the two derived tensor products, the unit comparison `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` and the
  right-unitor coherence of [Stacks, Tag 079U] as explicit hypotheses.
* `pullbackPushforwardTensorMap` and `isIso_pullbackPushforwardTensorMap_iff`: the canonical map
  `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K`, and the observation that it is invertible exactly when the
  projection-formula map at the source complex `𝒪_X[0]` is.
* `derivedPushforwardDerivedPullbackIsoOfIsIso`: [Stacks, Tag 08I9] in the form the source states
  it — arbitrary `K`, derived tensor product — carrying invertibility of the projection-formula
  map at `𝒪_X[0]`, that is [Stacks, Tag 08EU] at that source complex, as the one hypothesis.
* `pullbackPushforwardTensorMap_natural` and
  `derivedPushforwardDerivedPullbackIsoOfIsIso_hom_natural`: that map, and that isomorphism, are
  natural in `K`, on the naturality of the carried left unit law.  The map's naturality is
  unconditional; the isomorphism's statement needs the invertibility at `K` and at `K'`, only
  because it is what makes the two horizontal arrows isomorphisms at all.

## What is carried, and why

The source's proof of [Stacks, Tag 08EU] is a dévissage in `K`: reduce to `Y` affine, then to
`K` a direct sum of shifts of `𝒪_Y` using that all three functors commute with direct sums and
are exact functors of triangulated categories, then to `K = 𝒪_Y[k]`, where the claim is
immediate.  Three inputs of that argument are unavailable in this library, and each is carried
as a named hypothesis of `isIso_projectionFormulaMap_unitObject` rather than hidden:

*The right unitors of the two derived tensor products,* `ρY : Rf_*E ⊗^𝐋_{𝒪_Y} 𝒪_Y ≅ Rf_*E` and
`ρX`.  These exist — they are
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`, [Stacks, Tag 0FPT] — but
that declaration is indexed by an `AlgebraicGeometry.RingedSite`, while the projection-formula
map is indexed by a `RingedSpace`, and the two sheaf-of-rings spellings are not interchangeable
by instance search.  They are therefore taken as hypotheses, in the shape in which `rightUnitIso`
supplies them.

*Naturality of the right unitor on `X`,* `hρX`.  Proved, but not in the shape consumed here.
It is true that the file constructing `rightUnitIso` proves no naturality statement about it —
`leftUnitIso_eq`, an unfolding by `rfl`, is the only theorem in that file, and the pentagon, the
hexagon and the unit triangles are declared out of scope there.  It is proved in a different
module: `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ConstraintNaturality.lean`, through
`rightUnitTrans_app_Q` and `rightUnitIso_hom_eq`, which give the unitor's value at the class of
a complex as `comparisonRight ≫ Q (tensorComplexUnitIso)`.  Two mismatches, neither
mathematical, keep it a hypothesis here: that statement is *curried*,
`(T.tensor.map u).app (unitObject X)`, where `hρX` is uncurried, so crossing to it is
`Functor.uncurry_obj_map` followed by `map_id` and `comp_id`; and it is indexed by a
`RingedSite`, which is the mismatch already described for `ρY` and `ρX`.  The same directory's
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RightUnitorNaturality.lean` proves `rightUnitorNatIso_naturality_uncurry` in precisely `hρX`'s
shape, but about a parallel right unitor whose identification with `rightUnitIso` that file
records as not established.  The ordinary unit isomorphism
`Stacks.SheafOfModules.tensorComplexUnitIso` is natural too, by
`tensorComplexUnitIso_hom_naturality` in the same module.

*The unit comparison* `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`.  Constructed, in
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/UnitComparison.lean`: it composes
`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso`, which gives
`Lf^*(F[0]) ≅ (f^*F)[0]` for a flat `𝒪_Y`-module `F`, at the unit — flat by
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit` — with the degree-zero image of the
ordinary `f^*𝒪_Y ≅ 𝒪_X` of `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, and
`derivedPullbackSingleUnitIso_inv_comp_derivedPullbackUnitIso_hom` records that on
representatives it is that ordinary comparison and nothing more.  Only two of the three
spellings of the sheaf of rings arise: both ingredients are stated over
`structureSheafRing`, and the
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf` that flatness is stated over is the same
expression, by `StacksDraft.KFlat.ringSheaf_eq`.  It remains a hypothesis below, which keeps
this file independent of that one; no mathematics is missing.

*The right-unitor coherence of [Stacks, Tag 079U],* `hcoh`: that the comparison
`Lf^*(Z ⊗^𝐋_{𝒪_Y} 𝒪_Y) ⟶ Lf^*Z ⊗^𝐋_{𝒪_X} Lf^*𝒪_Y`, followed by `𝟙 ⊗ ν` and the right unitor on
`X`, is `Lf^*` of the right unitor on `Y`.  This is the derived analogue of
`Stacks.RingedSpace.comparison_rightUnitor`, which is the corresponding statement for the
*ordinary* comparison of [Stacks, Tag 01CD].  The derived statement is **proved**, as
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_app_q_of_kFlat` in
`ProjectionFormulaUnitKFlat.lean`, for an arbitrary morphism of ringed spaces and with no
hypothesis; `isIso_projectionFormulaMap_unitObject_unconditional` (`:541` of that file) is this
file's theorem with all five of its binders supplied from it, from
`Stacks.RingedSpace.derivedTensorRightUnitorNatIso` and from `derivedPullbackUnitIso`.  The
binders are kept here so that this file depends on none of that, which is what makes it the
place the base case is proved abstractly.

Nothing else is assumed: in particular no quasi-compactness, no quasi-separatedness, no
quasi-coherence, and no hypothesis on `E`, which is more general in those respects than the
source.  What is *not* done is the dévissage itself, so the invertibility of the
projection-formula map at a general `K` in `D_QCoh(𝒪_Y)` is not proved here.

## Implementation notes

*Why the base case is formal once the coherence is known.*  The whole of it is already in
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj`, an abstract
lemma about an adjunction `L ⊣ R`, two bifunctors and a morphism of bifunctors between them:
the projection-formula map at the unit object, composed with the unitors and the unit
comparison, is the unitor of the source, by the triangle identity.  That lemma was written for
the *ordinary* projection formula of [Stacks, Tag 0FZE]; it mentions no geometry and no derived
category, so it applies verbatim to the derived adjunction `Lf^* ⊣ Rf_*`, the two derived tensor
products and the comparison of [Stacks, Tag 079U].  Nothing connects the two: the map of
[Stacks, Tag 0B53] *is* that abstract morphism, by definition, which is what
`projectionFormulaMap_eq` records.

*The two restrictions of [Stacks, Tag 08I9].*
`Stacks.AlgebraicGeometry.DerivedAffinePushforward` proves [Stacks, Tag 08I9] with the ordinary
tensor product in place of `⊗^𝐋` and with `E` a module in degree zero.  Both restrictions are
lifted by one proposition, and `isIso_pullbackPushforwardTensorMap_iff` identifies it: the
invertibility of the projection-formula map at the *source* complex `𝒪_X[0]` and an arbitrary
`K`, which is [Stacks, Tag 08EU] at `E = 𝒪_X[0]`.  That is a statement about arbitrary `K`, not
about `K = 𝒪_Y[0]`, so the base case proved here does not discharge it and the two restrictions
are not lifted; `derivedPushforwardDerivedPullbackIsoOfIsIso` carries it as a hypothesis and
derives the unrestricted form of [Stacks, Tag 08I9] from it.

*The second leg is passed positionally.*  In `isIso_pullbackPushforwardTensorMap_iff` the
invertibility of `Rf_*` of the unit law is handed to `CategoryTheory.isIso_comp_right_iff` as an
explicit argument rather than left to instance search.  It has to be:
`Stacks.DerivedTensor.RingedSite.Modules Y.sheaf` and
`SheafOfModules (structureSheafRing Y)` are the same category carrying two
`Category` instances that are equal but not syntactically so, and instance search matches local
hypotheses only up to reducible unfolding, so it does not find the hypothesis even though it is
in context.

*The unit object is written out.*  `𝒪_Y[0]` appears as
`(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)` rather than as
`Stacks.DerivedTensor.RingedSite.unitObject`, which is the same object but indexed by a
`RingedSite`; writing it out keeps this file free of that indexing.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Invariance under isomorphism in each variable

Every step of the source's dévissage replaces `K` by an isomorphic object, so the first thing
its argument needs is that invertibility of the projection-formula map is a property of the
isomorphism class.  Both statements below are unconditional, and both are pure consequences of
the naturality of the map proved in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula`. -/

/-- If `a.hom ≫ g = f ≫ b.hom` for isomorphisms `a`, `b` and `f` is invertible, so is `g`. -/
private theorem isIso_of_square {C : Type*} [Category C] {A B A' B' : C} (a : A ≅ A')
    (b : B ≅ B') {g : A' ⟶ B'} {f : A ⟶ B} (h : a.hom ≫ g = f ≫ b.hom) [IsIso f] : IsIso g :=
  have : IsIso (f ≫ b.hom) := inferInstance
  IsIso.of_isIso_fac_left h

/-- **Invertibility of the projection-formula map transports along an isomorphism of the target
complex.**  Naturality in `K` exhibits the map at `K'` as the map at `K` conjugated by two
isomorphisms. -/
theorem isIso_projectionFormulaMap_of_iso_right
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (i : K ≅ K') (h : IsIso (projectionFormulaMap f E K)) :
    IsIso (projectionFormulaMap f E K') := by
  exact isIso_of_square
    (((derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj E)).mapIso i)
    ((derivedPushforward f).mapIso (((derivedTensorProductFunctor X.sheaf).obj E).mapIso
      ((derivedPullback f).mapIso i))) (projectionFormulaMap_natural_right f E i.hom)

/-- Invertibility of the projection-formula map depends on the target complex only through its
isomorphism class. -/
theorem isIso_projectionFormulaMap_congr_right
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (i : K ≅ K') :
    IsIso (projectionFormulaMap f E K) ↔ IsIso (projectionFormulaMap f E K') :=
  ⟨isIso_projectionFormulaMap_of_iso_right f E i,
    isIso_projectionFormulaMap_of_iso_right f E i.symm⟩

/-- **Invertibility of the projection-formula map transports along an isomorphism of the source
complex.** -/
theorem isIso_projectionFormulaMap_of_iso_left
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : E ≅ E')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso (projectionFormulaMap f E K)) :
    IsIso (projectionFormulaMap f E' K) := by
  exact isIso_of_square (((derivedTensorProductFunctor Y.sheaf).mapIso
      ((derivedPushforward f).mapIso e)).app K)
    ((derivedPushforward f).mapIso (((derivedTensorProductFunctor X.sheaf).mapIso e).app
      ((derivedPullback f).obj K))) (projectionFormulaMap_natural_left f e.hom K)

/-- Invertibility of the projection-formula map depends on the source complex only through its
isomorphism class. -/
theorem isIso_projectionFormulaMap_congr_left
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : E ≅ E')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso (projectionFormulaMap f E K) ↔ IsIso (projectionFormulaMap f E' K) :=
  ⟨isIso_projectionFormulaMap_of_iso_left f e K,
    isIso_projectionFormulaMap_of_iso_left f e.symm K⟩

/-! ### The base case: the target complex is the structure sheaf -/

/-- The structure sheaf of a ringed space placed in degree zero, as an object of `D(𝒪)`.  This is
`Stacks.DerivedTensor.RingedSite.unitObject` written out, so that this file does not have to
index anything by an `AlgebraicGeometry.RingedSite`. -/
abbrev singleUnit (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :=
  (DerivedCategory.singleFunctor (Modules Z.sheaf) 0).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))

/-- **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`.**  For an arbitrary morphism of ringed spaces
`f : X ⟶ Y` and an arbitrary `E` in `D(𝒪_X)`, the derived projection-formula morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} 𝒪_Y ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*𝒪_Y)`

is an isomorphism.  This is the case the source's proof calls immediate, and it is the base of
its dévissage in the target complex.

Four inputs are carried, all visible in the statement: the right unitors `ρY` and `ρX` of the
two derived tensor products — these are
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`, which is indexed by a
`RingedSite` rather than by a `RingedSpace` — the naturality `hρX` of the one on `X`, the unit
comparison `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, and the right-unitor coherence `hcoh` of the comparison
of [Stacks, Tag 079U].  The last is the derived analogue of
`Stacks.RingedSpace.comparison_rightUnitor`, and it is proved — see
`rightUnitorCoherence_app_q_of_kFlat` in `ProjectionFormulaUnitKFlat.lean`, which with the other
four inputs yields `isIso_projectionFormulaMap_unitObject_unconditional`, this statement with
nothing carried.  The binders stay here because this declaration is the abstract base case, used
at ringed spaces where none of the four is constructed.

No quasi-compactness, quasi-separatedness or quasi-coherence is used, and `E` is arbitrary, so
in those respects the statement is more general than the source's. -/
theorem isIso_projectionFormulaMap_unitObject
    (ρY : ∀ Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      ((derivedTensorProductFunctor Y.sheaf).obj Z).obj (singleUnit Y) ≅ Z)
    (ρX : ∀ W : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj W).obj (singleUnit X) ≅ W)
    (ν : (derivedPullback f).obj (singleUnit Y) ≅ singleUnit X)
    (hρX : ∀ {W W' : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X))} (u : W ⟶ W'),
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((u ×ₘ 𝟙 (singleUnit X)) :
            ((W, singleUnit X) : _ × _) ⟶ (W', singleUnit X)) ≫ (ρX W').hom =
        (ρX W).hom ≫ u)
    (hcoh : ∀ Z : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing Y)),
      (pullbackTensorComparison f).app (Z, singleUnit Y) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((𝟙 ((derivedPullback f).obj Z) ×ₘ ν.hom) :
              (((derivedPullback f).obj Z, (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
                ((derivedPullback f).obj Z, singleUnit X)) ≫
            (ρX ((derivedPullback f).obj Z)).hom =
        (derivedPullback f).map (ρY Z).hom)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMap f E (singleUnit Y)) :=
  Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj
    (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparison f) ρY ρX ν (fun u => hρX u) hcoh E

/-! ### What the two restrictions of [Stacks, Tag 08I9] cost

[Stacks, Tag 08I9] is the special case `E = 𝒪_X[0]` of [Stacks, Tag 08EU], as the comments on
its page observe.  The declarations below make that precise: they build the map of
[Stacks, Tag 08I9] out of the projection-formula map at `𝒪_X[0]`, and show that its
invertibility is equivalent to invertibility of the projection-formula map there.  Nothing in
this section is conditional except where a hypothesis is named. -/

/-- **The canonical morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K`** of [Stacks, Tag 08I9]: the
derived projection-formula morphism at the source complex `𝒪_X[0]`, followed by the direct image
of the left unit law `𝒪_X ⊗^𝐋_{𝒪_X} Lf^*K ≅ Lf^*K`, which is carried as the
hypothesis `unitLeft`. -/
def pullbackPushforwardTensorMap
    (unitLeft : ∀ W : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).obj W ≅ W)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((derivedTensorProductFunctor Y.sheaf).obj
        ((derivedPushforward f).obj (singleUnit X))).obj K ⟶
      (derivedPushforward f).obj ((derivedPullback f).obj K) :=
  projectionFormulaMap f (singleUnit X) K ≫
    (derivedPushforward f).map (unitLeft ((derivedPullback f).obj K)).hom

/-- The morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K` is invertible exactly when the
projection-formula morphism at the source complex `𝒪_X[0]` is: the second leg of the composite
is the direct image of an isomorphism.  So [Stacks, Tag 08EU] at `E = 𝒪_X[0]` is precisely what
[Stacks, Tag 08I9] needs, with no restriction on `K` and with the derived tensor product. -/
theorem isIso_pullbackPushforwardTensorMap_iff
    (unitLeft : ∀ W : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).obj W ≅ W)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso (pullbackPushforwardTensorMap f unitLeft K) ↔
      IsIso (projectionFormulaMap f (singleUnit X) K) := by
  have hiso : IsIso ((derivedPushforward f).map (unitLeft ((derivedPullback f).obj K)).hom) :=
    ((derivedPushforward f).mapIso (unitLeft ((derivedPullback f).obj K))).isIso_hom
  exact @isIso_comp_right_iff _ _ _ _ _ (projectionFormulaMap f (singleUnit X) K)
    ((derivedPushforward f).map (unitLeft ((derivedPullback f).obj K)).hom) hiso

/-- **[Stacks, Tag 08I9] in the form the source states it**, as an isomorphism

`Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ≅ Rf_*Lf^*K`,

for an arbitrary `K` in `D(𝒪_Y)` and with the *derived* tensor product — the two restrictions
carried by `Stacks.AlgebraicGeometry.DerivedAffinePushforward` both lifted — on the single
hypothesis `h` that the projection-formula morphism is invertible at the source complex
`𝒪_X[0]`, which is [Stacks, Tag 08EU] at `E = 𝒪_X[0]`.  No affineness is used: for `f` affine
and `K` in `D_QCoh(𝒪_Y)`, `h` is exactly what the source proves. -/
def derivedPushforwardDerivedPullbackIsoOfIsIso
    (unitLeft : ∀ W : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).obj W ≅ W)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso (projectionFormulaMap f (singleUnit X) K)) :
    ((derivedTensorProductFunctor Y.sheaf).obj
        ((derivedPushforward f).obj (singleUnit X))).obj K ≅
      (derivedPushforward f).obj ((derivedPullback f).obj K) :=
  have : IsIso (pullbackPushforwardTensorMap f unitLeft K) :=
    (isIso_pullbackPushforwardTensorMap_iff f unitLeft K).2 h
  asIso (pullbackPushforwardTensorMap f unitLeft K)

/-- **The morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K` of [Stacks, Tag 08I9] is natural in `K`**,
as soon as the left unit law it is built from is: the first leg is natural by
`projectionFormulaMap_natural_right`, and the second is `Rf_*` of the unit law at `Lf^*K`, whose
naturality is `hunitLeft` read at `Lf^*k`.

Naturality of `unitLeft` is carried rather than assumed of the particular family, exactly as
the family itself is: `Stacks.RingedSpace.derivedTensorLeftUnitor_naturality` supplies it for
the canonical derived tensor product of a ringed space. -/
theorem pullbackPushforwardTensorMap_natural
    (unitLeft : ∀ W : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).obj W ≅ W)
    (hunitLeft : ∀ {W W' : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X))} (w : W ⟶ W'),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).map w ≫ (unitLeft W').hom =
        (unitLeft W).hom ≫ w)
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (k : K ⟶ K') :
    ((derivedTensorProductFunctor Y.sheaf).obj
          ((derivedPushforward f).obj (singleUnit X))).map k ≫
        pullbackPushforwardTensorMap f unitLeft K' =
      pullbackPushforwardTensorMap f unitLeft K ≫
        (derivedPushforward f).map ((derivedPullback f).map k) := by
  have hunit : (derivedPushforward f).map
          (((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).map
            ((derivedPullback f).map k)) ≫
        (derivedPushforward f).map (unitLeft ((derivedPullback f).obj K')).hom =
      (derivedPushforward f).map (unitLeft ((derivedPullback f).obj K)).hom ≫
        (derivedPushforward f).map ((derivedPullback f).map k) :=
    ((derivedPushforward f).map_comp _ _).symm.trans
      ((congrArg (derivedPushforward f).map
          (hunitLeft ((derivedPullback f).map k))).trans
        ((derivedPushforward f).map_comp _ _))
  exact comp_chain_one_square_assoc
    (projectionFormulaMap_natural_right f (singleUnit X) k) hunit

/-- **[Stacks, Tag 08I9] in the form the source states it is natural in the complex.**  The
isomorphism of `derivedPushforwardDerivedPullbackIsoOfIsIso` is `asIso` of the morphism
`pullbackPushforwardTensorMap`, so this is `pullbackPushforwardTensorMap_natural` read on the
two isomorphisms; the invertibility hypotheses enter only through the existence of the two
isomorphisms and play no part in the square. -/
theorem derivedPushforwardDerivedPullbackIsoOfIsIso_hom_natural
    (unitLeft : ∀ W : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).obj W ≅ W)
    (hunitLeft : ∀ {W W' : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X))} (w : W ⟶ W'),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).map w ≫ (unitLeft W').hom =
        (unitLeft W).hom ≫ w)
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (k : K ⟶ K')
    (h : IsIso (projectionFormulaMap f (singleUnit X) K))
    (h' : IsIso (projectionFormulaMap f (singleUnit X) K')) :
    ((derivedTensorProductFunctor Y.sheaf).obj
          ((derivedPushforward f).obj (singleUnit X))).map k ≫
        (derivedPushforwardDerivedPullbackIsoOfIsIso f unitLeft K' h').hom =
      (derivedPushforwardDerivedPullbackIsoOfIsIso f unitLeft K h).hom ≫
        (derivedPushforward f).map ((derivedPullback f).map k) :=
  pullbackPushforwardTensorMap_natural f unitLeft hunitLeft k

end Stacks.Cohomology.DerivedProjectionFormula

end
