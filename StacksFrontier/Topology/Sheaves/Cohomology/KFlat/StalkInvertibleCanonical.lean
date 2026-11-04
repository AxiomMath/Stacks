module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor
public import StacksFrontier.Homology.Tor.CanonicalTensorDerivedBifunctor
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkInvertibleTransport

/-!
# Invertibility passes to the derived stalk, at the two named monoidal structures

`Stacks.SheafOfModules.DerivedTensorStalk.isInvertible_derivedStalk_of_isInvertible` takes the
two monoidal structures on `D(𝒪)` and `D(𝒪_x)` as arguments, each with a pairwise comparison
of its tensor product and an identification of its unit. This file supplies those data for the
two structures the development actually states invertibility in, and so reads that statement as

**Invertibility passes to derived stalks.** If `K` is an invertible object of `D(𝒪)` for the
symmetric monoidal structure of [Stacks, Tag 0FPT] — which is the structure of
[Stacks, Tag 0FPB] on a ringed space — then the derived stalk `K_x` is an invertible object of
`D(𝒪_x)` for the symmetric monoidal structure of [Stacks, Tag 0FNQ].

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorStalk.stalkMonoidal`,
  `Stacks.SheafOfModules.DerivedTensorStalk.stalkBraided`: the symmetric monoidal structure of
  [Stacks, Tag 0FNQ] on `D(𝒪_x)`, read at the `RingCat`-valued spelling of the stalk ring.
* `Stacks.SheafOfModules.DerivedTensorStalk.stalkTensorComparison`,
  `Stacks.SheafOfModules.DerivedTensorStalk.stalkUnitComparison`: its tensor product and its
  unit, compared with the K-flat descent of [Stacks, Tag 06YU] and with the stalk ring in
  degree zero.

## Main results

* `Stacks.SheafOfModules.DerivedTensorStalk.isInvertible_derivedStalk`: the statement above.

Clause (1)(a) itself is about Gorensteinness, and this is only its stalkwise input. The
Gorenstein-form direction "invertible dualizing complex ⟹ Gorenstein scheme" is
`Stacks.Duality.isGorenstein_of_isInvertible_dualizingComplex` in
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/GlobalInvertible.lean`, which composes
this statement with clause (1)(b) across the two spellings of the stalk ring.

## The converse

The converse — an object of `D(𝒪)` whose derived stalks are all invertible is invertible — is
not a stalkwise statement: invertibility of an object becomes a statement about a morphism only
through the unit evaluation `R𝓗om(K, 𝒪) ⊗^𝐋 K ⟶ 𝒪`, and `R𝓗om` does not commute with stalks.
What *is* local is invertibility on a covering by opens,
`Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction`, and that is
what clause (1)(a) of [Stacks, Tag 0BFQ] is proved from, affine locally, in
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/DualizingInvertible.lean`.

## Implementation notes

Every piece of the stalk side is a *named* definition with an ascribed type rather than an
instance. Two spellings of the stalk ring meet here — the `RingCat`-valued stalk that
`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over, and the `CommRing`
obtained from it by `StacksDraft.StalkTensor.commRing_stalk_ringSheaf`, which is what
[Stacks, Tag 0FNQ] is stated over — and they are definitionally but not syntactically equal, so
instance search does not cross between them while a conversion check does. Ascribing each
definition is what puts the crossing in a conversion check; the same device is used by
`Stacks.SheafOfModules.DerivedTensorStalk.stalkKFlatQ_isLocalization`.

The model of `D(𝒪_x)` is pinned to `HasDerivedCategory.standard`, because the monoidal
structure of [Stacks, Tag 0FNQ] exists only there.
`Stacks.SheafOfModules.DerivedTensorStalk.stalkStd` names that instance so that each definition
below can seat it in its own statement.

## References

* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules

universe u

namespace Stacks.SheafOfModules.DerivedTensorStalk

attribute [local instance] Stacks.SheafOfModules.KFlatStalkCriterion.monoidalStalkModuleCat
  Stacks.SheafOfModules.KFlatStalkCriterion.monoidalPreadditiveStalkModuleCat
  stalkKFlatQ_isLocalization stalkKFlatQLeft_isLocalization
  SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {Z : TopCat.{u}}
  (Rc : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology Z) CommRingCat.{u})
  (x : Z)

/-! ### Seating the structure of `Mod(𝒪_Z)`

Each of these is a named instance for the reason
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorHomAdjunction` records: the universes
of the site `Opens Z` and of the sections of `𝒪_Z` coincide, so instance search would have to
solve `max ?u ?v =?= u` with both unknown. -/

/-- Weak equivalences of presheaves of abelian groups on `Opens Z` are the locally bijective
morphisms. Instance search does reach this, but only through the essential smallness of the
site, and that search is deep enough that rerunning it inside each graded-tensor goal below
exhausts the synthesis budget; naming it here answers those goals immediately. -/
local instance wEqualsLocallyBijectiveSpace :
    (Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

/-- `⊗_{𝒪_Z}` is additive in its first variable. -/
local instance sheafTensorAdditiveSpace :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Rc).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive (J := Opens.grothendieckTopology Z) Rc

/-- `ℱ ⊗_{𝒪_Z} -` is additive. -/
local instance sheafTensorObjAdditiveSpace (A : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Rc)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Rc).obj A).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive (J := Opens.grothendieckTopology Z) Rc A

/-- The monoidal structure on `Mod(𝒪_Z)` whose tensor product is `⊗_{𝒪_Z}`. -/
local instance monoidalSpace : MonoidalCategory
    (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc) :=
  SheafOfModules.monoidalCategorySheafTensor (J := Opens.grothendieckTopology Z) Rc

/-- The graded tensor products of `𝒪_Z`-modules exist. -/
local instance hasTensorSpace : ∀ (X₁ X₂ : GradedObject ℤ
    (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc)), GradedObject.HasTensor X₁ X₂ :=
  fun _ _ => inferInstance

/-- The left-bracketed triple graded tensor products of `𝒪_Z`-modules are good. -/
local instance hasGoodTensor₁₂TensorSpace : ∀ (X₁ X₂ X₃ : GradedObject ℤ
    (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := fun _ _ _ => inferInstance

/-- The right-bracketed triple graded tensor products of `𝒪_Z`-modules are good. -/
local instance hasGoodTensorTensor₂₃Space : ∀ (X₁ X₂ X₃ : GradedObject ℤ
    (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := fun _ _ _ => inferInstance

/-- A morphism out of a fourfold graded tensor product of `𝒪_Z`-modules is determined on the
summands. -/
local instance hasTensor₄ObjExtSpace : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ
    (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := fun _ _ _ _ => inferInstance

variable [HasDerivedCategory.{u + 1} (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc)]

/-! ### The monoidal structure of Tag 0FNQ at the stalk ring -/

/-- The standard model of `D(𝒪_x)`, at the `RingCat`-valued spelling of the stalk ring. The
monoidal structure of [Stacks, Tag 0FNQ] exists only at this model. -/
abbrev stalkStd : HasDerivedCategory.{u + 1} (ModuleCat.{u} (stalkRing Rc x)) :=
  HasDerivedCategory.standard _

/-- **The monoidal structure of [Stacks, Tag 0FNQ] on `D(𝒪_x)`**, read at the `RingCat`-valued
spelling of the stalk ring. -/
@[instance_reducible]
def stalkMonoidal :
    letI := stalkStd Rc x
    MonoidalCategory (DerivedCategory (ModuleCat.{u} (stalkRing Rc x))) :=
  (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (stalkRing Rc x : Type u)).choose

/-- **The commutativity constraint of [Stacks, Tag 0FNQ] on `D(𝒪_x)`** — the Koszul symmetry —
read at the `RingCat`-valued spelling of the stalk ring. -/
@[instance_reducible]
def stalkBraided :
    letI := stalkStd Rc x
    letI := stalkMonoidal Rc x
    BraidedCategory (DerivedCategory (ModuleCat.{u} (stalkRing Rc x))) :=
  (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (stalkRing Rc x : Type u)).choose_spec.choose.toBraidedCategory

/-- The tensor product of [Stacks, Tag 0FNQ] on `D(𝒪_x)` is the K-flat descent of
[Stacks, Tag 06YU] at every pair of objects. This is
`CochainComplex.DerivedTensor.monoidalTensorObjIsoDerivedBifunctorObj` read at the
`RingCat`-valued spelling of the stalk ring. -/
def stalkTensorComparison :
    letI := stalkStd Rc x
    letI := stalkMonoidal Rc x
    ∀ A B : DerivedCategory (ModuleCat.{u} (stalkRing Rc x)),
      A ⊗ B ≅ ((CochainComplex.KFlatBifunctor.derivedBifunctor
        (curriedTensor (ModuleCat.{u} (stalkRing Rc x)))).obj A).obj B :=
  fun A B => CochainComplex.DerivedTensor.monoidalTensorObjIsoDerivedBifunctorObj
    (stalkRing Rc x : Type u) A B

/-- The unit of [Stacks, Tag 0FNQ] on `D(𝒪_x)` is the stalk ring in degree zero. This is
`CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj` read at the `RingCat`-valued
spelling of the stalk ring. -/
def stalkUnitComparison :
    letI := stalkStd Rc x
    letI := stalkMonoidal Rc x
    𝟙_ (DerivedCategory (ModuleCat.{u} (stalkRing Rc x))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (stalkRing Rc x)) 0).obj
        (ModuleCat.of (stalkRing Rc x) (stalkRing Rc x)) :=
  CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj (stalkRing Rc x : Type u)

/-! ### Invertibility passes to derived stalks -/

/-- **An invertible object of `D(𝒪)` has invertible derived stalks.** An invertible object of
`D(𝒪)` for the symmetric monoidal structure of [Stacks, Tag 0FPT] has, at every point, an
invertible derived stalk in `D(𝒪_x)` for the symmetric monoidal structure of
[Stacks, Tag 0FNQ].

This is a stalkwise input to [Stacks, Tag 0BFQ], clause (1)(a), not the clause, which is about
Gorensteinness: the direction it feeds — an invertible dualizing complex makes the scheme
Gorenstein — is `Stacks.Duality.isGorenstein_of_isInvertible_dualizingComplex`, and the clause is
`Stacks.Duality.isGorenstein_iff_isInvertible_dualizingComplex`. -/
public theorem isInvertible_derivedStalk
    (K : DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc))
    (hK : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Rc
      CategoryTheory.MonoidalCategory.IsInvertible K) :
    letI := stalkStd Rc x
    letI := stalkMonoidal Rc x
    CategoryTheory.MonoidalCategory.IsInvertible ((derivedStalk Rc x).obj K) :=
  let := stalkStd Rc x
  let : ∀ (left right : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
      HomologicalComplex.HasMapBifunctor left right
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Rc) (ComplexShape.up ℤ) :=
    fun left right => Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor Rc left right
  isInvertible_derivedStalk_of_isInvertible Rc x
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Rc)
    (stalkMonoidal Rc x) (stalkBraided Rc x)
    (fun A B => ((CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso
      (Stacks.SheafOfModules.DerivedMonoidal.Mod Rc)
      (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Rc)).app A).app B)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Rc)
    (stalkTensorComparison Rc x) (stalkUnitComparison Rc x) K hK

end Stacks.SheafOfModules.DerivedTensorStalk

end
