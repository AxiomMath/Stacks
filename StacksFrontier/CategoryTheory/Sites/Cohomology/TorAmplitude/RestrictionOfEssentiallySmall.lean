module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensorOfEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocalDistinguishedTriangles
public import StacksFrontier.Homology.PseudoCoherent.Locality
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Finite Tor dimension restricts along the arrows of a site with large objects

Let `(C, O)` be a ringed site whose objects form a type in an arbitrary universe `c` while its
morphisms, the sections of `O` and the sections of its modules all lie in one universe `u`, let
`C` be essentially `u`-small, and let `T` be a family of derived tensor products, one on each
slice of the site.  Then finite Tor dimension of the restriction of an object of `D(O)` to the
slice over `V` forces finite Tor dimension of its restriction to the slice over `W`, for every
arrow `W ⟶ V`, in the same interval.

This is the predicate
`Stacks.SheafOfModules.DerivedTensorProduct.FiniteTorDimensionRestricts` discharged at that
universe shape.  It is what two *local* hypotheses read over a common refinement of their two
coverings need, since a member of the refinement is only an arrow into a member of one of the
coverings and a family of derived tensor products carries no relation between its members; and
it is the last input of Stacks 0DKR for a morphism of algebraic spaces, whose small étale site
has exactly this shape.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.finiteTorDimensionRestricts`:
  finite Tor dimension restricts along the arrows of the site, for every family `T`.
* `DerivedTensorProduct.OfEssentiallySmall.isZero_homology_derivedRestriction_tensorModule`:
  Tor amplitude of the restriction of `E` to the slice over `U` makes the restriction to that
  slice of the cohomology of `E ⊗^L_O G[0]` vanish outside the interval, for every `O`-module `G`
  on `C`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceTotalExtensionRestrictionIso`
  : the restriction to the slice over `V` of the extension by zero of `Tot(P|_W ⊗ G[0])` is the
  total complex formed over `V` from `P|_V` and the module `j_{W!}G|_V`.  This is the one use of
  Stacks 0E8I, and it is made on `C` itself, before any restriction.
* `Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.torTestIso`: the `i`-th
  cohomology of `Q(P)|_U ⊗^L G[0]` is the `i`-th homology sheaf of the ordinary total complex
  `Tot(P|_U ⊗ G[0])`, for `P` a K-flat complex of `O`-modules.
* `Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.restrictTorTestIso`: the `i`-th
  cohomology of the *restriction* of `Q(P) ⊗^L_O G[0]` is the `i`-th homology sheaf of that same
  ordinary total complex `Tot(P|_U ⊗ (G|_U)[0])`.  This is what lets a hypothesis about the
  derived tensor product formed on a slice be read against the restriction of the one formed on
  `C`, with no isomorphism between the two derived tensor products — and so no naturality for one
  — being needed.

## Implementation notes

The route is *not* the one the source takes, Stacks 08G1 followed by Stacks 0E8J: both are
available only on a ringed site whose objects, morphisms and sections lie in one universe.
Instead a K-flat representative `P` on `C` is chosen once; its restriction to every slice is
again K-flat, by Stacks 0E8K at this universe shape
(`Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.kFlat_restrictionComplex`), so the
field `comparisonLeft` of the datum turns Tor amplitude at a slice into a statement about the
*ordinary* total tensor complex formed there — and that statement does transport along an arrow
of the site.

The transport reflects a zero object on a *homology sheaf*, and not exactness of a complex.
That distinction is the whole of it: the unit `G ⟶ (j_{W!}G)|_W` of the extension-by-zero
adjunction is a monomorphism and is *not* split — the objectwise retraction, projecting the
direct sum of Stacks 03DI onto the summand indexed by the structure map, is not natural — so it
transports a vanishing statement about a single module but would not transport exactness of a
complex.  `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.isZero_of_isZero_over_extensionByZero`
is the form used, and `StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso`
is what moves the homology of a complex across the exact functor `j_{W!}` followed by `|_V`, in
one step, the composite of two exact functors being exact.

*The spellings of the sheaf of rings on a slice.*  Three occur among the inputs:
`(X.over U).O`, which the localized ringed site and hence `T U` and
`FiniteTorDimensionRestricts` carry; `X.O.over U`, which the total tensor complex, its
restriction to a slice and the comparison of Stacks 0E8I are stated at; and
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U`, which extension by
zero is stated at.  All are definitionally equal, and term-level elaboration crosses between
them without trouble — but `AlgebraicGeometry.RingedSite.over` is `@[implicit_reducible]`, which
is below the transparency instance synthesis runs at, so no instance stated at one spelling is
found at another.  `SliceModules` names the second spelling and the local instances below carry
the hypotheses across once; a failure to do so does not present as a missing instance but as a
`whnf` timeout.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G2](https://stacks.math.columbia.edu/tag/08G2)
* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall

universe u c d

open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (extension restriction
  extensionComplex restrictionComplex)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheafification on a slice, at the spelling of the localized ringed site. -/
local instance sliceHasSheafify (U : X.C) : HasSheafify (X.over U).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (X.J.over U) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences on a slice, at the localized spelling. -/
local instance sliceWEqualsLocallyBijective (U : X.C) :
    (X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- Restriction to a slice preserves finite limits, by Stacks 04IX. -/
local instance preservesFiniteLimits_restriction (U : X.C) :
    PreservesFiniteLimits (restriction X U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction to a slice preserves finite colimits, by Stacks 04IX. -/
local instance preservesFiniteColimits_restriction (U : X.C) :
    PreservesFiniteColimits (restriction X U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

/-- Sheaves of modules on a slice, at the spelling `X.O.over U` of the slice of the structure
sheaf, which is the one `Stacks.SheafOfModules.Tensor.tensorComplex` and the restriction of a
total tensor complex to a slice are stated at.  It is the same category as
`AlgebraicGeometry.RingedSite.Modules (X.over U)`, but the identification unfolds
`AlgebraicGeometry.RingedSite.over`, which is `@[implicit_reducible]` and so invisible to
instance synthesis; the three instances below carry the hypotheses across it once. -/
abbrev SliceModules (U : X.C) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{max c u, u, u} (X.O.over U))

/-- The tensor bifunctor of a slice is additive, at the spelling `X.O.over U`. -/
local instance sliceTensorAdditive (U : X.C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U)).Additive :=
  inferInstanceAs
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive

/-- The tensor bifunctor of a slice is additive in its second variable, at that spelling. -/
local instance sliceTensorObjAdditive (U : X.C) (M : SliceModules X U) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u}
      (X.O.over U)).obj M).Additive :=
  inferInstanceAs
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive

/-- Total complexes of the tensor bifunctor of a slice exist, at that spelling. -/
local instance sliceHasMapBifunctor (U : X.C)
    (K L : CochainComplex (SliceModules X U) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ) :=
  inferInstanceAs (HomologicalComplex.HasMapBifunctor K L
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O)
    (ComplexShape.up ℤ))

variable (V W : X.C)

/-- Extension by zero from the slice over `W`, followed by restriction to the slice over `V`.
It is an exact functor `Mod(O|_W) ⥤ Mod(O|_V)`, and it is the functor the reflection of zero
objects by extension by zero is read through. -/
abbrev extensionThenRestriction :
    RingedSite.Modules.{max c u, u, u} (X.over W) ⥤
      RingedSite.Modules.{max c u, u, u} (X.over V) :=
  extension X W ⋙ restriction X V


/-! ### The restriction to the slice over `V` of `j_{W!}Tot(P|_W ⊗ G[0])` -/

open Stacks.SheafOfModules.Tensor (tensorComplex tensorComplexFlipIso)
open AlgebraicGeometry.RingedSite (tensorComplexOverIso)
open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (tensorComplexExtensionIso)

variable (P : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)

/-- `Tot(P|_W ⊗_{O|_W} G[0])`, the total complex whose homology sheaves measure the Tor
amplitude of the restriction of `Q(P)` to the slice over `W` against the module `G`. -/
abbrev sliceTotal (G : SliceModules X W) : CochainComplex (SliceModules X W) ℤ :=
  ((tensorComplex.{max c u, u, u} (X.O.over W)).obj ((restrictionComplex X W).obj P)).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)

/-- **The restriction to the slice over `V` of the extension by zero of `Tot(P|_W ⊗ G[0])` is
the total complex formed over `V` from `P|_V` and the module `j_{W!}G|_V`.**

This is the one place Stacks 0E8I is used, and it is used on `C` itself, before any
restriction: the symmetry of the tensor product puts the extension by zero in the left slot,
`tensorComplexExtensionIso` moves it outside the total complex, the restriction of a total
tensor complex to a slice is `tensorComplexOverIso`, the symmetry puts `P|_V` back in the left
slot, and `HomologicalComplex.singleMapHomologicalComplex` identifies the extension by zero
followed by the restriction of a module placed in degree zero with the module `j_{W!}G|_V`
placed in degree zero. -/
def sliceTotalExtensionRestrictionIso (G : SliceModules X W) :
    (restrictionComplex X V).obj ((extensionComplex X W).obj (sliceTotal X W P G)) ≅
      ((tensorComplex.{max c u, u, u} (X.O.over V)).obj ((restrictionComplex X V).obj P)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((extensionThenRestriction X V W).obj G)) :=
  (restrictionComplex X V).mapIso ((extensionComplex X W).mapIso
      (tensorComplexFlipIso.{max c u, u, u} (X.O.over W) ((restrictionComplex X W).obj P)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) ≪≫
    (tensorComplexExtensionIso X W
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) P).symm) ≪≫
  tensorComplexOverIso X V
      ((extensionComplex X W).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) P ≪≫
  tensorComplexFlipIso.{max c u, u, u} (X.O.over V)
      ((restrictionComplex X V).obj ((extensionComplex X W).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))
      ((restrictionComplex X V).obj P) ≪≫
  ((tensorComplex.{max c u, u, u} (X.O.over V)).obj ((restrictionComplex X V).obj P)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex (extensionThenRestriction X V W)
      (ComplexShape.up ℤ) 0).app G)

/-! ### The derived tensor product on a slice, computed by a K-flat representative -/

variable [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

/-- The derived category of the modules on a slice, at the spelling `X.O.over U`. -/
local instance sliceHasDerivedCategory (U : X.C) :
    HasDerivedCategory.{d} (SliceModules X U) :=
  hSliceDerived U

/-- **`Q(P)|_U ⊗^L_{O|_U} G[0]` is the ordinary total complex `Tot(P|_U ⊗ G[0])`**, for `P` a
K-flat complex of `O`-modules.  The restriction of a K-flat complex to a slice is K-flat,
Stacks 0E8K, so the left-hand K-flat comparison of the derived tensor product on the slice
applies, with no hypothesis on the right-hand factor. -/
def derivedTensorSliceTotalIso (U : X.C)
    (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (hP : Stacks.SheafOfModules.IsKFlat X.O P) (G : SliceModules X U) :
    (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj P))).obj
        ((DerivedCategory.singleFunctor
          (RingedSite.Modules.{max c u, u, u} (X.over U)) 0).obj G) ≅
      DerivedCategory.Q.obj (sliceTotal X U P G) :=
  (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj P))).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (RingedSite.Modules.{max c u, u, u} (X.over U)) 0).app G) ≪≫
    TU.comparisonLeft ((restrictionComplex X U).obj P)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
      (Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.kFlat_restrictionComplex X U P hP)


omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)] hSliceDerived in
/-- **The vanishing of a homology sheaf descends from the slice over `V` to the slice over
`W`.** If the `i`-th homology of `j_{W!}Z|_V` vanishes, so does the `i`-th homology of `Z`.

Extension by zero and restriction to a slice are both exact, so their composite commutes with
the homology of a complex; the vanishing of `j_{W!}(H^i Z)|_V` then reflects down to `H^i Z` by
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.isZero_of_isZero_over_extensionByZero`, the
unit of the extension-by-zero adjunction being a monomorphism. -/
theorem isZero_homology_of_isZero_homology_extensionRestriction
    (p : W ⟶ V) (Z : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over W)) ℤ) (i : ℤ)
    (h : IsZero ((HomologicalComplex.homologyFunctor
      (RingedSite.Modules.{max c u, u, u} (X.over V)) (ComplexShape.up ℤ) i).obj
        (((extensionThenRestriction X V W).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))) :
    IsZero ((HomologicalComplex.homologyFunctor
      (RingedSite.Modules.{max c u, u, u} (X.over W)) (ComplexShape.up ℤ) i).obj Z) := by
  refine Stacks.Sites.ExtensionByZero.OfEssentiallySmall.isZero_of_isZero_over_extensionByZero
    (J := X.J) (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (p := p)
    ((HomologicalComplex.homologyFunctor
      (RingedSite.Modules.{max c u, u, u} (X.over W)) (ComplexShape.up ℤ) i).obj Z) ?_
  exact h.of_iso ((StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso
    (extensionThenRestriction X V W) i).app Z).symm


/-! ### Finite Tor dimension restricts along an arrow of the site -/

/-- Every derived object `E` is represented by a K-flat complex `P` on `C`, whose restriction to
each slice represents the restriction of `E`. -/
private theorem exists_kFlat_iso_restriction (X : RingedSite.{c, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
    [∀ U : X.C, HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]
    (E : RingedSite.DerivedModules.{c, u, u, d} X) :
    ∃ (P : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)
      (_ : Stacks.SheafOfModules.IsKFlat X.O P) (_ : DerivedCategory.Q.obj P ≅ E),
      ∀ U : X.C, Nonempty ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj E ≅
        DerivedCategory.Q.obj ((restrictionComplex X U).obj P)) := by
  obtain ⟨P, pr, hP, hqi⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    X.O (DerivedCategory.Q.objPreimage E)
  have _ := hqi
  have eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map pr) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  exact ⟨P, hP, eP, fun U => ⟨(RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso eP.symm ≪≫
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O) U).mapDerivedCategoryFactors.app P⟩⟩

/-- The `i`-th cohomology of `Q(P)|_U ⊗^L_{O|_U} G[0]`, for `P` a K-flat complex of `O`-modules,
is the `i`-th homology sheaf of the ordinary total complex `Tot(P|_U ⊗ G[0])`. -/
def torTestIso (U : X.C) (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (hP : Stacks.SheafOfModules.IsKFlat X.O P) (G : SliceModules X U) (i : ℤ) :
    (DerivedCategory.homologyFunctor
          (RingedSite.Modules.{max c u, u, u} (X.over U)) i).obj
        ((TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj P))).obj
          ((DerivedCategory.singleFunctor
            (RingedSite.Modules.{max c u, u, u} (X.over U)) 0).obj G)) ≅
      (HomologicalComplex.homologyFunctor (SliceModules X U) (ComplexShape.up ℤ) i).obj
        (sliceTotal X U P G) :=
  (DerivedCategory.homologyFunctor (RingedSite.Modules.{max c u, u, u} (X.over U)) i).mapIso
      (derivedTensorSliceTotalIso X P U TU hP G) ≪≫
    (DerivedCategory.homologyFunctorFactors (SliceModules X U) i).app (sliceTotal X U P G)

/-- **Finite Tor dimension restricts along the arrows of a site with large objects.**  For every
family `T` of derived tensor products on the slices of a ringed site whose objects form a type in
an arbitrary universe `c` while its morphisms, the sections of its structure sheaf and the
sections of its modules lie in one universe `u`, and whose underlying category is essentially
`u`-small: if the restriction of `E` to the slice over `V` has finite Tor dimension and
`p : W ⟶ V` is an arrow, then the restriction of `E` to the slice over `W` has finite Tor
dimension — in the *same* interval.

This discharges `Stacks.SheafOfModules.DerivedTensorProduct.FiniteTorDimensionRestricts`, and
with it the one-universe inputs it stood in for, Stacks 08G1 followed by Stacks 0E8J, are not
needed.  The route is the other one: a K-flat representative on `C` whose restriction to every
slice is again K-flat, which is Stacks 0E8K at this universe shape, turns Tor amplitude at a
slice into a statement about the *ordinary* total tensor complex there, through the field
`comparisonLeft` of `Stacks.SheafOfModules.DerivedTensorProduct`; and a vanishing statement about
ordinary total complexes does transport along `p`, by Stacks 0E8I followed by the reflection of
zero objects by extension by zero.

In detail: let `P` be K-flat on `C` with `Q(P) ≅ E`, let `G` be a module on the slice over `W`
and put `Z = Tot(P|_W ⊗ G[0])`.  Stacks 0E8I, applied on `C` itself and before any restriction,
identifies `j_{W!}Z|_V` with `Tot(P|_V ⊗ (j_{W!}G|_V)[0])`, whose cohomology vanishes outside the
interval by the hypothesis at `V`; extension by zero and restriction to a slice are exact, so
that is the vanishing of `j_{W!}(H^i Z)|_V`, and the unit of the extension-by-zero adjunction
being a monomorphism reflects it down to `H^i Z`.

No splitting of that unit is used, and none is available: what is reflected is a zero object on a
homology sheaf, not exactness of a complex. -/
@[sga "4½ Th_finitude 1.7" "partial", sga "6 I 5.6.1" "a), special case"]
theorem finiteTorDimensionRestricts
    (T : ∀ U : X.C, DerivedTensorProduct.{max c u, u, u, d} (X.over U)) :
    FiniteTorDimensionRestricts.{c, u, u, d} T := by
  intro V W p E h
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨P, hP, eP, eR⟩ := exists_kFlat_iso_restriction X E
  replace eR := fun U => (eR U).some
  refine ⟨a, b, fun G i hi => ?_⟩
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor _ i).mapIso (((T W).tensor.mapIso (eR W)).app _) ≪≫
      torTestIso X P W (T W) hP G i)
  refine isZero_homology_of_isZero_homology_extensionRestriction X V W p
    (sliceTotal X W P G) i ?_
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
    (sliceTotalExtensionRestrictionIso X V W P G))
  exact (hab ((extensionThenRestriction X V W).obj G) i hi).of_iso
    (((DerivedCategory.homologyFunctor _ i).mapIso (((T V).tensor.mapIso (eR V)).app _) ≪≫
      torTestIso X P V (T V) hP ((extensionThenRestriction X V W).obj G) i).symm)

/-! ### The restriction of a global derived tensor product with a module -/

/-- **`(Q(P) ⊗^L_O G[0])|_U` is the ordinary total complex `Tot(P|_U ⊗ (G|_U)[0])`**, for `P` a
K-flat complex of `O`-modules and `G` a sheaf of `O`-modules.

This is the companion of `derivedTensorSliceTotalIso` on the other side of the restriction: that
one computes the derived tensor product formed *on the slice* by the same ordinary total complex,
and this one computes the restriction of the derived tensor product formed on `C`.  Together they
compare the two derived tensor products without any isomorphism between them being named, and
without naturality, which neither is available for.

The four steps are: the field `comparisonLeft` of `T`, which computes `Q(P) ⊗^L_O Q(G[0])` as the
ordinary total complex `Tot(P ⊗_O G[0])` with no hypothesis on the right-hand factor; the
factorization of the derived restriction through the restriction of complexes, restriction to a
slice being exact by Stacks 04IX; the underived compatibility
`AlgebraicGeometry.RingedSite.tensorComplexOverIso` of the total tensor complex with restriction;
and `HomologicalComplex.singleMapHomologicalComplex`, the restriction of a module placed in
degree zero being the restricted module placed in degree zero. -/
def restrictDerivedTensorSliceTotalIso (U : X.C)
    (T : DerivedTensorProduct.{c, u, u, d} X)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P) (G : RingedSite.Modules.{c, u, u} X) :
    (RingedSite.derivedRestriction.{c, u, u, d} X U).obj
        ((T.tensor.obj (DerivedCategory.Q.obj P)).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{c, u, u} X) 0).obj G)) ≅
      DerivedCategory.Q.obj (sliceTotal X U P ((restriction X U).obj G)) :=
  (RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso
      ((T.tensor.obj (DerivedCategory.Q.obj P)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ (RingedSite.Modules.{c, u, u} X) 0).app G) ≪≫
        T.comparisonLeft P ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) hP) ≪≫
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O) U).mapDerivedCategoryFactors.app
      (((tensorComplex.{c, u, u} X.O).obj P).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) ≪≫
    DerivedCategory.Q.mapIso (tensorComplexOverIso X U P
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) ≪≫
    DerivedCategory.Q.mapIso
      (((tensorComplex.{max c u, u, u} (X.O.over U)).obj ((restrictionComplex X U).obj P)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (restriction X U)
          (ComplexShape.up ℤ) 0).app G))

/-- The `i`-th cohomology of the restriction to the slice over `U` of `Q(P) ⊗^L_O G[0]`, for `P` a
K-flat complex of `O`-modules, is the `i`-th homology sheaf of the ordinary total complex
`Tot(P|_U ⊗ (G|_U)[0])` — the same complex `torTestIso` computes the slice-formed derived tensor
product by. -/
def restrictTorTestIso (U : X.C) (T : DerivedTensorProduct.{c, u, u, d} X)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P) (G : RingedSite.Modules.{c, u, u} X) (i : ℤ) :
    (DerivedCategory.homologyFunctor
          (RingedSite.Modules.{max c u, u, u} (X.over U)) i).obj
        ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj
          ((T.tensor.obj (DerivedCategory.Q.obj P)).obj
            ((DerivedCategory.singleFunctor (RingedSite.Modules.{c, u, u} X) 0).obj G))) ≅
      (HomologicalComplex.homologyFunctor (SliceModules X U) (ComplexShape.up ℤ) i).obj
        (sliceTotal X U P ((restriction X U).obj G)) :=
  (DerivedCategory.homologyFunctor (RingedSite.Modules.{max c u, u, u} (X.over U)) i).mapIso
      (restrictDerivedTensorSliceTotalIso X P U T hP G) ≪≫
    (DerivedCategory.homologyFunctorFactors (SliceModules X U) i).app
      (sliceTotal X U P ((restriction X U).obj G))

/-- **Tor amplitude of a restriction bounds the restricted homology of the global derived tensor
product.**  If the restriction of `E` to the slice over `U` has Tor amplitude in `[a, b]` for a
derived tensor product `TU` formed there, then for every sheaf of `O`-modules `G` on `C` and every
`i` outside `[a, b]` the restriction to that slice of the `i`-th cohomology of `E ⊗^L_O G[0]`
vanishes.

This is the per-member input of the descent of Tor amplitude from a covering family: the
hypothesis is read at the module `G|_U` rather than at `G`.  What makes that legitimate is that
the two derived tensor products — the one on `C` whose value is restricted, and the one on the
slice against which the hypothesis is stated — are computed by *one and the same ordinary total
complex* `Tot(A|_U ⊗ (G|_U)[0])`, for `A` a K-flat complex representing `E`: by `torTestIso` on
the slice side and by `restrictTorTestIso` on the restricted side.  The restriction of `A` is
K-flat by Stacks 0E8K at this universe shape, which is what both comparisons need.

Only vanishing is transported, so no naturality of either comparison is used, and none is
available for them. -/
theorem isZero_homology_derivedRestriction_tensorModule (U : X.C)
    (T : DerivedTensorProduct.{c, u, u, d} X)
    (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{c, u, u, d} X) (a b : ℤ)
    (hamp : HasTorAmplitude TU ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj E) a b)
    (G : RingedSite.Modules.{c, u, u} X) (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor
        (RingedSite.Modules.{max c u, u, u} (X.over U)) i).obj
      ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj
        ((T.tensor.obj E).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{c, u, u} X) 0).obj G)))) := by
  obtain ⟨A, hA, eA, eR⟩ := exists_kFlat_iso_restriction X E
  obtain ⟨eR⟩ := eR U
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor _ i).mapIso
        ((RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso
          ((T.tensor.mapIso eA.symm).app _)) ≪≫
      restrictTorTestIso X A U T hA G i)
  exact (hamp ((restriction X U).obj G) i hi).of_iso
    (((DerivedCategory.homologyFunctor _ i).mapIso ((TU.tensor.mapIso eR).app _) ≪≫
      torTestIso X A U TU hA ((restriction X U).obj G) i).symm)

end Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall

end
