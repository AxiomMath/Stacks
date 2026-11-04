module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# Tor amplitude in `[a, ∞)` on a ringed space, for the derived tensor product of Tag 06YU

Tag 08FZ (1) defines Tor amplitude in an interval. This file states its half-infinite case
`[a, ∞)` on a ringed space, against the *genuine* derived tensor product
`Stacks.Cohomology.TorAmplitude.derTensor`, which is the construction of Tag 06YU at the site of
opens, and it is the operation the duality development of Tag 0E2N tensors with. It also states
the version tested on an open cover, which is the hypothesis Tag 0E2N puts on its tensor factor.

Everything beyond the two definitions is transported, not reproved: the site-level development
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE` already carries Tag 0F1M for an
arbitrary derived tensor product on an arbitrary ringed site, and a ringed space is the ringed
site of its opens. What was missing was the identification of the two packagings of a derived
tensor product, which is `ofRingedSiteDerivedTensorProduct` below.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.ofRingedSiteDerivedTensorProduct`: a derived
  tensor product over the structure sheaf of a ringed site, read as a derived tensor product on
  `D(O)`. This is the inverse of the existing
  `Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct`, and like it
  carries every field across unchanged.
* `Stacks.Cohomology.TorAmplitude.derTensorSite`: the derived tensor product of Tag 06YU on a
  ringed space, in that packaging.
* `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE`: **Tag 08FZ (1) for `[a, ∞)`**, on a ringed
  space and for the tensor product of Tag 06YU.
* `Stacks.Cohomology.TorAmplitude.LocallyHasTorAmplitudeGE`: the same tested on the members of
  some open cover, which is what "locally has Tor amplitude in `[a, ∞)`" means.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_eq_site`: the predicate below *is* the
  site-level one at the ringed site of opens, by definition. Every lemma of the site-level
  development therefore applies, and those below are that development read here.
* `Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_hasTorAmplitude`: Tor amplitude in
  `[a, b]` bounds the amplitude below.
* `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE.of_iso` and
  `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE.mono`: transport along an isomorphism of
  `D(O_X)`, and a smaller bound is a weaker condition.
* `Stacks.Cohomology.TorAmplitude.isZero_homology_of_hasTorAmplitudeGE` and
  `Stacks.Cohomology.TorAmplitude.isGE_of_hasTorAmplitudeGE`: an object of Tor amplitude in
  `[a, ∞)` is itself concentrated in degrees `≥ a`.
* `Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_iff_exists_kFlatRepresentative`:
  **Tag 0F1M on a ringed space.** Tor amplitude in `[a, ∞)` is equivalent to being represented
  by a K-flat complex of flat `O_X`-modules vanishing in every degree below `a`.

## Implementation notes

**Why a second packaging exists at all.** `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`
is indexed by a sheaf of rings on a site and is the one the existence theorem of Tag 06YU
inhabits; `Stacks.SheafOfModules.DerivedTensorProduct` is indexed by a bundled
`AlgebraicGeometry.RingedSite` and is the one the Tor-amplitude development is stated at. The
two structures have the same fields in the same order, and their types agree because the two
abbreviations spelling K-flatness — `Stacks.SheafOfModules.IsKFlat` and
`Stacks.DerivedTensor.RingedSite.KFlat` — unfold to the same condition; so the conversion is
field-by-field in both directions. Only one direction was present. This is a presentational
duplication and not a mathematical one, and the two definitions are left where they are; the
conversion is what makes the duplication harmless.

**The predicate is a definitional unfolding of the site-level one, not a copy.** The `rfl` of
`hasTorAmplitudeGE_eq_site` is what makes that true, and it is why no proof below repeats a
site-level argument. It is stated and proved rather than left implicit so that a later change to
either definition breaks here rather than silently splitting the vocabulary in two.

**The local predicate carries no transport lemma.** `HasTorAmplitudeGE X E a` does not imply
`LocallyHasTorAmplitudeGE X E a` by anything in this library: passing between them needs the
compatibility of the derived tensor product of Tag 06YU with restriction to an open, which is
not proved. The same is true of the existing
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`, whose shape this definition
follows and which it deliberately mirrors rather than generalises: that one localises *finite*
Tor dimension, i.e. amplitude in *some* interval, and this one localises amplitude in a
*prescribed* half-infinite interval, so neither is an instance of the other.

**Universes.** The space, its structure sheaf and its modules share a universe, as they already
must for `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`; the derived category's own hom
universe stays independent, and the restrictions in the local predicate are allowed a second
one, exactly as in `LocallyHasFiniteTorDimension`.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

universe u d d'

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- A derived tensor product over the structure sheaf of a ringed site, read as a derived tensor
product on `D(O)`. The two packagings differ only in which of two equal abbreviations spells
K-flatness, so every field is carried across unchanged; this is the inverse of
`toRingedSiteDerivedTensorProduct`. -/
def ofRingedSiteDerivedTensorProduct
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d, u} X.O) :
    DerivedTensorProduct.{u, u, u, d} X where
  tensor := T.tensor
  comparison := T.comparison
  comparison_naturality := T.comparison_naturality
  comparisonRight := T.comparisonRight
  comparisonRight_naturality := T.comparisonRight_naturality
  comparisonRight_eq_comparison := T.comparisonRight_eq_comparison
  comparisonLeft := T.comparisonLeft
  comparisonLeft_naturality := T.comparisonLeft_naturality
  comparisonLeft_eq_comparison := T.comparisonLeft_eq_comparison
  toTensor := T.toTensor
  toTensor_naturality := T.toTensor_naturality
  toTensor_eq_comparisonRight := T.toTensor_eq_comparisonRight
  toTensor_eq_comparisonLeft := T.toTensor_eq_comparisonLeft
  commShift₂ := T.commShift₂
  exact_left := T.exact_left
  exact_right := T.exact_right

/-- The bifunctor of a derived tensor product is unchanged by the change of packaging. -/
@[simp]
theorem ofRingedSiteDerivedTensorProduct_tensor
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d, u} X.O) :
    (ofRingedSiteDerivedTensorProduct T).tensor = T.tensor :=
  rfl

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Stacks.Cohomology.TorAmplitude

section Space

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]

/-- `HasDerivedCategory` at the spelling the Tag 06YU development is stated at. The type is
`OXMod X` by `rfl`, but an instance proved at one spelling does not fire at the other. -/
local instance hasDerivedCategoryModulesOfRingSheaf :
    HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u} X))

/-- **The derived tensor product of Tag 06YU on a ringed space, in the site-level packaging.**
A ringed space is the ringed site of its opens, so `derTensor X` is a derived tensor product on
that ringed site; this is it, read through `ofRingedSiteDerivedTensorProduct`. -/
def derTensorSite :
    Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
      (Stacks.RingedSpace.toRingedSite X) :=
  Stacks.SheafOfModules.DerivedTensorProduct.ofRingedSiteDerivedTensorProduct (derTensor X)

/-- The bifunctor of `derTensorSite` is that of `derTensor`. -/
@[simp]
theorem derTensorSite_tensor : (derTensorSite X).tensor = (derTensor X).tensor :=
  rfl

/-- **Tag 08FZ (1), Tor amplitude in `[a, ∞)`.** An object of `D(O_X)` has Tor amplitude in
`[a, ∞)` when its derived tensor product with every `O_X`-module, placed in degree `0`, has
vanishing cohomology in every degree below `a`. The derived tensor product is the one of
Tag 06YU, as for `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`. -/
def HasTorAmplitudeGE (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]
    (E : DerivedCategory (OXMod.{u} X)) (a : ℤ) : Prop :=
  ∀ (F : OXMod.{u} X) (i : ℤ), i < a →
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} X) i).obj
      (((derTensor X).tensor.obj E).obj
        ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F)))

/-- **The predicate above is the site-level one at the ringed site of opens.** Stated so that a
later change to either definition is caught here. -/
theorem hasTorAmplitudeGE_eq_site (E : DerivedCategory (OXMod.{u} X)) (a : ℤ) :
    HasTorAmplitudeGE X E a =
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE (derTensorSite X) E a :=
  rfl

/-- **Tor amplitude in a bounded interval bounds the amplitude below.** -/
theorem hasTorAmplitudeGE_of_hasTorAmplitude (E : DerivedCategory (OXMod.{u} X)) (a b : ℤ)
    (hE : HasTorAmplitude X E a b) :
    HasTorAmplitudeGE X E a :=
  Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_hasTorAmplitude
    (derTensorSite X) E a b hE

/-- **Tor amplitude in `[a, ∞)` transports along an isomorphism of `D(O_X)`.** -/
theorem HasTorAmplitudeGE.of_iso {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]
    {E E' : DerivedCategory (OXMod.{u} X)} {a : ℤ} (hE : HasTorAmplitudeGE X E a)
    (e : E' ≅ E) :
    HasTorAmplitudeGE X E' a :=
  Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE.of_iso
    (T := derTensorSite X) hE e

/-- **A smaller lower bound is a weaker condition.** -/
theorem HasTorAmplitudeGE.mono {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]
    {E : DerivedCategory (OXMod.{u} X)} {a a' : ℤ} (hE : HasTorAmplitudeGE X E a)
    (h : a' ≤ a) :
    HasTorAmplitudeGE X E a' :=
  fun F i hi => hE F i (lt_of_lt_of_le hi h)

/-- **An object of Tor amplitude in `[a, ∞)` is concentrated in degrees `≥ a`.** Its derived
tensor product with the structure sheaf in degree zero is itself. -/
theorem isZero_homology_of_hasTorAmplitudeGE (E : DerivedCategory (OXMod.{u} X)) (a : ℤ)
    (hE : HasTorAmplitudeGE X E a) (i : ℤ) (hi : i < a) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} X) i).obj E) :=
  Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_of_hasTorAmplitudeGE
    (derTensorSite X) E a hE i hi

/-- **An object of Tor amplitude in `[a, ∞)` lies in `D^{≥ a}(O_X)`.** -/
theorem isGE_of_hasTorAmplitudeGE (E : DerivedCategory (OXMod.{u} X)) (a : ℤ)
    (hE : HasTorAmplitudeGE X E a) :
    E.IsGE a := by
  rw [DerivedCategory.isGE_iff]
  exact fun i hi => isZero_homology_of_hasTorAmplitudeGE X E a hE i hi

/-- **Tag 0F1M, the direction producing the representative.** An object of `D(O_X)` with Tor
amplitude in `[a, ∞)` is represented by a K-flat complex of flat `O_X`-modules vanishing in
every degree below `a`. -/
theorem exists_kFlatRepresentative_of_hasTorAmplitudeGE
    (E : DerivedCategory (OXMod.{u} X)) (a : ℤ) (hE : HasTorAmplitudeGE X E a) :
    ∃ K : CochainComplex (OXMod.{u} X) ℤ,
      Stacks.SheafOfModules.IsKFlat X.sheaf K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i)) ∧
      (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) :=
  Stacks.SheafOfModules.DerivedTensorProduct.exists_kFlatRepresentative_of_hasTorAmplitudeGE
    (derTensorSite X) E a hE

/-- **Tag 0F1M on a ringed space.** An object `E` of `D(O_X)` has Tor amplitude in `[a, ∞)`
exactly when it is represented by a K-flat complex of flat `O_X`-modules vanishing in every
degree below `a`. -/
theorem hasTorAmplitudeGE_iff_exists_kFlatRepresentative
    (E : DerivedCategory (OXMod.{u} X)) (a : ℤ) :
    HasTorAmplitudeGE X E a ↔
      ∃ K : CochainComplex (OXMod.{u} X) ℤ,
        Stacks.SheafOfModules.IsKFlat X.sheaf K ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K ≅ E) :=
  Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_iff_exists_kFlatRepresentative
    (derTensorSite X) E a

end Space

section Local

attribute [local instance] restrictModules_preservesFiniteLimits
attribute [local instance] restrictModules_preservesFiniteColimits

/-- **Tor amplitude in `[a, ∞)`, tested locally.** The restriction of the object to each member
of some open cover of `X` has Tor amplitude in `[a, ∞)`. This is the hypothesis Tag 0E2N puts on
its tensor factor, and the shape is that of
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`. -/
def LocallyHasTorAmplitudeGE (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)]
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u} X)) (a : ℤ) : Prop :=
  ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i : I, HasTorAmplitudeGE (X.restrict (U i).isOpenEmbedding)
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
        (U i)).mapDerivedCategory.obj E) a

end Local

end Stacks.Cohomology.TorAmplitude

end
