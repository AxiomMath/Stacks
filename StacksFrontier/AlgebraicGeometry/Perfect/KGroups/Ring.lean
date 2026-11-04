module

public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Saturation
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectKGroupRing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# The multiplication on the `K`-group of perfect complexes supported on a closed subscheme

Let `Z` be a closed subscheme of a scheme `X`. The derived tensor product of two perfect
objects of `D(𝒪_X)` whose cohomology sheaves are supported on `Z` is again perfect with
cohomology supported on `Z`, so `D_{Z, perf}(𝒪_X)` is a tensor triangulated subcategory of
`D(𝒪_X)` and its `K`-group carries an associative and commutative multiplication
`[K] · [L] = [K ⊗^𝐋_{𝒪_X} L]`. No unit comes with it: `𝒪_X` in degree zero has support all of
`X`, so it lies in `D_{Z, perf}(𝒪_X)` only when the closed subset underlying `Z` is all of `X`,
and in general the multiplication has no unit
(`AlgebraicGeometry.exists_supportedPerfect_not_exists_unit`, in
`StacksFrontier/AlgebraicGeometry/Perfect/KGroups/NoUnit.lean`).

## Main definitions

* `AlgebraicGeometry.supportedPerfectProperty`: the object property cutting out
  `D_{Z, perf}(𝒪_X)`, written out once rather than inline.
* `AlgebraicGeometry.supportedPerfectNonUnitalTensorStructure`: the non-unital tensor structure
  on `D_{Z, perf}(𝒪_X)` given by the derived tensor product of Tag 06YU.

## Main results

* `SheafOfModules.supp_subset_iff_forall_isZero_stalk`: the support of a sheaf of modules is
  contained in a subset exactly when its stalks vanish off that subset.
* `AlgebraicGeometry.cohomologySupportedOn_iff_forall_supp_subset`: the same for a derived
  object, matching the `AlgebraicGeometry.CohomologySupportedOn` of Tag 08DA against the
  cohomology-support condition `D_{Z, perf}(𝒪_X)` is defined by.
* `AlgebraicGeometry.supportedPerfect_canonicalDerivedTensorProduct`: the derived tensor
  product of a supported perfect object with *any* perfect object is a supported perfect
  object.
* `AlgebraicGeometry.supportedPerfectNonUnitalTensorStructure_tensor_obj`: the bifunctor of
  that tensor structure is the derived tensor product, read on underlying objects.
* `AlgebraicGeometry.supportedPerfectTensorObj`: that derived tensor product as an object of
  `D_{Z, perf}(𝒪_X)`.
* `AlgebraicGeometry.exists_supportedPerfect_nonUnitalCommRing` ([stacks 0FDN]): the `K`-group
  of `D_{Z, perf}(𝒪_X)` carries a non-unital commutative ring structure whose additive group
  is the one it already has and whose product of the classes of two objects is the class of
  their derived tensor product.

## Implementation notes

The ring axioms are not reproved here.
`CategoryTheory.Pretriangulated.K0.NonUnitalTensorStructure` and its `restrict` and
`exists_nonUnitalCommRing` already supply them for an arbitrary tensor triangulated category,
asking only for *object-level* associativity and commutativity isomorphisms, which is all `K₀`
can see; `NonUnitalCommRing` is exactly "a multiplication, distributive, associative and
commutative, with no unit asserted", which is what the source claims. The ambient tensor
structure on `D(𝒪_X)` is `AlgebraicGeometry.RingedSpace.derivedTensorStructure`, built for
Tag 0FDK, taken at the derived tensor product of Tag 06YU.

So the only new input is the closure of the object condition under the derived tensor product,
and it splits:

* perfectness is Tag 09J5,
  `AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct`;
* the support condition is
  `Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left`, the
  stalkwise argument through the derived form of Tag 01CB. It needs the support hypothesis on
  **one** factor only, so the closure proved here is stronger than closure of the subcategory
  under its tensor product: a supported perfect object tensored with an arbitrary perfect
  object is supported.

Two spelling seams are crossed, both by `rfl`:

* perfectness of a derived object has two fully-qualified names,
  `AlgebraicGeometry.RingedSpace.IsPerfect` (which `D_{Z, perf}(𝒪_X)` is defined with) and
  `Stacks.Cohomology.PerfectComplexes.IsPerfect` (which carries the Tag 08CM attribute). They
  are the same predicate: `AlgebraicGeometry.RingedSpace.isPerfect_iff_isPerfect` below is
  `Iff.rfl`.
* the support condition is stated over `StrictlyPerfect.OXMod X.toRingedSpace` and Tag 08DA's
  `CohomologySupportedOn` over
  `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)`. That seam is already
  recorded in the tree and is not restated here:
  `AlgebraicGeometry.RingedSpace.structureSheafOfRings_eq_tensorRingSheaf`
  (`StacksFrontier/Topology/Sheaves/Modules/StalkRestrictOpenExactness.lean:148`) and
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.modules_eq_OXMod`
  (`StacksFrontier/Topology/Sheaves/Cohomology/KFlat/OnARingedSpace.lean:103`) are the two `rfl`s
  that cross it, and `cohomologySupportedOn_iff_forall_supp_subset` below simply states the two
  sides at the two spellings and lets the elaborator cross it once.

The tagged statement is proved in term mode, from `nonUnitalCommRing`,
`nonUnitalCommRing_toAddCommGroup` and `mul_cls` directly, and not by `obtain`-ing the three
parts out of `exists_nonUnitalCommRing`. Entering tactic mode makes Lean
elaborate `exists_nonUnitalCommRing` with no expected type, so the six instances of the
pretriangulated structure of the full subcategory are searched for instead of being read off
the goal, and the search exceeds the heartbeat budget. With the expected type present the same
statement checks in seconds.

The derived-category model is `CategoryTheory.HasDerivedCategory.standard`, because the derived
form of Tag 01CB is available in that model only
(`Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left` is
stated there); the four earlier Tag 0FDN declarations leave the model a binder. The source
quantifies over no derived-category model, so this is a choice of model and not a hypothesis.

The remaining assertion of the source, that `K₀(D_{Z, perf}(𝒪_X))` has no unit in general, is
`AlgebraicGeometry.exists_supportedPerfect_not_exists_unit` in
`StacksFrontier/AlgebraicGeometry/Perfect/KGroups/NoUnit.lean`: for `X = Spec ℤ` and
`Z = Spec(ℤ/2)` the class of `(ℤ/2)^~` is nonzero and its product with every class vanishes.

## References

* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry StrictlyPerfect
open Stacks.DerivedTensor.RingedSite

universe u d

/-! ### The support of a sheaf of modules, as vanishing of stalks -/

namespace SheafOfModules

/-- **The support of a sheaf of modules is contained in a subset exactly when its stalks vanish
off that subset.** Membership in the support is nontriviality of the stalk, and an object of the
category of abelian groups is a zero object exactly when it is a subsingleton. -/
theorem supp_subset_iff_forall_isZero_stalk {X : TopCat.{u}}
    {R : TopCat.Sheaf RingCat.{u} X} (F : SheafOfModules.{u} R) (T : Set X) :
    supp F ⊆ T ↔ ∀ x : X, x ∉ T →
      IsZero ((show TopCat.Presheaf Ab.{u} X from F.val.presheaf).stalk x) := by
  constructor
  · intro h x hx
    exact AddCommGrpCat.isZero_iff_subsingleton.2 <| subsingleton_of_forall_eq 0 fun c =>
      Classical.byContradiction fun hc => hx (h ⟨c, hc⟩)
  · rintro h x ⟨a, ha⟩
    by_contra hxT
    exact ha ((AddCommGrpCat.isZero_iff_subsingleton.1 (h x hxT)).elim a 0)

end SheafOfModules

/-! ### The two names for perfectness -/

namespace AlgebraicGeometry.RingedSpace

/-- The two fully-qualified names for perfectness of an object of `D(𝒪_X)` are the same
predicate. `AlgebraicGeometry.RingedSpace.IsPerfect` is the one `D_{Z, perf}(𝒪_X)` is defined
with; `Stacks.Cohomology.PerfectComplexes.IsPerfect` is the one carrying the Tag 08CM
attribute. -/
theorem isPerfect_iff_isPerfect (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : DerivedCategory (OXMod.{u, u} X)) :
    IsPerfect K ↔ Stacks.Cohomology.PerfectComplexes.IsPerfect K :=
  Iff.rfl

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **Tag 08DA's cohomological support condition is the one `D_{Z, perf}(𝒪_X)` is defined
by.** `AlgebraicGeometry.CohomologySupportedOn` asks that every cohomology sheaf have vanishing
stalks off the subset; `D_{Z, perf}(𝒪_X)` asks that every cohomology sheaf have support inside
it. -/
theorem cohomologySupportedOn_iff_forall_supp_subset (X : RingedSpace.{u, u})
    (T : Set X.carrier) (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)) :
    CohomologySupportedOn (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) T E ↔
      ∀ n : ℤ, SheafOfModules.supp
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj E) ⊆ T :=
  forall_congr' fun n =>
    (SheafOfModules.supp_subset_iff_forall_isZero_stalk
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj E) T).symm

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The object property cutting out `D_{Z, perf}(𝒪_X)`: perfect objects of `D(𝒪_X)` all of
whose cohomology sheaves are set-theoretically supported on the closed subscheme. It is the
property `AlgebraicGeometry.supportedPerfectDerivedCategory` is the full subcategory on. -/
abbrev supportedPerfectProperty :
    ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :=
  fun K => RingedSpace.IsPerfect K ∧
    ∀ n : ℤ, SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
        Set.range i.base

/-- `D_{Z, perf}(𝒪_X)` is the full subcategory on
`AlgebraicGeometry.supportedPerfectProperty`. -/
theorem supportedPerfectDerivedCategory_eq :
    (supportedPerfectProperty i).FullSubcategory = supportedPerfectDerivedCategory i :=
  rfl

omit [IsClosedImmersion i] in
/-- **The derived tensor product of a supported perfect object with a perfect object is a
supported perfect object.** Perfectness is Tag 09J5. For the support: the derived stalk of a
derived tensor product is the derived tensor product of the derived stalks over the stalk ring
(the derived form of Tag 01CB), and the derived tensor product is exact, hence additive, in its
first variable, so a first factor with vanishing derived stalk off `Z` gives a product with
vanishing derived stalk off `Z`.

Only the first factor is assumed supported, which is more than the closure of
`D_{Z, perf}(𝒪_X)` under its tensor product needs. -/
theorem supportedPerfect_canonicalDerivedTensorProduct
    (A B : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hA : supportedPerfectProperty i A)
    (hB : RingedSpace.IsPerfect (X := X.toRingedSpace) B) :
    supportedPerfectProperty i
      (((canonicalDerivedTensorProduct X.toRingedSpace.sheaf).tensor.obj A).obj B) :=
  ⟨RingedSpace.isPerfect_canonicalDerivedTensorProduct X.toRingedSpace A B hA.1 hB,
    (cohomologySupportedOn_iff_forall_supp_subset X.toRingedSpace _ _).1
      (Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left
        X.toRingedSpace.sheaf _ A B
        ((cohomologySupportedOn_iff_forall_supp_subset X.toRingedSpace _ _).2 hA.2))⟩

/-- **The non-unital tensor structure on `D_{Z, perf}(𝒪_X)`.** The tensor structure of Tag 0FDK
on `D(𝒪_X)`, at the derived tensor product of Tag 06YU, restricted to the supported perfect
objects: they form a triangulated subcategory
(`AlgebraicGeometry.isTriangulated_supportedPerfect`) closed under the derived tensor product
(`AlgebraicGeometry.supportedPerfect_canonicalDerivedTensorProduct`).

No unit object is asked for and none is produced: `𝒪_X` in degree zero has support all of `X`,
so it is a supported perfect object only when the closed subset underlying `Z` is all of `X`. -/
def supportedPerfectNonUnitalTensorStructure :
    K0.NonUnitalTensorStructure (supportedPerfectDerivedCategory i) :=
  @K0.NonUnitalTensorStructure.restrict _ _ _ _ _ _ _
    (RingedSpace.derivedTensorStructure X.toRingedSpace
      (canonicalDerivedTensorProduct X.toRingedSpace.sheaf)).toNonUnitalTensorStructure
    (supportedPerfectProperty i) (isTriangulated_supportedPerfect i)
    (fun A B hA hB => supportedPerfect_canonicalDerivedTensorProduct i A B hA hB.1)

/-- **The bifunctor of `AlgebraicGeometry.supportedPerfectNonUnitalTensorStructure` is the
derived tensor product of Tag 06YU**, read on underlying objects. This is what pins the
multiplication below to the tensor product the source names, rather than to some unspecified
bifunctor. -/
theorem supportedPerfectNonUnitalTensorStructure_tensor_obj
    (K L : supportedPerfectDerivedCategory i) :
    (((supportedPerfectNonUnitalTensorStructure i).tensor.obj K).obj L).obj =
      ((canonicalDerivedTensorProduct X.toRingedSpace.sheaf).tensor.obj K.obj).obj L.obj :=
  rfl

/-- The derived tensor product of two supported perfect objects, as an object of
`D_{Z, perf}(𝒪_X)` — the underlying object is the derived tensor product of Tag 06YU and the
membership proof is `AlgebraicGeometry.supportedPerfect_canonicalDerivedTensorProduct`. -/
def supportedPerfectTensorObj (K L : supportedPerfectDerivedCategory i) :
    supportedPerfectDerivedCategory i :=
  ⟨((canonicalDerivedTensorProduct X.toRingedSpace.sheaf).tensor.obj K.obj).obj L.obj,
    supportedPerfect_canonicalDerivedTensorProduct i _ _ K.property L.property.1⟩

/-- The underlying object of `AlgebraicGeometry.supportedPerfectTensorObj` is the derived
tensor product of Tag 06YU. -/
theorem supportedPerfectTensorObj_obj (K L : supportedPerfectDerivedCategory i) :
    (supportedPerfectTensorObj i K L).obj =
      ((canonicalDerivedTensorProduct X.toRingedSpace.sheaf).tensor.obj K.obj).obj L.obj :=
  rfl

/-- **Stacks Project, Tag 0FDN.** The `K`-group `K₀(D_{Z, perf}(𝒪_X))` of the perfect objects
of `D(𝒪_X)` supported on a closed subscheme `Z` carries a non-unital commutative ring
structure: its additive group is the one `K₀` already has, and the product of the classes of
two objects is the class of their derived tensor product. Associativity,
commutativity and distributivity are the fields of `NonUnitalCommRing`; no unit is asserted,
and none exists in general: `AlgebraicGeometry.exists_supportedPerfect_not_exists_unit`. -/
@[stacks 0FDN "the multiplication on `K_0(D_{Z, perf}(O_X))` given by the derived tensor \
product, together with its associativity and commutativity -- the fields of \
`NonUnitalCommRing`. Stated at the standard derived-category model, which the source does not \
fix. The absence of a unit in general is \
`AlgebraicGeometry.exists_supportedPerfect_not_exists_unit`; the definition of the \
subcategory and its three adjectives are in `StacksFrontier/AlgebraicGeometry/Perfect/KGroups/Basic.lean` and `StacksFrontier/AlgebraicGeometry/Perfect/KGroups/Saturation.lean`"]
theorem exists_supportedPerfect_nonUnitalCommRing :
    ∃ r : NonUnitalCommRing (K0 (supportedPerfectDerivedCategory i)),
      r.toAddCommGroup = (inferInstance : AddCommGroup (K0 (supportedPerfectDerivedCategory i))) ∧
        ∀ K L : supportedPerfectDerivedCategory i,
          r.mul (K0.cls K) (K0.cls L) = K0.cls (supportedPerfectTensorObj i K L) :=
  ⟨(supportedPerfectNonUnitalTensorStructure i).nonUnitalCommRing,
    (supportedPerfectNonUnitalTensorStructure i).nonUnitalCommRing_toAddCommGroup,
    fun K L => (supportedPerfectNonUnitalTensorStructure i).mul_cls K L⟩

end AlgebraicGeometry

end
