module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormalFree
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermInteriorSource

/-!
# The third and fourth spots of the sequence of Stacks 0E3V, at the source's `Inf` terms

`Deformation.Examples.exact_schemeMorphismSixTerm_secondSpot_localizedTangent` restates exactness
at the **second** spot of the sequence of [Stacks Project, Tag 0E3V]

`Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X ⟶ Y} → T(Def_X × Def_Y)`

with the second term the source's `Deformation.localizedAutomorphismFunctorTangent QX` ×
`Deformation.localizedAutomorphismFunctorTangent QY`,
by bridging to `Deformation.Examples.globalLiftsOverBaseAutPair` at the two chosen *dual-number*
pushforwards. This file does the same for the **third** and **fourth** spots.

The third and fourth spots run through `Deformation.Examples.liftClass` and
`Deformation.Examples.schemeMorphismDerivationTangentMap`, which exist only once the common base
of the two endpoint deformations is `(Deformation.squareZeroExtensionArtinian Λ k).obj M` for a
finite-dimensional `M` — the hypotheses `hP` and `hQ` of
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`. At
`Deformation.Examples.firstOrderPushforward` that equation is unavailable: the base there is
`(Deformation.dualNumbersUnder).right`, the dual numbers read as an algebra *under* the base
object of the point, whose `Λ`-algebra structure is the composite one that
`Deformation.algebrasUnder` installs, and the square-zero extension of `𝒞_Λ` carries the direct
one. The two objects of `ArtinianLocalAlgCat Λ k` share a carrier and differ in the `algebra`
instance field, so they are *isomorphic* and not equal, and a theorem carrying `hP` at that
pushforward would assert nothing.

What this file supplies is the missing input: the self-map presentation of the `Inf` term at the
chosen pushforward to the **re-based** dual numbers `Deformation.squareZeroCrossUnder`, whose
`right` is `(Deformation.squareZeroExtensionArtinian Λ k).obj M` on the nose
(`Deformation.squareZeroCrossUnder_right`). At that pushforward `hP` and `hQ` are not hypotheses
at all but the second components of the chosen pushforwards
(`Deformation.Examples.firstOrderPushforwardCross_base`), and
`Deformation.Examples.exact_schemeMorphismSixTerm_interior` can be instantiated.

## Main definitions

* `Deformation.ChosenPushforwardsAt.transportAutMulEquiv`: transport of automorphisms along an
  isomorphism of coordinate objects is an isomorphism of groups, the two directions being
  mutually inverse.
* `Deformation.Examples.firstOrderPushforwardCross`: the chosen pushforward of a point of the
  deformation category of a scheme to the **re-based** dual numbers. Its base object is the
  square-zero extension of `𝒞_Λ` by the rank-one module, on the nose.
* `Deformation.Examples.localizedTangentEquivAutDualNumbers`: the `Inf` term as the full
  automorphism group of the chosen dual-number pushforward in its own fibre over
  `Deformation.dualNumbersUnder`, before any re-indexing.
* `Deformation.Examples.localizedTangentEquivSelfMapsCross`: **the missing input.** The `Inf` term
  is the set of invertible self-maps of the total space of the chosen pushforward to the re-based
  dual numbers, over the base and fixing the special-fibre immersion.
* `Deformation.Examples.localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross`: the bridge at
  the re-based pushforwards.
* `Deformation.Examples.globalLiftsOverBaseConjDerivationLocalizedTangentCross`: **the arrow `b`**,
  read out of the source's second term, at the re-based pushforwards.

## Main results

* `Deformation.Examples.firstOrderPushforwardCross_base`: the base of the re-based pushforward is
  `(Deformation.squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k (ULift k))`. This is the
  `hP` of `Deformation.Examples.exact_schemeMorphismSixTerm_interior`, discharged.
* `Deformation.Examples.exact_schemeMorphismSixTerm_thirdFourthSpot_localizedTangent`: **Tag 0E3V,
  exactness at the third and fourth spots with the second term the source's
  `Inf(Def_X × Def_Y)`.**

## Implementation notes

**Why the dual numbers under the base are a square-zero extension on the nose.**
`Deformation.dualNumbersUnder` is `Deformation.algebrasUnder` applied to
`Deformation.artinianDualNumbers`, which is `Deformation.squareZeroExtensionArtinian` of the base
algebra at the rank-one module; and `Deformation.squareZeroAlgFunctor` is
`Deformation.squareZeroExtensionArtinian` followed by `Deformation.algebrasUnder`. So
`Deformation.dualNumbersUnder` *is* the value of `Deformation.squareZeroAlgFunctor` at
`FGModuleCat.of k (ULift k)`, definitionally, and
`Deformation.squareZeroCrossUnderIso` — the comparison that is the identity on carriers — is
already an isomorphism out of it. That is the whole of
`Deformation.Examples.dualNumbersUnderIsoCross`: no new comparison of algebras is built here.

**Which module `M` the two spots are stated at.** `M` is forced to be
`FGModuleCat.of k (ULift k)`, the rank-one module: the `Inf` term of the source's sequence is a
tangent space of an automorphism functor, hence read on the dual numbers, and the re-based dual
numbers are the square-zero extension at exactly that module. This is the source's own case —
the sequence of [Stacks Project, Tag 0E3V] is a sequence of first-order data.

**What the restatement moves and what it does not.** The fourth spot of
`Deformation.Examples.exact_schemeMorphismSixTerm_interior` is
`Function.Exact (schemeMorphismDerivationTangentMap …) (schemeMorphismTangentPair …)`, between the
third, fourth and fifth terms of the source's sequence; **no `Inf` term occurs in it**, and its
three terms are already the source's on the nose. So at the fourth spot there is nothing to
bridge, and what this file adds is that the spot becomes *available* at the two chosen
pushforwards — the deformations at which the source's `Inf` terms live — which it was not, `hP`
being unavailable there. The third spot does carry an `Inf` term, as the source of the arrow `b`,
and that source is replaced by the source's own
`Deformation.localizedAutomorphismFunctorTangent QX` ×
`Deformation.localizedAutomorphismFunctorTangent QY` along the bridge.

**The deformations are the re-based pushforwards, not
`Deformation.Examples.firstOrderPushforward`.** The two are the chosen pushforwards of the same
point along the two spellings of the same arrow out of its base, hence canonically isomorphic, and
`Deformation.ChosenPushforwardsAt.transportAutMulEquiv` along
`Deformation.Examples.dualNumbersUnderIsoCross` is that identification on automorphism groups. The
second-spot restatement is stated at `Deformation.Examples.firstOrderPushforward` and is *more*
general in that respect — it needs no square-zero coordinate at all — so it is not restated here.

**No `k`-linearity is asserted**, exactly as in
`Deformation.Examples.exact_schemeMorphismSixTerm_interior` and
`Deformation.Examples.exact_schemeMorphismSixTerm_secondSpot_localizedTangent`: exactness is
`Function.Exact`, a statement about bare functions, and
`Deformation.Examples.localizedTangentEquivSelfMapsCross` is a bijection of sets. The `PARTIAL`
Tag 0E3V marker of `Deformation.Examples.schemeMorphismDeformation_endpointArrows` stays where it
is.

## References

* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation

/-! ### Transport of automorphisms along an isomorphism of coordinate objects -/

namespace ChosenPushforwardsAt

variable {F : Type*} [Category F] {C : Type*} [Category C] {p : F ⥤ C} {x : F}

/-- **Transport of automorphisms along an isomorphism of coordinate objects is an isomorphism of
groups.** `Deformation.ChosenPushforwardsAt.transportAutHom` is a homomorphism for every arrow,
and `Deformation.ChosenPushforwardsAt.transportAut_inv_transportAut_hom` with its companion say
that the transports along the two directions of an isomorphism are mutually inverse. -/
def transportAutMulEquiv (P : ChosenPushforwardsAt p x) {A B : Under (p.obj x)} (e : A ≅ B) :
    Aut (P.obj A) ≃* Aut (P.obj B) where
  toFun := P.transportAut e.hom
  invFun := P.transportAut e.inv
  left_inv := P.transportAut_inv_transportAut_hom e
  right_inv := P.transportAut_hom_transportAut_inv e
  map_mul' := (P.transportAutHom e.hom).map_mul

end ChosenPushforwardsAt

namespace Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

/-! ### The `Inf` term at the chosen pushforward to the re-based dual numbers -/

section Cross

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {Z : Over (Spec (CommRingCat.of k))}

/-- The chosen pushforward of a point of the deformation category of `Z` to the **re-based** dual
numbers: the first-order deformation at which the `Inf` term of the sequence is read when the
square-zero coordinate of its base object has to be visible in `𝒞_Λ`.

It differs from `Deformation.Examples.firstOrderPushforward` only in the spelling of the arrow
out of the base object along which the point is pushed forward:
`Deformation.squareZeroCrossUnder` where that one has `Deformation.dualNumbersUnder`. -/
abbrev firstOrderPushforwardCross
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    SchemeDeformationCategory (Λ := Λ) (k := k) Z :=
  (P.obj (squareZeroCrossUnder.{u, u, u}
    ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
    (FGModuleCat.of k (ULift.{u} k)))).1

/-- **The base object of the re-based pushforward is the square-zero extension of `𝒞_Λ` by the
rank-one module, on the nose.** This is the hypothesis `hP` of
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`: it is the second component of the
chosen pushforward, read through `Deformation.squareZeroCrossUnder_right`, which is `rfl`.

At `Deformation.Examples.firstOrderPushforward` the corresponding equation is *false* — the base
there is the dual numbers carrying the `Λ`-algebra structure composed through the base object of
the point — which is why the third and fourth spots are restated at this pushforward. -/
theorem firstOrderPushforwardCross_base
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    (firstOrderPushforwardCross P).base =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k)) :=
  (P.obj (squareZeroCrossUnder.{u, u, u}
    ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
    (FGModuleCat.of k (ULift.{u} k)))).2

/-- **The base object of the re-based pushforward carries a dual-number coordinate.**
`Deformation.Examples.artinianDualNumbersCoordinate` read through
`Deformation.Examples.firstOrderPushforwardCross_base`: the square-zero extension of `𝒞_Λ` by the
rank-one module is `k[ε]` with the `ε`-line lifted. -/
def firstOrderPushforwardCrossCoordinate
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    (firstOrderPushforwardCross P).base ≃ₐ[Λ] DualNumber k := by
  rw [firstOrderPushforwardCross_base P]
  exact artinianDualNumbersCoordinate

/-- **The maximal ideal of the base object of the re-based pushforward has square zero.** This is
the hypothesis `hm` of `Deformation.Examples.exact_schemeMorphismSixTerm_interior`, discharged at
this pushforward: the base carries a dual-number coordinate
(`Deformation.Examples.firstOrderPushforwardCrossCoordinate`), and
`Deformation.Examples.maximalIdeal_pow_two_eq_bot_of_coordinate` concludes.

It is recorded because `hm` is carried as a parameter below, as in
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`: this is what says the parameter can
be supplied, so the restatement is not a statement about an empty hypothesis. -/
theorem firstOrderPushforwardCross_maximalIdeal_pow_two
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    IsLocalRing.maximalIdeal (firstOrderPushforwardCross P).base ^ 2 = ⊥ :=
  maximalIdeal_pow_two_eq_bot_of_coordinate _ (firstOrderPushforwardCrossCoordinate P)

/-- **The conormal sheaf of the special fibre of the re-based pushforward is the structure sheaf
of the scheme being deformed.** This is the hypothesis `eC` of
`Deformation.Examples.exact_schemeMorphismSixTerm_interior`, discharged at this pushforward by
`Deformation.Examples.deformationConormalIsoUnit` with the dual-number coordinate
`Deformation.Examples.firstOrderPushforwardCrossCoordinate`.

As with `Deformation.Examples.firstOrderPushforwardCross_maximalIdeal_pow_two`, `eC` stays a
parameter below — the statement depends on the choice of trivialisation — and this says the
parameter can be supplied. -/
def firstOrderPushforwardCrossConormalIsoUnit
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    Stacks.Thickenings.conormalModules (firstOrderPushforwardCross P).specialMap ≅
      SheafOfModules.unit (structureSheafRing Z.left.toRingedSpace) :=
  deformationConormalIsoUnit (firstOrderPushforwardCross P)
    (firstOrderPushforwardCrossCoordinate P)

/-- **The dual numbers under the base object are isomorphic to the re-based dual numbers.**
`Deformation.dualNumbersUnder` is the value of `Deformation.squareZeroAlgFunctor` at the rank-one
module definitionally — both are `Deformation.squareZeroExtensionArtinian` of the base algebra
followed by `Deformation.algebrasUnder` — so this *is*
`Deformation.squareZeroCrossUnderIso`, the comparison that is the identity on carriers. -/
def dualNumbersUnderIsoCross
    (x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z) :
    dualNumbersUnder (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) (x := x₀) ≅
      squareZeroCrossUnder.{u, u, u}
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
        (FGModuleCat.of k (ULift.{u} k)) :=
  squareZeroCrossUnderIso.{u, u, u}
    ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
    (FGModuleCat.of k (ULift.{u} k))

/-- **The `Inf` term of the deformation sequence of a scheme is the automorphism group of the
chosen dual-number pushforward, read in the fibre over `Deformation.dualNumbersUnder`.** This is
`Deformation.Examples.localizedTangentEquivFiberAut` stopped one step earlier, before the
re-indexing of the fibre by `Deformation.Examples.autFiberBaseMulEquiv`: that composite is this
bijection followed by that re-indexing, definitionally. Stopping here is what lets the coordinate
object be moved first, which is what `Deformation.Examples.localizedTangentEquivSelfMapsCross`
does.

A bijection of sets, for the reasons recorded in
`StacksFrontier/Deformation/Examples/Geometric/SchemeDeformationTangentFiberAut.lean`: the group law
of the `Inf` term is the addition of the tangent space. -/
def localizedTangentEquivAutDualNumbers
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    localizedAutomorphismFunctorTangent P ≃
      Aut (P.obj (dualNumbersUnder
        (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) (x := x₀))) :=
  (localizedTangentEquivKernel P).trans
    ((MulEquiv.subgroupCongr
      (ker_transportAutHom_tangentReduction_eq_top hp P)).trans Subgroup.topEquiv).toEquiv

/-- `Deformation.Examples.localizedTangentEquivFiberAut` factors through
`Deformation.Examples.localizedTangentEquivAutDualNumbers`. -/
theorem localizedTangentEquivFiberAut_eq
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    localizedTangentEquivFiberAut hp P =
      (localizedTangentEquivAutDualNumbers hp P).trans
        (autFiberBaseMulEquiv (P.obj (dualNumbersUnder
          (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z)
          (x := x₀)))).toEquiv := rfl

/-- **The `Inf` term of the deformation sequence of a scheme is a set of self-maps of the
*re-based* first-order pushforward.** The analogue of
`Deformation.Examples.localizedTangentEquivSelfMaps` at
`Deformation.Examples.firstOrderPushforwardCross`: the term is the invertible self-maps of the
total space of the chosen pushforward to the re-based dual numbers, over the base and fixing the
special-fibre immersion.

The route is `Deformation.Examples.localizedTangentEquivAutDualNumbers`, then transport of
automorphisms along `Deformation.Examples.dualNumbersUnderIsoCross`
(`Deformation.ChosenPushforwardsAt.transportAutMulEquiv`), then the re-indexing of the fibre
(`Deformation.Examples.autFiberBaseMulEquiv`) and the reading of a fibre automorphism as a
self-map (`Deformation.Examples.fiberAutEquivSelfMaps`), exactly as in
`Deformation.Examples.localizedTangentEquivSelfMaps` with the transport inserted.

**This is what the third and fourth spots of [Stacks Project, Tag 0E3V] were missing**: the base
object of `Deformation.Examples.firstOrderPushforwardCross` is the square-zero extension of
`𝒞_Λ` on the nose (`Deformation.Examples.firstOrderPushforwardCross_base`), so the square-zero
hypotheses of `Deformation.Examples.exact_schemeMorphismSixTerm_interior` hold there.

A bijection of sets only: no `k`-vector space structure is transported. -/
def localizedTangentEquivSelfMapsCross
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    localizedAutomorphismFunctorTangent P ≃
      { e : (firstOrderPushforwardCross P).scheme ⟶ (firstOrderPushforwardCross P).scheme //
        e ≫ (firstOrderPushforwardCross P).toBase = (firstOrderPushforwardCross P).toBase ∧
          (firstOrderPushforwardCross P).specialMap ≫ e =
            (firstOrderPushforwardCross P).specialMap ∧ IsIso e } :=
  (localizedTangentEquivAutDualNumbers hp P).trans
    ((P.transportAutMulEquiv (dualNumbersUnderIsoCross x₀)).toEquiv.trans
      ((autFiberBaseMulEquiv (P.obj (squareZeroCrossUnder.{u, u, u}
          ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).obj x₀)
          (FGModuleCat.of k (ULift.{u} k))))).toEquiv.trans
        (fiberAutEquivSelfMaps (firstOrderPushforwardCross P))))

end Cross

/-! ### The bridge and the arrow `b` at the re-based pushforwards -/

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

section Bridge

variable
  (hpX : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  (hpY : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
  {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  (QX : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) x₀)
  {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  (QY : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)) y₀)

/-- **Stacks 0E3V: the second term of the source's sequence is the acting group of its proof, at
the re-based pushforwards.** The bridge
`Deformation.Examples.localizedTangentPairEquivGlobalLiftsOverBaseAutPair`
with `Deformation.Examples.localizedTangentEquivSelfMapsCross` in place of
`Deformation.Examples.localizedTangentEquivSelfMaps`, so that the two deformations are the chosen
pushforwards to the re-based dual numbers and their common base object is the square-zero
extension of `𝒞_Λ` on the nose.

As a bijection of sets only: each factor of the left-hand side is a `k`-vector space and nothing
here transports that structure. -/
def localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross
    (e : (firstOrderPushforwardCross QY).base ⟶ (firstOrderPushforwardCross QX).base) [IsIso e] :
    localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY ≃
      globalLiftsOverBaseAutPair pX pY (firstOrderPushforwardCross QX)
        (firstOrderPushforwardCross QY) e :=
  ((localizedTangentEquivSelfMapsCross hpX QX).prodCongr
      (localizedTangentEquivSelfMapsCross hpY QY)).trans
    (globalLiftsOverBaseAutPairEquivSelfMapsProd pX pY (e := e)).symm

/-- The source component of the bridge is the self-map of the first tangent vector. -/
@[simp]
theorem localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross_fst_val
    (e : (firstOrderPushforwardCross QY).base ⟶ (firstOrderPushforwardCross QX).base) [IsIso e]
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    (localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY e t).1.1 =
      (localizedTangentEquivSelfMapsCross hpX QX t.1).1 := rfl

/-- The target component of the bridge is the self-map of the second tangent vector. -/
@[simp]
theorem localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross_snd_val
    (e : (firstOrderPushforwardCross QY).base ⟶ (firstOrderPushforwardCross QX).base) [IsIso e]
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    (localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY e t).1.2 =
      (localizedTangentEquivSelfMapsCross hpY QY t.2).1 := rfl

end Bridge

section Arrows

variable (hf : f ≫ pY = pX)
  (hpX : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
  (hpY : IsPredeformationCategory.{u, u, u}
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
  {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
  (QX : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) x₀)
  {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
  (QY : ChosenPushforwardsAt
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)) y₀)
  {e : (firstOrderPushforwardCross QY).base ⟶ (firstOrderPushforwardCross QX).base} [IsIso e]
  (eC : Stacks.Thickenings.conormalModules (firstOrderPushforwardCross QX).specialMap ≅
    SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  (hm : IsLocalRing.maximalIdeal (firstOrderPushforwardCross QX).base ^ 2 = ⊥)

/-- **The arrow `b` of [Stacks Project, Tag 0E3V] at the re-based pushforwards, starting from the
source's second term.** `Deformation.Examples.globalLiftsOverBaseConjDerivation` — the unique
derivation carrying `ℓ₀` where a pair of infinitesimal automorphisms of the endpoints carries it
— precomposed with `Deformation.Examples.localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross`,
so that its source is `Inf(Def_X × Def_Y)` and its target the source's third term
`Der_k(𝒪_Y, f_*𝒪_X)`. -/
def globalLiftsOverBaseConjDerivationLocalizedTangentCross
    (ℓ₀ : globalLiftsOverBase f (firstOrderPushforwardCross QX)
      (firstOrderPushforwardCross QY) e)
    (t : localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY) :
    schemeMorphismDerivations f pY :=
  globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀
    (localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY e t)

/-- **Stacks 0E3V, exactness at the third and fourth spots of the source's sequence, with the
second term the source's `Inf(Def_X × Def_Y)`.**

Let `QX` and `QY` be choices of pushforward for a point of each endpoint deformation category,
let the two chosen pushforwards to the re-based dual numbers be *trivial* first-order
deformations, let the maximal ideal of their common base have square zero, let `eC` trivialise the
conormal sheaf of the special fibre of the first, and let `ℓ₀` be a lift of `f` to that pair whose
class in `T Def_{X ⟶ Y}` vanishes. Then

* the image of the arrow `b` out of `Inf(Def_X × Def_Y)` is the kernel of the arrow
  `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X ⟶ Y}` — exactness at the **third** spot; and
* the image of that arrow is the kernel of `T Def_{X ⟶ Y} → T(Def_X × Def_Y)` — exactness at the
  **fourth** spot.

The second term is the source's: the product `Deformation.localizedAutomorphismFunctorTangent QX` ×
`Deformation.localizedAutomorphismFunctorTangent QY`
of the tangent spaces at the identity of the two endpoint automorphism functors, the term
`Deformation.Examples.schemeMorphismInfinitesimalPair` maps into. The third, fourth and
fifth terms are the source's on the nose, with the arrows
`Deformation.Examples.schemeMorphismDerivationTangentMap` and
`Deformation.Examples.schemeMorphismTangentPair` between them.

This is `Deformation.Examples.exact_schemeMorphismSixTerm_interior` instantiated at the two
re-based pushforwards — where its square-zero hypotheses `hP` and `hQ` are
`Deformation.Examples.firstOrderPushforwardCross_base`, not assumptions — with the source of the
arrow `b` carried onto the source's second term along
`Deformation.Examples.localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross`, which being a
bijection does not change the image of `b`. No `Inf` term occurs at the fourth spot at all; there
the content is that the spot is available at these deformations.

Exactness is `Function.Exact`, about bare functions, so no `k`-linearity of any arrow is
asserted. -/
theorem exact_schemeMorphismSixTerm_thirdFourthSpot_localizedTangent
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (hP0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX
        (FGModuleCat.of k (ULift.{u} k))
        ⟨firstOrderPushforwardCross QX, firstOrderPushforwardCross_base QX⟩ = 0)
    (hQ0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY
        (FGModuleCat.of k (ULift.{u} k))
        ⟨firstOrderPushforwardCross QY, firstOrderPushforwardCross_base QY⟩ = 0)
    (ℓ₀ : globalLiftsOverBase f (firstOrderPushforwardCross QX)
      (firstOrderPushforwardCross QY)
      (eqToHom ((firstOrderPushforwardCross_base QY).trans
        (firstOrderPushforwardCross_base QX).symm)))
    (h0 : liftClass f pX pY hf hM (FGModuleCat.of k (ULift.{u} k))
      (firstOrderPushforwardCross_base QY) ℓ₀ = 0) :
    Function.Exact
        (globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf hpX hpY QX QY eC hm ℓ₀)
        (schemeMorphismDerivationTangentMap f pX pY hf hM (FGModuleCat.of k (ULift.{u} k))
          (firstOrderPushforwardCross_base QY)
          (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀) ℓ₀) ∧
      Function.Exact
        (schemeMorphismDerivationTangentMap f pX pY hf hM (FGModuleCat.of k (ULift.{u} k))
          (firstOrderPushforwardCross_base QY)
          (globalLiftsOverBaseDerivationVAdd f pX pY hf eC hm ℓ₀) ℓ₀)
        (schemeMorphismTangentPair f pX pY hf hM hX hY (FGModuleCat.of k (ULift.{u} k))) := by
  obtain ⟨-, h3, h4⟩ := exact_schemeMorphismSixTerm_interior f pX pY hf hM hX hY
    (FGModuleCat.of k (ULift.{u} k))
    (firstOrderPushforwardCross_base QX) (firstOrderPushforwardCross_base QY) hP0 hQ0 eC hm ℓ₀ h0
  refine ⟨fun D => (h3 D).trans ⟨?_, ?_⟩, h4⟩
  · rintro ⟨g, hg⟩
    refine ⟨(localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY hpX hpY QX QY
      (eqToHom ((firstOrderPushforwardCross_base QY).trans
        (firstOrderPushforwardCross_base QX).symm))).symm g, ?_⟩
    show globalLiftsOverBaseConjDerivation f pX pY hf eC hm ℓ₀ _ = D
    rw [Equiv.apply_symm_apply]
    exact hg
  · rintro ⟨t, ht⟩
    exact ⟨_, ht⟩

end Arrows

end Examples

end Deformation

end
