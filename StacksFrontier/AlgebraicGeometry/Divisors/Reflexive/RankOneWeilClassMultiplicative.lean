module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneWeilClass
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections

/-!
# The Weil divisor class of a rank one coherent reflexive module is multiplicative

Let `X` be an integral locally Noetherian normal scheme.  The map
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass` of [Stacks, Tag 0EBM] sends the
isomorphism class of a rank one coherent reflexive `𝒪_X`-module to its class in `Cl(X)`.  This
file proves that it is a homomorphism from the commutative monoid law
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonCommMonoid` of [Stacks, Tag 0EBL],
`ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨`, to the addition of `Cl(X)`.

Both factors are invertible on a common open subscheme `U` whose complement has codimension at
least two.  There the reflexive hull does nothing — `ℱ ⊗_{𝒪_X} 𝒢` is already invertible, hence
reflexive, so the canonical map to its double dual restricts to an isomorphism — and the
restriction of a tensor product is the tensor product of the restrictions, so the class of
`(ℱ ⊗_{𝒪_X} 𝒢)^∨∨` on `U` is the class of `ℱ|_U ⊗_{𝒪_U} 𝒢|_U`, which is the sum of the two
classes by [Stacks, Tag 02SL].

## Main results

* `AlgebraicGeometry.weilClassOfCodimTwoInvertible_tensorObj` — the class in `Cl(X)` of an
  invertible module on an open subscheme whose complement has codimension at least two is
  additive in the tensor product.
* `AlgebraicGeometry.CoherentReflexive.rankOneWeilClass_rankOneTensorObj` — the Weil divisor
  class of the hull tensor product of two rank one coherent reflexive modules is the sum of
  their Weil divisor classes.
* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_mul` and
  `rankOneSkeletonToWeilClass_one` — **the multiplicativity clause of [Stacks, Tag 0EBM]**: the
  map of that tag is a homomorphism from the monoid law of Tag 0EBL to `Cl(X)`.

## Implementation notes

**What of Tag 0EBM is here and what is not.**  The tag asserts that the map is an isomorphism of
*groups*.  Injectivity is
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_injective`, and this file adds
multiplicativity.  Surjectivity is not in this file; it is reduced to a statement about `Cl(X)`
alone by `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_surjective_iff`, and
what that statement needs — the construction of `𝒪_X(D)` for an arbitrary Weil divisor on a
normal scheme — is
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/NormalWeilDivisorInvertible.lean`, from
which `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_surjective` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassSurjective.lean` follows.  The
isomorphism of the tag is
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonMulEquivWeilDivisorClass` of that file, which
is where the multiplicativity proved here is consumed; no declaration in this file carries
`@[stacks 0EBM]`.

The group law on the source — inverses for `rankOneSkeletonCommMonoid` — is a part of Tag 0EBL,
not of Tag 0EBM, and is `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonCommGroup` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassSurjective.lean`: the
isomorphism above exhibits the source as a group, because its target is one.  The
multiplicativity proved here is one of its three inputs, and it uses only the commutative monoid
law, never inverses, so nothing is circular.

**Where the two inputs come from.**  The restriction of the tensor product is
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso`, which is [Stacks, Tag 01CD] for
an open immersion read through Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`; its statement is written at the
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` spelling of the tensor product, which
is definitionally the `AlgebraicGeometry.Scheme.Modules.tensorObj` spelling used here, so it is
quoted with no bridge.  That restriction isomorphism was previously recorded in this project as
missing in the `AlgebraicGeometry.Scheme.Modules.restrict` spelling, available only on the slice
site as `Stacks.SheafOfModules.SliceRestriction.tensorSheafOver`; that note was wrong, and no new
comparison is introduced here.  The hull half is
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual`.

## References

* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
* [Stacks Project, Tag 0EBL](https://stacks.math.columbia.edu/tag/0EBL)
* [Stacks Project, Tag 02SL](https://stacks.math.columbia.edu/tag/02SL)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive toDoubleDual)

universe u

namespace AlgebraicGeometry

attribute [local instance] schemePicardGroupAddCommGroup

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **The class in `Cl(X)` of an invertible module on an open subscheme whose complement has
codimension at least two is additive in the tensor product.**  Restriction `Cl(X) ≅ Cl(U)` is an
isomorphism of groups, and the first Chern class on `U` is additive by [Stacks, Tag 02SL]. -/
theorem weilClassOfCodimTwoInvertible_tensorObj (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (L M : U.toScheme.Modules) (hL) (hM) (hLM) :
    weilClassOfCodimTwoInvertible U hU (Scheme.Modules.tensorObj L M) hLM =
      weilClassOfCodimTwoInvertible U hU L hL + weilClassOfCodimTwoInvertible U hU M hM := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have := hL
  have := hM
  have := hLM
  change (weilDivisorClassRestrictEquiv U hU).symm
      (weilDivisorClassOfInvertibleSheaf U.toScheme (Scheme.Modules.tensorObj L M)) =
    (weilDivisorClassRestrictEquiv U hU).symm
        (weilDivisorClassOfInvertibleSheaf U.toScheme L) +
      (weilDivisorClassRestrictEquiv U hU).symm (weilDivisorClassOfInvertibleSheaf U.toScheme M)
  rw [weilDivisorClassOfInvertibleSheaf_tensorObj, map_add]

end AlgebraicGeometry

namespace AlgebraicGeometry.CoherentReflexive

open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules)

attribute [local instance] schemePicardGroupAddCommGroup rankOneSkeletonCommMonoid

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The tensor product of the restrictions of two rank one coherent reflexive modules to an open
subscheme on which both are invertible is invertible. -/
theorem isInvertible_tensorObj_restrict (U : X.Opens) (F G : RankOneReflexiveModules X)
    (hFU : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (F.module.restrict U.ι))
    (hGU : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (G.module.restrict U.ι)) :
    SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (Scheme.Modules.tensorObj (F.module.restrict U.ι) (G.module.restrict U.ι)) := by
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hFU
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hGU
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _).toAlgebraicGeometry

/-- **On an open subscheme whose complement has codimension at least two and on which both
factors are invertible, the hull tensor product is the ordinary tensor product.**  The ordinary
tensor product restricts to the tensor product of the restrictions by [Stacks, Tag 01CD], which
is invertible, hence reflexive; so the canonical map to the double dual restricts to an
isomorphism on that open. -/
def rankOneTensorObjRestrictIso (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (F G : RankOneReflexiveModules X)
    (hFU : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (F.module.restrict U.ι))
    (hGU : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (G.module.restrict U.ι)) :
    (rankOneTensorObj F G).module.restrict U.ι ≅
      Scheme.Modules.tensorObj (F.module.restrict U.ι) (G.module.restrict U.ι) :=
  haveI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  haveI hT : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (Scheme.Modules.tensorObj (F.module.restrict U.ι) (G.module.restrict U.ι)) :=
    isInvertible_tensorObj_restrict U F G hFU hGU
  haveI hcoh : _root_.SheafOfModules.IsCoherent
      (Scheme.Modules.tensorObj F.module G.module) :=
    (ordinaryTensor F.obj G.obj).property
  haveI : (Scheme.Modules.tensorObj (F.module.restrict U.ι)
      (G.module.restrict U.ι)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible U.toScheme _
  haveI : ((Scheme.Modules.tensorObj F.module G.module).restrict U.ι).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isCoherent X U _ hcoh
  let e : (Scheme.Modules.tensorObj F.module G.module).restrict U.ι ≅
      Scheme.Modules.tensorObj (F.module.restrict U.ι) (G.module.restrict U.ι) :=
    Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso U.ι F.module G.module
  haveI : IsReflexive ((Scheme.Modules.tensorObj F.module G.module).restrict U.ι) :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_of_iso e.symm
      (isReflexive_of_isInvertible U.toScheme _)
  haveI := Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual U
    (Scheme.Modules.tensorObj F.module G.module) ‹_›
  (asIso ((Scheme.Modules.restrictFunctor U.ι).map
    (toDoubleDual (Scheme.Modules.tensorObj F.module G.module)))).symm ≪≫ e

variable [IsNormal X]

/-- **The Weil divisor class of the hull tensor product is the sum of the Weil divisor
classes.**  Both factors are invertible on a common open subscheme whose complement has
codimension at least two; there the hull tensor product is the ordinary tensor product of the
restrictions, whose class is the sum of their classes by [Stacks, Tag 02SL]. -/
theorem rankOneWeilClass_rankOneTensorObj (F G : RankOneReflexiveModules X) :
    rankOneWeilClass (rankOneTensorObj F G) = rankOneWeilClass F + rankOneWeilClass G := by
  obtain ⟨U, hU, hFU⟩ := exists_codimTwo_isInvertible_restrict F
  obtain ⟨V, hV, hGV⟩ := exists_codimTwo_isInvertible_restrict G
  have hW := two_le_codimension_compl_inf U V hU hV
  have hFW := isInvertible_restrict_of_le (inf_le_left : U ⊓ V ≤ U) F.module hFU
  have hGW := isInvertible_restrict_of_le (inf_le_right : U ⊓ V ≤ V) G.module hGV
  have hT := isInvertible_tensorObj_restrict (U ⊓ V) F G hFW hGW
  have e := rankOneTensorObjRestrictIso (U ⊓ V) hW F G hFW hGW
  rw [rankOneWeilClass_eq F (U ⊓ V) hW hFW, rankOneWeilClass_eq G (U ⊓ V) hW hGW,
    rankOneWeilClass_eq (rankOneTensorObj F G) (U ⊓ V) hW
      (Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hT),
    weilClassOfCodimTwoInvertible_congr (U ⊓ V) hW _ hT e,
    weilClassOfCodimTwoInvertible_tensorObj (U ⊓ V) hW _ _ hFW hGW hT]

/-- **The multiplicativity clause of [Stacks, Tag 0EBM].**  The map from isomorphism classes of
rank one coherent reflexive modules to `Cl(X)` carries the monoid law of [Stacks, Tag 0EBL],
`ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨`, to the addition of `Cl(X)`. -/
theorem rankOneSkeletonToWeilClass_mul (a b : Skeleton (RankOneReflexiveModules X)) :
    rankOneSkeletonToWeilClass (a * b) =
      rankOneSkeletonToWeilClass a + rankOneSkeletonToWeilClass b := by
  obtain ⟨F, rfl⟩ : ∃ F, toSkeleton F = a := ⟨_, toSkeleton_fromSkeleton_obj a⟩
  obtain ⟨G, rfl⟩ : ∃ G, toSkeleton G = b := ⟨_, toSkeleton_fromSkeleton_obj b⟩
  change rankOneSkeletonToWeilClass (rankOneSkeletonMul _ _) = _
  rw [rankOneSkeletonMul_toSkeleton, rankOneSkeletonToWeilClass_toSkeleton,
    rankOneSkeletonToWeilClass_toSkeleton, rankOneSkeletonToWeilClass_toSkeleton]
  exact rankOneWeilClass_rankOneTensorObj F G

/-- **The unit clause of [Stacks, Tag 0EBM].**  The class of the structure sheaf is the trivial
divisor class; this is forced by multiplicativity. -/
theorem rankOneSkeletonToWeilClass_one :
    rankOneSkeletonToWeilClass (1 : Skeleton (RankOneReflexiveModules X)) = 0 := by
  simpa using rankOneSkeletonToWeilClass_mul (1 : Skeleton (RankOneReflexiveModules X)) 1

end AlgebraicGeometry.CoherentReflexive

end
