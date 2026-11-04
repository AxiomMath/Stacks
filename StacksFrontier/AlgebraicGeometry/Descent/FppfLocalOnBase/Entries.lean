module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.Affine
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.Finiteness
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.Immersions
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.Smoothness
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.Topological
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.FpqcLocal

/-!
# The entries of the list of Tag 02WH, one statement each

Tag 02WH selects, from the properties of morphisms of schemes which are stable under base
change, those which are moreover *fpqc local on the base*, and asserts that such a property is
a fortiori fppf local on the base. The content of the remark at one entry of its list is
therefore a three-fold conjunction: the property that entry names is stable under arbitrary base
change, it is local on the base for the fpqc precoverage, and it is local on the base for the
fppf precoverage.

This file states that conjunction once for every reading of every entry, so that each entry of
the remark is asserted in full by a single declaration naming its own property. Twenty-four
entries are listed. The entry about immersions splits into three cases; seven further entries
have two readings each, because the source states them with a parenthesis or a disjunction
(`(quasi-)separated`, `(locally) of finite type`, `(locally) quasi-finite`, `(locally) of finite
presentation`, `unramified (resp. G-unramified)`, `finite or integral`, and finite locally free
with the rank unconstrained or fixed). So there are thirty-three declarations in all, plus one
for the caveat of the last sentence.

Each declaration's Stacks-tag note begins with the index of the entry it states,
written as the source writes it: `entry (1)(a)`, ..., `entry (24)`, and
`last sentence (02YM)` for the closing caveat. So the notes on the tag enumerate the remark's
own list, and which entries are covered can be read off the notes alone, without matching
properties to types. Each reading is carried by exactly one of these conjunctions, and the
sibling modules of this one do not attach the tag again to the three halves a conjunction is
built from: a fragment of an entry registered beside the entry itself lengthens the tag's record
without saying anything the entry does not already say. Some halves proved in modules older than
this file do carry the tag where they are proved, and keep it; a tag on more than one
declaration is not a defect.

## Main results

* `Stacks.Descent.universallyClosed_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf`,
  and the thirty-two declarations of the same shape beside it: entry by entry, the property named
  is stable under base change, fpqc local on the base, and fppf local on the base.
* `Stacks.Descent.isImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fppf`: the caveat of
  the last sentence of the remark. Being an immersion is stable under base change and fppf local
  on the base; no fpqc conjunct is asserted.

## Implementation notes

Every declaration here is a conjunction of three facts already available, and its proof names
all three: nothing new is proved. The declarations exist so that each reading of each entry of
the list is stated in full by one declaration carrying the tag, rather than by three facts about
the same property recorded in three different files. The fpqc halves are the descent lemmas the
source cites; the "a fortiori" fppf halves are the instances recorded in the sibling modules of
`StacksFrontier/AlgebraicGeometry/Descent/FppfLocalOnBase/`, each of them one application of
`Stacks.Descent.isLocalAtTarget_fppfPrecoverage` to the fpqc half beside it.

The exception is the last sentence of the remark, which is a warning rather than an entry: the
property of being an immersion is *not* claimed to be fpqc local on the base, only fppf local on
the base, by Descent, Lemma 02YM. Its declaration accordingly conjoins stability under base
change with fppf locality, and has no fpqc conjunct.

Being a universal homeomorphism is the only entry whose stability under arbitrary base change is
not available as a named declaration; it is obtained here from
`AlgebraicGeometry.universalHomeomorphism_eq_inf`, which identifies the property with the
infimum of surjectivity, universal injectivity and universal openness.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-! ### Entry (1): immersions -/

/-- **Stacks 02WH**, entry (1)(a): being a closed immersion is stable under base change, fpqc
local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (1)(a): closed immersions",
  sga "1 VIII 5.5" "more general",
  sga "3 VIB 12.1" "more general",
  sga "4 IV 8.5.5"]
public theorem isClosedImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsClosedImmersion : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsClosedImmersion : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange,
    Stacks.Descent.isClosedImmersion_isLocalAtTarget_fpqc,
    Stacks.Descent.isClosedImmersion_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (1)(b): being an open immersion is stable under base change, fpqc
local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (1)(b): open immersions",
  ega "IV 2.7.1" "more general",
  sga "1 VIII 5.5" "more general",
  sga "4 IV 8.5.5"]
public theorem isOpenImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsOpenImmersion : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsOpenImmersion : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsOpenImmersion : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange,
    Stacks.Descent.isOpenImmersion_isLocalAtTarget_fpqc,
    Stacks.Descent.isOpenImmersion_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (1)(c): being a quasi-compact immersion is stable under base change,
fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (1)(c): quasi-compact immersions",
  ega "IV 2.7.1" "more general",
  sga "4 IV 8.5.5"]
public theorem
    isImmersion_inf_quasiCompact_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨Stacks.Descent.isImmersion_inf_quasiCompact_isStableUnderBaseChange,
    AlgebraicGeometry.isLocalAtTarget_isImmersion_inf_quasiCompact_fpqc,
    Stacks.Descent.isImmersion_inf_quasiCompact_isLocalAtTarget_fppf⟩

/-! ### Entry (2): quasi-compact morphisms -/

/-- **Stacks 02WH**, entry (2): being quasi-compact is stable under base change, fpqc local on
the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (2): quasi-compact"]
public theorem quasiCompact_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@QuasiCompact : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.quasiCompact_isStableUnderBaseChange,
    Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc,
    Stacks.Descent.quasiCompact_isLocalAtTarget_fppf⟩

/-! ### Entry (3): universally closed morphisms -/

/-- **Stacks 02WH**, entry (3): being universally closed is stable under base change, fpqc local
on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (3): universally closed", ega "IV 2.6.4" "more general"]
public theorem universallyClosed_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@UniversallyClosed : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversallyClosed : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversallyClosed : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.universallyClosed_isStableUnderBaseChange,
    AlgebraicGeometry.universallyClosed_isLocalAtTarget_fpqc,
    Stacks.Descent.universallyClosed_isLocalAtTarget_fppf⟩

/-! ### Entry (4): separated and quasi-separated morphisms -/

/-- **Stacks 02WH**, entry (4), separated case: being separated is stable under base change, fpqc
local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (4): separated"]
public theorem isSeparated_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsSeparated : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsSeparated : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsSeparated : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.IsSeparated.isStableUnderBaseChange,
    AlgebraicGeometry.isSeparated_isLocalAtTarget_fpqc,
    Stacks.Descent.isSeparated_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (4), quasi-separated case: being quasi-separated is stable under base
change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (4): quasi-separated"]
public theorem quasiSeparated_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@QuasiSeparated : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@QuasiSeparated : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@QuasiSeparated : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange,
    AlgebraicGeometry.quasiSeparated_isLocalAtTarget_fpqc,
    Stacks.Descent.quasiSeparated_isLocalAtTarget_fppf⟩

/-! ### Entry (5): monomorphisms -/

/-- **Stacks 02WH**, entry (5): being a monomorphism is stable under base change, fpqc local on
the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (5): monomorphism", sga "4 IV 8.5.5"]
public theorem monomorphisms_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (MorphismProperty.monomorphisms Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (MorphismProperty.monomorphisms Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (MorphismProperty.monomorphisms Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨MorphismProperty.IsStableUnderBaseChange.monomorphisms Scheme.{u},
    AlgebraicGeometry.isLocalAtTarget_monomorphisms_fpqc,
    AlgebraicGeometry.instIsLocalAtTargetFppfMonomorphisms⟩

/-! ### Entry (6): surjective morphisms -/

/-- **Stacks 02WH**, entry (6): being surjective is stable under base change, fpqc local on the
base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (6): surjective", sga "4 IV 8.5.5"]
public theorem surjective_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@Surjective : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@Surjective : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@Surjective : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme,
    AlgebraicGeometry.surjective_isLocalAtTarget_fpqc,
    AlgebraicGeometry.surjective_isLocalAtTarget_fppf⟩

/-! ### Entry (7): universally injective morphisms -/

/-- **Stacks 02WH**, entry (7): being universally injective is stable under base change, fpqc
local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (7): universally injective"]
public theorem universallyInjective_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@UniversallyInjective : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversallyInjective : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversallyInjective : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange,
    AlgebraicGeometry.universallyInjective_isLocalAtTarget_fpqc,
    AlgebraicGeometry.universallyInjective_isLocalAtTarget_fppf⟩

/-! ### Entry (8): affine morphisms -/

/-- **Stacks 02WH**, entry (8): being affine is stable under base change, fpqc local on the base,
and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (8): affine"]
public theorem isAffineHom_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsAffineHom : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsAffineHom : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.isAffineHom_isStableUnderBaseChange,
    Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc,
    Stacks.Descent.isAffineHom_isLocalAtTarget_fppf⟩

/-! ### Entry (9): quasi-affine morphisms -/

/-- **Stacks 02WH**, entry (9): being quasi-affine is stable under base change, fpqc local on the
base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (9): quasi-affine"]
public theorem isQuasiAffineHom_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange,
    Stacks.Descent.isQuasiAffineHom_isLocalAtTarget_fpqc,
    Stacks.Descent.isQuasiAffineHom_isLocalAtTarget_fppf⟩

/-! ### Entry (10): morphisms (locally) of finite type -/

/-- **Stacks 02WH**, entry (10), locally of finite type case: being locally of finite type is
stable under base change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (10): locally of finite type"]
public theorem locallyOfFiniteType_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange,
    Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fpqc,
    Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (10), finite type case: being of finite type is stable under base
change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (10): of finite type"]
public theorem finiteType_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
          Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
          Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.Space.finiteType_isStableUnderBaseChange,
    Stacks.Descent.finiteType_isLocalAtTarget_fpqc,
    Stacks.Descent.finiteType_isLocalAtTarget_fppf⟩

/-! ### Entry (11): (locally) quasi-finite morphisms -/

/-- **Stacks 02WH**, entry (11), locally quasi-finite case: being locally quasi-finite is stable
under base change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (11): locally quasi-finite"]
public theorem
  locallyOfFiniteType_inf_locallyQuasiFinite_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u})
          Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u})
          Scheme.fppfPrecoverage :=
  ⟨Stacks.Descent.locallyOfFiniteType_inf_locallyQuasiFinite_isStableUnderBaseChange,
    Stacks.Descent.locallyOfFiniteType_inf_locallyQuasiFinite_isLocalAtTarget_fpqc,
    Stacks.Descent.locallyOfFiniteType_inf_locallyQuasiFinite_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (11), quasi-finite case: being quasi-finite is stable under base
change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (11): quasi-finite"]
public theorem
    finiteType_inf_locallyQuasiFinite_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        ((@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ⊓
          @LocallyQuasiFinite) ∧
      MorphismProperty.IsLocalAtTarget
          ((@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ⊓
            @LocallyQuasiFinite) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          ((@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ⊓
            @LocallyQuasiFinite) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.Space.quasiFinite_isStableUnderBaseChange,
    Stacks.Descent.finiteType_inf_locallyQuasiFinite_isLocalAtTarget_fpqc,
    Stacks.Descent.finiteType_inf_locallyQuasiFinite_isLocalAtTarget_fppf⟩

/-! ### Entry (12): morphisms (locally) of finite presentation -/

/-- **Stacks 02WH**, entry (12), locally of finite presentation case: being locally of finite
presentation is stable under base change, fpqc local on the base, and a fortiori fppf local on
the base. -/
@[stacks 02WH "entry (12): locally of finite presentation", sga "4 IV 8.5.5" "partial"]
public theorem locallyOfFinitePresentation_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange,
    Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fpqc,
    Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (12), finite presentation case: being of finite presentation is stable
under base change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (12): of finite presentation", sga "4 IV 8.5.5"]
public theorem finitePresentation_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@FinitePresentation : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@FinitePresentation : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@FinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.Space.finitePresentation_isStableUnderBaseChange,
    AlgebraicGeometry.finitePresentation_isLocalAtTarget,
    Stacks.Descent.finitePresentation_isLocalAtTarget_fppf⟩

/-! ### Entry (13): morphisms locally of finite type of relative dimension `d` -/

/-- **Stacks 02WH**, entry (13): being locally of finite type of relative dimension `d` is stable
under base change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (13): locally of finite type of relative dimension d"]
public theorem
    locallyOfFiniteTypeRelativeDimension_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf
    (d : ℕ) :
    MorphismProperty.IsStableUnderBaseChange (locallyOfFiniteTypeRelativeDimension.{u} d) ∧
      MorphismProperty.IsLocalAtTarget
          (locallyOfFiniteTypeRelativeDimension.{u} d) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (locallyOfFiniteTypeRelativeDimension.{u} d) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension_isStableUnderBaseChange d,
    AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension_isLocalAtTarget_fpqc d,
    Stacks.Descent.locallyOfFiniteTypeRelativeDimension_isLocalAtTarget_fppf d⟩

/-! ### Entry (14): universally open morphisms -/

/-- **Stacks 02WH**, entry (14): being universally open is stable under base change, fpqc local on
the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (14): universally open", ega "IV 2.6.4" "more general", sga "4 IV 8.5.5"]
public theorem universallyOpen_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@UniversallyOpen : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversallyOpen : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversallyOpen : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme,
    AlgebraicGeometry.universallyOpen_isLocalAtTarget_fpqc,
    Stacks.Descent.universallyOpen_isLocalAtTarget_fppf⟩

/-! ### Entry (15): flat morphisms -/

/-- **Stacks 02WH**, entry (15): being flat is stable under base change, fpqc local on the base,
and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (15): flat"]
public theorem flat_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@Flat : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@Flat : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@Flat : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.Flat.isStableUnderBaseChange,
    Stacks.Descent.flat_isLocalAtTarget_fpqc,
    Stacks.Descent.flat_isLocalAtTarget_fppf⟩

/-! ### Entry (16): syntomic morphisms -/

/-- **Stacks 02WH**, entry (16): being syntomic is stable under base change, fpqc local on the
base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (16): syntomic"]
public theorem syntomic_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@Syntomic : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@Syntomic : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@Syntomic : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.syntomic_isStableUnderBaseChange,
    AlgebraicGeometry.syntomic_isLocalAtTarget,
    Stacks.Descent.syntomic_isLocalAtTarget_fppf⟩

/-! ### Entry (17): smooth morphisms -/

/-- **Stacks 02WH**, entry (17): being smooth is stable under base change, fpqc local on the base,
and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (17): smooth", sga "3 VIB 2.1.2", sga "3 VIIA 8.3.1" "partial"]
public theorem smooth_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@Smooth : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@Smooth : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@Smooth : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.smooth_isStableUnderBaseChange,
    Stacks.Descent.smooth_isLocalAtTarget_fpqc,
    Stacks.Descent.smooth_isLocalAtTarget_fppf⟩

/-! ### Entry (18): unramified and G-unramified morphisms -/

/-- **Stacks 02WH**, entry (18), unramified case: being unramified is stable under base change,
fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (18): unramified"]
public theorem unramified_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@Unramified : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@Unramified : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@Unramified : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.unramified_isStableUnderBaseChange,
    AlgebraicGeometry.unramified_isLocalAtTarget_fpqc,
    Stacks.Descent.unramified_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (18), G-unramified case: being G-unramified is stable under base
change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (18): G-unramified"]
public theorem gUnramified_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@GUnramified : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@GUnramified : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@GUnramified : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.gUnramified_isStableUnderBaseChange,
    AlgebraicGeometry.gUnramified_isLocalAtTarget_fpqc,
    Stacks.Descent.gUnramified_isLocalAtTarget_fppf⟩

/-! ### Entry (19): étale morphisms -/

/-- **Stacks 02WH**, entry (19): being étale is stable under base change, fpqc local on the base,
and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (19): etale"]
public theorem etale_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@Etale : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@Etale : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@Etale : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.Etale.etale_isStableUnderBaseChange,
    AlgebraicGeometry.etale_isLocalAtTarget_fpqc,
    AlgebraicGeometry.etale_isLocalAtTarget_fppf⟩

/-! ### Entry (20): proper morphisms -/

/-- **Stacks 02WH**, entry (20) of the list: **proper**, Descent, Lemma 02L1. The source's
"proper" is `AlgebraicGeometry.IsProper` in Lean. Being proper is stable under arbitrary base
change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (20): proper", sga "4 IV 8.5.5"]
public theorem isProper_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsProper : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsProper : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsProper : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.IsProper.isStableUnderBaseChange,
    AlgebraicGeometry.isProper_isLocalAtTarget_fpqc,
    Stacks.Descent.isProper_isLocalAtTarget_fppf⟩

/-! ### Entry (21): finite and integral morphisms -/

/-- **Stacks 02WH**, entry (21), finite case: being finite is stable under base change, fpqc local
on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (21): finite"]
public theorem isFinite_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsFinite : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsFinite : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsFinite : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme,
    Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc,
    Stacks.Descent.isFinite_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (21), integral case: being integral is stable under base change, fpqc
local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (21): integral"]
public theorem isIntegralHom_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsIntegralHom : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@IsIntegralHom : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@IsIntegralHom : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme,
    AlgebraicGeometry.isIntegralHom_isLocalAtTarget_fpqc,
    Stacks.Descent.isIntegralHom_isLocalAtTarget_fppf⟩

/-! ### Entry (22): finite locally free morphisms -/

/-- **Stacks 02WH**, entry (22) of the list: **finite locally free**, Descent, Lemma 02VO, with
the rank left unconstrained. The source's "finite locally free" is
`Stacks.Morphisms.IsFiniteLocallyFree` in Lean. Being finite locally free is stable under
arbitrary base change, fpqc local on the base, and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (22): finite locally free", sga "1 VIII 5.7" "more general"]
public theorem isFiniteLocallyFree_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u})
          Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u})
          Scheme.fppfPrecoverage :=
  ⟨Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange,
    Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc,
    Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fppf⟩

/-- **Stacks 02WH**, entry (22) of the list: **finite locally free**, Descent, Lemma 02VO, for a
fixed rank `d`. The source's "finite locally free" of rank `d` is
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d` in Lean. Being finite locally free of
rank `d` is stable under arbitrary base change, fpqc local on the base, and a fortiori fppf
local on the base. -/
@[stacks 02WH "entry (22): finite locally free of rank d", sga "1 VIII 5.7" "special case"]
public theorem
    isFiniteLocallyFreeOfRank_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf
    (d : ℕ) :
    MorphismProperty.IsStableUnderBaseChange
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d) ∧
      MorphismProperty.IsLocalAtTarget
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d) Scheme.fppfPrecoverage :=
  ⟨Stacks.Morphisms.isFiniteLocallyFreeOfRank_isStableUnderBaseChange d,
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc d,
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fppf d⟩

/-! ### Entry (23): universally submersive morphisms -/

/-- **Stacks 02WH**, entry (23) of the list: **universally submersive**, Descent, Lemma 0CEW.
A submersive morphism is one whose underlying map of topological spaces is a quotient map, so the
source's "universally submersive" is in Lean `(topologically Topology.IsQuotientMap).universally`
— the Lean name `universallyQuotientMap` denotes exactly the source's "universally submersive".
That property is stable under arbitrary base change, fpqc local on the base, and a fortiori fppf
local on the base. -/
@[stacks 02WH "entry (23): universally submersive",
  ega "IV 15.7.11.1" "fpqc-locality conjunct",
  sga "1 IX 4.2" "partial"]
public theorem universallyQuotientMap_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally) ∧
      MorphismProperty.IsLocalAtTarget
          ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
          Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
          Scheme.fppfPrecoverage :=
  ⟨CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange _,
    AlgebraicGeometry.universallyQuotientMap_isLocalAtTarget_fpqc,
    Stacks.Descent.universallyQuotientMap_isLocalAtTarget_fppf⟩

/-! ### Entry (24): universal homeomorphisms -/

/-- **Stacks 02WH**, entry (24) of the list: **universal homeomorphism**, Descent, Lemma 0CEX.
The source's "universal homeomorphism" is `AlgebraicGeometry.UniversalHomeomorphism` in Lean.
Being a universal homeomorphism is stable under arbitrary base change, fpqc local on the base,
and a fortiori fppf local on the base. -/
@[stacks 02WH "entry (24): universal homeomorphism",
  ega "IV 2.6.2" "(iv), special case",
  ega "IV 2.6.4" "more general", sga "1 VIII 4.7" "more general", sga "4 IV 8.5.5"]
public theorem universalHomeomorphism_isStableUnderBaseChange_and_isLocalAtTarget_fpqc_fppf :
    MorphismProperty.IsStableUnderBaseChange
        (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage ∧
      MorphismProperty.IsLocalAtTarget
          (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  ⟨by
    have : MorphismProperty.IsStableUnderBaseChange
        (@Surjective ⊓ @UniversallyInjective : MorphismProperty Scheme.{u}) := .inf
    rw [AlgebraicGeometry.universalHomeomorphism_eq_inf]
    exact .inf,
   AlgebraicGeometry.universalHomeomorphism_isLocalAtTarget_fpqc,
   Stacks.Descent.universalHomeomorphism_isLocalAtTarget_fppf⟩

/-! ### The caveat of the last sentence: immersions in general -/

/-- **Stacks 02WH**, the closing sentence of the remark: **immersions are fppf local on the
base**, Descent, Lemma 02YM. Being an immersion is stable under base change, and it is fppf local
on the base — that fppf locality is exactly the content of 02YM, which the remark's last sentence
cites. The remark records explicitly that being an immersion *may not be* fpqc local on the base,
so no fpqc conjunct is asserted here; only the three cases of entry (1) — closed, open and
quasi-compact immersions — are claimed fpqc local. -/
@[stacks 02WH "last sentence (02YM): immersions are fppf local on the base",
  ega "II 3.8.1" "more general"]
public theorem isImmersion_isStableUnderBaseChange_and_isLocalAtTarget_fppf :
    MorphismProperty.IsStableUnderBaseChange (@IsImmersion : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsLocalAtTarget (@IsImmersion : MorphismProperty Scheme.{u})
        Scheme.fppfPrecoverage :=
  ⟨AlgebraicGeometry.IsImmersion.isStableUnderBaseChange,
    Stacks.Descent.isImmersion_isLocalAtTarget_fppf⟩

end Stacks.Descent

end
