module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# The Deligne–Mumford and quasi-Deligne–Mumford loci of an algebraic stack

**Stacks 0DSM.** Every algebraic stack `𝒳` carries open substacks `𝒳'' ⊆ 𝒳' ⊆ 𝒳` with `𝒳''`
Deligne–Mumford, `𝒳'` quasi-Deligne–Mumford, and each the largest open substack with its
property. This file constructs the two loci and proves everything about them that does not
depend on the structure theorems for DM and quasi-DM stacks.

The two loci are built the way **Stacks 0DSJ** builds the unramified and locally quasi-finite
base loci of a group algebraic space one level down
(`AlgebraicGeometry.Space.unramifiedBaseLocus`,
`AlgebraicGeometry.Space.locallyQuasiFiniteBaseLocus`): as the supremum, in the complete
lattice `CategoryTheory.ObjectProperty 𝒳.val.val.obj`, of the object properties of those open
substacks that have the property in question. The supremum is a *construction*, so the loci are
definitions with genuine bodies, and their maximality — which is the force of the word
*largest* in the source — is `le_iSup` and needs no input at all.

What the supremum does not give for free is that it is again an *open substack* and that the
open substack it cuts out again has the property. In the source both come from the structure
theorems **Stacks 06N3** (a DM algebraic stack admits a surjective étale morphism from a
scheme) and **Stacks 06MF** (its quasi-DM analogue), neither of which the library carries, via
the local-global step the source's proof isolates: a union of DM open substacks is DM, because
the disjoint union of étale charts for the pieces is an étale chart for the union. That step is
carried here as the explicit named hypothesis
`AlgebraicGeometry.Stack.IsAbsolutelyDMLocalOnOpenSubstacks` (and its quasi-DM twin), and the
realizability of the locus by an open substack as a second explicit hypothesis. The existence
statements of **Stacks 0DSM** are then theorems under exactly those hypotheses.

## Main definitions

* `AlgebraicGeometry.Stack.OpenSubstack.toAlgebraicStack`: an open substack read as an algebraic
  stack over the same base.
* `AlgebraicGeometry.Stack.dmLocus`: the Deligne–Mumford locus, **Stacks 0DSM**'s `𝒳''`.
* `AlgebraicGeometry.Stack.quasiDMLocus`: the quasi-Deligne–Mumford locus, **Stacks 0DSM**'s
  `𝒳'`.
* `AlgebraicGeometry.Stack.IsAbsolutelyDMLocalOnOpenSubstacks` and
  `AlgebraicGeometry.Stack.IsAbsolutelyQuasiDMLocalOnOpenSubstacks`: the local-global step of
  the source's proof, as a hypothesis.

## Main results

* `AlgebraicGeometry.Stack.le_dmLocus` and `AlgebraicGeometry.Stack.le_quasiDMLocus`:
  maximality of the two loci, unconditionally.
* `AlgebraicGeometry.Stack.dmLocus_le_quasiDMLocus`: the nesting `𝒳'' ⊆ 𝒳'`,
  unconditionally.
* `AlgebraicGeometry.Stack.exists_largest_isAbsolutelyDM_openSubstack`,
  `AlgebraicGeometry.Stack.exists_largest_isAbsolutelyQuasiDM_openSubstack` and
  `AlgebraicGeometry.Stack.exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack`:
  the existence statements of **Stacks 0DSM**, under the carried hypotheses.

## Implementation notes

Containment of open substacks is containment of their object properties: an open substack is
determined by its property, by `AlgebraicGeometry.Stack.OpenSubstack.ext`, and `≤` on
`CategoryTheory.ObjectProperty` is the pointwise implication that `|𝒰| ⊆ |𝒱|` asks for.

The supremum is written as an `iSup` over the subtype of open substacks with the property,
rather than an `sSup` over a set of properties, so that `CategoryTheory.ObjectProperty`'s
pointwise description `CategoryTheory.ObjectProperty.prop_iSup_iff` and its
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` instance for suprema apply directly;
strict fullness of the loci is then an instance rather than a lemma.

The DM and quasi-DM properties used are the *absolute* ones of **Stacks 050D**, parts (5) and
(6), so the ambient big fppf site is required to contain the terminal scheme `Spec ℤ`; the
hypothesis is `hZ` throughout, exactly as in
`StacksFrontier/AlgebraicGeometry/Stacks/SeparationAbsolute.lean`.

The local-global hypotheses are indexed by a `Set` of open substacks rather than by an
arbitrary type, which keeps them free of a universe parameter beyond the two the algebraic
stack already has.

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0DSJ](https://stacks.math.columbia.edu/tag/0DSJ)
* [Stacks Project, Tag 0DSM](https://stacks.math.columbia.edu/tag/0DSM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An open substack of `𝒳`, read as an algebraic stack over the same base: the full
subcategory it selects, which is an algebraic stack by
`AlgebraicGeometry.Stack.OpenSubstack.isAlgebraic`. -/
noncomputable abbrev OpenSubstack.toAlgebraicStack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) : AlgebraicStacks.{u, w} B S hS :=
  fullSubcategoryAlgebraicStack 𝒳 U.property U.isAlgebraic

variable (B S hS)

/-- The open substacks of `𝒳` that are Deligne–Mumford, in the absolute sense of
**Stacks 050D**, part (5). -/
abbrev DMOpenSubstack (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Type _ :=
  {U : OpenSubstack 𝒳 // AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack}

/-- The open substacks of `𝒳` that are quasi-Deligne–Mumford, in the absolute sense of
**Stacks 050D**, part (6). -/
abbrev QuasiDMOpenSubstack (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Type _ :=
  {U : OpenSubstack 𝒳 // AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ U.toAlgebraicStack}

/-- **Stacks 0DSM**, the Deligne–Mumford locus. The object property of an algebraic stack `𝒳`
cut out by the supremum of the object properties of its Deligne–Mumford open substacks; this is
the substack `𝒳''` of the source. -/
@[stacks 0DSM "the DM locus, as the supremum of the DM open substacks"]
noncomputable def dmLocus (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : ObjectProperty 𝒳.val.val.obj :=
  ⨆ U : DMOpenSubstack B S hS hZ 𝒳, U.1.property

/-- **Stacks 0DSM**, the quasi-Deligne–Mumford locus. The object property of an algebraic stack
`𝒳` cut out by the supremum of the object properties of its quasi-Deligne–Mumford open
substacks; this is the substack `𝒳'` of the source. -/
@[stacks 0DSM "the quasi-DM locus, as the supremum of the quasi-DM open substacks"]
noncomputable def quasiDMLocus (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : ObjectProperty 𝒳.val.val.obj :=
  ⨆ U : QuasiDMOpenSubstack B S hS hZ 𝒳, U.1.property

variable (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- Membership in a supremum of the properties of the open substacks satisfying `P`. -/
private theorem prop_iSup_subtype_iff {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (P : OpenSubstack 𝒳 → Prop) (X : 𝒳.val.val.obj) :
    (⨆ U : {U : OpenSubstack 𝒳 // P U}, U.1.property) X ↔ ∃ U, P U ∧ U.property X := by
  rw [ObjectProperty.prop_iSup_iff]
  exact ⟨fun ⟨U, hX⟩ => ⟨U.1, U.2, hX⟩, fun ⟨U, hU, hX⟩ => ⟨⟨U, hU⟩, hX⟩⟩

/-- An object of `𝒳` lies in the Deligne–Mumford locus exactly when some Deligne–Mumford open
substack contains it. -/
theorem dmLocus_apply_iff (X : 𝒳.val.val.obj) :
    dmLocus B S hS hZ 𝒳 X ↔ ∃ U : OpenSubstack 𝒳,
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack ∧ U.property X := by
  exact prop_iSup_subtype_iff B S hS _ X

/-- An object of `𝒳` lies in the quasi-Deligne–Mumford locus exactly when some
quasi-Deligne–Mumford open substack contains it. -/
theorem quasiDMLocus_apply_iff (X : 𝒳.val.val.obj) :
    quasiDMLocus B S hS hZ 𝒳 X ↔ ∃ U : OpenSubstack 𝒳,
      AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ U.toAlgebraicStack ∧ U.property X := by
  exact prop_iSup_subtype_iff B S hS _ X

/-- **Stacks 0DSM, maximality for the DM locus.** Every Deligne–Mumford open substack of `𝒳` is
contained in the Deligne–Mumford locus. This is the force of the word *largest* in the source,
and it holds with no hypothesis beyond those of the ambient site. -/
@[stacks 0DSM "maximality of the DM locus"]
theorem le_dmLocus (U : OpenSubstack 𝒳)
    (hU : AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack) :
    U.property ≤ dmLocus B S hS hZ 𝒳 :=
  le_iSup (fun V : DMOpenSubstack B S hS hZ 𝒳 => V.1.property) ⟨U, hU⟩

/-- **Stacks 0DSM, maximality for the quasi-DM locus.** Every quasi-Deligne–Mumford open
substack of `𝒳` is contained in the quasi-Deligne–Mumford locus. -/
@[stacks 0DSM "maximality of the quasi-DM locus"]
theorem le_quasiDMLocus (U : OpenSubstack 𝒳)
    (hU : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ U.toAlgebraicStack) :
    U.property ≤ quasiDMLocus B S hS hZ 𝒳 :=
  le_iSup (fun V : QuasiDMOpenSubstack B S hS hZ 𝒳 => V.1.property) ⟨U, hU⟩

/-- The Deligne–Mumford locus is closed under isomorphism: it is a supremum of the object
properties of open substacks, each of which is strictly full. -/
instance isClosedUnderIsomorphisms_dmLocus :
    (dmLocus B S hS hZ 𝒳).IsClosedUnderIsomorphisms := by
  have : ∀ U : DMOpenSubstack B S hS hZ 𝒳, U.1.property.IsClosedUnderIsomorphisms :=
    fun U => U.1.strictlyFull
  rw [dmLocus]
  infer_instance

/-- The quasi-Deligne–Mumford locus is closed under isomorphism. -/
instance isClosedUnderIsomorphisms_quasiDMLocus :
    (quasiDMLocus B S hS hZ 𝒳).IsClosedUnderIsomorphisms := by
  have : ∀ U : QuasiDMOpenSubstack B S hS hZ 𝒳, U.1.property.IsClosedUnderIsomorphisms :=
    fun U => U.1.strictlyFull
  rw [quasiDMLocus]
  infer_instance

/-- **Stacks 0DSM, the nesting `𝒳'' ⊆ 𝒳'`.** The Deligne–Mumford locus is contained in the
quasi-Deligne–Mumford locus, because a Deligne–Mumford open substack is quasi-Deligne–Mumford by
**Stacks 050E** (`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isDM`). This holds with
no further input. -/
@[stacks 0DSM "the DM locus is contained in the quasi-DM locus"]
theorem dmLocus_le_quasiDMLocus :
    dmLocus B S hS hZ 𝒳 ≤ quasiDMLocus B S hS hZ 𝒳 := by
  rw [dmLocus]
  exact iSup_le fun U => le_quasiDMLocus B S hS hZ 𝒳 U.1
    (AlgebraicStacks.isQuasiDM_of_isDM B (⊤_ Scheme.{u}) hZ U.2)

/-- **The local-global step of the proof of Stacks 0DSM, for the absolute DM property.** An open
substack whose object property is the supremum of the object properties of a family of
Deligne–Mumford open substacks is itself Deligne–Mumford.

This is the one place the source's proof of **Stacks 0DSM** needs input beyond formal
manipulation of open substacks: the source obtains, from **Stacks 06N3**, a scheme with a
surjective étale morphism onto each member of the family, and notes that the disjoint union of
those schemes is then surjective and étale onto the union. **Stacks 06N3** is not in the
library, so this step is a hypothesis rather than a theorem. -/
abbrev IsAbsolutelyDMLocalOnOpenSubstacks : Prop :=
  ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) (s : Set (OpenSubstack 𝒴)) (W : OpenSubstack 𝒴),
    W.property = ⨆ U : s, (U : OpenSubstack 𝒴).property →
      (∀ U ∈ s, AlgebraicStacks.IsAbsolutelyDM B S hS hZ
          (OpenSubstack.toAlgebraicStack U)) →
        AlgebraicStacks.IsAbsolutelyDM B S hS hZ W.toAlgebraicStack

/-- **The local-global step of the proof of Stacks 0DSM, for the absolute quasi-DM property.**
The quasi-Deligne–Mumford twin of
`AlgebraicGeometry.Stack.IsAbsolutelyDMLocalOnOpenSubstacks`; the source deduces it the same
way from **Stacks 06MF** in place of **Stacks 06N3**. -/
abbrev IsAbsolutelyQuasiDMLocalOnOpenSubstacks : Prop :=
  ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) (s : Set (OpenSubstack 𝒴)) (W : OpenSubstack 𝒴),
    W.property = ⨆ U : s, (U : OpenSubstack 𝒴).property →
      (∀ U ∈ s, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ
          (OpenSubstack.toAlgebraicStack U)) →
        AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ W.toAlgebraicStack

/-- An open substack cutting out the Deligne–Mumford locus is Deligne–Mumford, given the
local-global step: the locus is by construction the supremum over the set of Deligne–Mumford
open substacks. -/
theorem isAbsolutelyDM_of_property_eq_dmLocus
    (hLocal : IsAbsolutelyDMLocalOnOpenSubstacks.{u, w} B S hS hZ)
    (W : OpenSubstack 𝒳) (hW : W.property = dmLocus B S hS hZ 𝒳) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ W.toAlgebraicStack :=
  hLocal 𝒳 {U : OpenSubstack 𝒳 |
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack} W hW fun _ hU => hU

/-- An open substack cutting out the quasi-Deligne–Mumford locus is quasi-Deligne–Mumford, given
the local-global step. -/
theorem isAbsolutelyQuasiDM_of_property_eq_quasiDMLocus
    (hLocal : IsAbsolutelyQuasiDMLocalOnOpenSubstacks.{u, w} B S hS hZ)
    (W : OpenSubstack 𝒳) (hW : W.property = quasiDMLocus B S hS hZ 𝒳) :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ W.toAlgebraicStack :=
  hLocal 𝒳 {U : OpenSubstack 𝒳 |
      AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ U.toAlgebraicStack} W hW fun _ hU => hU

/-- If `L` bounds every open substack satisfying `P` and is cut out by an open substack, which
then satisfies `P`, that substack is the largest one satisfying `P`. -/
private theorem exists_largest_of_locus (P : OpenSubstack 𝒳 → Prop)
    (L : ObjectProperty 𝒳.val.val.obj)
    (hmax : ∀ U, P U → U.property ≤ L) (hP : ∀ W : OpenSubstack 𝒳, W.property = L → P W)
    (hOpen : ∃ W : OpenSubstack 𝒳, W.property = L) :
    ∃ W : OpenSubstack 𝒳, W.property = L ∧ P W ∧ ∀ V, P V → V.property ≤ W.property := by
  obtain ⟨W, hW⟩ := hOpen
  exact ⟨W, hW, hP W hW, fun V hV => hW ▸ hmax V hV⟩

/-- **Stacks 0DSM for the DM property.** An algebraic stack has a largest Deligne–Mumford open
substack, and it cuts out the Deligne–Mumford locus.

Two inputs are carried, both standing for **Stacks 06N3**, which the library does not have:
`hOpen`, that the Deligne–Mumford locus is cut out by an open substack at all, and `hLocal`,
the local-global step. Maximality is not among them — it is
`AlgebraicGeometry.Stack.le_dmLocus`, which holds unconditionally. -/
@[stacks 0DSM "existence of the largest DM open substack; the structure theorem Stacks 06N3 is
  not in the library, so its two uses are carried as the hypotheses `hLocal` (a union of DM open
  substacks is DM) and `hOpen` (the DM locus is cut out by an open substack)"]
theorem exists_largest_isAbsolutelyDM_openSubstack
    (hLocal : IsAbsolutelyDMLocalOnOpenSubstacks.{u, w} B S hS hZ)
    (hOpen : ∃ W : OpenSubstack 𝒳, W.property = dmLocus B S hS hZ 𝒳) :
    ∃ W : OpenSubstack 𝒳,
      W.property = dmLocus B S hS hZ 𝒳 ∧
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ W.toAlgebraicStack ∧
      ∀ V : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyDM B S hS hZ V.toAlgebraicStack →
        V.property ≤ W.property := by
  exact exists_largest_of_locus B S hS 𝒳 _ _ (le_dmLocus B S hS hZ 𝒳)
    (isAbsolutelyDM_of_property_eq_dmLocus B S hS hZ 𝒳 hLocal) hOpen

/-- **Stacks 0DSM for the quasi-DM property.** An algebraic stack has a largest
quasi-Deligne–Mumford open substack, and it cuts out the quasi-Deligne–Mumford locus. The two
carried inputs stand for **Stacks 06MF**, as in
`AlgebraicGeometry.Stack.exists_largest_isAbsolutelyDM_openSubstack`. -/
@[stacks 0DSM "existence of the largest quasi-DM open substack; the structure theorem Stacks
  06MF is not in the library, so its two uses are carried as the hypotheses `hLocal` (a union of
  quasi-DM open substacks is quasi-DM) and `hOpen` (the quasi-DM locus is cut out by an open
  substack)"]
theorem exists_largest_isAbsolutelyQuasiDM_openSubstack
    (hLocal : IsAbsolutelyQuasiDMLocalOnOpenSubstacks.{u, w} B S hS hZ)
    (hOpen : ∃ W : OpenSubstack 𝒳, W.property = quasiDMLocus B S hS hZ 𝒳) :
    ∃ W : OpenSubstack 𝒳,
      W.property = quasiDMLocus B S hS hZ 𝒳 ∧
      AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ W.toAlgebraicStack ∧
      ∀ V : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ V.toAlgebraicStack →
        V.property ≤ W.property := by
  exact exists_largest_of_locus B S hS 𝒳 _ _ (le_quasiDMLocus B S hS hZ 𝒳)
    (isAbsolutelyQuasiDM_of_property_eq_quasiDMLocus B S hS hZ 𝒳 hLocal) hOpen

/-- **Stacks 0DSM.** For an algebraic stack `𝒳` there are open substacks `𝒳'' ⊆ 𝒳' ⊆ 𝒳` with
`𝒳''` Deligne–Mumford, `𝒳'` quasi-Deligne–Mumford, and each the largest open substack of `𝒳`
with its property. This is the statement of the source lemma.

The four carried hypotheses are the two uses apiece of **Stacks 06N3** and **Stacks 06MF**
described on
`AlgebraicGeometry.Stack.exists_largest_isAbsolutelyDM_openSubstack` and
`AlgebraicGeometry.Stack.exists_largest_isAbsolutelyQuasiDM_openSubstack`. The nesting
`𝒳'' ⊆ 𝒳'` is not among them: it is `AlgebraicGeometry.Stack.dmLocus_le_quasiDMLocus`, which
holds unconditionally. -/
@[stacks 0DSM "the lemma: nested largest DM and quasi-DM open substacks. The structure theorems
  Stacks 06N3 and 06MF are not in the library, so their uses are carried as the hypotheses
  `hLocalDM`, `hLocalQuasiDM` (a union of DM, resp. quasi-DM, open substacks has that property)
  and `hOpenDM`, `hOpenQuasiDM` (each locus is cut out by an open substack)"]
theorem exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack
    (hLocalDM : IsAbsolutelyDMLocalOnOpenSubstacks.{u, w} B S hS hZ)
    (hLocalQuasiDM : IsAbsolutelyQuasiDMLocalOnOpenSubstacks.{u, w} B S hS hZ)
    (hOpenDM : ∃ W : OpenSubstack 𝒳, W.property = dmLocus B S hS hZ 𝒳)
    (hOpenQuasiDM : ∃ W : OpenSubstack 𝒳, W.property = quasiDMLocus B S hS hZ 𝒳) :
    ∃ W' W'' : OpenSubstack 𝒳,
      W''.property ≤ W'.property ∧
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ W''.toAlgebraicStack ∧
      AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ W'.toAlgebraicStack ∧
      (∀ V : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyDM B S hS hZ V.toAlgebraicStack →
        V.property ≤ W''.property) ∧
      ∀ V : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ V.toAlgebraicStack →
        V.property ≤ W'.property := by
  obtain ⟨W'', hW''eq, hW''DM, hW''max⟩ :=
    exists_largest_isAbsolutelyDM_openSubstack B S hS hZ 𝒳 hLocalDM hOpenDM
  obtain ⟨W', hW'eq, hW'QDM, hW'max⟩ :=
    exists_largest_isAbsolutelyQuasiDM_openSubstack B S hS hZ 𝒳 hLocalQuasiDM hOpenQuasiDM
  refine ⟨W', W'', ?_, hW''DM, hW'QDM, hW''max, hW'max⟩
  rw [hW''eq, hW'eq]
  exact dmLocus_le_quasiDMLocus B S hS hZ 𝒳

end AlgebraicGeometry.Stack

end
