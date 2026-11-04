module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialize.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections

/-!
# The two spellings of the nonvanishing locus of Stacks Tag 01CY agree

Stacks Tag 01CY is stated in this repository twice. The tagged statement is about a
**ringed space** `X` with local stalks and a module `L : SheafOfModules (structureSheaf X.sheaf)`,
and that is the spelling of
`StacksFrontier/AlgebraicGeometry/NonvanishingTrivialize/Basic.lean`. Every consumer -- ampleness
(Stacks Tag 01PS), quasi-affineness, the section ring -- works with a **scheme** `X`, a module
`M : X.Modules` and a global section `s : Γ(M, ⊤)`, which is the spelling of
`StacksFrontier/AlgebraicGeometry/NonvanishingOpen/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/AmplePowers/Basic.lean`.

This file compares them, and the comparison is as cheap as it could be: **the two nonvanishing
loci are equal by `rfl`**, and so are the two nonvanishing opens. Nothing has to be transported,
nothing has to be rewritten; the only genuine difference between the two statements is that the
ringed-space one takes a restriction-compatible family `s : L.sections` where the scheme one takes
its value `s.eval (op ⊤)` at the terminal open, and the bridge for that is
`Stacks.SectionRingGeometric.sectionsEquivObj`.

## Main results

* `Stacks.NonvanishingSpelling.nonvanishingLocus_eq` and
  `Stacks.NonvanishingSpelling.nonvanishingOpen_eq`: **the identification**, both by `rfl`. The
  nonvanishing locus (resp. open) of `s : M.sections` computed for the underlying ringed space of
  a scheme is the one computed for the scheme itself, of the global section `s` names.
* `Stacks.NonvanishingSpelling.nonvanishingLocus_symm_eq` and
  `Stacks.NonvanishingSpelling.nonvanishingOpen_symm_eq`: the same identification read in the
  other direction, starting from a global section `s : Γ(M, ⊤)`. This is the form the consumers
  need, and it is not `rfl`: `(sectionsEquiv X M).symm s` restricts `s` along the unique morphism
  to `⊤`, which is the identity only up to `Equiv.apply_symm_apply`.
* `Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq` and
  `Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq`: the same identification for
  `Stacks.SheafOfModules.nonvanishingLocus`, which forms `𝔪_x · M_x` in the stalk module of
  Stacks Tag 01CB rather than in Mathlib's. The two module structures are equal but not
  definitionally so, so this one is a short proof rather than `rfl`.
* `Stacks.NonvanishingSpelling.isInvertible_toRingedSpace`: the invertibility hypothesis at the
  ringed-space spelling, obtained from `Stacks.Ample.IsInvertibleModule` by definitional
  unfolding. Instance search does **not** cross this gap on its own, which is the one real
  friction in the bridge, so this is a `scoped instance`: a consumer wanting to state anything at
  the ringed-space spelling needs `open Stacks.NonvanishingSpelling`. See *Implementation notes*.
* `Stacks.NonvanishingSpelling.sectionsEquiv`: `M.sections ≃ Γ(M, ⊤)` for a module on a scheme,
  i.e. `Stacks.SectionRingGeometric.sectionsEquivObj` with the terminality of `⊤` supplied.
* `Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff`: membership of the bundled scheme-level
  open spelled out at the level of germs.

The trivialization clause of the tag is transported in
`StacksFrontier/AlgebraicGeometry/NonvanishingSpelling/Trivialize.lean`.

## The route

Four definitional coincidences do all the work.

* `X.toRingedSpace.presheaf = X.presheaf` and
  `TopologicalSpace.Opens X.toRingedSpace = X.Opens`, so the stalks, the opens and the
  membership predicates are literally the same objects.
* `structureSheaf X.toRingedSpace.sheaf = X.ringCatSheaf` -- both sides are
  `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` -- so
  `SheafOfModules (structureSheaf X.toRingedSpace.sheaf) = X.Modules`, which is why
  `Stacks.NonvanishingSpelling.toSheafOfModules` can be the identity. This is the
  `rfl` already recorded as
  `Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf`, at the other `structureSheaf`.
* The two stalk-module instances, `Stacks.NonvanishingTrivialize.stalkModule` and
  `Stacks.ModuleStalk.stalkModule`, are the *same term*
  (`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier` applied to
  `X.presheaf` and `M.val`), so the submodules `𝔪_x · M_x` named by
  `Stacks.NonvanishingTrivialize.maximalSmul` and `Stacks.ModuleStalk.maximalSmul` are equal by
  `rfl` and not merely isomorphic.
* `Stacks.Ample.nonvanishingLocus M s` is `{x | (M.presheaf.Γgerm x).hom s ∉ maximalSmul M x}`
  and `Stacks.NonvanishingTrivialize.nonvanishingLocus X L s` is
  `{x | (TopCat.Presheaf.Γgerm L.val.presheaf x).hom (s.eval (op ⊤)) ∉ maximalSmul X L x}`, and
  `Scheme.Modules.presheaf M` is by definition `M.val.presheaf`. With the previous point the two
  set-builders are the same expression.

## Implementation notes

**Instance search does not cross the gap, definitional equality does.**
`Stacks.Ample.IsInvertibleModule X M` is `IsInvertible X.presheaf _ M` while the ringed-space
declarations ask for `IsInvertible X.toRingedSpace.sheaf.obj _ M`. The two are definitionally
equal -- `SheafedSpace.sheaf` packages the presheaf it is built from -- but instance search is
syntactic and fails on the first. `isInvertible_toRingedSpace` closes the gap with `‹_›`, the
definitional check happening once at that declaration.

It is a **`scoped instance`**: `open Stacks.NonvanishingSpelling` turns it on, and a file that
does not open the namespace is untouched. The reason for scoping it is caution, not an observed
failure. Its conclusion and its
hypothesis have the same class head, so a *global* instance would offer instance search a step
from `IsInvertible` to `IsInvertible` in every file importing this one; such an instance
does not loop -- the discrimination key retains `SheafedSpace.sheaf`, which no `IsInvertible`
goal at the scheme spelling matches, and `infer_instance` on a goal with no witness still fails
immediately. Scoping is kept anyway, since the opt-in costs a consumer one `open`.

The sheaf-condition arguments of the two `IsInvertible`s differ as terms and agree by proof
irrelevance; `IsInvertible` is a `Prop`-valued class, so this costs nothing and the `@[simp]`
lemmas below match up to it.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorSheafification
open Stacks.ModuleStalk

universe u

namespace Stacks.NonvanishingSpelling

variable (X : Scheme.{u}) (M : X.Modules)

/-! ### The identity coercion of the module -/

/-- An `𝒪_X`-module on a scheme, read as a module on the underlying ringed space of `X` in the
`Stacks.SheafOfModules.TensorSheafification` packaging of the structure sheaf. This is the
  **identity**: `X.Modules` is
`SheafOfModules X.ringCatSheaf`, and `structureSheaf X.toRingedSpace.sheaf` is `X.ringCatSheaf`,
both sides being `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`. It exists only so
that the ringed-space declarations can be applied without a type ascription at every use. -/
abbrev toSheafOfModules : SheafOfModules.{u} (_root_.structureSheaf X.toRingedSpace.sheaf) := M

/-- **Invertibility at the ringed-space spelling.** `Stacks.Ample.IsInvertibleModule X M` asks
for `IsInvertible X.presheaf _ M` and the ringed-space statement of Stacks Tag 01CY asks for
`IsInvertible X.toRingedSpace.sheaf.obj _ M`; the two are definitionally equal, and instance
search does not see it. A `scoped instance`, so that only a file opening this namespace gains the
extra step; see the implementation notes. -/
scoped instance isInvertible_toRingedSpace [Stacks.Ample.IsInvertibleModule X M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.sheaf.obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property (toSheafOfModules X M) := ‹_›


/-! ### Sections against global sections -/

/-- **The sections of an `𝒪_X`-module on a scheme are its global sections.** A
restriction-compatible family of sections over every open is determined by, and determines, its
value over `⊤`, because `⊤` is terminal in the site of opens. This is
`Stacks.SectionRingGeometric.sectionsEquivObj` with that terminality supplied. -/
noncomputable def sectionsEquiv : (toSheafOfModules X M).sections ≃ Γ(M, ⊤) :=
  Stacks.SectionRingGeometric.sectionsEquivObj isTerminalTop M.val

/-- `sectionsEquiv` sends a compatible family of sections to its value over `⊤`. -/
@[simp] theorem sectionsEquiv_apply (s : (toSheafOfModules X M).sections) :
    sectionsEquiv X M s = s.eval (op ⊤) := rfl

/-- The family produced from a global section restricts, over every open, to the restriction of
that global section. -/
@[simp] theorem sectionsEquiv_symm_eval (s : Γ(M, ⊤)) (W : X.Opens) :
    ((sectionsEquiv X M).symm s).eval (op W) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := rfl

/-! ### The nonvanishing locus -/

/-- **The submodules `𝔪_x · M_x` of the two spellings are equal**, by `rfl`: the stalk-module
instances `Stacks.NonvanishingTrivialize.stalkModule` and `Stacks.ModuleStalk.stalkModule` are
the same term, so `IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤` means the same thing on
both sides. -/
@[simp] theorem maximalSmul_eq (x : X) :
    Stacks.NonvanishingTrivialize.maximalSmul X.toRingedSpace (toSheafOfModules X M) x
      = Stacks.ModuleStalk.maximalSmul M x := rfl

/-- **The two spellings of the nonvanishing locus of Stacks Tag 01CY agree**, by `rfl`: the
ringed-space locus of a restriction-compatible family is the scheme-level locus of the global
section it names. -/
@[simp] theorem nonvanishingLocus_eq (s : (toSheafOfModules X M).sections) :
    Stacks.NonvanishingTrivialize.nonvanishingLocus X.toRingedSpace (toSheafOfModules X M) s
      = Stacks.Ample.nonvanishingLocus M (sectionsEquiv X M s) := rfl

/-- `nonvanishingLocus_eq` read from the scheme side: the ringed-space locus of the family
produced from a global section `s` is the scheme-level locus of `s`. Not `rfl` -- the family
restricts `s` along the unique morphism `W ⟶ ⊤`, which is the identity only after
`Equiv.apply_symm_apply`. -/
theorem nonvanishingLocus_symm_eq (s : Γ(M, ⊤)) :
    Stacks.NonvanishingTrivialize.nonvanishingLocus X.toRingedSpace (toSheafOfModules X M)
        ((sectionsEquiv X M).symm s) = Stacks.Ample.nonvanishingLocus M s :=
  by rw [nonvanishingLocus_eq, Equiv.apply_symm_apply]

/-! ### The nonvanishing open -/

variable [Stacks.Ample.IsInvertibleModule X M]

/-- **The two spellings of the nonvanishing open of Stacks Tag 01CY agree**, by `rfl`. The two
openness proofs are propositions, so the bundles are equal as soon as the carriers are, and here
the carriers are not merely equal but the same expression. -/
@[simp] theorem nonvanishingOpen_eq (s : (toSheafOfModules X M).sections) :
    Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace (toSheafOfModules X M) s
      = Stacks.NonvanishingOpen.nonvanishingOpen X M (sectionsEquiv X M s) := rfl

/-- `nonvanishingOpen_eq` read from the scheme side. This is the form the consumers need: it
turns the ringed-space `X_s` of the tagged statement into the `X.Opens` that ampleness and
quasi-affineness are stated with. -/
theorem nonvanishingOpen_symm_eq (s : Γ(M, ⊤)) :
    Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace (toSheafOfModules X M)
        ((sectionsEquiv X M).symm s) = Stacks.NonvanishingOpen.nonvanishingOpen X M s :=
  Opens.ext (nonvanishingLocus_symm_eq X M s)

/-- Membership of the bundled nonvanishing open, spelled out at the level of germs. The
scheme-level `Stacks.NonvanishingOpen.mem_nonvanishingOpen` unfolds the bundle and
`Stacks.Ample.mem_nonvanishingLocus_iff` unfolds the locus; this composes them, so that a
consumer never has to name the locus. -/
theorem mem_nonvanishingOpen_iff (s : Γ(M, ⊤)) (x : X) :
    x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X M s ↔
      (M.presheaf.Γgerm x).hom s ∉ Stacks.ModuleStalk.maximalSmul M x :=
  Iff.rfl

/-! ### The third spelling: the nonvanishing locus in the stalk module of Stacks Tag 01CB -/

omit [Stacks.Ample.IsInvertibleModule X M] in
/-- **The nonvanishing locus of Stacks Tag 01CY taken in the stalk module of Stacks Tag 01CB is
the scheme-level one.** `Stacks.SheafOfModules.nonvanishingLocus` asks that the germ of `s` avoid
`𝔪_x · M_x` formed in the hand-built module structure of Tag 01CB, and
`Stacks.Ample.nonvanishingLocus` asks it in Mathlib's; the two module structures are equal, by
`Stacks.NonvanishingPullback.stalkModule_eq_scheme`. -/
theorem stalkNonvanishingLocus_eq (s : (toSheafOfModules X M).sections) :
    Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M s
      = Stacks.Ample.nonvanishingLocus M (sectionsEquiv X M s) := by
  ext x
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, Stacks.NonvanishingPullback.mem_maximalSmul_iff]
  exact not_congr Iff.rfl

omit [Stacks.Ample.IsInvertibleModule X M] in
/-- `Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq` read from the scheme side, starting
from a global section rather than from a restriction-compatible family. This is the form a
consumer of Stacks Tag 01PS or Stacks Tag 01PY needs. -/
theorem stalkNonvanishingLocus_symm_eq (s : Γ(M, ⊤)) :
    Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M
        ((sectionsEquiv X M).symm s) = Stacks.Ample.nonvanishingLocus M s :=
  by rw [stalkNonvanishingLocus_eq, Equiv.apply_symm_apply]

end Stacks.NonvanishingSpelling

end
