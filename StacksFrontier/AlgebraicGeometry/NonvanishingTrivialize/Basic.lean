module

public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01CY: a nonvanishing section trivializes an invertible module

Let `(X, 𝒪_X)` be a ringed space all of whose stalks `𝒪_{X,x}` are local rings, let `L` be an
invertible `𝒪_X`-module and let `s` be a global section of `L`. On the nonvanishing locus

`X_s = {x ∈ X ∣ germ_x s ∉ 𝔪_x L_x}`

the section `s` is a basis of `L`. This file proves the statement of Stacks Tag 01CY that says
so: the morphism `𝒪_X ⟶ L` determined by `s`, restricted to `X_s`, is an isomorphism.

Everything is stated at the **ringed-space** spelling of the tagged statement --
`X : RingedSpace.{u}` and `L : SheafOfModules.{u} (structureSheaf X.sheaf)` for the
`structureSheaf` of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomLeftExact.lean` --
rather than at the scheme spelling
of `StacksFrontier/AlgebraicGeometry/NonvanishingOpen/Basic.lean`, which is where the openness
clause of the tag is proved and carries its attribute. Openness is therefore reproved here, at
this spelling, as a prerequisite for the statement of the trivialization: the open set `X_s`
cannot be formed without it. Its proof is the one of the sibling file, transported.

## Main definitions

* `Stacks.NonvanishingTrivialize.nonvanishingLocus` and
  `Stacks.NonvanishingTrivialize.nonvanishingOpen`: the locus `X_s` and, once openness is
  available, the open subset. The locus is the tagged statement's definition verbatim, the module
  structure
  on the stalk being the one named in `Stacks.NonvanishingTrivialize.stalkModule`.
* `Stacks.NonvanishingTrivialize.moduleSections`: the action of `𝒪_X(U)` on `L(U)` at the
  spelling `X.presheaf.obj (op U)` of the ring of sections. Mathlib has this for a scheme
  (`Module Γ(X, U) Γ(M, U)`) and not for a ringed space; see *The compiler option of the tagged
  statement*.
* `Stacks.NonvanishingTrivialize.res`: restriction of a section of `L`, landing in
  `L.val.obj (op W')` rather than in the restricted-scalars wrapper that
  `PresheafOfModules.map` produces.
* `Stacks.NonvanishingTrivialize.triv`, `basis`, `trivEval`, `TrivGermMem`: the trivializing
  map, the local basis section, the trivializing function of a global section and the predicate
  driving the induction -- the vocabulary of the sibling file, at this spelling.

## Main results

* `Stacks.NonvanishingTrivialize.isIso_over_nonvanishingOpen`: **Stacks Tag 01CY, the
  trivialization clause**, in the shape of the tagged statement, an instance as it is declared
  there:
  `IsIso ((L.unitHomEquiv.symm s).over (nonvanishingOpen X L s))`.
  `Stacks.NonvanishingTrivialize.isIso_over_of_le` is the same for an arbitrary open inside the
  nonvanishing locus, which is what the induction over the slice site consumes.
* `Stacks.NonvanishingTrivialize.bijective_smul`: the content of that clause in elementary
  terms -- over every open `W ⊆ X_s`, the map `a ↦ a • s|_W` from `𝒪_X(W)` to `L(W)` is
  bijective.
* `Stacks.NonvanishingTrivialize.isOpen_nonvanishingLocus` and
  `Stacks.NonvanishingTrivialize.nonvanishingOpen`: openness of `X_s` at this spelling, the
  prerequisite described above.
* `Stacks.NonvanishingTrivialize.notMem_maximalSmul_germ_basis` and
  `mem_nonvanishingLocus_iff_isUnit`: the two steps with content in openness -- the local basis
  section vanishes nowhere, and on a trivializing open a section fails to vanish exactly where
  its trivializing function is a unit.
* `Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app`: the morphism that the tag's statement
  builds from `s` acts on sections by multiplication by `s`. This is what connects the shape of
  the statement to the elementary content.

## The route

Invertibility enters only through clause 2 of Stacks Tag 0B8M, proved as
`Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible`: `L` is sectionwise trivial on
an open cover. Three steps then finish both the openness prerequisite and the trivialization.

* **The local basis section vanishes nowhere** (`notMem_maximalSmul_germ_basis`), by the
  induction of the sibling file over `Submodule.smul_induction_on`.
* **On a trivializing open `V`, `X_s ∩ V` is the basic open of the trivializing function**
  (`nonvanishingLocus_inter`). With `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen` this
  gives, around each point of `X_s`, an open on which -- and on every open inside which -- the
  trivializing function of `s` is a unit, hence on which `a ↦ a • s` is bijective
  (`bijective_smul_of_isUnit`, `exists_nhd_bijective_smul`).
* **Bijectivity is local** (`bijective_smul`). Injectivity glues by separatedness of `𝒪_X`;
  for surjectivity the local preimages agree on overlaps because multiplication by `s` is
  injective there, so they glue by the sheaf condition of `𝒪_X`, and the glued section
  multiplies to the given one because `L` is separated. These three uses of the sheaf conditions
  are `eq_of_res_eq_ring`, `exists_res_eq_ring` and `eq_of_res_eq`, thin restatements of
  Mathlib's unique-gluing API at this file's spellings.

Finally `IsIso` of the restricted morphism is reflected from presheaves of abelian groups: the
component of `(f.over U)` at an object `W` of the slice site is **definitionally** the component
of `f` at `W` (recorded by a `change` in `isIso_over_of_le`), a component is an isomorphism as
soon as it is bijective, and `PresheafOfModules.toPresheaf` and `SheafOfModules.forget` both
reflect isomorphisms.

No stalk of `L` is identified with anything, no Nakayama argument is used, and the stalk of a
tensor product is never compared with the tensor product of the stalks.

## The compiler option of the tagged statement

The tagged statement of Tag 01CY sets `backward.isDefEq.respectTransparency` to `false` for its
whole file. **This file sets no compiler option**, and the trivialization clause needs none: its
statement elaborates as it stands, and so does the tagged definition of the nonvanishing locus.

The tag's *other* unproved clause, the inverse section in the `(-1)`-st tensor power, is a
different matter, and it is recorded here because it is the one thing in that statement that
the option is doing. The statement pairs a section of the first tensor power with
one of the `(-1)`-st over the ring `X.presheaf.obj (op U)`. The tensor product needs
`Module ↑(X.presheaf.obj (op U)) ↑((tensorPower L 1).val.obj (op U))`, and that instance is
**not synthesized**: the sections of the module are a `ModuleCat` over the `RingCat`-valued
`(structureRingPresheaf X.presheaf).obj (op U)`, which is the same ring with another spelling,
and instance search is syntactic. Relaxing transparency makes the search succeed, which is why
the tagged statement needs the option for that clause. It is not the only repair: the missing
instance is
exactly the ringed-space analogue of Mathlib's `Module Γ(X, U) Γ(M, U)` for a scheme
(`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`), and supplying it -- as
`Stacks.NonvanishingTrivialize.moduleSections` does here for `L` itself, and as one more line
would do for the base ring sheaf spelled by Stacks Tag 05NA -- makes the inverse-section
statement elaborate at the tagged statement's exact spelling with no option and no change to
the statement.

## Universes

`AlgebraicGeometry.RingedSpace` has two universe parameters, the rings' and the carrier's, and
`RingedSpace.{u}` leaves the second free. Writing `structureSheaf X.sheaf` collapses them: that
`structureSheaf` takes a `TopCat.Sheaf CommRingCat.{v} Y` for `Y : TopCat.{v}`, so the mere act
of writing it forces `RingedSpace.{u}` to elaborate as `RingedSpace.{u, u}`, and the
sheafification instances for the site of `X` are then found. At the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf h𝒪` spelling the carrier
  universe stays free and they are
not; this is the observation recorded in
`StacksFrontier/AlgebraicGeometry/InvertibleRankOneIff/Basic.lean`, and it is why every
declaration below mentions `L`, whose type performs the collapse. The collapsed universe is also
what `Stacks.SheafDescent.Trivialization` needs, its module universe being `max u v w`.

The index type of the gluings is the subtype of the open being glued over, which lives in the
carrier's universe, as Mathlib's unique-gluing API requires.

## Transparency gotchas

**1. Three spellings of the sections, and the scalar action only exists at one.** The sections
of `L` over `W` can be written `L.val.obj (op W)` (a `ModuleCat`), `L.val.presheaf.obj (op W)`
(an `AddCommGrpCat`) or, after a restriction map, as the restricted-scalars wrapper
`(ModuleCat.restrictScalars _).obj (L.val.obj (op W))`. All three have the same carrier and none
is syntactically another, so each would need its own `SMul` and `Add` instances. The file fixes
the first spelling throughout and buys the uniformity with two definitions: `moduleSections`,
which supplies the action, and `res`, whose result type is the fixed spelling. Without `res` the
restriction of a section carries the wrapper, and neither `a • res h u` nor `res h u + res h u'`
elaborates.

**2. The germ API does not rewrite against `L.val.presheaf`.** `TopCat.Presheaf.germ_res_apply`
is stated for an `F : X.Presheaf C`, while `L.val.presheaf` has type
`(Opens X)ᵒᵖ ⥤ Ab` with no `TopCat.Presheaf` head, so `rw` will not instantiate `F` by keyed
matching -- the rewrite fails with "did not find an occurrence" even where the two terms are
identical. Every germ step below therefore either supplies `F` and the remaining arguments
explicitly (`germ_res`, which is the one such restatement, used everywhere after) or states the
needed equation in a local hypothesis and rewrites with that.

**3. `map_smul` must go through `toLinearMap`.** A `Stacks.SheafDescent.Trivialization` carries
its isomorphisms as `LinearEquiv`s whose scalars are spelled `structureRingPresheaf`. Writing
`map_smul (τ.θ W h) a u` fails, in either direction; `(τ.θ W h).toLinearMap.map_smul a u` works,
the explicit `LinearMap` pinning the scalar ring before the instances are sought. This is the
sibling file's gotcha and it is unchanged here.

**4. The sub-open proof must be the one in the goal.** Morphisms of `Opens X` are
proof-carrying, so `triv_res` and `res_res` take the composite morphism as an explicit argument
rather than forming it, letting each use site supply the morphism occurring in its goal; the
proofs are accepted by proof irrelevance.

**5. The sheaf conditions are restated.** `X.sheaf.obj` and `X.presheaf` are definitionally
equal and not syntactically equal, so a goal produced by Mathlib's gluing API is spelled in the
first and the lemmas of this file in the second. The three wrappers in the `SheafCondition`
section state the sheaf conditions at this file's spelling and are proved by handing the
Mathlib lemma the arguments, the definitional check happening once, at application.

No compiler option is set, no attribute is made locally reducible, and the two instances
introduced (`moduleSections`, `stalkModule`) are `scoped`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## What is not done

* **The inverse-section clause of Tag 01CY is not proved here**, and nothing here is stated about
  tensor powers: the file does not import them. It is proved elsewhere, as
  `Stacks.InverseSection.exists_tensorInv_section_pairing_eq_one`
  (`../InverseSection/Basic.lean`) and `Stacks.SheafOfModules.exists_tensorPairing_eq_one`
  (`../../Algebra/Category/ModuleCat/Sheaf/InvertibleTrivialization.lean`), both of which carry
  the `"inverse section"` label. What was missing at the time of writing is mathematical, not a
  spelling question. The clause asserts that `1` is the value of the canonical pairing on a pure
  tensor whose first factor is `s`, and the canonical pairing is
  `AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf` at degrees `1` and `-1`, an
  isomorphism built from a chosen tensor inverse by a recursion over `ℤ` whose action on
  sections is not computed anywhere. The available route does not need to compute it: a section
  of the sheafified tensor product mapping to `1` exists because the pairing is an isomorphism,
  it is locally the image of a finite sum of pure tensors because the sheafification unit is
  locally surjective, each first factor is a multiple of `s` on a small enough open by
  `bijective_smul` transported along
  `AlgebraicGeometry.SheafOfModules.tensorPowOneIso`, and the resulting local inverse sections
  glue because pairing against `s` is injective. Three ingredients of that are absent from this
  repository: the sections of the presheaf tensor product are nowhere identified with the tensor
  product of the sections, local surjectivity of
    `Stacks.SheafOfModules.TensorSheafification.toSheafify` is nowhere recorded at
  the sheaf-of-modules spelling, and `tensorPowOneIso` has no sectionwise description.
* **Only two of the three labels of Tag 01CY are attached here**: `"openness"`, on
  `isOpen_nonvanishingLocus`, and `"trivialization"`, on `isIso_over_nonvanishingOpen`. The
  openness clause is also carried by `Stacks.NonvanishingOpen.isOpen_nonvanishingLocus` at the
  scheme spelling; the two are the same claim at two spellings, not two independent assertions.
* The two vocabularies -- this file's and the scheme-level one of
  `StacksFrontier/AlgebraicGeometry/NonvanishingOpen/Basic.lean` -- are **not** bridged here, but
  they are bridged, in `../NonvanishingSpelling/Basic.lean`:
  `Stacks.NonvanishingSpelling.sectionsEquiv` on the carrier and
  `Stacks.NonvanishingSpelling.nonvanishingOpen_eq` on the open show that the nonvanishing locus
  of a scheme, computed with `Stacks.Ample.IsInvertibleModule` and
  `Stacks.ModuleStalk.maximalSmul`, is the one computed here for `X.toRingedSpace`. The two
  definitions also agree by inspection, and nothing in this file states the comparison, the
  module-sheaf wrappers differing (`X.Modules` against
  `SheafOfModules (structureSheaf X.sheaf)`).
* Nothing is proved for `AlgebraicGeometry.LocallyRingedSpace`: the hypothesis is the explicit
  one that every stalk of the structure sheaf is a local ring.
* No consequence of the trivialization is drawn. In particular nothing is said about ampleness
  (Stacks Tag 01PS), about the graded ring of sections (Stacks Tag 01CV), or about the
  restriction of `L` to `X_s` being isomorphic to the structure sheaf as a bare statement of
  triviality, which is the Stacks Tag 01CS form of what is proved here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorSheafification
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace Stacks.NonvanishingTrivialize

/-! ### Sections and stalks of a module on a ringed space -/

section Stalk

variable (X : RingedSpace.{u}) (L : SheafOfModules.{u} (structureSheaf X.sheaf))

/-- The module structure of the sections of a sheaf of modules on a ringed space over the
sections of the structure sheaf, at the spelling `X.presheaf.obj (op U)` of the latter. This is
the ringed-space analogue of Mathlib's `Module Γ(X, U) Γ(M, U)` for a scheme. -/
noncomputable scoped instance moduleSections
    (P : PresheafOfModules.{u} (structureSheaf X.sheaf).obj) (U : Opens X) :
    Module (X.presheaf.obj (op U)) (P.obj (op U)) := (P.obj (op U)).isModule

/-- The `𝒪_{X,x}`-module structure on the stalk at `x` of the abelian presheaf underlying a
sheaf of modules on a ringed space. This is Mathlib's stalk-module instance, with the base
presheaf written as `X.presheaf`; it is the instance the statement of Stacks Tag 01CY names. -/
noncomputable scoped instance stalkModule (x : X) :
    Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) L.val x

variable {X L}

/-- Restriction of a section of a sheaf of modules to a smaller open, with the target spelled
`L.val.obj (op W')` rather than the restricted-scalars wrapper that `PresheafOfModules.map`
produces. Only at this spelling do the scalar action and the germ API apply to a restricted
section without a transparency relaxation. -/
noncomputable def res {W W' : Opens X} (h : W' ⟶ W) (u : L.val.obj (op W)) : L.val.obj (op W') :=
  L.val.presheaf.map h.op u

/-- The germ of a restricted section is the germ of the section. -/
theorem germ_res {W W' : Opens X} (h : W' ⟶ W) (y : X) (hy : y ∈ W') (u : L.val.obj (op W)) :
    TopCat.Presheaf.germ L.val.presheaf W' y hy (res h u) =
      TopCat.Presheaf.germ L.val.presheaf W y (h.le hy) u :=
  TopCat.Presheaf.germ_res_apply L.val.presheaf h y hy u

/-- Restricting a global section of a sheaf of modules gives its value on the smaller open. -/
theorem res_eval (s : L.sections) {W W' : Opens X} (h : W' ⟶ W) :
    res h (s.eval (op W)) = s.eval (op W') :=
  s.property h.op

/-- Restriction is semilinear: restricting a scalar multiple multiplies by the restricted
scalar. -/
theorem res_smul {W W' : Opens X} (h : W' ⟶ W) (a : X.presheaf.obj (op W))
    (u : L.val.obj (op W)) : res h (a • u) = X.presheaf.map h.op a • res h u :=
  L.val.map_smul h.op a u

/-- Restricting a scalar multiple of a global section. -/
theorem res_smul_eval (s : L.sections) {W W' : Opens X} (h : W' ⟶ W)
    (a : X.presheaf.obj (op W)) :
    res h (a • s.eval (op W)) = X.presheaf.map h.op a • s.eval (op W') := by
  rw [res_smul, res_eval]

/-- The germ of a scalar multiple of a section is the scalar multiple of the germs. -/
theorem germ_smul (x : X) (U : Opens X) (hx : x ∈ U) (a : X.presheaf.obj (op U))
    (m : L.val.obj (op U)) :
    TopCat.Presheaf.germ L.val.presheaf U x hx (a • m) =
      X.presheaf.germ U x hx a • TopCat.Presheaf.germ L.val.presheaf U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) L.val x U hx a m

variable (X L)

/-- The submodule `𝔪_x · M_x` of the stalk at `x`, written out as the statement of Stacks
Tag 01CY writes it. -/
noncomputable def maximalSmul [∀ x : X, IsLocalRing (X.presheaf.stalk x)] (x : X) :
    Submodule (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x) :=
  IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤

variable {X L}

/-- `r • m` lies in `𝔪_x · M_x` precisely when `r` is a non-unit or `m` already lies there. -/
theorem smul_mem_maximalSmul_iff [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    {x : X} (r : X.presheaf.stalk x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x) :
    r • m ∈ maximalSmul X L x ↔ ¬ IsUnit r ∨ m ∈ maximalSmul X L x := by
  constructor
  · intro h
    by_cases hr : IsUnit r
    · exact Or.inr ((Submodule.smul_mem_iff_of_isUnit _ hr).mp h)
    · exact Or.inl hr
  · rintro (hr | hm)
    · exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal r).mpr hr) Submodule.mem_top
    · exact Submodule.smul_mem _ _ hm

end Stalk

/-! ### The sheaf conditions, at this file's spellings -/

section SheafCondition

variable {X : RingedSpace.{u}} {L : SheafOfModules.{u} (structureSheaf X.sheaf)}

/-- Restriction in two steps is restriction. -/
theorem res_res {W W' W'' : Opens X} (h : W' ⟶ W) (h' : W'' ⟶ W') (h'' : W'' ⟶ W)
    (u : L.val.obj (op W)) : res h' (res h u) = res h'' u := by
  change L.val.presheaf.map h'.op (L.val.presheaf.map h.op u) = L.val.presheaf.map h''.op u
  have e : L.val.presheaf.map h.op ≫ L.val.presheaf.map h'.op = L.val.presheaf.map h''.op :=
    (L.val.presheaf.map_comp h.op h'.op).symm
  exact (ConcreteCategory.comp_apply (L.val.presheaf.map h.op)
    (L.val.presheaf.map h'.op) u).symm.trans (ConcreteCategory.congr_hom e u)

/-- A section of the structure sheaf restricts to a unit on any open inside its basic open. -/
theorem isUnit_res_of_le_basicOpen {U W : Opens X} (f : X.presheaf.obj (op U)) (h : W ⟶ U)
    (hW : W ≤ X.basicOpen f) : IsUnit (X.presheaf.map h.op f) := by
  refine X.isUnit_of_isUnit_germ W _ fun x hx => ?_
  rw [TopCat.Presheaf.germ_res_apply]
  exact (X.mem_basicOpen f x (h.le hx)).mp (hW hx)

/-- Separatedness of the structure sheaf: two sections agreeing on a cover are equal. -/
theorem eq_of_res_eq_ring {ι : Type u} (C : ι → Opens X) (W : Opens X) (iCW : ∀ i, C i ⟶ W)
    (hcover : W ≤ iSup C) (a b : X.presheaf.obj (op W))
    (h : ∀ i, X.presheaf.map (iCW i).op a = X.presheaf.map (iCW i).op b) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq' X.sheaf C W iCW hcover a b h

/-- Separatedness of a sheaf of modules: two sections agreeing on a cover are equal. -/
theorem eq_of_res_eq {ι : Type u} (C : ι → Opens X) (W : Opens X) (iCW : ∀ i, C i ⟶ W)
    (hcover : W ≤ iSup C) (m m' : L.val.obj (op W))
    (h : ∀ i, res (iCW i) m = res (iCW i) m') : m = m' :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨L.val.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab.{u} _) C W iCW
    hcover m m' h

/-- The sheaf condition of the structure sheaf: a compatible family of sections on a cover
glues. -/
theorem exists_res_eq_ring {ι : Type u} (C : ι → Opens X) (W : Opens X) (iCW : ∀ i, C i ⟶ W)
    (hcover : W ≤ iSup C) (a : ∀ i, X.presheaf.obj (op (C i)))
    (hcompat : ∀ i j, X.presheaf.map (homOfLE (inf_le_left : C i ⊓ C j ≤ C i)).op (a i) =
      X.presheaf.map (homOfLE (inf_le_right : C i ⊓ C j ≤ C j)).op (a j)) :
    ∃ A : X.presheaf.obj (op W), ∀ i, X.presheaf.map (iCW i).op A = a i :=
  (TopCat.Sheaf.existsUnique_gluing' X.sheaf C W iCW hcover a hcompat).exists

end SheafCondition

/-! ### The trivializing map, at the ringed-space section spellings -/

section Triv

variable {X : RingedSpace.{u}} {L : SheafOfModules.{u} (structureSheaf X.sheaf)} {V : Opens X}
  (τ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)

/-- The trivializing map of a sectionwise trivialization over `V`, written at the spellings
`L.val.obj (op W)` and `X.presheaf.obj (op W)` of the sections rather than at the
`structureRingPresheaf` spelling the structure carries. -/
noncomputable def triv {W : Opens X} (h : W ⟶ V) (u : L.val.obj (op W)) :
    X.presheaf.obj (op W) := τ.θ W h u

/-- The trivializing map is injective. -/
theorem triv_injective {W : Opens X} (h : W ⟶ V) : Function.Injective (triv τ h) :=
  (τ.θ W h).injective

/-- The trivializing map commutes with restriction. The morphism `W' ⟶ V` is an explicit
argument, not the composite `h' ≫ h`, so that a use site can supply the one in its goal. -/
theorem triv_res {W W' : Opens X} (h : W ⟶ V) (h' : W' ⟶ W) (h'' : W' ⟶ V)
    (u : L.val.obj (op W)) :
    triv τ h'' (res h' u) = X.presheaf.map h'.op (triv τ h u) :=
  τ.θ_naturality h h' u

/-- The trivializing map is additive. -/
theorem triv_add {W : Opens X} (h : W ⟶ V) (u u' : L.val.obj (op W)) :
    triv τ h (u + u') = triv τ h u + triv τ h u' :=
  (τ.θ W h).toLinearMap.map_add u u'

/-- The trivializing map is linear over the sections of the structure sheaf. -/
theorem triv_smul {W : Opens X} (h : W ⟶ V) (a : X.presheaf.obj (op W))
    (u : L.val.obj (op W)) : triv τ h (a • u) = a * triv τ h u :=
  (τ.θ W h).toLinearMap.map_smul a u

/-- The local basis section: the section of `L` over `V` that the trivialization sends to `1`. -/
noncomputable def basis : L.val.obj (op V) := τ.basis

/-- The trivializing map sends the basis section to `1`. -/
theorem triv_basis : triv τ (𝟙 V) (basis τ) = 1 := τ.θ_basis

/-- The trivializing map sends every restriction of the basis section to `1`. -/
theorem triv_res_basis {W : Opens X} (h : W ⟶ V) : triv τ h (res h (basis τ)) = 1 :=
  τ.θ_basisAt h

/-- Every section of `L` over `V` is its trivializing function times the basis section. -/
theorem eq_triv_smul_basis (u : L.val.obj (op V)) : u = triv τ (𝟙 V) u • basis τ :=
  triv_injective τ (𝟙 V) (by rw [triv_smul, triv_basis, mul_one])

end Triv

/-! ### The nonvanishing locus -/

section Locus

variable (X : RingedSpace.{u}) (L : SheafOfModules.{u} (structureSheaf X.sheaf))
  [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- **The nonvanishing locus of Stacks Tag 01CY**: the points at which the germ of a global
section of a module on a ringed space generates its stalk modulo the maximal ideal. -/
noncomputable def nonvanishingLocus (s : L.sections) : Set X :=
  {x | (TopCat.Presheaf.Γgerm L.val.presheaf x).hom (s.eval (op ⊤)) ∉ maximalSmul X L x}

/-- A point `x` lies in the nonvanishing locus of `s` if and only if the germ of `s` at `x` does
not lie in `maximalSmul X L x`. -/
theorem mem_nonvanishingLocus_iff (s : L.sections) (x : X) :
    x ∈ nonvanishingLocus X L s ↔
      TopCat.Presheaf.Γgerm L.val.presheaf x (s.eval (op ⊤)) ∉ maximalSmul X L x :=
  Iff.rfl

variable {X L} {V : Opens X}
  (τ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)

/-- The predicate behind `Stacks.NonvanishingTrivialize.notMem_maximalSmul_germ_basis`: a stalk
element at `y` is the germ of a section, on some open inside `V`, whose trivializing function
has germ in the maximal ideal of `𝒪_{X,y}`. -/
def TrivGermMem (y : X) (m : TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y) : Prop :=
  ∃ (W : Opens X) (hyW : y ∈ W) (h : W ⟶ V) (u : L.val.obj (op W)),
    TopCat.Presheaf.germ L.val.presheaf W y hyW u = m ∧
      X.presheaf.germ W y hyW (triv τ h u) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)

/-- Two sections witnessing the predicate are restricted to the intersection of their opens and
added there. -/
theorem trivGermMem_add {y : X} {m m' : TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y}
    (hm : TrivGermMem τ y m) (hm' : TrivGermMem τ y m') : TrivGermMem τ y (m + m') := by
  obtain ⟨W, hyW, h, u, hu, hmem⟩ := hm
  obtain ⟨W', hyW', h', u', hu', hmem'⟩ := hm'
  have hiW : W ⊓ W' ⟶ W := homOfLE inf_le_left
  have hiW' : W ⊓ W' ⟶ W' := homOfLE inf_le_right
  have hyI : y ∈ W ⊓ W' := ⟨hyW, hyW'⟩
  refine ⟨W ⊓ W', hyI, hiW ≫ h, res hiW u + res hiW' u', ?_, ?_⟩
  · have hadd : TopCat.Presheaf.germ L.val.presheaf (W ⊓ W') y hyI (res hiW u + res hiW' u') =
        TopCat.Presheaf.germ L.val.presheaf (W ⊓ W') y hyI (res hiW u) +
          TopCat.Presheaf.germ L.val.presheaf (W ⊓ W') y hyI (res hiW' u') :=
      map_add _ _ _
    rw [hadd, germ_res, germ_res, hu, hu']
  · have e : triv τ (hiW ≫ h) (res hiW u + res hiW' u') =
        X.presheaf.map hiW.op (triv τ h u) + X.presheaf.map hiW'.op (triv τ h' u') := by
      rw [triv_add, triv_res τ h hiW (hiW ≫ h) u, triv_res τ h' hiW' (hiW ≫ h) u']
    rw [e, map_add, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact add_mem hmem hmem'

/-- A multiple of an arbitrary stalk element by an element of the maximal ideal witnesses the
predicate: represent both on a common open inside `V` and use linearity of the trivializing
map. -/
theorem trivGermMem_smul {y : X} (hy : y ∈ V) {r : X.presheaf.stalk y}
    (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y) : TrivGermMem τ y (r • m) := by
  obtain ⟨W, hWV, hyW, u, hu⟩ := TopCat.Presheaf.exists_le_germ_eq L.val.presheaf m hy
  obtain ⟨W', hW'W, hyW', a, ha⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf r hyW
  have hiW' : W' ⟶ W := homOfLE hW'W
  refine ⟨W', hyW', hiW' ≫ homOfLE hWV, a • res hiW' u, ?_, ?_⟩
  · rw [germ_smul, germ_res hiW' y hyW' u, ha, hu]
  · rw [triv_smul, map_mul, ha]
    exact Ideal.mul_mem_right _ _ hr

/-- **The basis section of a sectionwise trivialization vanishes at no point of the trivializing
open**: its germ at `y` avoids `𝔪_y · M_y`. This is the local-freeness input to Stacks Tag 01CY,
and the only step of its proof that is not formal. -/
theorem notMem_maximalSmul_germ_basis {y : X} (hy : y ∈ V) :
    TopCat.Presheaf.germ L.val.presheaf V y hy (basis τ) ∉ maximalSmul X L y := by
  intro hmem
  have hmem' : TopCat.Presheaf.germ L.val.presheaf V y hy (basis τ) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) •
        (⊤ : Submodule (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf y)) := hmem
  obtain ⟨W, hyW, h, u, hu, hmaxl⟩ :=
    Submodule.smul_induction_on (p := TrivGermMem τ y) hmem'
      (fun _ hr m _ => trivGermMem_smul τ hy hr m)
      fun _ _ hm hm' => trivGermMem_add τ hm hm'
  obtain ⟨W', hyW', iW, iV, heq⟩ :=
    TopCat.Presheaf.germ_eq L.val.presheaf y hyW hy u (basis τ) hu
  have h3 : X.presheaf.map iW.op (triv τ h u) = 1 := by
    rw [← triv_res τ h iW (iW ≫ h) u, show res iW u = res iV (basis τ) from heq]
    exact triv_res_basis τ iV
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf iW y hyW', h3, map_one] at hmaxl
  exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one hmaxl

/-- The trivializing function of a global section over the trivializing open `V`. -/
noncomputable def trivEval (s : L.sections) : X.presheaf.obj (op V) :=
  triv τ (𝟙 V) (s.eval (op V))

omit [∀ x : X, IsLocalRing (X.presheaf.stalk x)] in
/-- The trivializing function of a global section restricts to the trivializing function of the
section over a smaller open. -/
theorem res_trivEval (s : L.sections) {W : Opens X} (h : W ⟶ V) :
    X.presheaf.map h.op (trivEval τ s) = triv τ h (s.eval (op W)) := by
  rw [trivEval, ← triv_res τ (𝟙 V) h h (s.eval (op V)), res_eval]

/-- **On a trivializing open, a section fails to vanish exactly where its trivializing function
is a unit.** -/
theorem mem_nonvanishingLocus_iff_isUnit (s : L.sections) {y : X} (hy : y ∈ V) :
    y ∈ nonvanishingLocus X L s ↔ IsUnit (X.presheaf.germ V y hy (trivEval τ s)) := by
  have hsV : s.eval (op V) = trivEval τ s • basis τ := eq_triv_smul_basis τ _
  have hres : L.val.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (s.eval (op ⊤)) = s.eval (op V) :=
    res_eval s (homOfLE (le_top : V ≤ ⊤))
  have hg : TopCat.Presheaf.Γgerm L.val.presheaf y (s.eval (op ⊤)) =
      X.presheaf.germ V y hy (trivEval τ s) •
        TopCat.Presheaf.germ L.val.presheaf V y hy (basis τ) := by
    rw [← TopCat.Presheaf.Γgerm_res_apply (i := homOfLE (le_top : V ≤ ⊤)) L.val.presheaf y hy
      (s.eval (op ⊤)), hres, hsV, germ_smul]
  rw [mem_nonvanishingLocus_iff, hg, smul_mem_maximalSmul_iff, not_or, not_not]
  exact and_iff_left (notMem_maximalSmul_germ_basis τ hy)

/-- **On a trivializing open, the nonvanishing locus is a basic open.** -/
theorem nonvanishingLocus_inter (s : L.sections) :
    nonvanishingLocus X L s ∩ (V : Set X) = (X.basicOpen (trivEval τ s) : Set X) := by
  ext y
  constructor
  · rintro ⟨hys, hyV⟩
    exact (X.mem_basicOpen _ y hyV).mpr ((mem_nonvanishingLocus_iff_isUnit τ s hyV).mp hys)
  · intro hy
    have hyV : y ∈ V := X.basicOpen_le _ hy
    exact ⟨(mem_nonvanishingLocus_iff_isUnit τ s hyV).mpr ((X.mem_basicOpen _ y hyV).mp hy), hyV⟩

end Locus

/-! ### Openness of the nonvanishing locus -/

section Openness

variable (X : RingedSpace.{u}) (L : SheafOfModules.{u} (structureSheaf X.sheaf))
  [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
  [IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L]

/-- Clause 2 of Stacks Tag 0B8M, at the spelling of the statement of Stacks Tag 01CY: an
invertible module on a ringed space with local stalks is sectionwise trivial on an open cover. -/
theorem exists_cover_trivialization :
    ∃ V : X → Opens X, iSup V = ⊤ ∧
      ∀ x : X, Nonempty (Stacks.SheafDescent.Trivialization X.presheaf L.val (V x)) := by
  have h' : IsInvertible X.presheaf (structureSheaf X.sheaf).property L := ‹_›
  exact Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X) (structureSheaf X.sheaf).property L

/-- Every point of the nonvanishing locus lies in the basic open of the trivializing function of
the section, for some sectionwise trivialization over some open. -/
private theorem exists_trivialization_mem_basicOpen (s : L.sections) {y : X}
    (hy : y ∈ nonvanishingLocus X L s) :
    ∃ (V : Opens X) (τ : Stacks.SheafDescent.Trivialization X.presheaf L.val V),
      y ∈ X.basicOpen (trivEval τ s) := by
  obtain ⟨V, hV, htriv⟩ := exists_cover_trivialization X L
  obtain ⟨z, hz⟩ : ∃ z : X, y ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top y)
  obtain ⟨τ⟩ := htriv z
  exact ⟨V z, τ, (X.mem_basicOpen _ y hz).mpr ((mem_nonvanishingLocus_iff_isUnit τ s hz).mp hy)⟩

/-- **Stacks Tag 01CY, openness**, at the ringed-space spelling of the tagged statement: the
nonvanishing locus of a global section of an invertible module on a ringed space with local
stalks is open. -/
@[ega "0 5.5.2" "openness of X_f"]
theorem isOpen_nonvanishingLocus (s : L.sections) : IsOpen (nonvanishingLocus X L s) := by
  refine isOpen_iff_forall_mem_open.mpr fun y hy => ?_
  obtain ⟨V, τ, hyB⟩ := exists_trivialization_mem_basicOpen X L s hy
  exact ⟨_, (nonvanishingLocus_inter τ s).symm.subset.trans Set.inter_subset_left,
    (X.basicOpen _).2, hyB⟩

/-- **The nonvanishing open of Stacks Tag 01CY**: the nonvanishing locus of a global section of
an invertible module, bundled as an open subset by the openness theorem. -/
noncomputable def nonvanishingOpen (s : L.sections) : Opens X :=
  ⟨nonvanishingLocus X L s, isOpen_nonvanishingLocus X L s⟩

/-- The underlying set of the nonvanishing open is the nonvanishing locus. -/
@[simp] theorem coe_nonvanishingOpen (s : L.sections) :
    (nonvanishingOpen X L s : Set X) = nonvanishingLocus X L s := rfl

/-- A point lies in the nonvanishing open if and only if it lies in the nonvanishing locus. -/
theorem mem_nonvanishingOpen (s : L.sections) (y : X) :
    y ∈ nonvanishingOpen X L s ↔ y ∈ nonvanishingLocus X L s := Iff.rfl

end Openness

/-! ### Multiplication by a nonvanishing section is bijective -/

section Bijective

variable {X : RingedSpace.{u}} {L : SheafOfModules.{u} (structureSheaf X.sheaf)}
  [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

omit [∀ x : X, IsLocalRing (X.presheaf.stalk x)] in
/-- Over an open on which the trivializing function of `s` is a unit, multiplication by `s` is a
bijection from the sections of the structure sheaf to those of the module: read through the
trivialization it is multiplication by a unit. -/
theorem bijective_smul_of_isUnit {V : Opens X}
    (τ : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (s : L.sections)
    {W : Opens X} (h : W ⟶ V) (hu : IsUnit (triv τ h (s.eval (op W)))) :
    Function.Bijective fun a : X.presheaf.obj (op W) => a • s.eval (op W) := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨fun a b hab => (Units.mul_left_inj v).mp ?_,
    fun l => ⟨triv τ h l * (↑v⁻¹ : X.presheaf.obj (op W)), triv_injective τ h ?_⟩⟩
  · rw [hv, ← triv_smul, ← triv_smul]
    exact congrArg (triv τ h) hab
  · rw [triv_smul, ← hv, mul_assoc, Units.inv_mul, mul_one]

omit [∀ x : X, IsLocalRing (X.presheaf.stalk x)] in
/-- Multiplication by `s` is injective on the sections over `W` if it is so over each member of a
cover of `W`, by separatedness of the structure sheaf. -/
theorem injective_smul_of_cover {ι : Type u} (s : L.sections) (C : ι → Opens X) (W : Opens X)
    (iCW : ∀ i, C i ⟶ W) (hcover : W ≤ iSup C)
    (hC : ∀ i, Function.Injective fun a : X.presheaf.obj (op (C i)) => a • s.eval (op (C i))) :
    Function.Injective fun a : X.presheaf.obj (op W) => a • s.eval (op W) := by
  intro a b hab
  refine eq_of_res_eq_ring C W iCW hcover a b fun i => hC i ?_
  change X.presheaf.map (iCW i).op a • s.eval (op (C i)) =
    X.presheaf.map (iCW i).op b • s.eval (op (C i))
  rw [← res_smul_eval s (iCW i) a, ← res_smul_eval s (iCW i) b]
  exact congrArg (res (iCW i)) hab

omit [∀ x : X, IsLocalRing (X.presheaf.stalk x)] in
/-- Multiplication by `s` is surjective on the sections over `W` if it is bijective over every
open inside a member of a cover of `W`: the local preimages glue by the sheaf condition. -/
theorem surjective_smul_of_cover {ι : Type u} (s : L.sections) (C : ι → Opens X) (W : Opens X)
    (iCW : ∀ i, C i ⟶ W) (hcover : W ≤ iSup C)
    (hC : ∀ i (W' : Opens X), W' ≤ C i →
      Function.Bijective fun a : X.presheaf.obj (op W') => a • s.eval (op W')) :
    Function.Surjective fun a : X.presheaf.obj (op W) => a • s.eval (op W) := by
  intro l
  choose a ha using fun i => (hC i (C i) le_rfl).2 (res (iCW i) l)
  have ha' : ∀ i, a i • s.eval (op (C i)) = res (iCW i) l := ha
  have hcompat : ∀ i j,
      X.presheaf.map (homOfLE (inf_le_left : C i ⊓ C j ≤ C i)).op (a i) =
        X.presheaf.map (homOfLE (inf_le_right : C i ⊓ C j ≤ C j)).op (a j) := by
    intro i j
    have hiW : C i ⊓ C j ⟶ W := homOfLE ((inf_le_left : C i ⊓ C j ≤ C i).trans (leOfHom (iCW i)))
    refine (hC i (C i ⊓ C j) inf_le_left).1 ?_
    change X.presheaf.map (homOfLE (inf_le_left : C i ⊓ C j ≤ C i)).op (a i) •
        s.eval (op (C i ⊓ C j)) =
      X.presheaf.map (homOfLE (inf_le_right : C i ⊓ C j ≤ C j)).op (a j) •
        s.eval (op (C i ⊓ C j))
    rw [← res_smul_eval s (homOfLE (inf_le_left : C i ⊓ C j ≤ C i)) (a i),
      ← res_smul_eval s (homOfLE (inf_le_right : C i ⊓ C j ≤ C j)) (a j), ha' i, ha' j,
      res_res (iCW i) (homOfLE (inf_le_left : C i ⊓ C j ≤ C i)) hiW l,
      res_res (iCW j) (homOfLE (inf_le_right : C i ⊓ C j ≤ C j)) hiW l]
  obtain ⟨A, hA⟩ := exists_res_eq_ring C W iCW hcover a hcompat
  refine ⟨A, eq_of_res_eq C W iCW hcover _ l fun i => ?_⟩
  change res (iCW i) (A • s.eval (op W)) = res (iCW i) l
  rw [res_smul_eval, hA i, ha' i]

variable [IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L]

/-- Around every point of the nonvanishing locus there is an open neighbourhood such that over
every open inside it multiplication by `s` is bijective on sections: the basic open of the
trivializing function of `s` on a trivializing open of the cover of clause 2 of Stacks
Tag 0B8M. -/
theorem exists_nhd_bijective_smul (s : L.sections) {y : X} (hy : y ∈ nonvanishingLocus X L s) :
    ∃ G : Opens X, y ∈ G ∧ ∀ W' : Opens X, W' ≤ G →
      Function.Bijective fun a : X.presheaf.obj (op W') => a • s.eval (op W') := by
  obtain ⟨V, τ, hyB⟩ := exists_trivialization_mem_basicOpen X L s hy
  refine ⟨X.basicOpen (trivEval τ s), hyB, fun W' hW' => ?_⟩
  have hle : W' ≤ V := hW'.trans (X.basicOpen_le _)
  refine bijective_smul_of_isUnit τ s (homOfLE hle) ?_
  rw [← res_trivEval τ s (homOfLE hle)]
  exact isUnit_res_of_le_basicOpen (trivEval τ s) (homOfLE hle) hW'

/-- **Multiplication by a global section is bijective on the sections over every open inside its
nonvanishing locus.** Bijectivity is local by `exists_nhd_bijective_smul`; injectivity glues by
separatedness of the structure sheaf and surjectivity by its sheaf condition, the local inverses
agreeing on overlaps because multiplication by `s` is injective there, and the glued section
multiplies to the given one because the module is separated. -/
theorem bijective_smul (s : L.sections) {W : Opens X}
    (hW : W ≤ nonvanishingOpen X L s) :
    Function.Bijective fun a : X.presheaf.obj (op W) => a • s.eval (op W) := by
  choose G hyG hGbij using fun y : W => exists_nhd_bijective_smul s (hW y.2)
  let C : W → Opens X := fun y => W ⊓ G y
  have hCle : ∀ y : W, C y ⟶ W := fun _ => homOfLE inf_le_left
  have hcover : W ≤ iSup C := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hyG ⟨x, hx⟩⟩
  have hCbij : ∀ (y : W) (W' : Opens X), W' ≤ C y →
      Function.Bijective fun a : X.presheaf.obj (op W') => a • s.eval (op W') :=
    fun y W' h => hGbij y W' (h.trans inf_le_right)
  exact ⟨injective_smul_of_cover s C W hCle hcover fun y => (hCbij y _ le_rfl).1,
    surjective_smul_of_cover s C W hCle hcover hCbij⟩

end Bijective

/-! ### Multiplication by a section -/

section Multiplication

variable {X : RingedSpace.{u}} {L : SheafOfModules.{u} (structureSheaf X.sheaf)}

/-- **The morphism of modules determined by a global section is multiplication by it.** The
morphism is the one the statement of Stacks Tag 01CY applies the inverse of
`SheafOfModules.unitHomEquiv` to, and on sections over `W` it sends `a` to `a • s`. -/
theorem unitHomEquiv_symm_app (s : L.sections) (W : Opens X) (a : X.presheaf.obj (op W)) :
    (L.unitHomEquiv.symm s).val.app (op W) a = a • s.eval (op W) := by
  have h1 : s.eval (op W) = (L.unitHomEquiv.symm s).val.app (op W)
      (1 : X.presheaf.obj (op W)) := by
    conv_lhs => rw [← L.unitHomEquiv.apply_symm_apply s]
    exact SheafOfModules.unitHomEquiv_apply_coe L _ (op W)
  have h2 : ((L.unitHomEquiv.symm s).val.app (op W)).hom
      (a • (1 : X.presheaf.obj (op W))) =
      a • ((L.unitHomEquiv.symm s).val.app (op W)).hom (1 : X.presheaf.obj (op W)) :=
    map_smul _ a _
  rw [h1, ← h2, smul_eq_mul, mul_one]

end Multiplication

/-! ### The trivialization on the nonvanishing open -/

section Trivialization

variable {X : RingedSpace.{u}} {L : SheafOfModules.{u} (structureSheaf X.sheaf)}

/-- A component of a morphism of sheaves of modules on a ringed space is an isomorphism of
abelian groups as soon as it is bijective on sections. -/
theorem isIso_toPresheaf_app_of_bijective {M N : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (φ : M ⟶ N) (W : Opens X)
    (h : Function.Bijective fun m : M.val.obj (op W) => φ.val.app (op W) m) :
    IsIso (((PresheafOfModules.toPresheaf (structureSheaf X.sheaf).obj).map
      ((SheafOfModules.forget (structureSheaf X.sheaf)).map φ)).app (op W)) := by
  rwa [← isIso_iff_of_reflects_iso _ (forget Ab.{u}), isIso_iff_bijective]

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
  [IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L]

/-- **Stacks Tag 01CY, the trivialization, in the form of an arbitrary open inside the
nonvanishing locus.** On every open inside the nonvanishing locus of `s`, the morphism of modules
determined by `s` restricts to an isomorphism from the structure sheaf. The component at an open
`W` of the slice site is the component at `W` of the original morphism, which is multiplication
by `s` and bijective by `bijective_smul`; isomorphy is then reflected from presheaves of abelian
groups through `PresheafOfModules.toPresheaf` and `SheafOfModules.forget`. -/
theorem isIso_over_of_le (s : L.sections) {U : Opens X} (hU : U ≤ nonvanishingOpen X L s) :
    IsIso ((L.unitHomEquiv.symm s).over U) := by
  have happ : ∀ Y : (Over U)ᵒᵖ, IsIso (((PresheafOfModules.toPresheaf
      ((structureSheaf X.sheaf).over U).obj).map ((SheafOfModules.forget
        ((structureSheaf X.sheaf).over U)).map ((L.unitHomEquiv.symm s).over U))).app Y) := by
    intro Y
    change IsIso (((PresheafOfModules.toPresheaf (structureSheaf X.sheaf).obj).map
      ((SheafOfModules.forget (structureSheaf X.sheaf)).map (L.unitHomEquiv.symm s))).app
        (op (unop Y).left))
    refine isIso_toPresheaf_app_of_bijective _ _ ?_
    have hfun : (fun m : (SheafOfModules.unit (structureSheaf X.sheaf)).val.obj
        (op (unop Y).left) => (L.unitHomEquiv.symm s).val.app (op (unop Y).left) m) =
        fun a : X.presheaf.obj (op (unop Y).left) => a • s.eval (op (unop Y).left) :=
      funext fun a => unitHomEquiv_symm_app s (unop Y).left a
    rw [hfun]
    exact bijective_smul s ((leOfHom (unop Y).hom).trans hU)
  have h2 : IsIso ((PresheafOfModules.toPresheaf ((structureSheaf X.sheaf).over U).obj).map
      ((SheafOfModules.forget ((structureSheaf X.sheaf).over U)).map
        ((L.unitHomEquiv.symm s).over U))) := NatIso.isIso_of_isIso_app _
  have h3 : IsIso ((SheafOfModules.forget ((structureSheaf X.sheaf).over U)).map
      ((L.unitHomEquiv.symm s).over U)) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf ((structureSheaf X.sheaf).over U).obj)
  exact isIso_of_reflects_iso _ (SheafOfModules.forget ((structureSheaf X.sheaf).over U))

/-- **Stacks Tag 01CY, the trivialization.** Multiplication by a global section of an invertible
module on a ringed space with local stalks is an isomorphism from the structure sheaf on the
nonvanishing open of that section. -/
@[ega "0 5.5.4" "rank 1 case", ega "0 5.5.2" "(b) => (a)"]
instance isIso_over_nonvanishingOpen (s : L.sections) :
    IsIso ((L.unitHomEquiv.symm s).over (nonvanishingOpen X L s)) :=
  isIso_over_of_le s le_rfl

end Trivialization

end Stacks.NonvanishingTrivialize

end
