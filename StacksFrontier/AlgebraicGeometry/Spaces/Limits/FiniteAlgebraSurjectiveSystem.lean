module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SurjectiveFinitePresentationSystem

/-!
# A finite quasi-coherent algebra as a directed colimit with surjective transition maps

Let `S` be a scheme, let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and
let `𝒜` be a finite quasi-coherent `𝒪_Y`-algebra.  Stacks 086Z writes `𝒜 = colim 𝒜ᵢ` as a
*directed* colimit of quasi-coherent `𝒪_Y`-algebras which are *finite* and *of finite
presentation*, with *surjective* transition maps.  Four assertions, and this file proves all four
of them from the data the source's proof produces in its first steps — in particular it
*constructs* the system of those steps out of the quotients of an algebra sheaf by a sheaf of
ideals, so that the surjectivity of its transition maps is a theorem and not a hypothesis.

## Main results

* `Stacks.FiniteAlgebraSurjectiveSystem.exists_directed_of_filtered_colimit_hom`: a filtered
  colimit presentation with an essentially small index is a colimit over a nonempty directed
  preorder, preserving both a property of the objects of the diagram **and a property of its
  transition maps**.  Pure category theory.
* `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral.of_surjective_app`: integrality of an algebra
  sheaf passes to the target of a morphism which is surjective on the sections over the affine
  étale charts.
* `AlgebraicGeometry.Space.idealQuotientDiagram` and
  `AlgebraicGeometry.Space.idealQuotientQcohCocone`: **the system `p ↦ ℬ/ℐ_p` of quotients of one
  algebra sheaf by a family of sheaves of ideals growing along a filtered index, and its cocone
  over the target of a map killing every `ℐ_p`.**
* `AlgebraicGeometry.Space.isLocallySurjective_idealQuotientQcohDiagram_map`: **every transition
  map of that system is locally surjective.**
* `AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective`:
  **Stacks 086Z**, over the carried input described below.

## What is proved and what is carried

### No unrestricted `@[stacks 086Z]`

The attribute on the main theorem carries a clause, and this is what it says.

The source's proof has four steps.  Stacks 086Y gives a finitely presented quasi-coherent module
`ℱ` surjecting onto `𝒜`, which the algebra structure upgrades to a surjection
`Sym_{𝒪_Y}(ℱ) ↠ 𝒜`; Stacks 0829 writes the kernel ideal `𝒥` as the filtered colimit of its
finite type quasi-coherent submodules `ℰᵢ`; the quotients `𝒜ᵢ = Sym(ℱ)/(ℰᵢ)` are then a filtered
system of finitely presented quasi-coherent algebras with surjective transition maps and colimit
`𝒜`; and finally `𝒜ᵢ` is finite for `i` large.

Of that route this library has the two inputs and now part of the construction.  Stacks 086Y is
proved, as `AlgebraicGeometry.Space.exists_directed_isFinitePresentation_epi` in
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Main`, and Stacks 0829
as `AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject` together with
`AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9`.  Of the
passage from modules to algebras, the quotient of an algebra sheaf on an algebraic space by a
sheaf of ideals is now constructed, in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient`, together with its
universal property and the image factorization `𝒜 ⟶ 𝒜/ker f ⟶ 𝒞` of a morphism of algebra
sheaves, in `...AlgebraSheafIdealQuotientLift`.  So the *members and the transition maps* of the
system of the source's third step are no longer carried: they are built here, as
`AlgebraicGeometry.Space.idealQuotientDiagram` out of those quotients, and the surjectivity of
the transition maps — one of the four assertions of the tag — becomes a theorem about them.

What remains absent is what the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.IdealQuotientApproximationSystem` records as the
three carried inputs of Stacks 082A, and `hsource` is exactly those three plus the single-index
half of the fourth step.  **All three are now dischargeable from elementary data**, and none of
the three may be *substituted* for: in each case the elementary data is not among the remaining
conjuncts of `hsource`, so replacing a conjunct by it would make `hsource` stronger and this
theorem weaker.

* **the algebra sheaf `ℬ` and the map `ℬ ⟶ 𝒜`.**  In the source `ℬ = Sym_{𝒪_Y}(ℱ)` with the map
  induced by `ℱ ↠ 𝒜`.  Both halves of that construction now exist at the algebraic-space level:
  functoriality of the symmetric algebra is
  `AlgebraicGeometry.Space.symmetricAlgebraSheafMap` in
  `Spaces/SymmetricAlgebraSheafMap.lean`, and the *ungraded* universal property, producing a
  morphism of algebra sheaves `Sym(ℱ) ⟶ 𝒜` out of a morphism of modules `ℱ ⟶ 𝒜`, is
  `AlgebraicGeometry.Space.SymAlgSheaf.algebraLift` in
  `Spaces/SymmetricAlgebraSheafUngradedLift.lean`.  With Stacks 086Y, which is proved, one may
  therefore take `ℬ = Sym(ℱ)` and the map to be `algebraLift`.  Quasi-coherence of `Sym(ℱ)` is
  still unproved at this level, but `hsource` asks no quasi-coherence of `ℬ`, so it is not
  needed for this tag.
* **quasi-coherence and finite presentation of each quotient `ℬ/ℐ_j`.**  These are conditions on
  the sections of a *sheafification* over the affine étale charts, and what they need is the
  identification of those sections with the sections of the objectwise quotient.  **That
  identification is now proved**, in
  `StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientCokernel`.  The step that
  was missing was the identification of the underlying `𝒪_Y`-module of `ℬ/ℐ_j` with the
  **cokernel** of the inclusion of `ℐ_j`, and that is
  `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleIdealQuotientCokernelIso`: an epi-mono
  factorisation in the balanced category of `𝒪_Y`-modules, whose exactness input is
  `AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient` (the quotient morphism kills
  exactly the sections of the ideal) and whose epimorphism input is local surjectivity of
  `ℬ ⟶ ℬ/ℐ_j`.  With it:

  - quasi-coherence of `ℬ/ℐ_j` is
    `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_idealQuotient`, by
    `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`, **given
    quasi-coherence of `ℬ` and of `ℐ_j`**;
  - the sections of `ℬ/ℐ_j` over an affine étale chart `W` are `ℬ(W)/ℐ_j(W)`, by
    `AlgebraicGeometry.Space.AlgebraSheaf.bijective_idealQuotientSectionsLift` and
    `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientSectionsRingEquiv`, the surjectivity half
    being `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite` — the
    restated form of Descent, Proposition 03DW, *unconditional* in this tree by faithfully flat
    descent along a finite affine étale refinement — and the injectivity half the kernel
    statement above;
  - finite presentation of `ℬ/ℐ_j` is
    `AlgebraicGeometry.Space.AlgebraSheaf.isFinitePresentation_idealQuotient`, **given finite
    presentation of `ℬ` and finite generation of the ideal of sections `ℐ_j(W)` over every affine
    étale chart** — this is where the source's finite generation of `ℐ_j` enters.

  It is not a cohomology statement: no Čech cohomology
  appears anywhere in that chain.

  The conjunct is nevertheless **not** removed from `hsource`.  `hsource` asks no quasi-coherence
  of `ℬ`, no quasi-coherence of the `ℐ_j`, no finiteness of them and no finite presentation of
  `ℬ`, and none of those follow from its remaining conjuncts: finite presentation of a
  structure-algebra map on every affine chart says nothing about the restriction maps being base
  changes, so it does not imply quasi-coherence.  Dropping the conjunct would therefore require
  *adding* those four, which makes `hsource` stronger and this theorem weaker.  A caller holding
  them can produce the conjunct with no further mathematics; in the source they come from
  `ℬ = Sym(ℱ)` for the finitely presented `ℱ` of Stacks 086Y and from `ℐ_j` being a finite type
  quasi-coherent submodule of the kernel ideal (Stacks 0829).
* **the colimit property of the constructed cocone.**  This is no longer an unverifiable
  abstraction.  `AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientAlgCocone_iff_locally`
  in `Spaces/Limits/AlgebraSheafIdealQuotientColimit.lean` shows that, at the level of *all*
  algebra sheaves, the constructed cocone is colimiting **exactly when** `f` is locally
  surjective and every section of `ℬ` killed by `f` locally lies in one member of the family —
  two conditions on sections of `ℬ` and of `𝒜` over the objects of the small étale site, with no
  sheafification and no cohomology in them.  The quasi-coherent form that `hsource` asks for
  follows from the same two conditions, by
  `AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientQcohCocone_of_locally`.

  Those two conditions are nevertheless *not* substituted for the colimit conjunct of `hsource`.
  `AlgebraicGeometry.Space.QuasicoherentAlgebra` is a full subcategory, and a full subcategory
  inclusion reflects colimits but need not preserve them, so at the quasi-coherent level the
  implication runs one way only; substituting would make `hsource` **stronger** and this theorem
  weaker.  The gain is that a caller can now discharge the conjunct from elementary data, not
  that the conjunct is cheaper to state.

### The three are dischargeable together, and the tag is still not unconditional

The three bullets above are each accurate about their own conjunct, and, in the namespace
`AlgebraicGeometry.Space`,
`exists_directed_isFinite_isFinitePresentation_locallySurjective_of_elementaryData`
in `StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientColimit` is the theorem
that discharges all three at once: it has the conclusion of the theorem below over a carried input
every conjunct of which is a condition on sections over the objects of the small étale site, or on
a single affine étale chart.  **It does not make this tag unconditional, and nothing here does.**
Three things stand in the way, and the first two are the reason the first bullet above must not be
read as making `ℬ` free of cost:

* taking `ℬ = Sym(ℱ)`, as the first bullet invites, is paid for in the *third*.  Quasi-coherence
  of `ℬ/ℐ_j` is `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_idealQuotient`, whose
  hypothesis `hA` is quasi-coherence of `ℬ`.  So while `hsource` indeed asks no quasi-coherence of
  `ℬ`, *discharging* its quasi-coherence conjunct asks exactly that — and quasi-coherence of
  `Sym(ℱ)` on the small étale site of an algebraic space is absent.  The implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafMap` record it as the one thing that
  file does not supply and name what is missing; Stacks 01CK and 01CL are proved only for a ringed
  space, as `Stacks.SheafOfModules.isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent`.
* finite presentation of `ℬ/ℐ_j`,
  `AlgebraicGeometry.Space.AlgebraSheaf.isFinitePresentation_idealQuotient`, likewise asks finite
  presentation of `ℬ`.  For `ℬ = Sym(ℱ)` with `ℱ` of finite presentation that is not available
  either: `Sym(ℱ)` is a sheafification, and a section of it over a chart is only *locally* a
  finite sum of homogeneous ones, so `Sym(ℱ)(W) = Sym(ℱ(W))` is not at hand.
* integrality at one index is the source's fourth step, and is carried, as said above.

`hsource` therefore says: for **the** `Y` and **the** `𝒜` of the statement, given their
quasi-compactness, quasi-separatedness and finiteness, there are an algebra sheaf `ℬ`, a map
`ℬ ⟶ 𝒜`, and a **filtered** family of sheaves of ideals of `ℬ` killed by that map and growing
along the index, such that every quotient `ℬ/ℐ_j` is quasi-coherent of finite presentation, the
constructed cocone of those quotients is colimiting, and **some one** quotient is integral.  It
asserts no finiteness of any stage, no directedness, and **no surjectivity of any transition
map**; it mentions nothing of the system of the conclusion; and — the change this file now makes
— it is asked at the statement's own space and algebra only, not for every quasi-compact
quasi-separated algebraic space and every finite quasi-coherent algebra on it.

What is proved here, on top of `hsource`, is the rest of the tag:

* **surjectivity of every transition map.**  The transition map `ℬ/ℐ_p ⟶ ℬ/ℐ_q` composed after
  the quotient morphism `ℬ ⟶ ℬ/ℐ_p` *is* the quotient morphism `ℬ ⟶ ℬ/ℐ_q`, which is locally
  surjective because the objectwise quotient map is surjective on the sections over every chart
  and sheafification is locally surjective; a morphism written on the right of a locally
  surjective factorization is locally surjective, by
  `CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac`.  This is
  `AlgebraicGeometry.Space.isLocallySurjective_idealQuotientQcohDiagram_map`.
* **finiteness of every stage.**  Integrality is carried at a single index `j₀` only.  It is
  propagated to every index receiving a morphism from `j₀` by
  `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegral.of_surjective_app`, using that the transition
  maps are locally surjective and hence — the stages being quasi-coherent — surjective on the
  sections over every affine étale chart, by
  `AlgebraicGeometry.Space.AlgebraSheaf.epi_underlyingModuleMap_of_isLocallySurjective` followed by
  `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`.  Finiteness is then
  integrality together with finite type, which is
  `AlgebraicGeometry.Space.AlgebraSheaf.isFinite_iff_isIntegral_and_isFiniteType`, finite type
  coming from finite presentation.  The carried hypothesis is therefore strictly weaker than
  finiteness of a stage: for an algebra of finite presentation, integral and finite are the same
  condition, and `IsFinite` of the conclusion is nowhere assumed.
* **that the restriction loses no generality.**  Restricting to the indices under `j₀` is
  restriction along `CategoryTheory.Under.forget j₀`, which is final on a filtered category, so the
  colimit is still `𝒜`; this step is
  `Stacks.DirectedCokernelSystem.isColimit_whiskerLeft` of the Stacks 086Y module.
* **directedness**, by
  `Stacks.FiniteAlgebraSurjectiveSystem.exists_directed_of_filtered_colimit_hom`.
* **surjectivity of the transition maps of the directed system.**  Every transition map of the
  reindexed diagram is literally a transition map of the original one, both reindexings being
  restrictions along functors, which is why the reindexing theorem can carry a property of the
  maps and not only of the objects.

What the chart-uniformity of the carried integrality costs is worth naming.  The source chooses a
*single* affine étale surjection `U → Y` and argues on `U`; the predicates of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits` quantify over *every* affine étale
chart, so `hsource` asks for an index integral on all of them at once.  That uniformity is part of
what is carried, not part of what is proved.

### Relation to the two existing reindexing theorems

`Stacks.FiniteAlgebraSurjectiveSystem.exists_directed_of_filtered_colimit_hom` generalizes
`Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered` by concluding, in addition, that a
property of the transition maps survives; it is proved by that theorem's route.  The Stacks 086Y
module's `Stacks.DirectedCokernelSystem.exists_directed_epi_of_filtered_colimit` is the case of
the map property `CategoryTheory.Epi`, over a `FinallySmall` rather than an `EssentiallySmall`
index; local surjectivity is strictly stronger than being an epimorphism here, so that instance
does not serve, and the general form is needed.

## References

* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 086Y](https://stacks.math.columbia.edu/tag/086Y)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t v w c wC u m

namespace Stacks.FiniteAlgebraSurjectiveSystem

/-- **A filtered colimit with an essentially `t`-small index is a directed colimit over a preorder
in `Type t`, preserving a property of the objects *and a property of the transition maps*.**

The diagram produced is a restriction of the given one along a composite of two functors, so every
object of it is an object of the given diagram and every morphism of it is a morphism of the given
diagram; that is what lets `Q` travel alongside `P`.

The object half is `Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered`, whose route this
follows: replace the index by its small model, apply Deligne's theorem
`CategoryTheory.IsFiltered.exists_directed` to get a directed partial order mapping finally into
it, and whisker the colimit along both. -/
theorem exists_directed_of_filtered_colimit_hom {C : Type c} [Category.{wC, c} C]
    {J : Type v} [Category.{w, v} J] [IsFiltered J] [EssentiallySmall.{t} J]
    (P : C → Prop) (Q : ∀ Z Z' : C, (Z ⟶ Z') → Prop)
    (G : J ⥤ C) (M : C) (g : G ⟶ (Functor.const J).obj M)
    (hg : IsColimit (Cocone.mk M g)) (hP : ∀ j, P (G.obj j))
    (hQ : ∀ (j j' : J) (f : j ⟶ j'), Q _ _ (G.map f)) :
    ∃ (I : Type t) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ C) (φ : D ⟶ (Functor.const I).obj M) (_ : IsColimit (Cocone.mk M φ)),
      (∀ i, P (D.obj i)) ∧ ∀ (i j : I) (h : i ≤ j), Q _ _ (D.map (homOfLE h)) := by
  have : IsFiltered (SmallModel.{t} J) := IsFiltered.of_equivalence (equivSmallModel.{t} J)
  obtain ⟨α, _, hdir, hne, r, _⟩ := IsFiltered.exists_directed (SmallModel.{t} J)
  let e : SmallModel.{t} J ≌ J := (equivSmallModel.{t} J).symm
  exact ⟨α, inferInstance, hne, hdir, r ⋙ e.functor ⋙ G,
    (((Cocone.mk M g).whisker e.functor).whisker r).ι,
    (Functor.Final.isColimitWhiskerEquiv r _).symm (hg.whiskerEquivalence e),
    fun _ => hP _, fun _ _ _ => hQ _ _ _⟩

end Stacks.FiniteAlgebraSurjectiveSystem

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace AlgebraSheaf

/-- **Integrality passes to the target of a morphism which is surjective on the sections over the
affine étale charts.**  On such a chart the structure-algebra map of `C` is the structure-algebra
map of `A` followed by a surjection, and a surjective ring map is integral, so this is
`RingHom.IsIntegral.trans`.

This is the companion of `AlgebraicGeometry.Space.AlgebraSheaf.IsFiniteType.of_surjective_app`,
and together with it and
`AlgebraicGeometry.Space.AlgebraSheaf.isFinite_iff_isIntegral_and_isFiniteType` it propagates
finiteness along such a morphism. -/
theorem IsIntegral.of_surjective_app {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (hf : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective ((f.right.hom.app (.op U)).hom))
    (hA : A.IsIntegral) : C.IsIntegral := by
  intro U hU
  rw [← comp_algebraMap f (.op U)]
  exact RingHom.IsIntegral.trans (A.algebraMap (.op U)) ((f.right.hom.app (.op U)).hom)
    (hA U hU) (RingHom.isIntegral_of_surjective _ (hf U hU))

end AlgebraSheaf

/-! ### The system of quotients of one algebra sheaf by a growing family of ideals

This is the system of the third step of the source's proof, in the shape that step produces it:
*one* algebra sheaf `ℬ` — in the source `Sym_{𝒪_Y}(ℱ)` for a single finitely presented module
`ℱ` surjecting onto `𝒜` — divided by a family of sheaves of ideals growing along a filtered
index.  The members and the transition maps are built from
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient`, and the surjectivity of
the transition maps is a theorem about them rather than a hypothesis. -/

section IdealSystem

variable {Y : AlgebraicSpaces B S hS} (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    {P : Type u} [SmallCategory P] (ι : P → ℬ.IdealSheaf)
    (hι : ∀ p q : P, (p ⟶ q) → ι p ≤ ι q)

/-- **The diagram `p ↦ ℬ/ℐ_p` of quotients of one algebra sheaf by a family of sheaves of ideals
growing along the index.**  Its transition maps are the comparisons
`AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientMapOfLE`, and both functor laws are their
functoriality in the inclusion. -/
noncomputable def idealQuotientDiagram : P ⥤ AlgebraSheaf.{u, u} B S hS Y.1 Y.2 where
  obj p := ℬ.idealQuotient (ι p)
  map {p q} g := AlgebraSheaf.idealQuotientMapOfLE (hι p q g)
  map_id p := AlgebraSheaf.idealQuotientMapOfLE_refl (ι p) (hι p p (𝟙 p))
  map_comp {_ _ _} _ _ := (AlgebraSheaf.idealQuotientMapOfLE_comp _ _).symm

/-- The diagram of quotients read in the quasi-coherent algebras, once every member is known to
be quasi-coherent. -/
noncomputable def idealQuotientQcohDiagram (hqcoh : ∀ p, (ℬ.idealQuotient (ι p)).IsQuasicoherent) :
    P ⥤ QuasicoherentAlgebra B S hS Y :=
  ObjectProperty.lift _ (idealQuotientDiagram ℬ ι hι) hqcoh

/-- The underlying algebra sheaf of the member at `p` of the diagram of quotients in the
quasi-coherent algebras is `ℬ/ℐ_p`. -/
@[simp]
theorem idealQuotientQcohDiagram_obj_obj
    (hqcoh : ∀ p, (ℬ.idealQuotient (ι p)).IsQuasicoherent) (p : P) :
    ((idealQuotientQcohDiagram ℬ ι hι hqcoh).obj p).obj = ℬ.idealQuotient (ι p) :=
  rfl

/-- **Every transition map of the system of quotients is locally surjective.**  This is the one
assertion of Stacks 086Z that the quotient construction supplies on its own, and it is
`AlgebraicGeometry.Space.AlgebraSheaf.isLocallySurjective_idealQuotientMapOfLE`. -/
theorem isLocallySurjective_idealQuotientQcohDiagram_map
    (hqcoh : ∀ p, (ℬ.idealQuotient (ι p)).IsQuasicoherent) {p q : P} (g : p ⟶ q) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1)
      ((idealQuotientQcohDiagram ℬ ι hι hqcoh).map g).hom.right.hom :=
  AlgebraSheaf.isLocallySurjective_idealQuotientMapOfLE (hι p q g)

/-- **The cocone of the system of quotients over `A`.**  Its leg at `p` is the factorization of
`f : ℬ ⟶ A` through `ℬ ⟶ ℬ/ℐ_p`, available because `ℐ_p` is killed by `f`; compatibility is
`AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientMapOfLE_comp_idealQuotientLift`. -/
noncomputable def idealQuotientQcohCocone (A : QuasicoherentAlgebra B S hS Y) (f : ℬ ⟶ A.obj)
    (hkill : ∀ (p : P) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
      a ∈ (ι p).obj U → (f.right.hom.app U).hom a = 0)
    (hqcoh : ∀ p, (ℬ.idealQuotient (ι p)).IsQuasicoherent) :
    idealQuotientQcohDiagram ℬ ι hι hqcoh ⟶ (Functor.const P).obj A where
  app p := ObjectProperty.homMk (AlgebraSheaf.idealQuotientLift f (ι p) (hkill p))
  naturality p q g := by
    refine ObjectProperty.hom_ext _ ?_
    change AlgebraSheaf.idealQuotientMapOfLE (hι p q g) ≫
        AlgebraSheaf.idealQuotientLift f (ι q) (hkill q) =
      AlgebraSheaf.idealQuotientLift f (ι p) (hkill p) ≫ 𝟙 A.obj
    rw [Category.comp_id]
    exact AlgebraSheaf.idealQuotientMapOfLE_comp_idealQuotientLift f (hι p q g) (hkill p) (hkill q)

end IdealSystem

variable (B S hS)

/-- **Stacks Project, Tag 086Z.** Let `S` be a scheme, let `Y` be a quasi-compact and
quasi-separated algebraic space over `S` and let `A` be a finite quasi-coherent `𝒪_Y`-algebra.
Then `A` is the colimit of a system of quasi-coherent `𝒪_Y`-algebras indexed by a nonempty
directed preorder, every member of which is finite and of finite presentation, and every
transition map of which is surjective.

All four assertions of the source are in the conclusion: the index is a nonempty preorder which
is directed, every stage is `AlgebraicGeometry.Space.AlgebraSheaf.IsFinite` and
`AlgebraicGeometry.Space.AlgebraSheaf.IsFinitePresentation`, every transition map is locally
surjective, and the cocone with vertex `A` is colimiting.  Quasi-coherence of the stages is
structural, the diagram taking values in `AlgebraicGeometry.Space.QuasicoherentAlgebra`.

The quasi-compactness and quasi-separatedness of `Y` and the finiteness of `A` are used by being
handed to `hsource`, which is the *data* of the third step of the source's proof — one algebra
sheaf and a filtered family of sheaves of ideals of it — together with integrality at a single
index, **for this `Y` and this `A` and no other**.  The system itself is built from that data by
`AlgebraicGeometry.Space.idealQuotientDiagram` and
`AlgebraicGeometry.Space.idealQuotientQcohCocone`; see the module documentation for what `hsource`
stands for and for what is proved on top of it. -/
@[stacks 086Z "the directedness of the index, the finiteness of every stage, the finite \
presentation of every stage and the surjectivity of every transition map, over the carried input \
hsource. hsource is the DATA the first three steps of the source's proof produce, not the system \
they build: one algebra sheaf B (in the source Sym(F) for the finitely presented module F of \
Stacks 086Y), a map B to the algebra, and a FILTERED family of sheaves of ideals of B killed by \
that map and growing along the index (in the source the finite type submodules of the kernel \
ideal, Stacks 0829), plus quasi-coherence and finite presentation of each quotient B/I_j, the \
colimit property of the constructed cocone, and integrality — not finiteness — at ONE index, \
which is the single-index half of the fourth step. hsource is asked only AT THE Y AND THE A OF \
THE STATEMENT, not for every quasi-compact quasi-separated space and every finite algebra. The \
MEMBERS AND THE TRANSITION MAPS OF THE \
SYSTEM ARE NOT CARRIED: they are AlgebraicGeometry.Space.idealQuotientDiagram and \
AlgebraicGeometry.Space.idealQuotientQcohCocone, built from the quotient of an algebra sheaf on \
an algebraic space by a sheaf of ideals and its universal property \
(AlgebraicGeometry.Space.AlgebraSheaf.idealQuotient, idealQuotientMapOfLE, idealQuotientLift), \
and SURJECTIVITY OF EVERY TRANSITION MAP IS PROVED, by \
AlgebraicGeometry.Space.isLocallySurjective_idealQuotientQcohDiagram_map, so hsource asserts no \
surjectivity at all. Of the three inputs that leave Stacks 082A partial in \
AlgebraicGeometry.Space.exists_directed_isFinitePresentation_algebra_of_idealQuotients, ALL \
THREE ARE NOW DISCHARGEABLE FROM ELEMENTARY DATA and none may be SUBSTITUTED for: in each case \
that data is not among the remaining conjuncts of hsource, so replacing a conjunct by it would \
make hsource STRONGER and this theorem weaker. (1) B and the map are now CONSTRUCTIBLE at \
the algebraic space level: functoriality of the symmetric algebra is \
AlgebraicGeometry.Space.symmetricAlgebraSheafMap in Spaces/SymmetricAlgebraSheafMap.lean and the \
ungraded universal property producing a morphism of algebra sheaves Sym(F) to A out of a \
morphism of modules F to A is AlgebraicGeometry.Space.SymAlgSheaf.algebraLift in \
Spaces/SymmetricAlgebraSheafUngradedLift.lean, so with Stacks 086Y one may take B = Sym(F) and \
the map = algebraLift; quasi-coherence of Sym(F) is still unproved at this level but hsource \
asks NO quasi-coherence of B, so it is not needed here. (2) The colimit property of the \
constructed cocone is now EQUIVALENT, at the level of all algebra sheaves, to two elementary \
local conditions — local surjectivity of the map and local membership of every section it kills \
in some member of the family — by \
AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientAlgCocone_iff_locally in \
Spaces/Limits/AlgebraSheafIdealQuotientColimit.lean, and \
AlgebraicGeometry.Space.nonempty_isColimit_idealQuotientQcohCocone_of_locally supplies the \
quasi-coherent form that hsource asks for from those two conditions, with no affine-chart \
verification and no cohomology. It is NOT substituted into hsource: the quasi-coherent algebras \
are a full subcategory, whose inclusion reflects but need not preserve colimits, so at that \
level the implication runs one way only and substituting the local conditions would make this \
hypothesis STRONGER and the theorem weaker. (3) Quasi-coherence and finite presentation of a \
sheafified quotient over an affine etale chart — the identification of the sections of B/I_j over \
such a chart with the objectwise quotient — is NOW PROVED, in \
Spaces/Limits/AlgebraSheafIdealQuotientCokernel.lean. The step that was missing, the \
identification of the underlying module of B/I_j with the COKERNEL of the inclusion of I_j, is \
AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleIdealQuotientCokernelIso, an epi-mono \
factorisation in the balanced category of O_Y-modules whose exactness input is \
AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient (the quotient morphism kills \
exactly the sections of the ideal, Spaces/Limits/AlgebraSheafIdealQuotientKernel.lean) and whose \
epimorphism input is local surjectivity of the quotient morphism. From it: quasi-coherence of \
B/I_j is AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_idealQuotient, by \
AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional, GIVEN quasi-coherence of B \
and of I_j; the sections over an affine chart W are B(W)/I_j(W), by \
AlgebraicGeometry.Space.AlgebraSheaf.bijective_idealQuotientSectionsLift and \
idealQuotientSectionsRingEquiv, whose surjectivity half is \
AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite, the restated form of \
Descent 03DW, unconditional in this tree by faithfully flat descent with no Cech cohomology; and \
finite presentation of B/I_j is \
AlgebraicGeometry.Space.AlgebraSheaf.isFinitePresentation_idealQuotient, GIVEN finite \
presentation of B and finite generation of the ideal of sections I_j(W) over every affine chart, \
which is where the source's finite generation of the ideals enters and is why no finiteness is \
asked of them here. The conjunct is nevertheless NOT removed from hsource: hsource asks no \
quasi-coherence of B, no quasi-coherence of the I_j, no finiteness of them and no finite \
presentation of B, and none of those follow from its remaining conjuncts — finite presentation of \
a structure-algebra map on every affine chart says nothing about the restriction maps being base \
changes, so it does not imply quasi-coherence — so dropping the conjunct would require ADDING \
FOUR NEW ONES (quasi-coherence of B, quasi-coherence of each I_j, finite presentation of B, and \
finite generation of each I_j(W)), which makes hsource STRONGER and this theorem weaker. What has \
changed is that a caller holding those four can now produce the conjunct with no further \
mathematics. Stacks 086Y \
and Stacks 0829 are both proved here (as \
AlgebraicGeometry.Space.exists_directed_isFinitePresentation_epi_of_isFiniteType and as \
AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9 with \
AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject). hsource asserts no \
finiteness of any stage and no directedness; finiteness of every stage, directedness, \
surjectivity of every transition map and survival of the colimit are proved. The source argues \
on one affine étale chart while this tree's finiteness predicates quantify over all of them, so \
the chart-uniformity of the carried integrality is carried too"]
theorem exists_directed_isFinite_isFinitePresentation_locallySurjective
    (Y : AlgebraicSpaces B S hS) (A : QuasicoherentAlgebra B S hS Y)
    (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)
    (hA : A.obj.IsFinite)
    (hsource :
      IsQuasiCompactSpace B S hS Y.obj →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj →
      A.obj.IsFinite →
        ∃ (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ A.obj) (J : Type u)
          (inst : SmallCategory J),
          let _ := inst
          ∃ (_ : IsFiltered J) (ι : J → ℬ.IdealSheaf)
            (hι : ∀ j j' : J, (j ⟶ j') → ι j ≤ ι j')
            (hkill : ∀ (j : J) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
              a ∈ (ι j).obj U → (f.right.hom.app U).hom a = 0)
            (hqcoh : ∀ j, (ℬ.idealQuotient (ι j)).IsQuasicoherent),
            (∀ j, (ℬ.idealQuotient (ι j)).IsFinitePresentation) ∧
            (∃ j, (ℬ.idealQuotient (ι j)).IsIntegral) ∧
            Nonempty (IsColimit (Cocone.mk A
              (idealQuotientQcohCocone ℬ ι hι A f hkill hqcoh)))) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ QuasicoherentAlgebra B S hS Y) (φ : D ⟶ (Functor.const I).obj A),
      Nonempty (IsColimit (Cocone.mk A φ)) ∧
      (∀ i, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation) ∧
      ∀ i j (h : i ≤ j), Presheaf.IsLocallySurjective
        (SmallEtale.topology B S hS Y.obj) (D.map (homOfLE h)).hom.right.hom := by
  obtain ⟨ℬ, f, J, _, _, ι, hι, hkill, hqcoh, hfp, ⟨j₀, hj₀⟩, ⟨hcol⟩⟩ := hsource hqc hqs hA
  -- The system and its cocone are the constructed ones; only the data above is carried.
  let E : J ⥤ QuasicoherentAlgebra B S hS Y := idealQuotientQcohDiagram ℬ ι hι hqcoh
  let ψ : E ⟶ (Functor.const J).obj A := idealQuotientQcohCocone ℬ ι hι A f hkill hqcoh
  -- Surjectivity of the transition maps is a theorem about the quotients, not a hypothesis.
  have hls : ∀ (j j' : J) (g : j ⟶ j'), Presheaf.IsLocallySurjective
      (SmallEtale.topology B S hS Y.obj) (E.map g).hom.right.hom :=
    fun _ _ g => isLocallySurjective_idealQuotientQcohDiagram_map ℬ ι hι hqcoh g
  -- Integrality travels from `j₀` to every index under it, along the surjective transition maps.
  have hint : ∀ (j : J) (g : j₀ ⟶ j), (E.obj j).obj.IsIntegral := by
    intro j g
    refine AlgebraSheaf.IsIntegral.of_surjective_app (E.map g).hom (fun U hU => ?_) hj₀
    have hlsg : Sheaf.IsLocallySurjective (E.map g).hom.right := hls j₀ j g
    exact surjective_val_app_of_epi_of_isQuasicoherentOnSite _
      (AlgebraSheaf.epi_underlyingModuleMap_of_isLocallySurjective (E.map g).hom hlsg)
      (E.obj j₀).property (E.obj j).property U hU
  -- Restriction along the final functor `Under.forget j₀` keeps the colimit.
  obtain ⟨I, instI, hne, hdir, D, φ, hcolD, hobj, hmor⟩ :=
    Stacks.FiniteAlgebraSurjectiveSystem.exists_directed_of_filtered_colimit_hom.{u}
      (fun C : QuasicoherentAlgebra B S hS Y => C.obj.IsFinite ∧ C.obj.IsFinitePresentation)
      (fun (C C' : QuasicoherentAlgebra B S hS Y) (g : C ⟶ C') =>
        Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.obj) g.hom.right.hom)
      (Under.forget j₀ ⋙ E) A (Functor.whiskerLeft (Under.forget j₀) ψ)
      (Stacks.DirectedCokernelSystem.isColimit_whiskerLeft (Under.forget j₀) E A ψ hcol)
      (fun W => ⟨(AlgebraSheaf.isFinite_iff_isIntegral_and_isFiniteType _).2
        ⟨hint W.right W.hom, (hfp W.right).isFiniteType⟩, hfp W.right⟩)
      (fun _ _ _ => hls _ _ _)
  exact ⟨I, instI, hne, hdir, D, φ, ⟨hcolD⟩, hobj, hmor⟩

end AlgebraicGeometry.Space

end
