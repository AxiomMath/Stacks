module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# The direct-image algebra on morphisms and on squares

Stacks 081V asserts that the algebraic spaces affine over an algebraic space `X` are
anti-equivalent to the quasi-coherent sheaves of commutative `𝒪_X`-algebras, that the
anti-equivalence sends `f : Y ⟶ X` to `f_* 𝒪_Y`, and that it is compatible with arbitrary base
change.  `StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence` supplies the
vocabulary: the two categories, the direct-image algebra
`AlgebraicGeometry.Space.pushforwardAlgebra` of an algebraic space over `X`, and the map
`AlgebraicGeometry.Space.pushforwardRingMap` which a morphism over `X` induces on direct-image
sheaves of *rings*.

This file upgrades that map, and the square comparison
`AlgebraicGeometry.Space.pushforwardSquareMap`, from sheaves of rings to `𝒪_X`-algebras: both
are compatible with the structure-algebra maps, and the first is therefore packaged as a
morphism of algebra sheaves.  It then proves the two functoriality clauses of Stacks 03G8 for
that map — compatibility with composition and with identities — and assembles the contravariant
functor `(Over X)ᵒᵖ ⥤ AlgebraSheaf X` that Stacks 081V's anti-equivalence is built on.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardAlgebraMap` is the contravariant action of
  `f ↦ f_* 𝒪_Y` on a morphism of the over-category, as a morphism of `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.pushforwardSquareAlgebra` is `g_* (f'_* 𝒪_W)` as an `𝒪_X`-algebra,
  for `g : Y ⟶ X` and `f' = W.hom : W ⟶ Y`.  It is the target of the comparison attached to a
  commutative square over `g`.
* `AlgebraicGeometry.Space.pushforwardAlgebraFunctor` is the contravariant functor
  `f ↦ f_* 𝒪_Y` from the algebraic spaces over `X` to the sheaves of commutative
  `𝒪_X`-algebras, and `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` is its
  restriction to the algebraic spaces affine over `X`.
* `AlgebraicGeometry.Space.pushforwardSetMap` and `AlgebraicGeometry.Space.pushforwardAlgMap`
  are the direct-image map of a morphism `a : A₁ ⟶ A₂` over a structure morphism `y : A₂ ⟶ X`,
  on sheaves of sets and on sheaves of commutative rings.  Each is
  `AlgebraicGeometry.Space.pushforwardRingMap` with the structure morphism of the source left as
  the composite `a ≫ y`, so that the transport along `CategoryTheory.Over.w` is separated off
  and the composition law needs none.

## Main results

* `AlgebraicGeometry.Space.isIso_fSharp_id` is **the identity clause of Stacks 03G8** for the
  `CommRingCat`-valued structure map: the structure map of `𝟙 : A ⟶ A` is an isomorphism
  `𝒪_A ≅ (𝟙_A)_* 𝒪_A`.
* `AlgebraicGeometry.Space.pushforwardRingMap_id` and
  `AlgebraicGeometry.Space.pushforwardAlgebraMap_id`: the direct image of an identity is the
  identity.  This is the `CategoryTheory.Functor.map_id` half of Stacks 081V's functor.
* `AlgebraicGeometry.Space.pushforwardRingMap_comp` and
  `AlgebraicGeometry.Space.pushforwardAlgebraMap_comp`: the direct image `f ↦ f_* 𝒪_Y` carries a
  composite of morphisms over `X` to the composite of the induced maps in the other order, on
  sheaves of commutative rings and on `𝒪_X`-algebras.  This is the
  `CategoryTheory.Functor.map_comp` half of Stacks 081V's functor.
* `AlgebraicGeometry.Space.pushforwardSetMap_comp` and
  `AlgebraicGeometry.Space.pushforwardAlgMap_comp` are that composition law in the form without
  transports, on sheaves of sets and on sheaves of commutative rings; the first carries the
  whole argument and the second is the first read through the faithful functor forgetting the
  ring operations.
* `AlgebraicGeometry.Space.fSharp_comp_pushforwardRingMap`: the structure map of `Z ⟶ X`
  followed by the map induced by `f : Y ⟶ Z` is the structure map of `Y ⟶ X`.  This is the
  algebra compatibility of `AlgebraicGeometry.Space.pushforwardRingMap`.
* `AlgebraicGeometry.Space.fSharp_comp_pushforwardSquareMap`: the same for a commutative
  square, with `g_* (f'_* 𝒪_W)` carrying the `𝒪_X`-algebra structure obtained from `g` and from
  the `𝒪_Y`-algebra `f'_* 𝒪_W`.
* `AlgebraicGeometry.Space.fSharp_comp_compRingIso` and
  `AlgebraicGeometry.Space.fSharp_comp_compRingIso_inv` are the two forms of Stacks 03G8's
  composition law used here, the first with a trailing morphism so that it can be applied
  inside a longer composite.
* `AlgebraicGeometry.Space.cancelRetractionLeft` and
  `AlgebraicGeometry.Space.cancelRetractionRight` cancel a retracted morphism out of a
  composite, in an abstract category.

## Implementation notes

**What is delivered of Stacks 081V, and what is not.**  The *functor* `f ↦ f_* 𝒪_Y` is
constructed, as `AlgebraicGeometry.Space.pushforwardAlgebraFunctor`, together with its
restriction `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` to the algebraic spaces
affine over `X`.  What is not delivered is the assertion that it is an *anti-equivalence*, and
with it the base-change clause.  **Two inputs that might appear absent are
available**:

* the functor here lands in all of `AlgebraicGeometry.Space.AlgebraSheaf`, not in
  `AlgebraicGeometry.Space.QuasicoherentAlgebra X`.  Restricting the
  codomain needs quasi-coherence of `f_* 𝒪_Y`, which is Stacks 03M9.  **Stacks 03M9 is
  proved**, as
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs` of
  `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs`, at the tag's own
  quasi-compact and quasi-separated hypotheses, and the codomain-restricted functor built from
  it is `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor` of
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentPushforwardAlgebra`, where an affine
  morphism supplies both hypotheses.  So nothing about the codomain is still open.
* the functor is not shown to be an anti-equivalence.  The missing input is not
  Stacks 03M3 for an algebraic-space target:
  **Stacks 03M3 is proved for a target which is an algebraic space, and as an equivalence**:
  `AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence`, at
  the hypotheses of the source and nothing else.  It is a statement about quasi-coherent
  *modules*; the construction of Stacks 081V reads an algebra sheaf through its **algebra**
  analogue, and that is what is missing — `AlgebraicGeometry.Space.QuasicoherentAlgebra` occurs
  in no file of either groupoid tree, so there is no category of quasi-coherent algebras on a
  groupoid in algebraic spaces for such a statement to be about.
* compatibility with arbitrary base change needs the anti-equivalence to state at all: it is
  the field `baseChangeIso` of `AlgebraicGeometry.Space.BaseChangeCompatibility`.  Nine of that
  structure's twelve fields are built in
  `StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeCompatibilityReduction`, leaving
  `algebraPullback_isQuasicoherent`, `baseChangeIso` and `baseChangeIso_canonical`.

**Where the whole remaining content of the tag's first sentence sits.**  By
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.ofIsEquivalence` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceReduction`, the five-field
structure follows from the single assertion

```
∀ X, (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).IsEquivalence
```

the other four fields being identities and `rfl`.  So the two facet attributes below cover the
functor, and that one `Prop` is the entire gap between them and the tag's first sentence.  Its
three known routes are each blocked by a *missing identification*, not by a missing Stacks
result — every tag the source's proof cites (01SA, 02WW, 03M3, 03WG, 07S3) is formalized, 02WW
unconditionally:

* the étale-to-Zariski leg for algebras,
  `AlgebraicGeometry.SmallEtale.restrictQuasicoherentAlgebraToZariski`, is a functor and not an
  equivalence.  On modules it is one (Stacks 03DX (2)), and
  `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso` (Stacks 03EL at `ε`) makes the
  module equivalence monoidal, but there is no identification of `CategoryTheory.Under` of a
  sheaf of commutative rings with the commutative monoid objects of its sheaves of modules for
  that monoidality to act on.  The symmetric monoidal structure such a statement would be
  about does exist, generically, as
  `Stacks.SheafOfModules.symmetricCategory`; Mathlib has the non-sheafy
  `ModuleCat.monModuleEquivalenceAlgebra` and `CategoryTheory.commAlgCatEquivUnder` but no
  commutative monoid-object leg joining them.
* descent for sheaves of commutative rings on the small étale site, which with
  `CategoryTheory.Under.postEquiv` would carry algebra descent for free and so would supply the
  algebra analogue of 03M3 above.  What is available is descent for sheaves of *sets*,
  `AlgebraicGeometry.Space.SpacesEtale.isEquivalence_toDescentData_smallEtaleSheafSystem`.
  This is **not** a coefficient specialization of it, although the generic machinery
  (`CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`, Stacks
  04TS) is polymorphic in its coefficient category: that theorem needs
  `HasLimitsOfSize.{max u v, max u v}` of the coefficients, which on this site is
  `HasLimitsOfSize.{u + 1, u + 1}` because the small étale site has its objects one universe
  above its morphisms.  `Type (u + 1)` has it and `CommRingCat.{u}` does not — the instance was
  probed and fails to synthesize — and `CommRingCat.{u}` is where the structure sheaf and every
  `AlgebraicGeometry.Space.AlgebraSheaf` live.  So the sets-level statement cannot simply be
  reinstantiated at rings; it needs a form of 04TS whose index and sieve data are `u`-sized.
* invertibility of `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison`, which is
  unproved and is in addition stated only for a `CategoryTheory.SmallCategory` site.  It is
  *not* a route to the base-change field above: the scheme-level
  `Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent` is proved unconditionally,
  on stalks, and does not go through this comparison at all.

**The identity clause of Stacks 03G8 is available.**  (Elsewhere,
`AlgebraicGeometry.Space.pushforwardAlgebraIdIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization` obtains the one instance
it needs from an assumed anti-equivalence, and
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage` carries it as the hypothesis
`hid`.)  The clause is proved on sheaves of sets, as
`AlgebraicGeometry.Space.structureSharpSet_id` against the comparison
`AlgebraicGeometry.Space.smallEtaleDirectImageIdIso`, and on sheaves of *rings* as
`AlgebraicGeometry.Space.isIso_structureSharp_id`; what is added here is only its
`CommRingCat`-valued form `AlgebraicGeometry.Space.isIso_fSharp_id`, which is the one
`AlgebraicGeometry.Space.pushforwardAlgebra` is built from.

The step from there to `CategoryTheory.Functor.map_id` does not go through a comparison of
`AlgebraicGeometry.Space.pushforwardRingMap (𝟙 Y)` with the identity term by term.  By
`AlgebraicGeometry.Space.pushforwardRingMap_comp` that map is idempotent, since
`𝟙 Y ≫ 𝟙 Y = 𝟙 Y`, and an idempotent isomorphism is the identity; so it is enough that the map
be an *isomorphism*, which is `AlgebraicGeometry.Space.isIso_pushforwardRingMap`, and for that
it is enough that the structure map of `𝟙` be one.

**The cocycle condition is available.**
The associativity cocycle for `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso`
is stated at the universe `Type (u + 1)` of the sites as
`AlgebraicGeometry.Space.smallToposMorphism_comp_assoc`, and its `Type u` transcription is
proved, as `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`, and so is the
composition law of Stacks 03G8 for the structure map at the level of sheaves of sets,
`AlgebraicGeometry.Space.structureSharpSet_comp`.  Those two together with naturality of
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` are the whole proof of
`AlgebraicGeometry.Space.pushforwardSetMap_comp`, and the ring-level and algebra-level
composition laws follow from it because forgetting the ring operations is faithful on sheaves
and because a morphism of `AlgebraicGeometry.Space.AlgebraSheaf` is determined by its
underlying morphism of sheaves of rings.
`StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp` is imported for
`AlgebraicGeometry.Space.structureSharpSet_comp` alone, which is where that set-level form of
03G8 happens to live; it is not restated here.

The base-change half of Stacks 081V is likewise not reached.  What is here is the canonical
comparison of a commutative square and the statement that it respects the algebra structures;
the assertion of the tag is that the *anti-equivalence* commutes with base change, which is the
field `baseChangeIso` of `AlgebraicGeometry.Space.BaseChangeCompatibility` and needs the
anti-equivalence to state at all; no square is required to be cartesian below either.
Accordingly nothing about squares carries Stacks 081V here.  The square comparison is recorded
as the equation `AlgebraicGeometry.Space.fSharp_comp_pushforwardSquareMap` rather than bundled
into an `AlgebraicGeometry.Space.AlgebraSheaf.Hom`: the structure-algebra map of
`AlgebraicGeometry.Space.pushforwardSquareAlgebra` is a composite, and reducing a section of
that composite is work the kernel does not finish inside its reduction limit, so bundling would
mean adjusting those limits.  The equation is the whole content either way.

**Two inputs of the space-level construction of Stacks 081V are available**: Stacks 03M3, and
the base-change clause of the scheme-level Stacks 01SA, which reduces to the single assertion
`Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebraPullback`.

That assertion is discharged, as
`Stacks.AffineAlgebraEquivalence.isQuasicoherentAlgebraPullback`, and the scheme-level
anti-equivalence with its base-change compatibility is proved unconditionally as
`Stacks.AffineAlgebraEquivalence.affineAlgebraAntiEquivalence`, both in
`StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.GeneralBaseChange`.

Stacks 03M3 is proved too.  For a *scheme* target its registration is the functor from
quasi-coherent modules on a scheme to descent data on a groupoid,
`Stacks.Groupoids.GroupoidScheme.quasicoherentModuleOfBaseFunctor` of
`StacksFrontier.AlgebraicGeometry.Groupoids.QuasicoherentFromBase`; the algebraic-space target has
its own registration, and there the equivalence is proved.
The functor is `AlgebraicGeometry.Space.quasicoherentFromSpaceBase`, that it is an equivalence is
`AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase`, the equivalence itself is
`AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`, all three at the hypotheses of
the source and nothing else, and the descent direction that the construction of Stacks 081V reads
an algebra sheaf through is the essential surjectivity
`AlgebraicGeometry.Space.exists_spaceBaseObj_iso` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEssSurj`.

What still stands between those inputs and an inhabitant of
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is the construction itself, together with
the sections formula for the direct image of an arbitrary sheaf of commutative rings along a
morphism of algebraic spaces and the fibre product of quasi-coherent algebra sheaves on an
algebraic space; the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence` say what each is for.

**Why the proofs are composition-law computations and nothing else.**  By definition
`AlgebraicGeometry.Space.pushforwardAlgebra` is
`AlgebraicGeometry.Space.AlgebraSheaf.ofHom` applied to the structure map `f♯`, so its
structure-algebra map on an étale chart is a section of `f♯`.  The compatibility to be proved is
therefore exactly `Z.hom♯ ≫ pushforwardRingMap f = Y.hom♯`, and the factors of
`AlgebraicGeometry.Space.pushforwardRingMap` turn its left-hand side into the structure map of
`f.left ≫ Z.hom` by `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp`, after which
`CategoryTheory.Over.w` identifies that composite with `Y.hom` and the transport is discharged
by `AlgebraicGeometry.Space.pushforwardCommRingFunctor_fSharp_comp_eqToHom`.  Nothing is
chosen anywhere.

**Why the reassociations are isolated into their own lemmas.**  Rewriting with
`CategoryTheory.Category.assoc` inside these composites makes the unifier solve for the
intervening sheaves of commutative rings, and it then descends into the `Classical.choose`
inside `AlgebraicGeometry.Space.structureSharpCommRing` and does not terminate.  So
`AlgebraicGeometry.Space.fSharp_comp_compRingIso` and its companions are stated with every
object written out and with an explicit trailing morphism `t`, which fixes all of those sheaves
before any rewriting happens; at the use sites the statements then match on the nose and no
elaboration limits are adjusted.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A congruence for morphisms of sheaves of commutative rings -/

/-- Equal morphisms of sheaves of commutative rings have equal components.  This is the step
from the morphism-level compatibility of a direct-image map to the sectionwise compatibility
that a morphism of `AlgebraicGeometry.Space.AlgebraSheaf` carries. -/
theorem commRingSheafHom_app_congr {D : Type*} [Category D] {K : GrothendieckTopology D}
    {P Q : Sheaf K CommRingCat.{u}} {a b : P ⟶ Q} (h : a = b) (U : Dᵒᵖ) :
    a.hom.app U = b.hom.app U := by
  rw [h]

/-! ### Two cancellations of a retracted morphism -/

/-- Cancel a retracted morphism from the middle of a composite.  Stated abstractly, with the two
morphisms of the retraction and the two neighbours all explicit, so that it applies to the
composites of sheaves of commutative rings below without the unifier being asked to solve for
any of the intervening sheaves. -/
theorem cancelRetractionLeft {D : Type*} [Category D] {P T V R : D} (w : P ⟶ T)
    {c : T ⟶ V} {c' : V ⟶ T} (hc : c ≫ c' = 𝟙 T) (b' : T ⟶ R) :
    (w ≫ c) ≫ (c' ≫ b') = w ≫ b' := by
  rw [Category.assoc, ← Category.assoc c c' b', hc, Category.id_comp]

/-- Regroup a composite of four morphisms, bracketing off the last factor.  Stated abstractly
and used with all four morphisms given explicitly, so that regrouping
`AlgebraicGeometry.Space.pushforwardRingMap` never asks the unifier to guess a factor of it. -/
theorem comp_assoc₄ {D : Type*} [Category D] {P Q R T V : D} (a : P ⟶ Q) (b : Q ⟶ R)
    (c : R ⟶ T) (d : T ⟶ V) : a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  rw [Category.assoc, Category.assoc]

/-- Cancel a retracted morphism from the end of a composite of three. -/
theorem cancelRetractionRight {D : Type*} [Category D] {P Q R T : D} (u : P ⟶ Q) (v : Q ⟶ R)
    {b : R ⟶ T} {b' : T ⟶ R} (hb : b ≫ b' = 𝟙 R) :
    (u ≫ v ≫ b) ≫ b' = u ≫ v := by
  rw [Category.assoc, Category.assoc, hb, Category.comp_id]

/-! ### The composition law for the structure map, in applicable form -/

section CompositionLaw

variable {X X₁ X₂ : AlgebraicSpaces B S hS}

/-- Transporting the structure map along an equality of morphisms of algebraic spaces gives the
structure map of the other morphism. -/
theorem pushforwardCommRingFunctor_fSharp_comp_eqToHom {q q' : X₁ ⟶ X} (h : q = q') :
    (smallEtaleRingedToposHom B S hS q).fSharp ≫
        eqToHom (congrArg
          (fun r : X₁ ⟶ X =>
            (pushforwardCommRingFunctor
              (smallEtaleRingedToposHom B S hS r).toToposHom).obj
                (smallEtaleRingedTopos B S hS X₁).O) h) =
      (smallEtaleRingedToposHom B S hS q').fSharp := by
  subst h
  exact Category.comp_id _

/-- The same transport, with a trailing morphism, so that it applies inside a longer
composite. -/
theorem pushforwardCommRingFunctor_fSharp_comp_eqToHom_comp {q q' : X₁ ⟶ X} (h : q = q')
    {T : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (t : (pushforwardCommRingFunctor
            (smallEtaleRingedToposHom B S hS q').toToposHom).obj
          (smallEtaleRingedTopos B S hS X₁).O ⟶ T) :
    (smallEtaleRingedToposHom B S hS q).fSharp ≫
        (eqToHom (congrArg
            (fun r : X₁ ⟶ X =>
              (pushforwardCommRingFunctor
                (smallEtaleRingedToposHom B S hS r).toToposHom).obj
                  (smallEtaleRingedTopos B S hS X₁).O) h) ≫ t) =
      (smallEtaleRingedToposHom B S hS q').fSharp ≫ t := by
  subst h
  exact congrArg (fun m => (smallEtaleRingedToposHom B S hS q).fSharp ≫ m)
    (Category.id_comp t)

/-- **Stacks 03G8, compatibility with composition, in applicable form.**  The structure map of
`b`, the direct image along `b` of the structure map of `a`, the comparison of iterated direct
images and the comparison of Stacks 03G8 compose to the structure map of `a ≫ b`.  The
trailing morphism `t` fixes the intervening sheaves of commutative rings, so that the statement
applies to a composite without any reassociation. -/
theorem fSharp_comp_compRingIso (a : X₁ ⟶ X₂) (b : X₂ ⟶ X)
    {T : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (t : (pushforwardCommRingFunctor
            (smallEtaleRingedToposHom B S hS (a ≫ b)).toToposHom).obj
          (smallEtaleRingedTopos B S hS X₁).O ⟶ T) :
    (smallEtaleRingedToposHom B S hS b).fSharp ≫
        ((pushforwardCommRingFunctor
              (smallEtaleRingedToposHom B S hS b).toToposHom).map
            (smallEtaleRingedToposHom B S hS a).fSharp ≫
          (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
              (smallEtaleRingedToposHom B S hS b).toToposHom
              (smallEtaleRingedTopos B S hS X₁).O).hom ≫
            (smallEtaleRingedToposHom_compRingIso B S hS a b).hom.app
              (smallEtaleRingedTopos B S hS X₁).O ≫ t) =
      (smallEtaleRingedToposHom B S hS (a ≫ b)).fSharp ≫ t :=
  calc (smallEtaleRingedToposHom B S hS b).fSharp ≫
        ((pushforwardCommRingFunctor
              (smallEtaleRingedToposHom B S hS b).toToposHom).map
            (smallEtaleRingedToposHom B S hS a).fSharp ≫
          (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
              (smallEtaleRingedToposHom B S hS b).toToposHom
              (smallEtaleRingedTopos B S hS X₁).O).hom ≫
            (smallEtaleRingedToposHom_compRingIso B S hS a b).hom.app
              (smallEtaleRingedTopos B S hS X₁).O ≫ t)
      = (((smallEtaleRingedToposHom B S hS b).comp
            (smallEtaleRingedToposHom B S hS a)).fSharp ≫
          (smallEtaleRingedToposHom_compRingIso B S hS a b).hom.app
            (smallEtaleRingedTopos B S hS X₁).O) ≫ t := by
        simp only [RingedToposHom.comp, Category.assoc]
    _ = (smallEtaleRingedToposHom B S hS (a ≫ b)).fSharp ≫ t := by
        rw [smallEtaleRingedToposHom_comp_fSharp]

/-- **Stacks 03G8, compatibility with composition**, read in the other direction: the structure
map of `a ≫ b`, followed by the inverses of the two comparisons, is the structure map of `b`
followed by the direct image along `b` of the structure map of `a`. -/
theorem fSharp_comp_compRingIso_inv (a : X₁ ⟶ X₂) (b : X₂ ⟶ X) :
    (smallEtaleRingedToposHom B S hS (a ≫ b)).fSharp ≫
        ((smallEtaleRingedToposHom_compRingIso B S hS a b).inv.app
            (smallEtaleRingedTopos B S hS X₁).O ≫
          (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
            (smallEtaleRingedToposHom B S hS b).toToposHom
            (smallEtaleRingedTopos B S hS X₁).O).inv) =
      (smallEtaleRingedToposHom B S hS b).fSharp ≫
        (pushforwardCommRingFunctor
            (smallEtaleRingedToposHom B S hS b).toToposHom).map
          (smallEtaleRingedToposHom B S hS a).fSharp := by
  rw [← smallEtaleRingedToposHom_comp_fSharp B S hS a b]
  exact (cancelRetractionLeft _
      ((smallEtaleRingedToposHom_compRingIso B S hS a b).hom_inv_id_app
        (smallEtaleRingedTopos B S hS X₁).O) _).trans
    (cancelRetractionRight _ _
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedToposHom B S hS b).toToposHom
        (smallEtaleRingedTopos B S hS X₁).O).hom_inv_id)

end CompositionLaw

/-! ### Contravariant functoriality of the direct image -/

section Functoriality

variable {A₁ A₂ A₃ X : AlgebraicSpaces B S hS}

/-- The direct-image map of a morphism `a : A₁ ⟶ A₂` over a structure morphism `y : A₂ ⟶ X`,
at the level of sheaves of sets: the direct image along `y` of the structure map of `a`,
followed by the comparison of Stacks 03G2, part (3).  It is
`AlgebraicGeometry.Space.pushforwardRingMap` with the ring operations forgotten and with the
structure morphism of the source left as the composite `a ≫ y`, so that no transport along
`CategoryTheory.Over.w` appears and the composition law below is an equation between composites
of named morphisms. -/
noncomputable def pushforwardSetMap (a : A₁ ⟶ A₂) (y : A₂ ⟶ X) :
    (smallToposMorphismTypeU B S hS y).pushforward.obj (structureSetSheaf B S hS A₂) ⟶
      (smallToposMorphismTypeU B S hS (a ≫ y)).pushforward.obj
        (structureSetSheaf B S hS A₁) :=
  (smallToposMorphismTypeU B S hS y).pushforward.map (structureSharpSet B S hS a) ≫
    (smallToposMorphismTypeU_comp B S hS a y).hom.app (structureSetSheaf B S hS A₁)

/-- **The composition law for the direct-image map, at the level of sheaves of sets.**  Its
three ingredients are the composition law for the structure map, Stacks 03G8
(`AlgebraicGeometry.Space.structureSharpSet_comp`), the associativity cocycle for the comparison
of Stacks 03G2, part (3) (`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`), and
naturality of that comparison.

The statement typechecks on the nose because composition of morphisms of algebraic spaces is
associative definitionally, which is also what makes
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc` statable; so no transport appears
here.  The proof is written as a chain of equations with every object spelled out, because
reassociating inside these composites by rewriting makes the unifier solve for the intervening
sheaves of sets and diverge. -/
theorem pushforwardSetMap_comp (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (y : A₃ ⟶ X) :
    pushforwardSetMap B S hS b y ≫ pushforwardSetMap B S hS a (b ≫ y) =
      pushforwardSetMap B S hS (a ≫ b) y := by
  have hnat := (smallToposMorphismTypeU_comp B S hS b y).hom.naturality
    (structureSharpSet B S hS a)
  have hcoc := smallToposMorphismTypeU_comp_assoc B S hS a b y (structureSetSheaf B S hS A₁)
  simp only [pushforwardSetMap]
  calc _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (_ ≫ ·) (Category.assoc _ _ _).symm
    _ = _ := congrArg (_ ≫ · ≫ _) hnat.symm
    _ = _ := congrArg (_ ≫ ·) (Category.assoc _ _ _)
    _ = _ := congrArg (_ ≫ _ ≫ ·) hcoc.symm
    _ = _ := congrArg (_ ≫ ·) (Category.assoc _ _ _).symm
    _ = _ := congrArg (_ ≫ · ≫ _) (Functor.map_comp (smallToposMorphismTypeU B S hS y).pushforward
        ((smallEtaleDirectImage B S hS b).map (structureSharpSet B S hS a))
        ((smallToposMorphismTypeU_comp B S hS a b).hom.app (structureSetSheaf B S hS A₁))).symm
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ _)
        (Functor.map_comp (smallToposMorphismTypeU B S hS y).pushforward _ _).symm
    _ = _ := congrArg (· ≫ _) (congrArg _ (structureSharpSet_comp B S hS a b))

/-- The direct-image map of a morphism `a : A₁ ⟶ A₂` over a structure morphism `y : A₂ ⟶ X`, at
the level of sheaves of commutative rings: `AlgebraicGeometry.Space.pushforwardRingMap` with the
structure morphism of the source left as the composite `a ≫ y`, so that the transport along
`CategoryTheory.Over.w` is separated off. -/
noncomputable def pushforwardAlgMap (a : A₁ ⟶ A₂) (y : A₂ ⟶ X) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).obj
        (smallEtaleRingedTopos B S hS A₂).O ⟶
      (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS (a ≫ y)).toToposHom).obj
          (smallEtaleRingedTopos B S hS A₁).O :=
  (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
      (smallEtaleRingedToposHom B S hS a).fSharp ≫
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedToposHom B S hS y).toToposHom
        (smallEtaleRingedTopos B S hS A₁).O).hom ≫
    (smallEtaleRingedToposHom_compRingIso B S hS a y).hom.app
      (smallEtaleRingedTopos B S hS A₁).O

/-- Forgetting the ring operations takes the direct-image map of sheaves of commutative rings to
the direct-image map of sheaves of sets.  Each of the three factors is accounted for separately:
the direct image of the structure map by `AlgebraicGeometry.Space.forgetRing_map_fSharp`, the
comparison of iterated direct images by
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso_hom_forget`, which says it is the
identity on underlying sheaves of sets, and the comparison of Stacks 03G2, part (3) by the
lemma `underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom` of
`Stacks.Sheaves.ToposPullback`. -/
theorem forgetRing_pushforwardAlgMap (a : A₁ ⟶ A₂) (y : A₂ ⟶ X) :
    (smallEtaleRingedTopos B S hS X).forgetRing.map (pushforwardAlgMap B S hS a y) =
      pushforwardSetMap B S hS a y := by
  have hmap : (smallEtaleRingedTopos B S hS X).forgetRing.map
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
          (smallEtaleRingedToposHom B S hS a).fSharp) =
      (smallToposMorphismTypeU B S hS y).pushforward.map
        (structureSharpSet B S hS a) := by
    refine (underlyingRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
      (Φ := (smallEtaleRingedToposHom B S hS y).toToposHom.pushforward)
      (smallEtaleRingedToposHom B S hS a).fSharp).trans ?_
    rw [forgetRing_map_fSharp B S hS a]
    rfl
  have hcomp : (smallEtaleRingedTopos B S hS X).forgetRing.map
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedToposHom B S hS y).toToposHom
        (smallEtaleRingedTopos B S hS A₁).O).hom = 𝟙 _ :=
    pushforwardCommRingCompIso_hom_forget
      (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallEtaleRingedToposHom B S hS y).toToposHom
      (smallEtaleRingedTopos B S hS A₁).O
  have hiso : (smallEtaleRingedTopos B S hS X).forgetRing.map
        ((smallEtaleRingedToposHom_compRingIso B S hS a y).hom.app
          (smallEtaleRingedTopos B S hS A₁).O) =
      (smallToposMorphismTypeU_comp B S hS a y).hom.app (structureSetSheaf B S hS A₁) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS X.1) _ (smallToposMorphismTypeU_comp B S hS a y)
  simp only [pushforwardAlgMap, pushforwardSetMap]
  refine ((smallEtaleRingedTopos B S hS X).forgetRing.map_comp _ _).trans ?_
  refine (congrArg₂ (fun p q => p ≫ q) hmap
      (((smallEtaleRingedTopos B S hS X).forgetRing.map_comp _ _).trans
        (congrArg₂ (fun p q => p ≫ q) hcomp hiso))).trans ?_
  exact congrArg (fun m =>
    (smallToposMorphismTypeU B S hS y).pushforward.map (structureSharpSet B S hS a) ≫ m)
    (Category.id_comp _)

/-- **The composition law for the direct-image map, at the level of sheaves of commutative
rings.**  Forgetting the ring operations is faithful on sheaves, so this is
`AlgebraicGeometry.Space.pushforwardSetMap_comp`. -/
theorem pushforwardAlgMap_comp (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (y : A₃ ⟶ X) :
    pushforwardAlgMap B S hS b y ≫ pushforwardAlgMap B S hS a (b ≫ y) =
      pushforwardAlgMap B S hS (a ≫ b) y := by
  refine (smallEtaleRingedTopos B S hS X).forgetRing.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, forgetRing_pushforwardAlgMap,
    forgetRing_pushforwardAlgMap, forgetRing_pushforwardAlgMap]
  exact pushforwardSetMap_comp B S hS a b y

/-- Transporting the structure morphism of the target along an equality moves past the
direct-image map, at the cost of transporting the structure morphism of the source along the
same equality composed with `a`. -/
theorem eqToHom_comp_pushforwardAlgMap (a : A₁ ⟶ A₂) {m m' : A₂ ⟶ X} (h : m = m') :
    eqToHom (congrArg (fun q : A₂ ⟶ X =>
          (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS A₂).O) h) ≫
        pushforwardAlgMap B S hS a m' =
      pushforwardAlgMap B S hS a m ≫
        eqToHom (congrArg (fun q : A₁ ⟶ X =>
          (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS A₁).O)
          (congrArg (fun k : A₂ ⟶ X => a ≫ k) h)) := by
  subst h
  rw [eqToHom_refl _ _, eqToHom_refl _ _, Category.id_comp, Category.comp_id]

/-- The direct-image map of a morphism whose structure map is an isomorphism is an
isomorphism: the other two factors are isomorphisms by construction. -/
theorem isIso_pushforwardAlgMap (a : A₁ ⟶ A₂) (y : A₂ ⟶ X)
    (ha : IsIso (smallEtaleRingedToposHom B S hS a).fSharp) :
    IsIso (pushforwardAlgMap B S hS a y) := by
  have := ha
  have h1 : IsIso ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS y).toToposHom).map
      (smallEtaleRingedToposHom B S hS a).fSharp) := inferInstance
  have h2 : IsIso (pushforwardCommRingCompIso
      (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallEtaleRingedToposHom B S hS y).toToposHom
      (smallEtaleRingedTopos B S hS A₁).O).hom :=
    Iso.isIso_hom _
  have h3 : IsIso ((smallEtaleRingedToposHom_compRingIso B S hS a y).hom.app
      (smallEtaleRingedTopos B S hS A₁).O) := inferInstance
  unfold pushforwardAlgMap
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)

end Functoriality

/-! ### The identity clause of Stacks 03G8 -/

section Identity

/-- **The identity clause of Stacks 03G8:** the structure map of the morphism of small étale
ringed topoi of `𝟙 : A ⟶ A` is an isomorphism `𝒪_A ≅ (𝟙_A)_* 𝒪_A`.

On underlying sheaves of sets this is `AlgebraicGeometry.Space.structureSharpSet_id`, which
identifies the structure map of an identity with the canonical comparison
`AlgebraicGeometry.Space.smallEtaleDirectImageIdIso` of the direct image along an identity with
the identity functor; forgetting the ring operations reflects isomorphisms, so the
`CommRingCat`-valued structure map is invertible too.
`AlgebraicGeometry.Space.isIso_structureSharp_id` is the same statement for the `RingCat`-valued
`AlgebraicGeometry.Space.structureSharp`, which is not the map that
`AlgebraicGeometry.Space.pushforwardAlgebra` is built from. -/
@[stacks 03G8 "the identity clause: the structure map of an identity is an isomorphism"]
theorem isIso_fSharp_id (A : AlgebraicSpaces B S hS) :
    IsIso (smallEtaleRingedToposHom B S hS (𝟙 A)).fSharp := by
  suffices hs : IsIso ((smallEtaleRingedTopos B S hS A).forgetRing.map
      (smallEtaleRingedToposHom B S hS (𝟙 A)).fSharp) from
    isIso_of_reflects_iso _ (smallEtaleRingedTopos B S hS A).forgetRing
  rw [forgetRing_map_fSharp B S hS (𝟙 A), structureSharpSet_id B S hS A]
  exact ((smallEtaleDirectImageIdIso B S hS A).app (structureSetSheaf B S hS A)).isIso_inv

end Identity

/-! ### The direct-image algebra on morphisms -/

section Morphisms

variable {X : AlgebraicSpaces B S hS} {Y Z : Over X}

/-- The structure-algebra map of `f_* 𝒪_Z`, followed by the map which a morphism `f : Y ⟶ Z`
over `X` induces on direct images, is the structure-algebra map of `f_* 𝒪_Y`.  This is
Stacks 03G8's composition law together with `CategoryTheory.Over.w`. -/
theorem fSharp_comp_pushforwardRingMap (f : Y ⟶ Z) :
    (smallEtaleRingedToposHom B S hS Z.hom).fSharp ≫ pushforwardRingMap B S hS f =
      (smallEtaleRingedToposHom B S hS Y.hom).fSharp :=
  (fSharp_comp_compRingIso B S hS f.left Z.hom
      (eqToHom (congrArg
        (fun q : Y.left ⟶ X =>
          (pushforwardCommRingFunctor
            (smallEtaleRingedToposHom B S hS q).toToposHom).obj
              (smallEtaleRingedTopos B S hS Y.left).O)
        (Over.w f)))).trans
    (pushforwardCommRingFunctor_fSharp_comp_eqToHom B S hS (Over.w f))

/-- **The contravariant action of `f ↦ f_* 𝒪_Y` on morphisms, as a morphism of
`𝒪_X`-algebras.**  A morphism `f : Y ⟶ Z` of algebraic spaces over `X` induces
`f_* : Z.hom_* 𝒪_Z ⟶ Y.hom_* 𝒪_Y`, and that map of sheaves of commutative rings carries the
structure-algebra map of the first to the structure-algebra map of the second.

This is one piece of Stacks 081V: the functor of the anti-equivalence on morphisms.  It is
functorial, by `AlgebraicGeometry.Space.pushforwardAlgebraMap_id` and
`AlgebraicGeometry.Space.pushforwardAlgebraMap_comp`, and
`AlgebraicGeometry.Space.pushforwardAlgebraFunctor` is the functor they assemble; the
anti-equivalence itself is not constructed, see the implementation notes of this file. -/
@[stacks 081V "the direct image f ↦ f_* 𝒪_Y on morphisms, as a map of 𝒪_X-algebras"]
def pushforwardAlgebraMap (f : Y ⟶ Z) :
    pushforwardAlgebra B S hS Z ⟶ pushforwardAlgebra B S hS Y where
  right := pushforwardRingMap B S hS f
  comm U r :=
    ConcreteCategory.congr_hom
      (commRingSheafHom_app_congr (fSharp_comp_pushforwardRingMap B S hS f) U) r

/-- The morphism of algebra sheaves induced by a morphism over `X` is
`AlgebraicGeometry.Space.pushforwardRingMap` on underlying sheaves of rings. -/
@[simp]
theorem pushforwardAlgebraMap_right (f : Y ⟶ Z) :
    (pushforwardAlgebraMap B S hS f).right = pushforwardRingMap B S hS f :=
  rfl

/-- `AlgebraicGeometry.Space.pushforwardRingMap` is the direct-image map of the underlying
morphism of algebraic spaces over the structure morphism of the target, followed by the
transport along `CategoryTheory.Over.w`.  This is the definition with its last factor split
off, so the composition law can be proved with the transport handled once. -/
theorem pushforwardRingMap_eq (f : Y ⟶ Z) :
    pushforwardRingMap B S hS f =
      pushforwardAlgMap B S hS f.left Z.hom ≫
        eqToHom (congrArg
          (fun q : Y.left ⟶ X =>
            (pushforwardCommRingFunctor
              (smallEtaleRingedToposHom B S hS q).toToposHom).obj
                (smallEtaleRingedTopos B S hS Y.left).O)
          (Over.w f)) :=
  comp_assoc₄
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS Z.hom).toToposHom).map
      (smallEtaleRingedToposHom B S hS f.left).fSharp)
    ((pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f.left).toToposHom
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom
        (smallEtaleRingedTopos B S hS Y.left).O).hom)
    ((smallEtaleRingedToposHom_compRingIso B S hS f.left Z.hom).hom.app
      (smallEtaleRingedTopos B S hS Y.left).O)
    (eqToHom (congrArg
      (fun q : Y.left ⟶ X =>
        (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS Y.left).O)
      (Over.w f)))

/-- Bookkeeping for the three transports in the composition law of the direct-image map: if `e`
commutes past `c` to `c'` up to the transport `e'`, and `e''` is `e'` followed by `e₂`, then
`(a ≫ c') ≫ e'' = (a ≫ e) ≫ c ≫ e₂`. -/
private theorem comp_eqToHom_comp_aux {D : Type*} [Category D] {N M M' L L' L'' : D}
    (a : N ⟶ M) (e : M ⟶ M') (c : M' ⟶ L) (e₂ : L ⟶ L') (c' : M ⟶ L'') (e' : L'' ⟶ L)
    (e'' : L'' ⟶ L') {m : N ⟶ L''} (h : e ≫ c = c' ≫ e') (h' : e'' = e' ≫ e₂)
    (hm : a ≫ c' = m) : m ≫ e'' = (a ≫ e) ≫ c ≫ e₂ := by
  subst h' hm
  simp [reassoc_of% h]

/-- The composition law for `AlgebraicGeometry.Space.pushforwardAlgMap` with the three transports
along `CategoryTheory.Over.w` in place.  This is
`AlgebraicGeometry.Space.pushforwardRingMap_comp` with every object written out: stated on
`AlgebraicGeometry.Space.pushforwardAlgMap` rather than on
`AlgebraicGeometry.Space.pushforwardRingMap`, whose declared type spells the two direct images
through `AlgebraicGeometry.Space.pushforwardAlgebra`, so that all the steps of the computation
live in one and the same hom-type and `calc` can chain them. -/
theorem pushforwardAlgMap_comp_eqToHom {Y₁ Y₂ Y₃ : Over X} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    pushforwardAlgMap B S hS (f ≫ g).left Y₃.hom ≫ eqToHom (congrArg (fun q : Y₁.left ⟶ X =>
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y₁.left).O) (Over.w (f ≫ g))) =
      (pushforwardAlgMap B S hS g.left Y₃.hom ≫ eqToHom (congrArg (fun q : Y₂.left ⟶ X =>
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y₂.left).O) (Over.w g))) ≫ (pushforwardAlgMap B S hS f.left
        Y₂.hom ≫ eqToHom (congrArg (fun q : Y₁.left ⟶ X => (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS q).toToposHom).obj (smallEtaleRingedTopos B S hS
        Y₁.left).O) (Over.w f))) := by
  exact comp_eqToHom_comp_aux _ _ _ _ _ _ _
    (eqToHom_comp_pushforwardAlgMap B S hS f.left (Over.w g)) (eqToHom_trans _ _).symm
    (pushforwardAlgMap_comp B S hS f.left g.left Y₃.hom)

/-- **Compatibility of the direct-image map with composition, on sheaves of commutative
rings.**  The map which `AlgebraicGeometry.Space.pushforwardRingMap` attaches to a composite of
morphisms over `X` is the composite, in the other order, of the two maps it attaches to the
factors.

The content is `AlgebraicGeometry.Space.pushforwardAlgMap_comp`; what
`AlgebraicGeometry.Space.pushforwardAlgMap_comp_eqToHom` adds is the bookkeeping of the three
transports along `CategoryTheory.Over.w`, and what is left here is to split the transport off
each of the three maps by `AlgebraicGeometry.Space.pushforwardRingMap_eq`. -/
theorem pushforwardRingMap_comp {Y₁ Y₂ Y₃ : Over X} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    pushforwardRingMap B S hS (f ≫ g) =
      pushforwardRingMap B S hS g ≫ pushforwardRingMap B S hS f :=
  (pushforwardRingMap_eq B S hS (f ≫ g)).trans
    ((pushforwardAlgMap_comp_eqToHom B S hS f g).trans
      (congrArg₂ (fun p q => p ≫ q) (pushforwardRingMap_eq B S hS g)
        (pushforwardRingMap_eq B S hS f)).symm)

/-- **Compatibility of the direct-image algebra map with composition.**  A morphism of
`AlgebraicGeometry.Space.AlgebraSheaf` is determined by its underlying morphism of sheaves of
rings, so this is `AlgebraicGeometry.Space.pushforwardRingMap_comp`. -/
theorem pushforwardAlgebraMap_comp {Y₁ Y₂ Y₃ : Over X} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    pushforwardAlgebraMap B S hS (f ≫ g) =
      pushforwardAlgebraMap B S hS g ≫ pushforwardAlgebraMap B S hS f :=
  AlgebraSheaf.Hom.ext (pushforwardRingMap_comp B S hS f g)

/-- The direct-image map of a morphism over `X` whose structure map is an isomorphism is an
isomorphism.  This is `AlgebraicGeometry.Space.isIso_pushforwardAlgMap` with the transport
along `CategoryTheory.Over.w`, which is an `CategoryTheory.eqToHom`, put back. -/
theorem isIso_pushforwardRingMap (f : Y ⟶ Z)
    (ha : IsIso (smallEtaleRingedToposHom B S hS f.left).fSharp) :
    IsIso (pushforwardRingMap B S hS f) := by
  have hm : IsIso (pushforwardAlgMap B S hS f.left Z.hom) :=
    isIso_pushforwardAlgMap B S hS f.left Z.hom ha
  rw [pushforwardRingMap_eq B S hS f]
  exact IsIso.comp_isIso' hm (inferInstance : IsIso (eqToHom (congrArg
    (fun q : Y.left ⟶ X =>
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y.left).O)
    (Over.w f))))

/-- **The direct-image map of an identity is the identity.**  By
`AlgebraicGeometry.Space.pushforwardRingMap_comp` the map attached to `𝟙 Y` is idempotent, and
`AlgebraicGeometry.Space.isIso_pushforwardRingMap` together with the identity clause of
Stacks 03G8, `AlgebraicGeometry.Space.isIso_fSharp_id`, makes it an isomorphism.  An idempotent
isomorphism is the identity. -/
theorem pushforwardRingMap_id (Y : Over X) :
    pushforwardRingMap B S hS (𝟙 Y) = 𝟙 (pushforwardAlgebra B S hS Y).right := by
  have : IsIso (pushforwardRingMap B S hS (𝟙 Y)) :=
    isIso_pushforwardRingMap B S hS (𝟙 Y) (isIso_fSharp_id B S hS Y.left)
  exact (cancel_mono (pushforwardRingMap B S hS (𝟙 Y))).mp
    (((pushforwardRingMap_comp B S hS (𝟙 Y) (𝟙 Y)).symm.trans
        (congrArg (fun m : Y ⟶ Y => pushforwardRingMap B S hS m)
          (Category.comp_id (𝟙 Y)))).trans
      (Category.id_comp (pushforwardRingMap B S hS (𝟙 Y))).symm)

/-- **The direct-image algebra map of an identity is the identity.**  A morphism of
`AlgebraicGeometry.Space.AlgebraSheaf` is determined by its underlying morphism of sheaves of
rings, so this is `AlgebraicGeometry.Space.pushforwardRingMap_id`. -/
theorem pushforwardAlgebraMap_id (Y : Over X) :
    pushforwardAlgebraMap B S hS (𝟙 Y) = 𝟙 (pushforwardAlgebra B S hS Y) :=
  AlgebraSheaf.Hom.ext (pushforwardRingMap_id B S hS Y)

end Morphisms

/-! ### The direct-image functor -/

section Functor

variable (X : AlgebraicSpaces B S hS)

/-- **The direct-image functor of Stacks 081V.**  The contravariant functor from the algebraic
spaces over `X` to the sheaves of commutative `𝒪_X`-algebras which sends `f : Y ⟶ X` to
`f_* 𝒪_Y` and a morphism over `X` to the map it induces on direct images.

This is the functor of Stacks 081V on the whole over-category rather than on
`AlgebraicGeometry.Space.AffineOver X`, and with values in all algebra sheaves rather than in
`AlgebraicGeometry.Space.QuasicoherentAlgebra X`: quasi-coherence of `f_* 𝒪_Y` for a
quasi-compact, quasi-separated `f` is Stacks 03M9, which is stated nowhere in this development,
so restricting the codomain is not available.  It is *not* shown to be an anti-equivalence; see
the implementation notes of this file. -/
@[stacks 081V "the direct image functor f ↦ f_* 𝒪_Y"]
noncomputable def pushforwardAlgebraFunctor :
    (Over X)ᵒᵖ ⥤ AlgebraSheaf.{u, u} B S hS X.1 X.2 where
  obj Y := pushforwardAlgebra B S hS Y.unop
  map f := pushforwardAlgebraMap B S hS f.unop
  map_id Y := pushforwardAlgebraMap_id B S hS Y.unop
  map_comp f g := pushforwardAlgebraMap_comp B S hS g.unop f.unop

/-- The direct-image functor restricted to the algebraic spaces *affine* over `X`, which is the
source category of the anti-equivalence asserted by Stacks 081V. -/
noncomputable def affinePushforwardAlgebraFunctor :
    (AffineOver B S hS X)ᵒᵖ ⥤ AlgebraSheaf.{u, u} B S hS X.1 X.2 :=
  (ObjectProperty.ι (fun f : Over X => IsAffineHom B S hS f.hom.hom)).op ⋙
    pushforwardAlgebraFunctor B S hS X

end Functor

/-! ### The comparison of a commutative square -/

section Squares

variable {X Y : AlgebraicSpaces B S hS}

/-- `g_* (f'_* 𝒪_W)` as an `𝒪_X`-algebra, for `g : Y ⟶ X` and `f' = W.hom` the structure
morphism of an algebraic space `W` over `Y`: the structure map of `g`, followed by the direct
image along `g` of the structure map of `f'`.  This is the target of the comparison attached to
a commutative square over `g`. -/
def pushforwardSquareAlgebra (g : Y ⟶ X) (W : Over Y) : AlgebraSheaf.{u, u} B S hS X.1 X.2 :=
  AlgebraSheaf.ofHom ((smallEtaleRingedToposHom B S hS g).fSharp ≫
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
      (smallEtaleRingedToposHom B S hS W.hom).fSharp)

/-- The structure-algebra map of `f_* 𝒪_Z`, followed by the comparison attached to a
commutative square over `g : Y ⟶ X`, is the structure-algebra map of `g_* (f'_* 𝒪_W)`.  So the
square comparison respects the algebra structures.

The proof is Stacks 03G8's composition law twice: forwards for the top projection `p` over `X`,
and backwards for the factorization of `W.hom ≫ g` through `Y`, with the transport along the
commutativity `hw` of the square in between. -/
theorem fSharp_comp_pushforwardSquareMap (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g) :
    (smallEtaleRingedToposHom B S hS Z.hom).fSharp ≫
        pushforwardSquareMap B S hS g Z W p hw =
      (smallEtaleRingedToposHom B S hS g).fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
          (smallEtaleRingedToposHom B S hS W.hom).fSharp :=
  ((fSharp_comp_compRingIso B S hS p Z.hom
          (eqToHom (congrArg
              (fun q : W.left ⟶ X =>
                (pushforwardCommRingFunctor
                  (smallEtaleRingedToposHom B S hS q).toToposHom).obj
                    (smallEtaleRingedTopos B S hS W.left).O) hw) ≫
            (smallEtaleRingedToposHom_compRingIso B S hS W.hom g).inv.app
                (smallEtaleRingedTopos B S hS W.left).O ≫
              (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS W.hom).toToposHom
                (smallEtaleRingedToposHom B S hS g).toToposHom
                (smallEtaleRingedTopos B S hS W.left).O).inv)).trans
      (pushforwardCommRingFunctor_fSharp_comp_eqToHom_comp B S hS hw
        ((smallEtaleRingedToposHom_compRingIso B S hS W.hom g).inv.app
            (smallEtaleRingedTopos B S hS W.left).O ≫
          (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS W.hom).toToposHom
            (smallEtaleRingedToposHom B S hS g).toToposHom
            (smallEtaleRingedTopos B S hS W.left).O).inv))).trans
    (fSharp_comp_compRingIso_inv B S hS W.hom g)

end Squares

end AlgebraicGeometry.Space

end
