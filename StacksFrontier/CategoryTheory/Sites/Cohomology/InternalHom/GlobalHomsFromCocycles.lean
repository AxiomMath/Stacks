module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturalityDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsFromAKFlatSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv

/-! # Degree-zero global hypercohomology of the derived internal Hom, at a morphism of complexes

Let `(C, O)` be a ringed site, let `A` be a complex of `O`-modules and let `I` be a K-injective
complex of `O`-modules.  Stacks 0A94 identifies the degree-zero cohomology of the global sections
of the internal Hom complex `SheafHom(A, I)` with `Hom_{D(O)}(A, I)`, and Stacks 08JA identifies
the degree-zero global hypercohomology of the derived internal Hom `RSheafHom(QA, QI)` with the
same group.  Both identifications are built out of resolutions and comparison isomorphisms, and
neither comes with a description of what it does to the class of a *morphism of complexes*.

This file supplies that description.  A degree-zero global cohomology class of `SheafHom(A, M)`
is a cohomology class of degree-zero cocycles from `A` to `M`
(`AlgebraicGeometry.RingedSite.globalCohomologyClassEquiv`), hence in particular a morphism of
complexes `f : A ⟶ M` has a class
(`AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom`); and the two identifications above
send that class to `DerivedCategory.Q.map f`.  At `f = 𝟙 I` they therefore send it to the
identity of `Q I`: the *cocycle* reading of the identity and the *hypercohomology* reading of the
identity agree.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalCohomologyClassEquiv`: the degree-`n` cohomology of the
  global sections of `SheafHom(L, M)`, read as the group of degree-`n` cohomology classes of
  cocycles from `L` to `M`.  This is the cocycle description that the cochain-level currying
  bijection of Tag 0A90 is stated at.
* `AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom`: the degree-zero global cohomology
  class of `SheafHom(L, M)` attached to a morphism of complexes `L ⟶ M`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsModelEquiv`: the three comparisons
  out of which Stacks 08JA is built at a K-injective internal Hom complex, assembled as the
  identification of the degree-zero global hypercohomology of `RSheafHom(QA, QI)` with the
  degree-zero cohomology of the global sections of `SheafHom(A, I)`.
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsClassOfHom` and
  `AlgebraicGeometry.RingedSite.derivedGlobalSectionsClassOfHomOfKFlat`: the degree-zero global
  hypercohomology class of `RSheafHom(QA, QI)` attached to a morphism of complexes `A ⟶ I`.
* `AlgebraicGeometry.RingedSite.curryHomComplexMap`: currying of cochains as a morphism of Hom
  complexes of abelian groups, the *unlifted* form of
  `AlgebraicGeometry.RingedSite.curryGlobalIso`.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_eq_Q_map`: **Stacks
  0A94 globally, at the class of a cocycle, is a single `DerivedCategory.Q.map`** — the global
  counterpart of
  `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ`.
* `RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_globalCohomologyClassOfHom`
  and `…_id`: Stacks 0A94 globally sends the class of a morphism of complexes to its image under
  the localisation functor, and the class of the identity to the identity.
* `RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_derivedGlobalSectionsClassOfHom`
  and `…_id`, and
  `RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_derivedGlobalSectionsClassOfHomOfKFlat`:
  **the same for Stacks 08JA**, at a K-injective internal Hom complex and at a K-flat source.
* `AlgebraicGeometry.RingedSite.map_curryHomComplexMap`: the universe lift of `curryHomComplexMap`
  is `curryGlobalIso`, which pays the universe-lift crossing of the currying step once, at the
  level where it is `rfl`.
* `AlgebraicGeometry.RingedSite.homologyAddEquiv_curryHomComplexMap`: the cocycle description
  carries the map induced on homology by `curryHomComplexMap` to the currying of cocycles
  `AlgebraicGeometry.RingedSite.curryCocycleEquiv`.
* `AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom_curryHomEquiv`: **the cocycle
  description carries the cochain-level currying of Tag 0A90 to the currying bijection of
  morphism groups** `AlgebraicGeometry.RingedSite.curryHomEquiv`.

## Nothing here is tagged

Stacks 0A94 and Stacks 08JA each assert an identification of groups and make no claim about what
that identification does to the class of a morphism of complexes; their clauses already carry
their tags, at `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom` and
at `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom`'s published
form `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`.  Everything below is a
step of the proof of Tag 0GM7, so no declaration here carries a tag — the same reason the local
counterpart
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ` carries
none.

## What this unblocks, and what is still owed to Tag 0GM7

The module note of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv` records the last
square owed to Tag 0GM7 and records that proving it needs one further input: the identification
of Stacks 08JA, which is about a *quotient* — degree-zero global hypercohomology — read against
the degree-zero global *cocycle* description that
`AlgebraicGeometry.RingedSite.curryHomEquiv` is stated at.  That input is what this file is:
`globalCohomologyClassEquiv` is the cocycle description, and the results above say that both
Stacks 0A94 and Stacks 08JA read the class of a morphism of complexes as that morphism, so in
particular the two readings of `𝟙` agree.

The step between here and that square is about the *currying* rather than about the identity: the
cocycle description has to carry the cochain-level currying of Tag 0A90 to
`AlgebraicGeometry.RingedSite.curryHomEquiv`.  That is
`AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom_curryHomEquiv` below, and it is now
proved, so nothing on the cocycle side is owed to Tag 0GM7 any more.

The obstruction there was not the mathematics but the universe lift.  `globalSectionsIso` lands in
`AddCommGrpCat.uliftFunctor.mapHomologicalComplex` of the Hom complex, so
`AlgebraicGeometry.RingedSite.curryGlobalIso` is a morphism *between lifted* Hom complexes which
is not syntactically `AddCommGrpCat.uliftFunctor.map` of anything, and
`AlgebraicGeometry.RingedSite.ulift_mapHomologyIso_naturality` — the only lemma in the tree that
pushes the lift past `homologyMap` — therefore does not apply to it.  That crossing is paid
here, once and at the level where it is `rfl`:
`AlgebraicGeometry.RingedSite.curryHomComplexMap` is the *unlifted* morphism of Hom complexes
whose degree-`n` component is
`AlgebraicGeometry.RingedSite.curryCochainEquiv` — its commutation with the differentials being
exactly `AlgebraicGeometry.RingedSite.curryCochainEquiv_delta` — and
`AlgebraicGeometry.RingedSite.map_curryHomComplexMap` identifies its universe lift with
`(curryGlobalIso X A B D).hom`.

The other half of that statement is about cohomology classes rather than about universes:
`CochainComplex.HomComplex.homologyAddEquiv` has to carry the map induced on homology by
`curryHomComplexMap` to `AlgebraicGeometry.RingedSite.curryCocycleEquiv` on classes of cocycles.
That is `AlgebraicGeometry.RingedSite.homologyAddEquiv_curryHomComplexMap`, the exact analogue
for currying of `CochainComplex.HomComplex.homologyAddEquiv_conj` for `homComplexConj`, and it is
proved the same way: `CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom` turns
`curryCocycleEquiv` into a map of cohomology classes — this is
`AlgebraicGeometry.RingedSite.curryCohomologyClassMap` — once `curryCocycleEquiv` is known to
carry coboundaries to coboundaries
(`CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff`), and the class of a cycle is computed
by `CochainComplex.HomComplex.homologyAddEquiv_homologyπ` and
`CochainComplex.HomComplex.homologyAddEquiv_homologyMap` — the latter applicable because
`curryHomComplexMap` lands in an unlifted Hom complex.

## What is still owed to Tag 0GM7

The square itself, in `DerivedCategory (StructureSheafModules Rc)`, as displayed in the module
note of `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv`: that the
derived evaluation of Stacks 08DI, conjugated by the comparison of Stacks 08DM and the K-flat
comparison of Stacks 06YU, is `DerivedCategory.Q` of the cochain-level evaluation
`AlgebraicGeometry.RingedSite.cochainEvaluation`.  Nothing on the cocycle side of it is owed any
more, and the two reductions to a value at an identity are both available —
`Stacks.SheafOfModules.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation` on the derived side
and `AlgebraicGeometry.RingedSite.curryHomEquiv_eq_tensor_evaluation` on the cochain side — as is
the comparison of the two currying isomorphisms themselves,
`Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedCurryIso`.

**The comparison of the two models.**  Stacks 08DI's bijection
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` is defined through
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, which is Stacks 08JA at the
*chosen* K-flat and K-injective models of its two arguments, whereas the value at the class of a
morphism of complexes is known for
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat`, which is Stacks 08JA at
the complexes themselves — the statement above.  That these two agree at a *given* K-flat complex
and a *given* K-injective complex is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply_of_isKFlat`, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsAgreement`, with
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat` the same statement
read as an equality of the two bijections.  It is a statement and not a definitional unfolding,
the chosen models being different complexes.

Its only inputs are the two naturalities of the *OfKFlat* form against the two legs comparing the
pairs of representatives, and both are now public: in the target
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_target`, and
in the source
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_source`.
The latter was the obstruction this note described, and it was one of *visibility* rather than of
mathematics: the clause was proved only as a `private` lemma with a `private` statement, so that
only the model-based
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source` was exported,
and the agreement cannot be bootstrapped from that one.

## Implementation notes

*Why the hypothesis of `sheafHomGlobalHomologyEquivDerivedCategoryHom_eq_Q_map` is stated on the
class rather than on a cycle.*  The local counterpart
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ` takes a
degree-zero *cycle* of the section complex and a cocycle agreeing with its image, and converts
the one into the other with
`CochainComplex.HomComplex.homologyAddEquiv_homologyMap`.  That lemma is stated for a morphism
into an *unlifted* Hom complex and so is unavailable globally, for the reason recorded above.
Taking the hypothesis on the cohomology class instead costs nothing — `globalCohomologyClassEquiv`
is an isomorphism, so the hypothesis determines the class and is determined by it — and it is the
form in which the result is used, since the classes a consumer has in hand come from morphisms of
complexes and not from chosen cycles.

*`globalCohomologyClassEquiv` is assembled so that its action is the composite appearing in
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom_eq`*, which is why
`globalCohomologyClassEquiv_apply` is `rfl` and why the proof below can rewrite with it
backwards.  The same four factors assemble
`AlgebraicGeometry.RingedSite.sheafHomComplexHomologyEquivHomotopyCategory`, Stacks 0A8Z, whose
remaining factor is `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`.

*`derivedSheafHomGlobalSectionsModelEquiv` is the first factor of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom` written out*, so
that `derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_eq` holds by `rfl` and the Stacks 08JA
statements are the Stacks 0A94 ones transported along a named isomorphism.  The K-flat form is
then the K-injective-internal-Hom form at the instance
`Stacks.SheafOfModules.isKInjective_sheafHomComplex_of_isKFlat` supplies, which is how
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat` is defined.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The cocycle description of degree-zero global cohomology -/

/-- **The degree-`n` cohomology of the global sections of `SheafHom(L, M)`, as cohomology classes
of cocycles.**  The global description of the internal Hom complex of Tag 0A8Z identifies the
global sections of `SheafHom(L, M)` with the universe lift of the Hom complex `Hom^•(L, M)`, and
the degree-`n` cohomology of a Hom complex is the group of degree-`n` cohomology classes of
cocycles.

This is the first four factors of
`AlgebraicGeometry.RingedSite.sheafHomComplexHomologyEquivHomotopyCategory`, stopping before the
passage to the homotopy category. -/
def globalCohomologyClassEquiv
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n ≃+
      CohomologyClass L M n :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
        (sheafHomComplex X L M).globalSectionsIso).addCommGroupIsoToAddEquiv.trans
    ((uliftHomologyIso (L.HomComplex M) n).addCommGroupIsoToAddEquiv.trans
      (AddEquiv.ulift.trans (homologyAddEquiv L M n)))

/-- `globalCohomologyClassEquiv` acts by pushing a class along the global description of the
internal Hom complex, stripping the universe lift, and reading the result as a class of
cocycles.  This is its definition, recorded so that a consumer can see that no other map is
involved — and it is the composite that occurs in
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom_eq`. -/
theorem globalCohomologyClassEquiv_apply
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n) :
    globalCohomologyClassEquiv X L M n η =
      homologyAddEquiv L M n
        (AddEquiv.ulift ((uliftHomologyIso (L.HomComplex M) n).hom
          (HomologicalComplex.homologyMap
            (sheafHomComplex X L M).globalSectionsIso.hom n η))) :=
  rfl

/-- **The degree-zero global cohomology class of `SheafHom(L, M)` attached to a morphism of
complexes.**  A morphism `f : L ⟶ M` is a degree-zero cocycle, and
`globalCohomologyClassEquiv` identifies the cohomology classes of those with the degree-zero
cohomology of the global sections of `SheafHom(L, M)`. -/
def globalCohomologyClassOfHom
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : L ⟶ M) :
    (globalSectionsComplex X (sheafHomComplex X L M).obj).homology 0 :=
  (globalCohomologyClassEquiv X L M 0).symm (CohomologyClass.mk (Cocycle.ofHom f))

/-- The class of a morphism of complexes is read by the cocycle description as the class of the
cocycle that morphism is. -/
theorem globalCohomologyClassEquiv_globalCohomologyClassOfHom
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : L ⟶ M) :
    globalCohomologyClassEquiv X L M 0 (globalCohomologyClassOfHom X L M f) =
      CohomologyClass.mk (Cocycle.ofHom f) :=
  (globalCohomologyClassEquiv X L M 0).apply_symm_apply _

section Global

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Stacks 0A94 globally, at the class of a cocycle -/

/-- **Stacks 0A94 globally, at the class of a cocycle, is a single `DerivedCategory.Q.map`.**  Let
`η` be a degree-zero global cohomology class of the internal Hom complex from `L` to a K-injective
`I`, and let `x` be the degree-zero cocycle from `L` to `I` whose class the cocycle description
attaches to `η`.  Then the identification of Stacks 0A94 sends `η` to the image under the
localisation functor of the morphism of complexes `L ⟶ I` that `x` names.

This is the global counterpart of
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ`: all five
steps of the identification collapse into this one, the two ingredients being that
`CochainComplex.HomComplex.Cocycle.equivHomShift` composed with the degree-zero shift
normalisation is `CochainComplex.HomComplex.Cocycle.homOf`, and that
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv` is the identity on morphisms coming
from the homotopy category. -/
theorem sheafHomGlobalHomologyEquivDerivedCategoryHom_eq_Q_map
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0)
    (x : Cocycle L I 0) (hx : globalCohomologyClassEquiv X L I 0 η = CohomologyClass.mk x) :
    sheafHomGlobalHomologyEquivDerivedCategoryHom X L I η =
      DerivedCategory.Q.map (Cocycle.homOf x) := by
  rw [sheafHomGlobalHomologyEquivDerivedCategoryHom_apply X L I η,
    sheafHomGlobalHomotopyCategoryHom_eq X L I η, ← globalCohomologyClassEquiv_apply, hx,
    CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk]
  refine (congrArg (fun θ => homotopyHomDerivedCategoryEquiv L I θ) ?_).trans
    (homotopyHomDerivedCategoryEquiv_quotient_map (Cocycle.homOf x))
  rw [Category.id_comp, ← Functor.map_comp]
  exact congrArg _ (Cocycle.equivHomShift_symm_comp_shiftFunctorZero x)

/-- **Stacks 0A94 globally reads the class of a morphism of complexes as that morphism.**  For a
morphism of complexes `f : L ⟶ I` into a K-injective `I`, the identification of Stacks 0A94 sends
the degree-zero global cohomology class of `SheafHom(L, I)` attached to `f` to
`DerivedCategory.Q.map f`. -/
theorem sheafHomGlobalHomologyEquivDerivedCategoryHom_globalCohomologyClassOfHom
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (f : L ⟶ I) :
    sheafHomGlobalHomologyEquivDerivedCategoryHom X L I
        (globalCohomologyClassOfHom X L I f) = DerivedCategory.Q.map f :=
  (sheafHomGlobalHomologyEquivDerivedCategoryHom_eq_Q_map X L I _ (Cocycle.ofHom f)
    (globalCohomologyClassEquiv_globalCohomologyClassOfHom X L I f)).trans
      (congrArg DerivedCategory.Q.map (Cocycle.homOf_ofHom_eq_self f))

/-- **The two readings of the identity agree, for Stacks 0A94.**  The degree-zero global
cohomology class of `SheafHom(I, I)` attached to the identity morphism of complexes is carried by
the identification of Stacks 0A94 to the identity of `Q I`. -/
theorem sheafHomGlobalHomologyEquivDerivedCategoryHom_globalCohomologyClassOfHom_id
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    sheafHomGlobalHomologyEquivDerivedCategoryHom X I I
        (globalCohomologyClassOfHom X I I (𝟙 I)) = 𝟙 (DerivedCategory.Q.obj I) :=
  (sheafHomGlobalHomologyEquivDerivedCategoryHom_globalCohomologyClassOfHom X I I (𝟙 I)).trans
    (DerivedCategory.Q.map_id I)

/-! ### Stacks 08JA, at the class of a morphism of complexes -/

/-- **The comparison out of which Stacks 08JA is built at a K-injective internal Hom complex.**
If `I` and `SheafHom(A, I)` are K-injective then the degree-zero global hypercohomology of the
derived internal Hom `RSheafHom(QA, QI)` is the degree-zero cohomology of the global sections of
`SheafHom(A, I)`: the derived internal Hom is the class of the internal Hom complex because the
target is K-injective, and global sections compute derived global sections on a K-injective
complex.

This is the first factor of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom`, written out so
that it can be named. -/
def derivedSheafHomGlobalSectionsModelEquiv
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I))) : Type u) ≃+
      (globalSectionsComplex X (sheafHomComplex X A I).obj).homology 0 :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        ((derivedModuleGlobalSections X).mapIso (derivedSheafHomComparison X A I) ≪≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).symm) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
        (globalSectionsComplex X (sheafHomComplex X A I).obj)).addCommGroupIsoToAddEquiv

/-- Stacks 08JA at a K-injective internal Hom complex is the comparison with the global sections
of that complex followed by Stacks 0A94.  This is its definition. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_eq
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I =
      (derivedSheafHomGlobalSectionsModelEquiv X A I).trans
        (sheafHomGlobalHomologyEquivDerivedCategoryHom X A I) :=
  rfl

/-- **The degree-zero global hypercohomology class of `RSheafHom(QA, QI)` attached to a morphism
of complexes `A ⟶ I`**, for `I` and `SheafHom(A, I)` K-injective: the class of that morphism in
the global sections of the internal Hom complex, transported along the comparison
`derivedSheafHomGlobalSectionsModelEquiv`. -/
def derivedGlobalSectionsClassOfHom
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] (f : A ⟶ I) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u) :=
  (derivedSheafHomGlobalSectionsModelEquiv X A I).symm (globalCohomologyClassOfHom X A I f)

/-- **Stacks 08JA reads the class of a morphism of complexes as that morphism**, at a K-injective
internal Hom complex. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_derivedGlobalSectionsClassOfHom
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] (f : A ⟶ I) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I
        (derivedGlobalSectionsClassOfHom X A I f) = DerivedCategory.Q.map f := by
  rw [derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_eq X A I, AddEquiv.trans_apply,
    derivedGlobalSectionsClassOfHom, AddEquiv.apply_symm_apply,
    sheafHomGlobalHomologyEquivDerivedCategoryHom_globalCohomologyClassOfHom]

/-- **The two readings of the identity agree, for Stacks 08JA.**  The degree-zero global
hypercohomology class of `RSheafHom(QI, QI)` attached to the identity morphism of complexes is
the identity of `Q I`.

This is the statement that the *hypercohomology* reading of `𝟙` — Stacks 08JA, which identifies a
quotient with a group of derived-category morphisms — and the *cocycle* reading of `𝟙` that the
cochain-level currying bijection of Tag 0A90 is stated at agree. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_derivedGlobalSectionsClassOfHom_id
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X I I).obj).IsKInjective] :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X I I
        (derivedGlobalSectionsClassOfHom X I I (𝟙 I)) = 𝟙 (DerivedCategory.Q.obj I) :=
  (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_derivedGlobalSectionsClassOfHom X I I
    (𝟙 I)).trans (DerivedCategory.Q.map_id I)

end Global

/-! ### Stacks 08JA at a K-flat source -/

section KFlat

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The degree-zero global hypercohomology class of `RSheafHom(QA, QI)` attached to a morphism
of complexes `A ⟶ I`**, for `A` K-flat and `I` K-injective.  This is
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsClassOfHom` at the K-injectivity of
`SheafHom(A, I)` that the K-flatness of `A` supplies, which is how
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat` is defined. -/
def derivedGlobalSectionsClassOfHomOfKFlat
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] (f : A ⟶ I) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u) :=
  haveI := isKInjective_sheafHomComplex_of_isKFlat X A I hA
  derivedGlobalSectionsClassOfHom X A I f

/-- **Stacks 08JA reads the class of a morphism of complexes as that morphism**, at a K-flat
source and a K-injective target.  This is the form the dévissage of Tag 0GM7 asks for, the
K-flatness of the source being the hypothesis under which the total tensor complex computes the
derived tensor product. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_derivedGlobalSectionsClassOfHomOfKFlat
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] (f : A ⟶ I) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA
        (derivedGlobalSectionsClassOfHomOfKFlat X A I hA f) = DerivedCategory.Q.map f :=
  have := isKInjective_sheafHomComplex_of_isKFlat X A I hA
  derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_derivedGlobalSectionsClassOfHom X A I f

end KFlat

/-! ### Currying of cochains, unlifted -/

section Currying

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Currying of cochains, as a morphism of Hom complexes of abelian groups**

`Hom^•(A, SheafHom(B, D)) ⟶ Hom^•(Tot(A ⊗_O B), D)`.

Degreewise it is `AlgebraicGeometry.RingedSite.curryCochainEquiv`; that this commutes with the
Hom-complex differentials is `AlgebraicGeometry.RingedSite.curryCochainEquiv_delta`.

This is the *unlifted* form of `AlgebraicGeometry.RingedSite.curryGlobalIso`, which is a morphism
between the universe lifts of these two Hom complexes.  Naming it is what makes the lemmas that
push a universe lift past `homologyMap` —
`AlgebraicGeometry.RingedSite.ulift_mapHomologyIso_naturality` —
and the lemmas that compute a cohomology class out of a morphism into an unlifted Hom complex —
`CochainComplex.HomComplex.homologyAddEquiv_homologyMap` — applicable to the currying step. -/
def curryHomComplexMap :
    A.HomComplex (sheafHomComplex X B D).obj ⟶
      CochainComplex.HomComplex
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D where
  f n := AddCommGrpCat.ofHom (curryCochainEquiv X A B D n).toAddMonoidHom
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact AddCommGrpCat.hom_ext (AddMonoidHom.ext (curryCochainEquiv_delta X A B D i))

/-- **The universe lift of `curryHomComplexMap` is `curryGlobalIso`.**  This is the whole of the
universe-lift crossing of the currying step, paid once and at the level where it is `rfl`: after
it, the currying of cochains may be read on homology through the unlifted Hom complexes. -/
theorem map_curryHomComplexMap :
    (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (curryHomComplexMap X A B D) = (curryGlobalIso X A B D).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ULift.ext _ _ rfl)

/-- **The cocycle a cycle of a Hom complex is the class of.**  This is
`CochainComplex.HomComplex.homologyAddEquiv_homologyπ` with the representative named and its
underlying cochain identified, which is the form
`CochainComplex.HomComplex.homologyAddEquiv_homologyMap` consumes.  Stated over an abstract
category with both complexes variables, so that the identification of the cocycle with the cycle
is one `isDefEq` rather than a rewrite against terms of the size the global Hom complexes
have. -/
private theorem exists_cocycle_of_cycle {E : Type*} [Category E] [Preadditive E]
    (K M : CochainComplex E ℤ) (n : ℤ) (z : ((K.HomComplex M).cycles n)) :
    ∃ x : Cocycle K M n,
      homologyAddEquiv K M n ((K.HomComplex M).homologyπ n z) = CohomologyClass.mk x ∧
        (x : Cochain K M n) =
          AddCommGrpCat.Hom.hom ((K.HomComplex M).iCycles n) z :=
  ⟨(leftHomologyData K M n).cyclesIso.hom z, homologyAddEquiv_homologyπ K M n z,
    ConcreteCategory.congr_hom (leftHomologyData K M n).cyclesIso_hom_comp_i z⟩

/-- **Currying of cocycles, on cohomology classes.**  Currying of cochains commutes with the
Hom-complex differentials (`AlgebraicGeometry.RingedSite.curryCochainEquiv_delta`), so it carries
coboundaries to coboundaries and the bijection of cocycles
`AlgebraicGeometry.RingedSite.curryCocycleEquiv` descends to cohomology classes. -/
def curryCohomologyClassMap (n : ℤ) :
    CohomologyClass A (sheafHomComplex X B D).obj n →+
      CohomologyClass (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ n).comp (curryCocycleEquiv X A B D n).toAddMonoidHom)
    (by
      rintro z ⟨m, hm, β, hβ⟩
      subst hm
      change CohomologyClass.mk (curryCocycleEquiv X A B D _ z) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m rfl]
      exact ⟨curryCochainEquiv X A B D m β,
        (curryCochainEquiv_delta X A B D m β).trans
          (congrArg (curryCochainEquiv X A B D (m + 1)) hβ)⟩)

/-- Currying of cohomology classes is currying of cocycles on the class of a cocycle. -/
@[simp]
theorem curryCohomologyClassMap_mk (n : ℤ) (z : Cocycle A (sheafHomComplex X B D).obj n) :
    curryCohomologyClassMap X A B D n (CohomologyClass.mk z) =
      CohomologyClass.mk (curryCocycleEquiv X A B D n z) :=
  rfl

/-- **The cocycle description carries the currying of cochains to the currying of cocycles.**  The
map induced on homology by `AlgebraicGeometry.RingedSite.curryHomComplexMap` is, read through the
identification `CochainComplex.HomComplex.homologyAddEquiv` of the cohomology of a Hom complex
with cohomology classes of cocycles, the currying of cocycles
`AlgebraicGeometry.RingedSite.curryCocycleEquiv`.

This is the exact analogue, for currying, of
`CochainComplex.HomComplex.homologyAddEquiv_conj` for
`CochainComplex.HomComplex.homComplexConj`, and the hypothesis is taken on the cohomology class
of `η` rather than on a cycle representing it for the same reason as in
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_eq_Q_map`:
`CochainComplex.HomComplex.homologyAddEquiv` is an isomorphism, so the hypothesis both determines
the class and is determined by it. -/
theorem homologyAddEquiv_curryHomComplexMap (n : ℤ)
    (η : (A.HomComplex (sheafHomComplex X B D).obj).homology n)
    (a : Cocycle A (sheafHomComplex X B D).obj n)
    (ha : homologyAddEquiv A (sheafHomComplex X B D).obj n η = CohomologyClass.mk a) :
    homologyAddEquiv (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D n
        (HomologicalComplex.homologyMap (curryHomComplexMap X A B D) n η) =
      CohomologyClass.mk (curryCocycleEquiv X A B D n a) := by
  have hπ : Function.Surjective (ConcreteCategory.hom
      ((A.HomComplex (sheafHomComplex X B D).obj).homologyπ n)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ η
  obtain ⟨a₀, h1, h3⟩ := exists_cocycle_of_cycle A (sheafHomComplex X B D).obj n z
  rw [homologyAddEquiv_homologyMap (curryHomComplexMap X A B D) n z
    (curryCocycleEquiv X A B D n a₀) (congrArg (curryCochainEquiv X A B D n) h3)]
  exact congrArg (curryCohomologyClassMap X A B D n) (h1.symm.trans ha)

/-- **Currying of cocycles at a morphism of complexes is the currying bijection of morphism
groups.**  A morphism of complexes is a degree-zero cocycle, and
`AlgebraicGeometry.RingedSite.curryHomEquiv` is by definition
`AlgebraicGeometry.RingedSite.curryCocycleEquiv` in degree zero, read through that
identification. -/
theorem curryCocycleEquiv_ofHom (f : A ⟶ (sheafHomComplex X B D).obj) :
    curryCocycleEquiv X A B D 0 (Cocycle.ofHom f) =
      Cocycle.ofHom (curryHomEquiv X A B D f) :=
  (Cocycle.ofHom_homOf_eq_self _).symm

/-- **The cocycle description carries the cochain-level currying of Tag 0A90 to the currying
bijection of morphism groups.**  Let `f : A ⟶ SheafHom(B, D)` be a morphism of complexes.  The
degree-zero global cohomology class of `SheafHom(Tot(A ⊗_O B), D)` attached to the transpose
`AlgebraicGeometry.RingedSite.curryHomEquiv` of `f` is the image of the class attached to `f`
under the map induced on homology by the global sections of the isomorphism of Tag 0A90.

Both the universe lift of the currying step and the passage from a cycle to a cohomology class
are paid once here, by `AlgebraicGeometry.RingedSite.map_curryHomComplexMap` and
`AlgebraicGeometry.RingedSite.homologyAddEquiv_curryHomComplexMap` respectively. -/
theorem globalCohomologyClassOfHom_curryHomEquiv (f : A ⟶ (sheafHomComplex X B D).obj) :
    globalCohomologyClassOfHom X
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D
        (curryHomEquiv X A B D f) =
      HomologicalComplex.homologyMap
        (globalSectionsComplexMap X (sheafHomTensorCurryIso X A B D).hom) 0
        (globalCohomologyClassOfHom X A (sheafHomComplex X B D).obj f) := by
  have hsq : globalSectionsComplexMap X (sheafHomTensorCurryIso X A B D).hom ≫
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
          D).globalSectionsIso.hom =
      (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso.hom ≫
        (curryGlobalIso X A B D).hom := by
    rw [curryGlobalIso_hom, Iso.hom_inv_id_assoc]
  have key : HomologicalComplex.homologyMap
        (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
          D).globalSectionsIso.hom 0
          (HomologicalComplex.homologyMap
            (globalSectionsComplexMap X (sheafHomTensorCurryIso X A B D).hom) 0
              (globalCohomologyClassOfHom X A (sheafHomComplex X B D).obj f)) =
      HomologicalComplex.homologyMap
        ((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (curryHomComplexMap X A B D)) 0
        (HomologicalComplex.homologyMap
          (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso.hom 0
            (globalCohomologyClassOfHom X A (sheafHomComplex X B D).obj f)) := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      ← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      map_curryHomComplexMap, hsq]
  have ha : homologyAddEquiv A (sheafHomComplex X B D).obj 0
      (AddEquiv.ulift ((uliftHomologyIso (A.HomComplex (sheafHomComplex X B D).obj) 0).hom
        (HomologicalComplex.homologyMap
          (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso.hom 0
            (globalCohomologyClassOfHom X A (sheafHomComplex X B D).obj f)))) =
      CohomologyClass.mk (Cocycle.ofHom f) :=
    globalCohomologyClassEquiv_globalCohomologyClassOfHom X A (sheafHomComplex X B D).obj f
  apply (globalCohomologyClassEquiv X
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) D 0).injective
  rw [globalCohomologyClassEquiv_globalCohomologyClassOfHom, globalCohomologyClassEquiv_apply,
    key, ulift_mapHomologyIso_naturality,
    homologyAddEquiv_curryHomComplexMap X A B D 0 _ (Cocycle.ofHom f) ha,
    curryCocycleEquiv_ofHom]

end Currying

end AlgebraicGeometry.RingedSite

end
