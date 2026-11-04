module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedForgetful
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.DGFunctorAdmissible
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.Functor.Derived.ValueIsPointwise

/-!
# Derived Hom out of a complex, with values in differential graded modules

Let `B` be a preadditive category and let `K` be a cochain complex in `B`. The complexes in `B`
are the objects of a differential graded category over `ℤ` (Tag 09L9), and the endomorphisms of
`K` in it form a differential graded algebra `E = End(K)` such that `Hom(K, -)` takes values in
differential graded `E`-modules (Tag 09LE). Composing the comparison of `K(B)` with the homotopy
category of that differential graded category, the functor `Hom(K, -)` of Tag 09LE, and the
localization at the quasi-isomorphisms gives
`RHom(K, -)`'s *underlying* functor `K(B) ⥤ D(E, d)`, the functor whose right derived functor is
Tag 09LK.

The main clause of the tag is the functor itself, and it is constructed here: for `A` abelian
with a chosen derived category, the corrected derivability hypothesis produces the canonical
functor
`R Hom(K, -) : D(A) ⥤ D(E, d)`
as a left Kan extension of `Hom(K, -) : K(A) ⥤ D(E, d)` along the localization `K(A) ⥤ D(A)`,
together with its canonical comparison and the universal property that pins it down.

Two further clauses are unconditional.

The first is the half of the source's first step that needs no cone axioms: `Hom(K, -)` carries
an admissible short exact sequence of complexes to an admissible short exact sequence of
differential graded `E`-modules, with the two closed arrows the images of the given ones and the
connecting morphism `π d(s)` the image of the given connecting morphism. This is the cone
identification the source displays — `Hom(K, C(f))` is the cone of `Hom(K, f)` — read on a
graded splitting: the splitting of the sequence is carried along, and the differential of the
image middle term is determined by the image connecting morphism.

The second is the clause that *the construction reduces to the usual one on taking associated
complexes*, which is proved both pointwise and for the constructed functor. Pointwise: a value
of the right derived functor of the `D(E, d)`-valued functor at an object `X`, in the sense of
Tag 05S9, is carried by the forgetful functor
`DifferentialGradedModule.derivedForget : D(E, d) ⥤ D(Ab)` to a value of the right
derived functor of the `D(Ab)`-valued functor at `X`. Essential constancy of an ind-object is
preserved by postcomposition with an arbitrary functor, so no hypothesis on the forgetful
functor, and none on the class of morphisms being inverted, is needed. Globally:
`R Hom(K, -) : D(A) ⥤ D(E, d)` followed by that forgetful functor is itself a right derived
functor of `Hom(K, -) : K(A) ⥤ D(Ab)`.

## Main definitions

* `CochainComplex.endAlgebra`: the endomorphism differential graded algebra `E = End(K)`.
* `CochainComplex.homDGFunctor`: the functor `Hom(K, -)` of differential graded categories.
* `CochainComplex.homHomotopyFunctor`: the differential graded Hom functor
  `Hom(K, -) : K(B) ⥤ K(E, d)`.
* `CochainComplex.homToDerivedCategory`: the functor to be right derived,
  `Hom(K, -) : K(B) ⥤ D(E, d)`.
* `CochainComplex.homToDerivedCategoryForget`: the same functor read in `D(Ab)` by taking
  associated complexes, which is the functor the source right derives.
* `CochainComplex.derivedHomFunctor`: **the functor of Tag 09LK**,
  `R Hom(K, -) : D(A) ⥤ D(E, d)`, for `A` abelian — the right derived functor of
  `Hom(K, -) : K(A) ⥤ D(E, d)` along the localization at the quasi-isomorphisms.
* `CochainComplex.derivedHomFunctorUnit`: its canonical comparison
  `Hom(K, -) ⟶ Qh ⋙ R Hom(K, -)`.

## Main results

* `CochainComplex.derivedHomFunctor_isRightDerivedFunctor`: the comparison exhibits
  `CochainComplex.derivedHomFunctor` as a right derived functor, i.e. as a left Kan extension
  along `K(A) ⥤ D(A)`; this is the universal property that makes it *the* canonical functor.
* `CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor`: the constructed
  functor reduces to the usual one on associated complexes — composed with the forgetful functor
  `D(E, d) ⥤ D(Ab)` it is a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`.
* `CategoryTheory.Functor.preservesLeftKanExtension_of_isRightDerivable`: the general fact behind
  the previous one. If `W` has a left calculus of fractions and `F` is right derivable relative
  to `W`, then every functor out of the target of `F` carries a left Kan extension of `F` along a
  localization functor for `W` to one of the composite.
* `CochainComplex.exists_mapGradedSplitShortExact_homDGFunctor`: `Hom(K, -)` carries an
  admissible short exact sequence of complexes to one of differential graded `E`-modules,
  preserving the two closed arrows and the connecting morphism — the cone identification, read
  on graded splittings.
* `CategoryTheory.Functor.IsRightDerivedValueAt.comp`: a value of a right derived functor at an
  object is carried along postcomposition with an arbitrary functor, the value being the image
  cocone.
* `CochainComplex.isRightDerivedValueAt_homToDerivedCategoryForget`: Tag 09LK's reduction
  clause. A value of the right derived functor of `Hom(K, -) : K(B) ⥤ D(E, d)` at `X` has, as
  its associated complex, a value of the right derived functor of `Hom(K, -) : K(B) ⥤ D(Ab)`
  at `X`.
* `CochainComplex.isRightDerivable_homToDerivedCategoryForget` and
  `CochainComplex.isRightDerivable_homToDerivedCategoryForget_quasiIso`: consequently the
  corrected hypothesis — everywhere-definedness of the `D(E, d)`-valued right derived functor —
  implies the hypothesis the source states, which is everywhere-definedness of the
  `D(Ab)`-valued one.

## Implementation notes

*What is corrected, and why.* Tag 09LK assumes that the right derived functor of the
**abelian-group-valued** functor `Hom(K, -) : K(B) ⥤ D(Ab)` is everywhere defined, and concludes
that the **differential-graded-module-valued** functor `Hom(K, -) : K(B) ⥤ D(E, d)` has an
everywhere-defined right derived functor. The source justifies the step by compatibility of the
forgetful functor `D(E, d) ⥤ D(Ab)` with cohomology. What that compatibility yields is exactly
conservativity of the forgetful functor, which is
`DifferentialGradedModule.isIso_iff_isIso_derivedForget_map`, and conservativity is not enough.
Being defined at `X` means the ind-object `(s : X ⟶ X') ↦ Hom(K, X')` is essentially constant,
and an essentially constant filtered ind-object can have every transition map a
non-isomorphism: take `a` a retract of `b`, say `f : a ⟶ b` and `g : b ⟶ a` with `f ≫ g = 𝟙 a`,
index by the poset of natural numbers, let every object be `b` and every transition map be the
idempotent `g ≫ f`; this is essentially constant with value `a`, yet no transition map is
invertible, so no amount of reflected invertibility produces the witness. Transporting the
witness backwards along the forgetful functor instead needs that functor to be *full* — the
witness is a section of a coprojection, and lifting it is precisely a fullness statement — and
the forgetful functor is not full. So the hypothesis is corrected to derivability of the
`D(E, d)`-valued functor, which is the direction in which the witness does move: by
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith.map`, essential constancy is
preserved by postcomposition with an arbitrary functor. The corrected hypothesis implies the
source's, by `CochainComplex.isRightDerivable_homToDerivedCategoryForget`.

*How far the converse goes, and why it stops there.* The missing step is bounded from both
sides. On the positive side, `CategoryTheory.Functor.IsRightDerivable.of_comp` proves exactly
the converse of `CochainComplex.isRightDerivable_homToDerivedCategoryForget` for a functor that is
full and faithful and whose source has split idempotents: the idempotent `c_i ∘ r` carrying the
value is then the image of an idempotent upstairs, splitting it produces the value, and the
coprojections, the section and the cofinal factorisation are its preimages. Of those three
hypotheses `DifferentialGradedModule.derivedForget` satisfies only the one on its source, a
derived category of differential graded modules being idempotent complete; it is not full, and not
even faithful.

On the negative side, no hypothesis on the functor alone can replace the hypothesis on the source:
`CategoryTheory.EssentiallyConstantInd.exists_fullyFaithful_not_reflecting` exhibits a *fully
faithful* — hence conservative — functor that reflects no essential constancy at all, namely the
inclusion of the full subcategory of nonzero abelian groups, at the filtered system over `ℕ` that
is constant at `ℤ` with every non-identity transition morphism zero. In `Ab` that system is
essentially constant with value the zero group
(`CategoryTheory.EssentiallyConstantInd.isEssentiallyConstantInd_collapsingSystem_comp_ι`); inside
the subcategory it is not essentially constant
(`CategoryTheory.EssentiallyConstantInd.not_isEssentiallyConstantInd_collapsingSystem`), because
its value has been removed. So essential constancy is not invariant under enlarging the ambient
category along a fully faithful embedding, and therefore has no characterisation mentioning only
the image of the diagram that could be transported instead of the witness.

*The route through the colimit of Hom complexes, and why it fails.* Transporting a witness
backwards along a functor that is not full is not the only conceivable route. At the level of
complexes the ind-object of Tag 05S9 is an honest filtered system of differential graded
`E`-modules, `(s : X ⟶ X') ↦ Hom(K, X')`; in a *module* category a splitting of a coprojection
that is merely additive is automatically `E`-linear, because every element of a filtered colimit
comes from a term. So one could hope to build the essential-constancy witness at the level of
complexes, where the abelian-group-valued hypothesis lives, and localize afterwards. Three things
have to hold, and the third does not.

The first does: `W.Under ⊤ X` is filtered when `W` has a left calculus of fractions
(`CategoryTheory.MorphismProperty.isFiltered_under_of_hasLeftCalculusOfFractions`), the Hom
complexes form an honest filtered system of differential graded `E`-modules over it, and the
underlying-complex functor preserves its colimit, colimits of differential graded modules being
computed degreewise on the underlying groups.

The second does not hold as stated and is not needed: a coprojection into a filtered colimit is
in general not an epimorphism — a system of inclusions with strictly growing terms has none — and
no cofinal reindexing repairs that. What the `E`-linearity argument consumes is only that the
*family* of coprojections is jointly epimorphic, which in a module category is automatic.

The third fails, and fatally. The datum that argument consumes is an equation between
homomorphisms of modules: the transition `Hom(K, X_j) ⟶ Hom(K, X_k)` must factor through the
coprojection at `j`. Essential constancy of the image supplies the retraction, and the
factorisation, only as morphisms of `D(Ab)`, that is only up to quasi-isomorphism, and nothing
lifts either to a homomorphism of modules. That the gap is not a technicality is the content of
the following witness: for `E = ℤ[x]/(x²)` in degree
`0` and `P` the two-periodic free resolution of `E/(x)`, the `ℕ`-indexed system `n ↦ P[n]` with
transition morphisms the shifts of the invisible class `u : P ⟶ P[1]` is an honest filtered
system of differential graded `E`-modules whose colimit in those is the zero module, whose
coprojections are therefore epimorphisms, and which the forgetful functor `D(E, d) ⥤ D(Ab)`
carries to a system with all transition morphisms zero — hence essentially constant there, with
value the zero object — while in `D(E, d)` every composite transition morphism `uᵏ` is nonzero,
so by
`CategoryTheory.EssentiallyConstantInd.not_reflects_isEssentiallyConstantInd_of_map_eq_zero` it is
not essentially constant. Every structural hypothesis of the route holds for it and the conclusion
is false, so no argument using only that structure can prove the converse, and the hypothesis
stays corrected. What the witness does *not* settle is Tag 09LK's own statement: it is not the
ind-object of Tag 05S9 of any complex, so the source's hypothesis may still imply the corrected
one through something special to the systems `(s : X ⟶ X') ↦ Hom(K, X')`.

*The route through eventual constancy, and why it fails too.* What conservativity does suffice
for is the strictly stronger notion, Mathlib's
`CategoryTheory.Functor.IsEventuallyConstantFrom`:
`CategoryTheory.Functor.isEventuallyConstantFrom_of_comp` reflects it along any functor reflecting
isomorphisms. Essential constancy is strictly weaker — the retract example above is essentially
constant with no invertible transition morphism — and that difference is precisely what the
source's reason cannot cross. That left one route: were essential constancy in `D(Ab)` of the
particular systems `(s : X ⟶ X') ↦ Hom(K, X')` to force eventual constancy, that lemma would carry
it back along the forgetful functor and the source's hypothesis would imply the corrected one. It
does not force it, by a dichotomy for these systems. A transition morphism of `X/W` is a
quasi-isomorphism (`HomotopyCategory.quasiIso_right_of_under`), `Hom(K, -) : K(A) ⥤ D(E, d)`
being exact inverts a quasi-isomorphism exactly when it kills the acyclic third vertex of a
distinguished triangle on it, and therefore: if `Hom(K, -)` kills every acyclic object — if `K`
is K-projective, when the functor inverts `W` outright and nothing needs deriving — every one
of these systems is eventually constant from every index
(`CochainComplex.isEventuallyConstantFrom_homToDerivedCategory`); and otherwise *none* of them, at
no object and from no index, is eventually constant, in `D(E, d)` or in `D(Ab)`
(`CochainComplex.not_isEventuallyConstantFrom_homToDerivedCategory` and
`CochainComplex.not_isEventuallyConstantFrom_homToDerivedCategoryForget`), while at a zero object
of `K(A)` the system *is* essentially constant, with value a zero object
(`CochainComplex.exists_isRightDerivedValueAt_homToDerivedCategory_of_isZero`). So Tag 05S9's own
ind-object of an actual object of `K(A)` has an essentially constant image in `D(Ab)` and is
eventually constant from no index
(`CochainComplex.isEssentiallyConstantInd_and_not_isEventuallyConstantFrom`): the upgrade is
false, and this route is closed as well. It is closed, not conclusive against the source: a zero
object is also a place where the `D(E, d)`-valued system is essentially constant, so the witness
does not contradict Tag 09LK's implication. With both routes shut and no third identified, the
corrected hypothesis stands, as recorded on `CochainComplex.derivedHomFunctor`.

*Where the deviation is absent.* The deviation is a deviation only in the generality in which the
declarations below are stated, which is an arbitrary abelian category with a chosen derived
category. Over one in which every complex admits a quasi-isomorphism towards a K-injective
complex — in particular over any Grothendieck abelian category — the hypothesis below is not an
assumption at all but a theorem, by Tag 070Y: a K-injective complex is a terminal index of the
ind-object of Tag 05S9, so the right derived functor of an *arbitrary* functor out of `K(A)` is
defined everywhere.
`CochainComplex.isRightDerivable_homToDerivedCategory_of_exists_isKInjective` proves that, and
`CochainComplex.derivedHomFunctor_isRightDerivedFunctor_of_exists_isKInjective` and its
companions restate the clauses below with no derivability hypothesis of any kind, the source's
included.
That does not settle the implication the source asserts, which the two routes
above do not reach, and the declarations below keep the hypothesis they have, since neither
they nor the source assume anything about resolutions.

*How the functor is assembled.* Deligne's condition of Tag 05S9 — the ind-object
`(s : X ⟶ X') ↦ Hom(K, X')` is essentially constant — is not literally Mathlib's condition for a
pointwise left Kan extension along a localization functor, whose index category is the comma
category of arrows `Qh(Y) ⟶ Qh(X)` of the derived category.
`CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_isRightDerivable` bridges the two,
using that
the comparison functor between the index categories is final, which is where the left calculus
of fractions for the quasi-isomorphisms of `K(A)` is used. The left Kan extension then exists,
and `CochainComplex.derivedHomFunctor` is Mathlib's `Functor.totalRightDerived` of
`Hom(K, -) : K(A) ⥤ D(E, d)` along `DerivedCategory.Qh`.

The reduction clause for that functor is not an instance of
`CategoryTheory.Functor.IsRightDerivedValueAt.comp` applied pointwise: being a left Kan
extension is a statement about colimits over the comma categories, and the forgetful functor
would have to preserve *those* colimits.
`CategoryTheory.Functor.preservesLeftKanExtension_of_isRightDerivable` supplies exactly that,
again through finality of the comparison functor: the forgetful functor preserves the colimit of
Deligne's ind-object because a value of `RF` is a retract of a term of it, finality transports
the preservation to the comma-category colimit, and essential surjectivity of `Qh` spreads the
pointwise statement from the objects `Qh(X)` to all of `D(A)`. No hypothesis on the forgetful
functor is used, so the statement holds for an arbitrary functor out of `D(E, d)`.

*Where exactness is.* The conclusion that the functor is *exact* as a functor of triangulated
categories is not proved here, and is reached in two stages elsewhere.

The commutation with the translation is complete and holds at every level, up to and including
the derived functor itself: `CochainComplex.homComplexesFunctorCommShift`,
`CochainComplex.homHomotopyFunctorCommShift`, `CochainComplex.homToDerivedCategoryCommShift` and
`CochainComplex.derivedHomFunctorCommShift`. Preservation of distinguished triangles by the
functor being derived is `CochainComplex.exists_isDistinguishedTriangle_homComplexesFunctor`,
stated for a presentation of the triangle by a degreewise split short exact sequence; in the
`CategoryTheory.Functor.mapTriangle` form, `CochainComplex.homHomotopyFunctor_isTriangulated` and
`CochainComplex.homToDerivedCategory_isTriangulated` are the unconditional exactness of the
functor being derived.

Exactness of the derived functor itself is `CochainComplex.derivedHomFunctor_isTriangulated`,
under Tag 09LK's own hypothesis and no other. It is not reached through
`CategoryTheory.Functor.isTriangulated_of_leftExtension`, which asks, for every morphism `f` of
`D(A)`, a distinguished triangle of `K(A)` whose first arrow has
`Arrow.mk (Qh.map ·) ≅ Arrow.mk f` and at whose three vertices
`CochainComplex.derivedHomFunctorUnit` is invertible: everywhere-definedness says that an
ind-object is essentially constant, which says nothing about where the comparison is invertible.
It is reached instead through `CategoryTheory.Functor.isTriangulated_of_isRightDerivable`, the
everywhere-defined case of Tag 05SE, where the triangle whose distinguishedness is used is the
triangle of *values* of Tag 05SC.

Both ends carry a triangulated structure, and every piece of it is an instance. The source
`K(A)` is pretriangulated by Mathlib. On the target,
`DifferentialGradedModule.instHasShiftIntHomotopyCategory`,
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` and
`DifferentialGradedModule.instIsTriangulatedHomotopyCategory'` make `K(E, d)` triangulated, and
`DifferentialGradedModule.derivedCategory' E`, which is by definition the localization of
`K(E, d)` at `DifferentialGradedModule.quasiIsomorphisms' E`, inherits a shift, a pretriangulated
structure and the octahedron axiom from
`DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions'` and
`DifferentialGradedModule.quasiIsomorphisms_isCompatibleWithTriangulation'`, with the
localization functor itself exact and commuting with the shift. Mathlib's
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift` then equips the Kan extension with a
`CategoryTheory.Functor.CommShift` as soon as the functor being derived has one, since
`HomotopyCategory.quasiIso A (ComplexShape.up ℤ)` is compatible with the shift and
`DerivedCategory.Qh` commutes with it; that is how
`CochainComplex.derivedHomFunctorCommShift` is obtained.

Of the two halves of exactness of the functor being derived, the first,
`(CochainComplex.homToDerivedCategory A K).CommShift ℤ`, is
`CochainComplex.homToDerivedCategoryCommShift`; the second is
`CategoryTheory.Functor.IsTriangulated` for it, equivalently, since the localization functor is
exact, for `CochainComplex.homHomotopyFunctor`.

The content of the second is *preservation of distinguished triangles*. It is proved by the
route that avoids cones, the one taken for tensoring with a bimodule in
`DifferentialGraded.Bimodule.tensorHomotopyFunctor_isTriangulated'`: carry graded splittings
through the differential graded functor and recognise the image as the triangle of an admissible
short exact sequence. It has three inputs. A distinguished triangle of
`K(B)` need not be presented by a mapping cone at all, since
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` presents it by
a degreewise split short exact sequence of complexes, which
`CochainComplex.gradedSplitOfDegreewiseSplit` turns into a
`DGCategory.GradedSplitShortExact` for `CochainComplex.dgCategory B`, with
`CochainComplex.connectingHom_gradedSplitOfDegreewiseSplit` identifying its connecting morphism
with Mathlib's `CochainComplex.cocycleOfDegreewiseSplit`. The shift comparison
`Hom(K, X[1]) ≅ Hom(K, X)[1]` is `CochainComplex.homShiftIso`, obtained from
`DGCategory.representableShiftIso` and `CochainComplex.dgShiftComparisonData`; no
`DGCategory.ShiftAxiomB` for the differential graded category of complexes is needed, and none
could be had, since axiom (B) demands that the shift be strictly additive on objects while
Mathlib's shift on complexes reindexes by `p + n`. And the bridge from a
`DGCategory.GradedSplitShortExact` in `DifferentialGradedModule.dgCategory E` to the
`DifferentialGradedModule.IsAdmissibleShortExact` and
`DifferentialGradedModule.CompatibleSplittings` in terms of which
`DifferentialGradedModule.IsDistinguishedTriangle` — and hence
`DifferentialGradedModule.distinguishedTriangles_eq` — is phrased, is
`DifferentialGradedModule.isDistinguishedTriangle_gradedSplit`.

The coherence of the family `CochainComplex.homShiftIso` — naturality in `X` and compatibility
with `shiftFunctorZero` and `shiftFunctorAdd` at both ends, which is what a
`CategoryTheory.Functor.CommShift ℤ` asks for and what `CategoryTheory.Functor.mapTriangle` is
formed from — is `CochainComplex.homComplexesFunctorCommShift`. Putting the triangle statement
into the `CategoryTheory.Functor.mapTriangle` form at the *homotopy* level is
`CochainComplex.homHomotopyFunctor_isTriangulated`: the third arrow of
`mapTriangle` is formed with the degree-one component of the `CommShift` of
`CochainComplex.homHomotopyFunctor`, which is the comparison above transported along
`CochainComplex.homHomotopyFunctorLiftIso` and is not the identity, so the statement is proved
for the *descent* `CochainComplex.homHomotopyFunctorLift`, whose `CommShift` is
`CategoryTheory.Quotient.liftCommShift` and whose components are therefore pinned by
`CategoryTheory.Quotient.LiftCommShift.iso_hom_app`, and transported back along that
isomorphism.

The other route, Tag 0FQF's `DGCategory.DGFunctor.CommShiftK.isTriangulated`, is not usable: it
makes the functor induced on homotopy categories by a differential graded functor exact, but it
consumes a `DGCategory.ConeSituation` — the bundle of axioms (A), (B) and (C) — at *both* ends,
and none is constructed for `CochainComplex.dgCategory B` or for
`DifferentialGradedModule.dgCategory E`; axiom (B) is unavailable for the former for the reason
just given. Its conclusion would moreover be stated against the structure that
`DGCategory.homotopyPretriangulated` puts on the homotopy categories of the two differential
graded categories, which would then have to be matched with Mathlib's structure on `K(A)` across
`CochainComplex.homotopyCategoryEquivalence` and with
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` across
`DifferentialGradedModule.homotopyCategoryEquivalence` — a comparison of the cone-triangle and
admissible-sequence sign conventions.

*Generality.* The reduction clause at the level of values is stated for an arbitrary class `W` of
morphisms of `K(B)`, since nothing in its proof uses that `W` is the quasi-isomorphisms;
`CochainComplex.isRightDerivable_homToDerivedCategoryForget_quasiIso` specialises to the class
the source uses. Only `Preadditive B` is required for the differential graded category and for
everything below it, `CategoryWithHomology B` only for that specialisation.

The functor construction needs more, and the following is the weakest available. The target of
the Kan extension is `D(A)`, so `A` must be abelian and come with a chosen derived category:
Mathlib defines `DerivedCategory` only for an abelian category with `HasDerivedCategory`, and
the left calculus of fractions for `HomotopyCategory.quasiIso A (ComplexShape.up ℤ)`, which the
bridge to pointwise Kan extensions consumes, is likewise only available there.
`CategoryWithHomology A` would suffice for the quasi-isomorphisms themselves but not for either
of those two inputs. `HasDerivedCategory A` is not needed for
`CochainComplex.hasRightDerivedFunctor_homToDerivedCategory`, which speaks of the abstract
localization, and is omitted there; `HasDerivedCategory (ModuleCat.{0} ℤ)` enters only with the
`D(Ab)`-valued functor.

*Universes.* The morphisms of `B` are taken in `Type 0`, so that `B = Ab` is covered and the Hom
complexes are complexes of abelian groups that are sets, as in the source. This is forced by the
chosen derived category: `DifferentialGradedModule.derivedCategory'` and
`DifferentialGradedModule.derivedForget` are built at the single-universe encoding of
differential graded algebras over a base ring `R : Type u`, and the base ring here is `ℤ`,
whence `u = 0` and the degreewise pieces of `E = End(K)`, which are the homogeneous morphisms of
`K` in `B`, must lie in `Type 0`. The objects of `B` are in an arbitrary universe.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), the statement delivered
  here; the endomorphism algebra and the representable functor are
  [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the differential graded category of
  complexes is [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), and being defined at an
  object is [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w w' u

namespace CategoryTheory.Functor

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  {D'' : Type u₃} [Category.{v₃} D''] {E : Type u₄} [Category.{v₄} E]

/-- A value of a right derived functor is carried along postcomposition with an arbitrary
functor: if the cocone `c` exhibits `c.pt` as a value of `RF` at `X` in the sense of Tag 05S9,
then `G.mapCocone c` exhibits `G.obj c.pt` as a value of `R(F ⋙ G)` at `X`. Essential constancy
of an ind-object needs nothing of `G`. -/
theorem IsRightDerivedValueAt.comp {F : D ⥤ D'} {W : MorphismProperty D} {X : D}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (h : F.IsRightDerivedValueAt W X c) (G : D' ⥤ D'') :
    (F ⋙ G).IsRightDerivedValueAt W X (G.mapCocone c) := by
  obtain ⟨s₀, r, hr⟩ := (F.isRightDerivedValueAt_iff W X c).1 h
  exact ((F ⋙ G).isRightDerivedValueAt_iff W X _).2 ⟨s₀, G.map r, hr.map G⟩

/-- Every functor preserves the colimit that computes a value of a right derived functor: if the
cocone `c` exhibits a value of `RF` at `X` in the sense of Tag 05S9, then `G` carries every
colimit cocone on the ind-object `X/W ⟶ ℋ`, `(s : X ⟶ X') ↦ F(X')` to a colimit cocone. -/
theorem preservesColimit_of_isRightDerivedValueAt {F : D ⥤ D'} {W : MorphismProperty D} {X : D}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (h : F.IsRightDerivedValueAt W X c) (G : D' ⥤ D'') :
    Limits.PreservesColimit
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) G :=
  (Limits.preservesColimit_iff_isColimit_mapCocone h.isColimit).2 ⟨(h.comp G).isColimit⟩

/-- **Postcomposition preserves the derived functor of a right derivable functor.** Let `W` have
a left calculus of fractions, let `F` be right derivable relative to `W` and let `L` be a
localization functor for `W`. Then every functor `G` out of the target of `F` carries a left Kan
extension of `F` along `L` to one of `F ⋙ G`.

Each pointwise value of the Kan extension is a colimit over the arrows `L(Y) ⟶ L(X)` of the
localization, which by finality of the comparison functor of
`CategoryTheory.MorphismProperty.underToCostructuredArrow` is the colimit of Deligne's
ind-object; the latter is preserved by `G` because a value of `RF` is a retract of a term of the
ind-object. Essential surjectivity of `L` spreads the pointwise statement to every object. -/
theorem preservesLeftKanExtension_of_isRightDerivable (F : D ⥤ D')
    (W : MorphismProperty D) [W.HasLeftCalculusOfFractions] (hF : F.IsRightDerivable W)
    (L : D ⥤ E) [L.IsLocalization W] (G : D' ⥤ D'') :
    G.PreservesLeftKanExtension F L := by
  have hpd : F.HasPointwiseRightDerivedFunctor W :=
    F.hasPointwiseRightDerivedFunctor_of_isRightDerivable W hF
  have hple : HasPointwiseLeftKanExtension L F :=
    hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L W
  have hcol : ∀ X : D,
      Limits.PreservesColimit (CostructuredArrow.proj L (L.obj X) ⋙ F) G := by
    intro X
    obtain ⟨c, hc⟩ := hF X
    have h₁ : Limits.PreservesColimit
        (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) G :=
      preservesColimit_of_isRightDerivedValueAt hc G
    have hfin : (W.underToCostructuredArrow L X).Final :=
      W.final_underToCostructuredArrow L X
    have h₂ : Limits.PreservesColimit (W.underToCostructuredArrow L X ⋙
        CostructuredArrow.proj L (L.obj X) ⋙ F) G :=
      Limits.preservesColimit_of_iso_diagram G
        (F.underToCostructuredArrowCompProjCompIso W L X).symm
    exact Final.preservesColimit_of_comp (W.underToCostructuredArrow L X)
  have hall : G.PreservesPointwiseLeftKanExtension F L := by
    intro Y
    have := Localization.essSurj L W
    have hpw := pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F
    have := hcol (L.objPreimage Y)
    exact PreservesPointwiseLeftKanExtensionAt.mk' G F L Y (hpw Y)
      (LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _
        ((hpw (L.obj (L.objPreimage Y))).postcompose G) (L.objObjPreimageIso Y))
  infer_instance

end CategoryTheory.Functor

namespace CochainComplex

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)

/-- The endomorphism differential graded algebra `E = End(K)` of a cochain complex `K` in a
preadditive category: Tag 09LE applied to the object `K` of the differential graded category of
complexes of Tag 09L9. -/
abbrev endAlgebra : DifferentialGradedAlgebra ℤ :=
  (DGCategory.homRepresentation (dgCategory B) K).algebra

/-- The functor `Hom(K, -)` of differential graded categories, from the complexes in `B` to the
differential graded `E`-modules, of Tag 09LE. -/
abbrev homDGFunctor :
    DGCategory.DGFunctor (dgCategory B)
      (DifferentialGradedModule.dgCategory (endAlgebra B K)) :=
  (DGCategory.homRepresentation (dgCategory B) K).functor

/-- **Stacks 09LK, the cone identification (unconditional).** `Hom(K, -)` carries an admissible
short exact sequence of complexes in `B`, with a chosen graded splitting, to an admissible short
exact sequence of differential graded `E`-modules: its two closed arrows are the images of the
given ones under the induced functor on complexes, and its connecting morphism `π d(s)` is the
image of the given connecting morphism.

This is the content of the source's displayed isomorphism
`Hom(K, C(f)) ≅ C(Hom(K, A) ⟶ Hom(K, B))` read on graded splittings: the splitting of the cone
sequence is carried along by `Hom(K, -)`, so the image middle term is the image direct sum, and
its differential is pinned by the image of the connecting morphism. No hypothesis on `K`, on
`B`, or on the sequence beyond admissibility is used. -/
theorem exists_mapGradedSplitShortExact_homDGFunctor {x y z : CochainComplex B ℤ}
    (E : DGCategory.GradedSplitShortExact (A := dgCategory B) x y z) :
    ∃ F : DGCategory.GradedSplitShortExact
        (A := DifferentialGradedModule.dgCategory (endAlgebra B K))
        ((homDGFunctor B K).obj x) ((homDGFunctor B K).obj y) ((homDGFunctor B K).obj z),
      F.a = (homDGFunctor B K).onComp.map E.a ∧
        F.b = (homDGFunctor B K).onComp.map E.b ∧
        DGCategory.GradedSplitShortExact.connectingHom F =
          (homDGFunctor B K).map (DGCategory.GradedSplitShortExact.connectingHom E) :=
  ⟨(homDGFunctor B K).mapGradedSplitShortExact E,
    DGCategory.DGFunctor.onComp_map_a _ E, DGCategory.DGFunctor.onComp_map_b _ E,
    DGCategory.DGFunctor.connectingHom_mapGradedSplitShortExact _ E⟩

/-- The differential graded Hom functor `Hom(K, -) : K(B) ⥤ K(E, d)` out of a cochain complex
`K`: the comparison of the homotopy category of `B` with that of the differential graded
category of complexes, followed by the functor of Tag 09LE on homotopy classes. -/
def homHomotopyFunctor :
    HomotopyCategory B (ComplexShape.up ℤ) ⥤
      DifferentialGradedModule.HomotopyCategory (endAlgebra B K) :=
  (homotopyCategoryEquivalence B).functor ⋙
    (DGCategory.homRepresentation (dgCategory B) K).homotopyFunctor

/-- The functor to be right derived in Tag 09LK: the differential graded Hom functor
`Hom(K, -)`, followed by the localization of the category of differential graded `E`-modules at
the quasi-isomorphisms, so `K(B) ⥤ D(E, d)`. -/
def homToDerivedCategory :
    HomotopyCategory B (ComplexShape.up ℤ) ⥤
      DifferentialGradedModule.derivedCategory' (endAlgebra B K) :=
  homHomotopyFunctor B K ⋙
    (DifferentialGradedModule.quasiIsomorphisms' (endAlgebra B K)).Q

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- The functor the source of Tag 09LK right derives: the differential graded Hom functor
`Hom(K, -) : K(B) ⥤ D(E, d)` read in `D(Ab)` by taking associated complexes, i.e. followed by
the forgetful functor `DifferentialGradedModule.derivedForget`. -/
abbrev homToDerivedCategoryForget :
    HomotopyCategory B (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{0} ℤ) :=
  homToDerivedCategory B K ⋙ DifferentialGradedModule.derivedForget (endAlgebra B K)

variable (W : MorphismProperty (HomotopyCategory B (ComplexShape.up ℤ)))

/-- **Tag 09LK's reduction clause, pointwise and for an arbitrary class of morphisms.** A value
at `X` of the right derived functor of the
differential-graded-module-valued functor `Hom(K, -) : K(B) ⥤ D(E, d)` reduces, on taking
associated complexes, to a value at `X` of the right derived functor of the
abelian-group-valued functor `Hom(K, -) : K(B) ⥤ D(Ab)`: the image under the forgetful functor
of a cocone exhibiting the first is a cocone exhibiting the second.

This is unconditional, and it is the direction in which the essential-constancy witness moves:
postcomposition with the forgetful functor transports it, whereas the source's hypothesis on the
abelian-group-valued functor would have to be carried backwards along a functor that is only
conservative. The tag's reduction clause for the assembled functor is
`CochainComplex.derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor`. -/
theorem isRightDerivedValueAt_homToDerivedCategoryForget {X : HomotopyCategory B (.up ℤ)}
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙
      homToDerivedCategory B K)}
    (h : (homToDerivedCategory B K).IsRightDerivedValueAt W X c) :
    (homToDerivedCategoryForget B K).IsRightDerivedValueAt W X
      ((DifferentialGradedModule.derivedForget (endAlgebra B K)).mapCocone c) :=
  h.comp _

/-- **The corrected hypothesis of Tag 09LK implies the source's.** If the right derived functor
of the differential-graded-module-valued `Hom(K, -) : K(B) ⥤ D(E, d)` is defined everywhere,
then so is the right derived functor of the abelian-group-valued `Hom(K, -) : K(B) ⥤ D(Ab)`,
which is what the source assumes. -/
theorem isRightDerivable_homToDerivedCategoryForget
    (h : (homToDerivedCategory B K).IsRightDerivable W) :
    (homToDerivedCategoryForget B K).IsRightDerivable W := fun X => by
  obtain ⟨c, hc⟩ := h X
  exact ⟨_, hc.comp _⟩

/-- The previous implication at the class of morphisms the source inverts, the
quasi-isomorphisms of `K(B)`: derivability of the differential-graded-module-valued
`Hom(K, -)` implies the hypothesis of Tag 09LK as stated. -/
theorem isRightDerivable_homToDerivedCategoryForget_quasiIso [CategoryWithHomology B]
    (h : (homToDerivedCategory B K).IsRightDerivable
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))) :
    (homToDerivedCategoryForget B K).IsRightDerivable
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
  isRightDerivable_homToDerivedCategoryForget B K _ h

end CochainComplex

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{w'} A]
  (K : CochainComplex A ℤ)

omit [HasDerivedCategory.{w'} A] in
/-- The corrected hypothesis of Tag 09LK in the form Mathlib's Kan extensions need: if the right
derived functor of `Hom(K, -) : K(A) ⥤ D(E, d)` is defined at every object of `K(A)`, then that
functor has a left Kan extension along the localization at the quasi-isomorphisms. -/
theorem hasRightDerivedFunctor_homToDerivedCategory
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (homToDerivedCategory A K).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have := (homToDerivedCategory A K).hasPointwiseRightDerivedFunctor_of_isRightDerivable
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) h
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor (homToDerivedCategory A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- **The functor of Stacks 09LK, under a hypothesis stronger than the source's.** The canonical
functor `R Hom(K, -) : D(A) ⥤ D(E, d)`, for `E = End(K)` the endomorphism
differential graded algebra of a cochain complex `K` in an abelian category `A`: the right derived
functor of `Hom(K, -) : K(A) ⥤ D(E, d)` along the localization `K(A) ⥤ D(A)` at the
quasi-isomorphisms.

Tag 09LK assumes that the right derived functor of the `D(Ab)`-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` is everywhere defined; this declaration assumes it of the
`D(E, d)`-valued functor. The latter implies the former,
`CochainComplex.isRightDerivable_homToDerivedCategoryForget`; the converse is
`CochainComplex.ReflectsHomDerivability`, which is neither proved nor refuted here, so the
hypothesis used here is not known to be the source's. That converse asks for reflection of
essential constancy of an ind-object along the forgetful functor `D(E, d) ⥤ D(Ab)`. It holds
along a functor that is full and faithful with idempotent-complete source,
`CategoryTheory.Functor.IsRightDerivable.of_comp`, and the forgetful functor is neither full nor
faithful; it fails for some conservative functors,
`CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero`, but that
functor is not the forgetful functor of a differential graded algebra and is neither additive nor
exact, so it refutes the general lemma and not this instance. Deriving the `D(E, d)`-valued
functor is also the step the Stacks Project's own proof of 09LK takes. -/
def derivedHomFunctor
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    DerivedCategory A ⥤ DifferentialGradedModule.derivedCategory' (endAlgebra A K) :=
  have := hasRightDerivedFunctor_homToDerivedCategory A K h
  (homToDerivedCategory A K).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The canonical comparison `Hom(K, -) ⟶ Qh ⋙ R Hom(K, -)` of Tag 09LK: the unit exhibiting
`CochainComplex.derivedHomFunctor` as the right derived functor. -/
def derivedHomFunctorUnit
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    homToDerivedCategory A K ⟶ DerivedCategory.Qh ⋙ derivedHomFunctor A K h :=
  have := hasRightDerivedFunctor_homToDerivedCategory A K h
  (homToDerivedCategory A K).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The universal property pinning down `CochainComplex.derivedHomFunctor`: together with its
canonical comparison it is a right derived functor of `Hom(K, -) : K(A) ⥤ D(E, d)`, i.e. a left
Kan extension along the localization `K(A) ⥤ D(A)`. -/
theorem derivedHomFunctor_isRightDerivedFunctor
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomFunctor A K h).IsRightDerivedFunctor (derivedHomFunctorUnit A K h)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have := hasRightDerivedFunctor_homToDerivedCategory A K h
  inferInstanceAs
    (((homToDerivedCategory A K).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((homToDerivedCategory A K).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **The reduction clause of Stacks 09LK, under a hypothesis stronger than the source's.** The
canonical functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of `CochainComplex.derivedHomFunctor`,
followed by the forgetful functor `D(E, d) ⥤ D(Ab)` taking associated complexes, is a right
derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`: the construction reduces to the usual one on
associated complexes.

Tag 09LK assumes that the right derived functor of the `D(Ab)`-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` is everywhere defined; this declaration assumes it of the
`D(E, d)`-valued functor. The latter implies the former,
`CochainComplex.isRightDerivable_homToDerivedCategoryForget`; the converse is
`CochainComplex.ReflectsHomDerivability`, which is neither proved nor refuted here, so the
hypothesis used here is not known to be the source's. That converse asks for reflection of
essential constancy of an ind-object along the forgetful functor `D(E, d) ⥤ D(Ab)`. It holds
along a functor that is full and faithful with idempotent-complete source,
`CategoryTheory.Functor.IsRightDerivable.of_comp`, and the forgetful functor is neither full nor
faithful; it fails for some conservative functors,
`CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero`, but that
functor is not the forgetful functor of a differential graded algebra and is neither additive nor
exact, so it refutes the general lemma and not this instance. Deriving the `D(E, d)`-valued
functor is also the step the Stacks Project's own proof of 09LK takes. -/
theorem derivedHomFunctor_comp_derivedForget_isRightDerivedFunctor
    (h : (homToDerivedCategory A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomFunctor A K h ⋙
        DifferentialGradedModule.derivedForget (endAlgebra A K)).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedHomFunctorUnit A K h)
          (DifferentialGradedModule.derivedForget (endAlgebra A K)) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hpres := Functor.preservesLeftKanExtension_of_isRightDerivable
    (homToDerivedCategory A K) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) h
    DerivedCategory.Qh (DifferentialGradedModule.derivedForget (endAlgebra A K))
  have hder := derivedHomFunctor_isRightDerivedFunctor A K h
  have hkan : (derivedHomFunctor A K h).IsLeftKanExtension (derivedHomFunctorUnit A K h) :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  exact hpres.preserves (derivedHomFunctor A K h) (derivedHomFunctorUnit A K h)

end CochainComplex

end
