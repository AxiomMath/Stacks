module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint.HomologyCoproducts
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherent
public import StacksFrontier.Homology.PseudoCoherent.BaseChange

/-!
# The image of the derived tensor product with a complex of quasi-coherent cohomology

Let `(C, O)` be a ringed site — for instance the small etale site of an algebraic space over a
scheme, with its structure sheaf — let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The derived
tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX is built in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived`, and
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherent` computes it at the free
rank-one module, where its value is `K`. This file runs the dévissage that promotes that single
value to the *whole* image: if the cohomology sheaves of `K` are quasi-coherent then every object
of `D(E, d)` is sent into `D_QCoh(O)`.

What is proved is the dévissage of Tag 0FQE applied to the property "lies in `D_QCoh(O)`": the
property holds at every shift of the free rank-one module, is inherited by direct sums, and is
inherited by the third vertex of a distinguished triangle from the other two, so it holds at
every object of `D(E, d)`. The exactness of `- ⊗_E^𝐋 K` that the last of those three needs comes
from
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated` in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist`, which is
unconditional: it composes `- ⊗_E^𝐋 K` with the sign-twisted identity of `D(O)`, which has the
same action on objects and on morphisms, so the image of a distinguished triangle has the same
three vertices.

Two further statements here are **vacuous**, and are kept only as the record of why that twist is
needed: `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_isTriangulated'` and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated` assume the exactness of
tensoring with `K` for the pretriangulated structure in force here, and **that hypothesis cannot
be satisfied**; see the docstring of the first for the witness. Neither is used anywhere, and
neither carries a tag. They cannot be repaired in place: what they conclude is the exactness of
the *untwisted* functors, and that is exactly what the sign obstruction makes false.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCategoryB_tensorWithComplexDerived_obj`: **Stacks 09MA**,
  the image of `- ⊗_E^𝐋 K` is contained in `D_QCoh(O)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_isTriangulated'`: `- ⊗_E^𝐋 K`
  and its underived form carry distinguished triangles to distinguished triangles, under the
  hypothesis `hexact` that tensoring with `K` is exact on homotopy categories. **`hexact` cannot
  be satisfied, so both are vacuous**; the unconditional replacement is
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated`.

## Implementation notes

*What is assumed, and why.* Three inputs of the source's proof are assumptions here rather than
theorems, and each is named in the statement.

* That quasi-coherence is a weak Serre class, and `hqcsum`, that a direct sum of quasi-coherent
  `O`-modules is quasi-coherent. These are the two clauses of Tag 03M1, and they are what makes
  `D_QCoh(O)` a triangulated subcategory of `D(O)` closed under direct sums — the shape in which
  the dévissage consumes them; the passage from the two module-level clauses to that shape is
  carried out here, from `CategoryTheory.ObjectProperty.IsWeakSerreClass` through
  `WeakSerre.isWeakSerre_of_isWeakSerreClass` and
  `Stacks.Duality.derivedCategoryB_prop_coproduct`, the Grothendieck abelian structure on the
  ambient category of `O`-modules being supplied by
  `Stacks.SheafOfModules.sheafModulesGrothendieck`.

  The weak Serre clause is taken as a typeclass assumption, not an explicit hypothesis, so that
  it is supplied by instance search wherever this repository has it. For a *variable* ringed site
  it is not available, and cannot be: quasi-coherence is a weak Serre class because of the affine
  structure of the site, and the only unconditional instance in this repository is
  `Stacks.SheafOfModules.isQuasicoherentOnSite_isWeakSerreClass`, for a *chaotic* site with flat
  restriction maps, which is not the site of Tag 09MA. For the small etale site of an algebraic
  space the instance is
  `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass`, and it carries closure under
  kernels, cokernels and extensions as further instance assumptions: in this repository closure
  under cokernels is unconditional only at the module universe of the structure rings
  (`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, whose module universe
  is `u`), closure under kernels needs Descent, Proposition 03DX(2)
  (`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves`) and closure under
  extensions needs the uniform form of Descent, Proposition 03DW
  (`AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_schemeUniverse`), while
  the ambient category in which the tensor products of Tag 09LX are formed has its sections in
  `max u v w t s`, above the universe of the structure rings, and the one universe transport of the
  cokernel clause, `AlgebraicGeometry.Space.isClosedUnderCokernels_isQuasicoherentOnSite_of_ulift`,
  lowers the module universe rather than raising it.
* `htensorSum`, that tensoring with `K` carries a direct sum of differential graded `E`-modules
  to a direct sum in `D(O)`. The differential graded half of this is Tag 09LV, formalized as
  `AlgebraicGeometry.RingedSite.tensorWithComplexDG_preservesCoproducts`; what is missing between
  that and the hypothesis used here is the passage of the preservation statement through the
  quotient by homotopy and the localization at the quasi-isomorphisms, for which the identifying
  comparisons between the `Comp` category of the differential graded category of complexes and
  `CochainComplex` are not available in the form the transport needs.

None of them mentions quasi-coherence of the image of `- ⊗_E^𝐋 K`, which is what is proved. In
particular the exactness of `- ⊗_E^𝐋 K` is **not** among them: as a fourth assumption
`hexact`, Tag 09LW read against the wrong one of the two pretriangulated structures on
`K(Mod_(E, d))`, it would be unsatisfiable, and it is instead discharged by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated`.

*Why Tag 09LW has to be read through the sign twist.* Tag 09LW is formalized as
`AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_isTriangulated`, against
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, whose distinguished triangles
come from admissible short exact sequences, while the structure in which `D(E, d)`, its
localization and the dévissage of Tag 0FQE are all read is
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, whose distinguished triangles are
the cone triangles. The two classes of triangles are **different**, provably: they are the two
sign conventions for the third arrow, and Tag 09KH is not a comparison of them but the statement
that the admissible class is pretriangulated. See the docstring of
`AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_isTriangulated'` below for the
witness and for why neither structure can be exchanged for the other here. The cone-triangle
exactness of a differential graded tensor functor is proved in this repository only for a
bimodule over a differential graded algebra, in
`DifferentialGraded.Bimodule.tensorQuotientLift_isTriangulated`, by a bespoke comparison of the
tensor product of a cone with the cone of a tensor product.


*What the exactness of the derived functor needs.* The resolution clause that
`CategoryTheory.Functor.isTriangulated_of_rightExtension` asks for is
`AlgebraicGeometry.RingedSite.exists_distTriang_isIso_tensorWithComplexDerivedCounit`, in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist`; it is stated there,
not here, because the twisted exactness and the vacuous statement below consume the same clause
and it is about the right extension rather than about quasi-coherence.

*Why the instances are restated.* `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory`
is a `def`, so instance search does not see the composite `- ⊗_E K` followed by `Qh` inside it;
the commutation with the translation and the exactness of that composite are therefore seated by
hand, with the composite spelled out in a `show`.

*The regular module.* The dévissage is stated at `DifferentialGradedModule.regularModule`, while
the value of `- ⊗_E^𝐋 K` is computed in the staged reduction at `Hom(K, K)` viewed as a module
over itself, which is how the endomorphism algebra enters Tag 09LX. The two are identified by
`DGCategory.representableSelfIsoRegular`.

## References

* [Stacks Project, Tag 09MA](https://stacks.math.columbia.edu/tag/09MA)
* [Stacks Project, Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE), the dévissage.
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX), the functor.
* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW), its underived form, and
  [Tag 09KH](https://stacks.math.columbia.edu/tag/09KH), the pretriangulated structure on
  `K(Mod_(E, d))` whose distinguished triangles come from admissible short exact sequences.
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1), the two closure
  properties of quasi-coherence that are assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- Quasi-coherence of an `O`-module, for the ambient category of `O`-modules in which the
tensor products of Tag 09LX are formed: the site-level notion of Tag 03DL, whose module universe
is free. -/
abbrev tensorModOQuasicoherent : ObjectProperty (TensorModO.{u, v, w, t, s} X) :=
  SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- `D_QCoh(O)`: the objects of `D(O)` all of whose cohomology sheaves are quasi-coherent, for
the ambient category of `O`-modules in which the tensor products of Tag 09LX are formed. -/
abbrev tensorModOQuasicoherentDerived :
    ObjectProperty (DerivedCategory (TensorModO.{u, v, w, t, s} X)) :=
  DerivedCategoryB.derivedCategoryB (tensorModOQuasicoherent.{u, v, w, t, s} X)

/-! ### The derived tensor product is exact -/

/-- Tensoring with `K` followed by localization of the target is exact, both of its two factors
being so.

The exactness of tensoring with `K` itself is the hypothesis `hexact`, **and that hypothesis
cannot be satisfied**, so this statement and its consumer
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated` are vacuous as they
stand.

Tag 09LW is formalized as
`AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_isTriangulated` against
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, the pretriangulated structure on
`K(Mod_(E, d))` whose distinguished triangles come from admissible short exact sequences, whereas
the structure in force here — the one in which `D(E, d)` and its dévissage are read — is
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, whose distinguished triangles are
the cone triangles. **Those two classes are different, provably.** They are the two sign
conventions for the third arrow of the triangle of a homomorphism — a triangle lies in one
exactly when negating its third arrow gives a triangle in the other, which is
`DifferentialGradedModule.mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃` —
and negating the third arrow does *not* preserve the class: over `A = ℤ` concentrated in degree
`0` and `f = 3 : ℤ[0] ⟶ ℤ[0]` the groups `Hom_K(C, C)`, `Hom_K(L, C)` and `Hom_K(C, K[1])` are
all `ℤ/3`, so an isomorphism of triangles `(𝟙, 𝟙, c) : (f, i, -p) → (f, i, p)` would force
`c = 1` from `i ≫ c = i` and hence `1 = -1` in `ℤ/3`. Since `F.mapTriangle` of a cone triangle is
the third-arrow negation of `F.mapTriangle` of the corresponding admissible triangle, no functor
can be exact for both.

The two classes are not identified by Tag 09KH. Tag 09KH is formalized, as
`DifferentialGradedModule.exists_pretriangulated_structure`, and it is not an identification of
two classes at all: it is the statement that `K(Mod_(A, d))` is pretriangulated with the
admissible class, whose chosen instance is
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`.

What does transfer between the two structures is precomposition with the sign-twisted identity
`DifferentialGradedModule.signTwist`, whose `mapTriangle` is exactly the negation of the third
arrow: `DifferentialGradedModule.mapTriangle_mem_distTriang_of_isTriangulated` extracts the
pointwise hypothesis from Tag 09LW and
`DifferentialGradedModule.isTriangulated_signTwist_comp` turns it into exactness of
`signTwist _ ⋙ -` for the cone structure. There is no way to keep *this* statement and change
only the triangle class: the exactness of a functor is a statement about the comparison with the
translation that the functor carries, and the comparison is what the twist changes.

The exactness statement that does hold is in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist`, and it
**composes** with the twist rather than substituting it into the definition:
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated` is the
unconditional exactness of `- ⊗_E^𝐋 K ⋙ signTwist _`. Since `CategoryTheory.signTwist` is the
identity on objects and on morphisms, no definition changes and no existing statement moves — in
particular the carriers of Tag 09LX and of the maps on `Ext` of Tag 0CS6 in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived` are untouched, and no sign
flips at odd shifts. *Redefining* the functor being derived, as
`signTwist _ ⋙ tensorWithComplexHomotopy X ℤ K ⋙ DerivedCategory.Qh`, would move them, which
is why it is not done.

*Restating the consumer in the other structure is not an option either, though not because of
the shift.* The shift is no obstacle:
`DifferentialGradedModule.instHasShiftIntHomotopyCategory` *is*
`CategoryTheory.HasShift.quotient (DifferentialGradedModule.homotopyRel _) ℤ` — it is declared as
`inferInstanceAs` of it — the two are equal by `rfl` with nothing unsealed, and both are
instances, so they are interchangeable in the type of `CategoryTheory.Functor.IsTriangulated`.
Pinning `DifferentialGradedModule.instPretriangulatedHomotopyCategory'` in this file does make
`hexact` satisfiable: `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_isTriangulated`
then typechecks against it at the universes used here, which are not the diagonal ones, the
admissible structure being available at three independent universes.

What breaks instead is `D(E, d)` itself. Its triangulation is
`CategoryTheory.Triangulated.Localization.pretriangulated` applied to the *cone* structure, and
Mathlib supplies the additivity of the shift functors of a localization only under
`CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation`, which this library has for the
cone structure alone (`DifferentialGradedModule.quasiIsomorphisms_isCompatibleWithTriangulation`,
proved through `DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`). With the admissible
structure pinned, `∀ n : ℤ, (shiftFunctor (derivedCategory (Rep X K).algebra) n).Additive` fails
to synthesize, so `CategoryTheory.Pretriangulated (derivedCategory (Rep X K).algebra)` cannot be
formed at all and no statement about `D(E, d)` can be written down. Supplying the compatibility
for the admissible structure too would not help: it would make the triangulation of `D(E, d)` a
*second*, different structure, whereas the dévissage of Tag 0FQE, the weak generation of
`D(E, d)` by the regular module and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_fullyFaithful` are all read in the
cone-induced one. -/
theorem tensorWithComplexToDerivedCategory_isTriangulated'
    (hexact : (tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K).IsTriangulated) :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).IsTriangulated :=
  let := hexact
  show (tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙
    DerivedCategory.Qh (C := TensorModO.{u, v, w, t, s} X)).IsTriangulated from inferInstance

/-- **The derived tensor product is exact**: `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` carries distinguished
triangles to distinguished triangles.

The resolution of a morphism of `D(E, d)` that
`CategoryTheory.Functor.isTriangulated_of_rightExtension` asks for is
`AlgebraicGeometry.RingedSite.exists_distTriang_isIso_tensorWithComplexDerivedCounit`.

**The hypothesis `hexact` cannot be satisfied**, so this statement is vacuous; the sign-twisted
repair, which is unconditional, is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated` in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist`, and that is what
Tag 09MA below uses. Nothing uses this statement; it is kept, untagged, as the record of what the
twist is for, and it cannot be repaired in place — what it concludes is the exactness of the
*untwisted* functor, which is what the sign obstruction makes false. -/
theorem tensorWithComplexDerived_isTriangulated
    (hexact : (tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K).IsTriangulated) :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).IsTriangulated := by
  have := tensorWithComplexToDerivedCategory_isTriangulated'.{u, v, w, t, s} X K hexact
  exact Functor.isTriangulated_of_rightExtension
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K)
    (tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K)
    (fun {_ _} g => exists_distTriang_isIso_tensorWithComplexDerivedCounit.{u, v, w, t, s} X K g)

/-! ### The dévissage -/

/-- **Stacks 09MA**, and with it the content of section **09M9** that this file delivers. *"Let
`S` be a scheme, `X` an algebraic space over `S`. Let `K` be a complex of `O_X`-modules whose
cohomology sheaves are quasi-coherent. Let `(E, d) = Hom(K, K)` be the endomorphism differential
graded algebra. Then the functor `- ⊗_E^𝐋 K : D(E, d) ⟶ D(O_X)` of Tag 09LX has image contained
in `D_QCoh(O_X)`."*

The dévissage is the source's: a differential graded `E`-module with property (P) is the
homotopy colimit of the stages of its filtration, each stage carries a finite filtration whose
graded pieces are direct sums of shifts of `E`, and `E[k] ⊗_E K` is `K[k]`. Tag 0FQE packages
exactly that reduction, so what has to be checked is that lying in `D_QCoh(O)` holds at every
shift of the free rank-one module — which is the staged computation
`AlgebraicGeometry.RingedSite.derivedCategoryB_tensorWithComplexDerived_obj_regular` together
with the stability of `D_QCoh(O)` under the translation — is inherited by direct sums, and is
inherited by the third vertex of a distinguished triangle from the other two, the last because
`- ⊗_E^𝐋 K` is exact and `D_QCoh(O)` is a triangulated subcategory of `D(O)`.

Three assumptions are upstream inputs, not pieces of the conclusion: that quasi-coherence is a
weak Serre class and that `hqcsum`, a direct sum of quasi-coherent `O`-modules is quasi-coherent
(the two clauses of Tag 03M1, the first as a typeclass assumption so that instance search
supplies it where this repository has it); and `htensorSum`, that tensoring with `K` carries a
direct sum of differential graded `E`-modules to a direct sum in `D(O)` (the differential graded
half of which is Tag 09LV, formalized as
`AlgebraicGeometry.RingedSite.tensorWithComplexDG_preservesCoproducts`). The hypothesis
`hK` is the source's own, that the cohomology sheaves of `K` be quasi-coherent, stated for the
complex `liftComplex X K` that the functor tensors with.

Exactness of `- ⊗_E^𝐋 K`, which the two-out-of-three step needs, is **not assumed**. As a
hypothesis `hexact`, Tag 09LW read against the pretriangulated structure that is not the one in
force here, it would be unsatisfiable and this statement vacuous. What discharges it is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated`, the
unconditional exactness of `- ⊗_E^𝐋 K` composed with the sign-twisted identity of `D(O)`: that
composite has the same action on objects and on morphisms, so its image of a distinguished
triangle has the same three vertices, which is all this step uses of it. -/
@[stacks 09MA "RESTRICTED: assumes 03M1, 09LV", stacks 09M9 "RESTRICTED: 75.17.1 only"]
theorem derivedCategoryB_tensorWithComplexDerived_obj
    [ObjectProperty.IsWeakSerreClass (tensorModOQuasicoherent.{u, v, w, t, s} X)]
    (hqcsum : ∀ {ι : Type (max u v w t s)} (Mf : ι → TensorModO.{u, v, w, t, s} X)
      (c : Cofan Mf), IsColimit c →
      (∀ i, tensorModOQuasicoherent.{u, v, w, t, s} X (Mf i)) →
      tensorModOQuasicoherent.{u, v, w, t, s} X c.pt)
    (htensorSum : ∀ {ι : Type (max u v w t s)} [DecidableEq ι]
      (N : ι → DifferentialGradedModule.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra),
      IsColimit ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
        tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).mapCocone
          (Cofan.mk (General.directSumObj N) (General.directSumInj N))))
    (hK : tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (M : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :
    tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj M) := by
  classical
  let _hgr : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hqc : WeakSerre.IsWeakSerre (tensorModOQuasicoherent.{u, v, w, t, s} X) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc
  have hqcsum' : ∀ {ι : Type (max u v w t s)} (Mf : ι → TensorModO.{u, v, w, t, s} X),
      (∀ i, tensorModOQuasicoherent.{u, v, w, t, s} X (Mf i)) →
      tensorModOQuasicoherent.{u, v, w, t, s} X (∐ Mf) := fun Mf hMf =>
    hqcsum Mf _ (coproductIsCoproduct Mf) hMf
  have hqcsumDerived : ∀ {ι : Type (max u v w t s)}
      (D : Discrete ι ⥤ DerivedCategory (TensorModO.{u, v, w, t, s} X)) (c : Cocone D),
      IsColimit c →
      (∀ i, tensorModOQuasicoherentDerived.{u, v, w, t, s} X (D.obj i)) →
      tensorModOQuasicoherentDerived.{u, v, w, t, s} X c.pt := by
    intro ι D c hc hD
    let _ := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
      (TensorModO.{u, v, w, t, s} X) ι
    refine hcl.of_iso (hc.coconePointUniqueUpToIso (colimit.isColimit D) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := D))).symm ?_
    exact Stacks.Duality.derivedCategoryB_prop_coproduct (TensorModO.{u, v, w, t, s} X)
      (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc hqcsum' _ (fun i => hD ⟨i⟩)
  refine General.property_of_coproducts_of_two_out_of_three_of_shifts
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
    (fun N => tensorModOQuasicoherentDerived.{u, v, w, t, s} X
      ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj N)) ?_ ?_ ?_ M
  · intro ι Mfam hMfam
    choose P f hf hP using fun i =>
      General.exists_isQuasiIsomorphism_leftOrthogonal (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
        (((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.objPreimage (Mfam i)).as)
    have hisof : ∀ i, IsIso ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).map (f i)) :=
      fun i => General.isIso_q_map_of_isQuasiIsomorphism (f i) (hf i)
    let e : ∀ i, (toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).obj (P i) ≅ Mfam i := fun i =>
      asIso ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).map (f i)) ≪≫
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.objObjPreimageIso (Mfam i)
    have hcomp : ∀ P Y (e : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj P ≅ Y)
        (hP : (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal P),
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj Y ≅
          (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).obj P := by
      intro P Y e hP
      have := isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _ hP
      exact ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso e).symm ≪≫
        asIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app _)
    let β : Discrete.functor P ⋙ (toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q) ≅ Discrete.functor Mfam :=
      Discrete.natIso (fun i => e i.as)
    let eSum : (toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).obj
          (General.directSumObj P) ≅ ∐ Mfam :=
      (General.isColimit_q_mapCocone_directSumObj P hP).coconePointUniqueUpToIso
        ((IsColimit.precomposeHomEquiv β _).symm (colimit.isColimit (Discrete.functor Mfam)))
    exact hcl.of_iso
      (hcomp _ _ eSum (General.leftOrthogonal_acyclic_directSumObj P hP)).symm
      (hqcsumDerived _ _ (htensorSum P) fun ⟨i⟩ => hcl.of_iso (hcomp _ _ (e i) (hP i)) (hMfam i))
  · intro Δ hΔ
    have := tensorWithComplexDerived_signTwist_isTriangulated.{u, v, w, t, s} X K
    have hmap := (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).map_distinguished Δ hΔ
    have htri := DerivedCategoryB.derivedCategoryB_isTriangulated
      (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc
    refine ⟨fun h₁ h₂ => ?_, fun h₁ h₃ => ?_, fun h₂ h₃ => ?_⟩
    · exact (tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₃
        _ hmap h₁ h₂
    · exact (tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₂
        _ hmap h₁ h₃
    · exact (tensorModOQuasicoherentDerived.{u, v, w, t, s} X).ext_of_isTriangulatedClosed₁
        _ hmap h₂ h₃
  · intro k
    have hreg := derivedCategoryB_tensorWithComplexDerived_obj_regular.{u, v, w, t, s} X K hK
    have h0 : tensorModOQuasicoherentDerived.{u, v, w, t, s} X
        ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).obj
              (regularModule (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))) :=
      hcl.of_iso
        ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).mapIso
              DGCategory.representableSelfIsoRegular)) hreg
    exact hcl.of_iso
      (((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).commShiftIso k).app _).symm
      (DerivedCategoryB.derivedCategoryB_shift_mem
        (tensorModOQuasicoherent.{u, v, w, t, s} X) hqc k h0)

end AlgebraicGeometry.RingedSite

end
