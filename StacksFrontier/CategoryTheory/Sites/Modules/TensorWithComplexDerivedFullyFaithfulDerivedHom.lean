module

public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompactUniverseGeneral
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceExampleEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 09LZ for the derived Hom adjunction

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. [Stacks,
Tag 09LZ] says that if

1. `K` represents a compact object of `D(O)`, and
2. `E` computes the ext groups of `K` in `D(O)`,

then the derived tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived` (Tag 09LX) is fully faithful.

`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_fullyFaithful` proves this from a right
adjoint supplied as a hypothesis, together with the dévissage of `D(E, d)`, its direct sums and
the weak generation of `D(E, d)` by the regular module. This file takes that right adjoint to be
the derived Hom `RHom(K, -)` of Tag 09LK and supplies those inputs, leaving the statement with
the hypotheses the source has.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_fullyFaithful_of_ext`: **Stacks 09LZ**
  with the adjunction of Tag 09LY and the dévissage of Tag 0FQE supplied rather than assumed,
  and with **exactly the source's two hypotheses** and nothing else — hypothesis (1) being the
  compactness of `K` in `D(O)` itself.

## Implementation notes

*The inputs supplied.* Seven of the ten arguments of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_fullyFaithful`:

* the right adjoint `G` and the adjunction `- ⊗_E^𝐋 K ⊣ G` of **Tag 09LY** are
  `AlgebraicGeometry.RingedSite.derivedHomWithComplex` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplex`, which is
  unconditional;
* the commutation of `RHom(K, -)` with the translation is the one that adjunction induces,
  `Stacks.AlgebraicGeometry.ProjectiveGenerator.derivedHomWithComplexCommShift`;
* the compatibility of the adjunction with the translation is
  `CategoryTheory.Adjunction.commShift_of_leftAdjoint`;
* the dévissage of **Tag 0FQE** is
  `DifferentialGradedModule.General.property_of_coproducts_of_two_out_of_three_of_shifts`, the
  form of that tag with the carrier of the algebra in a universe of its own, which is what the
  endomorphism algebra of a complex of sheaves — an algebra over `ℤ` with carrier in the section
  universe of the site — needs;
* the direct sums of `D(E, d)` are
  `DifferentialGradedModule.General.hasCoproducts_derivedCategory`, found by instance search in
  the same shape;
* the weak generation of `D(E, d)` by the regular module is
  `Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule`,
  the independent-universe cone-triangle form of
  `DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`.

Beyond those seven, the commutation of `RHom(K, -)` with direct sums is *derived* from the
source's hypothesis (1) rather than assumed. `K` is compact in `D(O)`, the regular module `E` is
compact in `D(E, d)` at an arbitrary index universe by
`DifferentialGradedModule.General.isCompactObject_q_regularModule_arbitraryUniverse` — the
independent-universe form, which is what the endomorphism algebra of a complex of sheaves, an
algebra over `ℤ` with carrier in the section universe of the site, needs — and `E ⊗_E^𝐋 K = K`
by `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedObjRegularIso`, so the left adjoint
carries a compact weak generator to a compact object and
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` gives the
commutation. The two structural facts that step needs about `D(O)` — that it has direct sums
indexed by the module universe, and that `- ⊗_E^𝐋 K` is additive — are derived too: the first
from `Stacks.SheafOfModules.sheafModulesGrothendieck` through
`Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory`, the second from the exactness below
(Mathlib derives additivity from exactness), which also gives the additivity of the right
adjoint through `CategoryTheory.Adjunction.right_adjoint_additive`.

*Exactness, and the sign twist that supplies it.* Exactness of `RHom(K, -)` is not a
hypothesis of the source, and it is derived here, as follows.

Exactness of `- ⊗_E^𝐋 K` for the pretriangulated structure `D(E, d)` carries — the one induced
from the cone triangles of `K(Mod_(E, d))` — is **false**, because Tag 09LW supplies exactness
for the other of the two sign conventions for the third arrow of a triangle;
that is why `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated` has an
unsatisfiable hypothesis, and, the two exactnesses being interchangeable through the adjunction
(`CategoryTheory.Adjunction.isTriangulated_leftAdjoint` and
`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`), why exactness of `RHom(K, -)` for that
structure would be an unsatisfiable hypothesis too.

What *is* true, and unconditional, is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated`: `- ⊗_E^𝐋 K`
composed with the sign-twisted identity `CategoryTheory.signTwist` of `D(O)` is exact. That twist
is the identity on objects and on morphisms, carrying only the shift comparison `ε(n) = (-1)^n`,
so nothing is redefined: `- ⊗_E^𝐋 K` is still the functor of
Tag 09LX and the maps on `Ext` of Tag 0CS6 are untouched. The adjunction of Tag 09LY is read as
an adjunction between the twisted composites by
`CategoryTheory.Adjunction.compSignTwist`, whose compatibility with the shift is the untwisted
one — the sign appears twice and cancels, `CategoryTheory.Adjunction.commShift_compSignTwist` —
and `CategoryTheory.Adjunction.isTriangulated_rightAdjoint` then gives the exactness of the
twisted right adjoint, which is what
`CategoryTheory.Adjunction.fullyFaithfulL_of_devissage` is applied to. Its conclusion,
`(- ⊗_E^𝐋 K ⋙ signTwist _).FullyFaithful`, *is* `(- ⊗_E^𝐋 K).FullyFaithful`: full faithfulness
does not mention the comparison with the shift, so the two are the same statement by definitional
equality.

*The hypotheses.* There are two, and both are the source's own.

* `hExt` is the source's hypothesis (2), that `E` computes the ext groups of `K`, read as
  bijectivity of `- ⊗_E^𝐋 K` on the morphism groups `Hom_{D(E, d)}(E, E[n])`. This is the same
  shape as hypothesis (2) of Tag 09R9 in
  `DifferentialGraded.Bimodule.derivedTensorFunctor_fullyFaithful`, and it is the source's
  hypothesis read through the identifications `H^n(E) = Hom_{D(E, d)}(E, E[n])` and
  `E ⊗_E^𝐋 K = K`.
* `hcompact` is the source's hypothesis (1), **in the source's own words**: `K` represents a
  compact object of `D(O)`. The consequence the source's proof draws from compactness,
  `PreservesColimitsOfShape (Discrete ι) (RHom(K, -))`, is derived from it as above.

Nothing else is assumed. In particular the exactness of neither functor is a hypothesis; see
above, and `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated` for
the twist that supplies it.

## References

* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ), the result stated here.
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX) for the functor,
  [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK) for derived Hom,
  [Tag 09LY](https://stacks.math.columbia.edu/tag/09LY) for the adjunction,
  [Tag 09R9](https://stacks.math.columbia.edu/tag/09R9) for the same statement over a
  differential graded algebra, [Tag 07RB](https://stacks.math.columbia.edu/tag/07RB) for the
  criterion of full faithfulness, [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE) for the
  dévissage, [Tag 07LS](https://stacks.math.columbia.edu/tag/07LS) for compact objects and
  [Tag 09KH](https://stacks.math.columbia.edu/tag/09KH) for the pretriangulated structure on
  `K(Mod_(E, d))` with the admissible class of triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- **Stacks 09LZ.** *"Let `(C, O)` be a ringed site. Let `K` be a complex of `O`-modules.
Assume (1) `K` represents a compact object of `D(O)`, and (2)
`E = Hom_{Comp^dg(O)}(K, K)` computes the ext groups of `K` in `D(O)`. Then the functor
`- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Lemma 09LX is fully faithful."*

The functor is the one Tag 09LX constructs,
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived`, and the right adjoint through which the
source's proof runs is the derived Hom `RHom(K, -)` of Tag 09LK, the adjunction between them
being the unconditional
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplex` of Tag 09LY.

The source's two hypotheses are its two hypotheses here: `hcompact` is (1), that `K` represents a
compact object of `D(O)`, and `hExt` is (2), read as the bijectivity of the functor on the
morphism groups `Hom_{D(E, d)}(E, E[n])`. The source's proof uses (1) only through the
commutation of the right adjoint with direct sums, and that commutation is derived here rather
than assumed: the regular module `E` is a compact weak generator of `D(E, d)` and
`- ⊗_E^𝐋 K` sends it to `K`, so
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` applies.

Exactness of neither functor is assumed. The exactness of `- ⊗_E^𝐋 K` in the pretriangulated
structure in force on `D(E, d)` is false, by a sign; what holds, unconditionally, is the
exactness of its composite with the sign-twisted identity of `D(O)`
(`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated`), and the
adjunction read between the twisted composites carries that to the right adjoint. Since
`CategoryTheory.signTwist` is the identity on objects and on morphisms, the full faithfulness
obtained is full faithfulness of `- ⊗_E^𝐋 K` itself. See the module's implementation notes.

Everything else that
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_fullyFaithful` takes as an argument is
supplied here — the adjunction of Tag 09LY and its commutation
with the translation, the dévissage of Tag 0FQE, the direct sums of `D(E, d)` and the weak
generation of `D(E, d)` by the regular module. See the module's implementation notes.

Full faithfulness is data, a chosen inverse to the action on morphism groups, so this is a
definition. -/
@[stacks 09LZ "exactly the source's two hypotheses and nothing else: (1) is compactness of K in \
D(O), stated as such, and (2) is bijectivity of the functor on Hom(E, E[n]). The adjunction of \
Tag 09LY, the dévissage of Tag 0FQE, the direct sums and the weak generation of D(E, d), the \
commutation of RHom(K, -) with direct sums and the exactness of both functors (Tag 09LW, read \
through the sign-twisted identity of D(O)) are supplied by carriers of this library"]
def tensorWithComplexDerived_fullyFaithful_of_ext
    (hcompact : IsCompactObject.{max u v w t s}
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hExt : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f)) :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).FullyFaithful :=
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
  letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  letI : (derivedHomWithComplex.{u, v, w, t, s} X K).Additive := adj.right_adjoint_additive
  letI := tensorWithComplexDerived_signTwist_isTriangulated.{u, v, w, t, s} X K
  letI : (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
      derivedHomWithComplex.{u, v, w, t, s} X K).IsTriangulated :=
    adj.compSignTwist.isTriangulated_rightAdjoint
  let eReg : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
        ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
          ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))) ≅
      repRegularDerived.{u, v, w, t, s} X K :=
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.mapIso
      ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).mapIso
        DGCategory.representableSelfIsoRegular)
  let eTensor : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        (repRegularDerived.{u, v, w, t, s} X K) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) :=
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso eReg.symm ≪≫
      tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K
  letI : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  letI : HasCoproducts.{max u v w t s} (DerivedCategory (TensorModO.{u, v, w, t, s} X)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory
      (TensorModO.{u, v, w, t, s} X)
  letI : ∀ ι : Type (max u v w t s), PreservesColimitsOfShape (Discrete ι)
      (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
        derivedHomWithComplex.{u, v, w, t, s} X K) :=
    CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map adj
      (repRegularDerived.{u, v, w, t, s} X K)
      (Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{0,
        max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      (General.isCompactObject_q_regularModule_arbitraryUniverse.{max u v w t s, 0,
        max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      (isCompactObject_of_retract hcompact eTensor.hom eTensor.inv eTensor.hom_inv_id)
  show (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).FullyFaithful from
    CategoryTheory.Adjunction.fullyFaithfulL_of_devissage adj.compSignTwist
      (Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{0,
        max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      hExt
      (fun T => General.property_of_coproducts_of_two_out_of_three_of_shifts
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra T)

end AlgebraicGeometry.RingedSite

end
