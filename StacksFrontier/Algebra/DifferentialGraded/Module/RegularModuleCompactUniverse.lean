module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents

/-! # The regular module is a compact object at every index universe

Let `(A, d)` be a differential graded algebra over a commutative ring `R : Type u`.
`DifferentialGradedModule.isCompactObject_q_regularModule` says that the image of the regular
module in `D(A, d)` is a compact object *tested against families indexed by a type of `Type u`*,
that being the universe in which the bundled encoding of [Stacks, Tag 09JJ] provides direct sums.
This file removes the restriction: the image of the regular module is `IsCompactObject.{w}` for an
**arbitrary** universe `w`, and so is every retract of it. Compactness of the regular module
therefore does not depend on how the index sets of the source's direct sums are read.

*The mechanism.* Compactness of `K` is the bijectivity of the maps
`⨁ᵢ (K ⟶ Fᵢ) → (K ⟶ ∐ᵢ Fᵢ)` for families admitting a direct sum, and for `K = Q(A)` the
cohomological description of those groups bounds how large such a family can be. Indeed
`Hom_{D(A, d)}(A, X[n])` is the degree-`n` cohomology `H^n(X)`, a module of `Type u`
(`DifferentialGradedModule.cohomologyLinearEquivHomRegular`), and the shifts of the regular module
generate `D(A, d)` (`DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`), so a
nonzero member `Fᵢ` of the family receives a nonzero morphism from some shift `A[n]`. Composition
with the coprojections of the `n`-shifted cofan is injective on morphisms out of `A`
(`CategoryTheory.injective_cofanMap`, which is formal for any colimit cofan), so those nonzero
members inject into `Σ n : ℤ, H^n(∐ᵢ Fᵢ)`, a type of `Type u`: however large the index universe,
only `Type u`-many members of a family with a direct sum are nonzero. The remaining members are
zero objects and can be dropped from the cofan without disturbing its colimit property, which
reduces the test map to one indexed by a type of `Type u`.

## Main results

* `CategoryTheory.isColimitCofanSubtype`: a colimit cofan restricted to a subfamily whose
  complement consists of zero objects is again a colimit cofan.
* `CategoryTheory.isCompactObject_of_small_nonzero_index`: compactness transfers from one index
  universe to another, provided that every family admitting a direct sum carries a nonzero object
  at only small many of its indices.
* `DifferentialGradedModule.small_hom_shift_q_regularModule`: the morphisms of `D(A, d)` from the
  regular module to a shift of an object form a `Type u`-small type, being its cohomology.
* `DifferentialGradedModule.exists_hom_q_regularModule_ne_zero_of_not_isZero`: a nonzero object of
  `D(A, d)` receives a nonzero morphism from some shift of the regular module.
* `DifferentialGradedModule.small_nonzero_index_of_isColimitCofan`: in a colimit cofan of
  `D(A, d)` indexed by an arbitrary type, the indices carrying a nonzero object form a
  `Type u`-small type.
* `DifferentialGradedModule.isCompactObject_q_regularModule_arbitraryUniverse`: **the image of the
  regular module in `D(A, d)` is a compact object at an arbitrary index universe.**
* `DifferentialGradedModule.isCompactObject_of_retract_q_regularModule`: hence so is every retract
  of it — the formal form of the source's step that a direct summand of `A` is compact
  ([Stacks, Tag 09QH]).

## Implementation notes

*Why the index universe of Tag 09QI is not widened instead.* The bundled encoding of Tag 09JJ is
single-universe: the direct sum of a `Type w`-indexed family of modules whose carriers are in
`Type u` has carrier in `Type (max u w)`, so for `w > u` such a family has in general no direct
sum in `Mod_{(A,d)}` at all, and `DifferentialGradedModule.directSumObj` cannot even be formed.
Nothing is lost: `CategoryTheory.IsCompactObject` tests only families that *do* admit a direct
sum, and the content of the result below is that such a family, however large its index type,
has only `Type u`-many nonzero members.

*Where the general lemmas live.* `CategoryTheory.isColimitCofanSubtype` and
`CategoryTheory.isCompactObject_of_small_nonzero_index` are statements about compact objects in a
preadditive category and not about differential graded modules. They are kept here rather than in
`StacksFrontier/CategoryTheory/Triangulated/CompactObjects.lean` because the smallness hypothesis of
the second is discharged only by the cohomological computation of this file, which is specific to
`D(A, d)`.

*Shifting the cofan rather than the object.* The detection of nonzero objects uses the morphisms
`A ⟶ Fᵢ[n]`, not `A[n] ⟶ Fᵢ`, so the cofan that has to be recognised as a colimit is the
`n`-shifted one; that is `CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit` for the shift
functor, which preserves direct sums because it is an equivalence. The alternative — shifting the
regular module — would require transporting the representability isomorphism along the shift
adjunction, which this file would otherwise have no use for.

## References

* [Stacks Project, Tag 09QH](https://stacks.math.columbia.edu/tag/09QH), that a direct summand of
  a compact object is compact.
* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI), that direct sums in
  `D(A, d)` are computed on modules, which is what makes the regular module compact in the first
  place.
* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5), through which the
  morphisms out of the regular module are identified with cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v u

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- **A colimit cofan restricted to a subfamily whose complement consists of zero objects is again
a colimit cofan.** A family of morphisms out of the members indexed by `p` extends to the whole
family by zero, uniquely, because a morphism out of a zero object is unique. -/
def isColimitCofanSubtype {I : Type w} {E : I → D} {S : D} (j : ∀ i, E i ⟶ S)
    (hc : IsColimit (Cofan.mk S j)) (p : I → Prop) (hzero : ∀ i, ¬ p i → IsZero (E i)) :
    IsColimit (Cofan.mk S fun i : Subtype p => j i.1) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun t => hc.desc (Cofan.mk t.pt fun i => if h : p i then t.inj ⟨i, h⟩ else 0))
    (fun t i => ?_) (fun t m hm => ?_)
  · exact (hc.fac (Cofan.mk t.pt fun i => if h : p i then t.inj ⟨i, h⟩ else 0) ⟨i.1⟩).trans
      (dite_eq_left i.2)
  · refine hc.uniq (Cofan.mk t.pt fun i => if h : p i then t.inj ⟨i, h⟩ else 0) m fun i => ?_
    obtain ⟨i⟩ := i
    change j i ≫ m = if h : p i then t.inj ⟨i, h⟩ else 0
    by_cases h : p i
    · rw [dite_eq_left h]
      exact hm ⟨i, h⟩
    · rw [dite_eq_right h]
      exact (hzero i h).eq_of_src _ _

/-- **Compactness transfers from one index universe to another** as soon as every family indexed
by a type of the new universe `w` and admitting a direct sum carries a nonzero object at only
`w'`-small many of its indices, `w'` being the universe at which compactness is known.

Injectivity of the test map is formal (`CategoryTheory.injective_cofanMap`). For surjectivity the
indices carrying a zero object are dropped (`CategoryTheory.isColimitCofanSubtype`), the remaining
ones are reindexed by a type of `Type w'` (`CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv`),
and the compactness already available applies to the reindexed cofan
(`CategoryTheory.bijective_cofanMap`); a morphism factoring through finitely many of the
surviving members factors through finitely many members of the original family. -/
lemma isCompactObject_of_small_nonzero_index {K : D} (hK : IsCompactObject.{w'} K)
    (h : ∀ {I : Type w} (E : I → D) [HasCoproduct E], Small.{w'} {i : I // ¬ IsZero (E i)}) :
    IsCompactObject.{w} K := by
  classical
  constructor
  intro I _ E _
  change Function.Bijective (cofanMap K (Limits.Sigma.ι E))
  refine ⟨injective_cofanMap K _ (coproductIsCoproduct E), fun f => ?_⟩
  have := h E
  set p : I → Prop := fun i => ¬ IsZero (E i)
  let ε : Shrink.{w'} (Subtype p) ≃ Subtype p := (equivShrink (Subtype p)).symm
  have hc : IsColimit (Cofan.mk (∐ E) fun x => Limits.Sigma.ι E (ε x).1) :=
    Cofan.isColimitEquivOfEquiv ε _
      (isColimitCofanSubtype _ (coproductIsCoproduct E) p fun _ hi => not_not.1 hi)
  obtain ⟨y, hy⟩ := (bijective_cofanMap K hK _ hc).2 f
  refine ⟨DirectSum.toAddMonoid (fun x => DirectSum.of (fun i => (K ⟶ E i)) (ε x).1) y, ?_⟩
  have key : (cofanMap K (Limits.Sigma.ι E)).comp
      (DirectSum.toAddMonoid fun x => DirectSum.of (fun i => (K ⟶ E i)) (ε x).1)
      = cofanMap K fun x => Limits.Sigma.ι E (ε x).1 := by
    refine DirectSum.addHom_ext fun x z => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.toAddMonoid_of, cofanMap_of]
  exact (DFunLike.congr_fun key y).trans hy

end CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- **The morphisms of `D(A, d)` from the regular module into a shift form a `Type u`-small
type**: they are the cohomology of the target, which is a module over `R : Type u`. The morphisms
of `D(A, d)` themselves live in `Type (u + 1)`, so this is a genuine restriction on their
cardinality, and it is what bounds the size of a family admitting a direct sum. -/
lemma small_hom_shift_q_regularModule (X : derivedCategory' A) (n : ℤ) :
    Small.{u} ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶ X⟦n⟧) :=
  small_of_injective (f := (cohomologyLinearEquivHomRegular A n X).symm)
    (cohomologyLinearEquivHomRegular A n X).symm.injective

/-- **A nonzero object of `D(A, d)` receives a nonzero morphism from some shift of the regular
module**: the shifts of the regular module weakly generate `D(A, d)`
(`DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`). -/
lemma exists_hom_q_regularModule_ne_zero_of_not_isZero {X : derivedCategory' A}
    (hX : ¬ IsZero X) :
    ∃ (n : ℤ) (f : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶
      X⟦n⟧), f ≠ 0 := by
  by_contra! hcon
  exact hX ((ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero
    ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))).1
    (isWeakTriangulatedGenerator_q_regularModule A) X hcon)

/-- **In a colimit cofan of `D(A, d)` indexed by an arbitrary type, the indices carrying a nonzero
object form a `Type u`-small type.**

For each degree `n` the indices carrying an object which receives a nonzero morphism from `A[n]`
inject into the morphisms `A ⟶ S[n]` out of the vertex, by composing a chosen nonzero morphism
with the `n`-shifted coprojection: the test map of the shifted cofan is injective
(`CategoryTheory.injective_cofanMap`), so two indices with the same composite coincide. Those
morphism groups are `Type u`-small (`DifferentialGradedModule.small_hom_shift_q_regularModule`),
and every index carrying a nonzero object occurs in one of the countably many degrees
(`DifferentialGradedModule.exists_hom_q_regularModule_ne_zero_of_not_isZero`). -/
lemma small_nonzero_index_of_isColimitCofan {I : Type w} (E : I → derivedCategory' A)
    (S : derivedCategory' A) (j : ∀ i, E i ⟶ S) (hc : IsColimit (Cofan.mk S j)) :
    Small.{u} {i : I // ¬ IsZero (E i)} := by
  classical
  set K := (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)
  have hJ : ∀ n : ℤ, Small.{u} {i : I // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0} := by
    intro n
    have hs : Small.{u} (K ⟶ S⟦n⟧) := small_hom_shift_q_regularModule A S n
    have hcs : IsColimit (Cofan.mk (S⟦n⟧) fun i => (j i)⟦n⟧') :=
      isColimitCofanMkObjOfIsColimit (CategoryTheory.shiftFunctor (derivedCategory' A) n) E j hc
    refine small_of_injective
      (f := fun x : {i : I // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0} => x.2.choose ≫ (j x.1)⟦n⟧')
      fun a b hab => Subtype.ext ?_
    by_contra hne
    have hof : DirectSum.of (fun i => (K ⟶ (E i)⟦n⟧)) a.1 a.2.choose
        = DirectSum.of (fun i => (K ⟶ (E i)⟦n⟧)) b.1 b.2.choose := by
      refine injective_cofanMap K (fun i => (j i)⟦n⟧') hcs ?_
      rwa [cofanMap_of, cofanMap_of]
    have hsame := DFunLike.congr_fun hof a.1
    rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hne] at hsame
    exact a.2.choose_spec hsame
  choose nn ff hff using fun x : {i : I // ¬ IsZero (E i)} =>
    exists_hom_q_regularModule_ne_zero_of_not_isZero A x.2
  exact small_of_injective
    (f := fun x : {i : I // ¬ IsZero (E i)} =>
      (⟨nn x, ⟨x.1, ff x, hff x⟩⟩ : Σ n : ℤ, {i : I // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0}))
    fun a b hab => Subtype.ext
      (congrArg (fun x : (Σ n : ℤ, {i : I // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0}) => (x.2 : I)) hab)

/-- **The regular module is a compact object of the derived category at an arbitrary index
universe.** Let `(A, d)` be a differential graded algebra over a commutative ring `R : Type u`.
For every universe `w` and every family `Fᵢ`, `i ∈ I`, of objects of `D(A, d)` indexed by a type
`I : Type w` and admitting a direct sum, the canonical map
`⨁ᵢ Hom(A, Fᵢ) → Hom(A, ∐ᵢ Fᵢ)` is bijective.

This is `DifferentialGradedModule.isCompactObject_q_regularModule`, which tests families indexed
by `Type u`, combined with the observation that a family admitting a direct sum has only
`Type u`-many nonzero members
(`DifferentialGradedModule.small_nonzero_index_of_isColimitCofan`). -/
theorem isCompactObject_q_regularModule_arbitraryUniverse :
    IsCompactObject.{w}
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) :=
  isCompactObject_of_small_nonzero_index (isCompactObject_q_regularModule A)
    fun E => small_nonzero_index_of_isColimitCofan A E (∐ E) (Limits.Sigma.ι E)
      (coproductIsCoproduct E)

/-- **A retract of the image of the regular module is a compact object of `D(A, d)` at an
arbitrary index universe.** This is the source's step that a direct summand of `A` is compact
([Stacks, Tag 09QH]), in a form that quantifies over the index universe: the retraction splits the
compactness test map (`CategoryTheory.isCompactObject_of_retract`), at whatever universe it is
taken. -/
theorem isCompactObject_of_retract_q_regularModule {E : derivedCategory' A}
    (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))
    (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶ E)
    (hir : i ≫ r = 𝟙 E) : IsCompactObject.{w} E :=
  isCompactObject_of_retract (isCompactObject_q_regularModule_arbitraryUniverse A) i r hir

end DifferentialGradedModule

end
