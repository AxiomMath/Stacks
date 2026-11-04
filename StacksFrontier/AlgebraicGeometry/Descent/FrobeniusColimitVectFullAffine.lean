module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectFaithfulCover
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVectRetract
public import StacksFrontier.CategoryTheory.Functor.FullOfRetract

/-!
# The fullness half of [Stacks, Tag 0EXD], over an affine base

Full faithfulness of the comparison functor of [Stacks, Tag 0EXD] is the cartesianness of a
square of Hom-sets at every pair of finite locally free `colim_F 𝒪_{Spec A}`-modules, and that
square is already known to be cartesian at a pair of modules **trivialised over the whole base**
(`AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator`). The gap
between the two is bridged here, and it is bridged without any Zariski gluing at all.

The reason is that over an *affine* base the gap is not a local-to-global one. Fullness at a pair
of objects is surjectivity of `G.map` on the Hom-set between them, and that surjectivity passes
to **retracts** of the two objects by `CategoryTheory.Functor.full_of_retract`: the lift of
`ψ : G M ⟶ G N` is `i_M ≫ f₀ ≫ r_N`, where `f₀` lifts the conjugate of `ψ` at the ambient pair.
And over an affine base every finite locally free `colim_F 𝒪`-module *is* a retract of a free
one: it comes from a finite locally free `𝒪_{Spec A}`-module by [Stacks, Tag 0EXB]
(`AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso`), that module is a direct summand of a
finite free one because it is a finite projective `A`-module
(`AlgebraicGeometry.Scheme.Vect.exists_retract_free`), and extension of scalars along a
coprojection carries free modules to free modules
(`CategoryTheory.SheafOfModules.pullbackObjFreeIso`) and retracts to retracts, being a functor.

So the trivialising-cover argument — a cover of `Spec A` by basic opens over which both modules
become free, the almost blowup square over each `A_g`, and a gluing of the local solutions — is
what *faithfulness* needs, where it is
`AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_twoGenerator`; fullness does
not need it.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitFreeVectorBundle`: the free `colim_F 𝒪_X`-module of finite
  rank `n`, as an object of the category the comparison functor of [Stacks, Tag 0EXD] starts
  from.

## Main results

* `AlgebraicGeometry.exists_map_eq_frobeniusColimitVectorBundlesComparison_of_isPullback`: a
  cartesian square of Hom-sets at one pair of objects lifts one morphism of the categorical
  fibre product at that pair.
* `AlgebraicGeometry.full_frobeniusColimitVectorBundlesComparison_of_retract`: **the comparison
  functor of a commutative square of schemes in characteristic `p` is full as soon as it is full
  at the pairs of free modules and every module is a retract of a free one.** Stated with the
  square as variables, so that nothing of [Stacks, Example 0EVH] enters.
* `AlgebraicGeometry.exists_retract_frobeniusColimitFree`: **over an affine base every finite
  locally free `colim_F 𝒪`-module is a retract of a free one of finite rank.**
* `AlgebraicGeometry.full_twoGeneratorFrobeniusColimitComparison`: **the comparison functor of
  [Stacks, Tag 0EXD] is full**, under exactly the hypotheses of [Stacks, Example 0EVH]: a ring
  `A`, two elements `f₁, f₂` of it and a prime `p` vanishing in `A`.
* `AlgebraicGeometry.fullyFaithful_twoGeneratorFrobeniusColimitComparison`: **the comparison
  functor of [Stacks, Tag 0EXD] is fully faithful**, that being this file's fullness together
  with `AlgebraicGeometry.faithful_twoGeneratorFrobeniusColimitComparison`. This is one of the
  two halves of the tag, which asserts an equivalence; essential surjectivity is a separate
  matter and no `@[stacks 0EXD]` attribute appears here.

## Implementation notes

The two criteria are stated with the four corners of the square and the four transition functors
as *variables*. That is not presentation: with the concrete corners of
[Stacks, Example 0EVH] substituted, comparing the type of a component `ψ.fst` of a morphism of
the categorical fibre product against the corner of the cartesian Hom-square makes the unifier
unfold the comparison functor through
`CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback` and the
Frobenius colimit at once, and exhausts the `isDefEq` budget. Against variables the same
comparison is immediate, and the instantiation that follows only has to match arguments.

For the same reason the retract over an affine base is assembled from three `have`s with their
types written out rather than as one nested `CategoryTheory.Retract.trans`, whose elaboration
against the declared type exhausts the `whnf` budget.

The distinguished class fed to `CategoryTheory.Functor.full_of_retract` is *equality* to a free
module of finite rank, not isomorphism to one, because the retract produced below lands on the
free module itself; that keeps the fullness hypothesis at the literal free pair, where
`AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator` applies with
`CategoryTheory.Iso.refl` for both trivialisations.

The free module is indexed by `ULift (Fin n)` rather than by an arbitrary finite type, so that
the `Finite` instance which finite local freeness of a free module needs is found by instance
search.

The grading of `A[T₀,T₁]/(f₂T₀ - f₁T₁)` is the one the two-generator square carries,
`(Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded`, introduced by `letI` in
every statement about that square, exactly as in
`Stacks.AlmostBlowUp.twoGenerator_isPullback`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CommRingCat
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **The free `colim_F 𝒪_X`-module of finite rank `n`**, as an object of the category of finite
locally free `colim_F 𝒪_X`-modules that the comparison functor of [Stacks, Tag 0EXD] starts
from. Its finite local freeness is
`AlgebraicGeometry.isFiniteLocallyFreeFrobeniusColimitFree`. -/
abbrev frobeniusColimitFreeVectorBundle {X : Scheme.{u}} (hX : IsInCharacteristic X p) (n : ℕ) :
    frobeniusColimitVectorBundles X p hX :=
  ⟨_root_.SheafOfModules.free (ULift.{u} (Fin n)),
    isFiniteLocallyFreeFrobeniusColimitFree p hX (ULift.{u} (Fin n))⟩

section Square

variable {X X' Z E : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)

/-- **A cartesian square of Hom-sets at one pair of objects lifts one morphism of the categorical
fibre product at that pair.**

A morphism of the categorical fibre product is a pair of morphisms over the centre and over the
modification together with the compatibility over the exceptional corner that
`CategoryTheory.Limits.CategoricalPullback.Hom.w` records, so this is the existence clause of
`CategoryTheory.Limits.Types.isPullback_iff` read through
`CategoryTheory.Limits.CategoricalPullback.hom_ext`. -/
theorem exists_map_eq_frobeniusColimitVectorBundlesComparison_of_isPullback
    (M N : frobeniusColimitVectorBundles X p hX)
    (h : IsPullback
      (↾fun f : M ⟶ N => (frobeniusColimitVectorBundlesPullback p z hZ hX).map f)
      (↾fun f : M ⟶ N => (frobeniusColimitVectorBundlesPullback p b hX' hX).map f)
      (↾fun gg : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj M ⟶
          (frobeniusColimitVectorBundlesPullback p z hZ hX).obj N =>
        (frobeniusColimitVectorBundlesPullback p e hE hZ).map gg ≫
          (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app N)
      (↾fun kk : (frobeniusColimitVectorBundlesPullback p b hX' hX).obj M ⟶
          (frobeniusColimitVectorBundlesPullback p b hX' hX).obj N =>
        (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M ≫
          (frobeniusColimitVectorBundlesPullback p q hE hX').map kk))
    (ψ : (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj M ⟶
      (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj N) :
    ∃ f : M ⟶ N,
      (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).map f = ψ := by
  obtain ⟨f, hf₁, hf₂⟩ := Types.exists_of_isPullback h ψ.fst ψ.snd ψ.w
  exact ⟨f, CategoricalPullback.hom_ext hf₁ hf₂⟩

/-- **The comparison functor of a commutative square of schemes in characteristic `p` is full as
soon as it is full at the pairs of free modules of finite rank and every module is a retract of
such a free module.**

Nothing of [Stacks, Example 0EVH] enters: the four corners and the commutativity are variables.
The content is `CategoryTheory.Functor.full_of_retract` at the class of free modules of finite
rank, the retract hypothesis `hret` landing on such a module on the nose rather than up to
isomorphism, so that `hfree` is needed only at a literal pair of free modules. -/
theorem full_frobeniusColimitVectorBundlesComparison_of_retract
    (hret : ∀ M : frobeniusColimitVectorBundles X p hX,
      ∃ n : ℕ, Nonempty (Retract M (frobeniusColimitFreeVectorBundle p hX n)))
    (hfree : ∀ n m : ℕ,
      ∀ ψ : (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj
            (frobeniusColimitFreeVectorBundle p hX n) ⟶
          (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj
            (frobeniusColimitFreeVectorBundle p hX m),
        ∃ f : frobeniusColimitFreeVectorBundle p hX n ⟶ frobeniusColimitFreeVectorBundle p hX m,
          (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).map f = ψ) :
    (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).Full := by
  refine Functor.full_of_retract _
    (fun M₀ => ∃ n : ℕ, M₀ = frobeniusColimitFreeVectorBundle p hX n) ?_ ?_
  · intro M
    obtain ⟨n, ⟨hr⟩⟩ := hret M
    exact ⟨_, ⟨n, rfl⟩, ⟨hr⟩⟩
  · rintro M₀ N₀ ⟨n, rfl⟩ ⟨m, rfl⟩ ψ
    exact hfree n m ψ

end Square

/-- **Over an affine base every finite locally free `colim_F 𝒪`-module is a retract of a free one
of finite rank.**

By [Stacks, Tag 0EXB] — `AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso`, which applies
because `Spec A` is quasi-compact and quasi-separated — the module is the extension of scalars of
a finite locally free `𝒪_{Spec A}`-module along a coprojection. That module is a direct summand
of a finite free one, since it is a finite projective `A`-module
(`AlgebraicGeometry.Scheme.Vect.exists_retract_free`), and extension of scalars is a functor, so
it carries the splitting across; what it does to the ambient free module is
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`. -/
theorem exists_retract_frobeniusColimitFree (A : Type u) [CommRing A] (hpA : (p : A) = 0)
    (M : frobeniusColimitVectorBundles (Spec (.of A)) p (isInCharacteristic_spec A p hpA)) :
    ∃ n : ℕ, Nonempty (Retract M
      (frobeniusColimitFreeVectorBundle p (isInCharacteristic_spec A p hpA) n)) := by
  obtain ⟨k, E, ⟨eE⟩⟩ := exists_frobeniusStageFunctor_obj_iso (Spec (.of A)) p
    (isInCharacteristic_spec A p hpA) M
  obtain ⟨n, hfree, ⟨hret⟩⟩ := Scheme.Vect.exists_retract_free (.of A) E
  refine ⟨n, ⟨?_⟩⟩
  have h1 : Retract M ((frobeniusStageFunctor (Spec (.of A)) p
      (isInCharacteristic_spec A p hpA) k).obj E) := Retract.ofIso eE.symm
  have h2 : Retract
      ((frobeniusStageFunctor (Spec (.of A)) p (isInCharacteristic_spec A p hpA) k).obj E)
      ((frobeniusStageFunctor (Spec (.of A)) p (isInCharacteristic_spec A p hpA) k).obj
        ⟨_root_.SheafOfModules.free (ULift.{u} (Fin n)), hfree⟩) :=
    hret.map _
  have h3 : ((frobeniusStageFunctor (Spec (.of A)) p (isInCharacteristic_spec A p hpA) k).obj
        ⟨_root_.SheafOfModules.free (ULift.{u} (Fin n)), hfree⟩) ≅
      frobeniusColimitFreeVectorBundle p (isInCharacteristic_spec A p hpA) n :=
    ObjectProperty.isoMk _ (_root_.SheafOfModules.pullbackObjFreeIso
      (frobeniusStageStructureMap (Spec (.of A)) p (isInCharacteristic_spec A p hpA) k)
      (ULift.{u} (Fin n)))
  exact h1.trans (h2.trans (Retract.ofIso h3))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The comparison functor of [Stacks, Tag 0EXD] is full**, under exactly the hypotheses of
[Stacks, Example 0EVH]: a ring `A`, two elements `f₁, f₂` of it and a prime `p` vanishing in `A`.

This is `AlgebraicGeometry.full_frobeniusColimitVectorBundlesComparison_of_retract` at the almost
blowup square of [Stacks, Example 0EVH]. Its retract hypothesis is
`AlgebraicGeometry.exists_retract_frobeniusColimitFree`, and its fullness at a pair of free
modules is
`AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator` at the
identity trivialisations, read through
`AlgebraicGeometry.exists_map_eq_frobeniusColimitVectorBundlesComparison_of_isPullback`. -/
theorem full_twoGeneratorFrobeniusColimitComparison (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).Full := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  refine full_frobeniusColimitVectorBundlesComparison_of_retract p
    (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
    (exceptionalToCenter A f₁ f₂) (isInCharacteristic_spec A p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    (twoGenerator_isPullback A f₁ f₂).w
    (exists_retract_frobeniusColimitFree p A hpA) fun n m ψ => ?_
  exact exists_map_eq_frobeniusColimitVectorBundlesComparison_of_isPullback p
    (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
    (exceptionalToCenter A f₁ f₂) (isInCharacteristic_spec A p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    (twoGenerator_isPullback A f₁ f₂).w _ _
    (isPullback_squareComparison_homSquare_trivialised_twoGenerator p hp A f₁ f₂ hpA
      (ULift.{u} (Fin n)) (ULift.{u} (Fin m)) _ _ (Iso.refl _) (Iso.refl _)) ψ

/-- **The comparison functor of [Stacks, Tag 0EXD] is fully faithful**, under exactly the
hypotheses of [Stacks, Example 0EVH].

Fullness is `AlgebraicGeometry.full_twoGeneratorFrobeniusColimitComparison` and faithfulness is
`AlgebraicGeometry.faithful_twoGeneratorFrobeniusColimitComparison`. This is one of the two
halves of the tag, which asserts that the comparison is an **equivalence**; essential
surjectivity is a separate matter, so no `@[stacks 0EXD]` attribute appears here. -/
theorem fullyFaithful_twoGeneratorFrobeniusColimitComparison (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).Full ∧
      (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).Faithful :=
  ⟨full_twoGeneratorFrobeniusColimitComparison p hp A f₁ f₂ hpA,
    faithful_twoGeneratorFrobeniusColimitComparison p hp A f₁ f₂ hpA⟩

end AlgebraicGeometry

end
