module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceCompactGenerator
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedProjectiveRetract

/-! # Comparing a derived equivalence with a derived tensor product on graded projectives

Let `R` be a commutative ring, let `(A, d)` and `(B, d)` be differential graded `R`-algebras, let
`F : D(A, d) → D(B, d)` be an equivalence and let `N` be a differential graded `(A, B)`-bimodule,
so that `G = - ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is a second functor. Given an isomorphism
`e : G(A) ≅ F(A)` at the regular module, [Stacks, Tag 09SB] asserts that `e` extends to a
*functorial* isomorphism `G(M) → F(M)` for `M` graded projective — "e.g. a sum of shifts of
`A`" — and that consequently `G(M) ≅ F(M)` when `M` is a cone of a morphism between such modules.

This file proves both assertions, for the sums of shifts of `A` that the source names explicitly
and then for the *retracts* of such sums, which is the class the source's "graded projective"
reaches: a graded projective differential graded module whose differential vanishes is such a
retract (`DifferentialGradedModule`
`.exists_retract_coproduct_shift_q_regularModule_of_isProjective`, the bridge to Tag 09K0), and a
graded projective module with a nonzero differential need not be one at all. See the
implementation notes.

## Main definitions

* `DifferentialGraded.Bimodule.shiftComparison`: the comparison `G(A[k]) ≅ F(A[k])`, built from
  `e` and the commutation of both functors with the translation.
* `DifferentialGraded.Bimodule.coprodComparison` and
  `DifferentialGraded.Bimodule.shiftsComparison`: the comparison at a direct sum, assembled from
  comparisons at the summands, and its specialisation to a direct sum of shifts of `A`.
* `DifferentialGraded.Bimodule.retractComparison`: the comparison at a retract of an object at
  which a comparison commuting with the idempotent of the retraction is given.
* `DifferentialGraded.Bimodule.sumOfShiftsOfRegular`: the objects of `D(A, d)` isomorphic to a
  direct sum of shifts of the regular module. Its `ObjectProperty.retractClosure` is the class of
  the graded projective modules reached here.

## Main results

* `DifferentialGraded.Bimodule.sumOfShiftsNatIso`: **the functorial isomorphism**. The
  restrictions of `G` and of `F` to the full subcategory of objects isomorphic to a direct sum of
  shifts of `A` are isomorphic as functors.
* `DifferentialGraded.Bimodule.retractNatIso`: **the functorial isomorphism on the graded
  projectives**. The same conclusion over the full subcategory of *retracts* of direct sums of
  shifts of `A`.
* `DifferentialGraded.Bimodule.retractClosure_sumOfShiftsOfRegular_q_of_isProjectiveAsGradedModule`
  and `DifferentialGraded.Bimodule.gradedProjectiveComparison`: the bridge from graded
  projectivity (Tag 09K0) to that class, and the resulting isomorphism `G(M) ≅ F(M)` at a graded
  projective differential graded module with vanishing differential.
* `DifferentialGraded.Bimodule.shiftsComparison_naturality` and
  `DifferentialGraded.Bimodule.sumOfShiftsComparison_naturality`: the naturality read off a
  chosen presentation — the comparison at `⨁ᵢ A[kᵢ]` is natural in every morphism
  `⨁ᵢ A[kᵢ] ⟶ ⨁ⱼ A[lⱼ]` — and its presentation-free form.
* `DifferentialGraded.Bimodule.exists_iso_cone_of_sumOfShifts` and
  `DifferentialGraded.Bimodule.exists_iso_cone_of_retractOfSumOfShifts`: **the corollary for
  cones**. If the first two vertices of a distinguished triangle of `D(A, d)` are direct sums of
  shifts of `A`, respectively retracts of such sums, then `G` and `F` agree at the third.

## Implementation notes

*What replaces Proposition 09SA.* The source opens with "let `A`, `B`, `F`, `N` be as in
Proposition 09SA", whose content is the *existence* of a bimodule `N` making
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` an equivalence. That proposition *is* formalized in this library,
as `DifferentialGradedModule.exists_bimodule_of_derivedEquivalence`: for an `R`-linear,
shift-commuting equivalence `F` with `A = H^0(A)` and `B` K-flat over `R` it produces a bimodule
`N` whose derived tensor functor is an equivalence, together with an isomorphism of the class of
`N` with `F(A)`; composing with the identification of `G(A)` with the class of `N`
(`DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal`) gives an isomorphism
`e : G(A) ≅ F(A)`. What that conclusion does not record is
the compatibility of `e` with `End_{D(A,d)}(A)`, which 09SA's construction supplies — the action
of `A` on `N` *is* the one transported along `A = End(N)` — and which the naturality below needs.
So the data `(F, N, e, he)` is still taken as hypotheses rather than obtained from 09SA, and no
corollary instantiating the hypotheses from 09SA is stated: that would mean strengthening 09SA's
statement so that the compatibility is carried through its proof, which is a change to Tag 09SA
and not to this remark. Taking the data as hypotheses also makes the statements more general:
they hold for any `F`, `N` and `e` of that shape, whether or not `N` arises from 09SA.

*Why `e` is assumed compatible with the endomorphisms of `A`.* The hypothesis `he` below says
that `e.hom ≫ F.map f = G.map f ≫ e.hom` for every `f : A ⟶ A` in `D(A, d)`, that is, that `e`
is an isomorphism of modules over `End_{D(A,d)}(A)`, which for an algebra concentrated in degree
zero is `A` itself (`DifferentialGradedModule.regularEndAlgEquiv`). This is *not* a consequence
of `e` being an isomorphism of objects, and it is exactly what the word "functorial" in the
source needs: the naturality square of the extension at a self-morphism of `A` is the hypothesis
`he` shifted by `k`, and no weaker assumption makes it commute. In 09SA the isomorphism
`N = G(A) → F(A)` is an equality of the underlying module with the `A`-action transported along
`A = H^0(Hom(N, N)) = End_{D(B,d)}(N)`, so `he` holds there by construction; taking it as a
hypothesis is taking 09SA's data, not weakening its conclusion.

*The hypothesis `A = H^0(A)`.* Condition (1) of Proposition 09SA is carried along as
`hA : ∀ i ≠ 0, A.grading i = ⊥`, in the spelling of
`DifferentialGradedModule.exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence`
(Tag 09S8). It is used once: it makes `Hom_{D(A,d)}(A[k], A[l])` vanish for `k ≠ l`
(`DifferentialGraded.Bimodule.hom_shift_regular_eq_zero_of_ne`), so that the naturality of the
comparison on the shifts reduces to the degree-zero hypothesis `he`. Condition (2) of 09SA, that
`B` be K-flat over `R`, is not needed and is not assumed.

*How far the extension goes, and what is not proved.* The source claims the functorial
isomorphism for every graded projective `M`, with "a sum of shifts of `A`" as a parenthetical
example. Proved here are the example (`DifferentialGraded.Bimodule.sumOfShiftsNatIso`) and the
extension to all *retracts* in `D(A, d)` of sums of shifts of `A`
(`DifferentialGraded.Bimodule.retractNatIso`), which is where graded projectivity enters: a
graded projective module is by definition one onto which every surjection of graded modules
splits (`Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule`, Tag 09K0), the free
graded module on its homogeneous elements surjects onto it, and the resulting splitting is a
morphism of *differential* graded modules as soon as the two differentials vanish — which they do
for a sum of shifts of an algebra concentrated in degree zero, and which is therefore the one
hypothesis on `M`. That is the bridge
`DifferentialGradedModule.exists_retract_coproduct_shift_q_regularModule_of_isProjective`, and
`DifferentialGraded.Bimodule.gradedProjectiveComparison` is the comparison it yields.

The literal claim — the functorial isomorphism over the graded projective modules with no
condition on their differentials — is *not* proved, and it is not a gap in the argument above but
a statement this development declines to assert, for two independent reasons.

First, graded projectivity only ever produces a splitting of graded modules, with no compatibility
with the differentials; that is all Tag 09K0 itself concludes, namely that a surjection onto a
graded projective module is an *admissible* epimorphism, i.e. split after the differentials are
forgotten. And the conclusion really can fail: take `A = k[x]/(x²)` in degree zero and
`M = (A --x--> A)`, whose two terms are free, so that `M` is graded projective. Its cohomology
`H^0(M) = (x) ≅ k` is not a projective `A`-module, while a retract of `⨁ᵢ A[kᵢ]` in `D(A, d)` has
each cohomology a direct summand of the free module `⨁ᵢ A`; so this `M` is not a retract of any
sum of shifts of `A`, and the route above cannot reach it. (It *is* a cone of a morphism between
sums of shifts, so `G(M) ≅ F(M)` holds for it by the corollary below — which is the source's
second sentence, not its first.)

Second, taken over the whole class of graded projective modules the claim would contradict the
remark's own opening sentence. Every object of `D(A, d)` is isomorphic to the class of a module
with property (P) (Tag 09KP, `DifferentialGradedModule.exists_propertyP_telescope`), whose
underlying graded module is a direct sum of shifts of `A` — the filtration's inclusions are
admissible, hence graded-split, and its quotients are sums of shifts — and so is graded
projective. A natural isomorphism of `G` with `F` over the full subcategory of `D(A, d)` spanned
by the classes of graded projective modules would therefore transport to a natural isomorphism
`G ≅ F` on all of `D(A, d)`, which is exactly what the source opens by declining to assert ("it
is not clear that `F` and the functor `G` are isomorphic"). The reading formalized here — sums of
shifts of `A` and their retracts — is the one on which the remark's three sentences are
consistent with one another: it contains the parenthetical example, it is closed under neither
cones nor arbitrary graded projectives, and the cone statement is a genuine strengthening of it.
The clause strings on the tags say all of this.

That transport is valid because the naturality proved here is naturality in the morphisms of
`D(A, d)`, not merely in homomorphisms of differential graded modules: the source and target of
`DifferentialGraded.Bimodule.sumOfShiftsNatIso` and of
`DifferentialGraded.Bimodule.retractNatIso` are the restrictions of `G` and of `F` along
`CategoryTheory.ObjectProperty.ι`, the inclusion of a *full* subcategory of `D(A, d)`, so the
naturality square is asked of every `f : X.obj ⟶ Y.obj` of `D(A, d)`
(`DifferentialGraded.Bimodule.sumOfShiftsComparison_naturality`). Had naturality been taken only
in module homomorphisms, or in their homotopy classes, the full subcategory spanned by the
property-(P) modules would not be equivalent to `D(A, d)` and nothing would transport; the
literal claim would then be strictly weaker than `G ≅ F` and would not be the remark's open
question. It is the `D(A, d)`-naturality that makes the two coincide.

So `hMd` is where the source's "straightforward" stops being straightforward. It is not a
conceptual restriction on the class — it is exactly what turns the graded splitting of the free
cover into a morphism of *differential* graded modules, and the class it cuts out,
`{graded projective} ∩ {d = 0}`, sits between the source's parenthetical example and the retracts
of it in `D(A, d)`: a direct sum of shifts of an algebra concentrated in degree zero has
vanishing differential and free underlying graded module, and a graded projective module with
vanishing differential is a retract in `D(A, d)` of such a sum. Dropping `hMd` is not a
sharpening of the argument below but the open question itself.

*What is deliberately not formalized.* The remark opens with "it is not clear that `F` and the
functor `G` are isomorphic" and closes with "we don't know whether more is true in general".
Neither is a mathematical assertion — they record the absence of a proof — so neither is
formalized and neither is claimed by the tags below.

*The hypotheses on `F`, against the source's.* The source's `F` is an `R`-linear equivalence of
triangulated categories. What is assumed here is additivity, commutation with the translation and
being an equivalence, together with exactness (`Functor.IsTriangulated`) for the statement about
cones, which is the only place a distinguished triangle is moved. `R`-linearity is never used and
is not assumed, so the statements are more general than the source's in that respect too. The
functor `G = - ⊗_A^𝐋 N` is additive, exact and `R`-linear for every bimodule `N`, with no
hypotheses (Tags 09LR, 09LS and 09S7), and preserves direct sums because it is a left adjoint
(Tag 09LT).

*Universes.* As everywhere in this chapter the base ring, the algebras and the modules live in a
single universe `u`, following Tag 09JJ; direct sums are indexed by types in `Type u` and
compactness is `IsCompactObject.{u}`, matching Tags 09R9 and 09S7.

## References

* [Stacks Project, Tag 09SB](https://stacks.math.columbia.edu/tag/09SB), the remark proved here;
  [Tag 09SA](https://stacks.math.columbia.edu/tag/09SA) for the data it starts from, formalized as
  `DifferentialGradedModule.exists_bimodule_of_derivedEquivalence`, and
  [Tag 09S8](https://stacks.math.columbia.edu/tag/09S8) for the hypothesis `A = H^0(A)`.
* [Stacks Project, Tag 09K0](https://stacks.math.columbia.edu/tag/09K0) for graded projectivity
  and [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP) for the property-(P) resolutions
  which make every object of `D(A, d)` the class of a graded projective module.
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) for the derived tensor
  functor, [Tag 09LR](https://stacks.math.columbia.edu/tag/09LR) for its exactness,
  [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT) for its right adjoint,
  [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE) for the dévissage this file does *not*
  use — there is no natural transformation `G ⟶ F` to run it on — and
  [Tag 014A](https://stacks.math.columbia.edu/tag/014A) for the five lemma used at the cone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **The derived tensor product is a left adjoint.** Its right adjoint is the derived internal
Hom out of `N` (Tag 09LT); recording the adjunction as an instance is what makes
`- ⊗_A^𝐋 N` preserve the direct sums used below. -/
instance derivedTensorFunctor_isLeftAdjoint (N : Bimodule A B) :
    (derivedTensorFunctor N).IsLeftAdjoint :=
  (derivedTensorFunctor_adj_derivedHomFunctor N).isLeftAdjoint

/-! ### Vanishing of the morphisms between distinct shifts of the regular module -/

/-- **Distinct shifts of the regular module admit no nonzero morphism**, for an algebra
concentrated in degree zero. Shifting by `-k` identifies `Hom(A[k], A[l])` with
`Hom(A, A[l - k])`, which is `H^{l-k}(A)`
(`DifferentialGradedModule.cohomologyEquivDerivedShiftHom`, Tag 09KY for the regular module) and
so has at most one element when `l ≠ k`. The shift by `-k` is performed through the fullness of
the shift functor and the comparison `A[l] ≅ (A[l-k])[k]` of `shiftFunctorAdd'`. -/
theorem hom_shift_regular_eq_zero_of_ne (A : DifferentialGradedAlgebra.{u, u} R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) {k l : ℤ} (hkl : k ≠ l)
    (f : (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧) ⟶
      (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦l⟧)) :
    f = 0 := by
  have hm : l - k ≠ 0 := sub_ne_zero.2 (Ne.symm hkl)
  have hzero : ∀ g : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
      (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦l - k⟧),
      g = 0 := fun g =>
    (cohomologyEquivDerivedShiftHom A (l - k)).symm.injective
      (@Subsingleton.elim _ (A.subsingleton_cohomology hA hm) _ _)
  let φ := (shiftFunctorAdd' (derivedCategory' A) (l - k) k l (by omega)).app
    ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))
  obtain ⟨g, hg⟩ := (CategoryTheory.shiftFunctor (derivedCategory' A) k).map_surjective
    (f ≫ φ.hom)
  rw [hzero g, Functor.map_zero] at hg
  rw [← cancel_mono φ.hom, zero_comp]
  exact hg.symm

section

variable (F : derivedCategory' A ⥤ derivedCategory' B) [F.CommShift ℤ]
  {N : Bimodule A B}
  (e : (derivedTensorFunctor N).obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
      F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))

/-! ### The comparison at the shifts of the regular module -/

/-- **The comparison at the shift `A[k]`.** Both `G = - ⊗_A^𝐋 N` and `F` commute with the
translation, so the given isomorphism `e : G(A) ≅ F(A)` shifts to one
`G(A[k]) ≅ (G A)[k] ≅ (F A)[k] ≅ F(A[k])`. -/
def shiftComparison (k : ℤ) :
    (derivedTensorFunctor N).obj
        (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧) ≅
      F.obj (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧) :=
  ((derivedTensorFunctor N).commShiftIso k).app _ ≪≫
    (CategoryTheory.shiftFunctor (derivedCategory' B) k).mapIso e ≪≫
    ((F.commShiftIso k).app _).symm

/-- **The comparison at `A[k]` is natural for the `k`-th shift of a self-morphism of `A`.** The
two commutations with the translation are natural transformations, so the naturality square at
`g[k]` is the naturality square at `g` shifted by `k`, which is the hypothesis `he`. This is the
step at which `he` — the compatibility of `e` with `End_{D(A,d)}(A)` — is used, and it is the
reason that compatibility has to be assumed. -/
theorem shiftComparison_naturality_shift
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    (g : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))
    (k : ℤ) :
    (shiftComparison F e k).hom ≫
        F.map ((CategoryTheory.shiftFunctor (derivedCategory' A) k).map g) =
      (derivedTensorFunctor N).map
          ((CategoryTheory.shiftFunctor (derivedCategory' A) k).map g) ≫
        (shiftComparison F e k).hom := by
  have hFinv := (F.commShiftIso k).inv.naturality g
  have hGhom := ((derivedTensorFunctor N).commShiftIso k).hom.naturality g
  dsimp only [Functor.comp_map] at hFinv hGhom
  simp only [shiftComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← hFinv, ← Functor.map_comp_assoc, he g, Functor.map_comp_assoc]
  conv_rhs => rw [← Category.assoc, hGhom]
  simp only [Category.assoc]

variable [F.Additive]

/-- **The comparison at the shifts of the regular module is natural.** For an algebra
concentrated in degree zero, and given that `e` commutes with the self-morphisms of `A`, the
isomorphisms `G(A[k]) ≅ F(A[k])` are natural in *every* morphism `A[k] ⟶ A[l]`: for `k = l` the
morphism is the `k`-th shift of a self-morphism of `A`, because the shift functor is an
equivalence, and for `k ≠ l` there is no nonzero morphism to check. -/
theorem shiftComparison_naturality
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    {k l : ℤ}
    (f : (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧) ⟶
      (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦l⟧)) :
    (shiftComparison F e k).hom ≫ F.map f =
      (derivedTensorFunctor N).map f ≫ (shiftComparison F e l).hom := by
  by_cases hkl : k = l
  · subst hkl
    obtain ⟨g, rfl⟩ := (CategoryTheory.shiftFunctor (derivedCategory' A) k).map_surjective f
    exact shiftComparison_naturality_shift F e he g k
  · rw [hom_shift_regular_eq_zero_of_ne A hA hkl f, Functor.map_zero, Functor.map_zero,
      comp_zero, zero_comp]

end

/-! ### The comparison at a direct sum -/

section

variable (F : derivedCategory' A ⥤ derivedCategory' B) [F.IsEquivalence] {N : Bimodule A B}

/-- The comparison at a direct sum, assembled from comparisons at the summands: both functors
preserve direct sums, so the two coproduct comparisons and the direct sum of the given
isomorphisms compose to an isomorphism `G(⨁ Xᵢ) ≅ F(⨁ Xᵢ)`. -/
def coprodComparison {ι : Type u} {X : ι → derivedCategory' A}
    (α : ∀ i, (derivedTensorFunctor N).obj (X i) ≅ F.obj (X i)) :
    (derivedTensorFunctor N).obj (∐ X) ≅ F.obj (∐ X) :=
  PreservesCoproduct.iso (derivedTensorFunctor N) X ≪≫ Limits.Sigma.mapIso α ≪≫
    (PreservesCoproduct.iso F X).symm

/-- **The comparison at a direct sum restricts to the given comparison on each summand.** This
is the defining property of `DifferentialGraded.Bimodule.coprodComparison`, and the only thing
about it that the naturality argument uses. -/
theorem map_sigmaι_comp_coprodComparison {ι : Type u} {X : ι → derivedCategory' A}
    (α : ∀ i, (derivedTensorFunctor N).obj (X i) ≅ F.obj (X i)) (i : ι) :
    (derivedTensorFunctor N).map (Limits.Sigma.ι X i) ≫ (coprodComparison F α).hom =
      (α i).hom ≫ F.map (Limits.Sigma.ι X i) := by
  have h₁ : (derivedTensorFunctor N).map (Limits.Sigma.ι X i) ≫
      (PreservesCoproduct.iso (derivedTensorFunctor N) X).hom =
      Limits.Sigma.ι (fun j => (derivedTensorFunctor N).obj (X j)) i := by
    rw [← Iso.eq_comp_inv, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  have h₂ : Limits.Sigma.ι (fun j => F.obj (X j)) i ≫ (PreservesCoproduct.iso F X).inv =
      F.map (Limits.Sigma.ι X i) := by
    rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  simp only [coprodComparison, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, h₁, Limits.Sigma.ι_mapIso_hom_assoc, h₂]

variable [F.Additive]

/-- **The comparison at a direct sum of compact objects is natural.** If the comparisons at the
summands are natural in every morphism between summands, then the assembled comparisons are
natural in every morphism of the direct sums: a morphism out of a direct sum is determined by its
restrictions to the summands, and a morphism out of a compact object into a direct sum is a finite
sum of morphisms through the summands. -/
theorem coprodComparison_naturality {ι κ : Type u}
    {X : ι → derivedCategory' A} {Y : κ → derivedCategory' A}
    (α : ∀ i, (derivedTensorFunctor N).obj (X i) ≅ F.obj (X i))
    (β : ∀ j, (derivedTensorFunctor N).obj (Y j) ≅ F.obj (Y j))
    (hX : ∀ i, IsCompactObject.{u} (X i))
    (hnat : ∀ (i : ι) (j : κ) (f : X i ⟶ Y j),
      (α i).hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ (β j).hom)
    (f : (∐ X) ⟶ (∐ Y)) :
    (coprodComparison F α).hom ≫ F.map f =
      (derivedTensorFunctor N).map f ≫ (coprodComparison F β).hom := by
  classical
  have hstep : ∀ (i : ι) (h : X i ⟶ ∐ Y),
      (α i).hom ≫ F.map h =
        (derivedTensorFunctor N).map h ≫ (coprodComparison F β).hom := by
    intro i h
    obtain ⟨x, hx⟩ := (bijective_cofanMap (X i) (hX i) (Limits.Sigma.ι Y)
      (coproductIsCoproduct Y)).2 h
    subst hx
    induction x using DirectSum.induction_on with
    | zero =>
      rw [map_zero, Functor.map_zero, Functor.map_zero, comp_zero, zero_comp]
    | of j y =>
      rw [cofanMap_of, Functor.map_comp, Functor.map_comp, Category.assoc,
        map_sigmaι_comp_coprodComparison, ← Category.assoc, ← Category.assoc, hnat i j y]
    | add x y hx hy =>
      rw [map_add, Functor.map_add, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp, hx, hy]
  rw [← cancel_epi (sigmaComparison (derivedTensorFunctor N) X)]
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison_assoc, ← Category.assoc,
    map_sigmaι_comp_coprodComparison, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp_assoc]
  exact hstep i (Limits.Sigma.ι X i ≫ f)

end

/-! ### Transport of a comparison along retracts -/

/-- **Transport of a comparison square along retracts of the two objects.** If `a` and `b`
compare `G` with `F` at `X'` and `Y'`, if `X` is a retract of `X'` and `Y` of `Y'`, and if the
square at the induced morphism `ρ.r ≫ f ≫ σ.i : X' ⟶ Y'` commutes, then the transported
comparisons at `X` and `Y` make the square at `f` commute. This is what carries the naturality
from a chosen presentation of an object as a direct sum of shifts — or from a chosen presentation
of it as a retract of such a sum — to the object itself.

The two triangles `ρ.i ≫ ρ.r = 𝟙` and `σ.i ≫ σ.r = 𝟙` are the only thing used: `ρ.r ≫ f` is
rewritten as `(ρ.r ≫ f ≫ σ.i) ≫ σ.r` and `ρ.i ≫ ρ.r ≫ f ≫ σ.i` as `f ≫ σ.i`. -/
theorem retract_naturality {C D : Type*} [Category C] [Category D] (G F : C ⥤ D)
    {X Y X' Y' : C} (a : G.obj X' ⟶ F.obj X') (b : G.obj Y' ⟶ F.obj Y')
    (ρ : Retract X X') (σ : Retract Y Y') (f : X ⟶ Y)
    (hnat : a ≫ F.map (ρ.r ≫ f ≫ σ.i) = G.map (ρ.r ≫ f ≫ σ.i) ≫ b) :
    (G.map ρ.i ≫ a ≫ F.map ρ.r) ≫ F.map f =
      G.map f ≫ (G.map σ.i ≫ b ≫ F.map σ.r) := by
  have h₁ : F.map ρ.r ≫ F.map f = F.map (ρ.r ≫ f ≫ σ.i) ≫ F.map σ.r := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp
  have h₂ : G.map ρ.i ≫ G.map (ρ.r ≫ f ≫ σ.i) = G.map f ≫ G.map σ.i := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp
  simp only [Category.assoc]
  rw [h₁, ← Category.assoc a, hnat, Category.assoc, ← Category.assoc (G.map ρ.i), h₂,
    Category.assoc]

/-- **Transport of a comparison square along isomorphisms of the two objects**, the case of
`DifferentialGraded.Bimodule.retract_naturality` in which the retractions are isomorphisms. This
is what carries the naturality from a chosen presentation of an object as a direct sum of shifts
to the object itself. -/
theorem transport_naturality {C D : Type*} [Category C] [Category D] (G F : C ⥤ D)
    {X Y X' Y' : C} (a : G.obj X' ⟶ F.obj X') (b : G.obj Y' ⟶ F.obj Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y)
    (hnat : a ≫ F.map (eX.inv ≫ f ≫ eY.hom) = G.map (eX.inv ≫ f ≫ eY.hom) ≫ b) :
    (G.map eX.hom ≫ a ≫ F.map eX.inv) ≫ F.map f =
      G.map f ≫ (G.map eY.hom ≫ b ≫ F.map eY.inv) :=
  retract_naturality G F a b (Retract.ofIso eX) (Retract.ofIso eY) f hnat

/-- **The comparison at a retract.** If `a : G(X) ≅ F(X)` commutes with the idempotent
`ρ.r ≫ ρ.i` of `X` cut out by a retraction of `Y` onto `X`, then `G(Y) ≅ F(Y)`: the composite
`G(Y) → G(X) → F(X) → F(Y)` is an isomorphism, its inverse being the composite in the other
direction, because the two round trips are `G` and `F` applied to the idempotent, conjugated
back by `a`. No additivity or exactness is needed, only that one square commutes. -/
def retractComparison {C D : Type*} [Category C] [Category D] (G F : C ⥤ D) {X Y : C}
    (ρ : Retract Y X) (a : G.obj X ≅ F.obj X)
    (hnat : a.hom ≫ F.map (ρ.r ≫ ρ.i) = G.map (ρ.r ≫ ρ.i) ≫ a.hom) :
    G.obj Y ≅ F.obj Y where
  hom := G.map ρ.i ≫ a.hom ≫ F.map ρ.r
  inv := F.map ρ.i ≫ a.inv ≫ G.map ρ.r
  hom_inv_id := by
    have key : a.hom ≫ F.map (ρ.r ≫ ρ.i) ≫ a.inv = G.map (ρ.r ≫ ρ.i) := by
      rw [← Category.assoc, hnat, Category.assoc, a.hom_inv_id, Category.comp_id]
    have h : G.map ρ.i ≫ (a.hom ≫ F.map (ρ.r ≫ ρ.i) ≫ a.inv) ≫ G.map ρ.r = 𝟙 (G.obj Y) := by
      rw [key, ← Functor.map_comp, ← Functor.map_comp,
        show ρ.i ≫ (ρ.r ≫ ρ.i) ≫ ρ.r = 𝟙 Y from by simp, CategoryTheory.Functor.map_id]
    simpa only [Functor.map_comp, Category.assoc] using h
  inv_hom_id := by
    have key : a.inv ≫ G.map (ρ.r ≫ ρ.i) ≫ a.hom = F.map (ρ.r ≫ ρ.i) := by
      rw [← hnat, Iso.inv_hom_id_assoc]
    have h : F.map ρ.i ≫ (a.inv ≫ G.map (ρ.r ≫ ρ.i) ≫ a.hom) ≫ F.map ρ.r = 𝟙 (F.obj Y) := by
      rw [key, ← Functor.map_comp, ← Functor.map_comp,
        show ρ.i ≫ (ρ.r ≫ ρ.i) ≫ ρ.r = 𝟙 Y from by simp, CategoryTheory.Functor.map_id]
    simpa only [Functor.map_comp, Category.assoc] using h

/-- The forward map of `DifferentialGraded.Bimodule.retractComparison` is the composite
`G(Y) → G(X) → F(X) → F(Y)` of `G.map ρ.i`, `a.hom` and `F.map ρ.r`. -/
@[simp] theorem retractComparison_hom {C D : Type*} [Category C] [Category D] (G F : C ⥤ D)
    {X Y : C} (ρ : Retract Y X) (a : G.obj X ≅ F.obj X)
    (hnat : a.hom ≫ F.map (ρ.r ≫ ρ.i) = G.map (ρ.r ≫ ρ.i) ≫ a.hom) :
    (retractComparison G F ρ a hnat).hom = G.map ρ.i ≫ a.hom ≫ F.map ρ.r := rfl

/-! ### The comparison on the sums of shifts of the regular module -/

section

variable (F : derivedCategory' A ⥤ derivedCategory' B) [F.Additive] [F.CommShift ℤ]
  [F.IsEquivalence] {N : Bimodule A B}
  (e : (derivedTensorFunctor N).obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
      F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))

/-- **The comparison at a direct sum of shifts of the regular module**: the comparisons
`G(A[kᵢ]) ≅ F(A[kᵢ])` assembled over the summands. -/
def shiftsComparison {ι : Type u} (k : ι → ℤ) :
    (derivedTensorFunctor N).obj
        (∐ fun i => ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
          (regularModule A))⟦k i⟧) ≅
      F.obj (∐ fun i => ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
        (regularModule A))⟦k i⟧) :=
  coprodComparison F fun i => shiftComparison F e (k i)

/-- **The comparison on the sums of shifts of the regular module is natural.** The comparisons
`G(⨁ᵢ A[kᵢ]) ≅ F(⨁ᵢ A[kᵢ])` of `DifferentialGraded.Bimodule.shiftsComparison` are natural in
every morphism `⨁ᵢ A[kᵢ] ⟶ ⨁ⱼ A[lⱼ]` of `D(A, d)`. This is the functorial isomorphism of
[Stacks, Tag 09SB] read off a presentation of the objects as direct sums of shifts; the
presentation-free form is `DifferentialGraded.Bimodule.sumOfShiftsNatIso`.

The shifts of the regular module are compact (`DifferentialGradedModule`
`.isCompactObject_q_regularModule` and `CategoryTheory.isCompactObject_shift`), which is the
hypothesis under which
`DifferentialGraded.Bimodule.coprodComparison_naturality` propagates naturality from the summands
to the direct sums. -/
theorem shiftsComparison_naturality
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    {ι κ : Type u} (k : ι → ℤ) (l : κ → ℤ)
    (f : (∐ fun i => ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
          (regularModule A))⟦k i⟧) ⟶
      (∐ fun j => ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
        (regularModule A))⟦l j⟧)) :
    (shiftsComparison F e k).hom ≫ F.map f =
      (derivedTensorFunctor N).map f ≫ (shiftsComparison F e l).hom :=
  coprodComparison_naturality F _ _
    (fun i => isCompactObject_shift (isCompactObject_q_regularModule A) (k i))
    (fun _ _ g => shiftComparison_naturality F e hA he g) f

/-! ### The functorial comparison -/

/-- **The objects of `D(A, d)` isomorphic to a direct sum of shifts of the regular module.**
These are the objects at which the comparison of [Stacks, Tag 09SB] is first proved below — the
source's parenthetical example of a graded projective differential graded module. Its
`ObjectProperty.retractClosure`, the retracts of such sums, is the class to which the comparison
is then extended, and the class in which the graded projective modules of the source's statement
land as far as they can: see
`DifferentialGraded.Bimodule.retractClosure_sumOfShiftsOfRegular_q_of_isProjectiveAsGradedModule`
and the implementation notes of this file. -/
def sumOfShiftsOfRegular (A : DifferentialGradedAlgebra.{u, u} R) :
    ObjectProperty (derivedCategory' A) := fun X =>
  ∃ (ι : Type u) (k : ι → ℤ), Nonempty (X ≅
    ∐ fun i => ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k i⟧)

/-- **The comparison at an object which is a direct sum of shifts of the regular module**, taken
through a presentation of that object as such a direct sum chosen by
`Classical.choice`. Different presentations give different isomorphisms, which is why a choice is
made once and for all here: the naturality of the resulting family, proved in
`DifferentialGraded.Bimodule.sumOfShiftsNatIso`, does not depend on which presentations were
chosen. -/
def sumOfShiftsComparison (X : (sumOfShiftsOfRegular A).FullSubcategory) :
    (derivedTensorFunctor N).obj X.obj ≅ F.obj X.obj :=
  (derivedTensorFunctor N).mapIso X.2.choose_spec.choose_spec.some ≪≫
    shiftsComparison F e X.2.choose_spec.choose ≪≫
    (F.mapIso X.2.choose_spec.choose_spec.some).symm

/-- **The comparison on the sums of shifts of the regular module is natural**, in the
presentation-free form: the isomorphisms `DifferentialGraded.Bimodule.sumOfShiftsComparison` are
natural in every morphism of `D(A, d)` between objects isomorphic to direct sums of shifts of
`A`. It is the naturality of
`DifferentialGraded.Bimodule.shiftsComparison_naturality` transported along the chosen
presentations, and it is what both the functorial isomorphism and its extension to retracts are
assembled from. -/
theorem sumOfShiftsComparison_naturality
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    (X Y : (sumOfShiftsOfRegular A).FullSubcategory) (f : X.obj ⟶ Y.obj) :
    (sumOfShiftsComparison F e X).hom ≫ F.map f =
      (derivedTensorFunctor N).map f ≫ (sumOfShiftsComparison F e Y).hom :=
  transport_naturality (derivedTensorFunctor N) F _ _
    X.2.choose_spec.choose_spec.some Y.2.choose_spec.choose_spec.some f
    (shiftsComparison_naturality F e hA he _ _ _)

/-- **Stacks Tag 09SB, the functorial isomorphism.** Let `(A, d)` and `(B, d)` be differential
graded `R`-algebras with `A = H^0(A)`, let `F : D(A, d) ⥤ D(B, d)` be an additive,
shift-commuting equivalence, let `N` be a differential graded `(A, B)`-bimodule, write
`G = - ⊗_A^𝐋 N`, and let `e : G(A) ≅ F(A)` be an isomorphism compatible with the endomorphisms
of `A` in `D(A, d)`. Then the restrictions of `G` and of `F` to the full subcategory of objects
isomorphic to a direct sum of shifts of `A` are isomorphic *as functors*: the extension of `e`
asserted by the source is a natural isomorphism, not merely a pointwise one.

The data `(F, N, e)` is what Proposition 09SA produces. 09SA is formalized in this library
(`DifferentialGradedModule.exists_bimodule_of_derivedEquivalence`), but its conclusion does not
record the compatibility of the isomorphism it produces with `End_{D(A,d)}(A)` — which its
construction supplies and which a bare isomorphism of objects does not give — so the data is
hypothesised rather than obtained from it. See the implementation notes of this file.

The source states the extension for every graded projective differential graded module `M`, with
a sum of shifts of `A` as its example. This is the example;
`DifferentialGraded.Bimodule.retractNatIso` extends it to every retract of such a sum, which is
how far graded projectivity carries it. -/
def sumOfShiftsNatIso
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom) :
    (sumOfShiftsOfRegular A).ι ⋙ derivedTensorFunctor N ≅ (sumOfShiftsOfRegular A).ι ⋙ F :=
  NatIso.ofComponents (fun X => sumOfShiftsComparison F e X) fun {X Y} f =>
    (sumOfShiftsComparison_naturality F e hA he X Y f.hom).symm

/-! ### The comparison on the graded projective modules

The retract closure of the sums of shifts of `A` is the class on which the comparison extends,
and it is the class the source's "graded projective" denotes as far as this development can
reach: every graded projective differential graded module *with vanishing differential* lands in
it (`DifferentialGradedModule`
`.exists_retract_coproduct_shift_q_regularModule_of_isProjective`), while a graded projective
module with a nonzero differential need not. See the implementation notes of this file. -/

/-- **The comparison at an object which is a retract of a direct sum of shifts of the regular
module**, taken through a presentation of that object as such a retract chosen by
`Classical.choice`: the comparison at the chosen sum of shifts, transported along the retraction
by `DifferentialGraded.Bimodule.retractComparison`. The square that makes the transport an
isomorphism is the naturality of the comparison at the idempotent of the retraction. -/
def retractComparisonOfSumOfShifts
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    (X : (sumOfShiftsOfRegular A).retractClosure.FullSubcategory) :
    (derivedTensorFunctor N).obj X.obj ≅ F.obj X.obj :=
  retractComparison (derivedTensorFunctor N) F X.2.choose_spec.choose_spec.some
    (sumOfShiftsComparison F e ⟨X.2.choose, X.2.choose_spec.choose⟩)
    (sumOfShiftsComparison_naturality F e hA he ⟨X.2.choose, X.2.choose_spec.choose⟩
      ⟨X.2.choose, X.2.choose_spec.choose⟩
      (X.2.choose_spec.choose_spec.some.r ≫ X.2.choose_spec.choose_spec.some.i))

/-- **Stacks Tag 09SB, the functorial isomorphism on the graded projective modules.** In the
setting of `DifferentialGraded.Bimodule.sumOfShiftsNatIso`, the restrictions of `G` and of `F` to
the full subcategory of *retracts* of direct sums of shifts of `A` are isomorphic as functors.

This is the source's extension of `e` to the graded projective modules, in the reach this
development has: a graded projective differential graded module whose differential vanishes is
such a retract (`DifferentialGraded.Bimodule`
`.retractClosure_sumOfShiftsOfRegular_q_of_isProjectiveAsGradedModule`), graded projectivity
being precisely the splitting of the free cover, and the class of retracts can be strictly larger
than the class of direct sums of shifts for which
`DifferentialGraded.Bimodule.sumOfShiftsNatIso` states the same conclusion — over an `A` with a
projective non-free module it is, the cohomology of a sum of shifts being free. It is also the
largest class to which the comparison can be carried by this argument: see the implementation
notes for why a graded projective module with a nonzero differential need not be a retract of a
sum of shifts at all. -/
def retractNatIso
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom) :
    (sumOfShiftsOfRegular A).retractClosure.ι ⋙ derivedTensorFunctor N ≅
      (sumOfShiftsOfRegular A).retractClosure.ι ⋙ F :=
  NatIso.ofComponents (fun X => retractComparisonOfSumOfShifts F e hA he X) fun {X Y} f =>
    (retract_naturality (derivedTensorFunctor N) F
      (sumOfShiftsComparison F e ⟨X.2.choose, X.2.choose_spec.choose⟩).hom
      (sumOfShiftsComparison F e ⟨Y.2.choose, Y.2.choose_spec.choose⟩).hom
      X.2.choose_spec.choose_spec.some Y.2.choose_spec.choose_spec.some f.hom
      (sumOfShiftsComparison_naturality F e hA he ⟨X.2.choose, X.2.choose_spec.choose⟩
        ⟨Y.2.choose, Y.2.choose_spec.choose⟩
        (X.2.choose_spec.choose_spec.some.r ≫ f.hom ≫
          Y.2.choose_spec.choose_spec.some.i))).symm

end

/-! ### Graded projectivity -/

section

/-- **A graded projective differential graded module with vanishing differential is a retract of
a direct sum of shifts of `A` in `D(A, d)`.** This is the bridge between the source's "graded
projective" — projectivity of the underlying graded module, [Stacks, Tag 09K0],
`Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule` in the unbundled encoding — and
the sums of shifts of `A` on which the comparison of [Stacks, Tag 09SB] is built: the free graded
module on the homogeneous elements of `M` surjects onto `M`, graded projectivity splits that
surjection, and with both differentials zero the splitting is a homomorphism of differential
graded modules. It is proved as
`DifferentialGradedModule.exists_retract_coproduct_shift_q_regularModule_of_isProjective`. -/
theorem retractClosure_sumOfShiftsOfRegular_q_of_isProjectiveAsGradedModule
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    {M : DifferentialGradedModule.{u, u, u} A} (hMd : M.d = 0)
    (hM : Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
      (Unbundled.module M)) :
    (sumOfShiftsOfRegular A).retractClosure
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj M) := by
  obtain ⟨ι, k, ⟨ρ⟩⟩ :=
    exists_retract_coproduct_shift_q_regularModule_of_isProjective hA hMd hM
  exact ⟨_, ⟨ι, k, ⟨Iso.refl _⟩⟩, ⟨ρ⟩⟩

variable (F : derivedCategory' A ⥤ derivedCategory' B) [F.Additive] [F.CommShift ℤ]
  [F.IsEquivalence] {N : Bimodule A B}
  (e : (derivedTensorFunctor N).obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
      F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))

/-- **Stacks Tag 09SB at a graded projective module.** In the setting of
`DifferentialGraded.Bimodule.sumOfShiftsNatIso`, let `M` be a differential graded `A`-module
which is projective as a graded module and whose differential vanishes. Then `G(M) ≅ F(M)`,
by the component at `M` of the natural isomorphism
`DifferentialGraded.Bimodule.retractNatIso` — so this isomorphism is not merely pointwise: it is
natural in every morphism of `D(A, d)` between such modules, and more generally between retracts
of sums of shifts of `A`. -/
def gradedProjectiveComparison
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    {M : DifferentialGradedModule.{u, u, u} A} (hMd : M.d = 0)
    (hM : Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
      (Unbundled.module M)) :
    (derivedTensorFunctor N).obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj M) ≅
      F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj M) :=
  retractComparisonOfSumOfShifts F e hA he
    ⟨_, retractClosure_sumOfShiftsOfRegular_q_of_isProjectiveAsGradedModule hA hMd hM⟩

end

/-! ### The cone of a morphism -/

section

variable (F : derivedCategory' A ⥤ derivedCategory' B) [F.CommShift ℤ] [F.IsTriangulated]
  {N : Bimodule A B}

/-- **The comparison at the third vertex of a distinguished triangle.** Both functors are exact,
so they carry a distinguished triangle to a distinguished triangle; comparisons at the first two
vertices that make the first square commute extend to a morphism of distinguished triangles, and
the five lemma of Tag 014A makes its third component an isomorphism. -/
theorem exists_iso_obj₃_of_distinguished (T : Triangle (derivedCategory' A))
    (hT : T ∈ distTriang (derivedCategory' A))
    (α : (derivedTensorFunctor N).obj T.obj₁ ≅ F.obj T.obj₁)
    (β : (derivedTensorFunctor N).obj T.obj₂ ≅ F.obj T.obj₂)
    (hcomm : (derivedTensorFunctor N).map T.mor₁ ≫ β.hom = α.hom ≫ F.map T.mor₁) :
    Nonempty ((derivedTensorFunctor N).obj T.obj₃ ≅ F.obj T.obj₃) := by
  obtain ⟨γ, hγ₂, hγ₃⟩ := complete_distinguished_triangle_morphism
    ((derivedTensorFunctor N).mapTriangle.obj T) (F.mapTriangle.obj T)
    ((derivedTensorFunctor N).map_distinguished T hT) (F.map_distinguished T hT)
    α.hom β.hom hcomm
  have hγ : IsIso γ :=
    isIso₃_of_isIso₁₂ (T := (derivedTensorFunctor N).mapTriangle.obj T)
      (T' := F.mapTriangle.obj T)
      { hom₁ := α.hom, hom₂ := β.hom, hom₃ := γ
        comm₁ := hcomm, comm₂ := hγ₂, comm₃ := hγ₃ }
      ((derivedTensorFunctor N).map_distinguished T hT) (F.map_distinguished T hT)
      (inferInstanceAs (IsIso α.hom)) (inferInstanceAs (IsIso β.hom))
  exact ⟨@asIso _ _ _ _ γ hγ⟩

variable [F.Additive] [F.IsEquivalence]
  (e : (derivedTensorFunctor N).obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
      F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))

/-- **Stacks Tag 09SB, the corollary for cones.** In the setting of
`DifferentialGraded.Bimodule.sumOfShiftsNatIso`, if the first two vertices of a distinguished
triangle of `D(A, d)` are isomorphic to direct sums of shifts of `A` then `G` and `F` agree at
the third: `G(M) ≅ F(M)` for `M` a cone of a morphism between sums of shifts of `A`.

This is pointwise, as the source states it — the source writes `G(M) ≅ F(M)` here, not a
functorial isomorphism — and it is deduced from the functorial isomorphism on the sums of shifts:
it is the commuting square at the morphism, not the two isomorphisms alone, that the five lemma
needs. The same statement for a cone of a morphism between graded projective modules is
`DifferentialGraded.Bimodule.exists_iso_cone_of_retractOfSumOfShifts`. -/
theorem exists_iso_cone_of_sumOfShifts
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    {ι κ : Type u} (k : ι → ℤ) (l : κ → ℤ)
    (T : Triangle (derivedCategory' A)) (hT : T ∈ distTriang (derivedCategory' A))
    (eX : T.obj₁ ≅ ∐ fun i => ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
      (regularModule A))⟦k i⟧)
    (eY : T.obj₂ ≅ ∐ fun j => ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
      (regularModule A))⟦l j⟧) :
    Nonempty ((derivedTensorFunctor N).obj T.obj₃ ≅ F.obj T.obj₃) := by
  refine exists_iso_obj₃_of_distinguished F T hT
    ((derivedTensorFunctor N).mapIso eX ≪≫ shiftsComparison F e k ≪≫ (F.mapIso eX).symm)
    ((derivedTensorFunctor N).mapIso eY ≪≫ shiftsComparison F e l ≪≫ (F.mapIso eY).symm) ?_
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv]
  exact (transport_naturality (derivedTensorFunctor N) F _ _ eX eY T.mor₁
    (shiftsComparison_naturality F e hA he k l _)).symm

/-- **Stacks Tag 09SB, the corollary for cones, at the graded projective modules.** In the
setting of `DifferentialGraded.Bimodule.retractNatIso`, if the first two vertices of a
distinguished triangle of `D(A, d)` are retracts of direct sums of shifts of `A` — in particular
if they are the classes of graded projective differential graded modules with vanishing
differential, by `DifferentialGraded.Bimodule`
`.retractClosure_sumOfShiftsOfRegular_q_of_isProjectiveAsGradedModule` — then `G` and `F` agree
at the third: `G(M) ≅ F(M)` for `M` a cone of a morphism between such modules.

This is the source's second assertion, "one can conclude that `G(M) ≅ F(M)` when `M` is a cone of
a map between such modules", with "such modules" being the graded projective ones. It is
pointwise, as the source states it, and it is deduced from the functorial isomorphism on the
retracts: it is the commuting square at the morphism, not the two isomorphisms alone, that the
five lemma needs. -/
theorem exists_iso_cone_of_retractOfSumOfShifts
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (he : ∀ f : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)),
      e.hom ≫ F.map f = (derivedTensorFunctor N).map f ≫ e.hom)
    (T : Triangle (derivedCategory' A)) (hT : T ∈ distTriang (derivedCategory' A))
    (hX : (sumOfShiftsOfRegular A).retractClosure T.obj₁)
    (hY : (sumOfShiftsOfRegular A).retractClosure T.obj₂) :
    Nonempty ((derivedTensorFunctor N).obj T.obj₃ ≅ F.obj T.obj₃) := by
  exact exists_iso_obj₃_of_distinguished F T hT
    (retractComparisonOfSumOfShifts F e hA he ⟨T.obj₁, hX⟩)
    (retractComparisonOfSumOfShifts F e hA he ⟨T.obj₂, hY⟩)
    ((retractNatIso F e hA he).hom.naturality
      (ObjectProperty.homMk (X := ⟨T.obj₁, hX⟩) (Y := ⟨T.obj₂, hY⟩) T.mor₁))

end

end DifferentialGraded.Bimodule

end
