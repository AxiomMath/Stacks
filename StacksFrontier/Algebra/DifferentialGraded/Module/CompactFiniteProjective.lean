module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CompactCohomologyWindow
public import StacksFrontier.Algebra.DifferentialGraded.Module.Finite
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksFrontier.Algebra.Homology.DifferentialGraded.GradedProjective
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite modules computing their derived morphisms are compact

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. [Stacks, Tag 09RB]
asserts that, when `A` lives in only finitely many degrees, the compact objects of `D(A, d)` are
exactly the objects representable by a differential graded `A`-module `P` which is finite
projective as a graded `A`-module and satisfies `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for
every differential graded `A`-module `M`. This file proves the implication that goes from such a
representative to compactness, (2) ⟹ (1), which is the content of [Stacks, Tag 09R1] and needs
neither the boundedness of `A` nor the projectivity of `P`.

*The disposition of the other implication.* (1) ⟹ (2), read literally, is **a mistake in the
Stacks Project, pending review**: it is **contradicted by the source's own [Stacks, Tag 09R5]**,
and the contradiction is machine-checked in
`StacksFrontier/Examples/Algebra/CompactObjectNoFiniteProjectiveModel.lean`
(`Stacks.Examples.not_forall_exists_finite_gradedProjective_of_isCompactObject`), whose witness
is a compact object over a bounded algebra with no finite graded-projective representative at
all. The statement the source's proof does establish is registered under the tag in
`StacksFrontier/Algebra/DifferentialGraded/Module/CompactFiniteFree.lean`:
`DifferentialGradedModule.exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject`, where a
compact object is a *direct summand* in `D(A, d)` of the image of a module which is *finite free*
as a graded module and satisfies the condition of [Stacks, Tag 09R0] — unconditionally, with no
boundedness hypothesis. Its converse is
`DifferentialGradedModule.isCompactObject_of_retract_isFiniteFreeAsGradedModule`, which is the
implication proved below with condition (2) read in that corrected form: finite freeness is used
only through the finiteness it implies. So the tag's equivalence does hold once condition (2) is
corrected, and the file below is the half of it that the source states correctly.

The argument is the one indicated in the source: direct sums in `D(A, d)` are computed by direct
sums of differential graded modules (Tag 09QI), the hypothesis on `P` moves the test for
compactness from `D(A, d)` to `K(A, d)`, and there a morphism out of `P` is the homotopy class of
a homomorphism. A homomorphism `P ⟶ ⨁ᵢ Nᵢ` carries a finite generating set of `P` into a finite
subsum, hence factors through it; so it is the sum over a finite set of its coordinates, composed
with the coprojections. Injectivity of the test map needs no hypothesis at all, holding for the
test map of any colimit cofan.

## Main definitions

* `DifferentialGradedModule.evalAtPoint`: evaluation at a point of the source, as an additive map
  on the homomorphisms into a fixed differential graded module.

## Main results

* `DifferentialGradedModule.exists_eq_sum_comp_directSumInj_of_isFinite`: a homomorphism from a
  finite differential graded module into a direct sum is a finite sum of homomorphisms into the
  summands, composed with the coprojections.
* `DifferentialGradedModule.isCompactObject_q_of_isFinite`: a finite differential graded module
  out of which the localization functor is bijective on morphisms represents a compact object of
  `D(A, d)`.
* `DifferentialGradedModule.isCompactObject_of_exists_finite_projective_representative`:
  **[Stacks, Tag 09RB], the implication (2) ⟹ (1)**.

## Implementation notes

*Finiteness, not projectivity.* Only the finite generation of `P` as a right `A`-module —
`DifferentialGradedModule.IsFinite`, Tag 09R1 — enters the proof. Projectivity as a graded module
is part of condition (2) of Tag 09RB and is carried in the statement of the tagged result, as is
the boundedness of `A`, but neither is used. Neither is needed for the other implication either,
in the form in which that one is true: it produces a *finite free* graded module and a *direct
summand*, and needs no bound on `A`; see the disposition above.

*Where the finiteness is used.* The set of points of `P` whose image in `⨁ᵢ Nᵢ` is supported on a
fixed finite set of indices is an `Aᵐᵒᵖ`-submodule, so it is the whole of `P` as soon as it
contains a generating set; taking for the finite set the union of the supports of the images of a
finite generating set gives the factorisation. The coordinates of the factorisation are the
composites of the homomorphism with the coordinate maps
`DifferentialGradedModule.directSumComponent` of the direct sum.

*Transparency.* The carrier of `DifferentialGradedModule.directSumObj` is the direct sum
`⨁ᵢ (Nᵢ).M` of the carriers only after unfolding at default transparency, so the image of a point
is named at the honest type before any coordinate is read off, exactly as elsewhere in this
chapter.

*Universes.* Everything is single-universe, as in the rest of this chapter: the index type of a
direct sum is taken in the universe of the modules, which is the universe in which `D(A, d)` has
direct sums, and compactness is tested against those.

## References

* [Stacks Project, Tag 09RB](https://stacks.math.columbia.edu/tag/09RB)
* [Stacks Project, Tag 09R1](https://stacks.math.columbia.edu/tag/09R1), finiteness and the
  question answered here.
* [Stacks Project, Tag 09R0](https://stacks.math.columbia.edu/tag/09R0), the modules whose
  homotopy morphisms compute their derived morphisms.
* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI), the direct sums of
  `D(A, d)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Evaluation of a finite sum of homomorphisms -/

/-- Evaluation at a point of the source, as an additive map on the homomorphisms of differential
graded modules into a fixed target. It computes the value at that point of a finite sum of
homomorphisms. -/
def evalAtPoint {P T : DifferentialGradedModule.{u, u, u} A} (x : P.M) : (P ⟶ T) →+ T.M where
  toFun f := f.toFun x
  map_zero' := by rw [Hom.hom_zero_toFun]; rfl
  map_add' f g := by rw [Hom.hom_add_toFun]; rfl

/-- The value at a point of a finite sum of homomorphisms of differential graded modules. -/
theorem sum_toFun_apply {P T : DifferentialGradedModule.{u, u, u} A} {ι : Type*} (s : Finset ι)
    (f : ι → (P ⟶ T)) (x : P.M) :
    (∑ i ∈ s, f i).toFun x = ∑ i ∈ s, (f i).toFun x :=
  map_sum (evalAtPoint (T := T) x) f s

/-! ### Homomorphisms from a finite module into a direct sum -/

section DirectSum

variable {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule.{u, u, u} A)

/-- **A homomorphism from a finite differential graded module into a direct sum factors through a
finite subsum.** The points whose image is supported on the union of the supports of the images of
a finite generating set form an `Aᵐᵒᵖ`-submodule containing that generating set, hence all of the
source; so the homomorphism is the sum over that finite set of its coordinates, composed with the
coprojections. -/
theorem exists_eq_sum_comp_directSumInj_of_isFinite {P : DifferentialGradedModule.{u, u, u} A}
    (hP : IsFinite P) (g : P ⟶ directSumObj N) :
    ∃ (s : Finset ι) (h : ∀ i, P ⟶ N i),
      g = ∑ i ∈ s, h i ≫ directSumInj N i := by
  classical
  obtain ⟨G, hG⟩ := hP.fg_top
  set L : P.M →ₗ[MulOpposite A.A] (⨁ i, (N i).M) := g.toGradedHom.opLinearMap
  set s : Finset ι := G.biUnion fun x => (L x).support
  set W : Submodule (MulOpposite A.A) P.M :=
    { carrier := {x | ∀ i, i ∉ s → L x i = 0}
      add_mem' := fun {x y} hx hy i hi => by
        rw [map_add, DirectSum.add_apply, hx i hi, hy i hi, add_zero]
      zero_mem' := fun i _ => by rw [map_zero, DirectSum.zero_apply]
      smul_mem' := fun c x hx i hi => by
        rw [map_smul, DirectSum.smul_apply, hx i hi, smul_zero] }
  have hGW : (G : Set P.M) ⊆ (W : Set P.M) := fun x hx i hi =>
    DFinsupp.notMem_support_iff.mp fun hs =>
      hi (Finset.mem_biUnion.mpr ⟨x, hx, hs⟩)
  have hle : (⊤ : Submodule (MulOpposite A.A) P.M) ≤ W := by
    rw [← hG]
    exact Submodule.span_le.mpr hGW
  have hzero : ∀ (x : P.M) (i : ι), i ∉ s → L x i = 0 := fun x => hle Submodule.mem_top
  refine ⟨s, fun i => g ≫ directSumComponent N i, Hom.ext (LinearMap.ext fun x => ?_)⟩
  have hsupp : (L x).support ⊆ s := fun i hi =>
    not_not.mp fun hi' => (DFinsupp.mem_support_iff.mp hi) (hzero x i hi')
  have hterm : ∀ i ∈ s, ((g ≫ directSumComponent N i) ≫ directSumInj N i).toFun x
      = DirectSum.of (fun j => (N j).M) i (L x i) := fun i _ => by
    rw [Hom.comp_toFun_apply, directSumInj_toFun_apply, DirectSum.lof_eq_of]
    rfl
  rw [sum_toFun_apply, Finset.sum_congr rfl hterm,
    (Finset.sum_subset hsupp fun i _ hi => by
      rw [DFinsupp.notMem_support_iff.mp hi, map_zero]).symm,
    DirectSum.sum_support_of]
  rfl

end DirectSum

/-! ### Compactness -/

section Compact

variable (A)

/-- The canonical functor from differential graded modules to the derived category: the quotient
by homotopy followed by the localization at the quasi-isomorphisms. -/
private abbrev qDerived :
    DifferentialGradedModule.{u, u, u} A ⥤ derivedCategory' A :=
  toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q

variable {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule.{u, u, u} A)

/-- The images in `D(A, d)` of the coprojections of `⨁ᵢ Nᵢ` exhibit the image of `⨁ᵢ Nᵢ` as a
direct sum: **Tag 09QI**. -/
private def isColimitCofanOfDirectSum :
    IsColimit (Cofan.mk ((qDerived A).obj (directSumObj N))
      fun i => (qDerived A).map (directSumInj N i)) :=
  isColimitCofanMkObjOfIsColimit (qDerived A) N (directSumInj N) (isColimit_directSumObj N)

variable {P : DifferentialGradedModule.{u, u, u} A}

/-- Every morphism of `D(A, d)` out of a finite differential graded module `P` into the image of
`⨁ᵢ Nᵢ` is the image of a finite sum of morphisms into the images of the summands. It comes from
a morphism of `K(A, d)` by hypothesis, hence from a homomorphism of differential graded modules,
which is such a finite sum by
`DifferentialGradedModule.exists_eq_sum_comp_directSumInj_of_isFinite`. -/
private theorem surjective_cofanMap_of_isFinite (hP : IsFinite P)
    (hD : ∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
      (((quasiIsomorphisms' A).Q).map :
        ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) :
    Function.Surjective (cofanMap ((qDerived A).obj P)
      fun i => (qDerived A).map (directSumInj N i)) := by
  classical
  intro Ψ
  obtain ⟨ψ, hψ⟩ := (hD (directSumObj N)).2 Ψ
  obtain ⟨g, rfl⟩ : ∃ g : P ⟶ directSumObj N, (toHomotopyCategory A).map g = ψ := by
    induction ψ using Quot.inductionOn with
    | _ g => exact ⟨g, rfl⟩
  obtain ⟨s, h, hsum⟩ := exists_eq_sum_comp_directSumInj_of_isFinite N hP g
  refine ⟨∑ i ∈ s, DirectSum.of _ i ((qDerived A).map (h i)), ?_⟩
  rw [map_sum]
  simp only [cofanMap_of, ← Functor.map_comp]
  rw [← Functor.map_sum, ← hsum]
  exact hψ

/-- The canonical map `⨁ᵢ Hom(P, Q(Nᵢ)) → Hom(P, Q(⨁ᵢ Nᵢ))` is bijective. Injectivity holds for
the test map of any colimit cofan, and surjectivity is
`DifferentialGradedModule.surjective_cofanMap_of_isFinite`. -/
private theorem bijective_cofanMap_of_isFinite (hP : IsFinite P)
    (hD : ∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
      (((quasiIsomorphisms' A).Q).map :
        ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) :
    Function.Bijective (cofanMap ((qDerived A).obj P)
      fun i => (qDerived A).map (directSumInj N i)) :=
  ⟨injective_cofanMap _ _ (isColimitCofanOfDirectSum A N),
    surjective_cofanMap_of_isFinite A N hP hD⟩

/-- The canonical map `⨁ᵢ Hom(P, Fᵢ) → Hom(P, ∐ᵢ Fᵢ)` is bijective for a family of objects of
`D(A, d)` presented as the images of a family of differential graded modules: the two cofans have
isomorphic families, and both exhibit a direct sum of that family, so bijectivity transfers from
`DifferentialGradedModule.bijective_cofanMap_of_isFinite`. -/
private theorem bijective_cofanMap_sigmaι_of_isFinite (hP : IsFinite P)
    (hD : ∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
      (((quasiIsomorphisms' A).Q).map :
        ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _))
    (F : ι → derivedCategory' A) [HasCoproduct F]
    (e : ∀ i, (qDerived A).obj (N i) ≅ F i) :
    Function.Bijective (cofanMap ((qDerived A).obj P) (Limits.Sigma.ι F)) :=
  bijective_cofanMap_of_iso _ (fun i => (qDerived A).map (directSumInj N i))
    (Limits.Sigma.ι F) e
    ((isColimitCofanOfDirectSum A N).coconePointsIsoOfNatIso (coproductIsCoproduct F)
      (Discrete.natIso fun i => e i.as))
    (fun i => (isColimitCofanOfDirectSum A N).comp_coconePointsIsoOfNatIso_hom
      (coproductIsCoproduct F) (Discrete.natIso fun i => e i.as) ⟨i⟩)
    (bijective_cofanMap_of_isFinite A N hP hD)

/-- **A finite differential graded module whose morphisms in the homotopy category already
compute its morphisms in the derived category represents a compact object of `D(A, d)`.** This is
the question raised in [Stacks, Tag 09R1]: for every family `Fᵢ` of objects of `D(A, d)` indexed
by a type of the ambient universe the canonical map `⨁ᵢ Hom(P, Fᵢ) → Hom(P, ∐ᵢ Fᵢ)` is bijective,
because the family may be presented by differential graded modules, whose direct sum computes the
direct sum of the family.

This is the assertion of the remark: the source asks it for a `P` that is finite *and graded
projective*, and answers it affirmatively for a `P` that is moreover an object of the category
`𝒟` of [Stacks, Tag 09R0] — which is the hypothesis `hD` below. Graded projectivity is not
needed and is not assumed, so this is more general than the source's claim. The definition of
*finite* that the remark also gives is `DifferentialGradedModule.IsFinite`. -/
theorem isCompactObject_q_of_isFinite {P : DifferentialGradedModule.{u, u, u} A} (hP : IsFinite P)
    (hD : ∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
      (((quasiIsomorphisms' A).Q).map :
        ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) :
    IsCompactObject.{u} ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P) where
  bijective_toAddMonoid_rightComp_sigmaι F :=
    bijective_cofanMap_sigmaι_of_isFinite A
      (fun i => ((quasiIsomorphisms' A).Q.objPreimage (F i)).as) hP hD F
      (fun i => (quasiIsomorphisms' A).Q.objObjPreimageIso (F i))

end Compact

/-! ### Tag 09RB, the implication from a finite projective representative to compactness -/

/-- **[Stacks, Tag 09RB], the implication (2) ⟹ (1).** *"Let `(A, d)` be a differential graded
algebra. Assume that `A^n = 0` for `|n| ≫ 0`. Let `E` be an object of `D(A, d)`. The following are
equivalent: (1) `E` is a compact object, and (2) `E` can be represented by a differential graded
`A`-module `P` which is finite projective as a graded `A`-module and satisfies
`Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every differential graded `A`-module `M`."*

Condition (2) is read as the conjunction of: `P` is finite, that is finitely generated as a right
`A`-module (`DifferentialGradedModule.IsFinite`, Tag 09R1); `P` is projective as a graded module
(`Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule`, Tag 09K0); the localization
functor is bijective on morphisms out of the class of `P` into the class of every differential
graded module (Tag 09R0); and `E` is isomorphic in `D(A, d)` to the class of `P`.

The boundedness of `A` and the graded projectivity of `P` are hypotheses of the source statement
and are recorded here, but this implication uses neither: finiteness together with the comparison
of morphism groups already gives compactness. -/
@[stacks 09RB "(2) ⟹ (1)"]
theorem isCompactObject_of_exists_finite_projective_representative
    (A : DifferentialGradedAlgebra.{u, u} R) (c : ℤ)
    (_hA : ∀ n : ℤ, c ≤ |n| → A.grading n = ⊥) (E : derivedCategory' A)
    (hE : ∃ P : DifferentialGradedModule.{u, u, u} A, IsFinite P ∧
      Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
        (Unbundled.module P) ∧
      (∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
        (((quasiIsomorphisms' A).Q).map :
          ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) ∧
      Nonempty (E ≅ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)) :
    IsCompactObject.{u} E := by
  obtain ⟨P, hP, _, hD, ⟨e⟩⟩ := hE
  exact isCompactObject_of_iso e (isCompactObject_q_of_isFinite A hP hD)

end DifferentialGradedModule

end
