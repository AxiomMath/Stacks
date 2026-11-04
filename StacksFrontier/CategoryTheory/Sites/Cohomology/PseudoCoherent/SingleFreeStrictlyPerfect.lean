module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TruncatingApproximationsGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# A finite free module in a single degree is strictly perfect, hence pseudo-coherent

Let `(C, O)` be a ringed site.  A module which is a direct summand of a finite free `O`-module,
placed in a single cohomological degree, is a strictly perfect complex — it has one nonzero term
and that term is a direct summand of a finite free module — and a strictly perfect complex is
`m`-pseudo-coherent for every `m`, the identity of its own restriction being an approximation over
the total covering.

This is the **first vertex of the induction triangle** of Stacks 08HE (2) ⇒ (1): the step produces
a morphism `𝒪^{⊕t}[-n] ⟶ E` out of a finite free module placed in degree `n`, and the recursion
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks for that vertex to be
`m`-pseudo-coherent.

## Why it is stated here

`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_isStrictlyPerfect` already exists in
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`, but it is `private`
there, so no consumer outside that module can name it; the same holds for the restriction lemma
`Stacks.SheafOfModules.isStrictlyPerfect_over` it uses, whose two public ingredients
(`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex` and
`Stacks.SheafOfModules.overFunctorUnitIso`) are therefore composed again below.  Nothing here is
more general than the private forms; it is the same statement at the same universes, made
nameable.

Note that the induction needs **no** chain-level return: the recursion concludes
`X.IsPseudoCoherentFrom E m` from the derived-level Stacks 08FV, whose proof does the chain-level
work internally, and the first vertex's pseudo-coherence is supplied here from a strictly perfect
representative.  So `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`
(Stacks 08FR (1)), which is stated at module universe `0` only, is not on the critical path for
clause (2) ⇒ (1).

## Main results

* `IsDirectSummandOfFiniteFree.free`: a free module on a finite index type is a direct summand of
  a finite free module.
* `IsStrictlyPerfect.single_obj`: a direct summand of a finite free module, placed in a single
  degree, is a strictly perfect complex.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_isStrictlyPerfect_site` and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_obj_of_isStrictlyPerfect`: a strictly
  perfect complex is `m`-pseudo-coherent, at the level of complexes and in `D(O)`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_singleFunctor_obj_free`: **the first vertex**
  — `𝒪^{⊕t}` placed in degree `n` is `m`-pseudo-coherent for every `m` and `n`.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

/-- **A free module on a finite index type is a direct summand of a finite free module**: it is
one on the nose, the retraction being the identity after reindexing the generators by
`ULift (Fin t)`. -/
public theorem IsDirectSummandOfFiniteFree.free {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (ι : Type w) [Finite ι] :
    IsDirectSummandOfFiniteFree R (SheafOfModules.free (R := R) ι) := by
  obtain ⟨t, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine IsDirectSummandOfFiniteFree.of_iso R
    ((SheafOfModules.freeFunctor (R := R)).mapIso (e.trans Equiv.ulift.symm).toIso) ?_
  exact (isDirectSummandOfFiniteFree_iff_free R _).mpr ⟨t, 𝟙 _, 𝟙 _, Category.comp_id _⟩

/-- **A direct summand of a finite free module, placed in a single degree, is strictly perfect.**
Only the one degree is nonzero, and the term there is the module itself. -/
public theorem IsStrictlyPerfect.single_obj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (n : ℤ) (M : SheafOfModules.{w} R) (hM : IsDirectSummandOfFiniteFree R M) :
    IsStrictlyPerfect R
      ((HomologicalComplex.single (SheafOfModules.{w} R) (ComplexShape.up ℤ) n).obj M) := by
  refine ⟨(Set.finite_singleton n).subset fun i hi => ?_, fun i => ?_⟩
  · by_contra hne
    exact hi (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n M i hne)
  · by_cases h : i = n
    · subst h
      exact IsDirectSummandOfFiniteFree.of_iso R
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M) hM
    · exact IsDirectSummandOfFiniteFree.of_isZero_general R
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n M i h)

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A strictly perfect complex is `m`-pseudo-coherent for every `m`.**  Over every object of the
site the total covering works and the identity of the restriction is an approximation: restriction
to a slice is exact and carries the unit sheaf to the unit sheaf, so it carries a strictly perfect
complex to a strictly perfect complex
(`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex`). -/
public theorem isPseudoCoherentComplexFrom_of_isStrictlyPerfect_site
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) (m : ℤ) :
    X.IsPseudoCoherentComplexFrom P m := by
  intro U
  refine ⟨⊤, by simp, fun V f hf => ?_⟩
  have hover : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      (X.restrictComplex P V) :=
    have : PreservesFiniteColimits
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
    Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
      (Stacks.SheafOfModules.overFunctorUnitIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) hP
  exact ⟨X.restrictComplex P V, hover, 𝟙 _, fun _ _ => inferInstance, inferInstance⟩

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **A strictly perfect complex is `m`-pseudo-coherent in `D(O)` for every `m`.** -/
public theorem isPseudoCoherentFrom_Q_obj_of_isStrictlyPerfect
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) (m : ℤ) :
    X.IsPseudoCoherentFrom (DerivedCategory.Q.obj P) m :=
  ⟨P, X.isPseudoCoherentComplexFrom_of_isStrictlyPerfect_site P hP m, ⟨Iso.refl _⟩⟩

/-- **The first vertex of the induction triangle of Stacks 08HE (2) ⇒ (1).**  A free `O`-module on
a finite index type, placed in cohomological degree `n`, is `m`-pseudo-coherent in `D(O)` for every
integer `m`. -/
public theorem isPseudoCoherentFrom_singleFunctor_obj_free (n m : ℤ) (ι : Type w) [Finite ι] :
    X.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι)) m :=
  X.isPseudoCoherentFrom_Q_obj_of_isStrictlyPerfect _
    (IsStrictlyPerfect.single_obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) n _
      (IsDirectSummandOfFiniteFree.free (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ι)) m

end AlgebraicGeometry.RingedSite

end
