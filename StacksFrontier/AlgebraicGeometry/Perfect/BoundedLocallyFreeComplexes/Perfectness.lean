module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximation
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs

/-!
# Bounded complexes of finite locally free modules are perfect

This is the first assertion of Tag 0F8I: the obvious functor `K^b(A) ⥤ D(O_X)`, where `A` is the
additive category of finite locally free `O_X`-modules, lands in the full subcategory
`D_perf(O_X)` of perfect objects.

The proof needs no hypothesis on `X` at all: a bounded complex of finite locally free modules is
*itself* strictly perfect over a small enough open, so it is its own local strictly perfect
approximation and the quasi-isomorphism of Tag 08CM can be taken to be the identity. Around a
point `x`, finite local freeness gives one open neighbourhood per degree; only finitely many
degrees are nonzero, so a finite intersection of those neighbourhoods works for all degrees at
once, and the degrees outside the bounded range restrict to zero objects.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfect_of_boundedFiniteLocallyFree`: the image under
  `CategoryTheory.DerivedCategory.Qh` of an object of `K^b(A)` is perfect.

## Implementation notes

`StrictlyPerfect.isDirectSummandOfFiniteFree_of_iso_free` is the last step of the local
argument: a module isomorphic to a free module on a finite index set is a direct summand of a
finite free module, because the free module on a finite index set *is* a finite free module by
`StrictlyPerfect.finiteFreeIsoFree`.

The two shapes of restriction are identified by the equality of functors
`Stacks.Perfect.BoundedLocallyFreeComplexes.restrictModules_eq_restrictFunctor`. It is a
  propositional equality, not a
definitional one, so the local isomorphism is transported across it with
`CategoryTheory.eqToIso` rather than by rewriting the goal: the goal mentions
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex`, which `rw` cannot see into without
  breaking type-correctness at
`implicit` transparency.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes

universe u v w

namespace StrictlyPerfect

/-- **A module free of finite rank is a direct summand of a finite free module.** A finite index
set is equivalent to `Fin n`, and `StrictlyPerfect.finiteFreeIsoFree` identifies the free module
on `ULift (Fin n)` with `O_X ^ n`; the resulting isomorphism is in particular a retract. -/
theorem isDirectSummandOfFiniteFree_of_iso_free {X : RingedSpace.{u, u}}
    (M : OXMod.{u} X) (I : Type u) [Finite I] (e : M ≅ SheafOfModules.free I) :
    IsDirectSummandOfFiniteFree M := by
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin I
  rw [isDirectSummandOfFiniteFree_iff_retract]
  refine ⟨n, ⟨?_⟩⟩
  let e' : M ≅ finiteFree X n :=
    e ≪≫ SheafOfModules.freeFunctor.mapIso (Equiv.toIso (eqv.trans Equiv.ulift.symm)) ≪≫
      (finiteFreeIsoFree X n).symm
  exact ⟨e'.hom, e'.inv, e'.hom_inv_id⟩

end StrictlyPerfect

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-- **A point which lies in every member of a family of opens lies in an open contained in each
member of any finite subfamily.** Intersect the finitely many members. -/
theorem exists_mem_opens_le_of_finset {T : Type*} [TopologicalSpace T] (x : T)
    {ι : Type*} (V : ι → Opens T) (hxV : ∀ i, x ∈ V i) (s : Finset ι) :
    ∃ U : Opens T, x ∈ U ∧ ∀ i ∈ s, U ≤ V i := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨⊤, trivial, by simp⟩
  | insert j s hj ih =>
      obtain ⟨U, hxU, hU⟩ := ih
      refine ⟨U ⊓ V j, ⟨hxU, hxV j⟩, fun k hk => ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact inf_le_right
      · exact le_trans inf_le_left (hU k hk)

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **`K^b(A)` lands in `D_perf(O_X)`.** A bounded complex of finite locally free modules is
strictly perfect on a small enough neighbourhood of each point of `X`, so it is perfect in the
sense of Tag 08CM with the identity as the local quasi-isomorphism, and it represents its own
image in the derived category. -/
@[stacks 0F8I "the functor lands in perfect objects"]
theorem perfect_of_boundedFiniteLocallyFree (X : Scheme.{u})
    (E : BoundedFiniteLocallyFreeHomotopyCategory X) :
    IsPerfect (X := X.toRingedSpace) (DerivedCategory.Qh.obj E.obj) := by
  classical
  obtain ⟨K, ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hflf⟩, hKE⟩ :=
    (ObjectProperty.strictMap_iff _ _ _).mp E.property
  have := ha
  have := hb
  refine ⟨K, ?_, ⟨((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
    eqToIso (congrArg DerivedCategory.Qh.obj hKE)⟩⟩
  have hflf' : ∀ j : ℤ, Scheme.Modules.IsFiniteLocallyFree (K.X j) := by
    intro j
    have := hflf j
    exact Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFree _
  have key : ∀ x : X.carrier, ∃ U : X.Opens, x ∈ U ∧
      IsStrictlyPerfect (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex (X :=
        X.toRingedSpace) K U) := by
    intro x
    choose V hxV I hI eI using fun j : ℤ => hflf' j x
    obtain ⟨U, hxU, hUle⟩ := exists_mem_opens_le_of_finset x V hxV (Finset.Icc a b)
    have hzero : ∀ i, ¬(a ≤ i ∧ i ≤ b) →
        IsZero ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace
          U).obj (K.X i)) := by
      intro i hi
      refine (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace
        U).map_isZero ?_
      rw [not_and_or, not_le, not_le] at hi
      rcases hi with h | h
      · exact K.isZero_of_isStrictlyGE a i h
      · exact K.isZero_of_isStrictlyLE b i h
    refine ⟨U, hxU, ?_, ?_⟩
    · refine Set.Finite.subset (Set.finite_Icc a b) fun i hi => ?_
      simp only [Set.mem_ofPred_eq] at hi
      by_contra h
      exact hi (hzero i h)
    · intro i
      by_cases hi : a ≤ i ∧ i ≤ b
      · have hle : U ≤ V i := hUle i (Finset.mem_Icc.mpr hi)
        have := hI i
        have hobj := congrArg (fun F : X.Modules ⥤ _ => F.obj (K.X i))
          (restrictModules_eq_restrictFunctor X U)
        exact isDirectSummandOfFiniteFree_of_iso_free _ (I i)
          (eqToIso hobj ≪≫ Scheme.Modules.restrictFreeOfLE hle (K.X i) (I i) (eI i).some)
      · exact isDirectSummandOfFiniteFree_of_isZero (hzero i hi)
  choose U hxU hSP using key
  refine ⟨X.carrier, U, ?_, fun x => ⟨_, hSP x, 𝟙 _, inferInstance⟩⟩
  refine top_le_iff.mp fun x _ => ?_
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
