module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictionBijection
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction

/-!
# Being a relative cycle is local on the source

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let
`r ≥ 0`. A family `α` of `r`-cycles on the fibres of `X/S` is a relative `r`-cycle as soon as its
restriction to each member of a family of open subschemes of `X` covering `X` is one.

The restriction clause of [Stacks, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51),
`Stacks.Chow.isRelativeCycle_fiberCycleRestrict`, is the other implication, so the two together say
that the valuative condition of Definition 0H50 is local on `X`.

## Main results

* `Stacks.Chow.isRelativeCycle_of_openCover` — the valuative condition is local on the source.
* `Stacks.Chow.isRelativeCycle_iff_forall_fiberCycleRestrict` — the two implications together.

## References

* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Lemma 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace Stacks.Chow

/-- Let `g : T ⟶ S` and `t ∈ T`. A point of the fibre over `t` of `X ×_S T` whose image in `X` lies
in an open subscheme `j : U ⟶ X` over `S` lifts to the fibre over `t` of `U ×_S T`. -/
theorem mem_range_fiberRestrict_of_mem_range {X S U T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (g : T ⟶ S) (t : T)
    (y : (pullback.snd f g).fiber t)
    (hy : pullback.fst f g ((pullback.snd f g).fiberι t y) ∈ Set.range (j : U → X)) :
    y ∈ Set.range
      (fiberRestrict (pullback.snd f g) (pullback.snd fU g) (pullbackRestrict f fU j h g)
        (pullbackRestrict_snd f fU j h g) t : (pullback.snd fU g).fiber t →
          (pullback.snd f g).fiber t) := by
  have hrange := range_fiberRestrict (pullback.snd f g) (pullback.snd fU g)
    (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) t
  rw [hrange, range_pullbackRestrict]
  exact hy

/-- **Being a relative cycle is local on the source.** Let `S` be locally Noetherian, let
`f : X ⟶ S` be locally of finite type, let `r ≥ 0` and let `α` be a family of `r`-cycles on the
fibres of `X/S`. If `j i : U i ⟶ X` is a family of open immersions over `S` whose images cover
`X`, and the restriction of `α` to each `U i` is a relative `r`-cycle on `U i/S`, then `α` is a
relative `r`-cycle on `X/S`. -/
theorem isRelativeCycle_of_openCover {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) {ι : Type v} {U : ι → Scheme.{u}}
    (fU : ∀ i, U i ⟶ S) [∀ i, LocallyOfFiniteType (fU i)] (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (h : ∀ i, j i ≫ f = fU i)
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i : U i → X))
    (hα : ∀ i, IsRelativeCycle (fU i) r
      fun s ↦ fiberCycleRestrict f (fU i) (j i) (h i) s r (α s)) :
    IsRelativeCycle f r α := by
  intro R _ _ _ c
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  obtain ⟨i, hi⟩ := hcover
    (pullback.fst f c ((pullback.snd f c).fiberι (IsLocalRing.closedPoint R) y))
  obtain ⟨y', hy'⟩ := mem_range_fiberRestrict_of_mem_range f (fU i) (j i) (h i) c
    (IsLocalRing.closedPoint R) y hi
  have key := hα i R c
  simp only [baseChangeFamily_fiberCycleRestrict f (fU i) (j i) (h i) c r α (genericPoint _),
    baseChangeFamily_fiberCycleRestrict f (fU i) (j i) (h i) c r α (IsLocalRing.closedPoint R),
    specializationCycle_fiberCycleRestrict] at key
  subst hy'
  exact congrArg (fun z : FiberCycleGroup (pullback.snd (fU i) c) (IsLocalRing.closedPoint R) r ↦
      (z : AlgebraicCycle ((pullback.snd (fU i) c).fiber (IsLocalRing.closedPoint R)) ℤ) y') key

/-- **The valuative condition of Definition 0H50 is local on the source.** If `j i : U i ⟶ X` is a
family of open immersions over `S` whose images cover `X`, then `α` is a relative `r`-cycle on
`X/S` if and only if its restriction to each `U i` is a relative `r`-cycle on `U i/S`. -/
theorem isRelativeCycle_iff_forall_fiberCycleRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r)
    {ι : Type v} {U : ι → Scheme.{u}} (fU : ∀ i, U i ⟶ S) [∀ i, LocallyOfFiniteType (fU i)]
    (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)] (h : ∀ i, j i ≫ f = fU i)
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i : U i → X)) :
    IsRelativeCycle f r α ↔
      ∀ i, IsRelativeCycle (fU i) r
        fun s ↦ fiberCycleRestrict f (fU i) (j i) (h i) s r (α s) :=
  ⟨fun hα i ↦ isRelativeCycle_fiberCycleRestrict f (fU i) (j i) (h i) r hα,
    isRelativeCycle_of_openCover f r α fU j h hcover⟩

end Stacks.Chow

end
