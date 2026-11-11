module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardKernelDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PicardBaseClassDies
public import StacksFrontier.AlgebraicGeometry.Quot.SchemesOverCoveringFamily

/-!
# The exact sequence `0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)` (Stacks 0D27)

In Situation 0D25 — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` — assume that
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T` over `B`.  Stacks 0D27 states
that for every such `T` the sequence

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)`

is exact, the first arrow being pullback along `f_T : X_T ⟶ T` and the second the canonical map
into the fppf sheafification `Pic_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.mem_range_basePicardPullback_of_picardClassMap_eq`:
  a class of `X_T` that dies in `Pic_{X/B}(T)` is pulled back from `T`.
* `AlgebraicGeometry.Space.PicardSituation.exact_picardSequence`: **Stacks 0D27.**

## Implementation notes

The three parts of the exactness are proved in three places, all unconditionally:

* exactness at `Pic(T)` is `AlgebraicGeometry.Space.PicardSituation.injective_basePicardPullback`
  with its input `AlgebraicGeometry.Space.ModulePushforwardUnitIso` supplied by the theorem
  `AlgebraicGeometry.Space.modulePushforwardUnitIso`;
* that the composite is zero is
  `AlgebraicGeometry.Space.PicardSituation.picardClassMap_basePicardPullback`, which needs no
  hypothesis;
* that a class dying in `Pic_{X/B}(T)` comes from `T` is the descent argument of the source:
  the class is trivial on the base changes of an fpqc covering family of `T`
  (`AlgebraicGeometry.Space.SchemesOver.exists_isFpqcCovering_of_mem_restrictedTopology`), the
  trivializations give a descent datum on the structure sheaves of its members
  (`AlgebraicGeometry.Space.PicardSituation.LocalTrivialization.descentDatum`), and the
  descended module is invertible and pulls back to the given one.

"Exact at `Pic(X_T)`" is stated as: the kernel of `Pic(X_T) ⟶ Pic_{X/B}(T)`, the set of classes
with the same image as the trivial class `0`, is the image of `Pic(T)`.  `Pic_{X/B}(T)` is a set
(the value of the sheafification of a presheaf of sets), and the image of `0` is its neutral
element as the sheafification of a presheaf of groups.

## References

* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open QuasiCoherentDescent

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- **A Picard class of `X_T` dying in `Pic_{X/B}(T)` comes from `Pic(T)`**, under the
hypothesis of Stacks 0D27. -/
theorem mem_range_basePicardPullback_of_picardClassMap_eq (h : s.StructureSheafMapIso)
    (T : s.SchemesOver) (x : s.picardAt T) (hx : s.picardClassMap T x = s.picardClassMap T 0) :
    x ∈ Set.range (s.basePicardPullback T) := by
  obtain ⟨L, hL, rfl⟩ := exists_picardClass (s.baseChange T) x
  obtain ⟨R, hR, hRx⟩ := s.exists_forall_of_picardClassMap_eq _ _ hx
  obtain ⟨I, U, g, hg, hcov⟩ := SchemesOver.exists_isFpqcCovering_of_mem_restrictedTopology hR
  have htriv : ∀ i, Nonempty ((modulePullback B S hS (baseChangeMap s.f (g i))).obj L ≅
      structureModule (s.baseChange (U i))) := by
    intro i
    have := hRx (g i) (hg i)
    rw [picardMap_eq, picardPullback_picardClass, picardPullback_zero] at this
    exact (picardClass_eq_zero_iff _ _ _).1 this
  let t : s.LocalTrivialization T L := ⟨I, U, g, fun i ↦ (htriv i).some⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := forall_isEffective_of_isFpqcCovering B S hS t.Y t.fY hcov
    (t.descentDatum h)
  let e' : t.descentDatum h ≅ canonicalDescentDatum' B S hS t.Y t.fY N hN := e
  refine ⟨picardClass _ N (t.isInvertibleModule_descended h hN e' hcov), ?_⟩
  rw [basePicardPullback_picardClass]
  exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 (t.nonempty_iso_descended h hN e' hcov hL)

/-- **Stacks 0D27.**  In Situation 0D25, if `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every
scheme `T` over the base, then for every such `T` the sequence
`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)` is exact: pullback along `f_T` is injective, and a class
of `X_T` maps to the trivial element of the relative Picard functor exactly when it is pulled
back from `T`. -/
@[stacks 0D27 "the exact sequence 0 → Pic(T) → Pic(X_T) → Pic_{X/B}(T)"]
theorem exact_picardSequence (h : s.StructureSheafMapIso) (T : s.SchemesOver) :
    Function.Injective (s.basePicardPullback T) ∧
      ∀ x : s.picardAt T, s.picardClassMap T x = s.picardClassMap T 0 ↔
        x ∈ Set.range (s.basePicardPullback T) :=
  ⟨s.injective_basePicardPullback modulePushforwardUnitIso h T, fun x ↦
    ⟨s.mem_range_basePicardPullback_of_picardClassMap_eq h T x, by
      rintro ⟨y, rfl⟩
      exact s.picardClassMap_basePicardPullback T y⟩⟩

end PicardSituation

end AlgebraicGeometry.Space

end
