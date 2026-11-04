module

public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GenericFibres
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ProperPushforwardRelative

/-!
# Lifting a relative cycle along an envelope over a discrete valuation ring

Let `R` be a discrete valuation ring, let `g : Y ⟶ Spec R` be of finite type and let
`p : Y' ⟶ Y` be proper and completely decomposed (Stacks 0GTI), that is, an envelope of `Y`
(Stacks 0GU5). This file proves that every relative `e`-cycle `β` on `Y/Spec R` is the proper
pushforward of a relative `e`-cycle on `Y'/Spec R`.

## Main results

* `Stacks.Chow.exists_isRelativeCycle_properPushforwardFamily_eq` — the lift of a relative cycle
  along an envelope over a discrete valuation ring.

## Implementation notes

Over the spectrum of a discrete valuation ring a relative `e`-cycle is pinned down by its member
over the generic point: that is Lemma 0H55, since the generic point is the only generic point of
an irreducible component of `Spec R`. So it is enough to lift the one cycle `β_η` on the generic
fibre of `Y` to a cycle on the generic fibre of `Y'`, and then to produce *some* relative cycle
on `Y'/Spec R` with that generic member.

The first step is the surjectivity half of Stacks 0GU8 at the level of cycle groups, which needs
no rational equivalence: the morphism `Y'_η ⟶ Y_η` induced on generic fibres is proper and
completely decomposed, being a base change of `p` (`Stacks.Chow.isPullback_inducedFiberMap` and
Tag 0GTK), so `Stacks.Chow.envelopeCycleLift_pushforward` lifts `β_η` through it. The second step
is `Stacks.Chow.exists_cycleClassMap_apply_genericPoint_eq`: over a discrete valuation ring every
cycle on the generic fibre of a finite type morphism is the generic member of a combination of
the cycle classes of Tag 0H6V, and such a combination is a relative cycle by Equation 0H58.

Finally the pushforward of the relative cycle so obtained is a relative cycle by the proper
pushforward clause of Lemma 0H51, so Lemma 0H55 identifies it with `β` from the agreement of the
generic members.

## References

* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Tag 0GTK](https://stacks.math.columbia.edu/tag/0GTK)
* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Lemma 0H55](https://stacks.math.columbia.edu/tag/0H55)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
* [Stacks Project, Tag 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Surjectivity of proper pushforward of cycles along a completely decomposed morphism.** The
cycle-group half of Stacks 0GU8: every `k`-cycle on `B` is the pushforward of a `k`-cycle on `A`
along a proper completely decomposed `q : A ⟶ B` over the base of the Chow situation. This is
`Stacks.Chow.envelopeCycleLift_pushforward`, stated for an arbitrary factorization of the
structure morphism of `A` rather than for the composite `q ≫ sB`. -/
theorem exists_properPushforward_eq_of_isCompletelyDecomposed (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (q : A ⟶ B) [IsProper q] (hq : q ≫ sB = sA)
    (hcd : IsCompletelyDecomposed q) (k : ℤ) (c : CycleGroup C sB k) :
    ∃ d : CycleGroup C sA k, properPushforward C sA sB q hq k d = c := by
  subst hq
  exact ⟨envelopeCycleLift C sB q hcd k c, envelopeCycleLift_pushforward C sB q hcd k c⟩

/-- **The fibres of a completely decomposed morphism over the base are completely decomposed.**
The morphism induced on the fibres over a point `s` of the base by a completely decomposed
morphism over the base is a base change of it, so Tag 0GTK applies. -/
theorem isCompletelyDecomposed_inducedFiberMap {X Y S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) [LocallyOfFiniteType sY] (q : X ⟶ Y)
    (hq : q ≫ sY = sX) (hcd : IsCompletelyDecomposed q) (s : S) :
    IsCompletelyDecomposed (inducedFiberMap sX sY q hq s) :=
  IsCompletelyDecomposed.of_isPullback (isPullback_inducedFiberMap sX sY q hq s) hcd

/-- **Lifting a relative cycle along an envelope over a discrete valuation ring.** Let `R` be a
discrete valuation ring, let `g : Y ⟶ Spec R` be locally of finite type and quasi-compact and
let `p : Y' ⟶ Y` be proper and completely decomposed. Every relative `e`-cycle `β` on
`Y/Spec R` is the proper pushforward along `p` of a relative `e`-cycle on `Y'/Spec R`. -/
theorem exists_isRelativeCycle_properPushforwardFamily_eq {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {Y Y' : Scheme.{u}} (g : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [QuasiCompact g] (p : Y' ⟶ Y) [IsProper p]
    (hcd : IsCompletelyDecomposed p) (e : ℕ) {β : FamilyOfCycles g e}
    (hβ : IsRelativeCycle g e β) :
    ∃ β' : FamilyOfCycles (p ≫ g) e, IsRelativeCycle (p ≫ g) e β' ∧
      properPushforwardFamily (p ≫ g) g p rfl e β' = β := by
  obtain ⟨d, hd⟩ := exists_properPushforward_eq_of_isCompletelyDecomposed
    (fieldChowSituation ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))))
    (g.fiberToSpecResidueField (genericPoint (Spec (.of R))))
    ((p ≫ g).fiberToSpecResidueField (genericPoint (Spec (.of R))))
    (inducedFiberMap (p ≫ g) g p rfl (genericPoint (Spec (.of R))))
    (inducedFiberMap_fiberToSpecResidueField (p ≫ g) g p rfl (genericPoint (Spec (.of R))))
    (isCompletelyDecomposed_inducedFiberMap (p ≫ g) g p rfl hcd (genericPoint (Spec (.of R))))
    (e : ℤ) (β (genericPoint (Spec (.of R))))
  obtain ⟨b, hb⟩ := exists_cycleClassMap_apply_genericPoint_eq (p ≫ g) e d
  have hrel : IsRelativeCycle (p ≫ g) e (cycleClassMap (p ≫ g) e b) := by
    rw [← relativeCycleClassMap_val (p ≫ g) b]
    exact (relativeCycleClassMap (p ≫ g) b).2
  refine ⟨cycleClassMap (p ≫ g) e b, hrel, ?_⟩
  refine (IsRelativeCycle.eq_iff_eq_of_mem_genericPoints g e
    (isRelativeCycle_properPushforwardFamily (p ≫ g) g p rfl e hrel) hβ).mpr fun η hη ↦ ?_
  have hηgen : η = genericPoint (Spec (.of R)) := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hη
  subst hηgen
  rw [properPushforwardFamily_apply, hb]
  exact hd

end Stacks.Chow

end
