module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeRelative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingInjective
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GroupStructure
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.VanishingGeneralization

/-!
# The valuative condition for the family of zero-cycles attached to a weighting

Let `f : X ⟶ S` be locally quasi-finite with `S` locally Noetherian and `X` quasi-compact, let
`w` be a weighting of `f` and let `α` be a family of `0`-cycles on the fibres of `X/S` with
`w_α = n·w`. Then `α` is a relative `0`-cycle.

This is the last two paragraphs of the proof of Stacks Tag 0H5P. Over the spectrum of a discrete
valuation ring the base change `α'` of `α` again satisfies `w_{α'} = n·(w ∘ g')`, and `w ∘ g'` is
again a weighting; the relative `0`-cycle `β` whose generic member is that of `α'` exists by
Tag 0H5A, and `w_β - n·(w ∘ g')` is a weighting vanishing at every point over the generic point,
hence identically zero. So `w_β = w_{α'}`, so `β = α'` because `w_·` is injective, and the
valuative identity for `α'` is the one for `β`, which holds because `β` is a combination of cycle
classes of members of `Hilb`.

## Main results

* `Stacks.Chow.isRelativeCycle_of_relativeCycleWeight_eq_nsmul` — the statement just made, with
  the two inputs it needs from elsewhere in the proof of Tag 0H5P taken as hypotheses: the base-change
  compatibility of `w_·` and the weighting property of `w_γ` over a discrete valuation ring.

## Implementation notes

The two hypotheses `hbc` and `hdvr` are exactly the preliminary lemma of the source
(`w_{g^*α} = w_α ∘ g'`, untagged upstream) and the first clause of the lemma over a discrete
valuation ring. They are stated only at the base changes of `f` along morphisms from spectra of
discrete valuation rings, which is all this argument uses. Both are discharged where this result
is consumed; nothing here is conditional in the finished development.

Quasi-compactness of `f` is not assumed: it follows from `CompactSpace X` and the
quasi-separatedness of a locally Noetherian scheme, and is what makes `X ×_S Spec R` quasi-compact
so that Tag 0H5A applies to it.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 0H5A](https://stacks.math.columbia.edu/tag/0H5A)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Two families of `0`-cycles whose members over a point agree have the same weighting at every
point of the source above that point. -/
theorem relativeCycleWeight_eq_of_apply_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {α β : FamilyOfCycles f 0} {s : S} (hs : α s = β s) (x : X)
    (hx : f x = s) : relativeCycleWeight f α x = relativeCycleWeight f β x := by
  have h : α (f x) = β (f x) := by rw [hx]; exact hs
  rw [relativeCycleWeight_apply, relativeCycleWeight_apply, h]

/-- **Stacks Project, Tag 0H5P**, the last two paragraphs of the proof: a family of `0`-cycles
whose weighting is an integer multiple of a weighting is a relative `0`-cycle. -/
theorem isRelativeCycle_of_relativeCycleWeight_eq_nsmul {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian S] [CompactSpace X]
    (w : X → ℤ) (hw : IsWeighting f w) (n : ℕ) (α : FamilyOfCycles f 0)
    (hα : ∀ x : X, relativeCycleWeight f α x = (n : ℤ) * w x)
    (hbc : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S),
      relativeCycleWeight (pullback.snd f c) (baseChangeFamily f c 0 α) =
        relativeCycleWeight f α ∘ pullback.fst f c)
    (hdvr : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S) (γ : FamilyOfCycles (pullback.snd f c) 0),
      IsRelativeCycle (pullback.snd f c) 0 γ →
      IsWeighting (pullback.snd f c) (relativeCycleWeight (pullback.snd f c) γ)) :
    IsRelativeCycle f 0 α := by
  intro R _ _ _ c
  have : CompactSpace ↥(pullback f c) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f c)
  set f' := pullback.snd f c with hf'
  set p := pullback.fst f c with hp
  set α' := baseChangeFamily f c 0 α with hα'def
  -- `w ∘ p` is a weighting of the base change, and `w_{α'} = n · (w ∘ p)`.
  have hw' : IsWeighting f' (w ∘ p) := hw.comp_of_isPullback (IsPullback.of_hasPullback f c)
  have hα' : ∀ z : ↥(pullback f c), relativeCycleWeight f' α' z = (n : ℤ) * (w ∘ p) z := by
    intro z
    rw [hα'def, congrFun (hbc R c) z]
    exact hα (p z)
  -- The relative `0`-cycle with the same generic member, by Tag 0H5A.
  obtain ⟨b, hb⟩ := exists_cycleClassMap_apply_genericPoint_eq f' 0
    (α' (genericPoint (Spec (.of R))))
  set β := cycleClassMap f' 0 b with hβdef
  have hβrel : IsRelativeCycle f' 0 β := by
    have h1 := (relativeCycleClassMap (r := 0) f' b).2
    rw [mem_relativeCycles] at h1
    rwa [relativeCycleClassMap_val f' b] at h1
  -- `w_β - n · (w ∘ p)` is a weighting vanishing above the generic point, hence zero.
  have hpt : ∀ z : ↥(pullback f c),
      (relativeCycleWeight f' β - fun z ↦ (n : ℤ) * (w ∘ p) z) z = 0 := by
    have hdiff : relativeCycleWeight f' β - (fun z ↦ (n : ℤ) * (w ∘ p) z) = 0 := by
      refine IsWeighting.eq_zero_of_eq_zero_over_genericPoint
        (IsWeighting.sub (hdvr R c β hβrel) (IsWeighting.const_mul (n : ℤ) hw')) ?_
      intro z hz
      show relativeCycleWeight f' β z - (n : ℤ) * (w ∘ p) z = 0
      rw [relativeCycleWeight_eq_of_apply_eq f' hb z hz, hα' z, sub_self]
    exact fun z ↦ congrFun hdiff z
  -- Hence `β = α'`.
  have hβα : β = α' :=
    relativeCycleWeight_injective f' (funext fun z ↦ by
      rw [hα' z]
      exact sub_eq_zero.mp (hpt z))
  rw [← hβα]
  exact specializationCycle_cycleClassMap f' b

end Stacks.Chow

end
