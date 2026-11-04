module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Relative dimension is fpqc local on the base

For a fixed natural number `d`, being locally of finite type of relative dimension `d` is local
on the target for the fpqc topology.

## Main definitions

* `AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension` is the morphism property of being
  locally of finite type and of relative dimension `d`.

## Main results

* `AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension_isLocalAtTarget_fpqc`: being locally of
  finite type of relative dimension `d` is fpqc local on the base.

## Implementation notes

`AlgebraicGeometry.RelativeDimension` takes a local finite-type instance as an argument, so the
morphism property has to bundle that witness; this is what
`locallyOfFiniteTypeRelativeDimension` does.

Relative dimension `d` is a condition on whole fibres — each nonempty fibre is equidimensional of
dimension `d` — and both halves of the proof need the equivalent *pointwise* condition that the
local dimension of every fibre equals `d` at every point of it. For a fibre over a field the two
agree: the local dimension at a point is the largest dimension of an irreducible component
through that point (`AlgebraicGeometry.topologicalKrullDimAt_eq_iSup_irreducibleComponents`), so
a constant local dimension forces the components to have equal dimension and conversely.
In pointwise form the condition transports across any cartesian square, because the local
dimension of a fibre does
(`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback`), which gives both Zariski
locality on the target and the fpqc descent step at once.

## References

* [Stacks Project, Tag 02VJ](https://stacks.math.columbia.edu/tag/02VJ)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty TopologicalSpace

namespace AlgebraicGeometry

universe u

/-! ### The pointwise form of relative dimension -/

/-- Over a field, a scheme locally of finite type whose local dimension is constant is
equidimensional. -/
private theorem equidimensional_of_topologicalKrullDimAt_const
    (k : Type u) [Field k] (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] (z : WithBot ℕ∞) (hd : ∀ y : Y, topologicalKrullDimAt Y y = z) :
    Equidimensional Y := by
  have hcomponent : ∀ V ∈ irreducibleComponents Y, topologicalKrullDim V = z := by
    intro V hV
    have hηV : IsGenericPoint hV.1.genericPoint V :=
      hV.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents V hV)
    have honly : ∀ U ∈ irreducibleComponents Y, hV.1.genericPoint ∈ U → U = V := by
      intro U hU hηU
      have hVU : V ⊆ U := by
        rw [← hηV]
        exact closure_minimal (Set.singleton_subset_iff.mpr hηU)
          (isClosed_of_mem_irreducibleComponents U hU)
      exact (hV.2 hU.1 hVU).antisymm hVU
    have hlocal : topologicalKrullDimAt Y hV.1.genericPoint = topologicalKrullDim V := by
      rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y q hV.1.genericPoint]
      refine le_antisymm (iSup_le fun U ↦ iSup_le fun hU ↦ by rw [honly U hU.1 hU.2]) ?_
      exact le_iSup_of_le V (le_iSup_of_le ⟨hV, hηV.mem⟩ le_rfl)
    exact hlocal.symm.trans (hd _)
  exact fun Z hZ W hW ↦ (hcomponent Z hZ).trans (hcomponent W hW).symm

/-- The point of the fibre of `f` through `y` determined by `y` is `x` as soon as `y` is the
image of `x`. -/
public theorem asFiber_eq_of_fiberι_eq {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (x : f.fiber s)
    (y : X) (hy : f y = s) (h : y = f.fiberι s x) : hy ▸ f.asFiber y = x := by
  apply (f.fiberι s).isEmbedding.injective
  cases hy
  simpa using h

/-- Reading the local dimension of a fibre at a point of it as a local dimension at the
corresponding point of the source. -/
private theorem topologicalKrullDimAt_fiber_eq_at_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (x : f.fiber s) (z : X) (hz : z = f.fiberι s x) :
    topologicalKrullDimAt (f.fiber s) x =
      topologicalKrullDimAt (f.fiber (f z)) (f.asFiber z) := by
  have hq : f z = s := by rw [hz]; exact f.apply_fiberι s x
  have hcast : hq ▸ f.asFiber z = x := asFiber_eq_of_fiberι_eq f s x z hq hz
  cases hq
  simpa using congrArg (topologicalKrullDimAt (f.fiber (f z))) hcast.symm

/-- A morphism of relative dimension `d` has local fibre dimension `d` at every point of every
fibre. -/
private theorem topologicalKrullDimAt_fiber_eq_of_relativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ} (h : RelativeDimension f d) (s : S)
    (x : f.fiber s) : topologicalKrullDimAt (f.fiber s) x = (d : WithBot ℕ∞) :=
  have _ := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s
  (topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional (S.residueField s)
    (f.fiber s) (f.fiberToSpecResidueField s) (h s ⟨x⟩).1 x).trans (h s ⟨x⟩).2

/-- Conversely, constant local fibre dimension `d` gives relative dimension `d`. -/
private theorem relativeDimension_of_topologicalKrullDimAt_fiber_eq {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (d : ℕ)
    (h : ∀ s : S, ∀ x : f.fiber s,
      topologicalKrullDimAt (f.fiber s) x = (d : WithBot ℕ∞)) :
    RelativeDimension f d := by
  intro s hs
  have _ := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s
  have _ : Nonempty (f.fiber s) := hs
  refine ⟨equidimensional_of_topologicalKrullDimAt_const (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) d (h s), ?_⟩
  have hlocal : ∀ x : f.fiber s, localKrullDim (f.fiber s) x = (d : WithBot ℕ∞) := fun x ↦ by
    simpa only [← topologicalKrullDimAt_eq_localKrullDim] using h s x
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  simp [hlocal]

/-! ### Fpqc locality -/

/-- The property that a morphism of schemes is locally of finite type and has relative
dimension `d`. -/
def locallyOfFiniteTypeRelativeDimension (d : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ ∃ h : LocallyOfFiniteType f, @RelativeDimension _ _ f h d

/-- Being locally of finite type of relative dimension `d` is stable under base change. -/
instance locallyOfFiniteTypeRelativeDimension_isStableUnderBaseChange (d : ℕ) :
    (locallyOfFiniteTypeRelativeDimension.{u} d).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ _ g _ g'} sq hg := by
    obtain ⟨hft, hdim⟩ := hg
    have _ : LocallyOfFiniteType g := hft
    have hft' : LocallyOfFiniteType g' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sq (P := @LocallyOfFiniteType) hft
    have _ : LocallyOfFiniteType g' := hft'
    refine ⟨hft', relativeDimension_of_topologicalKrullDimAt_fiber_eq g' d fun s x ↦ ?_⟩
    rw [topologicalKrullDimAt_fiber_eq_at_fiberι g' s x (g'.fiberι s x) rfl,
      topologicalKrullDimAt_fiber_eq_of_isPullback sq]
    exact topologicalKrullDimAt_fiber_eq_of_relativeDimension g hdim _ _

/-- Being locally of finite type of relative dimension `d` is Zariski local on the target. -/
private theorem locallyOfFiniteTypeRelativeDimension_isZariskiLocalAtTarget (d : ℕ) :
    IsZariskiLocalAtTarget (locallyOfFiniteTypeRelativeDimension.{u} d) := by
  apply IsZariskiLocalAtTarget.mk'
  · intro X S f U hf
    exact MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      (P := locallyOfFiniteTypeRelativeDimension.{u} d) hf
  · intro X S f ι U hU hlocal
    have hft : LocallyOfFiniteType f := by
      have : MorphismProperty.IsLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
          Scheme.zariskiPrecoverage :=
        MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage
      exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFiniteType) U hU
        fun i ↦ (hlocal i).choose
    refine ⟨hft, relativeDimension_of_topologicalKrullDimAt_fiber_eq f d fun s x ↦ ?_⟩
    obtain ⟨i, hsi⟩ := TopologicalSpace.Opens.mem_iSup.mp (show s ∈ (⨆ i, U i : S.Opens) by
      rw [hU]; trivial)
    have _ : LocallyOfFiniteType (f ∣_ U i) := (hlocal i).choose
    have hξ : f (f.fiberι s x) ∈ U i := by simpa only [f.apply_fiberι s x] using hsi
    let ξ : (f ⁻¹ᵁ U i).toScheme := ⟨f.fiberι s x, hξ⟩
    rw [topologicalKrullDimAt_fiber_eq_at_fiberι f s x ((f ⁻¹ᵁ U i).ι ξ) rfl,
      ← topologicalKrullDimAt_fiber_eq_of_isPullback
        (isPullback_morphismRestrict f (U i)).flip ξ]
    exact topologicalKrullDimAt_fiber_eq_of_relativeDimension (f ∣_ U i) (hlocal i).choose_spec _ _

/-- Being locally of finite type of relative dimension `d` descends along surjective flat
quasi-compact morphisms. -/
instance locallyOfFiniteTypeRelativeDimension_descendsAlong (d : ℕ) :
    MorphismProperty.DescendsAlong (locallyOfFiniteTypeRelativeDimension.{u} d)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {_ _ _ _ fst snd g f} sq hg hfst := by
    obtain ⟨hft', hdim'⟩ := hfst
    obtain ⟨⟨hsurj, hflat⟩, hqc⟩ := id hg
    have _ : Surjective g := hsurj
    have _ : Flat g := hflat
    have _ : QuasiCompact g := hqc
    have _ : LocallyOfFiniteType fst := hft'
    have hsnd : Surjective snd :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sq (P := @Surjective) hsurj
    have hft : LocallyOfFiniteType f :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType)
        (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})) sq hg hft'
    have _ : LocallyOfFiniteType f := hft
    refine ⟨hft, relativeDimension_of_topologicalKrullDimAt_fiber_eq f d fun s x ↦ ?_⟩
    obtain ⟨z, hz⟩ := hsnd.surj (f.fiberι s x)
    rw [topologicalKrullDimAt_fiber_eq_at_fiberι f s x (snd z) hz,
      ← topologicalKrullDimAt_fiber_eq_of_isPullback sq.flip z]
    exact topologicalKrullDimAt_fiber_eq_of_relativeDimension fst hdim' _ _

/-- **Stacks Project, Tag 02VJ.** Being locally of finite type of relative dimension `d` is fpqc
local on the base. -/
@[stacks 02VJ]
instance locallyOfFiniteTypeRelativeDimension_isLocalAtTarget_fpqc (d : ℕ) :
    (locallyOfFiniteTypeRelativeDimension.{u} d).IsLocalAtTarget Scheme.fpqcPrecoverage :=
  have := locallyOfFiniteTypeRelativeDimension_isZariskiLocalAtTarget.{u} d
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (locallyOfFiniteTypeRelativeDimension.{u} d)
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end AlgebraicGeometry

end
