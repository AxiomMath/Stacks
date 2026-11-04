module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.HigherCodimension
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularPointBlowupTwistCohomology
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimensionOneCohomologyVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The higher direct images of a blowup at a closed point of a surface vanish above degree one

Let `X` be an integral Noetherian scheme with `topologicalKrullDim X = 2` and let `w ∈ X` be a
closed point with ideal sheaf `ℐ = ℐ_w`. For the blowing up `b : X' ⟶ X` of `X` in `ℐ` and any
quasi-coherent `ℱ` on `X'`,

`Rᵠ b_* ℱ = 0` for every `q ≥ 2`.

Nothing of the geometry of the blowup enters beyond the dimension of its fibres: the statement is
[Stacks, Tag 0E7H] clause (1) — Grothendieck's vanishing above the fibre dimension
([Stacks, Tag 02V7], at fibre dimension one) — and the only thing to supply is that every fibre
of `b` has dimension at most one.

In particular `R¹ b_* 𝒪_{X'}(kE) = 0` is *not* what is proved here. That is the boundary degree
`q = 1`, which does not follow from the fibre dimension and is
`AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_blowUpTwist_pointIdeal`, part (2) of
[Stacks, Tag 0AGS] relativized; the vanishing recorded below is its complement in the range
`q ≥ 2`, and together the two say that `Rb_*` of a twist is concentrated in degree zero.

## The fibre bound

`b` is a modification: it is proper over a Noetherian base, and birational because the ideal sheaf
of a reduced closed point of an integral scheme of dimension two is nonzero
(`Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot`); its source is integral
([Stacks, Tag 02ND]). The generic fibre of a birational morphism is a single point, so
[Stacks, Tag 0B2K] — `AlgebraicGeometry.topologicalKrullDimAt_fiber_add_one_le_of_genericPoints`,
applied at generic fibre dimension zero — bounds the dimension of the fibre at each of its points
by `dim 𝒪_{X,y} - 1 ≤ 1`, the local rings of `X` having dimension at most
`topologicalKrullDim X = 2`. A bound at every point of a space is a bound on the space.

## Main results

* `topologicalKrullDim_fiber_blowUpToBase_vanishingIdeal_singleton_le_one`: the fibre bound.
* `isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt`:
  **`Rᵠ b_* ℱ = 0` for `q ≥ 2` and `ℱ` quasi-coherent.**
* `isZero_rightDerivedPlus_pushforward_blowUpTwist_pointIdeal_of_one_lt` and
  `isZero_rightDerivedPlus_pushforward_exceptionalTwist_pointIdeal_of_one_lt`: the twisting
  sheaves `𝒪_{X'}(n)` and `𝒪_{X'}(E)`, the modules the induction of [Stacks, Tag 0B4T] meets.

## Implementation notes

*The fibre bound is proved over a global base.* A sequence of blowups at closed points has a
scheme at each stage, not the spectrum of a local ring, so the bound is proved for the point blowup
of an arbitrary integral Noetherian scheme of dimension two, directly from [Stacks, Tag 0B2K].

*No regularity.* The twisted statement of part (2) of [Stacks, Tag 0AGS] needs the local ring at
`w` to be regular of dimension two. The vanishing in degrees `q ≥ 2` does not: it needs only that
the fibres are at most curves, which the dimension of `X` alone gives. The hypotheses here are
therefore weaker than those of the `q = 1` statement it complements.

*The model of the derived category* is `CategoryTheory.HasDerivedCategory.standard`, the model at
which the `q = 1` statement and [Stacks, Tag 0E7H] are both written; the other derived-category
instances are erased in the section carrying the vanishing. The fibre bound is a statement about
topological spaces and needs no model.

## References

* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0B2K](https://stacks.math.columbia.edu/tag/0B2K)
* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.RelativeProj

universe u

namespace AlgebraicGeometry

/-! ### The fibres of a blowup at a closed point of a surface are at most curves -/

/-- **Every fibre of the blowing up of an integral Noetherian scheme of dimension two at a closed
point has dimension at most one.**

The blowing up `b : X' ⟶ X` is birational, the ideal sheaf of a reduced closed point of an
integral scheme of dimension two being nonzero, and `X'` is integral. So `X'` has a single
irreducible component, whose generic point lies over the generic point of `X` and has
zero-dimensional fibre
(`AlgebraicGeometry.topologicalKrullDimAt_fiber_genericPoint_eq_zero`); over a point `y` other
than the generic one [Stacks, Tag 0B2K] therefore gives
`dim_z(X'_y) + 1 ≤ dim 𝒪_{X,y} ≤ 2` at every `z` above `y`, and the dimension of a space is the
supremum of its local dimensions. Over the generic point the fibre is a single point. -/
@[sga "4½ Arcata 3.4.3" "n = 2 over a field"]
theorem topologicalKrullDim_fiber_blowUpToBase_vanishingIdeal_singleton_le_one
    {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X = 2) (w : X) (hw : IsClosed ({w} : Set X)) (y : X) :
    topologicalKrullDim ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds X))).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X) with hM
  have hne : M ≠ ⊥ := Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hdim w hw
  have : AlgebraicGeometry.IsIntegral (blowUp M) := isIntegral_blowUp M hne
  set g := blowUpToBase M with hg
  have hbir : IsBirational g := isBirational_blowUpToBase M hne
  have hstalk : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2 := fun x =>
    (ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim.le
  by_cases hygen : y = genericPoint X
  · subst hygen
    have : Subsingleton (g.fiber (genericPoint X)) := subsingleton_fiber_genericPoint g hbir
    exact (topologicalKrullDim_zero_of_discreteTopology _).trans (by simp)
  have hlocAt : ∀ z : blowUp M, g z = y →
      topologicalKrullDimAt (g.fiber (g z)) (g.asFiber z) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro z hz
    have hgeneric : ∀ Z ∈ irreducibleComponents (blowUp M), z ∈ Z →
        ∀ η : blowUp M, IsGenericPoint η Z →
        (g η ≠ g z ∧
          topologicalKrullDimAt (g.fiber (g η)) (g.asFiber η) = ((0 : ℕ) : WithBot ℕ∞)) := by
      intro Z hZ _ η hη
      have hZ' : Z = Set.univ := by
        rw [irreducibleComponents_eq_singleton] at hZ
        simpa using hZ
      have hη' : IsGenericPoint η Set.univ := by simpa [hZ'] using hη
      have hηeq : η = genericPoint (blowUp M) :=
        IsGenericPoint.eq hη' (genericPoint_spec (blowUp M))
      subst hηeq
      refine ⟨?_, by simpa using topologicalKrullDimAt_fiber_genericPoint_eq_zero g hbir⟩
      rw [IsBirational.genericPoint_eq g hbir, hz]
      exact Ne.symm hygen
    have hbound := topologicalKrullDimAt_fiber_add_one_le_of_genericPoints g z 0 hgeneric
    have hlt : topologicalKrullDimAt (g.fiber (g z)) (g.asFiber z) < ((2 : ℕ) : WithBot ℕ∞) :=
      ENat.WithBot.add_one_le_natCast_iff.mp (hbound.trans (by simpa using hstalk (g z)))
    exact ENat.WithBot.lt_add_one_iff.mp (by exact_mod_cast hlt)
  have hlocal : ∀ t : g.fiber y,
      topologicalKrullDimAt (g.fiber y) t ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro t
    have hy : g (g.fiberι y t) = y := by
      have ht := (g.fiberHomeo y t).2
      exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp ht)
    have hpoint : fiberHomeomorphOfEq g hy (g.asFiber (g.fiberι y t)) = t := by
      refine (g.fiberι y).isEmbedding.injective ?_
      rw [fiberι_fiberHomeomorphOfEq]
      simp [Scheme.Hom.fiberι_asFiber]
    rw [← hpoint, ← topologicalKrullDimAt_eq_of_homeomorph (fiberHomeomorphOfEq g hy)]
    exact hlocAt (g.fiberι y t) hy
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  exact iSup_le fun t => by
    simpa only [topologicalKrullDimAt_eq_localKrullDim] using hlocal t

/-! ### The vanishing above degree one -/

section Vanishing

attribute [local instance] HasDerivedCategory.standard

/-- **`Rᵠ b_* ℱ = 0` for `q ≥ 2`** for the blowing up `b : X' ⟶ X` of an integral Noetherian
scheme of dimension two at a closed point and `ℱ` a quasi-coherent `𝒪_{X'}`-module.

This is [Stacks, Tag 0E7H] clause (1) — the vanishing of the higher direct images of a proper
morphism above the dimension of its fibres, at fibre dimension one — applied to `b`, whose fibres
are bounded by
`AlgebraicGeometry.topologicalKrullDim_fiber_blowUpToBase_vanishingIdeal_singleton_le_one`. The
blowup of a locally Noetherian scheme is proper. -/
@[sga "6 VII 3.5" "Clause (i)"]
theorem isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt
    {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X = 2) (w : X) (hw : IsClosed ({w} : Set X))
    (F : (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X))).Modules)
    [F.IsQuasicoherent] (q : ℤ) (hq : 1 < q) :
    IsZero (((Scheme.Modules.pushforward (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds X)))).rightDerivedPlus q).obj F) :=
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_higherDirectImage_of_one_lt_of_isProper
    _ (topologicalKrullDim_fiber_blowUpToBase_vanishingIdeal_singleton_le_one hdim w hw) F q hq

/-- **`Rᵠ b_* 𝒪_{X'}(n) = 0` for `q ≥ 2`** for the blowing up `b : X' ⟶ X` of an integral
Noetherian scheme of dimension two at a closed point, and every `n`.

This is
`AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt`
at the `n`-th twisting sheaf of the blowup, which is quasi-coherent, being a twisting sheaf of a
relative `Proj`. Unlike the degree-one statement
`AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_blowUpTwist_pointIdeal`, this needs no
regularity of the local ring at the centre and holds for every `n`, not only for `n ≥ -1`. -/
@[sga "6 VII 3.5" "Clause (i)"]
theorem isZero_rightDerivedPlus_pushforward_blowUpTwist_pointIdeal_of_one_lt
    {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X = 2) (w : X) (hw : IsClosed ({w} : Set X)) (n : ℤ) (q : ℤ)
    (hq : 1 < q) :
    IsZero (((Scheme.Modules.pushforward (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : Closeds X)))).rightDerivedPlus q).obj
      (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) n)) :=
  have : (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds X)) n).IsQuasicoherent :=
    inferInstanceAs ((Situation.twistSheaf (reesSituation
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X))) n).IsQuasicoherent)
  isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt hdim w hw _ q hq

/-- **`Rᵠ b_* 𝒪_{X'}(E) = 0` for `q ≥ 2`**, with `E` the exceptional divisor of the blowing up of
an integral Noetherian scheme of dimension two at a closed point.

`𝒪_{X'}(E)` is the twist by `-1`, the ideal sheaf of `E` being `𝒪_{X'}(1)` — part (3) of
[Stacks, Tag 02OS], `AlgebraicGeometry.twistOneIsoExceptionalIdealModule` — so this is the case
`n = -1` of
`AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_blowUpTwist_pointIdeal_of_one_lt`. Together
with `AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_exceptionalTwist_pointIdeal` it
says that `Rb_*𝒪_{X'}(E)` is concentrated in degree zero. -/
theorem isZero_rightDerivedPlus_pushforward_exceptionalTwist_pointIdeal_of_one_lt
    {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X = 2) (w : X) (hw : IsClosed ({w} : Set X)) (q : ℤ) (hq : 1 < q) :
    IsZero (((Scheme.Modules.pushforward (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : Closeds X)))).rightDerivedPlus q).obj
      (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) (-1))) :=
  isZero_rightDerivedPlus_pushforward_blowUpTwist_pointIdeal_of_one_lt hdim w hw (-1) q hq

end Vanishing

end AlgebraicGeometry

end
