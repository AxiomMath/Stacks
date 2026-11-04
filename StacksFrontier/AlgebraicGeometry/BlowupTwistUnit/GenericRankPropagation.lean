module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionBirational
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSliceSite
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleNaturalIso
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMapsUnconditional

/-!
# The generic rank of the relative differentials along a sequence of blowups in closed points

Let `b : W' ⟶ W` be a morphism of schemes over `S₀` which is an isomorphism over an open `V₀` of
`W`. If `Ω_{W/S₀}` is finite locally free of rank `r` over an open `V`, then `Ω_{W'/S₀}` is
finite locally free of rank `r` over `b ⁻¹ᵁ (V₀ ⊓ V)`. Applied to the blowing up of a reduced
closed point, this shows: if `S` is an integral regular surface over `S₀` with `Ω_{S/S₀}` finite
locally free of rank `r`, then for every sequence of blowups in closed points `W ⟶ S` the module
`Ω_{W/S₀}` is finite locally free of rank `r` over a nonempty open of `W`. This is the
generic-rank hypothesis of [Stacks, Tag 0B3T] at every stage of the sequence of blowups of
[Stacks, Tag 0B4T].

## Main definitions

* `Stacks.BlowupTwistUnit.restrictIsoFreeRelativeDifferentialsComp`: a trivialisation of
  `Ω_{W/S₀}` on an open over which `b` is an isomorphism is a trivialisation of `Ω_{W'/S₀}` on
  its preimage.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `isFiniteLocallyFreeOfRank_over_relativeDifferentials_comp`: the generic rank of the relative
  differentials crosses a morphism which is an isomorphism over every sub-open of an open `V₀`,
  from rank `r` over `V` downstairs to rank `r` over `b ⁻¹ᵁ (V₀ ⊓ V)` upstairs.
* `isFiniteLocallyFreeOfRank_over_relativeDifferentials_pointBlowup`: the same at the blowing up
  of a reduced closed point, with `V₀` the complement of the point.
* `exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup`: at the blowing up of a reduced closed
  point, `Ω_{W'/S₀}` and `b^*Ω_{W/S₀}` are finite locally free of rank `r` on one nonempty open
  of the blowup.
* `exists_open_isFiniteLocallyFreeOfRank_over_relativeDifferentials_of_pointBlowupChain`: at
  every stage `W` of a sequence of blowups in closed points, `Ω_{W/S₀}` is finite locally free of
  rank `r` over a nonempty open of `W`.
* `exists_mem_inf_compl_singleton` and `exists_ne_of_topologicalKrullDim_eq_two`: a nonempty open
  of an integral scheme with a second point meets the complement of a closed point, and a scheme
  of topological Krull dimension two has a second point.

## Implementation notes

`Ω_{W'/S₀}` need not be finite locally free along a chain of blowups, so the rank is asserted
over a nonempty open. For `A = 𝔽_p[x, y]_{(x,y)}` and `A₀ = 𝔽_p[y]` the module `Ω_{A/A₀} = A·dx`
is free of rank one, while on the chart `A[y/x] = A[t]/(xt - y)` of the blowup of the closed
point one has `Ω_{W'/A₀} = (B·dx ⊕ B·dt)/(t·dx + x·dt) ≅ (x, t)B`, which needs two generators at
the origin of the chart.

The hypothesis `hiso` of `isFiniteLocallyFreeOfRank_over_relativeDifferentials_comp` asks for `b`
to be an isomorphism over every sub-open of `V₀`: the trivialisation of `Ω_{W/S₀}` lives on an
open other than `V₀`, and for a blowup
`AlgebraicGeometry.isIso_blowUpToBase_restrict_of_subset_compl_support` gives every sub-open of
the complement of the centre directly.

`exists_ne_of_topologicalKrullDim_eq_two` reads the dimension of the space rather than of a
stalk, because a chain of blowups propagates the dimension of the space
(`Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface`).

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.BlowupTwistUnit

variable {W' W S₀ : Scheme.{u}}

/-! ### A trivialisation of the differentials crosses an isomorphism over an open -/

/-- **A trivialisation of `Ω_{W/S₀}` on an open `V` over which `b : W' ⟶ W` is an isomorphism is
a trivialisation of `Ω_{W'/S₀}` on `b ⁻¹ᵁ V`**, on the same index type. -/
def restrictIsoFreeRelativeDifferentialsComp (b : W' ⟶ W) (g : W ⟶ S₀) (V : W.Opens)
    [IsIso (b ∣_ V)] (I : Type u)
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Hom.relativeDifferentials g) ≅
      SheafOfModules.free.{u} I) :
    (Scheme.Modules.restrictFunctor (b ⁻¹ᵁ V).ι).obj
        (Scheme.Hom.relativeDifferentials (b ≫ g)) ≅ SheafOfModules.free.{u} I :=
  have hq : (b ∣_ V) ≫ (V.ι ≫ g) = (b ⁻¹ᵁ V).ι ≫ (b ≫ g) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  (Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ V).ι).app _ ≪≫
    Scheme.Hom.etaleRelativeDifferentialsIso (b ⁻¹ᵁ V).ι (b ≫ g) _ rfl ≪≫
    (Scheme.Hom.etaleRelativeDifferentialsIso (b ∣_ V) (V.ι ≫ g) _ hq).symm ≪≫
    (Scheme.Modules.pullback (b ∣_ V)).mapIso
      ((Scheme.Hom.etaleRelativeDifferentialsIso V.ι g _ rfl).symm ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app _ ≪≫ e) ≪≫
    Scheme.Modules.pullbackFreeIso (b ∣_ V) I

/-- **The generic rank of the relative differentials crosses a morphism which is an isomorphism
over an open.** If `Ω_{W/S₀}` is finite locally free of rank `r` over `V` and `b : W' ⟶ W` is an
isomorphism over every sub-open of `V₀`, then `Ω_{W'/S₀}` is finite locally free of rank `r` over
`b ⁻¹ᵁ (V₀ ⊓ V)`. -/
theorem isFiniteLocallyFreeOfRank_over_relativeDifferentials_comp (b : W' ⟶ W) (g : W ⟶ S₀)
    (r : ℕ) (V₀ V : W.Opens) (hiso : ∀ V' : W.Opens, V' ≤ V₀ → IsIso (b ∣_ V'))
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials g).over V) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (b ≫ g)).over (b ⁻¹ᵁ (V₀ ⊓ V))) r := by
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_over_of_forall_restrictIso _ _ r fun t ht => ?_
  obtain ⟨W₁, hW₁, I, hI, ⟨e⟩⟩ :=
    Scheme.Modules.exists_restrictIso_of_isFiniteLocallyFreeOfRank_over
      (Scheme.Hom.relativeDifferentials g) V r (x := b.base t) ht.2
  have := hiso (W₁ ⊓ V₀) inf_le_right
  exact ⟨b ⁻¹ᵁ (W₁ ⊓ V₀), ⟨hW₁, ht.1⟩, I, hI,
    ⟨restrictIsoFreeRelativeDifferentialsComp b g (W₁ ⊓ V₀) I
      (Scheme.Modules.restrictFreeOfLE inf_le_left _ I e)⟩⟩

/-! ### Counting points -/

/-- **A nonempty open of an integral scheme meets the complement of a closed point**, provided
the scheme has a second point. -/
theorem exists_mem_inf_compl_singleton [AlgebraicGeometry.IsIntegral W] (w : W)
    (hw : IsClosed ({w} : Set W)) (V : W.Opens) (hV : ∃ x : W, x ∈ V) (hne : ∃ x : W, x ≠ w) :
    ∃ x : W, x ∈ (⟨({w} : Set W)ᶜ, hw.isOpen_compl⟩ : W.Opens) ⊓ V := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨x₁, hx₁⟩ := hV
  obtain ⟨y, -, hy⟩ := (IrreducibleSpace.isIrreducible_univ ↥W).2
    (({w} : Set W)ᶜ) (V : Set W) hw.isOpen_compl V.isOpen ⟨x₀, trivial, hx₀⟩ ⟨x₁, trivial, hx₁⟩
  exact ⟨y, hy⟩

/-- **A scheme of topological Krull dimension two has at least two points.** -/
theorem exists_ne_of_topologicalKrullDim_eq_two (w : W) (hdim : topologicalKrullDim W = 2) :
    ∃ x : W, x ≠ w := by
  by_contra hno
  have hsub : Subsingleton W :=
    ⟨fun a b => by
      have ha : a = w := by by_contra hne; exact hno ⟨a, hne⟩
      have hb : b = w := by by_contra hne; exact hno ⟨b, hne⟩
      exact ha.trans hb.symm⟩
  have h0 : topologicalKrullDim W ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  rw [hdim] at h0
  exact absurd h0 (by decide)

/-! ### At the blowing up of a reduced closed point -/

/-- The blowing up of a reduced closed point `w` is an isomorphism over every open inside `{w}ᶜ`. -/
private theorem isIso_blowUpToBase_restrict_of_le_compl_singleton (w : W)
    (hw : IsClosed ({w} : Set W)) :
    ∀ V' : W.Opens, V' ≤ (⟨({w} : Set W)ᶜ, hw.isOpen_compl⟩ : W.Opens) →
      IsIso (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ∣_ V') := fun V' hV' =>
  AlgebraicGeometry.isIso_blowUpToBase_restrict_of_subset_compl_support _ V' (by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hV')

/-- **The generic rank of the relative differentials crosses the blowing up of a reduced closed
point.** For `b` the blowing up of `W` in a reduced closed point `w`, if `Ω_{W/S₀}` is finite
locally free of rank `r` over `V`, then `Ω_{W'/S₀}` is finite locally free of rank `r` over
`b ⁻¹ᵁ ({w}ᶜ ⊓ V)`. -/
theorem isFiniteLocallyFreeOfRank_over_relativeDifferentials_pointBlowup
    {S : Scheme.{u}} (p : S ⟶ S₀) (g : W ⟶ S) (r : ℕ) (w : W) (hw : IsClosed ({w} : Set W))
    (V : W.Opens)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (g ≫ p)).over V) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
          (AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ (g ≫ p))).over
        (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ⁻¹ᵁ
          ((⟨({w} : Set W)ᶜ, hw.isOpen_compl⟩ : W.Opens) ⊓ V))) r :=
  isFiniteLocallyFreeOfRank_over_relativeDifferentials_comp _ (g ≫ p) r _ V
    (isIso_blowUpToBase_restrict_of_le_compl_singleton w hw)

/-- **`Ω_{W'/S₀}` and `b^*Ω_{W/S₀}` are finite locally free of rank `r` on one nonempty open of the
blowup.** At the blowing up `b` of a reduced closed point `w` of an integral scheme `W` over
`S ⟶ S₀`, if `Ω_{W/S₀}` is finite locally free of rank `r` over a nonempty open `V` then there is
a nonempty open `U` of the blowup over which both `Ω_{W'/S₀}` and `b^*Ω_{W/S₀}` are finite
locally free of rank `r`. -/
theorem exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup {S : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] (p : S ⟶ S₀) (g : W ⟶ S) (r : ℕ) (w : W)
    (hw : IsClosed ({w} : Set W)) (hne : ∃ x : W, x ≠ w) (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (g ≫ p)).over V) r] :
    ∃ U : (AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Opens,
      (∃ x, x ∈ U) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Hom.relativeDifferentials (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ≫ (g ≫ p))).over U) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj
          (Scheme.Hom.relativeDifferentials (g ≫ p))).over U) r := by
  set b := AlgebraicGeometry.blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))
  set V₀ : W.Opens := ⟨({w} : Set W)ᶜ, hw.isOpen_compl⟩
  have hiso := isIso_blowUpToBase_restrict_of_le_compl_singleton w hw
  obtain ⟨x, hx⟩ := exists_mem_inf_compl_singleton w hw V hV hne
  have := hiso (V₀ ⊓ V) inf_le_left
  have hup := isFiniteLocallyFreeOfRank_over_relativeDifferentials_pointBlowup p g r w hw V
  have hpb := Scheme.Modules.isFiniteLocallyFreeOfRank_over_pullback
    (Scheme.Hom.relativeDifferentials (g ≫ p)) b V r
  have hle : b ⁻¹ᵁ (V₀ ⊓ V) ≤ b ⁻¹ᵁ V := by intro t ht; exact ht.2
  refine ⟨b ⁻¹ᵁ (V₀ ⊓ V),
    ⟨((asIso (b ∣_ (V₀ ⊓ V))).inv.base ⟨x, hx⟩).1,
      ((asIso (b ∣_ (V₀ ⊓ V))).inv.base ⟨x, hx⟩).2⟩,
    hup, ?_⟩
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_over_of_le _ hle r

/-! ### Along the whole chain -/

open Stacks.ResolutionOfSurfaces in
/-- **The relative differentials have generic rank `r` at every stage of a sequence of blowups
in closed points.** Let `S` be an integral Noetherian scheme regular of dimension two over
`p : S ⟶ S₀` whose relative differentials are finite locally free of rank `r` — the hypothesis of
[Stacks, Tag 0B4T], where `S = Spec(A)`, `S₀ = Spec(A₀)` and `Ω_{A/A₀}` is free of rank `r`. Then
for every `g : W ⟶ S` obtained from `S` by a sequence of blowups in closed points, `Ω_{W/S₀}` is
finite locally free of rank `r` over a nonempty open of `W`. -/
theorem exists_open_isFiniteLocallyFreeOfRank_over_relativeDifferentials_of_pointBlowupChain
    {S : Scheme.{u}} (p : S ⟶ S₀) (r : ℕ) {T : Set S}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r]
    (hS : Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface S)
    {W : Scheme.{u}} {g : W ⟶ S}
    (hc : Stacks.ResolutionOfSurfaces.PointBlowupChain S T W g) :
    ∃ V : W.Opens, (∃ x : W, x ∈ V) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Hom.relativeDifferentials (g ≫ p)).over V) r := by
  induction hc with
  | refl =>
    have := hS.isIntegral
    obtain ⟨x⟩ : Nonempty S := inferInstance
    refine ⟨⊤, ⟨x, trivial⟩, ?_⟩
    simp only [Category.id_comp]
    exact Scheme.Modules.isFiniteLocallyFreeOfRank_over _ ⊤ r
  | @step W₀ g₀ hh w hw hwT ih =>
    obtain ⟨V, hV, inst⟩ := ih
    have := inst
    have hWs :=
      (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hh hS).1
    have := hWs.isIntegral
    obtain ⟨U, hU, hup, -⟩ := exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup p g₀ r w hw
      (exists_ne_of_topologicalKrullDim_eq_two w hWs.topologicalKrullDim_eq) V hV
    refine ⟨U, hU, ?_⟩
    simpa only [Category.assoc] using hup

end Stacks.BlowupTwistUnit

end
