module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.RingEquiv

/-!
# The graded pieces of 0ESU's increasing filtration are finite locally free on the divisors

Stacks tag 0ESU asserts that the graded piece `Fⁱ/Fⁱ⁻¹` of the increasing filtration of `ℱ` is
finite locally free *of rank `i`* on the effective Cartier divisor `D_i`. In the indexing of
`StacksFrontier.AlgebraicGeometry.DivisorSum.FittingDivisors`, where `D j` is the source's
`D_{j+1}`,
that is the assertion about the graded piece of `AlgebraicGeometry.fittingIncr` between degrees
`i` and `i + 1`: it is finite locally free of rank `i + 1` on `D i`.

`AlgebraicGeometry.essImage_pushforward_submoduleGraded_fittingIncr` already produces a sheaf of
modules on the divisor whose direct image is the graded piece. This file computes its rank, which
is the last clause of the increasing half of the source's conclusion.

The chart hypothesis is the per-point one that
`AlgebraicGeometry.exists_isAdmissibleBlowup_divisors_filtrations` produces: the ideal of an
effective Cartier divisor is principal near every point but need not be principal on a given
affine open. That is all the rank computation needs, since the rank is read off a cover of the
divisor by affine opens and the point whose neighbourhood is wanted is the image of a point of
the divisor.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_submoduleGraded_fittingIncr`: the graded
  piece of 0ESU's increasing filtration between degrees `i` and `i + 1` is the direct image of a
  finite locally free module of rank `i + 1` on the divisor `D i`.

## The route

The module on the divisor is not taken from the abstract essential-image statement but produced
explicitly: it is the pullback `ι^*(Fⁱ⁺¹/Fⁱ)` along `ι = (D i).subschemeι`, and the unit of the
pullback–pushforward adjunction is an isomorphism precisely because the ideal of `D i` annihilates
the graded piece (`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`, tag 08KS, applied to
`AlgebraicGeometry.annihilatedByKer_submoduleGraded_fittingIncr`). Having the module in hand as a
pullback is what makes its sections computable: the sections of a direct image over an open are
the sections of the module over the inverse image, so the sections of `ι^*(Fⁱ⁺¹/Fⁱ)` over
`ι⁻¹(V)` are the sections of the graded piece over `V`.

The rank is then read off on affine charts.
`Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens` reduces finite local freeness of
rank `r` of a quasi-coherent module on the divisor to the sections on a cover of the divisor by
affine opens, and the preimage `ι⁻¹(V)` of an affine open `V` of the ambient scheme is such an
open, a closed immersion being an affine morphism. Over it the ring of functions is
`Γ(X, V) ⧸ (D i)(V)` (`AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso`) and the sections
of the graded piece are `Stacks.FittingFiltration.gradedQuot` of the two filtration steps
(`AlgebraicGeometry.sectionsSubmodule_fittingIncr` and
`AlgebraicGeometry.submoduleGradedSectionsEquiv`), which
`Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_incr` says is finite locally free
of rank `i + 1` over `Γ(X, V) ⧸ (e_{i+1})`. The two base rings are different presentations of the
same ring, so the transport is `Module.IsFiniteLocallyFreeOfRank.of_ringEquiv`.

## Implementation notes

The local equation `e_{i+1}` generates `(D i)(V)` in *every* degree, including the degenerate
degrees past the chart's bound `N`: there `(D i)(V) = ⊤` and `e_{i+1}` is a unit, so the two
ideals agree again. No case split on `i` versus `N` is therefore needed here, unlike in the
annihilation statement.

`Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_incr_of_eq` is the transport of
the ring-level rank statement along an *equality of submodules*, the exact analogue of the two
transports in `StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedDescent` and needed for the
same reason: the sections of the sheaf-level graded piece are a `gradedQuot` of the submodules of
sections rather than of the local filtration steps, and the equality of those has to be
substituted into a type.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.FittingFiltration

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **A graded piece of the increasing filtration is a module over `R ⧸ (e_{i+1})`, stated for
submodules merely *equal* to the two filtration steps.** This is
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_incr` with the two equalities substituted into
the type of the graded piece, which is the form
`Stacks.FittingFiltration.smul_eq_zero_of_mem_span_gradedQuot_incr` makes available. -/
theorem isTorsionBySet_gradedQuot_incr_of_eq {Nsub Psub : _root_.Submodule R M} {e : ℕ → R}
    {n i : ℕ} (hN : Nsub = incr M e n i) (hP : Psub = incr M e n (i + 1)) :
    Module.IsTorsionBySet R (gradedQuot Nsub Psub) (Ideal.span {e (i + 1)} : Ideal R) :=
  (Module.isTorsionBySet_span_singleton_iff _).mpr fun x =>
    smul_eq_zero_of_mem_span_gradedQuot_incr hN hP (Ideal.mem_span_singleton_self _) x

/-- **A graded piece of the increasing filtration is finite locally free of rank `i + 1` over
`R ⧸ (e_{i+1})`, stated for submodules merely *equal* to the two filtration steps.** This is
`Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_incr` with the two equalities
substituted into the type of the graded piece. -/
theorem isFiniteLocallyFreeOfRank_gradedQuot_incr_of_eq [Module.Finite R M] {e : ℕ → R} {n i : ℕ}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, n < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) n, Ideal.span {e j} ^ (j - k))
    {Nsub Psub : _root_.Submodule R M} (hN : Nsub = incr M e n i)
    (hP : Psub = incr M e n (i + 1)) :
    letI := (isTorsionBySet_gradedQuot_incr_of_eq hN hP).module
    Module.IsFiniteLocallyFreeOfRank (R ⧸ Ideal.span {e (i + 1)}) (gradedQuot Nsub Psub)
      (i + 1) := by
  subst hN
  subst hP
  exact isFiniteLocallyFreeOfRank_gradedQuot_incr hmem hunit hprod i

end Stacks.FittingFiltration

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Divisors Stacks.FittingFiltration

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The graded pieces of 0ESU's increasing filtration are finite locally free of the prescribed
rank on their divisors.** Let `ℱ` be a quasi-coherent module of finite type on a scheme `X`, let
`D` be a locally finite family of ideal sheaves, and suppose every point has an affine open
neighbourhood `V` carrying local equations `e_1, …, e_N` for the family — nonzerodivisors, units
past `N` — cutting out the Fitting ideals of `ℱ` by the product formula
`Fit_k(ℱ)(V) = ∏_{j > k} (e_j)^{j-k}`. Then the graded piece
`Fⁱ⁺¹/Fⁱ` of `AlgebraicGeometry.fittingIncr` is the direct image along `(D i).subschemeι` of a
sheaf of modules on the divisor `D i` which is finite locally free of rank `i + 1`.

In the indexing used here `D i` is the source's `D_{i+1}` and `Fⁱ⁺¹/Fⁱ` is the source's graded
piece in degree `i + 1`, so the rank `i + 1` is the source's rank `i` on `D_i` read at
`i ↦ i + 1`. -/
theorem exists_isFiniteLocallyFreeOfRank_submoduleGraded_fittingIncr [F.IsFiniteType]
    [F.IsQuasicoherent] {D : ℕ → X.IdealSheafData} (hD : IsLocallyFiniteFamily D)
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, N ≤ j → (D j).ideal V = ⊤) ∧
      (∀ j, e j ∈ nonZeroDivisors Γ(X, V.1)) ∧
      (∀ j, N < j → IsUnit (e j)) ∧
      (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V =
        ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)))
    (i : ℕ) (hle : fittingIncr D F i ≤ fittingIncr D F (i + 1)) :
    ∃ G : (D i).subscheme.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (i + 1) ∧
        Nonempty (submoduleGraded hle ≅
          (Scheme.Modules.pushforward (D i).subschemeι).obj G) := by
  have := isQuasicoherent_fittingIncr D F i
  have := isQuasicoherent_fittingIncr D F (i + 1)
  have hweak : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, N ≤ j → (D j).ideal V = ⊤) := fun x => by
    obtain ⟨V, hxV, N, e, hlow, htop, -, -, -⟩ := hchart x
    exact ⟨V, hxV, N, e, hlow, htop⟩
  have : (submoduleGraded hle).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
      (SheafOfModules.Submodule.homOfLEModules hle)
  have hiso : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (D i).subschemeι).unit.app
      (submoduleGraded hle)) :=
    Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero _ _
      (annihilatedByKer_submoduleGraded_fittingIncr hD hweak i hle)
  let iso := @asIso _ _ _ _ _ hiso
  refine ⟨(Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle), ?_, ⟨iso⟩⟩
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
  refine Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens _ (i + 1) fun y => ?_
  obtain ⟨V, hxV, N, e, hlow, htop, hmem, hunit, hprod⟩ := hchart ((D i).subschemeι.base y)
  refine ⟨⟨(D i).subschemeι ⁻¹ᵁ V.1, V.2.preimage (D i).subschemeι⟩, hxV, ?_⟩
  have : Module.Finite Γ(X, V.1) Γ(F, V.1) := moduleFinite_sections_on_affine F V.1 V.2
  have hprodM : ∀ k : ℕ, _root_.fittingIdeal (R := Γ(X, V.1)) (M := Γ(F, V.1)) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k) := fun k => by
    rw [← fittingIdeal_ideal F (k : ℤ) V]
    exact hprod k
  -- The local equation of `D i` generates its ideal in every degree, degenerate ones included.
  have hDi : (D i).ideal V = Ideal.span {e (i + 1)} := by
    rcases le_or_gt (i + 1) N with h | h
    · exact hlow i h
    · rw [htop i (by omega)]
      exact (Ideal.span_singleton_eq_top.mpr (hunit (i + 1) (by omega))).symm
  have hsec := sectionsSubmodule_fittingIncr (F := F) hD V hlow htop
  have hT := isTorsionBySet_gradedQuot_incr_of_eq (hsec i) (hsec (i + 1))
  let := hT.module
  have hFLF : Module.IsFiniteLocallyFreeOfRank (Γ(X, V.1) ⧸ Ideal.span {e (i + 1)})
      (gradedQuot (sectionsSubmodule (fittingIncr D F i) V.1)
        (sectionsSubmodule (fittingIncr D F (i + 1)) V.1)) (i + 1) :=
    isFiniteLocallyFreeOfRank_gradedQuot_incr_of_eq hmem hunit hprodM (hsec i) (hsec (i + 1))
  -- The sections of the graded piece over `V`, read on the divisor.
  let eval : Γ(submoduleGraded hle, V.1) ≃ₗ[Γ(X, V.1)]
      Γ((Scheme.Modules.pushforward (D i).subschemeι).obj
        ((Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle)), V.1) :=
    ((SheafOfModules.evaluation _ (op V.1)).mapIso iso).toLinearEquiv
  let eSec : gradedQuot (sectionsSubmodule (fittingIncr D F i) V.1)
      (sectionsSubmodule (fittingIncr D F (i + 1)) V.1) ≃ₗ[Γ(X, V.1)]
      Γ((Scheme.Modules.pushforward (D i).subschemeι).obj
        ((Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle)), V.1) :=
    (submoduleGradedSectionsEquiv hle V).trans eval
  -- The sections of the direct image over `V` are the sections over `(D i).subschemeι ⁻¹ᵁ V`.
  let eAdd : gradedQuot (sectionsSubmodule (fittingIncr D F i) V.1)
      (sectionsSubmodule (fittingIncr D F (i + 1)) V.1) ≃+
      Γ((Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle),
        (D i).subschemeι ⁻¹ᵁ V.1) := eSec.toAddEquiv
  -- The two presentations of the ring of functions on the divisor.
  let eRing : (Γ(X, V.1) ⧸ Ideal.span {e (i + 1)}) ≃+*
      Γ((D i).subscheme, (D i).subschemeι ⁻¹ᵁ V.1) :=
    (Ideal.quotEquivOfEq hDi.symm).trans
      ((D i).subschemeObjIso V).commRingCatIsoToRingEquiv.symm
  have hRing : ∀ a : Γ(X, V.1), eRing (Ideal.Quotient.mk _ a) =
      ((D i).subschemeι.app V.1).hom a := by
    intro a
    change ((D i).subschemeObjIso V).commRingCatIsoToRingEquiv.symm
      ((Ideal.quotEquivOfEq hDi.symm) (Ideal.Quotient.mk _ a)) = _
    rw [Ideal.quotEquivOfEq_mk, (D i).subschemeι_app V]
    rfl
  refine Module.IsFiniteLocallyFreeOfRank.of_ringEquiv eRing eAdd ?_ hFLF
  intro r m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [hRing a]
  exact eSec.map_smul a m

end AlgebraicGeometry

end
