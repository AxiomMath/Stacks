module

public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.RingEquiv

/-!
# The graded pieces of 0ESU's decreasing filtration are finite locally free on the divisors

Stacks tag 0ESU asserts that the graded piece `F_{i+1}/F_{i+2}` of the decreasing filtration of
`ℱ` is a *finite locally free module of rank `i + 1`* on the divisor `D_{i+1}`.
`AlgebraicGeometry.essImage_pushforward_submoduleGraded_fittingDecr` puts the graded piece on the
divisor; this file computes its rank there, which is the other half of the clause.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_submoduleGraded_fittingDecr`: the graded
  piece of the decreasing filtration in degree `i` is the direct image of a module on `D i`
  which is finite locally free of rank `i + 1`.

## Implementation notes

**The module on the divisor is the pullback of the graded piece.** The descent
`AlgebraicGeometry.annihilatedByKer_submoduleGraded_fittingDecr` says the graded piece is
annihilated by the ideal sheaf of `D i`, which by [Stacks, Tag 08KS]
(`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`) makes the unit
`ℳ ⟶ ι_* ι^* ℳ` of the pullback–pushforward adjunction an isomorphism. Taking `ι^* ℳ` rather
than an unnamed object of the essential image is what makes the module on the divisor
quasi-coherent, which the rank computation needs: the pullback of a quasi-coherent module is
quasi-coherent, while membership in an essential image carries no such information.

**The rank is read off the sections on a chart.** Finite local freeness of rank `r` of a
quasi-coherent module is affine-local on sections
(`Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens`), and the affine opens of the
divisor that matter are the preimages `ι⁻¹V` of the affine opens `V` of `X` carrying local
equations. The chart hypothesis therefore need only produce such a `V` *around every point* —
which is what the producer of the divisors supplies, an effective Cartier divisor's ideal being
principal near a point rather than on a given affine open — and the point wanted is the image of
a point of the divisor. There
```
Γ(ι^* ℳ, ι⁻¹V) = Γ(ι_* ι^* ℳ, V) = Γ(ℳ, V)
  = gradedQuot (F_{i+2}(V)) (F_{i+1}(V)),
```
the ring-level graded piece, which
`Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_decr_of_eq` proves finite locally
free of rank `i + 1` over `Γ(X, V) ⧸ (e_{i+1})`. The two base rings are identified by
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso`, since `(e_{i+1})` is the ideal of
`D i` on the chart, and `Module.IsFiniteLocallyFreeOfRank.of_ringEquiv` transports the rank
across that identification. The scalar actions match on the nose: the `Γ(X, V)`-action on the
sections of a direct image is the one along the comorphism, which is
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app`, the quotient map followed by the same
identification.

**Where the hypotheses come from, and why they are more than the descent needs.** The descent
needs only the local equations of the divisors; the rank genuinely needs the Fitting-ideal
identity `Fit_k(ℱ)|_V = ∏_{j > k} (e_j)^{j-k}` as well, and finite presentation of `ℱ`. Without
them the conclusion is false: for `ℱ = 0` and a single nonempty divisor `D 0` every graded piece
vanishes, so the module on `D 0` is zero, which is finite locally free of rank `0` and not of
rank `1`. These are exactly the data that
`AlgebraicGeometry.exists_isAdmissibleBlowup_divisors_filtrations` produces on the blowup, where
the divisors are the Fitting divisors of `b^*ℱ` and `b^*ℱ` is of finite presentation. The
degenerate degrees need no separate treatment: past the last divisor the equation `e_{i+1}` is a
unit, so `(e_{i+1}) = ⊤ = (D i).ideal V` there too, and the ring-level statement applies
unchanged — over the zero ring `Γ(X, V) ⧸ ⊤` every module is finite locally free of every rank.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Divisors Stacks.FittingFiltration

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The graded pieces of 0ESU's decreasing filtration are finite locally free of rank `i + 1`
on the divisors.** For a finitely presented `ℱ` and a locally finite family of effective Cartier
divisors `D` whose local equations `e_j` cut out the Fitting ideals of `ℱ` through
`Fit_k(ℱ) = ∏_{j > k} (e_j)^{j-k}`, the graded piece `F_{i+1}/F_{i+2}` of the decreasing
filtration is the direct image along `(D i).subschemeι` of a module on the divisor `D i` — the
source's `D_{i+1}` — which is finite locally free of rank `i + 1` there.

This is the decreasing half of the graded-piece clause of the source, in the indexing of
`AlgebraicGeometry.fittingDecr`: the filtration is antitone and starts at `F_1 = ℱ`, so its
`i`-th graded piece is the quotient of the `(i+1)`-st step by the `(i+2)`-nd, and it lives on the
divisor of index `i`, whose equation is `e_{i+1}`. -/
theorem exists_isFiniteLocallyFreeOfRank_submoduleGraded_fittingDecr [F.IsFinitePresentation]
    {D : ℕ → X.IdealSheafData} (hD : IsLocallyFiniteFamily D)
    (hDcart : ∀ j, IsEffectiveCartierDivisor (D j))
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, N ≤ j → (D j).ideal V = ⊤) ∧
      (∀ j, e j ∈ nonZeroDivisors Γ(X, V.1)) ∧
      (∀ j, N < j → IsUnit (e j)) ∧
      (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V =
        ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)))
    (i : ℕ) (hle : fittingDecr D F (i + 2) ≤ fittingDecr D F (i + 1)) :
    ∃ G : (D i).subscheme.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (i + 1) ∧
        Nonempty (submoduleGraded hle ≅
          (Scheme.Modules.pushforward (D i).subschemeι).obj G) := by
  have := isQuasicoherent_fittingDecr_of_isEffectiveCartierDivisor D F hD hDcart (i + 2)
  have := isQuasicoherent_fittingDecr_of_isEffectiveCartierDivisor D F hD hDcart (i + 1)
  have hqM : (submoduleGraded hle).IsQuasicoherent :=
    inferInstanceAs (cokernel (SheafOfModules.Submodule.homOfLEModules hle)).IsQuasicoherent
  have hann := annihilatedByKer_submoduleGraded_fittingDecr hD hDcart
    (fun x => (hchart x).imp fun _ ⟨hxV, N, e, hlow, htop, _⟩ => ⟨hxV, N, e, hlow, htop⟩) i hle
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (D i).subschemeι).unit.app (submoduleGraded hle)) :=
    Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero _ _ hann
  have u : submoduleGraded hle ≅ (Scheme.Modules.pushforward (D i).subschemeι).obj
      ((Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle)) :=
    asIso ((Scheme.Modules.pullbackPushforwardAdjunction (D i).subschemeι).unit.app
      (submoduleGraded hle))
  have hqG : ((Scheme.Modules.pullback (D i).subschemeι).obj
      (submoduleGraded hle)).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent (D i).subscheme.toRingedSpace
      X.toRingedSpace (D i).subschemeι.toLRSHom.toShHom (submoduleGraded hle) hqM
  refine ⟨(Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle), ?_, ⟨u⟩⟩
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ (i + 1)).mp ?_
  refine Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens _ (i + 1) fun y => ?_
  obtain ⟨V, hyV, N, e, hlow, htop, hmem, hunit, hprod⟩ := hchart ((D i).subschemeι.base y)
  refine ⟨⟨(D i).subschemeι ⁻¹ᵁ V.1, V.2.preimage (D i).subschemeι⟩, hyV, ?_⟩
  -- The ideal of the divisor on the chart is the one generated by its equation, in every degree:
  -- past the last divisor both sides are the unit ideal.
  have hDiV : (D i).ideal V = Ideal.span {e (i + 1)} := by
    rcases le_or_gt (i + 1) N with hi | hi
    · exact hlow i hi
    · rw [htop i (by omega), Ideal.span_singleton_eq_top.mpr (hunit (i + 1) hi)]
  have := finitePresentation_sections_on_affine F V
  have hprod' : ∀ k : ℕ, _root_.fittingIdeal (R := Γ(X, V.1)) (M := Γ(F, V.1)) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k) :=
    fun k => (fittingIdeal_ideal F (k : ℤ) V).symm.trans (hprod k)
  have hS : ∀ k : ℕ, sectionsSubmodule (fittingDecr D F (k + 1)) V.1 =
      decr Γ(F, V.1) e N (k + 1) :=
    fun k => sectionsSubmodule_fittingDecr (F := F) hD V hlow htop k
  have hP := hS (i + 1)
  have hQ := hS i
  let := (isTorsionBySet_gradedQuot_decr_of_eq hP hQ).module
  have := (isTorsionBySet_gradedQuot_decr_of_eq hP hQ).isScalarTower (S := Γ(X, V.1))
  let eu : Γ(submoduleGraded hle, V.1) ≃ₗ[Γ(X, V.1)]
      Γ((Scheme.Modules.pushforward (D i).subschemeι).obj
        ((Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle)), V.1) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op V.1)).mapIso u).toLinearEquiv
  let g := (submoduleGradedSectionsEquiv hle V).trans eu
  let gW : gradedQuot (sectionsSubmodule (fittingDecr D F (i + 2)) V.1)
        (sectionsSubmodule (fittingDecr D F (i + 1)) V.1) ≃+
      Γ((Scheme.Modules.pullback (D i).subschemeι).obj (submoduleGraded hle),
        (D i).subschemeι ⁻¹ᵁ V.1) :=
    g.toAddEquiv
  -- The ring of the divisor on the chart is the quotient by the equation.
  let ε : (Γ(X, V.1) ⧸ Ideal.span {e (i + 1)}) ≃+*
      Γ((D i).subscheme, (D i).subschemeι ⁻¹ᵁ V.1) :=
    (Ideal.quotEquivOfEq hDiV.symm).trans
      ((D i).subschemeObjIso V).symm.commRingCatIsoToRingEquiv
  have hε : ∀ a : Γ(X, V.1), ε (Ideal.Quotient.mk (Ideal.span {e (i + 1)}) a)
      = ((D i).subschemeι.app V.1).hom a := by
    intro a
    change ((D i).subschemeObjIso V).symm.commRingCatIsoToRingEquiv
      (Ideal.quotEquivOfEq hDiV.symm (Ideal.Quotient.mk (Ideal.span {e (i + 1)}) a)) = _
    rw [Ideal.quotEquivOfEq_mk, (D i).subschemeι_app V]
    rfl
  refine Module.IsFiniteLocallyFreeOfRank.of_ringEquiv ε gW (fun r x => ?_)
    (isFiniteLocallyFreeOfRank_gradedQuot_decr_of_eq hP hQ hmem hunit hprod')
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [hε a]
  exact map_smul g a x

end AlgebraicGeometry

end
