module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Induction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.CoefficientUniverseVanishing

/-!
# Vanishing of higher direct images of torsion sheaves along proper morphisms

[Stacks, Tag 095U]: for a proper morphism of schemes `p : S ⟶ T` all of whose fibres have
dimension at most `N`, and a torsion abelian sheaf `F` on `S_étale`, `R^q p_* F = 0` for `q > 2N`.

This file states it for abelian sheaves on Mathlib's small étale sites with coefficients in
`AddCommGrpCat.{max (u + 1) r}`, at every coefficient universe `r`, with the higher direct images
Mathlib's right derived functors of `Stacks.EtaleCohomology.etaleAbelianDirectImage`. Two results
the source proves enter as named arguments: the proper base change theorem, [Stacks, Tag 095T]
(`h095T`), and the cohomology of curves, [Stacks, Tag 03SC] (`h03SC`).

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim`.

## References

* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 095U], from the case of proper curves.** As
`isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim`, with [Stacks, Tag 03SC]
replaced by the one clause of it the proof uses: `hcurve`, the vanishing `H^q(C, G) = 0` for
`q > 2` on every proper scheme `C` of dimension at most one over an algebraically closed field
and every torsion abelian sheaf `G`. The other argument is `h095T`, the conclusion of
[Stacks, Tag 095T]. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (hcurve : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * 1 < q →
          letI := isGrothendieckAbelian_sheaf_smallEtale.{u, r} X
          letI := IsGrothendieckAbelian.hasExt.{max (u + 1) r}
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
          Subsingleton (Sheaf.H.{max (u + 1) r} G q))
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (N : ℕ)
    (hN : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ N)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
    (hF : Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F) (q : ℕ) (hq : 2 * N < q) :
    IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F) := by
  let : ∀ S : Scheme.{u},
      HasExt.{max (u + 1) r} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) :=
    fun S ↦
      have := isGrothendieckAbelian_sheaf_smallEtale.{u, r} S
      IsGrothendieckAbelian.hasExt.{max (u + 1) r} _
  rcases Nat.eq_zero_or_pos N with rfl | hN1
  · exact isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiber_le_zero.{u, r} p hN F
      q hq
  · exact isZero_rightDerived_etaleAbelianDirectImage_of_geometricFibres.{u, r} p (h095T p) N hN
      (subsingleton_sheafH_of_isSepClosed_of_isAlgClosed.{u, r} N
        (subsingleton_sheafH_of_isProper_of_isAlgClosed_of_curve.{u, r} h095T hcurve N hN1))
      F hF q hq

/-- **[Stacks, Tag 095U]**, granted the proper base change theorem and the cohomology of curves.
Let `p : S ⟶ T` be a proper morphism of schemes all of whose fibres have dimension at most `N`.
Then for every torsion abelian sheaf `F` on `S_étale` the higher direct images vanish above
twice the fibre dimension: `R^q p_* F = 0` for every `q > 2N`.

It is stated for abelian sheaves with coefficients in `AddCommGrpCat.{max (u + 1) r}` at every
coefficient universe `r`, and takes two named arguments: `h095T`, the conclusion of
[Stacks, Tag 095T] (cohomology commutes with base change for every proper morphism), and
`h03SC`, the statement of [Stacks, Tag 03SC]. At the coefficient universe `0`, Tag 095T is
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`. The case `N = 0` needs
neither argument: it is
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiber_le_zero`.

The proof is the source's induction on `N`. The stalks of `R^q p_* F` at the geometric points
are the cohomology of the geometric fibres ([Stacks, Tag 0DDF], from `h095T`), which are proper
of dimension at most `N` over separably closed fields; passing to the algebraic closure is a
universal homeomorphism ([Stacks, Tag 03SI]). Over an algebraically closed field the case
`N = 1` is [Stacks, Tag 03SC]; for `N ≥ 2` the scheme is replaced by its reduction and then by
its irreducible components, and an integral `X` is modified along the closure of the graph of a
dominant rational map to `ℙ¹`, after which the Leray spectral sequence of the second projection,
whose fibres have dimension at most `N - 1`, concludes; see
`Stacks.EtaleCohomology.subsingleton_sheafH_of_isProper_of_isAlgClosed`. The modifications are
controlled by the Mayer–Vietoris sequence of [Stacks, Tag 0EW3], which is why no normalization
is needed. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (h03SC : CurveTorsionCohomologyStatement.{u, r})
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (N : ℕ)
    (hN : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ N)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
    (hF : Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F) (q : ℕ) (hq : 2 * N < q) :
    IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F) := by
  exact isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve.{u, r} h095T
    (fun k _ _ X π _ hX G hG q hq ↦
      subsingleton_sheafH_of_topologicalKrullDim_le_one.{u, r} h03SC k X π hX G hG q hq)
    p N hN F hF q hq

/-- **[Stacks, Tag 095U], from the case of proper curves at the smallest coefficient universe.**
As `isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve`, with the
curve vanishing `hcurve` asked only for torsion sheaves with sections in `AddCommGrpCat.{u + 1}`:
it is carried to the coefficient universe `max (u + 1) r` by
`subsingleton_sheafH_of_isProper_of_isAlgClosed_of_curve_univ`. The other argument is `h095T`,
the conclusion of [Stacks, Tag 095T]. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve_univ
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (hcurve : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * 1 < q →
          letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
          letI := IsGrothendieckAbelian.hasExt.{u + 1}
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          Subsingleton (Sheaf.H.{u + 1} G q))
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (N : ℕ)
    (hN : ∀ t : T, topologicalKrullDim (p.fiber t) ≤ N)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
    (hF : Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F) (q : ℕ) (hq : 2 * N < q) :
    IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F) :=
  isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim_of_curve.{u, r} h095T
    (fun k _ _ X π _ hX G hG q hq ↦
      subsingleton_sheafH_of_isProper_of_isAlgClosed_of_curve_univ.{r} hcurve k X π hX G hG q hq)
    p N hN F hF q hq

end Stacks.EtaleCohomology

end
