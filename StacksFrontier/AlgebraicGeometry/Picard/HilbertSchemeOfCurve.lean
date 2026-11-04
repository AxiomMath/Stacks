module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Heart.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertDivisorAddition
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePointsFiniteComponents
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.CurvePoints

/-!
# Hilbert schemes of points on a smooth proper curve

Let `X` be a geometrically irreducible smooth proper curve over a field `k`. This file proves,
for the schemes `H_d` representing the Hilbert functors `Hilb^d_{X/k}`, the three assertions of
Stacks Tag 0B9I:

1. `H_d` is a smooth proper variety of dimension `d` over `k`;
2. for a field extension `k'/k` the `k'`-rational points of `H_d` are the effective Cartier
   divisors of degree `d` on `X_{k'}`;
3. addition of divisors `H_{d₁} ×_k H_{d₂} ⟶ H_{d₁+d₂}` is finite locally free of degree
   `(d₁ + d₂).choose d₁`.

It also supplies, through Stacks Tag 09NN, the hypothesis under which the Hilbert functors of `X`
are representable (Stacks Tag 0B9A): every finite family of points of `X` lies in an affine open.

## Main results

* `Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve` — a smooth curve is smooth of
  relative dimension one.
* `Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_isCurve` — finitely many points of a curve
  lie in a common affine open.
* `Stacks.Hilbert.isProperVariety_of_represents` — part (1) for a representing scheme.
* `Stacks.Hilbert.rationalPointsEquiv` — part (2).
* Part (3) is `Stacks.Hilbert.isFiniteLocallyFreeOfRank_addDivisors_of_isCurve`
  (`StacksFrontier/AlgebraicGeometry/Picard/HilbertSchemeProperCurve.lean`).

## Implementation notes

*Representability.* The representability of `Hilb^d_{X/k}` is Stacks Tag 0B9A applied to `X`,
whose hypothesis is `Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_isCurve`. Part (1) needs
the Hilbert schemes of all degrees up to `d`, and is stated with that representability as the
single argument `hrep`.

*Properness and irreducibility.* The source deduces both from the finite surjection
`X^d ⟶ H_d`. Here the same is done one point at a time: point addition `H_d ×_k X ⟶ H_{d+1}` is
finite locally free of degree `d + 1` (Stacks Tag 0B9G), hence surjective, so properness
(Stacks Tag 03GN) and irreducibility pass from `H_d ×_k X` to `H_{d+1}`, starting from
`H_0 ≅ Spec k`.

*Degree of a divisor.* The degree of an effective Cartier divisor `D` on a proper curve is its
degree as a finite locally free scheme over the base field (Stacks Tag 0AYY), which is how it is
written in part (2).

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A smooth curve over a field is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isCurve [IsCurve k f] [Smooth f] :
    SmoothOfRelativeDimension 1 f := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f 1 fun x => ?_
  rw [Stacks.AlgebraicGeometry.Refute05M5Heart.topologicalKrullDimAt_fiber_eq_of_subsingleton,
    ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x,
    IsCurve.topologicalKrullDim_eq_one (f := f)]
  rfl

/-- The target of a surjective morphism of schemes with irreducible source is irreducible. -/
private theorem irreducibleSpace_of_surjective {A B : Scheme.{u}} (e : A ⟶ B) [Surjective e]
    [IrreducibleSpace A] : IrreducibleSpace B :=
  Function.Surjective.irreducibleSpace e.continuous Surjective.surj

/-- Along the point additions `H_n ×_k X ⟶ H_{n+1}`, which are finite locally free of degree
`n + 1` and hence surjective, properness (Stacks Tag 03GN) and irreducibility pass from
`H_n ×_k X` to `H_{n+1}`, starting from `H_0 ≅ Spec k`. -/
private theorem isProper_and_irreducibleSpace_of_represents [IsCurve k f]
    [GeometricallyIrreducible f] [Smooth f] [IsProper f] (G : ℕ → Over (Spec (.of k)))
    (hG : ∀ n, RepresentsHilbertFunctorOfRank (Over.mk f) (G n) n) (n : ℕ) :
    IsProper (G n).hom ∧ IrreducibleSpace (G n).left := by
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
  have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  have : GeometricallyIrreducible (Over.mk f).hom := inferInstanceAs (GeometricallyIrreducible f)
  have : UniversallyOpen (Over.mk f).hom := inferInstanceAs (UniversallyOpen f)
  induction n with
  | zero =>
    have : IsIso (G 0).hom := isIso_hom_of_representsHilbertFunctorOfRank_zero (hG 0)
    exact ⟨inferInstance, irreducibleSpace_of_surjective (inv (G 0).hom)⟩
  | succ n ih =>
    obtain ⟨hprop, hirr⟩ := ih
    let p := (addPoint (hG n) (hG (n + 1))).left
    have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p (n + 1) :=
      (isPointAddition_addPoint (hG n) (hG (n + 1))).isFiniteLocallyFreeOfRank_left
    obtain ⟨hfin, hflat, hfp⟩ :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p (n + 1))
    have : Surjective p := p.one_le_finrank_iff_surjective.mp fun y => by
      rw [(Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq p (n + 1)).mp
        hrank y]
      exact Nat.succ_le_succ (Nat.zero_le n)
    have hpq : p ≫ (G (n + 1)).hom = (G n ⨯ Over.mk f).hom := Over.w _
    have hprod : (G n ⨯ Over.mk f).hom = (Over.prodLeftIsoPullback (G n) (Over.mk f)).hom ≫
        pullback.fst (G n).hom (Over.mk f).hom ≫ (G n).hom := by
      rw [Over.prodLeftIsoPullback_hom_fst_assoc]
      exact (Over.w (prod.fst : G n ⨯ Over.mk f ⟶ G n)).symm
    have : UniversallyClosed (p ≫ (G (n + 1)).hom) := by
      rw [hpq, hprod]
      infer_instance
    have : IsSeparated (G (n + 1)).hom :=
      isSeparated_of_representsHilbertFunctorOfRank _ _ _ (hG (n + 1))
    have : Smooth (G (n + 1)).hom :=
      (smoothOfRelativeDimension_of_represents G hG (n + 1)).smooth
    refine ⟨isProper_of_comp_surjective p _, ?_⟩
    have : IrreducibleSpace (G n ⨯ Over.mk f).left :=
      irreducibleSpace_of_surjective (Over.prodLeftIsoPullback (G n) (Over.mk f)).inv
    exact irreducibleSpace_of_surjective p

/-- **Stacks Project, Tag 0B9I, part (1), for a representing scheme.** Let `X` be a
geometrically irreducible smooth proper curve over `k` whose Hilbert functors are representable.
A scheme `H` representing `Hilb^d_{X/k}` is a smooth proper variety of dimension `d` over `k`. -/
theorem isProperVariety_of_represents [IsCurve k f] [GeometricallyIrreducible f] [Smooth f]
    [IsProper f]
    (hrep : ∀ n : ℕ,
      Nonempty (Σ H : Over (Spec (.of k)), RepresentsHilbertFunctorOfRank (Over.mk f) H n))
    {d : ℕ} {H : Over (Spec (.of k))} (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    IsProperVariety k H.hom ∧ SmoothOfRelativeDimension d H.hom ∧
      topologicalKrullDim H.left = d := by
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
  let G : ℕ → Over (Spec (.of k)) := fun n => if n = d then H else (hrep n).some.1
  have hG : ∀ n, RepresentsHilbertFunctorOfRank (Over.mk f) (G n) n := by
    intro n
    by_cases hn : n = d
    · subst hn
      simpa [G] using hH
    · simpa [G, hn] using (hrep n).some.2
  have hd : G d = H := ite_eq_left rfl
  obtain ⟨hprop, hirr⟩ := isProper_and_irreducibleSpace_of_represents f G hG d
  have hsm := smoothOfRelativeDimension_of_represents G hG d
  rw [hd] at hprop hirr hsm
  have : Smooth H.hom := hsm.smooth
  have : IsSeparated H.hom := isSeparated_of_representsHilbertFunctorOfRank _ _ _ hH
  have : IsReduced H.left := isReduced_of_smooth_of_isAffine H.hom
  have : IsIntegral H.left := isIntegral_of_irreducibleSpace_of_isReduced H.left
  refine ⟨(isProperVariety_iff k H.hom).mpr ⟨IsVariety.mk, hprop⟩, hsm, ?_⟩
  have hpt (x : H.left) : TopologicalSpace.localKrullDim H.left x = (d : WithBot ℕ∞) := by
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
      ← Stacks.AlgebraicGeometry.Refute05M5Heart.topologicalKrullDimAt_fiber_eq_of_subsingleton
        H.hom x]
    exact fiberDimensionAt_eq_of_smoothOfRelativeDimension H.hom d x
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim, iSup_congr hpt, iSup_const]

/-- **Stacks Project, Tag 0B9I, part (2).** Let `X` be a smooth curve over `k` and let `H`
represent `Hilb^d_{X/k}`. For a field extension `k'/k`, the `k'`-rational points of `H` are in
bijection with the effective Cartier divisors of degree `d` on `X_{k'}`. -/
def rationalPointsEquiv [IsCurve k f] [Smooth f] {d : ℕ} {H : Over (Spec (.of k))}
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) (k' : Type u) [Field k']
    [Algebra k k'] :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶ H) ≃
      {D : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).IdealSheafData //
        Stacks.Divisors.IsEffectiveCartierDivisor D ∧
          Stacks.Morphisms.IsFiniteLocallyFreeOfRank
            (D.subschemeι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) d} :=
  hH.family.trans
    { toFun := fun Z =>
        ⟨Z.ideal,
          letI : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve f
          letI : SmoothOfRelativeDimension 1
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
            (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
              (IsPullback.of_hasPullback f _) inferInstance
          letI : Stacks.Morphisms.IsFiniteLocallyFree (Z.ideal.subschemeι ≫
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
            @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d
              Z.isFiniteLocallyFreeOfRank
          (AlgebraicGeometry.isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) Z.ideal).1,
          Z.isFiniteLocallyFreeOfRank⟩
      invFun := fun D => ⟨D.1, D.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Stacks.Hilbert

end
