module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurve
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafCurve
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeOfCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hilbert schemes of points of a smooth proper curve: geometry

Let `X` be a geometrically irreducible smooth proper curve over a field `k`. For every `d` the
degree-`d` Hilbert functor of points of `X` is representable, and every representing scheme is a
smooth proper variety of dimension `d` over `k` ([Stacks, Tag 0B9I], part (1)).

The source deduces the hypothesis of Tag 0B9A from projectivity of proper curves (Tag 0A26). Here
it comes from ampleness instead: a smooth curve is reduced, so it carries an ample invertible
sheaf by Tag 09NX, and every finite set of points then lies in an affine open (Remark 0B9B,
case (5)). The rest is `Stacks.Hilbert.Curve.exists_hilbertScheme`.

## Main results

* `Stacks.Hilbert.Curve.nonempty_represents_of_isCurve` and, for any representing scheme,
  `smooth_of_represents`, `isProper_of_represents`, `isVariety_of_represents` and
  `topologicalKrullDim_eq_of_represents`.

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert.Curve

variable {k : Type u} [Field k]

/-- Over a field, the fibre of a scheme through a point has the dimension of the scheme at that
point. -/
theorem topologicalKrullDimAt_fiber_eq {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = topologicalKrullDimAt X x := by
  have hpre : f ⁻¹' {f x} = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ Subsingleton.elim (f y) (f x)
  let ef : f.fiber (f x) ≃ₜ X :=
    (f.fiberHomeo (f x)).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))
  have hpoint : ef (f.asFiber x) = x := by
    have hx : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, by simp⟩ := Subtype.ext (f.fiberι_asFiber x)
    simp [ef, hx, Homeomorph.setCongr]
  rw [topologicalKrullDimAt_eq_of_homeomorph ef (f.asFiber x), hpoint]

/-- A smooth curve over a field is smooth of relative dimension one. -/
alias smoothOfRelativeDimension_one_of_isCurve :=
    Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve

/-- **Every finite set of points of a smooth curve lies in an affine open:** a smooth curve is
reduced, hence carries an ample invertible sheaf (Tag 09NX), and Remark 0B9B, case (5),
applies. -/
theorem hasAffineFinitePointsInFibres_of_isCurve {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] : HasAffineFinitePointsInFibres f := by
  have : IsReduced X := isReduced_of_smooth f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨L, hL, hA⟩ :=
    InvertibleSheafGeneral.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      X (by rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)])
  exact Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_isAmple f L hA

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The dimension of a scheme over a field which is irreducible and smooth of relative
dimension `d` is `d`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {H : Scheme.{u}}
    (h : H ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d h] [IrreducibleSpace H] :
    topologicalKrullDim H = (d : WithBot ℕ∞) := by
  have := SmoothOfRelativeDimension.smooth d h
  obtain ⟨x⟩ := (inferInstance : Nonempty H)
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k H h x,
    ← topologicalKrullDimAt_fiber_eq h x, fiberDimensionAt_eq_of_smoothOfRelativeDimension h d x]

/-- Any scheme representing the degree-`d` Hilbert functor of a geometrically irreducible smooth
proper curve is smooth of relative dimension `d`, proper and integral. -/
private theorem smoothOfRelativeDimension_and_isProper_of_represents [IsCurve k f]
    [GeometricallyIrreducible f] [Smooth f] [IsProper f] (d : ℕ) (H : Over (Spec (.of k)))
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    SmoothOfRelativeDimension d H.hom ∧ IsProper H.hom ∧ IsIntegral H.left := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : GeometricallyIrreducible (Over.mk f).hom := inferInstanceAs (GeometricallyIrreducible f)
  have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  have hX : HasAffineFinitePointsInFibres (Over.mk f).hom :=
    hasAffineFinitePointsInFibres_of_isCurve f
  let H₀ := scheme (Over.mk f) hX d
  have : SmoothOfRelativeDimension d H₀.hom := smoothOfRelativeDimension_scheme (Over.mk f) hX d
  have : IsProper H₀.hom := isProper_scheme (Over.mk f) hX d
  have : IrreducibleSpace H₀.left := irreducibleSpace_scheme (Over.mk f) hX d
  have := SmoothOfRelativeDimension.smooth d H₀.hom
  have : IsReduced H₀.left := isReduced_of_smooth H₀.hom
  have : IsIntegral H₀.left := isIntegral_of_irreducibleSpace_of_isReduced _
  let e : H₀ ≅ H := RepresentsHilbertFunctorOfRank.isoOver (represents (Over.mk f) hX d) hH
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).inv)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).hom)
  have hw : e.inv.left ≫ H₀.hom = H.hom := Over.w e.inv
  rw [← hw]
  refine ⟨?_, inferInstance, IsIntegral.of_isIso e.hom.left⟩
  simpa using smoothOfRelativeDimension_comp (n := 0) (m := d) e.inv.left H₀.hom

/-- **Stacks Project, Tag 0B9I, part (1).** Let `X` be a geometrically irreducible smooth proper
curve over a field `k` and `d ≥ 0`. The degree-`d` Hilbert functor of points of `X` is
representable, and every scheme representing it is a smooth proper variety of dimension `d`
over `k`. -/
@[stacks 0B9I "(1)", sga "4 XVII 6.3.8" "special case"]
theorem hilbertScheme_geometry [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]
    (d : ℕ) :
    Nonempty (Σ H : Over (Spec (.of k)), RepresentsHilbertFunctorOfRank (Over.mk f) H d) ∧
    ∀ (H : Over (Spec (.of k))), RepresentsHilbertFunctorOfRank (Over.mk f) H d →
      Smooth H.hom ∧ IsProper H.hom ∧ IsVariety k H.hom ∧
        topologicalKrullDim H.left = (d : WithBot ℕ∞) := by
  refine ⟨?_, fun H hH ↦ ?_⟩
  · have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
      smoothOfRelativeDimension_one_of_isCurve f
    have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
    have : GeometricallyIrreducible (Over.mk f).hom :=
      inferInstanceAs (GeometricallyIrreducible f)
    have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
    exact exists_represents (Over.mk f) (hasAffineFinitePointsInFibres_of_isCurve f) d
  obtain ⟨hd, hpr, hint⟩ := smoothOfRelativeDimension_and_isProper_of_represents f d H hH
  have := SmoothOfRelativeDimension.smooth d H.hom
  exact ⟨inferInstance, hpr, { }, topologicalKrullDim_eq_of_smoothOfRelativeDimension H.hom d⟩

/-- **Every scheme representing the degree-`d` Hilbert functor of a geometrically irreducible
smooth proper curve is smooth of relative dimension `d`.** -/
theorem smoothOfRelativeDimension_of_represents [IsCurve k f] [GeometricallyIrreducible f]
    [Smooth f] [IsProper f] (d : ℕ) (H : Over (Spec (.of k)))
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) : SmoothOfRelativeDimension d H.hom :=
  (smoothOfRelativeDimension_and_isProper_of_represents f d H hH).1

/-- **Stacks Project, Tag 0B9I, part (2).** Let `X` be a geometrically irreducible smooth proper
curve over a field `k`, let `H` represent its degree-`d` Hilbert functor and let `k'/k` be a field
extension. The `k'`-rational points of `H` are in bijection with the effective Cartier divisors of
degree `d` on `X_{k'}`: the closed subschemes of `X_{k'}` which are effective Cartier divisors and
finite locally free of degree `d` over `k'`. -/
@[stacks 0B9I "(2)"]
def rationalPointsEquiv {k' : Type u} [Field k'] [Algebra k k'] [IsCurve k f]
    [GeometricallyIrreducible f] [Smooth f] [IsProper f] (d : ℕ) (H : Over (Spec (.of k)))
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶ H) ≃
    {I : ((Over.pullback (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))).hom).obj
          (Over.mk f)).left.IdealSheafData //
      Stacks.Divisors.IsEffectiveCartierDivisor I ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫
          ((Over.pullback (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))).hom).obj
            (Over.mk f)).hom) d} := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  let f' := ((Over.pullback T.hom).obj (Over.mk f)).hom
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve f
  have : SmoothOfRelativeDimension 1 f' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) inferInstance
  have : IsProper f' := inferInstanceAs (IsProper (pullback.snd f T.hom))
  refine (hH.family (T := T)).trans
    { toFun := fun F ↦ ⟨F.ideal, ?_, F.isFiniteLocallyFreeOfRank⟩
      invFun := fun I ↦ ⟨I.1, I.2.2⟩
      left_inv := fun F ↦ rfl
      right_inv := fun I ↦ rfl }
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (F.ideal.subschemeι ≫ f') d :=
    F.isFiniteLocallyFreeOfRank
  exact ((isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper f' F.ideal).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d)).1

end Stacks.Hilbert.Curve

end
