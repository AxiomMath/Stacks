module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Weak association on a field-valued fibre descends to the scheme-theoretic fibre

Let `α : X ⟶ Y` be a morphism of schemes, `N` a quasi-coherent `𝒪_X`-module and
`g : Spec K ⟶ Y` a morphism from the spectrum of a field whose image is the single point
`v` of `Y`. The base change `X ×_Y Spec K` is then a base change of the scheme-theoretic
fibre `α.fiber v` along a field extension `κ(v) ⟶ K`, so Stacks 0CUC applies: a weakly
associated point of the inverse image of `N` on `X ×_Y Spec K` lies over a weakly associated
point of the inverse image of `N` on `α.fiber v`.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_fiber_of_fieldValuedFibre`: the descent
  statement, with the compatibility of the two points recorded as an equality in `X`.

## Implementation notes

The reduction to Stacks 0CUC is a pasting of pullback squares: `g` factors as
`Spec K ⟶ Spec κ(v) ⟶ Y` because the spectrum of a field is a one-point space, and pasting
the base change of `α.fiberToSpecResidueField v` along `Spec κ(v) ⟶ Spec K` onto the square
defining `α.fiber v` exhibits `X ×_Y Spec K` as a pullback of `α` along `g`. That pasting is
isolated in `AlgebraicGeometry.exists_isWeaklyAssociatedPoint_pullback_fst_of_comp`, which is
stated for arbitrary schemes: it is pure limit bookkeeping together with the transport of
Zariski weak association across an isomorphism of schemes, and knows nothing about fields.

The comparison isomorphism is obtained from `CategoryTheory.IsPullback.isoIsPullback` rather
than from a named pullback-of-pullback isomorphism, which keeps the identification of the
projections available as `isoIsPullback_hom_fst`; weak association is then carried across it
with `AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion`, an
isomorphism of schemes being an open immersion.

The `κ(v)`-algebra structure on `K` is the one induced by the factorisation, so that
`algebraMap ↥(Y.residueField v) K` is definitionally the underlying ring map of the
factorising morphism and Stacks 0CUC applies verbatim.

## References

* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 0CUC](https://stacks.math.columbia.edu/tag/0CUC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Pasting of pullback squares, in the form used for a fibre over a field-valued point: if
`h ≫ k = gl` then a weakly associated point of the inverse image of `N` on the base change of
`α` along `gl` lies over a weakly associated point of the inverse image of `N` on the base
change along `k`, after base changing that further along `h`. -/
private theorem exists_isWeaklyAssociatedPoint_pullback_fst_of_comp
    {X Y Z W : Scheme.{u}} (α : X ⟶ Y) (N : X.Modules) (h : W ⟶ Z) (k : Z ⟶ Y)
    (gl : W ⟶ Y) (hgl : h ≫ k = gl) (θ : (pullback α gl : Scheme.{u}))
    (hθ : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (pullback.fst α gl)).obj N) θ) :
    ∃ y : (pullback (pullback.snd α k) h : Scheme.{u}),
      (pullback.fst α k).base ((pullback.fst (pullback.snd α k) h).base y)
          = (pullback.fst α gl).base θ ∧
        Stacks.Divisors.IsWeaklyAssociatedPoint
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd α k) h)).obj
            ((Scheme.Modules.pullback (pullback.fst α k)).obj N)) y := by
  have Sbig := (IsPullback.of_hasPullback (pullback.snd α k) h).paste_horiz
    (IsPullback.of_hasPullback α k)
  rw [hgl] at Sbig
  let e := (IsPullback.of_hasPullback α gl).isoIsPullback _ _ Sbig
  have he : e.hom ≫ (pullback.fst (pullback.snd α k) h ≫ pullback.fst α k)
      = pullback.fst α gl := (IsPullback.of_hasPullback α gl).isoIsPullback_hom_fst _ _ Sbig
  refine ⟨e.hom.base θ, ?_, ?_⟩
  · simpa using congrArg (fun m : (pullback α gl : Scheme.{u}) ⟶ X => m.base θ) he
  · exact (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion e.hom _ _).mp
      ((isWeaklyAssociatedPoint_iff_of_iso ((Scheme.Modules.pullbackCongr he.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp e.hom _).app N).symm ≪≫ (Scheme.Modules.pullback e.hom).mapIso
          ((Scheme.Modules.pullbackComp _ _).app N).symm) θ).mp hθ)

/-- Weak association on the fibre of `α` over an arbitrary field-valued point of the target
descends to the scheme-theoretic fibre over the image point. -/
theorem isWeaklyAssociatedPoint_fiber_of_fieldValuedFibre
    {X Y : Scheme.{u}} (α : X ⟶ Y) (N : X.Modules) [N.IsQuasicoherent]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ Y) (v : Y)
    (hg : ∀ z, g.base z = v)
    (θ : (Limits.pullback α g : Scheme.{u}))
    (hθ : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (Limits.pullback.fst α g)).obj N) θ) :
    ∃ θ' : α.fiber v, α.fiberι v θ' = (Limits.pullback.fst α g).base θ ∧
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback (α.fiberι v)).obj N) θ' := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.residueField v ⟶ CommRingCat.of K,
      Spec.map φ ≫ Y.fromSpecResidueField v = g := by
    obtain rfl : v = g (IsLocalRing.closedPoint K) := (hg _).symm
    exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g⟩
  let alg : Algebra ↥(Y.residueField v) K := (CommRingCat.Hom.hom φ).toAlgebra
  obtain ⟨y, hy₁, hy₂⟩ := exists_isWeaklyAssociatedPoint_pullback_fst_of_comp α N
    (Spec.map (CommRingCat.ofHom (algebraMap ↥(Y.residueField v) K)))
    (Y.fromSpecResidueField v) g hφ θ hθ
  have hqc : ((Scheme.Modules.pullback (α.fiberι v)).obj N).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ (α.fiberι v).toLRSHom.toShHom N ‹_›
  refine ⟨(pullback.fst (α.fiberToSpecResidueField v)
    (Spec.map (CommRingCat.ofHom (algebraMap ↥(Y.residueField v) K)))).base y, hy₁, ?_⟩
  exact @isWeaklyAssociatedPoint_of_baseChange ↥(Y.residueField v) K inferInstance
    inferInstance alg (α.fiber v) (α.fiberToSpecResidueField v)
    ((Scheme.Modules.pullback (α.fiberι v)).obj N) hqc y _ rfl hy₂

end AlgebraicGeometry

end
