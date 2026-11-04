module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerVanishing
public import
  StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormTrivialOnProjectiveSpaceCurve
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.PointDifferenceSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerReduction
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineFibresRepresentable
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.PicardDescent
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsCurveJacobian

/-!
# The curve case of Voevodsky nilpotence from an Abel projective bundle

The curve case of Stacks 0FH9, assembled from a morphism `f : Sⁿ(X) = Hₙ ⟶ P` which is
Zariski-locally on `P` the projective space `ℙ^{n-g}`, with `g < n` and `P` only locally of
finite type over `k`. In the source `f` is the Abel map `Sⁿ(X) ⟶ Pic^n_{X/k}`, a projective
bundle for `n ≥ 2g - 1`.

## The argument

`ℒ = 𝒪_X(x - x')` is chosen once, by its Picard class `[ℐ_{x'}] - [ℐ_x]`, and its first Chern
class is computed to be `[x] - [x']` (`Stacks.Chow.curvePicardToChowZero_pointIdealClass`), so
that it serves both the norm computation and the Chow computation. The norm sheaf
`𝒩 = Norm_π(pr_{i₀}^*ℒ)` is trivial on every projective space mapping to `Hₙ` over `k`
(`Stacks.Divisors.pullbackPicardClass_normInvertible_fibrePower_eq_zero`), in particular on the
fibres of `f`, hence `𝒩 = f^*ℳ`
(`Stacks.ProjectiveBundle.exists_pullbackPicardClass_eq_of_isTrivial_fibres`). The bundle is flat,
surjective and of relative dimension `n - g`
(`Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.flat` and its siblings), and `Stacks.Chow`'s
`isOfFinAddOrder_smashPointDifference_of_surjective_pullbackPicardClass_symmetricPowerNorm`
concludes.

## Main results

* `Stacks.Chow.curvePicardToChowZero_pointIdealClass`: `c₁(ℐ_t) ∩ [X] = -[t]`.
* `Stacks.Chow.exists_picardClass_eq_pointIdealClass_sub_and_capOnChow_eq`: `𝒪_X(x - x')` with
  its Picard class and its first Chern class.
* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_isLocallyProjectiveSpace`: **the curve
  case of Stacks 0FH9 from an Abel projective bundle.**
* `Stacks.Chow.AbelBundleExists` and `Stacks.Chow.smashNilpotenceCurveCase_of_abelBundle`: the
  curve case `Stacks.Chow.SmashNilpotenceCurveCase` from the existence of Abel projective
  bundles. The Hilbert schemes are those of projective curves (Stacks 0B9A); smoothness of
  relative dimension one comes from smoothness and dimension one.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Hilbert

universe u

namespace Stacks.Chow

section PointIdeal

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [SmoothOfRelativeDimension 1 f] [IsCurve k f]

/-- **`c₁(𝒪_X(-t)) ∩ [X] = -[t]`** for a rational point `t` of a smooth proper curve: the class
of the ideal sheaf of `t` goes to minus the class of the point. -/
theorem curvePicardToChowZero_pointIdealClass (t : Spec (.of k) ⟶ X) (ht : t ≫ f = 𝟙 _) :
    curvePicardToChowZero k f (Stacks.Divisors.pointIdealClass f t ht) =
      -Stacks.WeilCohomology.rationalPointChowClass k f t ht := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have := isEffectiveCartierDivisor_ker_section t ht
  have hc := GenusOne.isClosed_point f t ht
  have hrange : Set.range t = ({GenusOne.point t} : Set X) := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact congrArg t (Subsingleton.elim _ _)
    · rintro rfl
      exact ⟨_, rfl⟩
  have hker : t.ker = Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point t}, hc⟩ : Closeds X) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine congrArg Scheme.IdealSheafData.vanishingIdeal ?_
    ext1
    rw [Closeds.coe_closure, hrange, hc.closure_eq]
    rfl
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{GenusOne.point t}, hc⟩ : Closeds X)) :=
    hker ▸ isEffectiveCartierDivisor_ker_section t ht
  rw [show Stacks.Divisors.pointIdealClass f t ht = -Stacks.Divisors.picardClass t.ker from
      Stacks.Divisors.negativeTwistPicardClass_eq_neg t.ker, map_neg,
    Stacks.Divisors.picardClass_congr hker,
    curvePicardToChowZero_divisorPicardClass k f (IsCurve.topologicalKrullDim_eq_one (f := f)),
    cycleAssociatedToClosedSubscheme_vanishingIdeal_point k f t ht]
  rfl

/-- **`𝒪_X(x - x')` with both of its descriptions.** On a smooth proper curve there is an
invertible module `ℒ` of Picard class `[ℐ_{x'}] - [ℐ_x]`, the description used for the norm
sheaf of Stacks 0FH9, with `c₁(ℒ) ∩ [X] = [x] - [x']`, the description used on Chow groups. -/
theorem exists_picardClass_eq_pointIdealClass_sub_and_capOnChow_eq
    (x x' : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L),
      X.picardClass L hL = Stacks.Divisors.pointIdealClass f x' hx' -
          Stacks.Divisors.pointIdealClass f x hx ∧
        (invCap (fieldChowSituation k) f L).capOnChow (fieldChowSituation k) f 0
          (fundamentalChowClass (fieldChowSituation k) f (0 + 1)) =
            pointDifference k f x x' hx hx' := by
  obtain ⟨L, hL, hcl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)
    (Stacks.Divisors.pointIdealClass f x' hx' - Stacks.Divisors.pointIdealClass f x hx)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL
  refine ⟨L, hL, this, hcl, (invCap_capOnChow_mk (fieldChowSituation k) f L 0
    (fundamentalCycle (fieldChowSituation k) f (0 + 1))).trans
      ((curvePicardToChowZero_picardClass k f L hL).symm.trans ?_)⟩
  rw [hcl, map_sub, curvePicardToChowZero_pointIdealClass k f x' hx',
    curvePicardToChowZero_pointIdealClass k f x hx, pointDifference, neg_sub_neg]

end PointIdeal

section AbelBundle

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [SmoothOfRelativeDimension 1 X.hom]
  [IsProper X.hom] [GeometricallyIrreducible X.hom] {H : ℕ → Over (Spec (.of k))}
  (hH : ∀ d, RepresentsHilbertFunctorOfRank X (H d) d)

include hH in
/-- **The curve case of Stacks 0FH9 from an Abel projective bundle.** Let `k` be algebraically
closed, `X` a smooth proper geometrically irreducible curve over `k`, `H d` representing its
Hilbert functors of points, and `x`, `x'` rational points. Let `g < n` and let `f : Hₙ ⟶ P` be a
morphism over `k` to a scheme `P` locally of finite type over `k`, Zariski-locally on `P` the
projective space `ℙ^{n-g}`. Then the smash power `([x] - [x'])^{×n}` is torsion in `CH_0(Xⁿ)`. -/
theorem isOfFinAddOrder_smashPointDifference_of_isLocallyProjectiveSpace [IsAlgClosed k]
    (x x' : Spec (.of k) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _) (hx' : x' ≫ X.hom = 𝟙 _)
    (n g : ℕ) (hgn : g < n) {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType sP]
    (f : (H n).left ⟶ P) (hf : f ≫ sP = (H n).hom)
    (hbundle : Stacks.ProjectiveBundle.IsLocallyProjectiveSpace f (n - g)) :
    IsOfFinAddOrder (smashPointDifference k X.hom x x' hx hx' n).cycle := by
  have := isCurve_of_smoothOfRelativeDimension_one X.hom
  obtain ⟨L, hL, hLag, hLc, hLchow⟩ :=
    exists_picardClass_eq_pointIdealClass_sub_and_capOnChow_eq k X.hom x x' hx hx'
  let i₀ : Fin n := ⟨0, by omega⟩
  have hN : Stacks.SheafOfModules.IsInvertible (H n).left.presheaf (H n).left.ringCatIsSheaf
      (symmetricPowerNorm hH n i₀ L) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (isInvertible_symmetricPowerNorm hH n i₀ L)
  have hfib : ∀ (j : projectiveSpaceOverRing (n - g) (.of k) ⟶ (H n).left)
      (p : Spec (.of k) ⟶ P), p ≫ sP = 𝟙 _ →
      j ≫ f = (projectiveSpaceOverRing (n - g) (.of k) ↘ Spec (.of k)) ≫ p →
      Stacks.SheafOfModules.pullbackPicardClass j (symmetricPowerNorm hH n i₀ L) hN = 0 := by
    intro j p hp hj
    have hj' : j ≫ (H n).hom =
        Stacks.Divisors.projectiveSpaceStructure (n - g) (Spec (.of k)) := by
      rw [← hf, ← Category.assoc, hj, Category.assoc, hp, Category.comp_id]
      rfl
    exact Stacks.Divisors.pullbackPicardClass_normInvertible_fibrePower_eq_zero (f := X.hom)
      x x' hx hx' L hL hLc i₀ (H n).hom (symmetricPowerMap hH n).left
      (Over.w (symmetricPowerMap hH n)) (n - g) j hj'
  obtain ⟨M, hM, hNM⟩ :=
    Stacks.ProjectiveBundle.exists_pullbackPicardClass_eq_of_isTrivial_fibres sP f (n - g)
      hbundle _ hN hfib
  have : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hM
  have := Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.flat hbundle
  exact isOfFinAddOrder_smashPointDifference_of_surjective_pullbackPicardClass_symmetricPowerNorm
    hH x x' hx hx' L hLchow n i₀ sP (n - g) (by omega) (Nat.sub_le n g) f hf
    hbundle.surjective.surj hbundle.relativeDimension M hNM

end AbelBundle

/-! ### The curve case from the existence of Abel projective bundles -/

/-- **Abel projective bundles exist**: for every smooth proper geometrically irreducible curve `X`
over an algebraically closed field `k` which is projective over `k` and has a rational point, and
every family `H d` representing its Hilbert functors of points, there are `g` and `N` such that
for every `n ≥ N` we have `g < n` and a morphism `Hₙ ⟶ P` over `k`, with `P` locally of finite
type over `k`, which is Zariski-locally on `P` the projective space `ℙ^{n-g}`. In the source this
is the Abel map `Sⁿ(X) ⟶ Pic^n_{X/k}` for `n ≥ 2g - 1`, with `g` the genus (Stacks 0BA0). -/
def AbelBundleExists : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] [GeometricallyIrreducible X.hom]
    (_ : AlgebraicGeometry.IsProjectiveMorphism X.hom) (H : ℕ → Over (Spec (.of k)))
    (_ : ∀ d, RepresentsHilbertFunctorOfRank X (H d) d)
    (x : Spec (.of k) ⟶ X.left), x ≫ X.hom = 𝟙 _ →
    ∃ g N : ℕ, ∀ n ≥ N, g < n ∧ ∃ (P : Scheme.{u}) (sP : P ⟶ Spec (.of k))
      (_ : LocallyOfFiniteType sP) (f : (H n).left ⟶ P), f ≫ sP = (H n).hom ∧
        Stacks.ProjectiveBundle.IsLocallyProjectiveSpace f (n - g)

/-- **The curve case of Stacks 0FH9 from the existence of Abel projective bundles.** -/
theorem smashNilpotenceCurveCase_of_abelBundle (h : AbelBundleExists.{u}) :
    SmashNilpotenceCurveCase.{u} := by
  intro k _ _ X f _ _ hproj _ hdim x x' hx hx'
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have : SmoothOfRelativeDimension 1 f :=
    Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one k f hdim
  let HH := fun d =>
    (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism
      (Over.mk f) hproj d).some
  have hH : ∀ d, RepresentsHilbertFunctorOfRank (Over.mk f) (HH d).1 d := fun d => (HH d).2
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom := ‹_›
  have : IsProper (Over.mk f).hom := ‹_›
  have : GeometricallyIrreducible (Over.mk f).hom := ‹_›
  obtain ⟨g, N, hN⟩ := h k (Over.mk f) hproj (fun d => (HH d).1) hH x hx
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hgn, P, sP, _, u, hu, hbundle⟩ := hN n hn
  exact isOfFinAddOrder_smashPointDifference_of_isLocallyProjectiveSpace hH x x' hx hx' n g hgn
    sP u hu hbundle

end Stacks.Chow

end
