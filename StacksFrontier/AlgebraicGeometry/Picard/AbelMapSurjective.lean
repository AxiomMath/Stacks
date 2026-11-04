module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapComponent
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import
  StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PointedCurveStructureSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Surjectivity of `γ_d` for `d` at least the genus

Let `X` be a geometrically irreducible smooth projective curve of genus `g` over a field `k`
with a `k`-rational point, let `H` represent the degree-`d` Hilbert functor of `X` and let
`Pic^d` represent the degree-`d` component of the Picard functor. If `d ≥ g`, the morphism
`γ_d : H ⟶ Pic^d` of [Stacks, Tag 0BA0], clause (4), is surjective ([Stacks, Tag 0BA0],
clause (5), first half).

The proof is the source's. A point `p` of `Pic^d` with residue field `K` is a `K`-point of the
degree-`d` component. Since `X` has a rational point, the Picard functor on `K` is the Picard
group of `X_K` ([Stacks, Tags 0B9N, 0B9U]), so the point is the class of an invertible module `ℒ`
on `X_K`, and `χ(X_K, ℒ) = d + 1 - g`. Then `deg ℒ = d ≥ g`, so `ℒ ≅ 𝒪_{X_K}(D)` for an effective
divisor `D` of degree `d` on `X_K` (Riemann-Roch). The divisor `D` is a `K`-point of `H` which
`γ_d` sends to the given `K`-point of `Pic^d`, so `p` is in the image of `γ_d`.

## Main results

* `Stacks.AbelMap.exists_isInvertible_of_mem`: every point of the degree-`d` component is the
  class of an invertible module whose fibres have Euler characteristic `d + 1 - g`.
* `Stacks.AbelMap.surjective_abelMap`: **Tag 0BA0, clause (5), surjectivity**.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Divisors (divisorSheaf IsEffectiveCartierDivisor)
open Stacks.FibreCohomology (fibreCohomology)
open Stacks.PicardFunctor (picardFunctor toPicardFunctor baseChange baseChangeMap picardAt
  picardMap testMap)

universe u

namespace Stacks.AbelMap

/-- **Over a field the fibre cohomology at the point is the cohomology.** -/
theorem finrank_cohomologyOverField_eq_fibreCohomology {K : Type u} [Field K] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (.of K)) [IsProper fZ] (L : Z.Modules) [L.IsQuasicoherent]
    (s : Spec (.of K)) (n : ℕ) :
    Module.finrank K (cohomologyOverField K fZ L n) =
      Module.finrank ((Spec (.of K)).residueField s) (fibreCohomology fZ L s n) := by
  have := isIso_fromSpecResidueField_of_field K s
  let φ : (Spec (.of K)).residueField s ⟶ CommRingCat.of K :=
    Spec.preimage (inv ((Spec (.of K)).fromSpecResidueField s))
  have hφ : Spec.map φ ≫ (Spec (.of K)).fromSpecResidueField s = 𝟙 _ := by
    simp [φ]
  refine Stacks.FibreCohomology.finrank_eq_of_isPullback fZ L s φ (𝟙 Z) fZ ?_ L
    ((Scheme.Modules.pullbackId Z).app L).symm n
  rw [hφ]
  exact IsPullback.id_horiz fZ

/-- **A smooth nonempty scheme over a separably closed field has a rational point.** The closed
points with finite separable residue field are dense ([Stacks, Tag 056U]), and a finite separable
extension of a separably closed field is trivial. -/
@[sga "6 X 7.18.2" "(a), special case"]
theorem exists_section_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [Nonempty X] : ∃ σ : Spec (.of k) ⟶ X, σ ≫ f = 𝟙 _ := by
  obtain ⟨x, -, hfin, hsep⟩ := (dense_closedPoints_with_finite_separable_residueField_of_smooth
    f).nonempty
  let φ : CommRingCat.of k ⟶ X.residueField x :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x
  let : Algebra k (X.residueField x) := φ.hom.toAlgebra
  have hbij : Function.Bijective φ :=
    ⟨φ.hom.injective, IsSepClosed.algebraMap_surjective k (X.residueField x)⟩
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr hbij
  have hφ : Spec.map φ = X.fromSpecResidueField x ≫ f := by
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecResidueField_toSpecΓ, Category.assoc,
      Category.assoc, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  refine ⟨Spec.map (inv φ) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  {d : ℕ} {P : Subfunctor (picardFunctor B hX hk f)}
  (hP : IsDegreeComponent B hX hk f d P)

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
include σ hσ hP in
/-- **Every point of the degree-`d` component is the class of an invertible module of fibre
Euler characteristic `d + 1 - g`.** With a rational point the Picard functor is the Picard group
of the base change ([Stacks, Tags 0B9N, 0B9U]). -/
theorem exists_isInvertible_of_mem (T : BigFppfOver B (Spec (.of k)) hk)
    (y : P.toFunctor.obj (op T)) :
    ∃ (L : (baseChange B hX hk f T).Modules)
      (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
        (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L),
      (toPicardFunctor B hX hk f).app (op T) (Stacks.SheafOfModules.picardClass _ _ L hL) =
          y.1 ∧
        HasFibreEuler B hX hk f T L (d + 1 - genus (B.inclusion.map f)) := by
  have hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (Stacks.PicardFunctor.baseChangeProj B hX hk f U).toLRSHom.toHom.c := fun U =>
    isIso_c_baseChange_of_isCurve_of_section (B.inclusion.map f) σ hσ (B.inclusion.map U.hom)
  obtain ⟨c, hc⟩ :=
    Stacks.PicardFunctor.surjective_toPicardFunctorHom B hX hk f σ hσ hOiso T y.1
  obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ c
  refine ⟨L, hL, hc, (hP T L hL).1 ?_⟩
  rw [← Stacks.PicardFunctor.toPicardFunctorHom_apply, hc]
  exact y.2

/-- Over a field, if the fibre Euler characteristic of an invertible module `L` on a curve of
genus `g` is `n`, then `deg L = n - 1 + g`. -/
private theorem invertibleCurveDegree_eq_of_fibreCohomology {K : Type u} [Field K] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (.of K)) [IsProper fZ] [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fZ.appTop)]
    (hdim : topologicalKrullDim Z ≤ 1) (L : Z.Modules) [L.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L]
    (s : Spec (.of K)) {n : ℤ}
    (hχ : (Module.finrank ((Spec (.of K)).residueField s) (fibreCohomology fZ L s 0) : ℤ) -
      Module.finrank ((Spec (.of K)).residueField s) (fibreCohomology fZ L s 1) = n) :
    invertibleCurveDegree K fZ hdim L = n - 1 + genus fZ := by
  have hχ' : (Module.finrank K (cohomologyOverField K fZ L 0) : ℤ) -
      Module.finrank K (cohomologyOverField K fZ L 1) = n := by
    rwa [finrank_cohomologyOverField_eq_fibreCohomology fZ L s 0,
      finrank_cohomologyOverField_eq_fibreCohomology fZ L s 1]
  rw [invertibleCurveDegree_eq_sub_of_isZero K fZ hdim L
    (isZero_cohomologyOverField_of_two_le' K fZ hdim L)
    (isZero_cohomologyOverField_of_two_le' K fZ hdim _),
    finrank_cohomologyOverField_unit_zero_eq_one fZ,
    ← genus_eq_finrank_cohomologyOverField_unit_one' K fZ]
  show (Module.finrank K (cohomologyOverField K fZ L 0) : ℤ) -
    Module.finrank K (cohomologyOverField K fZ L 1) - _ = _
  rw [hχ']
  ring

variable (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) d)
  {Pd : BigFppfOver B (Spec (.of k)) hk} (R : P.toFunctor.RepresentableBy Pd)

omit [IsProjectiveVariety k (B.inclusion.map f)] in
/-- **A degree-`d` family whose class is that of a `T`-point `a` of `Pic^d` lifts `a` through
`γ_d`.** -/
private theorem exists_comp_abelMap_eq {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ Pd)
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d)
    (hD : (toPicardFunctor B hX hk f).app (op T) D.picardClass = (R.homEquiv a).1) :
    ∃ b : T ⟶ H, b ≫ abelMap B hX hk f hP H hH R = a := by
  let h := hH.family.symm D
  let b : T ⟶ H := Over.homMk (B.inclusion.preimage h.left)
    (B.inclusion.map_injective (by rw [Functor.map_comp, Functor.map_preimage]; exact Over.w h))
  have htest : testMap B hk b = h := by
    ext
    exact Functor.map_preimage B.inclusion h.left
  refine ⟨b, R.homEquiv.injective ?_⟩
  rw [homEquiv_comp_abelMap, htest, Equiv.apply_symm_apply]
  exact Subtype.ext hD

include σ hσ in
/-- **Stacks Project, Tag 0BA0, clause (5): `γ_d` is surjective for `d ≥ g`.** Let `X` be a
geometrically irreducible smooth projective curve of genus `g` over `k` with a rational point,
`H` a scheme representing its degree-`d` Hilbert functor and `Pic^d` an object representing the
degree-`d` component of its Picard functor. If `g ≤ d`, then `γ_d : H ⟶ Pic^d` is surjective. -/
theorem surjective_abelMap (hdg : genus (B.inclusion.map f) ≤ d) :
    Surjective (B.inclusion.map (abelMap B hX hk f hP H hH R).left) := by
  refine ⟨fun p => ?_⟩
  let Y := B.inclusion.obj Pd.left
  have hK : B.Contains (Spec (Y.residueField p)) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (Y.fromSpecResidueField p))
      Pd.left.property
  let T : BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (Y.fromSpecResidueField p ≫ B.inclusion.map Pd.hom) :
      B.obj hK ⟶ B.obj hk)
  let a : T ⟶ Pd := Over.homMk (ObjectProperty.homMk (Y.fromSpecResidueField p)) rfl
  obtain ⟨L, hL, hcls, hχ⟩ := exists_isInvertible_of_mem B hX hk f σ hσ hP T (R.homEquiv a)
  let K := Y.residueField p
  let fT : baseChange B hX hk f T ⟶ Spec (.of K) :=
    pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)
  let : Algebra k K := (Spec.preimage (B.inclusion.map T.hom)).hom.toAlgebra
  have hZ : IsPullback (pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom)) fT
      (B.inclusion.map f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    have : Spec.map (CommRingCat.ofHom (algebraMap k K)) = B.inclusion.map T.hom :=
      Spec.map_preimage _
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have := isProper_of_isPullback (B.inclusion.map f) _ fT hZ
  have := isIntegral_of_isPullback (B.inclusion.map f) _ fT hZ
  have := isIso_globalSections_of_isPullback (B.inclusion.map f) _ fT hZ
  have hdim : topologicalKrullDim (baseChange B hX hk f T) ≤ 1 :=
    (topologicalKrullDim_eq_one_of_isPullback (B.inclusion.map f) _ fT hZ).le
  have hgen : genus fT = genus (B.inclusion.map f) :=
    genus_baseChange k K _ fT (B.inclusion.map f) hZ
  have := Stacks.Picard.isQuasicoherent_of_isInvertible L hL
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible
      (baseChange B hX hk f T).presheaf (baseChange B hX hk f T).ringCatSheaf.2 L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hL
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  have hdeg : invertibleCurveDegree K fT hdim L = d := by
    rw [invertibleCurveDegree_eq_of_fibreCohomology fT hdim L s (hχ s), hgen]
    ring
  obtain ⟨D, d', hD, ⟨e⟩, hflf, hd'⟩ :=
    exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree K fT hdim L
      (by rw [hdeg, hgen]; exact_mod_cast hdg)
  obtain rfl : d' = d := by
    rw [hdeg] at hd'
    exact_mod_cast hd'
  obtain ⟨b, hba⟩ := exists_comp_abelMap_eq B hX hk f hP H hH R a ⟨D, hflf⟩ (by
    rw [← hcls, Stacks.Hilbert.HilbertFamily.picardClass_eq _ hD]
    congr 1
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e.symm⟩)
  refine ⟨B.inclusion.map b.left s, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Over.comp_left, hba]
  exact Scheme.fromSpecResidueField_apply (X := Y) p s

end Stacks.AbelMap

end
