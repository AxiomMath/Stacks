module

public import Mathlib.Algebra.Order.SuccPred.WithBot
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.ZeroDimensional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusBirational
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.NormalizationComponents.PicardDisjointUnion
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# The `ℓ`-torsion of the Picard group of a normalization, from smooth projective curves

Let `K` be an algebraically closed field and let `ℓ` be a prime.  This file reduces the
statement

`dim_{F_ℓ} Pic(Z^ν)[ℓ] = 2 g_geom(Z/K)`,

for `Z` a proper scheme of dimension at most one over `K` and `Z^ν` its normalization, to the
statement `Pic(C)[ℓ] ≅ (ℤ/ℓℤ)^{⊕2g(C)}` for every smooth projective curve `C` over `K`, which is
clause (1) of [Stacks, Tag 0C1Z] at `n = ℓ` when `ℓ` is invertible in `K`.  The latter is the
hypothesis `hsm` of the theorems below.

## Main results

* `AlgebraicGeometry.finrank_picardTorsion_eq_zero_of_topologicalKrullDim_le_zero`: the Picard
  group of a proper scheme of dimension at most zero over a field has trivial `ℓ`-torsion.
* `AlgebraicGeometry.finiteDimensional_finrank_torsionBy_of_addEquiv`: an identification
  `A[ℓ] ≅ (ℤ/ℓℤ)^{⊕m}` computes the `F_ℓ`-dimension of `A[ℓ]`.
* `AlgebraicGeometry.finrank_picardTorsion_eq_two_mul_genus_of_isNormal`: for a normal proper
  scheme `N` of dimension at most one over `K`, `dim_{F_ℓ} Pic(N)[ℓ] = 2 g(N)`.
* `AlgebraicGeometry.rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus`:
  `dim_{F_ℓ} Pic(Z^ν)[ℓ] = 2 g_geom(Z/K)`.

## References

* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Picard (ofScheme)
open Stacks.AlgebraicGeometry.ComponentDegrees
  (discreteTopology_of_isProper_of_topologicalKrullDim_le_zero)

universe u

namespace AlgebraicGeometry

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### The `ℓ`-torsion of the Picard group in dimension zero -/

/-- **The `ℓ`-torsion of the Picard group of a proper scheme of dimension at most zero over a
field is zero-dimensional**, and in particular finite-dimensional. -/
theorem finrank_picardTorsion_eq_zero_of_topologicalKrullDim_le_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hdim : topologicalKrullDim (X : Type u) ≤ 0) (ℓ : ℕ) [Fact ℓ.Prime] :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) = 0 := by
  have := discreteTopology_of_isProper_of_topologicalKrullDim_le_zero k g hdim
  have := Stacks.Picard.subsingleton_ofScheme_of_discreteTopology X
  have : Subsingleton (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) :=
    ⟨fun _ _ ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  have : Finite (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) := Finite.of_subsingleton
  exact ⟨Module.Finite.of_finite, Module.finrank_zero_of_subsingleton⟩

/-! ### From `A[ℓ] ≅ (ℤ/ℓℤ)^{⊕m}` to the `F_ℓ`-dimension -/

/-- **An identification `A[ℓ] ≅ (ℤ/ℓℤ)^{⊕m}` computes `dim_{F_ℓ} A[ℓ] = m`.**  The `ℓ`-torsion is
taken as `Submodule.torsionBy ℤ` in the hypothesis and as `AddSubgroup.torsionBy` with its
`F_ℓ`-structure in the conclusion. -/
theorem finiteDimensional_finrank_torsionBy_of_addEquiv {A : Type*} [AddCommGroup A] (ℓ : ℕ)
    [Fact ℓ.Prime] (m : ℕ)
    (e : Submodule.torsionBy ℤ A (ℓ : ℤ) ≃+ (Fin m → ZMod ℓ)) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) = m := by
  let f : AddSubgroup.torsionBy A (ℓ : ℤ) →+ (Fin m → ZMod ℓ) :=
    { toFun := fun x ↦ e ⟨x.1, x.2⟩
      map_zero' := map_zero e
      map_add' := fun x y ↦ map_add e ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ }
  have hf : Function.Bijective f :=
    ⟨fun _ _ hxy ↦ Subtype.ext (congrArg Subtype.val (e.injective hxy)),
      fun z ↦ let ⟨x, hx⟩ := e.surjective z; ⟨⟨x.1, x.2⟩, hx⟩⟩
  let e' := LinearEquiv.ofBijective (f.toZModLinearMap ℓ) hf
  exact ⟨LinearEquiv.finiteDimensional e'.symm,
    e'.finrank_eq.trans (Module.finrank_fin_fun (ZMod ℓ))⟩

/-! ### A normal proper scheme of dimension at most one -/

/-- **`dim_{F_ℓ} Pic(N)[ℓ] = 2 g(N)` for a normal proper scheme `N` of dimension at most one over
an algebraically closed field `K`**, given `Pic(C)[ℓ] ≅ (ℤ/ℓℤ)^{⊕2g(C)}` for every smooth
projective curve `C` over `K` (`hsm`), `ℓ` being a prime invertible in `K`. -/
theorem finrank_picardTorsion_eq_two_mul_genus_of_isNormal (K : Type u) [Field K]
    [IsAlgClosed K] {N : Scheme.{u}} (q : N ⟶ Spec (.of K)) [IsProper q] [IsNormal N]
    (hdim : topologicalKrullDim (N : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (hsm : ∀ (C : Scheme.{u}) (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
      [IsProjectiveVariety K c], IsUnit (ℓ : K) →
      Nonempty (Submodule.torsionBy ℤ (ofScheme C) (ℓ : ℤ) ≃+ (Fin (2 * genus c) → ZMod ℓ))) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme N) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme N) (ℓ : ℤ)) = 2 * genus q := by
  classical
  have : IsNoetherian N :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q }
  have : NoetherianSpace (N : Type u) := inferInstance
  have : Finite (_root_.ConnectedComponents (N : Type u)) :=
    NoetherianSpace.finite_connectedComponents (N : Type u)
  let : Fintype (_root_.ConnectedComponents (N : Type u)) := Fintype.ofFinite _
  obtain ⟨U, hUclopen, hUconn, hUmem, hUmk⟩ :
      ∃ U : _root_.ConnectedComponents (N : Type u) → N.Opens,
        (∀ c, IsClopen (U c : Set N)) ∧ (∀ c, _root_.IsConnected (U c : Set N)) ∧
          (∀ x : N, x ∈ U (_root_.ConnectedComponents.mk x)) ∧
          ∀ (c) (x : N), x ∈ U c → _root_.ConnectedComponents.mk x = c :=
    ⟨fun c ↦ ⟨connectedComponent c.out,
        (isClopen_connectedComponent_of_finite_connectedComponents c.out).2⟩,
      fun c ↦ isClopen_connectedComponent_of_finite_connectedComponents c.out,
      fun _ ↦ isConnected_connectedComponent,
      fun _ ↦ _root_.ConnectedComponents.coe_eq_coe'.mp (Quotient.out_eq _).symm,
      fun c _ hx ↦ (_root_.ConnectedComponents.coe_eq_coe'.mpr hx).trans (Quotient.out_eq c)⟩
  have hci : ∀ c, IsClosedImmersion (U c).ι := fun c ↦
    IsClosedImmersion.of_isPreimmersion (U c).ι (by
      rw [Scheme.Opens.range_ι]; exact (hUclopen c).1)
  have hfin : ∀ c, IsFinite (U c).ι := fun c ↦
    (IsClosedImmersion.iff_isFinite_and_mono (U c).ι).mp (hci c) |>.1
  have hpi : ∀ c, IsProper ((U c).ι ≫ q) := fun _ ↦ inferInstance
  have hconn : ∀ c, ConnectedSpace ((U c).toScheme : Type u) := fun c ↦
    isConnected_iff_connectedSpace.mp (hUconn c)
  have hUdim : ∀ c, topologicalKrullDim ((U c).toScheme : Type u) ≤ 1 := fun c ↦
    (U c).ι.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hcover : IsOpenCover U :=
    eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨_root_.ConnectedComponents.mk x, hUmem x⟩
  have hdisj : Pairwise (Function.onFun Disjoint U) := fun c d hcd ↦
    disjoint_iff.mpr (eq_bot_iff.mpr fun x hx ↦
      absurd ((hUmk c x hx.1).symm.trans (hUmk d x hx.2)) hcd)
  have hrange : ∀ c, Set.range (U c).ι.base = (U c : Set N) := fun c ↦ Scheme.Opens.range_ι _
  have hdisjset : Pairwise fun c d ↦
      Disjoint (Set.range (U c).ι.base) (Set.range (U d).ι.base) := by
    intro c d hcd
    simp only [hrange]
    exact Set.disjoint_left.mpr fun x hx hx' ↦
      absurd ((hUmk c x hx).symm.trans (hUmk d x hx')) hcd
  have hcoverpt : ∀ y : N, ∃ c x, (U c).ι.base x = y := fun y ↦
    ⟨_root_.ConnectedComponents.mk y, ⟨y, hUmem y⟩, rfl⟩
  have hcomp : ∀ c, FiniteDimensional (ZMod ℓ)
      (AddSubgroup.torsionBy (ofScheme (U c).toScheme) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme (U c).toScheme) (ℓ : ℤ)) =
        2 * genus ((U c).ι ≫ q) := by
    intro c
    by_cases hz : topologicalKrullDim ((U c).toScheme : Type u) ≤ 0
    · rw [genus_eq_zero_of_topologicalKrullDim_le_zero K ((U c).ι ≫ q) hz]
      exact finrank_picardTorsion_eq_zero_of_topologicalKrullDim_le_zero K ((U c).ι ≫ q) hz ℓ
    · have hone : topologicalKrullDim ((U c).toScheme : Type u) = 1 :=
        le_antisymm (hUdim c) ((WithBot.one_le_iff_pos _).mpr (lt_of_not_ge hz))
      have : IsLocallyNoetherian (U c).toScheme :=
        LocallyOfFiniteType.isLocallyNoetherian ((U c).ι ≫ q)
      have : IsIntegral (U c).toScheme := Stacks.Chow.isIntegral_of_connectedSpace_of_isNormal
      have hp : IsProper ((U c).ι ≫ q) := hpi c
      have := hp.toUniversallyClosed
      have hqc : QuasiCompact ((U c).ι ≫ q) :=
        AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _
      have : IsVariety K ((U c).ι ≫ q) :=
        { toIsIntegral := inferInstance
          toIsSeparated := hp.toIsSeparated
          toLocallyOfFiniteType := hp.toLocallyOfFiniteType
          toQuasiCompact := hqc }
      have : IsCurve K ((U c).ι ≫ q) := { topologicalKrullDim_eq_one := hone }
      have : Smooth ((U c).ι ≫ q) := smooth_of_isRegular_of_perfectField K _
        (isRegular_of_isNormal_of_topologicalKrullDim_le_one _ hone.le)
      have : IsProjectiveVariety K ((U c).ι ≫ q) :=
        { isProjective := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper
            (f := (U c).ι ≫ q)).mpr
            ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral _ hone,
              inferInstance⟩ }
      obtain ⟨e⟩ := hsm (U c).toScheme ((U c).ι ≫ q) hℓ
      exact finiteDimensional_finrank_torsionBy_of_addEquiv ℓ _ e
  refine ⟨finiteDimensional_picardTorsion_of_pairwise_disjoint U hcover hdisj ℓ
    fun c ↦ (hcomp c).1, ?_⟩
  rw [finrank_picardTorsion_eq_sum_of_pairwise_disjoint U hcover hdisj ℓ fun c ↦ (hcomp c).1,
    genus_eq_sum_of_disjoint_cover (fun c ↦ (U c).ι) hcoverpt hdisjset q, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦ (hcomp c).2

/-! ### The normalization -/

/-- **`dim_{F_ℓ} Pic(Z^ν)[ℓ] = 2 g_geom(Z/K)`** for a proper scheme `Z` of dimension at most one
over an algebraically closed field `K` and its normalization `Z^ν`, given
`Pic(C)[ℓ] ≅ (ℤ/ℓℤ)^{⊕2g(C)}` for every smooth projective curve `C` over `K` (`hsm`), `ℓ` being a
prime invertible in `K`. -/
theorem rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus (K : Type u)
    [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (r : Z ⟶ Spec (.of K)) [IsProper r]
    (hdim : topologicalKrullDim (Z : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (hsm : ∀ (C : Scheme.{u}) (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
      [IsProjectiveVariety K c], IsUnit (ℓ : K) →
      Nonempty (Submodule.torsionBy ℤ (ofScheme C) (ℓ : ℤ) ≃+ (Fin (2 * genus c) → ZMod ℓ))) :
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy
        (ofScheme (normalizationSchemeOverField K r)) (ℓ : ℤ)) =
      ((2 * geometricGenus K r : ℕ) : Cardinal.{u + 1}) := by
  have : LocallyOfFiniteType r := IsProper.toLocallyOfFiniteType
  have := isFinite_normalizationOverField K r
  have := isDominant_normalizationOverField K r
  have : IsProper (normalizationOverField K r ≫ r) := isProper_normalizationOverField_comp K r
  have : IsNormal (normalizationSchemeOverField K r) :=
    Scheme.isNormal_normalizationScheme Z (finite_irreducibleComponents_of_locallyOfFiniteType K r)
  have hdimN : topologicalKrullDim (normalizationSchemeOverField K r : Type u) ≤ 1 :=
    (topologicalKrullDim_eq_of_isFinite_of_isDominant (normalizationOverField K r)).trans_le hdim
  obtain ⟨hfd, hfr⟩ := finrank_picardTorsion_eq_two_mul_genus_of_isNormal K
    (normalizationOverField K r ≫ r) hdimN ℓ hℓ hsm
  rw [← Module.finrank_eq_rank, hfr,
    geometricGenus_eq_genus_normalizationOverField_of_dim_le_one K r hdim]

end AlgebraicGeometry

end
