module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClassGroupPicardBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDivisorSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionKummer
public import StacksFrontier.GroupTheory.FiniteAbelian.NsmulComparison

/-!
# `μ_ℓ`-cohomology of a smooth curve under extension of the algebraically closed base field

Let `X` be a smooth curve over an algebraically closed field `k`, `k'/k` an algebraically closed
extension and `ℓ ∈ k^*`. Restriction `H^q(X, μ_ℓ) → H^q(X_{k'}, μ_ℓ)` is compared through the
Kummer sequence with restriction on `H^{q-1}(𝐆_m)` and `H^q(𝐆_m)`; the latter is, through
`H¹(𝐆_m) ≅ Cl`, the class group map `curveClassGroupScalarExtensionMap`.

## Main results

* `Stacks.EtaleCohomology.bijective_rootsOfUnityRestriction_scalarExtension_of_isProper`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.EtaleCohomology

open Stacks.Kummer

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### Global units of a proper curve -/

/-- **`H⁰(Y, 𝐆_m)` is divisible** on a smooth proper curve over an algebraically closed field:
the global units are the nonzero constants. -/
theorem exists_nsmul_eq_sheafH_zero_multiplicativeSheaf_of_isProper {K : Type u} [Field K]
    [IsAlgClosed K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [IsCurve K q] [Smooth q] [IsProper q]
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (a : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} Y) 0) :
    ∃ d, ℓ • d = a := by
  let e := Sheaf.H.equiv₀ (multiplicativeSheaf.{u, u + 1} Y) (isTerminalEtaleMkId Y)
  obtain ⟨w₀, hw⟩ := ofUnit_surjective.{u, u + 1} (e a)
  let w : (Γ(Y, ⊤))ˣ := w₀
  have := isIso_globalSections_of_isCurve_of_isProper q
  let φ : K →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop).hom
  let ψ : K ≃+* Γ(Y, ⊤) := RingEquiv.ofBijective φ
    (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop))
  let c : Kˣ := Units.map ψ.symm.toMonoidHom w
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (c : K) (Nat.pos_of_ne_zero hℓ)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← ht, zero_pow hℓ])
  let s : (Γ(Y, ⊤))ˣ := Units.map ψ.toMonoidHom (Units.mk0 t ht0)
  have hs : s ^ ℓ = w := Units.ext (by
    change ψ t ^ ℓ = (w : Γ(Y, ⊤))
    rw [← map_pow, ht]
    exact ψ.apply_symm_apply _)
  refine ⟨e.symm (ofUnit.{u, u + 1} (U := Scheme.Etale.mk (𝟙 Y)) s), ?_⟩
  rw [← map_nsmul, ← e.symm_apply_apply a, ← hw]
  refine congrArg e.symm ?_
  change ULift.up (ℓ • Additive.ofMul s) = ULift.up (Additive.ofMul w)
  rw [← ofMul_pow, hs]

/-! ### The class group map -/

section ClassGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

/-- The class group map is restriction on `H¹(𝐆_m)` read through `H¹(𝐆_m) ≅ Cl`. -/
theorem curveClassGroupScalarExtensionMap_apply (c : curveClassGroup g) :
    curveClassGroupScalarExtensionMap g k' c =
      sheafHOneMultiplicativeAddEquivClosedPointClassGroup (scalarExtensionSnd k k' g)
        (multiplicativeRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) 1
          ((sheafHOneMultiplicativeAddEquivClosedPointClassGroup g).symm c)) :=
  rfl

/-- Restriction on `H¹(𝐆_m)` is the class group map read through `H¹(𝐆_m) ≅ Cl`. -/
theorem multiplicativeRestriction_one_eq
    (b : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    multiplicativeRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) 1 b =
      (sheafHOneMultiplicativeAddEquivClosedPointClassGroup (scalarExtensionSnd k k' g)).symm
        (curveClassGroupScalarExtensionMap g k'
          (sheafHOneMultiplicativeAddEquivClosedPointClassGroup g b)) := by
  rw [curveClassGroupScalarExtensionMap_apply, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-- Restriction on `H¹(𝐆_m)`, read through `H¹(𝐆_m) ≅ Cl`, is the class group map. -/
private theorem sheafHOne_multiplicativeRestriction_eq_curveClassGroupScalarExtensionMap
    (b : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    sheafHOneMultiplicativeAddEquivClosedPointClassGroup (scalarExtensionSnd k k' g)
        (multiplicativeRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) 1 b) =
      curveClassGroupScalarExtensionMap g k'
        (sheafHOneMultiplicativeAddEquivClosedPointClassGroup g b) := by
  rw [multiplicativeRestriction_one_eq, AddEquiv.apply_symm_apply]

variable [IsProper g]

/-- The class group map preserves degrees. -/
theorem curveClassGroupDegree_curveClassGroupScalarExtensionMap (c : curveClassGroup g) :
    curveClassGroupDegree (scalarExtensionSnd k k' g) (curveClassGroupScalarExtensionMap g k' c) =
      curveClassGroupDegree g c := by
  have := isLocallyNoetherian_of_isCurve g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  have h : (curveClassGroupDegree (scalarExtensionSnd k k' g)).comp
      (curveClassGroupScalarExtensionMap g k') = curveClassGroupDegree g := by
    refine AddMonoidHom.eq_of_eqOn_dense (closure_range_closedPointClassGroup_single X) ?_
    rintro _ ⟨x, rfl⟩
    rw [AddMonoidHom.comp_apply, curveClassGroupScalarExtensionMap_single, curveClassGroupDegree_mk,
      curveClassGroupDegree_mk, Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  exact DFunLike.congr_fun h c

/-- On a smooth proper curve every class is congruent modulo `ℓ` to its degree times the class of
a given closed point. -/
theorem exists_sub_degree_nsmul_curveClassGroup {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [IsCurve K q] [Smooth q] [IsProper q] {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : K)) (y₀ : closedPoints Y) (c : curveClassGroup q) :
    ∃ d, c - curveClassGroupDegree q c •
      (QuotientAddGroup.mk (Finsupp.single y₀ (1 : ℤ)) : curveClassGroup q) = ℓ • d := by
  have := isLocallyNoetherian_of_isCurve q
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve q
  refine AddMonoidHom.exists_sub_nsmul_eq_of_closure_eq_top _ ℓ
    (closure_range_closedPointClassGroup_single Y) _ ?_ ?_ c
  · rintro _ ⟨y, rfl⟩
    rw [curveClassGroupDegree_mk, Finsupp.sum_single_index rfl]
  · rintro _ ⟨y, rfl⟩
    exact exists_nsmul_eq_sub_curveClassGroup_single q hℓ y y₀

end ClassGroup

/-! ### Proper curves -/

section Proper

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

omit [IsAlgClosed k] [Smooth g] in
include g in
/-- A smooth curve over a field has a closed point. -/
theorem nonempty_closedPoints_of_isCurve [IsProper g] : Nonempty (closedPoints X) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := X))
  exact ⟨⟨x, hx⟩⟩

/-- Restriction of `μ_ℓ`-cohomology to `X_{k'}` is bijective in degree one. -/
theorem bijective_rootsOfUnityRestriction_scalarExtension_one [IsProper g] {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : k)) :
    Function.Bijective
      (rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) ℓ 1) := by
  have hℓ0 : ℓ ≠ 0 := ne_zero_of_isUnit_natCast hℓ
  set φ := curveClassGroupScalarExtensionMap g k'
  have hφ := curveClassGroupScalarExtensionMap_single g k'
  set e := sheafHOneMultiplicativeAddEquivClosedPointClassGroup g
  set e' := sheafHOneMultiplicativeAddEquivClosedPointClassGroup (scalarExtensionSnd k k' g)
  refine bijective_rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) hℓ0
    (isUnit_natCast_globalSections_of_isUnit g hℓ) 0
    (fun a _ _ => exists_nsmul_eq_sheafH_zero_multiplicativeSheaf_of_isProper g hℓ0 a)
    (fun a' => ?_) (fun b _ hb => ?_) (fun b' hb' => ?_)
  · obtain ⟨d', hd'⟩ := exists_nsmul_eq_sheafH_zero_multiplicativeSheaf_of_isProper
      (scalarExtensionSnd k k' g) hℓ0 a'
    exact ⟨0, d', by rw [map_zero, zero_add, hd']⟩
  · have h1 : φ (e b) = 0 := by
      rw [← sheafHOne_multiplicativeRestriction_eq_curveClassGroupScalarExtensionMap, hb, map_zero]
    have h2 : e b = 0 := (injective_of_map_single_eq g k' φ hφ) (h1.trans (map_zero φ).symm)
    exact e.injective (h2.trans (map_zero e).symm)
  · obtain ⟨⟨c, hc⟩, hcc⟩ := (bijective_torsion_of_map_single_eq g k' hℓ φ hφ).2
      ⟨e' b', by rw [← map_nsmul, hb', map_zero]⟩
    refine ⟨e.symm c, by rw [← map_nsmul, hc, map_zero], ?_⟩
    apply e'.injective
    rw [sheafHOne_multiplicativeRestriction_eq_curveClassGroupScalarExtensionMap,
      AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val hcc

/-- Restriction of `μ_ℓ`-cohomology to `X_{k'}` is bijective in degree two. -/
theorem bijective_rootsOfUnityRestriction_scalarExtension_two [IsProper g] {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : k)) :
    Function.Bijective
      (rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) ℓ 2) := by
  have hℓ' : IsUnit (ℓ : k') := by simpa using hℓ.map (algebraMap k k')
  obtain ⟨x₀⟩ := nonempty_closedPoints_of_isCurve g
  set φ := curveClassGroupScalarExtensionMap g k'
  have hφ := curveClassGroupScalarExtensionMap_single g k'
  set e := sheafHOneMultiplicativeAddEquivClosedPointClassGroup g
  set e' := sheafHOneMultiplicativeAddEquivClosedPointClassGroup (scalarExtensionSnd k k' g)
  have hQ := AddMonoidHom.nsmul_comparison_of_degree φ (curveClassGroupDegree g)
    (curveClassGroupDegree (scalarExtensionSnd k k' g)) ℓ
    (curveClassGroupDegree_curveClassGroupScalarExtensionMap g k')
    (QuotientAddGroup.mk (Finsupp.single x₀ (1 : ℤ)))
    (exists_sub_degree_nsmul_curveClassGroup g hℓ x₀)
    (fun c' => by
      rw [hφ x₀]
      exact exists_sub_degree_nsmul_curveClassGroup (scalarExtensionSnd k k' g) hℓ'
        (scalarExtensionClosedPoint g k' x₀) c')
  have h2X := subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ.{u, u + 1, u + 1} g 2
    le_rfl
  have h2X' := subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ.{u, u + 1, u + 1}
    (scalarExtensionSnd k k' g) 2 le_rfl
  refine bijective_rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g)
    (ne_zero_of_isUnit_natCast hℓ) (isUnit_natCast_globalSections_of_isUnit g hℓ) 1
    (fun a z' h => ?_) (fun a' => ?_) (fun b _ _ => Subsingleton.elim _ _)
    (fun b' _ => ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩)
  · obtain ⟨d, hd⟩ := hQ.1 (e a) (e' z') (by
      rw [← sheafHOne_multiplicativeRestriction_eq_curveClassGroupScalarExtensionMap, ← h,
        map_nsmul])
    exact ⟨e.symm d, by rw [← map_nsmul, hd, AddEquiv.symm_apply_apply]⟩
  · obtain ⟨c, d', hcd⟩ := hQ.2 (e' a')
    refine ⟨e.symm c, e'.symm d', ?_⟩
    apply e'.injective
    rw [map_add, sheafHOne_multiplicativeRestriction_eq_curveClassGroupScalarExtensionMap,
      map_nsmul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← hcd]

/-- **Restriction of `μ_ℓ`-cohomology to `X_{k'}` is bijective in every positive degree** for a
smooth proper curve `X` over an algebraically closed field `k`, `ℓ ∈ k^*`. -/
theorem bijective_rootsOfUnityRestriction_scalarExtension_of_isProper [IsProper g] {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : k)) (q : ℕ) (hq : 1 ≤ q) :
    Function.Bijective
      (rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) ℓ q) := by
  obtain rfl | rfl | hq : q = 1 ∨ q = 2 ∨ 3 ≤ q := by omega
  · exact bijective_rootsOfUnityRestriction_scalarExtension_one g k' hℓ
  · exact bijective_rootsOfUnityRestriction_scalarExtension_two g k' hℓ
  have hℓ' : IsUnit (ℓ : k') := by simpa using hℓ.map (algebraMap k k')
  have := subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve.{u, u + 1, u + 1} g hℓ q
    (by omega)
  have := subsingleton_sheafH_rootsOfUnitySheaf_of_smoothCurve.{u, u + 1, u + 1}
    (scalarExtensionSnd k k' g) hℓ' q (by omega)
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

end Proper

end Stacks.EtaleCohomology

end
