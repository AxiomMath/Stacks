module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardFunctorRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowSurjective

/-!
# Divisibility and torsion of `Pic⁰` of a smooth projective curve

Let `X` be a smooth proper curve over an algebraically closed field `k` and `n` an integer
invertible in `k`. Through the Jacobian `J = Pic^0_{X/k}`, an abelian variety whose group of
rational points is `Pic⁰(X)` (`Stacks.PicardFunctor.jacobianPointsAddEquiv`), the properties of
abelian varieties of [Stacks, Tag 03RP] for `n ∈ k^*` transfer to `Pic⁰(X)`:

* (A) `Pic⁰(X)` is `n`-divisible;
* (B') `Pic(X)[n] = Pic⁰(X)[n]` is finite;
* (B'') for every field extension `K/k`, pullback `Pic(X)[n] ⟶ Pic(X_K)[n]` is bijective.

The curve is proper, hence projective
(`AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve`),
geometrically irreducible and has a rational point (`k` is algebraically closed); the site in
which the Picard functor is formed is chosen inside the proofs
(`AlgebraicGeometry.BigFppfSite.exists_containing`), so nothing of it appears in the statements.

## Main results

* `AlgebraicGeometry.exists_nsmul_eq_of_mem_picardDegreeZero` (A).
* `AlgebraicGeometry.finite_schemePicard_torsion` (B').
* `AlgebraicGeometry.bijective_schemePicardPullbackHom_torsion` (B'').
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
  [IsCurve k q] [Smooth q] [IsProper q]

/-- The data of the Jacobian of a smooth proper curve over an algebraically closed field, in a
big fppf site containing `Spec K`: it is an abelian variety with `J(k) = Pic⁰(X)` and
`J_K(K) = Pic⁰(X_K)` compatibly with base change. -/
theorem exists_jacobian_data (K : Type u) [Field K] [Algebra k K]
    (hdim : topologicalKrullDim Y ≤ 1) :
    ∃ (J : Over (Spec (.of k))) (_ : GrpObj J) (_ : IsAbelianVariety k J)
      (E : Additive (𝟙_ (Over (Spec (.of k))) ⟶ J) ≃+ picardDegreeZero k q hdim)
      (hdimK : topologicalKrullDim
        ((pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) ≤ 1)
      (_ : IsProper (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (_ : IsCurve K (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (EK : Additive (𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj J) ≃+
        picardDegreeZero K (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hdimK),
      ∀ p, (EK (Stacks.Groupoids.pointBaseChange J K p) : schemePicard _) =
        schemePicardPullbackHom (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (E p : schemePicard Y) := by
  let S₀ : Set Scheme.{u} := {Y, Spec (.of k), Spec (.of K)}
  have : Small.{u} S₀ := by
    dsimp [S₀]
    infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  have hX : B.Contains Y := hB Y (by simp [S₀])
  have hk : B.Contains (Spec (.of k)) := hB _ (by simp [S₀])
  have hK : B.Contains (Spec (.of K)) := hB _ (by simp [S₀])
  let f : B.obj hX ⟶ B.obj hk := ObjectProperty.homMk q
  have : IsCurve k (B.inclusion.map f) := ‹IsCurve k q›
  have : Smooth (B.inclusion.map f) := ‹Smooth q›
  have : IsProper (B.inclusion.map f) := ‹IsProper q›
  have : GeometricallyIrreducible (B.inclusion.map f) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k Y q
  have hprojM : IsProjectiveMorphism (B.inclusion.map f) :=
    isProjectiveMorphism_of_isProper_of_isCurve k q
  have : IsProjectiveVariety k (B.inclusion.map f) :=
    (isProjectiveVariety_iff_isProjectiveMorphism k q).2 hprojM
  obtain ⟨σ, hσ⟩ := Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed k q
  have := Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed k B hX hk f hprojM
  have := isAbelianVariety_jacobian B hX hk f σ hσ
  exact ⟨(jacobianGrp B hX hk f σ hσ).X, inferInstance, inferInstance,
    jacobianPointsAddEquiv B hX hk f σ hσ hdim, topologicalKrullDim_fieldCurve_le B hX hk f K hK,
    inferInstanceAs (IsProper (fieldCurve B hX hk f K hK)),
    inferInstanceAs (IsCurve K (fieldCurve B hX hk f K hK)),
    jacobianFieldPointsAddEquiv B hX hk f σ hσ K hK,
    jacobianFieldPointsAddEquiv_pointBaseChange B hX hk f σ hσ K hK hdim⟩

/-- **Stacks Project, Tag 03RP (4) for `Pic⁰`, ingredient (A) of Case I of Tag 0A5B**: for a
smooth proper curve over an algebraically closed field `k` and `n` invertible in `k`, every
degree-zero line bundle is the `n`-th power of a degree-zero line bundle. -/
theorem exists_nsmul_eq_of_mem_picardDegreeZero (hdim : topologicalKrullDim Y ≤ 1) {n : ℕ}
    (hn : IsUnit (n : k)) (x : picardDegreeZero k q hdim) :
    ∃ y : picardDegreeZero k q hdim, n • y = x := by
  obtain ⟨J, _, _, E, -⟩ := exists_jacobian_data q k hdim
  obtain ⟨b, hb⟩ := Stacks.Groupoids.exists_nsmul_eq_of_isUnit J n hn (E.symm x)
  exact ⟨E b, by rw [← map_nsmul, hb, AddEquiv.apply_symm_apply]⟩

include q in
/-- **Ingredient (B') of Case I of Tag 0A5B**: for a smooth proper curve over an algebraically
closed field `k` and `n` invertible in `k`, the `n`-torsion of the Picard group is finite (it is
the `n`-torsion of `Pic⁰`, the `n`-torsion of the rational points of the Jacobian). -/
theorem finite_schemePicard_torsion {n : ℕ} (hn : IsUnit (n : k)) :
    Finite {x : schemePicard Y // n • x = 0} := by
  have hdim : topologicalKrullDim Y ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := q)).le
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨J, _, _, E, -⟩ := exists_jacobian_data q k hdim
  have := Stacks.Groupoids.finite_torsionBy_of_isUnit J n hn
  exact Finite.of_injective
    (β := Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) (n : ℤ))
    (fun x => ⟨E.symm ⟨x.1, mem_picardDegreeZero_of_nsmul_eq_zero k q hdim
      hn0 x.1 x.2⟩, by
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← map_nsmul, AddEquiv.map_eq_zero_iff]
        exact Subtype.ext x.2⟩)
    fun x y hxy => Subtype.ext <| by
      simpa only [AddEquiv.apply_symm_apply] using congrArg (fun z => (E z.1 : schemePicard Y)) hxy

/-- **Ingredient (B'') of Case I of Tag 0A5B**: for a smooth proper curve `X` over an
algebraically closed field `k`, a field extension `K/k` and `n` invertible in `k`, pullback of
line bundles along `X_K ⟶ X` is a bijection `Pic(X)[n] ⟶ Pic(X_K)[n]`. -/
theorem bijective_schemePicardPullbackHom_torsion (K : Type u) [Field K] [Algebra k K] {n : ℕ}
    (hn : IsUnit (n : k)) :
    Function.Bijective (fun x : {x : schemePicard Y // n • x = 0} =>
      (⟨schemePicardPullbackHom (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          x.1, by rw [← map_nsmul, x.2, map_zero]⟩ :
        {y : schemePicard (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) //
          n • y = 0})) := by
  have hdim : topologicalKrullDim Y ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := q)).le
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨J, _, _, E, hdimK, _, _, EK, hEK⟩ := exists_jacobian_data q K hdim
  constructor
  · intro x y hxy
    have hxy' := congrArg Subtype.val hxy
    simp only at hxy'
    set px := E.symm ⟨x.1, mem_picardDegreeZero_of_nsmul_eq_zero k q hdim hn0 x.1 x.2⟩
    set py := E.symm ⟨y.1, mem_picardDegreeZero_of_nsmul_eq_zero k q hdim hn0 y.1 y.2⟩
    have hx : (E px : schemePicard Y) = x.1 := by simp [px]
    have hy : (E py : schemePicard Y) = y.1 := by simp [py]
    rw [← hx, ← hy, ← hEK, ← hEK] at hxy'
    have h₁ := Stacks.Groupoids.pointBaseChange_injective J K (EK.injective (Subtype.ext hxy'))
    exact Subtype.ext (by rw [← hx, ← hy, h₁])
  · rintro ⟨z, hz⟩
    set w := EK.symm ⟨z, mem_picardDegreeZero_of_nsmul_eq_zero K _ hdimK hn0 z hz⟩
    have hw : w ∈ Submodule.torsionBy ℤ _ (n : ℤ) := by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← map_nsmul, AddEquiv.map_eq_zero_iff]
      exact Subtype.ext hz
    obtain ⟨⟨p, hp⟩, hpw⟩ := (Stacks.Groupoids.torsionPointBaseChange_bijective J K n hn).2 ⟨w, hw⟩
    have hpw' : Stacks.Groupoids.pointBaseChange J K p = w := congrArg Subtype.val hpw
    refine ⟨⟨E p, ?_⟩, Subtype.ext ?_⟩
    · rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hp
      rw [← AddSubgroup.coe_nsmul, ← map_nsmul, hp, map_zero]
      rfl
    · change schemePicardPullbackHom _ (E p : schemePicard Y) = z
      rw [← hEK, hpw']
      simp [w]

end AlgebraicGeometry

end
