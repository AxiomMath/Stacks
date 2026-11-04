module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CoefficientUniverseReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionAffine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective

/-!
# Cohomology of `𝐙/ℓ` on a smooth curve under extension of the algebraically closed base field

Let `X` be a smooth curve over an algebraically closed field `k`, `k'/k` an algebraically closed
extension, `ℓ ∈ k^*` and `E` an abelian group cyclic of order `ℓ`. Restriction of the cohomology of
the constant sheaf `E` to `X_{k'}` is bijective in a degree as soon as restriction of
`μ_ℓ`-cohomology, moved along `π⁻¹ μ_ℓ ≅ μ_ℓ`, is: on `X` the constant sheaf `E` is isomorphic to
`μ_ℓ` since `k` is algebraically closed.

## Main results

* `bijective_etaleCohomologyRestrictionMap_rootsOfUnitySheaf_of_bijective`: restriction on `μ_n` is
  bijective once its composite with `π⁻¹ μ_n ≅ μ_n` is.
* `bijective_etaleCohomologyRestrictionMap_constantSheaf_of_rootsOfUnity`: the transfer from `μ_ℓ`
  to the constant sheaf `E` over `X_{k'} ⟶ X`.
* `bijective_etaleCohomologyRestrictionMap_constantSheaf_scalarExtension_of_isProper`: the proper
  case.
* `bijective_etaleCohomologyRestrictionMap_constantSheaf_scalarExtension`: every smooth curve
  (affine or proper by Tag 0A27).
* `curveStatementsConstantOnSmoothCurves_of_isUnit`: the statements of Situation 0A52 for the
  constant sheaf `𝐙/ℓ` on smooth curves over an algebraically closed field, `ℓ ∈ k^*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u

namespace Stacks.EtaleCohomology

open Stacks.Kummer

/-! ### Restriction on `μ_n` and its comparison -/

section RootsOfUnity

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (n : ℕ)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction on `H^q(μ_n)` is bijective** once its composite `rootsOfUnityRestriction` with
the comparison `π⁻¹ μ_n ⟶ μ_n` is, `n` being invertible on `X` (the comparison is then an
isomorphism). -/
theorem bijective_etaleCohomologyRestrictionMap_rootsOfUnitySheaf_of_bijective
    (hn : IsUnit ((n : ℕ) : Γ(X, ⊤))) (q : ℕ)
    (h : Function.Bijective (rootsOfUnityRestriction.{u, v, w} π n q)) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} X n) q) := by
  have := isIso_rootsOfUnityInverseImageComparison.{u, v} π n hn
  have hc := ExtFunctorial.bijective_comp_mk₀.{w}
    (X := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of (ULift ℤ)))
    (asIso (rootsOfUnityInverseImageComparison.{u, v} π n)) q
  refine ⟨fun a b hab => h.1 ?_, fun z => ?_⟩
  · rw [rootsOfUnityRestriction_apply, rootsOfUnityRestriction_apply, hab]
  · obtain ⟨a, ha⟩ := h.2 (Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, v} π n) q z)
    refine ⟨a, hc.1 ?_⟩
    rw [rootsOfUnityRestriction_apply, Sheaf.H.map_apply, Sheaf.H.map_apply] at ha
    exact ha

end RootsOfUnity

/-! ### From `μ_ℓ` to a constant sheaf cyclic of order `ℓ` -/

section Constant

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

omit [IsCurve k g] [Smooth g] [IsAlgClosed k'] in
/-- **Restriction of the cohomology of a constant sheaf cyclic of order `ℓ`** to `X_{k'}` is
bijective in degree `q` once restriction of `μ_ℓ`-cohomology (moved along `π⁻¹ μ_ℓ ≅ μ_ℓ`) is:
the two sheaves are isomorphic on `X`, `k` being algebraically closed. -/
theorem bijective_etaleCohomologyRestrictionMap_constantSheaf_of_rootsOfUnity {ℓ : ℕ}
    (hℓ : IsUnit (ℓ : k)) (E : AddCommGrpCat.{u + 1}) (hE : Nonempty (E ≃+ ZMod ℓ))
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' g).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ)
    (h : Function.Bijective
      (rootsOfUnityRestriction.{u, u + 1, u + 1} (scalarExtensionFst k k' g) ℓ q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' g)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q) := by
  obtain ⟨e⟩ := nonempty_constantSheaf_iso_rootsOfUnitySheaf.{u, u + 1} k g ℓ
    (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast g hℓ)) hℓ E hE
  have hμ : Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (scalarExtensionFst k k' g) (rootsOfUnitySheaf.{u, u + 1} X ℓ) q) :=
    bijective_etaleCohomologyRestrictionMap_rootsOfUnitySheaf_of_bijective
      (scalarExtensionFst k k' g) ℓ (isUnit_natCast_globalSections_of_isUnit g hℓ) q h
  have hc : Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (scalarExtensionFst k k' g)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) (u + 1)}).obj E) q) :=
    (etaleCohomologyRestrictionMap_iso_iff (scalarExtensionFst k k' g) e q).1.2 hμ
  exact hc

/-- **Restriction of the cohomology of `𝐙/ℓ` to `X_{k'}` is bijective in every positive degree for
a smooth proper curve** over an algebraically closed field, `ℓ ∈ k^*`, with coefficients any
abelian group `E` cyclic of order `ℓ`. -/
theorem bijective_etaleCohomologyRestrictionMap_constantSheaf_scalarExtension_of_isProper
    [IsProper g] {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' g).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 1 ≤ q) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' g)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q) :=
  bijective_etaleCohomologyRestrictionMap_constantSheaf_of_rootsOfUnity g k' hℓ E hE q
    (bijective_rootsOfUnityRestriction_scalarExtension_of_isProper g k' hℓ q hq)

/-- **Restriction of the cohomology of `𝐙/ℓ` to `X_{k'}` is bijective in every positive degree for
every smooth curve** `X` over an algebraically closed field `k`, `ℓ ∈ k^*`, `E` cyclic of order
`ℓ`: by Tag 0A27 the curve is affine or projective, hence proper, and both cases are proved. -/
theorem bijective_etaleCohomologyRestrictionMap_constantSheaf_scalarExtension
    {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' g).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 1 ≤ q) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' g)
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) q) := by
  rcases isAffine_or_isProjectiveMorphism k g with hX | hX
  · exact bijective_etaleCohomologyRestrictionMap_constantSheaf_of_rootsOfUnity g k' hℓ E hE q
      (bijective_rootsOfUnityRestriction_scalarExtension_of_isAffine g k' hℓ q hq)
  · have := isProper_of_isProjectiveMorphism g hX
    exact bijective_etaleCohomologyRestrictionMap_constantSheaf_scalarExtension_of_isProper g k' hℓ
      E hE q hq

end Constant

/-! ### The base case of Theorem 03SC for `𝐙/ℓ` -/

section BaseCase

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The base case of the dévissage of Theorem 03SC for `E ≅ 𝐙/ℓ𝐙`, `ℓ ∈ k^*`**, unconditional:
the scalar extension input of
`Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_scalarExtension` holds for every
smooth curve by
`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_constantSheaf_scalarExtension`. -/
theorem curveStatementsConstantOnSmoothCurves_of_isUnit (k : Type u) [Field k] [IsAlgClosed k]
    {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) (E : AddCommGrpCat.{u + 1}) (hE : Nonempty (E ≃+ ZMod ℓ)) :
    CurveStatementsConstantOnSmoothCurves k E :=
  curveStatementsConstantOnSmoothCurves_of_scalarExtension k hℓ E hE
    fun _ g _ _ k' _ _ _ _ _ q hq =>
      bijective_etaleCohomologyRestrictionMap_constantSheaf_scalarExtension g k' hℓ E hE q hq

end BaseCase

end Stacks.EtaleCohomology
