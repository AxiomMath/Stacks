module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberGeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout

/-!
# Units on the reduced special fibre of a regular proper model

In the situation of [Stacks, Tag 0C61] the reduced special fibre `(X_k)_red` is proper, reduced
and geometrically connected over `k`, so its ring of global functions is a field purely
inseparable over `k`. For an integer `h` prime to the characteristic of `k`, every invertible
global function on `(X_k)_red` is therefore an `h`-th power times a constant: if `u ^ q ∈ k` with
`q` a power of the characteristic exponent, then `u = (u ^ q) ^ α (u ^ β) ^ h` for a Bézout
relation `α q + β h = 1`. The constants lift to invertible functions on every truncation
`X_n = X ×_{Spec R} Spec(R/π^{n+1})`, so the condition
`Stacks.Thickenings.GlobalUnitsPowerLift` holds for every thickening `(X_k)_red ⟶ X_n`.

## Main results

* `Stacks.Models.exists_eq_zpow_mul_units_map_of_geometricallyConnected`: on a proper, reduced,
  geometrically connected scheme over a field `k`, every invertible global function is an
  `h`-th power times a constant, for `h` invertible in `k`.
* `Stacks.Models.RegularProperModelSituation.geometricallyConnected_specialFiberRedToBase`:
  the reduced special fibre is geometrically connected over `k`.
* `Stacks.Models.RegularProperModelSituation.globalUnitsPowerLift_specialFiberRedToTruncation`:
  the units condition of the corrected [Stacks, Tag 0C6S] holds for `(X_k)_red ⟶ X_n`.

## References

* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProperSectionsGeom (isField_globalSections_of_geometricallyConnected
  isGeometricallyIrreducible_globalSections_of_isProper)

universe u

namespace Stacks.Models

/-- An integer invertible in a field is coprime to every power of the characteristic exponent of
the field. -/
theorem isCoprime_expChar_pow (k : Type u) [Field k] {q : ℕ} [hq : ExpChar k q] {h : ℤ}
    (hh : (h : k) ≠ 0) (n : ℕ) : IsCoprime ((q : ℤ) ^ n) h := by
  refine IsCoprime.pow_left ?_
  cases hq with
  | zero => simpa using isCoprime_one_left
  | prime hp =>
    exact (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr
      fun hdvd => hh ((CharP.intCast_eq_zero_iff k q h).mpr hdvd)

/-- **Invertible functions on a geometrically connected proper reduced scheme over a field.**
Every invertible global function on a proper, reduced, geometrically connected scheme over a
field `k` is an `h`-th power times a constant, for every integer `h` invertible in `k`.

The ring of global functions is a field purely inseparable over `k`, so some `q`-th power of the
function lies in `k`, with `q` a power of the characteristic exponent; since `q` and `h` are
coprime, a Bézout relation writes the function as a power of that constant times an `h`-th
power. -/
theorem exists_eq_zpow_mul_units_map_of_geometricallyConnected (k : Type u) [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g] [GeometricallyConnected g]
    [IsReduced Y] {h : ℤ} (hh : (h : k) ≠ 0) (u : Γ(Y, ⊤)ˣ) :
    ∃ (v : Γ(Y, ⊤)ˣ) (c : kˣ),
      u = v ^ h * Units.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toMonoidHom c := by
  let alg : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  let fieldΓ : Field Γ(Y, ⊤) :=
    (isField_globalSections_of_geometricallyConnected k g).toField
  have hint : Algebra.IsIntegral k Γ(Y, ⊤) := ⟨fun x => by
    rw [_root_.IsIntegral, RingHom.algebraMap_toAlgebra]
    exact Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap g x⟩
  have hpi : IsPurelyInseparable k Γ(Y, ⊤) :=
    (separableClosure.eq_bot_iff (F := k) (E := Γ(Y, ⊤))).1
      ((separableClosure.eq_bot_iff_geometricallyIrreducible k Γ(Y, ⊤)).2
        (isGeometricallyIrreducible_globalSections_of_isProper k g))
  obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k (ringExpChar k) (u : Γ(Y, ⊤))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (u.isUnit.pow _).ne_zero hc.symm
  obtain ⟨α, β, hαβ⟩ := isCoprime_expChar_pow k (q := ringExpChar k) hh n
  refine ⟨u ^ β, (Units.mk0 c hc0) ^ α, ?_⟩
  have hq : Units.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toMonoidHom
      (Units.mk0 c hc0) = u ^ (ringExpChar k ^ n) :=
    Units.ext hc
  rw [map_zpow, hq, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
  conv_lhs => rw [← zpow_one u]
  congr 1
  rw [← hαβ]
  push_cast
  ring

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- The structure morphism from the reduced special fibre to `Spec k` is proper. -/
instance isProper_specialFiberRedToBase : IsProper S.specialFiberRedToBase := by
  unfold specialFiberRedToBase
  infer_instance

/-- The reduced special fibre is geometrically connected over `k`. -/
instance geometricallyConnected_specialFiberRedToBase :
    GeometricallyConnected S.specialFiberRedToBase := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  refine (pullbackRightPullbackFstIso S.specialFiberToSpec x
    S.specialFiber.reductionι).hom.homeomorph.connectedSpace_iff.mp ?_
  exact (Stacks.Thickenings.isThickening_of_isPullback
    (IsPullback.of_hasPullback S.specialFiber.reductionι
      (pullback.fst S.specialFiberToSpec x)).flip
    S.specialFiber.isThickening_reductionι).isHomeomorph.homeomorph.connectedSpace_iff.mpr
    (GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _))

/-- The square `(X_k)_red ⟶ X_n ⟶ Spec(R)` and `(X_k)_red ⟶ Spec(k) ⟶ Spec(R)` commutes. -/
theorem specialFiberRedToTruncation_comp_toBase (n : ℕ) :
    S.specialFiberRedToTruncation n ≫ S.truncationι n ≫ S.X_to_R =
      S.specialFiberRedToBase ≫ Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) := by
  rw [← Category.assoc, S.specialFiberRedToTruncation_comp_truncationι n, specialFiberRedι,
    specialFiberRedToBase, Category.assoc, Category.assoc, pullback.condition]

/-- On global functions, the constants of `R` restricted from `X_n` to `(X_k)_red` are the
constants of `k` through the residue map. -/
theorem appTop_specialFiberRedToTruncation_apply (n : ℕ) (r : S.R) :
    ((S.specialFiberRedToTruncation n).appTop).hom
        (((Scheme.ΓSpecIso (.of S.R)).inv ≫ (S.truncationι n ≫ S.X_to_R).appTop).hom r) =
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberRedToBase.appTop).hom
        (algebraMap S.R S.k r) := by
  have h := congrArg (fun φ => (Scheme.ΓSpecIso (.of S.R)).inv ≫ Scheme.Hom.appTop φ)
    (S.specialFiberRedToTruncation_comp_toBase n)
  simp only [Scheme.Hom.comp_appTop] at h
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc] at h
  exact congrArg (fun φ => φ.hom r) h

/-- **The units condition of the corrected [Stacks, Tag 0C6S] for `(X_k)_red ⟶ X_n`.** For `h`
invertible in `k`, every invertible function on the reduced special fibre is an `h`-th power
times the restriction of an invertible function on the truncation `X_n`: it is an `h`-th power
times a constant of `k`, and a nonzero constant of `k` is the image of a unit of `R`. -/
theorem globalUnitsPowerLift_specialFiberRedToTruncation {h : ℤ}
    (hh : IsUnit ((h : ℤ) : S.k)) (n : ℕ) :
    Thickenings.GlobalUnitsPowerLift (S.specialFiberRedToTruncation n) h := by
  intro u
  obtain ⟨v, c, hvc⟩ := exists_eq_zpow_mul_units_map_of_geometricallyConnected S.k
    S.specialFiberRedToBase hh.ne_zero u
  obtain ⟨r, hr⟩ := S.surjective_algebraMap (c : S.k)
  have hru : IsUnit r := by
    by_contra hnu
    exact c.ne_zero
      (hr ▸ (S.algebraMap_eq_zero_iff r).mpr ((IsLocalRing.mem_maximalIdeal r).mpr hnu))
  refine ⟨v, Units.map ((Scheme.ΓSpecIso (.of S.R)).inv ≫
    (S.truncationι n ≫ S.X_to_R).appTop).hom.toMonoidHom hru.unit, ?_⟩
  refine hvc.trans ?_
  congr 1
  ext
  change ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberRedToBase.appTop).hom (c : S.k) =
    ((S.specialFiberRedToTruncation n).appTop).hom
      (((Scheme.ΓSpecIso (.of S.R)).inv ≫ (S.truncationι n ≫ S.X_to_R).appTop).hom r)
  rw [S.appTop_specialFiberRedToTruncation_apply n r, hr]

end RegularProperModelSituation

end Stacks.Models

end
