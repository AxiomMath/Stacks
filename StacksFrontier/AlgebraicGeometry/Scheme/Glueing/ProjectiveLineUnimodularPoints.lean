module

public import StacksFrontier.AlgebraicGeometry.Scheme.GlueMorphismsAway
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineChartMorphisms
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineRigidityOverRing

/-!
# Points of the projective line given by unimodular pairs

Let `R` be a commutative ring, `B` a ring with a ring map `f : R ⟶ B`, and `u, v ∈ B` two
elements generating the unit ideal. The *point* `[u : v] : Spec B ⟶ ℙ¹_R` is the morphism which
on the basic open `D(v)` is the point `x = u / v` of the first chart and on `D(u)` the point
`y = v / u` of the second chart; on `D(u) ∩ D(v)` the two agree because the coordinates are
related by `y = x⁻¹`.

The point `[u : v]` is characterized by its restrictions: for every ring map `φ : B ⟶ C` with
`φ v` a unit, the composite `Spec C ⟶ Spec B ⟶ ℙ¹_R` is the point `x = φ u / φ v` of the first
chart, and similarly with `u`. The points are natural in `B`, lie over `Spec B ⟶ Spec R`, are
compatible with base change of `ℙ¹`, and two unimodular pairs define the same point exactly when
they are proportional, i.e. when `u v' = u' v`.

## Main definitions

* `AlgebraicGeometry.projectiveLineXPoint`, `AlgebraicGeometry.projectiveLineYPoint`: the point
  of the first, resp. second, chart with a given coordinate.
* `AlgebraicGeometry.projectiveLineHomogeneousPoint`: the point `[u : v]` of a unimodular pair.

## Main results

* `AlgebraicGeometry.Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right` and
  `AlgebraicGeometry.Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left`: over a ring
  `C` in which `v` (resp. `u`) becomes a unit, `[u : v]` is the point `x = u / v` of the first
  chart (resp. `y = v / u` of the second).
* `AlgebraicGeometry.Spec_map_comp_projectiveLineHomogeneousPoint`: naturality in `B`.
* `AlgebraicGeometry.projectiveLineHomogeneousPoint_smul`: `[w u : w v] = [u : v]` for a unit `w`.
* `AlgebraicGeometry.projectiveLineHomogeneousPoint_eq_iff`: `[u : v] = [u' : v']` if and only if
  `u v' = u' v`.
* `AlgebraicGeometry.projectiveLineHomogeneousPoint_comp_structureMorphism`: `[u : v]` lies over
  `Spec B`.
* `AlgebraicGeometry.projectiveLineHomogeneousPoint_comp_projectiveLineMap`: compatibility with
  base change.
* `AlgebraicGeometry.projectiveLineHomogeneousPoint_X_one` and
  `AlgebraicGeometry.projectiveLineHomogeneousPoint_one_X`:
  the two charts are the points `[x : 1]` and `[1 : y]`.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Polynomial

universe u

namespace AlgebraicGeometry

variable {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)

/-! ### Points of the charts -/

/-- The point `x = t` of the first chart of `ℙ¹_R`. -/
abbrev projectiveLineXPoint (t : B) : Spec (.of B) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (eval₂RingHom f t)) ≫ projectiveLineXChart R

/-- The point `y = t` of the second chart of `ℙ¹_R`. -/
abbrev projectiveLineYPoint (t : B) : Spec (.of B) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (eval₂RingHom f t)) ≫ projectiveLineYChart R

/-- Composing evaluation at `t` with a ring map `φ` is evaluation at `φ t`. -/
theorem eval₂RingHom_comp {C : Type u} [CommRing C] (φ : B →+* C) (t : B) :
    φ.comp (eval₂RingHom f t) = eval₂RingHom (φ.comp f) (φ t) :=
  Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- The point `x = t` pulled back along `Spec C ⟶ Spec B` is the point `x = φ t`. -/
@[reassoc]
theorem Spec_map_comp_projectiveLineXPoint {C : Type u} [CommRing C] (φ : B →+* C) (t : B) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineXPoint f t =
      projectiveLineXPoint (φ.comp f) (φ t) := by
  rw [← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom, eval₂RingHom_comp]

/-- The point `y = t` pulled back along `Spec C ⟶ Spec B` is the point `y = φ t`. -/
@[reassoc]
theorem Spec_map_comp_projectiveLineYPoint {C : Type u} [CommRing C] (φ : B →+* C) (t : B) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineYPoint f t =
      projectiveLineYPoint (φ.comp f) (φ t) := by
  rw [← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom, eval₂RingHom_comp]

/-- On the overlap, the point `x = t` of the first chart is the point `y = t⁻¹` of the second. -/
theorem projectiveLineXPoint_eq_projectiveLineYPoint {t t' : B} (h : t * t' = 1) :
    projectiveLineXPoint f t = projectiveLineYPoint f t' := by
  let w : Bˣ := ⟨t, t', h, by rw [mul_comm]; exact h⟩
  let L : LaurentPolynomial R →+* B := LaurentPolynomial.eval₂ f w
  have hX : eval₂RingHom f t = L.comp Polynomial.toLaurent :=
    Polynomial.ringHom_ext (fun r ↦ by simp [L, LaurentPolynomial.eval₂_C])
      (by simp [L, w])
  have hY : eval₂RingHom f t' =
      L.comp (projectiveLineOverlapInverseCoordinate R).toRingHom := by
    refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
    · simp [L, projectiveLineOverlapInverseCoordinate, LaurentPolynomial.eval₂_C]
    · simp only [coe_eval₂RingHom, eval₂_X, RingHom.coe_comp, Function.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projectiveLineOverlapInverseCoordinate,
        aeval_X, L, LaurentPolynomial.eval₂_T, zpow_neg, zpow_one]
      rfl
  rw [projectiveLineXPoint, projectiveLineYPoint, hX, hY,
    ← Spec_map_ofHom_comp_Spec_map_ofHom, ← Spec_map_ofHom_comp_Spec_map_ofHom, Category.assoc,
    Category.assoc]
  exact congrArg (_ ≫ ·) (isPullback_projectiveLineCharts R).w

/-- The point `x = t` of a chart `c` which is a monomorphism determines `t`. -/
private theorem injective_Spec_map_eval₂RingHom_comp {Y : Scheme.{u}} (c : Spec (.of R[X]) ⟶ Y)
    [Mono c] : Function.Injective fun t : B ↦ Spec.map (CommRingCat.ofHom (eval₂RingHom f t)) ≫ c :=
  fun t t' h ↦ by
  have h' := Spec.map_injective ((cancel_mono c).1 h)
  have := congrArg (fun φ : CommRingCat.of R[X] ⟶ CommRingCat.of B ↦ φ.hom X) h'
  simpa using this

/-- The point `x = t` of the first chart determines `t`. -/
theorem projectiveLineXPoint_injective : Function.Injective (projectiveLineXPoint (B := B) f) :=
  injective_Spec_map_eval₂RingHom_comp f _

/-- The point `y = t` of the second chart determines `t`. -/
theorem projectiveLineYPoint_injective : Function.Injective (projectiveLineYPoint (B := B) f) :=
  injective_Spec_map_eval₂RingHom_comp f _

/-! ### The point of a unimodular pair -/

/-- The two elements of a pair, indexed by `Bool`: `v` at `false` and `u` at `true`. -/
abbrev projectiveLinePairFamily (u v : B) : Bool → B := fun b ↦ bif b then u else v

/-- The two elements of a unimodular pair generate the unit ideal. -/
theorem span_projectiveLinePairFamily {u v : B} (h : IsCoprime u v) :
    Ideal.span (Set.range (projectiveLinePairFamily u v)) = ⊤ := by
  obtain ⟨a, b, hab⟩ := h
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨true, rfl⟩))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨false, rfl⟩))

/-- The point `x = u / v` of the first chart over `D(v)`. -/
def projectiveLineHomogeneousPointPieceX (u v : B) : Spec (.of (Localization.Away v)) ⟶
    projectiveLine R :=
  projectiveLineXPoint ((algebraMap B (Localization.Away v)).comp f)
    (algebraMap B (Localization.Away v) u * IsLocalization.Away.invSelf v)

/-- The point `y = v / u` of the second chart over `D(u)`. -/
def projectiveLineHomogeneousPointPieceY (u v : B) : Spec (.of (Localization.Away u)) ⟶
    projectiveLine R :=
  projectiveLineYPoint ((algebraMap B (Localization.Away u)).comp f)
    (algebraMap B (Localization.Away u) v * IsLocalization.Away.invSelf u)

/-- The two local descriptions of `[u : v]`, indexed by `Bool`. -/
def projectiveLineHomogeneousPointPiece (u v : B) :
    (b : Bool) → Spec (.of (Localization.Away (projectiveLinePairFamily u v b))) ⟶
      projectiveLine R
  | false => projectiveLineHomogeneousPointPieceX f u v
  | true => projectiveLineHomogeneousPointPieceY f u v

/-- The inverse of a localization element under a ring map. -/
theorem map_invSelf_mul {x : B} {C : Type u} [CommRing C] (φ : Localization.Away x →+* C) :
    φ (IsLocalization.Away.invSelf x) * φ (algebraMap B (Localization.Away x) x) = 1 := by
  rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

/-- Pulled back along `φ : B[1/v] ⟶ C`, the point `x = u / v` is the point `x = t` for any `t`
with `t φ(v) = φ(u)`. -/
theorem Spec_map_comp_projectiveLineHomogeneousPointPieceX (u v : B) {C : Type u} [CommRing C]
    (φ : Localization.Away v →+* C) (t : C)
    (ht : t * φ (algebraMap B (Localization.Away v) v) = φ (algebraMap B (Localization.Away v) u)) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPointPieceX (R := R) f u v =
      projectiveLineXPoint ((φ.comp (algebraMap B (Localization.Away v))).comp f) t := by
  rw [projectiveLineHomogeneousPointPieceX, Spec_map_comp_projectiveLineXPoint, RingHom.comp_assoc,
    map_mul, ← ht, mul_assoc, mul_comm (φ (algebraMap B _ v)), map_invSelf_mul, mul_one]

/-- Pulled back along `φ : B[1/u] ⟶ C`, the point `y = v / u` is the point `y = t` for any `t`
with `t φ(u) = φ(v)`. -/
theorem Spec_map_comp_projectiveLineHomogeneousPointPieceY (u v : B) {C : Type u} [CommRing C]
    (φ : Localization.Away u →+* C) (t : C)
    (ht : t * φ (algebraMap B (Localization.Away u) u) = φ (algebraMap B (Localization.Away u) v)) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPointPieceY (R := R) f u v =
      projectiveLineYPoint ((φ.comp (algebraMap B (Localization.Away u))).comp f) t := by
  rw [projectiveLineHomogeneousPointPieceY, Spec_map_comp_projectiveLineYPoint, RingHom.comp_assoc,
    map_mul, ← ht, mul_assoc, mul_comm (φ (algebraMap B _ u)), map_invSelf_mul, mul_one]

/-- Two ring maps `B[1/v] ⟶ C` agreeing on `B` pull the point `x = u / v` back to the same
point. -/
theorem projectiveLineHomogeneousPointPieceX_compat (u v : B) {C : Type u} [CommRing C]
    (φ ψ : Localization.Away v →+* C)
    (h : φ.comp (algebraMap B _) = ψ.comp (algebraMap B _)) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPointPieceX (R := R) f u v =
      Spec.map (CommRingCat.ofHom ψ) ≫ projectiveLineHomogeneousPointPieceX f u v := by
  rw [IsLocalization.ringHom_ext (Submonoid.powers v) h]

/-- Two ring maps `B[1/u] ⟶ C` agreeing on `B` pull the point `y = v / u` back to the same
point. -/
theorem projectiveLineHomogeneousPointPieceY_compat (u v : B) {C : Type u} [CommRing C]
    (φ ψ : Localization.Away u →+* C)
    (h : φ.comp (algebraMap B _) = ψ.comp (algebraMap B _)) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPointPieceY (R := R) f u v =
      Spec.map (CommRingCat.ofHom ψ) ≫ projectiveLineHomogeneousPointPieceY f u v := by
  rw [IsLocalization.ringHom_ext (Submonoid.powers u) h]

/-- Ring maps `B[1/v] ⟶ C` and `B[1/u] ⟶ C` agreeing on `B` pull the points `x = u / v` and
`y = v / u` back to the same point. -/
theorem projectiveLineHomogeneousPointPieceX_compat_Y (u v : B) {C : Type u} [CommRing C]
    (φ : Localization.Away v →+* C) (ψ : Localization.Away u →+* C)
    (h : φ.comp (algebraMap B _) = ψ.comp (algebraMap B _)) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPointPieceX (R := R) f u v =
      Spec.map (CommRingCat.ofHom ψ) ≫ projectiveLineHomogeneousPointPieceY f u v := by
  have e : ∀ b, φ (algebraMap B _ b) = ψ (algebraMap B _ b) := fun b ↦
    congrArg (fun g : B →+* C ↦ g b) h
  have hφ := map_invSelf_mul (x := v) φ
  have hψ := map_invSelf_mul (x := u) ψ
  rw [Spec_map_comp_projectiveLineHomogeneousPointPieceX f u v φ
      (φ (algebraMap B _ u) * φ (IsLocalization.Away.invSelf v)) (by rw [mul_assoc, hφ, mul_one]),
    Spec_map_comp_projectiveLineHomogeneousPointPieceY f u v ψ
      (ψ (algebraMap B _ v) * ψ (IsLocalization.Away.invSelf u)) (by rw [mul_assoc, hψ, mul_one]),
    h]
  apply projectiveLineXPoint_eq_projectiveLineYPoint
  rw [e u]
  calc ψ (algebraMap B _ u) * φ (IsLocalization.Away.invSelf v) *
        (ψ (algebraMap B _ v) * ψ (IsLocalization.Away.invSelf u))
      = (ψ (IsLocalization.Away.invSelf u) * ψ (algebraMap B _ u)) *
          (φ (IsLocalization.Away.invSelf v) * φ (algebraMap B _ v)) := by rw [e v]; ring
    _ = 1 := by rw [hφ, hψ, mul_one]

/-- The two local descriptions of `[u : v]` agree wherever both are defined. -/
theorem awayCompatible_projectiveLineHomogeneousPointPiece (u v : B) :
    Spec.AwayCompatible (projectiveLinePairFamily u v)
        (projectiveLineHomogeneousPointPiece (R := R) f u v) := by
  intro i j C _ φ ψ hφψ
  cases i <;> cases j
  · exact projectiveLineHomogeneousPointPieceX_compat f u v φ ψ hφψ
  · exact projectiveLineHomogeneousPointPieceX_compat_Y f u v φ ψ hφψ
  · exact (projectiveLineHomogeneousPointPieceX_compat_Y f u v ψ φ hφψ.symm).symm
  · exact projectiveLineHomogeneousPointPieceY_compat f u v φ ψ hφψ

/-- **The point `[u : v]` of `ℙ¹_R` defined by a unimodular pair `(u, v)` of elements of an
`R`-algebra `B`**: on `D(v)` the point `x = u / v` of the first chart, on `D(u)` the point
`y = v / u` of the second. -/
def projectiveLineHomogeneousPoint (u v : B) (h : IsCoprime u v) : Spec (.of B) ⟶
    projectiveLine R :=
  Spec.glueAway (span_projectiveLinePairFamily h)
      (awayCompatible_projectiveLineHomogeneousPointPiece f u v)

variable {f}

/-- **The point `[u : v]` where `v` is invertible** is the point `x = u / v` of the first chart. -/
theorem Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right {u v : B} (h : IsCoprime u v)
    {C : Type u} [CommRing C] (φ : B →+* C) (hv : IsUnit (φ v)) (t : C) (ht : t * φ v = φ u) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPoint f u v h =
      projectiveLineXPoint (φ.comp f) t := by
  rw [projectiveLineHomogeneousPoint, Spec.map_comp_glueAway_of_isUnit _ _ φ false hv,
    projectiveLineHomogeneousPointPiece]
  exact (Spec_map_comp_projectiveLineHomogeneousPointPieceX f u v _ t (by simpa using ht)).trans
    (by rw [IsLocalization.Away.lift_comp])

/-- **The point `[u : v]` where `u` is invertible** is the point `y = v / u` of the second
chart. -/
theorem Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left {u v : B} (h : IsCoprime u v)
    {C : Type u} [CommRing C] (φ : B →+* C) (hu : IsUnit (φ u)) (t : C) (ht : t * φ u = φ v) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPoint f u v h =
      projectiveLineYPoint (φ.comp f) t := by
  rw [projectiveLineHomogeneousPoint, Spec.map_comp_glueAway_of_isUnit _ _ φ true hu,
    projectiveLineHomogeneousPointPiece]
  exact (Spec_map_comp_projectiveLineHomogeneousPointPieceY f u v _ t (by simpa using ht)).trans
    (by rw [IsLocalization.Away.lift_comp])

/-- Morphisms out of `Spec B` are determined on the two basic opens `D(u)` and `D(v)` of a
unimodular pair. -/
theorem hom_ext_of_isCoprime {u v : B} (h : IsCoprime u v) {Y : Scheme.{u}}
    {g₁ g₂ : Spec (.of B) ⟶ Y}
    (hu : ∀ {C : Type u} [CommRing C] (φ : B →+* C), IsUnit (φ u) →
      Spec.map (CommRingCat.ofHom φ) ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ g₂)
    (hv : ∀ {C : Type u} [CommRing C] (φ : B →+* C), IsUnit (φ v) →
      Spec.map (CommRingCat.ofHom φ) ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ g₂) :
    g₁ = g₂ := by
  refine Spec.hom_ext_of_isUnit (span_projectiveLinePairFamily h) fun i ↦ ?_
  cases i
  · exact hv
  · exact hu

/-- Dividing by a unit and multiplying back. -/
theorem mul_isUnit_unit_inv_mul {C : Type u} [CommRing C] {w : C} (hw : IsUnit w) (a : C) :
    a * ↑(IsUnit.unit hw)⁻¹ * w = a := by
  rw [mul_assoc, IsUnit.val_inv_mul, mul_one]

/-- **The point `[u : v]` where `v` is invertible**, with the coordinate `φ u / φ v`. -/
private theorem Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit {u v : B}
    (h : IsCoprime u v) {C : Type u} [CommRing C] (φ : B →+* C) (hv : IsUnit (φ v)) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPoint f u v h =
      projectiveLineXPoint (φ.comp f) (φ u * ↑(IsUnit.unit hv)⁻¹) :=
  Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right h φ hv _
    (mul_isUnit_unit_inv_mul _ _)

/-- **The point `[u : v]` where `u` is invertible**, with the coordinate `φ v / φ u`. -/
private theorem Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit {u v : B}
    (h : IsCoprime u v) {C : Type u} [CommRing C] (φ : B →+* C) (hu : IsUnit (φ u)) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPoint f u v h =
      projectiveLineYPoint (φ.comp f) (φ v * ↑(IsUnit.unit hu)⁻¹) :=
  Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left h φ hu _
    (mul_isUnit_unit_inv_mul _ _)

/-- **Naturality of `[u : v]` in `B`.** -/
theorem Spec_map_comp_projectiveLineHomogeneousPoint {u v : B} (h : IsCoprime u v)
    {C : Type u} [CommRing C]
    (φ : B →+* C) :
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineHomogeneousPoint f u v h =
      projectiveLineHomogeneousPoint (φ.comp f) (φ u) (φ v) (h.map φ) := by
  refine hom_ext_of_isCoprime (h.map φ) (fun ψ hu ↦ ?_) (fun ψ hv ↦ ?_)
  · rw [← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit h (ψ.comp φ) hu,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit (h.map φ) ψ hu]
  · rw [← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit h (ψ.comp φ) hv,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit (h.map φ) ψ hv]

/-- **Rescaling a unimodular pair by a unit does not change its point.** -/
theorem projectiveLineHomogeneousPoint_smul {u v : B} (h : IsCoprime u v) {w : B} (hw : IsUnit w)
    (h' : IsCoprime (w * u) (w * v)) :
    projectiveLineHomogeneousPoint f (w * u) (w * v) h' =
        projectiveLineHomogeneousPoint f u v h := by
  refine hom_ext_of_isCoprime h (fun φ hu ↦ ?_) (fun φ hv ↦ ?_)
  · have hwu : IsUnit (φ (w * u)) := by rw [map_mul]; exact (hw.map φ).mul hu
    rw [Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit h φ hu,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left h' φ hwu
          (φ v * ↑(IsUnit.unit hu)⁻¹)
        (by rw [map_mul, map_mul, mul_comm (φ w) (φ u), ← mul_assoc, mul_isUnit_unit_inv_mul hu,
          mul_comm])]
  · have hwv : IsUnit (φ (w * v)) := by rw [map_mul]; exact (hw.map φ).mul hv
    rw [Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit h φ hv,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right h' φ hwv
          (φ u * ↑(IsUnit.unit hv)⁻¹)
        (by rw [map_mul, map_mul, mul_comm (φ w) (φ v), ← mul_assoc, mul_isUnit_unit_inv_mul hv,
          mul_comm])]

/-- **Proportional unimodular pairs define the same point.** -/
theorem projectiveLineHomogeneousPoint_eq_of_mul_eq_mul {u v u' v' : B} (h : IsCoprime u v)
    (h' : IsCoprime u' v') (e : u * v' = u' * v) :
    projectiveLineHomogeneousPoint f u v h = projectiveLineHomogeneousPoint f u' v' h' := by
  obtain ⟨r, s, hrs⟩ := h
  obtain ⟨r', s', hrs'⟩ := h'
  set w := r * u' + s * v'
  have hu : w * u = u' := by
    calc w * u = r * u' * u + s * (u * v') := by ring
      _ = u' * (r * u + s * v) := by rw [e]; ring
      _ = u' := by rw [hrs, mul_one]
  have hv : w * v = v' := by
    calc w * v = r * (u' * v) + s * v' * v := by ring
      _ = v' * (r * u + s * v) := by rw [← e]; ring
      _ = v' := by rw [hrs, mul_one]
  have hw : IsUnit w := by
    refine IsUnit.of_mul_eq_one (r' * u + s' * v) ?_
    calc w * (r' * u + s' * v) = r' * (w * u) + s' * (w * v) := by ring
      _ = 1 := by rw [hu, hv, hrs']
  have := projectiveLineHomogeneousPoint_smul (f := f) ⟨r, s, hrs⟩ hw
      (by rw [hu, hv]; exact ⟨r', s', hrs'⟩)
  simp only [hu, hv] at this
  exact this.symm

/-- Evaluation at `0` is the origin of the affine line composed with `Spec B ⟶ Spec R`. -/
private theorem Spec_map_eval₂RingHom_zero (c : Spec (.of R[X]) ⟶ projectiveLine R) :
    Spec.map (CommRingCat.ofHom (eval₂RingHom f (0 : B))) ≫ c =
      Spec.map (CommRingCat.ofHom f) ≫ affineLineOriginHom R ≫ c := by
  rw [affineLineOriginHom, ← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom]
  congr 3
  exact Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- The point `y = 0` of the second chart over `B` is the section `∞` composed with
`Spec B ⟶ Spec R`. -/
theorem projectiveLineYPoint_zero :
    projectiveLineYPoint f (0 : B) =
      Spec.map (CommRingCat.ofHom f) ≫ projectiveLineInfinitySection R :=
  Spec_map_eval₂RingHom_zero _

/-- The point `x = 0` of the first chart over `B` is the section `0` composed with
`Spec B ⟶ Spec R`. -/
theorem projectiveLineXPoint_zero :
    projectiveLineXPoint f (0 : B) =
      Spec.map (CommRingCat.ofHom f) ≫ projectiveLineZeroSection R :=
  Spec_map_eval₂RingHom_zero _

/-- A point of a scheme `Y` over `Spec C`, with `C` nontrivial, on the origin of a chart `c`
is not in the range of the chart, if `c` is the complement of the section `s`. -/
private theorem false_of_comp_eq_comp {C : Type u} [CommRing C] [Nontrivial C]
    {Z W Y P : Scheme.{u}} (g : Spec (.of C) ⟶ Z) (l : Z ⟶ W) (c : W ⟶ P) (a : Spec (.of C) ⟶ Y)
    (s : Y ⟶ P) (hc : Set.range c.base = (Set.range s.base)ᶜ) (e : g ≫ l ≫ c = a ≫ s) : False := by
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of C)) := inferInstance
  have h1 : (g ≫ l ≫ c).base p ∈ Set.range c.base :=
    ⟨(g ≫ l).base p, by rw [← Scheme.Hom.comp_apply, Category.assoc]⟩
  rw [e, hc] at h1
  exact h1 ⟨_, (Scheme.Hom.comp_apply _ _ p).symm⟩

/-- A non-unit `x` of a unimodular pair `(x, y)` vanishes in a nontrivial ring where `y` is a
unit. -/
private theorem exists_hom_isUnit_of_not_isUnit {x y : B} (h : IsCoprime x y) (hx : ¬ IsUnit x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Nontrivial C) (π : B →+* C), π x = 0 ∧ IsUnit (π y) := by
  obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal (Ideal.span {x})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hπx : Ideal.Quotient.mk m x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (hxm (Ideal.mem_span_singleton_self x))
  obtain ⟨a, b, hab⟩ := h
  refine ⟨B ⧸ m, inferInstance, ?_, Ideal.Quotient.mk m, hπx, ?_⟩
  · have := hm.ne_top
    exact Ideal.Quotient.nontrivial_iff.2 this
  · refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk m b) ?_
    have := congrArg (Ideal.Quotient.mk m) hab
    rw [map_add, map_mul, map_mul, hπx, mul_zero, zero_add, map_one] at this
    rw [mul_comm]
    exact this

/-- **If a point `[u : v]` lands in the first chart, then `v` is a unit.** -/
theorem isUnit_of_projectiveLineHomogeneousPoint_eq {u v : B} (h : IsCoprime u v)
    (l : Spec (.of B) ⟶ Spec (.of R[X]))
    (hl : projectiveLineHomogeneousPoint f u v h = l ≫ projectiveLineXChart R) : IsUnit v := by
  by_contra hv
  obtain ⟨C, _, _, π, hπv, hπu⟩ := exists_hom_isUnit_of_not_isUnit h.symm hv
  have e := Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left (f := f) h π hπu 0
    (by rw [zero_mul, hπv])
  rw [hl, projectiveLineYPoint_zero] at e
  exact false_of_comp_eq_comp _ _ _ _ _ range_projectiveLineXChart_eq_compl e

/-- **If a point `[u : v]` lands in the second chart, then `u` is a unit.** -/
theorem isUnit_of_projectiveLineHomogeneousPoint_eq_YChart {u v : B} (h : IsCoprime u v)
    (l : Spec (.of B) ⟶ Spec (.of R[X]))
    (hl : projectiveLineHomogeneousPoint f u v h = l ≫ projectiveLineYChart R) : IsUnit u := by
  by_contra hu
  obtain ⟨C, _, _, π, hπu, hπv⟩ := exists_hom_isUnit_of_not_isUnit h hu
  have e := Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right (f := f) h π hπv 0
    (by rw [zero_mul, hπu])
  rw [hl, projectiveLineXPoint_zero] at e
  exact false_of_comp_eq_comp _ _ _ _ _ range_projectiveLineYChart_eq_compl e

/-- An element vanishing on both `D(u)` and `D(v)` for a unimodular pair `(u, v)` is zero. -/
theorem eq_zero_of_isCoprime {u v : B} (h : IsCoprime u v) {x : B}
    (hu : algebraMap B (Localization.Away u) x = 0)
    (hv : algebraMap B (Localization.Away v) x = 0) : x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) _ x).1 hu
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers v) _ x).1 hv
  obtain ⟨a, b, hab⟩ := h.pow (m := n) (n := k)
  calc x = (a * u ^ n + b * v ^ k) * x := by rw [hab, one_mul]
    _ = a * (u ^ n * x) + b * (v ^ k * x) := by ring
    _ = 0 := by simp only at hn hk; rw [hn, hk, mul_zero, mul_zero, add_zero]

/-- **Two unimodular pairs define the same point if and only if they are proportional.** -/
theorem projectiveLineHomogeneousPoint_eq_iff {u v u' v' : B} (h : IsCoprime u v)
    (h' : IsCoprime u' v') :
    projectiveLineHomogeneousPoint f u v h = projectiveLineHomogeneousPoint f u' v' h' ↔
      u * v' = u' * v := by
  refine ⟨fun H ↦ ?_, projectiveLineHomogeneousPoint_eq_of_mul_eq_mul h h'⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_isCoprime h ?_ ?_
  · let φ := algebraMap B (Localization.Away u)
    have hu : IsUnit (φ u) := IsLocalization.Away.algebraMap_isUnit u
    have e₁ := Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit (f := f) h φ hu
    have e₂ := e₁
    rw [H] at e₂
    have hu' : IsUnit (φ u') := isUnit_of_projectiveLineHomogeneousPoint_eq_YChart (h'.map φ) _
      ((Spec_map_comp_projectiveLineHomogeneousPoint h' φ).symm.trans e₂)
    have e₃ := Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left (f := f) h' φ hu' _
      (mul_isUnit_unit_inv_mul hu' (φ v'))
    have ht := projectiveLineYPoint_injective _ (e₂.symm.trans e₃)
    have h₁ := mul_isUnit_unit_inv_mul hu (φ v)
    have h₂ := mul_isUnit_unit_inv_mul hu' (φ v')
    rw [map_sub, map_mul, map_mul, ← h₁, ← h₂, ht]
    ring
  · let φ := algebraMap B (Localization.Away v)
    have hv : IsUnit (φ v) := IsLocalization.Away.algebraMap_isUnit v
    have e₁ := Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit (f := f) h φ hv
    have e₂ := e₁
    rw [H] at e₂
    have hv' : IsUnit (φ v') := isUnit_of_projectiveLineHomogeneousPoint_eq (h'.map φ) _
      ((Spec_map_comp_projectiveLineHomogeneousPoint h' φ).symm.trans e₂)
    have e₃ := Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right (f := f) h' φ hv' _
      (mul_isUnit_unit_inv_mul hv' (φ u'))
    have ht := projectiveLineXPoint_injective _ (e₂.symm.trans e₃)
    have h₁ := mul_isUnit_unit_inv_mul hv (φ u)
    have h₂ := mul_isUnit_unit_inv_mul hv' (φ u')
    rw [map_sub, map_mul, map_mul, ← h₁, ← h₂, ht]
    ring

/-! ### Structure morphism, base change and the charts -/

/-- **The point `[u : v]` lies over `Spec B ⟶ Spec R`.** -/
@[reassoc (attr := simp)]
theorem projectiveLineHomogeneousPoint_comp_structureMorphism {u v : B} (h : IsCoprime u v) :
    projectiveLineHomogeneousPoint f u v h ≫ (projectiveLine R ↘ Spec (.of R)) =
      Spec.map (CommRingCat.ofHom f) := by
  refine hom_ext_of_isCoprime h (fun φ hu ↦ ?_) (fun φ hv ↦ ?_)
  · rw [← Category.assoc,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit h φ hu, Category.assoc,
      projectiveLineYChart_comp_structureMorphism,
      projectiveLineAffineStructureMorphism, Spec_map_ofHom_comp_Spec_map_ofHom,
      Spec_map_ofHom_comp_Spec_map_ofHom]
    congr 2
    ext r
    simp
  · rw [← Category.assoc,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit h φ hv, Category.assoc,
      projectiveLineXChart_comp_structureMorphism,
      projectiveLineAffineStructureMorphism, Spec_map_ofHom_comp_Spec_map_ofHom,
      Spec_map_ofHom_comp_Spec_map_ofHom]
    congr 2
    ext r
    simp

/-- Evaluation at `t` after base change of the coefficients along `g` is evaluation at `t` along
`f.comp g`. -/
theorem eval₂RingHom_comp_mapRingHom {R' : Type u} [CommRing R'] (g : R' →+* R) (t : B) :
    (eval₂RingHom f t).comp (mapRingHom g) = eval₂RingHom (f.comp g) t :=
  Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- **Points are compatible with base change**: `[u : v]` followed by `ℙ¹_R ⟶ ℙ¹_{R'}` is the
point `[u : v]` of `ℙ¹_{R'}`. -/
@[reassoc (attr := simp)]
theorem projectiveLineHomogeneousPoint_comp_projectiveLineMap {R' : Type u} [CommRing R']
    (g : R' →+* R)
    {u v : B} (h : IsCoprime u v) :
    projectiveLineHomogeneousPoint f u v h ≫ projectiveLineMap g =
        projectiveLineHomogeneousPoint (f.comp g) u v h := by
  refine hom_ext_of_isCoprime h (fun φ hu ↦ ?_) (fun φ hv ↦ ?_)
  · rw [← Category.assoc, Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit h φ hu,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left_unit h φ hu,
      projectiveLineYPoint, projectiveLineYPoint, Category.assoc,
      projectiveLineYChart_comp_projectiveLineMap, ← Category.assoc,
      Spec_map_ofHom_comp_Spec_map_ofHom, eval₂RingHom_comp_mapRingHom]
  · rw [← Category.assoc, Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit h φ hv,
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right_unit h φ hv,
      projectiveLineXPoint, projectiveLineXPoint, Category.assoc,
      projectiveLineXChart_comp_projectiveLineMap, ← Category.assoc,
      Spec_map_ofHom_comp_Spec_map_ofHom, eval₂RingHom_comp_mapRingHom]

variable (R)

/-- Precomposition with `Spec` of the identity ring map is the identity. -/
theorem Spec_map_id_comp {Y : Scheme.{u}} (g : Spec (.of B) ⟶ Y) :
    Spec.map (CommRingCat.ofHom (RingHom.id B)) ≫ g = g := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- Evaluating `R[X]` at `X` along `C` is the identity. -/
private theorem eval₂RingHom_comp_id_C_X :
    eval₂RingHom ((RingHom.id R[X]).comp C) X = RingHom.id R[X] :=
  Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- **The first chart is the point `[x : 1]`.** -/
theorem projectiveLineHomogeneousPoint_X_one :
    projectiveLineHomogeneousPoint (C : R →+* R[X]) X 1 isCoprime_one_right =
        projectiveLineXChart R := by
  rw [← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
    Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right (u := (X : R[X])) (v := 1) _
      (RingHom.id _) isUnit_one X (by simp), projectiveLineXPoint]
  rw [eval₂RingHom_comp_id_C_X, Spec_map_id_comp]

/-- **The second chart is the point `[1 : y]`.** -/
theorem projectiveLineHomogeneousPoint_one_X :
    projectiveLineHomogeneousPoint (C : R →+* R[X]) 1 X isCoprime_one_left =
        projectiveLineYChart R := by
  rw [← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
    Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left (u := 1) (v := (X : R[X])) _
      (RingHom.id _) isUnit_one X (by simp), projectiveLineYPoint]
  rw [eval₂RingHom_comp_id_C_X, Spec_map_id_comp]

/-- **The section `∞` is the point `[1 : 0]`.** -/
theorem projectiveLineInfinitySection_eq_projectiveLineHomogeneousPoint :
    projectiveLineInfinitySection R =
      projectiveLineHomogeneousPoint (RingHom.id R) 1 0 isCoprime_one_left := by
  rw [← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
    Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left (u := (1 : R)) (v := 0) _
        (RingHom.id _)
      isUnit_one 0 (by simp),
    projectiveLineYPoint_zero, Spec_map_id_comp]

/-- **The section `0` is the point `[0 : 1]`.** -/
theorem projectiveLineZeroSection_eq_projectiveLineHomogeneousPoint :
    projectiveLineZeroSection R =
      projectiveLineHomogeneousPoint (RingHom.id R) 0 1 isCoprime_one_right := by
  rw [← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
    Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right (u := (0 : R)) (v := 1) _
        (RingHom.id _)
      isUnit_one 0 (by simp),
    projectiveLineXPoint_zero, Spec_map_id_comp]

end AlgebraicGeometry
