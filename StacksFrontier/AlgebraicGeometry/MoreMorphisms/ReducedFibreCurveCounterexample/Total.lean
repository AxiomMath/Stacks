module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurveCounterexample.Base
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The total space of the counterexample

Over the line with infinitely many origins `S`, glue countably many copies of the affine plane
`Spec k[x, y]` along the torus `Spec k[x, t, (xt)⁻¹]`, the `n`-th copy mapping to the `n`-th
chart of `S` by `t = x ^ (n + 1) y`, and being identified with the torus away from `t = 0` by
`y = t / x ^ (n + 1)`. The result `X` is flat, affine and of finite type over `S`; over the `n`-th
origin its fibre contains the line `x = 0` with multiplicity `n + 1`.

## Main definitions

* `AlgebraicGeometry.ReducedFibreCurveCounterexample.total`: the scheme `X`.
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.totalMap`: the morphism `X ⟶ S`.

## Main results

* `AlgebraicGeometry.ReducedFibreCurveCounterexample.opensRange_torusι`: each copy of the torus
  is the open subscheme `xy ≠ 0` of the corresponding plane.
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.preimage_baseChart`: the preimage of the
  `n`-th chart of `S` is the `n`-th chart of `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.ReducedFibreCurveCounterexample

variable (k : Type u) [Field k]

/-- The coordinate ring `k[x, y]` of the plane, with `x = X 0` and `y = X 1`. -/
abbrev planeRing : Type u := MvPolynomial (Fin 2) k

/-- The coordinate ring `k[x, t, (xt)⁻¹]` of the torus, with `x = X 0` and `t = X 1`. -/
abbrev torusRing : Type u := Localization.Away (MvPolynomial.X 0 * MvPolynomial.X 1 : planeRing k)

/-- The coordinate `x` on the torus. -/
def torusX : torusRing k := algebraMap (planeRing k) (torusRing k) (MvPolynomial.X 0)

/-- The coordinate `t` on the torus. -/
def torusT : torusRing k := algebraMap (planeRing k) (torusRing k) (MvPolynomial.X 1)

/-- The coordinates `x` and `t` are both units on the torus. -/
private theorem isUnit_torusX_and_torusT : IsUnit (torusX k) ∧ IsUnit (torusT k) := by
  rw [torusX, torusT, ← IsUnit.mul_iff, ← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (S := torusRing k)
    (MvPolynomial.X 0 * MvPolynomial.X 1 : planeRing k)

/-- The coordinate `x` is a unit on the torus. -/
theorem isUnit_torusX : IsUnit (torusX k) := (isUnit_torusX_and_torusT k).1

/-- The coordinate `t` is a unit on the torus. -/
theorem isUnit_torusT : IsUnit (torusT k) := (isUnit_torusX_and_torusT k).2

/-- The inverse of `x` on the torus. -/
def torusXInv : torusRing k := ↑(isUnit_torusX k).unit⁻¹

/-- On the torus, `x * x⁻¹ = 1`. -/
theorem torusX_mul_torusXInv : torusX k * torusXInv k = 1 :=
  (isUnit_torusX k).mul_val_inv

/-- The inverse `x⁻¹` is a unit on the torus. -/
theorem isUnit_torusXInv : IsUnit (torusXInv k) := Units.isUnit _

/-- The automorphism of the torus fixing `x` and multiplying `t` by `c ^ m`, for a unit `c`
fixed by it. -/
def twistAux (m : ℕ) (c : torusRing k) (hc : IsUnit c) : torusRing k →ₐ[k] torusRing k :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X 0 * MvPolynomial.X 1 : planeRing k)
    (f := MvPolynomial.aeval ![torusX k, torusT k * c ^ m]) (by
      simp only [map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact (isUnit_torusX k).mul ((isUnit_torusT k).mul (hc.pow m)))

/-- `twistAux k m c hc` fixes `x`. -/
theorem twistAux_torusX (m : ℕ) (c : torusRing k) (hc : IsUnit c) :
    twistAux k m c hc (torusX k) = torusX k := by
  simp [twistAux, torusX, IsLocalization.Away.liftAlgHom_apply]

/-- `twistAux k m c hc` sends `t` to `t * c ^ m`. -/
theorem twistAux_torusT (m : ℕ) (c : torusRing k) (hc : IsUnit c) :
    twistAux k m c hc (torusT k) = torusT k * c ^ m := by
  simp [twistAux, torusT, IsLocalization.Away.liftAlgHom_apply]

/-- `twistAux k m c hc` fixes `x⁻¹`. -/
theorem twistAux_torusXInv (m : ℕ) (c : torusRing k) (hc : IsUnit c) :
    twistAux k m c hc (torusXInv k) = torusXInv k := by
  have h : twistAux k m c hc (torusXInv k) * torusX k = 1 := by
    calc twistAux k m c hc (torusXInv k) * torusX k
        = twistAux k m c hc (torusXInv k) * twistAux k m c hc (torusX k) := by
          rw [twistAux_torusX]
      _ = twistAux k m c hc (torusX k * torusXInv k) := by rw [map_mul, mul_comm]
      _ = 1 := by rw [torusX_mul_torusXInv, map_one]
  calc twistAux k m c hc (torusXInv k)
      = twistAux k m c hc (torusXInv k) * (torusX k * torusXInv k) := by
        rw [torusX_mul_torusXInv, mul_one]
    _ = (twistAux k m c hc (torusXInv k) * torusX k) * torusXInv k := by ring
    _ = torusXInv k := by rw [h, one_mul]

/-- If `c * c' = 1` and `twistAux k m c hc` fixes `c'`, then `twistAux k m c hc` is a left
inverse of `twistAux k m c' hc'`. -/
theorem twistAux_comp (m : ℕ) (c c' : torusRing k) (hc : IsUnit c) (hc' : IsUnit c')
    (hcc' : c * c' = 1) (hfix : twistAux k m c hc c' = c') :
    (twistAux k m c hc).comp (twistAux k m c' hc') = AlgHom.id k (torusRing k) := by
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (Submonoid.powers
    (MvPolynomial.X 0 * MvPolynomial.X 1 : planeRing k)) ?_
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · have hr : algebraMap (planeRing k) (torusRing k) (MvPolynomial.C r) =
        algebraMap k (torusRing k) r := by
      rw [IsScalarTower.algebraMap_apply k (planeRing k) (torusRing k), MvPolynomial.algebraMap_eq]
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, hr, AlgHom.commutes]
  · fin_cases i
    · show twistAux k m c hc (twistAux k m c' hc' (torusX k)) = torusX k
      rw [twistAux_torusX, twistAux_torusX]
    · show twistAux k m c hc (twistAux k m c' hc' (torusT k)) = torusT k
      rw [twistAux_torusT, map_mul, map_pow, twistAux_torusT, hfix, mul_assoc, ← mul_pow, hcc',
        one_pow, mul_one]

/-- The `m`-th twist of the torus: `x ↦ x` and `t ↦ t / x ^ m`. -/
def twist (m : ℕ) : torusRing k ≃ₐ[k] torusRing k :=
  AlgEquiv.ofAlgHom (twistAux k m (torusXInv k) (isUnit_torusXInv k))
    (twistAux k m (torusX k) (isUnit_torusX k))
    (twistAux_comp k m _ _ _ _ (by rw [mul_comm, torusX_mul_torusXInv])
      (twistAux_torusX k m _ _))
    (twistAux_comp k m _ _ _ _ (torusX_mul_torusXInv k) (twistAux_torusXInv k m _ _))

/-- The `m`-th twist of the torus fixes `x`. -/
theorem twist_torusX (m : ℕ) : twist k m (torusX k) = torusX k :=
  twistAux_torusX k m _ (isUnit_torusXInv k)

/-- The `m`-th twist of the torus sends `t` to `t / x ^ m`. -/
theorem twist_torusT (m : ℕ) : twist k m (torusT k) = torusT k * torusXInv k ^ m :=
  twistAux_torusT k m _ (isUnit_torusXInv k)


/-- The `m`-th identification of the plane, away from `xy = 0`, with the torus:
`x ↦ x` and `y ↦ t / x ^ m`. -/
def chartAlg (m : ℕ) : planeRing k →ₐ[k] torusRing k :=
  (twist k m).toAlgHom.comp (IsScalarTower.toAlgHom k (planeRing k) (torusRing k))

/-- The `m`-th identification of the plane with the torus sends `x` to `x`. -/
@[simp] theorem chartAlg_X0 (m : ℕ) : chartAlg k m (MvPolynomial.X 0) = torusX k :=
  twist_torusX k m

/-- The `m`-th identification of the plane with the torus sends `y` to `t / x ^ m`. -/
@[simp] theorem chartAlg_X1 (m : ℕ) :
    chartAlg k m (MvPolynomial.X 1) = torusT k * torusXInv k ^ m :=
  twist_torusT k m

/-- The affine plane `Spec k[x, y]`. -/
abbrev plane : Scheme.{u} := Spec (.of (planeRing k))

/-- The torus `Spec k[x, t, (xt)⁻¹]`. -/
abbrev torus : Scheme.{u} := Spec (.of (torusRing k))

/-- The `m`-th inclusion of the torus into the plane. -/
def torusι (m : ℕ) : torus k ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (chartAlg k m).toRingHom)

/-- The `m`-th inclusion of the torus into the plane is the `m`-th twist of the torus followed by
the localization map `Spec k[x, t, (xt)⁻¹] ⟶ Spec k[x, t]`. -/
theorem torusι_eq (m : ℕ) : torusι k m =
    Spec.map (twist k m).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (planeRing k) (torusRing k))) := by
  rw [← Spec.map_comp]
  rfl

/-- **The `m`-th chart of the torus is the open subscheme `xy ≠ 0` of the plane.** -/
instance (m : ℕ) : IsOpenImmersion (torusι k m) := by
  rw [torusι_eq]
  infer_instance

/-- The `m`-th map from the plane to the line: `t ↦ x ^ m y`. -/
def planeMap (m : ℕ) : k[X] →ₐ[k] planeRing k :=
  Polynomial.aeval (MvPolynomial.X 0 ^ m * MvPolynomial.X 1)

/-- The map from the torus to the punctured line: `t ↦ t`. -/
def torusMap : Localization.Away (X : k[X]) →ₐ[k] torusRing k :=
  IsLocalization.Away.liftAlgHom (X : k[X])
    (f := (IsScalarTower.toAlgHom k (planeRing k) (torusRing k)).comp
      (Polynomial.aeval (MvPolynomial.X 1))) (by
        simp only [AlgHom.comp_apply, Polynomial.aeval_X, IsScalarTower.coe_toAlgHom']
        exact isUnit_torusT k)

/-- The map from the torus to the punctured line sends `t` to `t`. -/
theorem torusMap_X : torusMap k (algebraMap k[X] (Localization.Away (X : k[X])) X) = torusT k := by
  rw [torusMap, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  show algebraMap (planeRing k) (torusRing k) (Polynomial.aeval (MvPolynomial.X 1) X) = _
  rw [Polynomial.aeval_X]
  rfl

/-- The `m`-th map from the plane to the line, `t ↦ x ^ m y`, followed by the `m`-th
identification of the plane with the torus, is the localization `k[t] → k[t, t⁻¹]` followed by
`torusMap`. -/
theorem chartAlg_comp_planeMap (m : ℕ) :
    (chartAlg k m).comp (planeMap k m) =
      (torusMap k).comp (IsScalarTower.toAlgHom k k[X] (Localization.Away (X : k[X]))) := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', torusMap_X, planeMap,
    Polynomial.aeval_X, map_mul, map_pow, chartAlg_X0, chartAlg_X1, mul_comm (torusT k),
    ← mul_assoc, ← mul_pow, torusX_mul_torusXInv, one_pow, one_mul]

/-- The `m`-th inclusion of the torus into the plane, followed by the `m`-th map to the line, is
the map from the torus to the punctured line followed by its inclusion into the line. -/
theorem torusι_specMap_planeMap (m : ℕ) :
    torusι k m ≫ Spec.map (CommRingCat.ofHom (planeMap k m).toRingHom) =
      Spec.map (CommRingCat.ofHom (torusMap k).toRingHom) ≫ puncturedLineι k := by
  rw [torusι, puncturedLineι, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg AlgHom.toRingHom (chartAlg_comp_planeMap k m)

/-- **The total space of the counterexample**: copies of the plane, one for each natural number,
glued along the torus, the `n`-th copy along `y = t / x ^ (n + 1)`. -/
def total : Scheme.{u} := StarGlue.glued (fun _ : ℕ ↦ plane k) (fun n ↦ torusι k (n + 1))

/-- The `n`-th chart of the total space. -/
def totalι (n : ℕ) : plane k ⟶ total k :=
  StarGlue.ι (fun _ : ℕ ↦ plane k) (fun n ↦ torusι k (n + 1)) n

/-- Each chart of the total space is an open immersion. -/
instance (n : ℕ) : IsOpenImmersion (totalι k n) :=
  StarGlue.isOpenImmersion_ι (fun _ : ℕ ↦ plane k) (fun n ↦ torusι k (n + 1)) n

/-- Every point of the total space lies in some chart. -/
theorem totalι_jointly_surjective (x : total k) : ∃ (n : ℕ) (y : plane k), totalι k n y = x :=
  StarGlue.ι_jointly_surjective _ _ x

/-- The torus maps to the total space by the same morphism through every chart. -/
@[reassoc]
theorem torusι_totalι (m n : ℕ) :
    torusι k (m + 1) ≫ totalι k m = torusι k (n + 1) ≫ totalι k n :=
  StarGlue.glue_condition _ _ m n

/-- The restriction of the structure morphism to the `n`-th chart. -/
def chartMap (n : ℕ) : plane k ⟶ base k :=
  Spec.map (CommRingCat.ofHom (planeMap k (n + 1)).toRingHom) ≫ baseι k n

/-- On the torus, the restriction of the structure morphism to the `n`-th chart is the map to the
punctured line followed by its inclusion into the `0`-th chart of the base. -/
theorem torusι_chartMap (n : ℕ) :
    torusι k (n + 1) ≫ chartMap k n =
      Spec.map (CommRingCat.ofHom (torusMap k).toRingHom) ≫ puncturedLineι k ≫ baseι k 0 := by
  rw [chartMap, ← Category.assoc, torusι_specMap_planeMap, Category.assoc,
    puncturedLineι_baseι k n 0]

/-- **The structure morphism of the counterexample.** -/
def totalMap : total k ⟶ base k :=
  StarGlue.desc _ _ (chartMap k) _ (torusι_chartMap k)

/-- The structure morphism restricts to `chartMap k n` on the `n`-th chart. -/
@[reassoc (attr := simp)]
theorem totalι_totalMap (n : ℕ) : totalι k n ≫ totalMap k = chartMap k n :=
  StarGlue.ι_desc _ _ _ _ _ n

/-- The map `k[t] → k[x, y]`, `t ↦ x ^ m y`, is injective. -/
theorem planeMap_injective (m : ℕ) : Function.Injective (planeMap k m) := by
  let ev : planeRing k →ₐ[k] k[X] := MvPolynomial.aeval ![1, X]
  have h : ev.comp (planeMap k m) = AlgHom.id k k[X] := by
    apply Polynomial.algHom_ext
    simp [ev, planeMap]
  exact Function.LeftInverse.injective (g := ev) (DFunLike.congr_fun h)

/-- The map `k[t] → k[x, y]`, `t ↦ x ^ m y`, is flat. -/
theorem flat_planeMap (m : ℕ) : (planeMap k m).toRingHom.Flat := by
  let := (planeMap k m).toAlgebra
  have : Module.IsTorsionFree k[X] (planeRing k) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (planeMap_injective k m)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The map `k[t] → k[x, y]`, `t ↦ x ^ m y`, is of finite type. -/
theorem finiteType_planeMap (m : ℕ) : (planeMap k m).toRingHom.FiniteType := by
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k k[X]) ?_
  rw [show (planeMap k m).toRingHom.comp (algebraMap k k[X]) = algebraMap k (planeRing k) from
    RingHom.ext fun r ↦ (planeMap k m).commutes r]
  rw [RingHom.finiteType_algebraMap]
  infer_instance

/-- The restriction of the structure morphism to each chart is flat. -/
instance (n : ℕ) : Flat (chartMap k n) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (planeMap k (n + 1)).toRingHom)) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
    exact flat_planeMap k (n + 1)
  unfold chartMap
  infer_instance

/-- The restriction of the structure morphism to each chart is locally of finite type. -/
instance (n : ℕ) : LocallyOfFiniteType (chartMap k n) := by
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (planeMap k (n + 1)).toRingHom)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
    exact finiteType_planeMap k (n + 1)
  unfold chartMap
  infer_instance

/-- **The counterexample is flat.** -/
instance : Flat (totalMap k) := by
  have : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  refine StarGlue.desc_mem _ _ _ _ _ @Flat (fun n ↦ inferInstanceAs (Flat (chartMap k n))) ?_
  rw [← torusι_chartMap k 0]
  infer_instance

/-- **The counterexample is locally of finite type.** -/
instance : LocallyOfFiniteType (totalMap k) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  refine StarGlue.desc_mem _ _ _ _ _ @LocallyOfFiniteType
    (fun n ↦ inferInstanceAs (LocallyOfFiniteType (chartMap k n))) ?_
  rw [← torusι_chartMap k 0]
  infer_instance

/-- The image of the `m`-th inclusion of the torus into the plane is the open subset `xy ≠ 0`. -/
theorem opensRange_torusι (m : ℕ) :
    (torusι k m).opensRange =
      PrimeSpectrum.basicOpen (MvPolynomial.X 0 * MvPolynomial.X 1 : planeRing k) := by
  have h1 := Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (twist k m).toRingEquiv.toCommRingCatIso.hom)
    (Spec.map (CommRingCat.ofHom (algebraMap (planeRing k) (torusRing k))))
  have h2 := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (planeRing k))
    (MvPolynomial.X 0 * MvPolynomial.X 1 : planeRing k)
  ext x
  show x ∈ Set.range (torusι k m) ↔ _
  rw [torusι_eq]
  exact SetLike.ext_iff.mp (h1.trans h2) x

/-- The `n`-th chart of the total space, as an affine open. -/
abbrev totalChart (n : ℕ) : (total k).Opens := (totalι k n) ''ᵁ ⊤

/-- Each chart of the total space is an affine open. -/
theorem isAffineOpen_totalChart (n : ℕ) : IsAffineOpen (totalChart k n) :=
  (isAffineOpen_top (plane k)).image_of_isOpenImmersion (totalι k n)

/-- The image of a point of the plane under the `n`-th chart lies in the `n`-th chart. -/
theorem mem_totalChart (n : ℕ) (y : plane k) : totalι k n y ∈ totalChart k n :=
  ⟨y, trivial, rfl⟩

/-- **The preimage of the `n`-th chart of the base is the `n`-th chart of the total space.** -/
theorem preimage_baseChart (n : ℕ) : totalMap k ⁻¹ᵁ baseChart k n = totalChart k n := by
  apply le_antisymm
  · rintro x ⟨y, -, hy⟩
    obtain ⟨j, w, rfl⟩ := totalι_jointly_surjective k x
    by_cases hjn : j = n
    · subst hjn
      exact mem_totalChart k j w
    have hx : baseι k j (Spec.map (CommRingCat.ofHom (planeMap k (j + 1)).toRingHom) w) =
        baseι k n y := by
      have h1 : chartMap k j w = totalMap k (totalι k j w) := by
        rw [← totalι_totalMap k j, Scheme.Hom.comp_apply]
      exact h1.trans hy.symm
    obtain ⟨v, hv, -⟩ := StarGlue.exists_eq_of_ι_eq_ι (fun _ : ℕ ↦ line k)
      (fun _ ↦ puncturedLineι k) hjn hx
    have hX : (X : k[X]) ∉ Ideal.comap (planeMap k (j + 1)).toRingHom w.asIdeal := by
      have hmem : puncturedLineι k v ∈ (puncturedLineι k).opensRange := ⟨v, rfl⟩
      rwa [opensRange_puncturedLineι, hv] at hmem
    have hxy : (MvPolynomial.X 0 * MvPolynomial.X 1 : planeRing k) ∉ w.asIdeal := by
      intro h
      apply hX
      show planeMap k (j + 1) X ∈ w.asIdeal
      rw [planeMap, Polynomial.aeval_X, pow_succ, mul_assoc]
      exact w.asIdeal.mul_mem_left _ h
    obtain ⟨v', rfl⟩ : w ∈ (torusι k (j + 1)).opensRange := by
      rw [opensRange_torusι]
      exact hxy
    exact ⟨torusι k (n + 1) v', trivial,
      congrArg (fun φ : torus k ⟶ total k ↦ φ v') (torusι_totalι k n j)⟩
  · rintro x ⟨y, -, rfl⟩
    show totalMap k (totalι k n y) ∈ baseChart k n
    rw [← Scheme.Hom.comp_apply, totalι_totalMap, chartMap, Scheme.Hom.comp_apply]
    exact mem_baseChart k n _

/-- **The counterexample is affine**, hence quasi-compact. -/
instance : IsAffineHom (totalMap k) := by
  refine isAffineHom_of_forall_exists_isAffineOpen (totalMap k) fun x ↦ ?_
  obtain ⟨n, y, rfl⟩ := baseι_jointly_surjective k x
  refine ⟨baseChart k n, mem_baseChart k n y, isAffineOpen_baseChart k n, ?_⟩
  rw [preimage_baseChart]
  exact isAffineOpen_totalChart k n

end AlgebraicGeometry.ReducedFibreCurveCounterexample
