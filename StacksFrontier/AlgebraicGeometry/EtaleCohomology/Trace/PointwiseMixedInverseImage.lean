module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageStalkEnd
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyBlockRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyTracePowers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldExtensionPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPointExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharSeriesRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedSheaf

/-!
# Pointwise mixedness under inverse image

Pointwise `ι`-mixedness of an ℓ-adic sheaf (Weil II 1.2.2) passes to inverse images along morphisms
of schemes of finite type over a finite field sending closed points to closed points, as in the
reduction of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH);
Deligne, Weil II 3.3) to curves. At a closed point `y` of `X'` over `x = g(y)` with
`[κ(y) : κ(x)] = m`, the geometric Frobenius `π_y` acts on `(g⁻¹F)_ȳ = F_x̄` as `π_x ^ m` does, up
to the change of geometric point `Stacks.Frobenius.residueClosurePointHom`, so the characteristic
roots of `π_y` are `m`-th powers of those of `π_x`.

## Main results

* `AlgebraicGeometry.GeometricPoint.Hom.comp_iterate_of_comp_eq`: intertwining passes to iterates.
* `Stacks.EtaleCohomology.LAdicSheaf.isUnit_rationalStalkEnd`: an endomorphism of a geometric point
  acts invertibly on the rational stalk.
* `Stacks.EtaleCohomology.LAdicSheaf.isRoot_charpoly_rationalStalkEnd_of_comp_eq`: characteristic
  roots are preserved by a change of geometric point.
* `Stacks.EtaleCohomology.LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage`: pointwise mixedness
  passes to inverse images along morphisms sending closed points to closed points.
* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow`:
  `Tr(π_y ^ n | (g⁻¹F)_ȳ) = Tr(π_x ^ ((e + 1) n) | F_x̄)` for `n ≥ 1`, the form in which
  realizability (Weil II 1.5) passes to inverse images.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- Composition of morphisms of geometric points is associative. -/
theorem GeometricPoint.Hom.comp_assoc {S : Scheme.{u}} {s t r v : GeometricPoint S}
    (a : GeometricPoint.Hom s t) (b : GeometricPoint.Hom t r) (c : GeometricPoint.Hom r v) :
    (a.comp b).comp c = a.comp (b.comp c) :=
  GeometricPoint.Hom.ext' (Category.assoc _ _ _)

/-- A morphism of geometric points intertwining two endomorphisms intertwines their iterates. -/
theorem GeometricPoint.Hom.comp_iterate_of_comp_eq {S : Scheme.{u}} {s t : GeometricPoint S}
    (θ : GeometricPoint.Hom s t) {a : GeometricPoint.Hom s s} {b : GeometricPoint.Hom t t}
    (h : θ.comp b = a.comp θ) (e : ℕ) : θ.comp (b.iterate e) = (a.iterate e).comp θ := by
  induction e with
  | zero => exact h
  | succ e ih =>
    simp only [GeometricPoint.Hom.iterate]
    rw [← GeometricPoint.Hom.comp_assoc, ih, GeometricPoint.Hom.comp_assoc, h,
      ← GeometricPoint.Hom.comp_assoc]

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **An endomorphism of a geometric point acts bijectively on the ℓ-adic stalk**: at every
level it acts by the isomorphism of stalk functors of Tag 04FN. -/
theorem LAdicSheaf.bijective_stalkEnd (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) : Function.Bijective (LAdicSheaf.stalkEnd B X ℓ F a) := by
  have hiso : ∀ n, IsIso (finiteLevelStalkEnd B X ℓ F a n) := fun n => by
    have := geometricPointStalkMap_isIso B X.1 X.property a
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    exact NatIso.isIso_app_of_isIso _ _
  have hinj : ∀ n, Function.Injective (finiteLevelStalkEnd B X ℓ F a n).hom := fun n =>
    (ConcreteCategory.bijective_of_isIso (finiteLevelStalkEnd B X ℓ F a n)).1
  have hsurj : ∀ n, Function.Surjective (finiteLevelStalkEnd B X ℓ F a n).hom := fun n =>
    (ConcreteCategory.bijective_of_isIso (finiteLevelStalkEnd B X ℓ F a n)).2
  refine ⟨fun v w hvw => Subtype.ext (funext fun n => hinj n ?_), fun w => ?_⟩
  · exact congrArg (fun z : LAdicSheaf.stalk B X ℓ F s => z.1 n) hvw
  · choose v hv using fun n => hsurj n (w.1 n)
    refine ⟨⟨v, fun n => hinj n ?_⟩, Subtype.ext (funext hv)⟩
    rw [← stalkTransition_finiteLevelStalkEnd, hv, hv]
    exact w.2 n

/-- An endomorphism of a geometric point acts invertibly on the rational stalk. -/
theorem LAdicSheaf.isUnit_rationalStalkEnd (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) : IsUnit (LAdicSheaf.rationalStalkEnd B X ℓ F a) := by
  let e := LinearEquiv.ofBijective _ (LAdicSheaf.bijective_stalkEnd B X ℓ F a)
  exact (Module.End.isUnit_iff _).2 (e.baseChange (PadicInt ℓ) (Padic ℓ) _ _).bijective

/-- **Changing the geometric point preserves the characteristic roots.** If `θ : s ⟶ t` carries an
endomorphism `a` of `s` to an endomorphism `b` of `t` (`θ ∘ b = a ∘ θ`), every characteristic root
of `a` on the rational stalk `F_s ⊗ ℚ_ℓ`, read along `ι`, is one of `b` on `F_t ⊗ ℚ_ℓ`. -/
theorem LAdicSheaf.isRoot_charpoly_rationalStalkEnd_of_comp_eq (F : LAdicSheaf B X ℓ)
    {s t : GeometricPoint X.1} (θ : GeometricPoint.Hom s t) {a : GeometricPoint.Hom s s}
    {b : GeometricPoint.Hom t t} (h : θ.comp b = a.comp θ) {L : Type*} [Field L]
    (ι : ℚ_[ℓ] →+* L) {z : L}
    (hz : ((LAdicSheaf.rationalStalkEnd B X ℓ F a).charpoly.map ι).IsRoot z) :
    ((LAdicSheaf.rationalStalkEnd B X ℓ F b).charpoly.map ι).IsRoot z := by
  classical
  have htr : ∀ k : ℕ, 1 ≤ k → LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkEnd B X ℓ F a ^ k) =
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkEnd B X ℓ F b ^ k) := by
    intro k hk
    obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
    rw [← LAdicSheaf.rationalStalkEnd_iterate, ← LAdicSheaf.rationalStalkEnd_iterate]
    exact LAdicSheaf.trace_rationalStalkEnd_eq_of_comm B X ℓ F θ _ _
      (θ.comp_iterate_of_comp_eq h e)
  let bA := Module.finBasis ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B X ℓ F s)
  let bB := Module.finBasis ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B X ℓ F t)
  let A := LinearMap.toMatrix bA bA (LAdicSheaf.rationalStalkEnd B X ℓ F a)
  let Bm := LinearMap.toMatrix bB bB (LAdicSheaf.rationalStalkEnd B X ℓ F b)
  have hloc : localCharSeries A 1 = ∏ _x ∈ ({()} : Finset Unit), localCharSeries Bm 1 := by
    rw [Finset.prod_singleton]
    refine localCharSeries_one_eq_of_trace_pow_eq A Bm fun k hk => ?_
    simp only [A, Bm]
    rw [LinearMap.toMatrix_pow, LinearMap.toMatrix_pow,
      ← LinearMap.trace_eq_matrix_trace, ← LinearMap.trace_eq_matrix_trace]
    exact htr k hk
  have hA : IsUnit A.det := by
    rw [LinearMap.det_toMatrix]
    exact (LinearMap.isUnit_iff_isUnit_det _).1 (LAdicSheaf.isUnit_rationalStalkEnd B X ℓ F a)
  rw [← LinearMap.charpoly_toMatrix _ bA] at hz
  obtain ⟨-, -, hx⟩ := exists_isRoot_charpoly_pow_of_localCharSeries_eq_prod ι A hA _
    (fun _ => Bm) (fun _ => 1) hloc hz
  rw [pow_one] at hx
  rwa [← LinearMap.charpoly_toMatrix _ bB]

section InverseImage

variable {B} {X' : B.Scheme} (g : X' ⟶ X)
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [IsNoetherian X'.1]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [LocallyOfFiniteType (B.inclusion.map g)]

/-- The identification `(g⁻¹F)_ȳ ≃ F_x̄` intertwines the Frobenius endomorphisms. -/
private theorem conj_rationalStalkEnd_frobeniusPointHom {Y Z : B.Scheme}
    [IsNoetherian Y.1] [IsNoetherian Z.1]
    (g : Z ⟶ Y) (F : LAdicSheaf B Y ℓ) (y : Z.1) [Finite (Z.1.residueField y)] :
    (rationalInverseImageStalkEquiv B g F (geometricPointAt Z.1 y)).conj
      (LAdicSheaf.rationalStalkEnd B Z ℓ (LAdicSheaf.inverseImage g F)
        (frobeniusPointHom Z.1 y)) = LAdicSheaf.rationalStalkEnd B Y ℓ F
        ((frobeniusPointHom Z.1 y).mapHom (B.inclusion.map g)) := by
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun (rationalInverseImageStalkEquiv_rationalStalkEnd B g F
    (geometricPointAt Z.1 y) (frobeniusPointHom Z.1 y))
    ((rationalInverseImageStalkEquiv B g F (geometricPointAt Z.1 y)).symm v)
  simpa [LinearEquiv.conj_apply] using this

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **Pointwise mixedness passes to inverse images.** Let `g : X' ⟶ X` be a morphism of schemes of
finite type over a finite field `k` sending closed points to closed points, and `F` an ℓ-adic sheaf
on `X` pointwise `ι`-mixed of weights `≤ w`. Then `g⁻¹F` is pointwise `ι`-mixed of weights `≤ w`.
-/
theorem LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage {F : LAdicSheaf B X ℓ} {q : ℕ}
    {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ} (hF : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F q ι w)
    (hg : ∀ y : closedPoints X'.1, (B.inclusion.map g).base y.1 ∈ closedPoints X.1) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B X' ℓ (B.inclusion.map g ≫ f)
      (LAdicSheaf.inverseImage g F) q ι w := by
  intro y z hz
  set x : closedPoints X.1 := ⟨(B.inclusion.map g).base y.1, hg y⟩
  have hy : Finite (X'.1.residueField y.1) := finite_residueField ((B.inclusion.map g) ≫ f) y.1 y.2
  have hx : Finite (X.1.residueField x.1) := finite_residueField f x.1 x.2
  have : Finite ((B.inclusion.obj X').residueField y.1) := hy
  have : Finite ((B.inclusion.obj X).residueField x.1) := hx
  let : Algebra (X.1.residueField x.1) (X'.1.residueField y.1) :=
    ((B.inclusion.map g).residueFieldMap y.1).hom.toAlgebra
  have : Module.Finite (X.1.residueField x.1) (X'.1.residueField y.1) := Module.Finite.of_finite
  set m := Module.finrank (X.1.residueField x.1) (X'.1.residueField y.1)
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Nat.card (X'.1.residueField y.1) =
      Nat.card (X.1.residueField x.1) ^ (m - 1 + 1) := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)]
    exact Module.natCard_eq_pow_finrank
  have hpoly : (LAdicSheaf.rationalStalkFrobenius B X' ℓ (LAdicSheaf.inverseImage g F) y.1
        (finite_residueField ((B.inclusion.map g) ≫ f) y.1 y.2)).charpoly =
      (LAdicSheaf.rationalStalkEnd B X ℓ F
        ((frobeniusPointHom X'.1 y.1).mapHom (B.inclusion.map g))).charpoly := by
    rw [LAdicSheaf.rationalStalkFrobenius, ← LinearEquiv.charpoly_conj
      (rationalInverseImageStalkEquiv B g F (geometricPointAt X'.1 y.1))]
    congr 1
    exact conj_rationalStalkEnd_frobeniusPointHom ℓ g F y.1
  rw [hpoly] at hz
  have hz' := LAdicSheaf.isRoot_charpoly_rationalStalkEnd_of_comp_eq B X ℓ F
    (residueClosurePointHom (B.inclusion.map g) y.1)
    (frobeniusPointHom_iterate_comm (B.inclusion.map g) y.1 (m - 1) hcard) ι hz
  rw [LAdicSheaf.rationalStalkEnd_iterate, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)] at hz'
  obtain ⟨α, hα, rfl⟩ := exists_isRoot_charpoly_map_pow_eq ι _ hm hz'
  obtain ⟨w', hw', hαn⟩ := hF x α hα
  refine ⟨w', hw', ?_⟩
  have hdeg : residueDegree ((B.inclusion.map g) ≫ f) y.1 = residueDegree f x.1 * m := by
    let := Fintype.ofFinite k
    have h1 : Nat.card (X'.1.residueField y.1) =
        Fintype.card k ^ residueDegree ((B.inclusion.map g) ≫ f) y.1 :=
      natCard_residueField_eq_pow_residueDegree ((B.inclusion.map g) ≫ f) y.1
    have h2 : Nat.card (X.1.residueField x.1) = Fintype.card k ^ residueDegree f x.1 :=
      natCard_residueField_eq_pow_residueDegree f x.1
    have h3 : Nat.card (X'.1.residueField y.1) = Nat.card (X.1.residueField x.1) ^ m :=
      Module.natCard_eq_pow_finrank
    rw [h1, h2, ← pow_mul] at h3
    exact Nat.pow_right_injective (Fintype.one_lt_card (α := k)) h3
  rw [norm_pow, hαn, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), hdeg]
  congr 1
  push_cast
  ring

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [LocallyOfFiniteType (B.inclusion.map g)] in
/-- **The traces of the powers of the geometric Frobenius at a point above a point.** If `y` is a
point of `X'` with finite residue field over `x = g(y)`, with `#κ(y) = #κ(x) ^ (e + 1)`, then for
`n ≥ 1`, `Tr(π_y ^ n | (g⁻¹F)_ȳ ⊗ ℚ_ℓ) = Tr(π_x ^ ((e + 1) n) | F_x̄ ⊗ ℚ_ℓ)`. -/
theorem LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow (F : LAdicSheaf B X ℓ)
    (y : X'.1) (hy : Finite (X'.1.residueField y))
    (hx : Finite (X.1.residueField ((B.inclusion.map g).base y))) (e : ℕ)
    (he : Nat.card (X'.1.residueField y) =
      Nat.card (X.1.residueField ((B.inclusion.map g).base y)) ^ (e + 1)) {n : ℕ} (hn : 1 ≤ n) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B X' ℓ (LAdicSheaf.inverseImage g F) y hy ^ n) =
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F ((B.inclusion.map g).base y) hx ^
          ((e + 1) * n)) := by
  have := hy
  have := hx
  have : Finite ((B.inclusion.obj X').residueField y) := hy
  have : Finite ((B.inclusion.obj X).residueField ((B.inclusion.map g).base y)) := hx
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  have hconj := conj_rationalStalkEnd_frobeniusPointHom ℓ g F y
  have hpow : ∀ m : ℕ, (rationalInverseImageStalkEquiv B g F (geometricPointAt X'.1 y)).conj
      (LAdicSheaf.rationalStalkEnd B X' ℓ (LAdicSheaf.inverseImage g F)
        (frobeniusPointHom X'.1 y) ^ m) = LAdicSheaf.rationalStalkEnd B X ℓ F
        ((frobeniusPointHom X'.1 y).mapHom (B.inclusion.map g)) ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]; rfl
    | succ m ih => rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearEquiv.conj_comp, ih, hconj]
  rw [LAdicSheaf.rationalStalkFrobenius, LAdicSheaf.rationalStalkFrobenius,
    ← LinearMap.trace_conj' _ (rationalInverseImageStalkEquiv B g F (geometricPointAt X'.1 y)),
    hpow, ← LAdicSheaf.rationalStalkEnd_iterate]
  refine (LAdicSheaf.trace_rationalStalkEnd_eq_of_comm B X ℓ F
    (residueClosurePointHom (B.inclusion.map g) y) _ _
    ((residueClosurePointHom (B.inclusion.map g) y).comp_iterate_of_comp_eq
      (frobeniusPointHom_iterate_comm (B.inclusion.map g) y e he) c)).trans ?_
  rw [LAdicSheaf.rationalStalkEnd_iterate, LAdicSheaf.rationalStalkEnd_iterate, pow_mul]
  rfl

end InverseImage

end Stacks.EtaleCohomology
