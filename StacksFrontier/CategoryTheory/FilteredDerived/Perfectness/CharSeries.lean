module

public import Mathlib.Algebra.FiniteSupport.Basic
public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace

/-!
# The characteristic series of an endomorphism of a perfect complex

Let `R` be a commutative ring. An endomorphism `f` of a perfect object `K` of the derived category
`D(R)` has a characteristic series `det(1 - f T | K) ∈ Λ⟦T⟧ˣ`. It is computed on any bounded
complex `P` of finite projective modules representing `K` as the alternating product
`∏_i det(1 - f T | P ^ i) ^ ((-1) ^ i)` of the characteristic series
(`ProjectiveDeterminant.charSeries`) of the components of a cochain map representing `f`. The
content of the construction is that this does not depend on the choices.

This is the determinant analogue of the trace `CategoryTheory.FilteredDerived.perfectDerivedTrace`
(Stacks 03TI). Over a ring with torsion it is strictly finer than the traces of the powers of `f`:
over `𝔽_ℓ` the identity of `𝔽_ℓ ^ ℓ` and the zero complex have the same traces of all powers, but
characteristic series `(1 - T) ^ ℓ = 1 - T ^ ℓ` and `1`.

## Main definitions

* `CategoryTheory.FilteredDerived.alternatingCharSeries`: the alternating product of the degreewise
  characteristic series of an endomorphism of a bounded complex of finite projective modules.
* `CategoryTheory.FilteredDerived.perfectDerivedCharSeries`: the characteristic series of an
  endomorphism of a perfect object of the derived category.

## Main results

* `CategoryTheory.FilteredDerived.alternatingCharSeries_eq_of_homotopy`: homotopic endomorphisms
  have the same characteristic series.
* `CategoryTheory.FilteredDerived.alternatingCharSeries_comp_comm`: `det(1 - (a ≫ b) T | P) =
  det(1 - (b ≫ a) T | Q)`.
* `CategoryTheory.FilteredDerived.alternatingCharSeries_of_shortExact`: multiplicativity along a
  degreewise short exact sequence of complexes.
* `CategoryTheory.FilteredDerived.alternatingCharSeries_baseChange`: compatibility with base change
  along a ring map `R → R'`.
* `CategoryTheory.FilteredDerived.perfectDerivedCharSeries_eq_alternatingCharSeries`: the derived
  characteristic series is computed by every finite projective representative and every
  representing cochain map.

## References

* [Stacks Project, Tag 03TI](https://stacks.math.columbia.edu/tag/03TI), for the trace.
* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ), where the
  characteristic series of `π_X^*` on `RΓ_c(X_k̄, F)` appears.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct

universe w u v

namespace CategoryTheory.FilteredDerived

/-! ### A telescoping lemma -/

section Telescoping

variable {G : Type*} [CommGroup G]

private lemma finprod_shift (x : ℤ → G) : ∏ᶠ n : ℤ, x (n + 1) = ∏ᶠ n : ℤ, x n :=
  finprod_eq_of_bijective (fun n : ℤ => n + 1)
    ⟨fun a b h => add_right_cancel h, fun b => ⟨b - 1, by simp⟩⟩ (fun _ => rfl)

private lemma hasFiniteMulSupport_shift {x : ℤ → G} (hx : Function.HasFiniteMulSupport x) :
    Function.HasFiniteMulSupport fun n => x (n + 1) := by
  have : (Function.mulSupport fun n => x (n + 1)) = (fun n => n + 1) ⁻¹' Function.mulSupport x :=
    rfl
  change (Function.mulSupport fun n => x (n + 1)).Finite
  rw [this]
  exact Set.Finite.preimage (fun a _ b _ h => add_right_cancel h) hx

private lemma hasFiniteMulSupport_alt {x : ℤ → G} (hx : Function.HasFiniteMulSupport x) :
    Function.HasFiniteMulSupport fun n => if Even n then x n else (x n)⁻¹ := by
  change (Function.mulSupport _).Finite
  refine Set.Finite.subset hx fun n hn => ?_
  by_cases he : Even n <;> simp_all

/-- If `a n * b (n + 1) = c n * c (n + 1)` for all `n`, with `c` finitely supported, then the
alternating products of `a` and `b` agree. -/
public lemma finprod_alternating_eq_of_telescope (a b c : ℤ → G)
    (hb : Function.HasFiniteMulSupport b) (hc : Function.HasFiniteMulSupport c)
    (h : ∀ n, a n * b (n + 1) = c n * c (n + 1)) :
    ∏ᶠ n : ℤ, (if Even n then a n else (a n)⁻¹) =
      ∏ᶠ n : ℤ, (if Even n then b n else (b n)⁻¹) := by
  let alt : (ℤ → G) → ℤ → G := fun x n => if Even n then x n else (x n)⁻¹
  have hpoint : ∀ n, alt a n = alt c n * (alt c (n + 1))⁻¹ * alt b (n + 1) := by
    intro n
    have ha' : a n = c n * c (n + 1) * (b (n + 1))⁻¹ := by
      rw [← h n]
      simp
    by_cases he : Even n
    · have : ¬ Even (n + 1) := by simpa [Int.even_add_one] using he
      simp only [alt, he, this, ite_true, ite_false, ha', inv_inv]
    · have : Even (n + 1) := by simpa [Int.even_add_one] using he
      simp only [alt, he, this, ite_true, ite_false, ha', mul_inv_rev, inv_inv]
      simp only [mul_comm, mul_left_comm]
  have hac := hasFiniteMulSupport_alt hc
  have hab := hasFiniteMulSupport_alt hb
  change ∏ᶠ n : ℤ, alt a n = ∏ᶠ n : ℤ, alt b n
  have hinv : Function.HasFiniteMulSupport fun x => (alt c (x + 1))⁻¹ :=
    Function.HasFiniteMulSupport.inv (hasFiniteMulSupport_shift hac)
  have h1 : Function.HasFiniteMulSupport fun x => alt c x * (alt c (x + 1))⁻¹ :=
    Function.HasFiniteMulSupport.mul hac hinv
  have h2 : Function.HasFiniteMulSupport fun x => alt b (x + 1) := hasFiniteMulSupport_shift hab
  rw [finprod_congr hpoint, finprod_mul_distrib h1 h2, finprod_mul_distrib hac hinv,
    finprod_inv_distrib (fun n => alt c (n + 1)), finprod_shift (alt c),
    finprod_shift (alt b)]
  rw [show (∏ᶠ (i : ℤ), if Even i then c i else (c i)⁻¹) = ∏ᶠ n : ℤ, alt c n from rfl,
    mul_inv_cancel, one_mul]

end Telescoping

/-! ### The cone identity for modules -/

section Cone

variable {R : Type u} [CommRing R]
variable {P₀ : Type v} [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀]
  [Module.Projective R P₀]
variable {P₁ : Type v} [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁]
  [Module.Projective R P₁]

/-- **The cone identity.** Let `d : P₀ → P₁` and `h : P₁ → P₀`, let `f₀` be an endomorphism of
`P₀` and `g₁, κ₁` endomorphisms of `P₁`, and put `κ₀ = f₀ - h ∘ d`. If `g₁ ∘ d = d ∘ κ₀`,
`κ₁ = g₁ + d ∘ h` and `κ₁ ∘ d = d ∘ f₀`, then
`det(1 - f₀ T ^ e) * det(1 - g₁ T ^ e) = det(1 - κ₀ T ^ e) * det(1 - κ₁ T ^ e)`. -/
public theorem charSeries_mul_charSeries_cone (d : P₀ →ₗ[R] P₁) (h : P₁ →ₗ[R] P₀)
    (f₀ : P₀ →ₗ[R] P₀) (g₁ κ₁ : P₁ →ₗ[R] P₁)
    (hA : g₁.comp d = d.comp (f₀ - h.comp d)) (hB : κ₁ = g₁ + d.comp h)
    (hC : κ₁.comp d = d.comp f₀) (e : ℕ) :
    ProjectiveDeterminant.charSeries f₀ e * ProjectiveDeterminant.charSeries g₁ e =
      ProjectiveDeterminant.charSeries (f₀ - h.comp d) e *
        ProjectiveDeterminant.charSeries κ₁ e := by
  let Φ : (P₁ × P₀) →ₗ[R] (P₁ × P₀) :=
    (LinearMap.inl R P₁ P₀).comp (g₁.comp (LinearMap.fst R P₁ P₀)) +
      (LinearMap.inr R P₁ P₀).comp (h.comp (LinearMap.fst R P₁ P₀) +
        f₀.comp (LinearMap.snd R P₁ P₀))
  have hΦ : ∀ x y, Φ (x, y) = (g₁ x, h x + f₀ y) := fun x y => by simp [Φ]
  have h1 := ProjectiveDeterminant.charSeries_of_exact (i := LinearMap.inr R P₁ P₀)
    (q := LinearMap.fst R P₁ P₀) LinearMap.inr_injective
    (by
      intro z
      constructor
      · intro hz
        exact ⟨z.2, Prod.ext (by simpa using hz.symm) rfl⟩
      · rintro ⟨y, rfl⟩
        rfl)
    (fun x => ⟨(x, 0), rfl⟩) f₀ Φ g₁
    (LinearMap.ext fun y => Prod.ext (by simp [hΦ]) (by simp [hΦ]))
    (LinearMap.ext fun z => by simp [hΦ]) e
  let j : P₀ →ₗ[R] (P₁ × P₀) := (-d).prod LinearMap.id
  let π : (P₁ × P₀) →ₗ[R] P₁ := (LinearMap.fst R P₁ P₀) + d.comp (LinearMap.snd R P₁ P₀)
  have hj : ∀ y, j y = (-d y, y) := fun y => rfl
  have hπ : ∀ x y, π (x, y) = x + d y := fun x y => rfl
  have h2 := ProjectiveDeterminant.charSeries_of_exact (i := j) (q := π)
    (fun y y' hy => by simpa [hj] using congrArg _root_.Prod.snd hy)
    (by
      intro ⟨x, y⟩
      constructor
      · intro hz
        refine ⟨y, ?_⟩
        rw [hπ] at hz
        rw [hj]
        exact Prod.ext (by simp [eq_neg_of_add_eq_zero_left hz]) rfl
      · rintro ⟨y, hy⟩
        rw [← hy, hj, hπ]
        simp)
    (fun x => ⟨(x, 0), by simp [hπ]⟩) (f₀ - h.comp d) Φ κ₁
    (by
      ext y
      · simp only [LinearMap.comp_apply, hj, hΦ]
        have := LinearMap.congr_fun hA y
        simp only [LinearMap.comp_apply] at this
        simp [this]
      · simp [hj, hΦ, sub_eq_add_neg, add_comm])
    (by
      refine LinearMap.ext fun z => ?_
      obtain ⟨x, y⟩ := z
      simp only [LinearMap.comp_apply, hΦ, hπ]
      have := LinearMap.congr_fun hC y
      simp only [LinearMap.comp_apply] at this
      rw [map_add κ₁ x (d y), this, hB]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, add_assoc]) e
  rw [← h1, h2]

end Cone

/-! ### The alternating characteristic series of a bounded finite projective complex -/

section Complex

variable (R : Type u) [CommRing R]

/-- The characteristic series `det(1 - φ T)` of an endomorphism of one term of a bounded complex of
finite projective modules, as a unit of `R⟦T⟧`. -/
public def charUnitAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (i : ℤ) (φ : P.X i ⟶ P.X i) : (PowerSeries R)ˣ :=
  letI : Module.Projective R (P.X i) := (hP.2 i).1
  letI : Module.Finite R (P.X i) := (hP.2 i).2
  (ProjectiveDeterminant.isUnit_charSeries φ.hom one_ne_zero).unit

/-- The underlying power series of `charUnitAt R P hP i φ` is `det(1 - φ T)`. -/
public theorem coe_charUnitAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (i : ℤ) (φ : P.X i ⟶ P.X i) :
    letI : Module.Projective R (P.X i) := (hP.2 i).1
    letI : Module.Finite R (P.X i) := (hP.2 i).2
    (charUnitAt R P hP i φ : PowerSeries R) = ProjectiveDeterminant.charSeries φ.hom 1 :=
  rfl

/-- The characteristic series at a degree where the complex vanishes is `1`. -/
public lemma charUnitAt_eq_one_of_isZero (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (i : ℤ) (φ : P.X i ⟶ P.X i)
    (hi : CategoryTheory.Limits.IsZero (P.X i)) : charUnitAt R P hP i φ = 1 := by
  let : Module.Projective R (P.X i) := (hP.2 i).1
  let : Module.Finite R (P.X i) := (hP.2 i).2
  let : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero hi
  have hφ : φ.hom = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
  apply Units.ext
  rw [coe_charUnitAt, hφ, ProjectiveDeterminant.charSeries_zero, Units.val_one]

private lemma mulSupport_charUnitAt_finite (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (φ : ∀ i, P.X i ⟶ P.X i) :
    (Function.mulSupport fun i => charUnitAt R P hP i (φ i)).Finite :=
  (finite_nonzero_degrees R P hP).subset fun i hi hz =>
    hi (charUnitAt_eq_one_of_isZero R P hP i (φ i) hz)

/-- A bounded complex of finite projective modules is K-projective. -/
private lemma isKProjective_of_finiteProjectiveComplex (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) : CochainComplex.IsKProjective P := by
  obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
  let : P.IsStrictlyLE d := hd
  let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
  let (i : ℤ) : Projective (P.X i) := inferInstance
  exact CochainComplex.isKProjective_of_projective P d

/-- **The characteristic series of an endomorphism of a bounded complex of finite projective
modules**: `det(1 - f T | P) = ∏_i det(1 - f T | P ^ i) ^ ((-1) ^ i)`, a unit of `R⟦T⟧`. A
degree where the complex vanishes contributes `1`, so the product is finite. -/
public def alternatingCharSeries (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (f : P ⟶ P) : (PowerSeries R)ˣ :=
  ∏ᶠ i : ℤ, if Even i then charUnitAt R P hP i (f.f i) else (charUnitAt R P hP i (f.f i))⁻¹

/-- **Homotopy invariance.** Homotopic endomorphisms of a bounded complex of finite projective
modules have the same characteristic series. -/
public theorem alternatingCharSeries_eq_of_homotopy (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) {f g : P ⟶ P} (H : Homotopy f g) :
    alternatingCharSeries R P hP f = alternatingCharSeries R P hP g := by
  classical
  let κ : ∀ n : ℤ, P.X n ⟶ P.X n := fun n => f.f n - P.d n (n + 1) ≫ H.hom (n + 1) n
  have hcomm : ∀ n : ℤ, f.f n = P.d n (n + 1) ≫ H.hom (n + 1) n +
      H.hom n (n - 1) ≫ P.d (n - 1) n + g.f n := by
    intro n
    have h := H.comm n
    rw [dNext_eq H.hom (ComplexShape.up_mk n (n + 1) rfl),
      prevD_eq H.hom (ComplexShape.up_mk (n - 1) n (by omega))] at h
    exact h
  have hcomm' : ∀ n : ℤ, f.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ H.hom (n + 1 + 1) (n + 1) +
      H.hom (n + 1) n ≫ P.d n (n + 1) + g.f (n + 1) := by
    intro n
    have h := hcomm (n + 1)
    rwa [add_sub_cancel_right] at h
  have hA : ∀ n : ℤ, P.d n (n + 1) ≫ g.f (n + 1) = κ n ≫ P.d n (n + 1) := by
    intro n
    simp only [κ, Preadditive.sub_comp, Category.assoc]
    rw [hcomm n]
    simp only [Preadditive.add_comp, Category.assoc, HomologicalComplex.d_comp_d,
      Limits.comp_zero, g.comm]
    abel
  have hB : ∀ n : ℤ, κ (n + 1) = g.f (n + 1) + H.hom (n + 1) n ≫ P.d n (n + 1) := by
    intro n
    simp only [κ]
    rw [hcomm' n]
    abel
  have hC : ∀ n : ℤ, P.d n (n + 1) ≫ κ (n + 1) = f.f n ≫ P.d n (n + 1) := by
    intro n
    simp only [κ, Preadditive.comp_sub, ← Category.assoc, HomologicalComplex.d_comp_d,
      Limits.zero_comp, sub_zero, f.comm]
  have key : ∀ n : ℤ, charUnitAt R P hP n (f.f n) * charUnitAt R P hP (n + 1) (g.f (n + 1)) =
      charUnitAt R P hP n (κ n) * charUnitAt R P hP (n + 1) (κ (n + 1)) := by
    intro n
    obtain ⟨_, _⟩ := hP.2 n
    obtain ⟨_, _⟩ := hP.2 (n + 1)
    apply Units.ext
    simp only [Units.val_mul, coe_charUnitAt]
    have hκ : (κ n).hom = (f.f n).hom - (H.hom (n + 1) n).hom.comp (P.d n (n + 1)).hom := by
      simp [κ]
    rw [hκ]
    refine charSeries_mul_charSeries_cone (P.d n (n + 1)).hom (H.hom (n + 1) n).hom
      (f.f n).hom (g.f (n + 1)).hom (κ (n + 1)).hom ?_ ?_ ?_ 1
    · have := congrArg ModuleCat.Hom.hom (hA n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at this
      rw [this, ← hκ]
    · have := congrArg ModuleCat.Hom.hom (hB n)
      rw [ModuleCat.hom_add, ModuleCat.hom_comp] at this
      exact this
    · have := congrArg ModuleCat.Hom.hom (hC n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at this
      exact this
  exact finprod_alternating_eq_of_telescope _ _ _ (mulSupport_charUnitAt_finite R P hP g.f)
    (mulSupport_charUnitAt_finite R P hP κ) key

/-- **Cyclicity.** For cochain maps `a : P ⟶ Q` and `b : Q ⟶ P` between bounded complexes of
finite projective modules, `det(1 - (a ≫ b) T | P) = det(1 - (b ≫ a) T | Q)`. -/
public theorem alternatingCharSeries_comp_comm (P Q : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : finiteProjectiveComplex R P) (hQ : finiteProjectiveComplex R Q)
    (a : P ⟶ Q) (b : Q ⟶ P) :
    alternatingCharSeries R P hP (a ≫ b) = alternatingCharSeries R Q hQ (b ≫ a) := by
  have h : ∀ i, charUnitAt R P hP i ((a ≫ b).f i) = charUnitAt R Q hQ i ((b ≫ a).f i) := by
    intro i
    obtain ⟨_, _⟩ := hP.2 i
    obtain ⟨_, _⟩ := hQ.2 i
    apply Units.ext
    rw [coe_charUnitAt, coe_charUnitAt, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, ModuleCat.hom_comp]
    exact ProjectiveDeterminant.charSeries_comp_comm _ _ 1
  simp only [alternatingCharSeries, h]

/-- **Multiplicativity along short exact sequences.** For a degreewise short exact sequence
`0 → P' → P → P'' → 0` of bounded complexes of finite projective modules and compatible
endomorphisms `f'`, `f`, `f''`, `det(1 - f T | P) = det(1 - f' T | P') * det(1 - f'' T | P'')`. -/
public theorem alternatingCharSeries_of_shortExact (P' P P'' : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP' : finiteProjectiveComplex R P') (hP : finiteProjectiveComplex R P)
    (hP'' : finiteProjectiveComplex R P'') (i : P' ⟶ P) (q : P ⟶ P'')
    (hi : ∀ n, Function.Injective (i.f n)) (hex : ∀ n, Function.Exact (i.f n) (q.f n))
    (hq : ∀ n, Function.Surjective (q.f n))
    (f' : P' ⟶ P') (f : P ⟶ P) (f'' : P'' ⟶ P'')
    (hf' : f' ≫ i = i ≫ f) (hf'' : f ≫ q = q ≫ f'') :
    alternatingCharSeries R P hP f =
      alternatingCharSeries R P' hP' f' * alternatingCharSeries R P'' hP'' f'' := by
  have h : ∀ n, charUnitAt R P hP n (f.f n) =
      charUnitAt R P' hP' n (f'.f n) * charUnitAt R P'' hP'' n (f''.f n) := by
    intro n
    obtain ⟨_, _⟩ := hP'.2 n
    obtain ⟨_, _⟩ := hP.2 n
    obtain ⟨_, _⟩ := hP''.2 n
    apply Units.ext
    rw [Units.val_mul, coe_charUnitAt, coe_charUnitAt, coe_charUnitAt]
    refine ProjectiveDeterminant.charSeries_of_exact (i := (i.f n).hom) (q := (q.f n).hom)
      (hi n) (hex n) (hq n) _ _ _ ?_ ?_ 1
    · have := congrArg ModuleCat.Hom.hom (HomologicalComplex.congr_hom hf' n)
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp,
        ModuleCat.hom_comp] at this
      exact this.symm
    · have := congrArg ModuleCat.Hom.hom (HomologicalComplex.congr_hom hf'' n)
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp,
        ModuleCat.hom_comp] at this
      exact this
  have hs : ∀ (Q : CochainComplex (ModuleCat.{v} R) ℤ) (hQ : finiteProjectiveComplex R Q)
      (g : Q ⟶ Q), Function.HasFiniteMulSupport fun n =>
        if Even n then charUnitAt R Q hQ n (g.f n) else (charUnitAt R Q hQ n (g.f n))⁻¹ :=
    fun Q hQ g => hasFiniteMulSupport_alt (mulSupport_charUnitAt_finite R Q hQ fun n => g.f n)
  unfold alternatingCharSeries
  rw [← finprod_mul_distrib (hs P' hP' f') (hs P'' hP'' f'')]
  refine finprod_congr fun n => ?_
  rw [h n]
  by_cases he : Even n <;> simp [he, mul_comm]

/-- **Base change of rings.** Let `R'` be an `R`-algebra, `P` and `P'` bounded complexes of finite
projective modules over `R` and `R'`, and `e n : P' ^ n ≃ R' ⊗[R] P ^ n` identifications under
which an endomorphism `f'` of `P'` is the base change of an endomorphism `f` of `P`. Then
`det(1 - f' T | P')` is the image of `det(1 - f T | P)` under `R⟦T⟧ → R'⟦T⟧`. -/
public theorem alternatingCharSeries_baseChange {R' : Type u} [CommRing R'] [Algebra R R']
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (hP : finiteProjectiveComplex R P)
    (P' : CochainComplex (ModuleCat.{v} R') ℤ) (hP' : finiteProjectiveComplex R' P')
    (f : P ⟶ P) (f' : P' ⟶ P')
    (e : ∀ n, P'.X n ≃ₗ[R'] R' ⊗[R] P.X n)
    (he : ∀ n, (e n).conj (f'.f n).hom = (f.f n).hom.baseChange R') :
    alternatingCharSeries R' P' hP' f' =
      Units.map (PowerSeries.map (algebraMap R R')).toMonoidHom
        (alternatingCharSeries R P hP f) := by
  have h : ∀ n, charUnitAt R' P' hP' n (f'.f n) =
      Units.map (PowerSeries.map (algebraMap R R')).toMonoidHom (charUnitAt R P hP n (f.f n)) := by
    intro n
    obtain ⟨_, _⟩ := hP.2 n
    obtain ⟨_, _⟩ := hP'.2 n
    apply Units.ext
    rw [Units.coe_map, coe_charUnitAt, coe_charUnitAt,
      ← ProjectiveDeterminant.charSeries_conj (e n), he n,
      ProjectiveDeterminant.charSeries_baseChange]
    rfl
  unfold alternatingCharSeries
  rw [MonoidHom.map_finprod _ (hasFiniteMulSupport_alt
    (mulSupport_charUnitAt_finite R P hP fun n => f.f n))]
  refine finprod_congr fun n => ?_
  rw [h n]
  by_cases he : Even n <;> simp [he]

end Complex

/-! ### The characteristic series of an endomorphism of a perfect derived object -/

section Derived

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- A chosen bounded complex of finite projective modules representing a perfect object. -/
public def perfectRep (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.Perfect.IsPerfect K) : CochainComplex (ModuleCat.{v} R) ℤ :=
  hK.choose

/-- The chosen representative `perfectRep R K hK` is a bounded complex of finite projective
modules. -/
public theorem perfectRep_spec (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.Perfect.IsPerfect K) : finiteProjectiveComplex R (perfectRep R K hK) := by
  obtain ⟨a, b, ha, hb, hfin, hproj, -⟩ := hK.choose_spec
  exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, fun i => ⟨hproj i, hfin i⟩⟩

/-- The chosen identification of the representative with the perfect object. -/
public def perfectRepIso (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.Perfect.IsPerfect K) : DerivedCategory.Q.obj (perfectRep R K hK) ≅ K :=
  (hK.choose_spec.choose_spec.choose_spec.2.2.2.2.some).symm

/-- **The characteristic series `det(1 - f T | K)` of an endomorphism `f` of a perfect object `K`
of the derived category**, a unit of `R⟦T⟧`. It is computed on a chosen bounded complex of finite
projective modules representing `K`; by
`perfectDerivedCharSeries_eq_alternatingCharSeries` every representative gives the same value. -/
public def perfectDerivedCharSeries (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.Perfect.IsPerfect K) (f : K ⟶ K) : (PowerSeries R)ˣ := by
  let P := perfectRep R K hK
  let hP := perfectRep_spec R K hK
  let e := perfectRepIso R K hK
  letI : CochainComplex.IsKProjective P := by
    obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
    let : P.IsStrictlyLE d := hd
    let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
    let (i : ℤ) : Projective (P.X i) := inferInstance
    exact CochainComplex.isKProjective_of_projective P d
  let qP := (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).obj P
  let α : DerivedCategory.Qh.obj qP ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P ≪≫ e
  let gₕ : qP ⟶ qP :=
    (CochainComplex.IsKProjective.Qh_map_bijective P qP).surjective
      (α.hom ≫ f ≫ α.inv) |>.choose
  let g : P ⟶ P :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).preimage gₕ
  exact alternatingCharSeries R P hP g

/-- **Well-definedness.** The characteristic series of an endomorphism of a perfect derived
object is computed on any bounded finite-projective representative, and hence is independent of
the representative, the chosen isomorphism, and the cochain map representing the endomorphism. -/
public theorem perfectDerivedCharSeries_eq_alternatingCharSeries
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : StacksDraft.Perfect.IsPerfect K) (f : K ⟶ K)
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (hP : finiteProjectiveComplex R P)
    (e : DerivedCategory.Q.obj P ≅ K) (g : P ⟶ P)
    (hg : DerivedCategory.Q.map g = e.hom ≫ f ≫ e.inv) :
    perfectDerivedCharSeries R K hK f = alternatingCharSeries R P hP g := by
  classical
  let P0 := perfectRep R K hK
  let hP0 := perfectRep_spec R K hK
  let e0 := perfectRepIso R K hK
  have := isKProjective_of_finiteProjectiveComplex R P0 hP0
  have := isKProjective_of_finiteProjectiveComplex R P hP
  let Q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let q0 := Q.obj P0
  let q := Q.obj P
  let α0 : DerivedCategory.Qh.obj q0 ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P0 ≪≫ e0
  let α : DerivedCategory.Qh.obj q ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P ≪≫ e
  let g0H : q0 ⟶ q0 :=
    (CochainComplex.IsKProjective.Qh_map_bijective P0 q0).surjective
      (α0.hom ≫ f ≫ α0.inv) |>.choose
  have hg0H : (DerivedCategory.Qh).map g0H = α0.hom ≫ f ≫ α0.inv :=
    (CochainComplex.IsKProjective.Qh_map_bijective P0 q0).surjective
      (α0.hom ≫ f ≫ α0.inv) |>.choose_spec
  let g0 : P0 ⟶ P0 := Q.preimage g0H
  have hg0 : Q.map g0 = g0H := by simp [g0]
  obtain ⟨uH, huH⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P0 q).surjective
    (α0.hom ≫ α.inv)
  obtain ⟨vH, hvH⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P q0).surjective
    (α.hom ≫ α0.inv)
  have hconj : α.inv ≫ (DerivedCategory.Qh).map (Q.map g) ≫ α.hom = f := by
    have hq : (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P ≫
        (DerivedCategory.Qh).map (Q.map g) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P =
          DerivedCategory.Q.map g := by
      have hn : DerivedCategory.Q.map g ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P =
            (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P ≫
              (DerivedCategory.Qh).map (Q.map g) :=
        DerivedCategory.quotientCompQhIso_inv_naturality g
      calc
        _ = ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P ≫
            (DerivedCategory.Qh).map (Q.map g)) ≫
              (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P := by
          simp only [Category.assoc]
        _ = (DerivedCategory.Q.map g ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P) ≫
              (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P := by
          rw [hn.symm]
        _ = DerivedCategory.Q.map g := by simp [Category.assoc]
    change (e.inv ≫ (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P) ≫
        (DerivedCategory.Qh).map (Q.map g) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P ≫ e.hom) = f
    calc
      _ = e.inv ≫ ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app P ≫
            (DerivedCategory.Qh).map (Q.map g) ≫
              (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P) ≫ e.hom := by
        simp [Category.assoc]
      _ = e.inv ≫ DerivedCategory.Q.map g ≫ e.hom := by rw [hq]
      _ = f := by rw [hg]; simp [Category.assoc]
  have hconjH : uH ≫ Q.map g ≫ vH = g0H := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective P0 q0).injective
    calc
      (DerivedCategory.Qh).map (uH ≫ Q.map g ≫ vH) =
          α0.hom ≫ (α.inv ≫ (DerivedCategory.Qh).map (Q.map g) ≫ α.hom) ≫ α0.inv := by
        simp [Functor.map_comp, huH, hvH, Category.assoc]
      _ = (DerivedCategory.Qh).map g0H := by rw [hconj, hg0H]
  have hVU : vH ≫ uH = 𝟙 q := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective P q).injective
    simp only [Functor.map_comp, hvH, huH]
    rw [CategoryTheory.Functor.map_id]
    simp [Category.assoc]
  let u : P0 ⟶ P := Q.preimage uH
  let v : P ⟶ P0 := Q.preimage vH
  have hu : Q.map u = uH := by simp [u]
  have hv : Q.map v = vH := by simp [v]
  have hcomp : Q.map (u ≫ g ≫ v) = g0H := by
    rw [Functor.map_comp, Functor.map_comp, hu, hv, hconjH]
  have h0 : Homotopy g0 (u ≫ g ≫ v) :=
    HomotopyCategory.homotopyOfEq g0 (u ≫ g ≫ v) (hg0.trans hcomp.symm)
  have hHomVU : Homotopy (v ≫ u) (𝟙 P) :=
    HomotopyCategory.homotopyOfEq (v ≫ u) (𝟙 P)
      (by rw [Functor.map_comp, hu, hv, hVU, Functor.map_id])
  change alternatingCharSeries R P0 hP0 g0 = alternatingCharSeries R P hP g
  calc
    alternatingCharSeries R P0 hP0 g0 = alternatingCharSeries R P0 hP0 (u ≫ g ≫ v) :=
      alternatingCharSeries_eq_of_homotopy R P0 hP0 h0
    _ = alternatingCharSeries R P hP (v ≫ u ≫ g) := by
      simpa [Category.assoc] using alternatingCharSeries_comp_comm R P0 P hP0 hP (u ≫ g) v
    _ = alternatingCharSeries R P hP g :=
      alternatingCharSeries_eq_of_homotopy R P hP (Homotopy.compRightId hHomVU g)

end Derived

end CategoryTheory.FilteredDerived
