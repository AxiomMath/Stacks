module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.IdealPowerSections.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.BasicOpenCover
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Sections
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.RestrictionMaps

/-!
# A two-generator counterexample for sections away from an ideal

Let `k` be a field and let `A` be the quotient of the polynomial ring over `k` in the variables
`f`, `g`, `x`, `y` and pairs `aₙ`, `bₙ` for `n ≥ 1` by the relations `f y = g x` and
`aₙ fⁿ + bₙ gⁿ = 0`. Write `I = (f, g)`. The fractions `x/f` and `y/g` agree on
`D(f) ∩ D(g)` and so glue to a section of the structure sheaf over `D(f) ∪ D(g)`, the complement
of `V(I)`. That section is **not** in the image of the canonical map from
`colim_n Hom_A(Iⁿ, A)` to the sections over the complement of `V(I)`. Hence that canonical map
is not an isomorphism in general: a quasi-coherent sheaf on an affine scheme is not recovered
from its sections away from a closed subset by taking a colimit of ideal duals.

## Main definitions

* `relationIdeal` and `counterexampleRing`: the presented ring `A`.
* `f`, `g`, `x`, `y`, `a`, `b`: its distinguished coordinates.
* `twoGeneratorIdeal`: the ideal `I = (f, g)`.

## Main results

* `gluedFractionSection`: the section of `𝒪` on the complement of `V(I)` built from the two
  fractions.
* `gluedFractionSection_f` and `gluedFractionSection_g`: the two equations `f · s = x` and
  `g · s = y` that characterize it.
* `gluedFractionSection_not_mem_range`: it is not in the range of the canonical map.
* `canonicalMapToSections_not_isIso`: consequently that canonical map is not an isomorphism.

## Implementation notes

The variables `aₙ₊₁` and `bₙ₊₁` are indexed by `n : ℕ`, so the variable index type is
`Fin 4 ⊕ (ℕ × Fin 2)`. The glued section is pinned down by the two equations `f • s = x` and
`g • s = y`, rather than by a description of `s` on each of `D(f)` and `D(g)`.

The target of the canonical map is the module of sections of the associated quasi-coherent sheaf
on the complement of the vanishing locus.

Several steps use `with_unfolding_all` rather than a `set_option`:
`AlgebraicGeometry.Scheme.Modules` and `AlgebraicGeometry.structurePresheafInModuleCat` agree
with the type-valued structure sheaf at default transparency only, so the
`StructureSheaf.const` API is not visible to `rw` at the transparency it uses.

## References

* [Stacks Project, Tag 01PN](https://stacks.math.columbia.edu/tag/01PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPowerSections
open TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TwoGeneratorCounterexample

variable (k : Type u) [Field k]

/-- The section `m / r` of `M̃` over the standard open `D(r)`. -/
noncomputable def localizedFraction {R : CommRingCat.{u}}
    (M : ModuleCat R) (r : ↑R) (m : ↑M) :
    (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
      (.op (PrimeSpectrum.basicOpen r)) :=
  IsLocalizedModule.iso (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (LocalizedModule.mk m ⟨r, Submonoid.mem_powers r⟩)

/-- The identification of the sections of `M̃` over `D(r)` with the localization `M_r`. -/
noncomputable def basicOpenLocalizationEquiv {R : CommRingCat.{u}}
    (M : ModuleCat R) (r : ↑R) :
    LocalizedModule.Away (R := R) r (↑M) ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
        (.op (PrimeSpectrum.basicOpen r)) :=
  IsLocalizedModule.iso (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom

/-- Restricting the fraction `m / r` from `D(r)` to `D(rs)` gives `s • m / rs`. -/
lemma moduleRestrictionMap_fraction {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    (r s : R) (hrs : PrimeSpectrum.basicOpen (r * s) ≤ PrimeSpectrum.basicOpen r)
    (m : M) :
    PrimeSpectrum.moduleRestrictionMap r (r * s) hrs
      (LocalizedModule.mk m ⟨r, Submonoid.mem_powers r⟩) =
    LocalizedModule.mk (s • m) ⟨r * s, Submonoid.mem_powers (r * s)⟩ := by
  let φ := PrimeSpectrum.ringRestrictionMap r (r * s) hrs
  let := Module.compHom (R := Localization.Away (r * s)) (S := Localization.Away r)
    (LocalizedModule.Away (R := R) (r * s) M) φ.toRingHom
  let : IsScalarTower R (Localization.Away r)
      (LocalizedModule.Away (R := R) (r * s) M) :=
    IsScalarTower.of_algebraMap_smul fun a z => by
      change φ (algebraMap R (Localization.Away r) a) • z = a • z
      rw [φ.commutes]
      exact IsScalarTower.algebraMap_smul (Localization.Away (r * s)) a z
  let F : LocalizedModule.Away (R := R) r M →ₗ[Localization.Away r]
      LocalizedModule.Away (R := R) (r * s) M :=
    PrimeSpectrum.moduleRestrictionMap r (r * s) hrs
  have hlocal : IsUnit (algebraMap R (Localization.Away (r * s)) r) :=
    (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (S := Localization.Away (r * s))).mp hrs
  have hz : (algebraMap R (Localization.Away r) r) •
      LocalizedModule.mk m ⟨r, Submonoid.mem_powers r⟩ =
      LocalizedModule.mkLinearMap (Submonoid.powers r) M m := by
    rw [← Localization.mk_one_eq_algebraMap (M := Submonoid.powers r) r,
      LocalizedModule.mk_smul_mk, one_mul, LocalizedModule.mkLinearMap_apply]
    exact LocalizedModule.mk_eq.mpr ⟨1, by simp⟩
  have hleft : (algebraMap R (Localization.Away (r * s)) r) •
      F (LocalizedModule.mk m ⟨r, Submonoid.mem_powers r⟩) =
      LocalizedModule.mk m (1 : Submonoid.powers (r * s)) := by
    calc
      _ = φ (algebraMap R (Localization.Away r) r) •
          F (LocalizedModule.mk m ⟨r, Submonoid.mem_powers r⟩) := by
        rw [← φ.commutes]
      _ = F ((algebraMap R (Localization.Away r) r) •
          LocalizedModule.mk m ⟨r, Submonoid.mem_powers r⟩) := (F.map_smul _ _).symm
      _ = F (LocalizedModule.mkLinearMap (Submonoid.powers r) M m) := congrArg F hz
      _ = LocalizedModule.mkLinearMap (Submonoid.powers (r * s)) M m :=
        PrimeSpectrum.moduleRestrictionMap_mk r (r * s) hrs m
      _ = LocalizedModule.mk m (1 : Submonoid.powers (r * s)) := rfl
  have hright : (algebraMap R (Localization.Away (r * s)) r) •
      LocalizedModule.mk (s • m) ⟨r * s, Submonoid.mem_powers (r * s)⟩ =
      LocalizedModule.mk m (1 : Submonoid.powers (r * s)) := by
    rw [← Localization.mk_one_eq_algebraMap (M := Submonoid.powers (r * s)) r,
      LocalizedModule.mk_smul_mk, one_mul]
    have hs : (⟨r * s, Submonoid.mem_powers (r * s)⟩ :
        Submonoid.powers (r * s)) • m = r • (s • m) := by
      change (r * s) • m = r • (s • m)
      rw [mul_smul]
    rw [← hs, LocalizedModule.mk_cancel]
  exact hlocal.smul_bijective.injective (hleft.trans hright.symm)

/-- Restricting `localizedFraction M r m` from `D(r)` to `D(rs)` gives
`localizedFraction M (r * s) (s • m)`. -/
lemma localizedFraction_restrict {R : CommRingCat.{u}}
    (M : ModuleCat R) (r s : ↑R) (m : ↑M) :
    (modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE (PrimeSpectrum.basicOpen_mul_le_left r s)).op
        (localizedFraction M r m) = localizedFraction M (r * s) (s • m) := by
  unfold localizedFraction
  rw [AlgebraicGeometry.tilde.map_basicOpen]
  refine congrArg (fun z : LocalizedModule (Submonoid.powers (r * s)) (↑M) =>
    (IsLocalizedModule.iso (Submonoid.powers (r * s))
      (tilde.toOpen M (PrimeSpectrum.basicOpen (r * s))).hom) z) ?_
  exact moduleRestrictionMap_fraction r s
    (PrimeSpectrum.basicOpen_mul_le_left r s) m

/-- Indices for `f,g,x,y` and for the pairs `aₙ,bₙ` with `n ≥ 1`. -/
abbrev variableIndex := Fin 4 ⊕ (ℕ × Fin 2)

/-- The relations `fy-gx` and `aₙfⁿ+bₙgⁿ`, for positive `n`. -/
noncomputable def relationIdeal : Ideal (MvPolynomial (variableIndex) k) :=
  let F : MvPolynomial variableIndex k := MvPolynomial.X (Sum.inl (0 : Fin 4))
  let G : MvPolynomial variableIndex k := MvPolynomial.X (Sum.inl (1 : Fin 4))
  let X : MvPolynomial variableIndex k := MvPolynomial.X (Sum.inl (2 : Fin 4))
  let Y : MvPolynomial variableIndex k := MvPolynomial.X (Sum.inl (3 : Fin 4))
  Ideal.span (Set.insert (F * Y - G * X)
    (Set.range fun n : ℕ =>
      MvPolynomial.X (Sum.inr (n, (0 : Fin 2))) * F ^ (n + 1) +
        MvPolynomial.X (Sum.inr (n, (1 : Fin 2))) * G ^ (n + 1)))

/-- The ring `k[f,g,x,y,{aₙ,bₙ}_{n≥1}]/(fy-gx,{aₙfⁿ+bₙgⁿ}_{n≥1})`. -/
abbrev counterexampleRing := MvPolynomial variableIndex k ⧸ relationIdeal k

/-- The coordinate `f` in the quotient ring. -/
noncomputable def f : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inl (0 : Fin 4)))

/-- The coordinate `g` in the quotient ring. -/
noncomputable def g : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inl (1 : Fin 4)))

/-- The coordinate `x` in the quotient ring. -/
noncomputable def x : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inl (2 : Fin 4)))

/-- The coordinate `y` in the quotient ring. -/
noncomputable def y : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inl (3 : Fin 4)))

/-- The coordinate `aₙ₊₁` in the quotient ring. -/
noncomputable def a (n : ℕ) : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inr (n, (0 : Fin 2))))

/-- The coordinate `bₙ₊₁` in the quotient ring. -/
noncomputable def b (n : ℕ) : counterexampleRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inr (n, (1 : Fin 2))))

/-- The ideal `(f,g)` in the quotient ring. -/
noncomputable def twoGeneratorIdeal : Ideal (counterexampleRing k) :=
  Ideal.span {f k, g k}

/-- The ideal `(f, g)` transported to the universe-lifted ring is still generated by the two
lifted elements. -/
lemma liftedTwoGeneratorIdeal_eq (k : Type u) [Field k] :
    liftedIdeal.{u, u} (counterexampleRing k) (twoGeneratorIdeal k) =
      Ideal.span {(ULift.up (f k) : ULift.{u, u} (counterexampleRing k)),
        (ULift.up (g k) : ULift.{u, u} (counterexampleRing k))} := by
  change (Ideal.span {f k, g k}).comap
      (ULift.ringEquiv : ULift.{u, u} (counterexampleRing k) ≃+* counterexampleRing k) = _
  rw [← Ideal.map_symm (ULift.ringEquiv :
    ULift.{u, u} (counterexampleRing k) ≃+* counterexampleRing k), Ideal.map_span]
  rw [Set.image_pair]
  congr 1

/-- The complement of `V(f, g)` is the union of the two standard opens `D(f)` and `D(g)`. -/
lemma complement_eq_basicOpen_sup (k : Type u) [Field k] :
    complementVanishing (ULift.{u} (counterexampleRing k))
      (liftedIdeal.{u, u} (counterexampleRing k) (twoGeneratorIdeal k)) =
      PrimeSpectrum.basicOpen (ULift.up (f k) : ULift.{u, u} (counterexampleRing k)) ⊔
    PrimeSpectrum.basicOpen (ULift.up (g k) : ULift.{u, u} (counterexampleRing k)) := by
  ext p
  change ¬ (liftedIdeal.{u, u} (counterexampleRing k) (twoGeneratorIdeal k) : Ideal
      (ULift.{u, u} (counterexampleRing k))) ≤ p.1 ↔
    (ULift.up (f k) : ULift.{u, u} (counterexampleRing k)) ∉ p.1 ∨
      (ULift.up (g k) : ULift.{u, u} (counterexampleRing k)) ∉ p.1
  rw [liftedTwoGeneratorIdeal_eq]
  have hspan :
    ({(ULift.up (f k) : ULift.{u, u} (counterexampleRing k)),
        (ULift.up (g k) : ULift.{u, u} (counterexampleRing k))} :
          Set (ULift.{u, u} (counterexampleRing k))) ⊆ p.1 ↔
        ULift.up (f k) ∈ p.1 ∧ ULift.up (g k) ∈ p.1 := Set.pair_subset_iff
  rw [Ideal.span_le, hspan]
  by_cases hf : (ULift.up (f k) : ULift.{u, u} (counterexampleRing k)) ∈ p.1
  · simp [hf]
  · simp [hf]

/-- The first defining relation of the counterexample ring: `f y = g x`. -/
lemma f_mul_y_eq_g_mul_x (k : Type u) [Field k] :
    f k * y k = g k * x k := by
  change Ideal.Quotient.mk (relationIdeal k)
      (MvPolynomial.X (Sum.inl (0 : Fin 4)) * MvPolynomial.X (Sum.inl (3 : Fin 4))) =
    Ideal.Quotient.mk (relationIdeal k)
      (MvPolynomial.X (Sum.inl (1 : Fin 4)) * MvPolynomial.X (Sum.inl (2 : Fin 4)))
  apply Ideal.Quotient.eq.mpr
  change _ - _ ∈ relationIdeal k
  rw [relationIdeal]
  apply Ideal.subset_span
  exact Set.mem_insert_iff.mpr (Or.inl rfl)

/-- The remaining defining relations of the counterexample ring: `aₙ₊₁ fⁿ⁺¹ + bₙ₊₁ gⁿ⁺¹ = 0`. -/
lemma relation_at_index (k : Type u) [Field k] (n : ℕ) :
    a k n * f k ^ (n + 1) + b k n * g k ^ (n + 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change _ ∈ relationIdeal k
  rw [relationIdeal]
  apply Ideal.subset_span
  right
  exact ⟨n, rfl⟩

private lemma obstruction_ne_zero (k : Type u) [Field k] (q : ℕ) :
    a k q * f k ^ q * x k + b k q * g k ^ q * y k ≠ 0 := by
  let S : Ideal (Polynomial k) := Ideal.span {(Polynomial.X : Polynomial k) ^ (q + 1)}
  let T := Polynomial k ⧸ S
  let t : T := Ideal.Quotient.mk S Polynomial.X
  let vars : variableIndex → T := fun v =>
    match v with
    | Sum.inl i => if i = 0 then t else if i = 2 then 1 else 0
    | Sum.inr (n, j) => if n = q ∧ j = 0 then 1 else 0
  let ev : MvPolynomial (variableIndex) k →+* T :=
    MvPolynomial.eval₂Hom (algebraMap k T) vars
  have ht : t ^ (q + 1) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  have hrel : relationIdeal k ≤ RingHom.ker ev := by
    rw [relationIdeal]
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with hp | hp
    · subst p
      change ev _ = 0
      simp [ev, vars]
    · rcases hp with ⟨n, rfl⟩
      change ev _ = 0
      by_cases hn : n = q
      · subst n
        simp [ev, vars, ht]
      · simp [ev, vars, hn]
  let evQ : counterexampleRing k →+* T :=
    Ideal.Quotient.lift (relationIdeal k) ev
      (fun p hp => RingHom.mem_ker.mp (hrel hp))
  have hnonzero : t ^ q ≠ 0 := by
    intro heq
    have hmem : (Polynomial.X : Polynomial k) ^ q ∈ S :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [t] using heq)
    change (Polynomial.X : Polynomial k) ^ q ∈
      Ideal.span {(Polynomial.X : Polynomial k) ^ (q + 1)} at hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp ⟨c, hc⟩) q (by omega)
    have hzero : (1 : k) = 0 := by simp at hcoeff
    exact one_ne_zero hzero
  have heval : evQ (a k q * f k ^ q * x k + b k q * g k ^ q * y k) = t ^ q := by
    simp [evQ, ev, vars, t, a, b, f, g, x, y, Ideal.Quotient.lift_mk]
  intro h
  have h' := congrArg evQ h
  rw [map_zero] at h'
  exact hnonzero (heval.symm.trans h')

/-- The glued section together with the two equations characterizing it. -/
noncomputable def gluedFractionSection_aux :
    {s : sectionsOnComplement (counterexampleRing k) (twoGeneratorIdeal k)
        (counterexampleRing k) //
      f k • s = toComplement (counterexampleRing k) (twoGeneratorIdeal k)
        (counterexampleRing k) (x k) ∧
      g k • s = toComplement (counterexampleRing k) (twoGeneratorIdeal k)
        (counterexampleRing k) (y k)} := by
  let A := counterexampleRing k
  let B := ULift.{u} A
  let R : CommRingCat.{u} := .of B
  let M : ModuleCat R := ModuleCat.of R B
  let H := modulesSpecToSheaf.obj (tilde M)
  let E := AlgebraicGeometry.tilde.modulesSpecToSheafIso M
  let G := structurePresheafInModuleCat B B
  let f' : B := ULift.up (f k)
  let g' : B := ULift.up (g k)
  let x' : B := ULift.up (x k)
  let y' : B := ULift.up (y k)
  let v : ULift.{u} Bool → B := fun i => if i.down then g' else f'
  let U : ULift.{u} Bool → Opens (PrimeSpectrum.Top B) :=
    fun i => PrimeSpectrum.basicOpen (v i)
  let sf : ∀ i, G.obj
      (.op (PrimeSpectrum.basicOpen (v i))) := fun i => match i with
    | ⟨false⟩ => StructureSheaf.const x' f'
        (PrimeSpectrum.basicOpen f') le_rfl
    | ⟨true⟩ => StructureSheaf.const y' g'
        (PrimeSpectrum.basicOpen g') le_rfl
  have hsup : iSup U = PrimeSpectrum.basicOpen f' ⊔ PrimeSpectrum.basicOpen g' := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      cases i with
      | up b => cases b <;> simp [U, v]
    · exact sup_le (le_iSup U (ULift.up false)) (le_iSup U (ULift.up true))
  have hcover : iSup U =
      complementVanishing B (liftedIdeal.{u, u} A (twoGeneratorIdeal k)) := by
    rw [hsup, ← complement_eq_basicOpen_sup]
  have hdiff : AlgebraicGeometry.StructureSheaf.basicOpenCoverDifference
      (R := B) (M := B) (ι := ULift.{u} Bool) v sf = 0 := by
    ext i j
    simp only [AlgebraicGeometry.StructureSheaf.basicOpenCoverDifference, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.zero_apply, sub_eq_zero]
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases i <;> cases j
        · simp [sf, v]
        · simp only [sf, v]
          have hrel : f' • y' = g' • x' := by
            change ULift.up (f k * y k) = ULift.up (g k * x k)
            exact congrArg ULift.up (f_mul_y_eq_g_mul_x k)
          exact StructureSheaf.const_eq_const_of_smul_eq_smul
            x' y' f' g' _
            (PrimeSpectrum.basicOpen_mul_le_left f' g')
            (PrimeSpectrum.basicOpen_mul_le_right f' g') hrel
        · simp only [sf, v]
          have hrel : g' • x' = f' • y' := by
            change ULift.up (g k * x k) = ULift.up (f k * y k)
            exact congrArg ULift.up (f_mul_y_eq_g_mul_x k).symm
          exact StructureSheaf.const_eq_const_of_smul_eq_smul
            y' x' g' f' _
            (PrimeSpectrum.basicOpen_mul_le_left g' f')
            (PrimeSpectrum.basicOpen_mul_le_right g' f') hrel
        · simp [sf, v]
  have hrange :=
    (AlgebraicGeometry.StructureSheaf.exact_basicOpenCoverRestriction_basicOpenCoverDifference
      (R := B) (M := B) (ι := ULift.{u} Bool) v) sf
  have hmem := hrange.mp hdiff
  let s := Classical.choose hmem
  have hs := Classical.choose_spec hmem
  have htoOpen (i : ULift.{u} Bool) (m : B) :
      G.map (homOfLE (le_iSup U i)).op
          (StructureSheaf.toOpenₗ B B (iSup U) m) =
        StructureSheaf.const m 1 (PrimeSpectrum.basicOpen (v i)) (by simp) := by
    change (structureSheafInType B B).1.map
        (homOfLE (le_iSup U i)).op
        (StructureSheaf.toOpenₗ B B (iSup U) m) = _
    rw [StructureSheaf.toOpenₗ_eq_const, StructureSheaf.res_const]
  have hfx : f' • s = StructureSheaf.toOpenₗ B B (iSup U) x' := by
    apply (AlgebraicGeometry.StructureSheaf.basicOpenCoverRestriction_injective
      (R := B) (M := B) (ι := ULift.{u} Bool) v)
    funext i
    have hsi := congrFun hs i
    change G.map (homOfLE (le_iSup U i)).op s = sf i at hsi
    change G.map (homOfLE (le_iSup U i)).op (f' • s) =
      G.map (homOfLE (le_iSup U i)).op (StructureSheaf.toOpenₗ B B (iSup U) x')
    rw [map_smul, hsi]
    cases i with
    | up b =>
      cases b
      · with_unfolding_all
          rw [htoOpen]
          exact (StructureSheaf.smul_const x' f' f' _ _).trans
            (StructureSheaf.const_eq_const_of_smul_eq_smul (f' • x') x' f' 1 _ _ _ (by simp))
      · with_unfolding_all
          rw [htoOpen]
          have hrel : g' • x' = f' • y' :=
            congrArg ULift.up (f_mul_y_eq_g_mul_x k).symm
          exact (StructureSheaf.smul_const y' f' g' _ _).trans
            (StructureSheaf.const_eq_const_of_smul_eq_smul (f' • y') x' g' 1 _ _ _
              (by simpa [smul_comm] using hrel))
  have hgy : g' • s = StructureSheaf.toOpenₗ B B (iSup U) y' := by
    apply (AlgebraicGeometry.StructureSheaf.basicOpenCoverRestriction_injective
      (R := B) (M := B) (ι := ULift.{u} Bool) v)
    funext i
    have hsi := congrFun hs i
    change G.map (homOfLE (le_iSup U i)).op s = sf i at hsi
    change G.map (homOfLE (le_iSup U i)).op (g' • s) =
      G.map (homOfLE (le_iSup U i)).op
        (StructureSheaf.toOpenₗ B B (iSup U) y')
    rw [map_smul, hsi]
    cases i with
    | up b =>
      cases b
      · with_unfolding_all
          rw [htoOpen]
          have hrel : f' • y' = g' • x' :=
            congrArg ULift.up (f_mul_y_eq_g_mul_x k)
          exact (StructureSheaf.smul_const x' g' f' _ _).trans
            (StructureSheaf.const_eq_const_of_smul_eq_smul (g' • x') y' f' 1 _ _ _
              (by simpa [smul_comm] using hrel))
      · with_unfolding_all
          rw [htoOpen]
          exact (StructureSheaf.smul_const y' g' g' _ _).trans
            (StructureSheaf.const_eq_const_of_smul_eq_smul (g' • y') y' g' 1 _ _ _ (by simp))
  let c := eqToHom hcover.symm
  let tG := G.map c.op s
  let tH : ↑(sectionsOnComplement A (twoGeneratorIdeal k) A) :=
    (E.app (.op (complementVanishing B
      (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv tG
  have htransport :
      (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).hom tH = tG := by
    with_unfolding_all
      exact ConcreteCategory.congr_hom
        (E.app (.op (complementVanishing B
          (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv_hom_id tG
  have hone : complementVanishing B (liftedIdeal.{u, u} A (twoGeneratorIdeal k)) ≤
      PrimeSpectrum.basicOpen (1 : B) := by
    with_unfolding_all
      simp only [PrimeSpectrum.basicOpen_one]
      exact le_top
  have htop : ∀ W : Opens (PrimeSpectrum.Top B), W ≤ PrimeSpectrum.basicOpen (1 : B) := fun W => by
    simp only [PrimeSpectrum.basicOpen_one]
    exact le_top
  have hfx' : f' • G.map c.op s =
      StructureSheaf.toOpenₗ B B (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) x' := by
    with_unfolding_all
      rw [← map_smul, hfx]
      change (structureSheafInType B B).1.map c.op
        (StructureSheaf.toOpenₗ B B (iSup U) x') = _
      rw [StructureSheaf.toOpenₗ_eq_const]
      exact (StructureSheaf.res_const x' 1 (iSup U) (htop _) _ (htop _) c.op).trans
        (StructureSheaf.toOpenₗ_eq_const _ x').symm
  have hgy' : g' • G.map c.op s =
      StructureSheaf.toOpenₗ B B (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) y' := by
    with_unfolding_all
      rw [← map_smul, hgy]
      change (structureSheafInType B B).1.map c.op
        (StructureSheaf.toOpenₗ B B (iSup U) y') = _
      rw [StructureSheaf.toOpenₗ_eq_const]
      exact (StructureSheaf.res_const y' 1 (iSup U) (htop _) _ (htop _) c.op).trans
        (StructureSheaf.toOpenₗ_eq_const _ y').symm
  have htoComp :
      (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).hom
          (toComplement A (twoGeneratorIdeal k) A (x k)) =
        StructureSheaf.toOpenₗ B B (complementVanishing B
          (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) x' := by
    simp [E, R, M, toComplement, AlgebraicGeometry.tilde.toOpen,
      AlgebraicGeometry.tilde.modulesSpecToSheafIso]
    rfl
  have htoCompY :
      (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).hom
          (toComplement A (twoGeneratorIdeal k) A (y k)) =
        StructureSheaf.toOpenₗ B B (complementVanishing B
          (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) y' := by
    simp [E, R, M, toComplement, AlgebraicGeometry.tilde.toOpen,
      AlgebraicGeometry.tilde.modulesSpecToSheafIso]
    rfl
  refine ⟨tH, ?_⟩
  constructor
  · have step1 : f k • tH = (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv (f' • tG) := by
      change f' • tH = (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv (f' • tG)
      exact (map_smul (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv.hom f' tG).symm
    have step2 : (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv (f' • tG) =
        (E.app (.op (complementVanishing B
          (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv
            (StructureSheaf.toOpenₗ B B (complementVanishing B
              (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) x') := by
      rw [hfx']
    have step3 : (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv
          (StructureSheaf.toOpenₗ B B (complementVanishing B
            (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) x') =
        toComplement A (twoGeneratorIdeal k) A (x k) := by
      rw [← htoComp]
      exact ConcreteCategory.congr_hom
        (E.app (.op (complementVanishing B
          (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).hom_inv_id
        (toComplement A (twoGeneratorIdeal k) A (x k))
    exact step1.trans (step2.trans step3)
  · have step1 : g k • tH = (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv (g' • tG) := by
      change g' • tH = (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv (g' • tG)
      exact (map_smul (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv.hom g' tG).symm
    have step2 : (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv (g' • tG) =
        (E.app (.op (complementVanishing B
          (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv
            (StructureSheaf.toOpenₗ B B (complementVanishing B
              (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) y') := by
      rw [hgy']
    have step3 : (E.app (.op (complementVanishing B
        (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).inv
          (StructureSheaf.toOpenₗ B B (complementVanishing B
            (liftedIdeal.{u, u} A (twoGeneratorIdeal k))) y') =
        toComplement A (twoGeneratorIdeal k) A (y k) := by
      rw [← htoCompY]
      exact ConcreteCategory.congr_hom
        (E.app (.op (complementVanishing B
          (liftedIdeal.{u, u} A (twoGeneratorIdeal k))))).hom_inv_id
        (toComplement A (twoGeneratorIdeal k) A (y k))
    exact step1.trans (step2.trans step3)

/-- The section on `D(f) ∪ D(g)` to which the fractions `x/f` and `y/g` glue. -/
@[stacks 01PN "two_generator_counterexample"]
noncomputable def gluedFractionSection :
    sectionsOnComplement (counterexampleRing k) (twoGeneratorIdeal k)
      (counterexampleRing k) := (gluedFractionSection_aux k).1

/-- `f` times the glued section is `x`, i.e. the section restricts to `x/f` on `D(f)`. -/
@[stacks 01PN "two_generator_counterexample"]
theorem gluedFractionSection_f :
    f k • gluedFractionSection k =
      toComplement (counterexampleRing k) (twoGeneratorIdeal k)
        (counterexampleRing k) (x k) := (gluedFractionSection_aux k).2.1

/-- `g` times the glued section is `y`, i.e. the section restricts to `y/g` on `D(g)`. -/
@[stacks 01PN "two_generator_counterexample"]
theorem gluedFractionSection_g :
    g k • gluedFractionSection k =
      toComplement (counterexampleRing k) (twoGeneratorIdeal k)
        (counterexampleRing k) (y k) := (gluedFractionSection_aux k).2.2

/-- Restricting the section of `𝒪` on the complement of `V(I)` attached to `m` down to a standard
open `D(f)` with `f ∈ I` gives the image of `m` under the canonical map to sections on `D(f)`. -/
lemma restrictToBasicOpen_toComplement_local (A : Type u) [CommRing A]
    (I : Ideal A) (f : A) (hf : f ∈ I) (m : A) :
    restrictToBasicOpen A I A f hf (toComplement A I A m) =
      (tilde.toOpen (ModuleCat.of (CommRingCat.of (ULift.{u, u} A)) (ULift.{u, u} A))
        (PrimeSpectrum.basicOpen (ULift.up.{u, u} f))).hom (ULift.up.{u, u} m) := by
  let B : Type u := ULift.{u, u} A
  let R : CommRingCat.{u} := .of B
  let M : ModuleCat R := ModuleCat.of R B
  let U := Stacks.AlgebraicGeometry.IdealPowerSections.complementVanishing B (liftedIdeal A I)
  let f' : B := ULift.up.{u, u} f
  let V := PrimeSpectrum.basicOpen f'
  have hf' : f' ∈ liftedIdeal A I := by
    change ULift.ringEquiv f' ∈ I
    simpa [ULift.ringEquiv] using hf
  have hUV : V ≤ U := Stacks.AlgebraicGeometry.IdealPowerSections.basicOpen_le_complementVanishing
    B (liftedIdeal A I) f' hf'
  have h := congrArg (fun q : M ⟶
      (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op V) => q (ULift.up m))
    (AlgebraicGeometry.tilde.toOpen_res M U V (homOfLE hUV))
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hUV).op)
      ((tilde.toOpen M U).hom (ULift.up.{u, u} m)) =
        (tilde.toOpen M V).hom (ULift.up.{u, u} m) at h
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hUV).op)
      ((tilde.toOpen M U).hom (ULift.up.{u, u} m)) =
        (tilde.toOpen M V).hom (ULift.up.{u, u} m)
  exact h

/-- If `h ∈ I` and `s` is a section on the complement of `V(I)` with `h • s = m`, which restricts
on `D(h)` to the fraction `φ(hⁿ) / hⁿ`, then `hᵈ⁺¹ φ(hⁿ) = hⁿ⁺ᵈ m` for all large `d`. -/
private lemma exists_pow_mul_eq_of_smul_eq {A : Type u} [CommRing A] {I : Ideal A} {h : A}
    (hh : h ∈ I) (m : A) (s : sectionsOnComplement A I A) (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] A)
    (hs : h • s = toComplement A I A m)
    (hz : canonicalMapToSections A I A (colimit.ι (idealPowersHom A I A) n φ) = s) :
    ∃ e : ℕ, ∀ d, e ≤ d →
      h ^ (d + 1) * φ ⟨h ^ n, Ideal.pow_mem_pow hh n⟩ = h ^ (n + d) * m := by
  have hres := (canonicalMapToSections_restrict_ι A I A n φ h hh).symm.trans
    (congrArg (restrictToBasicOpen A I A h hh) hz)
  have hmul := congrArg (fun q => h • q) hres
  rw [← map_smul, hs, restrictToBasicOpen_toComplement_local A I h hh m] at hmul
  let B := ULift.{u} A
  let R : CommRingCat.{u} := .of B
  let M : ModuleCat R := ModuleCat.of R B
  let h' : B := ULift.up h
  let m' : B := ULift.up m
  let mh : B := ULift.up (φ ⟨h ^ n, Ideal.pow_mem_pow hh n⟩)
  let pn : Submonoid.powers h' := ⟨h' ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩
  let If := basicOpenLocalizationEquiv M h'
  have hloc := congrArg If.symm hmul
  let : IsLocalizedModule.Away h' (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom :=
    .of_linearEquiv (Submonoid.powers h')
      (StructureSheaf.toOpenₗ B B (PrimeSpectrum.basicOpen h'))
      ((tilde.modulesSpecToSheafIso M).app _).toLinearEquiv.symm
  have hIfMk : If (LocalizedModule.mk mh pn) =
      IsLocalizedModule.mk' (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom mh pn :=
    IsLocalizedModule.iso_apply_mk (Submonoid.powers h')
      (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom mh _
  have hIfCancel : pn • IsLocalizedModule.mk'
      (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom mh pn =
      (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom mh :=
    IsLocalizedModule.mk'_cancel' _ _ _
  have hfrac : basicOpenFraction A A h n (φ ⟨h ^ n, Ideal.pow_mem_pow hh n⟩) =
      If (LocalizedModule.mk mh pn) := by
    rw [hIfMk]
    dsimp [basicOpenFraction, Stacks.AlgebraicGeometry.IdealPowerSections.basicOpenFraction,
      Stacks.AlgebraicGeometry.IdealPowerSections.tildeBasicOpenFraction, mh, pn, M, R, B]
  have hconvert : h • basicOpenFraction A A h n (φ ⟨h ^ n, Ideal.pow_mem_pow hh n⟩) =
      h' • If (LocalizedModule.mk mh pn) := by
    rw [hfrac]
    rfl
  have hcancel : pn • (h' • If (LocalizedModule.mk mh pn)) =
      (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom (h' • mh) := by
    calc
      _ = h' • (pn • If (LocalizedModule.mk mh pn)) := smul_comm (h' ^ n) h' _
      _ = h' • (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom mh := by
        rw [hIfMk, hIfCancel]
      _ = (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom (h' • mh) := by rw [← map_smul]
  have hsymm : If.symm (h' • If (LocalizedModule.mk mh pn)) = LocalizedModule.mk (h' • mh) pn :=
    IsLocalizedModule.iso_symm_apply' (Submonoid.powers h')
      (tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom _ (h' • mh) pn hcancel
  have hsymmOpen : If.symm ((tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom m') =
      LocalizedModule.mk m' 1 := by
    simp [If, basicOpenLocalizationEquiv]
  have hlocMk : LocalizedModule.mk (h' • mh) pn = LocalizedModule.mk m' 1 := by
    have h2 : If.symm (h • basicOpenFraction A A h n (φ ⟨h ^ n, Ideal.pow_mem_pow hh n⟩)) =
        If.symm ((tilde.toOpen M (PrimeSpectrum.basicOpen h')).hom m') := by
      with_unfolding_all exact hloc
    rw [hconvert, hsymm, hsymmOpen] at h2
    exact h2
  obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp hlocMk
  obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff (c : B) h').mp c.2
  refine ⟨e + 1, fun d hd => ?_⟩
  have hc' := hc
  simp only [Submonoid.smul_def, one_smul, smul_eq_mul] at hc'
  rw [← he, show (pn : B) = h' ^ n from rfl] at hc'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hB : h' ^ (e + 1 + j + 1) * mh = h' ^ (n + (e + 1 + j)) * m' := by
    calc
      _ = h' ^ (j + 1) * (h' ^ e * (h' * mh)) := by ring
      _ = h' ^ (j + 1) * (h' ^ e * (h' ^ n * m')) := by rw [hc']
      _ = _ := by ring
  exact congrArg ULift.down hB

/-- The glued fraction section is not obtained from a map out of any power of `(f,g)`. -/
@[stacks 01PN "two_generator_counterexample"]
theorem gluedFractionSection_not_mem_range :
    gluedFractionSection k ∉ Set.range (canonicalMapToSections (counterexampleRing k)
      (twoGeneratorIdeal k) (counterexampleRing k)) := by
  intro hmem
  rcases hmem with ⟨z, hz⟩
  let A := counterexampleRing k
  let F := idealPowersHom A (twoGeneratorIdeal k) A
  let J := ULiftHom.{u} (ULift.{u} ℕ)
  let E : ℕ ≌ J := ULiftHomULiftCategory.equiv.{u, u, 0, 0} ℕ
  let E' := E.symm
  let F' := E'.functor ⋙ F
  let G' := F' ⋙ forget₂ (ModuleCat A) AddCommGrpCat
  let w : E'.functor ⋙ F ≅ F' := Iso.refl _
  let eF : colimit F' ≅ colimit F := HasColimit.isoOfEquivalence E' w
  let : IsFiltered J := inferInstance
  let : PreservesColimitsOfShape J (forget AddCommGrpCat.{u}) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits.{u}
      |>.preserves_filtered_colimits J
  let e : (forget₂ (ModuleCat A) AddCommGrpCat).obj (colimit F') ≅ colimit G' :=
    preservesColimitIso (forget₂ (ModuleCat A) AddCommGrpCat) F'
  obtain ⟨i, φ, hφ⟩ := Concrete.colimit_exists_rep G' (e.hom (eF.inv z))
  change ↑(F.obj (E'.functor.obj i)) at φ
  have hrep : colimit.ι F (E'.functor.obj i) φ = z := by
    have hmap : e.hom ((colimit.ι F' i) φ) = colimit.ι G' i φ :=
      ConcreteCategory.congr_hom (ι_preservesColimitIso_hom
        (forget₂ (ModuleCat A) AddCommGrpCat) F' i) φ
    have heq : e.hom ((colimit.ι F' i) φ) = e.hom (eF.inv z) := hmap.trans hφ
    have hinv := congrArg (ConcreteCategory.hom e.inv) heq
    have hzrep : (colimit.ι F' i) φ = eF.inv z := by simpa using hinv
    have htransport : eF.hom ((colimit.ι F' i) φ) =
        (colimit.ι F (E'.functor.obj i)) φ :=
      ConcreteCategory.congr_hom
        (HasColimit.ι_isoOfEquivalence_hom E' w i) φ
    calc
      colimit.ι F (E'.functor.obj i) φ = eF.hom ((colimit.ι F' i) φ) := htransport.symm
      _ = z := by rw [hzrep]; simp
  have hf : f k ∈ twoGeneratorIdeal k := Ideal.subset_span (by simp)
  have hg : g k ∈ twoGeneratorIdeal k := Ideal.subset_span (by simp)
  have hz' := hz
  rw [← hrep] at hz'
  let n := E'.functor.obj i
  let φlin : (twoGeneratorIdeal k ^ n : Ideal A) →ₗ[A] A := φ
  obtain ⟨e₁, h₁⟩ := exists_pow_mul_eq_of_smul_eq hf (x k) _ n φlin
    (gluedFractionSection_f k) hz'
  obtain ⟨e₂, h₂⟩ := exists_pow_mul_eq_of_smul_eq hg (y k) _ n φlin
    (gluedFractionSection_g k) hz'
  let d := max e₁ e₂
  have hFscaleA := h₁ d (le_max_left _ _)
  have hGscaleA := h₂ d (le_max_right _ _)
  let vf : (twoGeneratorIdeal k ^ n : Ideal A) :=
    ⟨f k ^ n, Ideal.pow_mem_pow hf n⟩
  let vg : (twoGeneratorIdeal k ^ n : Ideal A) :=
    ⟨g k ^ n, Ideal.pow_mem_pow hg n⟩
  let relElt : (twoGeneratorIdeal k ^ n : Ideal A) :=
    ⟨a k (n + d) * f k ^ (n + d + 1) + b k (n + d) * g k ^ (n + d + 1), by
      rw [relation_at_index]
      exact zero_mem _⟩
  have hrelDecomp : relElt = a k (n + d) • (f k ^ (d + 1) • vf) +
      b k (n + d) • (g k ^ (d + 1) • vg) := by
    apply Subtype.ext
    change _ = a k (n + d) * (f k ^ (d + 1) * f k ^ n) + b k (n + d) * (g k ^ (d + 1) * g k ^ n)
    rw [← pow_add, ← pow_add, add_comm (d + 1) n, ← add_assoc]
  have hphiZero : φlin relElt = 0 := by
    rw [show relElt = 0 from Subtype.ext (relation_at_index k (n + d)), map_zero]
  rw [hrelDecomp] at hphiZero
  simp only [map_add, map_smul, smul_eq_mul] at hphiZero
  rw [hFscaleA, hGscaleA] at hphiZero
  exact obstruction_ne_zero k (n + d) (by simpa [mul_assoc] using hphiZero)

/-- The canonical map is not an isomorphism for the ideal `(f,g)`. -/
@[stacks 01PN "two_generator_counterexample"]
theorem canonicalMapToSections_not_isIso :
    ¬ IsIso (canonicalMapToSections (counterexampleRing k)
      (twoGeneratorIdeal k) (counterexampleRing k)) := by
  intro h
  apply gluedFractionSection_not_mem_range k
  refine ⟨inv (canonicalMapToSections (counterexampleRing k)
      (twoGeneratorIdeal k) (counterexampleRing k)) (gluedFractionSection k), ?_⟩
  have hh := congrArg (fun f => f.hom (gluedFractionSection k))
    (IsIso.inv_hom_id (canonicalMapToSections (counterexampleRing k)
      (twoGeneratorIdeal k) (counterexampleRing k)))
  exact hh

end Stacks.AlgebraicGeometry.TwoGeneratorCounterexample
