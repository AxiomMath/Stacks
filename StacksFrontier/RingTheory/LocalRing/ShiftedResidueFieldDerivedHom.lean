module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Maps out of the shifted residue field over a normal local domain of dimension at least two

Let `R` be a Noetherian normal local domain with maximal ideal `𝔪`, residue field
`κ = R/𝔪` and Krull dimension at least two, and let `E` be an object of `D(R)` with no
cohomology in negative degrees whose cohomology in degree zero is `R`. This file proves that a
morphism `α : κ[-1] ⟶ E` whose restriction along `R ⟶ κ` vanishes — that is, with
`(R[-1] ⟶ κ[-1]) ≫ α = 0` — is itself zero.

The algebraic input is that `𝔪` has no endomorphisms into `R` beyond the multiplications:
every `R`-linear map `𝔪 ⟶ R` is multiplication by an element of `R`, equivalently
`Hom_R(𝔪, R) = R`. Both halves are proved here.

## Main results

* `Stacks.NormalLocalDomain.maximalIdeal_ne_bot_of_one_lt_ringKrullDim`: over a Noetherian
  local ring of dimension at least two the maximal ideal is nonzero.
* `Stacks.NormalLocalDomain.exists_mul_eq_of_hom_maximalIdeal`: an `R`-linear map `𝔪 →ₗ[R] R`
  over a Noetherian normal local domain of dimension at least two is multiplication by an
  element of `R`.
* `Stacks.NormalLocalDomain.hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero`: a morphism
  `κ[-1] ⟶ E` in `D(R)` killed by precomposition with `R[-1] ⟶ κ[-1]` is zero.

## Implementation notes

*The algebraic half.* A map `g : 𝔪 →ₗ[R] R` satisfies `x · g(y) = y · g(x)`, so in the fraction
field `K` of `R` the quotient `a = g(x)/x` is independent of the nonzero `x ∈ 𝔪` chosen and
satisfies `a · x = g(x)` for every `x ∈ 𝔪`. There are two cases. If some `g(x)` is a unit then
`𝔪 = (x)`: for `y ∈ 𝔪` the identity `y · g(x) = x · g(y)` exhibits `y` as a multiple of `x`. A
principal maximal ideal has height at most one by Krull's principal ideal theorem
(`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing`), against the
hypothesis on the dimension; so in fact `g` maps `𝔪` into `𝔪`. Then `a` stabilises the
finitely generated nonzero `R`-submodule `𝔪 ⊆ K`, hence is integral over `R` by
`isIntegral_of_smul_mem_submodule`, hence lies in `R` because `R` is integrally closed.

*The homological half.* The short exact sequence `0 → 𝔪 → R → κ → 0` gives a distinguished
triangle `𝔪 ⟶ R ⟶ κ ⟶ 𝔪[1]` in `D(R)` by `ShortComplex.ShortExact.singleTriangle`. Shifting
`α` into a morphism `κ ⟶ E[1]` with the adjunction of the shift by `-1`, the vanishing
hypothesis places it, by `Pretriangulated.Triangle.yoneda_exact₃`, in the image of
precomposition with `κ ⟶ 𝔪[1]`: it is `δ ≫ β[1]` for some `β : 𝔪 ⟶ E`. Since `𝔪` and `R` sit in
degree zero and `E` has no cohomology in negative degrees, taking `H⁰` is a bijection on both
`Hom(𝔪, E)` and `Hom(R, E)` — this is
`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE` — so the algebraic half extends
`β` along `𝔪 ⟶ R`, writing `β = (𝔪 ⟶ R) ≫ γ`. Two consecutive morphisms of a distinguished
triangle compose to zero, so `α` is `δ ≫ (𝔪 ⟶ R)[1] ≫ γ[1] = 0`.

The hypothesis on the degree-zero cohomology of `E` is an isomorphism `H⁰(E) ≅ R` of
`R`-modules, which is what makes the algebraic half applicable; no compatibility with anything
else is required of it.

*Why not depth.* The statement `Hom_R(𝔪, R) = R` is the vanishing of `Ext⁰_R(κ, R)` and of
`Ext¹_R(κ, R)`, so `depth R ≥ 2` would give it; that route is not taken here, and should not be
taken in this library as it stands. `Module.depth` is referenced only from the per-tag statement files
and from `StacksFrontier/RingTheory/Serre/Criterion.lean`, and the library carries *two
incompatible definitions* of it which cannot be imported together: the implementation notes of
`StacksFrontier/RingTheory/Serre/Defs.lean` record that neither pair of Serre predicates "can be
restated in terms of the other until the two depths are merged". Normality together with the
dimension suffices on its own, through Krull's principal ideal theorem, and that is the proof
given here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace Stacks.NormalLocalDomain

/-! ### Maps from the maximal ideal to the ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- An `R`-linear map out of an ideal is symmetric on products: `x · g(y) = y · g(x)`. -/
private lemma mul_apply_comm (I : Ideal R) (g : I →ₗ[R] R) (x y : I) :
    (x : R) * g y = (y : R) * g x := by
  rw [← smul_eq_mul, ← g.map_smul, ← smul_eq_mul, ← g.map_smul]
  congr 1
  exact Subtype.ext (mul_comm _ _)

variable [IsLocalRing R] [IsNoetherianRing R]

/-- Over a Noetherian local ring of dimension at least two the maximal ideal is not
principal, since a principal maximal ideal has height at most one. -/
private lemma not_isPrincipal_maximalIdeal (hd : 1 < ringKrullDim R) :
    ¬ (IsLocalRing.maximalIdeal R).IsPrincipal := by
  intro hprin
  have hheight := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
    (IsLocalRing.maximalIdeal R) (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  have hdim : ringKrullDim R ≤ 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hheight
  exact (not_lt_of_ge hdim) hd

/-- Over a Noetherian local ring of dimension at least two, an `R`-linear map `𝔪 →ₗ[R] R` maps
the maximal ideal into itself: a value that was a unit would make `𝔪` principal. -/
private lemma apply_mem_maximalIdeal (hd : 1 < ringKrullDim R)
    (g : IsLocalRing.maximalIdeal R →ₗ[R] R) (x : IsLocalRing.maximalIdeal R) :
    g x ∈ IsLocalRing.maximalIdeal R := by
  by_contra hx
  have hunit : IsUnit (g x) := by simpa [IsLocalRing.mem_maximalIdeal] using hx
  obtain ⟨a, ha⟩ := hunit
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {(x : R)} := by
    apply le_antisymm
    · intro y hy
      rw [Ideal.mem_span_singleton]
      refine ⟨g ⟨y, hy⟩ * (↑a⁻¹ : R), ?_⟩
      calc
        y = y * (g x * (↑a⁻¹ : R)) := by rw [← ha, Units.mul_inv, mul_one]
        _ = x * (g ⟨y, hy⟩ * (↑a⁻¹ : R)) := by
          rw [← mul_assoc, ← mul_apply_comm _ g x ⟨y, hy⟩, mul_assoc]
    · exact Ideal.span_le.mpr (by simp)
  exact not_isPrincipal_maximalIdeal hd ⟨_, hm⟩

/-- **Over a Noetherian local ring of dimension at least two the maximal ideal is nonzero**,
since the zero ideal is principal and a principal maximal ideal has height at most one. -/
theorem maximalIdeal_ne_bot_of_one_lt_ringKrullDim (hd : 1 < ringKrullDim R) :
    IsLocalRing.maximalIdeal R ≠ ⊥ := by
  intro h
  exact not_isPrincipal_maximalIdeal hd
    (h ▸ inferInstanceAs (⊥ : Ideal R).IsPrincipal)

/-- **Every `R`-linear map from the maximal ideal to the ring is a multiplication.** Let `R` be
a Noetherian normal local domain of Krull dimension at least two with maximal ideal `𝔪`. Then
every `R`-linear map `g : 𝔪 →ₗ[R] R` is multiplication by an element of `R`; that is,
`Hom_R(𝔪, R) = R`.

The element is `g(x)/x` in the fraction field for any nonzero `x ∈ 𝔪`; it is integral over `R`
because it stabilises `𝔪`, which it does because `g` cannot take a unit value without making
`𝔪` principal, and it therefore lies in `R` because `R` is integrally closed. -/
theorem exists_mul_eq_of_hom_maximalIdeal [IsDomain R] [IsIntegrallyClosed R]
    (hd : 1 < ringKrullDim R) (g : IsLocalRing.maximalIdeal R →ₗ[R] R) :
    ∃ a : R, ∀ x : IsLocalRing.maximalIdeal R, g x = a * x := by
  let m := IsLocalRing.maximalIdeal R
  have hm : m ≠ ⊥ := maximalIdeal_ne_bot_of_one_lt_ringKrullDim hd
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff m).mp hm
  let K := FractionRing R
  let φ := algebraMap R K
  let a : K := φ (g ⟨x, hx⟩) / φ x
  have hxK : φ x ≠ 0 := by simpa [φ] using hx0
  have ha (y : m) : a * φ y = φ (g y) := by
    have h := congrArg φ (mul_apply_comm m g ⟨x, hx⟩ y)
    simp only [map_mul] at h
    dsimp [a]
    rw [div_mul_eq_mul_div, div_eq_iff hxK]
    simpa [mul_comm] using h.symm
  have hint : IsIntegral R a := by
    refine isIntegral_of_smul_mem_submodule (Submodule.map (Algebra.linearMap R K) m)
      ((Submodule.ne_bot_iff _).mpr ⟨φ x, ⟨x, hx, rfl⟩, hxK⟩)
      ((IsNoetherian.noetherian m).map _) a ?_
    rintro y ⟨r, hr, rfl⟩
    exact ⟨g ⟨r, hr⟩, apply_mem_maximalIdeal hd g _, by
      simpa [φ, Algebra.smul_def] using (ha ⟨r, hr⟩).symm⟩
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨b, fun y => IsFractionRing.injective R K ?_⟩
  rw [map_mul, hb]
  exact (ha y).symm

end Ring

/-! ### Maps out of the shifted residue field in the derived category -/

section Derived

/-- If the first morphism of a distinguished triangle is surjective on morphisms into `E` after
one shift, then every morphism into `E` out of the third vertex that is killed by the second
morphism of the triangle vanishes. -/
private lemma hom_eq_zero_of_comp_eq_zero_of_exists_comp
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (E : C)
    (h : ∀ β : T.obj₁⟦(1 : ℤ)⟧ ⟶ E, ∃ γ : T.obj₂⟦(1 : ℤ)⟧ ⟶ E, T.mor₁⟦(1 : ℤ)⟧' ≫ γ = β)
    (α : T.obj₃ ⟶ E) (hα : T.mor₂ ≫ α = 0) : α = 0 := by
  obtain ⟨β, rfl⟩ := T.yoneda_exact₃ hT α hα
  obtain ⟨γ, rfl⟩ := h β
  rw [← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
  [IsIntegrallyClosed R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- **Morphisms out of `𝔪` extend to `R`, in the derived category.** Let `R` be a Noetherian
normal local domain of dimension at least two and `E` an object of `D(R)` with no cohomology in
negative degrees whose degree-zero cohomology is `R`. Then every morphism `𝔪 ⟶ E` in `D(R)`,
the modules being placed in degree zero, factors through the inclusion `𝔪 ⟶ R`.

Taking `H⁰` is a bijection on morphisms from a module in degree zero to `E`, so this is
`exists_mul_eq_of_hom_maximalIdeal` read through that bijection. -/
private lemma exists_comp_eq_of_hom_single_maximalIdeal (hd : 1 < ringKrullDim R)
    (E : DerivedCategory (ModuleCat.{u} R)) [E.IsGE 0]
    (e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj E ≅ ModuleCat.of R R)
    (β : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (IsLocalRing.maximalIdeal R)) ⟶ E) :
    ∃ γ : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶ E,
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (IsLocalRing.maximalIdeal R).subtype) ≫ γ = β := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  let m := ModuleCat.of R (IsLocalRing.maximalIdeal R)
  let g : m ⟶ ModuleCat.of R R := ε.inv.app m ≫ H.map β ≫ e.hom
  obtain ⟨a, ha⟩ := exists_mul_eq_of_hom_maximalIdeal hd g.hom
  let c : ModuleCat.of R R ⟶ ModuleCat.of R R := ModuleCat.ofHom (a • LinearMap.id)
  have hc : ModuleCat.ofHom (IsLocalRing.maximalIdeal R).subtype ≫ c = g := by
    ext x
    exact (ha x).symm
  obtain ⟨γ, hγ⟩ := (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    (S.obj (ModuleCat.of R R)) E 0).surjective (ε.hom.app (ModuleCat.of R R) ≫ c ≫ e.inv)
  change H.map γ = ε.hom.app (ModuleCat.of R R) ≫ c ≫ e.inv at hγ
  refine ⟨γ, (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    (S.obj m) E 0).injective ?_⟩
  change H.map (S.map _ ≫ γ) = H.map β
  rw [H.map_comp, hγ]
  change H.map (S.map _) ≫ ε.hom.app _ ≫ c ≫ e.inv = H.map β
  have hn := ε.hom.naturality (ModuleCat.ofHom (IsLocalRing.maximalIdeal R).subtype)
  change H.map (S.map _) ≫ ε.hom.app _ = ε.hom.app _ ≫
    ModuleCat.ofHom (IsLocalRing.maximalIdeal R).subtype at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc, hc]
  dsimp only [g]
  dsimp only [S, H, m] at *
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [e.hom_inv_id, Category.comp_id]

/-- **A morphism out of `κ[-1]` that dies on `R[-1]` is zero.** Let `R` be a Noetherian normal
local domain of Krull dimension at least two, with maximal ideal `𝔪` and residue field `κ`, and
let `E` be an object of `D(R)` with no cohomology in negative degrees and with `H⁰(E) ≅ R`. If
a morphism `α : κ[-1] ⟶ E` is killed by precomposition with the shift of `R ⟶ κ`, then `α = 0`.

The hypothesis is exactly the vanishing of the image of `α` under
`Hom(κ[-1], E) ⟶ Hom(R[-1], E)`, so this says that map is injective. The proof factors `α`
through `𝔪` using the triangle of `0 → 𝔪 → R → κ → 0` and then extends that factorisation
along `𝔪 ⟶ R`, where it becomes a composite of two consecutive morphisms of a distinguished
triangle. -/
theorem hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero (hd : 1 < ringKrullDim R)
    (E : DerivedCategory (ModuleCat.{u} R)) [E.IsGE 0]
    (e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj E ≅ ModuleCat.of R R)
    (α : ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R)))⟦(-1 : ℤ)⟧ ⟶ E)
    (hα : ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      (ModuleCat.ofHom (IsLocalRing.maximalIdeal R).mkQ))⟦(-1 : ℤ)⟧' ≫ α = 0) :
    α = 0 := by
  let m := IsLocalRing.maximalIdeal R
  let S := ShortComplex.moduleCatMk m.subtype m.mkQ
    (LinearMap.exact_subtype_mkQ m).linearMap_comp_eq_zero
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
        (LinearMap.exact_subtype_mkQ m)
      mono_f := (ModuleCat.mono_iff_injective _).mpr m.subtype_injective
      epi_g := (ModuleCat.epi_iff_surjective _).mpr m.mkQ_surjective }
  let adj :=
    (shiftEquiv' (DerivedCategory (ModuleCat.{u} R)) (-1 : ℤ) 1 (by norm_num)).toAdjunction
  have hz (M : DerivedCategory (ModuleCat.{u} R)) : adj.homEquiv M E 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  refine (adj.homEquiv _ E).injective (Eq.trans ?_ (hz _).symm)
  apply hom_eq_zero_of_comp_eq_zero_of_exists_comp hS.singleTriangle
    hS.singleTriangle_distinguished (E⟦(1 : ℤ)⟧)
  · intro β
    obtain ⟨β₀, rfl⟩ :=
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)).map_surjective β
    obtain ⟨γ, rfl⟩ := exists_comp_eq_of_hom_single_maximalIdeal hd E e β₀
    exact ⟨γ⟦(1 : ℤ)⟧',
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)).map_comp _ γ).symm⟩
  · exact (adj.homEquiv_naturality_left
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom m.mkQ)) α).symm.trans
      ((congrArg (adj.homEquiv _ E) hα).trans (hz _))

end Derived

end Stacks.NormalLocalDomain

end
