module

public import StacksFrontier.RingTheory.FormsTrace.Descent
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsIndependence

/-!
# Trace maps on differential forms over a directed union

Let `R → B` be a finite projective ring map which is the "union" of finite projective ring maps
`R_i → B_i`, `i ∈ ι`: each `B` is the base change `R ⊗_{R_i} B_i`, and every finite collection
of elements of `R`, of `B`, of forms of `R` and of forms of `B` comes from a single stage `i`.
Given, for every `i`, maps `Θ_i^p : Ω^p_{B_i} → Ω^p_{R_i}` with property (1) of Stacks,
Lemma 0FLB which are compatible (two forms of stages with the same image in `Ω^p_B` have
images under `Θ` with the same image in `Ω^p_R`), they glue to maps `Θ^p : Ω^p_B → Ω^p_R`
with property (1), compatible with every `Θ_i`, and inheriting property (2) of Proposition 0FLC
and compatibility with the de Rham differentials from the stages.

The compatibility condition is stated without transition maps; when stages `i, j` map to a
common stage `k` by ring maps forming pushout towers over `R → B`, and `Ω^p_{B_k} → Ω^p_B` is
injective, it follows from the compatibility of `Θ_i, Θ_j` with `Θ_k` along the transition
maps (`Stacks.FormsTrace.formsMap_eq_of_tower`).

## Main definitions

* `Stacks.FormsTrace.IsExhaustive`: every finite collection of elements and forms of `R` and `B`
  comes from one stage.
* `Stacks.FormsTrace.IsCompatibleFamily`: the compatibility of the stage maps.
* `Stacks.FormsTrace.colimitForms`: the glued maps `Θ^p`.

## Main results

* `Stacks.FormsTrace.colimitForms_formsMap`: `Θ^p(η|_B) = Θ_i^p(η)|_R`.
* `Stacks.FormsTrace.isFormsTrace_colimitForms`, `Stacks.FormsTrace.isWedgeLinear_colimitForms`,
  `Stacks.FormsTrace.commutesWithD_colimitForms`: the glued maps inherit the three conditions.
* `Stacks.FormsTrace.isExhaustive_of_eventually`: exhaustion follows from the eventual lifting of
  elements of `R` and of `B` along a filter on the stages (forms are sums of `r₀ dr₁ ∧ ⋯ ∧ dr_p`,
  `Stacks.FormsTrace.eventually_mem_range_formsMap`).
* `Stacks.FormsTrace.eq_of_forall_formsMap_eq`: uniqueness of the glued maps.
* `Stacks.FormsTrace.formsMap_eq_of_tower`: compatibility from transition maps.
* `Stacks.FormsTrace.formsMap_injective_of_leftInverse`: the pull-back of forms along a split
  injection is injective.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u v

namespace Stacks.FormsTrace

open DescentAux

section Colimit

variable {ι : Type v} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  {Rs Bs : ι → Type u} [∀ i, CommRing (Rs i)] [∀ i, CommRing (Bs i)]
  [∀ i, Algebra (Rs i) (Bs i)] [∀ i, Algebra (Rs i) R] [∀ i, Algebra (Bs i) B]

variable (R B Rs Bs) in
/-- **The stages exhaust `R → B`**: any element of `R`, element of `B`, form of `R` and two forms
of `B` of a common degree come from one stage. -/
def IsExhaustive : Prop :=
  ∀ (q p : ℕ) (r : R) (b : B) (ω : ⋀[R]^q Ω[R⁄ℤ]) (x y : ⋀[B]^p Ω[B⁄ℤ]), ∃ i : ι,
    r ∈ Set.range (algebraMap (Rs i) R) ∧ b ∈ Set.range (algebraMap (Bs i) B) ∧
      ω ∈ Set.range (formsMap (Rs i) R q) ∧ x ∈ Set.range (formsMap (Bs i) B p) ∧
        y ∈ Set.range (formsMap (Bs i) B p)

variable (R B) in
/-- **Compatibility of maps on the forms of the stages**: two forms of stages with the same image
in `Ω^p_B` are carried to forms of the stages with the same image in `Ω^p_R`. -/
def IsCompatibleFamily (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ]) :
    Prop :=
  ∀ (i j : ι) (p : ℕ) (η : ⋀[Bs i]^p Ω[Bs i⁄ℤ]) (η' : ⋀[Bs j]^p Ω[Bs j⁄ℤ]),
    formsMap (Bs i) B p η = formsMap (Bs j) B p η' →
      formsMap (Rs i) R p (Θs i p η) = formsMap (Rs j) R p (Θs j p η')

omit [Algebra R B] [∀ i, Algebra (Rs i) (Bs i)] in
/-- Every form of `B` comes from a stage. -/
theorem IsExhaustive.exists_formsMap_eq (hex : IsExhaustive R B Rs Bs) {p : ℕ}
    (x : ⋀[B]^p Ω[B⁄ℤ]) : ∃ (i : ι) (η : ⋀[Bs i]^p Ω[Bs i⁄ℤ]), formsMap (Bs i) B p η = x := by
  obtain ⟨i, -, -, -, ⟨η, hη⟩, -⟩ := hex 0 p 0 0 0 x x
  exact ⟨i, η, hη⟩

omit [∀ i, Algebra (Rs i) (Bs i)] [∀ i, Algebra (Bs i) B] [Algebra R B] in
/-- If every element of `R` eventually comes from the stages `R_i` (along a filter on the index
set), so does every form of `R`: the forms `r₀ dr₁ ∧ ⋯ ∧ dr_p` span `Ω^p_R` additively. -/
theorem eventually_mem_range_formsMap (l : Filter ι)
    (h : ∀ r : R, ∀ᶠ i in l, r ∈ Set.range (algebraMap (Rs i) R)) (p : ℕ)
    (ω : ⋀[R]^p Ω[R⁄ℤ]) : ∀ᶠ i in l, ω ∈ Set.range (formsMap (Rs i) R p) := by
  have hω : ω ∈ Submodule.span ℤ (Set.range fun r : Fin (p + 1) → R =>
      r 0 • exteriorPower.ιMulti R p fun j => D ℤ R (r j.succ)) := by
    rw [Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ) (D ℤ R)
      (KaehlerDifferential.span_range_derivation ℤ R) p]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    refine (Filter.eventually_all.2 fun j => h (r j)).mono fun i hi => ?_
    choose c hc using hi
    refine ⟨c 0 • exteriorPower.ιMulti (Rs i) p fun j => D ℤ (Rs i) (c j.succ), ?_⟩
    rw [map_smulₛₗ, formsMap_ιMulti, hc]
    simp only [KaehlerDifferential.map_D, hc]
  | zero => exact Filter.Eventually.of_forall fun i => ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    exact (hx.and hy).mono fun i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨a + b, by rw [map_add, ha, hb]⟩
  | smul n x _ hx =>
    exact hx.mono fun i ⟨a, ha⟩ => ⟨n • a, by rw [map_zsmul, ha]⟩

omit [Algebra R B] [∀ i, Algebra (Rs i) (Bs i)] in
/-- **Exhaustion from eventual lifting of elements.** If, along a nontrivial filter on the index
set, every element of `R` and every element of `B` eventually comes from the stages, then the
stages exhaust `R → B`. -/
theorem isExhaustive_of_eventually (l : Filter ι) [l.NeBot]
    (hR : ∀ r : R, ∀ᶠ i in l, r ∈ Set.range (algebraMap (Rs i) R))
    (hB : ∀ b : B, ∀ᶠ i in l, b ∈ Set.range (algebraMap (Bs i) B)) :
    IsExhaustive R B Rs Bs := by
  intro q p r b ω x y
  exact ((((hR r).and (hB b)).and (eventually_mem_range_formsMap l hR q ω)).and
    ((eventually_mem_range_formsMap l hB p x).and
      (eventually_mem_range_formsMap l hB p y))).exists.imp
    fun i ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩

variable [∀ i, Algebra (Rs i) B] [∀ i, IsScalarTower (Rs i) R B]
  [∀ i, IsScalarTower (Rs i) (Bs i) B]

/-- The value of the glued map on a form of `B`, computed on a chosen stage. -/
def colimitFormsFun (hex : IsExhaustive R B Rs Bs)
    (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ]) (p : ℕ)
    (x : ⋀[B]^p Ω[B⁄ℤ]) : ⋀[R]^p Ω[R⁄ℤ] :=
  formsMap (Rs (hex.exists_formsMap_eq x).choose) R p
    (Θs _ p (hex.exists_formsMap_eq x).choose_spec.choose)

omit [Algebra R B] [∀ i, Algebra (Rs i) B] [∀ i, IsScalarTower (Rs i) R B]
  [∀ i, IsScalarTower (Rs i) (Bs i) B] in
/-- The glued map on the image of a stage. -/
theorem colimitFormsFun_formsMap (hex : IsExhaustive R B Rs Bs)
    (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ])
    (hc : IsCompatibleFamily R B Θs) (i : ι) {p : ℕ} (η : ⋀[Bs i]^p Ω[Bs i⁄ℤ]) :
    colimitFormsFun hex Θs p (formsMap (Bs i) B p η) = formsMap (Rs i) R p (Θs i p η) :=
  hc _ _ _ _ _ (hex.exists_formsMap_eq (formsMap (Bs i) B p η)).choose_spec.choose_spec

/-- **The glued trace maps** `Θ^p : Ω^p_B → Ω^p_R` of a compatible family on the stages of an
exhaustion: the value on the image of a form `η` of a stage `i` is the image of `Θ_i^p(η)`. -/
def colimitForms (hex : IsExhaustive R B Rs Bs)
    (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ])
    (hc : IsCompatibleFamily R B Θs) (p : ℕ) : ⋀[B]^p Ω[B⁄ℤ] →ₗ[R] ⋀[R]^p Ω[R⁄ℤ] where
  toFun := colimitFormsFun hex Θs p
  map_add' x y := by
    obtain ⟨i, -, -, -, ⟨η, rfl⟩, ⟨η', rfl⟩⟩ := hex 0 p 0 0 0 x y
    rw [← map_add, colimitFormsFun_formsMap hex Θs hc, colimitFormsFun_formsMap hex Θs hc,
      colimitFormsFun_formsMap hex Θs hc, map_add, map_add]
  map_smul' r x := by
    obtain ⟨i, ⟨r, rfl⟩, -, -, ⟨η, rfl⟩, -⟩ := hex 0 p r 0 0 x x
    have h : algebraMap (Rs i) R r • formsMap (Bs i) B p η = formsMap (Bs i) B p (r • η) := by
      rw [← algebraMap_smul (Bs i) r η, map_smulₛₗ, ← algebraMap_smul B (algebraMap (Rs i) R r),
        ← IsScalarTower.algebraMap_apply (Rs i) R B, IsScalarTower.algebraMap_apply (Rs i) (Bs i) B]
    rw [h, colimitFormsFun_formsMap hex Θs hc, colimitFormsFun_formsMap hex Θs hc, map_smul,
      map_smulₛₗ, RingHom.id_apply]

/-- **The defining property of the glued maps**: `Θ^p(η|_B) = Θ_i^p(η)|_R` for a form `η` of a
stage `i`. -/
theorem colimitForms_formsMap (hex : IsExhaustive R B Rs Bs)
    (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ])
    (hc : IsCompatibleFamily R B Θs) (i : ι) (p : ℕ) (η : ⋀[Bs i]^p Ω[Bs i⁄ℤ]) :
    colimitForms hex Θs hc p (formsMap (Bs i) B p η) = formsMap (Rs i) R p (Θs i p η) :=
  colimitFormsFun_formsMap hex Θs hc i η

omit [∀ i, Algebra (Rs i) (Bs i)] [∀ i, Algebra (Rs i) R] [∀ i, Algebra (Rs i) B]
  [∀ i, IsScalarTower (Rs i) R B] [∀ i, IsScalarTower (Rs i) (Bs i) B] in
/-- **Uniqueness**: a family of maps on the forms of `B` is determined by its composites with the
restrictions from the stages. -/
theorem eq_of_forall_formsMap_eq (hex : ∀ (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]),
      ∃ (i : ι) (η : ⋀[Bs i]^p Ω[Bs i⁄ℤ]), formsMap (Bs i) B p η = x)
    {Θ₁ Θ₂ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[R] ⋀[R]^p Ω[R⁄ℤ]}
    (h : ∀ (i : ι) (p : ℕ) (η : ⋀[Bs i]^p Ω[Bs i⁄ℤ]),
      Θ₁ p (formsMap (Bs i) B p η) = Θ₂ p (formsMap (Bs i) B p η)) :
    Θ₁ = Θ₂ := by
  funext p
  refine LinearMap.ext fun x => ?_
  obtain ⟨i, η, rfl⟩ := hex p x
  exact h i p η

/-- **The glued maps satisfy `IsFormsTrace`** (property (1) of Lemma 0FLB) when every stage map
does and `B = R ⊗_{R_i} B_i` for every stage. -/
theorem isFormsTrace_colimitForms [Module.Finite R B] [Module.Projective R B]
    [∀ i, Module.Finite (Rs i) (Bs i)] [∀ i, Module.Projective (Rs i) (Bs i)]
    [∀ i, Algebra.IsPushout (Rs i) (Bs i) R B] (hex : IsExhaustive R B Rs Bs)
    (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ])
    (hc : IsCompatibleFamily R B Θs) (htr : ∀ i, IsFormsTrace (Rs i) (Bs i) (Θs i)) :
    IsFormsTrace R B (colimitForms hex Θs hc) := by
  intro p b ω
  obtain ⟨i, -, ⟨b, rfl⟩, ⟨ω, rfl⟩, -, -⟩ := hex p p 0 b ω 0 0
  rw [formsMap_formsMap, ← formsMap_formsMap (B := Bs i), ← map_smulₛₗ, colimitForms_formsMap,
    htr, map_smulₛₗ, trace_algebraMap_of_isPushout (R₁ := Rs i)]

/-- **The glued maps are `IsWedgeLinear`** (property (2) of Proposition 0FLC) when every stage map
is. -/
theorem isWedgeLinear_colimitForms (hex : IsExhaustive R B Rs Bs)
    (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ])
    (hc : IsCompatibleFamily R B Θs) (hw : ∀ i, IsWedgeLinear (Rs i) (Bs i) (Θs i)) :
    IsWedgeLinear R B (colimitForms hex Θs hc) := by
  intro q p ω η
  obtain ⟨i, -, -, ⟨ω, rfl⟩, ⟨η, rfl⟩, -⟩ := hex q p 0 0 ω η η
  rw [formsMap_formsMap, ← formsMap_formsMap (B := Bs i), ← formsMap_wedgeMul,
    colimitForms_formsMap, hw, formsMap_wedgeMul, colimitForms_formsMap]

/-- **The glued maps commute with the de Rham differentials** when every stage map does. -/
theorem commutesWithD_colimitForms (hex : IsExhaustive R B Rs Bs)
    (Θs : ∀ (i : ι) (p : ℕ), ⋀[Bs i]^p Ω[Bs i⁄ℤ] →ₗ[Rs i] ⋀[Rs i]^p Ω[Rs i⁄ℤ])
    (hc : IsCompatibleFamily R B Θs) (hd : ∀ i, CommutesWithD (Rs i) (Bs i) (Θs i)) :
    CommutesWithD R B (colimitForms hex Θs hc) := by
  intro p η
  obtain ⟨i, η, rfl⟩ := hex.exists_formsMap_eq η
  rw [← formsMap_deRhamDifferential, colimitForms_formsMap, hd, formsMap_deRhamDifferential,
    colimitForms_formsMap]

end Colimit

section Tower

variable {R B Ri Bi Rk Bk : Type u} [CommRing R] [CommRing B] [CommRing Ri] [CommRing Bi]
  [CommRing Rk] [CommRing Bk] [Algebra Ri Bi] [Algebra Rk Bk] [Algebra Ri Rk] [Algebra Bi Bk]
  [Algebra Ri R] [Algebra Rk R] [Algebra Bi B] [Algebra Bk B] [IsScalarTower Ri Rk R]
  [IsScalarTower Bi Bk B]

/-- **Compatibility along a transition map, read in the limit.** If a stage `i` maps to a stage
`k` (rings `R_i → R_k`, `B_i → B_k` forming towers over `R`, `B`) and `Θ_k(η|_{B_k}) =
Θ_i(η)|_{R_k}`, then `Θ_k(η|_{B_k})|_R = Θ_i(η)|_R`. -/
theorem formsMap_formsMap_eq_of_transition
    (Θi : ∀ p : ℕ, ⋀[Bi]^p Ω[Bi⁄ℤ] →ₗ[Ri] ⋀[Ri]^p Ω[Ri⁄ℤ])
    (Θk : ∀ p : ℕ, ⋀[Bk]^p Ω[Bk⁄ℤ] →ₗ[Rk] ⋀[Rk]^p Ω[Rk⁄ℤ]) {p : ℕ}
    (h : ∀ η : ⋀[Bi]^p Ω[Bi⁄ℤ], Θk p (formsMap Bi Bk p η) = formsMap Ri Rk p (Θi p η))
    (η : ⋀[Bi]^p Ω[Bi⁄ℤ]) :
    formsMap Rk R p (Θk p (formsMap Bi Bk p η)) = formsMap Ri R p (Θi p η) := by
  rw [h, formsMap_formsMap]

end Tower

/-- **The pull-back of forms along a split injection is injective**: if `ρ : B → A` is a
retraction of `A → B`, the pull-back along `ρ` is a left inverse. -/
theorem formsMap_injective_of_leftInverse {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (ρ : B →+* A) (hρ : ∀ a, ρ (algebraMap A B a) = a) (p : ℕ) :
    Function.Injective (formsMap A B p) := by
  let : Algebra B A := ρ.toAlgebra
  have : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a => (hρ a).symm
  refine Function.LeftInverse.injective (g := formsMap B A p) fun η => ?_
  rw [formsMap_formsMap]
  exact ExteriorAlgebra.powMapₛₗ_eq_self p _ (fun _ => rfl) (Stacks.DeRham.kaehlerMapₛₗ_self _) η

/-- **Compatibility from transition maps.** If stages `i` and `j` both map to a stage `k` (by
towers of ring maps over `R → B`), `Θ_i` and `Θ_j` are compatible with `Θ_k` along these maps, and
`Ω^p_{B_k} → Ω^p_B` is injective, then forms of `B_i` and `B_j` with the same image in `Ω^p_B`
are carried by `Θ_i`, `Θ_j` to forms with the same image in `Ω^p_R`. -/
theorem formsMap_eq_of_tower {R B Ri Bi Rj Bj Rk Bk : Type u} [CommRing R] [CommRing B]
    [CommRing Ri] [CommRing Bi] [CommRing Rj] [CommRing Bj] [CommRing Rk] [CommRing Bk]
    [Algebra Ri Bi] [Algebra Rj Bj] [Algebra Rk Bk] [Algebra Ri Rk] [Algebra Bi Bk]
    [Algebra Rj Rk] [Algebra Bj Bk] [Algebra Ri R] [Algebra Rj R] [Algebra Rk R] [Algebra Bi B]
    [Algebra Bj B] [Algebra Bk B] [IsScalarTower Ri Rk R] [IsScalarTower Bi Bk B]
    [IsScalarTower Rj Rk R] [IsScalarTower Bj Bk B]
    (Θi : ∀ p : ℕ, ⋀[Bi]^p Ω[Bi⁄ℤ] →ₗ[Ri] ⋀[Ri]^p Ω[Ri⁄ℤ])
    (Θj : ∀ p : ℕ, ⋀[Bj]^p Ω[Bj⁄ℤ] →ₗ[Rj] ⋀[Rj]^p Ω[Rj⁄ℤ])
    (Θk : ∀ p : ℕ, ⋀[Bk]^p Ω[Bk⁄ℤ] →ₗ[Rk] ⋀[Rk]^p Ω[Rk⁄ℤ]) {p : ℕ}
    (hinj : Function.Injective (formsMap Bk B p))
    (hi : ∀ η : ⋀[Bi]^p Ω[Bi⁄ℤ], Θk p (formsMap Bi Bk p η) = formsMap Ri Rk p (Θi p η))
    (hj : ∀ η : ⋀[Bj]^p Ω[Bj⁄ℤ], Θk p (formsMap Bj Bk p η) = formsMap Rj Rk p (Θj p η))
    (η : ⋀[Bi]^p Ω[Bi⁄ℤ]) (η' : ⋀[Bj]^p Ω[Bj⁄ℤ])
    (h : formsMap Bi B p η = formsMap Bj B p η') :
    formsMap Ri R p (Θi p η) = formsMap Rj R p (Θj p η') := by
  have hk : formsMap Bi Bk p η = formsMap Bj Bk p η' :=
    hinj (by rw [formsMap_formsMap, formsMap_formsMap, h])
  rw [← formsMap_formsMap_eq_of_transition Θi Θk hi, ← formsMap_formsMap_eq_of_transition Θj Θk hj,
    hk]

end Stacks.FormsTrace

end
