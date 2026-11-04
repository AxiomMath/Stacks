module

public import StacksFrontier.RingTheory.FormsTrace.ColimitPolynomial
public import StacksFrontier.RingTheory.FormsTrace.DegreeOne
public import StacksFrontier.RingTheory.FormsTrace.UniversalComparison

/-!
# Existence of the trace maps on forms over polynomial charts

Let `R` be a ring, formally smooth over `ℤ`, and `c : A_d → R` a classifying map of the universal
finite free family whose discriminant `Δ` is a nonzerodivisor. For a set of variables `σ` let
`R[x_σ]` be the polynomial chart (`Stacks.FormsTrace.polynomialChart σ R`) and `B_σ` the base
change of the universal family to it (the algebra `Carrier (tableOfHom c_σ)` of the classifying
map `c_σ : A_d → R → R[x_σ]`). This file shows that `B_σ / R[x_σ]` carries trace maps on forms
`Θ^p : Ω^p_{B_σ} → Ω^p_{R[x_σ]}` with property (1) of Stacks, Lemma 0FLB, property (2) of
Proposition 0FLC, which commute with the de Rham differentials, granted the existence of maps
with property (1) for finitely many variables. The universal charts `N_g[x_σ]` and the charts
over the comparison rings are the two instances.

The proof is the passage to the limit in the proof of Proposition 0FLC:

* the stages are the charts `R[x_F] → B_F` for the finite subsets `F ⊆ σ`; they map to
  `R[x_σ] → B_σ` by renaming the variables, `B_σ = R[x_σ] ⊗_{R[x_F]} B_F`, every element of
  `R[x_σ]` and of `B_σ` involves finitely many variables, and `Ω^p_{B_F} → Ω^p_{B_σ}` is split
  injective (send the other variables to `0`);
* any two stage maps with property (1) are compatible along `F ⊆ F'`, because the image of `Δ` is
  a nice element on every chart (`Stacks.FormsTrace.discr_polynomialChart_nice`) and
  `Stacks.FormsTrace.IsFormsTrace.formsMap_comm_of_isPushout`;
* the glued maps (`Stacks.FormsTrace.colimitForms`) have property (1), and properties (2) and
  the compatibility with `d` follow from the niceness of the image of `Δ` on `R[x_σ]`.

## Main definitions

* `Stacks.FormsTrace.carrierHom`: the coordinatewise map `B_{c₁} → B_{c₂}` induced by a ring map
  `φ` with `φ ∘ c₁ = c₂`.

## Main results

* `Stacks.FormsTrace.isPushout_carrier_of_coord`: the square of a coordinatewise map of tables is
  a pushout.
* `Stacks.FormsTrace.exists_isFormsTrace_polynomialChart_of_finite`: the trace maps on a
  polynomial chart, from the trace maps with property (1) on the charts in finitely many
  variables.
* `Stacks.FormsTrace.exists_isFormsTrace_universalChart_of_finite`,
  `Stacks.FormsTrace.exists_isFormsTrace_comparisonChart_of_finite`: the universal charts and the
  comparison charts.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra MvPolynomial
open scoped TensorProduct nonZeroDivisors

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

section CarrierHom

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]

/-- The identification of the algebras of two equal tables. -/
def carrierCast {R : Type u} [CommRing R] {m m' : FiniteFreeAlgebra R d} (h : m = m') :
    Carrier m →+* Carrier m' :=
  h ▸ RingHom.id _

/-- The identification `carrierCast h` of the algebras of two equal tables preserves the
coordinates. -/
theorem carrierCast_apply {R : Type u} [CommRing R] {m m' : FiniteFreeAlgebra R d} (h : m = m')
    (x : Carrier m) (k : Fin d) : carrierCast h x k = x k := by
  subst h; rfl

/-- **The coordinatewise map of tables** `B_{c₁} → B_{c₂}` induced by a ring map `φ : R₁ → R₂` with
`φ ∘ c₁ = c₂`. -/
def carrierHom {c₁ : universalRing d →+* R₁} {c₂ : universalRing d →+* R₂} (φ : R₁ →+* R₂)
    (h : φ.comp c₁ = c₂) : Carrier (tableOfHom c₁) →+* Carrier (tableOfHom c₂) :=
  (carrierCast ((map_tableOfHom c₁ φ).trans (congrArg tableOfHom h))).comp
    (Carrier.mapRingHom φ (tableOfHom c₁))

/-- The `k`-th coordinate of `carrierHom φ h x` is `φ` applied to the `k`-th coordinate of `x`. -/
theorem carrierHom_apply {c₁ : universalRing d →+* R₁} {c₂ : universalRing d →+* R₂}
    (φ : R₁ →+* R₂) (h : φ.comp c₁ = c₂) (x : Carrier (tableOfHom c₁)) (k : Fin d) :
    carrierHom φ h x k = φ (x k) := by
  rw [carrierHom, RingHom.comp_apply, carrierCast_apply, Carrier.mapRingHom_apply]

/-- The map `carrierHom φ h` sends the image of `r ∈ R₁` in `B_{c₁}` to the image of `φ r` in
`B_{c₂}`. -/
theorem carrierHom_algebraMap {c₁ : universalRing d →+* R₁} {c₂ : universalRing d →+* R₂}
    (φ : R₁ →+* R₂) (h : φ.comp c₁ = c₂) (r : R₁) :
    carrierHom φ h (algebraMap R₁ (Carrier (tableOfHom c₁)) r) =
      algebraMap R₂ (Carrier (tableOfHom c₂)) (φ r) := by
  refine Carrier.ext fun k => ?_
  rw [carrierHom_apply, Carrier.algebraMap_coord, Carrier.algebraMap_coord]
  split <;> simp

/-- The composite of the coordinatewise maps induced by `φ` and `ψ` is the coordinatewise map
induced by `ψ ∘ φ`. -/
theorem carrierHom_carrierHom {c₁ : universalRing d →+* R₁} {c₂ : universalRing d →+* R₂}
    {c₃ : universalRing d →+* R₃} (φ : R₁ →+* R₂) (h : φ.comp c₁ = c₂) (ψ : R₂ →+* R₃)
    (h' : ψ.comp c₂ = c₃) (x : Carrier (tableOfHom c₁)) :
    carrierHom ψ h' (carrierHom φ h x) =
      carrierHom (ψ.comp φ) (by rw [RingHom.comp_assoc, h, h']) x :=
  Carrier.ext fun k => by
    rw [carrierHom_apply, carrierHom_apply, carrierHom_apply]
    rfl

/-- **The square of a coordinatewise map of tables is a pushout**: `B_{c₂} = R₂ ⊗_{R₁} B_{c₁}` when
the map `B_{c₁} → B_{c₂}` acts coordinatewise through `R₁ → R₂`. -/
theorem isPushout_carrier_of_coord [Algebra R₁ R₂] {c₁ : universalRing d →+* R₁}
    {c₂ : universalRing d →+* R₂} [Algebra (Carrier (tableOfHom c₁)) (Carrier (tableOfHom c₂))]
    [Algebra R₁ (Carrier (tableOfHom c₂))] [IsScalarTower R₁ R₂ (Carrier (tableOfHom c₂))]
    [IsScalarTower R₁ (Carrier (tableOfHom c₁)) (Carrier (tableOfHom c₂))]
    (hB : ∀ (x : Carrier (tableOfHom c₁)) (k : Fin d),
      algebraMap (Carrier (tableOfHom c₁)) (Carrier (tableOfHom c₂)) x k = algebraMap R₁ R₂ (x k)) :
    Algebra.IsPushout R₁ (Carrier (tableOfHom c₁)) R₂ (Carrier (tableOfHom c₂)) := by
  refine isPushout_of_bases_one (Carrier.basis _) (Carrier.basis _) fun x => ?_
  refine Carrier.ext fun k => ?_
  have hterm : ∀ i : Fin d,
      (algebraMap R₁ R₂ ((Carrier.basis (tableOfHom c₁)).repr x i) •
        Carrier.basis (tableOfHom c₂) i) k =
        algebraMap R₁ R₂ (x i) * (if k = i then (1 : R₂) else 0) := by
    intro i
    rw [Carrier.smul_apply, Carrier.basis_apply, Carrier.basisVector_apply]
    rfl
  rw [hB, Carrier.sum_apply, Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_eq_single k (fun i _ hi => by simp [Ne.symm hi])
      (fun h => absurd (Finset.mem_univ k) h)]
  simp

end CarrierHom

section Chart

variable {σ : Type u} {R : Type u} [CommRing R] {c : universalRing d →+* R}

variable (c) in
/-- The classifying map `A_d → R[x_τ]` of the base change of `B_c` to the polynomial chart. -/
abbrev chartClassify (τ : Type u) : universalRing d →+* polynomialChart τ R :=
  (algebraMap R (polynomialChart τ R)).comp c

/-- The renaming of variables `R[x_F] → R[x_σ]` for `F ⊆ σ`, between the chart rings. -/
def chartRename (F : Finset σ) : polynomialChart (↥F) R →+* polynomialChart σ R :=
  (rename (R := R) (Subtype.val : F → σ)).toRingHom

/-- The transition map `R_F → R_{F'}` for `F ⊆ F'`, between the chart rings. -/
def chartTransition {F F' : Finset σ} (h : F ⊆ F') :
    polynomialChart (↥F) R →+* polynomialChart (↥F') R :=
  (rename (R := R) (PolynomialStages.inclusion h)).toRingHom

/-- The retraction `R_σ → R_F` sending the variables outside `F` to `0`. -/
def chartRetraction (F : Finset σ) : polynomialChart σ R →+* polynomialChart (↥F) R :=
  (PolynomialStages.retraction R F).toRingHom

/-- A map of polynomial rings over `R` which is the identity on `R` is compatible with the
classifying maps of the charts. -/
theorem comp_chartClassify {τ τ' : Type u} (φ : MvPolynomial τ R →ₐ[R] MvPolynomial τ' R) :
    (φ.toRingHom : polynomialChart τ R →+* polynomialChart τ' R).comp
      (chartClassify c τ) = chartClassify c τ' := by
  refine RingHom.ext fun a => ?_
  exact φ.commutes _

/-- The renaming `R[x_F] → R[x_σ]` carries the classifying map of the chart in `F` to that of the
chart in `σ`. -/
theorem chartRename_classify (F : Finset σ) :
    (chartRename F).comp (chartClassify c (↥F)) = chartClassify c σ :=
  comp_chartClassify _

/-- The transition map `R[x_F] → R[x_{F'}]` carries the classifying map of the chart in `F` to that
of the chart in `F'`. -/
theorem chartTransition_classify {F F' : Finset σ} (h : F ⊆ F') :
    (chartTransition (R := R) h).comp (chartClassify c (↥F)) =
      chartClassify c (↥F') :=
  comp_chartClassify _

/-- The retraction `R[x_σ] → R[x_F]` carries the classifying map of the chart in `σ` to that of the
chart in `F`. -/
theorem chartRetraction_classify (F : Finset σ) :
    (chartRetraction F).comp (chartClassify c σ) = chartClassify c (↥F) :=
  comp_chartClassify _

/-- For `F ⊆ F'`, renaming along `F' ⊆ σ` after the transition `R[x_F] → R[x_{F'}]` is renaming
along `F ⊆ σ`. -/
theorem chartRename_chartTransition {F F' : Finset σ} (h : F ⊆ F')
    (x : polynomialChart (↥F) R) :
    chartRename F' (chartTransition h x) = chartRename F x :=
  PolynomialStages.rename_val_rename_inclusion _ h x

/-- The retraction `R[x_σ] → R[x_F]` is a left inverse of the renaming `R[x_F] → R[x_σ]`. -/
theorem chartRetraction_chartRename (F : Finset σ) (x : polynomialChart (↥F) R) :
    chartRetraction F (chartRename F x) = x :=
  PolynomialStages.retraction_rename _ F x

/-- The stage algebra structure `R_F → R_σ`, renaming the variables. -/
@[instance_reducible]
def chartAlgebra (F : Finset σ) : Algebra (polynomialChart (↥F) R) (polynomialChart σ R) :=
  (chartRename F).toAlgebra

/-- The stage algebra structure `B_F → B_σ`. -/
@[instance_reducible]
def chartCarrierAlgebra (F : Finset σ) :
    Algebra (Carrier (tableOfHom (chartClassify c (↥F))))
      (Carrier (tableOfHom (chartClassify c σ))) :=
  (carrierHom (chartRename F) (chartRename_classify F)).toAlgebra

/-- The stage algebra structure `R_F → B_σ`. -/
@[instance_reducible]
def chartCarrierAlgebra' (F : Finset σ) :
    Algebra (polynomialChart (↥F) R) (Carrier (tableOfHom (chartClassify c σ))) :=
  ((algebraMap (polynomialChart σ R) (Carrier (tableOfHom (chartClassify c σ)))).comp
    (chartRename F)).toAlgebra

attribute [local instance] chartAlgebra chartCarrierAlgebra chartCarrierAlgebra'

/-- The algebras `R[x_F] → R[x_σ] → B_σ` form a scalar tower. -/
theorem chart_isScalarTower (F : Finset σ) :
    IsScalarTower (polynomialChart (↥F) R) (polynomialChart σ R)
      (Carrier (tableOfHom (chartClassify c σ))) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The algebras `R[x_F] → B_F → B_σ` form a scalar tower. -/
theorem chart_isScalarTower' (F : Finset σ) :
    IsScalarTower (polynomialChart (↥F) R) (Carrier (tableOfHom (chartClassify c (↥F))))
      (Carrier (tableOfHom (chartClassify c σ))) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (carrierHom_algebraMap (chartRename F) (chartRename_classify F) r).symm

attribute [local instance] chart_isScalarTower chart_isScalarTower'

/-- The stage square is a pushout: `B_σ = R[x_σ] ⊗_{R[x_F]} B_F`. -/
theorem chart_isPushout (F : Finset σ) :
    Algebra.IsPushout (polynomialChart (↥F) R)
      (Carrier (tableOfHom (chartClassify c (↥F)))) (polynomialChart σ R)
      (Carrier (tableOfHom (chartClassify c σ))) :=
  isPushout_carrier_of_coord fun x k => carrierHom_apply _ _ x k

attribute [local instance] chart_isPushout

/-- The forms of a stage inject into the forms of `B_σ`. -/
theorem chart_formsMap_injective (F : Finset σ) (p : ℕ) :
    Function.Injective (formsMap (Carrier (tableOfHom (chartClassify c (↥F))))
      (Carrier (tableOfHom (chartClassify c σ))) p) := by
  refine formsMap_injective_of_leftInverse
    (carrierHom (chartRetraction F) (chartRetraction_classify F)) (fun x => ?_) p
  show carrierHom _ _ (carrierHom _ _ x) = x
  refine Carrier.ext fun k => ?_
  rw [carrierHom_apply, carrierHom_apply, chartRetraction_chartRename]

/-- The charts in finitely many variables exhaust the chart in the variables `σ`. -/
theorem chart_isExhaustive :
    IsExhaustive (polynomialChart σ R) (Carrier (tableOfHom (chartClassify c σ)))
      (fun F : Finset σ => polynomialChart (↥F) R)
      (fun F : Finset σ => Carrier (tableOfHom (chartClassify c (↥F)))) := by
  have hR : ∀ r : polynomialChart σ R, ∀ᶠ F : Finset σ in Filter.atTop,
      r ∈ Set.range (algebraMap (polynomialChart (↥F) R) (polynomialChart σ R)) := by
    intro r
    obtain ⟨s, q, hq⟩ := exists_finset_rename (R := R) r
    exact Filter.eventually_atTop.2 ⟨s, fun F hF =>
      ⟨chartTransition hF q, (chartRename_chartTransition hF q).trans hq.symm⟩⟩
  refine isExhaustive_of_eventually Filter.atTop hR fun b => ?_
  refine (Filter.eventually_all.2 fun k => hR (b k)).mono fun F hF => ?_
  choose q hq using hF
  let y : Carrier (tableOfHom (chartClassify c (↥F))) := q
  refine ⟨y, Carrier.ext fun k => ?_⟩
  show carrierHom _ _ y k = b k
  rw [carrierHom_apply]
  exact hq k

/-- The discriminant of the chart in the variables `τ`. -/
abbrev chartDiscr (τ : Type u) (c : universalRing d →+* R) : polynomialChart τ R :=
  Algebra.discr (polynomialChart τ R) (Carrier.basis (tableOfHom (chartClassify c τ)))

/-- **Any two trace maps with property (1) on the charts are compatible along `F ⊆ F'`**, the
discriminant being a nice element of every chart. -/
theorem chart_transition_comm [Algebra.FormallySmooth ℤ R]
    (hc : Algebra.discr R (Carrier.basis (tableOfHom c)) ∈ R⁰) {F F' : Finset σ} (h : F ⊆ F')
    {Θ : ∀ p : ℕ, ⋀[Carrier (tableOfHom (chartClassify c (↥F)))]^p
      Ω[Carrier (tableOfHom (chartClassify c (↥F)))⁄ℤ] →ₗ[polynomialChart (↥F) R]
        ⋀[polynomialChart (↥F) R]^p Ω[polynomialChart (↥F) R⁄ℤ]}
    {Θ' : ∀ p : ℕ, ⋀[Carrier (tableOfHom (chartClassify c (↥F')))]^p
      Ω[Carrier (tableOfHom (chartClassify c (↥F')))⁄ℤ] →ₗ[polynomialChart (↥F') R]
        ⋀[polynomialChart (↥F') R]^p Ω[polynomialChart (↥F') R⁄ℤ]}
    (hΘ : IsFormsTrace _ _ Θ) (hΘ' : IsFormsTrace _ _ Θ') :
    letI : Algebra (polynomialChart (↥F) R) (polynomialChart (↥F') R) :=
      (chartTransition h).toAlgebra
    letI : Algebra (Carrier (tableOfHom (chartClassify c (↥F))))
        (Carrier (tableOfHom (chartClassify c (↥F')))) :=
      (carrierHom (chartTransition h) (chartTransition_classify h)).toAlgebra
    ∀ (p : ℕ) (η : ⋀[Carrier (tableOfHom (chartClassify c (↥F)))]^p
      Ω[Carrier (tableOfHom (chartClassify c (↥F)))⁄ℤ]),
      Θ' p (formsMap _ _ p η) = formsMap _ _ p (Θ p η) := by
  let : Algebra (polynomialChart (↥F) R) (polynomialChart (↥F') R) :=
    (chartTransition h).toAlgebra
  let : Algebra (Carrier (tableOfHom (chartClassify c (↥F))))
      (Carrier (tableOfHom (chartClassify c (↥F')))) :=
    (carrierHom (chartTransition h) (chartTransition_classify h)).toAlgebra
  let : Algebra (polynomialChart (↥F) R)
      (Carrier (tableOfHom (chartClassify c (↥F')))) :=
    ((algebraMap (polynomialChart (↥F') R)
      (Carrier (tableOfHom (chartClassify c (↥F'))))).comp (chartTransition h)).toAlgebra
  have : IsScalarTower (polynomialChart (↥F) R) (polynomialChart (↥F') R)
      (Carrier (tableOfHom (chartClassify c (↥F')))) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (polynomialChart (↥F) R)
      (Carrier (tableOfHom (chartClassify c (↥F))))
      (Carrier (tableOfHom (chartClassify c (↥F')))) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (carrierHom_algebraMap (chartTransition h) (chartTransition_classify h) r).symm
  have : Algebra.IsPushout (polynomialChart (↥F) R)
      (Carrier (tableOfHom (chartClassify c (↥F)))) (polynomialChart (↥F') R)
      (Carrier (tableOfHom (chartClassify c (↥F')))) :=
    isPushout_carrier_of_coord fun x k => carrierHom_apply _ _ x k
  obtain ⟨n, hn⟩ := (discr_polynomialChart_nice (σ := ↥F) c hc).pow_smul_kaehler
  have hdiscr : algebraMap (polynomialChart (↥F) R) (polynomialChart (↥F') R)
      (chartDiscr (↥F) c) = chartDiscr (↥F') c := by
    show chartTransition h _ = _
    rw [chartDiscr, chartDiscr, discr_tableOfHom, discr_tableOfHom, ← RingHom.comp_apply,
      chartTransition_classify]
  intro p η
  refine IsFormsTrace.formsMap_comm_of_isPushout hn (fun q => ?_) hΘ hΘ' p η
  rw [hdiscr]
  exact (discr_polynomialChart_nice (σ := ↥F') c hc).regular q

/-- The renamings `R[x_G] → R[x_k] → R[x_σ]` form a scalar tower for `G ⊆ k`. -/
private theorem chart_isScalarTower_transition {G k : Finset σ} (hG : G ⊆ k)
    [Algebra (polynomialChart (↥G) R) (polynomialChart (↥k) R)]
    (h : algebraMap (polynomialChart (↥G) R) (polynomialChart (↥k) R) = chartTransition hG) :
    IsScalarTower (polynomialChart (↥G) R) (polynomialChart (↥k) R) (polynomialChart σ R) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [h]
    exact (chartRename_chartTransition hG x).symm

/-- The coordinatewise maps `B_G → B_k → B_σ` form a scalar tower for `G ⊆ k`. -/
private theorem chart_isScalarTower_carrier_transition {G k : Finset σ} (hG : G ⊆ k)
    [Algebra (Carrier (tableOfHom (chartClassify c (↥G))))
      (Carrier (tableOfHom (chartClassify c (↥k))))]
    (h : algebraMap (Carrier (tableOfHom (chartClassify c (↥G))))
      (Carrier (tableOfHom (chartClassify c (↥k)))) =
        carrierHom (chartTransition hG) (chartTransition_classify hG)) :
    IsScalarTower (Carrier (tableOfHom (chartClassify c (↥G))))
      (Carrier (tableOfHom (chartClassify c (↥k)))) (Carrier (tableOfHom (chartClassify c σ))) := by
  refine IsScalarTower.of_algebraMap_eq fun x => Carrier.ext fun j => ?_
  show carrierHom _ _ x j = carrierHom _ _ (algebraMap _ _ x) j
  rw [h, carrierHom_apply, carrierHom_apply, carrierHom_apply, chartRename_chartTransition]

/-- **The trace maps on a polynomial chart, from the charts in finitely many variables.** Let
`R` be formally smooth over `ℤ` and `c : A_d → R` a classifying map whose discriminant is a
nonzerodivisor, and let `σ` be any set of variables. If for every finite set of variables `τ` the
chart `R[x_τ] → B_τ` carries maps with property (1) of Stacks, Lemma 0FLB, then the chart
`R[x_σ] → B_σ` carries maps `Θ^p : Ω^p_{B_σ} → Ω^p_{R[x_σ]}` with property (1), property (2) of
Proposition 0FLC, and commuting with the de Rham differentials. -/
theorem exists_isFormsTrace_polynomialChart_of_finite (σ : Type u) {R : Type u} [CommRing R]
    [Algebra.FormallySmooth ℤ R] (c : universalRing d →+* R)
    (hc : Algebra.discr R (Carrier.basis (tableOfHom c)) ∈ R⁰)
    (hfin : ∀ (τ : Type u) [Finite τ], ∃ Θ : ∀ p : ℕ,
      ⋀[Carrier (tableOfHom ((algebraMap R (polynomialChart τ R)).comp c))]^p
        Ω[Carrier (tableOfHom ((algebraMap R (polynomialChart τ R)).comp c))⁄ℤ]
          →ₗ[polynomialChart τ R] ⋀[polynomialChart τ R]^p Ω[polynomialChart τ R⁄ℤ],
        IsFormsTrace (polynomialChart τ R)
          (Carrier (tableOfHom ((algebraMap R (polynomialChart τ R)).comp c))) Θ) :
    ∃ Θ : ∀ p : ℕ, ⋀[Carrier (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c))]^p
        Ω[Carrier (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c))⁄ℤ]
          →ₗ[polynomialChart σ R] ⋀[polynomialChart σ R]^p Ω[polynomialChart σ R⁄ℤ],
      IsFormsTrace (polynomialChart σ R)
        (Carrier (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c))) Θ ∧
      IsWedgeLinear (polynomialChart σ R)
        (Carrier (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c))) Θ ∧
      CommutesWithD (polynomialChart σ R)
        (Carrier (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c))) Θ := by
  let Θs : ∀ (F : Finset σ) (p : ℕ), ⋀[Carrier (tableOfHom (chartClassify c (↥F)))]^p
      Ω[Carrier (tableOfHom (chartClassify c (↥F)))⁄ℤ] →ₗ[polynomialChart (↥F) R]
        ⋀[polynomialChart (↥F) R]^p Ω[polynomialChart (↥F) R⁄ℤ] :=
    fun F => (hfin (↥F)).choose
  have htr : ∀ F : Finset σ, IsFormsTrace _ _ (Θs F) := fun F => (hfin (↥F)).choose_spec
  have hcomp : IsCompatibleFamily (polynomialChart σ R)
      (Carrier (tableOfHom (chartClassify c σ))) Θs := by
    classical
    intro F F' p η η' hηη'
    let k := F ∪ F'
    have hF : F ⊆ k := Finset.subset_union_left
    have hF' : F' ⊆ k := Finset.subset_union_right
    let : Algebra (polynomialChart (↥F) R) (polynomialChart (↥k) R) :=
      (chartTransition hF).toAlgebra
    let : Algebra (Carrier (tableOfHom (chartClassify c (↥F))))
        (Carrier (tableOfHom (chartClassify c (↥k)))) :=
      (carrierHom (chartTransition hF) (chartTransition_classify hF)).toAlgebra
    let : Algebra (polynomialChart (↥F') R) (polynomialChart (↥k) R) :=
      (chartTransition hF').toAlgebra
    let : Algebra (Carrier (tableOfHom (chartClassify c (↥F'))))
        (Carrier (tableOfHom (chartClassify c (↥k)))) :=
      (carrierHom (chartTransition hF') (chartTransition_classify hF')).toAlgebra
    have := chart_isScalarTower_transition (R := R) hF rfl
    have := chart_isScalarTower_transition (R := R) hF' rfl
    have := chart_isScalarTower_carrier_transition (c := c) hF rfl
    have := chart_isScalarTower_carrier_transition (c := c) hF' rfl
    exact formsMap_eq_of_tower (Θs F) (Θs F') (Θs k) (chart_formsMap_injective k p)
      (chart_transition_comm hc hF (htr F) (htr k) p)
      (chart_transition_comm hc hF' (htr F') (htr k) p) η η' hηη'
  have hnice := discr_polynomialChart_nice (σ := σ) c hc
  have hΘ := isFormsTrace_colimitForms chart_isExhaustive Θs hcomp htr
  exact ⟨colimitForms chart_isExhaustive Θs hcomp, hΘ, hΘ.isWedgeLinear_of_isNiceElement hnice,
    hΘ.commutesWithD_of_isNiceElement_of_free hnice⟩

/-- **The trace maps on the universal chart, from the charts in finitely many variables.** For a
syntomic-good `g` and any set of variables `σ`: if every universal chart `N_g[x_τ] → B_τ` in
finitely many variables carries maps with property (1) of Stacks, Lemma 0FLB, then
`N_g[x_σ] → B_σ` carries maps with property (1), property (2) of Proposition 0FLC, commuting with
the de Rham differentials. -/
theorem exists_isFormsTrace_universalChart_of_finite (σ : Type u) {g : universalRing d}
    (hg : IsSyntomicGood.{u} d g)
    (hfin : ∀ (τ : Type u) [Finite τ], ∃ Θ : ∀ p : ℕ,
      ⋀[Carrier (tableOfHom (universalChartClassify τ g))]^p
        Ω[Carrier (tableOfHom (universalChartClassify τ g))⁄ℤ] →ₗ[universalChartRing τ g]
          ⋀[universalChartRing τ g]^p Ω[universalChartRing τ g⁄ℤ],
        IsFormsTrace (universalChartRing τ g) (Carrier (tableOfHom (universalChartClassify τ g)))
          Θ) :
    ∃ Θ : ∀ p : ℕ, ⋀[Carrier (tableOfHom (universalChartClassify σ g))]^p
        Ω[Carrier (tableOfHom (universalChartClassify σ g))⁄ℤ] →ₗ[universalChartRing σ g]
          ⋀[universalChartRing σ g]^p Ω[universalChartRing σ g⁄ℤ],
      IsFormsTrace (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g))) Θ ∧
      IsWedgeLinear (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g)))
        Θ ∧
      CommutesWithD (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g)))
        Θ := by
  have := smooth_universalChartBase g hg
  exact exists_isFormsTrace_polynomialChart_of_finite σ (universalChartBaseClassify.{u} g)
    (discr_universalChartBase_mem_nonZeroDivisors g hg) hfin

/-- **The trace maps on the comparison charts, from the charts in finitely many variables.** For
a syntomic-good `g`, any `g'` and any set of variables `σ`: if every chart `R''[x_τ] → B_τ` over
the comparison ring in finitely many variables carries maps with property (1) of Stacks,
Lemma 0FLB, then `R''[x_σ] → B_σ` carries maps with property (1), property (2) of
Proposition 0FLC, commuting with the de Rham differentials. -/
theorem exists_isFormsTrace_comparisonChart_of_finite (σ : Type u) {g : universalRing d}
    (g' : universalRing d) (hg : IsSyntomicGood.{u} d g)
    (hfin : ∀ (τ : Type u) [Finite τ], ∃ Θ : ∀ p : ℕ,
      ⋀[Carrier (tableOfHom (comparisonChartClassify g g' τ))]^p
        Ω[Carrier (tableOfHom (comparisonChartClassify g g' τ))⁄ℤ]
          →ₗ[comparisonChartRing g g' τ]
          ⋀[comparisonChartRing g g' τ]^p Ω[comparisonChartRing g g' τ⁄ℤ],
        IsFormsTrace (comparisonChartRing g g' τ)
          (Carrier (tableOfHom (comparisonChartClassify g g' τ))) Θ) :
    ∃ Θ : ∀ p : ℕ, ⋀[Carrier (tableOfHom (comparisonChartClassify g g' σ))]^p
        Ω[Carrier (tableOfHom (comparisonChartClassify g g' σ))⁄ℤ]
          →ₗ[comparisonChartRing g g' σ]
          ⋀[comparisonChartRing g g' σ]^p Ω[comparisonChartRing g g' σ⁄ℤ],
      IsFormsTrace (comparisonChartRing g g' σ)
        (Carrier (tableOfHom (comparisonChartClassify g g' σ))) Θ ∧
      IsWedgeLinear (comparisonChartRing g g' σ)
        (Carrier (tableOfHom (comparisonChartClassify g g' σ))) Θ ∧
      CommutesWithD (comparisonChartRing g g' σ)
        (Carrier (tableOfHom (comparisonChartClassify g g' σ))) Θ := by
  have := smooth_comparisonRing g' hg
  refine exists_isFormsTrace_polynomialChart_of_finite σ
    ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g)) ?_ hfin
  rw [discr_tableOfHom]
  exact comparisonPr_discr_mem_nonZeroDivisors g' hg

end Chart

end Stacks.FormsTrace

end
