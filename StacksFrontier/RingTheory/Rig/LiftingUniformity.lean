module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwoTermExtBound
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.Lifting

/-!
# Lifting a map into a quotient of a complete algebra over a general ideal (Stacks 0GAQ)

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` an object of the category of Stacks 0AL4 for
`(A, I)` such that `I ^ c` annihilates `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`, and `C`
a Noetherian `I`-adically complete `A`-algebra. Stacks 0GAQ says that for `n` large every
`A`-algebra map `ψₙ : B → C / IⁿC` agrees, modulo a power of `I`, with the reduction of an
`A`-algebra map `φ : B → C`; the bound on `n` and the precision of the agreement are governed by
the two invariants `d = d(Gr_I(C))` and `q₀ = q(Gr_I(C))` of Local Cohomology, Section 0GA6.

The proof is the one of Stacks 0AK6 with the division by `a ^ c` — which is where the principal
case uses that `a` is a nonzerodivisor — replaced by the uniformity bound of Local Cohomology.
Write `B = A⟨x₁, …, x_r⟩ / J` for a completed polynomial presentation and lift `ψₙ` to a
continuous `A`-algebra map `ψ : A⟨x₁, …, x_r⟩ → C`, so that `ψ(J) ⊆ IᵐC` for `m = n`. For each
`a ∈ I ^ c` Stacks 0GAP gives `γ₁, …, γ_r ∈ J` with `a · g ≡ ∑ i (∂g/∂xᵢ) γᵢ` modulo `J²`. Over
`R = C / IᵐC` this says exactly that multiplication by `a` on the finite `R`-module

`M = R ⊗_{A⟨x⟩} J`

factors through the finite free module `Rʳ` by way of the differential `D : M → Rʳ`,
`1 ⊗ g ↦ (ψ(∂g/∂xᵢ) mod IᵐC)ᵢ`; so `M` is an `(C, m, c)`-module in the sense of Section 0GA6.
The obstruction `1 ⊗ g ↦ ψ(g) mod I^{2m}C` is a homomorphism `φ : M → IᵐC/I^{2m}C`, and
Tag 0GAC writes its twist down to level `m - (1+D)c` as `∑ aᵢψᵢ` with `aᵢ ∈ I^cC`; twisting once
more and feeding each `aᵢ` through the factorization exhibits the twist of `φ` to level
`g = m - (2+D)c` as `Λ ∘ D` for a single `Λ : Rʳ → I^gC/I^{g+m}C`. Lifting the values
`Λ(eᵢ)` to `δᵢ ∈ I^gC` gives

`ψ(g) - ∑ i ψ(∂g/∂xᵢ) δᵢ ∈ I^{g+m}C`  for every `g ∈ J`,

which is the conclusion the principal case obtains by dividing by `a ^ c`. The perturbation
`xᵢ ↦ ψ(xᵢ) - δᵢ` then has `ψ'(J) ⊆ I^{2g}C` by the first-order expansion of Stacks 0AK3, and
`Rig.exists_limit_algHom` iterates and passes to the limit in the complete ring `C`.

## Main results

* `Rig.exists_algHom_lift_of_dualSituation`: **Stacks 0GAQ**.

Auxiliary, and reusable:

* `Rig.partialDerivative_mul`: the Leibniz rule for formal partial differentiation of restricted
  power series.
* `Rig.exists_divided_obstruction_core`: the replacement for the division by `a ^ c`, as a
  statement about an abstract ideal `J` of an abstract Noetherian ring carrying a family of
  derivations and the obstruction relation of Stacks 0GAP.
* `Rig.exists_perturbed_continuousAlgHom_of_divided`: one step of the iteration, from a divided
  obstruction.

## Implementation notes

The invariants `d` and `q₀` of Stacks 0GA6 are carried, as everywhere in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/`, by the structure
`DualSituation`, which also fixes the thickness `n` of the subquotients it talks about. Since the
iteration applies Tag 0GAC at every level `m ≥ n`, the hypothesis here is a *family*
`S : ∀ m, c ≤ m → DualSituation C (I C) m c` together with the requirement that the two
invariants do not depend on `m`; that is what "`d = d(Gr_I(C))` and `q₀ = q(Gr_I(C))`" amounts
to in this formalization. The open duality input of Tag 0GAC (and so of Tag 0GAD) is carried as
the hypothesis `hdual`, for every level `m ≥ n`; what in it is proved and what is not is
recorded in the docstring of
`Stacks.LocalCohomology.UniformityIII.DualSituation.exists_sum_powQuotSmul`.

The family is indexed by the thicknesses `m ≥ c`, not by all of `ℕ`. This is not a restriction
on the supplier but the removal of a defect: a `DualSituation C (I C) m c` carries
`ModuleSituation.exponent_le : c ≤ m` as a field, so a family indexed by every `m : ℕ` is an
*empty* type as soon as `c ≥ 1` — its value at `m = 0` would prove `c ≤ 0` — and a statement
whose conclusion is an implication out of such a family asserts nothing. The proof below uses
`S` only at the thickness `max mm n`, and `n > 2(k+3)c ≥ c`, so nothing is lost and the
statement is strengthened.

The levels are carried as parameters wherever a subtraction would otherwise appear in a type,
exactly as in Tags 0GAC and 0GAD: `k + 1 = D = max(d, 1)`, `g + c = f`, `f + kc = e` and
`e + 2c = m`, so that `f = m - (1+D)c`, `g = m - (2+D)c` and `e = m - 2c`.

`Rig.exists_divided_obstruction_core` is stated for an abstract Noetherian ring `Rs` with an
ideal `J` and a family of derivations rather than for restricted power series, because nothing
about restricted power series enters it: the only inputs are the Leibniz rule, the obstruction
relation of Stacks 0GAP, and `Rig.exists_limit_algHom`'s hypothesis `ψ(J) ⊆ IᵐC`.

## References

* [Stacks Project, Tag 0GAQ](https://stacks.math.columbia.edu/tag/0GAQ)
* [Stacks Project, Tag 0GAP](https://stacks.math.columbia.edu/tag/0GAP)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
* [Stacks Project, Tag 0GAD](https://stacks.math.columbia.edu/tag/0GAD)
* [Stacks Project, Tag 0AK6](https://stacks.math.columbia.edu/tag/0AK6)
-/

@[expose] public noncomputable section

open CategoryTheory RestrictedPowerSeries Stacks.LocalCohomology.UniformityIII
open scoped TensorProduct

namespace Rig

universe u v w

section Leibniz

/-- The Leibniz rule for the formal partial derivatives of restricted power series: both sides
are computed coefficient quotient by coefficient quotient, where the rule is
`MvPolynomial.pderiv_mul`. -/
public theorem partialDerivative_mul {A : Type u} [CommRing A] (I : Ideal A) {σ : Type v}
    (i : σ) (x y : RestrictedPowerSeries I σ) :
    partialDerivative I i (x * y)
      = x * partialDerivative I i y + y * partialDerivative I i x := by
  refine Subtype.ext (funext fun n => ?_)
  change MvPolynomial.pderiv i (x.1 n * y.1 n)
    = x.1 n * MvPolynomial.pderiv i (y.1 n) + y.1 n * MvPolynomial.pderiv i (x.1 n)
  rw [MvPolynomial.pderiv_mul]
  ring

end Leibniz

section DividedObstruction

/-- **Extension along a split differential at a given level.** For every `(C, m, c)`-module `M`
and every `D : M → (C/IᵐC)ʳ` through which multiplication by every element of `I^c` factors, the
twist down to level `g` of every homomorphism `M → IᵐC/I^{2m}C` extends along `D`. This is what
Tag 0GAD provides for the two-term complex `[M → (C/IᵐC)ʳ]`, and the only input of the division
by `a ^ c` in `exists_divided_obstruction_of_extension`. -/
public def ExtendsAtLevel {C : Type u} [CommRing C] (JC : Ideal C) (m g c r : ℕ) (hgm : g ≤ m) :
    Prop :=
  ∀ (M : ANCModule JC m c) (D : M.1 →ₗ[C ⧸ JC ^ m] (Fin r → C ⧸ JC ^ m)),
    (∀ a ∈ Ideal.map (Ideal.Quotient.mk (JC ^ m)) (JC ^ c),
      ∃ h : (Fin r → C ⧸ JC ^ m) →ₗ[C ⧸ JC ^ m] M.1, ∀ z, h (D z) = a • z) →
    ∀ φ : resModule JC m M.1 →ₗ[C] powQuot JC m m,
      ∃ Λ : (Fin r → C ⧸ JC ^ m) →ₗ[C] powQuot JC g m,
        ∀ z, Λ (D z) = powQuotLe JC hgm (φ z)

/-- **The extension property from Tag 0GAC**, at the level `g = m - (2+D)c` that the library's
Tag 0GAC reaches. -/
public theorem extendsAtLevel_of_dualSituation {C : Type u} [CommRing C] [IsNoetherianRing C]
    {JC : Ideal C} {r c m g f e k : ℕ} (S : DualSituation C JC m c)
    (hgf : g + c = f) (hk : max S.d 1 = k + 1) (he : f + k * c = e) (hem : e + 2 * c = m)
    (hq : S.q₀ ≤ f)
    (hdual : ∀ (M : ANCModule JC m c)
        (φ : resModule JC m M.1 →ₗ[C] powQuot JC m m),
      ∃ σ' : S.H M.dual 0 (e : ℤ),
        S.ev M e (hq.trans (Nat.le.intro he)) σ'
          = (powQuotLe JC (Nat.le.intro hem)).comp φ) :
    ExtendsAtLevel JC m g c r
      ((Nat.le.intro hgf).trans ((Nat.le.intro he).trans (Nat.le.intro hem))) := by
  intro MANC D hret φ
  obtain ⟨σ', hσ⟩ := hdual MANC φ
  obtain ⟨N, a, ha, ψs, hsum⟩ := S.exists_sum_powQuotSmul MANC φ hgf hk he hem hq σ' hσ
  choose hmaps hmapseq using fun i : Fin N =>
    hret (Ideal.Quotient.mk (JC ^ m) (a i)) (Ideal.mem_map_of_mem _ (ha i))
  have hgm : g ≤ m := (Nat.le.intro hgf).trans ((Nat.le.intro he).trans (Nat.le.intro hem))
  refine ⟨
    { toFun := fun v => ∑ j : Fin N, ψs j (hmaps j v)
      map_add' := fun v w => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ =>
          (congrArg (ψs j) (map_add (hmaps j) v w)).trans (map_add (ψs j) _ _)
      map_smul' := fun t v => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hv : t • v = (Ideal.Quotient.mk (JC ^ m) t) • v := by
          rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
        rw [hv]
        exact (congrArg (ψs j) ((hmaps j).map_smul (Ideal.Quotient.mk (JC ^ m) t) v)).trans
          ((ψs j).map_smul t (hmaps j v)) }, fun z₀ => ?_⟩
  let z : resModule JC m MANC.1 := z₀
  have h0 := LinearMap.congr_fun hsum z
  have hsumapp : (∑ j : Fin N, (powQuotSmul JC (ha j) hgf).comp (ψs j)) z
      = ∑ j : Fin N, powQuotSmul JC (ha j) hgf ((ψs j) z) :=
    LinearMap.sum_apply Finset.univ _ z
  have h1 : powQuotLe JC ((Nat.le.intro he).trans (Nat.le.intro hem)) (φ z)
      = ∑ j : Fin N, powQuotSmul JC (ha j) hgf ((ψs j) z) := h0.trans hsumapp
  have h2 : powQuotLe JC hgm (φ z) = ∑ j : Fin N, a j • (ψs j) z := by
    rw [← powQuotLe_powQuotLe JC m ((Nat.le.intro he).trans (Nat.le.intro hem))
      (Nat.le.intro hgf), h1, map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      powQuotLe_powQuotSmul JC m (ha j) hgf ((ψs j) z)
  change ∑ j : Fin N, ψs j (hmaps j (D z₀)) = _
  rw [h2]
  exact Finset.sum_congr rfl fun j _ =>
    (congrArg (ψs j) (hmapseq j z₀)).trans ((ψs j).map_smul (a j) z)


/-- **The division by `a ^ c`, from an extension property.** The construction of
`exists_divided_obstruction_core`, with the extension of the twisted obstruction along the
differential taken from an arbitrary `ExtendsAtLevel` at level `g`. -/
public theorem exists_divided_obstruction_of_extension
    {A : Type u} [CommRing A] {I : Ideal A} {r : ℕ}
    {Rs : Type u} [CommRing Rs] [IsNoetherianRing Rs] [Algebra A Rs]
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra A C]
    (Jid : Ideal Rs) (der : Fin r → (Rs →+ Rs))
    (hleib : ∀ (i : Fin r) (x y : Rs), der i (x * y) = x * der i y + y * der i x)
    (c : ℕ)
    (hcramer : ∀ a ∈ I ^ c, ∃ γ : Fin r → Rs, (∀ i, γ i ∈ Jid) ∧
      ∀ x ∈ Jid, algebraMap A Rs a * x - ∑ i, der i x * γ i ∈ Jid ^ 2)
    (JC : Ideal C) (hJC : JC = I.map (algebraMap A C))
    {m g : ℕ} (hgm : g ≤ m) (hext : ExtendsAtLevel JC m g c r hgm)
    (ψ : Rs →ₐ[A] C) (hψJ : ∀ x ∈ Jid, ψ x ∈ JC ^ m) :
    ∃ δ : Fin r → C, (∀ i, δ i ∈ JC ^ g) ∧
      ∀ x ∈ Jid, ψ x - ∑ i, ψ (der i x) * δ i ∈ JC ^ (g + m) := by
  classical
  -- `C / IᵐC` is an `Rs`-algebra through `ψ`.
  let _ : Algebra Rs (C ⧸ JC ^ m) :=
    RingHom.toAlgebra ((Ideal.Quotient.mk (JC ^ m)).comp ψ.toRingHom)
  have halg : ∀ x : Rs,
      algebraMap Rs (C ⧸ JC ^ m) x = Ideal.Quotient.mk (JC ^ m) (ψ x) := fun _ => rfl
  have hzero : ∀ x ∈ Jid, algebraMap Rs (C ⧸ JC ^ m) x = 0 := by
    intro x hx
    rw [halg]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hψJ x hx)
  -- The subquotients of `C` are `Rs`-modules through the same map.
  let _ : Module Rs (powQuot JC m m) :=
    Module.compHom (powQuot JC m m) (algebraMap Rs (C ⧸ JC ^ m))
  have hsmulQ : ∀ (x : Rs) (z : powQuot JC m m), x • z = ψ x • z := by
    intro x z
    change (algebraMap Rs (C ⧸ JC ^ m) x) • z = ψ x • z
    rw [halg]
    exact powQuot_mk_smul JC m m (ψ x) z
  let _ : IsScalarTower Rs (C ⧸ JC ^ m) (powQuot JC m m) :=
    ⟨fun x y z => by
      rw [Algebra.smul_def]
      exact mul_smul (algebraMap Rs (C ⧸ JC ^ m) x) y z⟩
  -- `J` is a finite `Rs`-module, so `M = (C/IᵐC) ⊗_{Rs} J` is a finite `C/IᵐC`-module.
  have hJfin : Module.Finite Rs (Jid : Submodule Rs Rs) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian Jid)
  -- the canonical map `J → M`
  let ι : (Jid : Submodule Rs Rs) →ₗ[Rs]
      (C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs) :=
    TensorProduct.mk Rs (C ⧸ JC ^ m) (Jid : Submodule Rs Rs) 1
  have hιsmul : ∀ (x : Rs) (z : (Jid : Submodule Rs Rs)), ι (x • z) = x • ι z :=
    fun x z => ι.map_smul x z
  have hJsq : ∀ y : Rs, y ∈ Jid ^ 2 → ∀ hy : y ∈ Jid, ι ⟨y, hy⟩ = 0 := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on'
      (C := fun z _ => ∀ hz : z ∈ Jid, ι ⟨z, hz⟩ = 0) ?_ ?_ hy
    · intro p hp q hq hpq
      have h1 : (⟨p * q, hpq⟩ : (Jid : Submodule Rs Rs)) = p • ⟨q, hq⟩ := Subtype.ext rfl
      rw [h1, hιsmul]
      change p • ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨q, hq⟩ : (Jid : Submodule Rs Rs))) = 0
      rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, hzero p hp,
        TensorProduct.zero_tmul]
    · intro p hp q hq ihp ihq hpq
      have h1 : (⟨p + q, hpq⟩ : (Jid : Submodule Rs Rs))
          = ⟨p, Ideal.mul_le_left hp⟩ + ⟨q, Ideal.mul_le_left hq⟩ := Subtype.ext rfl
      rw [h1, map_add, ihp _, ihq _, add_zero]
  -- the obstruction homomorphism `M → IᵐC / I^{2m}C`
  let jhom : (Jid : Submodule Rs Rs) →+ (JC ^ m : Ideal C) :=
    AddMonoidHom.mk' (fun x => ⟨ψ (x : Rs), hψJ (x : Rs) x.2⟩)
      (fun x y => Subtype.ext (map_add ψ (x : Rs) (y : Rs)))
  let ω : (Jid : Submodule Rs Rs) →ₗ[Rs] powQuot JC m m :=
    { toFun := fun x => (powSub JC m m).mkQ (jhom x)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun a x => by
        have h1 : jhom (a • x) = ψ a • jhom x :=
          Subtype.ext (by
            change ψ (a * (x : Rs)) = ψ a * ψ (x : Rs)
            rw [map_mul])
        change (powSub JC m m).mkQ (jhom (a • x))
          = (RingHom.id Rs) a • (powSub JC m m).mkQ (jhom x)
        rw [h1, map_smul, RingHom.id_apply, hsmulQ] }
  have hω : ∀ (x : Rs) (hx : x ∈ Jid),
      ω ⟨x, hx⟩ = (powSub JC m m).mkQ ⟨ψ x, hψJ x hx⟩ := fun _ _ => rfl
  let φR : (C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs) →ₗ[C ⧸ JC ^ m] powQuot JC m m :=
    ω.liftBaseChange (C ⧸ JC ^ m)
  -- the differential `M → (C/IᵐC)ʳ`
  let derHom : (Jid : Submodule Rs Rs) →ₗ[Rs] (Fin r → C ⧸ JC ^ m) :=
    { toFun := fun x i => Ideal.Quotient.mk (JC ^ m) (ψ (der i (x : Rs)))
      map_add' := fun x y => by
        refine funext fun i => ?_
        change Ideal.Quotient.mk (JC ^ m) (ψ (der i ((x : Rs) + (y : Rs))))
          = Ideal.Quotient.mk (JC ^ m) (ψ (der i (x : Rs)))
            + Ideal.Quotient.mk (JC ^ m) (ψ (der i (y : Rs)))
        rw [map_add, map_add, map_add]
      map_smul' := fun a x => by
        refine funext fun i => ?_
        change Ideal.Quotient.mk (JC ^ m) (ψ (der i (a * (x : Rs))))
          = (RingHom.id Rs) a • (fun j => Ideal.Quotient.mk (JC ^ m) (ψ (der j (x : Rs)))) i
        rw [hleib, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
          (Ideal.Quotient.eq_zero_iff_mem).mpr (hψJ (x : Rs) x.2), zero_mul, add_zero,
          RingHom.id_apply]
        change _ = (algebraMap Rs (C ⧸ JC ^ m) a) * _
        rw [halg] }
  let D : (C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs) →ₗ[C ⧸ JC ^ m]
      (Fin r → C ⧸ JC ^ m) := derHom.liftBaseChange (C ⧸ JC ^ m)
  -- The obstruction relation makes multiplication by `I^cC` factor through `D`.
  have hretA : ∀ a ∈ (I ^ c : Ideal A), ∃ h : (Fin r → C ⧸ JC ^ m) →ₗ[C ⧸ JC ^ m]
      ((C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs)),
      ∀ z, h (D z) = (algebraMap A (C ⧸ JC ^ m) a) • z := by
    intro a ha
    obtain ⟨γ, hγmem, hγrel⟩ := hcramer a ha
    let hmap : (Fin r → C ⧸ JC ^ m) →ₗ[C ⧸ JC ^ m]
        ((C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs)) :=
      ∑ i : Fin r, (LinearMap.proj i).smulRight (ι ⟨γ i, hγmem i⟩)
    have hmapapp : ∀ v : Fin r → C ⧸ JC ^ m,
        hmap v = ∑ i : Fin r, v i • ι ⟨γ i, hγmem i⟩ :=
      fun v => LinearMap.sum_apply Finset.univ _ v
    refine ⟨hmap, ?_⟩
    have hbase : ∀ (x : Rs) (hx : x ∈ Jid),
        hmap (D ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs))))
          = (algebraMap A (C ⧸ JC ^ m) a) •
            ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs))) := by
      intro x hx
      have hDval : D ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs)))
          = fun i => algebraMap Rs (C ⧸ JC ^ m) (der i x) := by
        refine funext fun i => ?_
        change (derHom.liftBaseChange (C ⧸ JC ^ m))
            ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs))) i = _
        rw [LinearMap.liftBaseChange_one_tmul, halg]
        rfl
      rw [hDval, hmapapp]
      have hLHS : (∑ i : Fin r,
            (algebraMap Rs (C ⧸ JC ^ m) (der i x)) • ι ⟨γ i, hγmem i⟩)
          = ι ⟨∑ i, der i x * γ i, Ideal.sum_mem _ fun i _ =>
              Ideal.mul_mem_left _ _ (hγmem i)⟩ := by
        have hterm : ∀ i : Fin r,
            (algebraMap Rs (C ⧸ JC ^ m) (der i x)) • ι ⟨γ i, hγmem i⟩
              = ι ⟨der i x * γ i, Ideal.mul_mem_left _ _ (hγmem i)⟩ := by
          intro i
          rw [algebraMap_smul, ← hιsmul]
          exact congrArg ι (Subtype.ext rfl)
        rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum]
        exact congrArg ι (Subtype.ext (by simp))
      rw [hLHS]
      have hrel := hγrel x hx
      have hsub : ι ⟨algebraMap A Rs a * x - ∑ i, der i x * γ i,
          Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx)
            (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hγmem i))⟩ = 0 :=
        hJsq _ hrel _
      have hsplit : (⟨algebraMap A Rs a * x - ∑ i, der i x * γ i,
            Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx)
              (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hγmem i))⟩
            : (Jid : Submodule Rs Rs))
          = ⟨algebraMap A Rs a * x, Ideal.mul_mem_left _ _ hx⟩
            - ⟨∑ i, der i x * γ i,
              Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hγmem i)⟩ :=
        Subtype.ext rfl
      rw [hsplit, map_sub, sub_eq_zero] at hsub
      rw [← hsub]
      have hmul : (⟨algebraMap A Rs a * x, Ideal.mul_mem_left _ _ hx⟩
            : (Jid : Submodule Rs Rs))
          = (algebraMap A Rs a) • ⟨x, hx⟩ := Subtype.ext rfl
      rw [hmul, hιsmul]
      change _ = (algebraMap A (C ⧸ JC ^ m) a) • ι ⟨x, hx⟩
      rw [← algebraMap_smul (C ⧸ JC ^ m) (algebraMap A Rs a) (ι ⟨x, hx⟩), halg,
        AlgHom.commutes, IsScalarTower.algebraMap_apply A C (C ⧸ JC ^ m) a,
        Ideal.Quotient.algebraMap_eq]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul y x =>
      have hy : y ⊗ₜ[Rs] x = y • ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hy, map_smul, map_smul, hbase (x : Rs) x.2, smul_comm]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, smul_add]
  -- the same for an arbitrary element of `I^cC`
  have hret : ∀ a ∈ (JC ^ c : Ideal C), ∃ h : (Fin r → C ⧸ JC ^ m) →ₗ[C ⧸ JC ^ m]
      ((C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs)),
      ∀ z, h (D z) = (Ideal.Quotient.mk (JC ^ m) a) • z := by
    intro a ha
    have ha' : a ∈ Submodule.span C ((algebraMap A C) '' ((I ^ c : Ideal A) : Set A)) := by
      rw [hJC, ← Ideal.map_pow] at ha
      exact ha
    clear ha
    induction ha' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      obtain ⟨h, hh⟩ := hretA b hb
      refine ⟨h, fun z => ?_⟩
      have hb' : (algebraMap A (C ⧸ JC ^ m)) b
          = Ideal.Quotient.mk (JC ^ m) ((algebraMap A C) b) := by
        rw [IsScalarTower.algebraMap_apply A C (C ⧸ JC ^ m) b, Ideal.Quotient.algebraMap_eq]
      rw [hh z, hb']
    | zero => exact ⟨0, fun z => by rw [map_zero, LinearMap.zero_apply, zero_smul]⟩
    | add y₁ y₂ _ _ ih₁ ih₂ =>
      obtain ⟨h₁, hh₁⟩ := ih₁
      obtain ⟨h₂, hh₂⟩ := ih₂
      exact ⟨h₁ + h₂, fun z => by
        rw [LinearMap.add_apply, hh₁ z, hh₂ z, map_add, add_smul]⟩
    | smul y₁ y₂ _ ih =>
      obtain ⟨h, hh⟩ := ih
      refine ⟨(Ideal.Quotient.mk (JC ^ m) y₁) • h, fun z => ?_⟩
      rw [LinearMap.smul_apply, hh z, smul_smul, ← map_mul, smul_eq_mul]
  -- `M` is a `(C, m, c)`-module
  have hANC : IsANCModule JC m c (ModuleCat.of (C ⧸ JC ^ m)
      ((C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs))) := by
    refine ⟨inferInstance, fun ā hā => ?_⟩
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hā
    obtain ⟨h, hh⟩ := hret a ha
    exact FactorsThroughProj.mk' D h (LinearMap.ext fun z => (hh z).symm)
  let MANC : ANCModule JC m c :=
    ⟨ModuleCat.of (C ⧸ JC ^ m) ((C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs)), hANC⟩
  let φ : resModule JC m MANC.1 →ₗ[C] powQuot JC m m :=
    toResHom JC m m (ModuleCat.ofHom φR)
  -- the extension of the twisted obstruction along `D`
  have hret' : ∀ ā ∈ Ideal.map (Ideal.Quotient.mk (JC ^ m)) (JC ^ c),
      ∃ h : (Fin r → C ⧸ JC ^ m) →ₗ[C ⧸ JC ^ m] MANC.1, ∀ z, h (D z) = ā • z := by
    intro ā hā
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hā
    exact hret a ha
  obtain ⟨Λ, hΛ⟩ := hext MANC D hret' φ
  let LamHom : (Fin r → C ⧸ JC ^ m) →+ powQuot JC g m := Λ.toAddMonoidHom
  have hLamSmul : ∀ (t : C) (v : Fin r → C ⧸ JC ^ m),
      LamHom ((Ideal.Quotient.mk (JC ^ m) t) • v) = t • LamHom v := by
    intro t v
    have hv : (Ideal.Quotient.mk (JC ^ m) t) • v = t • v := by
      rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    change Λ ((Ideal.Quotient.mk (JC ^ m) t) • v) = t • Λ v
    rw [hv, map_smul]
  have hLamD : ∀ z : (C ⧸ JC ^ m) ⊗[Rs] (Jid : Submodule Rs Rs),
      LamHom (D z) = powQuotLe JC hgm (φ z) := hΛ
  -- read off the `δᵢ`
  choose y hy using fun i : Fin r =>
    (powSub JC g m).mkQ_surjective (LamHom (Pi.single i 1))
  refine ⟨fun i => (y i : C), fun i => (y i).2, ?_⟩
  intro x hx
  have hDsingle : D ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs)))
      = ∑ i : Fin r, (Ideal.Quotient.mk (JC ^ m) (ψ (der i x))) •
        (Pi.single i 1 : Fin r → C ⧸ JC ^ m) := by
    refine funext fun j => ?_
    have hval : D ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs))) j
        = Ideal.Quotient.mk (JC ^ m) (ψ (der j x)) := by
      change (derHom.liftBaseChange (C ⧸ JC ^ m))
          ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs))) j = _
      rw [LinearMap.liftBaseChange_one_tmul]
      rfl
    rw [hval, Finset.sum_apply]
    simp [Pi.single_apply]
  have hkey := hLamD ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs)))
  rw [hDsingle, map_sum] at hkey
  have hleft : ∑ i : Fin r,
        LamHom ((Ideal.Quotient.mk (JC ^ m) (ψ (der i x))) •
          (Pi.single i 1 : Fin r → C ⧸ JC ^ m))
      = (powSub JC g m).mkQ (∑ i : Fin r, (ψ (der i x)) • y i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hLamSmul, ← hy i, map_smul]
  have hright : powQuotLe JC hgm
        (φ ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs))))
      = (powSub JC g m).mkQ ⟨ψ x, Ideal.pow_le_pow_right hgm (hψJ x hx)⟩ := by
    have hφval : φ ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs)))
        = (powSub JC m m).mkQ ⟨ψ x, hψJ x hx⟩ := by
      change φR ((1 : C ⧸ JC ^ m) ⊗ₜ[Rs] (⟨x, hx⟩ : (Jid : Submodule Rs Rs))) = _
      rw [LinearMap.liftBaseChange_one_tmul]
      exact hω x hx
    rw [hφval]
    rfl
  rw [hleft, hright] at hkey
  have hdiff := (Submodule.Quotient.eq (powSub JC g m)).mp hkey.symm
  have hval : ((⟨ψ x, Ideal.pow_le_pow_right hgm (hψJ x hx)⟩ : (JC ^ g : Ideal C))
        - ∑ i : Fin r, (ψ (der i x)) • y i)
      = ⟨ψ x - ∑ i : Fin r, ψ (der i x) * ((y i : C)),
        Ideal.sub_mem _ (Ideal.pow_le_pow_right hgm (hψJ x hx))
          (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (y i).2)⟩ := by
    refine Subtype.ext ?_
    push_cast
    simp [smul_eq_mul]
  rw [hval] at hdiff
  simpa [powSub] using hdiff

/-- **The replacement for the division by `a ^ c`.**

Let `J` be an ideal of a Noetherian ring `Rs`, equipped with a family of derivations
`∂₁, …, ∂_r` and with the obstruction relation of Stacks 0GAP: for every `a ∈ I ^ c` there are
`γ₁, …, γ_r ∈ J` with `a · x ≡ ∑ i (∂ᵢ x) γᵢ` modulo `J²` for all `x ∈ J`. Let `ψ : Rs → C` be
an `A`-algebra map into a Noetherian `A`-algebra with `ψ(J) ⊆ IᵐC`. Then, in the numbering of
Tags 0GAC and 0GAD, there are `δ₁, …, δ_r ∈ I^gC` with

`ψ(x) - ∑ i ψ(∂ᵢ x) δᵢ ∈ I^{g+m}C`  for every `x ∈ J`.

In the principal case of Stacks 0AK6 the `δᵢ` are the quotients `ψ(γᵢ) / a ^ c`, which exist
because `a` is a nonzerodivisor on `C`. Here they come from Tag 0GAC applied to the
`(C, m, c)`-module `M = (C/IᵐC) ⊗_{Rs} J`: the obstruction relation makes multiplication by an
element of `I^cC` on `M` factor through the finite free module `(C/IᵐC)ʳ` by way of the
differential `1 ⊗ x ↦ (ψ(∂ᵢ x))ᵢ`, so `M` is an `(C, m, c)`-module, and the twist of the
obstruction homomorphism `1 ⊗ x ↦ ψ(x)` down to level `g` factors through that differential. -/
public theorem exists_divided_obstruction_core
    {A : Type u} [CommRing A] {I : Ideal A} {r : ℕ}
    {Rs : Type u} [CommRing Rs] [IsNoetherianRing Rs] [Algebra A Rs]
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra A C]
    (Jid : Ideal Rs) (der : Fin r → (Rs →+ Rs))
    (hleib : ∀ (i : Fin r) (x y : Rs), der i (x * y) = x * der i y + y * der i x)
    (c : ℕ)
    (hcramer : ∀ a ∈ I ^ c, ∃ γ : Fin r → Rs, (∀ i, γ i ∈ Jid) ∧
      ∀ x ∈ Jid, algebraMap A Rs a * x - ∑ i, der i x * γ i ∈ Jid ^ 2)
    (JC : Ideal C) (hJC : JC = I.map (algebraMap A C))
    {m g f e k : ℕ} (S : DualSituation C JC m c)
    (hgf : g + c = f) (hk : max S.d 1 = k + 1) (he : f + k * c = e) (hem : e + 2 * c = m)
    (hq : S.q₀ ≤ f)
    (hdual : ∀ (M : ANCModule JC m c)
        (φ : resModule JC m M.1 →ₗ[C] powQuot JC m m),
      ∃ σ' : S.H M.dual 0 (e : ℤ),
        S.ev M e (hq.trans (Nat.le.intro he)) σ'
          = (powQuotLe JC (Nat.le.intro hem)).comp φ)
    (ψ : Rs →ₐ[A] C) (hψJ : ∀ x ∈ Jid, ψ x ∈ JC ^ m) :
    ∃ δ : Fin r → C, (∀ i, δ i ∈ JC ^ g) ∧
      ∀ x ∈ Jid, ψ x - ∑ i, ψ (der i x) * δ i ∈ JC ^ (g + m) :=
  exists_divided_obstruction_of_extension Jid der hleib c hcramer JC hJC _
    (extendsAtLevel_of_dualSituation S hgf hk he hem hq hdual) ψ hψJ

end DividedObstruction

section Perturbation

/-- One step of the iteration, from a divided obstruction.

If the obstruction of a continuous `A`-algebra map `ψ : A⟨x₁, …, x_r⟩ → C` with `ψ(J) ⊆ IᵐC` is
divided at level `g ≤ m`, in the sense that there are `δᵢ ∈ I^gC` with
`ψ(x) - ∑ i ψ(∂x/∂xᵢ) δᵢ ∈ I^{g+m}C` for every `x ∈ J`, then the perturbation
`xᵢ ↦ ψ(xᵢ) - δᵢ` is a continuous `A`-algebra map `ψ'` with `ψ'(J) ⊆ I^{2g}C` which agrees with
`ψ` modulo `I^gC`. The two conclusions are the first-order expansion of Stacks 0AK3 applied to
the perturbation. -/
public theorem exists_perturbed_continuousAlgHom_of_divided
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    {r : ℕ} (Jid : Ideal (RestrictedPowerSeries I (Fin r))) (g m : ℕ) (hgm : g ≤ m)
    (ψ : RestrictedPowerSeries I (Fin r) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (δ : Fin r → C) (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ g)
    (hdiv : ∀ x ∈ Jid, ψ x - ∑ i, ψ (partialDerivative I i x) * δ i
      ∈ (I.map (algebraMap A C)) ^ (g + m)) :
    ∃ ψ' : RestrictedPowerSeries I (Fin r) →ₐ[A] C,
      (@Continuous _ _ (limitTopology I (Fin r))
        ((I.map (algebraMap A C)).adicTopology) ψ') ∧
      (∀ x ∈ Jid, ψ' x ∈ (I.map (algebraMap A C)) ^ (2 * g)) ∧
      (∀ x, ψ' x - ψ x ∈ (I.map (algebraMap A C)) ^ g) := by
  classical
  set JC : Ideal C := I.map (algebraMap A C) with hJC
  obtain ⟨ψ', ⟨hψ'c, hψ'var⟩, -⟩ :=
    exists_continuousAlgHom_add_variables I hI ψ hψc (fun i => -δ i)
  have hexp : ∀ x, ψ' x - (ψ x - ∑ i, ψ (partialDerivative I i x) * δ i)
      ∈ JC ^ (2 * g) := by
    intro x
    obtain ⟨ξ, hξmem, hξ⟩ := eval_add_variables_eq_linear_add_error I hI ψ ψ' hψc hψ'c
      (fun i => -δ i) hψ'var x
    have hξJ : ξ ∈ JC ^ (2 * g) := by
      refine (Ideal.span_le.mpr ?_) hξmem
      rintro z ⟨ij, rfl⟩
      simp only [SetLike.mem_coe, neg_mul_neg]
      rw [two_mul, pow_add]
      exact Ideal.mul_mem_mul (hδ ij.1) (hδ ij.2)
    rw [show ψ' x - (ψ x - ∑ i, ψ (partialDerivative I i x) * δ i) = ξ by
      rw [hξ]
      simp only [mul_neg, Finset.sum_neg_distrib]
      ring]
    exact hξJ
  refine ⟨ψ', hψ'c, ?_, ?_⟩
  · intro x hx
    have h1 := Ideal.add_mem (JC ^ (2 * g)) (hexp x)
      (Ideal.pow_le_pow_right (by omega : 2 * g ≤ g + m) (hdiv x hx))
    simpa using h1
  · intro x
    have h1 : (∑ i, ψ (partialDerivative I i x) * δ i) ∈ JC ^ g :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hδ i)
    have h2 := Ideal.sub_mem (JC ^ g)
      (Ideal.pow_le_pow_right (by omega : g ≤ 2 * g) (hexp x)) h1
    rw [show ψ' x - ψ x
        = (ψ' x - (ψ x - ∑ i, ψ (partialDerivative I i x) * δ i))
          - (∑ i, ψ (partialDerivative I i x) * δ i) by ring]
    exact h2

end Perturbation

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

attribute [local instance] HasDerivedCategory.standard

/-- **The iteration of Stacks 0GAQ, from an extension property.** If at every level `m ≥ n` the
twisted obstruction extends along the differential at level `m - o` (`ExtendsAtLevel`), and
`2o < n`, then every `A`-algebra map `ψₙ : B → C / IⁿC` agrees modulo `I^{n-o}` with the
reduction of an `A`-algebra map `φ : B → C`. This is the proof of Stacks 0GAQ with the
obstruction-killing step, Tag 0GAD, abstracted to the offset `o` it costs. -/
public theorem exists_algHom_lift_of_extension
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (c : ℕ)
    (hExt : ∀ a ∈ I ^ c, ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) • ξ = 0)
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (o n : ℕ) (hn : 2 * o < n)
    (hext : ∀ m : ℕ, n ≤ m →
      ExtendsAtLevel (I.map (algebraMap A C)) m (m - o) c P.variableCount (Nat.sub_le m o))
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B.carrier →ₐ[A] C,
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (Nat.sub_le n o))).comp ψn =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - o))).comp φ := by
  classical
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hNoethRs : IsNoetherianRing (RestrictedPowerSeries I (Fin P.variableCount)) :=
    isNoetherianRing_restrictedPowerSeries I (Fin P.variableCount)
  -- the obstruction relation of Stacks 0GAP, for every element of `I ^ c`
  have hcramer : ∀ a ∈ I ^ c,
      ∃ γ : Fin P.variableCount → RestrictedPowerSeries I (Fin P.variableCount),
      (∀ i, γ i ∈ P.restrictedKer) ∧
      ∀ x ∈ P.restrictedKer,
        algebraMap A (RestrictedPowerSeries I (Fin P.variableCount)) a * x
          - ∑ i, (partialDerivative I i) x * γ i ∈ P.restrictedKer ^ 2 := by
    intro a ha
    obtain ⟨γ, hγmem, hγrel⟩ := exists_restricted_cramer_relation a B P 1 (by
      intro N ξ
      rw [pow_one]
      exact hExt a ha N ξ)
    exact ⟨γ, hγmem, fun x hx => by simpa using hγrel x hx⟩
  -- lift `ψₙ` and iterate
  obtain ⟨ψ, hψc, hψred⟩ := exists_continuousAlgHom_lift_quotient hIfg P n ψn
  have hψJ : ∀ x ∈ P.restrictedKer, ψ x ∈ (I.map (algebraMap A C)) ^ n := by
    intro x hx
    rw [← Ideal.Quotient.eq_zero_iff_mem, hψred x,
      show P.restrictedToAlgHom x = 0 from hx, map_zero]
  -- the property the precision-raising step preserves
  let Good : (RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C) → Prop := fun F =>
    (@Continuous _ _ (limitTopology I (Fin P.variableCount))
        ((I.map (algebraMap A C)).adicTopology) F) ∧
      ∀ x ∈ P.restrictedKer, F x ∈ (I.map (algebraMap A C)) ^ n
  have hstep : ∀ (mm : ℕ) (F : RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C),
      2 * o < mm → Good F →
      (∀ x ∈ P.restrictedKer, F x ∈ (I.map (algebraMap A C)) ^ mm) →
      ∃ F' : RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C, Good F' ∧
        (∀ x ∈ P.restrictedKer,
          F' x ∈ (I.map (algebraMap A C)) ^ (2 * (mm - o))) ∧
        ∀ x, F' x - F x ∈ (I.map (algebraMap A C)) ^ (mm - o) := by
    intro mm F hmm hgood hJ
    -- work at the level `max mm n`, which is at least `n`
    have hFJ : ∀ x ∈ P.restrictedKer, F x ∈ (I.map (algebraMap A C)) ^ (max mm n) := by
      intro x hx
      rcases le_total mm n with h | h
      · rw [show max mm n = n by omega]
        exact hgood.2 x hx
      · rw [show max mm n = mm by omega]
        exact hJ x hx
    have hMn : n ≤ max mm n := le_max_right _ _
    have hMm : mm ≤ max mm n := le_max_left _ _
    obtain ⟨δ, hδmem, hδ⟩ := exists_divided_obstruction_of_extension P.restrictedKer
      (fun i => partialDerivative I i) (fun i x y => partialDerivative_mul I i x y) c
      hcramer (I.map (algebraMap A C)) rfl (Nat.sub_le (max mm n) o) (hext (max mm n) hMn) F hFJ
    obtain ⟨F', hF'c, hF'J, hF'd⟩ := exists_perturbed_continuousAlgHom_of_divided I hIfg
      P.restrictedKer (max mm n - o) (max mm n) (by omega) F hgood.1 δ hδmem hδ
    refine ⟨F', ⟨hF'c, fun x hx => ?_⟩, fun x hx => ?_, fun x => ?_⟩
    · exact Ideal.pow_le_pow_right (by omega) (hF'J x hx)
    · exact Ideal.pow_le_pow_right (by omega) (hF'J x hx)
    · exact Ideal.pow_le_pow_right (by omega) (hF'd x)
  obtain ⟨φ, hφker, hφdiff⟩ := exists_limit_algHom (I.map (algebraMap A C))
    P.restrictedKer Good o n (by omega) hstep ψ ⟨hψc, hψJ⟩ hψJ
  -- the final assembly, as in Stacks 0AK6
  set e := RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount) with he
  have hvanish : ∀ x ∈ P.ideal, (φ.comp e.symm.toAlgHom) x = 0 := by
    intro x hx
    rw [← P.ker_eq_ideal] at hx
    refine hφker _ ?_
    rw [RingHom.mem_ker]
    exact show P.toAlgHom (e (e.symm x)) = 0 by rw [e.apply_symm_apply]; exact hx
  refine ⟨(Ideal.Quotient.liftₐ P.ideal (φ.comp e.symm.toAlgHom) hvanish).comp
    P.quotientEquiv.symm.toAlgHom, ?_⟩
  have hfac : ∀ y : RestrictedPowerSeries I (Fin P.variableCount),
      ((Ideal.Quotient.liftₐ P.ideal (φ.comp e.symm.toAlgHom) hvanish).comp
        P.quotientEquiv.symm.toAlgHom) (P.restrictedToAlgHom y) = φ y := by
    intro y
    have hq : P.quotientEquiv.symm (P.restrictedToAlgHom y)
        = Ideal.Quotient.mk P.ideal (e y) :=
      P.quotientEquiv.symm_apply_apply _
    exact show (Ideal.Quotient.liftₐ P.ideal (φ.comp e.symm.toAlgHom) hvanish)
        (P.quotientEquiv.symm (P.restrictedToAlgHom y)) = φ y by
      rw [hq]
      exact show φ (e.symm (e y)) = φ y by rw [e.symm_apply_apply]
  refine AlgHom.ext fun b => ?_
  obtain ⟨z, rfl⟩ := P.restrictedToAlgHom_surjective b
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hfac z, ← hψred z]
  exact show Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ (n - o)) (ψ z)
      = Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ (n - o)) (φ z) by
    rw [Ideal.Quotient.eq]
    simpa using
      ((I.map (algebraMap A C)) ^ (n - o)).neg_mem (hφdiff z)

/-- **Stacks 0GAQ**, with the precision of the conclusion corrected as in the library's Tag 0GAD.

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` an object of the category of Stacks 0AL4 for
`(A, I)` with a completed polynomial presentation `P`, and suppose `I ^ c` annihilates
`Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`. Let `C` be a Noetherian `I`-adically complete
`A`-algebra whose invariants of Local Cohomology, Section 0GA6 are `d` and `q₀`, write
`D = k + 1 = max(d, 1)`, and let `n ≥ q₀ + (1+D)c` with `n > 2(2+D)c`. Then every `A`-algebra map
`ψₙ : B → C / IⁿC` agrees modulo `I^{n-(2+D)c}` with the reduction of an `A`-algebra map
`φ : B → C`.

**Deviation from the source.** The source concludes agreement modulo `I^{n-(1+d)c}` under
`n ≥ max(q₀ + (1+d)c, 2(1+d)c + 1)`. The level reached here is `n - (2+D)c`, which is the level
the source's argument for Tag 0GAD reaches with `D` in place of `d`
(`Stacks.LocalCohomology.UniformityIII.CanDualSituation.ext_one_powQuot_map_eq_zero` at `d`),
and the bound on `n` is adjusted to `n > 2(2+D)c` accordingly; `D = max(d, 1)` in place of `d` is
inherited from the library's Tag 0GAC. The discrepancy is the one that Tag 0GAD's docstring records:
the source's own argument produces maps at level `n - (2+d)c`, and for `d ≥ 1` the module it
asserts the obstruction dies in admits no canonical map to or from the one its argument reaches.
Twisting down is harmless for the iteration, so the only effect is on the numbers.

**The route.** The source passes from `Ext¹_B(NL^∧_{B/A}, N)` to `Ext¹_{C/IⁿC}` of the derived
base change (Tags 0E1W and 0G9G) in order to apply Tag 0GAD. Here the Ext-annihilation
hypothesis is used through Tag 0GAP in its cokernel form — the obstruction relation
`a · g ≡ ∑ i (∂g/∂xᵢ) γᵢ` modulo `J²` of `Rig.exists_restricted_cramer_relation` — which base
changes to `C / IᵐC` by elementary means, so that Tag 0GAC applies directly to the explicit
two-term complex and Tags 0E1W, 0G9G and 0GAD itself are not needed. The level reached is the
one of Tag 0GAD, as it must be: the argument is the same.

**The carried hypotheses.** `S` is the family of `DualSituation`s of Tag 0GA6, one at each
thickness `m ≥ c` — the thicknesses at which one can exist, see the module docstring — with the
invariants `d` and `q₀` independent of `m` (`hd`, `hq₀`); the structure
carries the blowup cohomology of Tag 0GAA, which the library does not build from the blowup.
`hdual` is the open duality input of the library's Tag 0GAC, carried for every level `m ≥ n`: it is
the section of `p^*(M^∨)` at level `m - 2c` obtained by factoring through
`can : p^*(M^∨) → (p^*M)^∨`. Of that step, the annihilation of the kernel and the cokernel of
`can` by `I^c` — "scheme theoretically supported on `Y_c`" — is proved as
`Stacks.LocalCohomology.UniformityIII.IsANCModule.kernel_map_pullbackModuleDualMap_eq_zero` and
`…cokernel_map_pullbackModuleDualMap_eq_zero`; the dual sheaf `(p^*M)^∨` of the pullback, the
passage from the homomorphism to a section of `(p^*M)^∨(m)`, the factorization of its image
through `Γ(p^*(M^∨)(m-2c))`, and a construction of a `ModuleSituation` out of the blowup are
not. Nothing else is assumed.

The family `S` is required only at the thicknesses `m ≥ c` where a `DualSituation` can
exist. `Rig.exists_algHom_lift_of_dualSituation` is the form that asks for one at every
`m`, and follows from this one. -/
public theorem exists_algHom_lift_of_dualSituation'
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (c : ℕ)
    (hExt : ∀ a ∈ I ^ c, ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) • ξ = 0)
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (S : ∀ m : ℕ, c ≤ m → DualSituation C (I.map (algebraMap A C)) m c)
    (d q₀ k : ℕ) (hd : ∀ m (hm : c ≤ m), (S m hm).d = d)
    (hq₀ : ∀ m (hm : c ≤ m), (S m hm).q₀ = q₀)
    (hk : max d 1 = k + 1)
    (n : ℕ) (hn₁ : q₀ + (k + 2) * c ≤ n) (hn₂ : 2 * ((k + 3) * c) < n)
    (hdual : ∀ (m e : ℕ) (hm : c ≤ m) (_ : n ≤ m) (hem : e + 2 * c = m)
      (hq : (S m hm).q₀ ≤ e)
      (M : ANCModule (I.map (algebraMap A C)) m c)
      (φ : resModule (I.map (algebraMap A C)) m M.1 →ₗ[C]
        powQuot (I.map (algebraMap A C)) m m),
      ∃ σ' : (S m hm).H M.dual 0 (e : ℤ),
        (S m hm).ev M e hq σ'
          = (powQuotLe (I.map (algebraMap A C)) (Nat.le.intro hem)).comp φ)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B.carrier →ₐ[A] C,
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (Nat.sub_le n ((k + 3) * c)))).comp ψn =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - (k + 3) * c))).comp φ := by
  have h3 : (k + 3) * c = k * c + 3 * c := by ring
  have h2 : (k + 2) * c = k * c + 2 * c := by ring
  have hkc : c ≤ (k + 3) * c := Nat.le_mul_of_pos_left c (by omega)
  refine exists_algHom_lift_of_extension B P c hExt ((k + 3) * c) n hn₂ (fun m hnm => ?_) ψn
  have hcm : c ≤ m := by omega
  have hqe : (S m hcm).q₀ ≤ m - (k + 3) * c + c := by rw [hq₀]; omega
  have hem : m - (k + 3) * c + c + k * c + 2 * c = m := by omega
  exact extendsAtLevel_of_dualSituation (S m hcm) rfl (by rw [hd]; exact hk) rfl hem hqe
    fun M φ ↦ hdual m _ hcm hnm hem (hqe.trans (Nat.le.intro rfl)) M φ

/-- **Stacks 0GAQ**, with the precision of the conclusion corrected as in the library's Tag 0GAD.

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` an object of the category of Stacks 0AL4 for
`(A, I)` with a completed polynomial presentation `P`, and suppose `I ^ c` annihilates
`Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`. Let `C` be a Noetherian `I`-adically complete
`A`-algebra whose invariants of Local Cohomology, Section 0GA6 are `d` and `q₀`, write
`D = k + 1 = max(d, 1)`, and let `n ≥ q₀ + (1+D)c` with `n > 2(2+D)c`. Then every `A`-algebra map
`ψₙ : B → C / IⁿC` agrees modulo `I^{n-(2+D)c}` with the reduction of an `A`-algebra map
`φ : B → C`.

**Deviation from the source.** The source concludes agreement modulo `I^{n-(1+d)c}` under
`n ≥ max(q₀ + (1+d)c, 2(1+d)c + 1)`. The level reached here is `n - (2+D)c`, which is the level
the source's argument for Tag 0GAD reaches with `D` in place of `d`
(`Stacks.LocalCohomology.UniformityIII.CanDualSituation.ext_one_powQuot_map_eq_zero` at `d`),
and the bound on `n` is adjusted to `n > 2(2+D)c` accordingly; `D = max(d, 1)` in place of `d` is
inherited from the library's Tag 0GAC. The discrepancy is the one that Tag 0GAD's docstring records:
the source's own argument produces maps at level `n - (2+d)c`, and for `d ≥ 1` the module it
asserts the obstruction dies in admits no canonical map to or from the one its argument reaches.
Twisting down is harmless for the iteration, so the only effect is on the numbers.

**The route.** The source passes from `Ext¹_B(NL^∧_{B/A}, N)` to `Ext¹_{C/IⁿC}` of the derived
base change (Tags 0E1W and 0G9G) in order to apply Tag 0GAD. Here the Ext-annihilation
hypothesis is used through Tag 0GAP in its cokernel form — the obstruction relation
`a · g ≡ ∑ i (∂g/∂xᵢ) γᵢ` modulo `J²` of `Rig.exists_restricted_cramer_relation` — which base
changes to `C / IᵐC` by elementary means, so that Tag 0GAC applies directly to the explicit
two-term complex and Tags 0E1W, 0G9G and 0GAD itself are not needed. The level reached is the
one of Tag 0GAD, as it must be: the argument is the same.

**The carried hypotheses.** `S` is the family of `DualSituation`s of Tag 0GA6, one for each
thickness `m`, with the invariants `d` and `q₀` independent of `m` (`hd`, `hq₀`); the structure
carries the blowup cohomology of Tag 0GAA, which the library does not build from the blowup.
`hdual` is the open duality input of the library's Tag 0GAC, carried for every level `m ≥ n`: it is
the section of `p^*(M^∨)` at level `m - 2c` obtained by factoring through
`can : p^*(M^∨) → (p^*M)^∨`, whose kernel and cokernel being scheme theoretically supported on
`Y_c` is not available. Nothing else is assumed. -/
@[stacks 0GAQ "with the conclusion at precision I^{n-(2+D)c}, D = max(d,1) -- the level the \
library's Tag 0GAD reaches -- in place of the source's I^{n-(1+d)c}, and with n > 2(2+D)c for the \
source's n > 2(1+d)c; the Ext hypothesis is used through Tag 0GAP's cokernel form and Tag 0GAC, \
so Tags 0E1W, 0G9G and 0GAD are not invoked; carries 0GAC's open duality input as `hdual`, and \
d, q₀ as a family `S` of DualSituations with m-independent invariants"]
public theorem exists_algHom_lift_of_dualSituation
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (c : ℕ)
    (hExt : ∀ a ∈ I ^ c, ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) • ξ = 0)
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (S : ∀ m : ℕ, DualSituation C (I.map (algebraMap A C)) m c)
    (d q₀ k : ℕ) (hd : ∀ m, (S m).d = d) (hq₀ : ∀ m, (S m).q₀ = q₀)
    (hk : max d 1 = k + 1)
    (n : ℕ) (hn₁ : q₀ + (k + 2) * c ≤ n) (hn₂ : 2 * ((k + 3) * c) < n)
    (hdual : ∀ (m e : ℕ) (_ : n ≤ m) (hem : e + 2 * c = m) (hq : (S m).q₀ ≤ e)
      (M : ANCModule (I.map (algebraMap A C)) m c)
      (φ : resModule (I.map (algebraMap A C)) m M.1 →ₗ[C]
        powQuot (I.map (algebraMap A C)) m m),
      ∃ σ' : (S m).H M.dual 0 (e : ℤ),
        (S m).ev M e hq σ'
          = (powQuotLe (I.map (algebraMap A C)) (Nat.le.intro hem)).comp φ)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B.carrier →ₐ[A] C,
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (Nat.sub_le n ((k + 3) * c)))).comp ψn =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - (k + 3) * c))).comp φ :=
  exists_algHom_lift_of_dualSituation' B P c hExt (fun m _ ↦ S m) d q₀ k
    (fun m _ ↦ hd m) (fun m _ ↦ hq₀ m) hk n hn₁ hn₂
    (fun m e _ hnm hem hq M φ ↦ hdual m e hnm hem hq M φ) ψn

end Main

end Rig

end
