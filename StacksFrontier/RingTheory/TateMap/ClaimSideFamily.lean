module

public import StacksFrontier.RingTheory.TateMap.ClaimEngine
public import StacksFrontier.RingTheory.TateMap.ClaimNaturality

/-!
# The family realizing one side of a comparison of presentations

Starting from a basic chart `C = univChart n d k` of the universal family, the *side family*
adds generic coefficients for a localization element `E(x)` and for graph polynomials
`ψ_1(x, t), …, ψ_m(x, t)` (and possibly further parameters `τ`): over the parameter ring
`S = univBase n d [σ]` it is

`Z = S[x_1, …, x_n, 1/(k E)]/(f_1, …, f_n)`,

and it has the second, global presentation obtained by removing the localization (a new
variable `t` with `k E t = 1`) and adding the graph variables `y_j = ψ_j(x, t)`.

## Main definitions

* `Stacks.TateMap.sideBase`, `Stacks.TateMap.sideE`, `Stacks.TateMap.sideψ`: the parameter ring
  and the generic polynomials.
* `Stacks.TateMap.sideRel`, `Stacks.TateMap.sideθ`: the global graph presentation of `Z`.
* `Stacks.TateMap.sideSpec`: the specialization of the parameters.
* `Stacks.TateMap.globalGraphEquiv`: the global graph presentation of a presentation
  `S[x, 1/H]/(f)`.

## Main results

* `Stacks.TateMap.isNiceChart_side`: over a quasi-finite basic chart which is a domain
  unramified at its generic point, the side family is Noetherian, flat, quasi-finite, of finite
  type and nice over the parameter ring.
-/

@[expose] public section

open MvPolynomial Stacks.Discriminant AlgebraicGeometry

universe u

namespace Stacks.TateMap

/-- The module structure of a localized complete intersection over its coefficient ring, coming
from its algebra structure. -/
noncomputable instance (priority := high) lciModule {S : Type u} [CommRing S] {N : ℕ}
    (h : MvPolynomial (Fin N) S) (f : Fin N → MvPolynomial (Fin N) S) :
    Module S (localizedCompleteIntersection S N h f) :=
  Algebra.toModule

/-- **The global graph move** of a presentation `S[x, 1/H]/(f)`: remove the localization (a new
variable `t` with `H t = 1`), then add graph variables `y = ψ(x, t)`. -/
noncomputable def globalGraphEquiv {S : Type u} [CommRing S] {n m N : ℕ}
    (eV : Fin (n + 1) ⊕ Fin m ≃ Fin N) (H : MvPolynomial (Fin n) S)
    (f : Fin n → MvPolynomial (Fin n) S) (ψ : Fin m → MvPolynomial (Fin (n + 1)) S) :
    localizedCompleteIntersection S n H f ≃ₐ[S]
      localizedCompleteIntersection S N 1 (graphRelations eV eV 1 (globalRelations H f) ψ 0) :=
  (lciGlobalEquiv H f).trans ((lciGraphEquiv eV eV 1 (globalRelations H f) ψ 0).trans
    (localizedCompleteIntersectionCongr (map_one _) rfl))

/-- The inverse of `globalGraphEquiv` on the class of a polynomial `q`: the inverse of the graph
move followed by the inverse of the removal of the localization. -/
theorem globalGraphEquiv_symm_lciMk {S : Type u} [CommRing S] {n m N : ℕ}
    (eV : Fin (n + 1) ⊕ Fin m ≃ Fin N) (H : MvPolynomial (Fin n) S)
    (f : Fin n → MvPolynomial (Fin n) S) (ψ : Fin m → MvPolynomial (Fin (n + 1)) S)
    (q : MvPolynomial (Fin N) S) :
    (globalGraphEquiv eV H f ψ).symm (lciMk _ _ q) =
      (lciGlobalEquiv H f).symm ((lciGraphEquiv eV eV 1 (globalRelations H f) ψ 0).symm
        (lciMk _ _ q)) := by
  rw [globalGraphEquiv, AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply, congr_symm_lciMk]

/-- Changing the localization element of a global presentation to a unit `D`:
`S[x, 1/D]/(r) ≅ S[x]/(r)`. -/
noncomputable def lciDetEquiv {S : Type u} [CommRing S] {N : ℕ} (D : MvPolynomial (Fin N) S)
    (r : Fin N → MvPolynomial (Fin N) S) (hD : IsUnit (lciMk 1 r D)) :
    localizedCompleteIntersection S N D r ≃ₐ[S] localizedCompleteIntersection S N 1 r :=
  lciEquivOfUnit hD (lciMk_relation _ _) (by rw [map_one]; exact isUnit_one) (lciMk_relation _ _)

/-- `lciDetEquiv` sends the class of a polynomial `q` to the class of `q`. -/
theorem lciDetEquiv_lciMk {S : Type u} [CommRing S] {N : ℕ} (D : MvPolynomial (Fin N) S)
    (r : Fin N → MvPolynomial (Fin N) S) (hD : IsUnit (lciMk 1 r D)) (q : MvPolynomial (Fin N) S) :
    lciDetEquiv D r hD (lciMk _ _ q) = lciMk _ _ q :=
  lciEquivOfUnit_lciMk _ _ _ _ q

variable (n d : ℕ) (k : MvPolynomial (Fin n) (univBase.{u} n d)) (e₁ m e₂ : ℕ) (τ : Type)

/-- The parameters: the coefficients of `E`, those of `ψ_1, …, ψ_m`, and further parameters
`τ`. -/
abbrev sideσ : Type := (Unit × MultiIndex n e₁) ⊕ ((Fin m × MultiIndex (n + 1) e₂) ⊕ τ)

/-- The parameter ring `univBase n d [σ]`. -/
abbrev sideBase : Type u := MvPolynomial (sideσ n e₁ m e₂ τ) (univBase.{u} n d)

/-- The generic localization element `E(x)` of degree at most `e₁`. -/
noncomputable def sideE : MvPolynomial (Fin n) (sideBase.{u} n d e₁ m e₂ τ) :=
  MvPolynomial.map (rename Sum.inl : MvPolynomial (Unit × MultiIndex n e₁) (univBase.{u} n d) →ₐ[_]
    sideBase.{u} n d e₁ m e₂ τ).toRingHom (genPoly (univBase.{u} n d) Unit n e₁ ())

/-- The generic graph polynomials `ψ_j(x, t)` of degree at most `e₂`. -/
noncomputable def sideψ (j : Fin m) : MvPolynomial (Fin (n + 1)) (sideBase.{u} n d e₁ m e₂ τ) :=
  MvPolynomial.map (rename (Sum.inr ∘ Sum.inl) :
    MvPolynomial (Fin m × MultiIndex (n + 1) e₂) (univBase.{u} n d) →ₐ[_]
      sideBase.{u} n d e₁ m e₂ τ).toRingHom (genPoly (univBase.{u} n d) (Fin m) (n + 1) e₂ j)

/-- The localization element `k E` of the family. -/
noncomputable abbrev sideH : MvPolynomial (Fin n) (sideBase.{u} n d e₁ m e₂ τ) :=
  paramH k (sideσ n e₁ m e₂ τ) * sideE n d e₁ m e₂ τ

/-- The relations of the family. -/
noncomputable abbrev sideF : Fin n → MvPolynomial (Fin n) (sideBase.{u} n d e₁ m e₂ τ) :=
  paramF (univPoly n d) (sideσ n e₁ m e₂ τ)

variable {N : ℕ} (e : Fin (n + 1) ⊕ Fin m ≃ Fin N)

/-- The relations of the global graph presentation of the family. -/
noncomputable abbrev sideRel : Fin N → MvPolynomial (Fin N) (sideBase.{u} n d e₁ m e₂ τ) :=
  graphRelations e e 1 (globalRelations (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ))
    (sideψ n d e₁ m e₂ τ) 0

/-- The global graph presentation of the family. -/
noncomputable def sideθ :
    localizedCompleteIntersection _ n (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ)
      ≃ₐ[sideBase.{u} n d e₁ m e₂ τ] localizedCompleteIntersection (sideBase.{u} n d e₁ m e₂ τ) N
        1 (sideRel n d k e₁ m e₂ τ e) :=
  (lciGlobalEquiv _ _).trans ((lciGraphEquiv e e 1 _ (sideψ n d e₁ m e₂ τ) 0).trans
    (localizedCompleteIntersectionCongr (map_one _) rfl))

/-- The inverse of `sideθ` on the class of a polynomial `q`: the inverse of the graph move
followed by the inverse of the removal of the localization. -/
theorem sideθ_symm_lciMk (q : MvPolynomial (Fin N) (sideBase.{u} n d e₁ m e₂ τ)) :
    (sideθ n d k e₁ m e₂ τ e).symm (lciMk _ _ q) =
      (lciGlobalEquiv (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ)).symm
        ((lciGraphEquiv e e 1 (globalRelations (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ))
          (sideψ n d e₁ m e₂ τ) 0).symm (lciMk _ _ q)) := by
  rw [sideθ, AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply, congr_symm_lciMk]

section Spec

variable {A : Type u} [CommRing A] (φ : univBase.{u} n d →+* A) (p : MvPolynomial (Fin n) A)
  (ψ : Fin m → MvPolynomial (Fin (n + 1)) A) (t : τ → A)

/-- The specialization of the parameters to the coefficients of `p`, of the `ψ_j`, and to
`t`. -/
noncomputable def sideSpec : sideBase.{u} n d e₁ m e₂ τ →+* A :=
  eval₂Hom φ (Sum.elim (fun iα ↦ coeff (multiIndexExponent n e₁ iα.2) p)
    (Sum.elim (fun jα ↦ coeff (multiIndexExponent (n + 1) e₂ jα.2) (ψ jα.1)) t))

/-- The specialization of the parameters is `φ` on the constants. -/
theorem sideSpec_C (c : univBase.{u} n d) :
    sideSpec n d e₁ m e₂ τ φ p ψ t (MvPolynomial.C c) = φ c :=
  eval₂Hom_C _ _ _

/-- The specialization of the parameters restricts to `φ` on `univBase n d`. -/
theorem sideSpec_comp_algebraMap :
    (sideSpec n d e₁ m e₂ τ φ p ψ t).comp (algebraMap _ (sideBase.{u} n d e₁ m e₂ τ)) = φ :=
  RingHom.ext fun c ↦ sideSpec_C n d e₁ m e₂ τ φ p ψ t c

/-- Specializing the parameters in the relations of the family gives the images under `φ` of
the universal relations. -/
theorem map_sideSpec_paramF (i : Fin n) :
    MvPolynomial.map (sideSpec n d e₁ m e₂ τ φ p ψ t) (sideF n d e₁ m e₂ τ i) =
      MvPolynomial.map φ (univPoly n d i) := by
  rw [MvPolynomial.map_map, sideSpec_comp_algebraMap]

/-- Specializing the parameters in `k`, read over the parameter ring, gives the image of `k`
under `φ`. -/
theorem map_sideSpec_paramH :
    MvPolynomial.map (sideSpec n d e₁ m e₂ τ φ p ψ t) (paramH k (sideσ n e₁ m e₂ τ)) =
      MvPolynomial.map φ k := by
  rw [MvPolynomial.map_map, sideSpec_comp_algebraMap]

/-- Specializing the parameters in a generic polynomial whose coefficient variables are sent into
the parameters by `g` gives the polynomial whose coefficients they specialize to. -/
private theorem map_sideSpec_map_rename_genPoly {ι : Type} {w ε : ℕ}
    (g : ι × MultiIndex w ε → sideσ n e₁ m e₂ τ) (P : ι → MvPolynomial (Fin w) A)
    (hg : ∀ iα, sideSpec n d e₁ m e₂ τ φ p ψ t (X (g iα)) =
      coeff (multiIndexExponent w ε iα.2) (P iα.1))
    (hP : ∀ j, (P j).totalDegree ≤ ε) (j : ι) :
    MvPolynomial.map (sideSpec n d e₁ m e₂ τ φ p ψ t)
      (MvPolynomial.map (rename g : MvPolynomial (ι × MultiIndex w ε) (univBase.{u} n d) →ₐ[_]
        sideBase.{u} n d e₁ m e₂ τ).toRingHom (genPoly (univBase.{u} n d) ι w ε j)) = P j := by
  let := φ.toAlgebra
  have : (sideSpec n d e₁ m e₂ τ φ p ψ t).comp
      (rename g : MvPolynomial (ι × MultiIndex w ε) (univBase.{u} n d) →ₐ[_]
        sideBase.{u} n d e₁ m e₂ τ).toRingHom =
      (genSpec (e := ε) (R := univBase.{u} n d) P :
        MvPolynomial (ι × MultiIndex w ε) (univBase.{u} n d) →+* A) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun iα ↦ ?_)
    · simp [sideSpec, genSpec, RingHom.algebraMap_toAlgebra]
    · simpa [genSpec] using hg iα
  rw [MvPolynomial.map_map, this]
  exact map_genPoly P hP j

/-- If `p` has total degree at most `e₁`, specializing the parameters in the generic
localization element `E` gives `p`. -/
theorem map_sideSpec_sideE (hp : p.totalDegree ≤ e₁) :
    MvPolynomial.map (sideSpec n d e₁ m e₂ τ φ p ψ t) (sideE n d e₁ m e₂ τ) = p :=
  map_sideSpec_map_rename_genPoly n d e₁ m e₂ τ φ p ψ t Sum.inl (fun _ ↦ p)
    (fun _ ↦ by simp [sideSpec]) (fun _ ↦ hp) ()

/-- If every `ψ_j` has total degree at most `e₂`, specializing the parameters in the generic
graph polynomial `ψ_j` gives `ψ_j`. -/
theorem map_sideSpec_sideψ (hψ : ∀ j, (ψ j).totalDegree ≤ e₂) (j : Fin m) :
    MvPolynomial.map (sideSpec n d e₁ m e₂ τ φ p ψ t) (sideψ n d e₁ m e₂ τ j) = ψ j :=
  map_sideSpec_map_rename_genPoly n d e₁ m e₂ τ φ p ψ t (Sum.inr ∘ Sum.inl) ψ
    (fun _ ↦ by simp [sideSpec]) hψ j

end Spec

section Nice

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The specialization of the parameters `E ↦ 1`, `ψ ↦ 0`, `τ ↦ 0`, over `univBase n d`. -/
noncomputable abbrev sideUnit : sideBase.{u} n d e₁ m e₂ τ →+* univBase.{u} n d :=
  sideSpec n d e₁ m e₂ τ (RingHom.id _) 1 0 0

/-- The image of the generic localization element in `C[σ]` is not zero, for `C` a nonzero
basic chart. -/
theorem paramImage_sideE_ne_zero [Nontrivial (univChart n d k)] :
    paramImage k (univPoly n d) (sideσ n e₁ m e₂ τ) (sideE n d e₁ m e₂ τ) ≠ 0 := by
  set π₀ := sideUnit.{u} n d e₁ m e₂ τ
  let π : MvPolynomial (sideσ n e₁ m e₂ τ) (univChart n d k) →+* univChart n d k :=
    eval₂Hom (RingHom.id _) fun s ↦ algebraMap (univBase.{u} n d) _ (π₀ (X s))
  have hc : ∀ c : sideBase.{u} n d e₁ m e₂ τ,
      π (MvPolynomial.map (algebraMap (univBase.{u} n d) (univChart n d k)) c) =
        algebraMap _ _ (π₀ c) := by
    intro c
    simp only [π, eval₂Hom_map_hom]
    induction c using MvPolynomial.induction_on with
    | C r => simp [π₀, sideSpec]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p s hp => rw [map_mul, map_mul, map_mul, hp, eval₂Hom_X']
  have key : ∀ q : MvPolynomial (Fin n) (sideBase.{u} n d e₁ m e₂ τ),
      π (paramEquiv k (univPoly n d) _ (lciMk _ _ q)) =
        lciMk k (univPoly n d) (MvPolynomial.map π₀ q) := by
    have := MvPolynomial.ringHom_ext
      (f := π.comp ((paramEquiv k (univPoly n d) (sideσ n e₁ m e₂ τ)).toRingEquiv.toRingHom.comp
        (lciMk (paramH k (sideσ n e₁ m e₂ τ))
          (paramF (univPoly n d) (sideσ n e₁ m e₂ τ))).toRingHom))
      (g := (lciMk k (univPoly n d)).toRingHom.comp (MvPolynomial.map π₀)) (fun c ↦ ?_)
      (fun i ↦ ?_)
    · exact fun q ↦ congrArg (· q) this
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, MvPolynomial.map_C]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgEquiv.commutes,
        MvPolynomial.algebraMap_def, hc, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, MvPolynomial.map_X]
      rw [paramEquiv_lciMk_X]
      exact eval₂Hom_C _ _ _
  intro h0
  have h1 := key (sideE n d e₁ m e₂ τ)
  rw [map_sideSpec_sideE n d e₁ m e₂ τ (RingHom.id _) 1 0 0 (by simp)] at h1
  rw [show paramEquiv k (univPoly n d) _ (lciMk _ _ (sideE n d e₁ m e₂ τ)) = 0 from h0,
    map_zero, map_one] at h1
  exact zero_ne_one h1

end Nice

/-- **Niceness of the side family.** For a quasi-finite basic chart which is a domain unramified
at its generic point, the side family is Noetherian, flat, quasi-finite and of finite type over
the parameter ring, and nice. -/
theorem isNiceChart_side [Finite τ] [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
    [IsDomain (univChart n d k)]
    [Algebra.IsUnramifiedAt (univBase.{u} n d) (⊥ : Ideal (univChart n d k))] :
    ∃ (_ : IsNoetherianRing (localizedCompleteIntersection (sideBase.{u} n d e₁ m e₂ τ) n
        (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ)))
      (_ : Module.Flat (sideBase.{u} n d e₁ m e₂ τ) (localizedCompleteIntersection
        (sideBase.{u} n d e₁ m e₂ τ) n (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ)))
      (_ : Algebra.QuasiFinite (sideBase.{u} n d e₁ m e₂ τ) (localizedCompleteIntersection
        (sideBase.{u} n d e₁ m e₂ τ) n (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ))),
      Algebra.FiniteType (sideBase.{u} n d e₁ m e₂ τ) (localizedCompleteIntersection
        (sideBase.{u} n d e₁ m e₂ τ) n (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ)) ∧
      IsNiceChart (sideBase.{u} n d e₁ m e₂ τ) (localizedCompleteIntersection
        (sideBase.{u} n d e₁ m e₂ τ) n (sideH n d k e₁ m e₂ τ) (sideF n d e₁ m e₂ τ)) := by
  have := Fintype.ofFinite τ
  exact isNiceChart_paramExt k (univPoly n d) (sideσ n e₁ m e₂ τ) (sideE n d e₁ m e₂ τ)
    (paramImage_sideE_ne_zero n d k e₁ m e₂ τ) ⊥


end Stacks.TateMap
