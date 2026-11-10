module

public import StacksFrontier.RingTheory.Cech.Substrate
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Additive

/-!
# Base change of the extended alternating Čech complex

Let `R` be a commutative ring, `f_1, …, f_r ∈ R`, `M` an `R`-module and `R → S` a ring map.
Write `g_i` for the image of `f_i` in `S` and `N = S ⊗_R M`. The extended alternating Čech
complex `C^•(g_1, …, g_r; N)` over `S` is canonically isomorphic to the base change
`C^•(f_1, …, f_r; M) ⊗_R S`: in each degree the comparison sends `c ⊗ (m / u)` to
`(c · (1 ⊗ m)) / u`, expressing that localization commutes with base change.

## Main definitions

* `Stacks.CechBaseChange.baseChangeR`: the `R`-linear comparison map `M_{f|s} → N_{g|s}`,
  `m / u ↦ (1 ⊗ m) / u`.
* `Stacks.CechBaseChange.baseChangeS`: the `S`-linear comparison map `S ⊗_R M_{f|s} → N_{g|s}`,
  `c ⊗ (m / u) ↦ (c · (1 ⊗ m)) / u`.
* `Stacks.CechBaseChange.baseChangeSEquiv`: `baseChangeS` as an `S`-linear isomorphism.
* `Stacks.CechBaseChange.termBaseChangeS`: the `S`-linear comparison map
  `S ⊗_R C^p(f; M) → C^p(g; N)`.
* `Stacks.CechBaseChange.termBaseChangeSInv`: the degreewise inverse of `termBaseChangeS`,
  assembled from the inverses of `baseChangeSEquiv` over each summand.
* `Stacks.CechBaseChange.termBaseChangeEquiv`: the degreewise `S`-linear isomorphism
  `S ⊗_R C^p(f; M) ≃ₗ[S] C^p(g; N)`.
* `Stacks.CechBaseChange.termBaseChangeEquivULift`: `termBaseChangeEquiv` with its target lifted to
  the universe of the base-change complex.
* `Stacks.CechBaseChange.cechModEmptyEquiv`: the localization of `M` at the empty subset is
  `M` itself.
* `Stacks.CechBaseChange.cechComplexBaseChange`: the cochain complex of `S`-modules with terms
  `S ⊗_R C^p(f; M)` and differentials `id_S ⊗ d^p`.
* `Stacks.CechBaseChange.cechComplexBaseChangeTarget`: the Čech complex `C^•(g; N)`, lifted to the
  universe of `cechComplexBaseChange`.
* `Stacks.CechBaseChange.cechComplexBaseChangeIso`: the isomorphism of cochain complexes
  `C^•(f; M) ⊗_R S ≅ C^•(g; N)` with degree-`p` component `termBaseChangeS`.

## Main results

* `Stacks.CechBaseChange.baseChangeS_bijective`: the comparison map at a single subset is
  bijective.
* `Stacks.CechBaseChange.termBaseChangeS_bijective`: the degreewise comparison map is bijective.
* `Stacks.CechBaseChange.termBaseChangeS_comm_d`: the comparison maps commute with the
  differentials.
* `Stacks.CechBaseChange.cechComplexBaseChangeIso_hom_f`: lowering the universe lift, each
  component of `cechComplexBaseChangeIso` is `termBaseChangeS`.
* `Stacks.CechBaseChange.exists_cechComplexBaseChange_iso`: the isomorphism of cochain complexes
  `C^•(f; M) ⊗_R S ≅ C^•(g; N)` whose components are `termBaseChangeS`.
* `Stacks.CechBaseChange.cechSub_empty`: the localizing submonoid of the empty subset is trivial.
* `Stacks.CechBaseChange.isLocalization_cechSub_empty`,
  `Stacks.CechBaseChange.isLocalizedModule_id_cechSub_empty`: `R` and `M` are their own
  localizations at the empty subset.

## Implementation notes

The target complex is lifted to the universe of the base-change complex so that `R`, `M`
and `S` may live in independent universes; after lowering the lift, each component of the
isomorphism is exactly `termBaseChangeS`.

## References

* [Stacks Project, Tag 0G6I](https://stacks.math.columbia.edu/tag/0G6I)
-/

@[expose] public section

namespace Stacks.CechBaseChange

noncomputable section

open Finset TensorProduct CategoryTheory Cech

universe u v w

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  (M : Type v) [AddCommGroup M] [Module R M] (S : Type w) [CommRing S] [Algebra R S]

/-- The images `g_i = algebraMap R S (f i)` of the elements `f_i` under `R → S`. -/
abbrev gfun : Fin r → S := fun i => algebraMap R S (f i)

/-- The product of the `g_i` over `s` is the image of the product of the `f_i`. -/
theorem gfun_prod (s : Finset (Fin r)) : ∏ i ∈ s, gfun f S i = algebraMap R S (∏ i ∈ s, f i) :=
  (map_prod (algebraMap R S) f s).symm

/-! ## Invertibility of the localizing elements -/

/-- Restricting scalars from `S` to `R` sends a unit of `Module.End S T` to a unit of
`Module.End R T`. -/
theorem isUnit_restrictScalars {T : Type*} [AddCommMonoid T] [Module S T] [Module R T]
    [IsScalarTower R S T] {e : Module.End S T} (he : IsUnit e) :
    IsUnit (e.restrictScalars R) :=
  (Module.End.isUnit_iff _).2 ((Module.End.isUnit_iff e).1 he)

/-- The base change `id_S ⊗ e` of a unit `e` of `Module.End R N` is a unit. -/
theorem isUnit_baseChange {N : Type*} [AddCommMonoid N] [Module R N] {e : Module.End R N}
    (he : IsUnit e) : IsUnit (LinearMap.baseChange S e) :=
  he.map (Module.End.baseChangeHom R S N)

/-- The scalar action of `R` on `Module.End R T` is the restriction of that of `S`. -/
private theorem algebraMap_end_eq_restrictScalars {T : Type*} [AddCommMonoid T] [Module S T]
    [Module R T] [IsScalarTower R S T] (x : R) :
    algebraMap R (Module.End R T) x
      = (algebraMap S (Module.End S T) (algebraMap R S x)).restrictScalars R := by
  ext y
  simp only [Module.algebraMap_end_apply, LinearMap.coe_restrictScalars, algebraMap_smul]

/-- Each element of `cechSub f s` acts invertibly on `N_{g|t}` whenever `s ⊆ t`, where
`N = S ⊗_R M`. -/
theorem isUnit_algebraMapR_gfun {s t : Finset (Fin r)} (hst : s ⊆ t) (x : cechSub f s) :
    IsUnit ((algebraMap R (Module.End R
      (cechMod (gfun f S) (TensorProduct R S M) t))) (x : R)) := by
  obtain ⟨n, hn⟩ := x.2
  have hSunit := isUnit_algebraMap (gfun f S) (TensorProduct R S M) hst
    (LocalizedModule.mkLinearMap (cechSub (gfun f S) t) (TensorProduct R S M))
    ⟨_, Submonoid.mem_powers (∏ j ∈ s, gfun f S j)⟩
  rw [← hn, map_pow, algebraMap_end_eq_restrictScalars S, ← gfun_prod]
  exact (isUnit_restrictScalars S hSunit).pow n

/-! ## Comparison at a single subset -/

/-- The canonical `R`-linear base-change comparison map at a single subset `s`:
`M_{f_{i_0}⋯f_{i_{p-1}}} → N_{g_{i_0}⋯g_{i_{p-1}}}` where `N = S ⊗_R M`. It sends `m / u` to
`(1 ⊗ m) / (image of u)`. -/
def baseChangeR (s : Finset (Fin r)) :
    cechMod f M s →ₗ[R] cechMod (gfun f S) (TensorProduct R S M) s :=
  LocalizedModule.lift _
    (((LocalizedModule.mkLinearMap (cechSub (gfun f S) s)
        (TensorProduct R S M)).restrictScalars R).comp ((TensorProduct.mk R S M) 1))
    (isUnit_algebraMapR_gfun f M S (subset_refl s))

/-- `baseChangeR` sends `m / 1` to `(1 ⊗ m) / 1`. -/
@[simp]
theorem baseChangeR_mk (s : Finset (Fin r)) (m : M) :
    baseChangeR f M S s (LocalizedModule.mkLinearMap (cechSub f s) M m)
      = LocalizedModule.mkLinearMap (cechSub (gfun f S) s) (TensorProduct R S M)
        ((1 : S) ⊗ₜ m) := by
  rw [LocalizedModule.mkLinearMap_apply, baseChangeR, LocalizedModule.lift_mk]; simp

/-- `baseChangeR` intertwines the localization maps `cechι` for `s ⊆ t`. -/
theorem baseChangeR_comm_cechι {s t : Finset (Fin r)} (hst : s ⊆ t) :
    (baseChangeR f M S t).comp (cechι f M hst)
      = ((cechι (gfun f S) (TensorProduct R S M) hst).restrictScalars R).comp
          (baseChangeR f M S s) := by
  refine IsLocalizedModule.ext (cechSub f s) (LocalizedModule.mkLinearMap (cechSub f s) M)
    (isUnit_algebraMapR_gfun f M S hst) ?_
  ext m
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
  rw [cechι_mk, baseChangeR_mk, baseChangeR_mk, cechι_mk]

/-- The canonical `S`-linear base-change comparison map at a single subset `s`:
`S ⊗_R M_{f|s} → N_{g|s}`, sending `c ⊗ (m / u)` to `(c · (1 ⊗ m)) / u`. -/
def baseChangeS (s : Finset (Fin r)) :
    TensorProduct R S (cechMod f M s) →ₗ[S] cechMod (gfun f S) (TensorProduct R S M) s :=
  (baseChangeR f M S s).liftBaseChange S

/-- `baseChangeS` sends `c ⊗ x` to `c • baseChangeR x`. -/
@[simp]
theorem baseChangeS_tmul (s : Finset (Fin r)) (c : S) (x : cechMod f M s) :
    baseChangeS f M S s (c ⊗ₜ x) = c • baseChangeR f M S s x :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- `baseChangeS` sends `c ⊗ (m / 1)` to `(c ⊗ m) / 1`. -/
@[simp high]
theorem baseChangeS_tmul_mk (s : Finset (Fin r)) (c : S) (m : M) :
    baseChangeS f M S s (c ⊗ₜ (LocalizedModule.mkLinearMap (cechSub f s) M m))
      = LocalizedModule.mkLinearMap (cechSub (gfun f S) s) (TensorProduct R S M) (c ⊗ₜ m) := by
  rw [baseChangeS_tmul, baseChangeR_mk, ← LinearMap.map_smul]
  congr 1
  rw [TensorProduct.smul_tmul']; simp

/-- The product of the `f_i` over `s` acts invertibly on `M_{f|s}`. -/
theorem isUnit_algebraMap_prod (s : Finset (Fin r)) :
    IsUnit ((algebraMap R (Module.End R (cechMod f M s))) (∏ i ∈ s, f i)) := by
  have hmem : (∏ i ∈ s, f i) ∈ cechSub f s := Submonoid.mem_powers _
  exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap _ _) ⟨_, hmem⟩

/-- Each element of `cechSub (gfun f S) s` acts invertibly on `S ⊗_R M_{f|s}`. -/
theorem isUnit_algebraMapS_tensor (s : Finset (Fin r)) (x : cechSub (gfun f S) s) :
    IsUnit ((algebraMap S (Module.End S (TensorProduct R S (cechMod f M s)))) (x : S)) := by
  obtain ⟨_, n, rfl⟩ := x
  have key : (algebraMap S (Module.End S (TensorProduct R S (cechMod f M s))))
        (algebraMap R S (∏ i ∈ s, f i))
      = LinearMap.baseChange S ((algebraMap R (Module.End R (cechMod f M s))) (∏ i ∈ s, f i)) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext c
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      Module.algebraMap_end_apply, LinearMap.baseChange_tmul]
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, algebraMap_smul]
  change IsUnit ((algebraMap S (Module.End S (TensorProduct R S (cechMod f M s))))
    ((∏ i ∈ s, gfun f S i) ^ n))
  rw [gfun_prod, map_pow, key]
  exact (isUnit_baseChange S (isUnit_algebraMap_prod f M s)).pow n

/-- Each element of `cechSub f s` acts invertibly on `S ⊗_R M_{f|s}` as an `R`-module. -/
theorem isUnit_algebraMapR_tensor (s : Finset (Fin r)) (x : cechSub f s) :
    IsUnit ((algebraMap R (Module.End R (TensorProduct R S (cechMod f M s)))) (x : R)) := by
  obtain ⟨_, n, rfl⟩ := x
  rw [map_pow, algebraMap_end_eq_restrictScalars S, ← gfun_prod]
  exact (isUnit_restrictScalars S
    (isUnit_algebraMapS_tensor f M S s ⟨_, Submonoid.mem_powers _⟩)).pow n

/-- The comparison map `baseChangeS f M S s : S ⊗_R M_{f|s} → N_{g|s}` is bijective. -/
theorem baseChangeS_bijective (s : Finset (Fin r)) :
    Function.Bijective (baseChangeS f M S s) := by
  set Φ := baseChangeS f M S s with hΦdef
  have Phi_one_tmul : ∀ x : cechMod f M s, Φ ((1 : S) ⊗ₜ x) = baseChangeR f M S s x := by
    intro x
    rw [hΦdef, baseChangeS_tmul, one_smul]
  set lN' : TensorProduct R S M →ₗ[S] TensorProduct R S (cechMod f M s) :=
    LinearMap.baseChange S (LocalizedModule.mkLinearMap (cechSub f s) M) with hlN'
  set Ψ : cechMod (gfun f S) (TensorProduct R S M) s →ₗ[S] TensorProduct R S (cechMod f M s) :=
    LocalizedModule.lift (cechSub (gfun f S) s) lN' (isUnit_algebraMapS_tensor f M S s) with hΨdef
  have Psi_mk : ∀ n : TensorProduct R S M,
      Ψ (LocalizedModule.mkLinearMap (cechSub (gfun f S) s) (TensorProduct R S M) n) = lN' n := by
    intro n
    rw [hΨdef, LocalizedModule.mkLinearMap_apply, LocalizedModule.lift_mk]; simp
  have Phi_lN' : ∀ n : TensorProduct R S M,
      Φ (lN' n) = LocalizedModule.mkLinearMap (cechSub (gfun f S) s) (TensorProduct R S M) n := by
    intro n
    induction n with
    | tmul c m => rw [hlN', LinearMap.baseChange_tmul, hΦdef, baseChangeS_tmul_mk]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  have hA : (Ψ.restrictScalars R) ∘ₗ (baseChangeR f M S s) =
      (TensorProduct.mk R S (cechMod f M s) 1) := by
    apply IsLocalizedModule.ext (cechSub f s) (LocalizedModule.mkLinearMap (cechSub f s) M)
        (isUnit_algebraMapR_tensor f M S s)
    ext m
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, baseChangeR_mk, Psi_mk,
      hlN', LinearMap.baseChange_tmul, TensorProduct.mk_apply]
  have hΨΦ : Ψ ∘ₗ Φ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext c
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.comp_apply, LinearMap.id_coe, id_eq]
    rw [Phi_one_tmul]
    exact LinearMap.congr_fun hA c
  have hΦΨ : Φ ∘ₗ Ψ = LinearMap.id := by
    apply IsLocalizedModule.ext (cechSub (gfun f S) s)
      (LocalizedModule.mkLinearMap (cechSub (gfun f S) s) (TensorProduct R S M))
      (fun x => IsLocalizedModule.map_units
        (LocalizedModule.mkLinearMap (cechSub (gfun f S) s) (TensorProduct R S M)) x)
    refine LinearMap.ext fun n => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq, Psi_mk, Phi_lN']
  exact (LinearEquiv.ofLinearMap Φ Ψ hΦΨ hΨΦ : _ ≃ₗ[S] _).bijective

/-! ## The degreewise comparison -/

/-- The canonical `R`-linear base-change comparison map on degree-`p` terms:
`C^p(f; M) → C^p(g; N)` assembled from `baseChangeR` over each summand. -/
def termBaseChangeR (p : ℕ) : cechTerm f M p →ₗ[R] cechTerm (gfun f S) (TensorProduct R S M) p :=
  DirectSum.toModule R _ _ (fun s =>
    (DirectSum.lof R {t : Finset (Fin r) // t.card = p}
      (fun t => cechMod (gfun f S) (TensorProduct R S M) t.1) s).comp (baseChangeR f M S s.1))

/-- `termBaseChangeR` sends the summand `lof s x` to `lof s (baseChangeR s x)`. -/
@[simp]
theorem termBaseChangeR_lof (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (x : cechMod f M s.1) :
    termBaseChangeR f M S p (DirectSum.lof R _ (fun t => cechMod f M t.1) s x)
      = DirectSum.lof R _ (fun t => cechMod (gfun f S) (TensorProduct R S M) t.1) s
          (baseChangeR f M S s.1 x) := by
  rw [termBaseChangeR, DirectSum.toModule_lof, LinearMap.comp_apply]

/-- `termBaseChangeR` commutes with the Čech differentials:
`termBaseChangeR (p + 1) (d^p z) = d^p (termBaseChangeR p z)`. -/
theorem termBaseChangeR_comm_d (p : ℕ) (z : cechTerm f M p) :
    termBaseChangeR f M S (p + 1) (cechD f M p z)
      = cechD (gfun f S) (TensorProduct R S M) p (termBaseChangeR f M S p z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of s x =>
    rw [← DirectSum.lof_eq_of R, cechD_lof, map_sum, termBaseChangeR_lof,
      DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of S,
      cechD_lof (gfun f S) (TensorProduct R S M) p s]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, termBaseChangeR_lof, DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of S]
    congr 1
    have hnat := LinearMap.congr_fun (baseChangeR_comm_cechι f M S
      (Finset.subset_insert i.1 s.1)) x
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] at hnat
    rw [hnat]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The canonical `S`-linear base-change comparison map on degree-`p` terms:
`S ⊗_R C^p(f; M) → C^p(g; N)`, sending `c ⊗ z` to `c • termBaseChangeR p z`. -/
def termBaseChangeS (p : ℕ) :
    TensorProduct R S (cechTerm f M p) →ₗ[S] cechTerm (gfun f S) (TensorProduct R S M) p :=
  (termBaseChangeR f M S p).liftBaseChange S

/-- `termBaseChangeS` sends `c ⊗ z` to `c • termBaseChangeR z`. -/
@[simp]
theorem termBaseChangeS_tmul (p : ℕ) (c : S) (z : cechTerm f M p) :
    termBaseChangeS f M S p (c ⊗ₜ z) = c • termBaseChangeR f M S p z :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The comparison isomorphism `S ⊗_R M_{f|s} ≃ₗ[S] N_{g|s}` at a single subset `s`. -/
def baseChangeSEquiv (s : Finset (Fin r)) :
    TensorProduct R S (cechMod f M s) ≃ₗ[S] cechMod (gfun f S) (TensorProduct R S M) s :=
  LinearEquiv.ofBijective (baseChangeS f M S s) (baseChangeS_bijective f M S s)

/-- `baseChangeSEquiv` acts as `baseChangeS`. -/
@[simp]
theorem baseChangeSEquiv_apply (s : Finset (Fin r)) (x : TensorProduct R S (cechMod f M s)) :
    baseChangeSEquiv f M S s x = baseChangeS f M S s x := rfl

/-- The inverse of `baseChangeSEquiv` sends `baseChangeR x` back to `1 ⊗ x`. -/
theorem baseChangeSEquiv_symm_baseChangeR (s : Finset (Fin r)) (x : cechMod f M s) :
    (baseChangeSEquiv f M S s).symm (baseChangeR f M S s x) = (1 : S) ⊗ₜ x := by
  have hone : baseChangeSEquiv f M S s ((1 : S) ⊗ₜ x) = baseChangeR f M S s x := by
    rw [baseChangeSEquiv_apply, baseChangeS_tmul, one_smul]
  rw [← hone, (baseChangeSEquiv f M S s).symm_apply_apply]

/-- The `R`-linear and `S`-linear inclusions of the summand at `s` into `C^p(g; N)` agree. -/
private theorem lof_R_eq_lof_S (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (y : cechMod (gfun f S) (TensorProduct R S M) s.1) :
    DirectSum.lof R _ (fun t => cechMod (gfun f S) (TensorProduct R S M) t.1) s y
      = DirectSum.lof S _ (fun t => cechMod (gfun f S) (TensorProduct R S M) t.1) s y := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]

/-- `termBaseChangeS` sends `1 ⊗ lof s x` to `lof s (baseChangeR x)`. -/
theorem termBaseChangeS_one_tmul_lof (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (x : cechMod f M s.1) :
    termBaseChangeS f M S p ((1 : S) ⊗ₜ DirectSum.lof R _ (fun t => cechMod f M t.1) s x)
      = DirectSum.lof S _ (fun t => cechMod (gfun f S) (TensorProduct R S M) t.1) s
          (baseChangeR f M S s.1 x) := by
  rw [← lof_R_eq_lof_S, termBaseChangeS_tmul, one_smul, termBaseChangeR_lof]

/-- The degreewise inverse of `termBaseChangeS`: on the summand at `s` it is the inverse of
`baseChangeSEquiv` followed by the base change of the inclusion of that summand. -/
def termBaseChangeSInv (p : ℕ) :
    cechTerm (gfun f S) (TensorProduct R S M) p →ₗ[S] TensorProduct R S (cechTerm f M p) :=
  DirectSum.toModule S {t : Finset (Fin r) // t.card = p} _ (fun s =>
    (LinearMap.baseChange S (DirectSum.lof R {t : Finset (Fin r) // t.card = p}
      (fun t => cechMod f M t.1) s)).comp (baseChangeSEquiv f M S s.1).symm.toLinearMap)

/-- `termBaseChangeSInv` sends the summand `lof s y` to the base change of the inclusion of
that summand, applied to `(baseChangeSEquiv s).symm y`. -/
theorem termBaseChangeSInv_lof (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (y : cechMod (gfun f S) (TensorProduct R S M) s.1) :
    termBaseChangeSInv f M S p
        (DirectSum.lof S _ (fun t => cechMod (gfun f S) (TensorProduct R S M) t.1) s y)
      = LinearMap.baseChange S (DirectSum.lof R _ (fun t => cechMod f M t.1) s)
          ((baseChangeSEquiv f M S s.1).symm y) := by
  rw [termBaseChangeSInv, DirectSum.toModule_lof, LinearMap.comp_apply]
  rfl

/-- `termBaseChangeSInv` is a left inverse of `termBaseChangeS`. -/
theorem termBaseChangeSInv_comp_termBaseChangeS (p : ℕ) :
    (termBaseChangeSInv f M S p).comp (termBaseChangeS f M S p) = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext; intro c
  apply DirectSum.linearMap_ext R
  intro s
  apply LinearMap.ext; intro x
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.comp_apply, LinearMap.id_coe, id_eq]
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul, termBaseChangeS_one_tmul_lof,
    termBaseChangeSInv_lof, baseChangeSEquiv_symm_baseChangeR, LinearMap.baseChange_tmul,
    ← TensorProduct.tmul_eq_smul_one_tmul]

/-- `termBaseChangeSInv` is a right inverse of `termBaseChangeS`. -/
theorem termBaseChangeS_comp_termBaseChangeSInv (p : ℕ) :
    (termBaseChangeS f M S p).comp (termBaseChangeSInv f M S p) = LinearMap.id := by
  apply DirectSum.linearMap_ext S
  intro s
  apply LinearMap.ext; intro y
  simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
  obtain ⟨z, rfl⟩ : ∃ z, baseChangeSEquiv f M S s.1 z = y :=
    ⟨(baseChangeSEquiv f M S s.1).symm y, (baseChangeSEquiv f M S s.1).apply_symm_apply y⟩
  rw [termBaseChangeSInv_lof, (baseChangeSEquiv f M S s.1).symm_apply_apply]
  induction z with
  | tmul c x =>
      rw [LinearMap.baseChange_tmul, baseChangeSEquiv_apply, baseChangeS_tmul,
        TensorProduct.tmul_eq_smul_one_tmul, map_smul, termBaseChangeS_one_tmul_lof, map_smul]
  | add a b ha hb =>
      rw [map_add, map_add, map_add, map_add, ha, hb]

/-- The comparison map `termBaseChangeS f M S p : S ⊗_R C^p(f; M) → C^p(g; N)` is
bijective. -/
theorem termBaseChangeS_bijective (p : ℕ) :
    Function.Bijective (termBaseChangeS f M S p) :=
  (LinearEquiv.ofLinearMap _ _ (termBaseChangeS_comp_termBaseChangeSInv f M S p)
    (termBaseChangeSInv_comp_termBaseChangeS f M S p) : _ ≃ₗ[S] _).bijective

/-- The comparison maps intertwine the base-changed Čech differential with the Čech
differential of `N`:
`termBaseChangeS (p + 1) ∘ (id_S ⊗ d^p_{f; M}) = d^p_{g; N} ∘ termBaseChangeS p`. -/
theorem termBaseChangeS_comm_d (p : ℕ) :
    (termBaseChangeS f M S (p + 1)).comp (LinearMap.baseChange S (cechD f M p))
      = (cechD (gfun f S) (TensorProduct R S M) p).comp (termBaseChangeS f M S p) := by
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul c z =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, termBaseChangeS_tmul, map_smul]
    congr 1
    exact termBaseChangeR_comm_d f M S p z
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The degree-`p` `S`-linear isomorphism `S ⊗_R C^p(f;M) ≃ₗ[S] C^p(g;N)` whose
underlying forward map is `termBaseChangeS f M S p`. -/
def termBaseChangeEquiv (p : ℕ) :
    TensorProduct R S (cechTerm f M p) ≃ₗ[S] cechTerm (gfun f S) (TensorProduct R S M) p :=
  LinearEquiv.ofBijective (termBaseChangeS f M S p) (termBaseChangeS_bijective f M S p)

/-- `termBaseChangeEquiv` acts as `termBaseChangeS`. -/
@[simp]
theorem termBaseChangeEquiv_apply (p : ℕ) (x : TensorProduct R S (cechTerm f M p)) :
    termBaseChangeEquiv f M S p x = termBaseChangeS f M S p x := rfl

/-- The inverse of `termBaseChangeEquiv` is `termBaseChangeSInv`. -/
@[simp]
theorem termBaseChangeEquiv_symm_apply (p : ℕ)
    (y : cechTerm (gfun f S) (TensorProduct R S M) p) :
    (termBaseChangeEquiv f M S p).symm y = termBaseChangeSInv f M S p y := by
  rw [LinearEquiv.symm_apply_eq, termBaseChangeEquiv_apply]
  exact (LinearMap.congr_fun (termBaseChangeS_comp_termBaseChangeSInv f M S p) y).symm

/-! ## The base-changed complex -/

/-- The base change `C^•(f; M) ⊗_R S` of the extended alternating Čech complex along `R → S`:
the cochain complex of `S`-modules with terms `S ⊗_R C^p(f; M)` and differentials
`id_S ⊗ d^p`. -/
def cechComplexBaseChange : CochainComplex (ModuleCat.{max u v w} S) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of S (TensorProduct R S (cechTerm f M p)))
    (fun p => ModuleCat.ofHom (LinearMap.baseChange S (cechD f M p)))
    (fun p => by
      apply ModuleCat.hom_ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        ← LinearMap.baseChange_comp]
      rw [cechD_comp_cechD]
      simp)

/-- The differentials of `cechComplexBaseChange` are `id_S ⊗ d^p`. -/
theorem cechComplexBaseChange_d (p : ℕ) :
    (cechComplexBaseChange f M S).d p (p + 1)
      = ModuleCat.ofHom (LinearMap.baseChange S (cechD f M p)) :=
  CochainComplex.of_d (fun q => ModuleCat.of S (TensorProduct R S (cechTerm f M q)))
    (fun q => ModuleCat.ofHom (LinearMap.baseChange S (cechD f M q))) p

/-- The Čech complex `C^•(g; N)`, lifted to the universe of `cechComplexBaseChange`. -/
abbrev cechComplexBaseChangeTarget : CochainComplex (ModuleCat.{max u v w} S) ℕ :=
  ((ModuleCat.uliftFunctor.{u, max v w} S).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (cechComplex (gfun f S) (TensorProduct R S M))

/-- The degreewise isomorphism `termBaseChangeEquiv`, with its target universe-lifted. -/
def termBaseChangeEquivULift (p : ℕ) :
    TensorProduct R S (cechTerm f M p) ≃ₗ[S]
      ULift.{u} (cechTerm (gfun f S) (TensorProduct R S M) p) :=
  (termBaseChangeEquiv f M S p).trans ULift.moduleEquiv.symm

/-- `termBaseChangeEquivULift` acts as `termBaseChangeS`, followed by the universe lift. -/
@[simp]
theorem termBaseChangeEquivULift_apply (p : ℕ) (x : TensorProduct R S (cechTerm f M p)) :
    termBaseChangeEquivULift f M S p x = ULift.up (termBaseChangeS f M S p x) := rfl

/-- The isomorphism of cochain complexes of `S`-modules `C^•(f; M) ⊗_R S ≅ C^•(g; N)`, with
the target lifted to the universe of the source; its degree-`p` component is
`termBaseChangeEquivULift f M S p`. -/
def cechComplexBaseChangeIso :
    cechComplexBaseChange f M S ≅ cechComplexBaseChangeTarget f M S :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (termBaseChangeEquivULift f M S p).toModuleIso) (by
      intro i j hij
      obtain rfl : j = i + 1 := hij.symm
      have hd2 : (cechComplex (gfun f S) (TensorProduct R S M)).d i (i + 1) =
          ModuleCat.ofHom (cechD (gfun f S) (TensorProduct R S M) i) :=
        CochainComplex.of_d
          (fun p => ModuleCat.of S (cechTerm (gfun f S) (TensorProduct R S M) p))
          (fun p => ModuleCat.ofHom (cechD (gfun f S) (TensorProduct R S M) p)) i
      change (termBaseChangeEquivULift f M S i).toModuleIso.hom ≫
          (cechComplexBaseChangeTarget f M S).d i (i + 1) =
        (cechComplexBaseChange f M S).d i (i + 1) ≫
          (termBaseChangeEquivULift f M S (i + 1)).toModuleIso.hom
      rw [cechComplexBaseChange_d, Functor.mapHomologicalComplex_obj_d, hd2]
      apply ModuleCat.hom_ext
      ext x
      dsimp [termBaseChangeEquivULift, termBaseChangeEquiv, cechComplexBaseChangeTarget]
      change ULift.up
          (cechD (gfun f S) (TensorProduct R S M) i (termBaseChangeS f M S i x)) =
        ULift.up (termBaseChangeS f M S (i + 1)
          (LinearMap.baseChange S (cechD f M i) x))
      congr 1
      exact LinearMap.congr_fun (termBaseChangeS_comm_d f M S i).symm x)

/-- Lowering the universe lift, the degree-`p` component of `cechComplexBaseChangeIso` is
`termBaseChangeS f M S p`. -/
theorem cechComplexBaseChangeIso_hom_f (p : ℕ) :
    ULift.moduleEquiv.toLinearMap.comp ((cechComplexBaseChangeIso f M S).hom.f p).hom
      = termBaseChangeS f M S p := by
  ext x
  rfl

/-- **Stacks 0G6I**.
Let `R → S` be a ring map, `g_i` the image of `f_i` in `S` and `N = S ⊗_R M`. There is an
isomorphism of cochain complexes of `S`-modules `e : C^•(f; M) ⊗_R S ≅ C^•(g; N)` (the
target lifted to the universe of the source) whose degree-`p` component, after lowering
the lift, is `termBaseChangeS f M S p`. -/
@[stacks 0G6I]
theorem exists_cechComplexBaseChange_iso :
    ∃ e : cechComplexBaseChange f M S ≅ cechComplexBaseChangeTarget f M S,
      ∀ p : ℕ, ULift.moduleEquiv.toLinearMap.comp (e.hom.f p).hom =
        termBaseChangeS f M S p :=
  ⟨cechComplexBaseChangeIso f M S, cechComplexBaseChangeIso_hom_f f M S⟩

/-! ## The empty subset -/

/-- The localization submonoid attached to the empty subset is trivial. -/
@[simp]
theorem cechSub_empty : cechSub f (∅ : Finset (Fin r)) = ⊥ := by
  simp [cechSub]

/-- Every element of `cechSub f ∅` is a unit, so `R` is its own localization at it. -/
theorem isLocalization_cechSub_empty : IsLocalization (cechSub f (∅ : Finset (Fin r))) R := by
  rw [cechSub_empty]
  exact IsLocalization.of_le_isUnit bot_le

/-- The identity of `M` exhibits `M` as the localization of `M` at `cechSub f ∅`. -/
theorem isLocalizedModule_id_cechSub_empty :
    IsLocalizedModule (cechSub f (∅ : Finset (Fin r))) (LinearMap.id (R := R) (M := M)) :=
  let := isLocalization_cechSub_empty f
  isLocalizedModule_id _ M R

/-- The localization of `M` at the empty subset is canonically `M` itself. -/
def cechModEmptyEquiv : cechMod f M (∅ : Finset (Fin r)) ≃ₗ[R] M :=
  letI := isLocalizedModule_id_cechSub_empty f M
  IsLocalizedModule.iso (cechSub f (∅ : Finset (Fin r))) (LinearMap.id (R := R) (M := M))

/-- `cechModEmptyEquiv` sends `m / 1` to `m`. -/
@[simp]
theorem cechModEmptyEquiv_mk (m : M) :
    cechModEmptyEquiv f M (LocalizedModule.mkLinearMap (cechSub f (∅ : Finset (Fin r))) M m)
      = m :=
  let := isLocalizedModule_id_cechSub_empty f M
  IsLocalizedModule.iso_mk_one (cechSub f (∅ : Finset (Fin r))) (LinearMap.id (R := R) (M := M)) m

/-- The inverse of `cechModEmptyEquiv` sends `m` to `m / 1`. -/
@[simp]
theorem cechModEmptyEquiv_symm_apply (m : M) :
    (cechModEmptyEquiv f M).symm m
      = LocalizedModule.mkLinearMap (cechSub f (∅ : Finset (Fin r))) M m :=
  let := isLocalizedModule_id_cechSub_empty f M
  IsLocalizedModule.iso_symm_apply (cechSub f (∅ : Finset (Fin r)))
    (LinearMap.id (R := R) (M := M)) m

end

end Stacks.CechBaseChange
