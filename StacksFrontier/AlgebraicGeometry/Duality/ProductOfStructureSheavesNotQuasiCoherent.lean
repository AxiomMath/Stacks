module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# A countable product of structure sheaves which is not quasi-coherent

Let `R` be a commutative ring, `Y = Spec R` and `t ∈ R`. The countable product
`∏_{n ≥ 0} 𝒪_Y` — the product taken in the category of sheaves of `𝒪_Y`-modules — is *not*
quasi-coherent as soon as no equation `t^j = t^{j+1} b` holds in `R`; for instance it is not
quasi-coherent on `Spec ℤ`, with `t = 2`. Conversely, if every `t ∈ R` satisfies such an equation
— for instance if `R` is a field — the product is quasi-coherent.

This is the obstruction of [Stacks, Tag 0GEU], whose full statement is
`Stacks.Duality.AffineLine.uncoheratedTrace_example`. For `Y = Spec R` and `X = 𝐀¹_R`, with
`L = 𝒪_X` and `K = 𝒪_Y`, the target `R𝓗om_{𝒪_Y}(Rf_*L, K)` of the sheafy trace map of
[Stacks, Tag 0B6H] is `∏_{n ≥ 0} 𝒪_Y`, while its source lies in `D_QCoh(𝒪_Y)`. So the trace
map cannot be an isomorphism, and the coherator `DQ_Y` in the statement of
[Stacks, Tag 0A9Q] — `Stacks.Duality.isIso_coherator_map_sheafyTrace_of_qcqs` — cannot be dropped.

The argument is the one of the source, in the equivalent form: a quasi-coherent module on
`Spec R` has localizing sections, so each of its sections over the standard open `D(t)` is a
global section divided by a *single* power of `t`. A section of `∏_{n ≥ 0} 𝒪_Y` over `D(t)` may
have `1/t^n` as its `n`-th coordinate, and no single power of `t` clears all those denominators
at once.

## Main results

* `Stacks.Duality.exists_pow_smul_eq_succ` — the algebraic heart. If a map `rU` out of an
  `R`-module `A` is a localization at the powers of `t`, if the same holds of a map `rP` out of
  `A'`, and if the sections of `rP` surject onto sequences of sections of `rU` compatibly, then
  some `e : A` satisfies `t^j • e = t^{j+1} • b`.
* `Stacks.Duality.bijective_piSections` — sections over an object of a product of sheaves of
  modules are the product of the sections, because evaluation preserves limits.
* `Stacks.Duality.not_isQuasicoherent_piStructureSheaf` — the product `∏_{n ≥ 0} 𝒪_{Spec R}` is
  not quasi-coherent when `t ∈ R` admits no equation `t^j = t^{j+1} b`.
* `Stacks.Duality.not_isQuasicoherent_piStructureSheaf_int` — `∏_{n ≥ 0} 𝒪_{Spec ℤ}` is not
  quasi-coherent.
* `Stacks.Duality.isQuasicoherent_piStructureSheaf` — the converse: the product is quasi-coherent
  when every `t ∈ R` satisfies an equation `t^j = t^{j+1} b`; and
  `Stacks.Duality.isQuasicoherent_piStructureSheaf_iff`, the two together.
* `Stacks.Duality.isQuasicoherent_piStructureSheaf_of_isField` — over a field the product is
  quasi-coherent, so the assertion of [Stacks, Tag 0GEU] fails for `R` a field.

## Implementation notes

*Where the rest of the example is.* The identification of `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)` with
`∏_{n ≥ 0} 𝒪_Y` for the affine line, the quasi-coherence of the other side and the assembled
statement are in `StacksFrontier/AlgebraicGeometry/Duality/AffineLineUncoheratedTrace.lean`.

*Why the condition on `t`.* Tag 0GEU writes `Y = Spec(R)` for an unspecified `R`, but the
assertion is false for some rings: on `Spec k` for a field `k` the space is a point and every
sheaf of modules is quasi-coherent. `Stacks.Duality.isQuasicoherent_piStructureSheaf_iff` says
exactly for which rings it holds: those with an element `t` admitting no equation
`t^j = t^{j+1} b`, such as `ℤ` with `t = 2`.

*Quasi-coherence is used through `AlgebraicGeometry.IsLocalizing`.* Mathlib's
`CategoryTheory.SheafOfModules.IsQuasicoherent` is the existence of local presentations;
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ` and
`AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing` turn it into the statement that sections
localize, which is the form the argument refutes.

## References

* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Duality

universe u

/-! ### The algebraic obstruction -/

/-- **No single power of `t` clears infinitely many growing denominators.** Let `t` be an element
of a commutative ring `R`, let `rU : A ⟶ B` be a localization of `R`-modules at the powers of
`t`, and let `rP : A' ⟶ B'` be another. Suppose given `R`-linear coordinate maps `qT n` and
`qD n` compatible with `rU` and `rP`, and suppose every sequence of elements of `B` is the
sequence of coordinates of an element of `B'`. Then for every `e : A` there are `j` and `b` with
`t^j • e = t^{j+1} • b`.

Indeed `B'` contains an element whose `n`-th coordinate is `e/t^n`; clearing its denominators
with one power `t^k` forces, in the coordinate `k + 1`, the equation `t^k • e = t^{k+1} • b` up
to `t`-torsion, which is the statement after absorbing the torsion exponent into `j`. -/
public theorem exists_pow_smul_eq_succ
    {R : Type*} [CommRing R] (t : R)
    {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    [Module R A] [Module R B] [Module R A'] [Module R B']
    {rU : A →ₗ[R] B} (hU : IsLocalizedModule (Submonoid.powers t) rU)
    {rP : A' →ₗ[R] B'} (hP : IsLocalizedModule (Submonoid.powers t) rP)
    (qT : ℕ → A' →ₗ[R] A) (qD : ℕ → B' →ₗ[R] B)
    (hnat : ∀ (n : ℕ) (x : A'), qD n (rP x) = rU (qT n x))
    (hsurj : Function.Surjective (fun (s : B') (n : ℕ) => qD n s))
    (e : A) :
    ∃ (j : ℕ) (b : A), t ^ j • e = t ^ (j + 1) • b := by
  have := hU
  have := hP
  have hmem : ∀ n : ℕ, t ^ n ∈ Submonoid.powers t := fun n => ⟨n, rfl⟩
  have hσ : ∀ n : ℕ, (t ^ n) • IsLocalizedModule.mk' rU e ⟨t ^ n, hmem n⟩ = rU e := fun n =>
    IsLocalizedModule.mk'_cancel' rU e ⟨t ^ n, hmem n⟩
  obtain ⟨s, hs⟩ := hsurj (fun n => IsLocalizedModule.mk' rU e ⟨t ^ n, hmem n⟩)
  obtain ⟨⟨a, c⟩, hac⟩ := IsLocalizedModule.surj (Submonoid.powers t) rP s
  obtain ⟨k, hk⟩ := c.2
  have hac' : (t ^ k) • s = rP a := by
    rw [show t ^ k = (c : R) from hk]; exact hac
  have h1 : (t ^ k) • qD (k + 1) s = rU (qT (k + 1) a) := by
    rw [← map_smul, hac', hnat]
  have h2 : qD (k + 1) s = IsLocalizedModule.mk' rU e ⟨t ^ (k + 1), hmem (k + 1)⟩ :=
    congrFun hs (k + 1)
  rw [h2] at h1
  have h3 : rU ((t ^ k) • e) = rU ((t ^ (k + 1)) • qT (k + 1) a) := by
    rw [map_smul, map_smul, ← h1, ← hσ (k + 1), smul_smul, smul_smul, mul_comm]
  obtain ⟨c', hc'⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers t) rU).mp h3
  obtain ⟨m, hm⟩ := c'.2
  refine ⟨m + k, qT (k + 1) a, ?_⟩
  have hc'' : (t ^ m) • ((t ^ k) • e) = (t ^ m) • ((t ^ (k + 1)) • qT (k + 1) a) := by
    rw [show t ^ m = (c' : R) from hm]; exact hc'
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hc''
  exact hc''

/-! ### Sections of a product of sheaves of modules -/

/-- **Sections of a product are the product of the sections.** For a family `f` of sheaves of
`R`-modules on a site and an object `U`, taking the coordinates of a section over `U` of the
product is a bijection onto the sequences of sections over `U` of the factors. This is
`CategoryTheory.SheafOfModules.evaluationPreservesLimitsOfSize`: evaluation at `U` preserves
limits, so the comparison map to the product is invertible. -/
public theorem bijective_piSections {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {ι : Type} (f : ι → SheafOfModules.{u} R) (U : Cᵒᵖ) :
    Function.Bijective
      (fun (s : ((SheafOfModules.evaluation R U).obj (∏ᶜ f) : Type u)) (i : ι) =>
        ((SheafOfModules.evaluation R U).map (Pi.π f i) s :
          ((SheafOfModules.evaluation R U).obj (f i) : Type u))) := by
  have key :
      (fun (s : ((SheafOfModules.evaluation R U).obj (∏ᶜ f) : Type u)) (i : ι) =>
        ((SheafOfModules.evaluation R U).map (Pi.π f i) s :
          ((SheafOfModules.evaluation R U).obj (f i) : Type u))) =
      fun s => (piComparison (SheafOfModules.evaluation R U) f ≫
        (ModuleCat.piIsoPi (fun i => (SheafOfModules.evaluation R U).obj (f i))).hom) s := by
    funext s i
    have h2 : piComparison (SheafOfModules.evaluation R U) f ≫ Pi.π _ i =
        (SheafOfModules.evaluation R U).map (Pi.π f i) := by simp [piComparison]
    have h1 := congrArg (fun φ => ModuleCat.Hom.hom φ
        ((ModuleCat.Hom.hom (piComparison (SheafOfModules.evaluation R U) f)) s))
      (ModuleCat.piIsoPi_hom_ker_subtype
        (fun i => (SheafOfModules.evaluation R U).obj (f i)) i)
    rw [ModuleCat.comp_apply, ← h2, ModuleCat.comp_apply]
    exact h1.symm
  rw [key]
  exact ConcreteCategory.bijective_of_isIso _

/-! ### The product of structure sheaves is not quasi-coherent -/

/-- The global sections of the structure sheaf of `Spec R`, as a module over `R` by restriction
of scalars along `Γ(Spec R, ⊤) ≅ R`, have `r • x` equal to the product of `r` and `x` read in
`R` along that isomorphism. -/
private theorem ΓSpecIso_hom_smul (R : CommRingCat.{u}) (r : R)
    (x : ((modulesSpecToSheaf.obj (SheafOfModules.unit (Spec R).ringCatSheaf)).obj.obj (op ⊤) :
      Type u)) :
    (Scheme.ΓSpecIso R).hom (r • x) = r * (Scheme.ΓSpecIso R).hom x := by
  have h : (Scheme.ΓSpecIso R).hom (r • x) =
      (Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv r) * (Scheme.ΓSpecIso R).hom x :=
    map_mul (Scheme.ΓSpecIso R).hom.hom _ _
  rw [h, Iso.inv_hom_id_apply]

/-- The `n`-th coordinate of a section over `U` of the product `∏_{n ≥ 0} 𝒪_{Spec R}`. -/
private def piCoord (R : CommRingCat.{u}) (U : Opens (Spec R)) (n : ℕ) :
    (modulesSpecToSheaf.obj
      (∏ᶜ (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf))).obj.obj (op U) →ₗ[R]
    (modulesSpecToSheaf.obj (SheafOfModules.unit (Spec R).ringCatSheaf)).obj.obj (op U) :=
  ((modulesSpecToSheaf.map
    (Pi.π (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf) n)).hom.app (op U)).hom

/-- The coordinates `piCoord` commute with restriction from `⊤` to `D(t)`. -/
private theorem piCoord_naturality (R : CommRingCat.{u}) (t : R) (n : ℕ) (x) :
    piCoord R (PrimeSpectrum.basicOpen t) n
      ((modulesSpecToSheaf.obj
        (∏ᶜ (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf))).obj.map
        (PrimeSpectrum.basicOpen t).leTop.op x) =
    (modulesSpecToSheaf.obj (SheafOfModules.unit (Spec R).ringCatSheaf)).obj.map
      (PrimeSpectrum.basicOpen t).leTop.op (piCoord R ⊤ n x) := by
  have := (modulesSpecToSheaf.map
    (Pi.π (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf) n)).hom.naturality
      (PrimeSpectrum.basicOpen t).leTop.op
  exact ConcreteCategory.congr_hom this x

/-- **A countable product of copies of the structure sheaf is not quasi-coherent.** Let `R` be a
commutative ring and `t ∈ R` an element for which no equation `t^j = t^{j+1} b` holds. Then the
product `∏_{n ≥ 0} 𝒪_{Spec R}`, taken in the category of sheaves of `𝒪_{Spec R}`-modules, is not
quasi-coherent.

Were it quasi-coherent its sections would localize, so the section over `D(t)` whose `n`-th
coordinate is `1/t^n` would be a global section divided by one power of `t`; reading off the
coordinate `k + 1` of such a presentation produces the forbidden equation. -/
public theorem not_isQuasicoherent_piStructureSheaf (R : CommRingCat.{u}) (t : R)
    (ht : ∀ (j : ℕ) (b : R), t ^ j * (1 - t * b) ≠ 0) :
    ¬ (∏ᶜ (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent := by
  intro hqc
  obtain ⟨j, b, hjb⟩ := exists_pow_smul_eq_succ t
    ((isIso_fromTildeΓ_iff_isLocalizing
      (SheafOfModules.unit (Spec R).ringCatSheaf)).mp inferInstance t)
    ((isIso_fromTildeΓ_iff_isLocalizing
        (∏ᶜ (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf))).mp
      ((isQuasicoherent_iff_isIso_fromTildeΓ _).mp hqc) t)
    (piCoord R ⊤) (piCoord R (PrimeSpectrum.basicOpen t)) (piCoord_naturality R t)
    (bijective_piSections _ (op (PrimeSpectrum.basicOpen t))).surjective
    (1 : Γ(Spec R, ⊤))
  have h : t ^ j * (Scheme.ΓSpecIso R).hom (1 : Γ(Spec R, ⊤)) =
      t ^ (j + 1) * (Scheme.ΓSpecIso R).hom b :=
    (ΓSpecIso_hom_smul R (t ^ j) _).symm.trans
      ((congrArg (fun x => (Scheme.ΓSpecIso R).hom x) hjb).trans
        (ΓSpecIso_hom_smul R (t ^ (j + 1)) b))
  rw [map_one, mul_one] at h
  refine ht j ((Scheme.ΓSpecIso R).hom b) ?_
  rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, ← h]
  ring

/-! ### The converse: when the product is quasi-coherent -/

/-- **A product of localizations at a strongly π-regular element is a localization.** Let `t` be
an element of a commutative ring `R` satisfying `t^j = t^{j+1} b` for some `j` and `b`, and let
`r_k : A_k ⟶ B_k` be a family of localizations of `R`-modules at the powers of `t`. Then the
product map `∏_k A_k ⟶ ∏_k B_k` is again a localization at the powers of `t`.

On each `B_k` the element `t` acts invertibly, so `t^j = t^{j+1} b` forces `t b = 1` there; hence
every element of `B_k` is an image `r_k(a)` with no denominator, and the `t`-power torsion of every
`A_k` is killed by the single power `t^j`. Both bounds are uniform in `k`. -/
theorem isLocalizedModule_pi_of_pow_eq {R : Type*} [CommRing R] (t : R) {j : ℕ} {b : R}
    (htb : t ^ j = t ^ (j + 1) * b) {ι : Type*} {A B : ι → Type*}
    [∀ k, AddCommGroup (A k)] [∀ k, AddCommGroup (B k)] [∀ k, Module R (A k)]
    [∀ k, Module R (B k)] (r : ∀ k, A k →ₗ[R] B k)
    (hr : ∀ k, IsLocalizedModule (Submonoid.powers t) (r k)) :
    IsLocalizedModule (Submonoid.powers t) (LinearMap.pi fun k ↦ r k ∘ₗ LinearMap.proj k) := by
  have hunit : ∀ (k : ι) (s : Submonoid.powers t),
      Function.Bijective (fun z : B k ↦ (s : R) • z) := fun k s ↦
    (Module.End.isUnit_iff _).1 ((hr k).map_units s)
  have hmem : ∀ n : ℕ, t ^ n ∈ Submonoid.powers t := fun n ↦ ⟨n, rfl⟩
  have hbt : ∀ (k : ι) (z : B k), (t * b) • z = z := by
    intro k z
    obtain ⟨z', rfl⟩ := (hunit k ⟨t ^ j, hmem j⟩).2 z
    show (t * b) • (t ^ j • z') = t ^ j • z'
    rw [smul_smul, show t * b * t ^ j = t ^ (j + 1) * b by ring, ← htb]
  have hkill : ∀ (m : ℕ) (k : ι) (w : A k), t ^ m • w = 0 → t ^ j • w = 0 := by
    have hpow : ∀ n : ℕ, t ^ j = t ^ (j + n) * b ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ih]
        calc t ^ (j + n) * b ^ n = t ^ n * t ^ j * b ^ n := by ring
          _ = t ^ n * (t ^ (j + 1) * b) * b ^ n := by rw [← htb]
          _ = t ^ (j + (n + 1)) * b ^ (n + 1) := by ring
    intro m k w hw
    rw [hpow m, show t ^ (j + m) * b ^ m = (b ^ m * t ^ j) * t ^ m by ring, ← smul_smul, hw,
      smul_zero]
  have hbtm : ∀ (k : ι) (m : ℕ) (z : B k), (t * b) ^ m • z = z := by
    intro k m z
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← smul_smul, hbt, ih]
  refine ⟨fun s ↦ ?_, fun y ↦ ?_, fun {x₁ x₂} h ↦ ?_⟩
  · refine (Module.End.isUnit_iff _).2 ⟨fun y y' h ↦ funext fun k ↦ ?_, fun y ↦ ?_⟩
    · exact (hunit k s).1 (congrFun h k)
    · choose z hz using fun k ↦ (hunit k s).2 (y k)
      exact ⟨z, funext hz⟩
  · have hy : ∀ k, ∃ a : A k, r k a = y k := by
      intro k
      obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := (hr k).surj (y k)
      refine ⟨b ^ m • a, ?_⟩
      change t ^ m • y k = r k a at ha
      rw [map_smul, ← ha, smul_smul, ← mul_pow, mul_comm b t, hbtm]
    choose a ha using hy
    exact ⟨⟨a, 1⟩, funext fun k ↦ by simp [ha k]⟩
  · refine ⟨⟨t ^ j, hmem j⟩, funext fun k ↦ ?_⟩
    obtain ⟨⟨_, m, rfl⟩, hc⟩ := (hr k).exists_of_eq (congrFun h k)
    show t ^ j • x₁ k = t ^ j • x₂ k
    rw [← sub_eq_zero, ← smul_sub]
    refine hkill m k _ ?_
    rw [smul_sub, sub_eq_zero]
    exact hc

/-- **A countable product of copies of a localization, read through coordinates, is a
localization.** This is `Stacks.Duality.isLocalizedModule_pi_of_pow_eq` transported along
coordinate maps: if `rU` is a localization at the powers of `t`, with `t^j = t^{j+1} b`, and the
coordinates `qT n`, `qD n` identify `rP` with the product of countably many copies of `rU`, then
`rP` is a localization at the powers of `t`. It is the converse counterpart of
`Stacks.Duality.exists_pow_smul_eq_succ`, with the same interface. -/
public theorem isLocalizedModule_of_coordinates
    {R : Type*} [CommRing R] (t : R) {j : ℕ} {b : R} (htb : t ^ j = t ^ (j + 1) * b)
    {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    [Module R A] [Module R B] [Module R A'] [Module R B']
    {rU : A →ₗ[R] B} (hU : IsLocalizedModule (Submonoid.powers t) rU) (rP : A' →ₗ[R] B')
    (qT : ℕ → A' →ₗ[R] A) (qD : ℕ → B' →ₗ[R] B)
    (hnat : ∀ (n : ℕ) (x : A'), qD n (rP x) = rU (qT n x))
    (hT : Function.Bijective (fun (x : A') (n : ℕ) => qT n x))
    (hD : Function.Bijective (fun (y : B') (n : ℕ) => qD n y)) :
    IsLocalizedModule (Submonoid.powers t) rP := by
  have hsq : LinearMap.pi qD ∘ₗ rP =
      (LinearMap.pi fun n : ℕ ↦ rU ∘ₗ LinearMap.proj n) ∘ₗ LinearMap.pi qT :=
    LinearMap.ext fun x ↦ funext fun n ↦ hnat n x
  have h1 : IsLocalizedModule (Submonoid.powers t)
      ((LinearMap.pi fun n : ℕ ↦ rU ∘ₗ LinearMap.proj n) ∘ₗ LinearMap.pi qT) :=
    (IsLocalizedModule.comp_iff_of_bijective_right _ _ hT).2
      (isLocalizedModule_pi_of_pow_eq t htb (fun _ ↦ rU) fun _ ↦ hU)
  rw [← hsq] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_left _ _ hD).1 h1

/-- **The converse of `Stacks.Duality.not_isQuasicoherent_piStructureSheaf`.** If every element
`t` of `R` satisfies an equation `t^j = t^{j+1} b`, then the countable product
`∏_{n ≥ 0} 𝒪_{Spec R}` is quasi-coherent: its sections over each standard open `D(t)` are the
product of the sections of `𝒪`, and a product of localizations at such a `t` is a
localization (`Stacks.Duality.isLocalizedModule_pi_of_pow_eq`). -/
public theorem isQuasicoherent_piStructureSheaf (R : CommRingCat.{u})
    (h : ∀ t : R, ∃ (j : ℕ) (b : R), t ^ j = t ^ (j + 1) * b) :
    (∏ᶜ (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent := by
  refine (isQuasicoherent_iff_isIso_fromTildeΓ _).2
    ((isIso_fromTildeΓ_iff_isLocalizing _).2 fun t ↦ ?_)
  obtain ⟨j, b, hjb⟩ := h t
  exact isLocalizedModule_of_coordinates t hjb
    ((isIso_fromTildeΓ_iff_isLocalizing
      (SheafOfModules.unit (Spec R).ringCatSheaf)).mp inferInstance t) _
    (piCoord R ⊤) (piCoord R (PrimeSpectrum.basicOpen t)) (piCoord_naturality R t)
    (bijective_piSections _ (op ⊤))
    (bijective_piSections _ (op (PrimeSpectrum.basicOpen t)))

/-- **When the countable product of structure sheaves is quasi-coherent.** The product
`∏_{n ≥ 0} 𝒪_{Spec R}` is quasi-coherent exactly when every element `t` of `R` satisfies an
equation `t^j = t^{j+1} b`. -/
public theorem isQuasicoherent_piStructureSheaf_iff (R : CommRingCat.{u}) :
    (∏ᶜ (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent ↔
      ∀ t : R, ∃ (j : ℕ) (b : R), t ^ j = t ^ (j + 1) * b := by
  refine ⟨fun hqc t ↦ ?_, isQuasicoherent_piStructureSheaf R⟩
  by_contra hne
  refine not_isQuasicoherent_piStructureSheaf R t (fun j b hjb ↦ hne ⟨j, b, ?_⟩) hqc
  linear_combination hjb

/-- **Over a field the countable product of structure sheaves is quasi-coherent.** Every element
`t` of a field satisfies `t^j = t^{j+1} b`: take `j = 1` when `t = 0` and `j = 0`, `b = t⁻¹`
otherwise. So the assertion of [Stacks, Tag 0GEU] that `∏_{n ≥ 0} 𝒪_Y` is not quasi-coherent
fails for `Y = Spec k`. -/
public theorem isQuasicoherent_piStructureSheaf_of_isField (R : CommRingCat.{u})
    (hR : IsField R) :
    (∏ᶜ (fun _ : ℕ => SheafOfModules.unit (Spec R).ringCatSheaf)).IsQuasicoherent := by
  let := hR.toField
  refine isQuasicoherent_piStructureSheaf R fun t ↦ ?_
  by_cases ht : t = 0
  · exact ⟨1, 0, by simp [ht]⟩
  · exact ⟨0, t⁻¹, by simp [ht]⟩

/-- **The countable product of structure sheaves of `Spec ℤ`.** The countable product
`∏_{n ≥ 0} 𝒪_{Spec ℤ}` of copies of the structure sheaf of `Spec ℤ` is not quasi-coherent.

This is the object the source produces as the target of the sheafy trace map of
[Stacks, Tag 0B6H] for the affine line over the base, with the structure sheaves as both inputs.
Its failure to be quasi-coherent is what shows that the statement of [Stacks, Tag 0A9Q] —
`Stacks.Duality.isIso_coherator_map_sheafyTrace_of_qcqs` — is false without the coherator
`DQ_Y`: the source of the trace map has quasi-coherent cohomology and its target does not, so the
trace map itself is not an isomorphism.

The base is `Spec ℤ` rather than an arbitrary `Spec R`: the example needs `R` to contain a
non-unit non-zerodivisor, and fails for a field, over which `Spec R` is a point and every sheaf
of modules is quasi-coherent. For `R = ℤ` and `t = 2` the obstruction is that no integer
sequence `(aₙ)` and exponent `k` satisfy `2^k = 2^{n} aₙ` for every `n`. -/
public theorem not_isQuasicoherent_piStructureSheaf_int :
    ¬ (∏ᶜ (fun _ : ℕ =>
      SheafOfModules.unit (Spec (CommRingCat.of ℤ)).ringCatSheaf)).IsQuasicoherent :=
  not_isQuasicoherent_piStructureSheaf (CommRingCat.of ℤ) 2 fun j b =>
    mul_ne_zero (pow_ne_zero j two_ne_zero) (show (1 : ℤ) - 2 * b ≠ 0 by omega)

end Stacks.Duality

end
