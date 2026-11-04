module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.Lifting.Algebra
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing

/-!
# From smooth algebraizations of finite type factorizations to solutions in the henselization

Let `Λ` be a Noetherian ring, `𝔪 ⊂ Λ` a maximal ideal and `R` a `Λ`-algebra. Suppose every
factorization `Λ → C → R` with `C` of finite type over `Λ` is dominated by a finite type
`Λ`-algebra `A` with a maximal ideal `𝔪_A` over `𝔪`, `κ(𝔪) = κ(𝔪_A)`, `Λ → A` smooth at `𝔪_A`, and
a `Λ`-algebra map `C → A`. This is the datum which Stacks Example 98.12.8 (Tag 07XI) reads off
the conclusion of Lemma 98.12.7 (Tag 07XH) for its categories `𝒳 = 𝒮_F`. Then every finite system
of polynomial equations over `Λ` with a solution in `R` has a solution in every henselian local
`Λ`-algebra whose maximal ideal contracts to `𝔪`; in particular in the henselization of `Λ_𝔪`.

The module `StacksFrontier.Deformation.Artin.Versality.GRingNecessity` assembles the Example
from the results below and its geometric half, and imports this file publicly, so its importers
(such as `StacksFrontier.Deformation.Artin.Versality.GRingExample`) see them.

## Main definitions

* `Deformation.Artin.AlgebraizesFiniteTypeFactorizations Λ 𝔪 R`: the datum above, with the
  smoothness already deduced from condition (4) of Stacks 02HT as the source does.

## Main results

* `Deformation.Artin.exists_algHom_of_isSmoothAt`: a finite type `Λ`-algebra `A` with a maximal
  ideal `𝔪_A` over `𝔪` such that `κ(𝔪) = κ(𝔪_A)` and `Λ → A` is smooth at `𝔪_A` maps to every
  henselian local `Λ`-algebra whose maximal ideal contracts to `𝔪`.
* `Deformation.Artin.exists_solution_of_algebraizesFiniteTypeFactorizations`: the datum makes
  every finite polynomial system over `Λ` with a solution in `R` solvable in every henselian local
  `Λ`-algebra whose maximal ideal contracts to `𝔪`.
* `Deformation.Artin.exists_ringHom_of_algebraizesFiniteTypeFactorizations`: the datum carries a
  single factorization `Λ → C → R` with `C` of finite type to a map `C → H` into every such
  `Λ`-algebra `H`.
* `Deformation.Artin.exists_solution_henselization_of_algebraizesFiniteTypeFactorizations`: the
  above with `R = Λ_𝔪^∧` and the target the henselization of `Λ_𝔪`.
* `Deformation.Artin.algebraizesFiniteTypeFactorizations_self`: the datum is satisfiable.

## Implementation notes

The source slices `A` to make `Λ → A` étale at `𝔪_A`. That step is avoided: smoothness at `𝔪_A`
of a finite type algebra over a Noetherian ring gives some `g ∉ 𝔪_A` with `A_g` smooth over `Λ`,
the residue field map out of `A` inverts `g`, and Stacks 0H74 lifts the resulting `Λ`-algebra map
`A_g → H/𝔪_H` to `A_g → H` along the henselian pair `(H, 𝔪_H)`.

`κ(𝔪) = κ(𝔪_A)` is stated as bijectivity of `Ideal.ResidueField.map`; since both ideals are
maximal this is converted internally to surjectivity of `Λ ⧸ 𝔪 → A ⧸ 𝔪_A`.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
* [Stacks Project, Tag 0H74](https://stacks.math.columbia.edu/tag/0H74)
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Deformation.Artin

universe u

/-- The square comparing the map of quotients by two corresponding ideals with the map of
residue fields they induce. -/
private theorem algebraMap_quotientMap_residueField
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) [I.IsPrime]
    (J : Ideal S) [J.IsPrime] (f : R →+* S) (hf : I = J.comap f) (x : R ⧸ I) :
    algebraMap (S ⧸ J) J.ResidueField (Ideal.quotientMap J f (le_of_eq hf) x) =
      Ideal.ResidueField.map I J f hf (algebraMap (R ⧸ I) I.ResidueField x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap]

/-- For maximal ideals, an isomorphism of residue fields is the same as surjectivity of the
induced map of residue rings. -/
private theorem surjective_quotientMap_of_bijective_residueFieldMap
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) [I.IsMaximal]
    (J : Ideal S) [J.IsMaximal] (f : R →+* S) (hf : I = J.comap f)
    (hbij : Function.Bijective (Ideal.ResidueField.map I J f hf)) :
    Function.Surjective (Ideal.quotientMap J f (le_of_eq hf)) := by
  intro y
  obtain ⟨z, hz⟩ := hbij.2 (algebraMap (S ⧸ J) J.ResidueField y)
  obtain ⟨x, hx⟩ := (Ideal.bijective_algebraMap_quotient_residueField I).2 z
  exact ⟨x, (Ideal.bijective_algebraMap_quotient_residueField J).1
    (by rw [algebraMap_quotientMap_residueField I J f hf, hx, hz])⟩

/-- An algebra with a maximal ideal over `𝔪` whose residue field is that of `𝔪` maps to the
residue field of any local algebra whose maximal ideal contracts to `𝔪`, by an algebra map
whose kernel is that maximal ideal. -/
private theorem exists_algHom_residueQuotient
    {Λ A H : Type*} [CommRing Λ] [CommRing A] [CommRing H] [IsLocalRing H]
    [Algebra Λ A] [Algebra Λ H] (m : Ideal Λ) (mA : Ideal A)
    (hmA : m = mA.comap (algebraMap Λ A))
    (hsurj : Function.Surjective (Ideal.quotientMap mA (algebraMap Λ A) (le_of_eq hmA)))
    (hH : m = (maximalIdeal H).comap (algebraMap Λ H)) :
    ∃ τ : A →ₐ[Λ] H ⧸ maximalIdeal H, ∀ a : A, τ a = 0 ↔ a ∈ mA := by
  set q : (Λ ⧸ m) ≃+* (A ⧸ mA) :=
    RingEquiv.ofBijective _ ⟨Ideal.quotientMap_injective' (le_of_eq hmA.symm), hsurj⟩ with hqdef
  set π : (Λ ⧸ m) →+* H ⧸ maximalIdeal H :=
    Ideal.quotientMap (maximalIdeal H) (algebraMap Λ H) (le_of_eq hH) with hπdef
  have hπinj : Function.Injective π := Ideal.quotientMap_injective' (le_of_eq hH.symm)
  refine ⟨{ ((π.comp q.symm.toRingHom).comp (Ideal.Quotient.mk mA)) with
    commutes' := fun c => ?_ }, fun a => ?_⟩
  · change π (q.symm (Ideal.Quotient.mk mA (algebraMap Λ A c))) = _
    have hq : q (Ideal.Quotient.mk m c) = Ideal.Quotient.mk mA (algebraMap Λ A c) := by
      rw [hqdef]
      exact Ideal.quotientMap_mk (J := m) (I := mA) (f := algebraMap Λ A)
        (H := le_of_eq hmA) (x := c)
    rw [← hq, q.symm_apply_apply, hπdef]
    rfl
  · change π (q.symm (Ideal.Quotient.mk mA a)) = 0 ↔ a ∈ mA
    rw [map_eq_zero_iff π hπinj, map_eq_zero_iff q.symm q.symm.injective,
      Ideal.Quotient.eq_zero_iff_mem]

/-- An algebra map to a residue field with kernel `𝔪_A` extends over the localization away
from any `g ∉ 𝔪_A`. -/
private theorem exists_algHom_localizationAway_of_notMem
    {Λ A H : Type*} [CommRing Λ] [CommRing A] [CommRing H] [IsLocalRing H]
    [Algebra Λ A] [Algebra Λ H] {mA : Ideal A}
    (τ : A →ₐ[Λ] H ⧸ maximalIdeal H) (hτ : ∀ a : A, τ a = 0 ↔ a ∈ mA)
    (g : A) (hg : g ∉ mA) :
    ∃ σ : Localization.Away g →ₐ[Λ] H ⧸ maximalIdeal H,
      ∀ a : A, σ (algebraMap A (Localization.Away g) a) = τ a := by
  let : Field (H ⧸ maximalIdeal H) := Ideal.Quotient.field _
  have hunits : ∀ y : Submonoid.powers g, IsUnit (τ.toRingHom (y : A)) := by
    rintro ⟨y, k, rfl⟩
    have hne : τ g ≠ 0 := fun h => hg ((hτ g).mp h)
    simpa using (isUnit_iff_ne_zero.mpr hne).pow k
  refine ⟨{ IsLocalization.lift (S := Localization.Away g) hunits with
    commutes' := fun c => ?_ }, fun a => IsLocalization.lift_eq hunits a⟩
  change IsLocalization.lift hunits (algebraMap Λ (Localization.Away g) c) = _
  rw [IsScalarTower.algebraMap_apply Λ A (Localization.Away g), IsLocalization.lift_eq]
  exact τ.commutes c

/-- **A finite type `Λ`-algebra smooth at a maximal ideal over `𝔪` with the same residue field
maps to every henselian local `Λ`-algebra whose maximal ideal contracts to `𝔪`.** Smoothness at
`𝔪_A` gives a `g ∉ 𝔪_A` with `A_g` smooth over `Λ`; the residue field condition gives a
`Λ`-algebra map `A_g → H/𝔪_H`; and Stacks 0H74 lifts that along the henselian pair
`(H, 𝔪_H)`. -/
public theorem exists_algHom_of_isSmoothAt {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {m : Ideal Λ} [m.IsMaximal] {A : Type u} [CommRing A] [Algebra Λ A]
    (hftA : Algebra.FiniteType Λ A) (mA : Ideal A) [mA.IsMaximal]
    (hmA : m = mA.comap (algebraMap Λ A))
    (hres : Function.Bijective (Ideal.ResidueField.map m mA (algebraMap Λ A) hmA))
    (hsm : Algebra.IsSmoothAt Λ mA)
    {H : Type u} [CommRing H] [HenselianLocalRing H] [Algebra Λ H]
    (hH : m = (maximalIdeal H).comap (algebraMap Λ H)) :
    Nonempty (A →ₐ[Λ] H) := by
  have : Algebra.FinitePresentation Λ A := Algebra.FinitePresentation.of_finiteType.mp hftA
  have := hsm
  obtain ⟨g, hg, hgs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth Λ mA
  obtain ⟨τ, hτ⟩ := exists_algHom_residueQuotient m mA hmA
    (surjective_quotientMap_of_bijective_residueFieldMap m mA _ hmA hres) hH
  obtain ⟨σ, -⟩ := exists_algHom_localizationAway_of_notMem τ hτ g hg
  obtain ⟨F, -⟩ := exists_lift_of_smooth_of_henselianPair (R := Λ)
    (S := Localization.Away g) (A := H) (maximalIdeal H) (henselianPair_maximalIdeal H) σ
  exact ⟨F.comp (IsScalarTower.toAlgHom Λ A (Localization.Away g))⟩

/-- The datum that the Example reads off the conclusion of Stacks 07XH for the categories
`𝒳 = 𝒮_F` it builds (a conclusion the Example assumes without the G-ring hypothesis of 07XH):
every factorization `Λ → C → R` with `C` of finite type over `Λ` is dominated by a finite type
`Λ`-algebra `A` carrying a maximal ideal `𝔪_A` over `𝔪` with `κ(𝔪) = κ(𝔪_A)`, smooth over `Λ`
at `𝔪_A`.

The source's items are `κ(𝔪) = κ(𝔪_A)`, condition (4) of Stacks 02HT, and the existence of a
`Λ`-algebra map `C → A`; the second is recorded here as the smoothness at `𝔪_A` which 02HT
deduces from it, exactly as the source does in its next sentence. -/
public def AlgebraizesFiniteTypeFactorizations (Λ : Type u) [CommRing Λ] (m : Ideal Λ)
    [m.IsMaximal] (R : Type u) [CommRing R] [Algebra Λ R] : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra Λ C], Algebra.FiniteType Λ C → (C →ₐ[Λ] R) →
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra Λ A), Algebra.FiniteType Λ A ∧
      ∃ (mA : Ideal A) (_ : mA.IsMaximal) (hmA : m = mA.comap (algebraMap Λ A)),
        Function.Bijective (Ideal.ResidueField.map m mA (algebraMap Λ A) hmA) ∧
        Algebra.IsSmoothAt Λ mA ∧ Nonempty (C →ₐ[Λ] A)

/-- The carried datum is satisfiable: it holds for `R = Λ`, with `A = Λ` and `𝔪_A = 𝔪`. The
residue field map is then the identity and `Λ` is smooth over itself at `𝔪` because
`Localization.AtPrime 𝔪` is a localization of `Λ`. -/
public theorem algebraizesFiniteTypeFactorizations_self (Λ : Type u) [CommRing Λ]
    (m : Ideal Λ) [m.IsMaximal] : AlgebraizesFiniteTypeFactorizations Λ m Λ := by
  intro C _ _ _ φ
  have hid : (algebraMap Λ Λ) = RingHom.id Λ := rfl
  have hmA : m = m.comap (algebraMap Λ Λ) := by rw [hid, Ideal.comap_id]
  refine ⟨Λ, inferInstance, inferInstance, inferInstance, m, inferInstance, hmA, ?_, ?_, ⟨φ⟩⟩
  · exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (by rw [hid]; exact RingHom.surjectiveOnStalks_of_surjective fun x => ⟨x, rfl⟩) m m hmA
  · exact Algebra.FormallySmooth.of_isLocalization m.primeCompl

/-- A finite type factorization `Λ → C → R` algebraized as in
`AlgebraizesFiniteTypeFactorizations` gives a `Λ`-algebra map `C → H` into every henselian local
`Λ`-algebra `H` whose maximal ideal contracts to `𝔪`. -/
private theorem nonempty_algHom_of_algebraizesFiniteTypeFactorizations
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {m : Ideal Λ} [m.IsMaximal]
    {R : Type u} [CommRing R] [Algebra Λ R]
    (hyp : AlgebraizesFiniteTypeFactorizations Λ m R)
    {C : Type u} [CommRing C] [Algebra Λ C] (hC : Algebra.FiniteType Λ C) (φ : C →ₐ[Λ] R)
    {H : Type u} [CommRing H] [HenselianLocalRing H] [Algebra Λ H]
    (hH : m = (maximalIdeal H).comap (algebraMap Λ H)) :
    Nonempty (C →ₐ[Λ] H) := by
  obtain ⟨A, _, _, hftA, mA, _, hmA, hres, hsm, ⟨ρ⟩⟩ := hyp C hC φ
  obtain ⟨F⟩ := exists_algHom_of_isSmoothAt hftA mA hmA hres hsm hH
  exact ⟨F.comp ρ⟩

/-- If every finite type factorization `Λ → C → R` is algebraized as in
`AlgebraizesFiniteTypeFactorizations`, then every finite system of polynomial equations over
`Λ` with a solution in `R` has a solution in every henselian local `Λ`-algebra whose maximal
ideal contracts to `𝔪`.

This is the implication the second half of Stacks 07XI runs; the target is specialized to the
henselization of `Λ_𝔪` in
`exists_solution_henselization_of_algebraizesFiniteTypeFactorizations`. -/
public theorem exists_solution_of_algebraizesFiniteTypeFactorizations
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {m : Ideal Λ} [m.IsMaximal]
    {R : Type u} [CommRing R] [Algebra Λ R]
    (hyp : AlgebraizesFiniteTypeFactorizations Λ m R)
    {H : Type u} [CommRing H] [HenselianLocalRing H] [Algebra Λ H]
    (hH : m = (maximalIdeal H).comap (algebraMap Λ H))
    {n k : ℕ} (f : Fin k → MvPolynomial (Fin n) Λ) (a : Fin n → R)
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) :
    ∃ b : Fin n → H, ∀ j, MvPolynomial.aeval b (f j) = 0 := by
  classical
  set I : Ideal (MvPolynomial (Fin n) Λ) := Ideal.span (Set.range f) with hI
  have hmem : ∀ j, f j ∈ I := fun j => Ideal.subset_span ⟨j, rfl⟩
  have hker : ∀ x ∈ I, (MvPolynomial.aeval a : MvPolynomial (Fin n) Λ →ₐ[Λ] R) x = 0 := by
    have hle : I ≤ RingHom.ker
        ((MvPolynomial.aeval a : MvPolynomial (Fin n) Λ →ₐ[Λ] R) : _ →+* R) := by
      rw [hI, Ideal.span_le]
      rintro x ⟨j, rfl⟩
      simpa [SetLike.mem_coe, RingHom.mem_ker] using ha j
    exact fun x hx => hle hx
  have hftC : Algebra.FiniteType Λ (MvPolynomial (Fin n) Λ ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ Λ I) Ideal.Quotient.mk_surjective
  obtain ⟨G⟩ := nonempty_algHom_of_algebraizesFiniteTypeFactorizations hyp hftC
    (Ideal.Quotient.liftₐ I (MvPolynomial.aeval a) hker) hH
  set χ : MvPolynomial (Fin n) Λ →ₐ[Λ] H := G.comp (Ideal.Quotient.mkₐ Λ I) with hχ
  refine ⟨fun i => χ (MvPolynomial.X i), fun j => ?_⟩
  rw [show (fun i => χ (MvPolynomial.X i)) = ⇑χ ∘ MvPolynomial.X from rfl,
    ← MvPolynomial.aeval_unique, hχ, AlgHom.comp_apply,
    show (Ideal.Quotient.mkₐ Λ I) (f j) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (hmem j),
    map_zero]

/-- If every finite type factorization `Λ → C → R` is algebraized as in
`AlgebraizesFiniteTypeFactorizations`, then one such factorization `Λ → C → R`, with `C` of
finite type over `Λ`, gives a `Λ`-algebra map `C → H` into every henselian local `Λ`-algebra
`H` whose maximal ideal contracts to `𝔪`.

This is the implication the second half of Stacks 07XI runs, in the form the Example's own
datum takes: the factorization `Λ → C → R` is the Example's, and for
`C = Λ[y_1, …, y_n]/(f_1, …, f_k)` the map `C → H` is a solution in `H` of a system with a
solution in `R`, which is the reading
`exists_solution_of_algebraizesFiniteTypeFactorizations` carries out. -/
public theorem exists_ringHom_of_algebraizesFiniteTypeFactorizations
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {m : Ideal Λ} [m.IsMaximal]
    {R : Type u} [CommRing R] [Algebra Λ R]
    (hyp : AlgebraizesFiniteTypeFactorizations Λ m R)
    {C : Type u} [CommRing C] (φ : Λ →+* C) (hφ : RingHom.FiniteType φ)
    (ψ : C →+* R) (hψ : ψ.comp φ = algebraMap Λ R)
    {H : Type u} [CommRing H] [HenselianLocalRing H] [Algebra Λ H]
    (hH : m = (maximalIdeal H).comap (algebraMap Λ H)) :
    ∃ χ : C →+* H, χ.comp φ = algebraMap Λ H := by
  let : Algebra Λ C := φ.toAlgebra
  obtain ⟨G⟩ := nonempty_algHom_of_algebraizesFiniteTypeFactorizations hyp hφ
    { ψ with commutes' := fun c => congrArg (fun g : Λ →+* R => g c) hψ } hH
  exact ⟨(G : C →+* H), RingHom.ext G.commutes⟩

/-- A henselization of the local ring of `Λ` at a maximal ideal `𝔪` exists, in the universe of
`Λ`, so the hypotheses placed on `H` in
`exists_solution_henselization_of_algebraizesFiniteTypeFactorizations` are satisfiable. -/
public theorem exists_henselization_over_maximalIdeal (Λ : Type u) [CommRing Λ]
    (m : Ideal Λ) [m.IsMaximal] :
    ∃ (H : Type u) (_ : CommRing H) (_ : IsLocalRing H)
      (_ : Algebra (Localization.AtPrime m) H) (_ : Algebra Λ H)
      (_ : IsScalarTower Λ (Localization.AtPrime m) H),
      IsHenselization (Localization.AtPrime m) (ResidueField (Localization.AtPrime m)) H := by
  obtain ⟨H, _, _, _, hH⟩ :=
    IsLocalRing.exists_isHenselization_residueField (Localization.AtPrime m)
  let algebraOfComp : Algebra Λ H :=
    ((algebraMap (Localization.AtPrime m) H).comp
      (algebraMap Λ (Localization.AtPrime m))).toAlgebra
  exact ⟨H, inferInstance, inferInstance, inferInstance, algebraOfComp,
    IsScalarTower.of_algebraMap_eq' rfl, hH⟩

/-- Solutions in the henselization: the step of
Stacks 07XI from the datum read off the conclusion of 07XH to solutions in `Λ_𝔪^h` of
polynomial systems over `Λ` solvable in `Λ_𝔪^∧`. Let `Λ` be a Noetherian ring, let `𝔪`
be a maximal ideal of `Λ`, and let `H` be a henselization of `Λ_𝔪`. Assume every
factorization `Λ → C → Λ_𝔪^∧` with `C` of finite type over `Λ` carries the datum that the
conclusion of Stacks 07XH supplies (assumed in the Example without the G-ring hypothesis of
07XH): a finite type
`Λ`-algebra `A`, a maximal ideal `𝔪_A` over `𝔪` with `κ(𝔪) = κ(𝔪_A)`, smoothness of `Λ → A`
at `𝔪_A`, and a `Λ`-algebra map `C → A`. Then every finite system of polynomial equations
over `Λ` with a solution in `Λ_𝔪^∧` has a solution in `H`. -/
public theorem exists_solution_henselization_of_algebraizesFiniteTypeFactorizations
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (m : Ideal Λ) [m.IsMaximal]
    (hyp : AlgebraizesFiniteTypeFactorizations Λ m
      (AdicCompletion (maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m)))
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra Λ H]
    [Algebra (Localization.AtPrime m) H] [IsScalarTower Λ (Localization.AtPrime m) H]
    [IsHenselization (Localization.AtPrime m) (ResidueField (Localization.AtPrime m)) H]
    {n k : ℕ} (f : Fin k → MvPolynomial (Fin n) Λ)
    (a : Fin n →
      AdicCompletion (maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m))
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) :
    ∃ b : Fin n → H, ∀ j, MvPolynomial.aeval b (f j) = 0 := by
  have : HenselianLocalRing H :=
    IsHenselization.henselian (R := Localization.AtPrime m)
      (L := ResidueField (Localization.AtPrime m)) (Rh := H)
  have : IsLocalHom (algebraMap (Localization.AtPrime m) H) :=
    IsHenselization.isLocalHom (L := ResidueField (Localization.AtPrime m))
  have hH : m = (maximalIdeal H).comap (algebraMap Λ H) := by
    rw [IsScalarTower.algebraMap_eq Λ (Localization.AtPrime m) H, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime m) m).symm
  exact exists_solution_of_algebraizesFiniteTypeFactorizations hyp hH f a ha

end Deformation.Artin

end
