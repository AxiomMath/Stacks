module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.RingTheory.Koszul.Augmentation
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.Blowup.Affine
public import StacksFrontier.RingTheory.Blowup.IdealFactorization
public import StacksFrontier.RingTheory.Koszul.BlowupRelations
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.AnnihilatorTruncationReduction

/-!
# Uniform annihilation of the high Tor modules of an affine blowup algebra

Let `I = (a₁, …, a_t)` be an ideal of a Noetherian ring `A`, let `a = a₁` and let `B = A[I/a]` be
the affine blowup algebra. A single power of `I` annihilates `Torᴬᵢ(B, M)` simultaneously for every
`A`-module `M` and every `i ≥ t`.

## Main results

* `Stacks.Blowup.exists_pow_le_annihilator_tor_affineBlowupAlgebra`: the uniform annihilating
  power of `I`.

## Implementation notes

`B` is presented as the quotient of `A[x₂, …, x_t]` by the `a`-power saturation of the ideal of
relations `a xⱼ - aⱼ`, and the Koszul complex on those relations is a complex of flat `A`-modules.

The generators are indexed by `Fin (n + 1)`, so `t = n + 1`, and the blowup algebra is formed in an
arbitrary localization away from the first generator.

## References

* [Stacks Project, Tag 0G9Y](https://stacks.math.columbia.edu/tag/0G9Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

/-! ### Saturation in a Noetherian ring -/

/-- If every element of an ideal of a Noetherian ring has some `a`-power multiple in a subideal,
then a single power of `a` works for all of them. -/
public theorem exists_pow_mul_mem {A : Type u} [CommRing A] [IsNoetherianRing A] (a : A)
    (Z J : Ideal A) (h : ∀ z ∈ Z, ∃ k : ℕ, a ^ k * z ∈ J) :
    ∃ c : ℕ, ∀ z ∈ Z, a ^ c * z ∈ J := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian Z)
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => hs ▸ Submodule.subset_span hx
  choose k hk using fun (x : A) (hx : x ∈ s) => h x (hsZ x hx)
  refine ⟨s.attach.sup fun x => k x.1 x.2, ?_⟩
  intro z hz
  rw [← hs] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
      have hle : k x hx ≤ s.attach.sup fun y => k y.1 y.2 :=
        Finset.le_sup (f := fun y : {y // y ∈ s} => k y.1 y.2) (Finset.mem_attach s ⟨x, hx⟩)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact J.mul_mem_left _ (hk x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left _ hx

/-! ### The polynomial presentation of an affine blowup algebra -/

section Presentation

variable {A : Type u} [CommRing A] (a : A) (S : Type u) [CommRing S] [Algebra A S]
  [IsLocalization.Away a S]

/-- The `A`-algebra map from a polynomial ring onto the affine blowup algebra, sending the `j`-th
variable to the fraction `bⱼ / a`. -/
public def pres {n : ℕ} (b : Fin n → A) : MvPolynomial (Fin n) A →ₐ[A] S :=
  MvPolynomial.aeval fun j => IsLocalization.mk' S (b j) ⟨a, Submonoid.mem_powers a⟩

/-- The image of the `j`-th variable under the presentation is the fraction `bⱼ / a`. -/
public theorem pres_X {n : ℕ} (b : Fin n → A) (j : Fin n) :
    pres a S b (MvPolynomial.X j) =
      IsLocalization.mk' S (b j) ⟨a, Submonoid.mem_powers a⟩ := by
  simp [pres]

/-- The presentation carries the `j`-th variable to a fraction with numerator `bⱼ` and
denominator `a`. -/
public theorem pres_X_mul {n : ℕ} (b : Fin n → A) (j : Fin n) :
    pres a S b (MvPolynomial.X j) * algebraMap A S a = algebraMap A S (b j) := by
  rw [pres_X, IsLocalization.mk'_spec_mk]

/-- The image of `a` in a localization away from `a` is a unit. -/
public theorem isUnit_algebraMap_away : IsUnit (algebraMap A S a) :=
  IsLocalization.map_units (M := Submonoid.powers a) S ⟨a, Submonoid.mem_powers a⟩

/-- The range of the polynomial presentation is the affine blowup algebra `A[I/a]`. -/
public theorem range_pres {n : ℕ} (b : Fin n → A) (I : Ideal A)
    (hI : I = Ideal.span (insert a (Set.range b))) :
    (pres a S b).range = affineBlowupAlgebra I a S := by
  have hgen : (pres a S b).range =
      Algebra.adjoin A (Set.range fun j : Fin n =>
        IsLocalization.mk' S (b j) ⟨a, Submonoid.mem_powers a⟩) :=
    (Algebra.adjoin_range_eq_range_aeval A _).symm
  rw [hgen]
  show Algebra.adjoin A _ = Algebra.adjoin A _
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro z ⟨j, rfl⟩
    refine Algebra.subset_adjoin ⟨b j, ?_, rfl⟩
    rw [hI]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  · rintro z ⟨y, hy, rfl⟩
    rw [hI] at hy
    obtain ⟨c, w, hw, hyc⟩ := Submodule.mem_span_insert.1 hy
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hw
    have key : IsLocalization.mk' S y ⟨a, Submonoid.mem_powers a⟩ =
        algebraMap A S c +
          ∑ j : Fin n, algebraMap A S (d j) *
            IsLocalization.mk' S (b j) ⟨a, Submonoid.mem_powers a⟩ := by
      refine (isUnit_algebraMap_away a S).mul_right_cancel ?_
      rw [IsLocalization.mk'_spec_mk, add_mul, Finset.sum_mul]
      have hterm : ∀ j : Fin n,
          algebraMap A S (d j) *
              IsLocalization.mk' S (b j) ⟨a, Submonoid.mem_powers a⟩ * algebraMap A S a =
            algebraMap A S (d j * b j) := by
        intro j
        rw [mul_assoc, IsLocalization.mk'_spec_mk, map_mul]
      rw [Finset.sum_congr rfl fun j _ => hterm j, ← map_sum, ← map_mul, ← map_add]
      congr 1
      rw [hyc, smul_eq_mul]
      congr 1
      simpa [smul_eq_mul] using hd.symm
    rw [key]
    refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ ?_)
    intro j _
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Algebra.subset_adjoin ⟨j, rfl⟩)

end Presentation

/-! ### The Koszul complex on the blowup relations -/

section Relations

variable {A : Type u} [CommRing A] (a : A) {n : ℕ} (b : Fin n → A)

/-- The relations `a xⱼ - bⱼ` cutting out the affine blowup algebra inside a polynomial ring. -/
public def rel : Fin n → MvPolynomial (Fin n) A :=
  fun j => MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j)

/-- Every term of the Koszul complex on the relations is a flat `A`-module. -/
public theorem flat_exteriorPower (m : ℕ) :
    Module.Flat A (⋀[MvPolynomial (Fin n) A]^m (Fin n → MvPolynomial (Fin n) A)) :=
  Module.Flat.trans A (MvPolynomial (Fin n) A) _

/-- The `m`-th Koszul differential of the relations, read as a map of `A`-modules. -/
public def relD (m : ℕ) :
    (⋀[MvPolynomial (Fin n) A]^(m + 1) (Fin n → MvPolynomial (Fin n) A)) →ₗ[A]
      (⋀[MvPolynomial (Fin n) A]^m (Fin n → MvPolynomial (Fin n) A)) :=
  LinearMap.restrictScalars A (Koszul.d (Koszul.seqDual (rel a b)) m)

/-- The image of the `m`-th Koszul differential of the relations. -/
public def relRange (m : ℕ) :
    Submodule A (⋀[MvPolynomial (Fin n) A]^m (Fin n → MvPolynomial (Fin n) A)) :=
  LinearMap.range (relD a b m)

/-- The kernel of the `m`-th Koszul differential of the relations. -/
public def relKer (m : ℕ) :
    Submodule A (⋀[MvPolynomial (Fin n) A]^(m + 1) (Fin n → MvPolynomial (Fin n) A)) :=
  LinearMap.ker (relD a b m)

/-- The image of the `(m + 1)`-st Koszul differential of the relations lies in the kernel of the
`m`-th. -/
public theorem relRange_succ_le_relKer (m : ℕ) : relRange a b (m + 1) ≤ relKer a b m := by
  rintro x ⟨y, rfl⟩
  exact LinearMap.congr_fun (Koszul.d_comp_d (Koszul.seqDual (rel a b)) m) y

/-- The short exact sequence `0 → ker dₘ → ⋀^{m+1} → im dₘ → 0` attached to the `m`-th Koszul
differential. -/
public def relSC (m : ℕ) : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (R := A) (Submodule.subtype (relKer a b m))
    (LinearMap.rangeRestrict (relD a b m)) (LinearMap.ext fun y => Subtype.ext y.2)

/-- The kernel of the `m`-th Koszul differential is exactly the kernel of its corestriction to
its image. -/
private theorem relSC_exact (m : ℕ) :
    Function.Exact (Submodule.subtype (relKer a b m))
      (LinearMap.rangeRestrict (relD a b m)) := fun y =>
  ⟨fun hy => ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact Subtype.ext z.2⟩

/-- The sequence `0 → ker dₘ → ⋀^{m+1} → im dₘ → 0` is short exact. -/
public theorem relSC_shortExact (m : ℕ) : (relSC a b m).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (relSC_exact a b m)
    (Submodule.injective_subtype (relKer a b m))
    (LinearMap.surjective_rangeRestrict (relD a b m))

/-- The short exact sequence `0 → im d_{m+1} → ker dₘ → H_{m+1} → 0` exhibiting the Koszul
homology in degree `m + 1`. -/
public def relSubSC (m : ℕ) : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (R := A)
    (Submodule.inclusion (relRange_succ_le_relKer a b m))
    (Submodule.mkQ (Submodule.comap (relKer a b m).subtype (relRange a b (m + 1))))
    (LinearMap.ext fun y => (Submodule.Quotient.mk_eq_zero _).2 y.2)

/-- Inside the kernel of the `m`-th Koszul differential, the image of the next differential is
exactly the kernel of the quotient map. -/
private theorem relSubSC_exact (m : ℕ) :
    Function.Exact (Submodule.inclusion (relRange_succ_le_relKer a b m))
      (Submodule.mkQ (Submodule.comap (relKer a b m).subtype (relRange a b (m + 1)))) := by
  intro y
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun hy => ⟨⟨y.1, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩

/-- The sequence `0 → im d_{m+1} → ker dₘ → H_{m+1} → 0` is short exact. -/
public theorem relSubSC_shortExact (m : ℕ) : (relSubSC a b m).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (relSubSC_exact a b m)
    (Submodule.inclusion_injective (relRange_succ_le_relKer a b m))
    (Submodule.mkQ_surjective (Submodule.comap (relKer a b m).subtype (relRange a b (m + 1))))

/-- The `A`-linear identification `⋀⁰ ≃ A[x₁, …, xₙ]` of the bottom term of the Koszul complex
with the polynomial ring. -/
public def zeroEquivA :
    (⋀[MvPolynomial (Fin n) A]^0 (Fin n → MvPolynomial (Fin n) A)) ≃ₗ[A]
      MvPolynomial (Fin n) A :=
  LinearEquiv.restrictScalars A
    (exteriorPower.zeroEquiv (MvPolynomial (Fin n) A) (Fin n → MvPolynomial (Fin n) A))

/-- Under the identification of the bottom term with the polynomial ring, the image of the
degree-zero Koszul differential is the ideal generated by the relations. -/
public theorem map_relRange_zero :
    Submodule.map (zeroEquivA (A := A) (n := n) : _ →ₗ[A] _) (relRange a b 0) =
      Submodule.restrictScalars A (Ideal.span (Set.range (rel a b))) := by
  ext x
  rw [Submodule.restrictScalars_mem, ← Koszul.range_d_zero (rel a b)]
  rfl

/-- The bottom image of the Koszul complex on the relations is isomorphic, as an `A`-module, to
the ideal generated by the relations. -/
public def relRangeZeroIso :
    ModuleCat.of A ↥(relRange a b 0) ≅
      ModuleCat.of A ↥(Submodule.restrictScalars A (Ideal.span (Set.range (rel a b)))) :=
  ((zeroEquivA (A := A) (n := n)).submoduleMap (relRange a b 0) ≪≫ₗ
    LinearEquiv.ofEq _ _ (map_relRange_zero a b)).toModuleIso

end Relations

/-! ### The presentation of the blowup algebra by the relations -/

section Saturation

variable {A : Type u} [CommRing A] (a : A) {n : ℕ} (b : Fin n → A)
  (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away a S] (I : Ideal A)

/-- The kernel of the polynomial presentation of the affine blowup algebra. -/
public def presKer : Ideal (MvPolynomial (Fin n) A) := RingHom.ker (pres a S b).toRingHom

/-- An element lies in the kernel of the presentation exactly when the presentation kills it. -/
public theorem mem_presKer_iff (z : MvPolynomial (Fin n) A) :
    z ∈ presKer a b S ↔ pres a S b z = 0 := Iff.rfl

/-- The relations `a xⱼ - bⱼ` lie in the kernel of the presentation. -/
public theorem span_rel_le_presKer :
    Ideal.span (Set.range (rel a b)) ≤ presKer a b S := by
  rw [Ideal.span_le]
  rintro x ⟨j, rfl⟩
  have h1 : pres a S b (MvPolynomial.C a) = algebraMap A S a := by simp [pres]
  have h2 : pres a S b (MvPolynomial.C (b j)) = algebraMap A S (b j) := by simp [pres]
  refine (mem_presKer_iff a b S _).2 ?_
  rw [rel, map_sub, map_mul, h1, h2, pres_X, mul_comm, IsLocalization.mk'_spec_mk, sub_self]

/-- A single power of `a` carries the kernel of the presentation into the ideal of
relations. -/
public theorem exists_pow_mul_presKer_le [IsNoetherianRing A]
    (hI : I = Ideal.span (insert a (Set.range b))) :
    ∃ c : ℕ, ∀ z ∈ presKer a b S,
      (MvPolynomial.C a) ^ c * z ∈ Ideal.span (Set.range (rel a b)) := by
  have h08 := (Ideal.range_eq_affineBlowup_and_ker_eq_saturation (I := I) hI (pres a S b)
    (pres_X_mul a S b)).2
  refine exists_pow_mul_mem (MvPolynomial.C a) (presKer a b S)
    (Ideal.span (Set.range (rel a b))) fun z hz => ?_
  obtain ⟨k, hk⟩ := (h08 z).1 ((mem_presKer_iff a b S z).1 hz)
  exact ⟨k, by rwa [MvPolynomial.smul_eq_C_mul, map_pow] at hk⟩

/-- The polynomial ring surjects onto the affine blowup algebra via the presentation. -/
public def presOnto (hI : I = Ideal.span (insert a (Set.range b))) :
    MvPolynomial (Fin n) A →ₗ[A] ↥((affineBlowupAlgebra I a S).toSubmodule) :=
  LinearMap.codRestrict ((affineBlowupAlgebra I a S).toSubmodule) (pres a S b).toLinearMap
    (fun p => by
      rw [Subalgebra.mem_toSubmodule, ← range_pres a S b I hI]
      exact ⟨p, rfl⟩)

/-- The presentation, corestricted to the blowup algebra, is surjective. -/
private theorem presOnto_surjective (hI : I = Ideal.span (insert a (Set.range b))) :
    Function.Surjective (presOnto a b S I hI) := by
  intro y
  have hy : (y : S) ∈ (pres a S b).range := by
    rw [range_pres a S b I hI]
    exact (Subalgebra.mem_toSubmodule _).1 y.2
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, Subtype.ext hp⟩

/-- The kernel of the presentation is exactly the kernel of the surjection onto the blowup
algebra. -/
private theorem presSC_exact (hI : I = Ideal.span (insert a (Set.range b))) :
    Function.Exact (Submodule.subtype (Submodule.restrictScalars A (presKer a b S)))
      (presOnto a b S I hI) := fun y =>
  ⟨fun hy => ⟨⟨y, (mem_presKer_iff a b S y).2 (congrArg Subtype.val hy)⟩, rfl⟩,
    by rintro ⟨z, rfl⟩; exact Subtype.ext ((mem_presKer_iff a b S _).1 z.2)⟩

/-- The short exact sequence `0 → ker → A[x₁, …, xₙ] → A[I/a] → 0`. -/
public def presSC (hI : I = Ideal.span (insert a (Set.range b))) :
    ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (R := A)
    (Submodule.subtype (Submodule.restrictScalars A (presKer a b S)))
    (presOnto a b S I hI)
    (LinearMap.ext fun y => Subtype.ext ((mem_presKer_iff a b S _).1 y.2))

/-- The sequence `0 → ker → A[x₁, …, xₙ] → A[I/a] → 0` is short exact. -/
public theorem presSC_shortExact (hI : I = Ideal.span (insert a (Set.range b))) :
    (presSC a b S I hI).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (presSC_exact a b S I hI)
    (Submodule.injective_subtype _) (presOnto_surjective a b S I hI)

/-- The relations form an `A`-submodule of the kernel of the presentation. -/
public theorem restrictScalars_span_rel_le :
    Submodule.restrictScalars A (Ideal.span (Set.range (rel a b))) ≤
      Submodule.restrictScalars A (presKer a b S) :=
  fun _ hx => span_rel_le_presKer a b S hx

/-- Inside the kernel of the presentation, the relations are exactly the kernel of the quotient
map. -/
private theorem presSubSC_exact :
    Function.Exact (Submodule.inclusion (restrictScalars_span_rel_le a b S))
      (Submodule.mkQ (Submodule.comap
        (Submodule.restrictScalars A (presKer a b S)).subtype
        (Submodule.restrictScalars A (Ideal.span (Set.range (rel a b)))))) := by
  intro y
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun hy => ⟨⟨y.1, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩

/-- The short exact sequence `0 → (relations) → ker → ker/(relations) → 0`. -/
public def presSubSC : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (R := A)
    (Submodule.inclusion (restrictScalars_span_rel_le a b S))
    (Submodule.mkQ (Submodule.comap
      (Submodule.restrictScalars A (presKer a b S)).subtype
      (Submodule.restrictScalars A (Ideal.span (Set.range (rel a b))))))
    (LinearMap.ext fun y => (Submodule.Quotient.mk_eq_zero _).2 y.2)

/-- The sequence `0 → (relations) → ker → ker/(relations) → 0` is short exact. -/
public theorem presSubSC_shortExact : (presSubSC a b S).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (presSubSC_exact a b S)
    (Submodule.inclusion_injective (restrictScalars_span_rel_le a b S))
    (Submodule.mkQ_surjective _)

end Saturation

/-- A flat module has `Torᴬₖ(X, M)` annihilated by `1` for every `k ≥ 1`. -/
private theorem one_mem_annihilator_tor_of_flat {A : Type u} [CommRing A] (X M : ModuleCat.{u} A)
    [Module.Flat A X] (k : ℕ) (hk : 1 ≤ k) :
    (1 : A) ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) k).obj X).obj M) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
  exact Module.mem_annihilator.mpr fun x => (ModuleCat.isZero_iff_subsingleton.mp
    (Tor_iso_Tor'.tor_flat_isZero A X M k')).elim _ _

/-- If `r` carries every element of a module into a submodule, then `r` annihilates the
quotient. -/
private theorem mem_annihilator_quotient {A : Type u} [CommRing A] {X : Type u} [AddCommGroup X]
    [Module A X] (N : Submodule A X) (r : A) (h : ∀ y : X, r • y ∈ N) :
    r ∈ Module.annihilator A (X ⧸ N) := by
  refine Module.mem_annihilator.mpr fun q => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact (Submodule.Quotient.mk_smul _ _ _).symm.trans ((Submodule.Quotient.mk_eq_zero _).2 (h y))

/-! ### The dimension-shifting induction -/

section Induction

variable {A : Type u} [CommRing A] (a : A) {n : ℕ} (b : Fin n → A)

/-- The image of the top Koszul differential vanishes once the exterior power above it does. -/
public theorem relRange_top_subsingleton
    (htop : Subsingleton
      (⋀[MvPolynomial (Fin n) A]^(n + 1) (Fin n → MvPolynomial (Fin n) A))) :
    Subsingleton ↥(relRange a b n) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  obtain ⟨u, hu⟩ := x.2
  obtain ⟨v, hv⟩ := y.2
  rw [← hu, ← hv, Subsingleton.elim u v]

/-- **Dimension shifting along the Koszul complex.** If one power of `a` carries every Koszul
cycle of the relations into the boundaries, then `a ^ (j * c)` annihilates `Torᴬᵢ` of the image
of the `(n - j)`-th Koszul differential in all degrees `i ≥ j`. -/
public theorem mem_annihilator_tor_relRange (c : ℕ)
    (htop : Subsingleton
      (⋀[MvPolynomial (Fin n) A]^(n + 1) (Fin n → MvPolynomial (Fin n) A)))
    (hc : ∀ (m : ℕ) (y : ↥(relKer a b m)),
      (a ^ c) • (y : ⋀[MvPolynomial (Fin n) A]^(m + 1) (Fin n → MvPolynomial (Fin n) A)) ∈
        relRange a b (m + 1)) :
    ∀ (j m : ℕ), m + j = n → ∀ (M : ModuleCat.{u} A) (i : ℕ), j ≤ i →
      a ^ (j * c) ∈ Module.annihilator A
        (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A ↥(relRange a b m))).obj M) := by
  intro j
  induction j with
  | zero =>
      intro m hm M i _
      obtain rfl : m = n := by lia
      have hsub := relRange_top_subsingleton a b htop
      have h1 : (1 : A) ∈ Module.annihilator A (ModuleCat.of A ↥(relRange a b m)) :=
        Module.mem_annihilator.mpr fun x => hsub.elim _ _
      simpa using mem_annihilator_tor_of_mem_annihilator
        (ModuleCat.of A ↥(relRange a b m)) M i h1
  | succ j ih =>
      intro m hm M i hi
      have hm' : (m + 1) + j = n := by lia
      have hX₃ : a ^ c ∈ Module.annihilator A (relSubSC a b m).X₃ :=
        mem_annihilator_quotient _ _ (hc m)
      have hmid := mem_annihilator_tor_middle (relSubSC a b m) (relSubSC_shortExact a b m) M
        hX₃ (fun k hk => ih (m + 1) hm' M k hk)
      have hflat : Module.Flat A ↥((relSC a b m).X₂) :=
        flat_exteriorPower (A := A) (n := n) (m + 1)
      have hshift := mem_annihilator_tor_of_shift (relSC a b m) (relSC_shortExact a b m) M
        hmid (one_mem_annihilator_tor_of_flat _ M) i (by lia) (by lia)
      have hpow : a ^ c * a ^ (j * c) * 1 = a ^ ((j + 1) * c) := by ring
      rwa [hpow] at hshift

end Induction

/-! ### Annihilation of Tor transported along isomorphisms -/

/-- Annihilation of a Tor module is invariant under isomorphism of the first variable. -/
public theorem mem_annihilator_tor_of_iso {A : Type u} [CommRing A] {X Y : ModuleCat.{u} A}
    (e : X ≅ Y) (M : ModuleCat.{u} A) (i : ℕ) {r : A}
    (hr : r ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) i).obj X).obj M)) :
    r ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) i).obj Y).obj M) :=
  (((Tor (ModuleCat.{u} A) i).mapIso e).app M).toLinearEquiv.annihilator_eq ▸ hr

/-! ### From a power of the generator to a power of the ideal -/

/-- If `a ^ c` annihilates a `Tor` module of the affine blowup algebra `A[I/a]`, then so does
`I ^ c`. -/
public theorem pow_le_annihilator_of_pow_mem_annihilator {A : Type u} [CommRing A] (a : A)
    (I : Ideal A) (ha : a ∈ I) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away a S] (M : ModuleCat.{u} A) (i c : ℕ)
    (h : a ^ c ∈ Module.annihilator A
      (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A ↥(affineBlowupAlgebra I a S))).obj M)) :
    I ^ c ≤ Module.annihilator A
      (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A ↥(affineBlowupAlgebra I a S))).obj M) := by
  intro x hx
  have hmem : algebraMap A ↥(affineBlowupAlgebra I a S) x ∈
      Ideal.span {algebraMap A ↥(affineBlowupAlgebra I a S) a ^ c} := by
    rw [← affineBlowupAlgebra.map_ideal_pow_eq_span_singleton (S := S) I a ha c]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 hmem
  have hfac : (x • 𝟙 (ModuleCat.of A ↥(affineBlowupAlgebra I a S))) =
      ModuleCat.ofHom (LinearMap.mulLeft A β) ≫
        (a ^ c • 𝟙 (ModuleCat.of A ↥(affineBlowupAlgebra I a S))) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply]
    rw [Algebra.smul_def, Algebra.smul_def, ← hβ, map_pow]
    ring
  refine (Stacks.Algebraization.smul_id_eq_zero_iff_mem_annihilator _ x).1 ?_
  rw [← tor_map_smul_id (ModuleCat.of A ↥(affineBlowupAlgebra I a S)) M i x, hfac,
    Functor.map_comp, NatTrans.comp_app,
    tor_map_smul_id (ModuleCat.of A ↥(affineBlowupAlgebra I a S)) M i (a ^ c),
    (Stacks.Algebraization.smul_id_eq_zero_iff_mem_annihilator _ (a ^ c)).2 h, Limits.comp_zero]


/-! ### The main theorem -/

/-- **Uniform annihilation of the high `Tor` modules of an affine blowup algebra.**
Let `I = (a₁, …, a_t)` be an ideal of a Noetherian ring `A`, let `a = a₁`, and let `B = A[I/a]`
be the affine blowup algebra. There is a `c > 0` such that `Iᶜ` annihilates `Torᴬᵢ(B, M)` for
every `A`-module `M` and every `i ≥ t`. -/
@[stacks 0G9Y]
public theorem exists_pow_le_annihilator_tor_affineBlowupAlgebra
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} (g : Fin (n + 1) → A)
    (I : Ideal A) (hI : I = Ideal.span (Set.range g))
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away (g 0) S] :
    ∃ c : ℕ, 0 < c ∧ ∀ (M : ModuleCat.{u} A) (i : ℕ), n + 1 ≤ i →
      I ^ c ≤ Module.annihilator A
        (((Tor (ModuleCat.{u} A) i).obj
          (ModuleCat.of A ↥(affineBlowupAlgebra I (g 0) S))).obj M) := by
  classical
  have hI' : I = Ideal.span (insert (g 0) (Set.range (Fin.tail g))) := by
    rw [hI, ← Fin.range_cons, Fin.cons_self_tail]
  have ha : g 0 ∈ I := hI ▸ Ideal.subset_span ⟨0, rfl⟩
  obtain ⟨c₁, hc₁⟩ := Koszul.exists_pow_smul_ker_le_range (g 0) (Fin.tail g)
  obtain ⟨c₂, hc₂⟩ := exists_pow_mul_presKer_le (g 0) (Fin.tail g) S I hI'
  have htop : Subsingleton
      (⋀[MvPolynomial (Fin n) A]^(n + 1) (Fin n → MvPolynomial (Fin n) A)) :=
    Koszul.subsingleton_exteriorPower_of_rank_lt (Nat.lt_succ_self n)
  have hc : ∀ (m : ℕ) (y : ↥(relKer (g 0) (Fin.tail g) m)),
      ((g 0) ^ c₁) • (y : ⋀[MvPolynomial (Fin n) A]^(m + 1) (Fin n → MvPolynomial (Fin n) A)) ∈
        relRange (g 0) (Fin.tail g) (m + 1) := by
    intro m y
    have hy := hc₁ m (y : _) y.2
    rwa [← map_pow, ← MvPolynomial.algebraMap_eq, algebraMap_smul] at hy
  refine ⟨c₂ + n * c₁ + 1, Nat.succ_pos _, ?_⟩
  intro M i hi
  refine (Ideal.pow_le_pow_right (Nat.le_succ _)).trans ?_
  refine pow_le_annihilator_of_pow_mem_annihilator (g 0) I ha S M i (c₂ + n * c₁) ?_
  have hind := mem_annihilator_tor_relRange (g 0) (Fin.tail g) c₁ htop hc n 0 (by lia) M
  have hbot : ∀ k, n ≤ k → (g 0) ^ (n * c₁) ∈ Module.annihilator A
      (((Tor (ModuleCat.{u} A) k).obj (ModuleCat.of A ↥(Submodule.restrictScalars A
        (Ideal.span (Set.range (rel (g 0) (Fin.tail g))))))).obj M) :=
    fun k hk => mem_annihilator_tor_of_iso (relRangeZeroIso (g 0) (Fin.tail g)) M k (hind k hk)
  have hX₃ : (g 0) ^ c₂ ∈ Module.annihilator A (presSubSC (g 0) (Fin.tail g) S).X₃ := by
    refine mem_annihilator_quotient _ _ fun y => ?_
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem, map_smul, Algebra.smul_def,
      MvPolynomial.algebraMap_eq, map_pow]
    exact hc₂ (y : MvPolynomial (Fin n) A) y.2
  have hmid := mem_annihilator_tor_middle (presSubSC (g 0) (Fin.tail g) S)
    (presSubSC_shortExact (g 0) (Fin.tail g) S) M hX₃ hbot
  have hflat : Module.Flat A ↥((presSC (g 0) (Fin.tail g) S I hI').X₂) :=
    inferInstanceAs (Module.Flat A (MvPolynomial (Fin n) A))
  have hshift := mem_annihilator_tor_of_shift (presSC (g 0) (Fin.tail g) S I hI')
    (presSC_shortExact (g 0) (Fin.tail g) S I hI') M hmid
    (one_mem_annihilator_tor_of_flat _ M) i (by lia) (by lia)
  have hpow : (g 0) ^ c₂ * (g 0) ^ (n * c₁) * 1 = (g 0) ^ (c₂ + n * c₁) := by
    rw [mul_one, ← pow_add]
  rwa [hpow] at hshift

end Stacks.Blowup
