module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Colimit
public import StacksFrontier.RingTheory.Henselian.FixedPoints
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Invariant.InertiaLocalization
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField

/-!
# A strict henselization as the inertia invariants of a localized integral closure

Let `A` be a normal local domain with fraction field `K`, let `L / K` be a Galois extension with
`L` separably closed — so that `L` is a separable closure of `K` — and let `B` be the integral
closure of `A` in `L`. Let `q` be a prime of `B` lying over the maximal ideal of `A` and let
`I = q.inertia Gal(L/K)` be its inertia group. Then

  `A ^ {sh} = (B_q) ^ I`,

that is, the ring of `I`-invariants of the localization of `B` at `q` is a strict henselization of
`A`. This is the unnumbered step on which the proof of Stacks 0BSW rests.

The ring `B_q` is realized here as the subring `localizedSubring q` of `L` consisting of the
elements with a denominator outside `q`, so that `Gal(L/K)` acts on it by restriction of its
action on `L`; `(B_q) ^ I` is then `inertiaInvariants A K L q`.

The four ingredients are:

* `B_q` is a normal local domain with separably closed fraction field `L`, hence strictly
  henselian by Stacks 0BSQ;
* `I` acts trivially on the residue field of `B_q`, so `(B_q) ^ I` inherits henselianness and
  separable closedness of the residue field, by the Hensel uniqueness of Stacks 06RR — this is
  `StacksFrontier.RingTheory.Henselian.FixedPoints`;
* `(B_q) ^ I` is the localization `C_p` of `C = B ^ I` at the prime `p = q ∩ C`, by the
  commutation of invariants with localization proved in
  `StacksFrontier.RingTheory.Invariant.InertiaLocalization`, so Stacks 0BSU exhibits it as a
  filtered
  colimit of étale `A`-algebras;
* a filtered colimit of étale algebras is weakly étale (Stacks 097N), whence the residue field
  extension is separable (Stacks 092R).

## Main results

* `IsFilteredColimitOfEtaleHom.ind_etale`: a filtered colimit of étale algebras is ind-étale in
  the sense of `CategoryTheory.ObjectProperty.ind`.
* `IsIntegralClosure.localizedSubring`: `B_q` as a subring of `L`.
* `IsIntegralClosure.henselianLocalRing_and_isSepClosed_localizedSubring`: `B_q` is strictly
  henselian.
* `IsIntegralClosure.inertiaInvariants`: the ring `(B_q) ^ I`.
* `IsIntegralClosure.smul_sub_mem_maximalIdeal_localizedSubring`: `I` acts trivially on the
  residue field of `B_q`.
* `IsIntegralClosure.localizationEquivInertiaInvariants`: the identification `C_p ≃ (B_q) ^ I`.
* `IsIntegralClosure.isHenselization_inertiaInvariants`: **`(B_q) ^ I` is a strict henselization
  of `A`.**

## Implementation notes

`IsFractionRing B L` holds because `L / K` is algebraic, but its statement does not mention `K`,
so it cannot be an instance here; it is `IsIntegralClosure.isFractionRing_integralClosure` and is
installed with `letI` in the proofs that need it. In exchange, `localizedSubring` is defined by its
carrier rather than through `Localization.subalgebra.ofField`, which keeps every statement in this
file free of such a side condition.

Strictness is recorded as the pair `IsLocalRing.IsHenselization A κ(R) R` together with
`IsSepClosure κ(A) κ(R)`, rather than through a bespoke predicate: by Stacks 04GQ the first says
that `R` is a henselization of `A` with residue field `κ(R)`, and the second that `κ(R)` is a
separable closure of `κ(A)`. The equality `𝔪_A · R = 𝔪_R` is then automatic by
`CommAlgCat.map_maximalIdeal_of_ind_etale`.

## References

* [Stacks Project, Tag 0BSW](https://stacks.math.columbia.edu/tag/0BSW)
* [Stacks Project, Tag 0BSU](https://stacks.math.columbia.edu/tag/0BSU)
* [Stacks Project, Tag 0BSQ](https://stacks.math.columbia.edu/tag/0BSQ)
* [Stacks Project, Tag 04GQ](https://stacks.math.columbia.edu/tag/04GQ)
* [Stacks Project, Tag 092R](https://stacks.math.columbia.edu/tag/092R)
* [Stacks Project, Tag 097N](https://stacks.math.columbia.edu/tag/097N)

## Tags

strict henselization, inertia group, integral closure, localization, separable closure,
henselian local ring, ind-étale
-/

@[expose] public section

universe u

open IsLocalRing

/-- A ring map exhibited as a filtered colimit of étale algebras is ind-étale in the categorical
sense of `CategoryTheory.ObjectProperty.ind`: the colimit cocone is a colimit presentation, and
`ind` is closed under isomorphism. -/
theorem IsFilteredColimitOfEtaleHom.ind_etale {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : IsFilteredColimitOfEtaleHom (algebraMap R S)) :
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S) := by
  obtain ⟨J, instJ, filtJ, F, hEt, c, ⟨eA⟩, ⟨hc⟩⟩ := h
  rw [toAlgebra_algebraMap] at eA
  exact (CommAlgCat.etale R).ind.prop_of_iso eA ⟨J, instJ, filtJ, ⟨F, c.ι, hc⟩, hEt⟩

namespace IsIntegralClosure

/-! ### The localization at a prime of the integral closure, as a subring of `L` -/

section Localized

variable {A L : Type u} [CommRing A] [Field L] [Algebra A L]
  (q : Ideal (integralClosure A L)) [q.IsPrime]

/-- **The localization `B_q` of the integral closure `B` of `A` in `L` at a prime `q`,
realized as a subring of `L`**: the set of elements of `L` admitting a denominator outside `q`.
This is the shape in which the Galois group acts on it, the action being the restriction of the
action on `L`. -/
def localizedSubring : Subring L where
  carrier := {x : L | ∃ b s : integralClosure A L, s ∉ q ∧ x * (s : L) = (b : L)}
  one_mem' := ⟨1, 1, q.primeCompl.one_mem, by simp⟩
  zero_mem' := ⟨0, 1, q.primeCompl.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨b, s, hs, hbs⟩ ⟨c, t, ht, hct⟩
    refine ⟨b * c, s * t, q.primeCompl.mul_mem hs ht, ?_⟩
    push_cast
    linear_combination (y * (t : L)) * hbs + (b : L) * hct
  add_mem' := by
    rintro x y ⟨b, s, hs, hbs⟩ ⟨c, t, ht, hct⟩
    refine ⟨b * t + c * s, s * t, q.primeCompl.mul_mem hs ht, ?_⟩
    push_cast
    linear_combination (t : L) * hbs + (s : L) * hct
  neg_mem' := by
    rintro x ⟨b, s, hs, hbs⟩
    exact ⟨-b, s, hs, by push_cast; linear_combination -hbs⟩

/-- Membership in `B_q` is having a denominator outside `q`. -/
theorem mem_localizedSubring {x : L} :
    x ∈ localizedSubring q ↔
      ∃ b s : integralClosure A L, s ∉ q ∧ x * (s : L) = (b : L) := Iff.rfl

omit [q.IsPrime] in
/-- An element of the integral closure outside `q` is nonzero in `L`. -/
theorem coe_ne_zero_of_notMem {s : integralClosure A L} (hs : s ∉ q) : (s : L) ≠ 0 :=
  fun h => hs (by simpa using (Subtype.val_injective h : s = 0) ▸ q.zero_mem)

/-- The integral closure is contained in its localization at `q`. -/
theorem coe_mem_localizedSubring (b : integralClosure A L) : (b : L) ∈ localizedSubring q :=
  ⟨b, 1, q.primeCompl.one_mem, by simp⟩

/-- A denominator outside `q` is inverted in `B_q`. -/
theorem inv_coe_mem_localizedSubring {s : integralClosure A L} (hs : s ∉ q) :
    ((s : L))⁻¹ ∈ localizedSubring q :=
  ⟨1, s, hs, by rw [inv_mul_cancel₀ (coe_ne_zero_of_notMem q hs)]; simp⟩

/-- `B_q` is a subring of the field `L`, hence an `L`-algebra source. -/
instance algebraLocalizedSubringField : Algebra (localizedSubring q) L :=
  (localizedSubring q).subtype.toAlgebra

/-- The structure map of `B_q` as an `L`-algebra is the inclusion. -/
theorem algebraMap_localizedSubring_field (x : localizedSubring q) :
    algebraMap (localizedSubring q) L x = (x : L) := rfl

/-- The integral closure maps into its localization at `q`. -/
instance algebraLocalizedSubring : Algebra (integralClosure A L) (localizedSubring q) :=
  (((integralClosure A L).val.toRingHom).codRestrict (localizedSubring q)
    (coe_mem_localizedSubring q)).toAlgebra

/-- The structure map `B → B_q` is the inclusion, read inside `L`. -/
theorem coe_algebraMap_localizedSubring (b : integralClosure A L) :
    ((algebraMap (integralClosure A L) (localizedSubring q) b : localizedSubring q) : L)
      = (b : L) := rfl

/-- `B ⊆ B_q ⊆ L` is a tower. -/
instance : IsScalarTower (integralClosure A L) (localizedSubring q) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **`B_q` is the localization of `B` at `q`.** -/
instance isLocalization_localizedSubring :
    IsLocalization q.primeCompl (localizedSubring q) := by
  rw [isLocalization_iff]
  refine ⟨fun s => ?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · refine isUnit_iff_exists_inv.mpr ⟨⟨((s : integralClosure A L) : L)⁻¹,
      inv_coe_mem_localizedSubring q s.2⟩, Subtype.ext ?_⟩
    change ((s : integralClosure A L) : L) * (((s : integralClosure A L) : L))⁻¹ = 1
    exact mul_inv_cancel₀ (coe_ne_zero_of_notMem q s.2)
  · obtain ⟨b, s, hs, hbs⟩ := z.2
    exact ⟨⟨b, ⟨s, hs⟩⟩, Subtype.ext hbs⟩
  · refine congrArg (fun z : integralClosure A L => ((1 : q.primeCompl) : _) * z) ?_
    exact Subtype.val_injective (congrArg (fun z : localizedSubring q => (z : L)) h)

/-- `B_q` is a local ring, being a localization at a prime. -/
instance isLocalRing_localizedSubring : IsLocalRing (localizedSubring q) :=
  IsLocalization.AtPrime.isLocalRing (localizedSubring q) q

/-- The image in `B_q` of an element of `q` lies in the maximal ideal. -/
theorem algebraMap_mem_maximalIdeal_localizedSubring {b : integralClosure A L} (hb : b ∈ q) :
    algebraMap (integralClosure A L) (localizedSubring q) b
      ∈ maximalIdeal (localizedSubring q) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (localizedSubring q) q b).mpr hb

/-- **A fraction with numerator in `q` lies in the maximal ideal of `B_q`.** -/
theorem mem_maximalIdeal_localizedSubring {x : localizedSubring q}
    {n d : integralClosure A L} (hn : n ∈ q) (hd : d ∉ q)
    (hx : (x : L) * (d : L) = (n : L)) :
    x ∈ maximalIdeal (localizedSubring q) := by
  obtain ⟨v, hv⟩ := IsLocalization.map_units (M := q.primeCompl) (localizedSubring q) ⟨d, hd⟩
  have hxd : x * algebraMap (integralClosure A L) (localizedSubring q) d
      = algebraMap (integralClosure A L) (localizedSubring q) n := Subtype.ext hx
  have hvd : (v : localizedSubring q)
      = algebraMap (integralClosure A L) (localizedSubring q) d := hv
  have hx' : x = algebraMap (integralClosure A L) (localizedSubring q) n * (↑v⁻¹) := by
    rw [← hxd, ← hvd, mul_assoc, v.mul_inv, mul_one]
  rw [hx']
  exact (maximalIdeal (localizedSubring q)).mul_mem_right _
    (algebraMap_mem_maximalIdeal_localizedSubring q hn)

end Localized

/-! ### `B_q` is strictly henselian -/

section Galois

open scoped Pointwise

variable (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]

attribute [local instance] galAction galSMulCommClass

include K in
omit [IsIntegrallyClosed A] in
/-- `L` is the fraction field of the integral closure of `A` in `L`, the extension `L / K` being
algebraic. -/
theorem isFractionRing_integralClosure : IsFractionRing (integralClosure A L) L := by
  have : Algebra.IsAlgebraic A L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K L)
  exact integralClosure.isFractionRing_of_algebraic fun _ hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero (algebraMap K L)).mp <| (IsScalarTower.algebraMap_apply A K L _).symm.trans hx)

include K in
omit [IsIntegrallyClosed A] in
/-- `L` is the fraction field of `B_q` as well. -/
theorem isFractionRing_localizedSubring (q : Ideal (integralClosure A L)) [q.IsPrime] :
    IsFractionRing (localizedSubring q) L :=
  let := isFractionRing_integralClosure A K L
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl
    (localizedSubring q) L

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- `B_q` is a normal domain: it is a localization of the integrally closed domain `B`. -/
theorem isIntegrallyClosed_localizedSubring (q : Ideal (integralClosure A L)) [q.IsPrime] :
    IsIntegrallyClosed (localizedSubring q) :=
  let : IsIntegrallyClosed (integralClosure A L) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure A L) L
  isIntegrallyClosed_of_isLocalization (localizedSubring q) q.primeCompl
    q.primeCompl_le_nonZeroDivisors

include K in
omit [IsIntegrallyClosed A] in
/-- **`B_q` is a strictly henselian local ring** when `L` is separably closed: it is a normal
local domain whose fraction field `L` is separably closed, which is Stacks 0BSQ. -/
theorem henselianLocalRing_and_isSepClosed_localizedSubring [IsSepClosed L]
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    HenselianLocalRing (localizedSubring q) ∧
      IsSepClosed (ResidueField (localizedSubring q)) :=
  let := isFractionRing_localizedSubring A K L q
  let := isIntegrallyClosed_localizedSubring A L q
  _root_.normal_local_domain_sepClosed_fractionField_isStrictlyHenselian
    (localizedSubring q) L

/-! ### The inertia action on `B_q` -/

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- **`B_q` is stable under an automorphism stabilizing `q`**, since `σ (b / s) = σ b / σ s`. -/
theorem smul_mem_localizedSubring (q : Ideal (integralClosure A L)) [q.IsPrime]
    {σ : Gal(L/K)} (hσ : σ • q = q) {x : L} (hx : x ∈ localizedSubring q) :
    σ x ∈ localizedSubring q := by
  obtain ⟨b, s, hs, hbs⟩ := hx
  refine ⟨σ • b, σ • s, notMem_smul_of_notMem A K L hσ hs, ?_⟩
  rw [coe_smul A K L, coe_smul A K L, ← map_mul, hbs]

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The inertia subgroup at `q` stabilizes `q`. -/
theorem inertia_smul_eq (q : Ideal (integralClosure A L)) [q.IsPrime]
    (σ : q.inertia Gal(L/K)) : (σ : Gal(L/K)) • q = q :=
  MulAction.mem_stabilizer_iff.mp (q.inertia_le_stabilizer σ.2)

/-- **The inertia group acts on `B_q`**, by restriction of its action on `L`. -/
noncomputable instance mulSemiringActionLocalizedSubring
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    _root_.MulSemiringAction (q.inertia Gal(L/K)) (localizedSubring q) :=
  Subring.mulSemiringActionOfStable (M := (q.inertia Gal(L/K))) (localizedSubring q)
    fun σ _ hx => smul_mem_localizedSubring A K L q (inertia_smul_eq A K L q σ) hx

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The action of the inertia group on `B_q` is the restriction of its action on `L`. -/
theorem coe_smul_localizedSubring (q : Ideal (integralClosure A L)) [q.IsPrime]
    (σ : q.inertia Gal(L/K)) (x : localizedSubring q) :
    ((σ • x : localizedSubring q) : L) = (σ : Gal(L/K)) (x : L) := rfl

/-- **`((A^sep)_{𝔪^sep})^I`**: the inertia invariants of the localization at `q` of the integral
closure of `A` in `L`. -/
noncomputable abbrev inertiaInvariants (q : Ideal (integralClosure A L)) [q.IsPrime] :
    Subring (localizedSubring q) :=
  FixedPoints.subring (localizedSubring q) (q.inertia Gal(L/K))

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- **The inertia group acts trivially on the residue field of `B_q`.** For `σ` in the inertia
group, `σ (b / s) - b / s = ((σ b - b) s + b (s - σ s)) / (s · σ s)`, whose numerator lies in `q`
and whose denominator lies outside `q`. -/
theorem smul_sub_mem_maximalIdeal_localizedSubring (q : Ideal (integralClosure A L)) [q.IsPrime]
    (σ : q.inertia Gal(L/K)) (x : localizedSubring q) :
    σ • x - x ∈ maximalIdeal (localizedSubring q) := by
  obtain ⟨b, s, hs, hbs⟩ := x.2
  have hb : (σ : Gal(L/K)) • b - b ∈ q := Ideal.mem_inertia.mp σ.2 b
  have hs' : s - (σ : Gal(L/K)) • s ∈ q := by
    simpa using q.neg_mem (Ideal.mem_inertia.mp σ.2 s)
  have hσbs : (σ : Gal(L/K)) (x : L) * (σ : Gal(L/K)) (s : L)
      = (σ : Gal(L/K)) (b : L) := by rw [← map_mul, hbs]
  refine mem_maximalIdeal_localizedSubring q
    (n := ((σ : Gal(L/K)) • b - b) * s + b * (s - (σ : Gal(L/K)) • s))
    (d := s * ((σ : Gal(L/K)) • s))
    (q.add_mem (q.mul_mem_right _ hb) (q.mul_mem_left _ hs'))
    (q.primeCompl.mul_mem hs (notMem_smul_of_notMem A K L (inertia_smul_eq A K L q σ) hs)) ?_
  push_cast [coe_smul_localizedSubring, coe_smul A K L]
  linear_combination ((s : L)) * hσbs - ((σ : Gal(L/K)) (s : L)) * hbs

/-- `R = (B_q)^I` is a local ring. -/
instance isLocalRing_inertiaInvariants (q : Ideal (integralClosure A L)) [q.IsPrime] :
    IsLocalRing (inertiaInvariants A K L q) :=
  Stacks.FixedPoints.isLocalRing _ _

include K in
omit [IsIntegrallyClosed A] in
/-- **`R = (B_q)^I` is henselian**, by Stacks 06RR applied inside the strictly henselian ring
`B_q` on which `I` acts trivially modulo the maximal ideal. -/
theorem henselianLocalRing_inertiaInvariants [IsSepClosed L]
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    HenselianLocalRing (inertiaInvariants A K L q) :=
  let := (henselianLocalRing_and_isSepClosed_localizedSubring A K L q).1
  Stacks.FixedPoints.henselianLocalRing _ _
    (smul_sub_mem_maximalIdeal_localizedSubring A K L q)

include K in
omit [IsIntegrallyClosed A] in
/-- **The residue field of `R = (B_q)^I` is separably closed.** -/
theorem isSepClosed_residueField_inertiaInvariants [IsSepClosed L]
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    IsSepClosed (ResidueField (inertiaInvariants A K L q)) :=
  let := (henselianLocalRing_and_isSepClosed_localizedSubring A K L q).1
  let := (henselianLocalRing_and_isSepClosed_localizedSubring A K L q).2
  Stacks.FixedPoints.isSepClosed_residueField _ _
    (smul_sub_mem_maximalIdeal_localizedSubring A K L q)

/-! ### `(B_q)^I` is the localization of `B^I` at the prime below `q` -/

/-- `C = B ^ I`, the inertia invariants of the integral closure: the ring whose localization
Stacks 0BSU exhibits as a filtered colimit of étale `A`-algebras. -/
noncomputable abbrev inertiaFixedSubalgebra (q : Ideal (integralClosure A L)) [q.IsPrime] :
    Subalgebra A (integralClosure A L) :=
  FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K))

/-- The inclusion of `C = B ^ I` into `B_q`. -/
noncomputable def fixedToLocalized (q : Ideal (integralClosure A L)) [q.IsPrime] :
    inertiaFixedSubalgebra A K L q →+* localizedSubring q :=
  (algebraMap (integralClosure A L) (localizedSubring q)).comp
    (inertiaFixedSubalgebra A K L q).val.toRingHom

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The inclusion `C → B_q` is the inclusion, read inside `L`. -/
theorem coe_fixedToLocalized (q : Ideal (integralClosure A L)) [q.IsPrime]
    (c : inertiaFixedSubalgebra A K L q) :
    ((fixedToLocalized A K L q c : localizedSubring q) : L)
      = ((c : integralClosure A L) : L) := rfl

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The inclusion `C → B_q` is injective, both rings sitting inside `L`. -/
theorem fixedToLocalized_injective (q : Ideal (integralClosure A L)) [q.IsPrime] :
    Function.Injective (fixedToLocalized A K L q) := fun _ _ h =>
  Subtype.val_injective (Subtype.val_injective
    (congrArg (fun z : localizedSubring q => (z : L)) h))

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- A denominator of `C` outside `p = q ∩ C` becomes a unit in `B_q`. -/
theorem isUnit_fixedToLocalized (q : Ideal (integralClosure A L)) [q.IsPrime]
    (t : (q.comap (inertiaFixedSubalgebra A K L q).val).primeCompl) :
    IsUnit (fixedToLocalized A K L q t) :=
  IsLocalization.map_units (M := q.primeCompl) (localizedSubring q)
    ⟨((t : inertiaFixedSubalgebra A K L q) : integralClosure A L), t.2⟩

/-- **The canonical map `C_p → B_q`**, obtained from the inclusion `C → B_q` by inverting the
elements outside `p = q ∩ C`. -/
noncomputable def localizationToLocalizedSubring (q : Ideal (integralClosure A L))
    [q.IsPrime] :
    Localization.AtPrime (q.comap (inertiaFixedSubalgebra A K L q).val) →+*
      localizedSubring q :=
  IsLocalization.lift (isUnit_fixedToLocalized A K L q)

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The defining property of `C_p → B_q` on a fraction. -/
theorem localizationToLocalizedSubring_mk'_spec (q : Ideal (integralClosure A L)) [q.IsPrime]
    (c : inertiaFixedSubalgebra A K L q) (v : localizedSubring q)
    (t : (q.comap (inertiaFixedSubalgebra A K L q).val).primeCompl) :
    localizationToLocalizedSubring A K L q (IsLocalization.mk' _ c t) = v
      ↔ fixedToLocalized A K L q c = fixedToLocalized A K L q t * v :=
  IsLocalization.lift_mk'_spec (isUnit_fixedToLocalized A K L q) c v t

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- `C_p → B_q` is injective: `C → B_q` is, and the denominators of `p` are already inverted
in `B_q`. -/
theorem localizationToLocalizedSubring_injective (q : Ideal (integralClosure A L))
    [q.IsPrime] : Function.Injective (localizationToLocalizedSubring A K L q) := by
  rw [localizationToLocalizedSubring, IsLocalization.lift_injective_iff]
  refine fun x y => ⟨fun h => ?_, fun h => congrArg _ (fixedToLocalized_injective A K L q h)⟩
  simpa using congrArg (IsLocalization.lift (isUnit_fixedToLocalized A K L q)) h

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- Membership in `(B_q)^I` is being fixed by the inertia group inside `L`. -/
theorem mem_inertiaInvariants_iff (q : Ideal (integralClosure A L)) [q.IsPrime]
    (x : localizedSubring q) :
    x ∈ inertiaInvariants A K L q ↔ ∀ σ ∈ q.inertia Gal(L/K), σ (x : L) = (x : L) :=
  ⟨fun hx σ hσ => congrArg (fun z : localizedSubring q => (z : L)) (hx ⟨σ, hσ⟩),
    fun hx σ => Subtype.ext (hx σ σ.2)⟩

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- **The image of `C_p` in `B_q` is exactly `(B_q)^I`.** The inclusion `⊆` is that `C` and its
denominators are inertia-invariant; the inclusion `⊇` is the commutation of invariants with
localization, `IsIntegralClosure.exists_inertia_invariant_num_den`. -/
theorem mem_range_localizationToLocalizedSubring (q : Ideal (integralClosure A L))
    [q.IsPrime] (x : localizedSubring q) :
    x ∈ Set.range (localizationToLocalizedSubring A K L q)
      ↔ x ∈ inertiaInvariants A K L q := by
  have hnum : ∃ b s : integralClosure A L, s ∉ q ∧ (x : L) * (s : L) = (b : L) := x.2
  have hcomm := exists_inertia_invariant_num_den A K L q (x : L)
  rw [mem_inertiaInvariants_iff]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨c, t, hzt⟩ :=
      IsLocalization.exists_mk'_eq (q.comap (inertiaFixedSubalgebra A K L q).val).primeCompl z
    rw [← hzt] at hz
    have hspec := (localizationToLocalizedSubring_mk'_spec A K L q c x t).mp hz
    refine (hcomm.mpr ⟨c, (t : inertiaFixedSubalgebra A K L q), t.2, ?_⟩).2
    have hval := congrArg (fun y : localizedSubring q => (y : L)) hspec
    push_cast [coe_fixedToLocalized] at hval
    linear_combination -hval
  · intro hfix
    obtain ⟨c, t, ht, hct⟩ := hcomm.mp ⟨hnum, hfix⟩
    refine ⟨_, (localizationToLocalizedSubring_mk'_spec A K L q c x ⟨t, ht⟩).mpr
      (Subtype.ext ?_)⟩
    push_cast [coe_fixedToLocalized]
    linear_combination -hct

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The inclusion `C → B_q` lands in `(B_q)^I`, because `C` is inertia-invariant. -/
theorem fixedToLocalized_mem_inertiaInvariants (q : Ideal (integralClosure A L)) [q.IsPrime]
    (c : inertiaFixedSubalgebra A K L q) :
    fixedToLocalized A K L q c ∈ inertiaInvariants A K L q := by
  rw [mem_inertiaInvariants_iff]
  intro σ hσ
  have hc := c.2 ⟨σ, hσ⟩
  rw [coe_fixedToLocalized, ← coe_smul A K L σ]
  exact congrArg (fun z : integralClosure A L => (z : L)) hc

/-- The structure map `A → (B_q)^I`, the restriction of `A → L`. -/
noncomputable instance algebraInertiaInvariants (q : Ideal (integralClosure A L))
    [q.IsPrime] : Algebra A (inertiaInvariants A K L q) :=
  (((fixedToLocalized A K L q).codRestrict (inertiaInvariants A K L q)
      (fixedToLocalized_mem_inertiaInvariants A K L q)).comp
    (algebraMap A (inertiaFixedSubalgebra A K L q))).toAlgebra

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The structure map `A → (B_q)^I` is the structure map `A → L`, read inside `L`. -/
theorem coe_algebraMap_inertiaInvariants (q : Ideal (integralClosure A L)) [q.IsPrime] (a : A) :
    (((algebraMap A (inertiaInvariants A K L q) a : inertiaInvariants A K L q) :
        localizedSubring q) : L)
      = algebraMap A L a := rfl

/-- **`C_p ≃ (B_q)^I`**: the localization of the inertia invariants of `B` at the prime below
`q` is the ring of inertia invariants of `B_q`. -/
noncomputable def localizationEquivInertiaInvariants (q : Ideal (integralClosure A L))
    [q.IsPrime] :
    Localization.AtPrime (q.comap (inertiaFixedSubalgebra A K L q).val) ≃+*
      inertiaInvariants A K L q :=
  RingEquiv.ofBijective
    ((localizationToLocalizedSubring A K L q).codRestrict (inertiaInvariants A K L q)
      fun z => (mem_range_localizationToLocalizedSubring A K L q _).mp ⟨z, rfl⟩)
    ⟨fun _ _ h => localizationToLocalizedSubring_injective A K L q
        (congrArg (fun z : inertiaInvariants A K L q => (z : localizedSubring q)) h),
      fun y => by
        obtain ⟨z, hz⟩ := (mem_range_localizationToLocalizedSubring A K L q _).mpr y.2
        exact ⟨z, Subtype.ext hz⟩⟩

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The identification `C_p ≃ (B_q)^I` is an identification of `A`-algebras. -/
theorem localizationEquivInertiaInvariants_algebraMap (q : Ideal (integralClosure A L))
    [q.IsPrime] (a : A) :
    localizationEquivInertiaInvariants A K L q
        (((algebraMap (inertiaFixedSubalgebra A K L q)
            (Localization.AtPrime (q.comap (inertiaFixedSubalgebra A K L q).val))).comp
          (algebraMap A (inertiaFixedSubalgebra A K L q))) a)
      = algebraMap A (inertiaInvariants A K L q) a := by
  refine Subtype.ext ?_
  change localizationToLocalizedSubring A K L q
      (algebraMap (inertiaFixedSubalgebra A K L q) _
        (algebraMap A (inertiaFixedSubalgebra A K L q) a)) = _
  rw [localizationToLocalizedSubring, IsLocalization.lift_eq]
  rfl

include K in
/-- **`(B_q)^I` is a filtered colimit of étale `A`-algebras**, by transporting Stacks 0BSU along
the identification `C_p ≃ (B_q)^I`. -/
theorem isFilteredColimitOfEtaleHom_inertiaInvariants (q : Ideal (integralClosure A L))
    [q.IsPrime] :
    IsFilteredColimitOfEtaleHom (algebraMap A (inertiaInvariants A K L q)) :=
  IsFilteredColimitOfEtaleHom.transport
    (isFilteredColimitOfEtale_localization_fixedPoints_inertia A K L q inferInstance)
    (localizationEquivInertiaInvariants A K L q)
    (localizationEquivInertiaInvariants_algebraMap A K L q)

/-! ### `(B_q)^I` is a strict henselization of `A` -/

variable [IsLocalRing A]

/-- **The structure map `A → (B_q)^I` is a local ring map**, because `q` lies over the maximal
ideal of `A`. -/
instance isLocalHom_algebraMap_inertiaInvariants (q : Ideal (integralClosure A L)) [q.IsPrime]
    [q.LiesOver (maximalIdeal A)] :
    IsLocalHom (algebraMap A (inertiaInvariants A K L q)) := by
  refine ⟨fun a hu => ?_⟩
  by_contra hna
  have haM : a ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).mpr hna
  rw [Ideal.LiesOver.over (P := q) (p := maximalIdeal A)] at haM
  have hmem : ((algebraMap A (inertiaInvariants A K L q) a : inertiaInvariants A K L q) :
      localizedSubring q) ∈ maximalIdeal (localizedSubring q) :=
    mem_maximalIdeal_localizedSubring q (n := algebraMap A (integralClosure A L) a) (d := 1)
      haM q.primeCompl.one_mem (by simp [coe_algebraMap_inertiaInvariants])
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
    (Stacks.FixedPoints.isUnit_val_iff.mpr hu)

/-- The identification of the residue field of a local ring with the residue field of its maximal
ideal. -/
private noncomputable abbrev residueFieldEquiv (S : Type u) [CommRing S] [IsLocalRing S] :
    ResidueField S ≃+* (maximalIdeal S).ResidueField :=
  RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal S))

include K in
/-- **The residue field of `(B_q)^I` is separable over that of `A`.** The structure map is a
filtered colimit of étale algebras, hence weakly étale by Stacks 097N, and Stacks 092R gives
separability of the residue field extension at the maximal ideals. -/
theorem isSeparable_residueField_inertiaInvariants (q : Ideal (integralClosure A L))
    [q.IsPrime] [q.LiesOver (maximalIdeal A)] :
    Algebra.IsSeparable (ResidueField A) (ResidueField (inertiaInvariants A K L q)) := by
  have hw : Algebra.WeaklyEtale A (inertiaInvariants A K L q) :=
    Algebra.weaklyEtale_of_ind_etale (StacksDraft.indEtale_iff.mpr
      (isFilteredColimitOfEtaleHom_inertiaInvariants A K L q).ind_etale)
  have hpq : maximalIdeal A
      = (maximalIdeal (inertiaInvariants A K L q)).comap
          (algebraMap A (inertiaInvariants A K L q)) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap A (inertiaInvariants A K L q))).symm
  let : Algebra (maximalIdeal A).ResidueField
      (maximalIdeal (inertiaInvariants A K L q)).ResidueField :=
    (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal (inertiaInvariants A K L q))
      (algebraMap A (inertiaInvariants A K L q)) hpq).toAlgebra
  have := (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A
    (inertiaInvariants A K L q) hw (maximalIdeal A)
    (maximalIdeal (inertiaInvariants A K L q)) hpq).1
  -- The two descriptions of the residue field of a local ring agree, compatibly.
  let eA := residueFieldEquiv A
  let eR := residueFieldEquiv (inertiaInvariants A K L q)
  have hkey : ∀ w : ResidueField A,
      eR (algebraMap (ResidueField A) (ResidueField (inertiaInvariants A K L q)) w)
        = algebraMap (maximalIdeal A).ResidueField
            (maximalIdeal (inertiaInvariants A K L q)).ResidueField (eA w) := by
    intro w
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) w
    change algebraMap (inertiaInvariants A K L q)
        (maximalIdeal (inertiaInvariants A K L q)).ResidueField
        (algebraMap A (inertiaInvariants A K L q) a)
      = Ideal.ResidueField.map (maximalIdeal A)
          (maximalIdeal (inertiaInvariants A K L q))
          (algebraMap A (inertiaInvariants A K L q)) hpq
          (algebraMap A (maximalIdeal A).ResidueField a)
    rw [Ideal.ResidueField.map_algebraMap]
  refine Algebra.IsSeparable.of_equiv_equiv eA.symm eR.symm (RingHom.ext fun z => ?_)
  obtain ⟨w, rfl⟩ := eA.surjective z
  change algebraMap (ResidueField A) (ResidueField (inertiaInvariants A K L q))
      (eA.symm (eA w))
    = eR.symm (algebraMap (maximalIdeal A).ResidueField
        (maximalIdeal (inertiaInvariants A K L q)).ResidueField (eA w))
  rw [eA.symm_apply_apply, ← hkey w, eR.symm_apply_apply]

include K in
/-- **`A^{sh} = ((A^{sep})_{𝔪^{sep}})^I`.** Let `A` be a normal local domain with fraction field
`K`, let `L / K` be a Galois extension with `L` separably closed — so that `L` is a separable
closure of `K` — and let `B` be the integral closure of `A` in `L`. For a prime `q` of `B` lying
over the maximal ideal of `A`, with inertia group `I = q.inertia Gal(L/K)`, the ring of
`I`-invariants of `B_q` is a strict henselization of `A`: it is a henselization of `A` with
residue field its own residue field, and that residue field is a separable closure of the residue
field of `A`.

This is the unnumbered step of the proof of Stacks 0BSW. Henselianness and separable closedness
of the residue field come from `B_q` being strictly henselian (Stacks 0BSQ) together with the
inertia group acting trivially on its residue field (Stacks 06RR); being a filtered colimit of
étale `A`-algebras is Stacks 0BSU transported along `C_p ≃ (B_q)^I`; and separability of the
residue field extension follows from that colimit presentation by Stacks 097N and 092R. -/
theorem isHenselization_inertiaInvariants [IsSepClosed L]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver (maximalIdeal A)] :
    IsLocalRing.IsHenselization A (ResidueField (inertiaInvariants A K L q))
        (inertiaInvariants A K L q) ∧
      IsSepClosure (ResidueField A) (ResidueField (inertiaInvariants A K L q)) :=
  ⟨IsLocalRing.IsHenselization.of_ind_etale
      (henselianLocalRing_inertiaInvariants A K L q)
      (isFilteredColimitOfEtaleHom_inertiaInvariants A K L q).ind_etale
      ⟨RingEquiv.refl _, fun x => IsLocalRing.ResidueField.algebraMap_residue x⟩,
    ⟨isSepClosed_residueField_inertiaInvariants A K L q,
      isSeparable_residueField_inertiaInvariants A K L q⟩⟩

end Galois

end IsIntegralClosure
