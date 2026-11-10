module

public import Mathlib.RingTheory.Etale.Locus
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.Flat.AdicFiltration
public import StacksFrontier.RingTheory.Flat.FlatLocusAway
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Rig.Henselization
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of a map of completions to the henselization (Stacks 0AKJ)

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` a finite type `A`-algebra which is étale
over `Spec(A) ∖ V(I)`, and `C` a Noetherian `A`-algebra.  Stacks 0AKJ says that every
`A`-algebra map `B^∧ → C^∧` of `I`-adic completions comes from a *unique* `A`-algebra map
`B → Cʰ`, where `Cʰ = henselization C (IC)` is the henselization of the pair `(C, IC)`.  This
file proves that `∃!`, both halves.

Uniqueness is the shorter half.  Let `R` be Noetherian and `I ⊆ R`.  Stacks 0AGV says that
`Rʰ` is Noetherian and that `Rʰ → R^∧` is faithfully flat; in particular `Rʰ` is a subring of
`R^∧`.  The route to that injectivity is short but it needs one thing that was missing.
Stacks 0AGV is available as `henselization_isNoetherian_and_completion_equiv`, stated for an
*arbitrary* `Rʰ` that is henselian over `(R, I)` **and satisfies the universal property**, and
the universal property of the canonical `henselization R I` was nowhere available: it occurs
only inside the existential of `@[stacks 0A02] exists_henselization`, and the maps realising it
(`toHenselian`, `toHenselian_unique`) are `private`.  So the first result below recovers it
from the existential, by transporting along the uniqueness of henselizations
(`nonempty_algEquiv_henselization`).  With that in hand, `henselization R I` is Noetherian,
`I·Rʰ` lies in the Jacobson radical because `(Rʰ, I·Rʰ)` is a henselian pair, so the Krull
intersection theorem makes `Rʰ` `I`-adically separated, and `Rʰ → (Rʰ)^∧ ≅ R^∧` is injective.
A map `B → Rʰ` is then determined by the induced map `B → B^∧ → R^∧`.

Existence is the long half, and it is proved here rather than following the source's own
route.  The source reduces to the case `A = C` by replacing `(A, I, B, C, φ)` with
`(C, IC, B ⊗_A C, C, σ)` and then runs a naive-cotangent computation; this file performs the
same reduction but reaches the hypothesis of Stacks 0ALR directly.  Write `D = C ⊗_A B` and
`T = C^∧`.  Étaleness of `B` off `V(I)` puts `Ω_{B/A}` in the support of `V(IB)`, so a power
`I^c` annihilates it (Stacks 0ALQ is the same computation, for `Ω` and `H¹(L)` together);
base change along `A → C` carries that to `(IC)^c · Ω_{D/C} = 0`.  Given that annihilation,
a `C`-algebra map `f : D → T` is lifted to `Cʰ` as follows.  The map extends to the completion
as `φ : D^∧ → T`, which is split by the completion map `σ : T → D^∧`, hence surjective; the
splitting turns the annihilation of `Ω` into annihilation of the conormal module
`Ker(φ)/Ker(φ)²` by `I^c`, which is exactly the hypothesis of **Stacks 0ALR**
(`exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated`).  So `T ≅ E^∧` for a
finite type `C`-algebra `E`.  Since `C^∧ ≅ E^∧` is an isomorphism, `C → E` is bijective
modulo every power of `IC`; flatness over a basic open and the vanishing of `Ω_{E/C}` near
`V(IE)` then produce `g ∈ 1 + IE` with `E_g` étale over `C` — and an étale `C`-algebra mapping
to `C^∧` lifts to `Cʰ`, because `(Cʰ, ICʰ)` is a henselian pair and the lift is unique by
formal unramifiedness.  Restricting that lift along `B → D` gives the required `B → Cʰ`.

## Main results

* `henselization_universalProperty`: the universal property of the canonical henselization,
  **Stacks 0A02** for `henselization R I` itself rather than for an unnamed witness.
* `isNoetherianRing_henselization`: **Stacks 0AGV**, the Noetherian half, for the canonical
  henselization.
* `isHausdorff_map_algebraMap_henselization`: the henselization of a Noetherian pair is
  `I`-adically separated.
* `Rig.injective_henselizationToAdicCompletion`: **`Rʰ → R^∧` is injective** — Stacks 0AGV's
  "`Rʰ` is a subring of `R^∧`", for the map `Rig.henselizationToAdicCompletion`.
* `Rig.eq_of_henselizationToAdicCompletion_comp_eq`: the uniqueness half of Stacks 0AKJ.
* `Rig.exists_algHom_henselization_of_annihilator_kaehlerDifferential`: the existence half,
  in the reduced form `A = C` — a finite type algebra whose differentials are annihilated by
  a power of `I` maps to `Rʰ` compatibly with any given map to `R^∧`.
* `Rig.exists_unique_algHom_henselization_of_algHom_adicCompletion`: the same descent, for an
  `A`-algebra map `B → C^∧` not assumed to extend over `B^∧`.
* `Rig.exists_unique_algHom_henselization_of_adicCompletion`: **Stacks 0AKJ**, descent and
  uniqueness as the single `∃!` the source states.

## Implementation notes

Stacks 0AKJ states descent as a single `∃!`, so uniqueness cannot be tagged apart from
existence: the tag sits on
`Rig.exists_unique_algHom_henselization_of_adicCompletion`, which carries both halves.  The
source's final assertion — that a map to `Cʰ` factors through an étale neighbourhood of the
closed fibre — is a separate statement and is tagged separately, on
`Rig.exists_etale_factorization_algHom_henselization` in
`StacksFrontier.RingTheory.Rig.Henselization`.

The hypothesis "`Spec(B) → Spec(A)` is étale over `Spec(A) ∖ V(I)`" is the library's
`Rig.IsEtaleOutside`, from `StacksFrontier.RingTheory.Rig.RigEtaleLocus`, which is also the
hypothesis of Stacks 0ALQ.  Only the consequence that a power of `IB` annihilates `Ω_{B/A}`
is used; `H¹(L_{B/A})` plays no part, because Stacks 0ALR is reached through the conormal
module of a *split* surjection rather than through the naive cotangent complex.

`henselization_universalProperty` is stated in exactly the shape that
`nonempty_algEquiv_henselization` and
`henselization_isNoetherian_and_completion_equiv` consume — with `CommRing B` an explicit
argument rather than an instance — so that it plugs into them with no adaptation.  Its
target universe is forced to be that of `R`, which is all those two consumers need since
they quantify over `Type (max u v)` and the canonical henselization lives in `Type u`.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
* [Stacks Project, Tag 0AGV](https://stacks.math.columbia.edu/tag/0AGV)
* [Stacks Project, Tag 0AKJ](https://stacks.math.columbia.edu/tag/0AKJ)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0ALR](https://stacks.math.columbia.edu/tag/0ALR)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-! ## The universal property of the canonical henselization -/

/-- If `g ∘ a = f` and `f` carries `I` into `J`, then `g` carries `I.map a` into `J`. -/
private theorem map_le_comap_of_comp_eq {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    {I : Ideal R} {J : Ideal B} {f : R →+* B} (hf : I ≤ J.comap f) (a : R →+* S) (g : S →+* B)
    (h : g.comp a = f) : I.map a ≤ J.comap g :=
  by subst h; exact Ideal.map_le_iff_le_comap.mpr hf

/-- **Stacks 0A02 for the canonical henselization.**  `henselization R I` is initial among
henselian pairs under `(R, I)`: for every henselian pair `(B, J)` and every `R → B` carrying
`I` into `J` there is a unique `R`-algebra map `henselization R I → B` compatible with `J`.

The statement of `exists_henselization` hides this behind an existential over the
henselization, and the maps realising it are `private`; this recovers it for the named
construction by transporting the existential witness's universal property along the
`R`-algebra equivalence of `nonempty_algEquiv_henselization`.  The shape — `CommRing B` an
explicit argument — is the one `nonempty_algEquiv_henselization` and
`henselization_isNoetherian_and_completion_equiv` take as a hypothesis. -/
public theorem henselization_universalProperty (R : Type u) [CommRing R] (I : Ideal R) :
    ∀ (B : Type u) (_ : CommRing B) (J : Ideal B), HenselianPair B J →
      ∀ f : R →+* B, I ≤ J.comap f →
        ∃! g : (henselization R I : Type u) →+* B,
          g.comp (algebraMap R (henselization R I : Type u)) = f ∧
            I.map (algebraMap R (henselization R I : Type u)) ≤ J.comap g := by
  obtain ⟨Ah, instAh, ι, hh, hup⟩ := exists_henselization.{u, u} R I
  let : CommRing Ah := instAh
  let : Algebra R Ah := ι.toAlgebra
  have hmap : (algebraMap R Ah) = ι := rfl
  obtain ⟨e⟩ := nonempty_algEquiv_henselization R I Ah (hmap ▸ hh)
    (fun C instC K hK g hg => hmap ▸ hup C instC K hK g hg)
  have hcomp : (e.toRingEquiv.toRingHom).comp
      (algebraMap R (henselization R I : Type u)) = ι :=
    RingHom.ext fun r => e.commutes r
  have hsymm : (e.symm.toRingEquiv.toRingHom).comp ι =
      algebraMap R (henselization R I : Type u) :=
    RingHom.ext fun r => e.symm.commutes r
  intro B instB J hB f hf
  let : CommRing B := instB
  obtain ⟨g, ⟨hg₁, -⟩, hguniq⟩ := hup B instB J hB f hf
  have h₁ : (g.comp e.toRingEquiv.toRingHom).comp
      (algebraMap R (henselization R I : Type u)) = f := by
    rw [RingHom.comp_assoc, hcomp, hg₁]
  refine ⟨g.comp e.toRingEquiv.toRingHom, ⟨h₁, map_le_comap_of_comp_eq hf _ _ h₁⟩, ?_⟩
  · rintro G ⟨hG₁, -⟩
    have hGe : G.comp e.symm.toRingEquiv.toRingHom = g := by
      have h₂ : (G.comp e.symm.toRingEquiv.toRingHom).comp ι = f := by
        rw [RingHom.comp_assoc, hsymm, hG₁]
      exact hguniq _ ⟨h₂, map_le_comap_of_comp_eq hf _ _ h₂⟩
    rw [← hGe, RingHom.comp_assoc]
    refine (RingHom.ext fun x => ?_).symm
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact congrArg G (e.symm_apply_apply x)

/-- **Stacks 0AGV, the Noetherian half, for the canonical henselization.**  The henselization
of a pair `(R, I)` with `R` Noetherian is again Noetherian. -/
@[sga "4 VIII 4.1" "more general"]
public theorem isNoetherianRing_henselization (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (henselization R I : Type u) :=
  (henselization_isNoetherian_and_completion_equiv R I (henselization R I : Type u)
    (henselianPair_henselization R I) (henselization_universalProperty R I)).2.1

/-- **The henselization of a Noetherian pair is `I`-adically separated.**  `(Rʰ, I·Rʰ)` is a
henselian pair, so `I·Rʰ` lies in the Jacobson radical of `Rʰ`, and `Rʰ` is Noetherian; the
Krull intersection theorem then gives `⋂ₙ (I·Rʰ)ⁿ = 0`. -/
public theorem isHausdorff_map_algebraMap_henselization (R : Type u) [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) :
    IsHausdorff (I.map (algebraMap R (henselization R I : Type u)))
      (henselization R I : Type u) := by
  have := isNoetherianRing_henselization R I
  exact IsHausdorff.of_le_jacobson _ _ (henselianPair_henselization R I).le_jacobson

namespace Rig

/-! ## `Rʰ → R^∧` is injective -/

/-- The canonical map of `Rig.toAdicCompletionOfBijective` is injective as soon as the
algebra is adically separated: the map is the structural map `B → B^∧` followed by the
inverse of the comparison isomorphism `R^∧ ≅ B^∧`. -/
public theorem injective_toAdicCompletionOfBijective {R : Type u} {B : Type v} [CommRing R]
    [CommRing B] [Algebra R B] (I : Ideal R)
    (hb : Function.Bijective
      (adicCompletionMap (algebraMap R B) I (I.map (algebraMap R B)) le_rfl))
    [IsHausdorff (I.map (algebraMap R B)) B] :
    Function.Injective (toAdicCompletionOfBijective I hb) := by
  intro x y hxy
  unfold toAdicCompletionOfBijective at hxy
  simp only [AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply] at hxy
  exact AdicCompletion.of_injective _ _ ((RingEquiv.ofBijective _ hb).symm.injective hxy)

/-- **Stacks 0AGV: `Rʰ` is a subring of `R^∧`.**  For a Noetherian ring `R` and an ideal
`I ⊆ R`, the canonical map `Rig.henselizationToAdicCompletion` from the henselization of the
pair `(R, I)` to the `I`-adic completion of `R` is injective.

The source gets this from faithful flatness; here it is the adic separatedness of `Rʰ`
(`isHausdorff_map_algebraMap_henselization`), which is what injectivity of `Rʰ → (Rʰ)^∧`
amounts to, composed with the comparison isomorphism `R^∧ ≅ (Rʰ)^∧`. -/
public theorem injective_henselizationToAdicCompletion (R : Type u) [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) :
    Function.Injective (henselizationToAdicCompletion R I).val := by
  have := isHausdorff_map_algebraMap_henselization R I
  unfold henselizationToAdicCompletion
  exact injective_toAdicCompletionOfBijective I _

/-! ## The uniqueness half of Stacks 0AKJ -/

/-- **The uniqueness half of Stacks 0AKJ (descent and uniqueness).**  Let `A` be Noetherian,
let `I ⊆ A`, let `B` be an `A`-algebra and let `C` be a Noetherian `A`-algebra.  Two
`A`-algebra maps `B → Cʰ` into the henselization of the pair `(C, IC)` that induce the same
map `B → C^∧` are equal.

This is the uniqueness assertion of the source, which it gets from the fact that `Cʰ` is a
subring of `C^∧` (Stacks 0AGV) — here
`Rig.injective_henselizationToAdicCompletion`.  Stacks 0AKJ states descent as a single
`∃!`, so this cannot be tagged on its own; it is the uniqueness component of
`Rig.exists_unique_algHom_henselization_of_adicCompletion`, which carries the tag. -/
public theorem eq_of_henselizationToAdicCompletion_comp_eq (A : Type u) (B : Type v)
    (C : Type w) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) [CommRing C]
    [Algebra A C] [IsNoetherianRing C] :
    let H := (henselization C (I.map (algebraMap A C)) : Type w)
    letI : Algebra A H :=
      ((algebraMap C H).comp (algebraMap A C)).toAlgebra
    letI : IsScalarTower A C H :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ ψ₁ ψ₂ : B →ₐ[A] H,
      ((henselizationToAdicCompletion C
          (I.map (algebraMap A C))).val.restrictScalars A).comp ψ₁ =
        ((henselizationToAdicCompletion C
          (I.map (algebraMap A C))).val.restrictScalars A).comp ψ₂ →
      ψ₁ = ψ₂ := by
  intro H ψ₁ ψ₂ heq
  let : Algebra A H := ((algebraMap C H).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C H := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact AlgHom.ext fun b =>
    injective_henselizationToAdicCompletion C (I.map (algebraMap A C)) (AlgHom.congr_fun heq b)

/-! ## Maps out of an adic completion are determined on the dense image -/

/-- Pushing `I.map (algebraMap R A)` along an `R`-algebra map `A → B` gives
`I.map (algebraMap R B)`. -/
private theorem map_map_algebraMap_algHom {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (I : Ideal R) (f : A →ₐ[R] B) :
    (I.map (algebraMap R A)).map f.toRingHom = I.map (algebraMap R B) := by
  rw [Ideal.map_map]
  exact congrArg I.map f.comp_algebraMap

/-- A linear map out of `B^∧` into an `I`-adically separated module vanishes as soon as it
vanishes on the image of `B`: every element of `B^∧` is congruent to one of `B` modulo
`Iⁿ`, so the value lies in `Iⁿ ·` the target for every `n`. -/
private theorem linearMap_eq_zero_of_adicCompletion_of_eq_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG)
    {M : Type w} [AddCommGroup M] [Module A M] [IsHausdorff I M]
    (f : AdicCompletion (I.map (algebraMap A B)) B →ₗ[A] M)
    (hf : ∀ b : B, f (algebraMap B _ b) = 0) : f = 0 := by
  refine LinearMap.ext fun x => ?_
  change f x = 0
  refine IsHausdorff.haus' (I := I) _ fun n => ?_
  let J := I.map (algebraMap A B)
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective
    (J ^ n • (⊤ : Submodule B B)) (AdicCompletion.eval J B n x)
  have hmB : x - algebraMap B _ b ∈ J ^ n • (⊤ : Submodule B (AdicCompletion J B)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _)]
    change AdicCompletion.eval J B n (x - AdicCompletion.of J B b) = 0
    rw [map_sub, AdicCompletion.eval_of]
    exact sub_eq_zero.mpr hb.symm
  have hmA : x - algebraMap B _ b ∈ I ^ n • (⊤ : Submodule A (AdicCompletion J B)) := by
    rw [Ideal.smul_top_eq_map]
    simpa only [Ideal.smul_top_eq_map, J, ← Ideal.map_pow, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq A B (AdicCompletion J B),
      Submodule.restrictScalars_mem] using hmB
  simpa only [Submodule.mem_comap, map_sub, hf, sub_zero, SModEq.zero] using
    Submodule.smul_top_le_comap_smul_top (I ^ n) f hmA

/-- Two `R`-algebra maps out of `R^∧` into an `I`-adically separated `R`-algebra agree. -/
private theorem algHom_ext_adicCompletion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) [IsHausdorff I S]
    (f g : AdicCompletion I R →ₐ[R] S) : f = g := by
  have h := linearMap_eq_zero_of_adicCompletion_of_eq_zero (B := R) (M := S) I hI
  rw [Algebra.algebraMap_self, Ideal.map_id] at h
  have he := h (f.toLinearMap - g.toLinearMap) (fun r => by simp)
  exact AlgHom.ext fun x => sub_eq_zero.mp (LinearMap.congr_fun he x)

/-- If `Iᶜ` annihilates `Ω_{B/A}` then `Iᶜ` annihilates every `A`-derivation of `B^∧`: the
derivation kills the image of `B` by the universal property of `Ω_{B/A}`, and
`linearMap_eq_zero_of_adicCompletion_of_eq_zero` propagates that to all of `B^∧`. -/
private theorem smul_derivation_adicCompletion_eq_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG)
    {M : Type w} [AddCommGroup M] [Module A M] [Module B M]
    [Module (AdicCompletion (I.map (algebraMap A B)) B) M]
    [IsScalarTower A B M]
    [IsScalarTower B (AdicCompletion (I.map (algebraMap A B)) B) M]
    [IsScalarTower A (AdicCompletion (I.map (algebraMap A B)) B) M]
    [IsHausdorff I M]
    (d : Derivation A (AdicCompletion (I.map (algebraMap A B)) B) M)
    (c : ℕ) (hc : (I.map (algebraMap A B)) ^ c ≤
      Module.annihilator B (KaehlerDifferential A B))
    (a : A) (ha : a ∈ I ^ c) (x : AdicCompletion (I.map (algebraMap A B)) B) :
    a • d x = 0 := by
  have heq : a • d.toLinearMap = 0 := by
    refine linearMap_eq_zero_of_adicCompletion_of_eq_zero I hI _ fun b => ?_
    let dB := d.compAlgebraMap B
    have hz := Module.mem_annihilator.mp
      (hc ((Ideal.map_pow _ I c).le (Ideal.mem_map_of_mem _ ha))) (KaehlerDifferential.D A B b)
    have hz' := congrArg dB.liftKaehlerDifferential hz
    rwa [map_smul, dB.liftKaehlerDifferential_comp_D, map_zero,
      IsScalarTower.algebraMap_smul] at hz'
  exact LinearMap.congr_fun heq x

/-! ## Étaleness off `V(I)` annihilates the differentials -/

/-- **The `Ω` half of Stacks 0ALQ, part (1).**  If `Spec(B) → Spec(A)` is étale over
`Spec(A) ∖ V(I)` then `Ω_{B/A}` is supported in `V(IB)`, so — being a finite module over the
Noetherian ring `B` — it is annihilated by a power of `IB`. -/
private theorem exists_pow_le_annihilator_kaehlerDifferential_of_isEtaleOutside
    (A : Type u) (B : Type v) [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) (hEtale : IsEtaleOutside I B) :
    ∃ c : ℕ, (I.map (algebraMap A B)) ^ c ≤
      Module.annihilator B (KaehlerDifferential A B) := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (I.fg_of_isNoetherianRing.map _)
  rw [← PrimeSpectrum.zeroLocus_subset_zeroLocus_iff, ← Module.support_eq_zeroLocus]
  intro q hq
  by_contra h
  have hp : q ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹'
      (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := by
    simp only [Set.mem_preimage, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe, PrimeSpectrum.comap_asIdeal]
    simpa only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      Ideal.map_le_iff_le_comap] using h
  have he := hEtale hp
  rw [Algebra.etaleLocus_eq_compl_support] at he
  exact he.1 hq

/-- **The conormal module of a split surjection out of `B^∧`.**  Let `φ : B^∧ → T` be an
`A`-algebra map with a section `σ`, and suppose `Iᶜ` annihilates `Ω_{B/A}`.  Then `Iᶜ`
annihilates `Ker(φ)/Ker(φ)²`.

The section makes `σ ∘ φ` a lift of `B^∧ → B^∧/Ker(φ)²` over the square-zero extension
`Ker(φ)/Ker(φ)²`, hence a derivation of `B^∧`; `smul_derivation_adicCompletion_eq_zero`
annihilates it, and that is exactly the assertion. -/
private theorem cotangent_annihilated_of_adicCompletion_section
    {A : Type u} {B : Type v} {T : Type w}
    [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [CommRing T] [Algebra A T]
    (I : Ideal A)
    (φ : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A] T)
    (σ : T →ₐ[A] AdicCompletion (I.map (algebraMap A B)) B)
    (hσ : φ.comp σ = AlgHom.id A T)
    (c : ℕ) (hc : (I.map (algebraMap A B)) ^ c ≤
      Module.annihilator B (KaehlerDifferential A B)) :
    I ^ c • (⊤ : Submodule A (RingHom.ker φ.toRingHom).Cotangent) = ⊥ := by
  let S := AdicCompletion (I.map (algebraMap A B)) B
  let J := RingHom.ker φ.toRingHom
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : IsNoetherianRing S := AdicCompletion.isNoetherianRing _
  let K := I.map (algebraMap A S)
  have hcomplete : IsAdicComplete K S := by
    have h := AdicCompletion.isAdicComplete (M := B)
      (I.fg_of_isNoetherianRing.map (algebraMap A B))
    rw [← IsAdicComplete.map_algebraMap_iff (S := S)] at h
    simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B S] using h
  let Q := S ⧸ J ^ 2
  let q : S →ₐ[A] Q := Ideal.Quotient.mkₐ A (J ^ 2)
  let g : S →ₐ[A] Q := q.comp (σ.comp φ)
  have hg : (Ideal.Quotient.mkₐ A J.cotangentIdeal).comp g =
      IsScalarTower.toAlgHom A S (Q ⧸ J.cotangentIdeal) := by
    refine AlgHom.ext fun x => ?_
    apply Ideal.Quotient.eq.mpr
    change Ideal.Quotient.mk (J ^ 2) (σ (φ x)) - Ideal.Quotient.mk (J ^ 2) x ∈
      J.cotangentIdeal
    rw [← map_sub, Ideal.mk_mem_cotangentIdeal]
    change φ (σ (φ x) - x) = 0
    rw [map_sub, show φ (σ (φ x)) = φ x from AlgHom.congr_fun hσ (φ x), sub_self]
  let d : Derivation A S J.cotangentIdeal :=
    derivationToSquareZeroOfLift J.cotangentIdeal J.cotangentIdeal_square g hg
  have : Module.Finite S J := Module.Finite.of_fg J.fg_of_isNoetherianRing
  have : Module.Finite S J.Cotangent :=
    Module.Finite.of_surjective J.toCotangent J.toCotangent_surjective
  have : Module.Finite S J.cotangentIdeal := Module.Finite.equiv J.cotangentEquivIdeal
  have : IsHausdorff K J.cotangentIdeal :=
    IsHausdorff.of_le_jacobson K _ (@IsAdicComplete.le_jacobson_bot S _ K hcomplete)
  have : IsHausdorff I J.cotangentIdeal :=
    (IsHausdorff.map_algebraMap_iff (S := S)).mp inferInstance
  refine le_antisymm (Submodule.smul_le.mpr fun a ha m _ => ?_) bot_le
  obtain ⟨x, rfl⟩ := J.toCotangent_surjective m
  have hd := smul_derivation_adicCompletion_eq_zero I I.fg_of_isNoetherianRing d c hc a ha x
  have hd' := congrArg (fun y : J.cotangentIdeal => (y : Q)) hd
  have hx : φ x = 0 := x.property
  simp only [Submodule.coe_smul_of_tower, Submodule.coe_zero, d,
    derivationToSquareZeroOfLift_apply, Algebra.smul_def] at hd'
  have hgx : g x = 0 := by
    change q (σ (φ x)) = 0
    rw [hx, map_zero, map_zero]
  rw [hgx, zero_sub, mul_neg, neg_eq_zero] at hd'
  have hm : algebraMap A S a * (x : S) ∈ J ^ 2 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, Ideal.Quotient.mk_algebraMap, Ideal.Quotient.algebraMap_eq] using hd'
  change a • J.toCotangent x = 0
  rwa [← IsScalarTower.algebraMap_smul S a (J.toCotangent x), ← map_smul,
    J.toCotangent_eq_zero]

/-! ## Recognising a completion from an isomorphism of completions -/

/-- The induced map of completions carries the canonical image of `r` to that of `f r`. -/
private theorem adicCompletionMap_algebraMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (h : I.map f ≤ J) (r : R) :
    adicCompletionMap f I J h (algebraMap R _ r) = algebraMap S _ (f r) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  unfold adicCompletionMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  simp

/-- The completion map `R^∧ → S^∧` of an `R`-algebra `S`, as an `R`-algebra map. -/
private noncomputable def adicCompletionAlgHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : AdicCompletion I R →ₐ[R]
      AdicCompletion (I.map (algebraMap R S)) S where
  __ := adicCompletionMap (algebraMap R S) I (I.map (algebraMap R S)) le_rfl
  commutes' r := by
    change adicCompletionMap (algebraMap R S) I _ le_rfl
      (algebraMap R (AdicCompletion I R) r) = _
    rw [adicCompletionMap_algebraMap]
    exact (IsScalarTower.algebraMap_apply R S _ r).symm

/-- The kernel of the `n`-th evaluation `R^∧ → R/Iⁿ` is `Iⁿ R^∧`. -/
private theorem ker_eval_adicCompletion
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  change AdicCompletion.evalₐ I n x = 0 ↔ _
  change _ ↔ x ∈ ((I ^ n).map (algebraMap R (AdicCompletion I R))).restrictScalars R
  rw [← Ideal.smul_top_eq_map]
  change _ ↔ x ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R))
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
  change _ ↔ AdicCompletion.eval I R n x = 0
  have h₁ := AdicCompletion.factor_evalₐ_eq_eval I x
    (show I ^ n ≤ I ^ n • (⊤ : Ideal R) by simp)
  have h₂ := AdicCompletion.factor_eval_eq_evalₐ I x
    (show I ^ n • (⊤ : Ideal R) ≤ I ^ n by simp)
  exact ⟨fun hx => by rw [← h₁, hx, map_zero], fun hx => by rw [← h₂, hx, map_zero]⟩

/-- `R^∧ / Iⁿ R^∧ ≅ R / Iⁿ`. -/
private noncomputable def adicCompletionQuotientEquivPow
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    ((AdicCompletion I R) ⧸ (I ^ n).map (algebraMap R (AdicCompletion I R))) ≃ₐ[R]
      (R ⧸ I ^ n) :=
  (Ideal.quotientEquivAlgOfEq R (ker_eval_adicCompletion I hI n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.surjective_evalₐ I n))

/-- An `R`-algebra isomorphism `R^∧ ≅ S^∧` makes `R → S` bijective modulo every power of
`I`: both sides compute the same quotient of the common completion. -/
private theorem bijective_quotientMap_of_adicCompletion_equiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG)
    (e : AdicCompletion I R ≃ₐ[R] AdicCompletion (I.map (algebraMap R S)) S)
    (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((I ^ n).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map) := by
  let J := I.map (algebraMap R S)
  have heI : (J ^ n).map (algebraMap S (AdicCompletion J S)) =
      ((I ^ n).map (algebraMap R (AdicCompletion I R))).map e.toRingHom := by
    change _ = ((I ^ n).map (algebraMap R (AdicCompletion I R))).map e.toAlgHom.toRingHom
    rw [map_map_algebraMap_algHom (I ^ n) e.toAlgHom]
    dsimp only [J]
    rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq R S _]
  let E₀ := ((adicCompletionQuotientEquivPow I hI n).symm.trans
    (Ideal.quotientEquivAlg _ _ e heI)).trans
      ((adicCompletionQuotientEquivPow J (hI.map _) n).restrictScalars R)
  let E := E₀.trans (Ideal.quotientEquivAlgOfEq R (Ideal.map_pow (algebraMap R S) I n).symm)
  have hE : ∀ x : R ⧸ I ^ n,
      E x = Ideal.quotientMap ((I ^ n).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map x := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change E (algebraMap R (R ⧸ I ^ n) r) = _
    rw [E.commutes]
    rfl
  have heq : (E : (R ⧸ I ^ n) → S ⧸ (I ^ n).map (algebraMap R S)) =
      Ideal.quotientMap ((I ^ n).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map := funext hE
  rw [← heq]
  exact E.bijective

/-! ## Shrinking to an étale neighbourhood of `V(I)` -/

/-- An open set containing `V(I)` contains a basic open `D(g)` with `g ∈ 1 + I`: the vanishing
ideal of the complement is comaximal with `I`, and `g` is the component of `1` in it. -/
private theorem exists_basicOpen_subset_of_zeroLocus_subset
    {R : Type u} [CommRing R] (I : Ideal R) {U : Set (PrimeSpectrum R)}
    (hU : IsOpen U) (hIU : PrimeSpectrum.zeroLocus (I : Set R) ⊆ U) :
    ∃ g : R, g - 1 ∈ I ∧ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆ U := by
  let K := PrimeSpectrum.vanishingIdeal Uᶜ
  have hK : PrimeSpectrum.zeroLocus (K : Set R) = Uᶜ := by
    dsimp only [K]
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.isClosed_compl.closure_eq]
  have hsup : I ⊔ K = ⊤ := by
    apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    rw [PrimeSpectrum.zeroLocus_sup, hK]
    exact Set.eq_empty_iff_forall_notMem.mpr fun q hq => hq.2 (hIU hq.1)
  obtain ⟨a, ha, g, hg, hag⟩ := Submodule.mem_sup.mp
    (show (1 : R) ∈ I ⊔ K from hsup ▸ Submodule.mem_top)
  refine ⟨g, ?_, ?_⟩
  · rw [show g - 1 = -a by linear_combination hag]
    exact I.neg_mem ha
  · exact fun q hq => Classical.byContradiction fun hn =>
      hq ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hg q hn)

/-- If `R → S` is surjective modulo `I` then `Ω_{S/R}` is generated by `IS`-multiples of
itself, so Nakayama produces `g ∈ 1 + IS` annihilating it. -/
private theorem exists_annihilator_sub_one_of_surjective_quotientMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (I : Ideal R)
    (h : Function.Surjective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    ∃ g : S, g - 1 ∈ I.map (algebraMap R S) ∧
      g ∈ Module.annihilator S (KaehlerDifferential R S) := by
  let Ω := KaehlerDifferential R S
  let J := I.map (algebraMap R S)
  have hle : (⊤ : Submodule S Ω) ≤ J • ⊤ := by
    conv_lhs => rw [← KaehlerDifferential.span_range_derivation R S]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, hx⟩ := h (Ideal.Quotient.mk J s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hm' : s - algebraMap R S r ∈ I • (⊤ : Submodule R S) := by
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq.mp hx.symm
    have hd := Submodule.smul_top_le_comap_smul_top I
      (KaehlerDifferential.D R S).toLinearMap hm'
    rw [Submodule.mem_comap] at hd
    change (KaehlerDifferential.D R S) (s - algebraMap R S r) ∈ _ at hd
    rw [map_sub, Derivation.map_algebraMap, sub_zero] at hd
    change (KaehlerDifferential.D R S) s ∈ (J • (⊤ : Submodule S Ω)).restrictScalars R
    rwa [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  obtain ⟨g, hg, hz⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    J (⊤ : Submodule S Ω) Module.Finite.fg_top hle
  exact ⟨g, hg, Module.mem_annihilator.mpr (fun x => hz x trivial)⟩

/-- Bijectivity of `R/I → S/IS` makes `S/IS` flat over `R/I`, trivially. -/
private theorem flat_quotient_of_bijective_quotientMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R)
    (h : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.Flat (R ⧸ I) (S ⧸ (I • (⊤ : Submodule R S))) := by
  let e : (R ⧸ I) ≃ₐ[R ⧸ I] (S ⧸ I.map (algebraMap R S)) :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) h
  have hf : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let E : (S ⧸ (I • (⊤ : Submodule R S))) ≃ₗ[R] (S ⧸ I.map (algebraMap R S)) :=
    (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I)).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)
  let E' : (S ⧸ (I • (⊤ : Submodule R S))) ≃ₗ[R ⧸ I]
      (S ⧸ I.map (algebraMap R S)) :=
    { __ := E.toAddEquiv
      map_smul' := fun a x => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact E.map_smul r x }
  exact Module.Flat.of_linearEquiv E'

/-- **A finite type algebra with the same completion as its base is étale near `V(I)`.**  If
`R → S` is bijective modulo every power of `I`, then there is `g ∈ 1 + IS` with `S_g` étale
over `R`.

Flatness comes from the flatness of all the quotients `S/IⁿS` over `R/Iⁿ` (Stacks 0AQX, here
`Module.Flat.of_flat_quotient_pow`) together with the openness of the flat locus, which
supplies a basic open around `V(IS)` on which `S` is `R`-flat.  Unramifiedness comes from
Nakayama, which supplies a second element of `1 + IS` annihilating `Ω_{S/R}`.  The product of
the two is the required `g`. -/
private theorem exists_etale_localization_of_bijective_quotientMap_pow
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (I : Ideal R)
    (h : ∀ n : ℕ, Function.Bijective (Ideal.quotientMap ((I ^ n).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    ∃ g : S, g - 1 ∈ I.map (algebraMap R S) ∧ Algebra.Etale R (Localization.Away g) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨a, ha, hza⟩ := exists_annihilator_sub_one_of_surjective_quotientMap (S := S) I
    (by
      have h₁ := h 1
      rw [pow_one] at h₁
      exact h₁.surjective)
  let U := {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal S)}
  have hIU : PrimeSpectrum.zeroLocus (I.map (algebraMap R S) : Set S) ⊆ U := fun q hq =>
    Module.Flat.of_flat_quotient_pow I S
      (fun n => flat_quotient_of_bijective_quotientMap _ (h (n + 1)))
      q.asIdeal hq _ (LocalizedModule.mkLinearMap q.asIdeal.primeCompl S)
  obtain ⟨b, hb, hUb⟩ := exists_basicOpen_subset_of_zeroLocus_subset
    (I.map (algebraMap R S)) (U := U)
    (Module.isOpen_setOf_flat_localizedModule_atPrime (R := R) (S := S) (M := S)) hIU
  let g := a * b
  have hg : g - 1 ∈ I.map (algebraMap R S) := by
    rw [show g - 1 = a * (b - 1) + (a - 1) by
      dsimp only [g]
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ a hb) ha
  have hflat : Module.Flat R (LocalizedModule.Away g S) :=
    Module.flat_localizedModule_away_of_forall_flat_atPrime (g := g) (fun q hq hgq =>
      hUb (a := (⟨q, hq⟩ : PrimeSpectrum S)) (fun hbq => hgq (q.mul_mem_left a hbq)))
  have : Module.Flat R (Localization.Away g) := Module.Flat.of_linearEquiv
    ((IsLocalizedModule.linearEquiv (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) S)
      (Algebra.linearMap S (Localization.Away g))).restrictScalars R).symm
  have : Algebra.FormallyUnramified R (Localization.Away g) := by
    apply Algebra.basicOpen_subset_unramifiedLocus_iff.mp
    rw [Algebra.unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus]
    intro q hq hsupport
    exact hq (q.asIdeal.mul_mem_right b (hsupport hza))
  exact ⟨g, hg, Algebra.Etale.of_formallyUnramified_of_flat⟩

/-! ## Lifting an étale algebra into the henselization -/

/-- Two maps out of a formally unramified, essentially finite type algebra into `B` agree as
soon as they agree modulo an ideal of the Jacobson radical: their difference is measured by
the idempotent-like element `e` of `S ⊗ S`, whose image is a unit. -/
private theorem unique_formallyUnramified_map_of_quotient
    {R : Type u} {S : Type*} {B : Type v}
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Algebra R B] (K : Ideal B) (hK : K ≤ (⊥ : Ideal B).jacobson)
    (f g : S →ₐ[R] B)
    (hfg : (Ideal.Quotient.mkₐ R K).comp f = (Ideal.Quotient.mkₐ R K).comp g) : f = g := by
  let θ : S ⊗[R] S →ₐ[R] B :=
    Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  let q : B →ₐ[R] B ⧸ K := Ideal.Quotient.mkₐ R K
  have hθ : q.comp θ = (q.comp f).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, θ, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
    have h := congrArg (fun φ : S →ₐ[R] B ⧸ K => φ y) hfg
    simpa only [AlgHom.comp_apply] using congrArg (q (f x) * ·) h.symm
  let e := Algebra.FormallyUnramified.elem R S
  have hunit : IsUnit (θ e) := by
    have hq : q (θ e) = 1 := by
      rw [← AlgHom.comp_apply, hθ, AlgHom.comp_apply,
        show Algebra.TensorProduct.lmul' R e = 1 from Algebra.FormallyUnramified.lmul_elem,
        map_one]
    have hm : θ e - 1 ∈ K := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change q (θ e - 1) = 0
      simp [hq]
    exact Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hK hm)
  refine AlgHom.ext fun x => ?_
  have heq := congrArg θ
    (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) (S := S) x)
  have hmul : f x * θ e = g x * θ e := by
    simpa [θ, e, Algebra.TensorProduct.lift_tmul, mul_comm] using heq.symm
  exact hunit.mul_right_cancel hmul

/-- **An étale algebra lifts a map to `R/J` into a henselian pair over `R`.**  Base changing
to `H` makes `H ⊗_R S` étale over `H`, and a henselian pair lifts the section of its closed
fibre; restricting the lift along `S → H ⊗_R S` is the required map. -/
private theorem exists_etale_lift_to_henselian
    {R S H : Type w} [CommRing R] [CommRing S] [CommRing H]
    [Algebra R S] [Algebra.Etale R S] [Algebra R H]
    (J : Ideal R) (K : Ideal H) (hH : HenselianPair H K)
    (hJK : J ≤ K.comap (algebraMap R H)) (σ : S →ₐ[R] R ⧸ J) :
    ∃ k : S →ₐ[R] H, (Ideal.Quotient.mkₐ R K).comp k =
      (Ideal.quotientMapₐ K (Algebra.ofId R H) hJK).comp σ := by
  let β : R ⧸ J →ₐ[R] H ⧸ K := Ideal.quotientMapₐ K (Algebra.ofId R H) hJK
  let q : H →ₐ[R] H ⧸ K := Ideal.Quotient.mkₐ R K
  let σR : H ⊗[R] S →ₐ[R] H ⧸ K :=
    Algebra.TensorProduct.lift q (β.comp σ) (fun _ _ => Commute.all _ _)
  let σH : H ⊗[R] S →ₐ[H] H ⧸ K :=
    { σR.toRingHom with
      commutes' := fun h => by
        change σR (h ⊗ₜ[R] 1) = Ideal.Quotient.mk K h
        simp [σR, q, Algebra.TensorProduct.lift_tmul] }
  have : Algebra.Etale H (H ⊗[R] S) := Algebra.Etale.baseChange R S H
  have hlift := ((henselianPair_tfae.{w, w} H K).out 1 2).mp hH
  obtain ⟨τ, hτ⟩ := hlift (H ⊗[R] S) σH
  refine ⟨(τ.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := H)), AlgHom.ext fun s => ?_⟩
  simpa [σH, σR, β, q, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.includeRight_apply] using AlgHom.congr_fun hτ (1 ⊗ₜ[R] s)

/-- A map `S → R^∧` extends over the completion of `S` along `IS`, because `R^∧` is
`I`-adically complete. -/
private theorem exists_extension_to_adicCompletion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (f : S →ₐ[R] AdicCompletion I R) :
    ∃ F : AdicCompletion (I.map (algebraMap R S)) S →ₐ[R] AdicCompletion I R,
      F.comp (IsScalarTower.toAlgHom R S _) = f := by
  let T := AdicCompletion I R
  let K := I.map (algebraMap R T)
  have : IsAdicComplete K T := AdicCompletion.isAdicComplete_self I hI
  have hmap : (I.map (algebraMap R S)).map f.toRingHom ≤ K :=
    (map_map_algebraMap_algHom I f).le
  let F₀ := (AdicCompletion.ofAlgEquiv K).symm.toRingHom.comp
    (adicCompletionMap f.toRingHom (I.map (algebraMap R S)) K hmap)
  have hF₀ (s : S) : F₀ (algebraMap S _ s) = f s := by
    dsimp only [F₀, RingHom.comp_apply]
    rw [adicCompletionMap_algebraMap]
    exact (AdicCompletion.ofAlgEquiv K).symm_apply_apply (f s)
  let F : AdicCompletion (I.map (algebraMap R S)) S →ₐ[R] T :=
    { __ := F₀
      commutes' := fun r => by
        change F₀ (algebraMap R _ r) = _
        rw [IsScalarTower.algebraMap_apply R S _, hF₀, f.commutes] }
  exact ⟨F, AlgHom.ext hF₀⟩

/-- **An étale `R`-algebra mapping to `R^∧` maps to `Rʰ`, compatibly.**  The map into
`R/I` obtained by evaluating in degree one is lifted into the henselian pair `(Rʰ, IRʰ)` by
`exists_etale_lift_to_henselian`, and the lift agrees with the original map after composing
with `Rʰ → R^∧` because both maps agree modulo `I R^∧`, which lies in the Jacobson radical of
the complete ring `R^∧`. -/
private theorem exists_etale_algHom_henselization_of_adicCompletion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (I : Ideal R) (hI : I.FG)
    (f : S →ₐ[R] AdicCompletion I R) :
    ∃ k : S →ₐ[R] (henselization R I : Type u),
      (henselizationToAdicCompletion R I).val.comp k = f := by
  let H := (henselization R I : Type u)
  let K := I.map (algebraMap R H)
  let T := AdicCompletion I R
  let L := I.map (algebraMap R T)
  have : IsAdicComplete L T := AdicCompletion.isAdicComplete_self I hI
  let α := (henselizationToAdicCompletion R I).val
  let σ := (AdicCompletion.evalOneₐ I).comp f
  obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R S
  have : Algebra.Etale R P.eval.obj := Algebra.Etale.of_equiv e
  obtain ⟨k₀, hk₀⟩ := exists_etale_lift_to_henselian I K
    (henselianPair_henselization R I) Ideal.le_comap_map (σ.comp e.symm.toAlgHom)
  let k := k₀.comp e.toAlgHom
  have hk : (Ideal.Quotient.mkₐ R K).comp k =
      (Ideal.quotientMapₐ K (Algebra.ofId R H) Ideal.le_comap_map).comp σ := by
    ext s
    exact (AlgHom.congr_fun hk₀ (e s)).trans (by simp)
  have hker : RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom = L :=
    AdicCompletion.ker_evalOneₐ_eq_map I hI
  refine ⟨k, ?_⟩
  apply unique_formallyUnramified_map_of_quotient L (IsAdicComplete.le_jacobson_bot L)
  ext s
  apply Ideal.Quotient.eq.mpr
  have heval : AdicCompletion.evalOneₐ I (α (k s) - f s) = 0 := by
    rw [map_sub]
    apply sub_eq_zero.mpr
    have he : (Ideal.Quotient.mkₐ R K) (k s) =
        Ideal.quotientMapₐ K (Algebra.ofId R H) Ideal.le_comap_map (σ s) :=
      AlgHom.congr_fun hk s
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (σ s)
    rw [← hr] at he
    have hm : k s - algebraMap R H r ∈ K := Ideal.Quotient.eq.mp he
    have hmα : α (k s) - algebraMap R T r ∈ L := by
      have hm' := Ideal.mem_map_of_mem α.toRingHom hm
      rw [map_map_algebraMap_algHom] at hm'
      change α (k s - algebraMap R H r) ∈ L at hm'
      rwa [map_sub, α.commutes] at hm'
    have hz := hker.symm ▸ hmα
    change AdicCompletion.evalOneₐ I (α (k s) - algebraMap R T r) = 0 at hz
    rw [map_sub, (AdicCompletion.evalOneₐ I).commutes] at hz
    exact (sub_eq_zero.mp hz).trans hr
  exact hker ▸ heval

/-- An `R`-algebra map into an `I`-adically complete `R`-algebra sends every element of
`1 + ID` to a unit. -/
public theorem isUnit_algHom_of_sub_one_mem_map
    {R : Type u} {D : Type v} {T : Type w} [CommRing R] [CommRing D] [CommRing T]
    [Algebra R D] [Algebra R T] (I : Ideal R) [IsAdicComplete (I.map (algebraMap R T)) T]
    (δ : D →ₐ[R] T) {g : D} (hg : g - 1 ∈ I.map (algebraMap R D)) : IsUnit (δ g) := by
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  apply IsAdicComplete.le_jacobson_bot (I.map (algebraMap R T))
  have hm := Ideal.mem_map_of_mem δ.toRingHom hg
  rw [map_map_algebraMap_algHom] at hm
  change δ (g - 1) ∈ _ at hm
  rwa [map_sub, map_one] at hm

/-- A finite type `R`-algebra `D` whose completion along `ID` is `R^∧` is étale near `V(ID)`,
so every `R`-algebra map `D → R^∧` factors through `Rʰ`. -/
public theorem exists_algHom_henselization_of_algEquiv_adicCompletion
    {R : Type u} {D : Type v} [CommRing R] [IsNoetherianRing R]
    [CommRing D] [Algebra R D] [Algebra.FiniteType R D] (I : Ideal R)
    (E : AdicCompletion I R ≃ₐ[R] AdicCompletion (I.map (algebraMap R D)) D)
    (δ : D →ₐ[R] AdicCompletion I R) :
    ∃ k : D →ₐ[R] (henselization R I : Type u),
      (henselizationToAdicCompletion R I).val.comp k = δ := by
  obtain ⟨g, hg, hEt⟩ := exists_etale_localization_of_bijective_quotientMap_pow I
    (fun n => bijective_quotientMap_of_adicCompletion_equiv I I.fg_of_isNoetherianRing E n)
  have : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  have hunit := isUnit_algHom_of_sub_one_mem_map I δ hg
  let δg : Localization.Away g →ₐ[R] AdicCompletion I R := IsLocalization.liftAlgHom
    (M := Submonoid.powers g) (f := δ) (by
      rintro ⟨_, n, rfl⟩
      exact (map_pow δ g n) ▸ hunit.pow n)
  obtain ⟨k, hk⟩ := exists_etale_algHom_henselization_of_adicCompletion I
    I.fg_of_isNoetherianRing δg
  refine ⟨k.comp (IsScalarTower.toAlgHom R D (Localization.Away g)), AlgHom.ext fun d => ?_⟩
  refine (AlgHom.congr_fun hk (algebraMap D (Localization.Away g) d)).trans ?_
  change δg (algebraMap D _ d) = δ d
  dsimp only [δg]
  rw [IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq _ _

/-! ## The existence half of Stacks 0AKJ -/

/-- **The existence half of Stacks 0AKJ, in the source's reduced form `A = C`.**  Let `R` be
Noetherian, `I ⊆ R` an ideal and `S` a finite type `R`-algebra whose differentials `Ω_{S/R}`
are annihilated by `(IS)ᶜ`.  Then every `R`-algebra map `S → R^∧` factors through the
henselization `Rʰ` of the pair `(R, I)`.

The map extends to `φ : S^∧ → R^∧`, which the completion map `R^∧ → S^∧` splits, so `φ` is
surjective and — by `cotangent_annihilated_of_adicCompletion_section` — its conormal module is
annihilated by `Iᶜ`.  **Stacks 0ALR** then presents `R^∧` as the completion of a finite type
`S`-algebra `D`, necessarily of finite type over `R`.  Since `R^∧ ≅ D^∧`, the map `R → D` is
bijective modulo every power of `I`, so `D` has an étale localization `D_g` with `g ∈ 1 + ID`
(`exists_etale_localization_of_bijective_quotientMap_pow`); `g` is a unit in the complete ring
`R^∧`, so `D_g` still maps there, and
`exists_etale_algHom_henselization_of_adicCompletion` lifts that map to `Rʰ`. -/
public theorem exists_algHom_henselization_of_annihilator_kaehlerDifferential
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (I : Ideal R) (c : ℕ) (hc : (I.map (algebraMap R S)) ^ c ≤
      Module.annihilator S (KaehlerDifferential R S))
    (f : S →ₐ[R] AdicCompletion I R) :
    ∃ k : S →ₐ[R] (henselization R I : Type u),
      (henselizationToAdicCompletion R I).val.comp k = f := by
  let T := AdicCompletion I R
  let J := I.map (algebraMap R S)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  obtain ⟨φ, hφf⟩ := exists_extension_to_adicCompletion I I.fg_of_isNoetherianRing f
  let σ : T →ₐ[R] AdicCompletion J S := adicCompletionAlgHom I
  have hσ : φ.comp σ = AlgHom.id R T :=
    algHom_ext_adicCompletion I I.fg_of_isNoetherianRing _ _
  have hsurj : Function.Surjective φ := fun t => ⟨σ t, AlgHom.congr_fun hσ t⟩
  have hcot := cotangent_annihilated_of_adicCompletion_section I φ σ hσ c hc
  let : Algebra S T := f.toRingHom.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let φS : AdicCompletion J S →ₐ[S] T :=
    { __ := φ.toRingHom
      commutes' := fun s => AlgHom.congr_fun hφf s }
  have hcotS : J ^ c • (⊤ : Submodule S (RingHom.ker φS.toRingHom).Cotangent) = ⊥ := by
    apply Submodule.restrictScalars_injective R
    dsimp only [J]
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top, Submodule.restrictScalars_bot]
    exact hcot
  have hh := exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated S S T J
  rw [Algebra.algebraMap_self, Ideal.map_id] at hh
  obtain ⟨D, _, _, hft, ⟨e⟩⟩ := hh φS hsurj c hcotS
  let : Algebra R D := ((algebraMap S D).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R D :=
    .trans inferInstance hft
  have hJ : J.map (algebraMap S D) = I.map (algebraMap R D) := by
    dsimp only [J]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S D]
  let E : T ≃ₐ[R] AdicCompletion (I.map (algebraMap R D)) D := by
    rw [← hJ]
    exact e.restrictScalars R
  let δS : D →ₐ[S] T := e.symm.toAlgHom.comp (IsScalarTower.toAlgHom S D _)
  obtain ⟨k, hk⟩ :=
    exists_algHom_henselization_of_algEquiv_adicCompletion I E (δS.restrictScalars R)
  refine ⟨k.comp (IsScalarTower.toAlgHom R S D), AlgHom.ext fun s => ?_⟩
  exact (AlgHom.congr_fun hk (algebraMap S D s)).trans (δS.commutes s)

/-- If `(IB)ᶜ` annihilates `Ω_{B/A}`, then `(IC)ᶜ` annihilates `Ω_{(C ⊗_A B)/C}`. -/
public theorem pow_map_le_annihilator_kaehlerDifferential_tensorProduct
    {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] (I : Ideal A) (c : ℕ)
    (hc : (I.map (algebraMap A B)) ^ c ≤ Module.annihilator B (KaehlerDifferential A B)) :
    ((I.map (algebraMap A C)).map (algebraMap C (C ⊗[A] B))) ^ c ≤
      Module.annihilator (C ⊗[A] B) (KaehlerDifferential C (C ⊗[A] B)) := by
  let : Algebra B (C ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A C (C ⊗[A] B), Ideal.map_le_iff_le_comap]
  intro a ha
  have hz : ∀ m : KaehlerDifferential A B, algebraMap A B a • m = 0 :=
    Module.mem_annihilator.mp (hc ((Ideal.map_pow _ I c).le (Ideal.mem_map_of_mem _ ha)))
  refine Module.mem_annihilator.mpr fun m => ?_
  let e := KaehlerDifferential.tensorKaehlerEquiv A C B (C ⊗[A] B)
  obtain ⟨x, rfl⟩ := e.surjective m
  rw [← e.map_smul, ← e.map_zero]
  congr 1
  induction x using TensorProduct.inductionOn with
  | tmul d m =>
    rw [TensorProduct.smul_tmul']
    change (algebraMap A (C ⊗[A] B) a * d) ⊗ₜ[B] m = 0
    rw [IsScalarTower.algebraMap_apply A B (C ⊗[A] B)]
    change (algebraMap A B a • d) ⊗ₜ[B] m = 0
    rw [TensorProduct.smul_tmul, hz, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- The descent half of Stacks 0AKJ, read on the composite `B → B^∧ → C^∧`: let `A` be a
Noetherian ring, `I ⊆ A` an ideal and `B` a finite type `A`-algebra such that
`Spec(B) → Spec(A)` is étale over `Spec(A) ∖ V(I)`, and let `C` be a Noetherian `A`-algebra. Then
every `A`-algebra map `B → C^∧` into the `IC`-adic completion of `C` factors uniquely through the
henselization `Cʰ` of the pair `(C, IC)`. -/
public theorem exists_unique_algHom_henselization_of_algHom_adicCompletion
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) (hEtale : IsEtaleOutside I B)
    [CommRing C] [Algebra A C] [IsNoetherianRing C] :
    let H := (henselization C (I.map (algebraMap A C)) : Type w)
    letI : Algebra A H :=
      ((algebraMap C H).comp (algebraMap A C)).toAlgebra
    letI : IsScalarTower A C H :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ f : B →ₐ[A] AdicCompletion (I.map (algebraMap A C)) C,
        ∃! ψ : B →ₐ[A] H,
          ((henselizationToAdicCompletion C
            (I.map (algebraMap A C))).val.restrictScalars A).comp ψ = f := by
  intro H
  let : Algebra A H := ((algebraMap C H).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro f
  let T := AdicCompletion (I.map (algebraMap A C)) C
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let fA : D →ₐ[A] T := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom A C T) f (fun _ _ => Commute.all _ _)
  let fC : D →ₐ[C] T :=
    { __ := fA.toRingHom
      commutes' := fun c => by
        change algebraMap C T c * f 1 = algebraMap C T c
        rw [map_one, mul_one] }
  obtain ⟨c, hc⟩ :=
    exists_pow_le_annihilator_kaehlerDifferential_of_isEtaleOutside A B I hEtale
  have hD := pow_map_le_annihilator_kaehlerDifferential_tensorProduct (C := C) I c hc
  obtain ⟨k, hk⟩ := exists_algHom_henselization_of_annihilator_kaehlerDifferential
    (I.map (algebraMap A C)) c hD fC
  let ψ : B →ₐ[A] H := (k.restrictScalars A).comp
    (Algebra.TensorProduct.includeRight (R := A) (A := C))
  have hψ : ((henselizationToAdicCompletion C
      (I.map (algebraMap A C))).val.restrictScalars A).comp ψ = f := by
    refine AlgHom.ext fun b => (AlgHom.congr_fun hk (1 ⊗ₜ[A] b)).trans ?_
    change algebraMap C T 1 * f b = f b
    rw [map_one, one_mul]
  exact ⟨ψ, hψ, fun ψ' hψ' =>
    eq_of_henselizationToAdicCompletion_comp_eq A B C I ψ' ψ (hψ'.trans hψ.symm)⟩

/-- **Stacks Project, Tag 0AKJ (descent and uniqueness).**  Let `A` be a Noetherian ring,
`I ⊆ A` an ideal and `B` a finite type `A`-algebra such that `Spec(B) → Spec(A)` is étale over
`Spec(A) ∖ V(I)`, and let `C` be a Noetherian `A`-algebra.  Then every `A`-algebra map
`B^∧ → C^∧` of `I`-adic completions comes from a *unique* `A`-algebra map `B → Cʰ` into the
henselization of the pair `(C, IC)`.

Uniqueness is `Rig.eq_of_henselizationToAdicCompletion_comp_eq`, which rests on the fact that
`Cʰ` is a subring of `C^∧`.  For existence, follow the source and replace `(A, I, B, C)` by
`(C, IC, C ⊗_A B, C)`: the given map makes `D = C ⊗_A B` a `C`-algebra over `C^∧`, and the
étaleness hypothesis, which annihilates `Ω_{B/A}` by a power of `I`, annihilates `Ω_{D/C}` by
the same power after base change.  `exists_algHom_henselization_of_annihilator_kaehlerDifferential`
then lifts `D → C^∧` to `D → Cʰ`, and restricting along `B → D` gives the map sought. -/
@[stacks 0AKJ "descent and uniqueness"]
public theorem exists_unique_algHom_henselization_of_adicCompletion
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) (hEtale : IsEtaleOutside I B)
    [CommRing C] [Algebra A C] [IsNoetherianRing C] :
    let H := (henselization C (I.map (algebraMap A C)) : Type w)
    letI : Algebra A H :=
      ((algebraMap C H).comp (algebraMap A C)).toAlgebra
    letI : IsScalarTower A C H :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ φ : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A]
          AdicCompletion (I.map (algebraMap A C)) C,
        ∃! ψ : B →ₐ[A] H,
          ((henselizationToAdicCompletion C
            (I.map (algebraMap A C))).val.restrictScalars A).comp ψ =
            φ.comp (IsScalarTower.toAlgHom A B
              (AdicCompletion (I.map (algebraMap A B)) B)) := by
  intro H
  let : Algebra A H := ((algebraMap C H).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro φ
  exact exists_unique_algHom_henselization_of_algHom_adicCompletion A B C I hEtale _

end Rig

end
