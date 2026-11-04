module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Nakayama
public import StacksCore.RingTheory.Jacobson.Ideal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Isomorphic lifts of finite projective modules

Let `I` be an ideal of a commutative ring `R` such that every element of `1 + I` is a unit,
equivalently `I` is contained in the Jacobson radical. A map of finite projective `R`-modules is
an isomorphism as soon as its reduction modulo `I` is one; consequently two finite projective
modules with isomorphic reductions are themselves isomorphic. So the lift of a finite stably free
module produced by `Module.exists_isStablyFree_lift` is unique up to isomorphism.

Surjectivity of the reduction already forces surjectivity by Nakayama's lemma, and a surjection
of finite projective modules whose reduction is injective splits, which upgrades it to a
bijection.

## Main definitions

* `inducedQuot`: the map `P / IP → P' / IP'` induced by a linear map `P → P'`.

## Main results

* `lift_iso_of_quot_iso`: bijectivity descends from the reduction modulo `I`.
* `quot_iso_lift`: two finite projective modules with isomorphic reductions are isomorphic.

## Implementation notes

The ring is taken commutative, as `OrzechProperty` requires. The submodule `IP` is
`I • (⊤ : Submodule R P)` and the reduction `P / IP` is `P ⧸ (I • ⊤)`, with the induced map given
by `Submodule.mapQ`. Isomorphy is expressed as `Function.Bijective` in the first result and as
nonemptiness of a linear equivalence in the second.

## References

* [Stacks Project, Tag 0BC6](https://stacks.math.columbia.edu/tag/0BC6)
-/

@[expose] public section

open Submodule

/-- The map on quotients `P / IP → P' / IP'` induced by an `R`-module map
`φ : P → P'`. Here `IP` and `IP'` are the submodules `I • ⊤`. -/
noncomputable def inducedQuot {R : Type*} [CommRing R] (I : Ideal R)
    {P P' : Type*} [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (φ : P →ₗ[R] P') :
    (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R] (P' ⧸ (I • (⊤ : Submodule R P'))) :=
  Submodule.mapQ _ _ φ (by
    rw [Submodule.map_le_iff_le_comap.symm, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

/-- The induced map sends the class of `p` to the class of `φ p`. -/
private theorem inducedQuot_mk {R : Type*} [CommRing R] (I : Ideal R)
    {P P' : Type*} [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (φ : P →ₗ[R] P') (p : P) :
    inducedQuot I φ (Submodule.Quotient.mk p) = Submodule.Quotient.mk (φ p) := rfl

/-- If every element of `1 + I` is a unit then `I` is contained in the Jacobson
radical of `R` (i.e. `I ≤ (⊥ : Ideal R).jacobson`). This is
`Ideal.le_ringJacobson_iff_isUnit_one_add` read through `Ideal.jacobson_bot`. -/
theorem jacobson_aux {R : Type*} [CommRing R] (I : Ideal R)
    (hI : ∀ x ∈ I, IsUnit (1 + x)) : I ≤ (⊥ : Ideal R).jacobson :=
  Ideal.jacobson_bot (R := R) ▸ (Ideal.le_ringJacobson_iff_isUnit_one_add I).mpr hI

/-- Surjectivity lifts from quotients: if the induced map `P/IP → P'/IP'` is
surjective (and `P'` is finitely generated), then `φ` is surjective. This is
Nakayama's lemma. -/
@[ega "0 7.1.14" "sufficiency",
  ega "IV 2.5.8.8" "partial",
  sga "3 V 4.1.3" "more general",
  sga "3 VIIB 0.3.4" "Corollary (i) of 0.3.4",
  sga "3 VIIB 0.3.7" "Nakayama step",
  sga "4 XIII 1.5" "special case"]
theorem surj_aux {R : Type*} [CommRing R] (I : Ideal R)
    (hI : ∀ x ∈ I, IsUnit (1 + x))
    {P P' : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P'] [Module.Finite R P']
    (φ : P →ₗ[R] P') (h : Function.Surjective (inducedQuot I φ)) :
    Function.Surjective φ := by
  rw [← LinearMap.range_eq_top]
  have hjac : I ≤ (⊥ : Ideal R).jacobson := jacobson_aux I hI
  have hfg : (⊤ : Submodule R P').FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule R P') ≤ LinearMap.range φ ⊔ I • ⊤ := by
    intro p' _
    obtain ⟨q, hq⟩ := h (Submodule.Quotient.mk p')
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [inducedQuot_mk] at hq
    have hmem : p' - φ p ∈ I • (⊤ : Submodule R P') := by
      rw [← Submodule.Quotient.eq]
      exact hq.symm
    have : p' = φ p + (p' - φ p) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨p, rfl⟩) (Submodule.mem_sup_right hmem)
  exact top_le_iff.mp (le_of_le_smul_of_le_jacobson_bot hfg hjac hle)

/-- The induced maps are functorial with respect to composition: if `φ ∘ s = id`
then the induced maps satisfy `inducedQuot φ ∘ inducedQuot s = id`. -/
theorem comp_aux {R : Type*} [CommRing R] (I : Ideal R)
    {P P' : Type*} [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (φ : P →ₗ[R] P') (s : P' →ₗ[R] P) (hs : φ ∘ₗ s = LinearMap.id) :
    inducedQuot I φ ∘ₗ inducedQuot I s = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.comp_apply, inducedQuot_mk, inducedQuot_mk]
  simpa using congrArg Submodule.Quotient.mk (LinearMap.congr_fun hs p)

/-- **(Lifting isomorphisms.)** If `φ : P → P'` is an `R`-module map between finite
projective modules whose induced map `P/IP → P'/IP'` is an isomorphism (bijective),
then `φ` itself is an isomorphism. -/
@[stacks 0BC6 "(1)", ega "0 19.1.10" "special case", sga "3 VIIB 0.3.4" "Corollary (ii) of 0.3.4"]
theorem lift_iso_of_quot_iso
    {R : Type*} [CommRing R] (I : Ideal R)
    (hI : ∀ x ∈ I, IsUnit (1 + x))
    {P P' : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup P'] [Module R P'] [Module.Finite R P'] [Module.Projective R P']
    (φ : P →ₗ[R] P') (h : Function.Bijective (inducedQuot I φ)) :
    Function.Bijective φ := by
  have hφsurj : Function.Surjective φ := surj_aux I hI φ h.surjective
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ LinearMap.id hφsurj
  have hssurj : Function.Surjective (inducedQuot I s) := fun y =>
    ⟨inducedQuot I φ y, h.injective (LinearMap.congr_fun (comp_aux I φ s hs) (inducedQuot I φ y))⟩
  have hlinv : Function.LeftInverse φ s := fun x => LinearMap.congr_fun hs x
  exact ⟨(hlinv.rightInverse_of_surjective (surj_aux I hI s hssurj)).injective, hφsurj⟩

/-- **(Lifting the isomorphism class.)** If `P/IP ≅ P'/IP'` as `R`-modules, then
`P ≅ P'` as `R`-modules. -/
@[stacks 0BC6 "(2)", sga "5 XV 3.Lemma3" "(ii), special case"]
theorem quot_iso_lift
    {R : Type*} [CommRing R] (I : Ideal R)
    (hI : ∀ x ∈ I, IsUnit (1 + x))
    {P P' : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup P'] [Module R P'] [Module.Finite R P'] [Module.Projective R P']
    (h : Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R] (P' ⧸ (I • (⊤ : Submodule R P'))))) :
    Nonempty (P ≃ₗ[R] P') := by
  obtain ⟨e⟩ := h
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property
    (Submodule.mkQ (I • (⊤ : Submodule R P')))
    ((e : (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R] _) ∘ₗ Submodule.mkQ (I • (⊤ : Submodule R P)))
    (Submodule.mkQ_surjective _)
  have hind : Function.Bijective (inducedQuot I φ) := by
    have heq : inducedQuot I φ = (e : (P ⧸ (I • (⊤ : Submodule R P))) →ₗ[R] _) := by
      refine LinearMap.ext fun x => ?_
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [inducedQuot_mk]
      simpa using LinearMap.congr_fun hφ p
    rw [heq]
    exact e.bijective
  exact ⟨LinearEquiv.ofBijective φ (lift_iso_of_quot_iso I hI φ hind)⟩
