module

public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksFrontier.Deformation.FlatAlgebraLiftCompletion
public import StacksFrontier.RingTheory.Henselian.Pair.NilpotentFactorization
public import StacksFrontier.RingTheory.Henselian.Pair.Operations
public import StacksFrontier.RingTheory.Rig.HenselizationDescent

/-!
# Deformations of henselizations

Let `A' → A` be a surjection of Noetherian rings with nilpotent kernel, let `B` be a finite
type flat `A`-algebra and let `𝔟 ⊆ B` be an ideal such that `A → B_h` is syntomic for every
`h ∈ 𝔟`. Stacks 0DZB says that `B` has a flat lift to `A'` if and only if the henselization
`Bʰ` of the pair `(B, 𝔟)` does. This file proves that equivalence.

The proof is the source's, and runs along the proof of the completion analogue Stacks 0DZ3.
Choose a surjection `P = A[x_1, …, x_n] → B`, let `P'` be the polynomial algebra over `A'` and
let `𝔭' ⊆ P'` be the preimage of `𝔟`. Flat algebra lifts of `B` to `A'` are the same thing as
`A'`-flat `P'`-module lifts of `B`, because a lift is a quotient of `P'` by Nakayama; likewise
over the henselization `Q'` of the pair `(P', 𝔭')`, whose base change `Q = P ⊗_{P'} Q'`
presents `Bʰ`. The map `P' → Q'` is flat and induces `P'/𝔭' = Q'/𝔭'Q'` by Stacks 0AGU, so the
two module-lifting problems are compared by Stacks 0DZ2, whose local liftability hypothesis is
supplied by Stacks 07M8 exactly as in Stacks 0DZ3.

## Main results

* `Deformation.hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift`: the implication from
  `B` to its henselization, assuming Stacks 0DZ2.
* `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization`: the implication from
  the henselization back to `B`, assuming Stacks 0DZ2.
* `Deformation.hasFlatAlgebraLift_henselization_iff`: **Stacks 0DZB**, the equivalence,
  assuming Stacks 0DZ2.

## Implementation notes

**`h0DZ2` IS FALSE, so this file's conditional theorems are vacuous.**
`Deformation.FlatModuleLiftBaseChangeStatement` — Stacks 0DZ2 at the source's hypotheses,
restricted to a finite module — is refuted by
`StacksFrontier.Deformation.Examples.Linear.NodalArtinSchreierLift`, whose counterexample module is
finite and cyclic, so the finiteness restriction does not save it. Everything below that takes
`h0DZ2` as a hypothesis is therefore vacuously true and establishes nothing; the registrations
say so. The `_of_sqZero` variants are not the repair, because Stacks 0DZB (Lemma 93.14.1) says
`nilpotent kernel`. What is left open is the route through the consumers: there `M` comes from a
syntomic `B_h`, where the higher `Ext` carrying the obstruction vanishes, so the obstruction
cannot arise — extra vanishing that 0DZ2's own hypotheses do not supply. Settling those three
tags by that route is not done here.

**The hypothesis `h0DZ2`.** `Deformation.FlatModuleLiftBaseChangeStatement` is Stacks 0DZ2
written out and restricted to a finite module, which is all the proof uses; it is the same
hypothesis that Stacks 0DZ3 is proved under, and the gap between it and the library's forms of
Stacks 0DZ2 is discussed in `StacksFrontier.Deformation.FlatAlgebraLiftCompletion`.

**The henselization.** `Bʰ` is described by the henselian-pair condition on
`(Bʰ, 𝔟Bʰ)` together with the universal property, rather than by a chosen model, which is the
same modelling the other deformation statement about henselizations of pairs,
Stacks 0DZC, uses. The comparison `(P ⊗_{P'} Q') ⊗_P Bʰ`, i.e. `Q' ⊗_{P'} B ≅ Bʰ`, is
Stacks 0DYE for the integral — indeed surjective — map of pairs `(P', 𝔭') → (B, 𝔟)`; the
equality of vanishing loci it asks for is automatic because `𝔟` is the image of `𝔭'`. The
comparison ring `Q'` is taken to be the canonical construction `henselization P' 𝔭'`, whose
flatness over `P'`, Noetherianness and quotient identification are Stacks 0AGU and 0AGV.

**The syntomic hypothesis.** It is stated as syntomy of `A → B_h` for every `h ∈ 𝔟`, which is
the affine reading of "`Spec(B) → Spec(A)` is syntomic on the complement of `V(𝔟)`": that
complement is covered by the opens `D(h)`, `h ∈ 𝔟`, and syntomy is local on the source. This
is also the form Stacks 07M8 consumes.

**The second implication.** It is the same comparison read backwards, and what it needs is a
lift of the presentation along `Q'`. Let `C'` be a flat algebra lift of `Bʰ` to `A'`. The
reduction `C' → Bʰ` is a surjection with nilpotent kernel, so `C'` is henselian along the
preimage `𝔠'` of `𝔟Bʰ`: the kernel is locally nilpotent, hence henselian by Stacks 0ALI, the
quotient `C'/ker` is `Bʰ`, which is henselian along `𝔟Bʰ`, and Stacks 0DYD assembles the two.
The presentation `P' → Bʰ` lifts to `C'` by formal smoothness, and the universal property of
the henselization extends it to `Q' → C'`; the extension agrees with the structure map of
`Bʰ` over `Q'` by the *uniqueness* half of that same universal property, which replaces the
Hausdorff argument used in the completion case.

## References

* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
* [Stacks Project, Tag 0DYE](https://stacks.math.columbia.edu/tag/0DYE)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
* [Stacks Project, Tag 0AGV](https://stacks.math.columbia.edu/tag/0AGV)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Two elementary facts -/

/-- A nilpotent ideal consists of nilpotent elements. -/
private theorem le_nilradical_of_isNilpotent {R : Type u} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) : I ≤ nilradical R := by
  obtain ⟨n, hn⟩ := hI
  intro x hx
  refine mem_nilradical.mpr ⟨n, ?_⟩
  have hmem : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
  rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hmem

/-- The chain of isomorphisms identifying `(P ⊗_{P'} Q') ⊗_P B` with `Bʰ`, given the
isomorphism `Q' ⊗_{P'} B ≅ Bʰ` of Stacks 0DYE. -/
private theorem exists_ringEquiv_tensorHenselization
    (P' P B Q' Bh : Type u) [CommRing P'] [CommRing P] [CommRing B] [CommRing Q'] [CommRing Bh]
    [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q'] [Algebra P' Bh] [Algebra B Bh]
    [IsScalarTower P' P B] [IsScalarTower P' B Bh]
    (g : Q' →ₐ[P'] Bh)
    (hbij : Function.Bijective (Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom P' B Bh)
      (fun _ _ => Commute.all _ _))) :
    ∃ e : ((P ⊗[P'] Q') ⊗[P] B) ≃+* Bh,
      ∀ p : P, e ((p ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) = algebraMap B Bh (algebraMap P B p) := by
  refine ⟨(Algebra.TensorProduct.comm P (P ⊗[P'] Q') B).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange P' P B B Q').toRingEquiv.trans
      ((Algebra.TensorProduct.comm P' B Q').toRingEquiv.trans
        (RingEquiv.ofBijective _ hbij))), fun p => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
  simp only [AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  rw [Algebra.smul_def, mul_one]
  show Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom P' B Bh)
    (fun _ _ => Commute.all _ _) ((1 : Q') ⊗ₜ[P'] (algebraMap P B p)) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-! ### Lifting a presentation to a flat algebra lift of a henselian algebra -/

/-- **A flat lift of a henselian pair is henselian.** Let `(C, 𝔠)` be a henselian pair and let
`C'` be a flat lift of `C` to `A'`. The reduction `C' → C` is a surjection with nilpotent
kernel, so `C'` is henselian along the preimage `𝔠'` of `𝔠`, and a formally smooth presentation
`P' → C` carrying an ideal `J'` into `𝔠` therefore extends from the henselization `Q'` of the
pair `(P', J')` to an `A'`-algebra map `Q' → C'`. -/
private theorem exists_algHom_henselization_of_algebraLift
    (A' A P' Q' C C' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [CommRing C] [CommRing C']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra A' C] [Algebra A' C']
    [Algebra A C] [Algebra P' C] [Algebra P' Q'] [Algebra Q' C]
    [IsScalarTower A' A C] [IsScalarTower A' P' C] [IsScalarTower A' P' Q']
    [IsScalarTower P' Q' C] [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (J' : Ideal P')
    (hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : P' →+* D, J' ≤ K.comap f →
        ∃! g : Q' →+* D, g.comp (algebraMap P' Q') = f ∧
          J'.map (algebraMap P' Q') ≤ K.comap g)
    (c : Ideal C) (hc : HenselianPair C c)
    (hJc : ∀ g ∈ J', algebraMap P' C g ∈ c)
    (eC : (A ⊗[A'] C') ≃ₐ[A] C) :
    ∃ g : Q' →ₐ[A'] C', ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x := by
  -- the reduction of the lift, a surjection with nilpotent kernel
  set rho : C' →ₐ[A'] C :=
    (eC.restrictScalars A').toAlgHom.comp Algebra.TensorProduct.includeRight with hrhodef
  have hrhoapp : ∀ y : C', rho y = eC (1 ⊗ₜ[A'] y) := fun _ => rfl
  have hrhosurj : Function.Surjective rho :=
    (eC.restrictScalars A').surjective.comp (surjective_includeRight A' A C' hsurjA)
  have hrhoker : RingHom.ker rho = (RingHom.ker (algebraMap A' A)).map (algebraMap A' C') :=
    ker_comp_includeRight C C' hsurjA (eC.restrictScalars A')
  have hrhonil : IsNilpotent (RingHom.ker rho) := by
    rw [hrhoker]
    exact isNilpotent_ideal_map hnilA _
  -- `C'` is henselian along the preimage of `𝔠`, by Stacks 0ALI and Stacks 0DYD
  set c' : Ideal C' := Ideal.comap rho.toRingHom c with hc'def
  have hkerle : RingHom.ker rho ≤ c' := by
    intro x hx
    rw [hc'def, Ideal.mem_comap]
    have hx0 : rho x = 0 := hx
    show rho x ∈ c
    rw [hx0]
    exact Ideal.zero_mem c
  set eρ : (C' ⧸ RingHom.ker rho) ≃ₐ[A'] C :=
    Ideal.quotientKerAlgEquivOfSurjective hrhosurj with heρdef
  let : Algebra C (C' ⧸ RingHom.ker rho) := eρ.symm.toRingHom.toAlgebra
  have hsymmsurj : Function.Surjective (algebraMap C (C' ⧸ RingHom.ker rho)) :=
    eρ.symm.surjective
  have : Algebra.IsIntegral C (C' ⧸ RingHom.ker rho) :=
    Algebra.isIntegral_of_surjective hsymmsurj
  have hquothens : HenselianPair (C' ⧸ RingHom.ker rho)
      (c.map (algebraMap C (C' ⧸ RingHom.ker rho))) :=
    henselianPair_map_of_isIntegral c hc
  have hmapeq : c.map (algebraMap C (C' ⧸ RingHom.ker rho)) =
      c'.map (Ideal.Quotient.mk (RingHom.ker rho)) := by
    have hcomp : (eρ.toRingEquiv.toRingHom).comp
        (Ideal.Quotient.mk (RingHom.ker rho)) = rho.toRingHom :=
      RingHom.ext fun x => Ideal.quotientKerAlgEquivOfSurjective_mk hrhosurj x
    have h1 : c' = Ideal.comap (Ideal.Quotient.mk (RingHom.ker rho))
        (Ideal.comap eρ.toRingEquiv.toRingHom c) := by
      rw [hc'def, Ideal.comap_comap, hcomp]
    rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun y hy => ?_
    · rw [Ideal.mem_comap]
      show eρ (eρ.symm x) ∈ c
      rw [eρ.apply_symm_apply]
      exact hx
    · rw [Ideal.mem_comap] at hy
      have hyval : y = algebraMap C (C' ⧸ RingHom.ker rho) (eρ y) := by
        show y = eρ.symm (eρ y)
        rw [eρ.symm_apply_apply]
      rw [hyval]
      exact Ideal.mem_map_of_mem _ hy
  have hC'hens : HenselianPair C' c' :=
    (henselianPair_iff_of_le hkerle).mp
      ⟨henselianPair_of_le_nilradical _ (le_nilradical_of_isNilpotent hrhonil),
        hmapeq ▸ hquothens⟩
  -- the lift of the presentation, extended across the henselization
  set η₀ : P' →ₐ[A'] C' := Algebra.FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom A' P' C) rho hrhosurj hrhonil with hη₀def
  have hη₀ : ∀ x : P', rho (η₀ x) = algebraMap P' C x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ rho hrhosurj hrhonil x
  have hJc' : J' ≤ c'.comap η₀.toRingHom := by
    intro x hx
    rw [Ideal.mem_comap, hc'def, Ideal.mem_comap]
    show rho (η₀ x) ∈ c
    rw [hη₀ x]
    exact hJc x hx
  obtain ⟨η, ⟨hη1, hη2⟩, -⟩ :=
    hunivQ C' inferInstance c' hC'hens η₀.toRingHom hJc'
  have hηP : ∀ x : P', η (algebraMap P' Q' x) = η₀ x := fun x => RingHom.congr_fun hη1 x
  let ηₐ : Q' →ₐ[A'] C' :=
    { η with
      commutes' := fun a => by
        rw [IsScalarTower.algebraMap_apply A' P' Q']
        show η (algebraMap P' Q' (algebraMap A' P' a)) = algebraMap A' C' a
        rw [hηP (algebraMap A' P' a)]
        exact η₀.commutes a }
  -- the extension agrees with the structure map of `C`, by uniqueness
  have hJcC : J' ≤ c.comap (algebraMap P' C) := fun x hx => hJc x hx
  have hcond1 : (rho.toRingHom.comp η).comp (algebraMap P' Q') = algebraMap P' C := by
    refine RingHom.ext fun p => ?_
    show rho (η (algebraMap P' Q' p)) = algebraMap P' C p
    rw [hηP p, hη₀ p]
  have hcond2 : J'.map (algebraMap P' Q') ≤ c.comap (rho.toRingHom.comp η) := by
    intro x hx
    rw [Ideal.mem_comap]
    show rho (η x) ∈ c
    exact hη2 hx
  have hcond1' : (algebraMap Q' C).comp (algebraMap P' Q') = algebraMap P' C :=
    (IsScalarTower.algebraMap_eq P' Q' C).symm
  have hcond2' : J'.map (algebraMap P' Q') ≤ c.comap (algebraMap Q' C) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact Ideal.map_le_iff_le_comap.mpr hJcC
  have heq := (hunivQ C inferInstance c hc (algebraMap P' C) hJcC).unique
    ⟨hcond1, hcond2⟩ ⟨hcond1', hcond2'⟩
  refine ⟨ηₐ, fun x => ?_⟩
  rw [← hrhoapp]
  exact RingHom.congr_fun heq x

/-! ### The comparison along a henselized presentation -/

/-- **Stacks 0DZB for a chosen presentation.** Let `A' → A` be a surjection of Noetherian rings
with nilpotent kernel, let `P' → P` be a surjection of Noetherian `A'`-algebras over it with
kernel `ker(A' → A) · P'` and `P = A ⊗_{A'} P'`, let `P → B` be a surjection, let `(Q', J'Q')`
be the henselization of a pair `(P', J')` and let `C` be a ring carrying a henselian ideal `𝔠`
and presented by `Q = P ⊗_{P'} Q'` as `Q ⊗_P B`. If the localizations of `B` at the elements of
`J'` have `A'`-flat module lifts, then `B` has a flat lift to `A'` if and only if `C` does. -/
private theorem hasFlatAlgebraLift_henselization_iff_of_presentation
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A P' P B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q'] [Algebra A' C]
    [Algebra A P] [Algebra A B] [Algebra A C] [Algebra P' P] [Algebra P' B] [Algebra P B]
    [Algebra P' Q']
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (J' : Ideal P')
    (hhensQ : HenselianPair Q' (J'.map (algebraMap P' Q')))
    (hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : P' →+* D, J' ≤ K.comap f →
        ∃! g : Q' →+* D, g.comp (algebraMap P' Q') = f ∧
          J'.map (algebraMap P' Q') ≤ K.comap g)
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] B)))
    (c : Ideal C) (hc : HenselianPair C c)
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hJc : ∀ g ∈ J', e (((algebraMap P' P g) ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) ∈ c) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C := by
  -- Stacks 0AGU and 0AGV for the henselization `Q'` of the pair `(P', J')`
  obtain ⟨hflatQ, hpowQ⟩ :=
    flat_henselization_and_bijective_quotientMap P' J' Q' hhensQ hunivQ
  have hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map) := by
    have h := hpowQ 1
    rw [pow_one] at h
    exact h
  have : Module.Flat P' Q' := hflatQ
  have : IsNoetherianRing Q' :=
    (henselization_isNoetherian_and_completion_equiv P' J' Q' hhensQ hunivQ).2.1
  -- the algebra structures on `C` over the henselized presentation
  let : Algebra (P ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] Q') ((P ⊗[P'] Q') ⊗[P] B))).toAlgebra
  let : Algebra Q' C :=
    ((algebraMap (P ⊗[P'] Q') C).comp (algebraMap Q' (P ⊗[P'] Q'))).toAlgebra
  let : Algebra P' C := ((algebraMap Q' C).comp (algebraMap P' Q')).toAlgebra
  have h1 : ∀ a' : A', algebraMap A' (P ⊗[P'] Q') a' =
      algebraMap Q' (P ⊗[P'] Q') (algebraMap A' Q' a') := by
    intro a'
    have e1 : algebraMap A' (P ⊗[P'] Q') a' = (algebraMap A' P a') ⊗ₜ[P'] (1 : Q') := rfl
    have e2 : algebraMap Q' (P ⊗[P'] Q') (algebraMap A' Q' a') =
        (1 : P) ⊗ₜ[P'] (algebraMap A' Q' a') := rfl
    rw [e1, e2, IsScalarTower.algebraMap_apply A' P' P,
      IsScalarTower.algebraMap_apply A' P' Q',
      Algebra.algebraMap_eq_smul_one (R := P') (A := P),
      Algebra.algebraMap_eq_smul_one (R := P') (A := Q'), TensorProduct.smul_tmul]
  have : IsScalarTower A' Q' (P ⊗[P'] Q') := IsScalarTower.of_algebraMap_eq h1
  have : IsScalarTower Q' (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (P ⊗[P'] Q') C := IsScalarTower.to₁₃₄ A' A (P ⊗[P'] Q') C
  have : IsScalarTower A' Q' C := IsScalarTower.to₁₂₄ A' Q' (P ⊗[P'] Q') C
  have : IsScalarTower P' Q' C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' P' C := IsScalarTower.to₁₂₄ A' P' Q' C
  -- the image of `J'` in `C` lies in the henselian ideal
  have htmul : ∀ x : P', ((1 : P) ⊗ₜ[P'] (algebraMap P' Q' x) : P ⊗[P'] Q') =
      (algebraMap P' P x) ⊗ₜ[P'] (1 : Q') := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one (R := P') (A := Q'),
      Algebra.algebraMap_eq_smul_one (R := P') (A := P), TensorProduct.smul_tmul]
  have hJcC : ∀ g ∈ J', algebraMap P' C g ∈ c := by
    intro g hg
    have hval : algebraMap P' C g =
        e (((1 : P) ⊗ₜ[P'] (algebraMap P' Q' g)) ⊗ₜ[P] (1 : B)) := rfl
    rw [hval, htmul g]
    exact hJc g hg
  refine ⟨hasFlatAlgebraLift_imp_baseChange_of_presentation h0DZ2 A' A P' P B Q'
      hsurjA hnilA hsurjP hkerP hsurjB J' hquot hloc C e hAe,
    hasFlatAlgebraLift_of_baseChange_of_presentation h0DZ2 A' A P' P B Q' C
      hsurjA hnilA hsurjP hkerP hsurjB ePP hePP J' hquot hloc e hAe (fun _ => rfl)
      (fun C' _ _ eCa => ?_)⟩
  exact exists_algHom_henselization_of_algebraLift A' A P' Q' C C' hsurjA hnilA J' hunivQ
    c hc hJcC eCa

/-! ### Stacks 0DZB -/

/-- **Stacks 0DZB.** For a surjection `A' → A` of Noetherian rings with nilpotent kernel and a
finite type flat `A`-algebra `B` with `A → B_h` syntomic for every `h` in an ideal `𝔟`, flat
lifts of `B` to `A'` exist exactly when flat lifts of the henselization `Bʰ` of the pair
`(B, 𝔟)` do. -/
@[stacks 0DZB "VACUOUS: `h0DZ2` cannot be satisfied, so nothing below is evidence for the tag. \
That hypothesis is `Deformation.FlatModuleLiftBaseChangeStatement` - Stacks 0DZ2 with the \
source's hypotheses and `M` restricted to be finite over `P` - and it is refuted outright, at \
universe zero by `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement` of \
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation` and at an arbitrary universe by \
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift` of \
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationUniverse`; the second covers the \
universe parameter `u` appearing below, so the vacuity here is unconditional. Read the module \
documentation of `NodalCubicRefutation` for the counterexample; it is stated there and nowhere \
else. A square-zero variant would not rescue 0DZB, whose hypothesis on `A' -> A` is nilpotence \
of the kernel. The open route for 0DZB is its own: Stacks 0DZD's henselization functor, which \
consumes this lemma, and where the module being lifted comes from a syntomic `B_h` whose higher \
`Ext` kills the obstruction - vanishing that 0DZ2 never assumes. Independently of all that, the \
henselization of the pair `(B, b)` is described here by the henselian-pair condition `hhens` \
together with its universal property `huniv`, as in Stacks 0DZC, rather than by a chosen model, \
and the syntomic hypothesis is the affine reading. See the implementation notes"]
public theorem hasFlatAlgebraLift_henselization_iff
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A Bh := by
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A' Bh := ((algebraMap A Bh).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A Bh := IsScalarTower.of_algebraMap_eq' rfl
  -- the polynomial presentation of `B`
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let : Algebra (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) :=
    (MvPolynomial.map (algebraMap A' A)).toAlgebra
  have hsurjP : Function.Surjective
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) :=
    MvPolynomial.map_surjective _ hsurjA
  have hkerP : RingHom.ker
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (MvPolynomial (Fin n) A')) :=
    MvPolynomial.ker_map (algebraMap A' A)
  have : IsScalarTower A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) := by
    refine IsScalarTower.of_algebraMap_eq fun a' => ?_
    show MvPolynomial.C (algebraMap A' A a') =
      MvPolynomial.map (algebraMap A' A) (MvPolynomial.C a')
    rw [MvPolynomial.map_C]
  let : Algebra (MvPolynomial (Fin n) A) B := f.toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hsurjB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B) := hf
  let : Algebra (MvPolynomial (Fin n) A') B :=
    ((algebraMap (MvPolynomial (Fin n) A) B).comp
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (MvPolynomial (Fin n) A) B :=
    IsScalarTower.to₁₃₄ A' A (MvPolynomial (Fin n) A) B
  have : IsScalarTower A' (MvPolynomial (Fin n) A') B :=
    IsScalarTower.to₁₂₄ A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B
  have hsurjPB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A') B) :=
    hsurjB.comp hsurjP
  have hnoethB : IsNoetherianRing B :=
    isNoetherianRing_of_surjective (MvPolynomial (Fin n) A) B
      (algebraMap (MvPolynomial (Fin n) A) B) hsurjB
  -- the preimage of `𝔟` in the lifted polynomial algebra, and its henselization
  set I' : Ideal (MvPolynomial (Fin n) A') :=
    Ideal.comap (algebraMap (MvPolynomial (Fin n) A') B) b with hI'def
  have hb : I'.map (algebraMap (MvPolynomial (Fin n) A') B) = b :=
    Ideal.map_comap_of_surjective _ hsurjPB b
  let Q' : Type u := (henselization (MvPolynomial (Fin n) A') I' : Type u)
  let : Algebra A' Q' :=
    ((algebraMap (MvPolynomial (Fin n) A') Q').comp
      (algebraMap A' (MvPolynomial (Fin n) A'))).toAlgebra
  have : IsScalarTower A' (MvPolynomial (Fin n) A') Q' :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hhensQ : HenselianPair Q'
      (I'.map (algebraMap (MvPolynomial (Fin n) A') Q')) :=
    henselianPair_henselization (MvPolynomial (Fin n) A') I'
  have hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ g : MvPolynomial (Fin n) A' →+* D, I' ≤ K.comap g →
        ∃! G : Q' →+* D,
          G.comp (algebraMap (MvPolynomial (Fin n) A') Q') = g ∧
            I'.map (algebraMap (MvPolynomial (Fin n) A') Q') ≤ K.comap G :=
    henselization_universalProperty (MvPolynomial (Fin n) A') I'
  -- Stacks 0DYE for the surjection `(P', 𝔭') → (B, 𝔟)`
  let : Algebra (MvPolynomial (Fin n) A') Bh :=
    ((algebraMap B Bh).comp (algebraMap (MvPolynomial (Fin n) A') B)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') B Bh :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsIntegral (MvPolynomial (Fin n) A') B :=
    Algebra.isIntegral_of_surjective hsurjPB
  have hmapI : I' ≤ b.comap (algebraMap (MvPolynomial (Fin n) A') B) := le_rfl
  have hPBh : I' ≤ (b.map (algebraMap B Bh)).comap
      (algebraMap (MvPolynomial (Fin n) A') Bh) := by
    intro x hx
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) A') B Bh]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨gh, ⟨hgh1, hgh2⟩, -⟩ := hunivQ Bh inferInstance (b.map (algebraMap B Bh)) hhens
    (algebraMap (MvPolynomial (Fin n) A') Bh) hPBh
  let ghₐ : Q' →ₐ[MvPolynomial (Fin n) A'] Bh :=
    { gh with commutes' := fun x => RingHom.congr_fun hgh1 x }
  have hzero : PrimeSpectrum.zeroLocus (b : Set B) =
      PrimeSpectrum.zeroLocus
        (I'.map (algebraMap (MvPolynomial (Fin n) A') B) : Set B) := by
    rw [hb]
  have hbij := henselization_tensorProduct_bijective_of_isIntegral
    (MvPolynomial (Fin n) A') Q' B Bh I' b hmapI hzero hhensQ hhens hunivQ huniv ghₐ hgh2
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorHenselization (MvPolynomial (Fin n) A')
    (MvPolynomial (Fin n) A) B Q' Bh ghₐ hbij
  -- the base change of the polynomial presentation along `A' → A`
  have hePP : ∀ x : MvPolynomial (Fin n) A',
      MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A ((1 : A) ⊗ₜ[A'] x) =
        algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) x := by
    intro x
    rw [← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) A' A x,
      AlgEquiv.apply_symm_apply]
    rfl
  -- the image of `𝔭'` in `Bʰ` lies in the henselian ideal
  have hJc : ∀ g ∈ I',
      e (((algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g)
          ⊗ₜ[MvPolynomial (Fin n) A'] (1 : Q'))
        ⊗ₜ[MvPolynomial (Fin n) A] (1 : B)) ∈ b.map (algebraMap B Bh) := by
    intro g hg
    rw [he (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g),
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) A')
        (MvPolynomial (Fin n) A) B g]
    exact Ideal.mem_map_of_mem _ hg
  refine hasFlatAlgebraLift_henselization_iff_of_presentation h0DZ2 A' A
    (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B Q' Bh hsurjA hnilA hsurjP hkerP
    hsurjB (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A) hePP I' hhensQ hunivQ
    (fun g hg => exists_flatModuleLift_localization_of_syntomic A' A
      (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B hsurjA hnilA hsurjP hkerP b hsyn
      g hg)
    (b.map (algebraMap B Bh)) hhens e (fun a => ?_) hJc
  show algebraMap A Bh a = e (((algebraMap A (MvPolynomial (Fin n) A) a)
    ⊗ₜ[MvPolynomial (Fin n) A'] (1 : Q')) ⊗ₜ[MvPolynomial (Fin n) A] (1 : B))
  rw [he (algebraMap A (MvPolynomial (Fin n) A) a),
    ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A) B,
    ← IsScalarTower.algebraMap_apply A B Bh]

/-- **The first implication of Stacks 0DZB.** A flat lift of `B` to `A'` gives one of the
henselization of the pair `(B, 𝔟)`: the henselization of the polynomial presentation `P'`
presents `Bʰ`, and Stacks 0DZ2 transports the module lift from `P'` to it. -/
public theorem hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A Bh :=
  (hasFlatAlgebraLift_henselization_iff h0DZ2 A' A B hsurjA hnilA b hsyn Bh hhens huniv).mp

/-- **The second implication of Stacks 0DZB.** A flat lift of the henselization of the pair
`(B, 𝔟)` to `A'` gives one of `B`: a flat algebra lift of `Bʰ` is an `A'`-flat module lift over
the henselized presentation `Q'`, and Stacks 0DZ2 transports that lift back to `P'`. -/
public theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A Bh → HasFlatAlgebraLift A' A B :=
  (hasFlatAlgebraLift_henselization_iff h0DZ2 A' A B hsurjA hnilA b hsyn Bh hhens huniv).mpr

end Deformation

end
