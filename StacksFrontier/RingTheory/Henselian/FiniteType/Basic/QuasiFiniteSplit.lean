module

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.Artinian.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.EtaleSection

/-!
# The quasi-finite split

Isolating idempotents for the quasi-finite locus over the closed point, and the splitting of a
finite type algebra over a henselian local ring as a product `A × B` with `A` module-finite and
`B` not quasi-finite at any prime over the maximal ideal (`exists_prod_finite_not_quasiFiniteAt`).
-/

@[expose] public section

universe u v

/-!
## Isolating idempotents for a nonempty quasi-finite locus

Given the henselian étale-point section of `henselian_etale_residue_point_section` — taken below
as the hypothesis `hsec` — an isolating idempotent exists whenever the quasi-finite locus over
`𝔪` is finite and nonempty. On top of that input the remaining steps are `IsIdempotentElem`,
`Module.Finite` and `primesOver` bookkeeping:

* For each of the finitely many quasi-finite primes `𝔮` over `𝔪`, Stacks 00UJ
  (`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`) gives an étale `R'_𝔮`, a prime
  `P_𝔮` over `𝔪` with residue-field bijectivity, and an idempotent `e_𝔮 ∈ R'_𝔮 ⊗_R S` with
  `Module.Finite R'_𝔮 (Localization.Away e_𝔮)` and an isolation clause.
* Applying `hsec` to `(R'_𝔮, P_𝔮)` gives a retraction `σ_𝔮 : R'_𝔮 →ₐ[R] R`. Pushing `e_𝔮` along
  `σ_𝔮 ⊗ id_S : R'_𝔮 ⊗_R S → R ⊗_R S ≅ S`, a ring hom and hence idempotent-preserving, yields an
  idempotent `f_𝔮 ∈ S` isolating `𝔮` on the closed fibre, with `Localization.Away f_𝔮`
  module-finite over `R` by descent along the section.
* The finitely many orthogonal closed-fibre idempotents `f_𝔮` combine into a single global
  idempotent `f ∈ S`, using `IsIdempotentElem.mul` and `IsIdempotentElem.one_sub`.
* Then `S ⧸ span{1-f}` is module-finite over `R`, the finite part, while `S ⧸ span{f}` has no
  quasi-finite prime over `𝔪` (`Algebra.quasiFinite_iff` 00PM,
  `QuasiFinite.iff_finite_primesOver`), because any such prime would be one of the removed
  quasi-finite points.
-/

/-- The henselian section of `henselian_etale_residue_point_section`, phrased as a hypothesis
`hsec` and specialized to the étale `Type u` algebra `R'` produced by Stacks 00UJ. Since `hsec`
already carries the residue identity and quantifies over `Type u`, this is a direct
application. -/
lemma per_point_section_with_residue
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (hsec : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
        (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)],
        Function.Bijective
          ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
              Ideal.LiesOver.over) →
        ∃ σ : R' →ₐ[R] R, ∀ r' : R', r' - algebraMap R R' (σ r') ∈ P)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
          Ideal.LiesOver.over)) :
    ∃ σ : R' →ₐ[R] R, ∀ r' : R', r' - algebraMap R R' (σ r') ∈ P :=
  hsec R' P hres

/-- The map `(lid) ∘ (σ ⊗ id_S)` sends `a ⊗ b` to `σ a * b`. -/
private theorem lid_comp_map_tmul {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S] (σ : R' →ₐ[R] R) (a : R') (b : S) :
    ((Algebra.TensorProduct.lid R S).toAlgHom.comp
      (Algebra.TensorProduct.map σ (AlgHom.id R S))) (a ⊗ₜ[R] b) = algebraMap R S (σ a) * b := by
  simp [Algebra.smul_def]

/-- Module-finite descent along a section. Let `R` be henselian local, let `R' : Type u` be an
étale `R`-algebra carrying a section `σ : R' →ₐ[R] R`, and let `e ∈ R' ⊗_R S` be an idempotent
whose `e`-localization is module-finite over `R'`. Then the image `g = δ e`, where
`δ = (lid) ∘ (σ ⊗ id_S) : R' ⊗_R S →ₐ[R] S`, cuts out a module-finite `g`-part: the quotient
`S ⧸ span{1 - g} ≅ S_g` is module-finite over `R`.

This descends `Module.Finite R' (Localization.Away e)` along `σ` via the base-change
identification `(R' ⊗_R S)_e ⊗_{R',σ} R ≅ S_g` (Zariski's main property, tag 00Q9). -/
lemma per_point_finite_descent
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (σ : R' →ₐ[R] R)
    (e : TensorProduct R R' S) (he : IsIdempotentElem e)
    (hfin : Module.Finite R' (Localization.Away e)) :
    Module.Finite R
      (S ⧸ Ideal.span {1 - ((Algebra.TensorProduct.lid R S).toAlgHom.comp
        (Algebra.TensorProduct.map σ (AlgHom.id R S))) e}) := by
  -- The g-part `S ⧸ span{1-g}` is `IsLocalization.Away g`
  -- (`IsLocalization.Away.quotient_of_isIdempotentElem`). The ring hom
  -- `δ : R'⊗S →ₐ[R] S` sends `e ↦ g`, inducing a SURJECTIVE map of localizations
  -- `Φ : Localization.Away e → S ⧸ span{1-g}` (δ surjective + quotient map surjective).
  -- `Φ` is `σ`-semilinear (Φ ∘ algebraMap R' = algebraMap R ∘ σ), and `σ` is surjective
  -- (it is a section), so `RingHomSurjective σ`. Hence `Module.Finite R' (Localization.Away e)`
  -- (= `hfin`) transfers to `Module.Finite R (S ⧸ span{1-g})` via `Module.Finite.of_surjective`.
  set δ : TensorProduct R R' S →ₐ[R] S :=
    (Algebra.TensorProduct.lid R S).toAlgHom.comp (Algebra.TensorProduct.map σ (AlgHom.id R S))
        with hδ
  set g : S := δ e with hg
  have hgidem : IsIdempotentElem g := he.map δ
  have hQloc : IsLocalization.Away g (S ⧸ Ideal.span {1 - g}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem hgidem
  let Φ : Localization.Away e →+* (S ⧸ Ideal.span {1 - g}) :=
    IsLocalization.Away.map (Localization.Away e) (S ⧸ Ideal.span {1 - g}) δ.toRingHom e
  have hcomp : Φ.comp (algebraMap (TensorProduct R R' S) (Localization.Away e))
      = (algebraMap S (S ⧸ Ideal.span {1 - g})).comp δ.toRingHom := IsLocalization.map_comp _
  -- σ surjective ⇒ RingHomSurjective
  have hσsurj : Function.Surjective (σ : R' → R) := fun r => ⟨algebraMap R R' r, by simp⟩
  have hσRsurj : Function.Surjective (σ.toRingHom : R' →+* R) := hσsurj
  have : RingHomSurjective (σ.toRingHom : R' →+* R) := ⟨hσRsurj⟩
  -- δ surjective
  have hδsurj : Function.Surjective (δ : TensorProduct R R' S → S) :=
    fun s => ⟨1 ⊗ₜ s, by simp [hδ, lid_comp_map_tmul]⟩
  -- Φ surjective
  have hΦsurj : Function.Surjective (Φ : Localization.Away e → _) := by
    have h1 : Function.Surjective ((algebraMap S (S ⧸ Ideal.span {1 - g})).comp δ.toRingHom) :=
      (Ideal.Quotient.mk_surjective).comp hδsurj
    rw [← hcomp] at h1
    exact Function.Surjective.of_comp h1
  -- semilinearity: Φ ∘ algebraMap R' = algebraMap R ∘ σ
  have hsemi : ∀ r' : R', Φ (algebraMap R' (Localization.Away e) r')
      = algebraMap R (S ⧸ Ideal.span {1 - g}) (σ r') := by
    intro r'
    rw [IsScalarTower.algebraMap_apply R' (TensorProduct R R' S) (Localization.Away e) r']
    rw [show Φ (algebraMap (TensorProduct R R' S) (Localization.Away e) (algebraMap R'
        (TensorProduct R R' S) r'))
        = (Φ.comp (algebraMap (TensorProduct R R' S) (Localization.Away e))) (algebraMap R'
            (TensorProduct R R' S) r') from rfl]
    rw [hcomp]
    simp only [RingHom.comp_apply]
    have hδr : δ.toRingHom (algebraMap R' (TensorProduct R R' S) r') = algebraMap R S (σ r') := by
      rw [Algebra.TensorProduct.algebraMap_apply]
      exact (lid_comp_map_tmul σ r' 1).trans (mul_one _)
    rw [hδr, ← IsScalarTower.algebraMap_apply R S (S ⧸ Ideal.span {1 - g}) (σ r')]
  -- build the σ-semilinear surjection and conclude module-finiteness
  let L : Localization.Away e →ₛₗ[σ.toRingHom] (S ⧸ Ideal.span {1 - g}) :=
    { toFun := Φ
      map_add' := Φ.map_add
      map_smul' := by
        intro r' x
        change Φ (r' • x) = σ.toRingHom r' • Φ x
        rw [Algebra.smul_def r' x, map_mul, hsemi, Algebra.smul_def]
        rfl }
  exact Module.Finite.of_surjective L hΦsurj

/-- The per-point isolating idempotent. For a single quasi-finite prime `𝔮` of `S` lying over
`𝔪`, and given the henselian section hypothesis `hsec`, there is an idempotent `g ∈ S` whose
`g`-part `S ⧸ span{1-g}` is module-finite over `R` and which satisfies `g ∉ 𝔮`, so that `𝔮` lies
in the open `D(g)` captured by the finite part.

Stacks 00UJ (`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`) applied to `𝔮` supplies
an étale `R'`, a prime `P` over `𝔪` with residue bijectivity, an idempotent `e ∈ R' ⊗_R S` with
`Module.Finite R' (Localization.Away e)`, and a prime `P'` of `R' ⊗_R S` over `𝔮` with `e ∉ P'`.
Applying `hsec` to `(R', P)` gives `σ : R' →ₐ[R] R`, and pushing `e` along
`δ = (lid) ∘ (σ ⊗ id_S) : R' ⊗_R S →ₐ[R] S` gives `g := δ e`, idempotent by
`IsIdempotentElem.map`. Module-finiteness of the `g`-part is `per_point_finite_descent`, and
`g ∉ 𝔮` follows from `e ∉ P'` together with the residue compatibility of `σ`. -/
lemma isolating_idempotent_per_point
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (hsec : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
        (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)],
        Function.Bijective
          ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
              Ideal.LiesOver.over) →
        ∃ σ : R' →ₐ[R] R, ∀ r' : R', r' - algebraMap R R' (σ r') ∈ P)
    (𝔮 : Ideal S) [𝔮.IsPrime] [𝔮.LiesOver (IsLocalRing.maximalIdeal R)]
    [Algebra.QuasiFiniteAt R 𝔮] :
    ∃ g : S, IsIdempotentElem g ∧ Module.Finite R (S ⧸ Ideal.span {1 - g}) ∧ g ∉ 𝔮 := by
  -- Module-finiteness of the g-part together with g ∉ 𝔮 places 𝔮 in the finite part D(g); neither
  -- g = 0 nor g = 1 works in general, so a nontrivial idempotent is genuinely needed.
  -- Step 1: Stacks 00UJ produces an étale R' (Type u), a κ-rational prime P over 𝔪, an idempotent
  -- e ∈ R'⊗S, and a prime P' of R'⊗S over both P and 𝔮 with e ∉ P', plus finiteness over R'.
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, hPP', hcomap, heP', hbij, hfin, _⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (IsLocalRing.maximalIdeal R) 𝔮
  -- Step 2: the henselian section σ : R' →ₐ[R] R, residue-compatible with P.
  obtain ⟨σ, hσP⟩ := per_point_section_with_residue R hsec R' P hbij
  -- Step 3: push e to g := δ e along δ = (lid) ∘ (σ ⊗ id_S).
  set δ : TensorProduct R R' S →ₐ[R] S :=
    (Algebra.TensorProduct.lid R S).toAlgHom.comp (Algebra.TensorProduct.map σ (AlgHom.id R S))
      with hδ
  refine ⟨δ e, he.map δ, ?_, ?_⟩
  · -- module-finiteness of the g-part, by descent along the section.
    exact per_point_finite_descent R S R' σ e he hfin
  · -- g ∉ 𝔮 : from e ∉ P', the residue compatibility hσP, and comap includeRight P' = 𝔮.
    intro hg
    apply heP'
    rw [← hcomap, Ideal.mem_comap] at hg
    have hgP' : Algebra.TensorProduct.includeRight (δ e) ∈ P' := hg
    -- π and π ∘ includeRight ∘ δ agree on R'⊗S as R-algebra homs into the quotient by P'.
    have hagree : (Ideal.Quotient.mkₐ R P' : TensorProduct R R' S →ₐ[R] _)
        = (Ideal.Quotient.mkₐ R P').comp (Algebra.TensorProduct.includeRight.comp δ) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      change (Ideal.Quotient.mkₐ R P') (a ⊗ₜ[R] b)
          = (Ideal.Quotient.mkₐ R P') (Algebra.TensorProduct.includeRight (δ (a ⊗ₜ[R] b)))
      have hδab : δ (a ⊗ₜ[R] b) = (algebraMap R S) (σ a) * b := by
        exact lid_comp_map_tmul σ a b
      rw [hδab, map_mul]
      have hir : Algebra.TensorProduct.includeRight ((algebraMap R S) (σ a))
          = (algebraMap R (TensorProduct R R' S)) (σ a) := by
        rw [← Algebra.TensorProduct.includeRight.commutes (σ a)]
      rw [hir, Algebra.TensorProduct.includeRight_apply]
      have key : a ⊗ₜ[R] b
          - (algebraMap R (TensorProduct R R' S)) (σ a) * (1 ⊗ₜ[R] b) ∈ P' := by
        have ha : a ⊗ₜ[R] b
            = (algebraMap R' (TensorProduct R R' S) a) * (1 ⊗ₜ[R] b) := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
          simp
        have hb : (algebraMap R (TensorProduct R R' S)) (σ a)
            = algebraMap R' (TensorProduct R R' S) (algebraMap R R' (σ a)) := by
          rw [← IsScalarTower.algebraMap_apply]
        rw [ha, hb, ← sub_mul]
        apply Ideal.mul_mem_right
        rw [← map_sub]
        have hmemP : a - algebraMap R R' (σ a) ∈ P := hσP a
        have hlo : P = Ideal.under R' P' := Ideal.LiesOver.over
        rw [hlo] at hmemP
        exact hmemP
      change (Ideal.Quotient.mkₐ R P') (a ⊗ₜ[R] b)
          = (Ideal.Quotient.mkₐ R P') ((algebraMap R (TensorProduct R R' S)) (σ a) * (1 ⊗ₜ[R] b))
      simp only [Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      exact key
    have hfe := congrArg (fun (h : TensorProduct R R' S →ₐ[R] _) => h e) hagree
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hfe
    rw [Ideal.Quotient.eq] at hfe
    have hsub : e - Algebra.TensorProduct.includeRight (δ e) ∈ P' := hfe
    have := Ideal.add_mem P' hsub hgP'
    simpa using this

/-- Joining finitely many isolating idempotents. Given a finite set `Q` of primes of `S` and, for
each `𝔮 ∈ Q`, an idempotent `g 𝔮` with `S ⧸ span{1 - g 𝔮}` module-finite over `R` and `g 𝔮 ∉ 𝔮`,
there is a single idempotent `f ∈ S` with `S ⧸ span{1 - f}` module-finite over `R` and `f ∉ 𝔮` for
every `𝔮 ∈ Q`.

Take the join `f := ⊔_{𝔮 ∈ Q} g 𝔮`, i.e. iterate `a ⊔ b = a + b - a*b` on idempotents. The
`f`-part is a finite product of clopen pieces, each a localization by an idempotent of some
`S_{g 𝔮}`, hence module-finite over `R`. And `f ∉ 𝔮` because `g 𝔮 ∉ 𝔮` while `g 𝔮 ≤ f` in the
idempotent lattice, that is, `g 𝔮 = f * g 𝔮`. -/
lemma combine_isolating_idempotents
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (Q : Set (Ideal S)) (hQfin : Q.Finite)
    (g : Ideal S → S)
    (hgidem : ∀ 𝔮 ∈ Q, IsIdempotentElem (g 𝔮))
    (hgfin : ∀ 𝔮 ∈ Q, Module.Finite R (S ⧸ Ideal.span {1 - g 𝔮}))
    (hgmem : ∀ 𝔮 ∈ Q, ∀ _ : 𝔮.IsPrime, g 𝔮 ∉ 𝔮) :
    ∃ f : S, IsIdempotentElem f ∧ Module.Finite R (S ⧸ Ideal.span {1 - f}) ∧
      (∀ 𝔮 ∈ Q, ∀ _ : 𝔮.IsPrime, f ∉ 𝔮) := by
  -- Induction over the finite set Q, joining idempotents by a ⊔ b = a + b - a*b: the join's
  -- finite part splits as the product of the a-part and the (b - a*b)-part, and f ∉ 𝔮 follows
  -- from g 𝔮 ≤ f.
  classical
  have hfactor_alg : ∀ {I J : Ideal S} (h : I ≤ J) (r : R),
      (Ideal.Quotient.factor h) (algebraMap R (S ⧸ I) r) = algebraMap R (S ⧸ J) r :=
    fun h r => (Ideal.Quotient.factorₐ R h).commutes r
  have hquot_le_fin : ∀ {I J : Ideal S}, I ≤ J → Module.Finite R (S ⧸ I) →
      Module.Finite R (S ⧸ J) := by
    intro I J hle hI
    exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  have hjoin_fin : ∀ (a b : S), IsIdempotentElem a → IsIdempotentElem b →
      Module.Finite R (S ⧸ Ideal.span {1 - a}) → Module.Finite R (S ⧸ Ideal.span {1 - b}) →
      Module.Finite R (S ⧸ Ideal.span {1 - (a + b - a*b)}) := by
    intro a b ha hb hfa hfb
    have hbleb' : Ideal.span {1 - b} ≤ Ideal.span {1 - (b - a*b)} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨1 - b, by linear_combination (-(1 - a))*hb.eq⟩
    have hfb' : Module.Finite R (S ⧸ Ideal.span {1 - (b - a*b)}) := hquot_le_fin hbleb' hfb
    have hcop : IsCoprime (Ideal.span {1-a}) (Ideal.span {1 - (b - a*b)}) := by
      rw [Ideal.isCoprime_iff_add, Ideal.one_eq_top, Ideal.eq_top_iff_one]
      have h1a : (1 - a) ∈ Ideal.span {1 - a} := Ideal.mem_span_singleton_self _
      have ha_mem : a ∈ Ideal.span {1 - (b - a*b)} := by
        rw [Ideal.mem_span_singleton']; exact ⟨a, by linear_combination (b)*ha.eq⟩
      simpa using Submodule.add_mem_sup h1a ha_mem
    have hfact : Ideal.span {(1:S) - (a + b - a*b)} = Ideal.span {(1-a) * (1 - (b - a*b))} := by
      congr 1; rw [Set.singleton_eq_singleton_iff]; linear_combination b*ha.eq
    have hspaninf : Ideal.span {(1-a) * (1 - (b - a*b))}
        = Ideal.span {1-a} ⊓ Ideal.span {1 - (b - a*b)} := by
      have hb'idem : IsIdempotentElem (b - a*b) := by
        change (b - a*b)*(b-a*b) = b - a*b; linear_combination (1 - 2*a + a*a)*hb.eq + b*ha.eq
      have hv : IsIdempotentElem (1 - (b - a*b)) := hb'idem.one_sub
      apply le_antisymm
      · exact le_inf (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _))
          (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
      · rintro x ⟨hxu, hxv⟩
        simp only [SetLike.mem_coe, Ideal.mem_span_singleton] at hxu hxv ⊢
        obtain ⟨c, rfl⟩ := hxu
        obtain ⟨d, hd⟩ := hxv
        exact ⟨c * (1 - (b - a*b)), by
          linear_combination (1 - (1 - (b - a*b))) * hd - (d + (1-a) * c) * hv.eq⟩
    rw [hfact, hspaninf]
    have hfinprod : Module.Finite R ((S ⧸ Ideal.span {1-a}) × (S ⧸ Ideal.span {1-(b-a*b)})) :=
      Module.Finite.prod
    let e : (S ⧸ Ideal.span {1-a} ⊓ Ideal.span {1-(b-a*b)}) ≃+*
        (S ⧸ Ideal.span {1-a}) × (S ⧸ Ideal.span {1-(b-a*b)}) :=
      Ideal.quotientInfEquivQuotientProd _ _ hcop
    have hefwd : ∀ (r : R), e (algebraMap R _ r) = algebraMap R _ r := by
      intro r
      rw [Prod.algebraMap_apply]
      apply Prod.ext
      · rw [Ideal.quotientInfEquivQuotientProd_fst]; exact hfactor_alg _ r
      · rw [Ideal.quotientInfEquivQuotientProd_snd]; exact hfactor_alg _ r
    exact Module.Finite.equiv (AlgEquiv.ofRingEquiv (f := e) hefwd).symm.toLinearEquiv
  -- induction over the finite locus
  suffices H : ∀ (T : Set (Ideal S)), T.Finite → T ⊆ Q →
      ∃ f : S, IsIdempotentElem f ∧ Module.Finite R (S ⧸ Ideal.span {1 - f}) ∧
        (∀ 𝔮 ∈ T, ∀ _ : 𝔮.IsPrime, f ∉ 𝔮) from H Q hQfin le_rfl
  intro T hTfin
  induction T, hTfin using Set.Finite.induction_on with
  | empty =>
    intro _
    refine ⟨0, IsIdempotentElem.zero, ?_, ?_⟩
    · rw [sub_zero, Ideal.span_singleton_one]
      infer_instance
    · intro 𝔮 h𝔮 _; exact absurd h𝔮 (by simp)
  | @insert 𝔮₀ T' h𝔮₀notin hT'fin IH =>
    intro hsub
    have hsubT' : T' ⊆ Q := fun x hx => hsub (Set.mem_insert_of_mem _ hx)
    have h𝔮₀Q : 𝔮₀ ∈ Q := hsub (Set.mem_insert _ _)
    obtain ⟨a, ha, hfa, hamem⟩ := IH hsubT'
    set b := g 𝔮₀ with hbdef
    have hb : IsIdempotentElem b := hgidem 𝔮₀ h𝔮₀Q
    have hfb : Module.Finite R (S ⧸ Ideal.span {1 - b}) := hgfin 𝔮₀ h𝔮₀Q
    have hbmem : ∀ _ : 𝔮₀.IsPrime, b ∉ 𝔮₀ := hgmem 𝔮₀ h𝔮₀Q
    refine ⟨a + b - a*b, ?_, ?_, ?_⟩
    · change (a + b - a*b)*(a + b - a*b) = a + b - a*b
      linear_combination (1 - 2*b + b*b) * ha.eq + (1 - 2*a + a*a) * hb.eq + (b - b*b) * ha.eq
    · exact hjoin_fin a b ha hb hfa hfb
    · intro 𝔮 h𝔮 hprime
      rcases Set.mem_insert_iff.mp h𝔮 with h | h
      · subst h
        intro hmem
        apply hbmem hprime
        have hbeq : (a + b - a*b) * b = b := by linear_combination -a * hb.eq + hb.eq
        rw [← hbeq]
        exact Ideal.mul_mem_right b 𝔮 hmem
      · intro hmem
        apply hamem 𝔮 h hprime
        have haeq : (a + b - a*b) * a = a := by linear_combination ha.eq - b*ha.eq
        rw [← haeq]
        exact Ideal.mul_mem_right a 𝔮 hmem

/-- The complement of an isolating idempotent carries no quasi-finite prime over `𝔪`. Let `f` be
an idempotent of `S` such that `f ∉ 𝔮` for every quasi-finite prime `𝔮` of `S` lying over `𝔪`,
i.e. all quasi-finite points over `𝔪` lie in the open `D(f)`. Then the complementary quotient
`S ⧸ span{f}` has no prime over `𝔪` at which `R` is quasi-finite.

A prime `𝔭` of `S ⧸ span{f}` over `𝔪` pulls back to a prime `𝔮` of `S` containing `f` and lying
over `𝔪`. As `f` is idempotent and `f ∈ 𝔮`, the element `1-f` is a unit in `S_𝔮`, so
`(S ⧸ span{f})_𝔭 ≅ S_𝔮` as `R`-algebras; quasi-finiteness at `𝔭` would therefore put `𝔮` in the
quasi-finite locus, contradicting `f ∉ 𝔮`. -/
lemma complement_not_qf_of_mem
    (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (f : S) (hf : IsIdempotentElem f)
    (hcov : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], 𝔮.LiesOver (IsLocalRing.maximalIdeal R) →
        Algebra.QuasiFiniteAt R 𝔮 → f ∉ 𝔮) :
    ∀ (𝔮 : Ideal (S ⧸ Ideal.span {f})) [𝔮.IsPrime],
      𝔮.LiesOver (IsLocalRing.maximalIdeal R) → ¬ Algebra.QuasiFiniteAt R 𝔮 := by
  -- A prime 𝔭 of S⧸span{f} over 𝔪 pulls back to a prime 𝔮 ∋ f of S over 𝔪. Since f is idempotent
  -- and f ∈ 𝔮, the element 1-f is a unit in S_𝔮, so (S⧸span{f})_𝔭 ≅ S_𝔮 as R-algebras; hence
  -- QuasiFiniteAt R 𝔭 gives QuasiFiniteAt R 𝔮, and hcov forces f ∉ 𝔮, contradicting f ∈ 𝔮.
  intro 𝔭 _ hlo hqf
  set π : S →+* (S ⧸ Ideal.span {f}) := Ideal.Quotient.mk (Ideal.span {f}) with hπ
  set 𝔮 : Ideal S := Ideal.comap π 𝔭 with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime π 𝔭
  have heq : 𝔮 = Ideal.comap π 𝔭 := h𝔮
  -- f ∈ 𝔮 since π f = 0
  have hfmem : f ∈ 𝔮 := by
    rw [h𝔮, Ideal.mem_comap]
    show π f ∈ 𝔭
    have hπf : π f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    rw [hπf]; exact 𝔭.zero_mem
  -- f maps to 0 in the localization at 𝔮 (1 - f is a unit there, f(1-f) = 0)
  have hfzero : (algebraMap S (Localization.AtPrime 𝔮)) f = 0 := by
    have h1f : (1 - f) ∈ 𝔮.primeCompl := by
      intro hmem
      have : (1 : S) ∈ 𝔮 := by
        simpa using Ideal.add_mem 𝔮 hfmem hmem
      exact h𝔮p.ne_top (Ideal.eq_top_of_isUnit_mem 𝔮 this isUnit_one)
    have hunit : IsUnit ((algebraMap S (Localization.AtPrime 𝔮)) (1 - f)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮) 𝔮 (1 - f)).mpr h1f
    have hprod : f * (1 - f) = 0 := by
      have hff : f * f = f := hf
      linear_combination -hff
    have hmul : (algebraMap S (Localization.AtPrime 𝔮)) f *
        (algebraMap S (Localization.AtPrime 𝔮)) (1 - f) = 0 := by
      rw [← map_mul, hprod, map_zero]
    exact (hunit.mul_left_eq_zero).mp hmul
  have hcompl : ∀ x : S, π x ∈ 𝔭.primeCompl → x ∈ 𝔮.primeCompl := fun x hx hxq => hx hxq
  -- the comparison map between the two localizations is bijective
  let g := Localization.localRingHom 𝔮 𝔭 π heq
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨⟨x, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hbcompl : b ∈ 𝔮.primeCompl := hcompl b hs
    exact ⟨IsLocalization.mk' (Localization.AtPrime 𝔮) a (⟨b, hbcompl⟩ : 𝔮.primeCompl),
      by rw [Localization.localRingHom_mk']⟩
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    rw [Localization.localRingHom_mk'] at hz
    rw [IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨m, hm⟩, hmeq⟩ := hz
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective m
    simp only at hmeq
    have huamem : u * a ∈ Ideal.span {f} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]; exact hmeq
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp huamem
    have hua_alg : (algebraMap S (Localization.AtPrime 𝔮)) (u * a) = 0 := by
      rw [hc, map_mul, hfzero, zero_mul]
    rw [map_mul] at hua_alg
    have huunit : IsUnit ((algebraMap S (Localization.AtPrime 𝔮)) u) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮) 𝔮 u).mpr (hcompl u hm)
    have ha_alg : (algebraMap S (Localization.AtPrime 𝔮)) a = 0 :=
      huunit.mul_right_eq_zero.mp hua_alg
    change IsLocalization.mk' (Localization.AtPrime 𝔮) a (⟨b, hb⟩ : 𝔮.primeCompl) = 0
    rw [IsLocalization.mk'_eq_mul_mk'_one, ha_alg, zero_mul]
  -- upgrade to an R-algebra isomorphism of the localizations
  let e : Localization.AtPrime 𝔮 ≃+* Localization.AtPrime 𝔭 :=
    RingEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hcompat : ∀ (r : R), e ((algebraMap R (Localization.AtPrime 𝔮)) r)
      = (algebraMap R (Localization.AtPrime 𝔭)) r := by
    intro r
    change g ((algebraMap R (Localization.AtPrime 𝔮)) r) = (algebraMap R (Localization.AtPrime 𝔭)) r
    rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime 𝔮)]
    rw [Localization.localRingHom_to_map]
    rw [IsScalarTower.algebraMap_apply R (S ⧸ Ideal.span {f}) (Localization.AtPrime 𝔭)]
    congr 1
  let ea : Localization.AtPrime 𝔮 ≃ₐ[R] Localization.AtPrime 𝔭 := AlgEquiv.ofRingEquiv hcompat
  -- transfer quasi-finiteness along the iso
  have hqf𝔮 : Algebra.QuasiFinite R (Localization.AtPrime 𝔮) :=
    (Algebra.QuasiFinite.iff_of_algEquiv ea).mpr hqf
  -- 𝔮 also lies over 𝔪
  have hlo𝔮 : 𝔮.LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    have hpover : (IsLocalRing.maximalIdeal R) = Ideal.under R 𝔭 := hlo.over
    rw [Ideal.under_def] at hpover ⊢
    rw [hpover, h𝔮, Ideal.comap_comap]
    congr 1
  exact hcov 𝔮 hlo𝔮 hqf𝔮 hfmem

/-- Existence of an isolating idempotent, assembled from the henselian section hypothesis `hsec`
and the finiteness `hfin` of the quasi-finite locus over `𝔪`: there is an idempotent `f ∈ S` whose
`f`-part `S ⧸ span{1-f}` is module-finite over `R` and whose complement `S ⧸ span{f}` has no
quasi-finite prime over `𝔪`.

The three ingredients are `isolating_idempotent_per_point`, `combine_isolating_idempotents` and
`complement_not_qf_of_mem`. -/
lemma exists_isolating_idempotent_nonempty_assembly
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (hsec : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
        (P : Ideal R') [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)],
        Function.Bijective
          ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R R')
              Ideal.LiesOver.over) →
        ∃ σ : R' →ₐ[R] R, ∀ r' : R', r' - algebraMap R R' (σ r') ∈ P)
    (hfin : {𝔮 : Ideal S | ∃ _ : 𝔮.IsPrime, 𝔮.LiesOver (IsLocalRing.maximalIdeal R) ∧
        Algebra.QuasiFiniteAt R 𝔮}.Finite) :
    ∃ f : S, IsIdempotentElem f ∧
      Module.Finite R (S ⧸ Ideal.span {1 - f}) ∧
      (∀ (𝔮 : Ideal (S ⧸ Ideal.span {f})) [𝔮.IsPrime],
        𝔮.LiesOver (IsLocalRing.maximalIdeal R) → ¬ Algebra.QuasiFiniteAt R 𝔮) := by
  -- Here span{1-f} is the finite part and span{f} the complement carrying no quasi-finite prime.
  --  * `isolating_idempotent_per_point` gives, for each quasi-finite prime 𝔮 over 𝔪, an
  --    idempotent g_𝔮 with S⧸span{1-g_𝔮} module-finite and g_𝔮 ∉ 𝔮.
  --  * `combine_isolating_idempotents` joins the finitely many g_𝔮 into one f with S⧸span{1-f}
  --    module-finite and f ∉ 𝔮 for every quasi-finite prime 𝔮 over 𝔪.
  --  * `complement_not_qf_of_mem` turns "f lies in no quasi-finite prime over 𝔪" into
  --    "S⧸span{f} has no quasi-finite prime over 𝔪".
  classical
  set Q := {𝔮 : Ideal S | ∃ _ : 𝔮.IsPrime, 𝔮.LiesOver (IsLocalRing.maximalIdeal R) ∧
      Algebra.QuasiFiniteAt R 𝔮} with hQ
  -- per-point: choose an isolating idempotent for each qf prime in Q
  have hper : ∀ 𝔮 ∈ Q, ∃ g : S, IsIdempotentElem g ∧
      Module.Finite R (S ⧸ Ideal.span {1 - g}) ∧ g ∉ 𝔮 := by
    intro 𝔮 h𝔮
    obtain ⟨hp, hlo, hqf⟩ := h𝔮
    exact isolating_idempotent_per_point R S hsec 𝔮
  -- pick the per-point idempotents via choice
  choose! g hgidem hgfin hgmem using hper
  -- combine over the finite locus Q
  obtain ⟨f, hfidem, hffin, hfmem⟩ :=
    combine_isolating_idempotents R S Q hfin g
      hgidem hgfin (fun 𝔮 h _ => hgmem 𝔮 h)
  exact ⟨f, hfidem, hffin,
    complement_not_qf_of_mem R S f hfidem fun 𝔮 hp hlo hqf => hfmem 𝔮 ⟨hp, hlo, hqf⟩ hp⟩

/-- Isolating idempotent for a nonempty quasi-finite locus, the analytic content of Stacks 04GG
part 11: when the quasi-finite locus over `𝔪` is finite, henselianness of `R` produces the
separating idempotent. The empty case is elementary, `f = 0` working there, and is handled in
`exists_isolating_idempotent` below.

The proof feeds `henselian_etale_residue_point_section` in as the `hsec` hypothesis of
`exists_isolating_idempotent_nonempty_assembly`. -/
@[sga "7 IX 2.2.3" "special case"]
lemma exists_isolating_idempotent_nonempty (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (hfin : {𝔮 : Ideal S | ∃ _ : 𝔮.IsPrime, 𝔮.LiesOver (IsLocalRing.maximalIdeal R) ∧
        Algebra.QuasiFiniteAt R 𝔮}.Finite) :
    ∃ f : S, IsIdempotentElem f ∧
      Module.Finite R (S ⧸ Ideal.span {1 - f}) ∧
      (∀ (𝔮 : Ideal (S ⧸ Ideal.span {f})) [𝔮.IsPrime],
        𝔮.LiesOver (IsLocalRing.maximalIdeal R) → ¬ Algebra.QuasiFiniteAt R 𝔮) := by
  -- Neither f = 0 (a nonempty locus means S itself has a quasi-finite prime over 𝔪) nor f = 1
  -- (S need not be module-finite) works in general: the idempotent requires henselian descent.
  exact exists_isolating_idempotent_nonempty_assembly R S
    (fun R' _ _ _ P _ _ hres => henselian_etale_residue_point_section R R' P hres) hfin

/-- Isolating idempotent (Stacks 04GG part 11). Given that the quasi-finite locus over `𝔪` is
finite, henselianness of `R` produces an idempotent `f ∈ S` whose `f`-part `S ⧸ span{1-f}` is
module-finite over `R` and whose complement `S ⧸ span{f}` retains no quasi-finite prime over `𝔪`.

Two cases on the finite quasi-finite locus over `𝔪`:
* an empty locus takes `f = 0`, since then `S ⧸ span{1} = 0` is module-finite and `S ⧸ span{0} ≅ S`
  has no quasi-finite prime over `𝔪`, transporting along `not_qf_over_maximal_of_algEquiv` and
  `AlgEquiv.quotientBot`;
* a nonempty locus is `exists_isolating_idempotent_nonempty`. -/
@[ega "II 6.2.6" "(f), special case",
  ega "IV 8.11.4" "special case",
  sga "3 X 4.3" "special case",
  sga "7 IX 2.2.3" "special case"]
alias exists_isolating_idempotent := exists_isolating_idempotent_nonempty

/-- The splitting idempotent for a finite type algebra over a henselian local ring: there is an
idempotent `f ∈ S` whose `f`-part `S ⧸ span{1-f}` is module-finite over `R` and whose complement
`S ⧸ span{f}` has no quasi-finite prime over `𝔪`.

The finitely many quasi-finite points over `𝔪` (`qf_primesOver_maximal_finite`) are isolated into
a single idempotent by henselian descent (`exists_isolating_idempotent`). -/
@[ega "IV 8.11.4" "special case", sga "3 X 4.3" "special case", sga "7 IX 2.2.3" "special case"]
lemma split_idem_exists (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ f : S, IsIdempotentElem f ∧
      Module.Finite R (S ⧸ Ideal.span {1 - f}) ∧
      (∀ (𝔮 : Ideal (S ⧸ Ideal.span {f})) [𝔮.IsPrime],
        𝔮.LiesOver (IsLocalRing.maximalIdeal R) → ¬ Algebra.QuasiFiniteAt R 𝔮) :=
  exists_isolating_idempotent R S (qf_primesOver_maximal_finite R S)

/-!
## Decomposition strategy (Stacks 04GJ = parts (10) + (11) of 04GG)

The proof factors into two independent structural results plus an assembly step.

* **Part (11) — the quasi-finite split (`exists_prod_finite_not_quasiFiniteAt`).**
  A finite type algebra `S` over the henselian local ring `R` splits, as an
  `R`-algebra, as `A × B` where `R → A` is *module-finite* and `R → B` is *not
  quasi-finite at any prime lying over `𝔪`*.

* **Part (10) — finite ⇒ product of locals (`exists_algEquiv_pi_isLocalRing`).**
  A *module-finite* algebra `A` over the henselian local ring `R` decomposes as a
  finite product `∏ i : Fin n, Aᵢ` of `R`-algebras, each *local* and *module-finite*
  over `R`.

* **Assembly (`exists_algEquiv_prod_of_henselianLocalRing`).**
  Compose `S ≃ₐ[R] A × B` with `(∏ Aᵢ) ≃ₐ[R] A` (whence `A × B ≃ₐ[R] (∏ Aᵢ) × B`),
  and transport the not-quasi-finite condition on `B` unchanged.
-/

/-- Part (11) of Stacks 04GG, the quasi-finite split. A finite type algebra `S` over a henselian
local ring `R` decomposes as an `R`-algebra product `A × B`, where `A` is module-finite over `R`
and `R → B` is not quasi-finite at any prime of `B` lying over the maximal ideal of `R`.

Informally: let `κ = R/𝔪` be the residue field and consider the closed fibre `S ⊗_R κ`, a finite
type `κ`-algebra, hence Noetherian of finite Krull dimension. The set of primes `𝔮` of
`S` lying over `𝔪` at which `R → S` is quasi-finite corresponds to the *isolated*
(dimension-zero, i.e. both open and closed) points of `Spec(S ⊗_R κ)`; there are only
finitely many of them, say `𝔮₁, …, 𝔮ₘ`. (Quasi-finiteness at `𝔮` over the closed point
is, by `Algebra.quasiFinite_iff` / tag 00PM, exactly the finiteness of the local fibre,
i.e. `𝔮` isolated in its fibre.)

For each such `𝔮ⱼ`, henselianness of `R` lets us *lift the separating idempotent*: by
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (tag 00UJ) there is an étale
neighbourhood and an idempotent `e` over the henselian base isolating `𝔮ⱼ` from all other
primes over `𝔪`; since `R` is henselian local, this étale-local idempotent descends to a
genuine idempotent of `S` (the étale extension splits off a finite piece). Combining the
idempotents for `𝔮₁, …, 𝔮ₘ` gives an idempotent `f ∈ S` cutting out exactly the union of
the quasi-finite points over `𝔪`. Set `A = S_f` (the `f`-part) and `B = S_{1-f}` (the
`(1-f)`-part), so `S ≃ₐ[R] A × B` via the central idempotent decomposition.

By construction every prime of `A` over `𝔪` is one of the isolated quasi-finite points,
and `A` is quasi-finite over `R` and *finite at the closed fibre*; by Zariski's Main
Theorem (`Algebra.zariskisMainProperty_iff_exists_saturation_eq_top`, tag 00Q9) a
quasi-finite algebra over a henselian local base whose closed fibre is finite is in fact
module-finite over `R`, giving `Module.Finite R A`. Dually, `B = S_{1-f}` retains none of
the quasi-finite points over `𝔪`: every prime `𝔮` of `B` lying over `𝔪` is non-isolated
in its fibre, so `R → B` is not quasi-finite at `𝔮` (`¬ Algebra.QuasiFiniteAt R 𝔮`). -/
@[sga "7 IX 2.2.3" "special case"]
theorem exists_prod_finite_not_quasiFiniteAt (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Module.Finite R A ∧
      (∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮.LiesOver (IsLocalRing.maximalIdeal R) →
        ¬ Algebra.QuasiFiniteAt R 𝔮) ∧
      Nonempty (S ≃ₐ[R] A × B) := by
  --  * `split_idem_exists` provides the splitting idempotent `f ∈ S` with `A := S⧸span{1-f}`
  --    module-finite and `B := S⧸span{f}` not quasi-finite over 𝔪.
  --  * `idem_algEquiv_prod` gives the central-idempotent algebra split `S ≃ₐ[R] A × B`.
  --  * The factors live in `Type v`; `ULift` them into `Type (max u v)` and transport the
  --    properties (`Module.Finite.equiv`, `not_qf_over_maximal_of_algEquiv`, `ULift.algEquiv`).
  obtain ⟨f, hf, hAfin, hBnqf⟩ := split_idem_exists R S
  obtain ⟨e⟩ := idem_algEquiv_prod R S f hf
  refine ⟨ULift.{u} (S ⧸ Ideal.span {1 - f}), inferInstance, inferInstance,
          ULift.{u} (S ⧸ Ideal.span {f}), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact Module.Finite.equiv (ULift.moduleEquiv (R := R)).symm
  · exact not_qf_over_maximal_of_algEquiv R ULift.algEquiv.symm hBnqf
  · exact ⟨e.trans (AlgEquiv.prodCongr ULift.algEquiv.symm ULift.algEquiv.symm)⟩

end
