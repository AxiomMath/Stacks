module

public import StacksFrontier.RingTheory.FinitePresentation.Relative
public import StacksFrontier.Algebra.Module.FinitePresentation.Transport

@[expose] public section

/-!
# Relatively finitely presented modules: independence of the presentation

Fix a commutative ring `R`, a commutative `R`-algebra `A` whose structure map `R → A` is of
finite type, and an `A`-module `M`.

A *presentation* of `A` over `R` is a pair `(n, α)` with `α : R[x_1, …, x_n] → A` a surjective
`R`-algebra homomorphism; presentations exist because `R → A` is of finite type. Given one, `M`
becomes an `R[x_1, …, x_n]`-module by restriction of scalars along `α`.

This file proves Stacks 05GY: the three conditions

1. `Module.FinitePresentationRel R A M` — `M` is finitely presented over `R[x_1, …, x_n]` for
   *some* presentation;
2. `Module.FinitePresentationRel.AllPresentations R A M` — the same for *every* presentation;
3. `Module.FinitePresentationRel.AllFPCovers R A M` — for every finitely presented `R`-algebra
   `A'` and every surjection `A' → A`, the module `M` is finitely presented over `A'`;

are equivalent, and that they imply that `M` is a finitely presented `A`-module. It also contains
the permanence properties that rest on this independence: Stacks 065C (composition of ring maps),
Stacks 0671 (two-out-of-three along a short exact sequence) and Stacks 0672 (direct summands).

The predicates themselves, together with the comparison engine for finite presentation along a
surjective ring map, live in `StacksFrontier.RingTheory.FinitePresentation.Relative`.
-/

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module A M]

namespace Module.FinitePresentationRel

/-- Stacks 05GY, `(3) → (2)`. A polynomial ring `R[x_1, …, x_n]` is itself a finitely presented
`R`-algebra, so every presentation of `A` is one of the finitely presented covers of condition
(3). -/
theorem allPresentations_of_allFPCovers (h3 : AllFPCovers.{u} R A M) :
    AllPresentations R A M := fun n α hα =>
  h3 (MvPolynomial (Fin n) R) (Algebra.FinitePresentation.mvPolynomial R R (Fin n)) α hα

/-- Stacks 05GY, `(2) → (1)`. Finite type of `R → A` produces at least one presentation, and
condition (2) applies to it. -/
theorem finitePresentationRel_of_allPresentations [Algebra.FiniteType R A]
    (h2 : AllPresentations R A M) : Module.FinitePresentationRel R A M := by
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact ⟨n, α, hα, h2 n α hα⟩

/-- Stacks 05GY, `(1) → (3)`: **independence of the presentation**, the substantive implication.

Let `α : R[x_1, …, x_n] → A` be a presentation for which `M` is finitely presented, and let
`π : A' → A` be a surjection from a finitely presented `R`-algebra. Choosing a presentation
`β : R[y_1, …, y_m] → A'` of `A'`, one builds two surjections out of the combined polynomial ring
`Q = R[x_1, …, x_n, y_1, …, y_m]`: a map `p : Q → R[x_1, …, x_n]` sending `y_j` to an
`α`-preimage of `π (β y_j)`, and a map `q : Q → A'` sending `x_i` to a `π`-preimage of `α x_i`.
These satisfy `α ∘ p = π ∘ q`, so ascending along `p` (surjective with finitely generated kernel,
being a surjection of finitely presented `R`-algebras) and then descending along `q` carries the
finite presentation of `M` from `R[x_1, …, x_n]` to `A'`. -/
theorem allFPCovers_of_finitePresentationRel (h1 : Module.FinitePresentationRel R A M) :
    AllFPCovers R A M := by
  classical
  obtain ⟨n, α, hαsurj, hfpα⟩ := h1
  intro A' _ _ hA'fp φ hφsurj
  obtain ⟨m, β, hβsurj, hβker⟩ := hA'fp.out
  -- Lifts of the `β`-variables to `R[x_1, …, x_n]` and of the `α`-variables to `A'`.
  set c : Fin m → MvPolynomial (Fin n) R :=
    fun j => Function.surjInv hαsurj (φ (β (MvPolynomial.X j)))
  set a' : Fin n → A' := fun i => Function.surjInv hφsurj (α (MvPolynomial.X i))
  have hcα : ∀ j, α (c j) = φ (β (MvPolynomial.X j)) := fun j => Function.surjInv_eq hαsurj _
  have ha'φ : ∀ i, φ (a' i) = α (MvPolynomial.X i) := fun i => Function.surjInv_eq hφsurj _
  -- The combined polynomial ring and the two maps out of it.
  set p : MvPolynomial (Fin n ⊕ Fin m) R →ₐ[R] MvPolynomial (Fin n) R :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X c) with hp
  set q : MvPolynomial (Fin n ⊕ Fin m) R →ₐ[R] A' :=
    MvPolynomial.aeval (Sum.elim a' (fun j => β (MvPolynomial.X j))) with hq
  have hpsurj : Function.Surjective p := by
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff,
      ← MvPolynomial.adjoin_range_X (σ := Fin n) (R := R), Algebra.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    exact ⟨MvPolynomial.X (Sum.inl i), by simp [hp]⟩
  have hqsurj : Function.Surjective q := by
    have hqβ : q.comp (MvPolynomial.rename Sum.inr) = β := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [hq]
    intro x
    obtain ⟨y, rfl⟩ := hβsurj x
    exact ⟨MvPolynomial.rename Sum.inr y, by rw [← AlgHom.comp_apply, hqβ]⟩
  have hcomp : α.comp p = φ.comp q := by
    apply MvPolynomial.algHom_ext
    rintro (i | j)
    · simp [hp, hq, ha'φ]
    · simp [hp, hq, hcα]
  have hcompRH : (α : MvPolynomial (Fin n) R →+* A).comp p.toRingHom
      = (φ : A' →+* A).comp q.toRingHom :=
    RingHom.ext fun x => DFunLike.congr_fun hcomp x
  have hQ : @Module.FinitePresentation (MvPolynomial (Fin n ⊕ Fin m) R) M _ _
      (Module.compHom M ((α : MvPolynomial (Fin n) R →+* A).comp p.toRingHom)) :=
    Module.finitePresentation_compHom_comp (α : MvPolynomial (Fin n) R →+* A) p.toRingHom
      hpsurj (Algebra.FinitePresentation.ker_fG_of_surjective p hpsurj) hfpα
  rw [hcompRH] at hQ
  exact Module.finitePresentation_of_compHom_comp (φ : A' →+* A) q.toRingHom hqsurj hQ

end Module.FinitePresentationRel

/-- Stacks 05GY: for an `A`-module `M` over a finite type ring map `R → A`, the three
conditions "some presentation", "all presentations" and "all finitely presented covers" are
equivalent. -/
@[stacks 05GY]
theorem Module.finitePresentationRel_tfae [Algebra.FiniteType R A] :
    [Module.FinitePresentationRel R A M,
     Module.FinitePresentationRel.AllPresentations R A M,
     Module.FinitePresentationRel.AllFPCovers.{u} R A M].TFAE := by
  tfae_have 2 → 1 := Module.FinitePresentationRel.finitePresentationRel_of_allPresentations
  tfae_have 1 → 3 := Module.FinitePresentationRel.allFPCovers_of_finitePresentationRel
  tfae_have 3 → 2 := Module.FinitePresentationRel.allPresentations_of_allFPCovers
  tfae_finish

/-- Stacks 05GY, `(1) ↔ (3)`: being finitely presented relative to `R` is the same as being
finitely presented over every finitely presented `R`-algebra surjecting onto `A`. -/
theorem Module.finitePresentationRel_iff_allFPCovers [Algebra.FiniteType R A] :
    Module.FinitePresentationRel R A M ↔
      Module.FinitePresentationRel.AllFPCovers.{u} R A M :=
  Module.finitePresentationRel_tfae.out 1 3

-- ===== merged from StacksDraft.Sec81.Tag065C =====


/-!
## Relative finite presentation and composition of ring maps

Let `R → A` and `A → B` be ring maps of finite type and let `M` be a `B`-module. This section
proves Stacks 065C (Lemma 15.82.7): if `M` is finitely presented relative to `A` and `A` is of
finite presentation over `R`, then `M` is finitely presented relative to `R`.

The proof combines a presentation `β : A[y_1, …, y_m] ↠ B` witnessing relative finite
presentation over `A` with a presentation `g : R[x_1, …, x_n] ↠ A` of finite presentation type:
applying `g` coefficientwise gives a surjection `R[y][x] ↠ A[y]` with finitely generated kernel,
which after reindexing `R[x_1, …, x_{m+n}] ≅ R[y][x]` transfers the finite presentation of `M`
from `A[y_1, …, y_m]` down to `R[x_1, …, x_{m+n}]`.
-/

open MvPolynomial

/-- Stacks 065C, Lemma 15.82.7. Given finite type ring maps `R → A` and `A → B` and a
`B`-module `M`, if `M` is finitely presented relative to `A` and `A` is of finite presentation
over `R`, then `M` is finitely presented relative to `R`. -/
@[stacks 065C]
theorem Module.finitePresentationRel_comp {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FinitePresentation R A] {M : Type*} [AddCommGroup M] [Module B M]
    (hM : Module.FinitePresentationRel A B M) : Module.FinitePresentationRel R B M := by
  classical
  obtain ⟨m, β, hβsurj, hβfp⟩ := hM
  obtain ⟨n, g, hgsurj, hgker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  let iso : MvPolynomial (Fin (m + n)) R ≃ₐ[R]
      MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    (MvPolynomial.renameEquiv R finSumFinEquiv).symm.trans
      (MvPolynomial.sumAlgEquiv R (Fin m) (Fin n))
  let α0 : MvPolynomial (Fin (m + n)) R →+* MvPolynomial (Fin m) A :=
    (MvPolynomial.map g.toRingHom).comp iso.toRingEquiv.toRingHom
  have hα0_surj : Function.Surjective α0 :=
    (MvPolynomial.map_surjective g.toRingHom hgsurj).comp iso.surjective
  have hαr_comm : ∀ r : R, β.toRingHom.comp α0 (algebraMap R _ r) = algebraMap R B r := by
    intro r
    change β (MvPolynomial.map g.toRingHom (iso (algebraMap R _ r))) = _
    rw [iso.commutes]
    simp [MvPolynomial.algebraMap_apply, IsScalarTower.algebraMap_apply R A B]
  refine ⟨m + n, { β.toRingHom.comp α0 with commutes' := hαr_comm }, hβsurj.comp hα0_surj, ?_⟩
  have hα0_ker : (RingHom.ker α0).FG := by
    have hmap : (RingHom.ker (MvPolynomial.map (σ := Fin m) g.toRingHom)).FG := by
      rw [MvPolynomial.ker_map]
      exact hgker.map _
    rw [← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, Ideal.comap_coe, ← Ideal.map_symm,
      ← Ideal.map_coe]
    exact hmap.map _
  exact @Module.finitePresentation_compHom _ _ M _ _ _ (Module.compHom M β.toRingHom) α0
    hα0_surj hα0_ker hβfp

-- ===== merged from StacksDraft.Sec81.Tag0671 =====


/-!
## Two-out-of-three for relatively finitely presented modules

Let `R → A` be a finite type ring map and let `0 → M' → M → M'' → 0` be a short exact sequence
of `A`-modules. This section proves Stacks 0671 (Lemma 15.82.9):

* if `M'` and `M''` are finitely presented relative to `R`, then so is `M`;
* if `M'` is a finite type `A`-module and `M` is finitely presented relative to `R`, then `M''`
  is finitely presented relative to `R`.

Part (1) uses the independence of the chosen presentation (Stacks 05GY) to put both `M'` and
`M''` over a single polynomial ring.
-/

/-- Restriction of scalars of an `A`-linear map along `α : S →+* A`, where both modules carry the
`S`-module structure `Module.compHom` induced by `α`. -/
private def restrictScalarsAlong {S : Type*} [CommRing S] {A : Type*} [CommRing A]
    (α : S →+* A) {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) :
    @LinearMap S S _ _ (RingHom.id S) M N _ _ (Module.compHom M α) (Module.compHom N α) :=
  letI := Module.compHom M α
  letI := Module.compHom N α
  { toFun := f, map_add' := f.map_add, map_smul' := fun s m => f.map_smul (α s) m }

section ShortExact

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable {M' M M'' : Type u}
variable [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
variable [AddCommGroup M''] [Module A M'']

/-- Stacks 0671, part (1). Given a short exact sequence of `A`-modules
`0 → M' →[i] M →[p] M'' → 0` (so `i` is injective, `p` is surjective and
`range i = ker p`), if `M'` and `M''` are finitely presented relative to `R`, then `M` is
finitely presented relative to `R`.

By Stacks 05GY, `M'` and `M''` are finitely presented over `R[x_1, …, x_n]` for *every*
presentation `α`, so one may pick a single presentation and apply two-out-of-three over the
polynomial ring `R[x_1, …, x_n]`. -/
@[stacks 0671 "(1)"]
theorem Module.finitePresentationRel_two_of_three (i : M' →ₗ[A] M) (p : M →ₗ[A] M'')
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p)
    (hM' : Module.FinitePresentationRel R A M')
    (hM'' : Module.FinitePresentationRel R A M'') :
    Module.FinitePresentationRel R A M := by
  -- Independence of the presentation (Stacks 05GY) for the two outer terms.
  have h2' : Module.FinitePresentationRel.AllPresentations R A M' :=
    (Module.finitePresentationRel_tfae.out 1 2).mp hM'
  have h2'' : Module.FinitePresentationRel.AllPresentations R A M'' :=
    (Module.finitePresentationRel_tfae.out 1 2).mp hM''
  -- Any single presentation of `A` now works for all three modules.
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  refine ⟨n, α, hα, ?_⟩
  -- Endow all three modules with the `R[x_1, …, x_n]`-structure via `α`.
  let mM'S : Module (MvPolynomial (Fin n) R) M' := Module.compHom M' α.toRingHom
  let mMS : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
  let mM''S : Module (MvPolynomial (Fin n) R) M'' := Module.compHom M'' α.toRingHom
  have hM'S : Module.FinitePresentation (MvPolynomial (Fin n) R) M' := h2' n α hα
  have hM''S : Module.FinitePresentation (MvPolynomial (Fin n) R) M'' := h2'' n α hα
  -- `i` and `p` are `R[x_1, …, x_n]`-linear, scalars acting through `α`.
  exact fp_two_of_three (restrictScalarsAlong α.toRingHom i) (restrictScalarsAlong α.toRingHom p)
    hi hp (SetLike.coe_injective (congrArg (SetLike.coe : Submodule A M → Set M) hex))

end ShortExact

/-- Stacks 0671, part (2). Given a short exact sequence of `A`-modules
`0 → M' →[i] M →[p] M'' → 0`, if `M'` is a finite type (finitely generated) `A`-module and `M`
is finitely presented relative to `R`, then `M''` is finitely presented relative to `R`. -/
@[stacks 0671 "(2)"]
theorem Module.finitePresentationRel_of_surjective_of_finite {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M'']
    (i : M' →ₗ[A] M) (p : M →ₗ[A] M'')
    (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p)
    (hM' : Module.Finite A M') (hM : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R A M'' := by
  obtain ⟨n, α, hαsurj, hfpM⟩ := hM
  refine ⟨n, α, hαsurj, ?_⟩
  set S := MvPolynomial (Fin n) R
  -- Module structures via restriction of scalars along `α`.
  let mM' : Module S M' := Module.compHom M' α.toRingHom
  let mM : Module S M := Module.compHom M α.toRingHom
  let mM'' : Module S M'' := Module.compHom M'' α.toRingHom
  have : Module.FinitePresentation S M := hfpM
  have : Module.Finite S M' := finite_restrict α.toRingHom hαsurj
  let iS := restrictScalarsAlong α.toRingHom i
  let pS := restrictScalarsAlong α.toRingHom p
  have hexS : LinearMap.range iS = LinearMap.ker pS :=
    SetLike.coe_injective (congrArg (SetLike.coe : Submodule A M → Set M) hex)
  -- `M'' = M / ker pS` and `ker pS = range iS` is finitely generated.
  exact Module.finitePresentation_of_surjective pS hp
    (hexS ▸ Module.Finite.iff_fg.mp (Module.Finite.range iS))

-- ===== merged from StacksDraft.Sec81.Tag0672 =====


/-!
## A direct summand of a relatively finitely presented module

This section proves Stacks 0672 (Lemma 15.82.10): if `R → A` is a finite type ring map and the
`A`-module `M ⊕ M'` is finitely presented relative to `R`, then so are `M` and `M'`.

The direct sum `M ⊕ M'` is the external direct sum `M × M'` with its componentwise `A`-module
structure.
-/

/-- Stacks 0672 (Lemma 15.82.10).

Let `R → A` be a ring map (in Stacks, of finite type — the hypothesis is not needed here) and
let `M`, `M'` be `A`-modules. If the direct sum `M × M'` is finitely presented relative to `R`,
then both `M` and `M'` are finitely presented relative to `R`. -/
@[stacks 0672]
theorem Module.finitePresentationRel_of_prod {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (h : Module.FinitePresentationRel R A (M × M')) :
    Module.FinitePresentationRel R A M ∧ Module.FinitePresentationRel R A M' := by
  obtain ⟨n, α, hα, hfp⟩ := h
  -- `M` and `M'` carry the `R[x_1, …, x_n]`-module structures obtained by restricting scalars
  -- along `α`; the one on `M × M'` used in `hfp` is their product.
  let iM : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
  let iM' : Module (MvPolynomial (Fin n) R) M' := Module.compHom M' α.toRingHom
  have : Module.FinitePresentation (MvPolynomial (Fin n) R) (M × M') := hfp
  exact ⟨⟨n, α, hα, Module.FinitePresentation.fst (M := M) (M' := M')⟩,
    ⟨n, α, hα, Module.FinitePresentation.snd (M := M) (M' := M')⟩⟩
