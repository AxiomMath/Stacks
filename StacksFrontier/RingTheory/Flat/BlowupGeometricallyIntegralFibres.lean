module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.ContentIdeal
public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapAtGenericFibre
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Flat.Blowup
public import StacksFrontier.RingTheory.Flat.MittagLeffler
public import StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut
public import StacksFrontier.RingTheory.Ideal.SymbolicPower

/-!
# Flattening a finite module on an affine blowup, over an algebra with integral fibres

Let `R → S` be flat and of finite presentation with geometrically integral fibres, let `f ∈ R`,
and let `M` be a finite `S`-module which is finitely presented after inverting `f` and free of
rank `r` at every extended prime `pS` with `f ∉ p`.  Stacks Tag 0810 produces a finitely generated
ideal `I ⊆ R` with `V(I) = V(f)` such that on *every* affine blowup chart `R' = R[I/a]`, `a ∈ I`,
the strict transform `M' = (M ⊗[R] R')/a`-power torsion is free of rank `r` on a principal
neighbourhood of each extended prime `p'S'` of `S' = S ⊗[R] R'`.

This generalizes `exists_fg_ideal_strictTransform_isFiniteLocallyFreeOfRank` (Stacks Tag 0BBJ),
which is the case `S = R`, and the proof below follows it closely.  The new ingredient is the
*ideal of coefficients*: geometric integrality of the fibres makes `S` a projective `R`-module
(Stacks Tag 05FT), so an element of `S` has a content ideal in `R`
(`exists_isContentIdeal_of_projective`), and the ideal of coefficients of the `r`th Fitting ideal
`J = Fit_r(M)` is a finitely generated ideal `I' ⊆ R` detecting, prime by prime, when `J` is
swallowed by an extended ideal.  The ideal `I = fI'` is the one the source produces.

## Main results

* `Module.Projective.injective_lsmul_localizedModule`: an element of `S` outside the extended
  prime `pS` acts injectively on the localization of `S` at `p`.  This is the one consequence of
  Stacks Tags 05FR/05I3 that the main theorem needs, and it is proved here directly from Stacks
  Tag 05FQ.
* `Algebra.ker_includeRight_fiber`: the kernel of `S → κ(p) ⊗[R] S` is the extension `pS`.
* `exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_projective`: the conclusion of Stacks
  Tag 0810, with projectivity of `S` over `R` assumed rather than deduced.
* `exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_good_halves`: the same conclusion from
  the fibre hypotheses of the source alone, granted the two statements about a single generic
  fibre that are all that is missing from Stacks Tag 05FT in this library.

## Implementation notes

**Stacks Tag 0810 is not tagged here.**  Its proof uses Stacks Tag 05FT — a flat algebra of finite
presentation with geometrically integral fibres is projective over its base — and that tag is not
available in this library: the strongest form proved is
`Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves`, which still assumes the
affine cases of Stacks Tags 0578 and 055A at the generic point (equivalently, by
`StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced` and
`StacksFrontier.RingTheory.GeometricallyIntegral.GoodIrreducible`, the affine cases of Stacks Tags
0579 and 055B).  Accordingly the content of Tag 0810 is proved twice: once with
`[Module.Projective R S]` as a hypothesis, which is unconditional, and once with those two
statements as hypotheses, which is Tag 0810 verbatim apart from them.  The moment Stacks Tag 05FT
lands, `@[stacks 0810]` belongs on a corollary of the first obtained by supplying the instance.

The source's `α : S^{⊕r} → N` and the equivalence of six conditions of Stacks Tag 05IA do not
appear.  The only consequence of that equivalence used in the source's argument is that elements
of `S ∖ pS` are nonzerodivisors on `S` localized at `p`, which
`Module.Projective.injective_lsmul_localizedModule` obtains from Stacks Tag 05FQ applied to the
projective module `S_p` over the local ring `R_p`, whose closed fibre `κ(p) ⊗[R] S` is a domain.

The affine blowup chart `R[I/a]` is `Blowup I a`; the base change of `M` is written as
`(S ⊗[R] R') ⊗[S] M`; the strict transform is the quotient by the submodule killed by a power of
the image of `a`.  The equality `V(f) = V(I)` is expressed pointwise on prime ideals, and freeness
of rank `r` by a linear equivalence with the free module on `Fin r`.

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 0BBJ](https://stacks.math.columbia.edu/tag/0BBJ)
* [Stacks Project, Tag 05FQ](https://stacks.math.columbia.edu/tag/05FQ)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-! ### The generic point of a fibre -/

/-- **The kernel of the map to the fibre.** For a flat `R`-algebra `S` and a prime `p ⊆ R`, the
kernel of `S → κ(p) ⊗[R] S` is the extension `pS`. -/
theorem Algebra.ker_includeRight_fiber {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    RingHom.ker (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom =
      Ideal.map (algebraMap R S) p := by
  let e := Algebra.TensorProduct.comm R p.ResidueField S
  have hk : RingHom.ker (algebraMap S (S ⊗[R] p.ResidueField)) =
      Ideal.map (algebraMap R S) p := by
    rw [Algebra.ker_algebraMap_tensorProduct_left, Ideal.ker_algebraMap_residueField]
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [RingHom.mem_ker] at hx
    rw [← hk, RingHom.mem_ker]
    simpa [e] using congrArg e hx
  · rw [← hk, RingHom.mem_ker] at hx
    rw [RingHom.mem_ker]
    refine e.injective ?_
    simpa [e] using hx

/-- **The generic point of an integral fibre.** If `R → S` is flat and the fibre of `S` over a
prime `p` of `R` is a domain, the extension `pS` is a prime ideal of `S`.

This is `Ideal.isPrime_map_of_flat_of_isGeometricallyIntegral` with geometric integrality of the
fibre weakened to integrality, which is all that the extension being prime needs.

`Ideal.isPrime_map_of_flat_of_isDomain_fiber` is the same conclusion under the additional
hypotheses that `R` is a domain and that `R` and `S` lie in the same universe; this statement
asks neither, so it carries the primed name. -/
theorem Ideal.isPrime_map_of_flat_of_isDomain_fiber' {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] (hdom : IsDomain (p.Fiber S)) :
    (Ideal.map (algebraMap R S) p).IsPrime := by
  have _ : IsDomain (p.Fiber S) := hdom
  exact Algebra.ker_includeRight_fiber (S := S) p ▸ RingHom.ker_isPrime _

/-! ### Elements outside the generic point of the fibre are nonzerodivisors

Stacks Tag 05I3 derives, from Stacks Tags 05FR and 05FT, that the elements of `S ∖ pS` are
nonzerodivisors on `S`.  For the localization at `p` this is a direct application of Stacks
Tag 05FQ: over the local ring `R_p` the module `S_p` is projective, its closed fibre is the domain
`κ(p) ⊗[R] S`, and multiplication by an element outside `pS` is injective there. -/

/-- **Elements outside the generic point of the fibre act injectively after localizing at the
base prime.**  Let `S` be a flat, projective `R`-algebra, let `p ⊆ R` be a prime with integral
fibre `κ(p) ⊗[R] S`, and let `s ∈ S ∖ pS`.  Then multiplication by `s` is injective on the
localization of `S` at `p`.

Over the local ring `R_p` the module `S_p` is projective, hence flat, and the quotient of `S_p`
by the extended maximal ideal is `κ(p) ⊗[R] S`, a domain in which the image of `s` is nonzero.
So Stacks Tag 05FQ makes multiplication by `s` universally injective, in particular injective. -/
theorem Module.Projective.injective_lsmul_localizedModule {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Projective R S] (p : Ideal R)
    [p.IsPrime] (hdom : IsDomain (p.Fiber S)) {s : S}
    (hs : s ∉ Ideal.map (algebraMap R S) p) :
    Function.Injective
      (LocalizedModule.map p.primeCompl ((LinearMap.lsmul S S s).restrictScalars R)) := by
  set A := Localization.AtPrime p with hA
  set B := A ⊗[R] S with hB
  set 𝔪 := IsLocalRing.maximalIdeal A with h𝔪
  set 𝔫 : Ideal B := Ideal.map (algebraMap A B) 𝔪 with h𝔫
  have _ : IsDomain ((A ⧸ 𝔪) ⊗[R] S) := hdom
  have hprime : 𝔫.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp
      ((Algebra.TensorProduct.quotientTensorEquiv (R := R) A S A
        𝔪).toRingEquiv.symm.injective.isDomain _)
  have hsn : (1 : A) ⊗ₜ[R] s ∉ 𝔫 := by
    intro hmem
    apply hs
    rw [← Algebra.ker_includeRight_fiber (S := S) p, RingHom.mem_ker]
    have h1 : Ideal.Quotient.mk 𝔫 ((1 : A) ⊗ₜ[R] s) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have h2 : (Algebra.TensorProduct.quotientTensorEquiv (R := R) A S A 𝔪)
        ((Ideal.Quotient.mk 𝔪 (1 : A)) ⊗ₜ[R] s) = 0 :=
      (Algebra.TensorProduct.quotientTensorEquiv_apply_tmul (R := R) (S := A)
        (T := S) (A := A) 𝔪 (1 : A) s).trans h1
    have h3 : (Ideal.Quotient.mk 𝔪 (1 : A)) ⊗ₜ[R] s = 0 :=
      (map_eq_zero_iff _ (AlgEquiv.injective _)).mp h2
    rw [map_one] at h3
    exact h3
  set e := LocalizedModule.equivTensorProduct p.primeCompl S with he
  have hmem : ∀ x : LocalizedModule p.primeCompl S,
      x ∈ 𝔪 • (⊤ : Submodule A (LocalizedModule p.primeCompl S)) ↔ e x ∈ 𝔫 := by
    intro x
    have hmap : Submodule.map (e : LocalizedModule p.primeCompl S →ₗ[A] B)
        (𝔪 • (⊤ : Submodule A (LocalizedModule p.primeCompl S))) =
          (𝔫).restrictScalars A := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective,
        ← Ideal.smul_top_eq_map]
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · have hx' : e x ∈ Submodule.map (e : LocalizedModule p.primeCompl S →ₗ[A] B) _ :=
        Submodule.mem_map_of_mem hx
      rwa [hmap] at hx'
    · have hx' : e x ∈ Submodule.map (e : LocalizedModule p.primeCompl S →ₗ[A] B)
          (𝔪 • (⊤ : Submodule A (LocalizedModule p.primeCompl S))) := by
        rw [hmap]; exact hx
      obtain ⟨y, hy, hxy⟩ := hx'
      rwa [e.injective hxy] at hy
  have hcomm : ∀ x : LocalizedModule p.primeCompl S,
      e (LocalizedModule.map p.primeCompl ((LinearMap.lsmul S S s).restrictScalars R) x) =
        ((1 : A) ⊗ₜ[R] s) * e x := by
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      rw [he]
      rw [show (LocalizedModule.map p.primeCompl ((LinearMap.lsmul S S s).restrictScalars R))
          (LocalizedModule.mk m t) = LocalizedModule.mk (s * m) t from ?_]
      · rw [LocalizedModule.equivTensorProduct_apply_mk,
          LocalizedModule.equivTensorProduct_apply_mk, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul]
      · rw [LocalizedModule.map_mk]
        rfl
  have hu : ∀ x : LocalizedModule p.primeCompl S,
      (LocalizedModule.map p.primeCompl ((LinearMap.lsmul S S s).restrictScalars R)) x ∈
        𝔪 • (⊤ : Submodule A (LocalizedModule p.primeCompl S)) →
      x ∈ 𝔪 • (⊤ : Submodule A (LocalizedModule p.primeCompl S)) := by
    intro x hx
    rw [hmem] at hx ⊢
    rw [hcomm] at hx
    exact (hprime.mem_or_mem hx).resolve_left hsn
  have hinj := Module.Flat.rTensor_injective_of_projective_of_mem_maximalIdeal_smul_top
    (R := A) (M := LocalizedModule p.primeCompl S) (N := LocalizedModule p.primeCompl S)
    (LocalizedModule.map p.primeCompl ((LinearMap.lsmul S S s).restrictScalars R)) hu A
  intro x y hxy
  have h1 : (LinearMap.rTensor A
        (LocalizedModule.map p.primeCompl ((LinearMap.lsmul S S s).restrictScalars R)))
        (x ⊗ₜ[A] (1 : A)) =
      (LinearMap.rTensor A
        (LocalizedModule.map p.primeCompl ((LinearMap.lsmul S S s).restrictScalars R)))
        (y ⊗ₜ[A] (1 : A)) :=
    congrArg (fun z : LocalizedModule p.primeCompl S ↦ z ⊗ₜ[A] (1 : A)) hxy
  simpa using congrArg (TensorProduct.rid A (LocalizedModule p.primeCompl S)) (hinj h1)

/-! ### The ideal of coefficients

For `S` projective over `R` the content ideal of an element of `S` is the ideal generated by its
coefficients in a decomposition `⨁ R = S ⊕ C`.  The ideal of coefficients of a finitely generated
ideal `J ⊆ S` is the supremum of the content ideals of a finite generating set; it is finitely
generated, and it detects prime by prime when `J` is swallowed by an extended ideal. -/

/-- **The ideal of coefficients of a finitely generated ideal.**  If `S` is a projective
`R`-module and `J ⊆ S` is a finitely generated ideal, there is a finitely generated ideal
`I ⊆ R` such that for every ideal `K ⊆ R` one has `J ⊆ KS` if and only if `I ⊆ K`.

`I` is the supremum of the content ideals of a finite generating set of `J`, which is finitely
generated by `exists_isContentIdeal_of_projective`. -/
private theorem exists_fg_coefficientIdeal_of_projective {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Projective R S] (J : Ideal S) (hJ : J.FG) :
    ∃ I : Ideal R, I.FG ∧ ∀ K : Ideal R, J ≤ Ideal.map (algebraMap R S) K ↔ I ≤ K := by
  classical
  obtain ⟨T, hT, hg⟩ := Submodule.fg_def.mp hJ
  have _ : Finite T := hT.to_subtype
  have hcontents (i : T) : ∃ I : Ideal R, I.FG ∧ IsContentIdeal (i : S) I := by
    obtain ⟨I, hfg, hI⟩ := exists_isContentIdeal_of_projective (A := R) (M := S) (i : S)
    exact ⟨I, hfg, hI⟩
  choose C hC_fg hC using hcontents
  refine ⟨⨆ i, C i, Submodule.fg_iSup C hC_fg, fun K ↦ ⟨fun hJK ↦ ?_, fun hIK ↦ ?_⟩⟩
  · refine iSup_le fun i ↦ (hC i).le_of_mem_smul_top ?_
    have hgi : (i : S) ∈ Ideal.map (algebraMap R S) K := hJK (by
      rw [← hg]
      exact Submodule.subset_span i.property)
    simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hgi
  · rw [← hg]
    refine Ideal.span_le.mpr fun x hx ↦ ?_
    have hgi : ((⟨x, hx⟩ : T) : S) ∈ Ideal.map (algebraMap R S) (C ⟨x, hx⟩) := by
      simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using
        (hC ⟨x, hx⟩).mem_smul_top
    exact Ideal.map_mono ((le_iSup C ⟨x, hx⟩).trans hIK) hgi

/-- **The ideal of coefficients after base change.**  Let `I ⊆ R` be the ideal of coefficients of
`J ⊆ S` as in `exists_fg_coefficientIdeal_of_projective`, let `A` be any `R`-algebra and let
`K ⊆ A` be an ideal.  If the extension of `J` to `S ⊗[R] A` is contained in the extension of `K`,
then the extension of `I` to `A` is contained in `K`.

The coefficient functionals of the decomposition of `S` are `R`-linear, so they base change to
`A`-linear functionals on `S ⊗[R] A` carrying the extension of `K` into `K`; applied to a
generator of `J` they exhibit each of its coefficients in the contraction of `K` to `R`. -/
private theorem coefficientIdeal_baseChange_le {R S A : Type u} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] [Module.Projective R S] (J : Ideal S) (I : Ideal R)
    (hcontent : ∀ K : Ideal R, J ≤ Ideal.map (algebraMap R S) K ↔ I ≤ K) (K : Ideal A)
    (hJ : Ideal.map (algebraMap S (S ⊗[R] A)) J ≤
      Ideal.map Algebra.TensorProduct.includeRight K) :
    Ideal.map (algebraMap R A) I ≤ K := by
  classical
  let B := S ⊗[R] A
  let _ : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let eAB : (A ⊗[R] S) ≃ₐ[A] B :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R A S).toRingEquiv) (by
        intro x
        rfl)
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := S)
  let K₀ : Ideal R := Ideal.comap (algebraMap R A) K
  refine Ideal.map_le_iff_le_comap.mpr ((hcontent K₀).1 fun j hj ↦ ?_)
  have hcoeff (i) : (s j) i ∈ K₀ := by
    let φ : S →ₗ[R] R := (Finsupp.lapply i).comp s
    let Φ : B →ₗ[A] A :=
      (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap.comp
        ((φ.baseChange A).comp eAB.symm.toLinearMap)
    have hΦK (y : B) (hy : y ∈ Ideal.map (algebraMap A B) K) : Φ y ∈ K := by
      have hy' : y ∈ K • (⊤ : Submodule A B) := by
        simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hy
      refine Submodule.smul_induction_on hy' ?_ ?_
      · intro a ha y _
        simpa only [map_smul, smul_eq_mul] using K.mul_mem_right (Φ y) ha
      · intro y z hy hz
        simpa only [map_add] using K.add_mem hy hz
    have hjB : algebraMap S B j ∈ Ideal.map (algebraMap A B) K :=
      hJ (Ideal.mem_map_of_mem (algebraMap S B) hj)
    have hΦj : Φ (algebraMap S B j) = algebraMap R A ((s j) i) := by
      have he : eAB.symm (algebraMap S B j) = (1 : A) ⊗ₜ[R] j := rfl
      change (TensorProduct.AlgebraTensorModule.rid R A A)
        ((φ.baseChange A) (eAB.symm (algebraMap S B j))) = _
      rw [he, LinearMap.baseChange_tmul]
      simp [φ, Finsupp.lapply_apply, Algebra.smul_def]
    change algebraMap R A ((s j) i) ∈ K
    rw [← hΦj]
    exact hΦK _ hjB
  have hjK : j ∈ K₀ • (⊤ : Submodule R S) := by
    have hx := (Submodule.mem_ideal_smul_span_iff_exists_sum K₀ (id : S → S) j).2
      ⟨s j, hcoeff, hs j⟩
    simpa only [Set.range_id, Submodule.span_univ] using hx
  simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hjK

/-! ### Approximating a module that is finitely presented after inverting `f`

A finite module `M` whose localization away from `f` is finitely presented is the target of a
surjection from a finitely presented module which becomes an isomorphism after inverting `f`:
take any finite free presentation of `M` and keep only finitely many of its relations, enough to
generate the kernel after inverting `f`. -/

/-- A module whose localization at `T` is finite over `Localization T` has a finitely generated
submodule whose localization is everything. -/
private theorem exists_fg_localized_eq_top {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] (T : Submonoid R) [Module.Finite (Localization T) (LocalizedModule T M)] :
    ∃ K : Submodule R M, K.FG ∧ K.localized T = ⊤ := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin
    (R := Localization T) (M := LocalizedModule T M)
  have hsurj (i : Fin n) :
      ∃ w : M × T, IsLocalizedModule.mk' (LocalizedModule.mkLinearMap T M) w.1 w.2 = g i :=
    IsLocalizedModule.mk'_surjective T (LocalizedModule.mkLinearMap T M) (g i)
  choose w hw using hsurj
  refine ⟨Submodule.span R (Set.range fun i : Fin n ↦ (w i).1),
    Submodule.fg_span (Set.finite_range _), top_unique ?_⟩
  rw [← hg]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, rfl⟩
  change g i ∈ (Submodule.span R (Set.range fun i : Fin n ↦ (w i).1)).localized' (Localization T)
    T (LocalizedModule.mkLinearMap T M)
  rw [Submodule.mem_localized']
  exact ⟨(w i).1, Submodule.subset_span ⟨i, rfl⟩, (w i).2, hw i⟩

/-- If the localization of `M` at `T` is finitely presented and `F` is finite over `R`, the
localization of the kernel of a surjection `F → M` is finite. -/
private theorem finite_localizedModule_ker {A F : Type u} {M : Type v} [CommRing A]
    [AddCommGroup F] [Module A F] [Module.Finite A F] [AddCommGroup M] [Module A M]
    (T : Submonoid A) [Module.FinitePresentation (Localization T) (LocalizedModule T M)]
    (q : F →ₗ[A] M) (hq : Function.Surjective q) :
    Module.Finite (Localization T) (LocalizedModule T q.ker) := by
  have hqL : Function.Surjective (LocalizedModule.map T q) :=
    IsLocalizedModule.map_surjective T (LocalizedModule.mkLinearMap T F)
      (LocalizedModule.mkLinearMap T M) q hq
  have hfinKer : Module.Finite (Localization T) (LocalizedModule.map T q).ker :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker (LocalizedModule.map T q) hqL)
  have hker : q.ker.localized T = (LocalizedModule.map T q).ker :=
    LinearMap.localized'_ker_eq_ker_localizedMap (Localization T) T
      (LocalizedModule.mkLinearMap T F) (LocalizedModule.mkLinearMap T M) q
  have hfinLocal : Module.Finite (Localization T) (q.ker.localized T) := by
    rw [hker]
    exact hfinKer
  exact Module.Finite.equiv (Submodule.localizedEquiv T q.ker)

/-- Pushing a submodule of a submodule `N` forward along the inclusion does not change its
localization when it already localizes to all of `N`. -/
private theorem localized_map_subtype_eq {A F : Type u} [CommRing A] [AddCommGroup F]
    [Module A F] (T : Submonoid A) (N : Submodule A F) (K₀ : Submodule A N)
    (hK₀ : K₀.localized T = ⊤) :
    (K₀.map N.subtype).localized T = N.localized T := by
  refine le_antisymm ?_ ?_
  · change (K₀.map N.subtype).localized' (Localization T) T
      (LocalizedModule.mkLinearMap T F) ≤
      N.localized' (Localization T) T (LocalizedModule.mkLinearMap T F)
    rw [Submodule.localized'_eq_span, Submodule.localized'_eq_span]
    exact Submodule.span_mono (Set.image_mono (Submodule.map_subtype_le N K₀))
  · change N.localized' (Localization T) T (LocalizedModule.mkLinearMap T F) ≤
      (K₀.map N.subtype).localized' (Localization T) T (LocalizedModule.mkLinearMap T F)
    rw [Submodule.localized'_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨z, hz, rfl⟩
    have hzloc : (LocalizedModule.mkLinearMap T N) ⟨z, hz⟩ ∈ K₀.localized T := by
      rw [hK₀]; trivial
    change (LocalizedModule.mkLinearMap T N) ⟨z, hz⟩ ∈
      K₀.localized' (Localization T) T (LocalizedModule.mkLinearMap T N) at hzloc
    rw [Submodule.mem_localized'] at hzloc
    obtain ⟨k, hk, t, hkt⟩ := hzloc
    change (LocalizedModule.mkLinearMap T F) z ∈
      (K₀.map N.subtype).localized' (Localization T) T (LocalizedModule.mkLinearMap T F)
    rw [Submodule.mem_localized']
    refine ⟨(k : F), ⟨k, hk, rfl⟩, t, ?_⟩
    calc
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap T F) (k : F) t =
          (LocalizedModule.map T N.subtype)
            (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap T N) k t) := by
              simp [LocalizedModule.map]
      _ = (LocalizedModule.map T N.subtype)
            ((LocalizedModule.mkLinearMap T N) ⟨z, hz⟩) :=
        congrArg (LocalizedModule.map T N.subtype) hkt
      _ = (LocalizedModule.mkLinearMap T F) z := by
        change ((IsLocalizedModule.map T (LocalizedModule.mkLinearMap T N)
          (LocalizedModule.mkLinearMap T F)) N.subtype)
            ((LocalizedModule.mkLinearMap T N) ⟨z, hz⟩) =
          (LocalizedModule.mkLinearMap T F) z
        simp only [IsLocalizedModule.map_apply]
        rfl

/-- A finite free presentation of `M` with finitely many relations which already generate the
kernel after inverting `f`. -/
private theorem exists_fg_relations_localized_ker_eq {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)
    (hfp : Module.FinitePresentation (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M)) :
    ∃ (n : ℕ) (q : (Fin n → A) →ₗ[A] M) (K : Submodule A (Fin n → A)),
      Function.Surjective q ∧ K.FG ∧ K ≤ q.ker ∧
        K.localized (Submonoid.powers f) = q.ker.localized (Submonoid.powers f) := by
  classical
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A M
  let _ : Module.FinitePresentation (Localization (Submonoid.powers f))
    (LocalizedModule (Submonoid.powers f) M) := hfp
  let _ : Module.Finite (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) q.ker) :=
    finite_localizedModule_ker (Submonoid.powers f) q hq
  obtain ⟨K₀, hK₀fg, hK₀top⟩ := exists_fg_localized_eq_top (Submonoid.powers f) (M := q.ker)
  exact ⟨n, q, K₀.map q.ker.subtype, hq, hK₀fg.map q.ker.subtype,
    Submodule.map_subtype_le q.ker K₀,
    localized_map_subtype_eq (Submonoid.powers f) q.ker K₀ hK₀top⟩

/-- Dividing out relations that generate the kernel after localizing gives an isomorphism after
localizing. -/
private theorem bijective_localizedModule_map_liftQ {A F : Type u} {M : Type v} [CommRing A]
    [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M] (T : Submonoid A)
    (q : F →ₗ[A] M) (hq : Function.Surjective q) (K : Submodule A F) (hK : K ≤ q.ker)
    (hKloc : K.localized T = q.ker.localized T) :
    Function.Bijective (LocalizedModule.map T (K.liftQ q hK)) := by
  have hcomp : LocalizedModule.map T q =
      (LocalizedModule.map T (K.liftQ q hK)).comp (LocalizedModule.map T K.mkQ) := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨⟨m, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective T (LocalizedModule.mkLinearMap T F) x
    simp [LocalizedModule.map, IsLocalizedModule.map_mk']
  have hkerπ : (LocalizedModule.map T K.mkQ).ker = K.localized T := by
    change ((IsLocalizedModule.map T (LocalizedModule.mkLinearMap T F)
      (LocalizedModule.mkLinearMap T (F ⧸ K)) K.mkQ).extendScalarsOfIsLocalization
        T (Localization T)).ker = K.localized T
    simpa only [Submodule.ker_mkQ] using
      (LinearMap.localized'_ker_eq_ker_localizedMap (Localization T) T
        (LocalizedModule.mkLinearMap T F)
        (LocalizedModule.mkLinearMap T (F ⧸ K)) K.mkQ).symm
  have hkerq : (LocalizedModule.map T q).ker = q.ker.localized T :=
    (LinearMap.localized'_ker_eq_ker_localizedMap (Localization T) T
      (LocalizedModule.mkLinearMap T F) (LocalizedModule.mkLinearMap T M) q).symm
  have hπsurj : Function.Surjective (LocalizedModule.map T K.mkQ) :=
    IsLocalizedModule.map_surjective T (LocalizedModule.mkLinearMap T F)
      (LocalizedModule.mkLinearMap T (F ⧸ K)) K.mkQ K.mkQ_surjective
  have hqKsurj : Function.Surjective (K.liftQ q hK) := fun m ↦ by
    obtain ⟨x, rfl⟩ := hq m
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine ⟨?_, IsLocalizedModule.map_surjective T (LocalizedModule.mkLinearMap T (F ⧸ K))
    (LocalizedModule.mkLinearMap T M) (K.liftQ q hK) hqKsurj⟩
  rw [← LinearMap.ker_eq_bot]
  refine bot_unique fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := hπsurj y
  have hxq : x ∈ (LocalizedModule.map T q).ker := by
    rw [LinearMap.mem_ker]
    exact hcomp ▸ hy
  have hxπ : x ∈ (LocalizedModule.map T K.mkQ).ker := by
    rwa [hkerπ, hKloc, ← hkerq]
  simpa only [Submodule.mem_bot] using LinearMap.mem_ker.mp hxπ

/-- A bijection after localizing at `T` stays a bijection after localizing at a larger monoid,
provided the map itself is surjective. -/
private theorem bijective_localizedModule_map_of_le {A : Type u} {X : Type v} {Y : Type w}
    [CommRing A] [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y] (T U : Submonoid A)
    (hTU : T ≤ U) (q : X →ₗ[A] Y) (hq : Function.Surjective q)
    (hqT : Function.Bijective (LocalizedModule.map T q)) :
    Function.Bijective (LocalizedModule.map U q) := by
  refine ⟨?_, IsLocalizedModule.map_surjective U (LocalizedModule.mkLinearMap U X)
    (LocalizedModule.mkLinearMap U Y) q hq⟩
  rw [← LinearMap.ker_eq_bot]
  refine bot_unique fun z hz ↦ ?_
  obtain ⟨⟨x, t⟩, rfl⟩ :=
    IsLocalizedModule.mk'_surjective U (LocalizedModule.mkLinearMap U X) z
  have hqzero : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap U Y) (q x) t = 0 := by
    rw [LinearMap.mem_ker] at hz
    simpa [LocalizedModule.map, IsLocalizedModule.mapExtendScalars] using hz
  obtain ⟨w, hw⟩ := (IsLocalizedModule.mk'_eq_zero'
    (LocalizedModule.mkLinearMap U Y) t).mp hqzero
  have hTzero : (LocalizedModule.mkLinearMap T Y) (q (w • x)) = 0 := by
    rw [show q (w • x) = 0 from by
      change q ((w : A) • x) = 0
      rw [map_smul, show (w : A) • q x = 0 from hw], map_zero]
  have hxT : (LocalizedModule.mkLinearMap T X) (w • x) = 0 := by
    refine hqT.1 ?_
    rw [map_zero]
    change ((IsLocalizedModule.map T (LocalizedModule.mkLinearMap T X)
      (LocalizedModule.mkLinearMap T Y)) q)
        ((LocalizedModule.mkLinearMap T X) (w • x)) = 0
    simpa only [IsLocalizedModule.map_apply] using hTzero
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff T
    (LocalizedModule.mkLinearMap T X)).mp hxT
  have hsU : (⟨s, hTU s.property⟩ : U) • (w • x) = 0 := hs
  refine (IsLocalizedModule.mk'_eq_zero' (LocalizedModule.mkLinearMap U X) t).mpr ?_
  exact ⟨⟨s, hTU s.property⟩ * w, by simpa only [mul_smul] using hsU⟩

/-- **Approximation by a finitely presented module.**  A finite module `M` whose localization away
from `f` is finitely presented receives a surjection from a finitely presented module which is an
isomorphism after inverting `f`. -/
private theorem exists_finitePresentation_bijective_away {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)
    (hfp : Module.FinitePresentation (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M)) :
    ∃ (n : ℕ) (K : Submodule A (Fin n → A)), K.FG ∧
      ∃ q : ((Fin n → A) ⧸ K) →ₗ[A] M, Function.Surjective q ∧
        Function.Bijective (LocalizedModule.map (Submonoid.powers f) q) := by
  classical
  obtain ⟨n, q, K, hq, hKfg, hKle, hKloc⟩ := exists_fg_relations_localized_ker_eq f hfp
  refine ⟨n, K, hKfg, K.liftQ q hKle, fun m ↦ ?_,
    bijective_localizedModule_map_liftQ (Submonoid.powers f) q hq K hKle hKloc⟩
  obtain ⟨x, rfl⟩ := hq m
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The Fitting ideals of a base change are the extensions of the Fitting ideals, at any integer
index. -/
private theorem fittingIdeal_tensor_eq_map {R : Type u} {M : Type v} {S : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [CommRing S] [Algebra R S] (k : ℤ) :
    fittingIdeal (R := S) (M := S ⊗[R] M) k =
      Ideal.map (algebraMap R S) (fittingIdeal (R := R) (M := M) k) := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [fittingIdeal_eq_bot_of_lt_zero hk, fittingIdeal_eq_bot_of_lt_zero hk, Ideal.map_bot]
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact (fittingIdeal_basic_properties.{u, v, u, w} (R := R) (M := M)).2.2.1 S j

/-- The Fitting ideals of a localized module are the extensions of the Fitting ideals. -/
private theorem fittingIdeal_localizedModule_eq_map {B : Type u} {P : Type v} [CommRing B]
    [AddCommGroup P] [Module B P] [Module.Finite B P] (T : Submonoid B) (k : ℤ) :
    fittingIdeal (R := Localization T) (M := LocalizedModule T P) k =
      Ideal.map (algebraMap B (Localization T)) (fittingIdeal (R := B) (M := P) k) := by
  rw [fittingIdeal_eq_of_linearEquiv_int (LocalizedModule.equivTensorProduct T P),
    fittingIdeal_tensor_eq_map]

/-- An ideal which becomes the unit ideal in a localization at `T` is not contained in a set
disjoint from `T`. -/
private theorem not_le_of_map_localization_eq_top {B : Type*} [CommRing B] (T : Submonoid B)
    (J q : Ideal B) (hdisj : Disjoint (T : Set B) q)
    (h : Ideal.map (algebraMap B (Localization T)) J = ⊤) : ¬ J ≤ q := fun hle ↦
  (IsLocalization.map_algebraMap_ne_top_iff_disjoint T (Localization T) q).2 hdisj
    (top_unique (h ▸ Ideal.map_mono hle))

/-! ### The lower Fitting ideal is `f`-power torsion

Freeness of rank `r` at every extended prime `pS` with `f ∉ p` makes the `(r-1)`st Fitting ideal
of `M` vanish in `S_q` for `q = pS`.  Because elements of `S ∖ pS` are nonzerodivisors on `S_p`,
the vanishing descends to `S_p`; and a section of `S` vanishing in `S_p` for every `p` missing `f`
vanishes in `S_f`. -/

/-- The fibre of a geometrically integral fibre ring is a domain. -/
private theorem isDomain_fiber_of_isGeometricallyIntegral {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (hgeom : Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber S)) :
    IsDomain (p.Fiber S) := by
  have _ : IsDomain (p.Fiber S ⊗[p.ResidueField] p.ResidueField) :=
    (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct p.ResidueField
      (p.Fiber S)).mp hgeom p.ResidueField
  exact (Algebra.TensorProduct.rid p.ResidueField p.ResidueField
    (p.Fiber S)).symm.toRingEquiv.injective.isDomain _

/-- **Vanishing at the generic point of the fibre descends to the base prime.**  If an element of
`S` dies in the localization of `S` at the extended prime `pS`, it already dies in the
localization of `S` at `p`, the fibre over `p` being integral and `S` projective over `R`. -/
private theorem mkLinearMap_atPrime_eq_zero_of_atExtended_eq_zero {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Projective R S] (p : Ideal R)
    [p.IsPrime] (hdom : IsDomain (p.Fiber S))
    [hq : (Ideal.map (algebraMap R S) p).IsPrime] (x : S)
    (hx : LocalizedModule.mkLinearMap (Ideal.map (algebraMap R S) p).primeCompl S x = 0) :
    LocalizedModule.mkLinearMap p.primeCompl S x = 0 := by
  obtain ⟨s, hsx⟩ := (IsLocalizedModule.eq_zero_iff
    (Ideal.map (algebraMap R S) p).primeCompl
    (LocalizedModule.mkLinearMap (Ideal.map (algebraMap R S) p).primeCompl S)).mp hx
  have hinj := Module.Projective.injective_lsmul_localizedModule p hdom (s := (s : S)) s.2
  have hmap : (LocalizedModule.map p.primeCompl
      ((LinearMap.lsmul S S (s : S)).restrictScalars R))
        (LocalizedModule.mkLinearMap p.primeCompl S x) =
      LocalizedModule.mkLinearMap p.primeCompl S ((s : S) * x) := by
    change (IsLocalizedModule.map p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl S)
      (LocalizedModule.mkLinearMap p.primeCompl S)
      ((LinearMap.lsmul S S (s : S)).restrictScalars R))
      (LocalizedModule.mk x 1) = LocalizedModule.mk ((s : S) * x) 1
    convert (IsLocalizedModule.map_LocalizedModules
      (S := p.primeCompl) ((LinearMap.lsmul S S (s : S)).restrictScalars R) x 1) using 1
    rfl
  refine hinj ?_
  rw [hmap, show (s : S) * x = 0 from by
    simpa only [Submonoid.smul_def, smul_eq_mul] using hsx]
  simp

/-- **A section vanishing at every prime missing `f` vanishes after inverting `f`.**  If an
element `x` of a module dies in the localization at every prime `p` with `f ∉ p`, then it dies in
the localization away from `f`.

Otherwise the annihilator of `x` misses the powers of `f`, so it is contained in a prime `p`
disjoint from them; the hypothesis at that `p` produces an annihilating element outside `p`,
a contradiction. -/
private theorem mkLinearMap_away_eq_zero_of_atPrime_eq_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (x : M)
    (h : ∀ (p : Ideal R) (_hp : p.IsPrime), f ∉ p →
      LocalizedModule.mkLinearMap p.primeCompl M x = 0) :
    LocalizedModule.mkLinearMap (Submonoid.powers f) M x = 0 := by
  classical
  by_contra hx
  have hdisj : Disjoint ((R ∙ x).annihilator : Set R) (Submonoid.powers f : Set R) := by
    rw [Set.disjoint_left]
    intro y hyI hyP
    refine hx ((IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mpr ?_)
    exact ⟨⟨y, hyP⟩, (Submodule.mem_annihilator_span_singleton x y).mp hyI⟩
  obtain ⟨p, hp, hIp, hpd⟩ :=
    Ideal.exists_le_prime_disjoint (R ∙ x).annihilator (Submonoid.powers f) hdisj
  have hf : f ∉ p := fun hfp ↦ (Set.disjoint_left.mp hpd) hfp (Submonoid.mem_powers f)
  have _ : p.IsPrime := hp
  obtain ⟨s, hsx⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).mp (h p hp hf)
  exact s.2 (hIp ((Submodule.mem_annihilator_span_singleton x s.1).mpr hsx))

/-- **The lower Fitting ideal of `M` is `f`-power torsion.**  Under the hypotheses of Stacks
Tag 0810, every element of `Fit_{r-1}(M)` dies in the localization of `S` away from `f`. -/
private theorem fittingIdeal_pred_away_eq_zero {R S : Type u} {M : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Projective R S] [AddCommGroup M]
    [Module S M] [Module.Finite S M] (f : R) (r : ℕ)
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber S))
    (hrank : ∀ (p : Ideal R) (hp : p.IsPrime), f ∉ p →
      letI := hp
      let q := Ideal.map (algebraMap R S) p
      ∀ hq : q.IsPrime,
        letI := hq
        Nonempty
          (LocalizedModule q.primeCompl M ≃ₗ[Localization q.primeCompl]
            (Fin r → Localization q.primeCompl)))
    {x : S} (hx : x ∈ fittingIdeal (R := S) (M := M) ((r : ℤ) - 1)) :
    LocalizedModule.mkLinearMap (Submonoid.powers f) S x = 0 := by
  classical
  refine mkLinearMap_away_eq_zero_of_atPrime_eq_zero f x fun p hp hf ↦ ?_
  have _ : p.IsPrime := hp
  have hdom : IsDomain (p.Fiber S) := isDomain_fiber_of_isGeometricallyIntegral p (hfibre p hp)
  have hq : (Ideal.map (algebraMap R S) p).IsPrime :=
    Ideal.isPrime_map_of_flat_of_isDomain_fiber' p hdom
  have _ : (Ideal.map (algebraMap R S) p).IsPrime := hq
  have hmap : Ideal.map
      (algebraMap S (Localization (Ideal.map (algebraMap R S) p).primeCompl))
      (fittingIdeal (R := S) (M := M) ((r : ℤ) - 1)) = ⊥ := by
    rw [← fittingIdeal_localizedModule_eq_map,
      fittingIdeal_eq_of_linearEquiv_int (hrank p hp hf hq).some, fittingIdeal_fin_eq_bot_or_top]
    simp
  refine mkLinearMap_atPrime_eq_zero_of_atExtended_eq_zero p hdom x ?_
  have hmem : (algebraMap S (Localization (Ideal.map (algebraMap R S) p).primeCompl)) x ∈
      Ideal.map (algebraMap S (Localization (Ideal.map (algebraMap R S) p).primeCompl))
        (fittingIdeal (R := S) (M := M) ((r : ℤ) - 1)) :=
    Ideal.mem_map_of_mem _ hx
  rw [hmap] at hmem
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff
    (Ideal.map (algebraMap R S) p).primeCompl
    (Localization (Ideal.map (algebraMap R S) p).primeCompl) x).mp (Ideal.mem_bot.mp hmem)
  refine (IsLocalizedModule.eq_zero_iff (Ideal.map (algebraMap R S) p).primeCompl
    (LocalizedModule.mkLinearMap (Ideal.map (algebraMap R S) p).primeCompl S)).mpr ?_
  exact ⟨t, by simpa only [Submonoid.smul_def, smul_eq_mul] using ht⟩

/-! ### From `f`-power torsion to vanishing on the chart -/

/-- An ideal contained in `(b)` and containing `g ⬝ b` becomes the principal ideal generated by
`b` after inverting `g`. -/
private theorem map_ideal_eq_span_of_le_and_mul_mem {B T : Type*} [CommRing B] [CommRing T]
    [Algebra B T] (J : Ideal B) (b g : B) [IsLocalization.Away g T] (hJ : J ≤ Ideal.span {b})
    (hgb : g * b ∈ J) :
    Ideal.map (algebraMap B T) J = Ideal.span {algebraMap B T b} := by
  refine le_antisymm ?_ ?_
  · calc
      Ideal.map (algebraMap B T) J ≤ Ideal.map (algebraMap B T) (Ideal.span {b}) :=
        Ideal.map_mono hJ
      _ = Ideal.span {algebraMap B T b} := by rw [Ideal.map_span]; simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hmul : algebraMap B T b * algebraMap B T g ∈ Ideal.map (algebraMap B T) J := by
      rw [← map_mul, mul_comm]
      exact Ideal.mem_map_of_mem (algebraMap B T) hgb
    exact ((Ideal.map (algebraMap B T) J).mul_unit_mem_iff_mem
      (IsLocalization.Away.algebraMap_isUnit g)).mp hmul

/-- An ideal all of whose elements are `f`-power torsion dies in any algebra where `f` becomes a
unit. -/
private theorem ideal_map_eq_bot_of_away_torsion {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (f : R)
    (J : Ideal S)
    (h : ∀ x ∈ J, LocalizedModule.mkLinearMap (Submonoid.powers f) S x = 0)
    (hunit : IsUnit (algebraMap R T f)) :
    Ideal.map (algebraMap S T) J = ⊥ := by
  refine (Ideal.map_eq_bot_iff_le_ker (algebraMap S T)).2 fun x hx ↦ ?_
  rw [RingHom.mem_ker]
  obtain ⟨s, hsx⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) S)).mp (h x hx)
  obtain ⟨_, ⟨n, rfl⟩⟩ := s
  have hfx : (algebraMap R S f) ^ n * x = 0 := by
    simpa only [Submonoid.smul_def, Algebra.smul_def, map_pow] using hsx
  have hzero : (algebraMap R T f) ^ n * (algebraMap S T x) = 0 := by
    simpa only [map_mul, map_pow, map_zero, IsScalarTower.algebraMap_apply R S T] using
      congrArg (algebraMap S T) hfx
  exact (hunit.pow n).mul_right_eq_zero.mp hzero

/-- An ideal dying after inverting a nonzerodivisor is zero. -/
private theorem ideal_eq_bot_of_map_away_eq_bot {R : Type*} [CommRing R] (a : R)
    (ha : a ∈ nonZeroDivisors R) (J : Ideal R)
    (hJ : Ideal.map (algebraMap R (Localization.Away a)) J = ⊥) :
    J = ⊥ := by
  have hinj : Function.Injective (algebraMap R (Localization.Away a)) :=
    IsLocalization.injectiveₛ (M := Submonoid.powers a) (Localization.Away a) (by
      intro c hc
      obtain ⟨n, hn⟩ := hc
      simpa [hn] using IsRegular.pow n (isRegular_iff_mem_nonZeroDivisors.mpr ha))
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  have hxmap : (algebraMap R (Localization.Away a)) x = 0 := by
    have hx' : (algebraMap R (Localization.Away a)) x ∈
        Ideal.map (algebraMap R (Localization.Away a)) J :=
      Ideal.mem_map_of_mem _ hx
    rw [hJ] at hx'
    exact Ideal.mem_bot.mp hx'
  exact Ideal.mem_bot.mpr (hinj (by simpa using hxmap))

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Geometrically integral fibres survive base change of the base.**  If every fibre of `S` over
`R` is geometrically integral, then for every prime `p'` of an `R`-algebra `A` the fibre of
`S ⊗[R] A` over `p'` is a domain.

The fibre over `p'` is the base change along `κ(p) → κ(p')` of the fibre over `p = p' ∩ R`, which
is a domain precisely because the latter is *geometrically* integral. -/
public theorem isDomain_fiber_baseChange {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber S))
    (p' : Ideal A) [p'.IsPrime] :
    letI : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    IsDomain (p'.Fiber (S ⊗[R] A)) := by
  let B := S ⊗[R] A
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let p : Ideal R := p'.comap (algebraMap R A)
  let : p.IsPrime := Ideal.IsPrime.comap (algebraMap R A)
  let : Algebra p.ResidueField p'.ResidueField :=
    (Ideal.ResidueField.mapₐ p p' (Algebra.ofId R A) rfl).toRingHom.toAlgebra
  let : Module p.ResidueField p'.ResidueField :=
    (inferInstance : Algebra p.ResidueField p'.ResidueField).toModule
  let : IsScalarTower R p.ResidueField p'.ResidueField :=
    .of_algebraMap_eq fun x ↦
      ((Ideal.ResidueField.mapₐ p p' (Algebra.ofId R A) rfl).commutes x).symm
  let : Algebra.IsPushout R S A B := inferInstance
  let e : (p'.ResidueField ⊗[p.ResidueField] p.Fiber S) ≃+* p'.Fiber B :=
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
      p'.ResidueField S).toRingEquiv.trans
      ((Algebra.TensorProduct.comm R p'.ResidueField S).toRingEquiv.trans
        ((Algebra.IsPushout.cancelBaseChangeAlg R S A B p'.ResidueField).symm.toRingEquiv.trans
          (Algebra.TensorProduct.comm A B p'.ResidueField).toRingEquiv))
  have hright : IsDomain (p.Fiber S ⊗[p.ResidueField] p'.ResidueField) :=
    (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct
      p.ResidueField (p.Fiber S)).mp (hfibre p inferInstance) p'.ResidueField
  have hleft : IsDomain (p'.ResidueField ⊗[p.ResidueField] p.Fiber S) :=
    (Algebra.TensorProduct.comm p.ResidueField p'.ResidueField
      (p.Fiber S)).toRingEquiv.injective.isDomain _
  exact e.symm.injective.isDomain _

/-! ### Flattening on every affine blowup chart -/

/-- **The conclusion of Stacks Tag 0810, granted projectivity of `S` over `R`.**  Let `R → S` be
flat and of finite presentation with geometrically integral fibres and projective as a module, let
`f ∈ R`, and let `M` be a finite `S`-module which is finitely presented after inverting `f` and
free of rank `r` at every extended prime `pS` with `f ∉ p`.  Then there is a finitely generated
ideal `I ⊆ R` with `V(f) = V(I)` such that for every `a ∈ I`, writing `R' = R[I/a]` and
`S' = S ⊗[R] R'`, the quotient `M'` of `S' ⊗[S] M` by its `a`-power torsion is free of rank `r`
after inverting some `g ∈ S'` outside `p'S'`, for every prime `p'` of `R'`.

Projectivity of `S` as an `R`-module is Stacks Tag 05FT, which is not available in this library;
see the module documentation and
`exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_good_halves`.

The ideal is `I = fI'` with `I'` the ideal of coefficients of `J = Fit_r(M₁)` for a finitely
presented approximation `M₁` of `M`; on the chart `R[I/a]`, `a = fb`, the ideal `I'` becomes
principal, generated by the image of `b`, which is a nonzerodivisor, so `Fit_r` of the strict
transform becomes the unit ideal near each extended prime and `Fit_{r-1}` of the strict transform
vanishes, these being the two conditions for freeness of rank `r`. -/
theorem exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_projective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S] [Module.Projective R S]
    (M : Type v) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (f : R) (r : ℕ)
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber S))
    (hfp : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule (Submonoid.powers (algebraMap R S f)) M))
    (hrank : ∀ (p : Ideal R) (hp : p.IsPrime), f ∉ p →
      letI := hp
      let q := Ideal.map (algebraMap R S) p
      ∀ hq : q.IsPrime,
        letI := hq
        Nonempty
          (LocalizedModule q.primeCompl M ≃ₗ[Localization q.primeCompl]
            (Fin r → Localization q.primeCompl))) :
    ∃ I : Ideal R, I.FG ∧
      (∀ (p : Ideal R), p.IsPrime → (f ∈ p ↔ I ≤ p)) ∧
      ∀ (a : R) (ha : a ∈ I),
        letI : Fact (a ∈ I) := ⟨ha⟩
        let R' := Blowup I a
        let S' := S ⊗[R] R'
        let N := S' ⊗[S] M
        let M' := N ⧸ Submodule.torsion' S' N
          (Submonoid.powers (algebraMap S S' (algebraMap R S a)))
        ∀ (p' : Ideal R') (_hp' : p'.IsPrime), ∃ g : S',
          g ∉ Ideal.map Algebra.TensorProduct.includeRight p' ∧
          Nonempty
            (LocalizedModule (Submonoid.powers g) M' ≃ₗ[Localization.Away g]
              (Fin r → Localization.Away g)) := by
  classical
  obtain ⟨n, K, hKfg, q, hq, hqf⟩ :=
    exists_finitePresentation_bijective_away (algebraMap R S f) hfp
  let N := (Fin n → S) ⧸ K
  let : Module.FinitePresentation S N :=
    Module.finitePresentation_of_free_of_surjective K.mkQ K.mkQ_surjective (by
      change (LinearMap.ker (Submodule.mkQ K)).FG
      rw [Submodule.ker_mkQ]
      exact hKfg)
  let J := fittingIdeal (R := S) (M := N) (r : ℤ)
  have hJfg : J.FG :=
    (fittingIdeal_basic_properties.{u, u, u, u} (R := S) (M := N)).2.2.2.1 inferInstance r
  obtain ⟨I', hI'fg, hI'content⟩ :=
    exists_fg_coefficientIdeal_of_projective (R := R) (S := S) J hJfg
  let I : Ideal R := Ideal.span {f} * I'
  have hIfg : I.FG := (Submodule.fg_span (Set.finite_singleton f)).mul hI'fg
  refine ⟨I, hIfg, ?_, ?_⟩
  · intro p hp
    refine ⟨fun hfp ↦ ?_, fun hIp ↦ ?_⟩
    · exact (Ideal.mul_le_left : I ≤ Ideal.span {f}).trans
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfp))
    · by_contra hfn
      have _ : p.IsPrime := hp
      have hI'p : I' ≤ p :=
        (hp.mul_le.mp hIp).resolve_left fun h ↦ hfn (h (Ideal.mem_span_singleton_self f))
      have hJq : J ≤ Ideal.map (algebraMap R S) p := (hI'content p).2 hI'p
      have hdom : IsDomain (p.Fiber S) := isDomain_fiber_of_isGeometricallyIntegral p (hfibre p hp)
      have hqprime : (Ideal.map (algebraMap R S) p).IsPrime :=
        Ideal.isPrime_map_of_flat_of_isDomain_fiber' p hdom
      have hqcontract : (Ideal.map (algebraMap R S) p).comap (algebraMap R S) = p :=
        comap_map_eq_of_flat_isPrime (algebraMap R S)
          (RingHom.flat_algebraMap_iff.mpr inferInstance) p hqprime
      have hfq : algebraMap R S f ∉ Ideal.map (algebraMap R S) p := fun hfq ↦ hfn (by
        rwa [← hqcontract])
      have hfree := hrank p hp hfn hqprime
      let qS := Ideal.map (algebraMap R S) p
      let : qS.IsPrime := hqprime
      have hpow : Submonoid.powers (algebraMap R S f) ≤ qS.primeCompl :=
        Submonoid.powers_le.mpr hfq
      have hqprimeiso : Function.Bijective (LocalizedModule.map qS.primeCompl q) :=
        bijective_localizedModule_map_of_le
          (Submonoid.powers (algebraMap R S f)) qS.primeCompl hpow q hq hqf
      let e : LocalizedModule qS.primeCompl N ≃ₗ[Localization qS.primeCompl]
          (Fin r → Localization qS.primeCompl) :=
        (LinearEquiv.ofBijective (LocalizedModule.map qS.primeCompl q) hqprimeiso).trans
          hfree.some
      have hmaptop : Ideal.map (algebraMap S (Localization qS.primeCompl)) J = ⊤ := by
        rw [← fittingIdeal_localizedModule_eq_map, fittingIdeal_eq_of_linearEquiv_int e,
          fittingIdeal_fin_eq_bot_or_top]
        simp
      exact not_le_of_map_localization_eq_top qS.primeCompl J qS
        (Set.disjoint_left.mpr fun _ hx hxq ↦ hx hxq) hmaptop hJq
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.mp ha
    let : Fact (f * b ∈ I) := ⟨ha⟩
    let A := Blowup I (f * b)
    let B := S ⊗[R] A
    let : Algebra A B := Algebra.TensorProduct.rightAlgebra
    let eAB : (A ⊗[R] S) ≃ₐ[A] B :=
      AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A S).toRingEquiv) (fun x ↦ rfl)
    let : Module.Flat A B := Module.Flat.of_linearEquiv eAB.symm.toLinearEquiv
    have hI'chart : Ideal.map (algebraMap R A) I' = Ideal.span {algebraMap R A b} :=
      blowup_map_eq_span_of_mul I' f b hb
    have hfbreg : algebraMap R A (f * b) ∈ nonZeroDivisors A :=
      blowup_image_a_mem_nonZeroDivisors I (f * b) ha
    have hbreg : algebraMap R A b ∈ nonZeroDivisors A := by
      refine mem_nonZeroDivisors_iff_left.mpr fun x hx ↦ ?_
      refine (mem_nonZeroDivisors_iff_left.mp hfbreg) x ?_
      rw [map_mul, mul_assoc, hx, mul_zero]
    have hcomm : (algebraMap S B).comp (algebraMap R S) = (algebraMap A B).comp (algebraMap R A) :=
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    have hJBle : Ideal.map (algebraMap S B) J ≤
        Ideal.span {algebraMap A B (algebraMap R A b)} := by
      calc
        Ideal.map (algebraMap S B) J ≤
            Ideal.map (algebraMap S B) (Ideal.map (algebraMap R S) I') :=
          Ideal.map_mono ((hI'content I').2 le_rfl)
        _ = Ideal.map (algebraMap A B) (Ideal.map (algebraMap R A) I') := by
          rw [Ideal.map_map, Ideal.map_map, hcomm]
        _ = Ideal.span {algebraMap A B (algebraMap R A b)} := by
          rw [hI'chart, Ideal.map_span]
          simp
    let C := B ⊗[S] N
    let D := B ⊗[S] M
    let P := D ⧸ Submodule.torsion' B D
      (Submonoid.powers (algebraMap S B (algebraMap R S (f * b))))
    have hCfinite : Module.Finite B C := inferInstance
    have hPfinite : Module.Finite B P := inferInstance
    have hfitC : fittingIdeal (R := B) (M := C) (r : ℤ) = Ideal.map (algebraMap S B) J :=
      fittingIdeal_tensor_eq_map (r : ℤ)
    have hfbEq : algebraMap S B (algebraMap R S (f * b)) =
        algebraMap A B (algebraMap R A (f * b)) :=
      congrArg (fun h : R →+* B ↦ h (f * b)) hcomm
    have hfbregB : algebraMap S B (algebraMap R S (f * b)) ∈ nonZeroDivisors B := by
      have hregA : IsSMulRegular A (algebraMap R A (f * b)) :=
        (isRegular_iff_mem_nonZeroDivisors.mpr hfbreg).left
      have hregB : IsSMulRegular B (algebraMap A B (algebraMap R A (f * b))) := hregA.of_flat
      refine hfbEq ▸ mem_nonZeroDivisors_iff_left.mpr fun x hx ↦ ?_
      exact (isSMulRegular_iff_right_eq_zero_of_smul.mp hregB) x (by
        simpa only [smul_eq_mul] using hx)
    have hbP : ∀ x : P, algebraMap A B (algebraMap R A b) • x = 0 → x = 0 := by
      intro x hx
      refine smul_eq_zero_of_quotient_torsion'
        (Submonoid.powers (algebraMap S B (algebraMap R S (f * b))))
        ⟨algebraMap S B (algebraMap R S (f * b)), Submonoid.mem_powers _⟩ x ?_
      change algebraMap S B (algebraMap R S (f * b)) • x = 0
      calc
        algebraMap S B (algebraMap R S (f * b)) • x =
            algebraMap A B (algebraMap R A (f * b)) • x :=
          congrArg (fun z : B ↦ z • x) hfbEq
        _ = 0 := by rw [map_mul (algebraMap R A), map_mul (algebraMap A B), mul_smul, hx, smul_zero]
    let qB : C →ₗ[B] D := q.baseChange B
    have hqB : Function.Surjective qB := LinearMap.baseChange_surjective B hq
    let qP : C →ₗ[B] P := (Submodule.mkQ _).comp qB
    have hqP : Function.Surjective qP := (Submodule.mkQ_surjective _).comp hqB
    dsimp only
    intro p' hp'
    let bB := algebraMap A B (algebraMap R A b)
    let q' : Ideal B := Ideal.map (algebraMap A B) p'
    let L : Ideal B := (Ideal.map (algebraMap S B) J).colon (Ideal.span {bB})
    have hJBL : Ideal.map (algebraMap S B) J ≤ Ideal.span {bB} * L := by
      intro y hy
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (hJBle hy)
      have hzL : z ∈ L := by
        rw [Ideal.mem_colon_span_singleton]
        exact ((mul_comm z bB).trans hz.symm) ▸ hy
      exact Ideal.mem_span_singleton_mul.mpr ⟨z, hzL, hz.symm⟩
    have hLnot : ¬ L ≤ q' := by
      intro hLq
      have hJq : Ideal.map (algebraMap S B) J ≤ Ideal.span {bB} * q' :=
        hJBL.trans (Ideal.mul_mono_right hLq)
      have hmapmul : Ideal.map (algebraMap A B) (Ideal.span {algebraMap R A b} * p') =
          Ideal.span {bB} * q' := by
        rw [Ideal.map_mul, Ideal.map_span]
        simp [bB, q']
      have hIle : Ideal.map (algebraMap R A) I' ≤ Ideal.span {algebraMap R A b} * p' :=
        coefficientIdeal_baseChange_le J I' hI'content _ (hmapmul.symm ▸ hJq)
      obtain ⟨z, hz, hzb⟩ := Ideal.mem_span_singleton_mul.mp
        (hIle (hI'chart.symm ▸ Ideal.mem_span_singleton_self (algebraMap R A b)))
      have hz1 : z = 1 := by
        refine sub_eq_zero.mp ((mem_nonZeroDivisors_iff_left.mp hbreg) (z - 1) ?_)
        rw [mul_sub, mul_one, hzb, sub_self]
      exact hp'.ne_top (p'.eq_top_iff_one.mpr (hz1 ▸ hz))
    obtain ⟨g, hgL, hgq⟩ := Set.not_subset.mp hLnot
    have hgb : g * bB ∈ Ideal.map (algebraMap S B) J := Ideal.mem_colon_span_singleton.mp hgL
    let T := Localization.Away g
    let E := LocalizedModule.Away g C
    let F := LocalizedModule.Away g P
    let : Module.Finite B C := hCfinite
    let : Module.Finite B P := hPfinite
    have hJg : Ideal.map (algebraMap B T) (Ideal.map (algebraMap S B) J) =
        Ideal.span {algebraMap B T bB} :=
      map_ideal_eq_span_of_le_and_mul_mem _ bB g hJBle hgb
    have hfitE : fittingIdeal (R := T) (M := E) (r : ℤ) = Ideal.span {algebraMap B T bB} := by
      rwa [fittingIdeal_localizedModule_eq_map, hfitC]
    have hqPg : Function.Surjective (LocalizedModule.map (Submonoid.powers g) qP) :=
      IsLocalizedModule.map_surjective (Submonoid.powers g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) C)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) P) qP hqP
    have hbF : ∀ x : F, algebraMap B T bB • x = 0 → x = 0 := by
      intro x hx
      refine smul_eq_zero_of_localizedModule (Submonoid.powers g) bB hbP x ?_
      simpa only [IsScalarTower.algebraMap_smul] using hx
    have hfitF : fittingIdeal (R := T) (M := F) (r : ℤ) = ⊤ :=
      fittingIdeal_eq_top_of_surjective_of_regular
        (LocalizedModule.map (Submonoid.powers g) qP) hqPg r (algebraMap B T bB) hfitE hbF
    let aB := algebraMap S B (algebraMap R S (f * b))
    let Ta := Localization.Away aB
    let U : Submodule B D := Submodule.torsion' B D (Submonoid.powers aB)
    let ePa : (Ta ⊗[B] P) ≃ₗ[Ta] (Ta ⊗[S] M) :=
      baseChangeQuotEquiv (R := S) (A := B) (S := Ta) (M := M) aB U le_rfl
    have hfTa : IsUnit (algebraMap R Ta f) := by
      have haunit : IsUnit (algebraMap B Ta aB) :=
        IsLocalization.map_units Ta ⟨aB, Submonoid.mem_powers aB⟩
      have hmul : algebraMap B Ta aB = algebraMap R Ta f * algebraMap R Ta b := by
        simp [aB, map_mul, IsScalarTower.algebraMap_apply R S B,
          IsScalarTower.algebraMap_apply R B Ta]
      rw [hmul] at haunit
      exact isUnit_of_mul_isUnit_left haunit
    have hJlowTa : Ideal.map (algebraMap S Ta)
        (fittingIdeal (R := S) (M := M) ((r : ℤ) - 1)) = ⊥ :=
      ideal_map_eq_bot_of_away_torsion f _
        (fun x hx ↦ fittingIdeal_pred_away_eq_zero f r hfibre hrank hx) hfTa
    have hfitP : fittingIdeal (R := B) (M := P) ((r : ℤ) - 1) = ⊥ :=
      ideal_eq_bot_of_map_away_eq_bot aB hfbregB _ (by
        rw [← fittingIdeal_tensor_eq_map, fittingIdeal_eq_of_linearEquiv_int ePa,
          fittingIdeal_tensor_eq_map]
        exact hJlowTa)
    have hqprime : q'.IsPrime := by
      have _ : p'.IsPrime := hp'
      exact Ideal.isPrime_map_of_flat_of_isDomain_fiber' p' (isDomain_fiber_baseChange hfibre p')
    have hdisj : Disjoint (Submonoid.powers g : Set B) (q' : Set B) := by
      rw [Set.disjoint_left]
      intro x hx hxq
      obtain ⟨n, rfl⟩ := hx
      exact hgq (hqprime.mem_of_pow_mem n hxq)
    have hfitNot : ¬ fittingIdeal (R := B) (M := P) (r : ℤ) ≤ q' :=
      not_le_of_map_localization_eq_top (Submonoid.powers g) _ q' hdisj (by
        rw [← fittingIdeal_localizedModule_eq_map]
        exact hfitF)
    obtain ⟨h, hhq, v, hv⟩ :=
      ((fittingIdeal_local_generation_tfae (R := B) (M := P) r q').out 1 4).mp hfitNot
    have hfitPh : fittingIdeal (R := Localization.Away h)
        (M := LocalizedModule.Away h P) ((r : ℤ) - 1) = ⊥ := by
      rw [fittingIdeal_localizedModule_eq_map, hfitP, Ideal.map_bot]
    obtain ⟨basis⟩ := basis_of_span_eq_top_of_fittingIdeal_eq_bot r v hv hfitPh
    exact ⟨h, hhq, ⟨basis.repr.trans
      (Finsupp.linearEquivFunOnFinite (Localization.Away h) (Localization.Away h) (Fin r))⟩⟩

/-! ### Stacks Tag 0810 from the good halves of the generic-fibre dichotomy -/

/-- Geometric integrality transports along an algebra isomorphism. -/
theorem Algebra.IsGeometricallyIntegral.of_algEquiv {k A B : Type u} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : Algebra.IsGeometricallyIntegral k A) :
    Algebra.IsGeometricallyIntegral k B := by
  rw [Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct] at h ⊢
  intro K _ _
  have _ : IsDomain (A ⊗[k] K) := h K
  exact (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toRingEquiv.toMulEquiv.isDomain _

/-- **Stacks Tag 0810, granted the two statements about a single generic fibre that Stacks
Tag 05FT still needs in this library.**  Let `R → S` be flat of finite presentation with
geometrically integral fibres, let `f ∈ R`, and let `M` be a finite `S`-module which is finitely
presented after inverting `f` and free of rank `r` at every extended prime `pS` with `f ∉ p`.
Then the conclusion of Stacks Tag 0810 holds, provided that over every Noetherian domain `D` with
a finite type algebra `T`:

* if the generic fibre of `T` is geometrically reduced, some nonempty basic open of `Spec D` lies
  in `Algebra.geometricallyReducedFibreLocus D T` (the affine case of Stacks Tag 0578), and
* if the generic fibre of `T` is geometrically irreducible, some nonempty basic open of `Spec D`
  lies in `Algebra.geometricallyIrreducibleFibreLocus D T` (the affine case of Stacks
  Tag 055A).

Those two hypotheses are exactly the ones of
`Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves`, and they serve only to make
`S` a projective `R`-module; the rest is
`exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_projective`. -/
theorem exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_good_halves
    (hred : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ Algebra.geometricallyReducedFibreLocus D T →
        ∃ d : D, d ≠ 0 ∧ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum D)) ⊆
          Algebra.geometricallyReducedFibreLocus D T)
    (hirr : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈
          Algebra.geometricallyIrreducibleFibreLocus D T →
        ∃ d : D, d ≠ 0 ∧ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum D)) ⊆
          Algebra.geometricallyIrreducibleFibreLocus D T)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (M : Type v) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (f : R) (r : ℕ)
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber S))
    (hfp : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule (Submonoid.powers (algebraMap R S f)) M))
    (hrank : ∀ (p : Ideal R) (hp : p.IsPrime), f ∉ p →
      letI := hp
      let q := Ideal.map (algebraMap R S) p
      ∀ hq : q.IsPrime,
        letI := hq
        Nonempty
          (LocalizedModule q.primeCompl M ≃ₗ[Localization q.primeCompl]
            (Fin r → Localization q.primeCompl))) :
    ∃ I : Ideal R, I.FG ∧
      (∀ (p : Ideal R), p.IsPrime → (f ∈ p ↔ I ≤ p)) ∧
      ∀ (a : R) (ha : a ∈ I),
        letI : Fact (a ∈ I) := ⟨ha⟩
        let R' := Blowup I a
        let S' := S ⊗[R] R'
        let N := S' ⊗[S] M
        let M' := N ⧸ Submodule.torsion' S' N
          (Submonoid.powers (algebraMap S S' (algebraMap R S a)))
        ∀ (p' : Ideal R') (_hp' : p'.IsPrime), ∃ g : S',
          g ∉ Ideal.map Algebra.TensorProduct.includeRight p' ∧
          Nonempty
            (LocalizedModule (Submonoid.powers g) M' ≃ₗ[Localization.Away g]
              (Fin r → Localization.Away g)) := by
  have _ : Module.Projective R S := by
    refine Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves hred hirr ?_
    intro p hp
    let _ : Algebra p.ResidueField (S ⊗[R] p.ResidueField) := Algebra.TensorProduct.rightAlgebra
    refine Algebra.IsGeometricallyIntegral.of_algEquiv
      (AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R p.ResidueField S).toRingEquiv)
        (fun x ↦ by
          simp [Algebra.TensorProduct.comm_tmul,
            Algebra.TensorProduct.right_algebraMap_apply])) (hfibre p hp)
  exact exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_projective
    R S M f r hfibre hfp hrank
