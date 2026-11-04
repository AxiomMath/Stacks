module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.Deformation.Examples.Geometric.LocalizedSplitting
public import StacksFrontier.Deformation.SquareZero.AlgebraExtensionMaps

/-!
# Torsion in the conormal cokernel away from the smooth locus

Let `k` be a commutative ring, let `B` be a `k`-algebra and let `P` be a presentation of `B`
over `k`.  The cokernel of precomposition with the conormal differential of `P`,

`coker( Hom_B(Ω_{P/k} ⊗ B, N) ⟶ Hom_B(I/I², N) )`,

presents `Ext¹_B(NL_{B/k}, N)`; for the canonical presentation it is
`Stacks.Deformation.extOneCokernel`.  This file collects what that cokernel does not depend on
and what kills it.

Two presentations of `B` over `k` admit maps both ways, and those maps are chain homotopic to
the identity in either composite, so precomposition identifies the two cokernels naturally in
the coefficients.  The cokernel is therefore computed at whichever presentation is convenient,
and a *finite* presentation is the convenient one: at a finite presentation the conormal
differential splits after inverting any element outside the non-smooth locus, so if `B` is
smooth over `k` away from `V(J)` then a power of `J` annihilates the cokernel with every
coefficient module.

## Main results

* `Deformation.Examples.conormalCokernelEquiv`: the cokernel does not depend on the
  presentation.
* `Deformation.Examples.exists_pow_le_conormalSplittingIdeal`: a power of `J` splits the
  conormal differential of a finite presentation when `B` is smooth over `k` away from `V(J)`.
* `Deformation.Examples.exists_pow_smul_eq_zero_extOneCokernel`: hence `Ext¹_B(NL_{B/k}, N)` is
  `J`-power torsion, for a finite type algebra over a field and an arbitrary module `N`.

## Implementation notes

`Stacks.Deformation.extOneCokernel` is built on the canonical presentation
`Algebra.Generators.self k B`, whose conormal module is not finite, so the splitting argument
cannot be run on it directly; it is run at `Algebra.Presentation.ofFinitePresentation` and
transported by `Deformation.Examples.conormalCokernelEquiv`.  Finite type over a field gives
finite presentation, and the reindexing `Algebra.Presentation.reindex` puts the variables in the
universe the transport needs.

Smoothness away from `V(J)` is taken in the form "every prime not containing `J` is a smooth
point"; `Deformation.Examples.exists_pow_smul_eq_zero_extOneCokernel_of_le_of_isSmoothAt` takes
it in the contrapositive form "the non-smooth locus is contained in `V(J)`", which is how the
deformation statements carry it.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 0DZ4](https://stacks.math.columbia.edu/tag/0DZ4)
-/

@[expose] public section

universe uk uB uN uN' uw uw' uw''

namespace Deformation.Examples

open Stacks.Deformation

/-! ### The conormal cokernel at an arbitrary presentation -/

section ConormalCokernel

variable {k : Type uk} {B : Type uB} [CommRing k] [CommRing B] [Algebra k B]

/-- The cokernel of precomposition with the conormal differential of the extension `P`.  For
the canonical presentation this is `Stacks.Deformation.extOneCokernel`, which presents
`Ext¹_B(NL_{B/k}, N)`. -/
abbrev conormalCokernelAt (P : Algebra.Extension.{uw} k B)
    (N : Type uN) [AddCommGroup N] [Module B N] :=
  (P.Cotangent →ₗ[B] N) ⧸
    LinearMap.range (LinearMap.lcomp B N P.cotangentComplex)

/-- Precomposition with the degree-one part of a map of extensions. -/
noncomputable def conormalCokernelPrecomp
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    (f : P.Hom P') (N : Type uN) [AddCommGroup N] [Module B N] :
    conormalCokernelAt P' N →ₗ[B] conormalCokernelAt P N :=
  Submodule.mapQ _ _ (LinearMap.lcomp B N (Algebra.Extension.Cotangent.map f)) (by
    rintro _ ⟨χ, rfl⟩
    refine ⟨χ.comp (Algebra.Extension.CotangentSpace.map f), ?_⟩
    ext x
    exact congrArg χ (Algebra.Extension.CotangentSpace.map_cotangentComplex f x))

/-- `Deformation.Examples.conormalCokernelPrecomp` on the class of a map: precompose it with the
degree-one part of `f`. -/
@[simp]
lemma conormalCokernelPrecomp_mk
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    (f : P.Hom P') (N : Type uN) [AddCommGroup N] [Module B N]
    (δ : P'.Cotangent →ₗ[B] N) :
    conormalCokernelPrecomp f N (Submodule.Quotient.mk δ) =
      Submodule.Quotient.mk (δ.comp (Algebra.Extension.Cotangent.map f)) := rfl

/-- Precomposition with the identity map of extensions is the identity. -/
lemma conormalCokernelPrecomp_id (P : Algebra.Extension.{uw} k B)
    (N : Type uN) [AddCommGroup N] [Module B N] :
    conormalCokernelPrecomp (Algebra.Extension.Hom.id P) N = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨δ, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [Submodule.mkQ_apply, conormalCokernelPrecomp_mk, Algebra.Extension.Cotangent.map_id]
  rfl

/-- Precomposition is contravariantly functorial in the map of extensions. -/
lemma conormalCokernelPrecomp_comp
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    {P'' : Algebra.Extension.{uw''} k B}
    (f : P.Hom P') (g : P'.Hom P'') (N : Type uN) [AddCommGroup N] [Module B N] :
    conormalCokernelPrecomp (g.comp f) N =
      (conormalCokernelPrecomp f N).comp (conormalCokernelPrecomp g N) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨δ, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [Submodule.mkQ_apply, conormalCokernelPrecomp_mk, LinearMap.comp_apply,
    conormalCokernelPrecomp_mk, conormalCokernelPrecomp_mk,
    Algebra.Extension.Cotangent.map_comp]
  rfl

/-- Two maps of extensions over the same base induce the same map on conormal cokernels: their
degree-one parts are chain homotopic, and the homotopy lands in the subgroup that is divided
out. -/
lemma conormalCokernelPrecomp_eq
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    (f g : P.Hom P') (N : Type uN) [AddCommGroup N] [Module B N] :
    conormalCokernelPrecomp f N = conormalCokernelPrecomp g N := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨δ, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [Submodule.mkQ_apply, conormalCokernelPrecomp_mk, conormalCokernelPrecomp_mk]
  refine (Submodule.Quotient.eq _).2 ⟨δ.comp (Algebra.Extension.Hom.sub f g), ?_⟩
  have h := Algebra.Extension.Cotangent.map_sub_map f g
  refine LinearMap.ext fun y ↦ ?_
  have hy := congrArg (fun m ↦ δ m) (congrArg (fun φ ↦ φ y) h)
  simpa using hy.symm

/-- Maps both ways between two presentations of `B` over `k` identify their conormal cokernels.
This is the statement dual to `Algebra.Extension.H1Cotangent.equiv`: the first Ext group of the
naive cotangent complex does not depend on the presentation. -/
noncomputable def conormalCokernelEquiv
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    (f : P.Hom P') (g : P'.Hom P) (N : Type uN) [AddCommGroup N] [Module B N] :
    conormalCokernelAt P' N ≃ₗ[B] conormalCokernelAt P N :=
  LinearEquiv.ofLinearMap (conormalCokernelPrecomp f N) (conormalCokernelPrecomp g N)
    (by rw [← conormalCokernelPrecomp_comp, conormalCokernelPrecomp_eq (g.comp f)
          (Algebra.Extension.Hom.id P), conormalCokernelPrecomp_id])
    (by rw [← conormalCokernelPrecomp_comp, conormalCokernelPrecomp_eq (f.comp g)
          (Algebra.Extension.Hom.id P'), conormalCokernelPrecomp_id])

/-- The identification `Deformation.Examples.conormalCokernelEquiv` is precomposition with `f`. -/
@[simp]
lemma conormalCokernelEquiv_apply
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    (f : P.Hom P') (g : P'.Hom P) (N : Type uN) [AddCommGroup N] [Module B N]
    (x : conormalCokernelAt P' N) :
    conormalCokernelEquiv f g N x = conormalCokernelPrecomp f N x := rfl

/-- Postcomposition with a coefficient map, on conormal cokernels. -/
noncomputable def conormalCokernelPushAt (P : Algebra.Extension.{uw} k B)
    {N : Type uN} [AddCommGroup N] [Module B N]
    {N' : Type uN'} [AddCommGroup N'] [Module B N'] (c : N →ₗ[B] N') :
    conormalCokernelAt P N →ₗ[B] conormalCokernelAt P N' :=
  Submodule.mapQ _ _ (LinearMap.compRight B c) (by
    rintro _ ⟨χ, rfl⟩
    exact ⟨c.comp χ, rfl⟩)

/-- `Deformation.Examples.conormalCokernelPushAt` on the class of a map: postcompose it with
`c`. -/
@[simp]
lemma conormalCokernelPushAt_mk (P : Algebra.Extension.{uw} k B)
    {N : Type uN} [AddCommGroup N] [Module B N]
    {N' : Type uN'} [AddCommGroup N'] [Module B N'] (c : N →ₗ[B] N')
    (δ : P.Cotangent →ₗ[B] N) :
    conormalCokernelPushAt P c (Submodule.Quotient.mk δ) =
      Submodule.Quotient.mk (c.comp δ) := rfl

/-- Precomposition with a map of extensions commutes with postcomposition with a coefficient
map. -/
lemma conormalCokernelPrecomp_comp_pushAt
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B} (f : P.Hom P')
    {N : Type uN} [AddCommGroup N] [Module B N]
    {N' : Type uN'} [AddCommGroup N'] [Module B N'] (c : N →ₗ[B] N') :
    (conormalCokernelPrecomp f N').comp (conormalCokernelPushAt P' c) =
      (conormalCokernelPushAt P c).comp (conormalCokernelPrecomp f N) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨δ, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

/-- Bijectivity of the coefficient-push map transfers along maps of extensions both ways. -/
private theorem bijective_conormalCokernelPushAt_of_hom
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    (f : P.Hom P') (g : P'.Hom P)
    {N : Type uN} [AddCommGroup N] [Module B N]
    {N' : Type uN'} [AddCommGroup N'] [Module B N'] (c : N →ₗ[B] N')
    (h : Function.Bijective (conormalCokernelPushAt P c)) :
    Function.Bijective (conormalCokernelPushAt P' c) := by
  have hcomm : ∀ x, conormalCokernelEquiv f g N' (conormalCokernelPushAt P' c x)
      = conormalCokernelPushAt P c (conormalCokernelEquiv f g N x) :=
    fun x ↦ DFunLike.congr_fun (conormalCokernelPrecomp_comp_pushAt f c) x
  have h1 : (conormalCokernelPushAt P' c : _ → _) = fun x ↦
      (conormalCokernelEquiv f g N').symm
        (conormalCokernelPushAt P c (conormalCokernelEquiv f g N x)) := by
    funext x
    rw [← hcomm, LinearEquiv.symm_apply_apply]
  exact h1 ▸ ((conormalCokernelEquiv f g N').symm.bijective.comp h).comp
    (conormalCokernelEquiv f g N).bijective

/-- Bijectivity of the coefficient-push map does not depend on the presentation. -/
lemma bijective_conormalCokernelPushAt_iff
    {P : Algebra.Extension.{uw} k B} {P' : Algebra.Extension.{uw'} k B}
    (f : P.Hom P') (g : P'.Hom P)
    {N : Type uN} [AddCommGroup N] [Module B N]
    {N' : Type uN'} [AddCommGroup N'] [Module B N'] (c : N →ₗ[B] N') :
    Function.Bijective (conormalCokernelPushAt P c) ↔
      Function.Bijective (conormalCokernelPushAt P' c) :=
  ⟨bijective_conormalCokernelPushAt_of_hom f g c, bijective_conormalCokernelPushAt_of_hom g f c⟩

end ConormalCokernel

/-! ### A power of `J` splits the conormal differential -/

section Splitting

variable {k : Type uk} {B : Type uB} [CommRing k] [CommRing B] [Algebra k B]

/-- The ideal of scalars `a` for which multiplication by `a` on the conormal module factors
through the conormal differential.  Such an `a` annihilates the conormal cokernel with any
coefficients. -/
noncomputable def conormalSplittingIdeal (P : Algebra.Extension.{uw} k B) : Ideal B :=
  (B ∙ (LinearMap.range (LinearMap.lcomp B P.Cotangent P.cotangentComplex)).mkQ
    LinearMap.id).annihilator

private theorem mem_conormalSplittingIdeal_iff (P : Algebra.Extension.{uw} k B) (a : B) :
    a ∈ conormalSplittingIdeal P ↔
      ∃ t : P.CotangentSpace →ₗ[B] P.Cotangent,
        t.comp P.cotangentComplex = a • LinearMap.id := by
  rw [conormalSplittingIdeal, Submodule.mem_annihilator_span_singleton, ← map_smul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- A scalar in the splitting ideal annihilates the conormal cokernel for any coefficients. -/
theorem smul_mem_range_lcomp_of_mem_conormalSplittingIdeal
    (P : Algebra.Extension.{uw} k B) {a : B} (ha : a ∈ conormalSplittingIdeal P)
    (N : Type uN) [AddCommGroup N] [Module B N] (φ : P.Cotangent →ₗ[B] N) :
    a • φ ∈ LinearMap.range (LinearMap.lcomp B N P.cotangentComplex) := by
  obtain ⟨t, ht⟩ := (mem_conormalSplittingIdeal_iff P a).1 ha
  refine ⟨φ.comp t, ?_⟩
  refine LinearMap.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun ht x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
  simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, LinearMap.smul_apply, hx, map_smul]

/-- An ideal inside the splitting ideal annihilates the conormal cokernel. -/
theorem smul_top_le_range_lcomp
    (P : Algebra.Extension.{uw} k B) {I : Ideal B} (hI : I ≤ conormalSplittingIdeal P)
    (N : Type uN) [AddCommGroup N] [Module B N] :
    I • (⊤ : Submodule B (P.Cotangent →ₗ[B] N)) ≤
      LinearMap.range (LinearMap.lcomp B N P.cotangentComplex) :=
  Submodule.smul_le.2 fun _ ha φ _ ↦
    smul_mem_range_lcomp_of_mem_conormalSplittingIdeal P (hI ha) N φ

/-- If `B` is smooth over `k` away from the zero set of `J`, then a power of `J` lies in the
splitting ideal: the conormal differential splits after inverting any element outside the
non-smooth locus, so every prime containing the splitting ideal contains `J`, and finiteness
turns that into an inclusion of a power of `J`. -/
theorem exists_pow_le_conormalSplittingIdeal
    [IsNoetherianRing B] [Algebra.EssFiniteType k B]
    (P : Algebra.Extension.{uw} k B) [Algebra.FormallySmooth k P.Ring]
    [Module.Finite B P.Cotangent] [Module.FinitePresentation B P.CotangentSpace]
    (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    ∃ n : ℕ, J ^ n ≤ conormalSplittingIdeal P := by
  have hrad : J ≤ (conormalSplittingIdeal P).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hple, hp⟩
    by_contra hJ
    obtain ⟨t, ht⟩ := exists_localized_cotangent_retraction_of_isSmoothAt P ⟨p, hp⟩
      (hsm ⟨p, hp⟩ hJ)
    obtain ⟨a, l, hl⟩ := exists_smul_id_factor_of_localized_split P.cotangentComplex
      p.primeCompl t ht
    exact a.property (hple ((mem_conormalSplittingIdeal_iff P a).2 ⟨l, hl⟩))
  exact Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)

end Splitting

/-! ### `Ext¹` of the naive cotangent complex is `J`-power torsion -/

section Torsion

variable (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B]

/-- **Stacks 00S1 read on `Ext¹`.**  Let `k` be a field, let `B` be a finite type `k`-algebra
and let `J ⊆ B` be an ideal outside whose zero set `B` is smooth over `k`.  Then a power of `J`
annihilates `Ext¹_B(NL_{B/k}, N)` for every `B`-module `N`.

The conormal differential of a finite presentation of `B` splits after inverting any element
outside the non-smooth locus, so a power of `J` lies in the splitting ideal of that
presentation, and a scalar in the splitting ideal annihilates the conormal cokernel with any
coefficients.  The canonical presentation, on which `Stacks.Deformation.extOneCokernel` is
built, is reached by `Deformation.Examples.conormalCokernelEquiv`. -/
theorem exists_pow_smul_eq_zero_extOneCokernel
    (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N] :
    ∃ n : ℕ, ∀ r ∈ J ^ n, ∀ x : extOneCokernel k B N, r • x = 0 := by
  let : Algebra.FinitePresentation k B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let P₀ := Algebra.Presentation.ofFinitePresentation k B
  let Q := P₀.reindex (Equiv.ulift.{uB}) (Equiv.refl _)
  let : Module.Finite B Q.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite Q.fg_ker
  let : Module.Finite B Q.toExtension.CotangentSpace :=
    Module.Finite.of_basis Q.toGenerators.cotangentSpaceBasis
  let : Module.FinitePresentation B Q.toExtension.CotangentSpace :=
    Module.finitePresentation_of_projective B Q.toExtension.CotangentSpace
  let : Algebra.FormallySmooth k Q.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth k (MvPolynomial _ k))
  obtain ⟨n, hn⟩ := exists_pow_le_conormalSplittingIdeal Q.toExtension J hsm
  refine ⟨n, fun r hr x ↦ ?_⟩
  let e : conormalCokernelAt Q.toExtension N ≃ₗ[B]
      conormalCokernelAt (Algebra.Generators.self k B).toExtension N :=
    conormalCokernelEquiv
      (Algebra.Generators.defaultHom (Algebra.Generators.self k B) Q.toGenerators).toExtensionHom
      (Algebra.Generators.defaultHom Q.toGenerators
        (Algebra.Generators.self k B)).toExtensionHom N
  refine e.symm.injective ?_
  obtain ⟨δ, hδ⟩ := Submodule.mkQ_surjective _ (e.symm x)
  rw [map_smul, map_zero, ← hδ, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  exact smul_mem_range_lcomp_of_mem_conormalSplittingIdeal Q.toExtension (hn hr) N δ

/-- `Deformation.Examples.exists_pow_smul_eq_zero_extOneCokernel` with the smoothness hypothesis
in the form the deformation statements carry it: the non-smooth locus of `B` over `k` is
contained in the zero set of `J`.  The conclusion is read element by element, as the
`J`-power torsion of every class. -/
theorem exists_pow_smul_eq_zero_extOneCokernel_of_le_of_isSmoothAt
    (J : Ideal B)
    (hsmooth : ∀ q : PrimeSpectrum B, ¬ Algebra.IsSmoothAt k q.asIdeal → J ≤ q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N] :
    ∀ g ∈ J, ∀ x : extOneCokernel k B N, ∃ n : ℕ, g ^ n • x = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_extOneCokernel k B J
    (fun q hq ↦ by_contra fun hs ↦ hq (hsmooth q hs)) N
  exact fun g hg x ↦ ⟨n, hn _ (Ideal.pow_mem_pow hg n) x⟩

end Torsion

end Deformation.Examples

end
