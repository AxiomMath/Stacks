module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatFibre
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatTensorProduct
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Weakly associated primes of a flat tensor product, read on the fibre at an arbitrary prime

Let `R → S` be a ring map of finite presentation, let `N` be an `S`-module of finite presentation
which is flat as an `R`-module, let `M` be an `R`-module, and let `𝔮` be a prime of `S` lying
over a prime `𝔭` of `R`.  [Stacks, Tag 05IG] asserts

`𝔮 ∈ WeakAss_S(M ⊗_R N) ↔ (𝔭 ∈ WeakAss_R(M) and 𝔮-bar ∈ Ass_{S-bar}(N-bar))`,

where `S-bar = S ⊗_R κ(𝔭)` is the fibre ring at `𝔭`, `N-bar = N ⊗_R κ(𝔭)` the fibre module,
and `𝔮-bar = 𝔮 S-bar`.  The two sides are not symmetric:  on the left and over `R` the primes
are *weakly* associated, while over the fibre ring they are associated in the strict sense of
[Stacks, Tag 00LA], namely annihilators of single elements.

This file proves the implication from left to right.  The base `𝔭` is replaced by the local ring
`R_𝔭` and `S` by `S_𝔭`, the localization of `S` at the image of `R ∖ 𝔭`;  the localized module
`S_𝔭 ⊗_S N` is again of finite presentation over `S_𝔭` and flat over `R_𝔭`, the map
`R_𝔭 → S_𝔭` is essentially of finite presentation, and the fibre ring `S_𝔭 / 𝔭 S_𝔭` is of
finite presentation over the field `κ(𝔭)` and hence Noetherian.  Those are exactly the
hypotheses of the local statement
`isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct` of
`Stacks.WeaklyAssociatedPrimes`, and weak association travels to `S_𝔭` by
[Stacks, Tag 05C9].  The conclusion is then divided by
`𝔭 S_𝔭` and read as a statement about `S-bar ⊗_S N`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_map_localization`:  weak association
  travels to a localization at a submonoid disjoint from the prime, a half of
  [Stacks, Tag 05C9].
* `Stacks.WeaklyAssociatedPrimes.essentiallyOfFinitePresentation_localization`:  `R_𝔭 → S_𝔭`
  is essentially of finite presentation.
* `Stacks.WeaklyAssociatedPrimes.fibreAlgEquiv`:  the fibre ring `S ⊗_R κ(𝔭)` is `S_𝔭 / 𝔭 S_𝔭`.
* `Stacks.WeaklyAssociatedPrimes.fibreQuotLinearEquiv`:  the fibre module `S-bar ⊗_S N` is
  `N_𝔭 / 𝔭 N_𝔭`.
* `isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct`, in
  `Stacks.WeaklyAssociatedPrimes`:  the fibre clause of [Stacks, Tag 05IG], with no finiteness
  hypothesis beyond the tag's own.
* `isWeaklyAssociatedPrime_and_isAssociatedPrimeStacks_fibre_of_tensorProduct`, in the same
  namespace:  the implication `⟹` of [Stacks, Tag 05IG], for a finitely generated `𝔭`.

## Implementation notes

`WeakAss` is `IsWeaklyAssociatedPrime` of
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs` (tag 0547):  `𝔭` is minimal among the
primes containing the annihilator of some element.  `Ass` is `IsAssociatedPrimeStacks` of
`StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs` (tag 00LA):  `𝔮` is prime and is the
annihilator of a single element — *not* Mathlib's `associatedPrimes`, which takes the radical of
such an annihilator.

The fibre ring is spelled `S_𝔭 / 𝔭 S_𝔭`, that is
`Localization (primeComplImage S p) ⧸ fibreIdeal S p`, and the fibre module as the base change
`S-bar ⊗_S N` of `N` along it.  Mathlib's `Ideal.Fiber`, `p.Fiber S = κ(𝔭) ⊗_R S`, is the same
ring:  `fibreAlgEquiv` is Mathlib's `Ideal.Fiber.algEquivQuotient` with the type written out, and
`map_fibreAlgEquiv_symm` carries `𝔮-bar` across it.  Stating the two main results over
`p.Fiber S` itself was tried and abandoned:  the `Module (p.Fiber S) (p.Fiber S ⊗_S N)` instance
synthesized for such a statement and the one obtained by instantiating the generic transport
lemma at `p.Fiber S` are definitionally but not syntactically equal, and reconciling them
exhausts the elaborator on `p.Fiber S = κ(𝔭) ⊗_R S`, itself a tensor product.  Transporting the
conclusion across `fibreAlgEquiv` by hand is `isAssociatedPrimeStacks_tensor_of_algEquiv`, which
is proved here at that generality.

The tensor product of the tag, `M ⊗_R N`, is written `N ⊗[R] M` throughout, as in the rest of
this development:  the `S`-module structure comes from `N`, and `Module S (N ⊗[R] M)` is the
instance Mathlib provides for the left factor.

## What is not proved

The implication `⟸` of [Stacks, Tag 05IG] is not proved, and the base clause of `⟹` below
assumes that `𝔭` is finitely generated, which the tag does not.  Both gaps have the same cause,
and it is not the absence of the étale-local structure theorem [Stacks, Tag 05ID]:  that theorem
*is* a theorem of this library, as
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt` in
`StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint`.  What
is missing is a *ring-theoretic* form of it, and of the étale comparison of weakly associated
primes [Stacks, Tag 05FP].  Both of those results are scheme-theoretic:  05ID speaks of
`EtaleNeighborhood`, `Scheme.Modules` and `IsFlatOverAt`, and concludes projectivity of
`Γ(V.scheme, ⊤)`-sections;  05FP is
`AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_etale`, about
`Stacks.Divisors.IsWeaklyAssociatedPoint` of a quasi-coherent `Scheme.Modules`.  Nothing in
`StacksDraft.RingTheory` states either one for `Algebra R S`, `Module.Flat R N` and
`IsWeaklyAssociatedPrime`, so neither can be applied here without first building the affine
translation:  `Module.Flat R N` to `IsFlatOverAt`, the global sections of an affine elementary
étale neighbourhood to an étale `R`-algebra, the distinguished points to primes lying over `𝔭`
and `𝔮`, and `Γ((Scheme.Modules.pullback U.toBase).obj N^~, ⊤)` to the base change `S' ⊗_S N`
carrying the `Γ(V.scheme, ⊤)`-action of the conclusion.  That translation is a substantial piece
of work in its own right and is not carried out here.

Granted those two ring-theoretic forms, the rest is short.  For the base clause:  with `N ⊗_S S'`
projective over the étale `R'`, hence free over `R'_{𝔭'}` by [Stacks, Tag 0593], the witness lies
in a finite free summand and one of its finitely many `M'`-coordinates is a witness outright, so
no prime avoidance — and therefore no finiteness of `𝔭` — is needed;  the finiteness-free content
available here, `exists_smul_pow_eq_zero_localizedModule_of_tensorProduct`, only covers `𝔭 R_𝔭`
by the primes weakly associated to `M_𝔭`, and finitely many generators of `𝔭` are what turn that
covering into a single witness.  For `⟸`:  over a local base, with `N` projective over `R` and
`𝔮-bar` maximal among the associated primes of the fibre, it is
`isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre` of
`Stacks.WeaklyAssociatedPrimes`, and the ring-theoretic 05ID is exactly what removes the first
two of those three hypotheses.

The fibre clause `isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct` is free
of all of this:  it assumes nothing beyond the tag's own hypotheses.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 0547](https://stacks.math.columbia.edu/tag/0547)
* [Stacks Project, Tag 05C9](https://stacks.math.columbia.edu/tag/05C9)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
-/

@[expose] public section

open TensorProduct

universe u v w t

namespace Stacks.WeaklyAssociatedPrimes

open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Transport of the two predicates -/

section Transport

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]
  {X : Type*} [AddCommGroup X] [Module A X] {Y : Type*} [AddCommGroup Y] [Module B Y]

/-- Weak association of a prime to a module only depends on the module up to isomorphism. -/
theorem isWeaklyAssociatedPrime_of_linearEquiv' {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (e : X ≃ₗ[A] Y) {J : Ideal A}
    (h : IsWeaklyAssociatedPrime A X J) : IsWeaklyAssociatedPrime A Y J := by
  obtain ⟨x, hx⟩ := h
  refine ⟨e x, ?_⟩
  have hann : (A ∙ e x).annihilator = (A ∙ x).annihilator := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton, ← e.map_smul,
      map_eq_zero_iff _ e.injective]
  rwa [hann]

/-- Association of a prime, in the strict sense of [Stacks, Tag 00LA], transports along a ring
isomorphism together with a compatible additive isomorphism of modules. -/
theorem isAssociatedPrimeStacks_of_semilinearEquiv (e : A ≃+* B) (φ : X ≃+ Y)
    (hφ : ∀ (a : A) (x : X), φ (a • x) = e a • φ x) {J : Ideal A}
    (h : IsAssociatedPrimeStacks A X J) : IsAssociatedPrimeStacks B Y (J.map e) := by
  obtain ⟨hJ, x, hx⟩ := h
  refine ⟨Ideal.map_isPrime_of_equiv e, φ x, ?_⟩
  rw [← hx]
  ext b
  simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot, Ideal.mem_map_iff_of_surjective
    _ e.surjective]
  constructor
  · intro hb
    refine ⟨e.symm b, φ.injective ?_, by simp⟩
    rw [hφ, map_zero, e.apply_symm_apply, hb]
  · rintro ⟨a, ha, rfl⟩
    rw [← hφ, ha, map_zero]

/-- Association of a prime, in the strict sense of [Stacks, Tag 00LA], only depends on the
module up to isomorphism. -/
theorem isAssociatedPrimeStacks_of_linearEquiv' {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (e : X ≃ₗ[A] Y) {J : Ideal A}
    (h : IsAssociatedPrimeStacks A X J) : IsAssociatedPrimeStacks A Y J := by
  have := isAssociatedPrimeStacks_of_semilinearEquiv (RingEquiv.refl A) e.toAddEquiv
    (fun a x => e.map_smul a x) h
  rwa [show J.map (RingEquiv.refl A) = J from Ideal.map_id J] at this

/-- An ideal contained in an associated prime and annihilating the module may be divided out of
the ring: association in the strict sense of [Stacks, Tag 00LA] passes to the quotient ring. -/
theorem isAssociatedPrimeStacks_quotient (I : Ideal A) {J : Ideal A} (hIJ : I ≤ J)
    (h : IsAssociatedPrimeStacks A X J) [Module (A ⧸ I) X] [IsScalarTower A (A ⧸ I) X] :
    IsAssociatedPrimeStacks (A ⧸ I) X (J.map (Ideal.Quotient.mk I)) := by
  obtain ⟨hJ, x, hx⟩ := h
  refine ⟨Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker]), x, ?_⟩
  ext b
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, Ideal.mem_quotient_iff_mem hIJ,
    ← hx, Submodule.mem_colon_span_singleton, Submodule.mem_bot,
    ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]

/-- An `S`-algebra isomorphism `e : A ≃ₐ[S] B` carries the base change `A ⊗_S X` to `B ⊗_S X`
semilinearly over `e`. -/
theorem tensorCongr_smul {S : Type*} [CommRing S] [Algebra S A] [Algebra S B]
    (e : A ≃ₐ[S] B) {Z : Type*} [AddCommGroup Z] [Module S Z] (a : A) (x : A ⊗[S] Z) :
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S Z) (a • x)
      = e a • TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S Z) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b n =>
    simp only [TensorProduct.smul_tmul', TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
      LinearEquiv.refl_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Association of a prime, in the strict sense of [Stacks, Tag 00LA], transports along an
`S`-algebra isomorphism of the base changes it acts on. -/
theorem isAssociatedPrimeStacks_tensor_of_algEquiv {S : Type*} [CommRing S]
    [Algebra S A] [Algebra S B] (e : A ≃ₐ[S] B) {Z : Type*} [AddCommGroup Z] [Module S Z]
    {J : Ideal A} {J' : Ideal B} (hJ : J.map e.toRingEquiv = J')
    (h : IsAssociatedPrimeStacks A (A ⊗[S] Z) J) :
    IsAssociatedPrimeStacks B (B ⊗[S] Z) J' :=
  hJ ▸ isAssociatedPrimeStacks_of_semilinearEquiv e.toRingEquiv
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S Z)).toAddEquiv
    (tensorCongr_smul e) h

end Transport

/-! ### Weakly associated primes and localization at a submonoid -/

/-- Weak association transfers to a localization at a submonoid disjoint from the prime:  if a
prime `q` of `S` disjoint from `T` is weakly associated to an `S`-module `X`, then `q T⁻¹S` is
weakly associated to `T⁻¹X`.  This is one half of [Stacks, Tag 05C9]. -/
theorem isWeaklyAssociatedPrime_map_localization {S : Type v} [CommRing S]
    {X : Type*} [AddCommGroup X] [Module S X] (T : Submonoid S) {q : Ideal S} [q.IsPrime]
    (hd : Disjoint (T : Set S) (q : Set S)) (h : IsWeaklyAssociatedPrime S X q) :
    IsWeaklyAssociatedPrime (Localization T) (LocalizedModule T X)
      (q.map (algebraMap S (Localization T))) := by
  set P : PrimeSpectrum S := ⟨q, inferInstance⟩ with hP
  have hq : P ∈ weakAss S X := h
  have hrange : P ∈ Set.range (localizationComap T) := by
    rwa [PrimeSpectrum.localization_comap_range (Localization T) T]
  have h2 : P ∈ weakAss S (LocalizedModule T X) :=
    (weakAss_inter_image_eq_weakAss_localizedModule T).subset ⟨hq, hrange⟩
  rw [weakAss_localizedModule_eq_image T] at h2
  obtain ⟨Q, hQ, hQe⟩ := h2
  have hmap : q.map (algebraMap S (Localization T)) = Q.asIdeal := by
    rw [show q = (localizationComap T Q).asIdeal from congrArg PrimeSpectrum.asIdeal hQe.symm]
    exact IsLocalization.map_under T _ Q.asIdeal
  rw [hmap]
  exact hQ

/-! ### The localizations at `𝔭` -/

section AtPrime

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {M : Type t} [AddCommGroup M] [Module R M]

variable (S) in
/-- The image in `S` of the multiplicative set `R ∖ 𝔭`.  Inverting it produces `S_𝔭`, the base
change of `S` to the local ring `R_𝔭`. -/
abbrev primeComplImage (p : Ideal R) [p.IsPrime] : Submonoid S :=
  Algebra.algebraMapSubmonoid S p.primeCompl

variable (p : Ideal R) [p.IsPrime]

/-- The `R_𝔭`-module structure on `S_𝔭 ⊗_S N`, obtained by restriction of scalars along
`R_𝔭 → S_𝔭`. -/
noncomputable local instance moduleLocalizationLocalizedModule :
    Module (Localization p.primeCompl) (LocalizedModule (primeComplImage S p) N) :=
  Module.compHom _ (algebraMap (Localization p.primeCompl)
    (Localization (primeComplImage S p)))

/-- The scalar actions of `R_𝔭` and `S_𝔭` on `S_𝔭 ⊗_S N` form a scalar tower. -/
local instance isScalarTowerLocalizationLocalizedModule :
    IsScalarTower (Localization p.primeCompl) (Localization (primeComplImage S p))
      (LocalizedModule (primeComplImage S p) N) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The scalar actions of `R` and `R_𝔭` on `S_𝔭 ⊗_S N` form a scalar tower. -/
local instance isScalarTowerBaseLocalizationLocalizedModule :
    IsScalarTower R (Localization p.primeCompl) (LocalizedModule (primeComplImage S p) N) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change (algebraMap (Localization p.primeCompl) (Localization (primeComplImage S p)))
      (algebraMap R (Localization p.primeCompl) r) • x = r • x
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S _,
      algebraMap_smul, algebraMap_smul]

/-- Flatness of `N` over `R` gives flatness of `S_𝔭 ⊗_S N` over the local ring `R_𝔭`. -/
local instance flatLocalizationLocalizedModule [Module.Flat R N] :
    Module.Flat (Localization p.primeCompl) (LocalizedModule (primeComplImage S p) N) := by
  have h : Module.Flat R (LocalizedModule (primeComplImage S p) N) :=
    Module.Flat.of_isLocalizedModule_tower (primeComplImage S p)
      (LocalizedModule.mkLinearMap (primeComplImage S p) N)
  exact (Module.flat_iff_of_isLocalization (Localization p.primeCompl) p.primeCompl _).mpr h

variable (N M) in
/-- `(S_𝔭 ⊗_S N) ⊗_{R_𝔭} M_𝔭` is `S_𝔭 ⊗_S (N ⊗_R M)`:  the base change of `M` to `R_𝔭` may be
cancelled against the `R_𝔭`-module structure of the left factor. -/
noncomputable def cancelBaseChangeLocalization :
    (LocalizedModule (primeComplImage S p) N) ⊗[Localization p.primeCompl]
        (Localization p.primeCompl ⊗[R] M) ≃ₗ[Localization (primeComplImage S p)]
      (LocalizedModule (primeComplImage S p) N) ⊗[R] M :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization p.primeCompl)
    (Localization (primeComplImage S p)) (LocalizedModule (primeComplImage S p) N) M

/-- The closed fibre of `R_𝔭 → S_𝔭` is the fibre ring `S ⊗_R κ(𝔭)` of `𝔭`, which is of finite
presentation over the field `κ(𝔭)` and therefore Noetherian. -/
local instance isNoetherianRing_quotient_maximalIdeal_localization
    [Algebra.FinitePresentation R S] :
    IsNoetherianRing (Localization (primeComplImage S p) ⧸
      Ideal.map (algebraMap (Localization p.primeCompl) (Localization (primeComplImage S p)))
        (maximalIdeal (Localization p.primeCompl))) := by
  have : Algebra.FinitePresentation p.ResidueField (p.Fiber S) :=
    Algebra.FinitePresentation.baseChange _
  have : IsNoetherianRing (p.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.ResidueField (p.Fiber S)
  exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivQuotient p).toRingEquiv

/-- **`R_𝔭 → S_𝔭` is essentially of finite presentation.**  The ring `S_𝔭` is a localization of
the base change `R_𝔭 ⊗_R S`, which is of finite presentation over `R_𝔭`. -/
theorem essentiallyOfFinitePresentation_localization [Algebra.FinitePresentation R S] :
    (algebraMap (Localization p.primeCompl)
      (Localization (primeComplImage S p))).EssentiallyOfFinitePresentation := by
  have : IsLocalization (primeComplImage S p) (Localization p.primeCompl ⊗[R] S) :=
    IsLocalization.tensorRight _ p.primeCompl
  let φ : Localization p.primeCompl ⊗[R] S →ₐ[Localization p.primeCompl]
      Localization (primeComplImage S p) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom R S (Localization (primeComplImage S p)))
      fun _ _ => Commute.all _ _
  let _ : Algebra (Localization p.primeCompl ⊗[R] S) (Localization (primeComplImage S p)) :=
    φ.toRingHom.toAlgebra
  have htow : IsScalarTower S (Localization p.primeCompl ⊗[R] S)
      (Localization (primeComplImage S p)) :=
    IsScalarTower.of_algebraMap_eq fun s => by
      change _ = φ (1 ⊗ₜ s)
      simp [φ]
  have : IsScalarTower (Localization p.primeCompl) (Localization p.primeCompl ⊗[R] S)
      (Localization (primeComplImage S p)) :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : Algebra.FinitePresentation (Localization p.primeCompl)
      (Localization p.primeCompl ⊗[R] S) := Algebra.FinitePresentation.baseChange _
  have := IsLocalization.isLocalization_of_submonoid_le (Localization p.primeCompl ⊗[R] S)
    (Localization (primeComplImage S p)) (primeComplImage S p) (primeComplImage S p) le_rfl
  exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization
    (C := Localization p.primeCompl ⊗[R] S)
    ((primeComplImage S p).map (algebraMap S (Localization p.primeCompl ⊗[R] S)))

variable (S) in
/-- The ideal `𝔭 S_𝔭` of `S_𝔭`, whose quotient is the fibre ring `S ⊗_R κ(𝔭)`. -/
noncomputable def fibreIdeal (p : Ideal R) [p.IsPrime] :
    Ideal (Localization (primeComplImage S p)) :=
  Ideal.map (algebraMap (Localization p.primeCompl) (Localization (primeComplImage S p)))
    (maximalIdeal (Localization p.primeCompl))

/-- A prime of `S` lying over `𝔭` extends to a prime of `S_𝔭` containing `𝔭 S_𝔭`. -/
theorem fibreIdeal_le_map (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    fibreIdeal S p ≤ q.map (algebraMap S (Localization (primeComplImage S p))) := by
  rw [fibreIdeal, ← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization p.primeCompl),
    Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S
      (Localization (primeComplImage S p)), ← Ideal.map_map]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr (q.over_def p).le)

/-- The fibre clause at `𝔭`, read inside `S_𝔭`:  the prime `𝔮 S_𝔭` contains `𝔭 S_𝔭` and is
associated, in the strict sense of [Stacks, Tag 00LA], to `(S_𝔭 ⊗_S N) / 𝔭 (S_𝔭 ⊗_S N)`. -/
theorem isAssociatedPrimeStacks_fibreIdeal_of_isWeaklyAssociatedPrime_tensorProduct
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N] [Module.Flat R N]
    {q : Ideal S} [q.IsPrime] [q.LiesOver p]
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsAssociatedPrimeStacks (Localization (primeComplImage S p))
      (LocalizedModule (primeComplImage S p) N ⧸
        (fibreIdeal S p • (⊤ : Submodule (Localization (primeComplImage S p))
          (LocalizedModule (primeComplImage S p) N))))
      (q.map (algebraMap S (Localization (primeComplImage S p)))) := by
  have hdisj : Disjoint ((primeComplImage S p : Submonoid S) : Set S) (q : Set S) :=
    Ideal.disjoint_primeCompl_of_liesOver q p
  have hprime : (q.map (algebraMap S (Localization (primeComplImage S p)))).IsPrime :=
    IsLocalization.AtPrime.isPrime_map_of_liesOver S p
      (Localization (primeComplImage S p)) q
  have hle := fibreIdeal_le_map p q
  -- the localization of `N ⊗_R M` at the image of `R ∖ 𝔭`
  have e1 : LocalizedModule (primeComplImage S p) (N ⊗[R] M)
      ≃ₗ[Localization (primeComplImage S p)]
      (LocalizedModule (primeComplImage S p) N) ⊗[R] M :=
    (IsLocalizedModule.linearEquiv (primeComplImage S p)
      (LocalizedModule.mkLinearMap (primeComplImage S p) (N ⊗[R] M))
      (TensorProduct.AlgebraTensorModule.rTensor R M
        (LocalizedModule.mkLinearMap (primeComplImage S p) N))).extendScalarsOfIsLocalization
          (primeComplImage S p) (Localization (primeComplImage S p))
  have h2 : IsWeaklyAssociatedPrime (Localization (primeComplImage S p))
      ((LocalizedModule (primeComplImage S p) N) ⊗[Localization p.primeCompl]
        (Localization p.primeCompl ⊗[R] M))
      (q.map (algebraMap S (Localization (primeComplImage S p)))) :=
    isWeaklyAssociatedPrime_of_linearEquiv' (cancelBaseChangeLocalization N M p).symm
      (isWeaklyAssociatedPrime_of_linearEquiv' e1
        (isWeaklyAssociatedPrime_map_localization _ hdisj hq))
  exact isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct
    (essentiallyOfFinitePresentation_localization p) hle h2

/-- **The fibre ring `S ⊗_R κ(𝔭)` is `S_𝔭 / 𝔭 S_𝔭`**, as `S`-algebras.  This is Mathlib's
`Ideal.Fiber.algEquivQuotient`, with the type spelled out. -/
noncomputable def fibreAlgEquiv :
    p.Fiber S ≃ₐ[S] (Localization (primeComplImage S p) ⧸ fibreIdeal S p) :=
  Ideal.Fiber.algEquivQuotient p

variable (N) in
/-- The fibre module `(S_𝔭 / 𝔭S_𝔭) ⊗_S N` is `N_𝔭 / 𝔭 N_𝔭`:  base change along `S → S_𝔭` followed
by the quotient by `𝔭S_𝔭`. -/
noncomputable def fibreQuotLinearEquiv :
    ((Localization (primeComplImage S p) ⧸ fibreIdeal S p) ⊗[S] N)
      ≃ₗ[Localization (primeComplImage S p) ⧸ fibreIdeal S p]
      (LocalizedModule (primeComplImage S p) N ⧸
        (fibreIdeal S p • (⊤ : Submodule (Localization (primeComplImage S p))
          (LocalizedModule (primeComplImage S p) N)))) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization (primeComplImage S p))
      (Localization (primeComplImage S p) ⧸ fibreIdeal S p)
      (Localization (primeComplImage S p) ⧸ fibreIdeal S p) N).symm ≪≫ₗ
    ((TensorProduct.congr (LinearEquiv.refl (Localization (primeComplImage S p)) _)
        ((isLocalizedModule_iff_isBaseChange (primeComplImage S p)
            (Localization (primeComplImage S p))
            (LocalizedModule.mkLinearMap (primeComplImage S p) N)).mp
          inferInstance).equiv).extendScalarsOfSurjective Ideal.Quotient.mk_surjective) ≪≫ₗ
    ((TensorProduct.quotTensorEquivQuotSMul (LocalizedModule (primeComplImage S p) N)
      (fibreIdeal S p)).extendScalarsOfSurjective Ideal.Quotient.mk_surjective)

/-- The extension of an ideal of `S` to the fibre ring `S ⊗_R κ(𝔭)` is its extension to
`S_𝔭 / 𝔭 S_𝔭` read through the identification `fibreAlgEquiv`. -/
theorem map_fibreAlgEquiv_symm (q : Ideal S) :
    (((q.map (algebraMap S (Localization (primeComplImage S p)))).map
        (Ideal.Quotient.mk (fibreIdeal S p))).map (fibreAlgEquiv p).symm.toRingEquiv)
      = Ideal.map (algebraMap S (p.Fiber S)) q := by
  change (((q.map (algebraMap S (Localization (primeComplImage S p)))).map
      (Ideal.Quotient.mk (fibreIdeal S p))).map
        (fibreAlgEquiv p).symm.toRingEquiv.toRingHom)
    = Ideal.map (algebraMap S (p.Fiber S)) q
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext s
  rw [RingHom.comp_apply, RingHom.comp_apply,
    show (Ideal.Quotient.mk (fibreIdeal S p))
        (algebraMap S (Localization (primeComplImage S p)) s)
      = algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p) s from
      (IsScalarTower.algebraMap_apply S (Localization (primeComplImage S p))
        (Localization (primeComplImage S p) ⧸ fibreIdeal S p) s).symm]
  exact (fibreAlgEquiv p).symm.commutes s

/-- Extending an ideal of `S` to `S_𝔭` and then reducing modulo `𝔭 S_𝔭` is extending it to
the fibre ring `S_𝔭 / 𝔭 S_𝔭` in one step. -/
theorem map_mk_map_algebraMap (q : Ideal S) :
    (q.map (algebraMap S (Localization (primeComplImage S p)))).map
        (Ideal.Quotient.mk (fibreIdeal S p))
      = Ideal.map (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p)) q := by
  rw [Ideal.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- **The fibre clause of [Stacks, Tag 05IG].**  Let `R → S` be a ring map of finite
presentation, let `N` be an `S`-module of finite presentation which is flat as an `R`-module, let
`M` be an `R`-module, and let `𝔮` be a prime of `S` lying over a prime `𝔭` of `R`.  If `𝔮` is
weakly associated to `N ⊗_R M` over `S`, then `𝔮-bar = 𝔮 S-bar` is an associated prime — in the
strict sense of [Stacks, Tag 00LA] — of the fibre module `N-bar = S-bar ⊗_S N` over the fibre
ring `S-bar`.

The fibre ring is written as `S_𝔭 / 𝔭 S_𝔭`;  that this is the fibre ring `S ⊗_R κ(𝔭)` of the
source is `fibreAlgEquiv`, the fibre module `N-bar` is `N_𝔭 / 𝔭 N_𝔭` by `fibreQuotLinearEquiv`,
and `𝔮-bar` corresponds to `𝔮 (S ⊗_R κ(𝔭))` by `map_fibreAlgEquiv_symm`.

No finiteness hypothesis on `𝔭` or on `WeakAss_R(M)` enters this clause. -/
theorem isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N] [Module.Flat R N]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsAssociatedPrimeStacks (Localization (primeComplImage S p) ⧸ fibreIdeal S p)
      ((Localization (primeComplImage S p) ⧸ fibreIdeal S p) ⊗[S] N)
      (Ideal.map (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p)) q) := by
  have h4 : IsAssociatedPrimeStacks (Localization (primeComplImage S p) ⧸ fibreIdeal S p)
      (LocalizedModule (primeComplImage S p) N ⧸
        (fibreIdeal S p • (⊤ : Submodule (Localization (primeComplImage S p))
          (LocalizedModule (primeComplImage S p) N))))
      ((q.map (algebraMap S (Localization (primeComplImage S p)))).map
        (Ideal.Quotient.mk (fibreIdeal S p))) :=
    isAssociatedPrimeStacks_quotient (fibreIdeal S p) (fibreIdeal_le_map p q)
      (isAssociatedPrimeStacks_fibreIdeal_of_isWeaklyAssociatedPrime_tensorProduct (M := M) p hq)
  rw [← map_mk_map_algebraMap p q]
  exact isAssociatedPrimeStacks_of_linearEquiv' (fibreQuotLinearEquiv N p).symm h4

/-- **[Stacks, Tag 05IG], the implication `⟹`.**  Let `R → S` be a ring map of finite
presentation, let `N` be an `S`-module of finite presentation which is flat as an `R`-module, let
`M` be an `R`-module, and let `𝔮` be a prime of `S` lying over a prime `𝔭` of `R` which is
finitely generated.  If `𝔮` is *weakly* associated to `N ⊗_R M` over `S`, then `𝔭` is *weakly*
associated to `M` over `R` and `𝔮-bar` is an *associated* prime, in the strict sense of
[Stacks, Tag 00LA], of `N-bar` over the fibre ring `S-bar`.

Finite generation of `𝔭` enters the base clause only.  It stands in for the étale-local
structure theorem [Stacks, Tag 05ID], which the source uses to make `N` projective over the base
and which this library has only in scheme-theoretic form;  see the module documentation for what
the ring-theoretic form would need.  With `N` projective over a local base the witness lands in a
finite free summand and no prime avoidance is needed, whereas the finiteness-free content
available here (`exists_smul_pow_eq_zero_localizedModule_of_tensorProduct`) only covers `𝔭 R_𝔭`
by the primes weakly associated to `M_𝔭`, and finitely many generators of `𝔭` are what turn
that covering into a single witness.  The variant
`..._of_tensorProduct_of_finite` trades it for finiteness of `WeakAss_R(M)`, and the fibre clause
`isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct` is free of both.

The converse implication of the tag is not proved here;  see the module documentation. -/
@[stacks 05IG "RESTRICTED: the implication ⟹ only, and its base clause carries the extra \
hypothesis that 𝔭 is finitely generated, which the tag does not have.  That hypothesis stands \
in for the étale-local structure theorem 05ID, proved only scheme-side here"]
theorem isWeaklyAssociatedPrime_and_isAssociatedPrimeStacks_fibre_of_tensorProduct
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N] [Module.Flat R N]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] (hfg : p.FG)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime R M p ∧
      IsAssociatedPrimeStacks (Localization (primeComplImage S p) ⧸ fibreIdeal S p)
        ((Localization (primeComplImage S p) ⧸ fibreIdeal S p) ⊗[S] N)
        (Ideal.map (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p)) q) := by
  refine ⟨?_, isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct p q hq⟩
  have hcomap : q.comap (algebraMap R S) = p := (q.over_def p).symm
  rw [← hcomap] at hfg ⊢
  exact isWeaklyAssociatedPrime_comap_tensorProduct_of_fg hq hfg

/-- **[Stacks, Tag 05IG], the implication `⟹`, with the finiteness taken on `WeakAss_R(M)`.**
The same conclusion as
`isWeaklyAssociatedPrime_and_isAssociatedPrimeStacks_fibre_of_tensorProduct`, with finite
generation of `𝔭` traded for the other hypothesis that makes the prime avoidance in the base
clause run:  finitely many primes weakly associated to `M`.  The two are independent, and
neither follows from the hypotheses of the tag;  both stand in for the ring-theoretic form of
[Stacks, Tag 05ID] discussed in the module documentation.  No attribute is attached here, the
tag being carried by the finitely generated form. -/
theorem isWeaklyAssociatedPrime_and_isAssociatedPrimeStacks_fibre_of_tensorProduct_of_finite
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N] [Module.Flat R N]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] (hfin : (weaklyAssociatedPrimes R M).Finite)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime R M p ∧
      IsAssociatedPrimeStacks (Localization (primeComplImage S p) ⧸ fibreIdeal S p)
        ((Localization (primeComplImage S p) ⧸ fibreIdeal S p) ⊗[S] N)
        (Ideal.map (algebraMap S (Localization (primeComplImage S p) ⧸ fibreIdeal S p)) q) := by
  refine ⟨?_, isAssociatedPrimeStacks_fibre_of_isWeaklyAssociatedPrime_tensorProduct p q hq⟩
  have hcomap : q.comap (algebraMap R S) = p := (q.over_def p).symm
  rw [← hcomap]
  exact isWeaklyAssociatedPrime_comap_tensorProduct hfin hq

end AtPrime

end Stacks.WeaklyAssociatedPrimes

end
