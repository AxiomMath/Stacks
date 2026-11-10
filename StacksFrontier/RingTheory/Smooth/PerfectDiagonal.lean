module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.Algebra.Homology.ProjectiveDimension
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.FiniteResolution
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.RingTheory.DividedPowers.Rodicio.GulliksenObstruction
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.Defs
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksFrontier.RingTheory.PseudoCoherentMap.Noetherian
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
public import StacksFrontier.RingTheory.Smooth.LocalizationOfSmooth
public import StacksFrontier.RingTheory.Smooth.NaiveCotangentCriterion
public import StacksFrontier.RingTheory.Smooth.SmoothAt

import StacksCore.Tactic.StacksAttribute

/-!
# Smooth ring maps and perfect diagonals

A ring map `A → B` is smooth exactly when its diagonal is perfect. This file proves the two
implications of that characterisation which rest on Rodicio's theorem: the local statement
Stacks 0FCW, that a flat local homomorphism of Noetherian local rings which is essentially of
finite type and has perfect diagonal is a localization of a smooth algebra, and its global
counterpart Stacks 0FCX, that a flat finite type map of Noetherian rings with perfect diagonal
is smooth. Both are proved from the weaker hypothesis that `B` has finite projective dimension
over `B ⊗[A] B`, which mentions no derived category.

## Main results

* `StacksDraft.Smooth.formallySmooth_of_hasProjectiveDimensionLT_diagonal`: for a flat map
  `A → B`, essentially of finite type, from a Noetherian ring to a local ring, finite projective
  dimension of `B` over `B ⊗[A] B` forces formal smoothness. This is the whole content of
  Stacks 0FCW.
* `StacksDraft.Smooth.exists_smooth_isLocalization_of_hasProjectiveDimensionLT_diagonal`:
  Stacks 0FCW.
* `StacksDraft.Smooth.smooth_of_flat_of_hasProjectiveDimensionLT_diagonal`: Stacks 0FCX.
* `StacksDraft.Smooth.formallySmooth_of_isPerfect_diagonal`,
  `StacksDraft.Smooth.exists_smooth_isLocalization_of_isPerfect_diagonal` and
  `StacksDraft.Smooth.smooth_of_flat_of_isPerfect_diagonal`: the same three statements with the
  source's hypothesis, a perfect diagonal.

## Implementation notes

The argument uses the diagonal only through finite projective dimension of `B` over
`B ⊗[A] B`, with the algebra structure on `B` over `B ⊗[A] B` induced by the multiplication map
`Algebra.TensorProduct.lmul'`. That condition mentions no derived category, so the main
statements take it as their hypothesis, and the tags 0FCW and 0FCX sit on those forms.

The source's hypothesis, a perfect diagonal, is `RingHom.IsPerfectRingMap` read at a model of
`D(B ⊗[A] B)` through a certified derived tensoring
`StacksDraft.TorAmplitude.CertifiedDerivedTensoring (B ⊗[A] B)`; by
`RingHom.isPerfectRingMap_iff_exists_flat_roof` it depends neither on the model nor on the
certificate. It implies finite projective dimension (`exists_hasProjectiveDimensionLT_diagonal`):
since `B ⊗[A] B` is Noetherian and `B` is a finite module over it, `B` is pseudo-coherent there
(Stacks 066E), a bounded complex of flat modules joined to `B[0]` by a roof of
quasi-isomorphisms makes it perfect (Stacks 0657), and a perfect module has a finite resolution
by finite projective modules. That step reads `D(B ⊗[A] B)` in the standard model inside a proof
whose statement mentions no derived category. The theorems with a perfect diagonal as hypothesis
are corollaries of the model-free ones.

The source argues with a presentation `B = R/K`, with `R` a localization of `A[x_1, …, x_n]`,
and runs Rodicio's theorem (Stacks 09PV) on the pair of ideals `I ⊆ J` of `(R ⊗_A R)_𝔪`
cutting out `B ⊗_A B` and `B`; it then identifies the matrix `(a_{ij})` relating
`f_i ⊗ 1 - 1 ⊗ f_i` to the `x_j ⊗ 1 - 1 ⊗ x_j` with the Jacobian matrix and concludes by a rank
count. The formalization replaces the rank count by its consequence: the injectivity supplied by
Rodicio's theorem is transported along the comparison map from `I` to
`κ ⊗_R K`, which says exactly that the cotangent complex of the presentation is injective after
base change to the residue field of `B`, and that is formal smoothness by
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`
(Stacks 07BU's infinitesimal form). The passage from formal smoothness back to "localization of
a smooth algebra" is `StacksDraft.Smooth.exists_smooth_isLocalization_of_formallySmooth`, and
the two are equivalent, so nothing is lost by pivoting through formal smoothness.

Stacks 0FCX is deduced from Stacks 0FCW rather than reproved: smoothness is checked at every
prime `q` of `B` by `Algebra.smooth_iff_forall_exists_notMem_smooth`, and the hypothesis on the
diagonal localizes because `C ⊗_{A_p} C` is a localization of `B ⊗_A B` — this is
`diagonal_isLocalization_of_isLocalization` below, which factors the two-variable localization
one variable at a time — and finite projective dimension of the diagonal passes to that
localization (`exists_hasProjectiveDimensionLT_diagonal_of_isLocalization`).

## References

* [Stacks Project, Tag 0FCW](https://stacks.math.columbia.edu/tag/0FCW)
* [Stacks Project, Tag 0FCX](https://stacks.math.columbia.edu/tag/0FCX)
-/

@[expose] public section

universe u v w

namespace StacksDraft.Smooth

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

/-! ### The local statement, Stacks 0FCW -/

/-- Over a quotient `κ` of `P`, every element of `κ ⊗[P] N` is of the form `1 ⊗ x`: the first
tensor factor can always be cleared into the second. -/
private theorem exists_eq_one_tmul
    (P : Type u) (κ : Type v) [CommRing P] [CommRing κ] [Algebra P κ]
    (hsurj : Function.Surjective (algebraMap P κ))
    (N : Type w) [AddCommGroup N] [Module P N] (y : κ ⊗[P] N) :
    ∃ x : N, y = (1 : κ) ⊗ₜ[P] x := by
  induction y using TensorProduct.inductionOn with
  | tmul c x =>
    obtain ⟨a, rfl⟩ := hsurj c
    exact ⟨a • x, by rw [← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]⟩
  | add y y' hy hy' =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨x', rfl⟩ := hy'
    exact ⟨x + x', (TensorProduct.tmul_add (1 : κ) x x').symm⟩

/-- Over a quotient `κ` of `P`, the element `1 ⊗ x` of `κ ⊗[P] N` vanishes exactly when `x` lies
in `𝔞 N`, for `𝔞` the kernel of `P → κ`. This is the Nakayama bookkeeping that the source's
argument runs on both `K` and `Ω[P⁄A]`. -/
private theorem one_tmul_eq_zero_iff_mem_ker_smul_top
    (P : Type u) (κ : Type v) [CommRing P] [CommRing κ] [Algebra P κ]
    (hsurj : Function.Surjective (algebraMap P κ))
    (N : Type w) [AddCommGroup N] [Module P N] (x : N) :
    (1 : κ) ⊗ₜ[P] x = 0 ↔ x ∈ RingHom.ker (algebraMap P κ) • (⊤ : Submodule P N) := by
  let a : Ideal P := RingHom.ker (algebraMap P κ)
  let eκ := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P κ) hsurj
  have heκone : eκ.symm (1 : κ) = Ideal.Quotient.mk a (1 : P) := by
    rw [show (1 : κ) = (Algebra.ofId P κ) (1 : P) by simp]
    exact Ideal.quotientKerAlgEquivOfSurjective_symm_apply (f := Algebra.ofId P κ) hsurj (1 : P)
  let e : κ ⊗[P] N ≃ₗ[P] N ⧸ (a • (⊤ : Submodule P N)) :=
    (TensorProduct.congr eκ.symm.toLinearEquiv (LinearEquiv.refl P N)).trans
      (TensorProduct.quotTensorEquivQuotSMul N a)
  have he (y : N) : e (1 ⊗ₜ[P] y) = Submodule.Quotient.mk y := by
    change TensorProduct.quotTensorEquivQuotSMul N a (eκ.symm (1 : κ) ⊗ₜ[P] y) = _
    rw [heκone]
    exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ _
  rw [← e.map_eq_zero_iff, he, Submodule.Quotient.mk_eq_zero]

/-- **Nakayama for the diagonal ideal.** Let `P` be a local `A`-algebra and `H ⊆ P ⊗[A] P` the
ideal of the diagonal. If `dk` lies in `𝔪_P Ω[P⁄A]`, then the element `1 ⊗ k - k ⊗ 1` of `H`
lies in `𝔪_P H + H²` already, where `𝔪_P` acts through the left tensor factor.

This is the step the source performs when it writes `f_i ⊗ 1 - 1 ⊗ f_i` as a combination of the
`x_j ⊗ 1 - 1 ⊗ x_j` with coefficients reducing to the partial derivatives: the conclusion drawn
there is exactly that the relation is a combination with coefficients in the maximal ideal. -/
private theorem one_tmul_sub_tmul_one_mem_maximalIdeal_mul_add_sq
    (A : Type u) (P : Type v) [CommRing A] [CommRing P] [IsLocalRing P] [Algebra A P] (k : P)
    (hDk : KaehlerDifferential.D A P k ∈
      IsLocalRing.maximalIdeal P • (⊤ : Submodule P Ω[P⁄A])) :
    (1 : P) ⊗ₜ[A] k - k ⊗ₜ[A] (1 : P) ∈
      Ideal.map (Algebra.TensorProduct.includeLeft
          (R := A) (S := A) (A := P) (B := P)).toRingHom (IsLocalRing.maximalIdeal P) *
        KaehlerDifferential.ideal A P + KaehlerDifferential.ideal A P ^ 2 := by
  let H : Ideal (TensorProduct A P P) := KaehlerDifferential.ideal A P
  let l : P →ₐ[A] TensorProduct A P P := Algebra.TensorProduct.includeLeft
  let mR : Ideal (TensorProduct A P P) := Ideal.map l.toRingHom (IsLocalRing.maximalIdeal P)
  let δ : TensorProduct A P P := (1 : P) ⊗ₜ[A] k - k ⊗ₜ[A] (1 : P)
  have hδH : δ ∈ H := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A k
  have hδcot : H.toCotangent ⟨δ, hδH⟩ ∈
      IsLocalRing.maximalIdeal P • (⊤ : Submodule P H.Cotangent) := by
    rw [show H.toCotangent ⟨δ, hδH⟩ = KaehlerDifferential.D A P k from
      (KaehlerDifferential.D_apply A P k).symm]
    exact Submodule.smul_le.mpr
      (fun r hr x _ => Submodule.smul_mem_smul hr Submodule.mem_top) hDk
  let fH : H →ₗ[P] H.Cotangent := H.toCotangent.restrictScalars P
  have hfHsurj : Function.Surjective fH := H.toCotangent_surjective
  have hmapH : (IsLocalRing.maximalIdeal P • (⊤ : Submodule P H)).map fH =
      IsLocalRing.maximalIdeal P • (⊤ : Submodule P H.Cotangent) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hfHsurj]
  obtain ⟨x, hx, hxf⟩ := Submodule.mem_map.mp (hmapH ▸ hδcot)
  have hxsub : (x : TensorProduct A P P) - δ ∈ H ^ 2 := (H.toCotangent_eq).mp hxf
  have hxmul : (x : TensorProduct A P P) ∈ mR * H := by
    refine Submodule.smul_induction_on hx (fun a ha y hy => ?_)
      fun y z hy hz => (mR * H).add_mem hy hz
    have hmul : algebraMap P (TensorProduct A P P) a * (y : TensorProduct A P P) ∈ mR * H := by
      rw [show algebraMap P (TensorProduct A P P) = l.toRingHom from rfl]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem l.toRingHom ha) y.2
    simpa only [Submodule.coe_smul_of_tower, Algebra.smul_def] using hmul
  change δ ∈ (mR * H : Submodule (TensorProduct A P P) (TensorProduct A P P)) ⊔
    (H ^ 2 : Submodule (TensorProduct A P P) (TensorProduct A P P))
  convert Submodule.add_mem_sup hxmul ((H ^ 2).neg_mem hxsub) using 1; abel

/-- A local algebra essentially of finite type is the localization of its finite type subalgebra
at the contraction of the maximal ideal: the denominators allowed by essential finite type are
units of the local ring, hence avoid the contracted maximal ideal, and conversely. -/
private theorem isLocalization_essFiniteType_subalgebra
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [Algebra.EssFiniteType A B] :
    letI C := Algebra.EssFiniteType.subalgebra A B
    IsLocalization ((IsLocalRing.maximalIdeal B).comap (algebraMap C B)).primeCompl B := by
  let C := Algebra.EssFiniteType.subalgebra A B
  let p : Ideal C := (IsLocalRing.maximalIdeal B).comap C.val.toRingHom
  let : IsLocalization (Algebra.EssFiniteType.submonoid A B) B :=
    Algebra.EssFiniteType.isLocalization A B
  refine IsLocalization.of_le (Algebra.EssFiniteType.submonoid A B) p.primeCompl
    (fun x hx => IsLocalRing.notMem_maximalIdeal.mpr hx) fun x hx =>
      IsLocalRing.notMem_maximalIdeal.mp ?_
  rwa [Ideal.mem_primeCompl_iff] at hx

/-- A local algebra essentially of finite type is a quotient of a localization of a polynomial
ring in finitely many variables at a prime ideal. This is the presentation `B = R/K` with
`R = A[x_1, …, x_n]_q` from which the source's argument starts. -/
@[ega "IV 1.3.11"]
private theorem exists_localization_mvPolynomial_surjective
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) A)) (_ : q.IsPrime)
      (g : Localization.AtPrime q →ₐ[A] B), Function.Surjective g := by
  classical
  let C := Algebra.EssFiniteType.subalgebra A B
  let p : Ideal C := (IsLocalRing.maximalIdeal B).comap (algebraMap C B)
  have : p.IsPrime := Ideal.IsPrime.comap _
  let : IsLocalization p.primeCompl B := isLocalization_essFiniteType_subalgebra A B
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := C)).mp inferInstance
  let q : Ideal (MvPolynomial (Fin n) A) := p.comap f.toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  have hmap : Submonoid.map f.toRingHom q.primeCompl = p.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective f.toRingHom hf p
  have : IsLocalization (Submonoid.map f.toRingHom q.primeCompl) (Localization.AtPrime p) := by
    rw [hmap]; infer_instance
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) B
  refine ⟨n, q, inferInstance,
    (e.restrictScalars A).toAlgHom.comp (Localization.localAlgHom q p f rfl), ?_⟩
  exact e.surjective.comp
    (IsLocalization.map_surjective_of_surjective (M := q.primeCompl)
      (S := Localization.AtPrime q) (g := f.toRingHom) (Localization.AtPrime p) hf)

/-- Restriction of scalars on endomorphisms, as a ring homomorphism. Used to transport
invertibility of multiplication by a denominator from the larger ring of scalars to the smaller
one, which is what universality of a localized module asks for. -/
private def restrictScalarsEndRingHom
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [AddCommMonoid M]
    [Module S M] [SMul R S] [Module R M] [IsScalarTower R S M] :
    Module.End S M →+* Module.End R M where
  toFun f := f.restrictScalars R
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl
  map_zero' := by ext x; rfl
  map_add' f g := by ext x; rfl

/-- The kernel of a composite `g ∘ f` maps `R`-linearly to the kernel of `g` along `f`, once the
`R`-module structure on `RingHom.ker g` is the one induced by `f`. -/
private theorem exists_kerMap_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T)
    (hcomp : g.comp f = h) [Module R (RingHom.ker g)]
    (hsmul : ∀ (r : R) (x : RingHom.ker g), (r • x : RingHom.ker g).1 = f r * x.1) :
    ∃ l : RingHom.ker h →ₗ[R] RingHom.ker g, ∀ x, (l x).1 = f x.1 := by
  have hmem : ∀ x : RingHom.ker h, f x.1 ∈ RingHom.ker g := fun x => by
    apply RingHom.mem_ker.mpr
    have hx := congrArg (fun k : R →+* T => k x.1) hcomp
    change g (f x.1) = h x.1 at hx
    rw [RingHom.mem_ker.mp x.property] at hx
    exact hx
  refine ⟨{ toFun x := ⟨f x.1, hmem x⟩
            map_add' x y := Subtype.ext (map_add f x.1 y.1)
            map_smul' r x := Subtype.ext ?_ }, fun x => rfl⟩
  calc f (r • x.1) = f (r * x.1) := rfl
    _ = f r * f x.1 := map_mul f r x.1
    _ = (r • (⟨f x.1, hmem x⟩ : RingHom.ker g)).1 := (hsmul r ⟨f x.1, hmem x⟩).symm

/-- A module of finite projective dimension stays of finite projective dimension after
localization. -/
private theorem exists_hasProjectiveDimensionLT_localizedModule
    (R : Type u) [CommRing R] (S : Submonoid R) (M : ModuleCat.{u} R)
    (h : ∃ n : ℕ, HasProjectiveDimensionLT M n) :
    ∃ n : ℕ, HasProjectiveDimensionLT (M.localizedModule S) n := by
  obtain ⟨n, hn⟩ := h
  let : HasProjectiveDimensionLT M n := hn
  let : HasProjectiveDimensionLE M n :=
    hasProjectiveDimensionLT_of_ge M n (n + 1) (by omega)
  exact ⟨n + 1, ModuleCat.localizedModule_hasProjectiveDimensionLE n S M⟩

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- **Finite projective dimension localizes**, over any localization `Rₛ` of `R` at `S`: if `M` has
finite projective dimension over `R`, then a localization `N` of `M` at `S` has finite projective
dimension over `Rₛ`. Mathlib's
`ModuleCat.localizedModule_hasProjectiveDimensionLE` gives this for `Localization S`, and the
canonical isomorphism `Localization S ≃ₐ[R] Rₛ` carries it across
(`ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv`). -/
private theorem exists_hasProjectiveDimensionLT_of_isLocalization
    {R : Type v} [CommRing R] (S : Submonoid R) (Rₛ : Type v) [CommRing Rₛ] [Algebra R Rₛ]
    [IsLocalization S Rₛ] (M : ModuleCat.{v} R) (N : Type v) [AddCommGroup N] [Module R N]
    [Module Rₛ N] [IsScalarTower R Rₛ N] (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (h : ∃ n : ℕ, HasProjectiveDimensionLT M n) :
    ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of Rₛ N) n := by
  obtain ⟨n, hn⟩ := exists_hasProjectiveDimensionLT_localizedModule R S M h
  let e : Localization S ≃ₐ[R] Rₛ := IsLocalization.algEquiv S (Localization S) Rₛ
  let : Module (Localization S) N := Module.compHom N (e : Localization S →+* Rₛ)
  have : IsScalarTower R (Localization S) N := IsScalarTower.of_algebraMap_smul fun r x => by
    change e (algebraMap R (Localization S) r) • x = r • x
    rw [e.commutes]
    exact algebraMap_smul Rₛ r x
  let l : M.localizedModule S ≃ₗ[Localization S] N :=
    LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S) f)
  let l' : M.localizedModule S ≃ₛₗ[RingHomClass.toRingHom e.toRingEquiv] ModuleCat.of Rₛ N :=
    { l.toAddEquiv with map_smul' := fun r x => l.map_smul r x }
  have : HasProjectiveDimensionLE (M.localizedModule S) n :=
    hasProjectiveDimensionLT_of_ge _ n (n + 1) (by omega)
  exact ⟨n + 1, ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e.toRingEquiv l' n⟩

/-- **Finite projective dimension from a bounded flat roof.** Over a Noetherian ring `T`, a finite
module `B` that is joined to `B[0]` by a roof of quasi-isomorphisms from a bounded complex of flat
modules has finite projective dimension: `B[0]` is pseudo-coherent (Stacks 066E) of finite Tor
amplitude, hence perfect (Stacks 0657), hence resolved by a finite complex of finite projective
modules. The statement mentions no derived category; the proof reads it in the standard model. -/
private theorem exists_hasProjectiveDimensionLT_of_exists_flat_roof
    {T : Type v} [CommRing T] [IsNoetherianRing T] (B : Type v) [AddCommGroup B] [Module T B]
    [Module.Finite T B]
    (h : ∃ (a b : ℤ) (E : CochainComplex (ModuleCat.{v} T) ℤ), (∀ i, Module.Flat T (E.X i)) ∧
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
        CochainComplex.QuasiIsoRoof E
          ((CochainComplex.singleFunctor (ModuleCat.{v} T) 0).obj (ModuleCat.of T B))) :
    ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of T B) n := by
  obtain ⟨a, b, E, hflat, hGE, hLE, hroof⟩ := h
  let : HasDerivedCategory (ModuleCat.{v} T) := HasDerivedCategory.standard _
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} T) 0).obj (ModuleCat.of T B)
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
    apply ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      K 0 B).2.1).2
    refine ⟨⟨0, fun i hi => DerivedCategory.isZero_of_isLE _ 0 i (by omega)⟩, fun i => ?_⟩
    by_cases hi : i = 0
    · subst i
      let : Module.Finite T ↑((𝟭 (ModuleCat T)).obj (ModuleCat.of T B)) := ‹Module.Finite T B›
      exact Module.Finite.equiv
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat T) 0).app
          (ModuleCat.of T B)).toLinearEquiv.symm
    · have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj K) := by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ 0 i hi
        · exact DerivedCategory.isZero_of_isLE _ 0 i hi
      let : Subsingleton ↑((DerivedCategory.homologyFunctor (ModuleCat T) i).obj K) :=
        ModuleCat.isZero_iff_subsingleton.mp hzero
      exact Module.Finite.of_finite
  obtain ⟨f⟩ := (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).mp hroof
  have hKperf : StacksDraft.Perfect.IsPerfect K :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).1.mpr
      ⟨hpc, a, b, E, hflat, hGE, hLE,
        ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} T) 0).app (ModuleCat.of T B) ≪≫
          f.symm⟩⟩
  obtain ⟨d, F, hF, hzero⟩ :=
    (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution B).mp
      (hKperf : StacksDraft.Perfect.IsPerfectModule (R := T) B)
  let G : (isProjective (ModuleCat T)).LeftResolution (ModuleCat.of T B) :=
    { complex := F.complex
      property i := by
        let : Module.Projective T (F.complex.X i) := (hF i).2
        exact ModuleCat.projective_of_categoryTheory_projective (F.complex.X i)
      π := F.π
      quasiIso := F.quasiIso }
  have hres : ∃ G : (isProjective (ModuleCat T)).LeftResolution (ModuleCat.of T B),
      ∀ i, d < i → IsZero (G.complex.X i) := ⟨G, hzero⟩
  exact ⟨d + 1, ((CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution
    (ModuleCat.of T B) d).out 2 1).mp hres⟩

/-- A perfect diagonal gives `B` finite projective dimension over `B ⊗[A] B`, for any model of
`D(B ⊗[A] B)` and any certified derived tensor product on it: `B ⊗[A] B` is Noetherian and `B` is
a finite module over it, and perfectness provides a bounded complex of flat modules joined to
`B[0]` by a roof of quasi-isomorphisms (`RingHom.isPerfectRingMap_iff_exists_flat_roof`), so
`exists_hasProjectiveDimensionLT_of_exists_flat_roof` applies. -/
private theorem exists_hasProjectiveDimensionLT_diagonal
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsNoetherianRing B] [Algebra A B]
    [Algebra.EssFiniteType A B]
    [HasDerivedCategory.{w} (ModuleCat.{v} (TensorProduct A B B))]
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring (TensorProduct A B B))
    (hperfect :
      letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      RingHom.IsPerfectRingMap (TensorProduct A B B) B D.tensor D.comparison D.isLeftDerived) :
    letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
    ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (TensorProduct A B B) B) n := by
  let T := TensorProduct A B B
  let : Algebra T B := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
  let : Algebra B T := Algebra.TensorProduct.leftAlgebra
  have : Algebra.EssFiniteType B T :=
    Algebra.EssFiniteType.baseChange (R := A) (S := B) (T := B)
  have : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing B T
  have : Module.Finite T B := by
    apply Module.Finite.of_surjective (Algebra.linearMap T B)
    change Function.Surjective (Algebra.TensorProduct.lmul' (R := A) (S := B))
    exact fun b => ⟨b ⊗ₜ[A] (1 : B), by simp⟩
  exact exists_hasProjectiveDimensionLT_of_exists_flat_roof B
    ((RingHom.isPerfectRingMap_iff_exists_flat_roof _ _).mp hperfect).2

/-- If `B` has finite projective dimension over `B ⊗[A] B`, it has finite projective dimension
over the *local* ring `(B ⊗[A] B)_𝔮`, the localization at the prime `𝔮` pulled back from the
maximal ideal of `B`. The multiplication map factors through that localization because every
element outside `𝔮` becomes a unit of the local ring `B`, and this is the form in which Rodicio's
theorem can be applied. -/
private theorem exists_hasProjectiveDimensionLT_diagonal_localization
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    (hpd : letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (TensorProduct A B B) B) n) :
    letI : Algebra (TensorProduct A B B) B :=
      (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
    let q : Ideal (TensorProduct A B B) := (IsLocalRing.maximalIdeal B).comap
      (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom
    letI : Algebra (Localization q.primeCompl) B :=
      (IsLocalization.lift (M := q.primeCompl)
        (g := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom)
        fun x => IsLocalRing.notMem_maximalIdeal.mp x.2).toAlgebra
    ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (Localization q.primeCompl) B) n := by
  let T := TensorProduct A B B
  let : Algebra T B := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
  let q : Ideal T := (IsLocalRing.maximalIdeal B).comap
    (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom
  let S := q.primeCompl
  have hunit : ∀ x : S, IsUnit ((Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom x.1) :=
    fun x => IsLocalRing.notMem_maximalIdeal.mp x.2
  let liftRing : Localization S →+* B := IsLocalization.lift (M := S)
    (g := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom) hunit
  let : Algebra (Localization S) B := liftRing.toAlgebra
  let : IsScalarTower T (Localization S) B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp (M := S)
      (g := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom) hunit).symm
  let incl : ModuleCat.of T B →ₗ[T] B := LinearMap.id
  have hf : IsLocalizedModule S incl := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      have heq : algebraMap T (Module.End T B) x.1 =
          (Algebra.lsmul T T B) (algebraMap T B x.1) := by
        ext b
        simp
      rw [heq]
      exact (hunit x).map (Algebra.lsmul T T B).toRingHom
    · intro y
      exact ⟨(y, ⟨1, S.one_mem⟩), by simp [incl]⟩
    · intro x y hxy
      exact ⟨⟨1, S.one_mem⟩, by simpa [incl] using hxy⟩
  exact exists_hasProjectiveDimensionLT_of_isLocalization S (Localization S) (ModuleCat.of T B) B
    incl hpd

/-! ### The configuration of a local presentation

Throughout, `A → P → B` with `P → B` surjective and `B` local. The source's argument runs in
the local ring `(P ⊗[A] P)_𝔪`, where `𝔪` is the prime lying under the maximal ideal of `B`, and
compares the two ideals of that ring cutting out `(B ⊗[A] B)_𝔮` and `B`. -/

section LocalPresentation

variable (A : Type u) (B : Type v) (P : Type u)
  [CommRing A] [CommRing B] [CommRing P] [IsLocalRing B]
  [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B]

/-- The map `P ⊗[A] P → B ⊗[A] B` induced by a presentation `P → B`. -/
private def presentationDiagonal : TensorProduct A P P →ₐ[A] TensorProduct A B B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A P B) (IsScalarTower.toAlgHom A P B)

/-- The prime `𝔮` of `B ⊗[A] B` lying under the maximal ideal of `B`. -/
private def diagonalPrime : Ideal (TensorProduct A B B) :=
  (IsLocalRing.maximalIdeal B).comap (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom

private instance diagonalPrime_isPrime : (diagonalPrime A B).IsPrime := Ideal.IsPrime.comap _

/-- The prime `𝔪` of `P ⊗[A] P` lying under the maximal ideal of `B`. -/
private def presentationPrime : Ideal (TensorProduct A P P) :=
  (diagonalPrime A B).comap (presentationDiagonal A B P).toRingHom

private instance presentationPrime_isPrime : (presentationPrime A B P).IsPrime :=
  Ideal.IsPrime.comap _

/-- The local ring `(B ⊗[A] B)_𝔮`. -/
private abbrev DiagonalLocalization : Type v := Localization.AtPrime (diagonalPrime A B)

/-- The local ring `(P ⊗[A] P)_𝔪`. -/
private abbrev PresentationLocalization : Type u :=
  Localization.AtPrime (presentationPrime A B P)

/-- The multiplication map `(B ⊗[A] B)_𝔮 → B`: every element outside `𝔮` becomes a unit of the
local ring `B`, so the multiplication map factors through the localization. -/
private noncomputable def diagonalMultiplication : DiagonalLocalization A B →ₐ[A] B :=
  IsLocalization.liftAlgHom (M := (diagonalPrime A B).primeCompl)
    (f := Algebra.TensorProduct.lmul' (R := A) (S := B))
    fun x => IsLocalRing.notMem_maximalIdeal.mp x.2

/-- The localized presentation map `(P ⊗[A] P)_𝔪 → (B ⊗[A] B)_𝔮`. -/
private noncomputable def presentationDiagonalLocalized :
    PresentationLocalization A B P →ₐ[A] DiagonalLocalization A B :=
  Localization.localAlgHom (presentationPrime A B P) (diagonalPrime A B)
    (presentationDiagonal A B P) rfl

/-- The composite `(P ⊗[A] P)_𝔪 → B`. -/
private noncomputable def presentationMultiplication :
    PresentationLocalization A B P →ₐ[A] B :=
  (diagonalMultiplication A B).comp (presentationDiagonalLocalized A B P)

/-- The ideal `I` of `(P ⊗[A] P)_𝔪` cutting out `(B ⊗[A] B)_𝔮`. -/
private noncomputable def diagonalIdeal : Ideal (PresentationLocalization A B P) :=
  RingHom.ker (presentationDiagonalLocalized A B P).toRingHom

/-- The ideal `J` of `(P ⊗[A] P)_𝔪` cutting out `B`. -/
private noncomputable def multiplicationIdeal : Ideal (PresentationLocalization A B P) :=
  RingHom.ker (presentationMultiplication A B P).toRingHom

private theorem diagonalIdeal_le_multiplicationIdeal :
    diagonalIdeal A B P ≤ multiplicationIdeal A B P := fun x hx => by
  change diagonalMultiplication A B (presentationDiagonalLocalized A B P x) = 0
  rw [show presentationDiagonalLocalized A B P x = 0 from hx, map_zero]

/-- Injectivity of `I/𝔪I → J/𝔪J`, the conclusion Rodicio's theorem (Stacks 09PV) supplies for
this pair of ideals. -/
private def ConormalInjective : Prop :=
  Function.Injective
    ((IsLocalRing.maximalIdeal (PresentationLocalization A B P) •
        (⊤ : Submodule (PresentationLocalization A B P) (diagonalIdeal A B P))).mapQ
      (IsLocalRing.maximalIdeal (PresentationLocalization A B P) •
        (⊤ : Submodule (PresentationLocalization A B P) (multiplicationIdeal A B P)))
      (Submodule.inclusion (diagonalIdeal_le_multiplicationIdeal A B P))
      (Submodule.smul_top_le_comap_smul_top _ _))

/-- What Rodicio's theorem yields at the relation `1 ⊗ k - k ⊗ 1` attached to an element `k` of
the kernel of `P → B`: that relation, viewed in `I`, is already in `𝔪 I`. -/
private def RelationMemConormal (k : RingHom.ker (algebraMap P B)) : Prop :=
  ∀ y : diagonalIdeal A B P,
    (y : PresentationLocalization A B P) =
      algebraMap (TensorProduct A P P) (PresentationLocalization A B P)
        ((1 : P) ⊗ₜ[A] (k : P) - (k : P) ⊗ₜ[A] (1 : P)) →
    y ∈ IsLocalRing.maximalIdeal (PresentationLocalization A B P) •
      (⊤ : Submodule (PresentationLocalization A B P) (diagonalIdeal A B P))

/-- The map `P ⊗[A] P → κ_B` through which `κ_B ⊗[P] K` is a `P ⊗[A] P`-module. -/
private noncomputable def residueDiagonalRingHom :
    TensorProduct A P P →+* IsLocalRing.ResidueField B :=
  (algebraMap B (IsLocalRing.ResidueField B)).comp
    ((algebraMap P B).comp (Algebra.TensorProduct.lmul' (R := A) (S := P)).toRingHom)

/-- `κ_B ⊗[P] K` as a module over `P ⊗[A] P`, through `residueDiagonalRingHom`. -/
@[instance_reducible]
private noncomputable def residueConormalModule :
    Module (TensorProduct A P P)
      (IsLocalRing.ResidueField B ⊗[P] RingHom.ker (algebraMap P B)) :=
  Module.compHom _ (residueDiagonalRingHom A B P)

omit [IsLocalRing B] in
private theorem lmul'_presentationDiagonal (z : TensorProduct A P P) :
    (Algebra.TensorProduct.lmul' (R := A) (S := B)) (presentationDiagonal A B P z) =
      algebraMap P B ((Algebra.TensorProduct.lmul' (R := A) (S := P)) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact (map_mul (algebraMap P B) a b).symm
  | add z z' hz hz' => simp [hz, hz']

private theorem residueDiagonalRingHom_eq :
    residueDiagonalRingHom A B P = (algebraMap B (IsLocalRing.ResidueField B)).comp
      ((Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.comp
        (presentationDiagonal A B P).toRingHom) :=
  RingHom.ext fun z => congrArg (algebraMap B (IsLocalRing.ResidueField B))
    (lmul'_presentationDiagonal A B P z).symm

omit [Algebra A B] [IsScalarTower A P B] in
private theorem surjective_residueDiagonalRingHom
    (hg : Function.Surjective (algebraMap P B)) :
    Function.Surjective (residueDiagonalRingHom A B P) := by
  refine (IsLocalRing.residue_surjective (R := B)).comp (hg.comp fun p => ⟨p ⊗ₜ[A] (1 : P), ?_⟩)
  change (Algebra.TensorProduct.lmul' (R := A) (S := P)) (p ⊗ₜ[A] (1 : P)) = p
  simp

private theorem isUnit_residueDiagonalRingHom
    {x : TensorProduct A P P} (hx : x ∈ (presentationPrime A B P).primeCompl) :
    IsUnit (residueDiagonalRingHom A B P x) := by
  have hB : (Algebra.TensorProduct.lmul' (R := A) (S := B)) (presentationDiagonal A B P x) ∉
      IsLocalRing.maximalIdeal B := hx
  refine ?_
  rw [show residueDiagonalRingHom A B P x = algebraMap B (IsLocalRing.ResidueField B)
    ((Algebra.TensorProduct.lmul' (R := A) (S := B)) (presentationDiagonal A B P x)) from
    congrArg (fun w : TensorProduct A P P →+* IsLocalRing.ResidueField B => w x)
      (residueDiagonalRingHom_eq A B P)]
  exact (IsLocalRing.notMem_maximalIdeal.mp hB).map _

end LocalPresentation

/-- The relation `1 ⊗ k - k ⊗ 1` attached to an element `k` of the kernel of `P → B` dies in
`B ⊗[A] B`. -/
private theorem presentationDiagonal_one_tmul_sub_tmul_one
    (A : Type u) (B : Type v) (P : Type u) [CommRing A] [CommRing B] [CommRing P]
    [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B]
    (k : RingHom.ker (algebraMap P B)) :
    presentationDiagonal A B P ((1 : P) ⊗ₜ[A] (k : P) - (k : P) ⊗ₜ[A] (1 : P)) = 0 := by
  have hk0 : algebraMap P B (k : P) = 0 := RingHom.mem_ker.mp k.property
  rw [presentationDiagonal, map_sub, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul]
  simp [hk0]

/-- An element of `P ⊗[A] P` killed in `B ⊗[A] B` becomes an element of `I` in `(P ⊗[A] P)_𝔪`. -/
private theorem algebraMap_mem_diagonalIdeal
    (A : Type u) (B : Type v) (P : Type u) [CommRing A] [CommRing B] [CommRing P]
    [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B] [IsLocalRing B]
    {z : TensorProduct A P P}
    (hz : presentationDiagonal A B P z = 0) :
    algebraMap (TensorProduct A P P) (PresentationLocalization A B P) z ∈ diagonalIdeal A B P := by
  refine RingHom.mem_ker.mpr ((Localization.localRingHom_to_map (presentationPrime A B P)
    (diagonalPrime A B) (presentationDiagonal A B P).toRingHom rfl z).trans ?_)
  exact (congrArg _ hz).trans (map_zero _)

/-- The multiplication map `(B ⊗[A] B)_𝔮 → B` restricts to the multiplication on `B ⊗[A] B`. -/
private theorem diagonalMultiplication_comp_algebraMap
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] :
    (diagonalMultiplication A B).toRingHom.comp
      (algebraMap (TensorProduct A B B) (DiagonalLocalization A B)) =
      (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom :=
  IsLocalization.lift_comp (M := (diagonalPrime A B).primeCompl)
    (g := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom)
    fun x => IsLocalRing.notMem_maximalIdeal.mp x.2

/-- **Rodicio's theorem at a local presentation.** Let `P → B` be a surjection onto a local ring
`B`, with `P` essentially of finite type over the Noetherian ring `A`. If `B` has finite
projective dimension over `B ⊗[A] B`, the conormal comparison `I/𝔪I → J/𝔪J` of the two ideals of
`(P ⊗[A] P)_𝔪` cutting out `(B ⊗[A] B)_𝔮` and `B` is injective.

The hypothesis of Rodicio's theorem (Stacks 09PV) is finite projective dimension of `B` over
the local ring `(P ⊗[A] P)_𝔪`, transported from
`StacksDraft.Smooth.exists_hasProjectiveDimensionLT_diagonal_localization` along the
isomorphisms `(P ⊗[A] P)_𝔪/I ≅ (B ⊗[A] B)_𝔮` and `(P ⊗[A] P)_𝔪/J ≅ B`. -/
private theorem conormalInjective_of_hasProjectiveDimensionLT_diagonal
    (A : Type u) (B : Type v) (P : Type u)
    [CommRing A] [CommRing B] [CommRing P] [IsNoetherianRing A]
    [IsLocalRing B] [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B]
    [Algebra.EssFiniteType A P]
    (hg : Function.Surjective (algebraMap P B))
    (hpd : letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (TensorProduct A B B) B) n) :
    ConormalInjective A B P := by
  classical
  let g : P →ₐ[A] B := IsScalarTower.toAlgHom A P B
  let R := TensorProduct A P P
  let T := TensorProduct A B B
  let f : R →ₐ[A] T := presentationDiagonal A B P
  let μ : T →ₐ[A] B := Algebra.TensorProduct.lmul' (R := A) (S := B)
  let : Algebra T B := μ.toRingHom.toAlgebra
  let : IsScalarTower A T B :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (μ.commutes a).symm)
  let q : Ideal T := diagonalPrime A B
  let m : Ideal R := presentationPrime A B P
  let Tq := DiagonalLocalization A B
  let Q := PresentationLocalization A B P
  have hf : Function.Surjective f := Algebra.TensorProduct.map_surjective g g hg hg
  have hmap : Submonoid.map f.toRingHom m.primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective f.toRingHom hf q
  let : IsLocalization (Submonoid.map f.toRingHom m.primeCompl) Tq := by
    rw [hmap]; infer_instance
  let fQ : Q →ₐ[A] Tq := presentationDiagonalLocalized A B P
  have hfQ : Function.Surjective fQ :=
    IsLocalization.map_surjective_of_surjective m.primeCompl Q Tq hf
  have hμ : Function.Surjective μ := by
    intro b
    refine ⟨b ⊗ₜ[A] (1 : B), ?_⟩
    change Algebra.TensorProduct.lmul' (R := A) (S := B) (b ⊗ₜ[A] (1 : B)) = b
    simp
  have hunitq : ∀ x : q.primeCompl, IsUnit (μ x.1) := fun x =>
    IsLocalRing.notMem_maximalIdeal.mp x.2
  let μq : Tq →ₐ[A] B := diagonalMultiplication A B
  let : Algebra Tq B := μq.toRingHom.toAlgebra
  have hμq_comp : μq.toRingHom.comp (algebraMap T Tq) = μ.toRingHom :=
    diagonalMultiplication_comp_algebraMap A B
  let : IsScalarTower T Tq B := IsScalarTower.of_algebraMap_eq' hμq_comp.symm
  have hμq : Function.Surjective μq := by
    intro b
    obtain ⟨x, hx⟩ := hμ b
    exact ⟨algebraMap T Tq x, by
      rw [show μq (algebraMap T Tq x) = μ x from
        congrArg (fun w : T →+* B => w x) hμq_comp]
      exact hx⟩
  let νq : Q →ₐ[A] B := presentationMultiplication A B P
  have hνq : Function.Surjective νq := hμq.comp hfQ
  let I : Ideal Q := RingHom.ker fQ
  let J : Ideal Q := RingHom.ker νq
  have hIJ : I ≤ J := diagonalIdeal_le_multiplicationIdeal A B P
  let : Algebra Q Tq := fQ.toRingHom.toAlgebra
  let : Algebra Q B := νq.toRingHom.toAlgebra
  let eI := Ideal.quotientKerAlgEquivOfSurjective (f := fQ) hfQ
  let eJ := Ideal.quotientKerAlgEquivOfSurjective (f := νq) hνq
  let : Small.{u} Tq := small_of_injective (f := eI.symm) eI.symm.injective
  let : Algebra (Q ⧸ I) (Q ⧸ J) := (Ideal.Quotient.factor hIJ).toAlgebra
  let : Module (Q ⧸ I) (Q ⧸ J) := Module.compHom (Q ⧸ J) (Ideal.Quotient.factor hIJ)
  let θ : Tq →+* (Q ⧸ J) :=
    (Ideal.Quotient.factor hIJ).comp eI.symm.toRingEquiv.toRingHom
  let : Module Tq (Q ⧸ J) := Module.compHom (Q ⧸ J) θ
  let : Module Tq B := Module.compHom B μq.toRingHom
  have hθ : eJ.toRingEquiv.toRingHom.comp θ = μq.toRingHom := by
    ext t
    obtain ⟨x, rfl⟩ := hfQ t
    change eJ (Ideal.Quotient.factor hIJ (eI.symm (fQ x))) = μq (fQ x)
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk]
    rfl
  have hθ_apply (t : Tq) : eJ (θ t) = μq.toRingHom t :=
    congrArg (fun w : Tq →+* B => w t) hθ
  let e : (Q ⧸ J) ≃ₗ[Tq] B :=
    { toFun := eJ
      invFun := eJ.symm
      left_inv := eJ.left_inv
      right_inv := eJ.right_inv
      map_add' := eJ.map_add
      map_smul' t x := by
        change eJ (θ t * x) = μq.toRingHom t * eJ x
        calc eJ (θ t * x) = eJ (θ t) * eJ x := map_mul eJ.toRingEquiv.toRingHom (θ t) x
          _ = μq.toRingHom t * eJ x := by rw [hθ_apply] }
  have hpdT := exists_hasProjectiveDimensionLT_diagonal_localization A B hpd
  change ∃ k : ℕ, HasProjectiveDimensionLT (ModuleCat.of Tq B) k at hpdT
  obtain ⟨k₀, hk₀⟩ := hpdT
  let : HasProjectiveDimensionLT (ModuleCat.of Tq B) k₀ := hk₀
  let : HasProjectiveDimensionLE (ModuleCat.of Tq B) k₀ :=
    hasProjectiveDimensionLT_of_ge (ModuleCat.of Tq B) k₀ (k₀ + 1) (by omega)
  have hpdQ : HasProjectiveDimensionLT (ModuleCat.of Tq (Q ⧸ J)) (k₀ + 1) :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv.{v, u}
      (M := ModuleCat.of Tq B) (N := ModuleCat.of Tq (Q ⧸ J)) e.symm k₀
  let eScalar : Tq ≃+* (Q ⧸ I) := eI.symm.toRingEquiv
  let : RingHomInvPair (eScalar : Tq →+* (Q ⧸ I)) (eScalar.symm : (Q ⧸ I) →+* Tq) :=
    RingHomInvPair.of_ringEquiv eScalar
  let : RingHomInvPair (eScalar.symm : (Q ⧸ I) →+* Tq) (eScalar : Tq →+* (Q ⧸ I)) :=
    RingHomInvPair.of_ringEquiv_symm eScalar
  let : HasProjectiveDimensionLT (ModuleCat.of Tq (Q ⧸ J)) (k₀ + 1) := hpdQ
  let : HasProjectiveDimensionLE (ModuleCat.of Tq (Q ⧸ J)) (k₀ + 1) :=
    hasProjectiveDimensionLT_of_ge (ModuleCat.of Tq (Q ⧸ J)) (k₀ + 1) (k₀ + 2) (by omega)
  have hTor : ∃ k : ℕ,
      let : Algebra (Q ⧸ I) (Q ⧸ J) := (Ideal.Quotient.factor hIJ).toAlgebra
      HasProjectiveDimensionLT (ModuleCat.of (Q ⧸ I) (Q ⧸ J)) k :=
    ⟨k₀ + 2, ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv.{u, u}
      (e := eScalar) (M := ModuleCat.of Tq (Q ⧸ J)) (N := ModuleCat.of (Q ⧸ I) (Q ⧸ J))
      { toFun := id
        invFun := id
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' r x := rfl } (k₀ + 1)⟩
  have : Algebra.EssFiniteType P R := Algebra.EssFiniteType.baseChange (R := A) (S := P) (T := P)
  have : Algebra.EssFiniteType A R := Algebra.EssFiniteType.comp A P R
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing A R
  have : IsNoetherianRing Q := IsLocalization.isNoetherianRing m.primeCompl Q inferInstance
  exact StacksDraft.Rodicio.injective_mapQ_maximalIdeal_of_finite_projectiveDimension
    I J (RingHom.ker_ne_top fQ.toRingHom) (RingHom.ker_ne_top νq.toRingHom) hIJ hTor

/-- **The relation `1 ⊗ k - k ⊗ 1` is already in `𝔪 I`.** This is Rodicio's injectivity
transported to the element the source's argument tests: the relation lies in `𝔪 J` because `dk`
lies in `𝔪_P Ω[P⁄A]` (Nakayama in the diagonal ideal), and injectivity of `I/𝔪I → J/𝔪J` moves
that back to `𝔪 I`. -/
private theorem relationMemConormal_of_conormalInjective
    (A : Type u) (B : Type v) (P : Type u)
    [CommRing A] [CommRing B] [CommRing P] [IsLocalRing B] [IsLocalRing P]
    [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B]
    (hg : Function.Surjective (algebraMap P B))
    (hconormal : ConormalInjective A B P)
    (k : RingHom.ker (algebraMap P B))
    (hDk : KaehlerDifferential.D A P (k : P) ∈
      IsLocalRing.maximalIdeal P • (⊤ : Submodule P Ω[P⁄A])) :
    RelationMemConormal A B P k := by
  classical
  let R := TensorProduct A P P
  let T := TensorProduct A B B
  let f : R →ₐ[A] T := presentationDiagonal A B P
  let μ : T →ₐ[A] B := Algebra.TensorProduct.lmul' (R := A) (S := B)
  let : Algebra T B := μ.toRingHom.toAlgebra
  let q : Ideal T := diagonalPrime A B
  let m : Ideal R := presentationPrime A B P
  let Tq := DiagonalLocalization A B
  let Q := PresentationLocalization A B P
  let νq : Q →ₐ[A] B := presentationMultiplication A B P
  let I : Ideal Q := diagonalIdeal A B P
  let J : Ideal Q := multiplicationIdeal A B P
  let ρ : R →+* Q := algebraMap R Q
  let H : Ideal R := KaehlerDifferential.ideal A P
  let δ : R := (1 : P) ⊗ₜ[A] (k : P) - (k : P) ⊗ₜ[A] (1 : P)
  let l : P →ₐ[A] R := Algebra.TensorProduct.includeLeft
  let mR : Ideal R := Ideal.map l.toRingHom (IsLocalRing.maximalIdeal P)
  have hδsum : δ ∈ mR * H + H ^ 2 :=
    one_tmul_sub_tmul_one_mem_maximalIdeal_mul_add_sq A P (k : P) hDk
  have : IsLocalHom (algebraMap P B) := IsLocalHom.of_surjective _ hg
  have hmRle : mR ≤ m := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    change μ (f (l.toRingHom a)) ∈ IsLocalRing.maximalIdeal B
    rw [lmul'_presentationDiagonal A B P (l.toRingHom a),
      show (Algebra.TensorProduct.lmul' (R := A) (S := P)) (l.toRingHom a) = a by
        change (Algebra.TensorProduct.lmul' (R := A) (S := P)) (a ⊗ₜ[A] (1 : P)) = a
        simp]
    exact map_nonunit (algebraMap P B) a ha
  have hmQ : Ideal.map ρ mR ≤ IsLocalRing.maximalIdeal Q := by
    calc Ideal.map ρ mR ≤ Ideal.map ρ m := Ideal.map_mono hmRle
      _ = IsLocalRing.maximalIdeal Q := IsLocalization.AtPrime.map_eq_maximalIdeal _ _
  have hμqcomp : (diagonalMultiplication A B).toRingHom.comp (algebraMap T Tq) = μ.toRingHom :=
    diagonalMultiplication_comp_algebraMap A B
  have hνρ (z : R) :
      νq (ρ z) = algebraMap P B ((Algebra.TensorProduct.lmul' (R := A) (S := P)) z) := by
    change diagonalMultiplication A B
      (Localization.localRingHom m q f.toRingHom rfl (algebraMap R Q z)) = _
    rw [Localization.localRingHom_to_map m q f.toRingHom rfl,
      show diagonalMultiplication A B (algebraMap T Tq (f.toRingHom z)) = μ (f z) from
        congrArg (fun w : T →+* B => w (f z)) hμqcomp]
    exact lmul'_presentationDiagonal A B P z
  have hHle : Ideal.map ρ H ≤ J := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    change KaehlerDifferential.ideal A P ≤ Ideal.comap ρ J
    rw [← KaehlerDifferential.span_range_eq_ideal A P]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    change νq (ρ ((1 : P) ⊗ₜ[A] a - a ⊗ₜ[A] (1 : P))) = 0
    rw [hνρ, show (Algebra.TensorProduct.lmul' (R := A) (S := P))
      ((1 : P) ⊗ₜ[A] a - a ⊗ₜ[A] (1 : P)) = 0 by simp, map_zero]
  have hJproper : J ≠ ⊤ := RingHom.ker_ne_top (presentationMultiplication A B P).toRingHom
  have hδQmJ : ρ δ ∈ IsLocalRing.maximalIdeal Q * J := by
    have hmem := Ideal.mem_map_of_mem ρ hδsum
    rw [show mR * H + H ^ 2 = mR * H ⊔ H ^ 2 from rfl, Ideal.map_sup, Ideal.map_mul,
      Ideal.map_pow] at hmem
    refine sup_le (Ideal.mul_mono hmQ hHle) ?_ hmem
    rw [pow_two]
    exact le_trans (Ideal.mul_mono hHle hHle)
      (Ideal.mul_mono (IsLocalRing.le_maximalIdeal hJproper) le_rfl)
  have hk0 : algebraMap P B (k : P) = 0 := RingHom.mem_ker.mp k.property
  have hδI : ρ δ ∈ I :=
    algebraMap_mem_diagonalIdeal A B P (presentationDiagonal_one_tmul_sub_tmul_one A B P k)
  have hδQmI : (⟨ρ δ, hδI⟩ : I) ∈ IsLocalRing.maximalIdeal Q • (⊤ : Submodule Q I) := by
    refine (Submodule.Quotient.mk_eq_zero _).mp (hconormal ?_)
    rw [Submodule.mapQ_apply]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    simpa [Submodule.mem_smul_top_iff, smul_eq_mul] using hδQmJ
  intro y hy
  rw [show y = (⟨ρ δ, hδI⟩ : I) from Subtype.ext hy]
  exact hδQmI

/-- **The comparison map of the source's argument, before localizing.** The kernel of
`P ⊗[A] P → B ⊗[A] B` maps to `κ_B ⊗_P K` by reducing a relation modulo the *left* tensor
factor: it factors through the kernel of `B ⊗[A] P → B ⊗[A] B`, which is the base change
`(B ⊗[A] P) ⊗_P K` of `K` because `B` is flat over `A`, and then through
`B ⊗[A] P → κ_B`. On the relation `1 ⊗ k - k ⊗ 1` the map takes the value `1 ⊗ k`. -/
private theorem exists_residueConormalComparison
    (A : Type u) (B : Type v) (P : Type u)
    [CommRing A] [CommRing B] [CommRing P] [IsLocalRing B]
    [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B] [Module.Flat A B]
    (hg : Function.Surjective (algebraMap P B)) :
    letI := residueConormalModule A B P
    ∃ η : RingHom.ker (presentationDiagonal A B P).toRingHom →ₗ[TensorProduct A P P]
        (IsLocalRing.ResidueField B ⊗[P] RingHom.ker (algebraMap P B)),
      ∀ (k : RingHom.ker (algebraMap P B))
        (y : RingHom.ker (presentationDiagonal A B P).toRingHom),
        (y : TensorProduct A P P) = (1 : P) ⊗ₜ[A] (k : P) - (k : P) ⊗ₜ[A] (1 : P) →
          η y = (1 : IsLocalRing.ResidueField B) ⊗ₜ[P] k := by
  classical
  let g : P →ₐ[A] B := IsScalarTower.toAlgHom A P B
  let kB := IsLocalRing.ResidueField B
  let Kker : Ideal P := RingHom.ker (algebraMap P B)
  let R := TensorProduct A P P
  let T := TensorProduct A B B
  let f : R →ₐ[A] T := presentationDiagonal A B P
  let μ : T →ₐ[A] B := Algebra.TensorProduct.lmul' (R := A) (S := B)
  let U := TensorProduct A B P
  let φ : R →ₐ[A] U := Algebra.TensorProduct.map g (AlgHom.id A P)
  let ψ : U →ₐ[A] T := Algebra.TensorProduct.map (AlgHom.id A B) g
  have hφψ : ψ.toRingHom.comp φ.toRingHom = f.toRingHom := by
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [RingHom.comp_apply]
      rfl
    | add x y hx hy =>
      change ψ (φ x) = f x at hx
      change ψ (φ y) = f y at hy
      simp [hx, hy]
  let rB : B →ₐ[B] kB := Algebra.ofId B kB
  let τ : U →ₐ[A] kB := Algebra.TensorProduct.lift (rB.restrictScalars A)
    ((rB.restrictScalars A).comp g) fun b x => Commute.all _ _
  have hτ : τ = (rB.restrictScalars A).comp ((μ.restrictScalars A).comp ψ) := by
    refine AlgHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul b x => exact (map_mul rB b (g x)).symm
    | add x y hx hy => simp [hx, hy]
  let rightInclU : P →ₐ[A] U := Algebra.TensorProduct.includeRight
  let : Algebra P U := rightInclU.toRingHom.toAlgebra
  let : Module P U := Algebra.toModule
  let : SMul P U := (Module.toDistribMulAction (R := P) (M := U)).toSMul
  let : IsScalarTower A P U := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => by
    change algebraMap A U a = rightInclU (algebraMap A P a)
    exact (rightInclU.commutes a).symm)
  let M := kB ⊗[P] Kker
  let : SMulCommClass P kB kB := ⟨fun x y z => by simp only [Algebra.smul_def]; ac_rfl⟩
  let : Module kB M := TensorProduct.leftModule
  have hτalgP (x : P) : τ (algebraMap P U x) = algebraMap P kB x := by
    change τ ((1 : B) ⊗ₜ[A] x) = _
    rw [show τ ((1 : B) ⊗ₜ[A] x) = rB 1 * rB (g x) from
      Algebra.TensorProduct.lift_tmul _ _ _ _ _, map_one, one_mul,
      IsScalarTower.algebraMap_apply P B kB x]
    rfl
  have hτsmul (x : P) (u : U) : τ (x • u) = algebraMap P kB x * τ u := by
    rw [Algebra.smul_def (R := P) (A := U) x u, map_mul, hτalgP]
  let : Algebra U kB := τ.toRingHom.toAlgebra
  let : Module U M := Module.compHom M τ.toRingHom
  let : SMul U M := (Module.toDistribMulAction (R := U) (M := M)).toSMul
  let : IsScalarTower P U kB := ⟨fun x u z => by
    simp only [Algebra.smul_def]
    change τ.toRingHom (x • u) * z = algebraMap P kB x * (τ.toRingHom u * z)
    rw [show τ.toRingHom (x • u) = algebraMap P kB x * τ.toRingHom u from hτsmul x u]
    ac_rfl⟩
  let : IsScalarTower U kB M :=
    IsScalarTower.of_algebraMap_smul (R := U) (A := kB) (M := M) fun x y => rfl
  let : SMulCommClass P U U := ⟨fun x y z => by
    change algebraMap P U x * (y * z) = y * (algebraMap P U x * z)
    ring⟩
  have hPU : IsScalarTower P U M := ⟨fun x u z => by
    change τ (x • u) • z = x • (τ u • z)
    rw [hτsmul, mul_smul]
    exact IsScalarTower.algebraMap_smul kB x (τ u • z)⟩
  let : IsScalarTower P U M := hPU
  let : SMulCommClass U U M := ⟨fun x y z => by
    change τ x • (τ y • z) = τ y • (τ x • z)
    rw [← mul_smul, ← mul_smul, mul_comm (τ x) (τ y)]⟩
  let : IsScalarTower U U M :=
    IsScalarTower.of_algebraMap_smul (R := U) (A := U) (M := M) fun x z => rfl
  let : Module U (U ⊗[P] Kker) := TensorProduct.leftModule
  let eKer := Algebra.kerTensorProductMapIdToAlgHomEquiv A P B B hg
  let lK : Kker →ₗ[P] M := TensorProduct.mk P kB Kker 1
  let lTensor : U ⊗[P] Kker →ₗ[U] M :=
    @LinearMap.liftBaseChange P Kker M U _ _ _ _ _ _ _ _ hPU lK
  let l0 : RingHom.ker ψ.toRingHom →ₗ[U] M := lTensor.comp eKer.toLinearMap
  let : Algebra R U := φ.toRingHom.toAlgebra
  let := residueConormalModule A B P
  let : SMul R M := (Module.toDistribMulAction (R := R) (M := M)).toSMul
  have hwτφ : τ.toRingHom.comp φ.toRingHom = residueDiagonalRingHom A B P := by
    rw [residueDiagonalRingHom_eq A B P]
    refine RingHom.ext fun z => ?_
    change τ (φ z) = algebraMap B kB (μ (f z))
    rw [hτ]
    change algebraMap B kB (μ (ψ (φ z))) = algebraMap B kB (μ (f z))
    rw [show ψ (φ z) = f z from congrArg (fun w : R →+* T => w z) hφψ]
  let : IsScalarTower R U M :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := U) (M := M) fun r z => by
      change τ (φ r) • z = (residueDiagonalRingHom A B P) r • z
      rw [show τ (φ r) = residueDiagonalRingHom A B P r from
        congrArg (fun w : R →+* kB => w r) hwτφ]
  let : Module R (RingHom.ker ψ.toRingHom) :=
    Module.compHom (RingHom.ker ψ.toRingHom) φ.toRingHom
  let : SMul R (RingHom.ker ψ.toRingHom) :=
    (Module.toDistribMulAction (R := R) (M := RingHom.ker ψ.toRingHom)).toSMul
  let : IsScalarTower R U (RingHom.ker ψ.toRingHom) :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := U)
      (M := RingHom.ker ψ.toRingHom) fun x z => rfl
  obtain ⟨kerMap, hkerMap⟩ :
      ∃ l : RingHom.ker f.toRingHom →ₗ[R] RingHom.ker ψ.toRingHom, ∀ x, (l x).1 = φ x.1 :=
    @exists_kerMap_of_comp R U T _ _ _ φ.toRingHom ψ.toRingHom f.toRingHom hφψ
      inferInstance fun r x => rfl
  refine ⟨(l0.restrictScalars R).comp kerMap, fun k y hy => ?_⟩
  have hk0 : algebraMap P B (k : P) = 0 := RingHom.mem_ker.mp k.property
  let kK : Kker := ⟨k, k.property⟩
  let uδ : U := (1 : B) ⊗ₜ[A] (k : P)
  have huδ : ψ uδ = 0 := by
    change Algebra.TensorProduct.map (AlgHom.id A B) g ((1 : B) ⊗ₜ[A] (k : P)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    change (1 : B) ⊗ₜ[A] algebraMap P B (k : P) = 0
    rw [hk0]
    simp
  have hkerMapy : kerMap y = (⟨uδ, huδ⟩ : RingHom.ker ψ.toRingHom) := by
    refine Subtype.ext ?_
    rw [hkerMap y, hy]
    change Algebra.TensorProduct.map g (AlgHom.id A P)
      ((1 : P) ⊗ₜ[A] (k : P) - (k : P) ⊗ₜ[A] (1 : P)) = uδ
    rw [map_sub, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    change (algebraMap P B (1 : P)) ⊗ₜ[A] (k : P) -
      (algebraMap P B (k : P)) ⊗ₜ[A] (1 : P) = uδ
    rw [hk0]
    simp [uδ]
  have hEquiv : eKer.symm ((1 : U) ⊗ₜ[P] kK) = (⟨uδ, huδ⟩ : RingHom.ker ψ.toRingHom) := by
    refine Subtype.ext ?_
    change (eKer.symm ((1 : U) ⊗ₜ[P] kK) : U) = uδ
    rw [show (1 : U) = ((1 : B) ⊗ₜ[A] (1 : P)) from rfl,
      Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply]
    simp [uδ, kK]
  have hlast : lTensor ((1 : U) ⊗ₜ[P] kK) = (1 : kB) ⊗ₜ[P] k := by
    rw [LinearMap.liftBaseChange_tmul]
    change (1 : U) • lK kK = (1 : kB) ⊗ₜ[P] k
    calc (1 : U) • lK kK = lK kK := one_smul _ _
      _ = (1 : kB) ⊗ₜ[P] k := rfl
  calc ((l0.restrictScalars R).comp kerMap) y = l0 (kerMap y) := rfl
    _ = l0 ⟨uδ, huδ⟩ := by rw [hkerMapy]
    _ = lTensor (eKer (eKer.symm ((1 : U) ⊗ₜ[P] kK))) :=
        congrArg (fun z => lTensor (eKer z)) hEquiv.symm
    _ = lTensor ((1 : U) ⊗ₜ[P] kK) := by rw [eKer.apply_symm_apply]
    _ = (1 : kB) ⊗ₜ[P] k := hlast

/-- **The vanishing the source's rank count produces.** If the relation `1 ⊗ k - k ⊗ 1` lies in
`𝔪 I`, then `k` dies in `κ_B ⊗_P K`.

The comparison map of `exists_residueConormalComparison` is localized at `𝔪` — `I` is the
localization of the kernel of `P ⊗[A] P → B ⊗[A] B`, and `κ_B ⊗_P K` is a module over the
*field* `κ_B`, so the denominators act invertibly — and the resulting map kills `𝔪 I` because
`𝔪` is the kernel of `(P ⊗[A] P)_𝔪 → κ_B`. -/
private theorem one_tmul_eq_zero_of_relationMemConormal
    (A : Type u) (B : Type v) (P : Type u)
    [CommRing A] [CommRing B] [CommRing P] [IsLocalRing B]
    [Algebra A B] [Algebra A P] [Algebra P B] [IsScalarTower A P B] [Module.Flat A B]
    (hg : Function.Surjective (algebraMap P B))
    (k : RingHom.ker (algebraMap P B))
    (h : RelationMemConormal A B P k) :
    (1 : IsLocalRing.ResidueField B) ⊗ₜ[P] k = 0 := by
  classical
  let kB := IsLocalRing.ResidueField B
  let Kker : Ideal P := RingHom.ker (algebraMap P B)
  let R := TensorProduct A P P
  let T := TensorProduct A B B
  let f : R →ₐ[A] T := presentationDiagonal A B P
  let q : Ideal T := diagonalPrime A B
  let m : Ideal R := presentationPrime A B P
  let Tq := DiagonalLocalization A B
  let Q := PresentationLocalization A B P
  let I : Ideal Q := diagonalIdeal A B P
  let M := kB ⊗[P] Kker
  let : Module R M := residueConormalModule A B P
  let : SMul R M := (Module.toDistribMulAction (R := R) (M := M)).toSMul
  let w : R →+* kB := residueDiagonalRingHom A B P
  have hwunit : ∀ x : m.primeCompl, IsUnit (w x.1) := fun x =>
    isUnit_residueDiagonalRingHom A B P x.2
  let wQ : Q →+* kB := IsLocalization.lift (M := m.primeCompl) (g := w) hwunit
  have hwQ_comp : wQ.comp (algebraMap R Q) = w :=
    IsLocalization.lift_comp (M := m.primeCompl) (g := w) hwunit
  let : Algebra R kB := w.toAlgebra
  let : IsScalarTower R kB M :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := kB) (M := M) fun x y => rfl
  let : IsScalarTower R R M := ⟨fun x y z => by
    change w (x * y) • z = w x • (w y • z)
    rw [map_mul, mul_smul]⟩
  let : SMulCommClass R R M := ⟨fun x y z => by
    change w x • (w y • z) = w y • (w x • z)
    rw [← mul_smul, ← mul_smul, mul_comm]⟩
  let : Algebra R (Module.End R M) := Module.End.instAlgebra R R M
  let : Module Q M := Module.compHom M wQ
  let : SMul Q M := (Module.toDistribMulAction (R := Q) (M := M)).toSMul
  let : IsScalarTower R Q M :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := Q) (M := M) fun r z => by
      change wQ (algebraMap R Q r) • z = w r • z
      rw [show wQ (algebraMap R Q r) = w r from congrArg (fun u : R →+* kB => u r) hwQ_comp]
  have hf : Function.Surjective f :=
    Algebra.TensorProduct.map_surjective (IsScalarTower.toAlgHom A P B)
      (IsScalarTower.toAlgHom A P B) hg hg
  have hmap : Submonoid.map f.toRingHom m.primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective f.toRingHom hf q
  let : IsLocalizedModule m.primeCompl
      (RingHom.toKerIsLocalization Q Tq f.toRingHom
        (hmap.symm ▸ Submonoid.le_comap_map m.primeCompl)) :=
    RingHom.toKerIsLocalization_isLocalizedModule (Q := Tq) f.toRingHom hmap
  let locf : Q →+* Tq := IsLocalization.map Tq f.toRingHom
    (hmap.symm ▸ Submonoid.le_comap_map m.primeCompl)
  have hlocf : (presentationDiagonalLocalized A B P).toRingHom = locf := by
    refine IsLocalization.ringHom_ext m.primeCompl (RingHom.ext fun x => ?_)
    change presentationDiagonalLocalized A B P (algebraMap R Q x) = locf (algebraMap R Q x)
    have h1 : presentationDiagonalLocalized A B P (algebraMap R Q x) = algebraMap T Tq (f x) :=
      Localization.localRingHom_to_map m q f.toRingHom rfl x
    have h2 : locf (algebraMap R Q x) = algebraMap T Tq (f x) :=
      IsLocalization.map_eq (M := m.primeCompl) _ x
    rw [h1, h2]
  have hkerf : I = RingHom.ker locf := congrArg RingHom.ker hlocf
  obtain ⟨η₀, hη₀⟩ := exists_residueConormalComparison A B P hg
  let ηAux : RingHom.ker locf →ₗ[R] M :=
    IsLocalizedModule.lift m.primeCompl
      (RingHom.toKerIsLocalization Q Tq f.toRingHom
        (hmap.symm ▸ Submonoid.le_comap_map m.primeCompl)) η₀ fun s => by
        rw [show algebraMap R (Module.End R M) s.1 =
            (Algebra.lsmul R R M : kB →ₐ[R] Module.End R M) (w s.1) from
          LinearMap.ext fun z => rfl]
        exact (hwunit s).map (Algebra.lsmul R R M : kB →ₐ[R] Module.End R M)
  let η : I →ₗ[Q] M :=
    (ηAux.comp ((LinearEquiv.ofEq _ _ hkerf).toLinearMap.restrictScalars R)
      ).extendScalarsOfIsLocalization m.primeCompl Q
  have hwQsurj : Function.Surjective wQ := by
    intro x
    obtain ⟨z, hz⟩ := surjective_residueDiagonalRingHom A B P hg x
    refine ⟨algebraMap R Q z, ?_⟩
    rwa [show wQ (algebraMap R Q z) = w z from congrArg (fun u : R →+* kB => u z) hwQ_comp]
  have hwQker : RingHom.ker wQ = IsLocalRing.maximalIdeal Q :=
    IsLocalRing.ker_eq_maximalIdeal wQ hwQsurj
  have hmax : ∀ r ∈ IsLocalRing.maximalIdeal Q, ∀ z : M, r • z = 0 := fun r hr z => by
    change wQ r • z = 0
    rw [show wQ r = 0 from RingHom.mem_ker.mp (hwQker ▸ hr), zero_smul]
  let δ : R := (1 : P) ⊗ₜ[A] (k : P) - (k : P) ⊗ₜ[A] (1 : P)
  have hδker : δ ∈ RingHom.ker f.toRingHom :=
    presentationDiagonal_one_tmul_sub_tmul_one A B P k
  have hδI : algebraMap R Q δ ∈ I := algebraMap_mem_diagonalIdeal A B P hδker
  have hηδ : η ⟨algebraMap R Q δ, hδI⟩ = 0 := by
    refine Submodule.smul_induction_on (h ⟨algebraMap R Q δ, hδI⟩ rfl) (fun r hr x _ => ?_)
      fun x y hx hy => by simp [hx, hy]
    rw [η.map_smul]
    exact hmax r hr _
  have hηvalue : η ⟨algebraMap R Q δ, hδI⟩ = (1 : kB) ⊗ₜ[P] k := by
    have hunfold : η ⟨algebraMap R Q δ, hδI⟩ =
        ηAux ((LinearEquiv.ofEq _ _ hkerf) ⟨algebraMap R Q δ, hδI⟩) := rfl
    rw [hunfold, show (LinearEquiv.ofEq _ _ hkerf) (⟨algebraMap R Q δ, hδI⟩ : I) =
      RingHom.toKerIsLocalization Q Tq f.toRingHom
        (hmap.symm ▸ Submonoid.le_comap_map m.primeCompl) ⟨δ, hδker⟩ from Subtype.ext rfl]
    dsimp only [ηAux]
    rw [IsLocalizedModule.lift_apply]
    exact hη₀ k ⟨δ, hδker⟩ rfl
  exact hηvalue.symm.trans hηδ

/-- **The content of Stacks 0FCW.** Let `A → B` be a flat ring map, essentially of finite type,
from a Noetherian ring to a local ring. If `B` has finite projective dimension over `B ⊗[A] B`,
then `B` is formally smooth over `A`. The hypothesis mentions no derived category.

The proof writes `B` as a quotient of `P = A[x_1, …, x_n]_𝔮` and runs Rodicio's theorem
(Stacks 09PV) on the pair of ideals `I ⊆ J` of the local ring `(P ⊗[A] P)_𝔪` cutting out
`(B ⊗[A] B)_𝔮` and `B`; see
`StacksDraft.Smooth.conormalInjective_of_hasProjectiveDimensionLT_diagonal`. The injectivity so
obtained is transported, by `StacksDraft.Smooth.one_tmul_eq_zero_of_relationMemConormal`, into the
statement that an element `k` of the kernel `K` of `P → B` whose differential lies in
`𝔪_P Ω[P⁄A]` already lies in `𝔪_P K`, which is exactly injectivity of the cotangent complex of the
presentation after base change to the residue field of `B`, hence formal smoothness. -/
public theorem formallySmooth_of_hasProjectiveDimensionLT_diagonal
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing A]
    [Algebra A B] [Module.Flat A B] [Algebra.EssFiniteType A B]
    (hpd : letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (TensorProduct A B B) B) n) :
    Algebra.FormallySmooth A B := by
  classical
  obtain ⟨n, q₀, hq₀, g, hg₀⟩ := exists_localization_mvPolynomial_surjective A B
  let : q₀.IsPrime := hq₀
  let P := Localization.AtPrime q₀
  let : IsLocalRing P := IsLocalization.AtPrime.isLocalRing P q₀
  let : Algebra P B := g.toRingHom.toAlgebra
  let : IsScalarTower A P B :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (g.commutes a).symm)
  have hg : Function.Surjective (algebraMap P B) := hg₀
  have : IsNoetherianRing P := IsLocalization.isNoetherianRing q₀.primeCompl P inferInstance
  have : Algebra.EssFiniteType A P := inferInstance
  have : Algebra.FormallySmooth A P := by
    let : Algebra.FormallyEtale (MvPolynomial (Fin n) A) P :=
      Algebra.FormallyEtale.of_isLocalization q₀.primeCompl
    exact Algebra.FormallySmooth.comp A (MvPolynomial (Fin n) A) P
  have : Module.Free P Ω[P⁄A] :=
    Module.Free.of_equiv
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A (MvPolynomial (Fin n) A) P)
  have : Module.Finite P Ω[P⁄A] :=
    Module.Finite.of_surjective
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A
        (MvPolynomial (Fin n) A) P).toLinearMap (LinearEquiv.surjective _)
  have hconormal := conormalInjective_of_hasProjectiveDimensionLT_diagonal A B P hg hpd
  have hcotangent : Function.Injective
      (KaehlerDifferential.cotangentComplexBaseChange A B P (IsLocalRing.ResidueField B)) := by
    let kB := IsLocalRing.ResidueField B
    let : IsScalarTower P B kB := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)
    have hPkB : Function.Surjective (algebraMap P kB) :=
      (IsLocalRing.residue_surjective (R := B)).comp hg
    have hPkBker : RingHom.ker (algebraMap P kB) = IsLocalRing.maximalIdeal P :=
      IsLocalRing.ker_eq_maximalIdeal (algebraMap P kB) hPkB
    intro z z' hzz'
    let c := KaehlerDifferential.cotangentComplexBaseChange A B P kB
    have hz : c (z - z') = 0 := by
      rw [map_sub c z z', show c z = c z' from hzz', sub_self]
    obtain ⟨k, hzrep⟩ := exists_eq_one_tmul P kB hPkB _ (z - z')
    have hDk : KaehlerDifferential.D A P (k : P) ∈
        IsLocalRing.maximalIdeal P • (⊤ : Submodule P Ω[P⁄A]) := by
      rw [← hPkBker]
      have hkB : algebraMap P kB (k : P) = 0 := by
        rw [IsScalarTower.algebraMap_eq P B kB]
        exact congrArg (algebraMap B kB) (RingHom.mem_ker.mp k.property)
      have hzero : KaehlerDifferential.kerToTensor A P kB ⟨k, hkB⟩ = 0 := by
        rw [hzrep, show c ((1 : kB) ⊗ₜ[P] (k : RingHom.ker (algebraMap P B))) =
          KaehlerDifferential.kerToTensor A P kB ⟨k, hkB⟩ by
            simp [c, KaehlerDifferential.cotangentComplexBaseChange_tmul]] at hz
        exact hz
      refine (one_tmul_eq_zero_iff_mem_ker_smul_top P kB hPkB _
        (KaehlerDifferential.D A P (k : P))).mp ?_
      simpa only [KaehlerDifferential.kerToTensor_apply] using hzero
    have hTensor : (1 : kB) ⊗ₜ[P] k = 0 :=
      one_tmul_eq_zero_of_relationMemConormal A B P hg k
        (relationMemConormal_of_conormalInjective A B P hg hconormal k hDk)
    exact sub_eq_zero.mp (hzrep.trans hTensor)
  exact (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
    (R := A) (S := B) (P := P) hg (IsNoetherian.noetherian _)).mpr hcotangent

/-- A flat local homomorphism of Noetherian local rings which is essentially of finite type and
whose diagonal `B ⊗[A] B → B` is perfect, for a certified derived tensor product on a model of
`D(B ⊗[A] B)`, is formally smooth; locality of `A` is not needed. A perfect diagonal gives `B`
finite projective dimension over `B ⊗[A] B`, so this is
`StacksDraft.Smooth.formallySmooth_of_hasProjectiveDimensionLT_diagonal`. -/
public theorem formallySmooth_of_isPerfect_diagonal
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing A]
    [Algebra A B] [Module.Flat A B]
    [Algebra.EssFiniteType A B]
    [HasDerivedCategory.{w} (ModuleCat.{v} (TensorProduct A B B))]
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring (TensorProduct A B B))
    (hperfect :
      letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      RingHom.IsPerfectRingMap (TensorProduct A B B) B D.tensor D.comparison D.isLeftDerived) :
    Algebra.FormallySmooth A B :=
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  formallySmooth_of_hasProjectiveDimensionLT_diagonal A B
    (exists_hasProjectiveDimensionLT_diagonal A B D hperfect)

/-- **Stacks 0FCW.** Let `A → B` be a flat ring map, essentially of finite type, from a Noetherian
ring to a local ring. If `B` has finite projective dimension over `B ⊗[A] B`, then `B` is the
localization of a smooth `A`-algebra.

The source states this for a local homomorphism of Noetherian local rings whose diagonal is
perfect; that form is `StacksDraft.Smooth.exists_smooth_isLocalization_of_isPerfect_diagonal`.
Finite projective dimension of the diagonal gives formal smoothness by
`StacksDraft.Smooth.formallySmooth_of_hasProjectiveDimensionLT_diagonal`, and a formally smooth
local algebra essentially of finite type is a localization of a smooth algebra by
`StacksDraft.Smooth.exists_smooth_isLocalization_of_formallySmooth`. -/
@[stacks 0FCW]
public theorem exists_smooth_isLocalization_of_hasProjectiveDimensionLT_diagonal
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing A]
    [Algebra A B] [Module.Flat A B] [Algebra.EssFiniteType A B]
    (hpd : letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (TensorProduct A B B) B) n) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Smooth A C)
      (M : Submonoid C) (_ : Algebra C B), IsScalarTower A C B ∧ IsLocalization M B :=
  exists_smooth_isLocalization_of_formallySmooth A B
    (formallySmooth_of_hasProjectiveDimensionLT_diagonal A B hpd)

/-- Stacks 0FCW in the source's form: let `A → B` be a local homomorphism of Noetherian local rings
with `B` flat and essentially of finite type over `A`. If the multiplication map `B ⊗[A] B → B` is
a perfect ring map, for a certified derived tensor product on a model of `D(B ⊗[A] B)`, then `B`
is the localization of a smooth `A`-algebra. Locality of `A` is not needed.

The perfect diagonal gives formal smoothness by
`StacksDraft.Smooth.formallySmooth_of_isPerfect_diagonal`, and a formally smooth local algebra
essentially of finite type is a localization of a smooth algebra by
`StacksDraft.Smooth.exists_smooth_isLocalization_of_formallySmooth`. -/
public theorem exists_smooth_isLocalization_of_isPerfect_diagonal
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing A]
    [Algebra A B] [Module.Flat A B]
    [Algebra.EssFiniteType A B]
    [HasDerivedCategory.{w} (ModuleCat.{v} (TensorProduct A B B))]
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring (TensorProduct A B B))
    (hperfect :
      letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      RingHom.IsPerfectRingMap (TensorProduct A B B) B D.tensor D.comparison D.isLeftDerived) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Smooth A C)
      (M : Submonoid C) (_ : Algebra C B), IsScalarTower A C B ∧ IsLocalization M B :=
  exists_smooth_isLocalization_of_formallySmooth A B
    (formallySmooth_of_isPerfect_diagonal A B D hperfect)

/-! ### The global statement, Stacks 0FCX -/

/-- `C ⊗[A] C` is a localization of `B ⊗[A] B` when `C` is a localization of `B`, by localizing
one tensor factor at a time; the submonoid contains the image of the original one. -/
private theorem diagonal_isLocalization_of_isLocalization
    {A : Type u} {B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (M : Submonoid B) [IsLocalization M C] :
    letI : Algebra B (B ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
    ∃ N : Submonoid (B ⊗[A] B),
      letI : Algebra (B ⊗[A] B) (C ⊗[A] C) :=
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C)
          (IsScalarTower.toAlgHom A B C)).toRingHom.toAlgebra
      IsLocalization N (C ⊗[A] C) ∧ Algebra.algebraMapSubmonoid (B ⊗[A] B) M ≤ N := by
  let f₁ : B ⊗[A] B →ₐ[A] C ⊗[A] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A B)
  let : Algebra (B ⊗[A] B) (C ⊗[A] B) := f₁.toRingHom.toAlgebra
  let : Algebra B (B ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
  let : Algebra B (C ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower B (B ⊗[A] B) (C ⊗[A] B) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext b
    simp [f₁, RingHom.algebraMap_toAlgebra]
  let : IsScalarTower A B (C ⊗[A] B) := .to₁₃₄ _ B _ _
  let : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[A] B) M) (C ⊗[A] B) :=
    IsLocalization.tensorProduct_tensorProduct A B M C (by
      ext b
      simp [f₁, RingHom.algebraMap_toAlgebra])
  let f₂ : C ⊗[A] B →ₐ[A] C ⊗[A] C :=
    Algebra.TensorProduct.map (AlgHom.id A C) (IsScalarTower.toAlgHom A B C)
  let f : B ⊗[A] B →ₐ[A] C ⊗[A] C :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (IsScalarTower.toAlgHom A B C)
  let : Algebra (B ⊗[A] B) (C ⊗[A] C) := f.toRingHom.toAlgebra
  let : Algebra (C ⊗[A] B) (C ⊗[A] C) := f₂.toRingHom.toAlgebra
  let : Algebra C (C ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
  let : Algebra C (C ⊗[A] C) := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower C (C ⊗[A] B) (C ⊗[A] C) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext c
    simp [f₂, RingHom.algebraMap_toAlgebra]
  let : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := A) (A := C)))
      (C ⊗[A] C) := by
    let : Algebra B (C ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    let : Algebra B (C ⊗[A] C) :=
      ((Algebra.TensorProduct.includeRight (R := A) (A := C) (B := C)).comp
        (IsScalarTower.toAlgHom A B C)).toRingHom.toAlgebra
    exact IsLocalization.tensorProduct_tensorProduct_right A C M C (by
      ext b
      simp [f₂, RingHom.algebraMap_toAlgebra])
  let : IsScalarTower (B ⊗[A] B) (C ⊗[A] B) (C ⊗[A] C) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul b₁ b₂ =>
      change f (b₁ ⊗ₜ[A] b₂) = f₂ (f₁ (b₁ ⊗ₜ[A] b₂))
      simp [f, f₁, f₂]
    | add x y hx hy => simp [hx, hy]
  refine ⟨IsLocalization.localizationLocalizationSubmodule
    (Algebra.algebraMapSubmonoid (B ⊗[A] B) M)
    (M.map (Algebra.TensorProduct.includeRight (R := A) (A := C))),
    IsLocalization.localization_localization_isLocalization
      (Algebra.algebraMapSubmonoid (B ⊗[A] B) M)
      (M.map (Algebra.TensorProduct.includeRight (R := A) (A := C))) (C ⊗[A] C),
    fun x hx => ?_⟩
  rw [IsLocalization.mem_localizationLocalizationSubmodule]
  exact ⟨1, ⟨x, hx⟩, by simp⟩

/-- **Finite projective dimension of the diagonal localizes.** If `B` has finite projective
dimension over `B ⊗[A] B` and `C` is a localization of `B` which is also an algebra over a
localization `Aₚ` of `A`, then `C` has finite projective dimension over `C ⊗[Aₚ] C`: the latter is a
localization of `B ⊗[A] B` (`diagonal_isLocalization_of_isLocalization`), over which `C` is the
corresponding localization of `B`. -/
private theorem exists_hasProjectiveDimensionLT_diagonal_of_isLocalization
    {A Aₚ : Type u} {B C : Type v} [CommRing A] [CommRing Aₚ] [CommRing B] [CommRing C]
    [Algebra A Aₚ] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra Aₚ C] [IsScalarTower A Aₚ C]
    (P : Submonoid A) [IsLocalization P Aₚ]
    (M : Submonoid B) [IsLocalization M C]
    (h : letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (B ⊗[A] B) B) n) :
    letI := (Algebra.TensorProduct.lmul' (R := Aₚ) (S := C)).toRingHom.toAlgebra
    ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (C ⊗[Aₚ] C) C) n := by
  let T := B ⊗[A] B
  let U := C ⊗[A] C
  let V := C ⊗[Aₚ] C
  let : Algebra T B := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
  let : Algebra B T := Algebra.TensorProduct.leftAlgebra
  let : Algebra T C := ((algebraMap B C).comp (algebraMap T B)).toAlgebra
  have : IsScalarTower T B C := IsScalarTower.of_algebraMap_eq' rfl
  let f : T →ₐ[A] U :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (IsScalarTower.toAlgHom A B C)
  let : Algebra T U := f.toRingHom.toAlgebra
  obtain ⟨N, hN, hleft⟩ := diagonal_isLocalization_of_isLocalization (A := A) (B := B) (C := C) M
  let : IsLocalization N U := hN
  let g : U ≃+* V := (IsLocalization.algebraTensorEquiv P Aₚ C C).symm.toRingEquiv
  let f' : T →+* V := g.toRingHom.comp f.toRingHom
  let : Algebra T V := f'.toAlgebra
  let : IsLocalization N V := (IsLocalization.isLocalization_iff_of_ringEquiv N g).mp hN
  let : Algebra Aₚ V := Algebra.TensorProduct.leftAlgebra
  let : Algebra V C := (Algebra.TensorProduct.lmul' (R := Aₚ) (S := C)).toRingHom.toAlgebra
  let : SMul T V := Algebra.toSMul
  let : SMul V C := Algebra.toSMul
  let : SMul T C := Algebra.toSMul
  let : IsScalarTower T V C := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul b₁ b₂ =>
      change algebraMap B C (b₁ * b₂) =
        (Algebra.TensorProduct.lmul' (R := Aₚ) (S := C)) (g (f (b₁ ⊗ₜ[A] b₂)))
      rw [show g (f (b₁ ⊗ₜ[A] b₂)) = algebraMap B C b₁ ⊗ₜ[Aₚ] algebraMap B C b₂ from
        Algebra.TensorProduct.mapOfCompatibleSMul_tmul Aₚ A Aₚ C C _ _]
      simp
    | add x y hx hy => simp [hx, hy]
  have hleftMap : M ≤ Algebra.algebraMapSubmonoid B N := fun b hb =>
    ⟨algebraMap B T b, hleft ⟨b, hb, rfl⟩, congrArg (fun w : B →ₐ[A] B => w b)
      (Algebra.TensorProduct.lmul'_comp_includeLeft (R := A) (S := B))⟩
  let : IsLocalization (Algebra.algebraMapSubmonoid B N) C :=
    IsLocalization.of_le M (N := Algebra.algebraMapSubmonoid B N) hleftMap (by
      rintro b ⟨t, ht, rfl⟩
      rw [← IsScalarTower.algebraMap_apply T B C t, IsScalarTower.algebraMap_apply T V C t]
      exact (IsLocalization.map_units V ⟨t, ht⟩).map (algebraMap V C))
  have : Algebra.IsPushout T V B C :=
    (Algebra.IsPushout.comm T B V C).mp
      ((Algebra.isLocalization_iff_isPushout N V).mp inferInstance)
  have : IsLocalizedModule N (IsScalarTower.toAlgHom T B C).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange N V _).mpr Algebra.IsPushout.out
  exact exists_hasProjectiveDimensionLT_of_isLocalization N V (ModuleCat.of T B) C
    (IsScalarTower.toAlgHom T B C).toLinearMap h

/-- **Stacks 0FCX.** Let `A → B` be a flat finite type ring map from a Noetherian ring. If `B` has
finite projective dimension over `B ⊗[A] B`, then `B` is a smooth `A`-algebra.

The source assumes that `B` is Noetherian and that the diagonal is perfect; that form is
`StacksDraft.Smooth.smooth_of_flat_of_isPerfect_diagonal`. Smoothness is local on `B`, and at a
prime `𝔮` of `B` over `𝔭` of `A` finite projective dimension of the diagonal passes to the
localized map `A_𝔭 → B_𝔮`, which is then formally smooth by
`StacksDraft.Smooth.formallySmooth_of_hasProjectiveDimensionLT_diagonal`. -/
@[stacks 0FCX]
public theorem smooth_of_flat_of_hasProjectiveDimensionLT_diagonal
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FiniteType A B]
    (hpd : letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of (TensorProduct A B B) B) n) :
    Algebra.Smooth A B := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [Algebra.smooth_iff_forall_exists_notMem_smooth]
  intro q hq
  let : q.IsPrime := hq
  let p := q.under A
  have : p.IsPrime := Ideal.IsPrime.under A q
  have : q.LiesOver p := ⟨rfl⟩
  let Aₚ := Localization.AtPrime p
  let C := Localization.AtPrime q
  let : Algebra Aₚ C := Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower A Aₚ C := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [Localization.AtPrime.algebraMap_eq,
      Localization.localRingHom_to_map p q (algebraMap A B) Ideal.LiesOver.over a]
    rfl
  have : Module.Flat Aₚ C :=
    (Module.flat_iff_of_isLocalization (S := Aₚ) p.primeCompl C).mpr (Module.Flat.trans A B C)
  have : Algebra.EssFiniteType B C := Algebra.EssFiniteType.of_isLocalization C q.primeCompl
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_finiteType A B
  have : Algebra.EssFiniteType A C := Algebra.EssFiniteType.comp A B C
  have : IsLocalization (Algebra.algebraMapSubmonoid C p.primeCompl) C :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨a, ha, rfl⟩
      rw [IsUnit.mem_submonoid_iff, IsScalarTower.algebraMap_apply A Aₚ C]
      exact (IsLocalization.map_units Aₚ ⟨a, ha⟩).map (algebraMap Aₚ C))
  have : Algebra.IsPushout A Aₚ C C :=
    (Algebra.IsPushout.comm A C Aₚ C).mp
      (Algebra.isPushout_of_isLocalization p.primeCompl Aₚ C C)
  have : Algebra.EssFiniteType Aₚ (Aₚ ⊗[A] C) := Algebra.EssFiniteType.baseChange A C Aₚ
  have : Algebra.EssFiniteType Aₚ C :=
    Algebra.EssFiniteType.of_surjective (Algebra.IsPushout.equiv A Aₚ C C).toAlgHom
      (Algebra.IsPushout.equiv A Aₚ C C).surjective
  have : Algebra.FormallySmooth Aₚ C :=
    formallySmooth_of_hasProjectiveDimensionLT_diagonal Aₚ C
      (exists_hasProjectiveDimensionLT_diagonal_of_isLocalization p.primeCompl q.primeCompl hpd)
  have : Algebra.FormallySmooth A Aₚ := Algebra.FormallySmooth.of_isLocalization p.primeCompl
  have : Algebra.IsSmoothAt A q := Algebra.FormallySmooth.comp A Aₚ C
  exact Algebra.IsSmoothAt.exists_notMem_smooth A q

/-- Stacks 0FCX in the source's form: let `A → B` be a flat finite type ring map of Noetherian
rings. If the multiplication map `B ⊗[A] B → B` is a perfect ring map, for a certified derived
tensor product on a model of `D(B ⊗[A] B)`, then `B` is a smooth `A`-algebra. A perfect diagonal
gives `B` finite projective dimension over `B ⊗[A] B`, so this is
`StacksDraft.Smooth.smooth_of_flat_of_hasProjectiveDimensionLT_diagonal`. -/
public theorem smooth_of_flat_of_isPerfect_diagonal
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FiniteType A B]
    [HasDerivedCategory.{w} (ModuleCat.{v} (TensorProduct A B B))]
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring (TensorProduct A B B))
    (hperfect :
      letI := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom.toAlgebra
      RingHom.IsPerfectRingMap (TensorProduct A B B) B D.tensor D.comparison D.isLeftDerived) :
    Algebra.Smooth A B := by
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_finiteType A B
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  exact smooth_of_flat_of_hasProjectiveDimensionLT_diagonal A B
    (exists_hasProjectiveDimensionLT_diagonal A B D hperfect)

end StacksDraft.Smooth

end
