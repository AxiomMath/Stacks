module

public import Mathlib
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Unramified.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.FieldTheory.SeparableAlgebraic.Localization
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.CohenMacaulay.LocusBaseChange
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.Localization
public import StacksFrontier.RingTheory.GeometricallyNormal.Separable
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyReduced.Separable
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.Reduced
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Serre.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Serre.FlatAscent
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.CohenMacaulay.Support
public import StacksFrontier.RingTheory.FormalFibres.Examples.GeometricallyReduced

@[expose] public section

/-!
# Formal fibre properties: `(R_n)` after finite field extensions

Stacks Project, Chapter 15 "More on Algebra". The tag treated here is

0BIZ.

## Tag 0BIZ — Serre's condition `(R_n)` after finite field extensions

Fix a nonnegative integer `n`. The property of a map from a field `k` to a Noetherian ring `R`
that every finite field extension of `k` makes the corresponding scalar extension of `R` satisfy
Serre's condition `(R_n)` has properties (A)--(E) used in the study of formal fibres.

### Main definitions

No new definitions are introduced.

### Main results

* `propertyRk_after_finiteExtensions_satisfies_formalFibre_properties`: the form of `(R_n)`
  after finite field extensions satisfies properties (A)--(E).

### Implementation notes

The scalar extension is written with the extending field on the left. A regular ring map is
expressed as a flat map whose fibres are geometrically regular. The fibre of `A → B` at `p` is
`p.Fiber B = κ(p) ⊗[A] B`, and a separable algebraic extension is `Algebra.IsSeparable`.

### References

* [Stacks Project, Tag 0BIZ](https://stacks.math.columbia.edu/tag/0BIZ)

-/

/-! ### Stacks Tag 0BIZ -/

section

section

set_option maxRecDepth 4096

@[expose] public section

open scoped TensorProduct

universe u v w x

/-- Serre's condition `(R_n)` is preserved by localization. -/
private theorem hasPropertyRk_of_isLocalization {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (n : ℕ) (h : HasPropertyRk R n) : HasPropertyRk S n := by
  intro q _ hq
  let p : Ideal R := q.comap (algebraMap R S)
  have : p.IsPrime := inferInstance
  have hp : p.height ≤ (n : ℕ∞) := by
    rw [show p.height = q.height from IsLocalization.height_under M q]
    exact hq
  have : IsRegularLocalRing (Localization.AtPrime p) := h p hp
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).toRingEquiv

/-- Serre's condition `(R_n)` descends along a faithfully flat homomorphism of Noetherian
rings. -/
private theorem hasPropertyRk_of_faithfullyFlat {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [IsNoetherianRing S] (n : ℕ) (h : HasPropertyRk S n) : HasPropertyRk R n :=
  (isNoetherianRing_and_isRegularLocalRing_atPrime_of_faithfullyFlat
    (S := S) (k := (n : ℕ∞)) h).2

/-- A regular ring satisfies every condition `(R_n)`. -/
private theorem hasPropertyRk_of_isRegularRing (R : Type u) [CommRing R]
    [IsRegularRing R] (n : ℕ) : HasPropertyRk R n :=
  fun p _ _ => IsRegularRing.isRegularLocalRing_localization p

/-- Serre's condition `(R_n)` is invariant under a ring equivalence. -/
private theorem hasPropertyRk_of_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) (n : ℕ)
    (h : HasPropertyRk R n) : HasPropertyRk S n := by
  intro p _ hp
  let q := p.comap e.toRingHom
  have : q.IsPrime := inferInstance
  have hq : q.height ≤ (n : ℕ∞) := by
    rw [show q.height = p.height from e.height_comap p]
    exact hp
  have : IsRegularLocalRing (Localization.AtPrime q) := h q hq
  exact IsRegularLocalRing.of_ringEquiv (Localization.localRingEquiv q p e rfl)

/-- Base change of a localization preserves `(R_n)` on the scalar extension. -/
private theorem hasPropertyRk_tensorProduct_of_isLocalization
    {k : Type u} {R : Type v} {R' : Type w} {K : Type x}
    [CommRing k] [CommRing R] [CommRing R'] [CommRing K]
    [Algebra k R] [Algebra R R'] [Algebra k R'] [IsScalarTower k R R']
    [Algebra k K] (M : Submonoid R) [IsLocalization M R'] (n : ℕ)
    (h : HasPropertyRk (K ⊗[k] R) n) : HasPropertyRk (K ⊗[k] R') n := by
  let : Algebra (K ⊗[k] R) (K ⊗[k] R') :=
    (Algebra.TensorProduct.map (AlgHom.id k K)
      (IsScalarTower.toAlgHom k R R')).toRingHom.toAlgebra
  have : IsScalarTower K (K ⊗[k] R) (K ⊗[k] R') := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K))) (K ⊗[k] R') :=
    IsLocalization.tensorProduct_tensorProduct_right k K M R'
      (by ext a; simp [RingHom.algebraMap_toAlgebra])
  exact hasPropertyRk_of_isLocalization
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K))) n h

/-- Regularity at a prime can be read after a localization that retains that prime. -/
private theorem isRegularLocalRing_of_isLocalization_of_hasPropertyRk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (n : ℕ)
    (p : Ideal R) [p.IsPrime] (hp : p.height ≤ (n : ℕ∞))
    (hdis : Disjoint (M : Set R) (p : Set R))
    (h : HasPropertyRk S n) : IsRegularLocalRing (Localization.AtPrime p) := by
  let q : Ideal S := p.map (algebraMap R S)
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S p inferInstance hdis
  have hqp : Ideal.under R q = p :=
    IsLocalization.under_map_of_isPrime_disjoint M S inferInstance hdis
  have hq : q.height ≤ (n : ℕ∞) := by
    rw [← IsLocalization.height_under M q, hqp]
    exact hp
  have : IsRegularLocalRing (Localization.AtPrime q) := h q hq
  have hloc : IsLocalization.AtPrime (Localization.AtPrime q) (Ideal.under R q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    simpa only [hqp] using hloc
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q)
      (Localization.AtPrime p)).toRingEquiv

/-- Serre's condition `(R_n)` can be checked on the localizations at all primes. -/
private theorem hasPropertyRk_iff_forall_atPrime (R : Type u) [CommRing R] (n : ℕ) :
    HasPropertyRk R n ↔ ∀ (p : Ideal R) [p.IsPrime],
      HasPropertyRk (Localization.AtPrime p) n := by
  constructor
  · intro h p _
    exact hasPropertyRk_of_isLocalization p.primeCompl n h
  · intro h p _ hp
    exact isRegularLocalRing_of_isLocalization_of_hasPropertyRk p.primeCompl n p hp
      (Set.disjoint_left.mpr fun _ hx => hx) (h p)

/-- The finite-extension `(R_n)` condition on every local ring of `R` implies it on `R`, for
one fixed extension field. -/
private theorem hasPropertyRk_tensorProduct_of_forall_atPrime
    {k : Type u} {R : Type v} {K : Type w}
    [CommRing k] [CommRing R] [CommRing K] [Algebra k R] [Algebra k K]
    (n : ℕ)
    (h : ∀ (p : Ideal R) [p.IsPrime],
      HasPropertyRk (K ⊗[k] Localization.AtPrime p) n) :
    HasPropertyRk (K ⊗[k] R) n := by
  intro q _ hq
  let p : Ideal R := q.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R)
  have : p.IsPrime := inferInstance
  let : Algebra (K ⊗[k] R) (K ⊗[k] Localization.AtPrime p) :=
    (Algebra.TensorProduct.map (AlgHom.id k K)
      (IsScalarTower.toAlgHom k R (Localization.AtPrime p))).toRingHom.toAlgebra
  have : IsScalarTower K (K ⊗[k] R) (K ⊗[k] Localization.AtPrime p) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  let M : Submonoid (K ⊗[k] R) :=
    p.primeCompl.map (Algebra.TensorProduct.includeRight (R := k) (A := K))
  have : IsLocalization M (K ⊗[k] Localization.AtPrime p) :=
    IsLocalization.tensorProduct_tensorProduct_right k K p.primeCompl _
      (by ext a; simp [RingHom.algebraMap_toAlgebra])
  have hdis : Disjoint (M : Set (K ⊗[k] R)) (q : Set (K ⊗[k] R)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, rfl⟩ hx
    exact ha hx
  exact isRegularLocalRing_of_isLocalization_of_hasPropertyRk M n q hq hdis (h p)

/-- Property (B): the finite-extension condition can be checked at all local rings. -/
private theorem propertyRk_after_finiteExtensions_iff_forall_atPrime
    (n : ℕ) (k : Type u) (R : Type v) [Field k] [CommRing R]
    [Algebra k R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
        HasPropertyRk (K ⊗[k] Localization.AtPrime p) n) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
        HasPropertyRk (K ⊗[k] R) n := by
  constructor
  · intro h K _ _ _
    exact hasPropertyRk_tensorProduct_of_forall_atPrime n (fun p _ => h p K)
  · intro h p _ K _ _ _
    exact hasPropertyRk_tensorProduct_of_isLocalization p.primeCompl n (h K)

/-- Finite extension fields in any universe can be tested in the universe of the base field. -/
private theorem hasPropertyRk_tensorProduct_of_finite_anyUniverse
    (n : ℕ) (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
      HasPropertyRk (K ⊗[k] R) n)
    (L : Type w) [Field L] [Algebra k L] [FiniteDimensional k L] :
    HasPropertyRk (L ⊗[k] R) n := by
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  let f : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  have : Module.Finite k ↥f.fieldRange := Module.Finite.equiv f.equivFieldRange.toLinearEquiv
  exact hasPropertyRk_of_ringEquiv
    (Algebra.TensorProduct.congr f.equivFieldRange.symm AlgEquiv.refl).toRingEquiv n
    (h ↥f.fieldRange)

/-- Property (A) when the first field extension is finite: a second finite extension is still
finite over the original ground field. -/
private theorem propertyRk_after_finiteExtensions_baseChange_of_finite
    (n : ℕ) (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    [FiniteDimensional k k']
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L],
      HasPropertyRk (L ⊗[k] R) n)
    (K : Type v) [Field K] [Algebra k' K] [FiniteDimensional k' K] :
    HasPropertyRk (K ⊗[k'] (k' ⊗[k] R)) n := by
  let : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional k K := Module.Finite.trans k' K
  exact hasPropertyRk_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange k k' K K R).symm.toRingEquiv n
    (hasPropertyRk_tensorProduct_of_finite_anyUniverse n k R h K)

/-- Serre's condition `(R_n)` ascends along a smooth map of Noetherian rings. -/
private theorem hasPropertyRk_of_smooth (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.Smooth R S] (n : ℕ) (h : HasPropertyRk R n) : HasPropertyRk S n := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply property_Rk_of_flat_of_fibre_of_base R S n ?_ h
  intro p _
  have : IsRegularRing (p.Fiber S) :=
    Algebra.isRegularRing_of_smooth p.ResidueField (p.Fiber S)
  have : IsRegularRing (fibreRing R S p) :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm R p.ResidueField S).toRingEquiv
  exact hasPropertyRk_of_isRegularRing _ n

/-- Scalar extension by an essentially finite type field extension preserves Noetherianness. -/
@[sga "5 V 5.1.5" "special case"]
private theorem isNoetherianRing_tensorProduct_essFiniteType_field
    (k : Type u) (K : Type v) (R : Type w)
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R]
    [Algebra.EssFiniteType k K] [IsNoetherianRing R] :
    IsNoetherianRing (K ⊗[k] R) := by
  have : IsNoetherianRing (R ⊗[k] K) :=
    Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm k R K).toRingEquiv

/-- A smooth algebra followed by a localization preserves `(R_n)` after scalar extension. -/
private theorem hasPropertyRk_tensorProduct_of_smooth_of_isLocalization
    (R : Type u) (C : Type v) (B : Type w) (L : Type w)
    [CommRing R] [CommRing C] [CommRing B] [CommRing L]
    [Algebra R C] [Algebra R B] [Algebra R L] [Algebra B L]
    [IsScalarTower R B L] [Algebra.Smooth R B] [IsNoetherianRing C]
    (n : ℕ) (hC : HasPropertyRk C n)
    (M : Submonoid B) [IsLocalization M L] :
    HasPropertyRk (C ⊗[R] L) n := by
  have : Algebra.Smooth C (C ⊗[R] B) := Algebra.Smooth.baseChange R B C
  have hCB : HasPropertyRk (C ⊗[R] B) n :=
    hasPropertyRk_of_smooth C (C ⊗[R] B) n hC
  exact hasPropertyRk_tensorProduct_of_isLocalization M n hCB

/-- In a field-extension square with separable upper-right extension, `(R_n)` over the lower
field implies `(R_n)` over the upper-left field. -/
private theorem hasPropertyRk_tensorProduct_of_isSeparableExtension
    (n : ℕ) (k : Type u) (R : Type v) (K k' K' : Type w)
    [Field k] [CommRing R] [Algebra k R] [Field K] [Field k'] [Field K']
    [Algebra k K] [Algebra k k'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    [Algebra.EssFiniteType k' K'] [IsNoetherianRing (k' ⊗[k] R)]
    [IsNoetherianRing (K' ⊗[k] R)]
    (hC : HasPropertyRk (k' ⊗[k] R) n)
    (hsep : Algebra.IsSeparableExtension k' K') :
    HasPropertyRk (K ⊗[k] R) n := by
  obtain ⟨B, hBsm, hBfr⟩ :=
    ((Algebra.IsSeparableExtension.tfae_exists_smooth k' K').out 1 2).mp hsep
  have := hBsm
  have := hBfr
  have h23 : HasPropertyRk ((k' ⊗[k] R) ⊗[k'] K') n :=
    hasPropertyRk_tensorProduct_of_smooth_of_isLocalization k' (k' ⊗[k] R) ↥B K' n
      hC (nonZeroDivisors ↥B)
  have h3 : HasPropertyRk (K' ⊗[k] R) n :=
    hasPropertyRk_of_ringEquiv
      ((Algebra.TensorProduct.comm k' (k' ⊗[k] R) K').trans
        (Algebra.TensorProduct.cancelBaseChange k k' k' K' R)).toRingEquiv n h23
  have : IsNoetherianRing ((K ⊗[k] R) ⊗[K] K') :=
    isNoetherianRing_of_ringEquiv _
      ((Algebra.TensorProduct.cancelBaseChange k K K K' R).symm.trans
        (Algebra.TensorProduct.comm K (K ⊗[k] R) K').symm).toRingEquiv
  have h4 : HasPropertyRk ((K ⊗[k] R) ⊗[K] K') n :=
    hasPropertyRk_of_ringEquiv
      ((Algebra.TensorProduct.cancelBaseChange k K K K' R).symm.trans
        (Algebra.TensorProduct.comm K (K ⊗[k] R) K').symm).toRingEquiv n h3
  exact hasPropertyRk_of_faithfullyFlat n h4

/-- Finite field extensions suffice to test `(R_n)` after every finitely generated field
extension. -/
private theorem hasPropertyRk_tensorProduct_of_essFiniteType
    (n : ℕ) (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L],
      HasPropertyRk (L ⊗[k] R) n)
    (K : Type w) [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    HasPropertyRk (K ⊗[k] R) n := by
  obtain ⟨K', k', hfinK', -, hfink', -, hsep, -, -, -⟩ :=
    exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType
      k K (AlgebraicClosure K)
  have : Module.Finite K ↥K' := hfinK'
  have : Module.Finite k ↥k' := hfink'
  have hC : HasPropertyRk (↥k' ⊗[k] R) n :=
    hasPropertyRk_tensorProduct_of_finite_anyUniverse n k R h ↥k'
  have : Algebra.EssFiniteType K ↥K' := inferInstance
  have : Algebra.EssFiniteType k ↥K' := Algebra.EssFiniteType.comp k K ↥K'
  have : Algebra.EssFiniteType ↥k' ↥K' := Algebra.EssFiniteType.of_comp k ↥k' ↥K'
  have : IsNoetherianRing (↥k' ⊗[k] R) :=
    isNoetherianRing_tensorProduct_essFiniteType_field k ↥k' R
  have : IsNoetherianRing (↥K' ⊗[k] R) :=
    isNoetherianRing_tensorProduct_essFiniteType_field k ↥K' R
  exact hasPropertyRk_tensorProduct_of_isSeparableExtension n k R K ↥k' ↥K' hC hsep

/-- The ring isomorphism `(A ⊗[k] K) ⊗[A] B ≃+* K ⊗[k] B`. -/
private def tensorTensorRingEquiv (k : Type u) (A : Type v) (B : Type w) (K : Type x)
    [CommRing k] [CommRing A] [CommRing B] [CommRing K]
    [Algebra k A] [Algebra k B] [Algebra k K] [Algebra A B] [IsScalarTower k A B] :
    ((A ⊗[k] K) ⊗[A] B) ≃+* (K ⊗[k] B) :=
  ((Algebra.TensorProduct.comm A B (A ⊗[k] K)).symm.trans
    (Algebra.TensorProduct.cancelBaseChange k A A B K)).toRingEquiv.trans
      (Algebra.TensorProduct.comm k B K).toRingEquiv

/-- Faithfully flat descent of `(R_n)` commutes with arbitrary extension of scalars. -/
private theorem hasPropertyRk_tensorProduct_of_faithfullyFlat
    {k : Type u} {A : Type v} {B : Type w} {K : Type x}
    [CommRing k] [CommRing A] [CommRing B] [CommRing K]
    [Algebra k A] [Algebra k B] [Algebra k K]
    [Algebra A B] [IsScalarTower k A B] [Module.FaithfullyFlat A B]
    [IsNoetherianRing (K ⊗[k] B)] (n : ℕ)
    (h : HasPropertyRk (K ⊗[k] B) n) : HasPropertyRk (K ⊗[k] A) n := by
  let e := tensorTensorRingEquiv k A B K
  have : IsNoetherianRing ((A ⊗[k] K) ⊗[A] B) :=
    isNoetherianRing_of_ringEquiv _ e.symm
  have hAB : HasPropertyRk ((A ⊗[k] K) ⊗[A] B) n :=
    hasPropertyRk_of_ringEquiv e.symm n h
  have hA : HasPropertyRk (A ⊗[k] K) n := hasPropertyRk_of_faithfullyFlat n hAB
  exact hasPropertyRk_of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv n hA


/-- Property (D): the finite-extension condition on fibres descends along a faithfully flat
map. -/
private theorem propertyRk_fibres_of_faithfullyFlat
    (n : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Module.Flat A B] [Module.FaithfullyFlat B C]
    (h : ∀ (p : Ideal A) [p.IsPrime],
      ∀ (K : Type u) [Field K] [Algebra p.ResidueField K]
        [FiniteDimensional p.ResidueField K],
        HasPropertyRk (K ⊗[p.ResidueField] p.Fiber C) n)
    (p : Ideal A) [p.IsPrime]
    (K : Type u) [Field K] [Algebra p.ResidueField K]
      [FiniteDimensional p.ResidueField K] :
    HasPropertyRk (K ⊗[p.ResidueField] p.Fiber B) n := by
  let : Algebra A K :=
    ((algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)).toAlgebra
  have : IsScalarTower A p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber C) :=
    isNoetherianRing_finite_extension_fiber A C p K
  let eC := Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField K C
  have : IsNoetherianRing (K ⊗[A] C) :=
    isNoetherianRing_of_ringEquiv _ eC.toRingEquiv
  have hKC : HasPropertyRk (K ⊗[A] C) n :=
    hasPropertyRk_of_ringEquiv eC.toRingEquiv n (h p K)
  have hKB : HasPropertyRk (K ⊗[A] B) n :=
    hasPropertyRk_tensorProduct_of_faithfullyFlat n hKC
  exact hasPropertyRk_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField K B).symm.toRingEquiv
    n hKB

/-- The fibre of a base changed map is regular when the original fibre is geometrically
regular and the new residue field is essentially of finite type over the old one. -/
private theorem isRegularRing_fiber_baseChange
    (B : Type u) (C : Type v) (D : Type w)
    [CommRing B] [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    [Algebra.EssFiniteType B D]
    (q : Ideal B) [q.IsPrime] (Q : Ideal D) [Q.IsPrime] [Q.LiesOver q]
    [Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C)] :
    IsRegularRing (Q.Fiber (D ⊗[B] C)) := by
  let : Algebra q.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.mapₐ q Q (Algebra.ofId B D) (Ideal.over_def Q q)).toRingHom.toAlgebra
  have : IsScalarTower B q.ResidueField Q.ResidueField :=
    .of_algebraMap_eq fun x =>
      ((Ideal.ResidueField.mapₐ q Q (Algebra.ofId B D)
        (Ideal.over_def Q q)).commutes x).symm
  have : Algebra.EssFiniteType B Q.ResidueField :=
    Algebra.EssFiniteType.comp B D Q.ResidueField
  have : Algebra.EssFiniteType q.ResidueField Q.ResidueField :=
    Algebra.EssFiniteType.of_comp B q.ResidueField Q.ResidueField
  have : IsRegularRing (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular q.ResidueField (q.Fiber C)
      Q.ResidueField
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.cancelBaseChange B q.ResidueField q.ResidueField
      Q.ResidueField C).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange B D D Q.ResidueField C).symm.toRingEquiv)

/-- `(R_n)` ascends along an essentially finite type base change of a flat map with
geometrically regular fibres. -/
private theorem hasPropertyRk_of_flat_geometricFibres_baseChange
    (B : Type u) (C : Type v) (D : Type w)
    [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] [Algebra B D] [Module.Flat B C]
    [Algebra.EssFiniteType B D]
    [IsNoetherianRing D] [IsNoetherianRing (D ⊗[B] C)]
    (n : ℕ) (hD : HasPropertyRk D n)
    (hgeo : ∀ (q : Ideal B) [q.IsPrime],
      Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C)) :
    HasPropertyRk (D ⊗[B] C) n := by
  apply property_Rk_of_flat_of_fibre_of_base D (D ⊗[B] C) n ?_ hD
  intro Q _
  let q : Ideal B := Q.comap (algebraMap B D)
  have : q.IsPrime := inferInstance
  have : Q.LiesOver q := ⟨rfl⟩
  have : Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := hgeo q
  have : IsRegularRing (Q.Fiber (D ⊗[B] C)) :=
    isRegularRing_fiber_baseChange B C D q Q
  have : IsRegularRing (fibreRing D (D ⊗[B] C) Q) :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm D Q.ResidueField (D ⊗[B] C)).toRingEquiv
  exact hasPropertyRk_of_isRegularRing _ n

/-- Property (C): a flat map with geometrically regular fibres preserves the finite-extension
condition on fibres after composition. -/
private theorem propertyRk_fibres_of_flat_geometricFibres
    (n : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Module.Flat A B] [Module.Flat B C]
    (hB : ∀ (p : Ideal A) [p.IsPrime],
      ∀ (K : Type u) [Field K] [Algebra p.ResidueField K]
        [FiniteDimensional p.ResidueField K],
        HasPropertyRk (K ⊗[p.ResidueField] p.Fiber B) n)
    (hgeo : ∀ (q : Ideal B) [q.IsPrime],
      Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C))
    (p : Ideal A) [p.IsPrime]
    (K : Type u) [Field K] [Algebra p.ResidueField K]
      [FiniteDimensional p.ResidueField K] :
    HasPropertyRk (K ⊗[p.ResidueField] p.Fiber C) n := by
  let : Algebra A K :=
    ((algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)).toAlgebra
  have : IsScalarTower A p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.EssFiniteType A K :=
    Algebra.EssFiniteType.comp A p.ResidueField K
  have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber B) :=
    isNoetherianRing_finite_extension_fiber A B p K
  have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber C) :=
    isNoetherianRing_finite_extension_fiber A C p K
  let eB := Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField K B
  let eC := Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField K C
  have : IsNoetherianRing (K ⊗[A] B) :=
    isNoetherianRing_of_ringEquiv _ eB.toRingEquiv
  have : IsNoetherianRing (K ⊗[A] C) :=
    isNoetherianRing_of_ringEquiv _ eC.toRingEquiv
  have hKB : HasPropertyRk (K ⊗[A] B) n :=
    hasPropertyRk_of_ringEquiv eB.toRingEquiv n (hB p K)
  have hD : HasPropertyRk (B ⊗[A] K) n :=
    hasPropertyRk_of_ringEquiv (Algebra.TensorProduct.comm A B K).symm.toRingEquiv n hKB
  have : IsNoetherianRing (B ⊗[A] K) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A B K).symm.toRingEquiv
  let eBC := tensorTensorRingEquiv A B C K
  have : IsNoetherianRing ((B ⊗[A] K) ⊗[B] C) :=
    isNoetherianRing_of_ringEquiv _ eBC.symm
  have hDC : HasPropertyRk ((B ⊗[A] K) ⊗[B] C) n :=
    hasPropertyRk_of_flat_geometricFibres_baseChange B C (B ⊗[A] K) n hD hgeo
  have hKC : HasPropertyRk (K ⊗[A] C) n := hasPropertyRk_of_ringEquiv eBC n hDC
  exact hasPropertyRk_of_ringEquiv eC.symm.toRingEquiv n hKC

/-- Property (A): the finite-extension condition persists after a finitely generated extension
of the ground field. -/
private theorem propertyRk_after_finiteExtensions_baseChange
    (n : ℕ) (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    [Algebra.EssFiniteType k k'] [IsNoetherianRing R]
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L],
      HasPropertyRk (L ⊗[k] R) n)
    (K : Type v) [Field K] [Algebra k' K] [FiniteDimensional k' K] :
    HasPropertyRk (K ⊗[k'] (k' ⊗[k] R)) n := by
  let : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k k' K
  exact hasPropertyRk_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange k k' k' K R).symm.toRingEquiv n
    (hasPropertyRk_tensorProduct_of_essFiniteType n k R h K)

/-- Smooth ascent of `(R_n)` commutes with extension of scalars. -/
private theorem hasPropertyRk_tensorProduct_of_smooth
    {k : Type u} {A : Type v} {B : Type w} {K : Type x}
    [CommRing k] [CommRing A] [CommRing B] [CommRing K]
    [Algebra k A] [Algebra k B] [Algebra k K]
    [Algebra A B] [IsScalarTower k A B] [Algebra.Smooth A B]
    [IsNoetherianRing (K ⊗[k] A)] (n : ℕ)
    (h : HasPropertyRk (K ⊗[k] A) n) : HasPropertyRk (K ⊗[k] B) n := by
  let e := tensorTensorRingEquiv k A B K
  have : IsNoetherianRing (A ⊗[k] K) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k K A).toRingEquiv
  have hA : HasPropertyRk (A ⊗[k] K) n :=
    hasPropertyRk_of_ringEquiv (Algebra.TensorProduct.comm k K A).toRingEquiv n h
  exact hasPropertyRk_of_ringEquiv e n
    (hasPropertyRk_of_smooth (A ⊗[k] K) ((A ⊗[k] K) ⊗[A] B) n hA)

/-- Property (E) for a finite separable extension of the ground field. -/
private theorem propertyRk_after_finiteExtensions_of_finite_isSeparable
    (n : ℕ) (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k R] [Algebra k' R] [IsScalarTower k k' R]
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [IsNoetherianRing R]
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L],
      HasPropertyRk (L ⊗[k] R) n)
    (K : Type x) [Field K] [Algebra k' K] [FiniteDimensional k' K] :
    HasPropertyRk (K ⊗[k'] R) n := by
  let A := k' ⊗[k] R
  let f : A →ₐ[k'] R := Algebra.TensorProduct.lift (Algebra.ofId k' R)
    (AlgHom.id k R) (fun _ _ => Commute.all _ _)
  let : Algebra A R := f.toRingHom.toAlgebra
  have : IsScalarTower k' A R := .of_algebraMap_eq fun x => (f.commutes x).symm
  have : IsNoetherianRing A :=
    isNoetherianRing_tensorProduct_essFiniteType_field k k' R
  have : Algebra.Smooth A R := by
    let : Algebra R A := Algebra.TensorProduct.rightAlgebra
    have : IsScalarTower R A R := .of_algebraMap_eq fun x => by
      change x = algebraMap k' R 1 * x
      simp only [map_one, one_mul]
    have : Algebra.FormallyUnramified k k' :=
      Algebra.FormallyUnramified.of_isSeparable k k'
    let e : (R ⊗[k] k') ≃ₐ[R] A :=
      { (Algebra.TensorProduct.comm k R k').toRingEquiv with
        commutes' r := by
          change (Algebra.TensorProduct.comm k R k') (r ⊗ₜ[k] 1) = 1 ⊗ₜ[k] r
          exact Algebra.TensorProduct.comm_tmul _ _ _ }
    have : Algebra.FormallyUnramified R A := Algebra.FormallyUnramified.of_equiv e
    have : Algebra.FormallySmooth A R := Algebra.FormallySmooth.of_restrictScalars R A R
    have : Algebra.FiniteType A R := Algebra.FiniteType.of_surjective
      (Algebra.ofId A R) (fun r => ⟨1 ⊗ₜ[k] r, by
        change algebraMap k' R 1 * r = r
        simp only [map_one, one_mul]⟩)
    exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' K := .of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional k K := Module.Finite.trans k' K
  let e := Algebra.TensorProduct.cancelBaseChange k k' k' K R
  have : IsNoetherianRing (K ⊗[k] R) :=
    isNoetherianRing_tensorProduct_essFiniteType_field k K R
  have : IsNoetherianRing (K ⊗[k'] A) := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  exact hasPropertyRk_tensorProduct_of_smooth n
    (hasPropertyRk_of_ringEquiv e.symm.toRingEquiv n
      (hasPropertyRk_tensorProduct_of_finite_anyUniverse n k R h K))

/-- A finite basis over an algebraic extension descends to a finite intermediate field
containing the multiplication and unit structure constants. -/
private theorem exists_finite_subalgebra_basis
    {k : Type u} {l : Type v} [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] {K : Type w} [Ring K] [Algebra l K]
    {σ : Type*} [Finite σ] (b : Module.Basis σ l K) :
    ∃ (m : IntermediateField k l), Module.Finite k m ∧
      ∃ (B : Subalgebra m K) (c : Module.Basis σ m B), ∀ s, (c s : K) = b s := by
  let a : (σ × σ × σ) ⊕ σ → l :=
    Sum.elim (fun t => b.repr (b t.1 * b t.2.1) t.2.2) (fun t => b.repr 1 t)
  let m := IntermediateField.adjoin k (Set.range a)
  have hm : Module.Finite k m := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact ⟨m, hm, Stacks.GeometricallyRegular.FieldColimit.exists_subalgebra_basis_of_repr_mem
    m.toSubfield b (fun p q r ↦ IntermediateField.subset_adjoin k _ ⟨Sum.inl (p, q, r), rfl⟩)
    (fun r ↦ IntermediateField.subset_adjoin k _ ⟨Sum.inr r, rfl⟩)⟩

/-- Property (E): the finite-extension condition persists upon passing to a separable
algebraic extension of the ground field. -/
private theorem propertyRk_after_finiteExtensions_of_isSeparable
    (n : ℕ) (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k R] [Algebra k' R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R]
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L],
      HasPropertyRk (L ⊗[k] R) n)
    (K : Type v) [Field K] [Algebra k' K] [FiniteDimensional k' K] :
    HasPropertyRk (K ⊗[k'] R) n := by
  obtain ⟨m, hm, B, c, hc⟩ := exists_finite_subalgebra_basis (k := k) (Module.finBasis k' K)
  have : Module.Finite k m := hm
  have : Module.Finite m B := .of_basis c
  let : Field B := (isField_of_isIntegral_of_isField' (Field.toIsField m)).toField
  have hB : HasPropertyRk (B ⊗[m] R) n :=
    propertyRk_after_finiteExtensions_of_finite_isSeparable n k m R h B
  let e : (k' ⊗[m] B) ≃ₐ[k'] K :=
    AlgEquiv.ofBijective
      (Algebra.TensorProduct.lift (Algebra.ofId k' K) (Subalgebra.val B)
        (fun _ _ => Commute.all _ _))
      (Stacks.GeometricallyRegular.FieldColimit.lift_bijective_of_basis (R := m)
        (Module.finBasis k' K) B.val c hc)
  exact hasPropertyRk_of_ringEquiv
    ((Algebra.TensorProduct.comm m B R).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange m k' k' R B).symm.trans
        ((Algebra.TensorProduct.congr AlgEquiv.refl e).trans
          (Algebra.TensorProduct.comm k' R K))).toRingEquiv) n hB

/-- For fixed `n`, the property that every finite extension of the ground field makes an algebra
satisfy Serre's condition `(R_n)` satisfies properties (A)--(E) for formal fibres: base change by
a finitely generated field extension, detection on local rings, ascent along a regular map,
faithfully flat descent, and separable algebraic extension of the base field. -/
@[stacks 0BIZ]
public theorem propertyRk_after_finiteExtensions_satisfies_formalFibre_properties (n : ℕ) :
    (∀ (k : Type u) (k' : Type v) (R : Type w) [Field k] [Field k'] [CommRing R]
      [Algebra k k'] [Algebra k R] [Algebra.EssFiniteType k k'] [IsNoetherianRing R],
      (∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
        HasPropertyRk (K ⊗[k] R) n) →
      ∀ (K : Type v) [Field K] [Algebra k' K] [FiniteDimensional k' K],
        HasPropertyRk (K ⊗[k'] (k' ⊗[k] R)) n) ∧
    (∀ (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ (p : Ideal R) [p.IsPrime],
        ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
          HasPropertyRk (K ⊗[k] Localization.AtPrime p) n) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
        HasPropertyRk (K ⊗[k] R) n) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ (p : Ideal A) [p.IsPrime],
        ∀ (K : Type u) [Field K] [Algebra p.ResidueField K]
          [FiniteDimensional p.ResidueField K],
          HasPropertyRk (K ⊗[p.ResidueField] p.Fiber B) n) →
      (∀ (q : Ideal B) [q.IsPrime],
        Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C)) →
      ∀ (p : Ideal A) [p.IsPrime],
        ∀ (K : Type u) [Field K] [Algebra p.ResidueField K]
          [FiniteDimensional p.ResidueField K],
          HasPropertyRk (K ⊗[p.ResidueField] p.Fiber C) n) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ (p : Ideal A) [p.IsPrime],
        ∀ (K : Type u) [Field K] [Algebra p.ResidueField K]
          [FiniteDimensional p.ResidueField K],
          HasPropertyRk (K ⊗[p.ResidueField] p.Fiber C) n) →
      ∀ (p : Ideal A) [p.IsPrime],
        ∀ (K : Type u) [Field K] [Algebra p.ResidueField K]
          [FiniteDimensional p.ResidueField K],
          HasPropertyRk (K ⊗[p.ResidueField] p.Fiber B) n) ∧
    (∀ (k : Type u) (k' : Type v) (R : Type w)
      [Field k] [Field k'] [CommRing R]
      [Algebra k k'] [Algebra k R] [Algebra k' R] [IsScalarTower k k' R]
      [Algebra.IsSeparable k k'] [IsNoetherianRing R],
      (∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
        HasPropertyRk (K ⊗[k] R) n) →
      ∀ (K : Type v) [Field K] [Algebra k' K] [FiniteDimensional k' K],
        HasPropertyRk (K ⊗[k'] R) n) :=
  ⟨propertyRk_after_finiteExtensions_baseChange n,
    propertyRk_after_finiteExtensions_iff_forall_atPrime n,
    propertyRk_fibres_of_flat_geometricFibres n,
    propertyRk_fibres_of_faithfullyFlat n,
    propertyRk_after_finiteExtensions_of_isSeparable n⟩

end

end

end

end
