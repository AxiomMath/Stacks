module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksFrontier.RingTheory.Dualizing.Ubiquity
public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary

/-!
# The depth–dimension inequality on a punctured cone

Let `π : L → P` be the cone of an invertible sheaf on a scheme `P`, let `U ⊆ L` be the
punctured cone and let `A` be the section ring, so that `U` is an open subscheme of `Spec A`.
A coherent sheaf `𝓕` on `P` pulls back to `𝓕_U = (π|_U)^*𝓕` on `U`, which is `M̃|_U` for a
finite `A`-module `M`.

A bound `depth(𝓕_p) + dim({p}‾) > σ` at the points `p ∈ P` outside the zero scheme of a section
gives the bound `depth(M_𝔭) + dim((A/𝔭)_𝔮) > σ + 1` at the relevant pairs of primes of `A` that
appears in Faltings' annihilator theorem
(`Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff`, Stacks 0EFC). Since
`π|_U` is smooth of relative dimension `1`, a point `u` of `U` over `p` is either the generic
point of the fibre, where `depth(𝓕_{U,u}) = depth(𝓕_p)` and `dim({u}‾) = dim({p}‾) + 1`, or a
closed point of the fibre, where `depth(𝓕_{U,u}) = depth(𝓕_p) + 1` and `dim({u}‾) = dim({p}‾)`.
Either way the sum rises by exactly one.

## Main definitions

* `Stacks.Algebraization.localizedDepth` — the depth `depth(M_𝔭)` of a localization of `M`.
* `Stacks.Algebraization.relativeDimAt` — the dimension `dim((A/𝔭)_𝔮)` of the local ring of
  `V(𝔭)` at a point `𝔮` of `V(𝔭)`.
* `Stacks.Algebraization.depthAddRelativeDim` — the sum of the two, in the extended integers.

## Main results

* `Stacks.Algebraization.lt_depthAddRelativeDim_of_fibreSplitting` — the fibre dichotomy of a
  smooth morphism of relative dimension one carries a bound `> σ` on the base to the bound
  `> σ + 1`.
* `Stacks.Algebraization.exists_ideal_le_annihilator_localCohomology_of_fibreSplitting` — under
  the fibre dichotomy and the bound on the base, an ideal annihilating the local cohomology of `M`
  in degrees at most `σ + 1`.
* `Stacks.Algebraization.exists_isDualizingComplex_of_finiteType_field` — a finite type algebra
  over a field has a dualizing complex.
* `Stacks.Algebraization.exists_ideal_le_annihilator_localCohomology_of_fibreSplitting_finiteType`
  — the same conclusion for a finite type algebra over a field, with no dualizing-complex
  hypothesis left.

## Implementation notes

The base is abstract: a map `proj` from the primes of `A` to an index type `P`, together with
the two functions `baseDepth` and `baseDim` recording `depth(𝓕_p)` and `dim({p}‾)` at a point
of the base. Nothing about `P` is used beyond those three, so the translation applies to any
situation producing the fibre dichotomy, and the geometry of the cone enters only through the
hypothesis `hsplit`. That hypothesis is the source's dichotomy verbatim: smoothness of `π|_U`,
its relative dimension and the splitting of a fibre into its generic point and its closed
points are what produce it, and it is not discharged here.

The source's `dim({u}‾)` is already written as `dim((A/𝔭)_𝔮)`, the dimension of the local ring
of `V(𝔭)` at `𝔮`; the two agree in the situation of 0EL1 because every point of `Z = Spec A₀`
is closed, and that identification is part of `hsplit` rather than a separate step.

Depth takes values in `ℕ∞` and Krull dimension in `WithBot ℕ∞`; both are placed in `EInt` by
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt`, as in the
statement of Faltings' theorem.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC), Faltings' annihilator
  theorem.
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG), the cone.
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K), dualizing complexes
  over an algebra essentially of finite type.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.Algebraization

/-! ### Arithmetic in the extended integers -/

/-- A strict lower bound by an integer survives adding one to both sides. -/
private theorem intCast_add_one_lt_add_one {s : ℤ} {x : EInt} (h : (s : EInt) < x) :
    ((s + 1 : ℤ) : EInt) < x + ((1 : ℤ) : EInt) := by
  induction x using WithBotTop.rec with
  | bot => exact absurd h (by simp)
  | top =>
    rw [show ((⊤ : EInt)) + ((1 : ℤ) : EInt) = (⊤ : EInt) from rfl]
    change (WithBot.some (WithTop.some (s + 1))) < (WithBot.some (⊤ : WithTop ℤ))
    exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  | coe y =>
    rw [← Stacks.Chow.coe_add_coe_eq_coe_add]
    exact WithBotTop.coe_lt_coe.2 (by have := WithBotTop.coe_lt_coe.1 h; omega)

/-- The dichotomy of a fibre of relative dimension one raises the sum of a depth and a
dimension by exactly one, whichever of the two summands the extra one falls on. -/
private theorem lt_add_one_of_splitting {d d' : ℕ∞} {D D' : WithBot ℕ∞} {s : ℤ}
    (hsplit : (d' = d ∧ D' = D + 1) ∨ (d' = d + 1 ∧ D' = D))
    (hbase : enatToEInt d + krullDimToEInt D > (s : EInt)) :
    enatToEInt d' + krullDimToEInt D' > ((s + 1 : ℤ) : EInt) := by
  have key : enatToEInt d' + krullDimToEInt D' =
      (enatToEInt d + krullDimToEInt D) + ((1 : ℤ) : EInt) := by
    obtain ⟨hd, hD⟩ | ⟨hd, hD⟩ := hsplit
    · rw [hd, hD, krullDimToEInt_add_one, intCast_one_eq_one, add_assoc]
    · rw [hd, hD, enatToEInt_add_one, intCast_one_eq_one, add_right_comm]
  rw [key]
  exact intCast_add_one_lt_add_one hbase

/-! ### The two quantities of Faltings' annihilator theorem -/

/-- The depth `depth(M_𝔭)` of the localization of `M` at a prime `𝔭`, taken over the local ring
`A_𝔭` along its maximal ideal. -/
public def localizedDepth (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    (p : PrimeSpectrum A) : ℕ∞ :=
  Module.depth (Localization.AtPrime p.asIdeal)
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule p.asIdeal.primeCompl M)

/-- The dimension `dim((A/𝔭)_𝔮)` of the local ring of the closed subscheme `V(𝔭)` at a point
`𝔮`, presented as the Krull dimension of `A_𝔮` modulo the ideal generated by `𝔭`. -/
public def relativeDimAt (A : Type u) [CommRing A] (p q : PrimeSpectrum A) : WithBot ℕ∞ :=
  ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
    p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))

/-- The sum `depth(M_𝔭) + dim((A/𝔭)_𝔮)`, read in the extended integers. -/
public def depthAddRelativeDim (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M]
    [Module A M] (p q : PrimeSpectrum A) : EInt :=
  enatToEInt (localizedDepth A M p) + krullDimToEInt (relativeDimAt A p q)

/-! ### The translation -/

/-- If at every relevant prime the depth and the relative dimension of `M` are those of the base
with one extra unit distributed between them — the dichotomy produced by a fibre of a smooth
morphism of relative dimension one — then a bound `> s` on the base becomes the bound `> s + 1`
on `Spec A`. -/
public theorem lt_depthAddRelativeDim_of_fibreSplitting
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
    {T T' : Set (PrimeSpectrum A)} {P : Type v} (proj : PrimeSpectrum A → P)
    (baseDepth : P → ℕ∞) (baseDim : P → WithBot ℕ∞) (s : ℤ)
    (hsplit : ∀ p : PrimeSpectrum A, p ∉ T' → ∀ q : PrimeSpectrum A, q ∈ T →
      p.asIdeal ≤ q.asIdeal →
      (localizedDepth A M p = baseDepth (proj p) ∧
          relativeDimAt A p q = baseDim (proj p) + 1) ∨
        (localizedDepth A M p = baseDepth (proj p) + 1 ∧
          relativeDimAt A p q = baseDim (proj p)))
    (hbase : ∀ p : PrimeSpectrum A, p ∉ T' →
      enatToEInt (baseDepth (proj p)) + krullDimToEInt (baseDim (proj p)) > (s : EInt))
    (p : PrimeSpectrum A) (hp : p ∉ T') (q : PrimeSpectrum A) (hq : q ∈ T)
    (hpq : p.asIdeal ≤ q.asIdeal) :
    depthAddRelativeDim A M p q > ((s + 1 : ℤ) : EInt) :=
  lt_add_one_of_splitting (hsplit p hp q hq hpq) (hbase p hp)

/-- Given a dualizing complex for `A`, the fibre dichotomy of the punctured cone together with
the depth–dimension bound on the base gives an ideal `J` with `V(J) ⊆ T'` annihilating the local
cohomology of `M` with support in `T` in degrees at most `s + 1`. -/
public theorem exists_ideal_le_annihilator_localCohomology_of_fibreSplitting
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T T' : Set (PrimeSpectrum A)) (hTT' : T ⊆ T')
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    {P : Type v} (proj : PrimeSpectrum A → P)
    (baseDepth : P → ℕ∞) (baseDim : P → WithBot ℕ∞) (s : ℤ) (hs : 0 ≤ s)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hsplit : ∀ p : PrimeSpectrum A, p ∉ T' → ∀ q : PrimeSpectrum A, q ∈ T →
      p.asIdeal ≤ q.asIdeal →
      (localizedDepth A M p = baseDepth (proj p) ∧
          relativeDimAt A p q = baseDim (proj p) + 1) ∨
        (localizedDepth A M p = baseDepth (proj p) + 1 ∧
          relativeDimAt A p q = baseDim (proj p)))
    (hbase : ∀ p : PrimeSpectrum A, p ∉ T' →
      enatToEInt (baseDepth (proj p)) + krullDimToEInt (baseDim (proj p)) > (s : EInt)) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ i : ℤ, i ≤ s + 1 → J ≤ Module.annihilator A
        (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) :=
  (Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff A M T T' hTT' hT hT'
      (s + 1) (by omega) omega homega).mpr
    fun p q hp hq hpq ↦
      lt_depthAddRelativeDim_of_fibreSplitting proj baseDepth baseDim s hsplit hbase p hp q hq hpq

/-! ### Discharging the dualizing-complex hypothesis -/

/-- A finite type algebra over a field has a dualizing complex. -/
public theorem exists_isDualizingComplex_of_finiteType_field (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K := by
  obtain ⟨K, hK⟩ := Dualizing.exists_isDualizingComplex k
  obtain ⟨_hA, L, hL⟩ := Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType
    (Dualizing.isEssentiallyOfFiniteType_of_finiteType (A := k) (C := A) inferInstance) K hK
  exact ⟨L, hL⟩

/-- For a finite type algebra `A` over a field, the fibre dichotomy of the punctured cone together
with the depth–dimension bound on the base gives an ideal `J` with `V(J) ⊆ T'` annihilating the
local cohomology of `M` with support in `T` in degrees at most `s + 1`. -/
public theorem exists_ideal_le_annihilator_localCohomology_of_fibreSplitting_finiteType
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsNoetherianRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T T' : Set (PrimeSpectrum A)) (hTT' : T ⊆ T')
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    {P : Type v} (proj : PrimeSpectrum A → P)
    (baseDepth : P → ℕ∞) (baseDim : P → WithBot ℕ∞) (s : ℤ) (hs : 0 ≤ s)
    (hsplit : ∀ p : PrimeSpectrum A, p ∉ T' → ∀ q : PrimeSpectrum A, q ∈ T →
      p.asIdeal ≤ q.asIdeal →
      (localizedDepth A M p = baseDepth (proj p) ∧
          relativeDimAt A p q = baseDim (proj p) + 1) ∨
        (localizedDepth A M p = baseDepth (proj p) + 1 ∧
          relativeDimAt A p q = baseDim (proj p)))
    (hbase : ∀ p : PrimeSpectrum A, p ∉ T' →
      enatToEInt (baseDepth (proj p)) + krullDimToEInt (baseDim (proj p)) > (s : EInt)) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ i : ℤ, i ≤ s + 1 → J ≤ Module.annihilator A
        (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
  obtain ⟨omega, homega⟩ := exists_isDualizingComplex_of_finiteType_field k A
  exact exists_ideal_le_annihilator_localCohomology_of_fibreSplitting A M T T' hTT' hT hT'
    proj baseDepth baseDim s hs omega homega hsplit hbase

end Stacks.Algebraization

end
