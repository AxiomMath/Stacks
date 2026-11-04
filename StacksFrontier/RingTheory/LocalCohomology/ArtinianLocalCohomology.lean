module

public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.AlgebraicGeometry.Divisors.PuncturedSpectrumAffineCriterion.Artinian
public import StacksFrontier.RingTheory.LocalCohomology.CechModel
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# The descending chain condition for local cohomology at the maximal ideal

Let `(A, 𝔪)` be a Noetherian local ring. Stacks 0DX0 asserts that the local cohomology
`H^i_𝔪(M)` of a finite `A`-module satisfies the descending chain condition in every degree. This
file supplies two things: the reduction of that assertion to a statement about socles, and the
base case of the induction by which Stacks proves it.

The reduction is immediate once one knows that local cohomology modules are always power torsion.
By Stacks 08Z8 (2) an `A`-module has the descending chain condition exactly when it is
`𝔪`-power torsion and its socle is a finite-dimensional vector space over the residue field; and
`H^i_𝔪(M)` is `𝔪`-power torsion for free, because `RΓ_{V(𝔪)}` is by construction a functor into
the full subcategory of the derived category on the objects with `𝔪`-power-torsion cohomology. So
`IsArtinian A (H^i_𝔪(M))` is equivalent to finiteness of the socle of `H^i_𝔪(M)`, which is what
the Stacks induction actually produces.

The base case is the case of an `𝔪`-power-torsion coefficient module, and it is proved here
outright through the Čech model of Stacks 0A6R: if `𝔪 = (f_1, …, f_r)` and `M` is `𝔪`-power
torsion, then every localization `M_{f_{i_0} ⋯ f_{i_p}}` with `p ≥ 0` vanishes, because the
product of the inverted elements lies in `𝔪` and therefore kills each element of `M` after
raising it to a power. Hence the extended alternating Čech complex `C^•(f; M)` is concentrated in
degree zero, where it is `M`; a finite `𝔪`-power-torsion module over a Noetherian local ring is
Artinian; and the cohomology of a complex whose terms are Artinian is Artinian, being a
subquotient of a term.

## Main results

* `Stacks.LocalCohomology.isIPowerTorsion_localCohomologyModule` — `H^i_{V(I)}(M)` is always
  `I`-power torsion.
* `Stacks.LocalCohomology.isArtinian_localCohomologyModule_iff_hasFiniteSocle` — **the reduction
  of Stacks 0DX0 (1) to the finiteness of the socle**, valid for a coefficient module in any
  universe.
* `Stacks.LocalCohomology.isArtinian_homology_of_isArtinian_X` — the cohomology of a cochain
  complex of modules is Artinian in any degree whose term is Artinian.
* `Stacks.LocalCohomology.isArtinian_localCohomologyModule_of_isIPowerTorsion` — **Stacks 0DX0
  (1) under the extra hypothesis that `M` is `𝔪`-power torsion**, which is the base case of the
  Stacks induction on `dim Supp M`. The general statement is not proved here.

No Stacks attribute for tag 0DX0 is placed anywhere in this file. That tag has two parts and
neither is proved: the result below is strictly weaker than part (1), since it assumes the
coefficient module is already `𝔪`-power torsion, and part (2) is about cohomology on the
punctured spectrum.

## References

* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0)
* [Stacks Project, Tag 08Z8](https://stacks.math.columbia.edu/tag/08Z8)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u w

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### Local cohomology modules are power torsion -/

/-- The local cohomology modules of `M` with support in `V(I)` are `I`-power torsion. This is
true by construction: `RΓ_{V(I)}` takes values in the full subcategory of `D(A)` on the objects
all of whose cohomology modules are `I`-power torsion. -/
theorem isIPowerTorsion_localCohomologyModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{v} A) (i : ℤ) :
    IsIPowerTorsion A (localCohomologyModule A I hI M i) I :=
  ((Dualizing.localCohomologyFunctor A I hI).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)).property i

/-- **The reduction of Stacks 0DX0 (1) to a statement about socles.** Over a Noetherian local
ring, a local cohomology module at the maximal ideal has the descending chain condition exactly
when its socle is finite-dimensional over the residue field: the other half of the criterion of
Stacks 08Z8 (2), that the module be `𝔪`-power torsion, holds automatically. -/
theorem isArtinian_localCohomologyModule_iff_hasFiniteSocle
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{v} A) (i : ℤ) :
    IsArtinian A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i) ↔
      Dualizing.HasFiniteSocle A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i) := by
  rw [Dualizing.isArtinian_iff_powerTorsion_and_finiteSocle]
  exact and_iff_right (isIPowerTorsion_localCohomologyModule A _ _ M i)

/-! ### Artinian terms give Artinian cohomology -/

/-- The descending chain condition passes to the source of a monomorphism of modules. -/
private theorem isArtinian_of_mono_moduleCat {X Y : ModuleCat.{v} A} (g : X ⟶ Y) [Mono g]
    (h : IsArtinian A Y) : IsArtinian A X :=
  isArtinian_of_injective g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)

/-- The descending chain condition transports along an isomorphism of modules. -/
theorem isArtinian_of_moduleCatIso {X Y : ModuleCat.{v} A} (e : X ≅ Y) (h : IsArtinian A Y) :
    IsArtinian A X :=
  isArtinian_of_mono_moduleCat e.hom h

/-- The cohomology of a cochain complex of `A`-modules in a degree whose term has the descending
chain condition has the descending chain condition itself: it is a quotient of the cycles, which
are a submodule of the term. -/
theorem isArtinian_homology_of_isArtinian_X
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) (h : IsArtinian A (K.X i)) :
    IsArtinian A (K.homology i) := by
  have hcyc : IsArtinian A (K.cycles i) := isArtinian_of_mono_moduleCat (K.iCycles i) h
  exact isArtinian_of_surjective _ (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)

/-! ### The Čech complex of a power-torsion module -/

variable {r : ℕ}

/-- If `M` is power torsion for the ideal generated by `f_1, …, f_r`, then inverting the product
of a nonempty subfamily kills `M`: the product lies in the ideal, so a power of it annihilates
any given element. -/
theorem subsingleton_cechMod_of_isIPowerTorsion (f : Fin r → A)
    (M : Type w) [AddCommGroup M] [Module A M]
    (hM : IsIPowerTorsion A M (Ideal.span (Set.range f)))
    {s : Finset (Fin r)} (hs : s.Nonempty) :
    Subsingleton (Cech.cechMod f M s) := by
  rw [LocalizedModule.subsingleton_iff]
  intro x
  obtain ⟨n, -, hkill⟩ := hM x
  obtain ⟨i₀, hi₀⟩ := hs
  refine ⟨(∏ i ∈ s, f i) ^ n, ⟨n, rfl⟩, hkill _ (Ideal.pow_mem_pow ?_ n)⟩
  rw [← Finset.mul_prod_erase s f hi₀]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i₀, rfl⟩)

/-- Every term of the alternating Čech complex of a power-torsion module in a positive degree
vanishes: each of its summands does. -/
theorem subsingleton_cechTerm_of_isIPowerTorsion (f : Fin r → A)
    (M : Type w) [AddCommGroup M] [Module A M]
    (hM : IsIPowerTorsion A M (Ideal.span (Set.range f)))
    {p : ℕ} (hp : 0 < p) :
    Subsingleton (Cech.cechTerm f M p) := by
  refine ⟨fun x y => DFinsupp.ext fun s => ?_⟩
  have : Subsingleton (Cech.cechMod f M s.1) :=
    subsingleton_cechMod_of_isIPowerTorsion f M hM
      (Finset.card_pos.mp (by rw [s.2]; exact hp))
  exact Subsingleton.elim _ _

/-- For a power-torsion module with the descending chain condition, every term of the extended
alternating Čech complex has the descending chain condition: it is `M` in degree zero and zero in
every other degree. -/
theorem isArtinian_extendedCechComplex_X (f : Fin r → A) (M : ModuleCat.{max u v} A)
    (hM : IsIPowerTorsion A M (Ideal.span (Set.range f))) (hA : IsArtinian A M) (i : ℤ) :
    IsArtinian A ((extendedCechComplex f M).X i) := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have : Subsingleton ((extendedCechComplex f M).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_extendedCechComplex_X f M i (Or.inl hi))
    infer_instance
  · exact isArtinian_of_moduleCatIso (extendedCechXZeroIso f M) hA
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    have hn : 0 < n := by exact_mod_cast hi
    have hsub : Subsingleton ((Cech.cechComplex f M).X n) :=
      subsingleton_cechTerm_of_isIPowerTorsion f M hM hn
    exact isArtinian_of_moduleCatIso (HomologicalComplex.extendXIso (Cech.cechComplex f M)
      ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp)) inferInstance

/-! ### The base case of Stacks 0DX0 (1) -/

/-- **The base case of Stacks 0DX0 (1).** Over a Noetherian local ring, the local cohomology at
the maximal ideal of a finite module that is *already* `𝔪`-power torsion has the descending chain
condition in every degree.

This is the starting point of the induction on `dim Supp M` by which Stacks proves part (1) of
Tag 0DX0: when the support of `M` is `{𝔪}` the module is `𝔪`-power torsion, and then all of the
local cohomology is concentrated in degree zero where it is `M` itself. The hypothesis
`IsIPowerTorsion A M (maximalIdeal A)` is an extra hypothesis, not present in Tag 0DX0; the
general statement is not proved here. -/
theorem isArtinian_localCohomologyModule_of_isIPowerTorsion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{max u v} A) [Module.Finite A M]
    (hM : IsIPowerTorsion A M (IsLocalRing.maximalIdeal A)) (i : ℤ) :
    IsArtinian A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i) := by
  have hArt : IsArtinian A M :=
    Stacks.Divisors.isArtinian_of_forall_exists_pow_smul_eq_zero (fun g hg x => by
      obtain ⟨n, -, hn⟩ := hM x
      exact ⟨n, hn _ (Ideal.pow_mem_pow hg n)⟩)
  obtain ⟨S, hS⟩ := (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  obtain ⟨t, f, hf⟩ := S.finite_toSet.fin_embedding
  have hgen : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A := by rw [hf]; exact hS
  obtain ⟨e⟩ := nonempty_homology_localCohomology_iso_cechHomology f M
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing hgen i
  exact isArtinian_of_moduleCatIso e
    (isArtinian_homology_of_isArtinian_X _ i
      (isArtinian_extendedCechComplex_X f M (hgen ▸ hM) hArt i))

end Stacks.LocalCohomology
