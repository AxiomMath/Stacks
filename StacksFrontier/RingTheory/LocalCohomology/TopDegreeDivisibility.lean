module

public import Mathlib.RingTheory.QuotSMulTop
public import StacksFrontier.RingTheory.KrullDimension.AvoidTopMinimalPrimes
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing
public import StacksFrontier.RingTheory.LocalCohomology.DimensionBoundUnconditional
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.SupportReduction

/-!
# Multiplication by an element on top local cohomology

Let `A` be a Noetherian ring of Krull dimension `d`, let `I ⊆ A` be an ideal, let `Y = V(I)` and
let `M` be a finite `A`-module. If `f ∈ A` lies outside every minimal prime `p` with
`dim A/p = d`, then multiplication by `f` is surjective on the top local cohomology module
`H^d_Y(M)`.

The argument factors multiplication by `f` on `M` as

`M ↠ fM ↪ M`

and applies the long exact sequence of local cohomology to the two short exact sequences
`0 → ker(M ↠ fM) → M → fM → 0` and `0 → fM → M → M/fM → 0`. Both surjectivity criteria come
from the vanishing of local cohomology above the dimension of the support:
`dim Supp(M/fM) < d` because `f` avoids the top-dimensional minimal primes, so `H^d_Y(M/fM) = 0`
and `H^d_Y(fM) → H^d_Y(M)` is onto; and `dim Supp ker(M ↠ fM) ≤ dim A = d < d + 1`, so
`H^{d+1}_Y(ker) = 0` and `H^d_Y(M) → H^d_Y(fM)` is onto. The composite of the two is
multiplication by `f`.

## Main results

* `Stacks.LocalCohomology.localCohomologyModuleMap_comp` — functoriality of the map induced on
  local cohomology modules.
* `Stacks.LocalCohomology.surjective_smul_top_localCohomologyModule_of_avoidsTopMinimalPrimes` —
  **Stacks 0EB3**: the surjectivity, unconditionally.
* `Stacks.LocalCohomology.surjective_smul_localCohomologyModule_of_avoidsTopMinimalPrimes` — the
  same conclusion over a ring that is not assumed Noetherian, from an explicit bound on the
  cohomological dimension.

## Implementation notes

The vanishing of local cohomology above the dimension of the support is Stacks 0DXC, available as
`Stacks.LocalCohomology.localCohomologyModule_isZero_of_supportDim_lt`; it is the only input, and
it is what makes the statement carrying `@[stacks 0EB3]` unconditional. The variant taking the
bound `cd(B, J) ≤ dim B` as a hypothesis is kept because that bound is stated for rings not
assumed Noetherian, so the variant is not a consequence of the unconditional statement. Both are
specializations of one private core, stated with the vanishing as a hypothesis.

Local cohomology with support in `V(I)` is taken in the model of Stacks 0A6Q, the coreflection
onto the derived objects with `I`-power-torsion cohomology, which is the model Stacks 0DXC is
formalized in here. The general-support model
`Stacks.LocalCohomology.localCohomologyWithSupportIn` of Remark 0EF4 is not used: the comparison
`Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology` between the two is not known to
be invertible in this library, that being Stacks 0955.

The commutative-algebra input, the dimension drop for `M/fM`, is
`Module.supportDim_quotSMulTop_lt_of_avoidsTopMinimalPrimes` of
`StacksFrontier/RingTheory/KrullDimension/AvoidTopMinimalPrimes.lean`. The two surjectivity criteria
and the map on local cohomology modules come from
`StacksFrontier/RingTheory/LocalCohomology/LongExactSequence/Triangulated.lean`, and the
identification of the map induced by `f • 𝟙` with `f • 𝟙` is
`Stacks.LocalCohomology.localCohomologyModuleMap_lsmul`.

Multiplication by `f` is pinned at the single spelling `LinearMap.lsmul A M f`, which is the
spelling `localCohomologyModuleMap_lsmul` is stated at; `f • (⊤ : Submodule A M)` is its range,
and the quotient by it is `QuotSMulTop f M`, which is the module the dimension drop is about.

## References

* [Stacks Project, Tag 0EB3](https://stacks.math.columbia.edu/tag/0EB3)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe w v u

namespace Stacks.LocalCohomology

/-- **Functoriality of the map induced on local cohomology modules.** The map of
`Stacks.LocalCohomology.localCohomologyModuleMap` is the image of a map of modules under a
composite of four functors, so it respects composition. -/
theorem localCohomologyModuleMap_comp
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N P : ModuleCat.{w} A) (g : M ⟶ N) (h : N ⟶ P) (i : ℤ) :
    localCohomologyModuleMap A I hI M N g i ≫ localCohomologyModuleMap A I hI N P h i =
      localCohomologyModuleMap A I hI M P (g ≫ h) i := by
  simp only [localCohomologyModuleMap, ← Functor.map_comp]

/-- The argument of Stacks 0EB3, with the vanishing of local cohomology above the dimension of
the support as a hypothesis.

Multiplication by `f` on `M` is factored as `M ↠ fM ↪ M` and the two surjectivity criteria of the
long exact sequence are applied to `0 → ker(M ↠ fM) → M → fM → 0` and `0 → fM → M → M/fM → 0`.
The hypothesis `hvan` is used exactly twice, for `H^d_Y(M/fM) = 0` and for
`H^{d+1}_Y(ker(M ↠ fM)) = 0`. -/
private theorem surjective_smul_localCohomologyModule_of_vanishing
    (A : Type u) [CommRing A] [IsNoetherianRing A] (d : ℕ) (hd : ringKrullDim A = d) (f : A)
    (hf : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = d → f ∉ p.asIdeal)
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A) [Module.Finite A M]
    (hvan : ∀ N : ModuleCat.{max u v} A, Module.Finite A N → ∀ i : ℤ,
      Module.supportDim A N < ((i.toNat : ℕ) : WithBot ℕ∞) →
        IsZero (localCohomologyModule A I hI N i)) :
    Function.Surjective fun x : localCohomologyModule A I hI M (d : ℤ) => f • x := by
  classical
  let V := (M : Type (max u v))
  let m : V →ₗ[A] V := LinearMap.lsmul A V f
  let N : Submodule A V := f • (⊤ : Submodule A V)
  have hmem (x : V) : m x ∈ N :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, trivial, rfl⟩
  let mN : V →ₗ[A] N := m.codRestrict N hmem
  have hmNsurj : Function.Surjective mN := fun y ↦ by
    obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 y.2
    exact ⟨x, Subtype.ext hx⟩
  -- `0 → fM → M → M/fM → 0`
  let S₁ : ShortComplex (ModuleCat.{max u v} A) :=
    ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext x; simp)
  have hS₁ : S₁.ShortExact :=
    ModuleCat.shortComplex_shortExact S₁ (LinearMap.exact_subtype_mkQ N)
      N.subtype_injective N.mkQ_surjective
  -- `0 → ker(M ↠ fM) → M → fM → 0`
  let S₂ : ShortComplex (ModuleCat.{max u v} A) := mN.shortComplexKer
  have hS₂ : S₂.ShortExact := mN.shortExact_shortComplexKer hmNsurj
  -- `dim Supp(M/fM) < d`, hence `H^d_Y(M/fM) = 0`
  have hqdim : Module.supportDim A (QuotSMulTop f V) < (d : WithBot ℕ∞) :=
    Module.supportDim_quotSMulTop_lt_of_avoidsTopMinimalPrimes.{u, v} A d hd f hf V
  have hzero₁ : IsZero (localCohomologyModule A I hI S₁.X₃ (d : ℤ)) := by
    refine hvan (ModuleCat.of A (QuotSMulTop f V)) inferInstance (d : ℤ) ?_
    simpa using hqdim
  -- `dim Supp ker(M ↠ fM) ≤ dim A = d < d + 1`, hence `H^{d+1}_Y(ker) = 0`
  have hkerdim : Module.supportDim A (LinearMap.ker mN) ≤ (d : WithBot ℕ∞) :=
    calc Module.supportDim A (LinearMap.ker mN)
        ≤ Module.supportDim A V :=
          Module.supportDim_le_of_injective (LinearMap.ker mN).subtype
            (LinearMap.ker mN).injective_subtype
      _ ≤ ringKrullDim A := Module.supportDim_le_ringKrullDim A V
      _ = (d : WithBot ℕ∞) := hd
  have hzero₂ : IsZero (localCohomologyModule A I hI S₂.X₁ ((d : ℤ) + 1)) := by
    refine hvan (ModuleCat.of A (LinearMap.ker mN)) inferInstance ((d : ℤ) + 1) ?_
    have hcast : (((d : ℤ) + 1).toNat : ℕ) = d + 1 := by omega
    rw [hcast]
    refine lt_of_le_of_lt hkerdim ?_
    exact_mod_cast Nat.lt_succ_self d
  have hα : Function.Surjective (localCohomologyModuleMap A I hI S₁.X₁ S₁.X₂ S₁.f (d : ℤ)).hom :=
    surjective_localCohomologyModuleMap_of_isZero_X₃ A I hI S₁ (d : ℤ) hS₁ hzero₁
  have hβ : Function.Surjective (localCohomologyModuleMap A I hI S₂.X₂ S₂.X₃ S₂.g (d : ℤ)).hom :=
    surjective_localCohomologyModuleMap_of_isZero_X₁_succ A I hI S₂ (d : ℤ) hS₂ hzero₂
  -- the composite `M ↠ fM ↪ M` is multiplication by `f`
  have hfactor : S₂.g ≫ S₁.f = ModuleCat.ofHom m := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  have hlsmul : localCohomologyModuleMap A I hI (ModuleCat.of A V) (ModuleCat.of A V)
      (ModuleCat.ofHom m) (d : ℤ) =
      f • 𝟙 (localCohomologyModule A I hI (ModuleCat.of A V) (d : ℤ)) :=
    localCohomologyModuleMap_lsmul A I hI (ModuleCat.of A V) f (d : ℤ)
  have hcomp : localCohomologyModuleMap A I hI S₂.X₂ S₂.X₃ S₂.g (d : ℤ) ≫
      localCohomologyModuleMap A I hI S₁.X₁ S₁.X₂ S₁.f (d : ℤ) =
      f • 𝟙 (localCohomologyModule A I hI (ModuleCat.of A V) (d : ℤ)) := by
    rw [localCohomologyModuleMap_comp A I hI S₂.X₂ S₂.X₃ S₁.X₂ S₂.g S₁.f (d : ℤ), hfactor]
    exact hlsmul
  have hsurj : Function.Surjective
      (f • 𝟙 (localCohomologyModule A I hI (ModuleCat.of A V) (d : ℤ))).hom := by
    rw [← hcomp]
    exact hα.comp hβ
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  exact ⟨y, hy⟩

/-- **Stacks Project, Tag 0EB3.** Let `A` be a Noetherian ring of Krull dimension `d`, let
`I ⊆ A` be a finitely generated ideal, let `Y = V(I)` and let `M` be a finite `A`-module. An
element `f ∈ A` lying outside every minimal prime `p` with `dim A/p = d` acts surjectively on
`H^d_Y(M)`.

The source assumes `A` local. That is not used: the dimension drop for `M/fM` and the vanishing
above the dimension of the support both hold over an arbitrary Noetherian ring, so the hypothesis
is dropped. -/
@[stacks 0EB3]
theorem surjective_smul_top_localCohomologyModule_of_avoidsTopMinimalPrimes
    (A : Type u) [CommRing A] [IsNoetherianRing A] (d : ℕ) (hd : ringKrullDim A = d) (f : A)
    (hf : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = d → f ∉ p.asIdeal)
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    Function.Surjective fun x : localCohomologyModule A I hI M (d : ℤ) => f • x :=
  surjective_smul_localCohomologyModule_of_vanishing.{v, u} A d hd f hf I hI M
    fun N hN i hi ↦ by
      have := hN
      exact localCohomologyModule_isZero_of_supportDim_lt A I hI N i hi

/-- **Stacks 0EB3, with the bound of Stacks 0DXC as a hypothesis.** Let `A` be a Noetherian ring
of Krull dimension `d`, let `I ⊆ A` be a finitely generated ideal, let `Y = V(I)` and let `M` be
a finite `A`-module. An element `f ∈ A` lying outside every minimal prime `p` with `dim A/p = d`
acts surjectively on `H^d_Y(M)`.

The hypothesis `hcd` is the bound `cd(B, J) ≤ dim B` of Stacks 0DXC, quantified over every ring
`B` in the universe of `A` with no Noetherian assumption; it is used twice, once for
`H^d_Y(M/fM) = 0` and once for `H^{d+1}_Y(ker(M ↠ fM)) = 0`. For Noetherian `B` the bound is
available and
`Stacks.LocalCohomology.surjective_smul_top_localCohomologyModule_of_avoidsTopMinimalPrimes`
states the conclusion outright. -/
theorem surjective_smul_localCohomologyModule_of_avoidsTopMinimalPrimes
    (hcd : ∀ (B : Type u) [CommRing B] (J : Ideal B) (hJ : J.FG) (e : ℕ),
      ringKrullDim B ≤ (e : WithBot ℕ∞) → cohomologicalDimension B J hJ ≤ (e : ℤ))
    (A : Type u) [CommRing A] [IsNoetherianRing A] (d : ℕ) (hd : ringKrullDim A = d) (f : A)
    (hf : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = d → f ∉ p.asIdeal)
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    Function.Surjective fun x : localCohomologyModule A I hI M (d : ℤ) => f • x :=
  surjective_smul_localCohomologyModule_of_vanishing.{v, u} A d hd f hf I hI M
    fun N hN i hi ↦ by
      have := hN
      exact isZero_localCohomologyModule_of_supportDim_lt_of_bound.{v, u} hcd A I hI N i hi

end Stacks.LocalCohomology

end
