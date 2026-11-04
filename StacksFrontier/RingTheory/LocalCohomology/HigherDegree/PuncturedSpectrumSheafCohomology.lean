module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedComplement
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.SupportReduction
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ComplementSections
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison

/-!
# Sheaf cohomology of a quasi-coherent module on a punctured spectrum

Let `I` be a finitely generated ideal of a commutative ring `A` and `U = Spec A ∖ V(I)`. If the
local cohomology `H^i_{V(I)}(A)` vanishes for every `i > d`, with `d ≥ 1`, then the
`Ext`-theoretic sheaf cohomology `H^n(U, ℱ)` of every quasi-coherent module `ℱ` on `U` is trivial
for every `n ≥ d`. For a local ring and `I` its maximal ideal, `U` is the punctured spectrum.

All names are in the namespace `Stacks.LocalCohomology`.

## Main results

* `eq_zero_sheafH_complement_of_isZero_localCohomologyModule`: the vanishing on
  `U = Spec A ∖ V(I)`, in every degree `n ≥ d`.
* `eq_zero_sheafH_puncturedSpectrum_of_isZero_localCohomologyModule`: the same for the punctured
  spectrum of a local ring.
* `eq_zero_sheafH_puncturedSpectrum_degree_of_isZero_localCohomologyModule`: the one-degree form:
  vanishing of `H^i_𝔪(A)` for `i > n` gives the vanishing of degree-`n` sheaf cohomology, for
  `n ≥ 1`.
* `eq_zero_sheafH_puncturedSpectrum_degree_of_isNoetherianRing`: the same for a Noetherian local
  ring.
* `eq_zero_sheafH_complementTilde_of_isZero_localCohomologyModule`,
  `eq_zero_sheafH_complementTilde_of_isZero_localCohomologyWithSupportIn` and
  `eq_zero_sheafH_complementTilde_of_isZero_localCohomologyWithSupportIn_closedPoint`: the
  single-degree statements for `M̃|U`.
* `eq_zero_sheafH_of_isQuasicoherent_of_isZero_localCohomologyModule` and
  `eq_zero_sheafH_puncturedSpectrum_of_isZero_localCohomologyWithSupportIn`: the single-degree
  statements for an arbitrary quasi-coherent module.
* `eq_zero_sheafH_unit_of_isZero_localCohomologyModule`,
  `eq_zero_sheafH_unit_of_isZero_localCohomologyWithSupportIn_closedPoint` and
  `eq_zero_sheafH_unit_puncturedSpectrum_of_isZero_localCohomologyWithSupportIn`: the
  single-degree statements for the structure sheaf `𝒪_U`, whose hypothesis is about the module
  `A` alone.
* `eq_zero_sheafH_unit_puncturedSpectrumQuotient_of_isZero_localCohomologyWithSupportIn` and
  `eq_zero_sheafH_unit_puncturedClosedFibre_of_isZero_localCohomologyWithSupportIn`: the
  single-degree statements for `𝒪` on the punctured spectrum of `A ⧸ fA`, with the hypothesis on
  the `A`-module `A ⧸ fA`.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0BJB](https://stacks.math.columbia.edu/tag/0BJB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- For a Noetherian local ring, vanishing of local cohomology with support the closed point is
vanishing of local cohomology at the maximal ideal. -/
private theorem isZero_localCohomologyWithSupportIn_closedPoint_iff [IsNoetherianRing A]
    [IsLocalRing A] (M : ModuleCat.{u} A) (i : ℤ) :
    IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) ↔
    IsZero (localCohomologyModule A (maximalIdeal A)
      (IsNoetherian.noetherian (maximalIdeal A)) M i) := by
  rw [← AlgebraicGeometry.zeroLocus_maximalIdeal_eq_singleton]
  exact ⟨fun h => h.of_iso (localCohomologyWithSupportInIsoLocalCohomologyModule A
      (maximalIdeal A) (IsNoetherian.noetherian (maximalIdeal A)) M i).symm,
    fun h => h.of_iso (localCohomologyWithSupportInIsoLocalCohomologyModule A
      (maximalIdeal A) (IsNoetherian.noetherian (maximalIdeal A)) M i)⟩

/-- **Local cohomology of `A` vanishing above `d ≥ 1` kills the sheaf cohomology of every
quasi-coherent module on `U = Spec A ∖ V(I)` in degrees `≥ d`.** The support is `V(I)`, and the
sheaf cohomology is the `Ext`-theoretic cohomology of the underlying abelian sheaf. -/
theorem eq_zero_sheafH_complement_of_isZero_localCohomologyModule (I : Ideal A) (hI : I.FG)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(complementZeroLocus A I : Scheme)) AddCommGrpCat.{u})]
    (d : ℤ) (hd : 1 ≤ d)
    (h : ∀ i : ℤ, d < i → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i))
    (F : (complementZeroLocus A I : Scheme).Modules) (hF : F.IsQuasicoherent)
    (n : ℕ) (hn : d ≤ (n : ℤ))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (complementZeroLocus A I : Scheme).ringCatSheaf).obj F) n) :
    x = 0 :=
  Stacks.Cohomology.ModuleComparison.eq_zero_sheafH_of_isZero_schemeHgroupTop
    (complementZeroLocus A I : Scheme) n F
    (isZero_hgroup_of_isQuasicoherent I hI d hd
      (fun M i hi =>
        isZero_homology_localCohomology_of_isZero_homology_self.{u} I hI d h M i hi)
      F hF n hn) x

/-- **The same on the punctured spectrum of a local ring.** If `H^i_𝔪(A) = 0` for every `i > d`,
with `d ≥ 1`, then the degree-`n` sheaf cohomology of every quasi-coherent module on
`Spec A ∖ {𝔪}` is trivial for every `n ≥ d`. -/
theorem eq_zero_sheafH_puncturedSpectrum_of_isZero_localCohomologyModule [IsLocalRing A]
    (hm : (maximalIdeal A).FG)
    [hExt : HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Divisors.puncturedSpectrum A : Scheme)) AddCommGrpCat.{u})]
    (d : ℤ) (hd : 1 ≤ d)
    (h : ∀ i : ℤ, d < i →
      IsZero (localCohomologyModule A (maximalIdeal A) hm (ModuleCat.of A A) i))
    (F : (Stacks.Divisors.puncturedSpectrum A : Scheme).Modules) (hF : F.IsQuasicoherent)
    (n : ℕ) (hn : d ≤ (n : ℤ))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf).obj F) n) :
    x = 0 := by
  revert hExt F hF x
  rw [AlgebraicGeometry.puncturedSpectrum_eq_complementZeroLocus A]
  intro hExt F hF x
  exact eq_zero_sheafH_complement_of_isZero_localCohomologyModule (maximalIdeal A) hm d hd h F hF
    n hn x

/-- **The one-degree form.** For a local ring `A` whose maximal ideal is finitely generated, a
degree `n ≥ 1` and a quasi-coherent module `ℱ` on the punctured spectrum, the vanishing of
`H^i_𝔪(A)` for every `i > n` makes the degree-`n` sheaf cohomology of `ℱ` trivial. -/
theorem eq_zero_sheafH_puncturedSpectrum_degree_of_isZero_localCohomologyModule [IsLocalRing A]
    (hm : (maximalIdeal A).FG)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Divisors.puncturedSpectrum A : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ i : ℤ, (n : ℤ) < i →
      IsZero (localCohomologyModule A (maximalIdeal A) hm (ModuleCat.of A A) i))
    (F : (Stacks.Divisors.puncturedSpectrum A : Scheme).Modules) (hF : F.IsQuasicoherent)
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf).obj F) n) :
    x = 0 :=
  eq_zero_sheafH_puncturedSpectrum_of_isZero_localCohomologyModule hm (n : ℤ)
    (by exact_mod_cast hn) h F hF n le_rfl x

/-- **The one-degree form for a Noetherian local ring**, where the maximal ideal is finitely
generated because every ideal is. -/
theorem eq_zero_sheafH_puncturedSpectrum_degree_of_isNoetherianRing [IsNoetherianRing A]
    [IsLocalRing A]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Divisors.puncturedSpectrum A : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ i : ℤ, (n : ℤ) < i → IsZero (localCohomologyModule A (maximalIdeal A)
      (IsNoetherian.noetherian (maximalIdeal A)) (ModuleCat.of A A) i))
    (F : (Stacks.Divisors.puncturedSpectrum A : Scheme).Modules) (hF : F.IsQuasicoherent)
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf).obj F) n) :
    x = 0 :=
  eq_zero_sheafH_puncturedSpectrum_degree_of_isZero_localCohomologyModule
    (IsNoetherian.noetherian (maximalIdeal A)) n hn h F hF x

/-! ### Single-degree forms -/

/-- **One degree of local cohomology kills one degree of sheaf cohomology.** For `n ≥ 1` the
vanishing of `H^{n+1}_{V(I)}(M)` makes every degree-`n` sheaf cohomology class of `M̃|U` on
`U = Spec A ∖ V(I)` zero. -/
theorem eq_zero_sheafH_complementTilde_of_isZero_localCohomologyModule (I : Ideal A) (hI : I.FG)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(complementZeroLocus A I : Scheme)) AddCommGrpCat.{u})]
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyModule A I hI M ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (complementZeroLocus A I : Scheme).ringCatSheaf).obj (complementTilde A I M)) n) :
    x = 0 :=
  Stacks.Cohomology.ModuleComparison.eq_zero_sheafH_of_isZero_schemeHgroupTop
    (complementZeroLocus A I : Scheme) n (complementTilde A I M)
    ((isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule I hI M n hn).2 h) x

/-- The same over a Noetherian ring, with the hypothesis in the supported-sections model of local
cohomology. -/
theorem eq_zero_sheafH_complementTilde_of_isZero_localCohomologyWithSupportIn
    [IsNoetherianRing A] (I : Ideal A)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(complementZeroLocus A I : Scheme)) AddCommGrpCat.{u})]
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (complementZeroLocus A I : Scheme).ringCatSheaf).obj (complementTilde A I M)) n) :
    x = 0 :=
  eq_zero_sheafH_complementTilde_of_isZero_localCohomologyModule I
    (Ideal.fg_of_isNoetherianRing I) M n hn
    (h.of_iso (localCohomologyWithSupportInIsoLocalCohomologyModule A I
      (Ideal.fg_of_isNoetherianRing I) M ((n : ℤ) + 1)).symm) x

/-- **The single-degree form at the closed point of a Noetherian local ring.** For `n ≥ 1` the
vanishing of the degree-`n+1` local cohomology of `M` with support the closed point kills every
degree-`n` sheaf cohomology class of `M̃` on `complementZeroLocus A 𝔪 = Spec A ∖ {𝔪}`. -/
theorem eq_zero_sheafH_complementTilde_of_isZero_localCohomologyWithSupportIn_closedPoint
    [IsNoetherianRing A] [IsLocalRing A]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(complementZeroLocus A (maximalIdeal A) : Scheme)) AddCommGrpCat.{u})]
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (complementZeroLocus A (maximalIdeal A) : Scheme).ringCatSheaf).obj
        (complementTilde A (maximalIdeal A) M)) n) :
    x = 0 :=
  eq_zero_sheafH_complementTilde_of_isZero_localCohomologyWithSupportIn (maximalIdeal A) M n hn
    (by rwa [AlgebraicGeometry.zeroLocus_maximalIdeal_eq_singleton]) x

/-- **The single-degree form for an arbitrary quasi-coherent module on `U = Spec A ∖ V(I)`.**
For `n ≥ 1`, if `H^{n+1}_{V(I)}(M)` vanishes for every `A`-module `M`, then every degree-`n` sheaf
cohomology class of `ℱ` is zero. -/
theorem eq_zero_sheafH_of_isQuasicoherent_of_isZero_localCohomologyModule (I : Ideal A)
    (hI : I.FG)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(complementZeroLocus A I : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ M : ModuleCat.{u} A, IsZero (localCohomologyModule A I hI M ((n : ℤ) + 1)))
    (F : (complementZeroLocus A I : Scheme).Modules) (hF : F.IsQuasicoherent)
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (complementZeroLocus A I : Scheme).ringCatSheaf).obj F) n) :
    x = 0 := by
  obtain ⟨M, ⟨e⟩⟩ := exists_module_iso_restrict_tilde A I hI F
  refine Stacks.Cohomology.ModuleComparison.eq_zero_sheafH_of_isZero_schemeHgroupTop
    (complementZeroLocus A I : Scheme) n F ?_ x
  refine ((isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule I hI M n hn).2
    (h M)).of_iso ?_
  exact (Hfunctor (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n).mapIso e

/-- **The single-degree form for an arbitrary quasi-coherent module on the punctured spectrum of
a Noetherian local ring**, with the hypothesis in the supported-sections model at the closed
point. -/
theorem eq_zero_sheafH_puncturedSpectrum_of_isZero_localCohomologyWithSupportIn
    [IsNoetherianRing A] [IsLocalRing A]
    [hExt : HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Divisors.puncturedSpectrum A : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ M : ModuleCat.{u} A, IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ((n : ℤ) + 1)))
    (F : (Stacks.Divisors.puncturedSpectrum A : Scheme).Modules) (hF : F.IsQuasicoherent)
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf).obj F) n) :
    x = 0 := by
  revert hExt F hF x
  rw [AlgebraicGeometry.puncturedSpectrum_eq_complementZeroLocus A]
  intro hExt F hF x
  refine eq_zero_sheafH_of_isQuasicoherent_of_isZero_localCohomologyModule (maximalIdeal A)
    (IsNoetherian.noetherian (maximalIdeal A)) n hn (fun M => ?_) F hF x
  exact (isZero_localCohomologyWithSupportIn_closedPoint_iff M _).1 (h M)

/-! ### Single-degree forms for the structure sheaf -/

/-- **One degree of local cohomology of `A` kills one degree of the sheaf cohomology of
`𝒪_U`.** For `n ≥ 1` the vanishing of `H^{n+1}_{V(I)}(A)` makes every degree-`n` sheaf cohomology
class of the structure sheaf of `U = Spec A ∖ V(I)` zero. -/
theorem eq_zero_sheafH_unit_of_isZero_localCohomologyModule (I : Ideal A) (hI : I.FG)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(complementZeroLocus A I : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyModule A I hI (ModuleCat.of A A) ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (complementZeroLocus A I : Scheme).ringCatSheaf).obj
        (SheafOfModules.unit (complementZeroLocus A I : Scheme).ringCatSheaf)) n) :
    x = 0 := by
  refine Stacks.Cohomology.ModuleComparison.eq_zero_sheafH_of_isZero_schemeHgroupTop
    (complementZeroLocus A I : Scheme) n
    (SheafOfModules.unit (complementZeroLocus A I : Scheme).ringCatSheaf) ?_ x
  refine ((isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule I hI
    (ModuleCat.of A A) n hn).2 h).of_iso ?_
  exact (Hfunctor (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n).mapIso
    (complementTildeRingIsoUnit A I).symm

/-- The same for a Noetherian local ring with `I` the maximal ideal, with the hypothesis in the
supported-sections model at the closed point. -/
theorem eq_zero_sheafH_unit_of_isZero_localCohomologyWithSupportIn_closedPoint
    [IsNoetherianRing A] [IsLocalRing A]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(complementZeroLocus A (maximalIdeal A) : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
        ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (complementZeroLocus A (maximalIdeal A) : Scheme).ringCatSheaf).obj
        (SheafOfModules.unit
          (complementZeroLocus A (maximalIdeal A) : Scheme).ringCatSheaf)) n) :
    x = 0 := by
  exact eq_zero_sheafH_unit_of_isZero_localCohomologyModule (maximalIdeal A)
    (IsNoetherian.noetherian (maximalIdeal A)) n hn
    ((isZero_localCohomologyWithSupportIn_closedPoint_iff _ _).1 h) x

/-- **The structure sheaf of the punctured spectrum of a Noetherian local ring, in a single
degree.** For `n ≥ 1`, if the degree-`n+1` local cohomology of `A` with support the closed point
is zero then every degree-`n` sheaf cohomology class of `𝒪_U` on `U = Spec A ∖ {𝔪}` is zero. -/
theorem eq_zero_sheafH_unit_puncturedSpectrum_of_isZero_localCohomologyWithSupportIn
    [IsNoetherianRing A] [IsLocalRing A]
    [hExt : HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Divisors.puncturedSpectrum A : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
        ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf).obj
        (SheafOfModules.unit
          (Stacks.Divisors.puncturedSpectrum A : Scheme).ringCatSheaf)) n) :
    x = 0 := by
  revert hExt x
  rw [AlgebraicGeometry.puncturedSpectrum_eq_complementZeroLocus A]
  intro hExt x
  exact eq_zero_sheafH_unit_of_isZero_localCohomologyWithSupportIn_closedPoint n hn h x

/-! ### The punctured spectrum of a quotient by one element -/

/-- **One degree of local cohomology of `A ⧸ fA` over `A` kills one degree of the sheaf
cohomology of `𝒪` on the punctured spectrum of `A ⧸ fA`.** For `n ≥ 1` the hypothesis is the
vanishing of the degree-`n+1` local cohomology of the `A`-module `A ⧸ fA` with support the closed
point of `Spec A`, and the conclusion is about the quotient ring. -/
theorem eq_zero_sheafH_unit_puncturedSpectrumQuotient_of_isZero_localCohomologyWithSupportIn
    [IsNoetherianRing A] [IsLocalRing A] (f : A) [IsLocalRing (A ⧸ Ideal.span {f})]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Divisors.puncturedSpectrum (A ⧸ Ideal.span {f}) : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (Stacks.Divisors.puncturedSpectrum (A ⧸ Ideal.span {f}) : Scheme).ringCatSheaf).obj
        (SheafOfModules.unit
          (Stacks.Divisors.puncturedSpectrum (A ⧸ Ideal.span {f}) : Scheme).ringCatSheaf)) n) :
    x = 0 := by
  set q : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk (Ideal.span {f}) with hq
  have hlh : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal A).map q = maximalIdeal (A ⧸ Ideal.span {f}) := by
    rw [← IsLocalRing.maximalIdeal_comap q,
      Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective]
  have hAmod : IsZero (localCohomologyModule A (maximalIdeal A)
      (IsNoetherian.noetherian (maximalIdeal A))
      ((ModuleCat.restrictScalars q).obj
        (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f}))) ((n : ℤ) + 1)) :=
    (isZero_localCohomologyWithSupportIn_closedPoint_iff _ _).1 h
  have hBres : IsZero ((ModuleCat.restrictScalars q).obj
      (localCohomologyModule (A ⧸ Ideal.span {f}) ((maximalIdeal A).map q)
        (IsNoetherian.noetherian ((maximalIdeal A).map q))
        (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})) ((n : ℤ) + 1))) :=
    hAmod.of_iso (localCohomologyModuleRestrictScalarsIso q (maximalIdeal A)
      (IsNoetherian.noetherian (maximalIdeal A))
      (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})) ((n : ℤ) + 1)).symm
  have hB : IsZero (localCohomologyModule (A ⧸ Ideal.span {f}) ((maximalIdeal A).map q)
      (IsNoetherian.noetherian ((maximalIdeal A).map q))
      (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})) ((n : ℤ) + 1)) := by
    rwa [ModuleCat.isZero_iff_subsingleton] at hBres ⊢
  have hB2 : IsZero (localCohomologyModule (A ⧸ Ideal.span {f})
      (maximalIdeal (A ⧸ Ideal.span {f}))
      (IsNoetherian.noetherian (maximalIdeal (A ⧸ Ideal.span {f})))
      (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})) ((n : ℤ) + 1)) := by
    rwa [← hmap]
  refine eq_zero_sheafH_unit_puncturedSpectrum_of_isZero_localCohomologyWithSupportIn n hn ?_ x
  exact (isZero_localCohomologyWithSupportIn_closedPoint_iff _ _).2 hB2

/-- **The same on the punctured closed fibre of `f`.** For `f` in the maximal ideal of a
Noetherian local ring `A` and `n ≥ 1`, if the degree-`n+1` local cohomology of the `A`-module
`A ⧸ fA` with support the closed point vanishes, then every degree-`n` sheaf cohomology class of
`𝒪` on the part of `Spec (A ⧸ fA)` lying over the punctured spectrum of `A` is zero. -/
theorem eq_zero_sheafH_unit_puncturedClosedFibre_of_isZero_localCohomologyWithSupportIn
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (hf : f ∈ maximalIdeal A)
    [hExt : HasExt.{u} (Sheaf (Opens.grothendieckTopology
      ↥(Stacks.Algebraization.puncturedClosedFibre A f : Scheme)) AddCommGrpCat.{u})]
    (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) ((n : ℤ) + 1)))
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf
      (Stacks.Algebraization.puncturedClosedFibre A f : Scheme).ringCatSheaf).obj
        (SheafOfModules.unit
          (Stacks.Algebraization.puncturedClosedFibre A f : Scheme).ringCatSheaf)) n) :
    x = 0 := by
  have hIle : Ideal.span {f} ≤ maximalIdeal A := Ideal.span_le.mpr (by simpa using hf)
  have hIne : Ideal.span {f} ≠ ⊤ := fun htop =>
    (maximalIdeal.isMaximal A).ne_top (top_unique (htop ▸ hIle))
  have : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (A ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
      Ideal.Quotient.mk_surjective
  revert hExt x
  rw [Stacks.Algebraization.puncturedClosedFibre_eq_puncturedSpectrum A f hf]
  intro hExt x
  exact eq_zero_sheafH_unit_puncturedSpectrumQuotient_of_isZero_localCohomologyWithSupportIn
    f n hn h x

end Stacks.LocalCohomology

end
