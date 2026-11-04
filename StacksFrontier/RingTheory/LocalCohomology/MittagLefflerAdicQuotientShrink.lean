module

public import Mathlib.CategoryTheory.CofilteredSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedLocalCohomologyShrink
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyProjections
public import StacksFrontier.RingTheory.LocalCohomology.AlreadyTorsion
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerSystems
public import StacksFrontier.RingTheory.LocalCohomology.PuncturedSpectrumDescendingChain

/-!
# The local cohomology of the adic quotients at an ideal meeting `V(I)` in the closed point

Let `(A, 𝔪)` be a Noetherian local ring, let `I` and `J` be ideals with
`V(J) ∩ V(I) = {𝔪}`, and let `M` be a finite `A`-module. This file proves that the inverse
system `n ↦ Hⁱ_J(M/IⁿM)` satisfies the Mittag-Leffler condition, in every degree.

`Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology` is the
same statement at `J = 𝔪`, where it follows from the Artinianness of local cohomology at the
maximal ideal. For a general `J` the modules `Hⁱ_J(N)` of a finite module `N` are not Artinian;
what rescues the argument here is that the terms of the tower are annihilated by a power of `I`.
For such a module `N` the ideal may be enlarged by `I` without changing the local cohomology,
which is Stacks 0DWS, and `V(J + I) = V(J) ∩ V(I) = {𝔪} = V(𝔪)`, so local cohomology sees only
the maximal ideal: `Hⁱ_J(N) ≅ Hⁱ_{J + I}(N) ≅ Hⁱ_𝔪(N)`, which is Artinian.

## Main results

* `Stacks.LocalCohomology.isIPowerTorsion_adicQuotientModuleSystem_obj` — the term `M/IⁿM` of the
  tower is `I`-power torsion.
* `Stacks.LocalCohomology.isArtinian_localCohomologyModule_of_isIPowerTorsion_of_zeroLocus_inter`
  — for an `I`-power-torsion finite module `N` and an ideal `J` with `V(J) ∩ V(I) = {𝔪}`, the
  module `Hⁱ_J(N)` is Artinian.
* `Stacks.LocalCohomology.isMittagLefflerCategorical_adicQuotientLocalCohomologySystem` — the
  Mittag-Leffler condition for the tower `n ↦ Hⁱ_J(M/IⁿM)`.
* `Stacks.LocalCohomology.isMittagLeffler_forget_of_isArtinian` — a tower of Artinian modules is
  Mittag-Leffler in Mathlib's range formulation, and
  `Stacks.LocalCohomology.isMittagLeffler_forget_adicQuotientLocalCohomologySystem` the same
  formulation for the tower above. Both formulations are needed: the subobject one by Tag 0DXJ,
  the range one by Tag 070B.

## References

* [Stacks Project, Tag 0DWS](https://stacks.math.columbia.edu/tag/0DWS)
* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0)
* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A]

/-- **The terms of the adic quotient tower are `I`-power torsion.** The `n`-th term `M/IⁿM` is
annihilated by `Iⁿ`, hence by `Iⁿ⁺¹`, which is a strictly positive power. -/
public theorem isIPowerTorsion_adicQuotientModuleSystem_obj (I : Ideal A) (M : ModuleCat.{u} A)
    (n : ℕ) :
    IsIPowerTorsion A ((adicQuotientModuleSystem A I M).obj (op n)) I := by
  intro m
  refine ⟨n + 1, n.succ_pos, fun a ha ↦ ?_⟩
  exact Module.mem_annihilator.1
    (Dualizing.pow_le_annihilator_adicQuotient A I M n
      (Ideal.pow_le_pow_right n.le_succ ha)) m

variable [IsLocalRing A] [IsNoetherianRing A]

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- Artinianness transports along an isomorphism of `A`-modules. -/
private theorem isArtinian_of_iso {X Y : ModuleCat.{u} A} (e : X ≅ Y) (h : IsArtinian A X) :
    IsArtinian A Y := by
  let := h
  exact isArtinian_of_linearEquiv e.toLinearEquiv

/-- **Local cohomology of an `I`-power-torsion finite module at an ideal meeting `V(I)` in the
closed point is Artinian.** Stacks 0DWS identifies `Hⁱ_J(N)` with `Hⁱ_{J + I}(N)` for an
`I`-power-torsion `N`; the zero locus of `J + I` is `V(J) ∩ V(I) = {𝔪} = V(𝔪)`, so that module
is `Hⁱ_𝔪(N)`, which is Artinian by Stacks 0DX0. -/
public theorem isArtinian_localCohomologyModule_of_isIPowerTorsion_of_zeroLocus_inter
    (I J : Ideal A)
    (N : ModuleCat.{u} A) [Module.Finite A N] (hN : IsIPowerTorsion A N I)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℤ) :
    IsArtinian A (localCohomologyModule A J J.fg_of_isNoetherianRing N i) := by
  have hzero : PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) := by
    rw [PrimeSpectrum.zeroLocus_sup, Stacks.Algebraization.zeroLocus_maximalIdeal,
      Set.inter_comm]
    exact hV
  -- `Hⁱ_{I ⊔ J}(N) ≅ Hⁱ_𝔪(N)`, hence Artinian
  have hart : IsArtinian A
      (localCohomologyModule A (I ⊔ J) (Ideal.fg_of_isNoetherianRing _) N i) := by
    have e := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (Stacks.Algebraization.localCohomologyDerivedIsoOfZeroLocusEq A (maximalIdeal A) (I ⊔ J)
        (Ideal.fg_of_isNoetherianRing _) (Ideal.fg_of_isNoetherianRing _) hzero
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))
    exact isArtinian_of_iso A e.symm (isArtinian_localCohomology_maximalIdeal A N i)
  -- Stacks 0DWS: the comparison `Hⁱ_{I ⊔ J}(N) ⟶ Hⁱ_J(N)` is an isomorphism
  have hiso := isIso_homology_localCohomologyComparison_of_isIPowerTorsion A I J
    (Ideal.fg_of_isNoetherianRing _) J.fg_of_isNoetherianRing N hN i
  exact isArtinian_of_iso A
    (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (Stacks.Algebraization.localCohomologyComparison A (I ⊔ J) J
        (Submodule.FG.sup (Ideal.fg_of_isNoetherianRing _) J.fg_of_isNoetherianRing)
        J.fg_of_isNoetherianRing le_sup_right
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))) hart

/-- **A tower of Artinian modules is Mittag-Leffler**, in the range formulation of Mathlib's
`CategoryTheory.Functor.IsMittagLeffler` for the underlying tower of sets. The images in a fixed
term of the maps coming from above form a descending chain of submodules, which stabilizes. -/
public theorem isMittagLeffler_forget_of_isArtinian {R : Type u} [Ring R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} R) (hF : ∀ n : ℕᵒᵖ, IsArtinian R (F.obj n)) :
    (F ⋙ forget (ModuleCat.{u} R)).IsMittagLeffler := by
  refine (Functor.isMittagLeffler_iff_subset_range_comp _).2 fun j => ?_
  obtain ⟨n⟩ := j
  set rng : ℕ → Submodule R (F.obj (op n)) := fun k =>
    LinearMap.range (F.map (homOfLE (show n ≤ n + k by omega)).op).hom with hrng
  have hstep : ∀ a b : ℕ, a ≤ b → rng b ≤ rng a := by
    intro a b hab
    have hc : F.map (homOfLE (show n ≤ n + b by omega)).op =
        F.map (homOfLE (show n + a ≤ n + b by omega)).op ≫
          F.map (homOfLE (show n ≤ n + a by omega)).op := by
      rw [← F.map_comp]
      exact congrArg F.map (Subsingleton.elim _ _)
    simp only [hrng]
    rw [hc]
    exact LinearMap.range_comp_le_range _ _
  have _ := hF (op n)
  obtain ⟨c, hc⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k => (rng k : (Submodule R (F.obj (op n)))ᵒᵈ), fun a b hab => hstep a b hab⟩ :
      ℕ →o (Submodule R (F.obj (op n)))ᵒᵈ)
  refine ⟨op (n + c), (homOfLE (show n ≤ n + c by omega)).op, ?_⟩
  intro k g
  obtain ⟨l⟩ := k
  have hlc : n + c ≤ l := leOfHom g.unop
  obtain ⟨d, rfl⟩ : ∃ d, l = n + d := ⟨l - n, by omega⟩
  have heq : rng c = rng d := hc d (by omega)
  have hgf : g ≫ (homOfLE (show n ≤ n + c by omega)).op =
      (homOfLE (show n ≤ n + d by omega)).op := Subsingleton.elim _ _
  rw [hgf]
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have hmem : (F.map (homOfLE (show n ≤ n + c by omega)).op).hom y ∈ rng d := by
    rw [← heq]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

/-- Every term `Hⁱ_J(M/IⁿM)` of the tower is Artinian. -/
private theorem isArtinian_adicQuotientLocalCohomology_obj (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℤ) (n : ℕᵒᵖ) :
    IsArtinian A ((Dualizing.adicQuotientLocalCohomologySystem A I J J.fg_of_isNoetherianRing M ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj n) := by
  obtain ⟨n⟩ := n
  have : Module.Finite A ((adicQuotientModuleSystem A I M).obj (op n)) :=
    Module.Finite.quotient A _
  exact isArtinian_localCohomologyModule_of_isIPowerTorsion_of_zeroLocus_inter A I J
    ((adicQuotientModuleSystem A I M).obj (op n))
    (isIPowerTorsion_adicQuotientModuleSystem_obj A I M n) hV i

/-- **The tower of local cohomologies of the adic quotients is Mittag-Leffler.** For an ideal `J`
with `V(J) ∩ V(I) = {𝔪}` and a finite module `M`, the inverse system `n ↦ Hⁱ_J(M/IⁿM)` satisfies
the Mittag-Leffler condition in every degree: each of its terms is Artinian by
`isArtinian_localCohomologyModule_of_isIPowerTorsion_of_zeroLocus_inter`, and a descending chain
of submodules of an Artinian module stabilizes. -/
public theorem isMittagLefflerCategorical_adicQuotientLocalCohomologySystem (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℤ) :
    IsMittagLefflerCategorical
      (Dualizing.adicQuotientLocalCohomologySystem A I J J.fg_of_isNoetherianRing M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) := by
  exact isMittagLefflerCategorical_of_isArtinian _
    (isArtinian_adicQuotientLocalCohomology_obj A I J M hV i)

/-- **The tower `n ↦ Hⁱ_J(M/IⁿM)` is Mittag-Leffler in the range formulation** as well, which is
the form Tag 070B consumes. -/
public theorem isMittagLeffler_forget_adicQuotientLocalCohomologySystem (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℤ) :
    ((Dualizing.adicQuotientLocalCohomologySystem A I J J.fg_of_isNoetherianRing M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⋙
      forget (ModuleCat.{u} A)).IsMittagLeffler := by
  exact isMittagLeffler_forget_of_isArtinian _
    (isArtinian_adicQuotientLocalCohomology_obj A I J M hV i)

end Stacks.LocalCohomology

end
