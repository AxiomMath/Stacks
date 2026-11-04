module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalLocalCohomologyFiniteLength
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalExtImageFiniteLength
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExtDetection
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# Stacks 0DXU, assembled

Fix an algebraization situation `S` (the data of [Stacks, Tag 0EHC]) whose ring `A` is Noetherian
local with `𝔞 = 𝔪`, and let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)` on `U = X ∖ V(𝔪)`.  Under the
six hypotheses of [Stacks, Tag 0DXU] the system `(ℱₙ)` extends canonically to `X`, and when `A`
is `I`-adically complete it is the completion of a coherent `𝒪_U`-module.  This file performs the
last assembly, from the two statements the source's final paragraphs produce:

* the finite length of the image of the `Ext` map
  `Ext^{-2}_A(M₁, ω) ⟶ Ext^{-2}_A(Mₙ, ω)` for some `n`, where `Mₙ = H⁰(U, ℱₙ)`, which is what
  hypotheses (2), (4), (5) and (6) give over the localizations `A_𝔮` at the primes
  `𝔮 ∈ V(f) ∖ {𝔪}`; and
and the vanishing direction of local duality, which carries the resulting annihilation by a power
of `𝔪` from the `Ext` side back to local cohomology.

## Main results

* `Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_isFiniteLength_range_ext` — both
  conclusions of [Stacks, Tag 0DXU] from hypotheses (1)–(5) together with that `Ext` input.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK), local duality.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite IsLocalRing
open Stacks.RingTheory.PrincipalDivisorDepth
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-- **[Stacks, Tag 0DXU] from the `Ext` side of its last step.**  Hypotheses (1)–(5) of the
source, together with the finite length of the image of `Ext^{-2}_A(M₁, ω) ⟶ Ext^{-2}_A(Mₙ, ω)`
for some `n` give both conclusions of the tag.

The `Ext` input is what the source's final paragraphs produce from hypotheses (2), (4), (5) and
(6).  It is carried back to local cohomology by
`Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero`, the converse
of `Dualizing.LocalDuality.comp_eq_zero_of_homologyMap_localCohomology_eq_zero`; the finiteness
side condition under which [Stacks, Tag 0A06] applies to `RHom_A(M₁, ω⟦-2⟧)` is discharged here
from the boundedness and coherence of a dualizing complex and the finiteness of `M₁`. -/
theorem canonicallyExtends_and_isCompletion_of_isFiniteLength_range_ext
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (ha : S.a = maximalIdeal S.A)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (hI : S.I = Ideal.span {f}) (hf : f ∈ nonZeroDivisors S.A)
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F)
    (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex (A := S.A) (K := omega))
    (h5 : DepthDimOnDivisor f)
    (nomega : DerivedCategory (ModuleCat.{u} S.A))
    (hnomega : Dualizing.IsNormalizedDualizingComplex.{u, u} nomega)
    (hext : ∃ n : ℕ, IsFiniteLength S.A ↥(LinearMap.range
      (CategoryTheory.Linear.leftComp S.A
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S.A))
          (-(2 : ℤ))).obj nomega)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).map
          ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op))))) :
    CanonicallyExtends S F ∧
      (IsAdicComplete (Ideal.span {f}) S.A →
        (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage
          (kerComapSystem S F)) := by
  classical
  obtain ⟨n, hn⟩ := hext
  have hM0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) :=
    finite_globalSectionsSystem_zero_of_depthDimOnDivisor S ha F f hI hfree omega homega h5
  -- the finiteness side condition under which Stacks 0A06 applies to `RHom_A(M₁, ω⟦-2⟧)`
  obtain ⟨b, hb⟩ := hnomega.1.bounded.1
  have hb' : ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S.A))
      (-(2 : ℤ))).obj nomega).IsGE (b + 2) :=
    let := hb
    DerivedCategory.TStructure.t.isGE_shift nomega b (-(2 : ℤ)) (b + 2) (by omega)
  have hfinK : ∀ n : ℤ, Module.Finite S.A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) n).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := S.A)).hom.obj
          (op ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj
              ((globalSectionsSystem S F).obj (op 0))),
            (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S.A))
              (-(2 : ℤ))).obj nomega))) := fun n =>
    StacksDraft.DerivedHom.finite_homology_derivedHom
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := S.A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj
        ((globalSectionsSystem S F).obj (op 0)))
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S.A))
        (-(2 : ℤ))).obj nomega) 0 (b + 2) inferInstance hb'
      (fun k => Dualizing.finite_homology_single ((globalSectionsSystem S F).obj (op 0)) k)
      (fun k => Dualizing.finite_homology_shift nomega hnomega.1.finiteCohomology (-(2 : ℤ)) k) n
  -- the vanishing direction of local duality: an injective hull of the residue field and a
  -- finite generating family of the maximal ideal
  obtain ⟨iota, hiotaMono, hiota⟩ :=
    Dualizing.LocalDuality.exists_isInjectiveHull_homology_zero_localCohomology.{u, u}
      S.A nomega hnomega
  have := hiotaMono
  obtain ⟨rgen, fgen, hfgen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A))
  change Ideal.span (Set.range fgen) = maximalIdeal S.A at hfgen
  -- the finite length on the local cohomology side, in the local duality spelling
  have hlc :=
    Dualizing.LocalDuality.isFiniteLength_range_homologyMap_localCohomology_of_isFiniteLength_range
      S.A nomega 2 ((globalSectionsSystem S F).obj (op n)) ((globalSectionsSystem S F).obj (op 0))
      ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)
      (fun g hg =>
        Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero
          S.A fgen hfgen nomega hnomega iota hiota 2 g hfinK hg) hn
  -- and in the spelling the Mittag-Leffler criterion consumes
  refine canonicallyExtends_and_isCompletion_of_isFiniteLength_range_localCohomology S ha F f hI
    hf hfree omega homega h5 ⟨n, ?_⟩
  refine isFiniteLength_range_localCohomologyDegreeFunctor_of_eq_maximalIdeal
    S.a (Ideal.fg_of_isNoetherianRing S.a) ha (((1 : ℕ) : ℤ) + 1) _ ?_
  exact hlc

/-- **[Stacks, Tag 0DXU].**  In the situation of [Stacks, Tag 0EHC] let `(ℱₙ)` be an object of
`Coh(U, I𝒪_U)`.  Assume

1. `A` is local and `𝔞 = 𝔪` is the maximal ideal,
2. `A` has a dualizing complex,
3. `I = (f)` is principal for a nonzerodivisor `f`,
4. each `ℱₙ` is finite locally free over `𝒪_U/fⁿ𝒪_U`,
5. `depth((A/f)_𝔭) + dim(A/𝔭) > 1` for every `𝔭 ∈ V(f)` other than `𝔪`, and
6. `depth(A_𝔭) + dim(A/𝔭) > 3` for every `𝔭 ∉ V(f)` with `V(𝔭) ∩ V(f) ≠ {𝔪}`.

Then `(ℱₙ)` extends canonically to `X = Spec(A)`; in particular, if `A` is `I`-adically complete
then `(ℱₙ)` is the completion of a coherent `𝒪_U`-module.

The proof is the source's.  Conditions (b) and (c) of the Mittag-Leffler criterion
[Stacks, Tag 0EHH] come from hypotheses (3), (4) and (5); condition (a) is the finite length of
the image of `H¹(U, ℱₙ) ⟶ H¹(U, ℱ₁)`, which [Stacks, Tag 0BK0] (2) and [Stacks, Tag 0EIR] turn
into the finite length of the image of `H²_𝔪(Mₙ) ⟶ H²_𝔪(M₁)` for `Mₙ = H⁰(U, ℱₙ)`, and which
local duality — in the shape that reads a vanishing of `Ext` back as a vanishing of local
cohomology — reduces to the finite length of the image of
`Ext^{-2}_A(M₁, ω) ⟶ Ext^{-2}_A(Mₙ, ω)`.  That last statement is where hypotheses (2), (4), (5)
and (6) are spent, over the localizations `A_𝔮` at the primes `𝔮 ∈ V(f) ∖ {𝔪}`.  The normalized
dualizing complex the computation needs is produced from hypothesis (2) by
`Dualizing.exists_isNormalizedDualizingComplex_shift`. -/
@[stacks 0DXU]
theorem canonicallyExtends_and_isCompletion_of_depthDim
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (ha : S.a = maximalIdeal S.A)
    (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex (A := S.A) (K := omega))
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (hI : S.I = Ideal.span {f}) (hf : f ∈ nonZeroDivisors S.A)
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F)
    (h5 : DepthDimOnDivisor f) (h6 : DepthDimOffDivisor f) :
    CanonicallyExtends S F ∧
      (IsAdicComplete (Ideal.span {f}) S.A →
        (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage
          (kerComapSystem S F)) := by
  obtain ⟨m, hnorm⟩ :=
    Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} omega homega
  exact canonicallyExtends_and_isCompletion_of_isFiniteLength_range_ext S ha F f hI hf hfree
    omega homega h5
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S.A)) (-m)).obj omega) hnorm
    (exists_isFiniteLength_range_extPrecompGlobalSections S F ha _ hnorm hI hf hfree h5 h6)

end Stacks.Algebraization

end
