module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsHigherDirect.CohomologyOfOpen
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CechModelComparison
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.QuasiCoherentExtension

/-!
# Cohomology on the complement of a zero locus is local cohomology, shifted

Let `I` be a finitely generated ideal of a commutative ring `A`, let `Y = V(I)` and let
`U = Spec A \ Y`, viewed as an open subscheme of `Spec A`. This file proves the vanishing form of
Stacks 0DWR in degrees above zero:

`H^n(U, ℱ) = 0  ↔  H^{n+1}_Y(M) = 0`  for `n ≥ 1`,

where `ℱ` is a quasi-coherent module on `U` and `M` an `A`-module with `ℱ = M̃|U`, and `H^n(U, -)`
is the cohomology functor of Stacks 01E3 on the open subscheme. Every quasi-coherent module on
`U` is of that form, by Stacks 0DWR part (1), so the statement covers all of them.

The chain has four steps, each of them proved elsewhere:

1. Stacks 01E1 moves cohomology on the open subscheme `U` to cohomology over the open `U` of
   `Spec A` (`AlgebraicGeometry.cohomologyOverNatIsoRestriction`);
2. Stacks 01F1 replaces the abelian-group-valued cohomology functor of Stacks 01E3 by the
   module-valued right derived functor of sections
   (`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`);
3. Stacks 01EQ and Stacks 01ET compute those right derived functors by the Čech complex of the
   standard covering of `U` by the basic opens of a family of generators of `I`
   (`Stacks.LocalCohomology.cechCohomologyIsoCohomology` and
   `Stacks.LocalCohomology.derivedGlobalSectionsIsoRightDerived`);
4. Stacks 0A6R identifies the Čech cohomology of that covering with local cohomology, shifted by
   one (`Stacks.LocalCohomology.isZero_cechPlusHomology_iff_isZero_localCohomologyModule`).

## Main definitions

* `Stacks.LocalCohomology.hgroupRestrictIso` — Stacks 01E1 in the spelling of Stacks 01E3:
  cohomology of a restricted module on an open subscheme is cohomology over that open.

## Main results

* `Stacks.LocalCohomology.isZero_hgroup_iff_isZero_rightDerived` — the abelian-group-valued and
  the module-valued cohomology of an open vanish together.
* `Stacks.LocalCohomology.isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule` —
  **Stacks 0DWR above degree zero, in the vanishing form.**
* `Stacks.LocalCohomology.isZero_hgroup_of_isQuasicoherent` — **the same for an arbitrary
  quasi-coherent module on `U`**, by the extension result of Stacks 0DWR part (1).
* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_isZero_hgroup` — the converse
  direction, taking the module to be `A` itself.

## Implementation notes

Everything is at module universe equal to the ring universe. That is forced by step 3: Stacks
01ET is available for `SheafOfModules.{u} 𝒪` only, as recorded in the implementation notes of
`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CechSheafCohomology.lean`. The restriction
costs the intended consumer nothing: `Stacks.LocalCohomology.complementTilde` is the sheaf
`M̃|U` at an arbitrary module universe, but Stacks 0DWR part (1) produces its module in the
ring's universe (`Stacks.LocalCohomology.exists_module_iso_restrict_tilde`), and the vanishing
statement for `A`-modules in any universe is obtained from the one for `A` itself by the
descending induction of
`StacksFrontier/RingTheory/LocalCohomology/LongExactSequence/AllModules.lean`.

The comparison of step 3 depends on a chosen finite family of generators of `I`; since all four
steps are isomorphisms, and the statements below are vanishing statements, the choice is
invisible in the conclusion and is made inside the proofs.

`HasDerivedCategory.standard` is pinned as a local instance, as in every file of this
development.

No Stacks tag attribute is placed here: Stacks 0DWR has three parts and only its comparison in
positive degrees is below.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

universe u

namespace Stacks.LocalCohomology

/-! ### Cohomology on an open subscheme -/

/-- **Stacks 01E1 in the spelling of Stacks 01E3.** The cohomology of a module on a scheme over
an open `V`, in the sense of Stacks 01E3, is the cohomology of its restriction over the whole of
the open subscheme `V`.

This is `AlgebraicGeometry.cohomologyOverNatIsoRestriction`, read through two definitional
identifications: `Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso` says that the
functor whose right derived functors `Stacks.Cohomology.Hfunctor` takes *is* module-valued
sections followed by the forgetful functor, and
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` says
that Mathlib's restriction of modules to an open subscheme is the ringed-space restriction the
former is stated for. -/
def hgroupRestrictIso (X : Scheme.{u}) (V : X.Opens) (n : ℕ) (G : X.Modules) :
    Hgroup X.ringCatSheaf V n G ≅
      Hgroup (V : Scheme).ringCatSheaf ⊤ n ((Scheme.Modules.restrictFunctor V.ι).obj G) := by
  rw [Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction]
  exact (AlgebraicGeometry.cohomologyOverNatIsoRestriction
    (asRingSheafedSpace X.toRingedSpace) V n).app G

/-- **The two cohomologies of an open vanish together.** The abelian-group-valued cohomology
functor of Stacks 01E3 and the module-valued right derived functor of sections over the same open
have the same zero objects, by the comparison of Stacks 01F1. -/
theorem isZero_hgroup_iff_isZero_rightDerived {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} R)]
    (V : Opens X) (n : ℕ) (G : SheafOfModules.{u} R) :
    IsZero (Hgroup R V n G) ↔
      IsZero (((SheafOfModules.evaluation R (op V)).rightDerived n).obj G) := by
  rw [← isZero_forget₂_iff (((SheafOfModules.evaluation R (op V)).rightDerived n).obj G)]
  exact ⟨fun h ↦ h.of_iso
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso R V n).app G),
    fun h ↦ h.of_iso
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso R V n).app G).symm⟩

/-! ### The comparison of Stacks 0DWR in positive degrees -/

variable {A : Type u} [CommRing A]

/-- The restriction to `U = Spec A \ V(I)` of the sheaf associated to an `A`-module in the
ring's universe is quasi-coherent: it is the restriction of Mathlib's `tilde`. -/
instance isQuasicoherent_complementTilde (I : Ideal A) (M : ModuleCat.{u} A) :
    (complementTilde A I M).IsQuasicoherent :=
  inferInstanceAs (((Scheme.Modules.restrictFunctor (complementZeroLocus A I).ι).obj
    (tilde M)).IsQuasicoherent)

/-- The module-valued cohomology over `U = Spec A \ V(I)` of `M̃` vanishes in degree `n ≥ 1`
exactly when `H^{n+1}_{V(I)}(M)` does.

This is the Čech computation: `Stacks.LocalCohomology.cechCohomologyIsoCohomology` and
`Stacks.LocalCohomology.derivedGlobalSectionsIsoRightDerived` identify the right derived functors
of sections with the Čech cohomology of the standard covering, and
`Stacks.LocalCohomology.isZero_cechPlusHomology_iff_isZero_localCohomologyModule` identifies
that with local cohomology, shifted. -/
theorem isZero_rightDerived_complement_iff_isZero_localCohomologyModule (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 1 ≤ n) :
    IsZero (((SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
        (op (complementZeroLocus A I))).rightDerived n).obj (associatedSheaf A M)) ↔
      IsZero (localCohomologyModule A I hI M ((n : ℤ) + 1)) := by
  obtain ⟨r, f, hIf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  have hdeg : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
  have hshift : ((q + 1 : ℕ) : ℤ) + 1 = (q : ℤ) + 2 := by push_cast; ring
  rw [hshift]
  refine Iff.trans ?_ (isZero_cechPlusHomology_iff_isZero_localCohomologyModule f I hIf M hI q)
  rw [← hdeg]
  exact ⟨fun h ↦ h.of_iso (cechCohomologyIsoCohomology f I hIf M (q + 1) ≪≫
      derivedGlobalSectionsIsoRightDerived I (associatedSheaf A M) (q + 1)),
    fun h ↦ h.of_iso (cechCohomologyIsoCohomology f I hIf M (q + 1) ≪≫
      derivedGlobalSectionsIsoRightDerived I (associatedSheaf A M) (q + 1)).symm⟩

/-- **Stacks 0DWR above degree zero, in the vanishing form.** For `n ≥ 1` the degree-`n`
cohomology of `M̃|U` on `U = Spec A \ V(I)` is a zero object exactly when the degree-`n+1` local
cohomology of `M` with support in `V(I)` is. -/
theorem isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 1 ≤ n) :
    IsZero (Hgroup (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n
        (complementTilde A I M)) ↔
      IsZero (localCohomologyModule A I hI M ((n : ℤ) + 1)) := by
  refine Iff.trans ?_ (isZero_rightDerived_complement_iff_isZero_localCohomologyModule I hI M n hn)
  refine Iff.trans ?_ (isZero_hgroup_iff_isZero_rightDerived
    (Spec (CommRingCat.of A)).ringCatSheaf (complementZeroLocus A I) n (associatedSheaf A M))
  exact ⟨fun h ↦ h.of_iso (hgroupRestrictIso (Spec (CommRingCat.of A))
      (complementZeroLocus A I) n (associatedSheaf A M)),
    fun h ↦ h.of_iso (hgroupRestrictIso (Spec (CommRingCat.of A))
      (complementZeroLocus A I) n (associatedSheaf A M)).symm⟩

/-! ### An arbitrary quasi-coherent module on the complement -/

/-- **The vanishing of local cohomology above a bound makes every quasi-coherent module on the
complement acyclic above that bound.** For `d ≥ 1`, if `H^i_{V(I)}(M) = 0` for every `A`-module
`M` and every `i > d`, then `H^n(U, ℱ) = 0` for every quasi-coherent module `ℱ` on
`U = Spec A \ V(I)` and every `n ≥ d`.

Stacks 0DWR part (1) — `Stacks.LocalCohomology.exists_module_iso_restrict_tilde` — writes `ℱ` as
`M̃|U`, and the comparison above turns the conclusion into the vanishing of
`H^{n+1}_{V(I)}(M)`, which holds because `n + 1 > d`. -/
theorem isZero_hgroup_of_isQuasicoherent (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : 1 ≤ d)
    (h : ∀ (M : ModuleCat.{u} A) (i : ℤ), d < i → IsZero (localCohomologyModule A I hI M i))
    (F : (complementZeroLocus A I : Scheme).Modules) (hF : F.IsQuasicoherent)
    (n : ℕ) (hn : d ≤ (n : ℤ)) :
    IsZero (Hgroup (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n F) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨M, ⟨e⟩⟩ := exists_module_iso_restrict_tilde A I hI F
  refine ((isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule I hI M n hn1).2
    (h M ((n : ℤ) + 1) (by omega))).of_iso ?_
  exact (Hfunctor (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n).mapIso e

/-- **The converse direction.** If `H^n(U, ℱ) = 0` for every quasi-coherent module `ℱ` on
`U = Spec A \ V(I)` and every `n ≥ d`, with `d ≥ 1`, then `H^i_{V(I)}(A) = 0` for every `i > d`.

Only one quasi-coherent module is used, namely `Ã|U`; the degrees `i > d` are exactly the
degrees `n + 1` for `n ≥ d`, and `d ≥ 1` keeps `n ≥ 1`, which is where the comparison holds. -/
theorem isZero_localCohomologyModule_of_isZero_hgroup (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hd : 1 ≤ d)
    (h : ∀ (F : (complementZeroLocus A I : Scheme).Modules), F.IsQuasicoherent →
      ∀ n : ℕ, d ≤ (n : ℤ) → IsZero (Hgroup (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n F))
    (i : ℤ) (hi : d < i) :
    IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  have hn1 : 1 ≤ n := by omega
  refine (isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule I hI
    (ModuleCat.of A A) n hn1).1 ?_
  exact h (complementTilde A I (ModuleCat.of A A)) inferInstance n (by omega)

end Stacks.LocalCohomology

end
