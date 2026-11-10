module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.Examples.Completion.CompleteModulesEquivAdicSystems
public import StacksFrontier.RingTheory.Dualizing.ExtBaseChangeCompletedAway
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleCodescent
public import StacksFrontier.Homology.ExtendScalars.Localization
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Module

/-!
# A finite module model becomes an adic system over a chart of the punctured spectrum

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`. A *finite module
model* `(M_n)` (`Stacks.Algebraization.IsFiniteModuleModel`) has finite terms annihilated by
powers of `I`, but its transition maps are only controlled up to `𝔞`-power torsion: clause (3)
provides a factoring map `M_{n+1}/Iⁿ⁺¹M_{n+1} → M_n` whose kernel and cokernel are `𝔞`-power
torsion, not an isomorphism. So `(M_n)` is *not* an adic system in the sense of
`Stacks.Examples.IsAdicModuleSystem`, whose transitions are surjective with kernel exactly
`Iⁿ⁺¹M_{n+1}`.

Over a chart `D(f)` of the punctured spectrum the gap closes. Inverting an `f ∈ 𝔞` kills
`𝔞`-power torsion, so clause (3)'s comparison map becomes *bijective* in `A[1/f]`, and the
localized system `(M_n[1/f])` is an honest adic system along `I A[1/f]`. That is what makes the
vertex of [Stacks, Tag 0EHK] exist: `Dualizing.finite_adicCompletion_limit` and
`Dualizing.adicSystemQuotNatIso`, both stated for an adic system, then produce the finite module
`M = (lim M_{n,f})^∧` over `B = (A_f)^∧_I` whose adic quotients are the `M_{n,f}`.

## Main results

* `Stacks.Examples.IsAdicModuleSystem.of_natIso` — being an adic system is invariant under
  isomorphism of systems.
* `Stacks.Algebraization.isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel` — the
  bridge: the system of localizations of a finite module model away from an element of `𝔞` is an
  adic system along the extended ideal.
* `Stacks.Algebraization.isAdicModuleSystem_extendScalars_of_isFiniteModuleModel` — the same
  bridge in the extension-of-scalars spelling, which is the one
  `Stacks.Algebraization.dualizingExtSystemLocalizationNatIso` localizes systems in.
* `Stacks.Algebraization.finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel`
  — the vertex over the chart is a *finite* module over `B = (A_f)^∧_I`.
* `Stacks.Algebraization.localizedModuleFunctorAdicQuotientNatIso` — its tower of adic quotients
  is the localized model, as an isomorphism of systems.

## Implementation notes

Nothing about the comparison map is reproved here. Its bijectivity after inverting `f` is
`bijective_isLocalizedModule_map_of_isIPowerTorsion`, and the kernel of the localized transition
map is computed from Mathlib's exactness of localization (`IsLocalizedModule.map_exact`), the
identification of the range of a localized map
(`LinearMap.range_localizedMap_eq_localized₀_range`) and `Submodule.localized₀_smul` with
`Submodule.localized₀_top`. The `𝔞`-torsion hypotheses enter only through the first of these.

The localized system is taken in the `ModuleCat.localizedModuleFunctor` spelling rather than the
`ModuleCat.extendScalars` one, because the former's objects carry the `IsLocalizedModule`
instance the proof reasons with, while the latter's carrier is a tensor product formed over a
restriction of scalars and has no `A`-module structure to hand. The two functors are isomorphic
by `extendScalars_iso_localizedModuleFunctor`, which is why the second spelling needs no second
proof.

Clause (2) of the model is not used: annihilation of `M_n` by `Iⁿ⁺¹` is a *consequence* of being
an adic system (`Stacks.Examples.IsAdicModuleSystem.pow_smul_top_eq_bot`), so deriving it from
the model as well would be redundant.

## References

* [The Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
* [The Stacks Project, Lemma 52.11.1 (0DXT)](https://stacks.math.columbia.edu/tag/0DXT)
* [The Stacks Project, Lemma 51.8.2 (0BK0)](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped Pointwise

universe u

namespace Stacks.Examples

/-- **Being an adic system of modules is invariant under isomorphism of systems.** Each
transition map of the second system is the corresponding transition of the first conjugated by
the components of the isomorphism. Surjectivity is then a composite of surjections, and the
kernel is carried across by `Submodule.comap_equiv_eq_map_symm`, after which the ideal-power
multiple is preserved because the component is surjective (`Submodule.map_smul''`). -/
public theorem IsAdicModuleSystem.of_natIso {R : Type u} [CommRing R] (I : Ideal R)
    {S S' : ℕᵒᵖ ⥤ ModuleCat.{u} R} (e : S ≅ S') (hS : IsAdicModuleSystem I S) :
    IsAdicModuleSystem I S' := by
  have hcomp : ∀ n : ℕ, (S'.map (homOfLE (Nat.le_succ n)).op).hom =
      ((CategoryTheory.Iso.app e (op n)).toLinearEquiv.toLinearMap.comp
          (S.map (homOfLE (Nat.le_succ n)).op).hom).comp
        (CategoryTheory.Iso.app e (op (n + 1))).toLinearEquiv.symm.toLinearMap := by
    intro n
    have h : e.inv.app (op (n + 1)) ≫ S.map (homOfLE (Nat.le_succ n)).op ≫ e.hom.app (op n) =
        S'.map (homOfLE (Nat.le_succ n)).op := by
      rw [← Category.assoc, ← e.inv.naturality (homOfLE (Nat.le_succ n)).op, Category.assoc,
        e.inv_hom_id_app, Category.comp_id]
    rw [← h]
    rfl
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [hcomp n]
    exact (CategoryTheory.Iso.app e (op n)).toLinearEquiv.surjective.comp
      ((hS.1 n).comp (CategoryTheory.Iso.app e (op (n + 1))).toLinearEquiv.symm.surjective)
  · rw [hcomp n, LinearMap.ker_comp, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr (CategoryTheory.Iso.app e (op n)).toLinearEquiv.injective),
      hS.2 n, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm, Submodule.map_smul'',
      Submodule.map_top, LinearMap.range_eq_top.mpr
        (CategoryTheory.Iso.app e (op (n + 1))).toLinearEquiv.surjective]

end Stacks.Examples

namespace Stacks.Algebraization

/-- One index of `isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel`, with the
factorisation of clause (3) supplied explicitly. Inverting `f ∈ 𝔞` makes the comparison map `g`
bijective, so the localized transition map is the localized projection onto `N ⧸ Q`: surjective,
with kernel the localization of `Q`. -/
private theorem localizedMap_surjective_and_ker_of_factorisation
    {A : Type u} [CommRing A] {a : Ideal A} {f : A} (hf : f ∈ a)
    {N P : ModuleCat.{u} A} (t : N ⟶ P) (Q : Submodule A N)
    (g : (N ⧸ Q) →ₗ[A] P) (hgc : g.comp Q.mkQ = t.hom)
    (hgk : IsIPowerTorsion A (LinearMap.ker g) a)
    (hgcok : IsIPowerTorsion A (P ⧸ LinearMap.range g) a) :
    Function.Surjective (IsLocalizedModule.map (Submonoid.powers f)
        (N.localizedModuleMkLinearMap (Submonoid.powers f))
        (P.localizedModuleMkLinearMap (Submonoid.powers f)) t.hom) ∧
      LinearMap.ker (IsLocalizedModule.map (Submonoid.powers f)
          (N.localizedModuleMkLinearMap (Submonoid.powers f))
          (P.localizedModuleMkLinearMap (Submonoid.powers f)) t.hom) =
        Submodule.localized₀ (Submonoid.powers f)
          (N.localizedModuleMkLinearMap (Submonoid.powers f)) Q := by
  set T := Submonoid.powers f with hT
  set lN := N.localizedModuleMkLinearMap T with hlN
  set lP := P.localizedModuleMkLinearMap T with hlP
  set lQ := LocalizedModule.mkLinearMap T (N ⧸ Q) with hlQ
  set lQs := LocalizedModule.mkLinearMap T Q with hlQs
  have hdec : IsLocalizedModule.map T lN lP t.hom =
      (IsLocalizedModule.map T lQ lP g).comp (IsLocalizedModule.map T lN lQ Q.mkQ) := by
    rw [← hgc, IsLocalizedModule.map_comp' T lN lQ lP Q.mkQ g]
  have hgbij : Function.Bijective (IsLocalizedModule.map T lQ lP g) :=
    bijective_isLocalizedModule_map_of_isIPowerTorsion a g lQ lP hgk hgcok hf
  have hmkQsurj : Function.Surjective (IsLocalizedModule.map T lN lQ Q.mkQ) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_localizedMap_eq_localized₀_range T lN lQ,
      LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective Q), Submodule.localized₀_top]
  have hmkQker : LinearMap.ker (IsLocalizedModule.map T lN lQ Q.mkQ) =
      Submodule.localized₀ T lN Q := by
    rw [(IsLocalizedModule.map_exact T lQs lN lQ Q.subtype Q.mkQ
      (LinearMap.exact_subtype_mkQ Q)).linearMap_ker_eq,
      LinearMap.range_localizedMap_eq_localized₀_range T lQs lN, Submodule.range_subtype]
  refine ⟨hdec ▸ hgbij.2.comp hmkQsurj, ?_⟩
  rw [hdec, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hgbij.1), hmkQker]

/-- **The localizations of a finite module model away from an element of `𝔞` form an adic
system.** Let `(M_n)` be a finite module model for an algebraization situation `A, I ⊆ 𝔞` and let
`f ∈ 𝔞`. Then the system `n ↦ (M_n)_f` of `A[1/f]`-modules has surjective transition maps whose
kernels are exactly the `(n+1)`-st power multiples of the extended ideal `I A[1/f]`, that is, it
is an `I A[1/f]`-adic system in the sense of `Stacks.Examples.IsAdicModuleSystem`.

Clause (3) of the model factors the transition `M_{n+1} → M_n` as the projection onto
`M_{n+1}/Iⁿ⁺¹M_{n+1}` followed by a map `g` with `𝔞`-power torsion kernel and cokernel.
Inverting `f` makes `g` bijective
(`bijective_isLocalizedModule_map_of_isIPowerTorsion`), so the localized transition map *is* the
localized projection: surjective, with kernel the localization of `Iⁿ⁺¹M_{n+1}`, which is
`(I A[1/f])ⁿ⁺¹` times the whole localized module. -/
public theorem isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel
    (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (hM : IsFiniteModuleModel S M) {f : S.A} (hf : f ∈ S.a) :
    Stacks.Examples.IsAdicModuleSystem
      (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
      (M ⋙ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers f)) := by
  have main : ∀ n : ℕ, Function.Surjective (IsLocalizedModule.map (Submonoid.powers f)
        ((M.obj (op (n + 1))).localizedModuleMkLinearMap (Submonoid.powers f))
        ((M.obj (op n)).localizedModuleMkLinearMap (Submonoid.powers f))
        (M.map (homOfLE (Nat.le_succ n)).op).hom) ∧
      LinearMap.ker (IsLocalizedModule.map (Submonoid.powers f)
          ((M.obj (op (n + 1))).localizedModuleMkLinearMap (Submonoid.powers f))
          ((M.obj (op n)).localizedModuleMkLinearMap (Submonoid.powers f))
          (M.map (homOfLE (Nat.le_succ n)).op).hom) =
        S.I ^ (n + 1) • (⊤ : Submodule S.A
          ((M.obj (op (n + 1))).localizedModule (Submonoid.powers f))) := by
    intro n
    obtain ⟨g, hgc, hgk, hgcok⟩ := hM.2.2 n
    obtain ⟨hsurj, hker⟩ := localizedMap_surjective_and_ker_of_factorisation hf
      (M.map (homOfLE (Nat.le_succ n)).op) _ g hgc hgk hgcok
    refine ⟨hsurj, hker.trans ?_⟩
    rw [Submodule.localized₀_smul, Submodule.localized₀_top]
  refine ⟨fun n => (main n).1, fun n => ?_⟩
  change LinearMap.ker ((ModuleCat.localizedModuleMap (Submonoid.powers f)
      (M.map (homOfLE (Nat.le_succ n)).op)).hom) =
    (S.I.map (algebraMap S.A (Localization (Submonoid.powers f)))) ^ (n + 1) •
      (⊤ : Submodule (Localization (Submonoid.powers f))
        ((M.obj (op (n + 1))).localizedModule (Submonoid.powers f)))
  refine Submodule.restrictScalars_injective S.A _ _ ?_
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top,
    ← (main n).2]
  rfl

/-- **The bridge in the extension-of-scalars spelling.** Extension of scalars along
`A → A[1/f]` is the localized-module functor
(`extendScalars_iso_localizedModuleFunctor`), so
`Stacks.Algebraization.isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel`
transports along that isomorphism of systems. This is the spelling in which
`Stacks.Algebraization.dualizingExtSystemLocalizationNatIso` localizes a system, so it is the one
the route of [Stacks, Tag 0EHK] composes with. -/
public theorem isAdicModuleSystem_extendScalars_of_isFiniteModuleModel
    (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (hM : IsFiniteModuleModel S M) {f : S.A} (hf : f ∈ S.a) :
    Stacks.Examples.IsAdicModuleSystem
      (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
      (M ⋙ ModuleCat.extendScalars.{u, u, u}
        (algebraMap S.A (Localization (Submonoid.powers f)))) :=
  Stacks.Examples.IsAdicModuleSystem.of_natIso _
    (Functor.isoWhiskerLeft M
      (extendScalars_iso_localizedModuleFunctor.{u, u} (Submonoid.powers f))).symm
    (isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel S M hM hf)

/-! ### The vertex over the chart -/

/-- The terms of the localized system are finite over the localized ring: localization is base
change along `A → A[1/f]`, and base change of a finite module is finite.

Public because it is the hypothesis `hfin` of `Dualizing.extendScalarsAdicSystemNatIso` read at
the chart, which `Stacks.Algebraization.chartAdicQuotientModuleSystemNatIso` supplies. -/
public theorem finite_localizedModule_of_finite (S : AlgebraizationSituation.{u})
    (N : ModuleCat.{u} S.A) (hN : Module.Finite S.A N) (f : S.A) :
    Module.Finite (Localization (Submonoid.powers f))
      (N.localizedModule (Submonoid.powers f)) := by
  have := hN
  have := Module.Finite.base_change S.A (Localization (Submonoid.powers f)) (N : Type u)
  exact Module.Finite.equiv (IsLocalizedModule.isBaseChange (Submonoid.powers f)
    (Localization (Submonoid.powers f)) (N.localizedModuleMkLinearMap (Submonoid.powers f))).equiv

/-- **The vertex of [Stacks, Tag 0EHK] over a chart of the punctured spectrum: it is a finite
module.** For a finite module model `(M_n)` and an `f ∈ 𝔞`, the limit of the localized system
`(M_{n,f})`, completed along the extended ideal, is a *finite* module over
`B = (A[1/f])^∧_{I A[1/f]}` — the ring `Rig.CompletedAway S.I f`.

This is `Dualizing.finite_adicCompletion_limit` at the ring `A[1/f]`, which is Noetherian, and at
the adic system supplied by
`Stacks.Algebraization.isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel`. Over `A`
itself there is no such module: the limit of a finite module model need not be finite, and the
counterexample is recorded with
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_support`. -/
public theorem finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel
    (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (hM : IsFiniteModuleModel S M) {f : S.A} (hf : f ∈ S.a) :
    Module.Finite
      (AdicCompletion (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
        (Localization (Submonoid.powers f)))
      (AdicCompletion (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
        (Limits.limit (M ⋙ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers f)) :
          ModuleCat.{u} (Localization (Submonoid.powers f)))) :=
  Dualizing.finite_adicCompletion_limit _
    (isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel S M hM hf)
    (finite_localizedModule_of_finite S (M.obj (op 0)) (hM.1 0) f)

/-- **The vertex of [Stacks, Tag 0EHK] over a chart of the punctured spectrum: its adic quotients
are the localized terms.** The tower of adic quotients `M ⧸ Iⁿ⁺¹ M` of the finite
`B`-module `M = (lim M_{n,f})^∧` of
`Stacks.Algebraization.finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel`
is, as a *system*, the localized system `(M_{n,f})` itself.

This is `Dualizing.adicSystemQuotNatIso` at the same data, and it is the second half of what the
globalization of `hconst` asks of the vertex: with the module finite over `B` and its adic
quotients identified with the terms of the localized model, the maps `β` are the transitions of
the tower. The identification is `A[1/f]`-linear, which is no loss: an `A[1/f]`-linear map between
`B`-modules is `B`-linear by `Stacks.Coherent.completion_linearMap_smul`. -/
public def localizedModuleFunctorAdicQuotientNatIso (S : AlgebraizationSituation.{u})
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (hM : IsFiniteModuleModel S M) {f : S.A} (hf : f ∈ S.a) :
    Stacks.Examples.adicQuotientTower
        ((S.I.map (algebraMap S.A (Localization (Submonoid.powers f)))).map (algebraMap
          (Localization (Submonoid.powers f))
          (AdicCompletion (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
            (Localization (Submonoid.powers f)))))
        (ModuleCat.of
          (AdicCompletion (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
            (Localization (Submonoid.powers f)))
          (AdicCompletion (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
            (Limits.limit (M ⋙ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers f)) :
              ModuleCat.{u} (Localization (Submonoid.powers f))))) ⋙
      ModuleCat.restrictScalars (algebraMap (Localization (Submonoid.powers f))
        (AdicCompletion (S.I.map (algebraMap S.A (Localization (Submonoid.powers f))))
          (Localization (Submonoid.powers f)))) ≅
      M ⋙ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers f) :=
  Dualizing.adicSystemQuotNatIso _
    (isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel S M hM hf)

end Stacks.Algebraization

end
