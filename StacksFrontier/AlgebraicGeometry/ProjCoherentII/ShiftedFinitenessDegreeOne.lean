module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.ProjCoherentDegreeOne.GradedSections
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TwistedToShiftedScalar
public import StacksFrontier.AlgebraicGeometry.ProjCoherentModule.Basic

/-!
# Finiteness of `N' = ⨁_{n ≥ k} Γ(Proj A, M(n)~)` for a ring generated in degree one

Let `A` be a graded ring with `A₀` Noetherian, generated over `A₀` by finitely many elements of
`A₁`, let `M` be a finite graded `A`-module, `X = Proj A` and `k ∈ ℤ`. [Stacks, Tag 0B5R] studies
the two graded `A`-modules

`N  = ⨁_{n ≥ k} Γ(X, M̃(n))`   and   `N' = ⨁_{n ≥ k} Γ(X, M(n)~)`,

and its part (1) asserts that `N'` is a finite `A`-module. This file proves that assertion under
the degree-one hypothesis, which is the case the source reduces the general one to by the Veronese
trick.

The proof is the composition of three known facts. `A` is Noetherian, so `M̃` is coherent, so
assertion (4) of [Stacks, Tag 0AG6] makes `N` a finite `A`-module. The comparison `N → N'` of part
(3) of the tag — the global sections of the canonical map `M̃ ⊗ 𝒪(n) → M(n)~` of
[Stacks, Tag 01MQ], assembled over the direct sum — is bijective in every degree, since the
standard opens of the degree-one elements already cover `X`; and it is `A`-linear. So `N ≅ N'` as
`A`-modules and the finiteness transports.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.ProjCoherentII`.

* `twistedToShiftedSections_eq_map`: the assembled comparison is the coordinatewise
  `DirectSum.map` of the degreewise comparisons.
* `bijective_twistedToShiftedSections`: a degreewise bijective comparison is bijective.
* `twistedToShiftedLinearMap`: the comparison `⨁_n Γ(X, M̃(n)) → ⨁_n Γ(X, M(n)~)` as an
  `A`-linear map.
* `map_truncation_twistedToShiftedLinearMap`: a degreewise bijective comparison carries the
  degree-`≥ k` truncation of the source *onto* the degree-`≥ k` truncation of the target.
* `moduleFinite_shiftedTruncation_of_degreeOne`: **`N'` is a finite `A`-module**, which is
  [Stacks, Tag 0B5R] (1) for a graded ring generated in degree one.

## Implementation notes

Bijectivity of the assembled comparison is not reproved from scratch: `DirectSum.map_injective`
and `DirectSum.map_surjective` already say that a coordinatewise map of direct sums is injective
(surjective) exactly when every coordinate is, so the only work is identifying
`Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections` — defined as a
`DirectSum.toAddMonoid` of the degreewise maps followed by the inclusions of the summands — with
`DirectSum.map` of those same degreewise maps. That identification is
`twistedToShiftedSections_eq_map`, and it is exactly `twistedToShiftedSections_component` read
through `DirectSum.apply_eq_component`.

The truncations are handled abstractly. `map_truncation_twistedToShiftedLinearMap` takes the two
submodules together with the statement that each is cut out by the vanishing of the components in
degrees `< k`, rather than naming
`Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule.truncation` and
`Stacks.AlgebraicGeometry.ProjShiftedSections.GlobalSectionsModuleMap.truncation`: both of those
are cut out by exactly that condition, so the hypotheses are supplied by reflexivity, and the
lemma does not have to repeat their module-structure plumbing. The forward inclusion is the one
already recorded by `truncatedTwistedToShifted`; the reverse one is the only new content, and it
needs the *injectivity* of the degreewise comparison, which is why the hypothesis is bijectivity
in every degree and not merely the existence of the map.

The degree-one hypothesis enters only twice: through
`Stacks.ProjCoherentDegreeOne.isNoetherianRing`, which is what makes `M̃` coherent, and through
`Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.degreeOpen_one_eq_top`, which is the hypothesis
of `bijective_twistedToShiftedComponent` at `d = 1`; every integer is divisible by `1`, so the
comparison is bijective in *every* degree and no residue-class bookkeeping appears.

`Stacks.ProjCoherentDegreeOne.moduleFinite_truncation` asks for a generating family indexed by
`Fin (m + 1 + 1)`, the padding of
`Stacks.ProjCoherentDegreeOne.exists_two_le_generators` being what lets the statements proved on
`ℙⁿ` for `n ≥ 1` be applied; the family of the hypothesis here is padded by that lemma.

No `stacks` attribute is attached. Part (1) of [Stacks, Tag 0B5R] is asserted without a
degree-one hypothesis, and the Veronese reduction that removes it is not finished.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (associatedModuleSheaf twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent shiftedModuleGlobalSections globalSectionsModuleMap)
open Stacks.AlgebraicGeometry.ProjTwistedSections
  (twistedSectionsComponent twistedGlobalSectionsModule)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjCoherentII

universe u w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

section Comparison

variable {S : Type u} {M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The comparison `N → N'` of [Stacks, Tag 0B5R] (3) is the coordinatewise map of the
degreewise comparisons.** Both sides have the same components, by
`twistedToShiftedSections_component`. -/
public theorem twistedToShiftedSections_eq_map :
    twistedToShiftedSections 𝒮 𝒨 = DirectSum.map (twistedToShiftedComponent 𝒮 𝒨) :=
  AddMonoidHom.ext fun z => DirectSum.ext fun n => by
    have h := twistedToShiftedSections_component 𝒮 𝒨 z n
    rw [← DirectSum.apply_eq_component, ← DirectSum.apply_eq_component] at h
    rw [DirectSum.map_apply]
    exact h

/-- **A degreewise bijective comparison is bijective.** The assembled comparison is the
coordinatewise map of the degreewise ones, and a coordinatewise map of direct sums is injective
(surjective) exactly when each coordinate is. -/
public theorem bijective_twistedToShiftedSections
    (hbij : ∀ n : ℤ, Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n)) :
    Function.Bijective (twistedToShiftedSections 𝒮 𝒨) := by
  rw [twistedToShiftedSections_eq_map]
  exact ⟨(DirectSum.map_injective (twistedToShiftedComponent 𝒮 𝒨)).mpr fun n => (hbij n).1,
    (DirectSum.map_surjective (twistedToShiftedComponent 𝒮 𝒨)).mpr fun n => (hbij n).2⟩

section Linear

variable [Module S (twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨))]
  [Module S (shiftedModuleGlobalSections 𝒮 𝒨)]
  (hsmul : ∀ (c : S) (z : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)),
    twistedToShiftedSections 𝒮 𝒨 (c • z) = c • twistedToShiftedSections 𝒮 𝒨 z)

/-- **The comparison `⨁_n Γ(X, M̃(n)) → ⨁_n Γ(X, M(n)~)` of [Stacks, Tag 0B5R] (3) as an
`S`-linear map.** The hypothesis `hsmul` is its compatibility with the scalar actions, which for
the two canonical graded module structures is
`Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedSections_smul`. -/
public def twistedToShiftedLinearMap :
    twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨) →ₗ[S]
      shiftedModuleGlobalSections 𝒮 𝒨 where
  toFun := twistedToShiftedSections 𝒮 𝒨
  map_add' := map_add _
  map_smul' := hsmul

/-- **A degreewise bijective comparison carries `N` onto `N'`.** The two truncations are cut out
by the vanishing of the components in degrees `< k`, and the comparison is degreewise, so a
section has vanishing low components exactly when its image does; the reverse implication is
where the injectivity of the degreewise comparison is used. -/
public theorem map_truncation_twistedToShiftedLinearMap
    (hbij : ∀ n : ℤ, Function.Bijective (twistedToShiftedComponent 𝒮 𝒨 n)) (k : ℤ)
    (P : Submodule S (twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨)))
    (hP : ∀ z : twistedGlobalSections 𝒮 (associatedModuleSheaf 𝒮 𝒨), z ∈ P ↔
      ∀ n : ℤ, n < k → DirectSum.component ℤ ℤ
        (fun j : ℤ => twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) j) n z = 0)
    (Q : Submodule S (shiftedModuleGlobalSections 𝒮 𝒨))
    (hQ : ∀ w : shiftedModuleGlobalSections 𝒮 𝒨, w ∈ Q ↔
      ∀ n : ℤ, n < k → DirectSum.component ℤ ℤ
        (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n w = 0) :
    Submodule.map (twistedToShiftedLinearMap 𝒮 𝒨 hsmul) P = Q := by
  refine le_antisymm (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨z, hz, rfl⟩ := hw
    refine (hQ _).mpr fun n hn => ?_
    show DirectSum.component ℤ ℤ (fun j : ℤ => shiftedSectionsComponent 𝒮 𝒨 j) n
      (twistedToShiftedSections 𝒮 𝒨 z) = 0
    rw [twistedToShiftedSections_component, (hP z).mp hz n hn, map_zero]
  · obtain ⟨z, hzw⟩ := bijective_twistedToShiftedSections 𝒮 𝒨 hbij |>.2 w
    refine ⟨z, (hP z).mpr fun n hn => (hbij n).1 ?_, hzw⟩
    rw [map_zero, ← twistedToShiftedSections_component, hzw]
    exact (hQ w).mp hw n hn

end Linear

end Comparison

/-- **[Stacks, Tag 0B5R] (1) for a graded ring generated in degree one.** Let `A` be a graded ring
whose degree-zero part is Noetherian and which is generated over `A₀` by finitely many elements of
`A₁`, let `M` be a finite graded `A`-module and `X = Proj A`. Then for every `k ∈ ℤ` the graded
`A`-module

`N' = ⨁_{n ≥ k} Γ(X, M(n)~)`

is a finite `A`-module.

`A` is Noetherian, so `M̃` is coherent and assertion (4) of [Stacks, Tag 0AG6] makes
`N = ⨁_{n ≥ k} Γ(X, M̃(n))` a finite `A`-module. The standard opens of the degree-one elements
cover `X`, so the comparison `N → N'` of part (3) of the tag is bijective in every degree — every
integer being divisible by `1` — hence bijective; it is `A`-linear, and it matches the two
truncations, so `N ≅ N'` as `A`-modules. -/
public theorem moduleFinite_shiftedTruncation_of_degreeOne
    {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing (𝒜 0)]
    {n : ℕ} (x : Fin (n + 1) → A) (hx : ∀ i, x i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {τ : Type u} [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ)
    [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒜 𝒨] (k : ℤ) :
    letI := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
    Module.Finite A ((globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 k) := by
  have : IsNoetherianRing A := Stacks.ProjCoherentDegreeOne.isNoetherianRing 𝒜 x hx hgen
  obtain ⟨m, y, hy, hygen⟩ :=
    Stacks.ProjCoherentDegreeOne.exists_two_le_generators 𝒜 x hx hgen
  let := (twistedGlobalSectionsModule 𝒜 (associatedModuleSheaf 𝒜 𝒨)).moduleInst
  let := (globalSectionsModuleMap 𝒜 𝒨).moduleInst
  have hN : Module.Finite A
      (ProjTwistedSections.TwistedGlobalSectionsModule.truncation 𝒜
        (associatedModuleSheaf 𝒜 𝒨)
        (twistedGlobalSectionsModule 𝒜 (associatedModuleSheaf 𝒜 𝒨)) k) :=
    Stacks.ProjCoherentDegreeOne.moduleFinite_truncation 𝒜 (associatedModuleSheaf 𝒜 𝒨) y hy hygen
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheaf 𝒜 𝒨)
      (twistedGlobalSectionsModule 𝒜 (associatedModuleSheaf 𝒜 𝒨)) k
  have hbij : ∀ j : ℤ, Function.Bijective (twistedToShiftedComponent 𝒜 𝒨 j) := fun j =>
    bijective_twistedToShiftedComponent 𝒜 𝒨
      (Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.degreeOpen_one_eq_top 𝒜
        (Stacks.ProjCoherentDegreeOne.adjoin_degreeOne_eq_top 𝒜 x hx hgen))
      (by simp)
  have hinj : Function.Injective
      (twistedToShiftedLinearMap 𝒜 𝒨 (twistedToShiftedSections_smul 𝒜 𝒨)) :=
    (bijective_twistedToShiftedSections 𝒜 𝒨 hbij).1
  have hmap := map_truncation_twistedToShiftedLinearMap 𝒜 𝒨
    (twistedToShiftedSections_smul 𝒜 𝒨) hbij k
    (ProjTwistedSections.TwistedGlobalSectionsModule.truncation 𝒜 (associatedModuleSheaf 𝒜 𝒨)
      (twistedGlobalSectionsModule 𝒜 (associatedModuleSheaf 𝒜 𝒨)) k)
    (fun _ => Iff.rfl) ((globalSectionsModuleMap 𝒜 𝒨).truncation 𝒜 𝒨 k) (fun _ => Iff.rfl)
  exact Module.Finite.equiv
    ((Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ hmap))

end Stacks.AlgebraicGeometry.ProjCoherentII

end
