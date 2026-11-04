module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CanonicalExtensionDepthThree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.MittagLefflerCdOne

/-!
# Canonical extension in cohomological dimension one, from a pro-isomorphism

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)` that is
pro-isomorphic to an inverse system `(ℱ''ₙ)` of `𝒪_U`-modules. This file assembles the proof of
[Stacks, Tag 0EJI] from three inputs: the Mittag-Leffler property of `(H⁰(U, ℱₙ))`
(`Stacks.Algebraization.isMittagLefflerCategorical_globalSectionsSystem_of_cd_one`), the
agreement of the limit topology with the `I`-adic topology
(`Stacks.Algebraization.limitGlobalSections_topology_eq_adicModuleTopology`), and the finiteness
of the images of the transition maps of `(Hᵖ(U, ℱₙ))`, `p ≤ 1`, which a pro-isomorphism carries
over from the `I`-power torsion subsheaves of the `ℱ''ₙ`.

## Main definitions

* `Stacks.Algebraization.HasFiniteTorsionCohomology` — the maps from `I ^ k`-torsion modules
  factor through a subsheaf with finite `H⁰` and `H¹` on `U`.

## Main results

* `Stacks.Algebraization.finite_range_tr_of_proIso` — the images of the transition maps of
  `(Hᵖ(U, ℱₙ))`, `p ≤ 1`, are eventually finite.
* `Stacks.Algebraization.finite_range_limitProjection_of_torsionFinite` — condition (c) of
  [Stacks, Tag 0EHH].
* `Stacks.Algebraization.canonicallyExtends_of_proIso_of_torsionFinite` — canonical extension
  from those finiteness properties.

## References

* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The property of an `𝒪_U`-module `ℱ''` that, for every `k`, the maps into `ℱ''` from modules
killed by `I ^ k` factor through a subsheaf whose sections and first cohomology on `U` are finite
`A`-modules. For a coherent `ℱ''` with `depth(ℱ''_y) + δ^Y_Z(y) ≥ 3` on `U ∩ Y` the subsheaf is the
`I ^ k`-torsion of `ℱ''`. -/
def HasFiniteTorsionCohomology (G : S.U.toScheme.Modules) : Prop :=
  ∀ k : ℕ, ∃ (K : S.U.toScheme.Modules) (ι : K ⟶ G),
    (∀ {W : S.U.toScheme.Modules} (φ : W ⟶ G),
      (∀ a ∈ S.I ^ k, sectionSmul (scalarMap S a) W = 0) → ∃ φ' : W ⟶ K, φ' ≫ ι = φ) ∧
    Module.Finite S.A ((openSectionsFunctor S).obj K) ∧
      Module.Finite S.A ((openCohomologyFunctor S 1).obj K)

/-- The image of a linear map out of a finite module is finite. -/
theorem finite_range_of_finite {M N : Type u} [AddCommGroup M] [Module S.A M]
    [AddCommGroup N] [Module S.A N] [Module.Finite S.A M] (g : M →ₗ[S.A] N) :
    Module.Finite S.A (LinearMap.range g) :=
  Module.Finite.of_surjective g.rangeRestrict (LinearMap.surjective_rangeRestrict _)

/-- A submodule of a finite module over a Noetherian ring is finite. -/
theorem finite_of_le_of_finite {N : Type u} [AddCommGroup N] [Module S.A N]
    {P Q : Submodule S.A N} (hle : P ≤ Q) (hQ : Module.Finite S.A Q) : Module.Finite S.A P := by
  refine Module.Finite.iff_fg.mpr ?_
  have hmap := (IsNoetherian.noetherian (P.comap Q.subtype)).map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_of_le_right hle] at hmap

/-- **The images of the transition maps are eventually finite**, for any functor to `A`-modules
which is finite on the torsion subsheaves, when `(ℱₙ)` is pro-isomorphic to a system whose terms
have finite torsion cohomology. The transition from level `α(β N)` to level `N` factors through
`ℱ''_{β N}`, and the first map, out of a module killed by `I ^ (α(β N) + 1)`, factors through the
torsion subsheaf. -/
theorem finite_range_tr_of_proIso (G : ℕᵒᵖ ⥤ S.U.toScheme.Modules)
    (e : InverseSequence.ProIso F.obj G) (P : S.U.toScheme.Modules ⥤ ModuleCat.{u} S.A)
    (hP : ∀ n k, ∃ (K : S.U.toScheme.Modules) (ι : K ⟶ G.obj (op n)),
      (∀ {W : S.U.toScheme.Modules} (φ : W ⟶ G.obj (op n)),
        (∀ a ∈ S.I ^ k, sectionSmul (scalarMap S a) W = 0) → ∃ φ' : W ⟶ K, φ' ≫ ι = φ) ∧
      Module.Finite S.A (P.obj K))
    (N : ℕ) :
    Module.Finite S.A (LinearMap.range (P.map
      (tr S F ((e.βle N).trans (e.αle (e.β N))))).hom) := by
  obtain ⟨K, ι, hfac, hfin⟩ := hP (e.β N) (e.α (e.β N) + 1)
  obtain ⟨φ', hφ'⟩ := hfac (e.φ (e.β N)) fun a ha => sectionSmul_term_eq_zero S F _ ha
  have htr : tr S F ((e.βle N).trans (e.αle (e.β N))) = φ' ≫ ι ≫ e.ψ N := by
    rw [← Category.assoc, hφ']
    exact (e.ψφ N).symm
  refine finite_of_le_of_finite S ?_ (finite_range_of_finite S (P.map (ι ≫ e.ψ N)).hom)
  rintro _ ⟨y, rfl⟩
  refine ⟨(P.map φ').hom y, ?_⟩
  rw [htr]
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Condition (c) of [Stacks, Tag 0EHH] from the pro-isomorphism.** -/
theorem finite_range_limitProjection_of_torsionFinite (G : ℕᵒᵖ ⥤ S.U.toScheme.Modules)
    (e : InverseSequence.ProIso F.obj G) (hG : ∀ n, HasFiniteTorsionCohomology S (G.obj (op n)))
    (n : ℕ) :
    Module.Finite S.A
      (LinearMap.range (limit.π (globalSectionsSystem S F) (op n)).hom) := by
  set h := (e.βle n).trans (e.αle (e.β n))
  refine finite_of_le_of_finite S ?_ (finite_range_tr_of_proIso S F G e (openSectionsFunctor S)
    (fun m k => by
      obtain ⟨K, ι, hfac, h0, -⟩ := hG m k
      exact ⟨K, ι, hfac, h0⟩) n)
  rintro _ ⟨x, rfl⟩
  refine ⟨(limit.π (globalSectionsSystem S F) (op (e.α (e.β n)))).hom x, ?_⟩
  rw [← ModuleCat.comp_apply]
  exact congrArg (fun φ => φ.hom x) (limit.w (globalSectionsSystem S F) (homOfLE h).op)

/-- **Canonical extension in cohomological dimension one, from a pro-isomorphism.** In Situation
0EHC with `cd(A, I) = 1`, an object `(ℱₙ)` of `Coh(U, I𝒪_U)` pro-isomorphic to a system of
`𝒪_U`-modules with finite torsion cohomology canonically extends to `X`. -/
theorem canonicallyExtends_of_proIso_of_torsionFinite
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (G : ℕᵒᵖ ⥤ S.U.toScheme.Modules) (e : InverseSequence.ProIso F.obj G)
    (hG : ∀ n, HasFiniteTorsionCohomology S (G.obj (op n))) :
    CanonicallyExtends S F :=
  canonicallyExtends_of_finite_limit_images S F
    (isMittagLefflerCategorical_globalSectionsSystem_of_cd_one S F hcd fun N =>
      ⟨_, _, finite_range_tr_of_proIso S F G e (openCohomologyFunctor S 1)
        (fun m k => by
          obtain ⟨K, ι, hfac, -, h1⟩ := hG m k
          exact ⟨K, ι, hfac, h1⟩) N⟩)
    (limitGlobalSections_topology_eq_adicModuleTopology S F hcd)
    (finite_range_limitProjection_of_torsionFinite S F G e hG)

end Stacks.Algebraization

end
