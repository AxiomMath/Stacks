module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.SecondFactorFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.Main
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Stein factorization of a proper flat morphism with geometrically reduced fibres

Let `f : X ⟶ S` be a proper morphism of schemes which is flat, of finite presentation and has
geometrically reduced fibres, and let `X ⟶ S' ⟶ S` be its Stein factorization, with
`S' = f.normalization` the normalization of `S` in `X`. Then the second factor
`f.fromNormalization : S' ⟶ S` is finite étale.

## Main results

* `Stacks.SteinFactorization.etale_fromNormalization_of_properFlat` and
  `Stacks.SteinFactorization.isFinite_fromNormalization_of_properFlat`: the two properties of
  the second factor.
* `Stacks.SteinFactorization.isFinite_and_etale_fromNormalization_of_properFlat`: the two
  together.

## Proof

Near a point `s ∈ S` with geometrically reduced fibre, the algebra `f_* 𝒪_X` is finite étale over
`𝒪_S`: the result
`StacksDraft.Perfect.GeomReducedFibre.exists_open_finiteEtale_and_derivedPushforward_splitting`
produces an open neighbourhood `W` of `s` such that `Γ(S, V) ⟶ Γ(X, f⁻¹V)` is a finite étale ring
map for every affine open `V ⊆ W`. Since the affine opens form a basis, `s` has an *affine* open
neighbourhood `V ⊆ W`, so every point of `S` lies in an affine open over which the structure map
of `f_* 𝒪_X` is étale.

Étaleness of a morphism of schemes is Zariski-local on the target, so this cover suffices:
`Stacks.SteinFactorization.etale_toBase_pushforwardSpectrum_of_cover` checks étaleness of the
structure morphism of `Spec_S(f_* 𝒪_X)` over the members of any affine open cover of `S`, through
the chart isomorphism of the relative spectrum. The identification
`AlgebraicGeometry.normalizationIsoPushforwardSpectrum_hom_comp_toBase` of the second factor of
the Stein factorization with that structure morphism transfers the conclusion to
`f.fromNormalization`, and finiteness then costs nothing: the second factor is integral for every
universally closed quasi-separated morphism, and an étale morphism is locally of finite type.

## References

* [Stacks Project, Tag 0BUN](https://stacks.math.columbia.edu/tag/0BUN)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
* [SGA1, Exposé X, Proposition 1.2]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Étaleness of the second factor from an affine open cover of the base -/

section Cover

variable [UniversallyClosed f] [QuasiSeparated f]

/-- The structure morphism `Spec_S(f_* 𝒪_X) ⟶ S` is étale as soon as the structure map
`Γ(S, U) ⟶ Γ(X, f⁻¹U)` is étale for the members `U` of a single affine open cover of `S`. -/
public theorem etale_toBase_pushforwardSpectrum_of_cover {ι : Type*} (U : ι → S.affineOpens)
    (hcov : ⨆ i, (U i).1 = ⊤)
    (h : ∀ i, ((pushforwardSituation f).algebra.hom.hom.app (op (U i).1)).hom.Etale) :
    Etale (pushforwardSpectrum f).toBase := by
  have : IsZariskiLocalAtTarget @Etale := HasRingHomProperty.instIsZariskiLocalAtTarget @Etale
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale) (fun i ↦ (U i).1) hcov]
  intro i
  rw [← chartIsoPreimage_inv_comp_specSectionsToOpen f (U i)]
  have := etale_specSectionsToOpen f (U i) (h i)
  infer_instance

/-- The second factor of the factorization of `f` through the normalization of `S` in `X` is
étale as soon as every point of `S` has an affine open neighbourhood `U` over which the structure
map `Γ(S, U) ⟶ Γ(X, f⁻¹U)` is étale. -/
public theorem etale_fromNormalization_of_exists_etale_app
    (h : ∀ s : S, ∃ U : S.affineOpens, s ∈ U.1 ∧
      ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale) :
    Etale f.fromNormalization := by
  classical
  choose U hmem hetale using h
  have hcov : ⨆ s : S, (U s).1 = ⊤ :=
    top_unique fun s _ ↦ Opens.mem_iSup.mpr ⟨s, hmem s⟩
  rw [← normalizationIsoPushforwardSpectrum_hom_comp_toBase f]
  have := etale_toBase_pushforwardSpectrum_of_cover f U hcov hetale
  infer_instance

/-- The second factor of the factorization of `f` through the normalization of `S` in `X` is
finite as soon as every point of `S` has an affine open neighbourhood `U` over which the structure
map `Γ(S, U) ⟶ Γ(X, f⁻¹U)` is étale: it is integral for every universally closed quasi-separated
`f`, and an étale morphism is locally of finite type. -/
public theorem isFinite_fromNormalization_of_exists_etale_app
    (h : ∀ s : S, ∃ U : S.affineOpens, s ∈ U.1 ∧
      ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale) :
    IsFinite f.fromNormalization := by
  have := etale_fromNormalization_of_exists_etale_app f h
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f.fromNormalization).mpr
    ⟨isIntegralHom_fromNormalization f, inferInstance⟩

end Cover

/-! ### The proper flat case -/

section ProperFlat

variable [IsProper f] [Flat f] [GeometricallyReduced f]

open StacksDraft.Perfect.GeomReducedFibre in
/-- For a proper, flat morphism of finite presentation with geometrically reduced fibres, every
point of `S` has an affine open neighbourhood `U` over which the structure map
`Γ(S, U) ⟶ Γ(X, f⁻¹U)` of `f_* 𝒪_X` is étale. -/
public theorem exists_affineOpen_etale_app_of_properFlat (hfp : FinitePresentation f) (s : S) :
    ∃ U : S.affineOpens, s ∈ U.1 ∧
      ((pushforwardSituation f).algebra.hom.hom.app (op U.1)).hom.Etale := by
  obtain ⟨W, hsW, -, hfe, -⟩ :=
    exists_open_finiteEtale_and_derivedPushforward_splitting.{u} f hfp s inferInstance
  obtain ⟨V, hVaff, hsV, hVW⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hsW
  refine ⟨⟨V, hVaff⟩, hsV, ?_⟩
  let : Algebra Γ(S, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  exact RingHom.etale_algebraMap.2 (hfe ⟨V, hVaff⟩ hVW).2

/-- **Stacks Project, Tag 0BUN.** Let `f : X ⟶ S` be a proper morphism of schemes which is flat,
of finite presentation and has geometrically reduced fibres, and let `X ⟶ S' ⟶ S` be its Stein
factorization. Then the second factor `S' ⟶ S` is étale. -/
@[stacks 0BUN "étaleness of the second factor", sga "1 X 1.2" "Y′ → Y is étale"]
public theorem etale_fromNormalization_of_properFlat (hfp : FinitePresentation f) :
    Etale f.fromNormalization :=
  etale_fromNormalization_of_exists_etale_app f
    (exists_affineOpen_etale_app_of_properFlat f hfp)

/-- **Stacks Project, Tag 0BUN.** Let `f : X ⟶ S` be a proper morphism of schemes which is flat,
of finite presentation and has geometrically reduced fibres, and let `X ⟶ S' ⟶ S` be its Stein
factorization. Then the second factor `S' ⟶ S` is finite. -/
@[stacks 0BUN "finiteness of the second factor", ega "III 7.8.10" "partial"]
public theorem isFinite_fromNormalization_of_properFlat (hfp : FinitePresentation f) :
    IsFinite f.fromNormalization :=
  isFinite_fromNormalization_of_exists_etale_app f
    (exists_affineOpen_etale_app_of_properFlat f hfp)

/-- **Stacks Project, Tag 0BUN.** The second factor of the Stein factorization of a proper, flat
morphism of finite presentation with geometrically reduced fibres is finite étale. -/
public theorem isFinite_and_etale_fromNormalization_of_properFlat (hfp : FinitePresentation f) :
    IsFinite f.fromNormalization ∧ Etale f.fromNormalization :=
  ⟨isFinite_fromNormalization_of_properFlat f hfp, etale_fromNormalization_of_properFlat f hfp⟩

end ProperFlat

end Stacks.SteinFactorization

end
