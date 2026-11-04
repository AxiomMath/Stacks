module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Iso

/-!
# Functoriality of the twist comparison

Let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be homomorphisms of nonnegatively graded rings with
`ℬ₊ ≤ 𝒜₊.map φ` and `𝒞₊ ≤ ℬ₊.map ψ`, so that
`AlgebraicGeometry.Proj.map (ψ.comp φ) = Proj.map ψ ≫ Proj.map φ` by
`AlgebraicGeometry.Proj.map_comp`. This file proves that the twist comparison of
`StacksFrontier/AlgebraicGeometry/RelativeProj/Twist/Comparison.lean` is functorial in the
homomorphism: the comparison attached to `ψ.comp φ` is the comparison attached to `φ` followed by
the comparison attached to `ψ`.

The mathematical content is a single line. The comparison is defined pointwise, its fibre at a
homogeneous prime is `Localization.localRingHom`, and `Localization.localRingHom_comp` says that
the localization of a composite is the composite of the localizations. Everything else is
bookkeeping about which open one is working over, and here there is none to do: the preimage of an
open under `Proj.map` of a composite *is* its two-step preimage, definitionally
(`comp_preimage`), because `ProjectiveSpectrum.comapFun` of a composite is the composite of the
`comapFun`s, definitionally (`comapFun_comp`).

That is why the results below are stated at the level of
`Stacks.ProjTwistComparison.sectionsMap` rather than as an equation between morphisms of sheaves
of modules. `Stacks.ProjTwistComparison.twistMap` is an adjoint transpose, so an equation between
`twistMap (ψ.comp φ)` and the composite of the two `twistMap`s cannot even be *stated* without
transporting along `AlgebraicGeometry.Proj.map_comp` — the two sides live over
`Scheme.Modules.pullback (Proj.map (ψ.comp φ))` and
`Scheme.Modules.pullback (Proj.map ψ) ⋙ Scheme.Modules.pullback (Proj.map φ)`, which are not
definitionally equal functors — and then proving it means computing with that transport. The
sections form needs none of that, and it is what the consumers need: `IsIso (twistMap φ)` is
decided by bijectivity on sections
(`Stacks.ProjTwistComparison.isIso_twistMap_of_bijective`), and bijectivity composes.

## Main results

* `Stacks.ProjTwistComparison.comapFun_comp` and `Stacks.ProjTwistComparison.comp_preimage`: the
  point below a point, and the preimage of an open, are reached in either order — both by `rfl`.
* `Stacks.ProjTwistComparison.fibreMap_comp`: **the fibre comparison is functorial.** This is
  `Localization.localRingHom_comp`.
* `Stacks.ProjTwistComparison.sectionsMap_comp` and
  `Stacks.ProjTwistComparison.sectionsMap_comp'`: **the comparison on sections is functorial**,
  as a pointwise identity and as an equality of functions.
* `Stacks.ProjTwistComparison.bijective_sectionsMap_comp`: bijectivity on sections is inherited
  by a composite.
* `Stacks.ProjTwistComparison.isIso_twistMap_comp`: **the twist comparison of a composite is an
  isomorphism** as soon as each factor is bijective on the sections that matter.
* `Stacks.ProjTwistComparison.comapFun_eq_comp` and
  `Stacks.ProjTwistComparison.sectionsMap_apply_eq_comp`: the two results above for a
  homomorphism *presented* as a composite by an equation, which is how a restriction map of
  graded section rings factors.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B C : Type u} {σ τ ρ : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
  (hψφ : 𝒞₊ ≤ 𝒜₊.map (ψ.comp φ))

/-- The point of `Proj 𝒜` below a point of `Proj 𝒞` is reached in either order. -/
theorem comapFun_comp (y : ProjectiveSpectrum 𝒞) :
    ProjectiveSpectrum.comapFun (ψ.comp φ) hψφ y
      = ProjectiveSpectrum.comapFun φ hφ (ProjectiveSpectrum.comapFun ψ hψ y) := rfl

/-- The preimage of an open of `Proj 𝒜` under `Proj.map` of a composite is its preimage in two
steps. -/
theorem comp_preimage (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    AlgebraicGeometry.Proj.map (ψ.comp φ) hψφ ⁻¹ᵁ U
      = AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ (AlgebraicGeometry.Proj.map φ hφ ⁻¹ᵁ U) := rfl

/-- **The fibre comparison is functorial.** At a point of `Proj 𝒞` the localization of a composite
of homomorphisms of graded rings is the composite of the localizations; this is
`Localization.localRingHom_comp`, and it is the whole mathematical content of the functoriality of
the twist comparison. -/
theorem fibreMap_comp (y : ProjectiveSpectrum 𝒞)
    (z : ModuleFiber (M := A) 𝒜 (ProjectiveSpectrum.comapFun (ψ.comp φ) hψφ y)) :
    fibreMap (ψ.comp φ) hψφ y z
      = fibreMap ψ hψ y (fibreMap φ hφ (ProjectiveSpectrum.comapFun ψ hψ y) z) :=
  DFunLike.congr_fun (Localization.localRingHom_comp
    (ProjectiveSpectrum.comapFun (ψ.comp φ) hψφ y).asHomogeneousIdeal.toIdeal
    (ProjectiveSpectrum.comapFun ψ hψ y).asHomogeneousIdeal.toIdeal
    y.asHomogeneousIdeal.toIdeal φ.toRingHom rfl ψ.toRingHom rfl) z

variable (n : ℤ)

/-- **The comparison on sections is functorial.** The comparison attached to a composite of
homomorphisms of graded rings is, on sections over an open `U` of `Proj 𝒜`, the composite of the
two comparisons; no identification of opens is needed, because the preimage of `U` under
`Proj.map` of the composite *is* its two-step preimage (`comp_preimage`). -/
theorem sectionsMap_comp (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : moduleSections 𝒜 (twistGrading (S := A) 𝒜 n) U) :
    sectionsMap (ψ.comp φ) hψφ n U a
      = sectionsMap ψ hψ n (U.comap (ProjectiveSpectrum.comap φ hφ))
          (sectionsMap φ hφ n U a) :=
  Subtype.ext (funext fun y => fibreMap_comp φ hφ ψ hψ hψφ y.1 _)

/-- `sectionsMap` of a composite, as an equality of functions. -/
theorem sectionsMap_comp' (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    sectionsMap (ψ.comp φ) hψφ n U
      = sectionsMap ψ hψ n (U.comap (ProjectiveSpectrum.comap φ hφ)) ∘
          sectionsMap φ hφ n U :=
  funext (sectionsMap_comp φ hφ ψ hψ hψφ n U)

/-- **Bijectivity of the comparison on sections is inherited by a composite.** -/
theorem bijective_sectionsMap_comp (U : Opens (ProjectiveSpectrum.top 𝒜))
    (h₁ : Function.Bijective (sectionsMap φ hφ n U))
    (h₂ : Function.Bijective
      (sectionsMap ψ hψ n (U.comap (ProjectiveSpectrum.comap φ hφ)))) :
    Function.Bijective (sectionsMap (ψ.comp φ) hψφ n U) :=
  (sectionsMap_comp' φ hφ ψ hψ hψφ n U) ▸ h₂.comp h₁

/-- **The twist comparison of a composite is an isomorphism** as soon as each factor is bijective
on the sections over the opens that matter: those in the image of `Proj.map` of the composite, and
their preimages in `Proj ℬ`.

This is the form in which functoriality is consumed. `Stacks.ProjTwistComparison.twistMap` is
defined as an adjoint transpose, so an equation between the comparison of a composite and the
composite of the comparisons has to be stated modulo
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` and a transport along
`AlgebraicGeometry.Proj.map_comp`; but `Stacks.ProjTwistComparison.isIso_twistMap_of_bijective`
reduces `IsIso` to bijectivity on sections, where `sectionsMap_comp` applies with no transport at
all. -/
theorem isIso_twistMap_comp
    [IsOpenImmersion (AlgebraicGeometry.Proj.map (ψ.comp φ) hψφ)]
    (h₁ : ∀ V : (AlgebraicGeometry.Proj 𝒞).Opens, Function.Bijective (sectionsMap φ hφ n
      ((AlgebraicGeometry.Proj.map (ψ.comp φ) hψφ).opensFunctor.obj V)))
    (h₂ : ∀ V : (AlgebraicGeometry.Proj 𝒞).Opens, Function.Bijective (sectionsMap ψ hψ n
      (((AlgebraicGeometry.Proj.map (ψ.comp φ) hψφ).opensFunctor.obj V).comap
        (ProjectiveSpectrum.comap φ hφ)))) :
    IsIso (twistMap (ψ.comp φ) hψφ n) :=
  isIso_twistMap_of_bijective (ψ.comp φ) hψφ n fun V =>
    bijective_sectionsMap_comp φ hφ ψ hψ hψφ n _ (h₁ V) (h₂ V)

/-! ### Functoriality along a factorization presented by an equation -/

section EqComp

variable {χ : 𝒜 →+*ᵍ 𝒞}

/-- The point of `Proj 𝒜` below a point of `Proj 𝒞` is reached in two steps, for a homomorphism
`χ` *presented* as a composite by an equation rather than written as one. -/
theorem comapFun_eq_comp (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (hcomp : χ = ψ.comp φ)
    (y : ProjectiveSpectrum 𝒞) :
    ProjectiveSpectrum.comapFun χ hχ y
      = ProjectiveSpectrum.comapFun φ hφ (ProjectiveSpectrum.comapFun ψ hψ y) := by
  subst hcomp
  rfl

/-- A point of `Proj 𝒞` lying over an open `U` of `Proj 𝒜` for a homomorphism `χ` presented as a
composite lies over `U` in two steps. -/
theorem mem_comap_comap_of_eq_comp (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (hcomp : χ = ψ.comp φ)
    {U : Opens (ProjectiveSpectrum.top 𝒜)} {y : ProjectiveSpectrum 𝒞}
    (hy : y ∈ U.comap (ProjectiveSpectrum.comap χ hχ)) :
    y ∈ (U.comap (ProjectiveSpectrum.comap φ hφ)).comap (ProjectiveSpectrum.comap ψ hψ) := by
  subst hcomp
  exact hy

/-- **The comparison on sections is functorial**, for a homomorphism `χ` presented as a composite
by an equation.

Stated at a point rather than as an equality of maps of section modules: the comparison attached
to `χ` lands in the sections over `U.comap (comap χ hχ)` and the composite of the two comparisons
in the sections over the two-step preimage, and those two opens are equal only up to the
equation, so the two maps of section modules do not have the same type. -/
theorem sectionsMap_apply_eq_comp (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (hcomp : χ = ψ.comp φ)
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : moduleSections 𝒜 (twistGrading (S := A) 𝒜 n) U)
    (y : U.comap (ProjectiveSpectrum.comap χ hχ)) :
    (sectionsMap χ hχ n U a).1 y
      = (sectionsMap ψ hψ n (U.comap (ProjectiveSpectrum.comap φ hφ))
          (sectionsMap φ hφ n U a)).1
          ⟨y.1, mem_comap_comap_of_eq_comp φ hφ ψ hψ hχ hcomp y.2⟩ := by
  subst hcomp
  exact fibreMap_comp φ hφ ψ hψ hχ y.1 _

end EqComp

end Stacks.ProjTwistComparison

end
