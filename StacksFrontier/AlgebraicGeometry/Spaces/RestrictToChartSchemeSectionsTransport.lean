module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProjectiveSectionsTransport

/-!
# Projectivity of the global sections of the sheafified chart restriction

The global sections of the sheafified chart restriction
`AlgebraicGeometry.Space.restrictToChartScheme` of an `𝒪_X`-module at an étale chart are the
sections of the module over that chart, linearly over the functions on the chart's scheme. In
particular, if the former are projective over the functions on an object of the site, so are the
latter.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.sectionsAddEquiv`: the sections of an isomorphism of
  `𝒪_X`-modules over a Zariski open, as an additive equivalence.
* `AlgebraicGeometry.Space.restrictToChartSchemeIsoChartRestrictionSheaf`: the restriction of an
  `𝒪_X`-module to the scheme of an étale chart is isomorphic to the unsheafified chart
  restriction.
* `AlgebraicGeometry.Space.restrictToChartSchemeTopSectionsAddEquiv`: the global sections of
  `AlgebraicGeometry.Space.restrictToChartScheme` at a chart are the sections of the module over
  that chart, additively.

## Main results

* `Module.Projective.of_compHom_addEquiv`: projectivity across an additive equivalence semilinear
  over the larger ring, with the two actions of the smaller ring restricted along a ring map.
* `AlgebraicGeometry.Scheme.Modules.sectionsAddEquiv_smul`: the sections of an isomorphism are
  linear over the functions on the open.
* `AlgebraicGeometry.Space.restrictToChartSchemeTopSectionsAddEquiv_smul`: the equivalence of
  global sections is linear over the functions on the chart's scheme.
* `AlgebraicGeometry.Space.projective_sections_of_projective_restrictToChartScheme`: if the global
  sections of the chart restriction are projective over the functions on an object of the site,
  so are the sections of the module over the chart.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

/-- Let `M` and `P` be `A`-modules with an additive equivalence `M ≃+ P` compatible with the two
`A`-actions, and let `f : R →+* A`. If `M` is projective over `R` with the scalars acting through
`f`, then so is `P`. -/
theorem Module.Projective.of_compHom_addEquiv {A R : Type u} [CommRing A] [CommRing R]
    (f : R →+* A) {M P : Type u} [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    (e : M ≃+ P) (he : ∀ (c : A) (y : M), e (c • y) = c • e y)
    (h : letI : Module R M := Module.compHom M f; Module.Projective R M) :
    letI : Module R P := Module.compHom P f
    Module.Projective R P := by
  let : Module R M := Module.compHom M f
  let : Module R P := Module.compHom P f
  exact Stacks.AdicCompletion.SplitShortExact.projective_of_ringEquiv (RingEquiv.refl R) e
    (fun a x => he (f a) x) h

namespace AlgebraicGeometry

/-- The sections of an isomorphism of `𝒪_X`-modules over a Zariski open, as an additive
equivalence. -/
noncomputable def Scheme.Modules.sectionsAddEquiv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) : (Γ(M, U) : Type u) ≃+ (Γ(N, U) : Type u) :=
  (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op U)).addCommGroupIsoToAddEquiv

/-- The sections of an isomorphism of `𝒪_X`-modules are linear over the functions on the
open. -/
theorem Scheme.Modules.sectionsAddEquiv_smul {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (c : Γ(X, U)) (y : (Γ(M, U) : Type u)) :
    Scheme.Modules.sectionsAddEquiv e U (c • y) = c • Scheme.Modules.sectionsAddEquiv e U y :=
  Scheme.Modules.Hom.app_smul e.hom c y

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The global sections of the sheafified chart restriction -/

/-- The restriction of an `𝒪_X`-module to the scheme of an étale chart, spelled through
`AlgebraicGeometry.Space.restrictToChartSchemeModules`, is isomorphic to the unsheafified chart
restriction `AlgebraicGeometry.Space.chartRestrictionSheaf`. -/
noncomputable def restrictToChartSchemeIsoChartRestrictionSheaf
    (G : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1) :
    restrictToChartSchemeModules B S hS X.1 X.2 G A ≅ chartRestrictionSheaf B S hS X G A :=
  (restrictToChartIsoRestrictToChartScheme B S hS X.2 G A).symm ≪≫
    restrictToChartIsoChartRestrictionSheaf B S hS X G A

/-- The global sections of `AlgebraicGeometry.Space.restrictToChartScheme` at an étale chart are
the sections of the module over that chart, as an additive equivalence. -/
noncomputable def restrictToChartSchemeTopSectionsAddEquiv (G : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    (Γ(restrictToChartSchemeModules B S hS X.1 X.2 G A, ⊤) : Type u) ≃+
      (G.val.obj (op A) : Type u) :=
  (Scheme.Modules.sectionsAddEquiv (restrictToChartSchemeIsoChartRestrictionSheaf B S hS X G A)
      ⊤).trans (chartRestrictionSheafTopEquiv B S hS X G A).symm.toAddEquiv

/-- The equivalence of `AlgebraicGeometry.Space.restrictToChartSchemeTopSectionsAddEquiv` is
linear over the functions on the chart's scheme. -/
theorem restrictToChartSchemeTopSectionsAddEquiv_smul (G : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) (c : Γ(chartScheme A, ⊤))
    (y : (Γ(restrictToChartSchemeModules B S hS X.1 X.2 G A, ⊤) : Type u)) :
    restrictToChartSchemeTopSectionsAddEquiv B S hS X G A (c • y) =
      c • restrictToChartSchemeTopSectionsAddEquiv B S hS X G A y := by
  show (chartRestrictionSheafTopEquiv B S hS X G A).symm
      (Scheme.Modules.sectionsAddEquiv
        (restrictToChartSchemeIsoChartRestrictionSheaf B S hS X G A) ⊤ (c • y)) =
    c • (chartRestrictionSheafTopEquiv B S hS X G A).symm
      (Scheme.Modules.sectionsAddEquiv
        (restrictToChartSchemeIsoChartRestrictionSheaf B S hS X G A) ⊤ y)
  rw [Scheme.Modules.sectionsAddEquiv_smul, LinearEquiv.map_smul]

/-- Let `G` be an `𝒪_X`-module, `A` an étale scheme chart of `X`, `E'` an object of the big fppf
site and `k` a morphism from the object of `A` to `E'`. If the global sections of `G|_A` form a
projective module over the functions on `E'`, then so do the sections `G(A)` of `G` over the
chart, the scalars acting through `k` in both cases. -/
theorem projective_sections_of_projective_restrictToChartScheme
    (G : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1)
    (E' : BigFppfOver B S hS) (k : (SmallEtale.toOver B S hS X.1).obj A ⟶ E')
    (hproj :
      letI M := restrictToChartSchemeModules B S hS X.1 X.2 G A
      letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (Γ(M, ⊤) : Type u) :=
        Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
      Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (Γ(M, ⊤) : Type u)) :
    letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (G.val.obj (op A) : Type u) :=
      Module.compHom _ ((BigFppfOver.toScheme B S hS).map k).appTop.hom
    Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤)
      (G.val.obj (op A) : Type u) :=
  Module.Projective.of_compHom_addEquiv ((BigFppfOver.toScheme B S hS).map k).appTop.hom
    (restrictToChartSchemeTopSectionsAddEquiv B S hS X G A)
    (restrictToChartSchemeTopSectionsAddEquiv_smul B S hS X G A) hproj

end Space

end AlgebraicGeometry

end
