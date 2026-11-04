module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartNatural
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalCocycle

/-!
# The scheme factor of the chart maps `χ_w` of `θ` of Stacks 0D2Z along morphisms of points

The chart map `χ_w : w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` at a scheme point `w` of `U(ψ)`
(`…InvertibleTwistingRestriction.chartMap`) is a composite of three factors; its middle factor
is the module attached (Stacks 03DX (2)) to the map `θ` of [Stacks, Tag 01O9] on `W` read along
the section `c_w` (`…InvertibleTwistingRestriction.chartSchemeTheta`).  This file provides the
steps of the square of that factor along a morphism `τ : T' ⟶ T` of test schemes:

* the passage from a square of maps of quasi-coherent modules on the schemes to the square of
  the attached modules, in the shape of the middle hypothesis of
  `AlgebraicGeometry.Space.pullbackTransportSquare_of_squares`;
* the abstract coherence reducing the square of the maps `θ` read along sections to the
  comparison `θ_{x ∘ τ} = j^*(l^*θ_x)` of
  `…InvertibleTwistingRestriction.theta_map_eq_pullback` and to the compatibility of the
  identifications of the sources and of the targets;
* the factorisation of `τ` through the loci used by that comparison;
* the same reduction for maps of quasi-coherent modules on the schemes of the site, with the maps
  `θ` given in the shape of their definitions, and the degreewise form of the comparison of `θ`;
* the coherence of the canonical identifications behind the compatibility of the sources, at
  variables: the two composites of contractions `τ^*c_x^*t_x^*M ⟶ g'^*j^*l^*r_x^*M` around the
  square, one through the section `c_{x'}` and the morphism `y` of base changes, agree; the
  identification of the inverse images of the twists along the square of loci composed with the
  twist comparison is canonical; together, the source compatibility in the shape of the
  reduction;
* the underlying morphisms of the source comparison `σ` and of the comparison of twists along a
  square, written out.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_functor_map_comp_eq_of_square`
* `AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq`,
  `AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq_of_factors`
* `…InvertibleTwistingRestriction.map_comp_chartLift`
* `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison_comp_of_comp_eq`
* `AlgebraicGeometry.Space.quasicoherentPullbackMap_comp_eq_of_theta_eq_of_factors`,
  `AlgebraicGeometry.Space.app_eq_comp_pullback_map_app`
* `AlgebraicGeometry.Space.canHom_source_square_coherence`,
  `AlgebraicGeometry.Space.canHom_squareChain_coherence`,
  `AlgebraicGeometry.Space.source_square_coherence_of_squareChain`
* `AlgebraicGeometry.Space.quasicoherentPullbackCompIso_hom_comp_eqToHom_comp_inv_comp_map_hom`,
  `AlgebraicGeometry.Space.pullbackSheafIsoOfSquare_gradedPieceIso_hom`

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

section Attached

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The square of the module attached to a morphism of quasi-coherent modules, from a square
on the scheme.**  For `g : V ⟶ U` of the site, morphisms `θ : M ⟶ N` on `U` and `θ' : M' ⟶ N'`
on `V`, and `σ : g^*M ⟶ M'`, `ρ : g^*N ⟶ N'` with `g^*θ ≫ ρ = σ ≫ θ'`, the inverse image along
`g` of the module map attached to `θ` (Stacks 03DX (2)), followed by `g^*(N^a) ≅ (g^*N)^a` and the
module map attached to `ρ`, is `g^*(M^a) ≅ (g^*M)^a` followed by the module maps attached to `σ`
and to `θ'`. -/
theorem modulePullback_map_functor_map_comp_eq_of_square {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {M' N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (θ : M ⟶ N) (θ' : M' ⟶ N') (σ : quasicoherentPullbackObj B S hS g M ⟶ M')
    (ρ : quasicoherentPullbackObj B S hS g N ⟶ N')
    (h : quasicoherentPullbackMap B S hS g θ ≫ ρ = σ ≫ θ') :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map θ).hom ≫
      ((modulePullbackRepresentedQuasicoherentIso B S hS g N).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ρ).hom) =
    ((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map σ).hom) ≫
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map θ').hom := by
  have hn := modulePullbackRepresentedQuasicoherentIso_naturality B S hS g θ
  have hE : ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackMap B S hS g θ)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map ρ).hom =
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map σ).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map θ').hom :=
    congrArg InducedCategory.Hom.hom
      (((representedQuasicoherentSchemeEquivalence B S hS V).functor.map_comp _ _).symm.trans
        ((congrArg (representedQuasicoherentSchemeEquivalence B S hS V).functor.map h).trans
          ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map_comp _ _)))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hE).trans (Category.assoc _ _ _).symm)))

end Attached

section SchemeCoherence

variable {T T' Ux Ux' Usq : Scheme.{u}} (τ : T' ⟶ T) (g : T ⟶ Ux) (g' : T' ⟶ Ux')
  (j : Ux' ⟶ Usq) (l : Usq ⟶ Ux) (hk : τ ≫ g = g' ≫ j ≫ l)

/-- The comparison `τ^*(g^*M) ≅ (τ ≫ g)^*M = (g' ≫ j ≫ l)^*M ≅ g'^*(j^*(l^*M))` of the
pseudofunctoriality of the inverse image of modules on schemes is natural in `M`. -/
theorem pullback_comp_naturality_of_eq {M N : Ux.Modules} (θ : M ⟶ N) :
    (Scheme.Modules.pullback τ).map ((Scheme.Modules.pullback g).map θ) ≫
        ((Scheme.Modules.pullbackComp τ g).hom.app N ≫
          (Scheme.Modules.pullbackCongr hk).hom.app N ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app N ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app N)) =
      ((Scheme.Modules.pullbackComp τ g).hom.app M ≫
          (Scheme.Modules.pullbackCongr hk).hom.app M ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app M ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app M)) ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map
          ((Scheme.Modules.pullback l).map θ)) := by
  have h1 := (Scheme.Modules.pullbackComp τ g).hom.naturality θ
  have h2 := (Scheme.Modules.pullbackCongr hk).hom.naturality θ
  have h3 := (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.naturality θ
  have h4 := (Scheme.Modules.pullbackComp j l).inv.naturality θ
  simp only [Functor.comp_map] at h1 h2 h3 h4
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, ← Functor.map_comp, h4, Functor.map_comp]

/-- **A square of maps read along sections, from the comparison of `θ` along a chain of
inverse images.**  Let `τ ≫ g = g' ≫ j ≫ l`, `θ : M ⟶ N` on `U_x`, and `θ' : M₃ ⟶ N₃` on `U_{x'}`
equal to `θ` pulled back along `l` and then `j`, through given maps `B⁻¹`, `C`, `A⁻¹`, `D`
(`hθ`).  For maps `Θ₀ = ε ≫ g^*θ ≫ λ₀` on `T` and `Θ₁ = ε' ≫ g'^*θ' ≫ λ₁` on `T'` and morphisms
`σ`, `ρ` compatible with the identifications of the sources (`hSrc`) and of the targets (`hTgt`)
through `τ^*g^* ≅ g'^*j^*l^*`, the square `τ^*Θ₀ ≫ ρ = σ ≫ Θ₁` commutes.  All factors are
variables with their values as equations. -/
theorem pullback_map_comp_eq_of_theta_eq {M N : Ux.Modules} (θ : M ⟶ N)
    {M₂ N₂ : Usq.Modules} (Bi : M₂ ⟶ (Scheme.Modules.pullback l).obj M)
    (Ch : (Scheme.Modules.pullback l).obj N ⟶ N₂) {M₃ N₃ : Ux'.Modules}
    (Ai : M₃ ⟶ (Scheme.Modules.pullback j).obj M₂) (Dh : (Scheme.Modules.pullback j).obj N₂ ⟶ N₃)
    (θ' : M₃ ⟶ N₃)
    (hθ : θ' = Ai ≫ (Scheme.Modules.pullback j).map (Bi ≫ (Scheme.Modules.pullback l).map θ ≫ Ch) ≫
      Dh)
    {P₀ Q₀ : T.Modules} (ε : P₀ ⟶ (Scheme.Modules.pullback g).obj M)
    (lam₀ : (Scheme.Modules.pullback g).obj N ⟶ Q₀) (Θ₀ : P₀ ⟶ Q₀)
    (hΘ₀ : Θ₀ = ε ≫ (Scheme.Modules.pullback g).map θ ≫ lam₀)
    {P₁ Q₁ : T'.Modules} (ε' : P₁ ⟶ (Scheme.Modules.pullback g').obj M₃)
    (lam₁ : (Scheme.Modules.pullback g').obj N₃ ⟶ Q₁) (Θ₁ : P₁ ⟶ Q₁)
    (hΘ₁ : Θ₁ = ε' ≫ (Scheme.Modules.pullback g').map θ' ≫ lam₁)
    (σ : (Scheme.Modules.pullback τ).obj P₀ ⟶ P₁) (ρ : (Scheme.Modules.pullback τ).obj Q₀ ⟶ Q₁)
    (hSrc : (Scheme.Modules.pullback τ).map ε ≫
        ((Scheme.Modules.pullbackComp τ g).hom.app M ≫
          (Scheme.Modules.pullbackCongr hk).hom.app M ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app M ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app M)) =
      σ ≫ ε' ≫ (Scheme.Modules.pullback g').map Ai ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map Bi))
    (hTgt : ((Scheme.Modules.pullbackComp τ g).hom.app N ≫
          (Scheme.Modules.pullbackCongr hk).hom.app N ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app N ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app N)) ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map Ch) ≫
        (Scheme.Modules.pullback g').map Dh ≫ lam₁ =
      (Scheme.Modules.pullback τ).map lam₀ ≫ ρ) :
    (Scheme.Modules.pullback τ).map Θ₀ ≫ ρ = σ ≫ Θ₁ := by
  subst hθ hΘ₀ hΘ₁
  have hn := pullback_comp_naturality_of_eq τ g g' j l hk θ
  simp only [Functor.map_comp, Category.assoc] at hSrc hTgt hn ⊢
  rw [← hTgt, reassoc_of% hn, reassoc_of% hSrc]

/-- `AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq` with the identifications of the
sources `ε = e₁ ≫ e₂ ≫ e₃` given by three factors, the shape in which the maps
`…InvertibleTwistingRestriction.chartSchemeTheta` unfold. -/
theorem pullback_map_comp_eq_of_theta_eq_of_factors {M N : Ux.Modules} (θ : M ⟶ N)
    {M₂ N₂ : Usq.Modules} (Bi : M₂ ⟶ (Scheme.Modules.pullback l).obj M)
    (Ch : (Scheme.Modules.pullback l).obj N ⟶ N₂) {M₃ N₃ : Ux'.Modules}
    (Ai : M₃ ⟶ (Scheme.Modules.pullback j).obj M₂) (Dh : (Scheme.Modules.pullback j).obj N₂ ⟶ N₃)
    (θ' : M₃ ⟶ N₃)
    (hθ : θ' = Ai ≫ (Scheme.Modules.pullback j).map (Bi ≫ (Scheme.Modules.pullback l).map θ ≫ Ch) ≫
      Dh)
    {P₀ P₀' P₀'' Q₀ : T.Modules} (e₁ : P₀ ⟶ P₀') (e₂ : P₀' ⟶ P₀'')
    (e₃ : P₀'' ⟶ (Scheme.Modules.pullback g).obj M)
    (lam₀ : (Scheme.Modules.pullback g).obj N ⟶ Q₀) (Θ₀ : P₀ ⟶ Q₀)
    (hΘ₀ : Θ₀ = e₁ ≫ e₂ ≫ e₃ ≫ (Scheme.Modules.pullback g).map θ ≫ lam₀)
    {P₁ P₁' P₁'' Q₁ : T'.Modules} (e₁' : P₁ ⟶ P₁') (e₂' : P₁' ⟶ P₁'')
    (e₃' : P₁'' ⟶ (Scheme.Modules.pullback g').obj M₃)
    (lam₁ : (Scheme.Modules.pullback g').obj N₃ ⟶ Q₁) (Θ₁ : P₁ ⟶ Q₁)
    (hΘ₁ : Θ₁ = e₁' ≫ e₂' ≫ e₃' ≫ (Scheme.Modules.pullback g').map θ' ≫ lam₁)
    (σ : (Scheme.Modules.pullback τ).obj P₀ ⟶ P₁) (ρ : (Scheme.Modules.pullback τ).obj Q₀ ⟶ Q₁)
    (hSrc : (Scheme.Modules.pullback τ).map (e₁ ≫ e₂ ≫ e₃) ≫
        ((Scheme.Modules.pullbackComp τ g).hom.app M ≫
          (Scheme.Modules.pullbackCongr hk).hom.app M ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app M ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app M)) =
      σ ≫ (e₁' ≫ e₂' ≫ e₃') ≫ (Scheme.Modules.pullback g').map Ai ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map Bi))
    (hTgt : ((Scheme.Modules.pullbackComp τ g).hom.app N ≫
          (Scheme.Modules.pullbackCongr hk).hom.app N ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app N ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app N)) ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map Ch) ≫
        (Scheme.Modules.pullback g').map Dh ≫ lam₁ =
      (Scheme.Modules.pullback τ).map lam₀ ≫ ρ) :
    (Scheme.Modules.pullback τ).map Θ₀ ≫ ρ = σ ≫ Θ₁ :=
  pullback_map_comp_eq_of_theta_eq τ g g' j l hk θ Bi Ch Ai Dh θ' hθ (e₁ ≫ e₂ ≫ e₃) lam₀ Θ₀
    (hΘ₀.trans (by simp only [Category.assoc])) (e₁' ≫ e₂' ≫ e₃') lam₁ Θ₁
    (hΘ₁.trans (by simp only [Category.assoc])) σ ρ hSrc hTgt

end SchemeCoherence

section FactorsOnSite

open Stacks.RingedSpace in
/-- **A comparison of maps of graded algebras along two inverse images, degreewise.**  If
`θ' = A⁻¹ ≫ j^*(B⁻¹ ≫ l^*θ ≫ C) ≫ D` as maps of sheaves of graded algebras, then in every degree
`d` the same holds for the pieces, with the inverse images read as `Scheme.Modules.pullback`; the
shape of the comparison hypothesis of
`AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq`. -/
theorem app_eq_comp_pullback_map_app {Ux Usq Ux' : Scheme.{u}} (j : Ux' ⟶ Usq) (l : Usq ⟶ Ux)
    {A B : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Ux.toRingedSpace)}
    {A₂ B₂ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Usq.toRingedSpace)}
    {A₃ B₃ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Ux'.toRingedSpace)}
    (θ : A ⟶ B) (θ' : A₃ ⟶ B₃) (Ai : pullbackGradedAlgebra j.toLRSHom.toShHom A₂ ≅ A₃)
    (Bi : pullbackGradedAlgebra l.toLRSHom.toShHom A ≅ A₂)
    (Ch : pullbackGradedAlgebra l.toLRSHom.toShHom B ≅ B₂)
    (Dh : pullbackGradedAlgebra j.toLRSHom.toShHom B₂ ≅ B₃)
    (h : θ' = Ai.inv ≫ pullbackGradedAlgebraMap j.toLRSHom.toShHom
      (Bi.inv ≫ pullbackGradedAlgebraMap l.toLRSHom.toShHom θ ≫ Ch.hom) ≫ Dh.hom) (d : ℤ) :
    θ'.app d = Ai.inv.app d ≫ (Scheme.Modules.pullback j).map (Bi.inv.app d ≫
      (Scheme.Modules.pullback l).map (θ.app d) ≫ Ch.hom.app d) ≫ Dh.hom.app d := by
  subst h
  rfl

/-- `AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq_of_factors` for maps of
quasi-coherent modules on the schemes of the site: for `τ : V ⟶ U` and maps `Θ₀ = (e₁ ≫ e₂ ≫ T₀)`,
`T₀ = e₃ ≫ g^*θ ≫ λ₀` on `U` and `Θ₁ = (e₁' ≫ e₂' ≫ T₁)`, `T₁ = e₃' ≫ g'^*θ' ≫ λ₁` on `V`
(the shape in which `…InvertibleTwistingRestriction.chartSchemeTheta` is defined), the square
`τ^*Θ₀ ≫ ρ = σ ≫ Θ₁` of quasi-coherent modules follows from the comparison of `θ` and the
compatibilities of the sources and of the targets. -/
theorem quasicoherentPullbackMap_comp_eq_of_theta_eq_of_factors {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S}
    {V U : BigFppfOver B S hS} (τq : V ⟶ U) {Ux Ux' Usq : Scheme.{u}}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ Ux) (g' : (BigFppfOver.toScheme B S hS).obj V ⟶ Ux')
    (j : Ux' ⟶ Usq) (l : Usq ⟶ Ux)
    (hk : (BigFppfOver.toScheme B S hS).map τq ≫ g = g' ≫ j ≫ l) {M N : Ux.Modules} (θ : M ⟶ N)
    {M₂ N₂ : Usq.Modules} (Bi : M₂ ⟶ (Scheme.Modules.pullback l).obj M)
    (Ch : (Scheme.Modules.pullback l).obj N ⟶ N₂) {M₃ N₃ : Ux'.Modules}
    (Ai : M₃ ⟶ (Scheme.Modules.pullback j).obj M₂) (Dh : (Scheme.Modules.pullback j).obj N₂ ⟶ N₃)
    (θ' : M₃ ⟶ N₃)
    (hθ : θ' = Ai ≫ (Scheme.Modules.pullback j).map (Bi ≫ (Scheme.Modules.pullback l).map θ ≫ Ch) ≫
      Dh)
    {P₀ Q₀ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {P₀' P₀'' : ((BigFppfOver.toScheme B S hS).obj U).Modules} (e₁ : P₀.obj ⟶ P₀') (e₂ : P₀' ⟶ P₀'')
    (e₃ : P₀'' ⟶ (Scheme.Modules.pullback g).obj M)
    (lam₀ : (Scheme.Modules.pullback g).obj N ⟶ Q₀.obj) (T₀ : P₀'' ⟶ Q₀.obj)
    (hT₀ : T₀ = e₃ ≫ (Scheme.Modules.pullback g).map θ ≫ lam₀) (Θ₀ : P₀ ⟶ Q₀)
    (hΘ₀ : Θ₀ = ObjectProperty.homMk (e₁ ≫ e₂ ≫ T₀))
    {P₁ Q₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    {P₁' P₁'' : ((BigFppfOver.toScheme B S hS).obj V).Modules} (e₁' : P₁.obj ⟶ P₁')
    (e₂' : P₁' ⟶ P₁'')
    (e₃' : P₁'' ⟶ (Scheme.Modules.pullback g').obj M₃)
    (lam₁ : (Scheme.Modules.pullback g').obj N₃ ⟶ Q₁.obj) (T₁ : P₁'' ⟶ Q₁.obj)
    (hT₁ : T₁ = e₃' ≫ (Scheme.Modules.pullback g').map θ' ≫ lam₁) (Θ₁ : P₁ ⟶ Q₁)
    (hΘ₁ : Θ₁ = ObjectProperty.homMk (e₁' ≫ e₂' ≫ T₁))
    (σ : quasicoherentPullbackObj B S hS τq P₀ ⟶ P₁)
    (ρ : quasicoherentPullbackObj B S hS τq Q₀ ⟶ Q₁)
    (hSrc : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τq)).map (e₁ ≫ e₂ ≫ e₃) ≫
        ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τq) g).hom.app M ≫
          (Scheme.Modules.pullbackCongr hk).hom.app M ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app M ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app M)) =
      σ.hom ≫ (e₁' ≫ e₂' ≫ e₃') ≫ (Scheme.Modules.pullback g').map Ai ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map Bi))
    (hTgt : ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τq) g).hom.app N ≫
          (Scheme.Modules.pullbackCongr hk).hom.app N ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app N ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app N)) ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map Ch) ≫
        (Scheme.Modules.pullback g').map Dh ≫ lam₁ =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τq)).map lam₀ ≫ ρ.hom) :
    quasicoherentPullbackMap B S hS τq Θ₀ ≫ ρ = σ ≫ Θ₁ := by
  subst hΘ₀ hΘ₁ hT₀ hT₁
  refine ObjectProperty.hom_ext _ ?_
  exact pullback_map_comp_eq_of_theta_eq_of_factors _ g g' j l hk θ Bi Ch Ai Dh θ' hθ e₁ e₂ e₃ lam₀
    _ rfl e₁' e₂' e₃' lam₁ _ rfl σ.hom ρ.hom hSrc hTgt

end FactorsOnSite

section PureCoherence

open Stacks.AlgebraicGeometry.ModuleLimits (canHom canHom_comp canHom_comp_assoc canHom_rfl)

variable {T T' Fx Fx' Px Px' Ux Ux' Usq : Scheme.{u}}

/-- The inverse of the contraction `a^*(b^*F) ≅ (a ≫ b)^*F` is the inverse of the canonical
identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` at the composite written out. -/
theorem pullbackComp_inv_app_eq_inv_canHom {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Z.Modules) :
    (Scheme.Modules.pullbackComp a b).inv.app F = inv (canHom a b (a ≫ b) rfl F) := by
  refine IsIso.eq_inv_of_hom_inv_id ?_
  rw [canHom_rfl]
  exact Iso.hom_inv_id_app _ _

/-- The cocycle `canHom_comp`, with the contraction `r^*(q^*(g^*F)) ≅ s^*(g^*F)` moved to the
other side. -/
private theorem inv_canHom_comp_map_canHom_comp_canHom {V W Z X : Scheme.{u}} (r : V ⟶ W)
    (q : W ⟶ Z) (g : Z ⟶ X) (s : V ⟶ Z) (pi : W ⟶ X) (t : V ⟶ X) (hs : r ≫ q = s)
    (hpi : q ≫ g = pi) (ht : s ≫ g = t) (hrt : r ≫ pi = t) (F : X.Modules) :
    inv (canHom r q s hs ((Scheme.Modules.pullback g).obj F)) ≫
        (Scheme.Modules.pullback r).map (canHom q g pi hpi F) ≫ canHom r pi t hrt F =
      canHom s g t ht F := by
  rw [IsIso.inv_comp_eq]
  exact canHom_comp r q g s pi t hs hpi ht hrt F

/-- **The coherence of the source identifications around the square of the chart maps**, at
variables.  For `c_x ≫ t_x = g ≫ r_x`, `c_{x'} ≫ t_{x'} = g' ≫ j ≫ r'`, `τ ≫ g = g' ≫ j ≫ l`,
`τ ≫ c_x = c_{x'} ≫ y`, `y ≫ t_x = t_{x'} ≫ y_P` and `r' ≫ y_P = l ≫ r_x`, the two composites of
the canonical identifications (Stacks 01ZR (2), the cocycle of 03LU)
`τ^*(c_x^*(t_x^*M)) ⟶ g'^*(j^*(l^*(r_x^*M)))` agree: the one through `τ^*(g^*(r_x^*M))` and the
one through `c_{x'}^*(y^*(t_x^*M))`, `c_{x'}^*(t_{x'}^*(y_P^*M))` and `g'^*(j^*(r'^*(y_P^*M)))`.
Both are compared with the contraction to `(g' ≫ j ≫ l ≫ r_x)^*M` through
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`. -/
theorem canHom_source_square_coherence (τ : T' ⟶ T) (cx : T ⟶ Fx) (tx : Fx ⟶ Px) (gx : T ⟶ Ux)
    (rx : Ux ⟶ Px)
    (cx' : T' ⟶ Fx') (tx' : Fx' ⟶ Px') (gx' : T' ⟶ Ux') (j : Ux' ⟶ Usq) (l : Usq ⟶ Ux)
    (rsq : Usq ⟶ Px') (y : Fx' ⟶ Fx) (ym : Px' ⟶ Px)
    (h1 : cx ≫ tx = gx ≫ rx) (h2 : cx' ≫ tx' = gx' ≫ j ≫ rsq) (hk : τ ≫ gx = gx' ≫ j ≫ l)
    (h4 : τ ≫ cx = cx' ≫ y) (h5 : y ≫ tx = tx' ≫ ym) (H₁ : rsq ≫ ym = l ≫ rx) (X : Px.Modules) :
    (Scheme.Modules.pullback τ).map (canHom cx tx (gx ≫ rx) h1 X) ≫
        (Scheme.Modules.pullback τ).map (inv (canHom gx rx (gx ≫ rx) rfl X)) ≫
        canHom τ gx (gx' ≫ j ≫ l) hk ((Scheme.Modules.pullback rx).obj X) ≫
        inv (canHom gx' (j ≫ l) (gx' ≫ j ≫ l) rfl ((Scheme.Modules.pullback rx).obj X)) ≫
        (Scheme.Modules.pullback gx').map (inv (canHom j l (j ≫ l) rfl
          ((Scheme.Modules.pullback rx).obj X))) =
      canHom τ cx (cx' ≫ y) h4 ((Scheme.Modules.pullback tx).obj X) ≫
        inv (canHom cx' y (cx' ≫ y) rfl ((Scheme.Modules.pullback tx).obj X)) ≫
        (Scheme.Modules.pullback cx').map (canHom y tx (tx' ≫ ym) h5 X) ≫
        (Scheme.Modules.pullback cx').map (inv (canHom tx' ym (tx' ≫ ym) rfl X)) ≫
        canHom cx' tx' (gx' ≫ j ≫ rsq) h2 ((Scheme.Modules.pullback ym).obj X) ≫
        inv (canHom gx' (j ≫ rsq) (gx' ≫ j ≫ rsq) rfl ((Scheme.Modules.pullback ym).obj X)) ≫
        (Scheme.Modules.pullback gx').map (inv (canHom j rsq (j ≫ rsq) rfl
          ((Scheme.Modules.pullback ym).obj X))) ≫
        (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map
          (canHom rsq ym (l ≫ rx) H₁ X ≫ inv (canHom l rx (l ≫ rx) rfl X))) := by
  have hτ : τ ≫ gx ≫ rx = gx' ≫ j ≫ l ≫ rx := by rw [← Category.assoc, hk]; simp
  have hc : cx' ≫ tx' ≫ ym = gx' ≫ j ≫ l ≫ rx := by rw [← Category.assoc, h2]; simp [H₁]
  have hy : (cx' ≫ y) ≫ tx = gx' ≫ j ≫ l ≫ rx := by
    rw [Category.assoc, h5, ← Category.assoc, h2]; simp [H₁]
  -- the total contraction of the target
  let K := (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map
      (canHom l rx (l ≫ rx) rfl X)) ≫
    (Scheme.Modules.pullback gx').map (canHom j (l ≫ rx) (j ≫ l ≫ rx) rfl X) ≫
    canHom gx' (j ≫ l ≫ rx) (gx' ≫ j ≫ l ≫ rx) rfl X
  have hK : IsIso K := by dsimp only [K]; infer_instance
  refine (cancel_mono K).1 ?_
  dsimp only [K]
  -- the left side
  have eL1 : (Scheme.Modules.pullback gx').map (inv (canHom j l (j ≫ l) rfl
        ((Scheme.Modules.pullback rx).obj X))) ≫
      (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map
        (canHom l rx (l ≫ rx) rfl X)) ≫
      (Scheme.Modules.pullback gx').map (canHom j (l ≫ rx) (j ≫ l ≫ rx) rfl X) =
      (Scheme.Modules.pullback gx').map (canHom (j ≫ l) rx (j ≫ l ≫ rx) (by simp) X) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      inv_canHom_comp_map_canHom_comp_canHom j l rx (j ≫ l) (l ≫ rx) (j ≫ l ≫ rx) rfl rfl
        (by simp) rfl X]
  have eL2 : inv (canHom gx' (j ≫ l) (gx' ≫ j ≫ l) rfl ((Scheme.Modules.pullback rx).obj X)) ≫
      (Scheme.Modules.pullback gx').map (canHom (j ≫ l) rx (j ≫ l ≫ rx) (by simp) X) ≫
      canHom gx' (j ≫ l ≫ rx) (gx' ≫ j ≫ l ≫ rx) rfl X =
      canHom (gx' ≫ j ≫ l) rx (gx' ≫ j ≫ l ≫ rx) (by simp) X := by
    rw [inv_canHom_comp_map_canHom_comp_canHom gx' (j ≫ l) rx (gx' ≫ j ≫ l) (j ≫ l ≫ rx)
      (gx' ≫ j ≫ l ≫ rx) rfl (by simp) (by simp) rfl X]
  have eL3 : canHom τ gx (gx' ≫ j ≫ l) hk ((Scheme.Modules.pullback rx).obj X) ≫
      canHom (gx' ≫ j ≫ l) rx (gx' ≫ j ≫ l ≫ rx) (by simp) X =
      (Scheme.Modules.pullback τ).map (canHom gx rx (gx ≫ rx) rfl X) ≫
        canHom τ (gx ≫ rx) (gx' ≫ j ≫ l ≫ rx) hτ X :=
    (canHom_comp τ gx rx (gx' ≫ j ≫ l) (gx ≫ rx) (gx' ≫ j ≫ l ≫ rx) hk rfl (by simp)
      hτ X).symm
  have eR1 : (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map
        (canHom rsq ym (l ≫ rx) H₁ X ≫ inv (canHom l rx (l ≫ rx) rfl X))) ≫
      (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map
        (canHom l rx (l ≫ rx) rfl X)) =
      (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map
        (canHom rsq ym (l ≫ rx) H₁ X)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp
  have eR2 : (Scheme.Modules.pullback gx').map (inv (canHom j rsq (j ≫ rsq) rfl
        ((Scheme.Modules.pullback ym).obj X))) ≫
      (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map
        (canHom rsq ym (l ≫ rx) H₁ X)) ≫
      (Scheme.Modules.pullback gx').map (canHom j (l ≫ rx) (j ≫ l ≫ rx) rfl X) =
      (Scheme.Modules.pullback gx').map (canHom (j ≫ rsq) ym (j ≫ l ≫ rx)
        (by rw [Category.assoc, H₁]) X) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      inv_canHom_comp_map_canHom_comp_canHom j rsq ym (j ≫ rsq) (l ≫ rx) (j ≫ l ≫ rx) rfl H₁
        (by rw [Category.assoc, H₁]) rfl X]
  have eR3 : inv (canHom gx' (j ≫ rsq) (gx' ≫ j ≫ rsq) rfl ((Scheme.Modules.pullback ym).obj X)) ≫
      (Scheme.Modules.pullback gx').map (canHom (j ≫ rsq) ym (j ≫ l ≫ rx)
        (by rw [Category.assoc, H₁]) X) ≫
      canHom gx' (j ≫ l ≫ rx) (gx' ≫ j ≫ l ≫ rx) rfl X =
      canHom (gx' ≫ j ≫ rsq) ym (gx' ≫ j ≫ l ≫ rx) (by simp [H₁]) X := by
    rw [inv_canHom_comp_map_canHom_comp_canHom gx' (j ≫ rsq) ym (gx' ≫ j ≫ rsq) (j ≫ l ≫ rx)
      (gx' ≫ j ≫ l ≫ rx) rfl (by rw [Category.assoc, H₁]) (by simp [H₁]) rfl X]
  have eR4 : canHom cx' tx' (gx' ≫ j ≫ rsq) h2 ((Scheme.Modules.pullback ym).obj X) ≫
      canHom (gx' ≫ j ≫ rsq) ym (gx' ≫ j ≫ l ≫ rx) (by simp [H₁]) X =
      (Scheme.Modules.pullback cx').map (canHom tx' ym (tx' ≫ ym) rfl X) ≫
        canHom cx' (tx' ≫ ym) (gx' ≫ j ≫ l ≫ rx) hc X :=
    (canHom_comp cx' tx' ym (gx' ≫ j ≫ rsq) (tx' ≫ ym) (gx' ≫ j ≫ l ≫ rx) h2 rfl (by simp [H₁])
      hc X).symm
  have eR5 : (Scheme.Modules.pullback cx').map (canHom y tx (tx' ≫ ym) h5 X) ≫
      canHom cx' (tx' ≫ ym) (gx' ≫ j ≫ l ≫ rx) hc X =
      canHom cx' y (cx' ≫ y) rfl ((Scheme.Modules.pullback tx).obj X) ≫
        canHom (cx' ≫ y) tx (gx' ≫ j ≫ l ≫ rx)
          hy X :=
    canHom_comp cx' y tx (cx' ≫ y) (tx' ≫ ym) (gx' ≫ j ≫ l ≫ rx) rfl h5
      hy
      hc X
  have eR6 : canHom τ cx (cx' ≫ y) h4 ((Scheme.Modules.pullback tx).obj X) ≫
      canHom (cx' ≫ y) tx (gx' ≫ j ≫ l ≫ rx)
        hy X =
      (Scheme.Modules.pullback τ).map (canHom cx tx (gx ≫ rx) h1 X) ≫
        canHom τ (gx ≫ rx) (gx' ≫ j ≫ l ≫ rx) hτ X :=
    (canHom_comp τ cx tx (cx' ≫ y) (gx ≫ rx) (gx' ≫ j ≫ l ≫ rx) h4 h1
      hy
      hτ X).symm
  -- assemble
  simp only [Category.assoc]
  rw [reassoc_of% eL1, eL2, eL3, reassoc_of% eR1, reassoc_of% eR2, eR3, eR4]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [eR5, IsIso.inv_hom_id_assoc, eR6]

end PureCoherence

section SourceCoherence

open Stacks.AlgebraicGeometry.ModuleLimits (canHom canHom_comp canHom_naturality)

local notation "pb" => Scheme.Modules.pullback
local notation "pC" => Scheme.Modules.pullbackComp
local notation "pCg" => Scheme.Modules.pullbackCongr

/-- The inverse of the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` is natural in the module. -/
theorem inv_canHom_naturality {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) {A B : X.Modules} (f : A ⟶ B) :
    inv (canHom q g pi hpi A) ≫ (pb q).map ((pb g).map f) =
      (pb pi).map f ≫ inv (canHom q g pi hpi B) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← canHom_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- **The square-chain identification of the inverse images of the twists, at variables.**  Let
`n ≫ k₂ = k`, `n ≫ j₂ = l`, `(k ≫ r) ≫ p₁ = r_sq`, `(k₂ ≫ r) ≫ p₂ = r_c`, `j₂ ≫ r_x = r_c` and
`p₁ ≫ y_P = p₂`, and let `c_y : y_P^*X ≅ X'`, `c₁ : p₁^*X' ≅ W`, `c₂ : p₂^*X ≅ W` be isomorphisms
with `c₂` the contraction `p₂^*X ≅ p₁^*(y_P^*X)` followed by `p₁^*c_y` and `c₁`.  Then `r_sq^*c_y`
followed by the identification `r_sq^*X' ⟶ l^*(r_x^*X)` assembled from `c₁`, `c₂` and the
contractions of Stacks 01ZR (2) along the two factorisations of the square is the canonical
identification `r_sq^*(y_P^*X) ⟶ l^*(r_x^*X)`. -/
theorem canHom_squareChain_coherence {Usq U₂ Uat Pw Px Px' Ux : Scheme.{u}}
    (rsq : Usq ⟶ Px') (ym : Px' ⟶ Px) (l : Usq ⟶ Ux) (rx : Ux ⟶ Px) (n : Usq ⟶ U₂)
    (k₂ : U₂ ⟶ Uat) (k : Usq ⟶ Uat) (j₂ : U₂ ⟶ Ux) (rat : Uat ⟶ Pw) (pc₁ : Pw ⟶ Px')
    (pc₂ : Pw ⟶ Px) (rtc : U₂ ⟶ Px)
    (hk' : n ≫ k₂ = k) (hj' : n ≫ j₂ = l) (h8 : (k ≫ rat) ≫ pc₁ = rsq)
    (h9 : (k₂ ≫ rat) ≫ pc₂ = rtc) (h10 : j₂ ≫ rx = rtc) (hcomp : pc₁ ≫ ym = pc₂)
    (H₁ : rsq ≫ ym = l ≫ rx)
    {X : Px.Modules} {X' : Px'.Modules} {W : Pw.Modules} (cy : (pb ym).obj X ≅ X')
    (c1 : (pb pc₁).obj X' ≅ W) (c2 : (pb pc₂).obj X ≅ W)
    (hc : c2.hom = inv (canHom pc₁ ym pc₂ hcomp X) ≫ (pb pc₁).map cy.hom ≫ c1.hom) :
    (pb rsq).map cy.hom ≫ inv (canHom (k ≫ rat) pc₁ rsq h8 X') ≫
      inv (canHom k rat (k ≫ rat) rfl ((pb pc₁).obj X')) ≫ (pb k).map ((pb rat).map c1.hom) ≫
      inv (canHom n k₂ k hk' ((pb rat).obj W)) ≫
      (pb n).map ((pb k₂).map ((pb rat).map c2.inv) ≫
        canHom k₂ rat (k₂ ≫ rat) rfl ((pb pc₂).obj X) ≫ canHom (k₂ ≫ rat) pc₂ rtc h9 X ≫
        inv (canHom j₂ rx rtc h10 X)) ≫
      canHom n j₂ l hj' ((pb rx).obj X) =
    canHom rsq ym (l ≫ rx) H₁ X ≫ inv (canHom l rx (l ≫ rx) rfl X) := by
  -- move `cy` and `c1` to the right
  have m1 := inv_canHom_naturality (k ≫ rat) pc₁ rsq h8 cy.hom
  have m2 := inv_canHom_naturality k rat (k ≫ rat) rfl ((pb pc₁).map cy.hom)
  have m3 := inv_canHom_naturality n k₂ k hk' ((pb rat).map ((pb pc₁).map cy.hom ≫ c1.hom))
  have hcan : (pb pc₁).map cy.hom ≫ c1.hom ≫ c2.inv = canHom pc₁ ym pc₂ hcomp X := by
    rw [← Category.assoc, Iso.comp_inv_eq, hc, IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% m1, ← reassoc_of% m2, ← Functor.map_comp_assoc (pb k),
    ← Functor.map_comp (pb rat), ← reassoc_of% m3, ← Functor.map_comp_assoc (pb n),
    ← Functor.map_comp_assoc (pb k₂), ← Functor.map_comp (pb rat), Category.assoc, hcan]
  -- the canonical identity
  rw [← cancel_mono (canHom l rx (l ≫ rx) rfl X)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hA : n ≫ rtc = l ≫ rx := by rw [← h10, ← hj', Category.assoc]
  have hB : n ≫ (k₂ ≫ rat) ≫ pc₁ = rsq := by rw [← h8, ← hk']; simp only [Category.assoc]
  have hC : n ≫ k₂ ≫ rat = k ≫ rat := by rw [← hk', Category.assoc]
  have hD : ((k₂ ≫ rat) ≫ pc₁) ≫ ym = rtc := by rw [← h9, ← hcomp, Category.assoc]
  have e1 := canHom_comp n j₂ rx l rtc (l ≫ rx) hj' h10 rfl hA X
  have e2 := canHom_naturality k₂ rat (k₂ ≫ rat) rfl (canHom pc₁ ym pc₂ hcomp X)
  have e3 := canHom_comp (k₂ ≫ rat) pc₁ ym ((k₂ ≫ rat) ≫ pc₁) pc₂ rtc rfl hcomp hD h9 X
  have e4 := canHom_comp n ((k₂ ≫ rat) ≫ pc₁) ym rsq rtc (l ≫ rx) hB hD H₁ hA X
  have e5 := canHom_comp n (k₂ ≫ rat) pc₁ (k ≫ rat) ((k₂ ≫ rat) ≫ pc₁) rsq hC rfl h8 hB
    ((pb ym).obj X)
  have e6 := canHom_comp n k₂ rat k (k₂ ≫ rat) (k ≫ rat) hk' rfl rfl hC
    ((pb pc₁).obj ((pb ym).obj X))
  rw [← e1, ← Functor.map_comp_assoc (pb n)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% e2, e3, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, e4,
    reassoc_of% e5, reassoc_of% e6]
  simp only [IsIso.inv_hom_id_assoc]


/-- **The coherence of the source identifications around the square of the chart maps**, in the
shape of the source hypothesis of `AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq`:
the identifications are written with `Scheme.Modules.pullbackComp` and
`Scheme.Modules.pullbackCongr`, the comparison of sources along `τ ≫ c_x = c_{x'} ≫ y` uses the
twist comparison `c_y : y_P^*X ⟶ X'`, and the last factor `B` is any morphism with
`r_sq^*c_y ≫ B` the canonical identification (as provided by
`AlgebraicGeometry.Space.canHom_squareChain_coherence`).  Reduced to
`AlgebraicGeometry.Space.canHom_source_square_coherence` by the naturality of the canonical
identifications in `c_y`. -/
theorem source_square_coherence_of_squareChain {T T' Fx Fx' Px Px' Ux Ux' Usq : Scheme.{u}}
    (τ : T' ⟶ T) (cx : T ⟶ Fx)
    (tx : Fx ⟶ Px) (gx : T ⟶ Ux) (rx : Ux ⟶ Px) (cx' : T' ⟶ Fx') (tx' : Fx' ⟶ Px')
    (gx' : T' ⟶ Ux') (rx' : Ux' ⟶ Px') (j : Ux' ⟶ Usq) (l : Usq ⟶ Ux) (rsq : Usq ⟶ Px')
    (y : Fx' ⟶ Fx) (ym : Px' ⟶ Px)
    (h1 : cx ≫ tx = gx ≫ rx) (h2 : cx' ≫ tx' = gx' ≫ rx') (hk : τ ≫ gx = gx' ≫ j ≫ l)
    (h4 : τ ≫ cx = cx' ≫ y) (h5 : y ≫ tx = tx' ≫ ym) (hr : j ≫ rsq = rx')
    (H₁ : rsq ≫ ym = l ≫ rx) {X : Px.Modules} {X' : Px'.Modules} (cy : (pb ym).obj X ⟶ X')
    (Bi : (pb rsq).obj X' ⟶ (pb l).obj ((pb rx).obj X))
    (hBi : (pb rsq).map cy ≫ Bi = canHom rsq ym (l ≫ rx) H₁ X ≫ inv (canHom l rx (l ≫ rx) rfl X))
    (E4 : (pb (τ ≫ cx)).obj ((pb tx).obj X) = (pb (cx' ≫ y)).obj ((pb tx).obj X)) :
    (pb τ).map ((pC cx tx).hom.app X ≫ (pCg h1).hom.app X ≫ (pC gx rx).inv.app X) ≫
        ((pC τ gx).hom.app ((pb rx).obj X) ≫ (pCg hk).hom.app ((pb rx).obj X) ≫
          (pC gx' (j ≫ l)).inv.app ((pb rx).obj X) ≫
          (pb gx').map ((pC j l).inv.app ((pb rx).obj X))) =
      ((pC τ cx).hom.app ((pb tx).obj X) ≫ eqToHom E4 ≫ (pC cx' y).inv.app ((pb tx).obj X) ≫
          (pb cx').map ((pC y tx).hom.app X ≫ (pCg h5).hom.app X ≫ (pC tx' ym).inv.app X ≫
            (pb tx').map cy)) ≫
        ((pC cx' tx').hom.app X' ≫ (pCg h2).hom.app X' ≫ (pC gx' rx').inv.app X') ≫
        (pb gx').map ((pCg hr).inv.app X' ≫ (pC j rsq).inv.app X') ≫
        (pb gx').map ((pb j).map Bi) := by
  subst hr
  have hE : eqToHom E4 = (pCg h4).hom.app ((pb tx).obj X) := by
    simp [Scheme.Modules.pullbackCongr, eqToHom_app]
  rw [hE]
  have cv1 : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
      (F : C.Modules) {Z : A.Modules} (z : (pb c).obj F ⟶ Z),
      (pC a b).hom.app F ≫ (pCg h).hom.app F ≫ z = canHom a b c h F ≫ z := by
    intros; rw [← Category.assoc]; rfl
  have cv2 : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (F : C.Modules),
      (pC a b).inv.app F = inv (canHom a b (a ≫ b) rfl F) :=
    fun a b F => pullbackComp_inv_app_eq_inv_canHom a b F
  have cv3 : ∀ {A C : Scheme.{u}} (a : A ⟶ C) (h : a = a) (F : C.Modules),
      (pCg h).inv.app F = 𝟙 _ := by intros; rfl
  simp only [Functor.map_comp, Category.assoc, cv1, cv2, cv3, Category.id_comp]
  have key := canHom_source_square_coherence τ cx tx gx rx cx' tx' gx' j l rsq y ym h1 h2 hk h4
    h5 H₁ X
  rw [← hBi] at key
  simp only [Functor.map_comp] at key
  rw [key]
  have n1 := canHom_naturality cx' tx' (gx' ≫ j ≫ rsq) h2 cy
  have n2 := inv_canHom_naturality gx' (j ≫ rsq) (gx' ≫ j ≫ rsq) rfl cy
  have n3 := inv_canHom_naturality j rsq (j ≫ rsq) rfl cy
  have n3' : (pb gx').map ((pb (j ≫ rsq)).map cy) ≫
      (pb gx').map (inv (canHom j rsq (j ≫ rsq) rfl X')) ≫ (pb gx').map ((pb j).map Bi) =
      (pb gx').map (inv (canHom j rsq (j ≫ rsq) rfl ((pb ym).obj X))) ≫
        (pb gx').map ((pb j).map ((pb rsq).map cy)) ≫ (pb gx').map ((pb j).map Bi) := by
    rw [← Functor.map_comp_assoc, ← n3, Functor.map_comp_assoc]
  rw [reassoc_of% n1, ← reassoc_of% n2, n3']

end SourceCoherence

section SigmaUnfold

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying morphism of the identification of two equal objects of a full subcategory. -/
theorem fullSubcategory_eqToHom_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

/-- A commutative square of the site, read on the schemes through the inclusion of the small
étale sites. -/
theorem schemeHom_comp_eq_of_comp_eq {W V V' U : BigFppfOver B S hS} {τ : W ⟶ V} {c : V ⟶ U}
    {c' : W ⟶ V'} {y : V' ⟶ U} (e : τ ≫ c = c' ≫ y) :
    SmallEtale.schemeHom (associatedBigEtaleSite B) τ.left ≫
        SmallEtale.schemeHom (associatedBigEtaleSite B) c.left =
      SmallEtale.schemeHom (associatedBigEtaleSite B) c'.left ≫
        SmallEtale.schemeHom (associatedBigEtaleSite B) y.left :=
  congrArg (fun k => SmallEtale.schemeHom (associatedBigEtaleSite B) (Over.Hom.left k)) e

/-- **The source comparison `σ` on the underlying modules**: the contraction
`τ^*(c^*N) ≅ (τ ≫ c)^*N`, the identification along `τ ≫ c = c' ≫ y`, the inverse contraction and
the pullback along `c'` of `t : y^*N ⟶ N'`, as morphisms of quasi-coherent modules, are on the
underlying modules the corresponding composite of `Scheme.Modules.pullbackComp` and `eqToHom`
along the scheme morphisms of the site. -/
theorem quasicoherentPullbackCompIso_hom_comp_eqToHom_comp_inv_comp_map_hom
    {W V V' U : BigFppfOver B S hS}
    (τ : W ⟶ V) (c : V ⟶ U) (c' : W ⟶ V') (y : V' ⟶ U) (e : τ ≫ c = c' ≫ y)
    (N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V').ringCatSheaf).FullSubcategory}
    (t : quasicoherentPullbackObj B S hS y N ⟶ N') :
    InducedCategory.Hom.hom ((quasicoherentPullbackCompIso B S hS τ c N).hom ≫
        eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k N) e) ≫
        (quasicoherentPullbackCompIso B S hS c' y N).inv ≫ quasicoherentPullbackMap B S hS c' t) =
      (Scheme.Modules.pullbackComp (SmallEtale.schemeHom (associatedBigEtaleSite B) τ.left)
          (SmallEtale.schemeHom (associatedBigEtaleSite B) c.left)).hom.app N.obj ≫
        eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj N.obj)
          (schemeHom_comp_eq_of_comp_eq e)) ≫
        (Scheme.Modules.pullbackComp (SmallEtale.schemeHom (associatedBigEtaleSite B) c'.left)
          (SmallEtale.schemeHom (associatedBigEtaleSite B) y.left)).inv.app N.obj ≫
        (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B) c'.left)).map
          t.hom := by
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, fullSubcategory_eqToHom_hom]
  rfl

end SigmaUnfold

section SquareUnfold

open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra) in
/-- `AlgebraicGeometry.Space.pullbackSheafIsoOfSquare` of the piece of a comparison of graded
algebras, written out. -/
theorem pullbackSheafIsoOfSquare_gradedPieceIso_hom {X' X Y' Y : Scheme.{u}} (ιX : X' ⟶ X)
    (ιY : Y' ⟶ Y) (y : Y' ⟶ X') (pc : Y ⟶ X) (h : y ≫ ιX = ιY ≫ pc) {G : SchemeGradedAlgebra X}
    {G' : SchemeGradedAlgebra Y}
    (e : Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS pc G ≅ G')
    (n : ℤ) :
    (pullbackSheafIsoOfSquare ιX ιY y pc h (gradedPieceIso pc e n)).hom =
      (Scheme.Modules.pullbackComp y ιX).hom.app (G.piece n) ≫
        (Scheme.Modules.pullbackCongr h).hom.app (G.piece n) ≫
        (Scheme.Modules.pullbackComp ιY pc).inv.app (G.piece n) ≫
        (Scheme.Modules.pullback ιY).map (e.hom.app n) :=
  rfl

end SquareUnfold

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
  Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable (s : RelativeProjSituation.{u, m})

/-- `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison_comp` along a morphism
`k''` equal to the composite `k' ≫ k` (rather than the composite itself): the comparison of
twists along `pc'' = pc' ≫ pc` lying over `k''` is the comparison along `pc` pulled back along
`pc'`, followed by the comparison along `pc'`.  The shape in which the comparisons of twists along
`τ` and along `𝟙 ≫ τ = τ` meet. -/
theorem pointTwistComparison_comp_of_comp_eq {U V W : BigFppfOver s.site s.base s.containsBase}
    (k : V ⟶ U) (k' : W ⟶ V) (k'' : W ⟶ U) (hk : k' ≫ k = k'')
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (w : yoneda.obj W ⟶ s.space.1)
    (hv : yoneda.map k ≫ u = v) (hw : yoneda.map k' ≫ v = w) (hw'' : yoneda.map k'' ≫ u = w)
    (pc : (relativeProj (s.shrink.pointAlgebra V v)).scheme ⟶
      (relativeProj (s.shrink.pointAlgebra U u)).scheme)
    (hpc : pc = (relativeProjCongr (A₁ := s.shrink.pointAlgebra V v)
      (A₂ := (s.shrink.pointAlgebra U u).pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
      (s.quadrupleRestriction.restrict k u v hv)
      (s.quadrupleRestriction.isIso_restrict_app k u v hv)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra U u)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
    (pc' : (relativeProj (s.shrink.pointAlgebra W w)).scheme ⟶
      (relativeProj (s.shrink.pointAlgebra V v)).scheme)
    (hpc' : pc' = (relativeProjCongr (A₁ := s.shrink.pointAlgebra W w)
      (A₂ := (s.shrink.pointAlgebra V v).pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k'))
      (s.quadrupleRestriction.restrict k' v w hw)
      (s.quadrupleRestriction.isIso_restrict_app k' v w hw)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra V v)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k'))
    (pc'' : (relativeProj (s.shrink.pointAlgebra W w)).scheme ⟶
      (relativeProj (s.shrink.pointAlgebra U u)).scheme)
    (hpc'' : pc'' = (relativeProjCongr (A₁ := s.shrink.pointAlgebra W w)
      (A₂ := (s.shrink.pointAlgebra U u).pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k''))
      (s.quadrupleRestriction.restrict k'' u w hw'')
      (s.quadrupleRestriction.isIso_restrict_app k'' u w hw'')).hom ≫
        baseChangeHom (s.shrink.pointAlgebra U u)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k''))
    (hcomp : pc'' = pc' ≫ pc)
    (hpcT : pc ≫ (relativeProj (s.shrink.pointAlgebra U u)).toBase =
      (relativeProj (s.shrink.pointAlgebra V v)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (hpcT' : pc' ≫ (relativeProj (s.shrink.pointAlgebra V v)).toBase =
      (relativeProj (s.shrink.pointAlgebra W w)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k') :
    s.pointTwistComparison k'' u w hw'' pc'' hpc'' =
      Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _ hcomp ≪≫
        (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
          pc' pc).symm ≪≫
        Stacks.RingedSpace.pullbackGradedAlgebraMapIso _
          (s.pointTwistComparison k u v hv pc hpc) ≪≫
        s.pointTwistComparison k' v w hw pc' hpc' := by
  subst hk
  exact s.pointTwistComparison_comp k u v hv pc hpc k' w hw hw'' pc' hpc' pc'' hpc'' hcomp hpcT
    hpcT'

end AlgebraicGeometry.Space.RelativeProjSituation

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
  (x : yoneda.obj T ⟶ X.1) (hx : (ofUnitalHom s f L ψ).locusOpen T x = ⊤)

/-- **`τ` restricted to the loci**: for a scheme point `x` of `U(ψ)` at `T` and `τ : T' ⟶ T`,
the composite `T' ⟶ T ⟶ U(x^*ψ)` of `τ` and the section of `U(x^*ψ) ⊆ T` is the section
`T' ⟶ U((x ∘ τ)^*ψ)`, followed by `U((x ∘ τ)^*ψ) ⊆ U(τ^*(x^*ψ))` and the restriction
`U(τ^*(x^*ψ)) ⟶ U(x^*ψ)` of `τ`. -/
theorem map_comp_chartLift (hx'' : (ofUnitalHom s f L ψ).locusOpen T' (yoneda.map τ ≫ x) = ⊤) :
    (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ ≫
        (ofUnitalHom s f L ψ).chartLift x hx =
      (ofUnitalHom s f L ψ).chartLift (yoneda.map τ ≫ x) hx'' ≫
        (Scheme.homOfLE ((BigFppfOver.toScheme s.shrink.site s.shrink.base
          s.shrink.containsBase).obj T') ((ofUnitalHom s f L ψ).coveringOpen_twisting_map_le τ x) ≫
        Scheme.Hom.resLE
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ)
          (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting T x)).coveringOpen
          (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
            s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
            ((ofUnitalHom s f L ψ).twisting T x) ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
            (yoneda_map_id_comp_assoc s f.hom τ x))).coveringOpen
          (s.quadrupleRestriction.coveringOpen_squareTwisting
            s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
            ((ofUnitalHom s f L ψ).twisting T x) ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
            (yoneda_map_id_comp_assoc s f.hom τ x)).le) := by
  refine (cancel_mono
    (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting T x)).coveringOpen.ι).1 ?_
  refine ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((ofUnitalHom s f L ψ).chartLift_ι x hx)).trans
      (Category.comp_id _))).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Scheme.Hom.resLE_comp_ι _ _)))).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (Scheme.homOfLE_ι _ _)))).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    ((ofUnitalHom s f L ψ).chartLift_ι (yoneda.map τ ≫ x) hx'')).trans (Category.id_comp _))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
