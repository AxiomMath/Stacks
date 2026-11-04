module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.ThickeningLift
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningMorphismComparison

/-!
# Pulling back lifts of an object of `Coh_{X/Y}` along a morphism of thickenings

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and let `h : T ⟶ T'`,
`h₂ : T ⟶ T'₂` be morphisms of test schemes over `Y`, together with a morphism `g : T'₂ ⟶ T'`
under `T`, `h₂ ≫ g = h`. A lift `(𝒢', (X_h)^*𝒢' ≅ 𝒢)` of `ξ` across `h` pulls back to the lift
`((X_g)^*𝒢', (X_{h₂})^*(X_g)^*𝒢' ≅ (X_h)^*𝒢' ≅ 𝒢)` of `ξ` across `h₂`: this is the base change
of objects of `Coh_{X/Y}` (the cartesian morphism over `g`), and it is how the functoriality of
the deformation functors of `Coh_{X/Y}` in the thickening (for instance, in the module `M` of
the trivial square-zero extension `A[M]`) acts on lifts. Isomorphic lifts pull back to isomorphic
lifts, so the pullback descends to isomorphism classes.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.pullback`: the pulled back lift.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLiftClass.pullback`: its action on
  isomorphism classes.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}

/-- `X_{h₂} ≫ X_g = X_h` for `h₂ ≫ g = h`, in the spelling of the relative square. -/
theorem relativeMap_comp_of_comp_eq (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) :
    D.relativeSquareSituation.relativeMap h₂ ≫ D.relativeSquareSituation.relativeMap g =
      D.relativeSquareSituation.relativeMap h :=
  (D.relativeSquareSituation.relativeMap_comp h₂ g).trans
    (congrArg D.relativeSquareSituation.relativeMap hg)

/-- `X_g ≫ X_r = X_{r₂}` for `r₂ = g ≫ r`. -/
theorem relativeMap_comp_of_eq_comp {T₀ : SchemesOver D.Y} (g : T'₂ ⟶ T') {r : T' ⟶ T₀}
    {r₂ : T'₂ ⟶ T₀}
    (hgr : r₂ = g ≫ r) :
    D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.relativeMap r =
      D.relativeSquareSituation.relativeMap r₂ :=
  (D.relativeSquareSituation.relativeMap_comp g r).trans
    (congrArg D.relativeSquareSituation.relativeMap hgr.symm)

/-- The comparison `(X_{h₂})^*(X_g)^*𝒢' ≅ (X_h)^*𝒢'` for `h₂ ≫ g = h`: the comparison of
Stacks 03LU for `X_{h₂} ≫ X_g = X_h` (`AlgebraicGeometry.Space.modulePullbackTriangle`). -/
def pullbackComparison (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) :
    modulePullback B S hS (D.relativeMap g) ⋙ modulePullback B S hS (D.relativeMap h₂) ≅
      modulePullback B S hS (D.relativeMap h) :=
  (modulePullbackTriangle B S hS (relativeMap_comp_of_comp_eq g hg)).symm

/-- The comparison `(X_{h₂})^*(X_g)^*𝒢' ≅ (X_h)^*𝒢'` is the comparison of Stacks 03LU for the
composite `h₂ ≫ g` (`AlgebraicGeometry.Space.CoherentSituation.compComparison`), followed by the
identification of the inverse images along the morphisms of base changes induced by the equal
morphisms `h₂ ≫ g` and `h`. -/
theorem pullbackComparison_eq (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) :
    pullbackComparison g hg = (D.compComparison h₂ g).symm ≪≫ D.relativeMapComparison hg := by
  subst hg
  rw [relativeMapComparison, eqToIso_refl, Iso.trans_refl, compComparison]
  exact congrArg Iso.symm (D.relativeSquareSituation.relativeMapTriangle_eq h₂ g)

/-- **The pullback of a lift of `ξ` across `h` along a morphism `g : T'₂ ⟶ T'` under `T`.** The
module is the inverse image `(X_g)^*𝒢'`, which is again quasi-coherent of finite presentation,
flat over `T'₂` and with support proper over `T'₂` (base change in `Coh_{X/Y}`,
`AlgebraicGeometry.Space.CoherentSituation.pullbackObject'`), and the comparison is
`(X_{h₂})^*(X_g)^*𝒢' ≅ (X_h)^*𝒢' ≅ 𝒢`. -/
def ThickeningLift.pullback (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    D.ThickeningLift ξ h₂ where
  F := (modulePullback B S hS (D.relativeMap g)).obj L.F
  quasicoherent :=
    (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS) L.toObject
      g).quasicoherent
  finitePresentation :=
    (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS) L.toObject
      g).finitePresentation
  flat := (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS) L.toObject g).flat
  properSupport :=
    (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS) L.toObject
      g).properSupport
  fibre := (pullbackComparison g hg).hom.app L.F ≫ L.fibre
  isIso_fibre := @IsIso.comp_isIso _ _ _ _ _ _ _
    (Iso.isIso_hom ((pullbackComparison g hg).app L.F)) L.isIso_fibre

/-- The module of the pulled back lift is the inverse image of the lifted module along `X_g`. -/
theorem ThickeningLift.pullback_F (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    (L.pullback g hg).F = (modulePullback B S hS (D.relativeMap g)).obj L.F :=
  rfl

/-- The comparison of the pulled back lift. -/
theorem ThickeningLift.pullback_fibre (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    (L.pullback g hg).fibre = (pullbackComparison g hg).hom.app L.F ≫ L.fibre :=
  rfl

/-- **The comparisons of pulled back lifts are natural in the lift**: a map of lifted modules
compatible with the comparisons pulls back to one. -/
theorem ThickeningLift.pullback_fibre_naturality (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    {L₁ L₂ : D.ThickeningLift ξ h} (e : L₁.F ⟶ L₂.F)
    (he : (modulePullback B S hS (D.relativeMap h)).map e ≫ L₂.fibre = L₁.fibre) :
    (modulePullback B S hS (D.relativeMap h₂)).map
        ((modulePullback B S hS (D.relativeMap g)).map e) ≫ (L₂.pullback g hg).fibre =
      (L₁.pullback g hg).fibre := by
  rw [ThickeningLift.pullback_fibre, ThickeningLift.pullback_fibre, ← Category.assoc]
  have hn := (pullbackComparison g hg).hom.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [hn, Category.assoc, he]

/-- Isomorphic lifts pull back to isomorphic lifts. -/
theorem ThickeningLift.pullback_isIsomorphic (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    {L₁ L₂ : D.ThickeningLift ξ h} (H : L₁.IsIsomorphic L₂) :
    (L₁.pullback g hg).IsIsomorphic (L₂.pullback g hg) :=
  ⟨(modulePullback B S hS (D.relativeMap g)).mapIso H.choose,
    ThickeningLift.pullback_fibre_naturality g hg H.choose.hom H.choose_spec⟩

/-- **The pullback of isomorphism classes of lifts** along a morphism `g : T'₂ ⟶ T'` of
thickenings under `T`. -/
def ThickeningLiftClass.pullback (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) :
    D.ThickeningLiftClass ξ h → D.ThickeningLiftClass ξ h₂ :=
  Quotient.map (ThickeningLift.pullback g hg)
    (fun _ _ H => ThickeningLift.pullback_isIsomorphic g hg H)

/-- The pullback of the class of a lift is the class of its pullback. -/
theorem ThickeningLiftClass.pullback_mk (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    ThickeningLiftClass.pullback g hg (Quotient.mk (ThickeningLift.setoid D ξ h) L) =
      Quotient.mk (ThickeningLift.setoid D ξ h₂) (L.pullback g hg) :=
  rfl

/-- Isomorphic lifts from an isomorphism of the lifted modules compatible with the comparisons. -/
theorem ThickeningLift.isIsomorphic_of_iso {L₁ L₂ : D.ThickeningLift ξ h} (e : L₁.F ≅ L₂.F)
    (he : (modulePullback B S hS (D.relativeMap h)).map e.hom ≫ L₂.fibre = L₁.fibre) :
    L₁.IsIsomorphic L₂ :=
  ⟨e, he⟩

/-- **The cartesian morphism of `Coh_{X/Y}` from a pulled back lift to the lift**, over `g`: it is
the morphism `AlgebraicGeometry.Space.CoherentSituation.pullbackHom'` of base change in
`Coh_{X/Y}`, with the identity as its comparison of modules. -/
def ThickeningLift.pullbackHom (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    CoherentHom (L.pullback g hg).toObject L.toObject :=
  pullbackHom' (modulePullbackStabilityOfFinitePresentation B S hS) L.toObject g

/-- The base of the cartesian morphism from a pulled back lift is `g`. -/
theorem ThickeningLift.pullbackHom_base (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) : (L.pullbackHom g hg).base = g :=
  rfl

/-- The comparison of the cartesian morphism from a pulled back lift is the identity. -/
theorem ThickeningLift.pullbackHom_fibre (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    (L.pullbackHom g hg).fibre = 𝟙 ((modulePullback B S hS (D.relativeMap g)).obj L.F) :=
  rfl

end AlgebraicGeometry.Space.CoherentSituation

end
