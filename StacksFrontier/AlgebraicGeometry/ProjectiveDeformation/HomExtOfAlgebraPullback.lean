module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DegreeBound

/-!
# A morphism of deformations is determined by its base map and its algebra map

Let `φ : D₁ ⟶ D₂` be a morphism of admissible deformations of a polarized family, over
`g : S'₁ ⟶ S'₂`, with total part `g' : X'₁ ⟶ X'₂` and polarization `g'^* ℒ'₂ ≅ ℒ'₁`. For a cut
`d₀` at which `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` is invertible, the functoriality of `r'` and `θ'` of
[Stacks, Tag 0D4F] says

* `r'₁ ≫ M = g' ≫ r'₂`, where `M : Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` is built from `g`
  and `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` alone (`canonicalProjHom_comp_projBaseChangeHom`);
* `g'^* θ'₂` followed by the polarization is a composite built from `r'₁`, `r'₂`, `M`, the map of
  Serre twists along `M` and `θ'₁` (`canonicalTwistMap_comp_polarization`).

As `r'₂` and `θ'₂` are isomorphisms, a morphism of admissible deformations is determined by `g`
and by the homomorphism `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`.

## Main results

The names below are in the namespace `Stacks.AlgebraicGeometry.ProjectiveDeformation`.

* `PolarizedFamily.AdmissibleDeformation.Hom.ext_of_algebraPullbackSheafHom_of_isIso`: the
  statement at any cut `d₀` at which both algebra maps are invertible.
* `PolarizedFamily.AdmissibleDeformation.Hom.ext_of_algebraPullbackSheafHom`: the statement at
  the chosen degree bound `P.degreeBound`.
* `PolarizedFamily.AdmissibleDeformation.Hom.ext_of_base_eq_id`: two endomorphisms of a
  deformation over the identity of the base with the same algebra map are equal.
* `projMapOfEventuallyIso_comp_baseChangeHom_congr`: `M` and the map of Serre twists along it
  depend only on `g` and on `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`.
* `heq_of_pullback_map_comp_hom_eq`: an isomorphism `g'^* ℒ'₂ ≅ ℒ'₁` is determined by its
  composite with `g'^* θ'₂`.

## Implementation notes

The algebra map `algebraPullbackSheafHom φ d₀ hd₀` has type
`SheafGradedAlgebraHom (𝒜'(D₂).pullback φ.base) 𝒜'(D₁)`, which depends on `φ.base`; the
hypothesis comparing the algebra maps of two morphisms is therefore a `HEq`, which becomes an
equality once the base maps are identified. Likewise the polarization lives over `φ.total`, so
the two polarizations are compared as a `HEq`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

section General

variable {S₁ S₂ : Scheme.{u}} {A₁ : SheafGradedAlgebra S₁} {A₂ : SheafGradedAlgebra S₂}

/-- **The morphism `Proj_{S₁}(A₁) ⟶ Proj_{S₁}(g^* A₂) ⟶ Proj_{S₂}(A₂)` depends only on `g` and on
the homomorphism `g^* A₂ ⟶ A₁`**, and so does the map of Serre twists along it: for `g₁ = g₂` and
homomorphisms `ψᵢ : gᵢ^* A₂ ⟶ A₁` agreeing up to this equality, the two morphisms agree, and so do
the two maps of Serre twists, up to this equality. -/
theorem projMapOfEventuallyIso_comp_baseChangeHom_congr {g₁ g₂ : S₁ ⟶ S₂} (hg : g₁ = g₂)
    {ψ₁ : SheafGradedAlgebraHom (A₂.pullback g₁) A₁}
    {ψ₂ : SheafGradedAlgebraHom (A₂.pullback g₂) A₁}
    (hψ : HEq ψ₁ ψ₂) (h₁ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₁.app (d : ℤ)))
    (h₂ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ₂.app (d : ℤ))) :
    projMapOfEventuallyIso ψ₁ h₁ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A₂ g₁ =
      projMapOfEventuallyIso ψ₂ h₂ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A₂ g₂ ∧
    HEq ((baseChangeTwistHom ψ₁ h₁).app 1) ((baseChangeTwistHom ψ₂ h₂).app 1) := by
  subst hg
  cases eq_of_heq hψ
  exact ⟨rfl, HEq.rfl⟩

end General

/-- **An isomorphism `t^* L₂ ≅ L₁` is determined by its composite with the pullback of an
isomorphism `θ₂ : r₂^* O₂ ⟶ L₂`**, when that composite is read through a factorization
`t ≫ r₂ = r₁ ≫ M` and a map `τ : M^* O₂ ⟶ O₁`: if two such isomorphisms, over `t₁ = t₂`, have
composites `t^* r₂^* O₂ ≅ (t ≫ r₂)^* O₂ ≅ (r₁ ≫ M)^* O₂ ≅ r₁^* M^* O₂ ⟶ r₁^* O₁ ⟶ L₁` for data
`(M₁, τ₁)` and `(M₂, τ₂)` that agree, then they agree. -/
theorem heq_of_pullback_map_comp_hom_eq {X₁ X₂ P₁ P₂ : Scheme.{u}} {t₁ t₂ : X₁ ⟶ X₂}
    (ht : t₁ = t₂) (r₁ : X₁ ⟶ P₁) (r₂ : X₂ ⟶ P₂) {O₂ : P₂.Modules} {O₁ : P₁.Modules}
    {L₂ : X₂.Modules} {L₁ : X₁.Modules} (θ₂ : (Scheme.Modules.pullback r₂).obj O₂ ⟶ L₂) [IsIso θ₂]
    (θ₁ : (Scheme.Modules.pullback r₁).obj O₁ ⟶ L₁) {M₁ M₂ : P₁ ⟶ P₂} (hM : M₁ = M₂)
    {τ₁ : (Scheme.Modules.pullback M₁).obj O₂ ⟶ O₁} {τ₂ : (Scheme.Modules.pullback M₂).obj O₂ ⟶ O₁}
    (hτ : HEq τ₁ τ₂) (e₁ : t₁ ≫ r₂ = r₁ ≫ M₁) (e₂ : t₂ ≫ r₂ = r₁ ≫ M₂)
    (pol₁ : (Scheme.Modules.pullback t₁).obj L₂ ≅ L₁)
    (pol₂ : (Scheme.Modules.pullback t₂).obj L₂ ≅ L₁)
    (h₁ : (Scheme.Modules.pullback t₁).map θ₂ ≫ pol₁.hom =
      (Scheme.Modules.pullbackComp t₁ r₂).hom.app O₂ ≫
        (Scheme.Modules.pullbackCongr e₁).hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁ M₁).inv.app O₂ ≫
        (Scheme.Modules.pullback r₁).map τ₁ ≫ θ₁)
    (h₂ : (Scheme.Modules.pullback t₂).map θ₂ ≫ pol₂.hom =
      (Scheme.Modules.pullbackComp t₂ r₂).hom.app O₂ ≫
        (Scheme.Modules.pullbackCongr e₂).hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁ M₂).inv.app O₂ ≫
        (Scheme.Modules.pullback r₁).map τ₂ ≫ θ₁) :
    HEq pol₁ pol₂ := by
  subst ht hM
  cases eq_of_heq hτ
  refine heq_of_eq (Iso.ext ?_)
  rw [← cancel_epi ((Scheme.Modules.pullback t₁).map θ₂)]
  exact h₁.trans h₂.symm

namespace PolarizedFamily.AdmissibleDeformation.Hom

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation}

/-- **A morphism of admissible deformations is determined by its base map and its algebra map**,
at any cut `d₀` at which `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` is invertible for both morphisms. -/
theorem ext_of_algebraPullbackSheafHom_of_isIso (φ ψ : Hom D₁ D₂) (d₀ : ℕ) (hd₀ : 0 < d₀)
    (hisoφ : ∀ n : ℤ, IsIso ((algebraPullbackHom φ d₀ hd₀).app n))
    (hisoψ : ∀ n : ℤ, IsIso ((algebraPullbackHom ψ d₀ hd₀).app n))
    (hbase : φ.base = ψ.base)
    (halg : HEq (algebraPullbackSheafHom φ d₀ hd₀) (algebraPullbackSheafHom ψ d₀ hd₀)) :
    φ = ψ := by
  obtain ⟨hM, hτ⟩ := projMapOfEventuallyIso_comp_baseChangeHom_congr hbase halg
    (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hisoφ)
    (eventually_isIso_algebraPullbackSheafHom ψ d₀ hd₀ hisoψ)
  change projBaseChangeHom φ d₀ hd₀ hisoφ = projBaseChangeHom ψ d₀ hd₀ hisoψ at hM
  change HEq (projBaseChangeTwistMap φ d₀ hd₀ hisoφ) (projBaseChangeTwistMap ψ d₀ hd₀ hisoψ) at hτ
  have htotal : φ.total = ψ.total := by
    rw [← cancel_mono (D₂.canonicalProjHom d₀ hd₀),
      ← canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hisoφ, hM,
      canonicalProjHom_comp_projBaseChangeHom ψ d₀ hd₀ hisoψ]
  have hpol := heq_of_pullback_map_comp_hom_eq htotal (D₁.canonicalProjHom d₀ hd₀)
    (D₂.canonicalProjHom d₀ hd₀) (D₂.canonicalTwistMap d₀ hd₀) (D₁.canonicalTwistMap d₀ hd₀) hM hτ
    (canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hisoφ).symm
    (canonicalProjHom_comp_projBaseChangeHom ψ d₀ hd₀ hisoψ).symm φ.polarization ψ.polarization
    (canonicalTwistMap_comp_polarization φ d₀ hd₀ hisoφ)
    (canonicalTwistMap_comp_polarization ψ d₀ hd₀ hisoψ)
  obtain ⟨b, t, _, _, _, pol⟩ := φ
  obtain ⟨b', t', _, _, _, pol'⟩ := ψ
  dsimp only at hbase htotal hpol
  subst hbase htotal
  cases eq_of_heq hpol
  rfl

/-- **A morphism of admissible deformations is determined by its base map and its algebra map**
`g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` at the chosen degree bound `P.degreeBound` of [Stacks, Tag 0D4F]. -/
theorem ext_of_algebraPullbackSheafHom (φ ψ : Hom D₁ D₂) (hbase : φ.base = ψ.base)
    (halg : HEq (algebraPullbackSheafHom φ P.degreeBound P.degreeBound_pos)
      (algebraPullbackSheafHom ψ P.degreeBound P.degreeBound_pos)) :
    φ = ψ :=
  ext_of_algebraPullbackSheafHom_of_isIso φ ψ P.degreeBound P.degreeBound_pos
    ((degreeBoundData P).isIso_algebraPullbackHom φ)
    ((degreeBoundData P).isIso_algebraPullbackHom ψ) hbase halg

/-- **Two endomorphisms of an admissible deformation over the identity of the base with the same
algebra map `𝒜'(D)` at the chosen degree bound are equal.** -/
theorem ext_of_base_eq_id {D : P.AdmissibleDeformation} (φ ψ : Hom D D) (hφ : φ.base = 𝟙 D.S')
    (hψ : ψ.base = 𝟙 D.S')
    (halg : HEq (algebraPullbackSheafHom φ P.degreeBound P.degreeBound_pos)
      (algebraPullbackSheafHom ψ P.degreeBound P.degreeBound_pos)) :
    φ = ψ :=
  ext_of_algebraPullbackSheafHom φ ψ (hφ.trans hψ.symm) halg

end PolarizedFamily.AdmissibleDeformation.Hom

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
