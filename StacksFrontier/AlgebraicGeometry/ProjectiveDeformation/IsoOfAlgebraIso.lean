module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DegreeBound
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistBaseChange

/-!
# Isomorphisms of deformations out of isomorphisms of their section algebras

Let `D₁, D₂` be admissible deformations of a polarized family `P`, let `g : S'₁ ≅ S'₂` be an
isomorphism of their bases, and let `γ : g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` be a homomorphism of graded
algebras which is an isomorphism in every degree, where `𝒜'(Dᵢ)` is the truncated section algebra
at the degree bound `d₀` of [Stacks, Tag 0D4F] (`PolarizedFamily.degreeBound`). This file turns
`γ` into an isomorphism of the deformed families:

* the morphism `M : Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₁}(g^* 𝒜'(D₂)) ⟶ Proj_{S'₂}(𝒜'(D₂))`, the
  isomorphism of [Stacks, Tag 07ZJ] for `γ` followed by the base change morphism of
  [Stacks, Tag 01O3], is an isomorphism over `g`;
* through the isomorphisms `r'ᵢ : X'ᵢ ⟶ Proj_{S'ᵢ}(𝒜'(Dᵢ))` of conclusion (4) of
  [Stacks, Tag 0D4F] it gives an isomorphism `X'₁ ≅ X'₂` over `g`, whose square is cartesian;
* through the isomorphisms `θ'ᵢ : (r'ᵢ)^* 𝒪(1) ⟶ ℒ'ᵢ` of conclusion (5) and the map of Serre
  twists along `M` it carries `ℒ'₂` to `ℒ'₁`.

This generalizes `Hom.projBaseChangeHom` and `projBaseChangeTwistMap`, which are the case of the
homomorphism `algebraPullbackSheafHom φ` attached to a morphism of deformations `φ`.

## Main definitions

* `…AdmissibleDeformation.projHomOfAlgebraIso`, `…AdmissibleDeformation.projIsoOfAlgebraIso`:
  `M : Proj_{S'₁}(𝒜'(D₁)) ≅ Proj_{S'₂}(𝒜'(D₂))`.
* `…AdmissibleDeformation.canonicalProjIso`, `…AdmissibleDeformation.canonicalTwistIso`: `r'` and
  `θ'` at the degree bound, as isomorphisms.
* `…AdmissibleDeformation.projTwistIsoOfAlgebraIso`: the map of Serre twists
  `M^* 𝒪(1) ≅ 𝒪(1)` along `M`.
* `…AdmissibleDeformation.totalIsoOfAlgebraIso`: `X'₁ ≅ X'₂`.
* `…AdmissibleDeformation.polarizationIsoOfAlgebraIso`: `(X'₁ ≅ X'₂)^* ℒ'₂ ≅ ℒ'₁`.

## Main results

* `…ProjectiveDeformation.isPullback_projBaseChangeOfAlgebraHom`: for a homomorphism
  `ψ : g^* A ⟶ A'` invertible in all large degrees, `Proj_{S'}(A')` is the base change of
  `Proj_S(A)` along `g`.
* `…ProjectiveDeformation.isIso_baseChangeTwistHom_app`: the map of Serre twists along
  `Proj_{S'}(A') ⟶ Proj_S(A)` is an isomorphism in every degree.
* `…AdmissibleDeformation.totalIsoOfAlgebraIso_hom_comp`,
  `…AdmissibleDeformation.isPullback_totalIsoOfAlgebraIso`: `X'₁ ≅ X'₂` lies over `g`, with a
  cartesian square.

## Implementation notes

The isomorphism `M` is the base change morphism of [Stacks, Tag 01O3] composed with an
isomorphism, so it is the top row of a cartesian square whose bottom row `g` is an isomorphism,
hence an isomorphism (`IsPullback.isIso_fst_of_isIso`). The map of Serre twists is
`baseChangeTwistHom` in degree one; it is a composite of pseudofunctoriality isomorphisms of the
inverse image, the inverse image of the comparison of twists of [Stacks, Tag 01O3], and the
inverse image of the map of twists of [Stacks, Tag 07ZG], invertible by [Stacks, Tag 07ZJ].

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGTwist Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

section BaseChange

variable {S S' : Scheme.{u}} {A : SheafGradedAlgebra S} {g : S' ⟶ S} {A' : SheafGradedAlgebra S'}
  (ψ : SheafGradedAlgebraHom (A.pullback g) A')
  (hψ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)))

/-- **`Proj_{S'}(A')` is the base change of `Proj_S(A)` along `g`**, through the isomorphism
`Proj_{S'}(A') ⟶ Proj_{S'}(g^*A)` of [Stacks, Tag 07ZJ] for `ψ : g^*A ⟶ A'` followed by the base
change morphism of [Stacks, Tag 01O3]. -/
theorem isPullback_projBaseChangeOfAlgebraHom :
    IsPullback
      (projMapOfEventuallyIso ψ hψ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g)
      (relativeProj A').toBase (relativeProj A).toBase g := by
  have h := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.isPullback_baseChangeHom A g
  refine IsPullback.of_iso h (asIso (projMapOfEventuallyIso ψ hψ)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp
  · simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id]
    rw [IsIso.eq_inv_comp, projMapOfEventuallyIso_comp_toBase]

/-- **The map of Serre twists along `Proj_{S'}(A') ⟶ Proj_S(A)` is an isomorphism in every
degree**: it is built from pseudofunctoriality isomorphisms of the inverse image, the comparison
of twists of [Stacks, Tag 01O3] and the map of twists of [Stacks, Tag 07ZG], invertible by
[Stacks, Tag 07ZJ]. -/
instance isIso_baseChangeTwistHom_app (n : ℤ) : IsIso ((baseChangeTwistHom ψ hψ).app n) := by
  have := isIso_relativeTwistMap_of_eventually_isIso ψ hψ n
  let e : (Scheme.Modules.pullback
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g)).obj
        (relativeTwist A n) ≅ relativeTwist (A.pullback g) n :=
    { hom := (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom.app n
      inv := (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).inv.app n
      hom_inv_id := congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n)
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom_inv_id
      inv_hom_id := congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n)
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).inv_hom_id }
  change IsIso ((Scheme.Modules.pullbackComp (projMapOfEventuallyIso ψ hψ)
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g)).inv.app
        (relativeTwist A n) ≫
    (Scheme.Modules.pullback (projMapOfEventuallyIso ψ hψ)).map
      ((Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom.app n) ≫
    (projTwistHomOf ψ (projRetract ψ hψ) (projRetract_comp_ι ψ hψ)).app n)
  rw [projTwistHomOf_app]
  have h₁ : IsIso ((Scheme.Modules.pullback (projMapOfEventuallyIso ψ hψ)).map
      ((Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom.app n)) :=
    ((Scheme.Modules.pullback (projMapOfEventuallyIso ψ hψ)).mapIso e).isIso_hom
  have h₂ : IsIso ((Scheme.Modules.pullback (projRetract ψ hψ)).map (relativeTwistMap ψ n)) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' ((Scheme.Modules.pullbackComp _ _).app _).isIso_inv
    (IsIso.comp_isIso' h₁ (IsIso.comp_isIso' ((Scheme.Modules.pullbackComp _ _).app _).isIso_inv
    (IsIso.comp_isIso' h₂ (IsIso.comp_isIso' ((Scheme.Modules.pullbackComp _ _).app _).isIso_hom
    (IsIso.comp_isIso' ((Scheme.Modules.pullbackCongr _).app _).isIso_hom
      ((Scheme.Modules.pullbackId _).app _).isIso_hom)))))

end BaseChange

namespace PolarizedFamily.AdmissibleDeformation

variable {P : PolarizedFamily.{u}} (D₁ D₂ : P.AdmissibleDeformation) (g : D₁.S' ≅ D₂.S')
  (γ : SheafGradedAlgebraHom ((D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).pullback
    g.hom) (D₁.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos))
  (hγ : ∀ n : ℤ, IsIso (γ.app n))

include hγ in
/-- A homomorphism invertible in every degree is invertible in all large degrees. -/
theorem eventually_isIso_app_of_isIso :
    ∀ᶠ d : ℕ in Filter.atTop, IsIso (γ.app (d : ℤ)) :=
  Filter.Eventually.of_forall fun d => hγ d

/-- **The morphism `Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` attached to `γ`**: the isomorphism
`Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₁}(g^* 𝒜'(D₂))` of [Stacks, Tag 07ZJ] for `γ`, followed by the base
change morphism `Proj_{S'₁}(g^* 𝒜'(D₂)) ⟶ Proj_{S'₂}(𝒜'(D₂))` of [Stacks, Tag 01O3]. -/
def projHomOfAlgebraIso :
    (relativeProj (D₁.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).scheme ⟶
      (relativeProj (D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).scheme :=
  projMapOfEventuallyIso γ (eventually_isIso_app_of_isIso D₁ D₂ g γ hγ) ≫
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
      (D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos) g.hom

/-- **`Proj_{S'₁}(𝒜'(D₁))` is the base change of `Proj_{S'₂}(𝒜'(D₂))` along `g`**, through
`projHomOfAlgebraIso`. -/
theorem isPullback_projHomOfAlgebraIso :
    IsPullback (projHomOfAlgebraIso D₁ D₂ g γ hγ)
      (relativeProj (D₁.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).toBase
      (relativeProj (D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).toBase g.hom :=
  isPullback_projBaseChangeOfAlgebraHom γ (eventually_isIso_app_of_isIso D₁ D₂ g γ hγ)

/-- **`projHomOfAlgebraIso` is an isomorphism**: it is the top row of a cartesian square whose
bottom row `g` is an isomorphism. -/
instance isIso_projHomOfAlgebraIso : IsIso (projHomOfAlgebraIso D₁ D₂ g γ hγ) :=
  (isPullback_projHomOfAlgebraIso D₁ D₂ g γ hγ).isIso_fst_of_isIso

/-- **The isomorphism `Proj_{S'₁}(𝒜'(D₁)) ≅ Proj_{S'₂}(𝒜'(D₂))` attached to `γ`**, the morphism
`projHomOfAlgebraIso`. -/
def projIsoOfAlgebraIso :
    (relativeProj (D₁.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).scheme ≅
      (relativeProj (D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).scheme :=
  asIso (projHomOfAlgebraIso D₁ D₂ g γ hγ)

/-- **`projIsoOfAlgebraIso` lies over `g`.** -/
theorem projIsoOfAlgebraIso_hom_comp_toBase :
    (projIsoOfAlgebraIso D₁ D₂ g γ hγ).hom ≫
        (relativeProj (D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).toBase =
      (relativeProj (D₁.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).toBase ≫
        g.hom :=
  (isPullback_projHomOfAlgebraIso D₁ D₂ g γ hγ).w

/-- `r'` at the degree bound of [Stacks, Tag 0D4F] as an isomorphism `X' ≅ Proj_{S'}(𝒜')`
(conclusion (4) of the tag). -/
def canonicalProjIso (D : P.AdmissibleDeformation) :
    D.X' ≅ (relativeProj (D.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).scheme :=
  haveI := P.degreeBoundData.isIso_canonicalProjHom D
  asIso (D.canonicalProjHom P.degreeBound P.degreeBound_pos)

/-- **The isomorphism of deformed total spaces `X'₁ ≅ X'₂` attached to `γ`**:
`r'₁ ≫ M ≫ (r'₂)⁻¹`, for `M = projIsoOfAlgebraIso`. -/
def totalIsoOfAlgebraIso : D₁.X' ≅ D₂.X' :=
  canonicalProjIso D₁ ≪≫ projIsoOfAlgebraIso D₁ D₂ g γ hγ ≪≫ (canonicalProjIso D₂).symm

/-- **`totalIsoOfAlgebraIso` lies over `g`.** -/
theorem totalIsoOfAlgebraIso_hom_comp :
    (totalIsoOfAlgebraIso D₁ D₂ g γ hγ).hom ≫ D₂.f' = D₁.f' ≫ g.hom := by
  have h₁ := P.degreeBoundData.canonicalProjHom_comp_toBase D₁
  have h₂ := P.degreeBoundData.canonicalProjHom_comp_toBase D₂
  have h₂' : (canonicalProjIso D₂).inv ≫ D₂.f' =
      (relativeProj (D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos)).toBase := by
    rw [Iso.inv_comp_eq, ← h₂]
    rfl
  simp only [totalIsoOfAlgebraIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, h₂',
    projIsoOfAlgebraIso_hom_comp_toBase]
  rw [← Category.assoc]
  exact congrArg (· ≫ g.hom) h₁

/-- **The square of `totalIsoOfAlgebraIso` over `g` is cartesian**: both horizontal maps are
isomorphisms. -/
theorem isPullback_totalIsoOfAlgebraIso :
    IsPullback (totalIsoOfAlgebraIso D₁ D₂ g γ hγ).hom D₁.f' D₂.f' g.hom :=
  IsPullback.of_horiz_isIso ⟨totalIsoOfAlgebraIso_hom_comp D₁ D₂ g γ hγ⟩

/-- **`totalIsoOfAlgebraIso` is compatible with `r'`**: `(X'₁ ≅ X'₂) ≫ r'₂ = r'₁ ≫ M`. -/
theorem totalIsoOfAlgebraIso_hom_comp_canonicalProjHom :
    (totalIsoOfAlgebraIso D₁ D₂ g γ hγ).hom ≫
        D₂.canonicalProjHom P.degreeBound P.degreeBound_pos =
      D₁.canonicalProjHom P.degreeBound P.degreeBound_pos ≫ projHomOfAlgebraIso D₁ D₂ g γ hγ := by
  change (canonicalProjIso D₁ ≪≫ projIsoOfAlgebraIso D₁ D₂ g γ hγ ≪≫
      (canonicalProjIso D₂).symm).hom ≫ (canonicalProjIso D₂).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- `θ'` at the degree bound of [Stacks, Tag 0D4F] as an isomorphism `(r')^* 𝒪(1) ≅ ℒ'`
(conclusion (5) of the tag). -/
def canonicalTwistIso (D : P.AdmissibleDeformation) :
    (Scheme.Modules.pullback (D.canonicalProjHom P.degreeBound P.degreeBound_pos)).obj
        (relativeTwist (D.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos) 1) ≅ D.L' :=
  haveI := P.degreeBoundData.isIso_canonicalTwistMap D
  asIso (D.canonicalTwistMap P.degreeBound P.degreeBound_pos)

/-- **The map of Serre twists along `M = projHomOfAlgebraIso`** as an isomorphism
`M^* 𝒪_{Proj_{S'₂}(𝒜'(D₂))}(1) ≅ 𝒪_{Proj_{S'₁}(𝒜'(D₁))}(1)`: `baseChangeTwistHom γ` in degree
one. -/
def projTwistIsoOfAlgebraIso :
    (Scheme.Modules.pullback (projHomOfAlgebraIso D₁ D₂ g γ hγ)).obj
        (relativeTwist (D₂.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos) 1) ≅
      relativeTwist (D₁.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos) 1 :=
  @asIso _ _ _ _ ((baseChangeTwistHom γ (eventually_isIso_app_of_isIso D₁ D₂ g γ hγ)).app 1)
    (isIso_baseChangeTwistHom_app γ (eventually_isIso_app_of_isIso D₁ D₂ g γ hγ) 1)

/-- **The isomorphism of polarizations attached to `γ`**: `(X'₁ ≅ X'₂)^* ℒ'₂ ≅ ℒ'₁`, through
`θ'₂⁻¹`, the pseudofunctoriality of the inverse image along `r'₁ ≫ M = (X'₁ ≅ X'₂) ≫ r'₂`, the map
of Serre twists along `M` and `θ'₁`. -/
def polarizationIsoOfAlgebraIso :
    (Scheme.Modules.pullback (totalIsoOfAlgebraIso D₁ D₂ g γ hγ).hom).obj D₂.L' ≅ D₁.L' :=
  (Scheme.Modules.pullback (totalIsoOfAlgebraIso D₁ D₂ g γ hγ).hom).mapIso
      (canonicalTwistIso D₂).symm ≪≫
    (Scheme.Modules.pullbackComp (totalIsoOfAlgebraIso D₁ D₂ g γ hγ).hom
      (D₂.canonicalProjHom P.degreeBound P.degreeBound_pos)).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (totalIsoOfAlgebraIso_hom_comp_canonicalProjHom D₁ D₂ g γ hγ)).app _ ≪≫
    ((Scheme.Modules.pullbackComp (D₁.canonicalProjHom P.degreeBound P.degreeBound_pos)
      (projHomOfAlgebraIso D₁ D₂ g γ hγ)).app _).symm ≪≫
    (Scheme.Modules.pullback (D₁.canonicalProjHom P.degreeBound P.degreeBound_pos)).mapIso
      (projTwistIsoOfAlgebraIso D₁ D₂ g γ hγ) ≪≫
    canonicalTwistIso D₁

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
