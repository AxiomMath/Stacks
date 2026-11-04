module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseAction

/-!
# The action on the lifting sheaf is natural in the thickening

Let `k : Z ⟶ Z'` be an immersion, `i : X ⟶ X'` a first order thickening and `j : Y ⟶ Y'` an
immersion, both over `Z'`, with `Y = Z ×_{Z'} Y'`. The sheaf `Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})`
acts on the elementary lifting rule of [Stacks Project, Tag 04FK] by
`Stacks.Thickenings.liftsOverBaseVAddOfBase`; that is the action clause of
[Stacks Project, Tag 0CK2], proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseAction`.

That action is constructed at **one** such situation. This file supplies its naturality: given a
second situation and vertical maps from it to the first — the shape a *pushforward of a pair of
deformations along a morphism of `𝒞_Λ`* presents, where `X'` and `Y'` are the total spaces of two
deformations, `Z' = Spec` of the base, and the vertical maps are the projections of the two base
changes — acting and then pushing a lift forward is the same as pushing it forward and acting by
the pushed-forward section.

This is what any statement about a *sum* of first-order deformations consumes. The addition on the
tangent module of a deformation category is Schlessinger's, so by
`Deformation.exists_linearFunctorLift_sum` a sum of two tangent vectors is realized only over the
doubled coordinate module `M × M`: a construction has to be run once over `k[M × M]` and pushed
forward along the two projections `k[M × M] ⟶ k[M]` and their sum. For the derivation arrow of
[Stacks Project, Tag 0E3V] the construction is the translation action on lifts of a morphism, and
pushing it forward along those three morphisms of `𝒞_Λ` is exactly this naturality.

## Main results

* `Stacks.Thickenings.liftsOverBaseVAddOfBase_coe`: the morphism underlying the action is the
  lift `θ ⬝ b` of [Stacks Project, Tag 0CK1], `Stacks.Thickenings.homSectionAct`. Both of the
  identifications the action is read through are the identity on underlying morphisms, and
  `homSectionAct` depends on the proof that `b` restricts to `a` only through a proposition.
* `Stacks.Thickenings.homSectionAct_comp_of_homSectionValue_comm`: **the lift `θ ⬝ b` is natural
  in the thickening.** For two situations with vertical maps `(w, v)` and sections `θ₁`, `θ₂`
  whose perturbations agree under `w^♯` and `v^♯`, acting commutes with the vertical maps:
  `(θ₂ ⬝ b₂) ≫ v = w ≫ (θ₁ ⬝ b₁)`.
* `Stacks.Thickenings.liftsOverBaseVAddOfBase_comp_of_homSectionValue_comm`: **the action of
  [Stacks Project, Tag 0CK2] on the elementary lifting rule is natural in the thickening**, the
  same statement for `Stacks.Thickenings.liftsOverBaseVAddOfBase`.

## Route

Nothing geometric is reproved. The naturality of the lift `θ ⬝ b` is the remark
[Stacks Project, Tag 04BZ], proved for arbitrary schemes as
`Stacks.Thickenings.derivationActionSheaf_comp_of_derivationSection_comm`: two derivation data
whose derivations make the square of the source commute act compatibly with the vertical maps of
a diagram of first-order thickenings. Here the thickenings are the restrictions `i ∣_ V` of the
two thickenings to the opens carrying the lifts, and the data are the translates of `θ₁` and
`θ₂` along the conormal-track bridge, so that `θ ⬝ b` in the sense of
`Stacks.Thickenings.homSectionAct` is `θ ⬝ b` in the sense of
`Stacks.Thickenings.derivationActionSheaf`
(`Stacks.Thickenings.homSectionAct_eq_derivationActionSheaf`).

The hypothesis is stated with the perturbation `Stacks.Thickenings.homSectionValue` of the
deformation-sheaf development rather than with the derivation
`Stacks.Thickenings.derivationSectionι` of the derivation track, because that is the spelling in
which a consumer can check it: it is a statement about the conormal sections
`Stacks.Thickenings.conormalSection` that `θ₁` and `θ₂` produce. The two spellings agree by
`Stacks.Thickenings.derivationSectionι_eq_conormalSection`, which is how the hypothesis is fed to
that theorem.

## References

* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04BZ](https://stacks.math.columbia.edu/tag/04BZ)
* [Stacks Project, Tag 04FK](https://stacks.math.columbia.edu/tag/04FK)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

/-! ### The morphism underlying the action -/

section Coe

variable {X X' Y Y' Z Z' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {k : Z ⟶ Z'}
  [IsClosedImmersion i] [IsImmersion j] [IsImmersion k]
  {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X ⟶ Y}

/-- **The morphism underlying the action of [Stacks Project, Tag 0CK2] is the lift `θ ⬝ b` of
[Stacks Project, Tag 0CK1].** `Stacks.Thickenings.liftsOverBaseVAddOfBase` reads
`Stacks.Thickenings.compatibleLiftsVAdd` through two identifications, both of which are the
identity on underlying morphisms, and `Stacks.Thickenings.homSectionAct` depends on the witness
that `b` restricts to `a` only through a proposition; so the underlying morphism is
`Stacks.Thickenings.homSectionAct` at the transported section, for any such witness. -/
theorem liftsOverBaseVAddOfBase_coe (hsq : i.ker ^ 2 = ⊥) (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens)
    (θ : deformationHomSections i a h V) (c : liftsOverBase i j g' h' a V)
    (cb : i ∣_ V ≫ c.1 = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j) :
    (liftsOverBaseVAddOfBase hsq sq ci hA V θ c).1 =
      homSectionAct hsq h' cb (baseDeformationHomSectionsEquiv sq a V θ) := rfl

end Coe

/-! ### Naturality of the lift `θ ⬝ b` -/

section Naturality

variable {S₁ S₂ X₁ X₁' X₂ X₂' Y₁ Y₁' Y₂ Y₂' : Scheme.{u}}
  {i₁ : X₁ ⟶ X₁'} {i₂ : X₂ ⟶ X₂'} {j₁ : Y₁ ⟶ Y₁'} {j₂ : Y₂ ⟶ Y₂'}
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsImmersion j₁] [IsImmersion j₂]
  {a₁ : X₁ ⟶ Y₁} {a₂ : X₂ ⟶ Y₂} {V₁ : X₁'.Opens} {V₂ : X₂'.Opens}
  {b₁ : V₁.toScheme ⟶ Y₁'} {b₂ : V₂.toScheme ⟶ Y₂'}

/-- **The lift `θ ⬝ b` of [Stacks Project, Tag 0CK1] is natural in the thickening**, the remark
[Stacks Project, Tag 04BZ] in the spelling of the deformation sheaf of
[Stacks Project, Tag 04FH].

Let `i₁ : X₁ ⟶ X₁'` and `i₂ : X₂ ⟶ X₂'` be first-order thickenings, let `V₁` and `V₂` be opens
of `X₁'` and `X₂'` carrying lifts `b₁` and `b₂` of `a₁` and `a₂` along `j₁` and `j₂`, and let
`(wX, w)` and `(vY, v)` be vertical maps of the two thickenings compatible with the lifts, so
that `b₂ ≫ v = w ≫ b₁`. Let `θ₁` and `θ₂` be sections of the two sheaves of homomorphisms whose
perturbations `Stacks.Thickenings.homSectionValue` correspond under `w^♯` and `v^♯`. Then

`(θ₂ ⬝ b₂) ≫ v = w ≫ (θ₁ ⬝ b₁)`.

Nothing is assumed étale and nothing is assumed affine: the hypothesis `hθ` replaces the étale
transport of the datum, exactly as in [Stacks Project, Tag 04BZ]. -/
theorem homSectionAct_comp_of_homSectionValue_comm (hsq₁ : i₁.ker ^ 2 = ⊥)
    (hsq₂ : i₂.ker ^ 2 = ⊥) (pY₁' : Y₁' ⟶ S₁) (pY₂' : Y₂' ⟶ S₂)
    (cb₁ : i₁ ∣_ V₁ ≫ b₁ = ((i₁ ⁻¹ᵁ V₁).ι ≫ a₁) ≫ j₁)
    (cb₂ : i₂ ∣_ V₂ ≫ b₂ = ((i₂ ⁻¹ᵁ V₂).ι ≫ a₂) ≫ j₂)
    {wX : (i₂ ⁻¹ᵁ V₂).toScheme ⟶ (i₁ ⁻¹ᵁ V₁).toScheme} {w : V₂.toScheme ⟶ V₁.toScheme}
    {vY : Y₂ ⟶ Y₁} {v : Y₂' ⟶ Y₁'}
    (cT : i₂ ∣_ V₂ ≫ w = wX ≫ i₁ ∣_ V₁) (cj : j₂ ≫ v = vY ≫ j₁)
    (cX : ((i₂ ⁻¹ᵁ V₂).ι ≫ a₂) ≫ vY = wX ≫ ((i₁ ⁻¹ᵁ V₁).ι ≫ a₁))
    (cA : b₂ ≫ v = w ≫ b₁)
    (θ₁ : deformationHomSections i₁ a₁ (j₁ ≫ pY₁') V₁)
    (θ₂ : deformationHomSections i₂ a₂ (j₂ ≫ pY₂') V₂)
    (hθ : ∀ (W : Y₁'.Opens) (s : Γ(Y₁', W)),
      (V₂.toScheme.presheaf.map (eqToHom (preimage_comp_eq cA W)).op).hom
          ((w.app (b₁ ⁻¹ᵁ W)).hom (homSectionValue hsq₁ pY₁' cb₁ θ₁ W s))
        = homSectionValue hsq₂ pY₂' cb₂ θ₂ (v ⁻¹ᵁ W) ((v.app W).hom s)) :
    homSectionAct hsq₂ pY₂' cb₂ θ₂ ≫ v = w ≫ homSectionAct hsq₁ pY₁' cb₁ θ₁ := by
  rw [homSectionAct_eq_derivationActionSheaf hsq₁ pY₁' cb₁ θ₁,
    homSectionAct_eq_derivationActionSheaf hsq₂ pY₂' cb₂ θ₂]
  refine derivationActionSheaf_comp_of_derivationSection_comm
    (ker_pow_morphismRestrict_eq_bot i₁ hsq₁ V₁) (ker_pow_morphismRestrict_eq_bot i₂ hsq₂ V₂)
    pY₁' pY₂' cb₁ cb₂ cT cj cX cA (fun W s => ?_)
  rw [derivationSectionι_eq_conormalSection hsq₁ pY₁' cb₁ θ₁ W ((j₁.app W).hom s),
    derivationSectionι_eq_conormalSection hsq₂ pY₂' cb₂ θ₂ (v ⁻¹ᵁ W)
      ((j₂.app (v ⁻¹ᵁ W)).hom ((v.app W).hom s))]
  exact hθ W s

end Naturality

/-! ### Naturality of the action of Tag 0CK2 -/

section ActionNaturality

variable {X₁ X₁' X₂ X₂' Y₁ Y₁' Y₂ Y₂' Z₁ Z₁' Z₂ Z₂' : Scheme.{u}}
  {i₁ : X₁ ⟶ X₁'} {i₂ : X₂ ⟶ X₂'} {j₁ : Y₁ ⟶ Y₁'} {j₂ : Y₂ ⟶ Y₂'}
  {k₁ : Z₁ ⟶ Z₁'} {k₂ : Z₂ ⟶ Z₂'}
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsImmersion j₁] [IsImmersion j₂]
  [IsImmersion k₁] [IsImmersion k₂]
  {h₁ : Y₁ ⟶ Z₁} {h₁' : Y₁' ⟶ Z₁'} {g₁' : X₁' ⟶ Z₁'} {a₁ : X₁ ⟶ Y₁}
  {h₂ : Y₂ ⟶ Z₂} {h₂' : Y₂' ⟶ Z₂'} {g₂' : X₂' ⟶ Z₂'} {a₂ : X₂ ⟶ Y₂}

/-- **The action of [Stacks Project, Tag 0CK2] on the elementary lifting rule is natural in the
thickening.** This is the input a statement about a *sum* of first-order deformations needs: the
sum is realized over the doubled coordinate module `M × M`
(`Deformation.exists_linearFunctorLift_sum`), so the action has to be run once over `k[M × M]`
and pushed forward along the two projections `k[M × M] ⟶ k[M]` and their sum, and this is the
compatibility of the action with those pushforwards.

Let two situations of [Stacks Project, Tag 0CK2] be given, with vertical maps `(wX, w)` of the
thickenings and `(vY, v)` of the targets. Let `c` be an elementary lift over an open `V₁` of
`X₁'`, let `d` be one over an open `V₂` of `X₂'` with `d ≫ v = w ≫ c` on underlying morphisms,
and let `θ₁` and `θ₂` be sections of the two acting sheaves whose perturbations correspond under
`w^♯` and `v^♯`. Then acting and pushing forward commute:

`(θ₂ ⬝ d) ≫ v = w ≫ (θ₁ ⬝ c)`

on underlying morphisms. The hypothesis `hθ` is the commuting square of
[Stacks Project, Tag 04BZ] read on the conormal sections the two sections produce, and it is
transported to the acting sheaf of the source — the differentials relative to `Z₁` and to `Z₂` —
by `Stacks.Thickenings.baseDeformationHomSectionsEquiv`, which is the identification the action
is defined through. -/
@[stacks 0CK2 "the action of Hom(a^*Ω_{Y/Z}, 𝒞_{X/X'}) on the elementary lifting rule is \
natural in the thickening: for two situations of the tag with vertical maps, acting and pushing \
a lift forward commute, given the commuting square of Tag 04BZ for the two acting sections. \
This is naturality of the action, not a new construction of it"]
theorem liftsOverBaseVAddOfBase_comp_of_homSectionValue_comm
    (hsq₁ : i₁.ker ^ 2 = ⊥) (hsq₂ : i₂.ker ^ 2 = ⊥)
    (sq₁ : IsPullback j₁ h₁ h₁' k₁) (sq₂ : IsPullback j₂ h₂ h₂' k₂)
    (ci₁ : i₁ ≫ g₁' = (a₁ ≫ h₁) ≫ k₁) (ci₂ : i₂ ≫ g₂' = (a₂ ≫ h₂) ≫ k₂)
    {A₁ : (modulePullback a₁.toLRSHom.toShHom).obj (immersionConormalSheaf j₁) ⟶
      immersionConormalSheaf i₁}
    {A₂ : (modulePullback a₂.toLRSHom.toShHom).obj (immersionConormalSheaf j₂) ⟶
      immersionConormalSheaf i₂}
    (hA₁ : IsBaseCompatibleConormalMap i₁ j₁ k₁ h₁ h₁' g₁' a₁ sq₁.w ci₁ A₁)
    (hA₂ : IsBaseCompatibleConormalMap i₂ j₂ k₂ h₂ h₂' g₂' a₂ sq₂.w ci₂ A₂)
    (V₁ : X₁'.Opens) (V₂ : X₂'.Opens)
    (θ₁ : deformationHomSections i₁ a₁ h₁ V₁) (θ₂ : deformationHomSections i₂ a₂ h₂ V₂)
    (c : liftsOverBase i₁ j₁ g₁' h₁' a₁ V₁) (d : liftsOverBase i₂ j₂ g₂' h₂' a₂ V₂)
    {wX : (i₂ ⁻¹ᵁ V₂).toScheme ⟶ (i₁ ⁻¹ᵁ V₁).toScheme} {w : V₂.toScheme ⟶ V₁.toScheme}
    {vY : Y₂ ⟶ Y₁} {v : Y₂' ⟶ Y₁'}
    (cT : i₂ ∣_ V₂ ≫ w = wX ≫ i₁ ∣_ V₁) (cj : j₂ ≫ v = vY ≫ j₁)
    (cX : ((i₂ ⁻¹ᵁ V₂).ι ≫ a₂) ≫ vY = wX ≫ ((i₁ ⁻¹ᵁ V₁).ι ≫ a₁))
    (cA : d.1 ≫ v = w ≫ c.1)
    (hθ : ∀ (W : Y₁'.Opens) (s : Γ(Y₁', W)),
      (V₂.toScheme.presheaf.map (eqToHom (preimage_comp_eq cA W)).op).hom
          ((w.app (c.1 ⁻¹ᵁ W)).hom
            (homSectionValue hsq₁ h₁' c.2.2
              (baseDeformationHomSectionsEquiv sq₁ a₁ V₁ θ₁) W s))
        = homSectionValue hsq₂ h₂' d.2.2
            (baseDeformationHomSectionsEquiv sq₂ a₂ V₂ θ₂) (v ⁻¹ᵁ W) ((v.app W).hom s)) :
    (liftsOverBaseVAddOfBase hsq₂ sq₂ ci₂ hA₂ V₂ θ₂ d).1 ≫ v =
      w ≫ (liftsOverBaseVAddOfBase hsq₁ sq₁ ci₁ hA₁ V₁ θ₁ c).1 := by
  rw [liftsOverBaseVAddOfBase_coe hsq₁ sq₁ ci₁ hA₁ V₁ θ₁ c c.2.2,
    liftsOverBaseVAddOfBase_coe hsq₂ sq₂ ci₂ hA₂ V₂ θ₂ d d.2.2]
  exact homSectionAct_comp_of_homSectionValue_comm hsq₁ hsq₂ h₁' h₂'
    c.2.2 d.2.2 cT cj cX cA (baseDeformationHomSectionsEquiv sq₁ a₁ V₁ θ₁)
    (baseDeformationHomSectionsEquiv sq₂ a₂ V₂ θ₂) hθ

end ActionNaturality

end Stacks.Thickenings

end
