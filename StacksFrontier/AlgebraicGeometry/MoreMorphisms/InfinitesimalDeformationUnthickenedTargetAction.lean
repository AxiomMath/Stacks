module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafHomTransitivity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationUnthickenedTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action on the lifting sheaf of an unthickened target

Let `S` be a scheme, let `i : X ⟶ X'` be a first order thickening over `S` and let `j : Y ⟶ Y'`
be an *isomorphism* — the case `Y = Y'` of [Stacks Project, Tag 04FK]. The sheaf of
[Stacks Project, Tag 04FH] is then the elementary rule
`Stacks.Thickenings.liftsOverBasePresheaf`, assigning to an open `V` of `X'` the morphisms
`V ⟶ Y'` over `S` restricting to `a` on `i⁻¹V`; that identification is
`Stacks.Thickenings.compatibleLiftsPresheafIsoLiftsOverBasePresheaf` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationUnthickenedTarget`.

This file supplies the remaining assertion of the remark: that
`Hom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` **acts** on that elementary rule, simply transitively over an
open carrying a lift, and compatibly with the restriction maps.

## Main definitions

* `Stacks.Thickenings.compatibleLiftsEquivLiftsOverBase`: the bijection between the lifts of
  [Stacks Project, Tag 04FI] over an open `V` and the elementary lifts over `V`. It is the
  identity on underlying morphisms.
* `Stacks.Thickenings.liftsOverBaseVAdd`: the action of a section of
  `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over `i⁻¹V` on an elementary lift over `V`.

## Main results

* `Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBase`: **the action clause of
  [Stacks Project, Tag 04FK]**, with the group laws, the compatibility with restriction, and
  simple transitivity over an open carrying a lift.

## Route

Nothing is reproved. The third condition of [Stacks Project, Tag 04FI] is automatic when `j` is
an isomorphism (`Stacks.Thickenings.isCompatibleLift_iff_of_isIso`), so the two notions of lift
over an open differ only in the proof component of a subtype and the bijection between them is
the identity on underlying morphisms. The action, its group laws, its compatibility with
restriction and its simple transitivity are the unrestricted [Stacks Project, Tag 04FJ] —
`Stacks.Thickenings.compatibleLiftsVAdd`, `Stacks.Thickenings.homSectionAct_zero`,
`Stacks.Thickenings.homSectionAct_add`,
`Stacks.Thickenings.compatibleLiftsRestrict_compatibleLiftsVAdd` and
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq` — transported along that bijection.

The conormal datum is taken to be `0`, which costs nothing: by
`Stacks.Thickenings.eq_zero_of_isIso` every datum for an isomorphic target is `0`, and the
elementary rule does not mention the datum at all.

## Implementation notes

The restriction maps on the two sides are `Stacks.Thickenings.compatibleLiftsRestrict` and
`Stacks.Thickenings.liftsOverBaseRestrict`, both of which compose the lift with the inclusion of
opens; `Stacks.Thickenings.liftsOverBaseRestrict_compatibleLiftsEquivLiftsOverBase` says the
bijection intertwines them, by `Subtype.ext rfl`.

## References

* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 04FK](https://stacks.math.columbia.edu/tag/04FK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'}
  [IsClosedImmersion i] [IsImmersion j] [IsIso j]

/-- **The lifts of [Stacks Project, Tag 04FI] are the elementary lifts when `Y = Y'`**, as a
bijection over each open `V` of `X'`. The third condition of the tag is automatic by
`Stacks.Thickenings.isCompatibleLift_iff_of_isIso`, so both sides are the morphisms `V ⟶ Y'`
over `S` restricting to `a` on `i⁻¹V`, and the bijection is the identity on underlying
morphisms. -/
def compatibleLiftsEquivLiftsOverBase (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) :
    compatibleLifts pX' pY' a A V ≃ liftsOverBase i j pX' pY' a V where
  toFun c := ⟨c.1, (isCompatibleLift_iff_of_isIso pX' pY' a A V c.1).mp c.2⟩
  invFun c := ⟨c.1, (isCompatibleLift_iff_of_isIso pX' pY' a A V c.1).mpr c.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The bijection of `Stacks.Thickenings.compatibleLiftsEquivLiftsOverBase` is the identity on
underlying morphisms. -/
theorem compatibleLiftsEquivLiftsOverBase_coe (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) (c : compatibleLifts pX' pY' a A V) :
    (compatibleLiftsEquivLiftsOverBase pX' pY' a A V c).1 = c.1 := rfl

/-- The inverse of `Stacks.Thickenings.compatibleLiftsEquivLiftsOverBase` is the identity on
underlying morphisms. -/
theorem compatibleLiftsEquivLiftsOverBase_symm_coe (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) (c : liftsOverBase i j pX' pY' a V) :
    ((compatibleLiftsEquivLiftsOverBase pX' pY' a A V).symm c).1 = c.1 := rfl

/-- **The bijection intertwines the two restriction maps.** Both
`Stacks.Thickenings.compatibleLiftsRestrict` and `Stacks.Thickenings.liftsOverBaseRestrict`
compose the lift with the inclusion `V' ⟶ V`. -/
theorem liftsOverBaseRestrict_compatibleLiftsEquivLiftsOverBase (pX' : X' ⟶ S) (pY' : Y' ⟶ S)
    (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V)
    (c : compatibleLifts pX' pY' a A V) :
    liftsOverBaseRestrict i j pX' pY' a hV (compatibleLiftsEquivLiftsOverBase pX' pY' a A V c)
      = compatibleLiftsEquivLiftsOverBase pX' pY' a A V'
          (compatibleLiftsRestrict pX' pY' a A hV c) :=
  Subtype.ext rfl

/-- **The bijection intertwines the two restriction maps**, in the direction needed for the
inverse: restricting an elementary lift and then crossing over is crossing over and then
restricting. -/
theorem compatibleLiftsRestrict_compatibleLiftsEquivLiftsOverBase_symm (pX' : X' ⟶ S)
    (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V)
    (c : liftsOverBase i j pX' pY' a V) :
    compatibleLiftsRestrict pX' pY' a A hV
        ((compatibleLiftsEquivLiftsOverBase pX' pY' a A V).symm c)
      = (compatibleLiftsEquivLiftsOverBase pX' pY' a A V').symm
          (liftsOverBaseRestrict i j pX' pY' a hV c) :=
  Subtype.ext rfl

/-- **The action of a section of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` on an elementary
lift.** This is `Stacks.Thickenings.compatibleLiftsVAdd` — the action of
[Stacks Project, Tag 04FJ] — read through the bijection
`Stacks.Thickenings.compatibleLiftsEquivLiftsOverBase`. -/
def liftsOverBaseVAdd (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (V : X'.Opens) (θ : deformationHomSections i a (j ≫ pY') V)
    (c : liftsOverBase i j pX' pY' a V) : liftsOverBase i j pX' pY' a V :=
  compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V
    (compatibleLiftsVAdd hsq pX' pY' a 0 V θ
      ((compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V).symm c))

/-- **The action clause of [Stacks Project, Tag 04FK].** Let `S` be a scheme, let `i : X ⟶ X'`
be a first order thickening, let `j : Y ⟶ Y'` be an isomorphism — the case `Y = Y'` of the
remark — let `p : X' ⟶ S` and `q : Y' ⟶ S` be the structure morphisms and let `a : X ⟶ Y`. The
sheaf `Hom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` acts on the elementary rule
`Stacks.Thickenings.liftsOverBasePresheaf` of the remark: over every open `V` of `X'` the
additive group of sections of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over `i⁻¹V` acts on the
morphisms `V ⟶ Y'` over `S` restricting to `a` on `i⁻¹V`, the action commutes with the
restriction maps of that rule, and over an open carrying a lift it is **simply transitive**.

No affineness is assumed, of `S`, `X'`, `Y'` or `V`, and no condition on conormal sheaves
appears anywhere: this is the action on the elementary rule itself, which is what the remark
asserts.

The action is `Stacks.Thickenings.liftsOverBaseVAdd`; everything about it is the unrestricted
[Stacks Project, Tag 04FJ] transported along
`Stacks.Thickenings.compatibleLiftsEquivLiftsOverBase`. -/
@[stacks 04FK "the action of Hom(a^*Ω_{Y/S}, 𝒞_{X/X'}) on the elementary lifting rule, with the \
group laws, the compatibility with restriction, and simple transitivity over an open carrying a \
lift", sga "3 XII 9.4" "partial"]
theorem exists_simplyTransitive_addAction_liftsOverBase (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S)
    (pY' : Y' ⟶ S) (a : X ⟶ Y) :
    ∃ act : ∀ V : X'.Opens, deformationHomSections i a (j ≫ pY') V →
        liftsOverBase i j pX' pY' a V → liftsOverBase i j pX' pY' a V,
      (∀ (V : X'.Opens) (c : liftsOverBase i j pX' pY' a V), act V 0 c = c) ∧
        (∀ (V : X'.Opens) (θ η : deformationHomSections i a (j ≫ pY') V)
          (c : liftsOverBase i j pX' pY' a V), act V (θ + η) c = act V θ (act V η c)) ∧
        (∀ (V V' : X'.Opens) (hV : V' ≤ V) (θ : deformationHomSections i a (j ≫ pY') V)
          (c : liftsOverBase i j pX' pY' a V),
          liftsOverBaseRestrict i j pX' pY' a hV (act V θ c)
            = act V' (moduleHomSections.restrict (i.preimage_mono hV) θ)
                (liftsOverBaseRestrict i j pX' pY' a hV c)) ∧
        ∀ (V : X'.Opens) (b₀ c₀ : liftsOverBase i j pX' pY' a V),
          ∃! θ : deformationHomSections i a (j ≫ pY') V, act V θ b₀ = c₀ := by
  -- The datum is `0`; by `Stacks.Thickenings.eq_zero_of_isIso` there is no other choice, and the
  -- elementary rule does not mention it.  The bijection is the identity on underlying morphisms,
  -- so the first three clauses hold by `Subtype.ext` from the unrestricted statements.
  refine ⟨liftsOverBaseVAdd hsq pX' pY' a, fun V c => Subtype.ext homSectionAct_zero,
    fun V θ η c => Subtype.ext homSectionAct_add, fun V V' hV θ c => ?_, fun V b₀ c₀ => ?_⟩
  · have h := compatibleLiftsRestrict_compatibleLiftsVAdd hsq pX' pY' a 0 hV θ
      ((compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V).symm c)
    exact Subtype.ext (congrArg (fun z => z.1) h)
  · obtain ⟨θ, hθ, huniq⟩ :=
      existsUnique_compatibleLiftsVAdd_eq hsq pX' pY' a 0 V
        ((compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V).symm b₀)
        ((compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V).symm c₀)
    refine ⟨θ, ?_, fun η hη => huniq η ?_⟩
    · exact Eq.trans (congrArg (compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V) hθ)
        ((compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V).apply_symm_apply c₀)
    · exact (compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V).injective
        (hη.trans ((compatibleLiftsEquivLiftsOverBase pX' pY' a 0 V).apply_symm_apply c₀).symm)

end Stacks.Thickenings

end
