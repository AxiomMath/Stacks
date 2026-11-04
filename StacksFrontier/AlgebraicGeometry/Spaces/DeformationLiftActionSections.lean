module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMoveAction

/-!
# The action of local derivations on the sections of the sheaf of lifts

Let `X ⊂ X'` and `Y ⊂ Y'` be first order thickenings of algebraic spaces over a base `T`, let
`a : X ⟶ Y` be a morphism and `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` a map of `𝒪_X`-modules.  For an
object `U'` of the spaces-étale site of `X'` with `U = X ×_{X'} U'` (read as the inverse image
of `X` in `U'`), the sections over `U'` of the sheaf of [Stacks Project, Tag 061B] are
`AlgebraicGeometry.Space.conormalLiftSubfunctor`.  The group
`Hom_{𝒪_U}(a|_U^*Ω_{Y/T}, 𝒞_{U/U'})` acts on them, by the action `θ · a'` of
[Stacks Project, Tag 0CK6] at the morphism of thickenings `(a|_U, a') : (U ⊂ U') ⟶ (Y ⊂ Y')`,
and the action is simply transitive: this is the sectionwise content of
[Stacks Project, Tag 061C].

## Main definitions

* `AlgebraicGeometry.Space.conormalLiftActionHom`: the group `Hom_{𝒪_U}(a|_U^*Ω_{Y/T}, 𝒞_{U/U'})`.
* `AlgebraicGeometry.Space.conormalLiftAction`: the action `θ · a'` on the sections over `U'`.

## Main results

* `AlgebraicGeometry.Space.derivationMove_mem_conormalLiftSubfunctor`: `θ · a'` satisfies the
  three conditions of [Stacks Project, Tag 061A] when `a'` does.
* `AlgebraicGeometry.Space.conormalLiftAction_zero`,
  `AlgebraicGeometry.Space.conormalLiftAction_add`: it is an action.
* `AlgebraicGeometry.Space.conormalLiftAction_existsUnique`: it is simply transitive.

## References

* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

section Projection

variable {X' : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj}
  (hG : IsThickening C S hS X' G)

/-- **The two readings of `U = X ×_{X'} U'` restrict alike.**  Two morphisms out of `U'` which
agree on the inverse image of `X` in `U'` agree on the fibre product `X ×_{X'} U'`. -/
theorem thickeningProjection_comp_eq_of_subspaceInclusion_comp_eq (U' : SpacesEtale C S hS X')
    {Y' : AlgebraicSpaces C S hS} (a' b' : (SpacesEtale.toSpaces C S hS X').obj U' ⟶ Y')
    (h : subspaceInclusion C S hS ((SpacesEtale.toSpaces C S hS X').obj U')
          (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
            ⟨G, hG.1⟩) ≫ a' =
      subspaceInclusion C S hS ((SpacesEtale.toSpaces C S hS X').obj U')
          (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
            ⟨G, hG.1⟩) ≫ b') :
    (thickeningProjection C S hS hG).app U' ≫ a' =
      (thickeningProjection C S hS hG).app U' ≫ b' := by
  have hpb := (spacesBaseChange C S hS (IsThickening.inclusion C S hS hG)).isPullback U'
  have hl := (isPullback_preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
    (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).lift_snd _ _ hpb.w.symm
  exact (congrArg (· ≫ a') hl.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ b') hl))))

end Projection

variable {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
  (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)
  (A : (modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
    conormalModule C S hS X' ⟨G, hG.1⟩)

/-- **The group acting on the sections over `U'`**: the `𝒪_U`-linear maps
`a|_U^*Ω_{Y/T} ⟶ 𝒞_{U/U'}`, where `U` is the inverse image of `X` in `U'`, `a|_U` is the
projection `U ⟶ X` followed by `a`, and `Ω_{Y/T}` is taken along `Y ⊂ Y' ⟶ T`. -/
abbrev conormalLiftActionHom (U' : SpacesEtale C S hS X') : Type (u + 1) :=
  (modulePullback C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫ a)).obj
      (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ⟨H, hH.1⟩ ≫ pY')) ⟶
    conormalModule C S hS _
      (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)

variable {hG hH} (hG₁ : IsFirstOrderThickening C S hS X' G)
  (hH₁ : IsFirstOrderThickening C S hS Y' H)

include hH₁ in
/-- **`θ · a'` is again a section of the sheaf of [Stacks Project, Tag 061B].**  If `a'` satisfies
the three conditions of [Stacks Project, Tag 061A] over `U'`, then so does `θ · a'`. -/
theorem derivationMove_mem_conormalLiftSubfunctor (U' : SpacesEtale C S hS X')
    (θ : conormalLiftActionHom C S hS hG hH pY' a U')
    (s : (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) :
    derivationMove C S hS
        (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)
        ⟨H, hH.1⟩
        (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫ a)
        pY' (isFirstOrderThickening_preimage C S hS G _ hG₁) s.1 s.2.2.square θ
        (((SpacesEtale.inclusion C S hS X').obj U').hom ≫ pX') s.2.1.1 ∈
      (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U') := by
  obtain ⟨hb, hbq, hcon, -⟩ := derivationMove_spec C S hS
    (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)
    ⟨H, hH.1⟩
    (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫ a)
    pY' (isFirstOrderThickening_preimage C S hS G _ hG₁) hH₁ s.1 s.2.2.square θ
    (((SpacesEtale.inclusion C S hS X').obj U').hom ≫ pX') s.2.1.1
  exact ⟨⟨hbq, (thickeningProjection_comp_eq_of_subspaceInclusion_comp_eq C S hS hG U' _ s.1
    (hb.trans s.2.2.square.symm)).trans s.2.1.2⟩, ⟨hb, hcon.symm.trans s.2.2.conormal⟩⟩

/-- **The action of [Stacks Project, Tag 061C] on the sections over `U'`**: `θ · a'` of
[Stacks Project, Tag 0CK6] at the morphism of first order thickenings
`(a|_U, a') : (U ⊂ U') ⟶ (Y ⊂ Y')` over `T`. -/
def conormalLiftAction (U' : SpacesEtale C S hS X')
    (θ : conormalLiftActionHom C S hS hG hH pY' a U')
    (s : (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) :
    (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U') :=
  ⟨_, derivationMove_mem_conormalLiftSubfunctor C S hS pX' pY' a A hG₁ hH₁ U' θ s⟩

include hH₁ in
/-- `0 · a' = a'`. -/
theorem conormalLiftAction_zero (U' : SpacesEtale C S hS X')
    (s : (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) :
    conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' 0 s = s :=
  Subtype.ext (derivationMove_zero C S hS _ _ _ pY' _ hH₁ s.1 s.2.2.square _ s.2.1.1)

include hH₁ in
/-- `(θ₁ + θ₂) · a' = θ₁ · (θ₂ · a')`. -/
theorem conormalLiftAction_add (U' : SpacesEtale C S hS X')
    (θ₁ θ₂ : conormalLiftActionHom C S hS hG hH pY' a U')
    (s : (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) :
    conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' (θ₁ + θ₂) s =
      conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' θ₁
        (conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' θ₂ s) :=
  Subtype.ext (derivationMove_add C S hS _ _ _ pY' _ hH₁ s.1 s.2.2.square _ s.2.1.1 θ₁ θ₂
    (conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' θ₂ s).2.2.square
    (conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' θ₂ s).2.1.1)

include hH₁ in
/-- **Simple transitivity over `U'`.**  Any two sections `s, t` of the sheaf of
[Stacks Project, Tag 061B] over `U'` differ by the action of exactly one `θ`: there is a unique
`θ` with `θ · s = t`. -/
theorem conormalLiftAction_existsUnique (U' : SpacesEtale C S hS X')
    (s t : (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) :
    ∃! θ : conormalLiftActionHom C S hS hG hH pY' a U',
      conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' θ s = t := by
  obtain ⟨θ, hθ⟩ := exists_derivationMove_eq C S hS _ _ _ pY'
    (isFirstOrderThickening_preimage C S hS G _ hG₁) hH₁ s.1 s.2.2.square _ s.2.1.1 t.1
    t.2.2.square t.2.1.1 (s.2.2.conormal.trans t.2.2.conormal.symm)
  refine ⟨θ, Subtype.ext hθ, fun θ' hθ' ↦ ?_⟩
  exact derivationMove_injective C S hS _ _ _ pY' _ hH₁ s.1 s.2.2.square _ s.2.1.1 θ' θ
    ((congrArg Subtype.val hθ').trans hθ.symm)

end AlgebraicGeometry.Space

end
