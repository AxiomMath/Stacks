module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModuleHomSheaf

/-!
# The sheaf acting on the sheaf of lifts

Let `X ⊂ X'` and `Y ⊂ Y'` be thickenings of algebraic spaces over a base `T` and let
`a : X ⟶ Y` be a morphism.  This file builds the acting sheaf of [Stacks Project, Tag 061C],
`SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})`, as a sheaf of abelian groups on the spaces-étale site of
`X'`, and lets its sections act on the sections of the sheaf of lifts of
[Stacks Project, Tag 061B] (`AlgebraicGeometry.Space.conormalLiftSubfunctor`).

Sheaves on `X` and on `X'` are identified as in Equation [Stacks Project, Tag 05ZL]: an object
`U'` of `X'_{spaces,étale}` is sent to the inverse image `U = X ×_{X'} U'` of `X` in `U'`, an
object of `X_{spaces,étale}` (`AlgebraicGeometry.Space.thickeningPreimage`, which is isomorphic
to the base change functor and so continuous).  The sections of the acting sheaf over `U'` are
therefore the `𝒪_U`-linear maps `(a^*Ω_{Y/T})|_U ⟶ 𝒞_{X/X'}|_U`, the sections of
`SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})` over `U`
(`AlgebraicGeometry.Space.spacesEtaleModuleHom`).  Such a section is read as a map
`a|_U^*Ω_{Y/T} ⟶ 𝒞_{U/U'}` through the comparison of Stacks 03LU and the canonical
identification `𝒞_{X/X'}|_U ≅ 𝒞_{U/U'}` of [Stacks Project, Tag 04CQ] for the étale morphism
`U' ⟶ X'` (`AlgebraicGeometry.Space.conormalLiftActingEquiv`), and acts by the action `θ · a'`
of [Stacks Project, Tag 0CK6].

## Main definitions

* `AlgebraicGeometry.Space.thickeningPreimage`: `U' ↦ X ×_{X'} U'`, read as the inverse image.
* `AlgebraicGeometry.Space.conormalLiftActingPresheaf`: the acting sheaf
  (`AlgebraicGeometry.Space.isSheaf_conormalLiftActingPresheaf`).
* `AlgebraicGeometry.Space.conormalLiftActingEquiv`, `AlgebraicGeometry.Space.conormalLiftActing`:
  its sections over `U'`, read as maps `a|_U^*Ω_{Y/T} ⟶ 𝒞_{U/U'}`.
* `AlgebraicGeometry.Space.conormalLiftSheafAddAction`: the action on the sections over `U'`.

## Main results

* `AlgebraicGeometry.Space.conormalLiftSheafAddAction_bijective`: the action is simply transitive
  over every `U'` over which the sheaf of lifts has a section.

## References

* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 061B](https://stacks.math.columbia.edu/tag/061B)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

section Preimage

variable {X' : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} (hG : IsThickening C S hS X' G)

/-- The inverse image `U = X ×_{X'} U'` of the thickening `X ⊂ X'` in an object `U'` of the
spaces-étale site of `X'`, as an object of the spaces-étale site of `X`: its structure morphism
is the projection `U ⟶ X`, étale as a base change of `U' ⟶ X'`. -/
abbrev thickeningPreimageObj (U' : SpacesEtale C S hS X') :
    SpacesEtale C S hS (IsThickening.space C S hS hG) :=
  ⟨Over.mk (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
      ⟨G, hG.1⟩),
    isEtale_preimageProjection C S hS _ U'.property ⟨G, hG.1⟩⟩

/-- The inverse image of `X` in `U'` is the base change `X ×_{X'} U'`: both are fibre products of
`X ⟶ X' ⟵ U'`. -/
def thickeningPreimageIso (U' : SpacesEtale C S hS X') :
    thickeningPreimageObj C S hS hG U' ≅ (thickeningBaseChange C S hS hG).obj U' :=
  ObjectProperty.isoMk (e := Over.isoMk
    ((isPullback_preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
      ⟨G, hG.1⟩).flip.isoIsPullback _ _
      ((spacesBaseChange C S hS (IsThickening.inclusion C S hS hG)).isPullback U'))
    (IsPullback.isoIsPullback_hom_snd _ _ _ _))

/-- **The identification of Equation [Stacks Project, Tag 05ZL] on objects**: the functor
`U' ↦ X ×_{X'} U'` from the spaces-étale site of `X'` to that of `X`, with `X ×_{X'} U'` read as
the inverse image of `X` in `U'`.  It is the base change functor
`AlgebraicGeometry.Space.thickeningBaseChange` with its objects replaced by the inverse images. -/
def thickeningPreimage :
    SpacesEtale C S hS X' ⥤ SpacesEtale C S hS (IsThickening.space C S hS hG) :=
  (thickeningBaseChange C S hS hG).copyObj (thickeningPreimageObj C S hS hG)
    fun U' => (thickeningPreimageIso C S hS hG U').symm

/-- The functor `U' ↦ X ×_{X'} U'` is continuous for the étale topologies of the spaces-étale sites
of `X'` and of `X`. -/
instance isContinuous_thickeningPreimage :
    (thickeningPreimage C S hS hG).IsContinuous (SpacesEtale.topology C S hS X')
      (SpacesEtale.topology C S hS (IsThickening.space C S hS hG)) :=
  Functor.isContinuous_of_iso ((thickeningBaseChange C S hS hG).isoCopyObj _ _) _ _

/-- **The inverse images of `X` restrict along a morphism of the spaces-étale site of `X'`.**
For `k : V' ⟶ U'`, the morphism `X ×_{X'} V' ⟶ X ×_{X'} U'` underlying
`AlgebraicGeometry.Space.thickeningPreimage` at `k`, followed by the inclusion of the inverse
image of `X` in `U'`, is the inclusion of the inverse image of `X` in `V'` followed by `k`. -/
theorem toSpaces_map_thickeningPreimage_map_comp_subspaceInclusion {U' V' : SpacesEtale C S hS X'}
    (k : V' ⟶ U') :
    (SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
        ((thickeningPreimage C S hS hG).map k) ≫
      subspaceInclusion C S hS ((SpacesEtale.toSpaces C S hS X').obj U')
        (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩) =
    subspaceInclusion C S hS ((SpacesEtale.toSpaces C S hS X').obj V')
        (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj V').hom ⟨G, hG.1⟩) ≫
      (SpacesEtale.toSpaces C S hS X').map k := by
  have hf : ∀ W' : SpacesEtale C S hS X',
      (SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
          (thickeningPreimageIso C S hS hG W').hom ≫ (thickeningProjection C S hS hG).app W' =
        subspaceInclusion C S hS ((SpacesEtale.toSpaces C S hS X').obj W')
          (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj W').hom ⟨G, hG.1⟩) :=
    fun W' ↦ IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hn := (thickeningProjection C S hS hG).naturality k
  show (SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
      ((thickeningPreimageIso C S hS hG V').hom ≫ (thickeningBaseChange C S hS hG).map k ≫
        (thickeningPreimageIso C S hS hG U').inv) ≫ _ = _
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← hf U',
    ← Category.assoc ((SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
      (thickeningPreimageIso C S hS hG U').inv), ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← hf V', Category.assoc]
  exact congrArg (_ ≫ ·) hn

end Preimage

variable {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
  (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)
  (A : (modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
    conormalModule C S hS X' ⟨G, hG.1⟩)

/-- **The acting sheaf of [Stacks Project, Tag 061C]**: `SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})`,
the presheaf on the spaces-étale site of `X` whose sections over `U` are the `𝒪_U`-linear maps
`(a^*Ω_{Y/T})|_U ⟶ 𝒞_{X/X'}|_U` (`AlgebraicGeometry.Space.spacesEtaleModuleHom`), read on the
spaces-étale site of `X'` through `U' ↦ X ×_{X'} U'` (Equation [Stacks Project, Tag 05ZL]).
Here `Ω_{Y/T}` is the sheaf of differentials of `Y ⊂ Y' ⟶ T`.  It is a sheaf,
`AlgebraicGeometry.Space.isSheaf_conormalLiftActingPresheaf`, and its sections are abelian groups
(`Hom` groups of modules) with additive restriction maps. -/
abbrev conormalLiftActingPresheaf : (SpacesEtale C S hS X')ᵒᵖ ⥤ Type (u + 1) :=
  (thickeningPreimage C S hS hG).op ⋙ spacesEtaleModuleHom C S hS
    ((modulePullback C S hS a).obj
      (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ⟨H, hH.1⟩ ≫ pY')))
    (conormalModule C S hS X' ⟨G, hG.1⟩)

/-- The acting presheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})`, read through
`U' ↦ X ×_{X'} U'`, is a sheaf on the spaces-étale site of `X'`. -/
@[stacks 061C "the acting sheaf SheafHom_{O_X}(a^*Ω_{Y/B}, C_{X/X'}), read on (X')_{spaces, étale} \
through the identification 05ZL, is a sheaf"]
theorem isSheaf_conormalLiftActingPresheaf :
    Presieve.IsSheaf (SpacesEtale.topology C S hS X')
      (conormalLiftActingPresheaf C S hS hG hH pY' a) :=
  Functor.op_comp_isSheaf_of_isSheaf_type (F := thickeningPreimage C S hS hG)
    (SpacesEtale.topology C S hS X') (isSheaf_spacesEtaleModuleHom C S hS _ _)

/-- The canonical map `𝒞_{X/X'}|_U ⟶ 𝒞_{U/U'}` of [Stacks Project, Tag 04CP] for the étale
restriction square of `U' ⟶ X'`. -/
abbrev conormalRestrictionMap (U' : SpacesEtale C S hS X') :
    (modulePullback C S hS
        (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)).obj
        (conormalModule C S hS X' ⟨G, hG.1⟩) ⟶
      conormalModule C S hS _
        (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩) :=
  conormalMap C S hS
    (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩) ⟨G, hG.1⟩
    ((SpacesEtale.inclusion C S hS X').obj U').hom
    (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)
    (conormalEtaleRestrictionSquare C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
      ⟨G, hG.1⟩)

/-- The canonical map `𝒞_{X/X'}|_U ⟶ 𝒞_{U/U'}` is an isomorphism, the flat clause of
[Stacks Project, Tag 04CQ] at the étale morphism `U' ⟶ X'`. -/
def conormalRestrictionIso (U' : SpacesEtale C S hS X') :
    (modulePullback C S hS
        (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)).obj
        (conormalModule C S hS X' ⟨G, hG.1⟩) ≅
      conormalModule C S hS _
        (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩) :=
  @asIso _ _ _ _ (conormalRestrictionMap C S hS hG U')
    (isIso_conormalMap_of_isEtale C S hS _ U'.property ⟨G, hG.1⟩)

/-- **The sections of the acting sheaf over `U'`, read as maps `a|_U^*Ω_{Y/T} ⟶ 𝒞_{U/U'}`.**  A
section `θ : (a^*Ω_{Y/T})|_U ⟶ 𝒞_{X/X'}|_U` is composed with the comparison
`a|_U^*Ω_{Y/T} ≅ (a^*Ω_{Y/T})|_U` of Stacks 03LU and with the isomorphism
`𝒞_{X/X'}|_U ≅ 𝒞_{U/U'}` of [Stacks Project, Tag 04CQ] for the étale morphism `U' ⟶ X'`.  This
is a bijection. -/
def conormalLiftActingEquiv (U' : SpacesEtale C S hS X') :
    ((modulePullback C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)).obj
      ((modulePullback C S hS a).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ⟨H, hH.1⟩ ≫ pY'))) ⟶
    (modulePullback C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩)).obj
      (conormalModule C S hS X' ⟨G, hG.1⟩)) ≃
      conormalLiftActionHom C S hS hG hH pY' a U' :=
  Iso.homCongr ((modulePullbackCompIso C S hS
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩) a).app
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ⟨H, hH.1⟩ ≫ pY')))
    (conormalRestrictionIso C S hS hG U')

/-- **The acting sheaf of [Stacks Project, Tag 061C], with its sections read as maps
`a|_U^*Ω_{Y/T} ⟶ 𝒞_{U/U'}`**: `AlgebraicGeometry.Space.conormalLiftActingPresheaf` with its
sections replaced along the bijections `AlgebraicGeometry.Space.conormalLiftActingEquiv`, so that
its sections over `U'` are `AlgebraicGeometry.Space.conormalLiftActionHom` on the nose. -/
def conormalLiftActing : (SpacesEtale C S hS X')ᵒᵖ ⥤ Type (u + 1) :=
  (conormalLiftActingPresheaf C S hS hG hH pY' a).copyObj
    (fun U' => conormalLiftActionHom C S hS hG hH pY' a U'.unop)
    fun U' => (conormalLiftActingEquiv C S hS hG hH pY' a U'.unop).toIso

/-- The sections of `AlgebraicGeometry.Space.conormalLiftActing` over `U'` are
`Hom_{𝒪_U}(a|_U^*Ω_{Y/T}, 𝒞_{U/U'})`. -/
theorem conormalLiftActing_obj (U' : SpacesEtale C S hS X') :
    (conormalLiftActing C S hS hG hH pY' a).obj (op U') =
      conormalLiftActionHom C S hS hG hH pY' a U' :=
  rfl

/-- `AlgebraicGeometry.Space.conormalLiftActing` is isomorphic to the acting sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/T}, 𝒞_{X/X'})` read on `X'`. -/
def conormalLiftActingIso :
    conormalLiftActingPresheaf C S hS hG hH pY' a ≅ conormalLiftActing C S hS hG hH pY' a :=
  (conormalLiftActingPresheaf C S hS hG hH pY' a).isoCopyObj _ _

/-- **The acting presheaf of [Stacks Project, Tag 061C] is a sheaf** on the spaces-étale site
of `X'`. -/
theorem isSheaf_conormalLiftActing :
    Presieve.IsSheaf (SpacesEtale.topology C S hS X') (conormalLiftActing C S hS hG hH pY' a) :=
  Presieve.isSheaf_iso _ (conormalLiftActingIso C S hS hG hH pY' a)
    (isSheaf_conormalLiftActingPresheaf C S hS hG hH pY' a)

variable {hG hH} (hG₁ : IsFirstOrderThickening C S hS X' G)
  (hH₁ : IsFirstOrderThickening C S hS Y' H)

/-- **The action on the sheaf of lifts over `U'`.**  A section `θ` of the acting sheaf
over `U'` acts on a section `a'` of the sheaf of lifts (061B) by the action `θ · a'` of
[Stacks Project, Tag 0CK6], `θ` read as a map `a|_U^*Ω_{Y/T} ⟶ 𝒞_{U/U'}` by
`AlgebraicGeometry.Space.conormalLiftActingEquiv`. -/
@[instance_reducible, stacks 061C "the action, over every object U' of (X')_{spaces, étale}, of \
the sections of SheafHom_{O_X}(a^*Ω_{Y/B}, C_{X/X'}) on the sections of the sheaf 061B"]
def conormalLiftSheafAddAction (U' : SpacesEtale C S hS X') :
    AddAction (conormalLiftActionHom C S hS hG hH pY' a U')
      ((conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) where
  vadd θ s := conormalLiftAction C S hS pX' pY' a A hG₁ hH₁ U' θ s
  zero_vadd s := conormalLiftAction_zero C S hS pX' pY' a A hG₁ hH₁ U' s
  add_vadd θ₁ θ₂ s := conormalLiftAction_add C S hS pX' pY' a A hG₁ hH₁ U' θ₁ θ₂ s

/-- **Simple transitivity of the action on the sheaf of lifts** over every object `U'`
over which the sheaf of lifts (061B) has a section `s`: `θ ↦ θ · s` is a bijection from the
sections of the acting sheaf over `U'` onto the sections of the sheaf of lifts over `U'`. -/
@[stacks 061C "the action is simply transitive over every object U' of (X')_{spaces, étale} \
over which the sheaf 061B has a section"]
theorem conormalLiftSheafAddAction_bijective (U' : SpacesEtale C S hS X')
    (s : (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).obj (op U')) :
    letI := conormalLiftSheafAddAction C S hS pX' pY' a A hG₁ hH₁ U'
    Function.Bijective (fun θ : conormalLiftActionHom C S hS hG hH pY' a U' => θ +ᵥ s) := by
  let := conormalLiftSheafAddAction C S hS pX' pY' a A hG₁ hH₁ U'
  have ex := conormalLiftAction_existsUnique C S hS pX' pY' a A hG₁ hH₁ U' s
  refine ⟨fun θ₁ θ₂ h => ?_, fun t => ?_⟩
  · obtain ⟨θ, -, hu⟩ := ex (θ₂ +ᵥ s)
    exact (hu θ₁ h).trans (hu θ₂ rfl).symm
  · obtain ⟨θ, hθ, -⟩ := ex t
    exact ⟨θ, hθ⟩

end AlgebraicGeometry.Space

end
