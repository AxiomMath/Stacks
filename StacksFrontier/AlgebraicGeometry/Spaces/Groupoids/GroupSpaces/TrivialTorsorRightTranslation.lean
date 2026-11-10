module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TrivialTorsorUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Right translation of a trivial torsor and the morphisms of `[[X/G]]`

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, acting on an algebraic space `X` over `B`.  A point `x : U ⟶ X` of `X` gives the trivial
torsor with equivariant map `(U, x ≫ X.hom, G_U, h ↦ h · x)` of
`AlgebraicGeometry.Space.trivialTorsorWithMap`, an object of the category `[[X/G]]` of
Situation 04WL.  This file constructs the morphisms: a morphism `f : U ⟶ U'` of the site
together with a section `g : U ⟶ G` carrying `x` to the restriction of `x'` along `f` induces a
morphism `(U, x) ⟶ (U', x')` of `[[X/G]]`, whose morphism of total spaces is the right
translation `(h, u) ↦ (h · g(u)⁻¹, f(u))`.

Right translation is the composite of an isomorphism of `G_U` — right multiplication by the
section `g⁻¹` — with the canonical base change `G_U ⟶ G_{U'}` of
`AlgebraicGeometry.Space.groupBaseChange`.  That factorisation is what makes it cartesian over
`f` and equivariant: both properties hold for each of the two factors.

## Main definitions

* `AlgebraicGeometry.Space.trivialTorsorInvSection` is the section of `G_U` given by `g⁻¹`.
* `AlgebraicGeometry.Space.trivialTorsorRightProduct` is the morphism `G_U ⟶ G`,
  `h ↦ h · g⁻¹`.
* `AlgebraicGeometry.Space.trivialTorsorRightTranslation` is the right translation
  `G_U ⟶ G_{U'}`, `(h, u) ↦ (h · g(u)⁻¹, f(u))`.
* `AlgebraicGeometry.Space.trivialTorsorWithMapHom` is the resulting morphism of `[[X/G]]`.

## Main results

* `AlgebraicGeometry.isModHom_mulRight`: right multiplication by a global section of a group
  object is a morphism of modules for the left translation action.
* `AlgebraicGeometry.Space.isPullback_groupBaseChange` and
  `AlgebraicGeometry.Space.groupBaseChange_mul_left`: the base change `G_U ⟶ G_{U'}` is
  cartesian over `f`, and multiplicative.
* `AlgebraicGeometry.Space.trivialTorsorRightTranslation_isPullback`,
  `AlgebraicGeometry.Space.trivialTorsorRightTranslation_smul` and
  `AlgebraicGeometry.Space.trivialTorsorRightTranslation_comp_trivialTorsorMap`: right
  translation is cartesian over `f`, equivariant, and compatible with the equivariant maps
  `h ↦ h · x`.
* `AlgebraicGeometry.Space.trivialTorsorRightTranslation_id` and
  `AlgebraicGeometry.Space.trivialTorsorRightTranslation_comp`: right translation by the unit
  along the identity is the identity, and right translations compose.

## Implementation notes

The total space of the trivial torsor has two spellings: the slice object
`(pullbackGroup hB G U b).obj.X` carrying the group structure, and the bare fibre product
`CategoryTheory.Limits.pullback G.obj.X.hom b`; likewise a morphism of the site is both
`U ⟶ U'` and `(trivialTorsorObj hB G U b).U ⟶ (trivialTorsorObj hB G U' b').U`.  Each pair
agrees definitionally, but the unfolding chain passes through the choice of limit cone, so the
agreement is invisible at the transparency at which `rw` and `simp only` match — a goal mixing
the two spellings is not even type-correct there, and rewriting in it fails.  Each such
morphism therefore gets a `private` alias whose type is written in the bare fibre-product
spelling, together with the equations characterising its composites with the two projections;
every proof is carried out with those, where rewriting is sound, and the statements below —
elaborated at full transparency, where the spellings do agree — are discharged from the aliased
form by definitional unfolding.

The group-theoretic content is read in the slice `Over B`, where `CategoryTheory.Hom.group`
makes the morphisms into `G` a group and `CategoryTheory.ModObj` makes the morphisms into `X`
a set with an action: `h ↦ h · g⁻¹` is literally `π * (p ≫ g)⁻¹` there, so that
`AlgebraicGeometry.Space.trivialTorsorRightTranslation_id` and
`AlgebraicGeometry.Space.trivialTorsorRightTranslation_comp` are the group laws, and
`AlgebraicGeometry.Space.trivialTorsorRightTranslation_comp_trivialTorsorMap` is the
computation `(π * g⁻¹) · (g · x) = π · x`.

## References

* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Situation 04WL](https://stacks.math.columbia.edu/tag/04WL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe v₁ u₁ u

namespace AlgebraicGeometry

/-- Right multiplication by a global section of a group object is a morphism of modules for the
left translation action of the group object on itself. -/
@[sga "3 IV 5.1.2" "Case X = H"]
theorem isModHom_mulRight {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
    (H : C) [GrpObj H] (g : 𝟙_ C ⟶ H) :
    letI := ModObj.regular H; IsModHom H (GrpObj.mulRight g).hom := by
  let := ModObj.regular H
  constructor
  change μ[H] ≫ _ = H ◁ _ ≫ μ[H]
  have hw (f : H ⟶ H) : H ◁ f =
      CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst H H)
        (CartesianMonoidalCategory.snd H H ≫ f) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [hw]
  simp only [GrpObj.mulRight_hom, CartesianMonoidalCategory.comp_lift_assoc,
    Category.comp_id, CartesianMonoidalCategory.comp_toUnit_assoc]
  conv_lhs =>
    enter [1, 1]
    rw [← Category.id_comp μ[H], ← CartesianMonoidalCategory.lift_fst_snd]
  exact MonObj.lift_lift_assoc _ _ _

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)
  (G : GroupAlgebraicSpace 𝒞 S hS B hB)

variable {U U' U'' : BigFppfOver 𝒞 S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` instance search on presheaves over the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_TrivialTorsorRightTranslation :
    HasPullbacks ((BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_TrivialTorsorRightTranslation
    {X Y Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Aliases in the bare fibre-product spelling -/

/-- The multiplication of `G_U`, read as a morphism of bare fibre products. -/
private def rawMul (b : yoneda.obj U ⟶ B) :
    pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ⟶
      pullback G.obj.X.hom b :=
  (μ[(pullbackGroup hB G U b).obj.X]).left

private theorem rawMul_comp_fst (b : yoneda.obj U ⟶ B) :
    rawMul hB G b ≫ pullback.fst G.obj.X.hom b =
      pullback.lift
        (pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
          pullback.fst G.obj.X.hom b)
        (pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
          pullback.fst G.obj.X.hom b)
        (baseChange_fst_comp_hom_eq b G.obj.X) ≫ (μ[G.obj.X]).left :=
  pullbackGroup_mul_left_comp_fst hB G U b

private theorem rawMul_comp_snd (b : yoneda.obj U ⟶ B) :
    rawMul hB G b ≫ pullback.snd G.obj.X.hom b =
      pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
        pullback.snd G.obj.X.hom b :=
  (μ[(pullbackGroup hB G U b).obj.X]).w

/-- The base change `G_U ⟶ G_{U'}`, read as a morphism of bare fibre products. -/
private def rawBaseChange (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U')
    (hf : yoneda.map f ≫ b' = b) :
    pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b' :=
  groupBaseChange (T := trivialTorsorObj hB G U b) (T' := trivialTorsorObj hB G U' b') f hf

private theorem rawBaseChange_comp_fst (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    rawBaseChange hB G b b' f hf ≫ pullback.fst G.obj.X.hom b' =
      pullback.fst G.obj.X.hom b :=
  groupBaseChange_fst (T := trivialTorsorObj hB G U b)
    (T' := trivialTorsorObj hB G U' b') f hf

private theorem rawBaseChange_comp_snd (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    rawBaseChange hB G b b' f hf ≫ pullback.snd G.obj.X.hom b' =
      pullback.snd G.obj.X.hom b ≫ yoneda.map f :=
  groupBaseChange_snd (T := trivialTorsorObj hB G U b)
    (T' := trivialTorsorObj hB G U' b') f hf

/-- The base change `G_U ×_U G_U ⟶ G_{U'} ×_{U'} G_{U'}` of the action of `G_U` on itself,
read as a morphism of bare fibre products. -/
private def rawActionBaseChange (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U')
    (hf : yoneda.map f ≫ b' = b) (t : pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b')
    (ht : pullback.snd G.obj.X.hom b ≫ yoneda.map f = t ≫ pullback.snd G.obj.X.hom b') :
    pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ⟶
      pullback (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') :=
  actionBaseChange (T := trivialTorsorObj hB G U b) (T' := trivialTorsorObj hB G U' b')
    f hf t ht

private theorem rawActionBaseChange_comp_fst (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b)
    (t : pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b')
    (ht : pullback.snd G.obj.X.hom b ≫ yoneda.map f = t ≫ pullback.snd G.obj.X.hom b') :
    rawActionBaseChange hB G b b' f hf t ht ≫
        pullback.fst (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') =
      pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
        rawBaseChange hB G b b' f hf :=
  actionBaseChange_fst (T := trivialTorsorObj hB G U b)
    (T' := trivialTorsorObj hB G U' b') f hf t ht

private theorem rawActionBaseChange_comp_snd (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b)
    (t : pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b')
    (ht : pullback.snd G.obj.X.hom b ≫ yoneda.map f = t ≫ pullback.snd G.obj.X.hom b') :
    rawActionBaseChange hB G b b' f hf t ht ≫
        pullback.snd (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') =
      pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫ t :=
  actionBaseChange_snd (T := trivialTorsorObj hB G U b)
    (T' := trivialTorsorObj hB G U' b') f hf t ht

/-! ### The base change of the acting group -/

private theorem isPullback_groupBaseChange_raw (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    IsPullback (rawBaseChange hB G b b' f hf) (pullback.snd G.obj.X.hom b)
      (pullback.snd G.obj.X.hom b') (yoneda.map f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst G.obj.X.hom b') ?_
    (rawBaseChange_comp_snd hB G b b' f hf) (IsPullback.of_hasPullback G.obj.X.hom b')
  rw [rawBaseChange_comp_fst, hf]
  exact IsPullback.of_hasPullback G.obj.X.hom b

/-- The base change `G_U ⟶ G_{U'}` of the acting group along a morphism `f : U ⟶ U'` over `B`
exhibits `G_U` as the fibre product `U ×_{f, U'} G_{U'}`. -/
theorem isPullback_groupBaseChange {b : yoneda.obj U ⟶ B} {b' : yoneda.obj U' ⟶ B}
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    IsPullback (groupBaseChange (T := trivialTorsorObj hB G U b)
        (T' := trivialTorsorObj hB G U' b') f hf)
      (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b') (yoneda.map f) :=
  isPullback_groupBaseChange_raw hB G b b' f hf

/-- The multiplication of `G_U = U ×_{b, B} G` is a morphism over `U`: followed by the
projection to `U` it is the first projection of `G_U ×_U G_U` followed by the projection to
`U`. -/
theorem pullbackGroup_mul_left_comp_snd (b : yoneda.obj U ⟶ B) :
    (μ[(pullbackGroup hB G U b).obj.X]).left ≫ pullback.snd G.obj.X.hom b =
      pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
        pullback.snd G.obj.X.hom b :=
  (μ[(pullbackGroup hB G U b).obj.X]).w

private theorem rawActionBaseChange_comp_lift (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    pullback.lift
        (pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
          pullback.fst G.obj.X.hom b)
        (pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
          pullback.fst G.obj.X.hom b)
        (baseChange_fst_comp_hom_eq b G.obj.X) =
      rawActionBaseChange hB G b b' f hf (rawBaseChange hB G b b' f hf)
          (rawBaseChange_comp_snd hB G b b' f hf).symm ≫
        pullback.lift
          (pullback.fst (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') ≫
            pullback.fst G.obj.X.hom b')
          (pullback.snd (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') ≫
            pullback.fst G.obj.X.hom b')
          (baseChange_fst_comp_hom_eq b' G.obj.X) := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
      rawActionBaseChange_comp_fst, Category.assoc, rawBaseChange_comp_fst]
  · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
      rawActionBaseChange_comp_snd, Category.assoc, rawBaseChange_comp_fst]

private theorem rawBaseChange_mul (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    rawMul hB G b ≫ rawBaseChange hB G b b' f hf =
      rawActionBaseChange hB G b b' f hf (rawBaseChange hB G b b' f hf)
          (rawBaseChange_comp_snd hB G b b' f hf).symm ≫ rawMul hB G b' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, rawBaseChange_comp_fst, rawMul_comp_fst, Category.assoc,
      rawMul_comp_fst, ← Category.assoc, ← rawActionBaseChange_comp_lift]
  · rw [Category.assoc, Category.assoc, rawMul_comp_snd,
      reassoc_of% (rawActionBaseChange_comp_fst hB G b b' f hf _ _), rawBaseChange_comp_snd,
      ← Category.assoc, rawMul_comp_snd, Category.assoc]

/-- The base change `G_U ⟶ G_{U'}` is multiplicative: it carries the multiplication of `G_U` to
the multiplication of `G_{U'}` along the induced morphism `G_U ×_U G_U ⟶ G_{U'} ×_{U'} G_{U'}`
of `AlgebraicGeometry.Space.actionBaseChange`. -/
theorem groupBaseChange_mul_left {b : yoneda.obj U ⟶ B} {b' : yoneda.obj U' ⟶ B}
    (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    (μ[(pullbackGroup hB G U b).obj.X]).left ≫
        groupBaseChange (T := trivialTorsorObj hB G U b)
          (T' := trivialTorsorObj hB G U' b') f hf =
      actionBaseChange (T := trivialTorsorObj hB G U b)
          (T' := trivialTorsorObj hB G U' b') f hf
          (groupBaseChange (T := trivialTorsorObj hB G U b)
            (T' := trivialTorsorObj hB G U' b') f hf)
          (isPullback_groupBaseChange hB G f hf).w.symm ≫
        (μ[(pullbackGroup hB G U' b').obj.X]).left :=
  rawBaseChange_mul hB G b b' f hf

/-! ### Right translation -/

/-- The compatibility exhibiting the inverse of a section `g` of `G` over `b` as a section of
`G_U = U ×_{b, B} G` over `U`. -/
theorem trivialTorsorInvSection_condition (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    (g ≫ (ι[G.obj.X]).left) ≫ G.obj.X.hom = 𝟙 (yoneda.obj U) ≫ b := by
  rw [Category.assoc, (ι[G.obj.X]).w, hg, Category.id_comp]

/-- The section of `G_U = U ×_{b, B} G` given by the inverse of a section `g` of `G` over
`b`. -/
def trivialTorsorInvSection (b : yoneda.obj U ⟶ B) (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) :
    𝟙_ (Over (yoneda.obj U)) ⟶ (pullbackGroup hB G U b).obj.X :=
  Over.homMk
    (pullback.lift (g ≫ (ι[G.obj.X]).left) (𝟙 (yoneda.obj U))
      (trivialTorsorInvSection_condition hB G b g hg))
    (pullback.lift_snd (g ≫ (ι[G.obj.X]).left) (𝟙 (yoneda.obj U))
      (trivialTorsorInvSection_condition hB G b g hg))

/-- The section `g⁻¹` of `G_U`, read as a morphism to a bare fibre product. -/
private def rawInvSection (b : yoneda.obj U ⟶ B) (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) : yoneda.obj U ⟶ pullback G.obj.X.hom b :=
  (trivialTorsorInvSection hB G b g hg).left

private theorem rawInvSection_comp_fst (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawInvSection hB G b g hg ≫ pullback.fst G.obj.X.hom b = g ≫ (ι[G.obj.X]).left :=
  pullback.lift_fst (g ≫ (ι[G.obj.X]).left) (𝟙 (yoneda.obj U))
    (trivialTorsorInvSection_condition hB G b g hg)

/-- The compatibility pairing the projection `G_U ⟶ G` with the section `g⁻¹` over `B`. -/
theorem trivialTorsorRightProduct_condition (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    pullback.fst G.obj.X.hom b ≫ G.obj.X.hom =
      (pullback.snd G.obj.X.hom b ≫ g ≫ (ι[G.obj.X]).left) ≫ G.obj.X.hom := by
  rw [Category.assoc, Category.assoc, (ι[G.obj.X]).w, hg]
  exact pullback.condition

/-- The morphism `G_U ⟶ G`, `h ↦ h · g⁻¹`, attached to a section `g` of `G` over `b`. -/
def trivialTorsorRightProduct (b : yoneda.obj U ⟶ B) (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) : pullback G.obj.X.hom b ⟶ G.obj.X.left :=
  pullback.lift (pullback.fst G.obj.X.hom b)
      (pullback.snd G.obj.X.hom b ≫ g ≫ (ι[G.obj.X]).left)
      (trivialTorsorRightProduct_condition hB G b g hg) ≫
    (μ[G.obj.X]).left

private theorem trivialTorsorRightProduct_eq (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b)
    (hc : pullback.fst G.obj.X.hom b ≫ G.obj.X.hom =
      (pullback.snd G.obj.X.hom b ≫ g ≫ (ι[G.obj.X]).left) ≫ G.obj.X.hom) :
    trivialTorsorRightProduct hB G b g hg =
      pullback.lift (pullback.fst G.obj.X.hom b)
          (pullback.snd G.obj.X.hom b ≫ g ≫ (ι[G.obj.X]).left) hc ≫
        (μ[G.obj.X]).left :=
  rfl

/-- The morphism `h ↦ h · g⁻¹` lies over `b`. -/
theorem trivialTorsorRightProduct_comp_hom (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    trivialTorsorRightProduct hB G b g hg ≫ G.obj.X.hom =
      pullback.snd G.obj.X.hom b ≫ b := by
  have hmw : (μ[G.obj.X]).left ≫ G.obj.X.hom =
      pullback.fst G.obj.X.hom G.obj.X.hom ≫ G.obj.X.hom := (μ[G.obj.X]).w
  rw [trivialTorsorRightProduct_eq hB G b g hg (trivialTorsorRightProduct_condition hB G b g hg),
    Category.assoc, hmw, pullback.lift_fst_assoc]
  exact pullback.condition

/-- The right translation `G_U ⟶ G_{U'}`, `(h, u) ↦ (h · g(u)⁻¹, f(u))`, attached to a
morphism `f : U ⟶ U'` over `B` and a section `g` of `G` over `b`. -/
def trivialTorsorRightTranslation (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hb : b = yoneda.map f ≫ b') (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) :
    pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b' :=
  pullback.lift (trivialTorsorRightProduct hB G b g hg)
    (pullback.snd G.obj.X.hom b ≫ yoneda.map f)
    (by rw [trivialTorsorRightProduct_comp_hom hB G b g hg, Category.assoc, ← hb])

private theorem trivialTorsorRightTranslation_comp_fst (b : yoneda.obj U ⟶ B)
    (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    trivialTorsorRightTranslation hB G b b' f hb g hg ≫ pullback.fst G.obj.X.hom b' =
      trivialTorsorRightProduct hB G b g hg :=
  pullback.lift_fst (trivialTorsorRightProduct hB G b g hg)
    (pullback.snd G.obj.X.hom b ≫ yoneda.map f) _

private theorem trivialTorsorRightTranslation_comp_snd (b : yoneda.obj U ⟶ B)
    (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    trivialTorsorRightTranslation hB G b b' f hb g hg ≫ pullback.snd G.obj.X.hom b' =
      pullback.snd G.obj.X.hom b ≫ yoneda.map f :=
  pullback.lift_snd (trivialTorsorRightProduct hB G b g hg)
    (pullback.snd G.obj.X.hom b ≫ yoneda.map f) _

private theorem trivialTorsorRightTranslation_comp_snd_comp (b : yoneda.obj U ⟶ B)
    (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    trivialTorsorRightTranslation hB G b b' f hb g hg ≫
        (pullback.snd G.obj.X.hom b' ≫ b') = pullback.snd G.obj.X.hom b ≫ b := by
  rw [← Category.assoc, trivialTorsorRightTranslation_comp_snd, Category.assoc, ← hb]

/-- Right multiplication by the section `g⁻¹` of `G_U`, read as a morphism of bare fibre
products. -/
private def rawMulRight (b : yoneda.obj U ⟶ B) (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) : pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b :=
  (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom.left

/-- The pairing `(𝟙, g⁻¹)` whose composite with the multiplication is right multiplication by
`g⁻¹`, read as a morphism of bare fibre products. -/
private def rawMulRightLift (b : yoneda.obj U ⟶ B) (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) :
    pullback G.obj.X.hom b ⟶
      pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) :=
  (CartesianMonoidalCategory.lift (𝟙 (pullbackGroup hB G U b).obj.X)
    (CartesianMonoidalCategory.toUnit (pullbackGroup hB G U b).obj.X ≫
      trivialTorsorInvSection hB G b g hg)).left

private theorem rawMulRight_eq (b : yoneda.obj U ⟶ B) (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) :
    rawMulRight hB G b g hg = rawMulRightLift hB G b g hg ≫ rawMul hB G b :=
  rfl

private theorem rawMulRightLift_comp_fst (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawMulRightLift hB G b g hg ≫
        pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) =
      𝟙 (pullback G.obj.X.hom b) :=
  congrArg Over.Hom.left
    (CartesianMonoidalCategory.lift_fst (𝟙 (pullbackGroup hB G U b).obj.X)
      (CartesianMonoidalCategory.toUnit (pullbackGroup hB G U b).obj.X ≫
        trivialTorsorInvSection hB G b g hg))

private theorem rawMulRightLift_comp_snd (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawMulRightLift hB G b g hg ≫
        pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) =
      pullback.snd G.obj.X.hom b ≫ rawInvSection hB G b g hg :=
  congrArg Over.Hom.left
    (CartesianMonoidalCategory.lift_snd (𝟙 (pullbackGroup hB G U b).obj.X)
      (CartesianMonoidalCategory.toUnit (pullbackGroup hB G U b).obj.X ≫
        trivialTorsorInvSection hB G b g hg))

private theorem rawMulRight_comp_snd (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawMulRight hB G b g hg ≫ pullback.snd G.obj.X.hom b = pullback.snd G.obj.X.hom b :=
  (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom.w

private theorem rawMulRight_comp_fst (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawMulRight hB G b g hg ≫ pullback.fst G.obj.X.hom b =
      trivialTorsorRightProduct hB G b g hg := by
  have hc := trivialTorsorRightProduct_condition hB G b g hg
  have key : rawMulRightLift hB G b g hg ≫
        pullback.lift
          (pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
            pullback.fst G.obj.X.hom b)
          (pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
            pullback.fst G.obj.X.hom b)
          (baseChange_fst_comp_hom_eq b G.obj.X) =
      pullback.lift (pullback.fst G.obj.X.hom b)
        (pullback.snd G.obj.X.hom b ≫ g ≫ (ι[G.obj.X]).left) hc := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
        rawMulRightLift_comp_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
        rawMulRightLift_comp_snd, Category.assoc, rawInvSection_comp_fst]
  rw [rawMulRight_eq, Category.assoc, rawMul_comp_fst, ← Category.assoc, key]
  exact (trivialTorsorRightProduct_eq hB G b g hg hc).symm

private theorem trivialTorsorRightTranslation_eq_raw (b : yoneda.obj U ⟶ B)
    (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    trivialTorsorRightTranslation hB G b b' f hb g hg =
      rawMulRight hB G b g hg ≫ rawBaseChange hB G b b' f hb.symm := by
  refine pullback.hom_ext ?_ ?_
  · rw [trivialTorsorRightTranslation_comp_fst, Category.assoc, rawBaseChange_comp_fst,
      rawMulRight_comp_fst]
  · rw [trivialTorsorRightTranslation_comp_snd, Category.assoc, rawBaseChange_comp_snd,
      ← Category.assoc, rawMulRight_comp_snd]

/-- Right translation factors as right multiplication by the section `g⁻¹` of `G_U` followed by
the base change `G_U ⟶ G_{U'}`. -/
theorem trivialTorsorRightTranslation_eq (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hb : b = yoneda.map f ≫ b') (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) :
    trivialTorsorRightTranslation hB G b b' f hb g hg =
      (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom.left ≫
        groupBaseChange (T := trivialTorsorObj hB G U b)
          (T' := trivialTorsorObj hB G U' b') f hb.symm :=
  trivialTorsorRightTranslation_eq_raw hB G b b' f hb g hg

/-- Right translation exhibits `G_U` as the fibre product `U ×_{f, U'} G_{U'}`. -/
theorem trivialTorsorRightTranslation_isPullback (b : yoneda.obj U ⟶ B)
    (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    IsPullback (trivialTorsorRightTranslation hB G b b' f hb g hg)
      (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b') (yoneda.map f) := by
  have : IsIso (rawMulRight hB G b g hg) := by
    change IsIso ((Over.forget (yoneda.obj U)).map
      (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom)
    infer_instance
  have hsq : IsPullback (rawMulRight hB G b g hg) (pullback.snd G.obj.X.hom b)
      (pullback.snd G.obj.X.hom b) (𝟙 (yoneda.obj U)) :=
    IsPullback.of_horiz_isIso
      ⟨(rawMulRight_comp_snd hB G b g hg).trans (Category.comp_id _).symm⟩
  have hp := hsq.paste_horiz (isPullback_groupBaseChange_raw hB G b b' f hb.symm)
  rw [trivialTorsorRightTranslation_eq_raw]
  rwa [Category.id_comp] at hp

/-- The whiskering of right multiplication by `g⁻¹`, read as a morphism of bare fibre
products. -/
private def rawWhiskerMulRight (b : yoneda.obj U ⟶ B) (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) :
    pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ⟶
      pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) :=
  ((pullbackGroup hB G U b).obj.X ◁
    (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom).left

private theorem rawWhiskerMulRight_comp_fst (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawWhiskerMulRight hB G b g hg ≫
        pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) =
      pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) :=
  Over.whiskerLeft_left_fst (R := (pullbackGroup hB G U b).obj.X)
    (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom

private theorem rawWhiskerMulRight_comp_snd (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawWhiskerMulRight hB G b g hg ≫
        pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) =
      pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
        rawMulRight hB G b g hg :=
  Over.whiskerLeft_left_snd (R := (pullbackGroup hB G U b).obj.X)
    (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom

private theorem trivialTorsorRightTranslation_smul_raw (b : yoneda.obj U ⟶ B)
    (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    rawMul hB G b ≫ trivialTorsorRightTranslation hB G b b' f hb g hg =
      rawActionBaseChange hB G b b' f hb.symm
          (trivialTorsorRightTranslation hB G b b' f hb g hg)
          (trivialTorsorRightTranslation_isPullback hB G b b' f hb g hg).w.symm ≫
        rawMul hB G b' := by
  let : ModObj (pullbackGroup hB G U b).obj.X (pullbackGroup hB G U b).obj.X :=
    ModObj.regular (pullbackGroup hB G U b).obj.X
  have hmod : IsModHom (pullbackGroup hB G U b).obj.X
      (GrpObj.mulRight (trivialTorsorInvSection hB G b g hg)).hom :=
    isModHom_mulRight (pullbackGroup hB G U b).obj.X (trivialTorsorInvSection hB G b g hg)
  have he : rawMul hB G b ≫ rawMulRight hB G b g hg =
      rawWhiskerMulRight hB G b g hg ≫ rawMul hB G b :=
    congrArg Over.Hom.left hmod.smul_hom
  have ht : trivialTorsorRightTranslation hB G b b' f hb g hg =
      rawMulRight hB G b g hg ≫ rawBaseChange hB G b b' f hb.symm :=
    trivialTorsorRightTranslation_eq_raw hB G b b' f hb g hg
  have hH : rawWhiskerMulRight hB G b g hg ≫
        rawActionBaseChange hB G b b' f hb.symm (rawBaseChange hB G b b' f hb.symm)
          (rawBaseChange_comp_snd hB G b b' f hb.symm).symm =
      rawActionBaseChange hB G b b' f hb.symm
        (trivialTorsorRightTranslation hB G b b' f hb g hg)
        (trivialTorsorRightTranslation_isPullback hB G b b' f hb g hg).w.symm := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, rawActionBaseChange_comp_fst, rawActionBaseChange_comp_fst,
        ← Category.assoc, rawWhiskerMulRight_comp_fst]
    · rw [Category.assoc, rawActionBaseChange_comp_snd, rawActionBaseChange_comp_snd,
        ← Category.assoc, rawWhiskerMulRight_comp_snd, Category.assoc, ← ht]
  conv_lhs => rw [ht, ← Category.assoc, he, Category.assoc,
    rawBaseChange_mul hB G b b' f hb.symm, ← Category.assoc, hH]

/-- Right translation is equivariant: it carries the action of `G_U` on itself to the action of
`G_{U'}` on itself along the induced morphism `G_U ×_U G_U ⟶ G_{U'} ×_{U'} G_{U'}`. -/
theorem trivialTorsorRightTranslation_smul (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (f : U ⟶ U') (hb : b = yoneda.map f ≫ b') (g : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) :
    (μ[(pullbackGroup hB G U b).obj.X]).left ≫
        trivialTorsorRightTranslation hB G b b' f hb g hg =
      actionBaseChange (T := trivialTorsorObj hB G U b)
          (T' := trivialTorsorObj hB G U' b') f hb.symm
          (trivialTorsorRightTranslation hB G b b' f hb g hg)
          (trivialTorsorRightTranslation_isPullback hB G b b' f hb g hg).w.symm ≫
        (μ[(pullbackGroup hB G U' b').obj.X]).left :=
  trivialTorsorRightTranslation_smul_raw hB G b b' f hb g hg

/-! ### The morphisms of `[[X/G]]` -/

section EquivariantMap

variable (X : Over B) [ModObj G.obj.X X]

/-- If the section `g` of `G` carries the point `x` of `X` to the restriction of the point `x'`
along `f`, then `f` is a morphism from `x ≫ X.hom` to `x' ≫ X.hom` over `B`. -/
theorem trivialTorsorHom_base_compat (x : yoneda.obj U ⟶ X.left) (x' : yoneda.obj U' ⟶ X.left)
    (f : U ⟶ U') (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = x ≫ X.hom)
    (ha : pullback.lift g x hg ≫ (γ[G.obj.X,X]).left = yoneda.map f ≫ x') :
    x ≫ X.hom = yoneda.map f ≫ x' ≫ X.hom := by
  have hgw : (γ[G.obj.X, X]).left ≫ X.hom =
      pullback.fst G.obj.X.hom X.hom ≫ G.obj.X.hom := (γ[G.obj.X, X]).w
  rw [← Category.assoc, ← ha, Category.assoc, hgw, pullback.lift_fst_assoc]
  exact hg.symm

/-- Right translation is compatible with the equivariant maps `h ↦ h · x`: translating and then
applying `h ↦ h · x'` is `h ↦ h · x`. -/
theorem trivialTorsorRightTranslation_comp_trivialTorsorMap
    (x : yoneda.obj U ⟶ X.left) (x' : yoneda.obj U' ⟶ X.left) (f : U ⟶ U')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = x ≫ X.hom)
    (ha : pullback.lift g x hg ≫ (γ[G.obj.X,X]).left = yoneda.map f ≫ x') :
    trivialTorsorRightTranslation hB G (x ≫ X.hom) (x' ≫ X.hom) f
          (trivialTorsorHom_base_compat hB G X x x' f g hg ha) g hg ≫
        trivialTorsorMap hB G X U' x' =
      trivialTorsorMap hB G X U x := by
  have hb := trivialTorsorHom_base_compat hB G X x x' f g hg ha
  let UB : Over B := Over.mk (x ≫ X.hom)
  let PB : Over B := Over.mk (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x ≫ X.hom)
  let p : PB ⟶ UB := Over.homMk (pullback.snd G.obj.X.hom (x ≫ X.hom)) rfl
  let x₀ : UB ⟶ X := Over.homMk x rfl
  let x₁ : UB ⟶ X := Over.homMk (yoneda.map f ≫ x') ((Category.assoc _ _ _).trans hb.symm)
  let g₀ : UB ⟶ G.obj.X := Over.homMk g hg
  let π : PB ⟶ G.obj.X := Over.homMk (pullback.fst G.obj.X.hom (x ≫ X.hom)) pullback.condition
  have hact : g₀ • x₀ = x₁ := Over.OverMorphism.ext ha
  have hact' : p ≫ x₁ = (p ≫ g₀) • (p ≫ x₀) := by rw [← hact, ModObj.comp_smul]
  have hprod : trivialTorsorRightProduct hB G (x ≫ X.hom) g hg = (π * (p ≫ g₀)⁻¹).left := rfl
  have hc' : pullback.fst G.obj.X.hom (x' ≫ X.hom) ≫ G.obj.X.hom =
      (pullback.snd G.obj.X.hom (x' ≫ X.hom) ≫ x') ≫ X.hom := by
    simpa only [Category.assoc] using
      pullback.condition (f := G.obj.X.hom) (g := x' ≫ X.hom)
  have hmap' : trivialTorsorMap hB G X U' x' =
      pullback.lift (pullback.fst G.obj.X.hom (x' ≫ X.hom))
        (pullback.snd G.obj.X.hom (x' ≫ X.hom) ≫ x') hc' ≫ (γ[G.obj.X, X]).left := rfl
  have hRfst : (CartesianMonoidalCategory.lift (π * (p ≫ g₀)⁻¹) (p ≫ x₁)).left ≫
      pullback.fst G.obj.X.hom X.hom = (π * (p ≫ g₀)⁻¹).left :=
    congrArg Over.Hom.left
      (CartesianMonoidalCategory.lift_fst (π * (p ≫ g₀)⁻¹) (p ≫ x₁))
  have hRsnd : (CartesianMonoidalCategory.lift (π * (p ≫ g₀)⁻¹) (p ≫ x₁)).left ≫
      pullback.snd G.obj.X.hom X.hom =
      pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ yoneda.map f ≫ x' :=
    congrArg Over.Hom.left
      (CartesianMonoidalCategory.lift_snd (π * (p ≫ g₀)⁻¹) (p ≫ x₁))
  have hkeyf : (trivialTorsorRightTranslation hB G (x ≫ X.hom) (x' ≫ X.hom) f hb g hg ≫
        pullback.lift (pullback.fst G.obj.X.hom (x' ≫ X.hom))
          (pullback.snd G.obj.X.hom (x' ≫ X.hom) ≫ x') hc') ≫
        pullback.fst G.obj.X.hom X.hom =
      (CartesianMonoidalCategory.lift (π * (p ≫ g₀)⁻¹) (p ≫ x₁)).left ≫
        pullback.fst G.obj.X.hom X.hom := by
    rw [Category.assoc, pullback.lift_fst, trivialTorsorRightTranslation_comp_fst, hprod, hRfst]
  have hkeys : (trivialTorsorRightTranslation hB G (x ≫ X.hom) (x' ≫ X.hom) f hb g hg ≫
        pullback.lift (pullback.fst G.obj.X.hom (x' ≫ X.hom))
          (pullback.snd G.obj.X.hom (x' ≫ X.hom) ≫ x') hc') ≫
        pullback.snd G.obj.X.hom X.hom =
      (CartesianMonoidalCategory.lift (π * (p ≫ g₀)⁻¹) (p ≫ x₁)).left ≫
        pullback.snd G.obj.X.hom X.hom := by
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
      trivialTorsorRightTranslation_comp_snd, Category.assoc, hRsnd]
  have hR : trivialTorsorRightTranslation hB G (x ≫ X.hom) (x' ≫ X.hom) f hb g hg ≫
      trivialTorsorMap hB G X U' x' = ((π * (p ≫ g₀)⁻¹) • (p ≫ x₁)).left := by
    rw [hmap', ← Category.assoc, pullback.hom_ext hkeyf hkeys]
    rfl
  rw [hR, hact', mul_smul, inv_smul_smul]
  rfl

/-- **Stacks 04WM**, the morphisms of the comparison functor.  A morphism `f : U ⟶ U'` of the
big fppf site together with a section `g : U ⟶ G` carrying the point `x` of `X` to the
restriction of the point `x'` along `f` induces a morphism of `[[X/G]]` from the trivial torsor
with equivariant map attached to `x` to the one attached to `x'`, whose morphism of total spaces
is the right translation `(h, u) ↦ (h · g(u)⁻¹, f(u))`. -/
def trivialTorsorWithMapHom (x : yoneda.obj U ⟶ X.left) (x' : yoneda.obj U' ⟶ X.left)
    (f : U ⟶ U') (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = x ≫ X.hom)
    (ha : pullback.lift g x hg ≫ (γ[G.obj.X,X]).left = yoneda.map f ≫ x') :
    trivialTorsorWithMap hB G X U x ⟶ trivialTorsorWithMap hB G X U' x' where
  toHom :=
    { f := f
      comp_b := (trivialTorsorHom_base_compat hB G X x x' f g hg ha).symm
      g := trivialTorsorRightTranslation hB G (x ≫ X.hom) (x' ≫ X.hom) f
        (trivialTorsorHom_base_compat hB G X x x' f g hg ha) g hg
      isPullback := trivialTorsorRightTranslation_isPullback hB G (x ≫ X.hom) (x' ≫ X.hom) f
        (trivialTorsorHom_base_compat hB G X x x' f g hg ha) g hg
      smul_comp := trivialTorsorRightTranslation_smul hB G (x ≫ X.hom) (x' ≫ X.hom) f
        (trivialTorsorHom_base_compat hB G X x x' f g hg ha) g hg }
  comp_map := trivialTorsorRightTranslation_comp_trivialTorsorMap hB G X x x' f g hg ha

end EquivariantMap

/-! ### Functoriality of right translation -/

/-- Right translation by the unit section along the identity is the identity. -/
theorem trivialTorsorRightTranslation_id (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b)
    (hunit : g = b ≫ (η[G.obj.X]).left) :
    trivialTorsorRightTranslation hB G b b (𝟙 U) (by simp) g hg =
      𝟙 (pullback G.obj.X.hom b) := by
  let UB : Over B := Over.mk b
  let PB : Over B := Over.mk (pullback.snd G.obj.X.hom b ≫ b)
  let p : PB ⟶ UB := Over.homMk (pullback.snd G.obj.X.hom b) rfl
  let g₀ : UB ⟶ G.obj.X := Over.homMk g hg
  let π : PB ⟶ G.obj.X := Over.homMk (pullback.fst G.obj.X.hom b) pullback.condition
  have hg₀ : g₀ = 1 := Over.OverMorphism.ext hunit
  have key : π * (p ≫ g₀)⁻¹ = π := by
    rw [hg₀, MonObj.comp_one, inv_one, mul_one]
  refine pullback.hom_ext ?_ ?_
  · rw [trivialTorsorRightTranslation_comp_fst, Category.id_comp]
    exact congrArg Over.Hom.left key
  · rw [trivialTorsorRightTranslation_comp_snd, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id]

/-- Right translation by `(g' ∘ f) · g` along `f ≫ k` is right translation by `g` along `f`
followed by right translation by `g'` along `k`. -/
theorem trivialTorsorRightTranslation_comp (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (b'' : yoneda.obj U'' ⟶ B) (f : U ⟶ U') (k : U' ⟶ U'')
    (hf : b = yoneda.map f ≫ b') (hk : b' = yoneda.map k ≫ b'')
    (g : yoneda.obj U ⟶ G.obj.X.left) (g' : yoneda.obj U' ⟶ G.obj.X.left)
    (gg : yoneda.obj U ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = b) (hg' : g' ≫ G.obj.X.hom = b')
    (hgg : gg ≫ G.obj.X.hom = b)
    (hmul : gg = pullback.lift (yoneda.map f ≫ g') g
      (by rw [Category.assoc, hg', hg, hf]) ≫ (μ[G.obj.X]).left) :
    trivialTorsorRightTranslation hB G b b'' (f ≫ k)
        (by rw [CategoryTheory.Functor.map_comp, Category.assoc, ← hk, ← hf]) gg hgg =
      trivialTorsorRightTranslation hB G b b' f hf g hg ≫
        trivialTorsorRightTranslation hB G b' b'' k hk g' hg' := by
  let UB : Over B := Over.mk b
  let U'B : Over B := Over.mk b'
  let PB : Over B := Over.mk (pullback.snd G.obj.X.hom b ≫ b)
  let P'B : Over B := Over.mk (pullback.snd G.obj.X.hom b' ≫ b')
  let p : PB ⟶ UB := Over.homMk (pullback.snd G.obj.X.hom b) rfl
  let p' : P'B ⟶ U'B := Over.homMk (pullback.snd G.obj.X.hom b') rfl
  let f₀ : UB ⟶ U'B := Over.homMk (yoneda.map f) hf.symm
  let g₀ : UB ⟶ G.obj.X := Over.homMk g hg
  let g₁ : U'B ⟶ G.obj.X := Over.homMk g' hg'
  let g₂ : UB ⟶ G.obj.X := Over.homMk gg hgg
  let π : PB ⟶ G.obj.X := Over.homMk (pullback.fst G.obj.X.hom b) pullback.condition
  let π' : P'B ⟶ G.obj.X := Over.homMk (pullback.fst G.obj.X.hom b') pullback.condition
  let R₀ : PB ⟶ P'B := Over.homMk (trivialTorsorRightTranslation hB G b b' f hf g hg)
    (trivialTorsorRightTranslation_comp_snd_comp hB G b b' f hf g hg)
  have hπ : R₀ ≫ π' = π * (p ≫ g₀)⁻¹ :=
    Over.OverMorphism.ext (trivialTorsorRightTranslation_comp_fst hB G b b' f hf g hg)
  have hp : R₀ ≫ p' = p ≫ f₀ :=
    Over.OverMorphism.ext (trivialTorsorRightTranslation_comp_snd hB G b b' f hf g hg)
  have hmul' : g₂ = (f₀ ≫ g₁) * g₀ := Over.OverMorphism.ext hmul
  have key : π * (p ≫ g₂)⁻¹ = R₀ ≫ (π' * (p' ≫ g₁)⁻¹) := by
    rw [hmul', MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hπ,
      ← Category.assoc R₀ p', hp, Category.assoc p f₀]
    group
  refine pullback.hom_ext ?_ ?_
  · rw [trivialTorsorRightTranslation_comp_fst, Category.assoc,
      trivialTorsorRightTranslation_comp_fst]
    exact congrArg Over.Hom.left key
  · rw [trivialTorsorRightTranslation_comp_snd, Category.assoc,
      trivialTorsorRightTranslation_comp_snd, ← Category.assoc,
      trivialTorsorRightTranslation_comp_snd, Category.assoc,
      ← CategoryTheory.Functor.map_comp]

end AlgebraicGeometry.Space

end
