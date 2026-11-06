module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsWithEquivariantMap

/-!
# The trivial torsor with equivariant map attached to a point

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, acting on an algebraic space `X` over `B`.  A point `x : U ⟶ X` of `X` over an object `U`
of the big fppf site determines an object of the category `[[X/G]]` of Situation 04WL: the
*trivial* torsor `G_U = U ×_{b, B} G` over `U`, where `b = x ≫ X.hom` is the induced morphism
`U ⟶ B`, equipped with its left translation action, together with the `G`-equivariant morphism
`G_U ⟶ X`, `h ↦ h · x`.

## Main definitions

* `AlgebraicGeometry.Space.trivialTorsorObj` is the trivial fppf torsor over `U` under
  `G_U = U ×_{b, B} G`: the group algebraic space `G_U` acting on itself by left translation.
* `AlgebraicGeometry.Space.trivialTorsorMap` is the morphism `G_U ⟶ X`, `h ↦ h · x`.
* `AlgebraicGeometry.Space.trivialTorsorWithMap` is the resulting object of `[[X/G]]`, the
  quadruple `(U, x ≫ X.hom, G_U, h ↦ h · x)`.

## Main results

* `AlgebraicGeometry.isPseudoTorsor_regular`: the left translation action of a group object on
  itself is a pseudo-torsor.
* `AlgebraicGeometry.Space.pullbackGroup_mul_left_comp_fst`: the projection `G_U ⟶ G` is
  multiplicative, that is it carries the multiplication of `G_U` to the multiplication of `G`.
* `AlgebraicGeometry.Space.trivialTorsorMap_over` and
  `AlgebraicGeometry.Space.trivialTorsorMap_smul`: the morphism `h ↦ h · x` lies over `b` and
  is `G`-equivariant.

## Implementation notes

The group algebraic space `G_U` is the base change of `G` along `b`, so its multiplication is
the one transported by the monoidal pullback functor `CategoryTheory.Over.pullback b`.  The
only computation needed about that transported multiplication is its composite with the
projection `G_U ⟶ G`, which is `AlgebraicGeometry.Space.pullbackGroup_mul_left_comp_fst`; it
follows from the projection formulas for the monoidal structure morphism of
`CategoryTheory.Over.pullback` and says precisely that the projection is multiplicative.

Granted that, equivariance of `h ↦ h · x` is the associativity law of the action, read on the
morphisms out of `G_U ×_U G_U` viewed as an object over `B`: the point `h ↦ h · x` of `X` is
`π • x` for the projection `π : G_U ⟶ G`, so the two sides of the equivariance square are
`(π₁ * π₂) • x` and `π₁ • (π₂ • x)`, where `π₁` and `π₂` are the two projections of
`G_U ×_U G_U` followed by `π`.  Multiplicativity of `π` identifies the first with the image of
the multiplication of `G_U`, and `mul_smul` for the induced action on morphisms finishes the
proof.

Triviality of the torsor `G_U` is witnessed by the identity covering of `U` together with the
unit section of `G_U`, and the pseudo-torsor condition is the general statement that left
translation of a group object on itself is simply transitive on morphisms into it.

## References

* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Situation 04WL](https://stacks.math.columbia.edu/tag/04WL)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe v₁ u₁ u

namespace AlgebraicGeometry

/-- The left translation action of a group object on itself is a pseudo-torsor: the group
element carrying one morphism into it to another exists and is unique, namely `y * x⁻¹`. -/
@[sga "3 IV 5.1.0" "more general"]
theorem isPseudoTorsor_regular {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
    (H : C) [GrpObj H] :
    @IsPseudoTorsor C _ _ H H _ (ModObj.regular H) := by
  let _ : ModObj H H := ModObj.regular H
  refine ModObj.isIso_leftSMul_iff.mpr fun T a c => ?_
  let _ : Group (T ⟶ H) := CategoryTheory.Hom.group
  refine ⟨c * a⁻¹, ?_, ?_⟩
  · show c * a⁻¹ * a = c
    group
  · intro z hz
    change z * a = c at hz
    rw [← hz]
    group

namespace Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)
  (G : GroupAlgebraicSpace 𝒞 S hS B hB)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_TrivialTorsorWithMap :
    HasPullbacks ((BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_TrivialTorsorWithMap
    {X Y Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The lax monoidal structure of base change along a morphism into `B` (instance search times
out without this shortcut). -/
local instance (priority := high) overPullbackLaxMonoidal_TrivialTorsorWithMap
    {Y : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (b : Y ⟶ B) : (Over.pullback b).LaxMonoidal :=
  inferInstance

/-! ### The projection from a base change of a group algebraic space -/

/-- The two projections of `R_Y ×_Y R_Y` to `R`, where `R_Y = Y ×_{b, B} R` is a base change of
an object `R` over `B`, agree after composition with the structure morphism of `R`.  This is
the compatibility that pairs them into a single morphism to `R ×_B R`. -/
theorem baseChange_fst_comp_hom_eq {Y : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (b : Y ⟶ B)
    (R : Over B) :
    (pullback.fst (pullback.snd R.hom b) (pullback.snd R.hom b) ≫
        pullback.fst R.hom b) ≫ R.hom =
      (pullback.snd (pullback.snd R.hom b) (pullback.snd R.hom b) ≫
        pullback.fst R.hom b) ≫ R.hom := by
  rw [Category.assoc, Category.assoc, pullback.condition (f := R.hom) (g := b),
    ← Category.assoc, ← Category.assoc, pullback.condition]

/-- A morphism `m : R ×_B R ⟶ R` over `B`, transported to the base change along `b` and
composed with the projection to `R`, is the pair of projections of `R_Y ×_Y R_Y` followed by
`m`. -/
private theorem laxMonoidalMu_map_left_comp_fst
    {Y : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (b : Y ⟶ B) (R : Over B) (m : R ⊗ R ⟶ R) :
    (Functor.LaxMonoidal.μ (Over.pullback b) R R ≫ (Over.pullback b).map m).left ≫
        pullback.fst R.hom b =
      pullback.lift
        (pullback.fst (pullback.snd R.hom b) (pullback.snd R.hom b) ≫ pullback.fst R.hom b)
        (pullback.snd (pullback.snd R.hom b) (pullback.snd R.hom b) ≫ pullback.fst R.hom b)
        (baseChange_fst_comp_hom_eq b R) ≫ m.left := by
  have hmap : ((Over.pullback b).map m).left ≫ pullback.fst R.hom b =
      pullback.fst (R ⊗ R).hom b ≫ m.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hfst : (Functor.LaxMonoidal.μ (Over.pullback b) R R).left ≫
      pullback.fst (R ⊗ R).hom b =
      pullback.lift
        (pullback.fst (pullback.snd R.hom b) (pullback.snd R.hom b) ≫ pullback.fst R.hom b)
        (pullback.snd (pullback.snd R.hom b) (pullback.snd R.hom b) ≫ pullback.fst R.hom b)
        (baseChange_fst_comp_hom_eq b R) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact Over.μ_pullback_left_fst_fst R R
    · rw [Category.assoc, pullback.lift_snd]
      exact Over.μ_pullback_left_fst_snd R R
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hfst]

/-- The projection `G_U ⟶ G` of the base change `G_U = U ×_{b, B} G` is multiplicative: the
multiplication of `G_U` followed by the projection is the pair of projections followed by the
multiplication of `G`. -/
theorem pullbackGroup_mul_left_comp_fst (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    (μ[(pullbackGroup hB G U b).obj.X]).left ≫ pullback.fst G.obj.X.hom b =
      pullback.lift
        (pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
          pullback.fst G.obj.X.hom b)
        (pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫
          pullback.fst G.obj.X.hom b)
        (baseChange_fst_comp_hom_eq b G.obj.X) ≫ (μ[G.obj.X]).left :=
  laxMonoidalMu_map_left_comp_fst b G.obj.X (μ[G.obj.X])

/-! ### The trivial torsor -/

/-- The base change `G_U = U ×_{b, B} G`, acting on itself by left translation, is an fppf
torsor over `U`: it is a pseudo-torsor, and it has a section over the identity covering of
`U`, namely its unit. -/
theorem isFppfTorsor_regular_pullbackGroup (U : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ B) :
    @IsFppfTorsor 𝒞 S hS (yoneda.obj U) (isAlgebraicSpace_yoneda 𝒞 S hS U)
      (pullbackGroup hB G U b).obj.X (pullbackGroup hB G U b).obj.X _
      (ModObj.regular (pullbackGroup hB G U b).obj.X)
      (pullbackGroup hB G U b).property (pullbackGroup hB G U b).property :=
  ⟨isPseudoTorsor_regular (pullbackGroup hB G U b).obj.X, PUnit.{u + 2},
    fun _ => yoneda.obj U, fun _ => 𝟙 (yoneda.obj U),
    fun _ => isAlgebraicSpace_yoneda 𝒞 S hS U,
    isFppfCovering_of_isIso 𝒞 S hS (yoneda.obj U) (yoneda.obj U) (𝟙 (yoneda.obj U))
      (isAlgebraicSpace_yoneda 𝒞 S hS U),
    fun _ => ⟨η[(pullbackGroup hB G U b).obj.X] ≫
      (Over.pullbackId (X := yoneda.obj U)).inv.app (pullbackGroup hB G U b).obj.X⟩⟩

/-- The trivial fppf torsor over an object `U` of the big fppf site equipped with a morphism
`b : U ⟶ B`: the group algebraic space `G_U = U ×_{b, B} G` acting on itself by left
translation. -/
def trivialTorsorObj (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) : TorsorObj hB G where
  U := U
  b := b
  total := (pullbackGroup hB G U b).obj.X
  isAlgebraicSpace := (pullbackGroup hB G U b).property
  action := ModObj.regular (pullbackGroup hB G U b).obj.X
  isFppfTorsor := isFppfTorsor_regular_pullbackGroup hB G U b

/-! ### The equivariant map `h ↦ h · x` -/

section EquivariantMap

variable (X : Over B) [ModObj G.obj.X X]

/-- The morphism `G_U ⟶ X`, `h ↦ h · x`, attached to a point `x : U ⟶ X` of `X`, where
`G_U = U ×_{b, B} G` for `b = x ≫ X.hom`: the projection to `G` paired with the point `x`,
followed by the action of `G` on `X`. -/
def trivialTorsorMap (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    pullback G.obj.X.hom (x ≫ X.hom) ⟶ X.left :=
  pullback.lift (pullback.fst G.obj.X.hom (x ≫ X.hom))
      (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x)
      (by
        simpa only [Category.assoc] using
          pullback.condition (f := G.obj.X.hom) (g := x ≫ X.hom)) ≫
    (γ[G.obj.X, X]).left

/-- The morphism `h ↦ h · x` lies over `b = x ≫ X.hom`. -/
theorem trivialTorsorMap_over (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    trivialTorsorMap hB G X U x ≫ X.hom =
      pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x ≫ X.hom := by
  rw [trivialTorsorMap, Category.assoc, (γ[G.obj.X, X]).w]
  show pullback.lift (pullback.fst G.obj.X.hom (x ≫ X.hom))
      (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x) _ ≫
      pullback.fst G.obj.X.hom X.hom ≫ G.obj.X.hom = _
  rw [← Category.assoc, pullback.lift_fst, pullback.condition]

/-- The projection of `G_U ×_U G_U` to `G` and its second projection followed by `h ↦ h · x`
agree over `B`.  This is the compatibility that pairs them into the morphism
`G_U ×_U G_U ⟶ G ×_B X` against which equivariance is expressed. -/
theorem trivialTorsorMap_pair_condition (U : BigFppfOver 𝒞 S hS)
    (x : yoneda.obj U ⟶ X.left) :
    (pullback.fst (pullback.snd G.obj.X.hom (x ≫ X.hom))
          (pullback.snd G.obj.X.hom (x ≫ X.hom)) ≫
        pullback.fst G.obj.X.hom (x ≫ X.hom)) ≫ G.obj.X.hom =
      (pullback.snd (pullback.snd G.obj.X.hom (x ≫ X.hom))
          (pullback.snd G.obj.X.hom (x ≫ X.hom)) ≫
        trivialTorsorMap hB G X U x) ≫ X.hom := by
  rw [Category.assoc, Category.assoc, trivialTorsorMap_over,
    pullback.condition (f := G.obj.X.hom) (g := x ≫ X.hom), ← Category.assoc,
    pullback.condition (f := pullback.snd G.obj.X.hom (x ≫ X.hom))
      (g := pullback.snd G.obj.X.hom (x ≫ X.hom)),
    Category.assoc]

/-- The morphism `h ↦ h · x` is `G`-equivariant: acting by `G_U` and then applying it agrees
with applying it and then acting by `G` through the projection `G_U ⟶ G`. -/
theorem trivialTorsorMap_smul (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    (μ[(pullbackGroup hB G U (x ≫ X.hom)).obj.X]).left ≫ trivialTorsorMap hB G X U x =
      pullback.lift
        (pullback.fst (pullback.snd G.obj.X.hom (x ≫ X.hom))
            (pullback.snd G.obj.X.hom (x ≫ X.hom)) ≫
          pullback.fst G.obj.X.hom (x ≫ X.hom))
        (pullback.snd (pullback.snd G.obj.X.hom (x ≫ X.hom))
            (pullback.snd G.obj.X.hom (x ≫ X.hom)) ≫ trivialTorsorMap hB G X U x)
        (trivialTorsorMap_pair_condition hB G X U x) ≫ (γ[G.obj.X, X]).left := by
  set P := (pullbackGroup hB G U (x ≫ X.hom)).obj.X
  let PB : Over B := (Over.map (x ≫ X.hom)).obj P
  let proj : PB ⟶ G.obj.X :=
    Over.homMk (pullback.fst G.obj.X.hom (x ≫ X.hom)) pullback.condition
  let point : PB ⟶ X :=
    Over.homMk (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x) (Category.assoc _ _ _)
  let mulHom := (Over.map (x ≫ X.hom)).map (μ[P])
  let fstHom := (Over.map (x ≫ X.hom)).map (CartesianMonoidalCategory.fst P P)
  let sndHom := (Over.map (x ≫ X.hom)).map (CartesianMonoidalCategory.snd P P)
  have hmul : mulHom ≫ proj = (fstHom ≫ proj) * (sndHom ≫ proj) :=
    Over.OverMorphism.ext (pullbackGroup_mul_left_comp_fst hB G U (x ≫ X.hom))
  have hpoint : mulHom ≫ point = sndHom ≫ point := Over.OverMorphism.ext (by
    change (μ[P]).left ≫ P.hom ≫ x = (CartesianMonoidalCategory.snd P P).left ≫ P.hom ≫ x
    rw [← Category.assoc, Over.w, ← Category.assoc, Over.w])
  have key : mulHom ≫ (proj • point) = (fstHom ≫ proj) • (sndHom ≫ (proj • point)) := by
    rw [ModObj.comp_smul, hmul, hpoint, mul_smul, ModObj.comp_smul]
  exact congrArg Over.Hom.left key

/-- **Stacks 04WM**, the trivial torsor with its equivariant map.  The object of the category
`[[X/G]]` of Situation 04WL attached to a point `x : U ⟶ X` of `X`: the trivial torsor
`G_U = U ×_{b, B} G` over `U`, for `b = x ≫ X.hom`, with its left translation action, together
with the `G`-equivariant morphism `G_U ⟶ X`, `h ↦ h · x`. -/
@[stacks 04WM "the trivial torsor with equivariant map attached to a point of X"]
def trivialTorsorWithMap (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    TorsorWithMap hB G X where
  toTorsorObj := trivialTorsorObj hB G U (x ≫ X.hom)
  map := trivialTorsorMap hB G X U x
  map_over := trivialTorsorMap_over hB G X U x
  smul_map := trivialTorsorMap_smul hB G X U x

/-- The object of `[[X/G]]` attached to a point `x : U ⟶ X` is the quadruple the source
describes: its base is `U`, its morphism to `B` is `x ≫ X.hom`, its total space is the base
change `U ×_{x ≫ X.hom, B} G` with its left translation action, and its equivariant morphism
is the projection to `G` paired with `x`, followed by the action of `G` on `X`. -/
example (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    { A : AlgebraicGeometry.Space.TorsorWithMap hB G X //
        A.toTorsorObj.U = U ∧
        HEq A.toTorsorObj.b (x ≫ X.hom) ∧
        HEq A.toTorsorObj.total
          (AlgebraicGeometry.Space.pullbackGroup hB G U (x ≫ X.hom)).obj.X ∧
        HEq A.toTorsorObj.action
          (CategoryTheory.ModObj.regular
            (AlgebraicGeometry.Space.pullbackGroup hB G U (x ≫ X.hom)).obj.X) ∧
        HEq A.map
          (CategoryTheory.Limits.pullback.lift
              (CategoryTheory.Limits.pullback.fst G.obj.X.hom (x ≫ X.hom))
              (CategoryTheory.Limits.pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x)
              (by
                simpa only [Category.assoc] using
                  CategoryTheory.Limits.pullback.condition
                    (f := G.obj.X.hom) (g := x ≫ X.hom)) ≫
            (γ[G.obj.X, X]).left) } :=
  ⟨AlgebraicGeometry.Space.trivialTorsorWithMap hB G X U x, rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    HEq.rfl⟩

end EquivariantMap

end Space

end AlgebraicGeometry

end
