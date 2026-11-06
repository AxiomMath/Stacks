module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.FiniteTypeEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveFiniteTypeCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheavesEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
import StacksCore.Tactic.StacksAttribute

/-!
# Effective descent for finite-type algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `p_ft` be the projection from
algebraic spaces of finite type over varying schemes to the big fppf site of `S`. Every descent
datum for `p_ft` relative to an fppf covering sieve is effective; this is condition (3) of
Stacks 04UD, whose conditions (1) and (2) are
`AlgebraicGeometry.finiteTypeSpacesProjection_isFibered` and
`AlgebraicGeometry.finiteTypeSpacesProjection_isMorSheaf`.

The structure morphism of an object of a fibre of `p_ft` is a morphism of presheaves
(`AlgebraicGeometry.FiniteTypeSpacesDescent.fibreStructure`) to the representable presheaf of the
base, and it forms fibre product squares with the chosen cartesian lifts.

## Main definitions

* `AlgebraicGeometry.FiniteTypeSpacesDescent.fibreStructure`: the structure morphism of an object
  of a fibre of `p_ft`, as a morphism of presheaves.

## Main results

* `AlgebraicGeometry.finiteTypeSpacesProjection_hasEffectiveDescent`: every descent datum of
  finite-type algebraic spaces relative to an fppf covering sieve is effective.
* `AlgebraicGeometry.FiniteTypeSpacesDescent.isPullback_pullbackMap`: the square of presheaves of
  a chosen pullback is a fibre product.

## References

* [Stacks Project, Tag 04UD](https://stacks.math.columbia.edu/tag/04UD)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion


namespace AlgebraicGeometry

universe u

namespace FiniteTypeSpacesDescent

attribute [local instance] finiteTypeSpacesProjection_isFibered

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying presheaf of a finite-type algebraic space over a varying scheme. -/
def toPresheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    FiniteTypeSpaces B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (isFiniteTypeSpace B S hS).ι ⋙ Comma.fst _ _ ⋙ ObjectProperty.ι _

/-- `toPresheaf` sends a morphism `φ` of finite-type algebraic spaces to the underlying morphism
of presheaves of `φ`. -/
theorem toPresheaf_map {a b : FiniteTypeSpaces B S hS} (φ : a ⟶ b) :
    (toPresheaf B S hS).map φ = φ.hom.left.hom :=
  rfl

/-- The structure morphism of an object of the fibre over `V` of the projection from finite-type
algebraic spaces, as a morphism of presheaves to the representable presheaf of `V`. -/
def fibreStructure {V : BigFppfOver B S hS} (x : (finiteTypeSpacesProjection B S hS).Fiber V) :
    (toPresheaf B S hS).obj x.1 ⟶ yoneda.obj V :=
  x.1.obj.hom ≫ yoneda.map (eqToHom x.2)

/-- A morphism of finite-type algebraic spaces lying over `g` has base morphism `g`. -/
private theorem right_eq_of_isHomLift {a b : FiniteTypeSpaces B S hS}
    (g : (finiteTypeSpacesProjection B S hS).obj a ⟶ (finiteTypeSpacesProjection B S hS).obj b)
    (φ : a ⟶ b) [(finiteTypeSpacesProjection B S hS).IsHomLift g φ] : φ.hom.right = g := by
  simpa using IsHomLift.fac' (finiteTypeSpacesProjection B S hS) g φ

/-- A morphism of finite-type algebraic spaces over varying schemes lying over `g` commutes with
the structure morphisms, read through the identifications of the bases with `V` and `W`. -/
@[reassoc]
theorem hom_comp_structure {a b : FiniteTypeSpaces B S hS} {V W : BigFppfOver B S hS}
    (g : V ⟶ W) (φ : a ⟶ b) [(finiteTypeSpacesProjection B S hS).IsHomLift g φ]
    (ha : (finiteTypeSpacesProjection B S hS).obj a = V)
    (hb : (finiteTypeSpacesProjection B S hS).obj b = W) :
    φ.hom.left.hom ≫ b.obj.hom ≫ yoneda.map (eqToHom hb) =
      (a.obj.hom ≫ yoneda.map (eqToHom ha)) ≫ yoneda.map g := by
  subst ha hb
  obtain rfl := right_eq_of_isHomLift g φ
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  exact φ.hom.w

/-- A cartesian morphism of finite-type algebraic spaces over varying schemes is a fibre product
square of presheaves (Stacks 04U9), read through the identifications of the bases with `V` and
`W`. -/
theorem isPullback_of_isCartesian {a b : FiniteTypeSpaces B S hS} {V W : BigFppfOver B S hS}
    (g : V ⟶ W) (φ : a ⟶ b) [hφ : (finiteTypeSpacesProjection B S hS).IsCartesian g φ]
    (ha : (finiteTypeSpacesProjection B S hS).obj a = V)
    (hb : (finiteTypeSpacesProjection B S hS).obj b = W) :
    IsPullback φ.hom.left.hom (a.obj.hom ≫ yoneda.map (eqToHom ha))
      (b.obj.hom ≫ yoneda.map (eqToHom hb)) (yoneda.map g) := by
  have := spacesProjection_isFibered B S hS
  subst ha hb
  obtain rfl := right_eq_of_isHomLift g φ
  simp only [eqToHom_refl]
  have hc : (spacesProjection B S hS).IsCartesian φ.hom.right φ.hom :=
    Functor.isCartesian_map_ι (spacesProjection B S hS) (isFiniteTypeSpace B S hS)
      (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS) _ φ hφ
  exact (isPullback_hom_of_isStronglyCartesian B S hS φ.hom inferInstance).flip

/-- Conversely, a morphism of finite-type algebraic spaces over varying schemes whose square of
presheaves is a fibre product is cartesian (Stacks 04U9). -/
theorem isCartesian_of_isPullback {a b : FiniteTypeSpaces B S hS} (φ : a ⟶ b)
    (h : IsPullback φ.hom.left.hom a.obj.hom b.obj.hom (yoneda.map φ.hom.right)) :
    (finiteTypeSpacesProjection B S hS).IsCartesian φ.hom.right φ := by
  have := spacesProjection_isFibered B S hS
  have hlift : IsIso (pullback.lift a.obj.hom φ.hom.left.hom φ.hom.w.symm :
      a.obj.left.obj ⟶ pullback (yoneda.map φ.hom.right) b.obj.hom) := by
    have he : h.flip.isoPullback.hom = pullback.lift a.obj.hom φ.hom.left.hom φ.hom.w.symm := by
      apply pullback.hom_ext
      · rw [IsPullback.isoPullback_hom_fst]
        exact (pullback.lift_fst _ _ _).symm
      · rw [IsPullback.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).symm
    rw [← he]
    infer_instance
  have hiso : IsIso (ObjectProperty.homMk (pullback.lift a.obj.hom φ.hom.left.hom φ.hom.w.symm) :
      a.obj.left ⟶ AlgebraicSpaces.fiberProduct B S hS
        (schemeSpaceMap φ.hom.right) (ObjectProperty.homMk b.obj.hom)) := by
    have : IsIso ((ObjectProperty.ι _).map
        (ObjectProperty.homMk (pullback.lift a.obj.hom φ.hom.left.hom φ.hom.w.symm) :
          a.obj.left ⟶ AlgebraicSpaces.fiberProduct B S hS
            (schemeSpaceMap φ.hom.right) (ObjectProperty.homMk b.obj.hom))) := hlift
    exact isIso_of_fully_faithful (ObjectProperty.ι _) _
  have hs := (spacesProjection_isStronglyCartesian_iff φ.hom).2 hiso
  exact Functor.isCartesian_of_isCartesian_map_ι (spacesProjection B S hS)
    (isFiniteTypeSpace B S hS) _ φ
    (inferInstance : (spacesProjection B S hS).IsCartesian φ.hom.right φ.hom)

/-- A morphism of fibres lying over `g` commutes with the structure morphisms of
`fibreStructure`. -/
@[reassoc]
theorem map_comp_fibreStructure {V W : BigFppfOver B S hS}
    {x : (finiteTypeSpacesProjection B S hS).Fiber V}
    {y : (finiteTypeSpacesProjection B S hS).Fiber W} (g : V ⟶ W) (φ : x.1 ⟶ y.1)
    [(finiteTypeSpacesProjection B S hS).IsHomLift g φ] :
    (toPresheaf B S hS).map φ ≫ fibreStructure y = fibreStructure x ≫ yoneda.map g :=
  hom_comp_structure g φ x.2 y.2

/-- A morphism of one fibre commutes with the structure morphisms of `fibreStructure`. -/
@[reassoc (attr := simp)]
theorem fiberInclusion_map_comp_fibreStructure {V : BigFppfOver B S hS}
    {x y : (finiteTypeSpacesProjection B S hS).Fiber V} (m : x ⟶ y) :
    (toPresheaf B S hS).map (Functor.Fiber.fiberInclusion.map m) ≫ fibreStructure y =
      fibreStructure x := by
  have : (finiteTypeSpacesProjection B S hS).IsHomLift (𝟙 V)
      (Functor.Fiber.fiberInclusion.map m) := m.2
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
    map_comp_fibreStructure (𝟙 V) (Functor.Fiber.fiberInclusion.map m)

/-- The chosen cartesian lift of `g` at `x` is a fibre product square of presheaves. -/
theorem isPullback_pullbackMap {V W : BigFppfOver B S hS}
    (x : (finiteTypeSpacesProjection B S hS).Fiber V) (g : W ⟶ V) :
    IsPullback ((toPresheaf B S hS).map (Functor.IsPreFibered.pullbackMap x.2 g))
      (fibreStructure (Functor.pullbackFiber _ x g)) (fibreStructure x) (yoneda.map g) := by
  have := Functor.IsPreFibered.pullbackMap.IsCartesian x.2 g
  exact isPullback_of_isCartesian g _ _ _

/-- The chosen cartesian lift of `g` commutes with the structure morphisms. -/
@[reassoc (attr := simp)]
theorem pullbackMap_comp_fibreStructure {V W : BigFppfOver B S hS}
    (x : (finiteTypeSpacesProjection B S hS).Fiber V) (g : W ⟶ V) :
    (toPresheaf B S hS).map (Functor.IsPreFibered.pullbackMap x.2 g) ≫ fibreStructure x =
      fibreStructure (Functor.pullbackFiber _ x g) ≫ yoneda.map g :=
  (isPullback_pullbackMap x g).w

/-- The fibre product square of representable presheaves over a fibre product of schemes. -/
theorem isPullback_yoneda {V W U : BigFppfOver B S hS} (f : V ⟶ U) (g : W ⟶ U) :
    IsPullback (yoneda.map (pullback.fst f g)) (yoneda.map (pullback.snd f g)) (yoneda.map f)
      (yoneda.map g) :=
  (IsPullback.of_hasPullback f g).map yoneda

/-- The structure morphism of `x`, regarded as an object of the fibre over its own base, is
`x.obj.hom`. -/
theorem fibreStructure_mk (x : FiniteTypeSpaces B S hS) :
    fibreStructure (⟨x, rfl⟩ : (finiteTypeSpacesProjection B S hS).Fiber _) = x.obj.hom := by
  simp only [fibreStructure, eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.comp_id _


end FiniteTypeSpacesDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every descent datum of finite-type algebraic spaces relative to an fppf covering sieve of the
big fppf site of `S` is effective. -/
@[stacks 04UD "condition (3)"]
theorem finiteTypeSpacesProjection_hasEffectiveDescent :
    haveI : (finiteTypeSpacesProjection B S hS).IsFibered :=
      finiteTypeSpacesProjection_isFibered B S hS
    (finiteTypeSpacesProjection B S hS).HasEffectiveDescent (BigFppfOver.topology B S hS) :=
  (finiteTypeSpacesProjection_isStack_of_bootstrap B S hS).hasEffectiveDescent

end AlgebraicGeometry

end
