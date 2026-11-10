module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Basic

/-!
# Versality of an object at a point

Let `𝓧` be a category fibred in groupoids over a scheme `U`, and let `x` be an object of
`𝓧` lying over `U`. By the 2-Yoneda lemma `x` corresponds to a morphism from the category
of schemes over `U` to `𝓧`, and at a field-valued point `u₀` of `U` this morphism induces a
morphism `\hat x` of predeformation categories over the category of Artinian local algebras.
The object `x` is *versal at* `u₀` exactly when `\hat x` is smooth.

The point used is the canonical spectrum of the residue field of `u₀`, and the deformation
base is the local ring of `S` at the image of that point.

## Main definitions

* `Deformation.Artin.residueFieldPoint` — the canonical residue-field point of a scheme over
  `S`, regarded as an object of the slice over `U`.
* `Deformation.Artin.basePoint` — the point of `S` at which the deformation base is
  localized, and `Deformation.Artin.residueFieldAlgebra` the resulting algebra structure on
  the residue field.
* `Deformation.Artin.IsVersalAt` — versality of an object at a field-valued point.
* `Deformation.Artin.HatXConstruction` — a 2-Yoneda representative of an object over `U`, its
  pullback at the chosen point, and the induced map on predeformation categories.

## Main results

* `Deformation.Artin.residueFieldPoint_base_eq` — the canonical residue-field point factors
  through the local ring of its image in `S`.
* `Deformation.Artin.hatX` — construction of the morphism `\hat x` of predeformation
  categories.

## Implementation notes

`IsVersalAt` writes out the lifting property defining smoothness of `\hat x`: for a
surjection `B ⟶ A` of Artinian local algebras, an arrow `y ⟶ z` over `Spec A ⟶ Spec B`
together with an arrow `y ⟶ x` restricting to `u₀` must extend to an arrow `z ⟶ x` making
the triangle commute.

## References

* [Stacks Project, Tag 07XE](https://stacks.math.columbia.edu/tag/07XE)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
-/

@[expose] public section

namespace Deformation.Artin

/-! ### Versality at a field-valued point -/

noncomputable section
open AlgebraicGeometry CategoryTheory

universe u v w

variable {S : Scheme.{u}} (U : Over S)

/-- The canonical residue-field point of a scheme over `S`, regarded as an
object of the slice over `U`. -/
public abbrev residueFieldPoint (u₀ : U.left) : Over U :=
  Over.mk (Over.homMk
    (U := Over.mk (U.left.fromSpecResidueField u₀ ≫ U.hom))
    (U.left.fromSpecResidueField u₀))

variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S)

/-- The image in `S` of the residue-field point of `U`. -/
public abbrev residueFieldBasePoint (u₀ : U.left) :
    Spec (U.left.residueField u₀) ⟶ S :=
  U.left.fromSpecResidueField u₀ ≫ U.hom

/-- The point of `S` at which the deformation base is localized. -/
public abbrev basePoint (u₀ : U.left) : S :=
  (residueFieldBasePoint U u₀)
    (IsLocalRing.closedPoint (U.left.residueField u₀))

/-- The canonical local-ring action on the residue field of `u₀`. -/
public noncomputable abbrev residueFieldAlgebra (u₀ : U.left) :
    Algebra (S.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀) :=
  (Scheme.stalkClosedPointTo (residueFieldBasePoint U u₀)).hom.toAlgebra

/-- The canonical residue-field point factors through the local ring of its
image in `S`. -/
public theorem residueFieldPoint_base_eq (u₀ : U.left) :
    letI := residueFieldAlgebra U u₀
    (Over.forget U).obj (residueFieldPoint U u₀) = Over.mk
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀))) ≫
        S.fromSpecStalk (basePoint U u₀)) := by
  change Over.mk (residueFieldBasePoint U u₀) = Over.mk _
  congr 1
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk
    (residueFieldBasePoint U u₀)).symm

/-- An object `x` over `U` is versal at `u₀` if the induced map of predeformation categories is
smooth: for a surjection `B ⟶ A` of Artinian local algebras, an arrow `y ⟶ z` over
`Spec A ⟶ Spec B` and an arrow `y ⟶ x` restricting to `u₀` extend to an arrow `z ⟶ x` making
the triangle commute. -/
@[stacks 07XF]
public noncomputable abbrev IsVersalAt
    (u₀ : U.left) (x : X) (hx : q.obj x = U) : Prop :=
  letI : Algebra (S.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀) :=
    residueFieldAlgebra U u₀
  ∀ (A B : Deformation.ArtinianLocalAlgCat.{u, u, u}
      (S.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀))
    (f : B ⟶ A), Function.Surjective f.hom →
    ∀ (y z : X)
      (hy : q.obj y = Over.mk
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk (basePoint U u₀)) A)) ≫
          S.fromSpecStalk (basePoint U u₀)))
      (hz : q.obj z = Over.mk
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk (basePoint U u₀)) B)) ≫
          S.fromSpecStalk (basePoint U u₀)))
      (i : y ⟶ z),
      eqToHom (congrArg Over.left hy).symm ≫ (q.map i).left ≫
          eqToHom (congrArg Over.left hz) =
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (a : y ⟶ x),
        Spec.map (CommRingCat.ofHom (residueMap A)) ≫
            eqToHom (congrArg Over.left hy).symm ≫ (q.map a).left ≫
            eqToHom (congrArg Over.left hx) = U.left.fromSpecResidueField u₀ →
        ∃ b : z ⟶ x, i ≫ b = a

end

/-! ### The morphism on predeformation categories induced by an object over a scheme -/

section
open AlgebraicGeometry CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
variable (U : Over S)
variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
variable (u₀ : Over U)
variable (hu₀ : (Over.forget U).obj u₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The category structure on the carrier of a predeformation construction. -/
public noncomputable instance
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : PredeformationConstruction iΛ q x₀ hx₀) : Category C.carrier :=
  C.category

/-- A 2-Yoneda representative of `x`, its pullback `x₀` at `u₀`, and the
induced map `\hat x` on predeformation categories. -/
public structure HatXConstruction
    (x : X) (hx : q.obj x = U) where
  /-- The chosen 2-Yoneda representative of `x`, as a based functor. -/
  yonedaFunctor : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor q
  /-- Its value at the identity of `U` is identified with `x`. -/
  evaluationIso : yonedaFunctor.obj (Over.mk (𝟙 U)) ≅ x
  /-- That identification lies over the identity of `U`. -/
  evaluationIso_over_identity : q.IsHomLift (𝟙 U) evaluationIso.hom
  /-- The representative carries every arrow of the slice to a cartesian arrow. -/
  cartesian : ∀ {a b : Over U} (f : a ⟶ b),
    q.IsStronglyCartesian f.left (yonedaFunctor.map f)
  /-- The distinguished pullback of `x` at the chosen point. -/
  point : X
  /-- The distinguished pullback is the value of the representative at the point. -/
  point_eq : point = yonedaFunctor.obj u₀
  /-- The distinguished pullback lies over the chosen point. -/
  point_base : q.obj point = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
  /-- The induced functor on predeformation categories, over the Artinian-algebra
  category. -/
  toBasedFunctor :
    BasedCategory.ofFunctor
      (predeformationCategory iΛ (Over.forget U) u₀ hu₀).projection ⥤ᵇ
    BasedCategory.ofFunctor
      (predeformationCategory iΛ q point point_base).projection
  /-- The induced functor sends a deformation object to the image of its point. -/
  object_point : ∀ a,
    ((predeformationCategory iΛ q point point_base).objects
      (toBasedFunctor.obj a)).point =
      yonedaFunctor.obj
        ((predeformationCategory iΛ (Over.forget U) u₀ hu₀).objects a).point
  /-- The induced functor sends a deformation object to the image of its arrow. -/
  object_arrow : ∀ a,
    ((predeformationCategory iΛ q point point_base).objects
      (toBasedFunctor.obj a)).arrow =
      eqToHom point_eq ≫
        yonedaFunctor.map
          ((predeformationCategory iΛ (Over.forget U) u₀ hu₀).objects
          a).arrow ≫
        eqToHom (object_point a).symm
  /-- The induced functor sends a morphism of deformation objects to the image of its
  reversed arrow. -/
  morphism_arrow : ∀ {a b} (f : a ⟶ b),
    ((predeformationCategory iΛ q point point_base).morphisms _ _
      (toBasedFunctor.map f)).arrow =
      eqToHom (object_point b) ≫
        yonedaFunctor.map
          ((predeformationCategory iΛ (Over.forget U) u₀ hu₀).morphisms
          a b f).arrow ≫
        eqToHom (object_point a).symm

/-- The map `\hat x : 𝓕_{(Sch/U)_{fppf},k,u₀} ⟶ 𝓕_{𝓧,k,x₀}` over
`𝒞_Λ`, for the 2-Yoneda functor associated to the given object over `U`. -/
@[stacks 07XE]
public noncomputable def hatX
    (x : X) (hx : q.obj x = U) (_ : q.IsFiberedInGroupoids) :
    HatXConstruction iΛ U q u₀ hu₀ x hx := by
  let ev := Functor.twoYonedaEvaluation q U
  letI : ev.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence q ‹q.IsFiberedInGroupoids› U
  let yonedaFunctor := ev.asEquivalence.inverse.obj (Functor.Fiber.mk hx)
  let evIso := ev.asEquivalence.counitIso.app (Functor.Fiber.mk hx)
  let evaluationIso := Functor.Fiber.fiberInclusion.mapIso evIso
  let induced := mapPredeformationCategory iΛ (Over.forget U) q
    yonedaFunctor.toFunctor yonedaFunctor.w u₀ hu₀
  refine {
    yonedaFunctor := yonedaFunctor
    evaluationIso := evaluationIso
    evaluationIso_over_identity := evIso.hom.2
    cartesian := ?_
    point := yonedaFunctor.obj u₀
    point_eq := rfl
    point_base := imageBasePoint iΛ (Over.forget U) q
      yonedaFunctor.toFunctor yonedaFunctor.w u₀ hu₀
    toBasedFunctor := induced.toBasedFunctor
    object_point := induced.object_point
    object_arrow := ?_
    morphism_arrow := ?_ }
  · intro a b f
    have hbase : (Over.forget U).IsHomLift f.left f := by
      simpa only [Over.forget_map] using
        (inferInstance : (Over.forget U).IsHomLift ((Over.forget U).map f) f)
    have : (BasedCategory.ofFunctor (Over.forget U)).p.IsHomLift f.left f := hbase
    have hlift : q.IsHomLift f.left (yonedaFunctor.map f) :=
      BasedFunctor.preserves_isHomLift yonedaFunctor f.left f
    have := hlift
    exact ‹q.IsFiberedInGroupoids›.isStronglyCartesian_homLift f.left (yonedaFunctor.map f)
  · intro a
    exact (induced.object_arrow a).trans (Category.id_comp _).symm
  · intro a b f
    exact induced.morphism_arrow f

end

end Deformation.Artin
