module

public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A point of a smooth chart over a finite extension of the residue field

Let `f : (Sch/V) ⟶ 𝒳` be a 1-morphism from the category represented by a scheme `V`, representable
by algebraic spaces, whose base change along every scheme-valued point is surjective and smooth,
and let `x₀` be an object of `𝒳` over `Spec k`. Then there are a finite extension `l/k`, an object
`u₀` of `(Sch/V)` over `Spec l` and an arrow `f(u₀) ⟶ x₀` of `𝒳` lying over `Spec l ⟶ Spec k`.

This is the first step of the proof of Stacks 07X1. The source reads it off Stacks 07W4 for the
algebraic space `U_{x₀}`; here a smooth, hence flat and locally finitely presented, surjective
scheme morphism `T ⟶ Spec k` along which `x₀` lifts to `(Sch/V)` is used instead, by
`AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation`,
and the field is the residue field at a closed point of `T`, which is finite over `k` because `T`
is locally of finite type over `k` (Stacks 0478). Separability of `l/k` is not needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Artin

-- `Over.post` and the fibres of a functor are plain `def`s, so goals mentioning an object of the
-- site read in `Over S` are not type-correct at `implicit` transparency.
attribute [local implicit_reducible] CategoryTheory.Over.post
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

/-- **The residue field at a closed point of a scheme locally of finite type over a field is a
finite extension of that field** (Stacks 0478 (1), the finite form). -/
@[ega "I 6.4.2" "necessity"]
theorem finite_residueField_of_isClosed_of_field {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {x : X} (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.Finite k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hx; infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ p) := inferInstance
  rw [← p.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  let : Algebra.FiniteType k (X.residueField x) := by
    show RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    · rfl
    · simp only [RingHom.algebraMap_toAlgebra]
      rw [← Scheme.Γevaluation_naturality]
      simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  exact finite_of_finite_type_of_isJacobsonRing _ _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A chart point from a scheme lift at a point.** Let `f : (Sch/V) ⟶ 𝒳` be a 1-morphism and
`x₀` an object of `𝒳` over `Spec k`, and suppose `x₀` lifts along `f` after a morphism
`m : T ⟶ Spec k` of the site: an object `z` of `(Sch/V)` and an arrow `φ : f(z) ⟶ x₀` lying over
`m`. Then every point `t` of `T` gives, for `l = κ(t)`, an object `u₀` of `(Sch/V)` lying over
`Spec l` and an arrow `f(u₀) ⟶ x₀` lying over `Spec l ⟶ Spec k`. -/
theorem exists_chart_point_of_lift
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (V : BigFppfOver B S hS) (f : Stack.schemeFibredCategory B S hS V ⟶ 𝒳)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (T : B.Schemes) (m : T ⟶ (𝒳.val.p.obj x₀).left)
    (z : (Stack.schemeFibredCategory B S hS V).val.obj)
    (φ : (CatFiberedInGroupoids.homFunctor f).obj z ⟶ x₀)
    (hφ : 𝒳.val.p.IsHomLift
      (Over.homMk m rfl : (Over.mk (m ≫ (𝒳.val.p.obj x₀).hom) : BigFppfOver B S hS) ⟶
        𝒳.val.p.obj x₀) φ)
    (t : B.inclusion.obj T) :
    letI : Algebra k ((B.inclusion.obj T).residueField t) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (B.inclusion.map m ≫ eqToHom (congrArg Over.left hx₀)).appTop ≫
        (B.inclusion.obj T).Γevaluation t).hom.toAlgebra
    letI : Algebra Λ ((B.inclusion.obj T).residueField t) :=
      ((algebraMap k ((B.inclusion.obj T).residueField t)).comp (algebraMap Λ k)).toAlgebra
    ∃ (u₀ : Over V)
      (_hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap Λ ((B.inclusion.obj T).residueField t))) ≫ iΛ))
      (hxₗ : (𝒳.val.p ⋙ Over.post B.inclusion).obj ((CatFiberedInGroupoids.homFunctor f).obj u₀) =
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap Λ ((B.inclusion.obj T).residueField t))) ≫ iΛ))
      (η : (CatFiberedInGroupoids.homFunctor f).obj u₀ ⟶ x₀),
      eqToHom (congrArg Over.left hxₗ).symm ≫ ((𝒳.val.p ⋙ Over.post B.inclusion).map η).left ≫
        eqToHom (congrArg Over.left hx₀) =
          Spec.map (CommRingCat.ofHom (algebraMap k ((B.inclusion.obj T).residueField t))) := by
  classical
  let U := 𝒳.val.p.obj x₀
  have hU : B.inclusion.obj U.left = Spec (.of k) := congrArg Over.left hx₀
  let X : Scheme.{u} := B.inclusion.obj T
  let g : X ⟶ Spec (.of k) := B.inclusion.map m ≫ eqToHom hU
  let l := X.residueField t
  let algkl : Algebra k l :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation t).hom.toAlgebra
  let algΛl : Algebra Λ l := ((algebraMap k l).comp (algebraMap Λ k)).toAlgebra
  have : IsScalarTower Λ k l := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k l)) = X.fromSpecResidueField t ≫ g :=
    SpecMap_algebraMap_residueField g t
  have hl : B.Contains (Spec (.of l)) := B.residueField_spec_contains T.2 t
  let jT : B.obj hl ⟶ T := B.inclusion.preimage (X.fromSpecResidueField t)
  have hjT : B.inclusion.map jT = X.fromSpecResidueField t := B.inclusion.map_preimage _
  -- the base of `z`
  have hz : z.left = (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f) z).symm.trans
      (IsHomLift.domain_eq 𝒳.val.p
        (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ)
  let L : BigFppfOver B S hS := Over.mk (jT ≫ m ≫ U.hom)
  let a₀ : L ⟶ (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) := Over.homMk jT rfl
  let a' : L ⟶ z.left := a₀ ≫ eqToHom hz.symm
  let u₀ : Over V := Over.mk (a' ≫ z.hom)
  let ψ : u₀ ⟶ z := Over.homMk a' rfl
  -- the structure morphism of `Spec l` over `S`
  have hUhom : B.inclusion.map U.hom =
      eqToHom hU ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
    have hw := Over.w (eqToHom hx₀)
    rw [Over.eqToHom_left] at hw
    exact hw.symm
  have hbase : B.inclusion.map L.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
    show B.inclusion.map (jT ≫ m ≫ U.hom) = _
    rw [Functor.map_comp, Functor.map_comp, hjT, hUhom]
    have hΛl : CommRingCat.ofHom (algebraMap Λ l) =
        CommRingCat.ofHom (algebraMap Λ k) ≫ CommRingCat.ofHom (algebraMap k l) := rfl
    rw [hΛl, Spec.map_comp, hspec]
    simp only [g, Category.assoc]
  have hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) :=
    congrArg Over.mk hbase
  have hxₗ : (𝒳.val.p ⋙ Over.post B.inclusion).obj ((CatFiberedInGroupoids.homFunctor f).obj u₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) :=
    (congrArg (Over.post B.inclusion).obj
      (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f) u₀)).trans hu₀
  refine ⟨u₀, hu₀, hxₗ, (CatFiberedInGroupoids.homFunctor f).map ψ ≫ φ, ?_⟩
  have hψ₀ : (Over.forget V).IsHomLift a₀ ψ :=
    (IsHomLift.lift_comp_eqToHom_iff (p := Over.forget V) a₀ ψ hz.symm).mp
      (IsHomLift.map (p := Over.forget V) ψ)
  have hψ₁ : 𝒳.val.p.IsHomLift a₀ ((CatFiberedInGroupoids.homFunctor f).map ψ) :=
    PresheafOfCategories.isHomLift_map_of_comp (CatFiberedInGroupoids.homFunctor_comp_p f) a₀ ψ hψ₀
  have hη := IsHomLift.fac' 𝒳.val.p
    (a₀ ≫ (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U))
    ((CatFiberedInGroupoids.homFunctor f).map ψ ≫ φ)
  rw [Functor.comp_map, hη]
  simp only [Over.post_map, Over.homMk_left, Over.comp_left, Over.eqToHom_left,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, a₀]
  rw [hjT, hspec]
  simp [g]

/-- **A point of a smooth surjective chart over a finite extension of the residue field.** Let
`f : (Sch/V) ⟶ 𝒳` be representable by algebraic spaces, with surjective and smooth base change
along every scheme-valued point (the presentation clause of Stacks 026O), and let `x₀` be an
object of `𝒳` over `Spec k`. Then for some finite extension `l/k` there are an object `u₀` of
`(Sch/V)` lying over `Spec l` and an arrow `f(u₀) ⟶ x₀` lying over `Spec l ⟶ Spec k`. -/
theorem exists_finite_extension_chart_point
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (V : BigFppfOver B S hS) (f : Stack.schemeFibredCategory B S hS V ⟶ 𝒳)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (W : BigFppfOver B S hS)
      (yv : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map W.hom)
      (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B W.left.1 W.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W.hom) (Stack.schemeFibredCategory B S hS V).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS W
        ((spacesOverSmallerBaseFunctor B W.left.1 S W.left.2 hS W.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Algebra Λ l) (_ : IsScalarTower Λ k l),
      Module.Finite k l ∧
      ∃ (u₀ : Over V)
        (_hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (hxₗ : (𝒳.val.p ⋙ Over.post B.inclusion).obj ((CatFiberedInGroupoids.homFunctor f).obj u₀) =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (η : (CatFiberedInGroupoids.homFunctor f).obj u₀ ⟶ x₀),
        eqToHom (congrArg Over.left hxₗ).symm ≫ ((𝒳.val.p ⋙ Over.post B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) := by
  classical
  let U := 𝒳.val.p.obj x₀
  let y : 𝒳.val.p.Fiber U := ⟨x₀, rfl⟩
  obtain ⟨T, m, -, hlfp, hsurj, z, φ, hφ⟩ :=
    Stack.exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS f hf
      (fun W yv hyv F hF he => by
        obtain ⟨hs, hsm⟩ := hprop W yv hyv F hF he
        exact ⟨hs, Space.isFlat_of_isSmooth B S hS _ hsm,
          Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩) U y
  have hU : B.inclusion.obj U.left = Spec (.of k) := congrArg Over.left hx₀
  let X : Scheme.{u} := B.inclusion.obj T
  let g : X ⟶ Spec (.of k) := B.inclusion.map m ≫ eqToHom hU
  have : LocallyOfFiniteType (B.inclusion.map m) := inferInstance
  have : LocallyOfFiniteType g := inferInstance
  have : Surjective g := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨t₀, -⟩ := g.surjective (IsLocalRing.closedPoint k)
  obtain ⟨t, -, ht⟩ := nonempty_inter_closedPoints (X := X) (Z := Set.univ) ⟨t₀, trivial⟩
    isClosed_univ.isLocallyClosed
  have htc : IsClosed ({t} : Set X) := ht
  have hfin := finite_residueField_of_isClosed_of_field g htc
  let algkl : Algebra k (X.residueField t) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation t).hom.toAlgebra
  let algΛl : Algebra Λ (X.residueField t) :=
    ((algebraMap k (X.residueField t)).comp (algebraMap Λ k)).toAlgebra
  obtain ⟨u₀, hu₀, hxₗ, η, hη⟩ := exists_chart_point_of_lift 𝒳 V f iΛ x₀ hx₀ T m z φ hφ t
  exact ⟨_, inferInstance, algkl, algΛl, IsScalarTower.of_algebraMap_eq (fun _ => rfl), hfin, u₀,
    hu₀, hxₗ, η, hη⟩

end Deformation.Artin
