module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.Deformation.Artin.FormalObject

/-!
# Lifting a formal object along a morphism formally smooth on objects

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
a scheme `S`, and let `η = (R, η_n, g_n)` be a formal object of `𝒴`. If `F` is formally
smooth on objects and the closed-point level `η_0` has a lift to `𝒳`, then the whole of `η`
lifts: there is a formal object `ξ` of `𝒳` over the same complete local base whose image
under `F` is isomorphic to `η`.

## Main definitions

* `Deformation.Artin.FormalObject.map` — the image of a formal object under a 1-morphism of
  categories fibred in groupoids, level by level.

## Main results

* `Deformation.Artin.isFirstOrderThickening_truncationSucc` — the inclusion of one infinitesimal
  thickening of the base of a formal object in the next is a first-order thickening.
* `Deformation.Artin.exists_formalObject_lift` — a lift of the closed-point level extends to a
  lift of the whole formal object.

## Implementation notes

The index `n` stands for the quotient by `𝔪 ^ (n + 1)`, so the "first level" of the source is the
index `0` here. The lifted formal object is taken over the same complete local base and retains
the given closed-point object on the nose. Local Noetherianness of the ambient scheme is not
assumed: the base of a formal object is already Noetherian.

## References

* [Stacks Project, Tag 07X5](https://stacks.math.columbia.edu/tag/07X5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open IsLocalRing
open Stacks.Thickenings

namespace Deformation.Artin

/- The fibre categories of the structure functors `𝒳.val.p` are built from definitions that the
`implicit` transparency level does not unfold; these are made unfoldable here. -/
attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.Fiber.mapOfComp CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.instCategoryObj

universe u v w

/-! ### The inclusions of consecutive levels are first-order thickenings -/

/-- The inclusion of one infinitesimal thickening of the base of a formal object in the next
is a first-order thickening of affine schemes. -/
public theorem isFirstOrderThickening_truncationSucc {S : Scheme.{u}} (A : FormalBase S)
    (n : ℕ) : IsFirstOrderThickening (A.truncationSucc n) := by
  let ψ := Ideal.Quotient.factorPow (maximalIdeal A.R) (Nat.le_succ (n + 1))
  have hsurj : Function.Surjective ψ := Ideal.Quotient.factor_surjective _
  have hker : RingHom.ker ψ ^ 2 = ⊥ := by
    rw [Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))]
    have hpow : (maximalIdeal A.R ^ (n + 1)) ^ 2 ≤ maximalIdeal A.R ^ (n + 2) := by
      rw [← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    simpa using hpow
  show IsFirstOrderThickening (Spec.map (CommRingCat.ofHom ψ))
  exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom ψ) hsurj hker

/-! ### The image of a formal object under a 1-morphism -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) (p : 𝒳 ⟶ 𝒴)

/-- The image of a formal object under a 1-morphism of categories fibred in groupoids: the
same complete local base, with every level and every transition morphism pushed forward. -/
public def FormalObject.map (ξ : FormalObject B S hS 𝒳.val.p) :
    FormalObject B S hS 𝒴.val.p := by
  let F := CatFiberedInGroupoids.homFunctor p
  have hF := CatFiberedInGroupoids.homFunctor_comp_p p
  refine
    { base := ξ.base
      contains := ξ.contains
      level := fun n => F.obj (ξ.level n)
      level_eq := fun n => (Functor.congr_obj hF (ξ.level n)).trans (ξ.level_eq n)
      transition := fun n => F.map (ξ.transition n)
      transition_lift := fun n => ?_ }
  let := ξ.transition_lift n
  exact BasedFunctor.preserves_isHomLift p.hom
    (truncationOverSucc B S hS ξ.base ξ.contains n) (ξ.transition n)

/-! ### The recursion on infinitesimal levels -/

/-- A lift of the `n`-th level of `η` to `𝒳`, together with an isomorphism of its image with
`η_n` in the fibre over the `n`-th thickening. -/
private structure LiftStage (η : FormalObject B S hS 𝒴.val.p) (n : ℕ) where
  /-- The lift of the `n`-th level. -/
  source : 𝒳.val.p.Fiber (truncationOver B S hS η.base η.contains n)
  /-- Its image is identified with the `n`-th level of `η`. -/
  imageIso :
    (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p)
      (truncationOver B S hS η.base η.contains n)).obj source ≅
        ⟨η.level n, η.level_eq n⟩

/-- An extension of a stage by one infinitesimal level: the next stage, the transition
morphism to it, and the compatibility of the two identifications with the transition morphism
of `η`. -/
private structure LiftStep (η : FormalObject B S hS 𝒴.val.p) (n : ℕ)
    (s : LiftStage B S hS 𝒳 𝒴 p η n) where
  /-- The stage one level up. -/
  next : LiftStage B S hS 𝒳 𝒴 p η (n + 1)
  /-- The transition morphism of the lift. -/
  transition : s.source.1 ⟶ next.source.1
  /-- It lies over the inclusion of consecutive thickenings. -/
  transition_lift : 𝒳.val.p.IsHomLift
    (truncationOverSucc B S hS η.base η.contains n) transition
  /-- The square formed by the two identifications and the two transition morphisms
  commutes. -/
  naturality : (CatFiberedInGroupoids.homFunctor p).map transition ≫
      Functor.Fiber.fiberInclusion.map next.imageIso.hom =
    Functor.Fiber.fiberInclusion.map s.imageIso.hom ≫ η.transition n

/-- Formal smoothness on objects extends any stage by one infinitesimal level. -/
private theorem nonempty_liftStep (hp : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p)
    (η : FormalObject B S hS 𝒴.val.p) (n : ℕ) (s : LiftStage B S hS 𝒳 𝒴 p η n) :
    Nonempty (LiftStep B S hS 𝒳 𝒴 p η n s) := by
  classical
  let Xp := 𝒳.val.p
  let Yp := 𝒴.val.p
  let F := CatFiberedInGroupoids.homFunctor p
  let hF := CatFiberedInGroupoids.homFunctor_comp_p p
  let U := truncationOver B S hS η.base η.contains n
  let U' := truncationOver B S hS η.base η.contains (n + 1)
  let i := truncationOverSucc B S hS η.base η.contains n
  let pU := fun V => Functor.Fiber.mapOfComp Xp Yp F hF V
  let y : Yp.Fiber U' := ⟨η.level (n + 1), η.level_eq (n + 1)⟩
  let : Xp.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : Yp.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let : Yp.IsHomLift i (η.transition n) := η.transition_lift n
  let : Yp.IsStronglyCartesian i (η.transition n) :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift i (η.transition n)
  let pbηMap := Functor.IsPreFibered.pullbackMap y.2 i
  let targetCompare : Functor.pullbackFiber Yp y i ≅ ⟨η.level n, η.level_eq n⟩ :=
    Functor.fiberIsoOfCartesian i pbηMap (η.transition n) inferInstance inferInstance
  let γ : (pU U).obj s.source ≅ Functor.pullbackFiber Yp y i :=
    s.imageIso ≪≫ targetCompare.symm
  have hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := by
    show IsAffine (η.base.truncation n)
    infer_instance
  have hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U') := by
    show IsAffine (η.base.truncation (n + 1))
    infer_instance
  have hi : IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) := by
    show IsFirstOrderThickening (η.base.truncationSucc n)
    exact isFirstOrderThickening_truncationSucc η.base n
  obtain ⟨x', β, γ', hsq⟩ := hp U U' i hU hU' hi s.source y γ
  let pbXMap := Functor.IsPreFibered.pullbackMap x'.2 i
  let trans := Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap
  have hpbX : Xp.IsHomLift i pbXMap :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 i).toIsHomLift
  have htrans : Xp.IsHomLift i trans := by
    have hcomp := @IsHomLift.comp _ _ _ _ Xp U U U'
      s.source.1 (Functor.pullbackFiber Xp x' i).1 x'.1
      (𝟙 U) i (Functor.Fiber.fiberInclusion.map β.inv) pbXMap β.inv.2 hpbX
    simpa [trans, Category.id_comp, Functor.Fiber.fiberInclusion] using hcomp
  let next : LiftStage B S hS 𝒳 𝒴 p η (n + 1) := ⟨x', γ'⟩
  let compare : Functor.pullbackFiber Yp ((pU U').obj x') i ≅
      (pU U).obj (Functor.pullbackFiber Xp x' i) :=
    Functor.fiberIsoOfCartesian i
      (Functor.IsPreFibered.pullbackMap ((pU U').obj x').2 i) (F.map pbXMap) inferInstance
      (by
        let : Xp.IsHomLift i pbXMap := hpbX
        have := CatFiberedInGroupoids.isStronglyCartesian_map p i pbXMap
        exact Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
          Yp i (F.map pbXMap))
  have hsqMap := congrArg Functor.Fiber.fiberInclusion.map
    (show (compare.hom ≫ (pU U).map β.hom) ≫ γ.hom =
      Functor.pullbackFiberHom γ'.hom i from hsq)
  have hcompare : Functor.Fiber.fiberInclusion.map compare.hom ≫ F.map pbXMap =
      Functor.IsPreFibered.pullbackMap ((pU U').obj x').2 i := by
    simp [compare]
  have hgamma : Functor.Fiber.fiberInclusion.map γ.hom ≫ pbηMap =
      Functor.Fiber.fiberInclusion.map s.imageIso.hom ≫ η.transition n := by
    have htc : Functor.Fiber.fiberInclusion.map targetCompare.inv ≫ pbηMap =
        η.transition n := by
      simp [targetCompare]
    dsimp [γ]
    rw [Functor.map_comp, Category.assoc, htc]
  have hcancel : F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
      Functor.Fiber.fiberInclusion.map s.imageIso.hom ≫ η.transition n =
        F.map pbXMap ≫ Functor.Fiber.fiberInclusion.map γ'.hom := by
    refine (cancel_epi (Functor.Fiber.fiberInclusion.map compare.hom)).mp ?_
    have h := congrArg (fun f => f ≫ pbηMap) hsqMap
    rw [Functor.Fiber.fiberInclusion.map_comp, Functor.Fiber.fiberInclusion.map_comp] at h
    rw [Functor.Fiber.fiberInclusion_map_mapOfComp_map Xp Yp F hF U β.hom] at h
    have h' : (Functor.Fiber.fiberInclusion.map compare.hom ≫
          F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
          Functor.Fiber.fiberInclusion.map γ.hom) ≫ pbηMap =
        Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom γ'.hom i) ≫ pbηMap := by
      simpa [pU, pbηMap, Category.assoc] using h
    simp only [Category.assoc] at h'
    rw [hgamma, Functor.pullbackFiberHom_fac γ'.hom i] at h'
    calc
      Functor.Fiber.fiberInclusion.map compare.hom ≫
            F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
            Functor.Fiber.fiberInclusion.map s.imageIso.hom ≫ η.transition n =
          Functor.IsPreFibered.pullbackMap ((pU U').obj x').2 i ≫
            Functor.Fiber.fiberInclusion.map γ'.hom := by
          simpa [Category.assoc] using h'
      _ = Functor.Fiber.fiberInclusion.map compare.hom ≫
            F.map pbXMap ≫ Functor.Fiber.fiberInclusion.map γ'.hom := by
          rw [← hcompare]
          simp [Category.assoc]
  refine ⟨⟨next, trans, htrans, ?_⟩⟩
  have hβ : F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
      F.map (Functor.Fiber.fiberInclusion.map β.hom) = 𝟙 _ := by
    simp
  calc
    F.map trans ≫ Functor.Fiber.fiberInclusion.map next.imageIso.hom =
        F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
          F.map pbXMap ≫ Functor.Fiber.fiberInclusion.map γ'.hom := by
        dsimp [trans, next]
        rw [Functor.map_comp, Category.assoc]
    _ = F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
          F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
          Functor.Fiber.fiberInclusion.map s.imageIso.hom ≫ η.transition n := by
        rw [hcancel]
    _ = (F.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
          F.map (Functor.Fiber.fiberInclusion.map β.hom)) ≫
          Functor.Fiber.fiberInclusion.map s.imageIso.hom ≫ η.transition n := by
        simp
    _ = Functor.Fiber.fiberInclusion.map s.imageIso.hom ≫ η.transition n := by
        rw [hβ, Category.id_comp]

/-! ### The lift of a formal object -/

/-- If `F : 𝒳 ⟶ 𝒴` is formally smooth on objects, every formal object `η` of `𝒴` whose
closed-point level lifts to `𝒳` is, up to isomorphism, the image of a formal object of `𝒳` over
the same complete local base and with the given closed-point lift. -/
@[stacks 07X5]
public theorem exists_formalObject_lift
    (hp : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p)
    (η : FormalObject B S hS 𝒴.val.p)
    (ξ₀ : 𝒳.val.p.Fiber (truncationOver B S hS η.base η.contains 0))
    (hξ₀ : (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p)
      (truncationOver B S hS η.base η.contains 0)).obj ξ₀ ≅
        ⟨η.level 0, η.level_eq 0⟩) :
    ∃ ξ : FormalObject B S hS 𝒳.val.p,
      ξ.base = η.base ∧ ξ.level 0 = ξ₀.1 ∧
        Nonempty (FormalObject.map B S hS 𝒳 𝒴 p ξ ≅ η) := by
  classical
  let stepData (n : ℕ) (s : LiftStage B S hS 𝒳 𝒴 p η n) : LiftStep B S hS 𝒳 𝒴 p η n s :=
    Classical.choice (nonempty_liftStep B S hS 𝒳 𝒴 p hp η n s)
  let states : (n : ℕ) → LiftStage B S hS 𝒳 𝒴 p η n :=
    Nat.rec ⟨ξ₀, hξ₀⟩ (fun n s => (stepData n s).next)
  let ξ : FormalObject B S hS 𝒳.val.p :=
    { base := η.base
      contains := η.contains
      level := fun n => (states n).source.1
      level_eq := fun n => (states n).source.2
      transition := fun n => (stepData n (states n)).transition
      transition_lift := fun n => (stepData n (states n)).transition_lift }
  let toη : FormalObject.map B S hS 𝒳 𝒴 p ξ ⟶ η :=
    { app := fun n => Functor.Fiber.fiberInclusion.map (states n).imageIso.hom
      naturality := fun n => (stepData n (states n)).naturality }
  let fromη : η ⟶ FormalObject.map B S hS 𝒳 𝒴 p ξ :=
    { app := fun n => Functor.Fiber.fiberInclusion.map (states n).imageIso.inv
      naturality := fun n => by
        let st := states n
        let st' := states (n + 1)
        have h := (stepData n st).naturality
        have hcur : Functor.Fiber.fiberInclusion.map st.imageIso.inv ≫
            Functor.Fiber.fiberInclusion.map st.imageIso.hom = 𝟙 _ := by
          rw [← Functor.Fiber.fiberInclusion.map_comp, Iso.inv_hom_id,
            Functor.Fiber.fiberInclusion.map_id]
        have hnext : Functor.Fiber.fiberInclusion.map st'.imageIso.hom ≫
            Functor.Fiber.fiberInclusion.map st'.imageIso.inv =
              𝟙 ((CatFiberedInGroupoids.homFunctor p).obj st'.source.1) := by
          rw [← Functor.Fiber.fiberInclusion.map_comp, Iso.hom_inv_id,
            Functor.Fiber.fiberInclusion.map_id]
          rfl
        calc
          η.transition n ≫ Functor.Fiber.fiberInclusion.map st'.imageIso.inv =
              (Functor.Fiber.fiberInclusion.map st.imageIso.inv ≫
                Functor.Fiber.fiberInclusion.map st.imageIso.hom) ≫
                η.transition n ≫ Functor.Fiber.fiberInclusion.map st'.imageIso.inv := by
                rw [hcur, Category.id_comp]
          _ = Functor.Fiber.fiberInclusion.map st.imageIso.inv ≫
                (Functor.Fiber.fiberInclusion.map st.imageIso.hom ≫ η.transition n) ≫
                Functor.Fiber.fiberInclusion.map st'.imageIso.inv := by
                simp [Category.assoc]
          _ = Functor.Fiber.fiberInclusion.map st.imageIso.inv ≫
                ((CatFiberedInGroupoids.homFunctor p).map (stepData n st).transition ≫
                  Functor.Fiber.fiberInclusion.map st'.imageIso.hom) ≫
                Functor.Fiber.fiberInclusion.map st'.imageIso.inv := by rw [← h]
          _ = Functor.Fiber.fiberInclusion.map st.imageIso.inv ≫
                (CatFiberedInGroupoids.homFunctor p).map (stepData n st).transition := by
                rw [Category.assoc, hnext, Category.comp_id] }
  refine ⟨ξ, rfl, rfl, ⟨⟨toη, fromη, ?_, ?_⟩⟩⟩
  · refine FormalObject.Hom.ext fun n => ?_
    show Functor.Fiber.fiberInclusion.map (states n).imageIso.hom ≫
      Functor.Fiber.fiberInclusion.map (states n).imageIso.inv = 𝟙 _
    rw [← Functor.Fiber.fiberInclusion.map_comp, Iso.hom_inv_id,
      Functor.Fiber.fiberInclusion.map_id]
  · refine FormalObject.Hom.ext fun n => ?_
    show Functor.Fiber.fiberInclusion.map (states n).imageIso.inv ≫
      Functor.Fiber.fiberInclusion.map (states n).imageIso.hom = 𝟙 _
    rw [← Functor.Fiber.fiberInclusion.map_comp, Iso.inv_hom_id,
      Functor.Fiber.fiberInclusion.map_id]

end Deformation.Artin
