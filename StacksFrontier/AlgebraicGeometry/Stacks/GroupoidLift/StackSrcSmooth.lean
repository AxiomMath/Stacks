module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# The source map of the groupoid of a chart is formally smooth

With the notation of `AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid`, let the 1-morphism
`a : (Sch/U₀) ⟶ 𝒳` be formally smooth on objects (Stacks 06D0), and let `ι : Spec P ⟶ U₀` lift
points of `U₀` across square-zero thickenings of `κ`-small `A'`-algebras, as a morphism étale
over `U₀ ×_S T'` does. Then the source map of the groupoid of the chart is formally smooth: an
arrow `(u₁, u₂, φ)` over `C` lifts, with any prescribed lift `ℓ` of `u₁`, to an arrow over `C'`.

Indeed `a` solves the lifting problem of the object `ξ ℓ` over `Spec C'` and the point
`ι ∘ Spec u₂` of `U₀` over `Spec C`, matched by `φ`: it produces a point `m'` of `U₀` over
`Spec C'` restricting to `ι ∘ Spec u₂` and an isomorphism `a(m') ≅ ξ ℓ` compatible with `φ`. The
point `m'` is `ι ∘ Spec u₂'` for a lift `u₂'` of `u₂`, and the inverse of the isomorphism is the
required arrow from `ℓ` to `u₂'`.

The lifting problem is posed through
`AlgebraicGeometry.Stack.IsFormallySmoothOnObjects.exists_lift_of_obj_eq`, the form of Stacks
06D0 that names a morphism over the thickening instead of a chosen pullback.

## Main results

* `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects.exists_lift_of_obj_eq`.
* `AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid_srcFormallySmooth`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack

universe u v w

section Lift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒜 ℬ : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {g : 𝒜 ⟶ ℬ}

/-- **Formal smoothness on objects, without chosen pullbacks.** For a first-order thickening
`i : U ⟶ U'` of affines, an object `x` over `U` and a morphism `ψ : g(x) ⟶ y'` over `i`, there
are a morphism `β : x ⟶ x'` over `i` and a morphism `γ' : g(x') ⟶ y'` over the identity with
`g(β) ≫ γ' = ψ`. -/
theorem IsFormallySmoothOnObjects.exists_lift_of_obj_eq
    (hg : IsFormallySmoothOnObjects B S hS 𝒜 ℬ g)
    {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U'))
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    {x : 𝒜.val.obj} (hx : 𝒜.val.p.obj x = U) {y' : ℬ.val.obj} (hy' : ℬ.val.p.obj y' = U')
    (ψ : (CatFiberedInGroupoids.homFunctor g).obj x ⟶ y') [ℬ.val.p.IsHomLift i ψ] :
    ∃ (x' : 𝒜.val.obj) (_ : 𝒜.val.p.obj x' = U') (β : x ⟶ x') (_ : 𝒜.val.p.IsHomLift i β)
      (γ' : (CatFiberedInGroupoids.homFunctor g).obj x' ⟶ y')
      (_ : ℬ.val.p.IsHomLift (𝟙 U') γ'),
      (CatFiberedInGroupoids.homFunctor g).map β ≫ γ' = ψ := by
  have : 𝒜.val.p.IsFibered := 𝒜.isFiberedInGroupoids.isFibered
  have : ℬ.val.p.IsFibered := ℬ.isFiberedInGroupoids.isFibered
  let F := CatFiberedInGroupoids.homFunctor g
  have hF := CatFiberedInGroupoids.homFunctor_comp_p g
  let x₀ : 𝒜.val.p.Fiber U := ⟨x, hx⟩
  let y₀ : ℬ.val.p.Fiber U' := ⟨y', hy'⟩
  have := ℬ.isFiberedInGroupoids.isStronglyCartesian_homLift i ψ
  have hψ : ℬ.val.p.IsCartesian i ψ := inferInstance
  let γ := Functor.fiberIsoOfCartesian (p := ℬ.val.p)
    (z := (Functor.Fiber.mapOfComp 𝒜.val.p ℬ.val.p F hF U).obj x₀)
    (z' := Functor.pullbackFiber ℬ.val.p y₀ i) i ψ
    (Functor.IsPreFibered.pullbackMap y₀.2 i) hψ
    (Functor.IsPreFibered.pullbackMap.IsCartesian y₀.2 i)
  obtain ⟨x', β, γ', hsq⟩ := hg U U' i hU hU' hi x₀ y₀ γ
  have hc : ℬ.val.p.IsCartesian i (F.map (Functor.IsPreFibered.pullbackMap x'.2 i)) :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ _ _ _ _ _ _ _
      (CatFiberedInGroupoids.isStronglyCartesian_map g i
        (Functor.IsPreFibered.pullbackMap x'.2 i))
  let pbF := Functor.IsPreFibered.pullbackMap
    ((Functor.Fiber.mapOfComp 𝒜.val.p ℬ.val.p F hF U').obj x').2 i
  let pbX := Functor.IsPreFibered.pullbackMap x'.2 i
  let pbY := Functor.IsPreFibered.pullbackMap y₀.2 i
  let comp := Functor.fiberIsoOfCartesian (p := ℬ.val.p)
    (z :=
      Functor.pullbackFiber ℬ.val.p ((Functor.Fiber.mapOfComp 𝒜.val.p ℬ.val.p F hF U').obj x') i)
    (z' :=
      (Functor.Fiber.mapOfComp 𝒜.val.p ℬ.val.p F hF U).obj (Functor.pullbackFiber 𝒜.val.p x' i))
    i pbF (F.map pbX) (Functor.IsPreFibered.pullbackMap.IsCartesian _ i) hc
  let fI {V : BigFppfOver B S hS} := (Functor.Fiber.fiberInclusion (p := ℬ.val.p) (S := V))
  let mU := Functor.Fiber.mapOfComp 𝒜.val.p ℬ.val.p F hF U
  have hhom : fI.map comp.hom ≫ F.map pbX = pbF :=
    Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hγ : fI.map γ.hom ≫ pbY = ψ :=
    Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _
  let fA := Functor.Fiber.fiberInclusion (p := 𝒜.val.p) (S := U)
  have h1 : (fI.map comp.hom ≫ fI.map (mU.map β.hom) ≫ fI.map γ.hom) ≫ pbY =
      pbF ≫ fI.map γ'.hom := by
    have h := congrArg (fun f => Functor.Fiber.fiberInclusion.map f ≫ pbY) hsq
    simp only [Functor.map_comp, Category.assoc] at h
    exact h.trans (Functor.pullbackFiberHom_fac (p := ℬ.val.p) γ'.hom i)
  have hββ : fA.map β.hom ≫ fA.map β.inv ≫ pbX = pbX :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pbX) ((fA.map_comp _ _).symm.trans
      ((congrArg fA.map β.hom_inv_id).trans (fA.map_id _)))).trans (Category.id_comp _))
  have e : fI.map (mU.map β.hom) ≫ F.map (fA.map β.inv ≫ pbX) = F.map pbX :=
    (F.map_comp _ _).symm.trans (congrArg F.map hββ)
  have hpb : 𝒜.val.p.IsHomLift i pbX :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 i).toIsHomLift
  have hbi : 𝒜.val.p.IsHomLift (𝟙 U) (fA.map β.inv) := β.inv.2
  let Kiso := fI.mapIso comp ≪≫ fI.mapIso (mU.mapIso β)
  refine ⟨x'.1, x'.2, fA.map β.inv ≫ pbX,
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒜.val.p _ _ _ _ _ i pbX hpb (fA.map β.inv) hbi,
    fI.map γ'.hom, γ'.hom.2, ?_⟩
  refine (Iso.cancel_iso_hom_left Kiso _ _).1 ?_
  change (fI.map comp.hom ≫ fI.map (mU.map β.hom)) ≫ (F.map (fA.map β.inv ≫ pbX) ≫
    fI.map γ'.hom) = (fI.map comp.hom ≫ fI.map (mU.map β.hom)) ≫ ψ
  refine ((Category.assoc _ _ _).trans (congrArg (fI.map comp.hom ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ fI.map γ'.hom) e)))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ fI.map γ'.hom) hhom)).trans ?_
  refine h1.symm.trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg (fI.map comp.hom ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg (fI.map (mU.map β.hom) ≫ ·) hγ)))).trans
    (Category.assoc _ _ _).symm

end Lift

namespace GroupoidLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}

open StackChart

/-- **The source map of the groupoid of a chart is formally smooth** when the chart
`a : (Sch/U₀) ⟶ 𝒳` is formally smooth on objects and `ι : Spec P ⟶ U₀` lifts points of `U₀`
across square-zero thickenings. -/
theorem stackGroupoid_srcFormallySmooth
    (ha : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U₀) 𝒳 a)
    (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m') :
    (stackGroupoid (a := a) (ι := ι)).SrcFormallySmooth := by
  intro C' C e r ℓ hℓ
  obtain ⟨u₁, u₂, φ, hl⟩ := r
  obtain rfl : e.q.hom.hom.comp ℓ = u₁ := hℓ
  have hthk : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (specOverMap e.q)) :=
    Stacks.Smooth.isFirstOrderThickening_specMap _ e.surj e.sq
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (specOver C)) φ
  have hφi : IsIso φ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 (specOver C)) φ
  have hψ : 𝒳.val.p.IsHomLift (specOverMap e.q) (CategoryTheory.inv φ ≫
      StackChart.trans a ι e.q ℓ) := inferInstance
  obtain ⟨x', hx', β, hβ, γ', hγ', hfac⟩ := ha.exists_lift_of_obj_eq (specOverMap e.q)
    inferInstance inferInstance hthk (x := pt ι u₂) rfl (ξ_obj a ι ℓ)
    (CategoryTheory.inv φ ≫ StackChart.trans a ι e.q ℓ)
  obtain ⟨L, ⟨⟨⟩⟩, m⟩ := x'
  obtain rfl : L = specOver C' := hx'
  have fβ := IsHomLift.fac' (schemeFibredCategory B S hS U₀).val.p (specOverMap e.q) β
  change β.left = 𝟙 _ ≫ specOverMap e.q ≫ 𝟙 _ at fβ
  rw [Category.id_comp, Category.comp_id] at fβ
  have hm : specOverMap e.q ≫ m = specOverMap (SmallAlg.homMk u₂) ≫ ι := by
    rw [← fβ]
    exact Over.w β
  obtain ⟨u₂', hu₂', hm'⟩ := hι e m u₂ hm
  subst hu₂' hm'
  obtain rfl : β = Over.homMk (specOverMap e.q) (specOverMap_comp_pt ι e.q u₂') :=
    Over.OverMorphism.ext fβ
  change StackChart.trans a ι e.q u₂' ≫ γ' = _ at hfac
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (specOver C')) γ'
  have : IsIso γ' :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 (specOver C')) γ'
  have hl' : 𝒳.val.p.IsHomLift (𝟙 (specOver C')) (CategoryTheory.inv γ') := inferInstance
  have key : φ ≫ StackChart.trans a ι e.q u₂' =
      StackChart.trans a ι e.q ℓ ≫ CategoryTheory.inv γ' := by
    refine (IsIso.eq_comp_inv γ').2 ?_
    rw [Category.assoc, hfac, IsIso.hom_inv_id_assoc]
  exact ⟨⟨ℓ, u₂', CategoryTheory.inv γ', hl'⟩,
    Arr.map_eq_mk (a := a) (ι := ι) e.q ⟨ℓ, u₂', CategoryTheory.inv γ', hl'⟩ φ hl key, rfl⟩

end GroupoidLift

end AlgebraicGeometry.Stack

end
