module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# Essential surjectivity of smooth morphisms

A smooth morphism of predeformation categories is essentially
surjective, and stays essentially surjective after completion.

## Main results

* `essSurj_of_isSmooth_of_fiber_essSurj`
  promotes essential surjectivity on the special fibre to essential
  surjectivity of the underlying functor.
* `completionMap_essSurj_of_isSmooth_of_fiber_essSurj`
  gives essential surjectivity of the induced functor on formal objects.

## Implementation notes

### Essential surjectivity of a smooth morphism

The special fibre is formed using `residueFieldObject` and the
induced fibre functor `fiberFunctor`. Only the target projection
needs to be cofibered in groupoids: the source proof pushes forward an object
of the target and then applies smoothness to lift it.

### Essential surjectivity after completion

The residue-field fibre is represented by `residueFieldObject` and
its induced functor by `fiberFunctor`. Only the target projection
needs to be cofibered in groupoids: its formal-object fibres have invertible
morphisms, so the levelwise lift produced by smoothness is an isomorphism.

## References

* [Stacks Project, Tag 06HN](https://stacks.math.columbia.edu/tag/06HN)
-/

@[expose] public section

namespace Deformation

/-! ### Essential surjectivity of a smooth morphism -/

section
open CategoryTheory
universe u w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A smooth morphism of categories over `\mathcal C_\Lambda` with cofibered
target is essentially surjective whenever its special-fibre functor is. -/
@[stacks 06HN "essentially_surjective"]
public theorem essSurj_of_isSmooth_of_fiber_essSurj
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖)
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (hφ : IsSmooth φ)
    (h₀ : (fiberFunctor φ (residueFieldObject Λ k)).EssSurj) :
    φ.toFunctor.EssSurj := by
  refine ⟨fun y => ?_⟩
  let A := 𝓖.p.obj y
  let resAlg : A →ₐ[Λ] IsLocalRing.ResidueField A :=
    IsScalarTower.toAlgHom Λ A (IsLocalRing.ResidueField A)
  let e : A →ₐ[Λ] ULift.{w} k :=
    (ULift.algEquiv (R := Λ) (A := k)).symm.toAlgHom.comp
      (A.residueEquiv.toAlgHom.comp resAlg)
  let q : A ⟶ residueFieldObject Λ k :=
    { hom := e
      isLocal := ⟨fun a ha =>
        (inferInstance : IsLocalHom (IsLocalRing.residue A)).map_nonunit a
          ((MulEquiv.isUnit_map A.residueEquiv).mp
            ((MulEquiv.isUnit_map (ULift.algEquiv (R := Λ) (A := k)).symm).mp ha))⟩
      residue_comm := fun _ => rfl }
  have hq_surjective : Function.Surjective q.hom := by
    change Function.Surjective
      (fun a : A => (ULift.algEquiv (R := Λ) (A := k)).symm
        (A.residueEquiv (IsLocalRing.residue A a)))
    exact (ULift.algEquiv (R := Λ) (A := k)).symm.surjective.comp
      (A.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A)))
  obtain ⟨y₀op, pushop, hpushop⟩ :=
    h𝓖.exists_lift q.op (Opposite.op y) rfl
  let y₀ : 𝓖.obj := Opposite.unop y₀op
  have hy₀ : 𝓖.p.obj y₀ = residueFieldObject Λ k :=
    congrArg Opposite.unop (IsHomLift.domain_eq (p := 𝓖.p.op) q.op pushop)
  let push : y ⟶ y₀ := Opposite.unop pushop
  have hpush : 𝓖.p.IsHomLift q push := isHomLift_unop 𝓖.p q.op pushop (inst := hpushop)
  let y₀K : Functor.Fiber 𝓖.p (residueFieldObject Λ k) := ⟨y₀, hy₀⟩
  obtain ⟨x₀, ⟨i⟩⟩ := h₀.mem_essImage y₀K
  obtain ⟨x, h, a, hh, ha, hcomm⟩ := hφ q hq_surjective y x₀.1
    (push ≫ i.inv.val) (by
      let : 𝓖.p.IsHomLift (𝟙 (residueFieldObject Λ k)) i.inv.val := i.inv.property
      exact IsHomLift.comp_lift_id_right' 𝓖.p q push
        (residueFieldObject Λ k) i.inv.val)
  have hx : 𝓕.p.obj x = A := IsHomLift.domain_eq (p := 𝓕.p) q h
  let : IsGroupoid (Functor.Fiber 𝓖.p.op (Opposite.op A)) :=
    Functor.IsFiberedInGroupoids.fiber_isGroupoid h𝓖 (Opposite.op A)
  let yAop : Functor.Fiber 𝓖.p.op (Opposite.op A) := ⟨Opposite.op y, rfl⟩
  let φxAop : Functor.Fiber 𝓖.p.op (Opposite.op A) :=
    ⟨Opposite.op (φ.obj x), congrArg Opposite.op (by rw [φ.w_obj, hx])⟩
  have haop : 𝓖.p.op.IsHomLift (𝟙 (Opposite.op A)) a.op := by
    simpa using isHomLift_op 𝓖.p (𝟙 A) a (inst := ha)
  let aAop : yAop ⟶ φxAop := ⟨a.op, haop⟩
  let : IsIso aAop := inferInstance
  let iop : Opposite.op y ≅ Opposite.op (φ.obj x) :=
    (Functor.Fiber.fiberInclusion (p := 𝓖.p.op) (S := Opposite.op A)).mapIso (asIso aAop)
  exact ⟨x, ⟨Iso.unop iop⟩⟩

end

/-! ### Essential surjectivity after completion -/

section
open CategoryTheory
universe u v w uF vF uG vG

set_option backward.isDefEq.respectTransparency.types false

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism of a category fibered in groupoids lying over an identity is an isomorphism:
`f : x ⟶ y` between two objects over `A` which lies over `𝟙 A` is invertible, being a morphism
of the groupoid fiber over `A`. -/
noncomputable def iso_of_vertical
    {C D : Type*} [Category C] [Category D] (q : C ⥤ D)
    (hq : q.op.IsFiberedInGroupoids) {A : D} {x y : C}
    (f : x ⟶ y) (hx : q.obj x = A) (hy : q.obj y = A)
    (hf : q.IsHomLift (𝟙 A) f) : x ≅ y := by
  letI : IsGroupoid (Functor.Fiber q.op (Opposite.op A)) :=
    Functor.IsFiberedInGroupoids.fiber_isGroupoid hq (Opposite.op A)
  let x' : Functor.Fiber q.op (Opposite.op A) := ⟨Opposite.op x, congrArg Opposite.op hx⟩
  let y' : Functor.Fiber q.op (Opposite.op A) := ⟨Opposite.op y, congrArg Opposite.op hy⟩
  have hf' : q.op.IsHomLift (𝟙 (Opposite.op A)) f.op := by
    simpa using (isHomLift_op q (𝟙 A) f (inst := hf))
  let f' : y' ⟶ x' := ⟨f.op, hf'⟩
  let i : Opposite.op y ≅ Opposite.op x :=
    (Functor.Fiber.fiberInclusion (p := q.op) (S := Opposite.op A)).mapIso (asIso f')
  exact Iso.unop i

/-- A lift of a formal object `η` of `q` along `φ`, defined up to level `n`: an object of `F` over
the `n`-th adic truncation of `η.base`, together with a vertical map from `η.level n` to its
image. -/
structure CompletionLiftState
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (η : FormalObject q) (n : ℕ) where
  /-- The object of `F` at level `n`. -/
  obj : F
  /-- `obj` lies over the `n`-th adic truncation of `η.base`. -/
  obj_base : (BasedCategory.ofFunctor p).p.obj obj =
    (AdicTruncation.functor n).obj η.base
  /-- The map from `η.level n` to the image of `obj` under `φ`. -/
  app : η.level n ⟶ φ.obj obj
  /-- `app` lies over the identity of the `n`-th adic truncation of `η.base`. -/
  app_lift : (BasedCategory.ofFunctor q).p.IsHomLift
    (𝟙 ((AdicTruncation.functor n).obj η.base)) app

/-- One step of the lifting process: a lift at level `n + 1` extending the state `s` at
level `n`, through a map lying over the adic transition map and compatible with `η`. -/
structure CompletionLiftStep
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (η : FormalObject q) (n : ℕ)
    (s : CompletionLiftState φ η n) where
  /-- The lift at level `n + 1`. -/
  next : CompletionLiftState φ η (n + 1)
  /-- The map from the object at level `n + 1` to the object at level `n`. -/
  transition : next.obj ⟶ s.obj
  /-- `transition` lies over the adic transition map from level `n + 1` to level `n`. -/
  transition_lift : (BasedCategory.ofFunctor p).p.IsHomLift
    ((AdicTruncation.transitionNat n).app η.base) transition
  /-- The maps to the images under `φ` are compatible with the transition maps of `η`. -/
  naturality : η.transition n ≫ s.app = next.app ≫ φ.map transition

/-- Smoothness of `φ` extends every such lift one level further: the adic transition map is
surjective, so the smoothness lifting property applies to it. -/
lemma completionLiftStep_exists
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (hq : IsCofiberedInGroupoids q)
    (hφ : IsSmooth φ) (η : FormalObject q) (n : ℕ)
    (s : CompletionLiftState φ η n) : Nonempty (CompletionLiftStep φ η n s) := by
  let A := (AdicTruncation.functor n).obj η.base
  let B := (AdicTruncation.functor (n + 1)).obj η.base
  let f := (AdicTruncation.transitionNat n).app η.base
  let p₀ := (BasedCategory.ofFunctor p).p
  let q₀ := (BasedCategory.ofFunctor q).p
  have hg : q₀.IsHomLift f (η.transition n ≫ s.app) := by
    have : q₀.IsHomLift f (η.transition n) := η.transition_lift n
    have : q₀.IsHomLift (𝟙 A) s.app := s.app_lift
    exact IsHomLift.comp_lift_id_right' q₀ f (η.transition n) A s.app
  have hf : Function.Surjective f.hom := by
    dsimp [f, AdicTruncation.transitionNat, AdicTruncation.transition]
    exact Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  obtain ⟨x, h, a, hh, ha, hcomm⟩ := hφ f hf (η.level (n + 1)) s.obj
    (η.transition n ≫ s.app) hg
  have : p₀.IsHomLift f h := hh
  have hx : p₀.obj x = B := IsHomLift.domain_eq (p := p₀) f h
  have hy : q₀.obj (φ.obj x) = B := by rw [φ.w_obj, hx]
  let i : φ.obj x ≅ η.level (n + 1) := iso_of_vertical q₀ hq a hy (η.level_eq (n + 1)) ha
  have hainv : q₀.IsHomLift (𝟙 B) i.inv := by
    have : q₀.IsHomLift (𝟙 B) i.hom := ha
    exact IsHomLift.lift_id_inv q₀ B i
  refine ⟨⟨⟨x, hx, i.inv, hainv⟩, h, hh, ?_⟩⟩
  rw [hcomm]
  exact (i.inv_hom_id_assoc _).symm

private lemma completionLiftState_zero
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (hq : IsCofiberedInGroupoids q)
    (hφ : IsSmooth φ)
    (h₀ : (fiberFunctor φ (residueFieldObject Λ k)).EssSurj)
    (η : FormalObject q) : Nonempty (CompletionLiftState φ η 0) := by
  let p₀ := (BasedCategory.ofFunctor p).p
  let q₀ := (BasedCategory.ofFunctor q).p
  let A := (AdicTruncation.functor 0).obj η.base
  let K := residueFieldObject.{u, v, w} Λ k
  let resAlg : A →ₐ[Λ] IsLocalRing.ResidueField A :=
    IsScalarTower.toAlgHom Λ A (IsLocalRing.ResidueField A)
  let e : A →ₐ[Λ] ULift.{v} k :=
    (ULift.algEquiv (R := Λ) (A := k)).symm.toAlgHom.comp
      (A.residueEquiv.toAlgHom.comp resAlg)
  let r : A ⟶ K :=
    { hom := e
      isLocal := ⟨fun a ha =>
        (inferInstance : IsLocalHom (IsLocalRing.residue A)).map_nonunit a
          ((MulEquiv.isUnit_map A.residueEquiv).mp
            ((MulEquiv.isUnit_map (ULift.algEquiv (R := Λ) (A := k)).symm).mp ha))⟩
      residue_comm := fun _ => rfl }
  have hr : Function.Surjective r.hom := by
    change Function.Surjective (fun a : A =>
      (ULift.algEquiv (R := Λ) (A := k)).symm (A.residueEquiv (IsLocalRing.residue A a)))
    exact (ULift.algEquiv (R := Λ) (A := k)).symm.surjective.comp
      (A.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A)))
  obtain ⟨y₀op, pushop, hpushop⟩ :=
    hq.exists_lift r.op (Opposite.op (η.level 0)) (congrArg Opposite.op (η.level_eq 0))
  have hpushop' : q₀.op.IsHomLift r.op pushop := hpushop
  let y₀ := Opposite.unop y₀op
  have hy₀ : q₀.obj y₀ = K :=
    congrArg Opposite.unop (IsHomLift.domain_eq (p := q₀.op) r.op pushop)
  let push : η.level 0 ⟶ y₀ := Opposite.unop pushop
  have hpush : q₀.IsHomLift r push := isHomLift_unop q₀ r.op pushop (inst := hpushop')
  let y₀K : Functor.Fiber (BasedCategory.ofFunctor q).p K := ⟨y₀, hy₀⟩
  obtain ⟨x₀, ⟨i⟩⟩ := h₀.mem_essImage y₀K
  let g : η.level 0 ⟶ φ.obj x₀.1 := push ≫ i.inv.val
  have hg : q₀.IsHomLift r g := by
    let : q₀.IsHomLift (𝟙 K) i.inv.val := i.inv.property
    exact IsHomLift.comp_lift_id_right' (p := q₀) r push K i.inv.val
  obtain ⟨x, h, a, hh, ha, hcomm⟩ := hφ r hr (η.level 0) x₀.1 g hg
  have hx : p₀.obj x = A := IsHomLift.domain_eq (p := p₀) r h
  have hy : q₀.obj (φ.obj x) = A := by rw [φ.w_obj, hx]
  let i := iso_of_vertical q₀ hq a hy (η.level_eq 0) ha
  have : q₀.IsHomLift (𝟙 A) i.hom := ha
  exact ⟨⟨x, hx, i.inv, IsHomLift.lift_id_inv q₀ A i⟩⟩

/-- A smooth morphism, essentially surjective over the residue field, is
essentially surjective after completion. -/
@[stacks 06HN "completion_essentially_surjective"]
public theorem completionMap_essSurj_of_isSmooth_of_fiber_essSurj
    {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (hq : IsCofiberedInGroupoids q)
    (hφ : IsSmooth φ)
    (h₀ : (fiberFunctor φ (residueFieldObject Λ k)).EssSurj) :
    (completionMap φ).toFunctor.EssSurj := by
  refine ⟨fun η => ?_⟩
  change FormalObject q at η
  let stepData (n : ℕ) (s : CompletionLiftState φ η n) : CompletionLiftStep φ η n s :=
    Classical.choice (completionLiftStep_exists φ hq hφ η n s)
  let states : (n : ℕ) → CompletionLiftState φ η n :=
    Nat.rec (Classical.choice (completionLiftState_zero φ hq hφ h₀ η))
      (fun n s => (stepData n s).next)
  let ξ : (BasedCategory.ofFunctor (FormalObject.projection (p := p))).obj :=
    { base := η.base
      level := fun n => (states n).obj
      level_eq := fun n => (states n).obj_base
      transition := fun n => (stepData n (states n)).transition
      transition_lift := fun n => (stepData n (states n)).transition_lift }
  let ξform : FormalObject p := ξ
  have hcb : ((completionMap φ).obj ξ).base = η.base := by
    simp [completionMap_obj_base, ξ]
  let appMap (n : ℕ) := (states n).app ≫
    eqToHom (completionMap_obj_level φ ξform n).symm
  let baseMap := eqToHom hcb.symm
  let m : η ⟶ (completionMap φ).obj ξ :=
    { base := baseMap
      app := appMap
      app_lift := fun n => by
        let q₀ := (BasedCategory.ofFunctor q).p
        let hA : q₀.obj (η.level n) = (AdicTruncation.functor n).obj η.base :=
          η.level_eq n
        have hB : q₀.obj (((completionMap φ).obj ξ).level n) =
            (AdicTruncation.functor n).obj
              ((completionMap φ).obj ξ).base := by
          rw [completionMap_obj_level φ ξform n, φ.w_obj,
            (states n).obj_base, completionMap_obj_base φ ξform]
        let : q₀.IsHomLift (𝟙 ((AdicTruncation.functor n).obj η.base))
            (states n).app := (states n).app_lift
        have happfac := IsHomLift.fac' q₀
          (𝟙 ((AdicTruncation.functor n).obj η.base)) (states n).app
        have hmapcomp := q₀.map_comp (states n).app
          (eqToHom (completionMap_obj_level φ ξform n).symm)
        refine IsHomLift.of_fac q₀ ((AdicTruncation.functor n).map baseMap)
          (appMap n) hA hB ?_
        change (AdicTruncation.functor n).map baseMap =
          eqToHom hA.symm ≫ q₀.map (appMap n) ≫ eqToHom hB
        dsimp only [appMap]
        calc
          _ = eqToHom (congrArg (fun R => (AdicTruncation.functor n).obj R) hcb.symm) :=
            eqToHom_map _ _
          _ = eqToHom hA.symm ≫ q₀.map ((states n).app ≫
                eqToHom (completionMap_obj_level φ ξform n).symm) ≫
                eqToHom hB := by
            have hcomp := congrArg (fun g => eqToHom hA.symm ≫ g ≫ eqToHom hB) hmapcomp
            rw [happfac] at hcomp
            simpa [hA, hB, hcb, completionMap_obj_level,
              completionMap_obj_base, ξform, ξ, Category.assoc,
              eqToHom_trans_assoc, eqToHom_map] using hcomp.symm
      naturality := fun n => by
        have hn := congrArg (fun t => t ≫
          eqToHom (completionMap_obj_level φ ξform n).symm)
          (stepData n (states n)).naturality
        simpa [appMap, completionMap_obj_transition,
          completionMap_obj_level, Category.assoc] using hn }
  let π := FormalObject.projection (p := q)
  have hπ : IsCofiberedInGroupoids π :=
    formalObjectProjection_isCofiberedInGroupoids q hq
  have hm : π.IsHomLift (𝟙 η.base) m := by
    apply IsHomLift.of_fac π (𝟙 η.base) m rfl hcb ?_
    simp [π, m, baseMap, FormalObject.projection]
  have hTargetBase : π.obj ((completionMap φ).obj ξ) = η.base := by
    simpa [π] using hcb
  let i : η ≅ (completionMap φ).obj ξ :=
    iso_of_vertical π hπ m rfl hTargetBase hm
  exact ⟨ξform, ⟨i.symm⟩⟩

end

end Deformation
