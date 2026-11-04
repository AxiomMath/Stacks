module

public import StacksFrontier.Deformation.Formal.MinimalVersal.CofiberedPushforward

/-!
# The formal object attached to an object over an Artinian base

An object `Y` lying over an Artinian local algebra `A` gives a formal object over `A` viewed as a
complete local algebra: push `Y` forward along the projections of `A` onto its own adic
truncations. The construction is functorial in `Y`, and a formal object maps canonically to the
formal object attached to its zeroth level.

## Main definitions

* `Deformation.artinianFormalizationLevel`: the `n`-th level of the formal object attached to an
  object `Y` lying over an Artinian local algebra: the pushforward of `Y` along the projection onto
  the `n`-th adic truncation.
* `Deformation.artinianFormalizationInclusion`: the arrow from `Y` to the `n`-th level of its
  attached formal object.
* `Deformation.artinianFormalizationTransition`: the transition morphism between consecutive
  levels of the formal object attached to `Y`.
* `Deformation.artinianFormalization`: the formal object attached to an object lying over an
  Artinian local algebra, obtained by pushing it forward along the projections onto the adic
  truncations of its base.
* `Deformation.formalResidueBaseMap`: the morphism from the base of a formal object to the
  Artinian local algebra under its zeroth level, regarded as a complete local algebra.
* `Deformation.versalInitialFormalizationMap`: the canonical morphism from a formal object to the
  formal object attached to its zeroth level.
* `Deformation.artinianFormalizationMap`: the morphism of formal objects induced by a morphism of
  the objects they are attached to.

## Main results

* `Deformation.artinianFormalizationInclusion_lift`: the arrow from `Y` to the `n`-th level of its
  formal object lies over the projection onto the `n`-th adic truncation.
* `Deformation.artinianFormalizationTransition_lift`: the transition morphisms of the formal
  object attached to `Y` lie over the truncation transitions.
* `Deformation.artinianFormalizationInclusion_fac`: the arrows from `Y` into the levels of its
  formal object are compatible with the transition morphisms.
* `Deformation.formalResidueBaseMap_trunc_fac`: `formalResidueBaseMap` is compatible with the
  projections onto the adic truncations of the zeroth level.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


/-- The pushforward arrow to the `n`-th level lies over the `(n + 1)`-st adic projection followed by
the truncation transition. -/
private theorem pushforwardMap_lift_quotient_comp_transition
    (hp : IsCofiberedInGroupoids p) (Y : F) (n : ℕ) :
    p.IsHomLift (artinianAdicQuotient (p.obj Y) (n + 1) ≫
      AdicTruncation.transition (artinianToComplete.obj (p.obj Y)) n)
      (cofiberedPushforwardMap hp (artinianAdicQuotient (p.obj Y) n) Y rfl) := by
  have hq := artinianAdicQuotient_transition (p.obj Y) n
  let := cofiberedPushforwardMap_lift hp (artinianAdicQuotient (p.obj Y) n) Y rfl
  exact hq ▸ cofiberedPushforwardMap_lift hp (artinianAdicQuotient (p.obj Y) n) Y rfl

section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- The `n`-th level of the formal object attached to an object `Y` lying over an Artinian local
algebra: the pushforward of `Y` along the projection onto the `n`-th adic truncation. -/
noncomputable def artinianFormalizationLevel
    (hp : IsCofiberedInGroupoids p) (Y : F) (n : ℕ) : F :=
  cofiberedPushforwardObj hp (artinianAdicQuotient (p.obj Y) n) Y rfl

/-- The arrow from `Y` to the `n`-th level of its attached formal object. -/
noncomputable def artinianFormalizationInclusion
    (hp : IsCofiberedInGroupoids p) (Y : F) (n : ℕ) :
    Y ⟶ artinianFormalizationLevel hp Y n :=
  cofiberedPushforwardMap hp (artinianAdicQuotient (p.obj Y) n) Y rfl

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The arrow from `Y` to the `n`-th level of its formal object lies over the projection onto the
`n`-th adic truncation. -/
theorem artinianFormalizationInclusion_lift
    (hp : IsCofiberedInGroupoids p) (Y : F) (n : ℕ) :
    p.IsHomLift (artinianAdicQuotient (p.obj Y) n)
      (artinianFormalizationInclusion hp Y n) :=
  cofiberedPushforwardMap_lift hp (artinianAdicQuotient (p.obj Y) n) Y rfl

/-- The transition morphism between consecutive levels of the formal object attached to `Y`. -/
noncomputable def artinianFormalizationTransition
    (hp : IsCofiberedInGroupoids p) (Y : F) (n : ℕ) :
    artinianFormalizationLevel hp Y (n + 1) ⟶ artinianFormalizationLevel hp Y n :=
  cofiberedPushforwardDesc hp (artinianAdicQuotient (p.obj Y) (n + 1))
    (AdicTruncation.transition (artinianToComplete.obj (p.obj Y)) n)
    Y (artinianFormalizationLevel hp Y n) rfl (artinianFormalizationInclusion hp Y n)
    (by
      have hq := artinianAdicQuotient_transition (p.obj Y) n
      let := artinianFormalizationInclusion_lift hp Y n
      exact hq ▸ cofiberedPushforwardMap_lift hp (artinianAdicQuotient (p.obj Y) n) Y rfl)

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The transition morphisms of the formal object attached to `Y` lie over the truncation
transitions. -/
theorem artinianFormalizationTransition_lift
    (hp : IsCofiberedInGroupoids p) (Y : F) (n : ℕ) :
    p.IsHomLift
      (AdicTruncation.transition (artinianToComplete.obj (p.obj Y)) n)
      (artinianFormalizationTransition hp Y n) :=
  cofiberedPushforwardDesc_lift hp (artinianAdicQuotient (p.obj Y) (n + 1))
    (AdicTruncation.transition (artinianToComplete.obj (p.obj Y)) n)
    Y (artinianFormalizationLevel hp Y n) rfl (artinianFormalizationInclusion hp Y n)
    (pushforwardMap_lift_quotient_comp_transition hp Y n)

/-- The formal object attached to an object lying over an Artinian local algebra, obtained by
pushing it forward along the projections onto the adic truncations of its base. -/
noncomputable def artinianFormalization
    (hp : IsCofiberedInGroupoids p) (Y : F) : FormalObject p where
  base := artinianToComplete.obj (p.obj Y)
  level := artinianFormalizationLevel hp Y
  level_eq := fun n => cofiberedPushforwardObj_eq hp
    (artinianAdicQuotient (p.obj Y) n) Y rfl
  transition := artinianFormalizationTransition hp Y
  transition_lift := artinianFormalizationTransition_lift hp Y

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The arrows from `Y` into the levels of its formal object are compatible with the transition
morphisms. -/
theorem artinianFormalizationInclusion_fac
    (hp : IsCofiberedInGroupoids p) (Y : F) (n : ℕ) :
    artinianFormalizationInclusion hp Y (n + 1) ≫
      artinianFormalizationTransition hp Y n =
        artinianFormalizationInclusion hp Y n :=
  cofiberedPushforwardDesc_fac hp
    (artinianAdicQuotient (p.obj Y) (n + 1))
    (AdicTruncation.transition (artinianToComplete.obj (p.obj Y)) n)
    Y (artinianFormalizationLevel hp Y n) rfl
    (artinianFormalizationInclusion hp Y n)
    (pushforwardMap_lift_quotient_comp_transition hp Y n)

/-- The morphism from the base of a formal object to the Artinian local algebra under its zeroth
level, regarded as a complete local algebra. -/
noncomputable def formalResidueBaseMap (ξ : FormalObject p) :
    ξ.base ⟶ artinianToComplete.obj (p.obj (ξ.level 0)) := by
  let I := AdicTruncation.ideal ξ.base 0
  let q : ξ.base →ₐ[Λ] AdicTruncation.obj ξ.base 0 := Ideal.Quotient.mkₐ Λ I
  let e : AdicTruncation.obj ξ.base 0 ⟶ p.obj (ξ.level 0) :=
    eqToHom (ξ.level_eq 0).symm
  let φ := e.hom.comp q
  letI : IsIso e := inferInstance
  have heSurj : Function.Surjective e.hom := artinianHom_surjective_of_isIso e
  refine
    { hom := φ
      isLocal := IsLocalHom.of_surjective φ.toRingHom
        (heSurj.comp Ideal.Quotient.mk_surjective)
      residue_comm := ?_ }
  intro r
  have hq : AdicTruncation.residueEquiv ξ.base 0
      (residue (AdicTruncation.obj ξ.base 0) (q r)) =
      ξ.base.residueEquiv (residue ξ.base r) :=
    AdicTruncation.residueEquiv_residue_mk ξ.base 0 r
  have he := e.residue_comm (q r)
  change (p.obj (ξ.level 0)).residueEquiv
      (residue (p.obj (ξ.level 0)) (e.hom (q r))) =
    ξ.base.residueEquiv (residue ξ.base r)
  exact he.trans hq

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `formalResidueBaseMap` is compatible with the projections onto the adic truncations of the
zeroth level. -/
theorem formalResidueBaseMap_trunc_fac
    (ξ : FormalObject p) (n : ℕ) :
    formalTransitionToZeroBase ξ n ≫
        eqToHom (ξ.level_eq 0).symm ≫
        artinianAdicQuotient (p.obj (ξ.level 0)) n =
      (AdicTruncation.functor n).map (formalResidueBaseMap ξ) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [adicTruncationMap_mk]
  change (artinianAdicQuotient (p.obj (ξ.level 0)) n).hom
      ((eqToHom (ξ.level_eq 0).symm).hom
        ((formalTransitionToZeroBase ξ n).hom
          (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r :
            AdicTruncation.obj ξ.base n))) =
    Ideal.Quotient.mk _ ((formalResidueBaseMap ξ).hom r)
  rw [formalTransitionToZeroBase_mk]
  rfl

/-- The canonical morphism from a formal object to the formal object attached to its zeroth level.
The canonical morphism from a formal object to the formal object attached to its zeroth level. -/
noncomputable def versalInitialFormalizationMap
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :
    FormalObject.Hom ξ (artinianFormalization hp (ξ.level 0)) := by
  let app (n : ℕ) := formalTransitionToZero ξ n ≫
    artinianFormalizationInclusion hp (ξ.level 0) n
  refine
    { base := formalResidueBaseMap ξ
      app := app
      app_lift := fun n => ?_
      naturality := fun n => ?_ }
  · have hleft := formalTransitionToZero_lift ξ n
    have hmid : p.IsHomLift (eqToHom (ξ.level_eq 0).symm)
        (𝟙 (ξ.level 0)) :=
      IsHomLift.id_lift_eqToHom_domain (ξ.level_eq 0).symm (ξ.level_eq 0)
    have hright := artinianFormalizationInclusion_lift hp (ξ.level 0) n
    let := hleft
    let := hmid
    let := hright
    have hcomp : p.IsHomLift
        (formalTransitionToZeroBase ξ n ≫
          eqToHom (ξ.level_eq 0).symm ≫
          artinianAdicQuotient (p.obj (ξ.level 0)) n) (app n) := inferInstance
    exact (formalResidueBaseMap_trunc_fac ξ n).symm ▸ hcomp
  · dsimp [app]
    calc
      ξ.transition n ≫
          (formalTransitionToZero ξ n ≫
            artinianFormalizationInclusion hp (ξ.level 0) n) =
        (ξ.transition n ≫ formalTransitionToZero ξ n) ≫
          artinianFormalizationInclusion hp (ξ.level 0) n := by
            simp only [Category.assoc]
      _ = formalTransitionToZero ξ (n + 1) ≫
          artinianFormalizationInclusion hp (ξ.level 0) (n + 1) ≫
          artinianFormalizationTransition hp (ξ.level 0) n := by
            rw [formalTransitionToZero, artinianFormalizationInclusion_fac]
      _ = (formalTransitionToZero ξ (n + 1) ≫
          artinianFormalizationInclusion hp (ξ.level 0) (n + 1)) ≫
          artinianFormalizationTransition hp (ξ.level 0) n := by
            simp only [Category.assoc]

/-- The morphism of formal objects induced by a morphism of the objects they are attached to. -/
noncomputable def artinianFormalizationMap
    (hp : IsCofiberedInGroupoids p) {Y Z : F} (f : Y ⟶ Z) :
    FormalObject.Hom (artinianFormalization hp Y) (artinianFormalization hp Z) := by
  let α := p.map f
  let β (n : ℕ) := (AdicTruncation.functor n).map
    (artinianToComplete.map α)
  let qY (n : ℕ) := artinianAdicQuotient (p.obj Y) n
  let qZ (n : ℕ) := artinianAdicQuotient (p.obj Z) n
  let incZ (n : ℕ) := artinianFormalizationInclusion hp Z n
  have hψ (n : ℕ) : p.IsHomLift (qY n ≫ β n) (f ≫ incZ n) := by
    let : p.IsHomLift α f := IsHomLift.of_fac p α f rfl rfl (by simp [α])
    let := artinianFormalizationInclusion_lift hp Z n
    have hcomp : p.IsHomLift (α ≫ qZ n) (f ≫ incZ n) := inferInstance
    exact (artinianAdicQuotient_naturality α n).symm ▸ hcomp
  let app (n : ℕ) := cofiberedPushforwardDesc hp (qY n) (β n) Y
    (artinianFormalizationLevel hp Z n) rfl (f ≫ incZ n) (hψ n)
  have app_lift (n : ℕ) : p.IsHomLift (β n) (app n) :=
    cofiberedPushforwardDesc_lift hp (qY n) (β n) Y
      (artinianFormalizationLevel hp Z n) rfl (f ≫ incZ n) (hψ n)
  have app_fac (n : ℕ) :
      artinianFormalizationInclusion hp Y n ≫ app n = f ≫ incZ n :=
    cofiberedPushforwardDesc_fac hp (qY n) (β n) Y
      (artinianFormalizationLevel hp Z n) rfl (f ≫ incZ n) (hψ n)
  refine
    { base := artinianToComplete.map α
      app := app
      app_lift := app_lift
      naturality := fun n => ?_ }
  let τY := AdicTruncation.transition (artinianToComplete.obj (p.obj Y)) n
  let τZ := AdicTruncation.transition (artinianToComplete.obj (p.obj Z)) n
  have hβ : β (n + 1) ≫ τZ = τY ≫ β n := by
    dsimp [β, τY, τZ]
    exact (AdicTruncation.transitionNat n).naturality
      (artinianToComplete.map α)
  have hl : p.IsHomLift (τY ≫ β n)
      (artinianFormalizationTransition hp Y n ≫ app n) :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ τY (β n)
      (artinianFormalizationTransition hp Y n) (app n)
      (artinianFormalizationTransition_lift hp Y n) (app_lift n)
  have hr : p.IsHomLift (τY ≫ β n)
      (app (n + 1) ≫ artinianFormalizationTransition hp Z n) := by
    let : p.IsHomLift (β (n + 1)) (app (n + 1)) := app_lift (n + 1)
    let : p.IsHomLift τZ (artinianFormalizationTransition hp Z n) :=
      artinianFormalizationTransition_lift hp Z n
    have hcomp : p.IsHomLift (β (n + 1) ≫ τZ)
        (app (n + 1) ≫ artinianFormalizationTransition hp Z n) := inferInstance
    exact hβ ▸ hcomp
  let : p.IsStronglyCocartesian (qY (n + 1))
      (artinianFormalizationInclusion hp Y (n + 1)) :=
    cofibered_pushforward_isCocartesian hp (qY (n + 1)) Y rfl
  refine @Functor.IsStronglyCocartesian.ext _ _ _ _ p _ _ _ _
    (qY (n + 1)) (artinianFormalizationInclusion hp Y (n + 1)) inferInstance
    _ _ (τY ≫ β n) _ _ hl hr ?_
  calc
    artinianFormalizationInclusion hp Y (n + 1) ≫
        (artinianFormalizationTransition hp Y n ≫ app n) =
      (artinianFormalizationInclusion hp Y (n + 1) ≫
        artinianFormalizationTransition hp Y n) ≫ app n :=
          (Category.assoc _ _ _).symm
    _ = artinianFormalizationInclusion hp Y n ≫ app n := by
      rw [artinianFormalizationInclusion_fac hp Y n]
    _ = f ≫ artinianFormalizationInclusion hp Z n :=
      app_fac n
    _ = f ≫ (artinianFormalizationInclusion hp Z (n + 1) ≫
        artinianFormalizationTransition hp Z n) :=
          congrArg (fun t => f ≫ t)
            (artinianFormalizationInclusion_fac hp Z n).symm
    _ = (f ≫ artinianFormalizationInclusion hp Z (n + 1)) ≫
        artinianFormalizationTransition hp Z n := (Category.assoc _ _ _).symm
    _ = (artinianFormalizationInclusion hp Y (n + 1) ≫ app (n + 1)) ≫
        artinianFormalizationTransition hp Z n :=
          congrArg (fun t => t ≫ artinianFormalizationTransition hp Z n)
            (app_fac (n + 1)).symm
    _ = artinianFormalizationInclusion hp Y (n + 1) ≫
        (app (n + 1) ≫ artinianFormalizationTransition hp Z n) :=
          Category.assoc _ _ _

end

end Deformation

end
