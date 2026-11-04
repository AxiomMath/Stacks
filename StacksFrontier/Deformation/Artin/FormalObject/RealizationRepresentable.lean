module

public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationRepresentable
public import StacksFrontier.Deformation.Artin.FormalObject.SmoothLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity

/-!
# Realizations for represented categories, and along 1-morphisms

Two steps of the essential surjectivity in **Stacks 07X8**.

* **Case I**: every formal object of the category fibred in groupoids `(Sch/X)_{fppf}`
  represented by an object `X` of the site, whose complete local base belongs to the site, is
  realized. A formal object of `(Sch/X)_{fppf}` is a compatible system of morphisms
  `Spec(R/𝔪^{n+1}) ⟶ X`, and by completeness of `R` it comes from a unique morphism
  `Spec R ⟶ X` (`Deformation.Artin.exists_lift_of_adicThickening`, a case of Stacks 0AQG).
* Realizations are carried along a 1-morphism of categories fibred in groupoids.

## Main results

* `Deformation.Artin.FormalObject.exists_realization_overForget`: Case I.
* `Deformation.Artin.FormalObject.Realization.map`: the image of a realization under a
  1-morphism realizes the image of the formal object.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- A realization from arrows lying over the inclusions of the thickenings. -/
def FormalObject.Realization.ofIsHomLift (ξ : FormalObject B S hS p)
    (hA : B.Contains (Spec (.of ξ.base.R))) {x : F} (hx : p.obj x = baseOver B S hS ξ.base hA)
    (r : ∀ n, ξ.level n ⟶ x)
    (hr : ∀ n, p.IsHomLift (restrictionToBase B S hS ξ.base hA ξ.contains n) (r n))
    (hrt : ∀ n, ξ.transition n ≫ r (n + 1) = r n) : ξ.Realization hA x hx where
  r := r
  comp_transition := hrt
  map_eq n := by
    have := hr n
    rw [IsHomLift.fac' p (restrictionToBase B S hS ξ.base hA ξ.contains n) (r n)]

/-- Each arrow `R.r n` of a realization lies over the inclusion of the `n`-th thickening into
the base. -/
theorem FormalObject.Realization.isHomLift {ξ : FormalObject B S hS p}
    {hA : B.Contains (Spec (.of ξ.base.R))} {x : F} {hx : p.obj x = baseOver B S hS ξ.base hA}
    (R : ξ.Realization hA x hx) (n : ℕ) :
    p.IsHomLift (restrictionToBase B S hS ξ.base hA ξ.contains n) (R.r n) :=
  IsHomLift.of_fac' _ _ _ (ξ.level_eq n) hx (R.map_eq n)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Case I of Stacks 07X8.** Every formal object of the category fibred in groupoids represented
by an object `Xo` of the big fppf site, whose complete local base belongs to the site, is realized
by an object over that base. -/
theorem FormalObject.exists_realization_overForget (Xo : BigFppfOver B S hS)
    (ζ : FormalObject B S hS (Over.forget Xo)) (hA : B.Contains (Spec (.of ζ.base.R))) :
    ∃ (x : Over Xo) (hx : (Over.forget Xo).obj x = baseOver B S hS ζ.base hA),
      Nonempty (ζ.Realization hA x hx) := by
  classical
  have : IsAdicComplete (maximalIdeal ζ.base.R) ζ.base.R := ζ.base.complete
  let a : ∀ n, truncationOver B S hS ζ.base ζ.contains n ⟶ Xo := fun n =>
    eqToHom (ζ.level_eq n).symm ≫ (ζ.level n).hom
  have htl : ∀ n, (ζ.transition n).left = eqToHom (ζ.level_eq n) ≫
      truncationOverSucc B S hS ζ.base ζ.contains n ≫ eqToHom (ζ.level_eq (n + 1)).symm :=
    fun n => by
      have := ζ.transition_lift n
      exact IsHomLift.fac' (Over.forget Xo) _ (ζ.transition n)
  have ha : ∀ n, truncationOverSucc B S hS ζ.base ζ.contains n ≫ a (n + 1) = a n := fun n => by
    simp only [a]
    rw [← Over.w (ζ.transition n), htl]
    simp
  let a' : ∀ n, ζ.base.truncation n ⟶ (BigFppfOver.toScheme B S hS).obj Xo := fun n =>
    (BigFppfOver.toScheme B S hS).map (a n)
  have haS : ∀ n, a' n ≫ B.inclusion.map Xo.hom = ζ.base.truncationToS n := fun n =>
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w (a n)))
  have ha' : ∀ n, adicThickeningSucc ζ.base.R (maximalIdeal ζ.base.R) n ≫ a' (n + 1) = a' n :=
    fun n =>
      (Functor.map_comp _ _ _).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map (ha n))
  obtain ⟨bm, hbm⟩ := exists_lift_of_adicThickening (R := ζ.base.R) a' ha'
  have hbmS : bm ≫ B.inclusion.map Xo.hom = ζ.base.toS := by
    refine hom_ext_of_adicThickening (R := ζ.base.R) fun n => ?_
    rw [← Category.assoc, hbm n]
    exact haS n
  let xh : baseOver B S hS ζ.base hA ⟶ Xo :=
    Over.homMk (ObjectProperty.homMk (X := B.obj hA) bm) (by
      apply ObjectProperty.hom_ext; exact hbmS)
  let x : Over Xo := Over.mk xh
  have hrtb : ∀ n, restrictionToBase B S hS ζ.base hA ζ.contains n ≫ x.hom = a n := fun n =>
    (BigFppfOver.toScheme B S hS).map_injective (hbm n)
  refine ⟨x, rfl, ⟨FormalObject.Realization.ofIsHomLift ζ hA rfl
    (fun n => Over.homMk (eqToHom (ζ.level_eq n) ≫
      restrictionToBase B S hS ζ.base hA ζ.contains n) (by
        rw [Category.assoc, hrtb]; simp [a])) (fun n => ?_) (fun n => ?_)⟩⟩
  · refine IsHomLift.of_fac' _ _ _ (ζ.level_eq n) rfl ?_
    show eqToHom (ζ.level_eq n) ≫ restrictionToBase B S hS ζ.base hA ζ.contains n = _
    simp
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, htl, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [restrictionToBase_succ]

/-- **Realizations are carried along 1-morphisms.** -/
def FormalObject.Realization.map
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (P : 𝒳 ⟶ 𝒴)
    {ξ : FormalObject B S hS 𝒳.val.p} {hA : B.Contains (Spec (.of ξ.base.R))} {x : 𝒳.val.obj}
    {hx : 𝒳.val.p.obj x = baseOver B S hS ξ.base hA} (R : ξ.Realization hA x hx) :
    (FormalObject.map B S hS 𝒳 𝒴 P ξ).Realization hA ((CatFiberedInGroupoids.homFunctor P).obj x)
      ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p P) x).trans hx) :=
  FormalObject.Realization.ofIsHomLift (FormalObject.map B S hS 𝒳 𝒴 P ξ) hA _
    (fun n => (CatFiberedInGroupoids.homFunctor P).map (R.r n))
    (fun n => by
      have := R.isHomLift n
      exact BasedFunctor.preserves_isHomLift P.hom
        (restrictionToBase B S hS ξ.base hA ξ.contains n) (R.r n))
    (fun n => by
      change (CatFiberedInGroupoids.homFunctor P).map (ξ.transition n) ≫
        (CatFiberedInGroupoids.homFunctor P).map (R.r (n + 1)) = _
      rw [← Functor.map_comp, R.comp_transition])

end Deformation.Artin

end
