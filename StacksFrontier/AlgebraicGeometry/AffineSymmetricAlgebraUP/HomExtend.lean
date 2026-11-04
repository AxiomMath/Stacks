module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Transport

/-!
# Extension of a morphism of presheaves of modules along a locally bijective comparison

`Stacks.BilinearMap.extend` extends a *bilinear* map of presheaves of modules along a locally
bijective morphism in its first variable, when the target is a sheaf. **This file is the unary
form of that statement**: a morphism `φ : F ⟶ S` of presheaves of modules whose target is a
sheaf factors uniquely through a locally bijective comparison `w : F ⟶ T`.

## Main definitions

* `Stacks.extendHomVal`: the value of the extension at a local section of `T`, the unique
  section of `S` whose restriction along each local lift is the `φ`-image of that lift.
* `Stacks.homExtend`: the extension itself.

## Main results

* `Stacks.existsUnique_extendVal`: the gluing step — the local sections `φ x` attached to the
  local lifts `x` of a section of `T` amalgamate uniquely.
* `Stacks.homExtend_comparison` and `Stacks.comp_homExtend`: the extension restricts to `φ`
  along `w`.
* `Stacks.hom_eq_of_comp_eq`: a morphism out of `T` into a separated presheaf of modules is
  determined by its restriction along a locally surjective comparison.
* `Stacks.existsUnique_homExtend`: **the universal property**, in `∃!` form.

## Implementation notes

The proofs are those of `Stacks.BilinearMap.extendVal` and its laws, with the second variable
deleted; the bilinear statement is not specialized to a rank-one second variable instead,
because the two scalar laws of a `Stacks.BilinearMap` force the scalars acting on the target to
commute and the base here is a presheaf of possibly noncommutative rings.

Separatedness of the target suffices for uniqueness (`Stacks.hom_eq_of_comp_eq`), and only the
existence half needs the full sheaf condition, which is where the amalgamation over the sieve of
local lifts happens.

## References

* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PresheafOfModules

universe v u t a

namespace Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ RingCat.{t}}
  {F T S : PresheafOfModules.{a} R}

section Separated

variable (hS : Presheaf.IsSeparated J S.presheaf) (w : F ⟶ T) (φ : F ⟶ S)
include hS

/-- A morphism into a separated presheaf of modules only depends on the image of its argument
under a locally injective morphism. -/
theorem app_eq_of_isLocallyInjective [PresheafOfModules.IsLocallyInjective J w] {X : Cᵒᵖ}
    (x x' : F.obj X) (hx : Hom.app w X x = Hom.app w X x') :
    Hom.app φ X x = Hom.app φ X x' := by
  refine hS _ _ (Presheaf.equalizerSieve_mem J ((toPresheaf _).map w) x x' hx) _ _ ?_
  intro Y f hf
  show S.map f.op _ = S.map f.op _
  rw [← naturality_apply φ f.op, ← naturality_apply φ f.op]
  exact congrArg (Hom.app φ (op Y)) (show F.map f.op x = F.map f.op x' from hf)

end Separated

section Extend

variable (hS : Presheaf.IsSheaf J S.presheaf) (w : F ⟶ T)
  [PresheafOfModules.IsLocallySurjective J w] [PresheafOfModules.IsLocallyInjective J w]
  (φ : F ⟶ S)
include hS

/-- **The gluing step.** The `φ`-images of the local lifts of a section of `T` form a compatible
family, and so amalgamate to a unique section of `S`. -/
theorem existsUnique_extendVal {X : Cᵒᵖ} (t : T.obj X) :
    ∃! z : S.obj X, ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y),
      Hom.app w Y x = T.map f t → S.map f z = Hom.app φ Y x := by
  set ψ := (toPresheaf R).map w
  set Sv := Presheaf.imageSieve ψ t with hSv
  have hSmem : Sv ∈ J X.unop := Presheaf.imageSieve_mem J ψ t
  have hStype : Presheaf.IsSheaf J (S.presheaf ⋙ forget AddCommGrpCat.{a}) :=
    ((sheafCompose J (forget AddCommGrpCat.{a})).obj ⟨S.presheaf, hS⟩).2
  choose x hx using fun (Y : C) (f : Y ⟶ X.unop) (hf : Sv f) => imageSieve_apply w t f hf
  have hfam : Presieve.FamilyOfElements.Compatible
      (P := S.presheaf ⋙ forget AddCommGrpCat.{a}) (R := Sv.arrows)
      (fun Y f hf => Hom.app φ (op Y) (x Y f hf)) := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    show S.map g₁.op (Hom.app φ (op Y₁) (x Y₁ f₁ h₁)) =
      S.map g₂.op (Hom.app φ (op Y₂) (x Y₂ f₂ h₂))
    rw [← naturality_apply φ g₁.op, ← naturality_apply φ g₂.op]
    refine app_eq_of_isLocallyInjective hS.isSeparated w φ _ _ ?_
    rw [naturality_apply w g₁.op, naturality_apply w g₂.op, hx, hx,
      ← T.map_comp_apply, ← T.map_comp_apply, ← op_comp, ← op_comp, fac]
  have key : ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (x₀ : F.obj Y), Hom.app w Y x₀ = T.map f t →
      S.map f ((hStype.isSheafFor Sv hSmem).amalgamate _ hfam) = Hom.app φ Y x₀ := by
    intro Y f x₀ hx₀
    have hf : Sv f.unop := ⟨x₀, hx₀⟩
    rw [show S.map f ((hStype.isSheafFor Sv hSmem).amalgamate _ hfam) =
        Hom.app φ Y (x _ f.unop hf) from
      (hStype.isSheafFor Sv hSmem).isAmalgamation hfam f.unop hf]
    exact app_eq_of_isLocallyInjective hS.isSeparated w φ _ x₀
      ((hx _ f.unop hf).trans hx₀.symm)
  refine ⟨(hStype.isSheafFor Sv hSmem).amalgamate _ hfam, fun f x₀ hx₀ => key f x₀ hx₀,
    fun z hz => ?_⟩
  refine eq_of_forall_lift hS.isSeparated w t _ _ fun {Y} f x₀ hx₀ => ?_
  rw [hz f x₀ hx₀, key f x₀ hx₀]

/-- The value of the extension of `φ` along `w` at a local section of `T`. -/
def extendHomVal {X : Cᵒᵖ} (t : T.obj X) : S.obj X := (existsUnique_extendVal hS w φ t).choose

/-- The restriction of `extendHomVal hS w φ t` along `f` is the `φ`-image of any lift along `w` of
the restriction of `t`. -/
theorem map_extendHomVal {X Y : Cᵒᵖ} (t : T.obj X) (f : X ⟶ Y) (x : F.obj Y)
    (hx : Hom.app w Y x = T.map f t) :
    S.map f (extendHomVal hS w φ t) = Hom.app φ Y x :=
  (existsUnique_extendVal hS w φ t).choose_spec.1 f x hx

/-- A section of `S` whose restriction along every morphism is the `φ`-image of each lift along `w`
of the restriction of `t` equals `extendHomVal hS w φ t`. -/
theorem eq_extendHomVal {X : Cᵒᵖ} (t : T.obj X) (z : S.obj X)
    (hz : ∀ {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y),
      Hom.app w Y x = T.map f t → S.map f z = Hom.app φ Y x) :
    z = extendHomVal hS w φ t :=
  (existsUnique_extendVal hS w φ t).choose_spec.2 z hz

/-- On the image of `w`, the extension takes the value of `φ`. -/
@[simp]
theorem extendHomVal_comparison {X : Cᵒᵖ} (x : F.obj X) :
    extendHomVal hS w φ (Hom.app w X x) = Hom.app φ X x := by
  refine (eq_extendHomVal hS w φ _ _ fun {Y} f x' hx' => ?_).symm
  rw [← naturality_apply φ f x]
  exact app_eq_of_isLocallyInjective hS.isSeparated w φ _ x'
    ((naturality_apply w f x).trans hx'.symm)

/-- `extendHomVal` is additive. -/
theorem extendHomVal_add {X : Cᵒᵖ} (t t' : T.obj X) :
    extendHomVal hS w φ (t + t') = extendHomVal hS w φ t + extendHomVal hS w φ t' := by
  refine eq_of_forall_lift₂ hS.isSeparated w t t' _ _ fun {Y} f x x' hx hx' => ?_
  have hsum : Hom.app w Y (x + x') = T.map f (t + t') := by
    rw [map_add, hx, hx']
    exact (map_add (ConcreteCategory.hom (T.map f)) t t').symm
  rw [map_extendHomVal hS w φ _ f _ hsum, map_add (ConcreteCategory.hom (S.map f)),
    map_extendHomVal hS w φ t f x hx, map_extendHomVal hS w φ t' f x' hx']
  exact map_add (ConcreteCategory.hom (Hom.app φ Y)) x x'

/-- `extendHomVal` commutes with the action of `R`. -/
theorem extendHomVal_smul {X : Cᵒᵖ} (r : R.obj X) (t : T.obj X) :
    extendHomVal hS w φ (r • t) = r • extendHomVal hS w φ t := by
  refine eq_of_forall_lift hS.isSeparated w t _ _ fun {Y} f x hx => ?_
  have hsm : Hom.app w Y (R.map f r • x) = T.map f (r • t) := by
    rw [map_smul, hx]
    exact (T.map_smul f r t).symm
  rw [map_extendHomVal hS w φ _ f _ hsm, S.map_smul f r (extendHomVal hS w φ t),
    map_extendHomVal hS w φ t f x hx]
  exact map_smul (ConcreteCategory.hom (Hom.app φ Y)) _ x

/-- `extendHomVal` commutes with the restriction maps of `T` and `S`. -/
theorem extendHomVal_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : T.obj X) :
    S.map f (extendHomVal hS w φ t) = extendHomVal hS w φ (X := Y) (T.map f t) := by
  refine eq_extendHomVal hS w φ (X := Y) (T.map f t) _ fun {Z} g x hx => ?_
  have hx' : Hom.app w Z x = T.map (f ≫ g) t := by rw [hx, T.map_comp_apply]
  rw [← S.map_comp_apply]
  exact map_extendHomVal hS w φ t (f ≫ g) x hx'

/-- **The extension of a morphism of presheaves of modules along a locally bijective
comparison.** -/
def homExtend : T ⟶ S where
  app _ := ModuleCat.ofHom
    { toFun := extendHomVal hS w φ
      map_add' := extendHomVal_add hS w φ
      map_smul' := extendHomVal_smul hS w φ }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun t =>
    (extendHomVal_naturality hS w φ f t).symm)

/-- The component of `homExtend hS w φ` at `X` sends `t` to `extendHomVal hS w φ t`. -/
theorem homExtend_app {X : Cᵒᵖ} (t : T.obj X) :
    Hom.app (homExtend hS w φ) X t = extendHomVal hS w φ t := rfl

/-- The extension restricts to `φ` along the comparison. -/
theorem homExtend_comparison (X : Cᵒᵖ) (x : F.obj X) :
    Hom.app (homExtend hS w φ) X (Hom.app w X x) = Hom.app φ X x :=
  extendHomVal_comparison hS w φ x

/-- The composite of `w` with the extension `homExtend hS w φ` is `φ`. -/
theorem comp_homExtend : w ≫ homExtend hS w φ = φ :=
  PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => homExtend_comparison hS w φ X x)

end Extend

section Unique

variable (hS : Presheaf.IsSeparated J S.presheaf) (w : F ⟶ T)
  [PresheafOfModules.IsLocallySurjective J w]
include hS

/-- A morphism out of `T` into a separated presheaf of modules is determined by its restriction
along a locally surjective comparison. -/
theorem hom_eq_of_comp_eq {h h' : T ⟶ S} (hh : w ≫ h = w ≫ h') : h = h' := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  refine eq_of_forall_lift hS w t _ _ fun {Y} f x hx => ?_
  rw [← naturality_apply h f t, ← naturality_apply h' f t, ← hx]
  exact congrArg (fun q : F ⟶ S => Hom.app q Y x) hh

/-- The sectionwise form of `Stacks.hom_eq_of_comp_eq`. -/
theorem hom_eq_of_app_eq {h h' : T ⟶ S}
    (hh : ∀ (X : Cᵒᵖ) (x : F.obj X), Hom.app h X (Hom.app w X x) = Hom.app h' X (Hom.app w X x)) :
    h = h' :=
  hom_eq_of_comp_eq hS w (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => hh X x))

end Unique

/-- **The universal property of a locally bijective comparison.** A morphism of presheaves of
modules into a sheaf factors uniquely through a locally bijective comparison. -/
theorem existsUnique_homExtend (hS : Presheaf.IsSheaf J S.presheaf) (w : F ⟶ T)
    [PresheafOfModules.IsLocallySurjective J w] [PresheafOfModules.IsLocallyInjective J w]
    (φ : F ⟶ S) : ∃! h : T ⟶ S, w ≫ h = φ :=
  ⟨homExtend hS w φ, comp_homExtend hS w φ, fun _ hh =>
    hom_eq_of_comp_eq hS.isSeparated w (hh.trans (comp_homExtend hS w φ).symm)⟩

end Stacks
