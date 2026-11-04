module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting

/-!
# Morphisms out of the lifted unit are unchanged by a pushforward between sites with terminal
objects

Let `F : C ⥤ D` be a continuous functor between sites and
`φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R` a morphism of sheaves of rings, so
that `SheafOfModules.pushforward φ` restricts sheaves of `R`-modules on `D` to sheaves of
`S`-modules on `C`.  Suppose both sites have terminal objects, `Z_C` in `C` and `Z_D` in `D`,
and that `F` carries the one to the other, `F.obj Z_C ≅ Z_D`.

Morphisms out of the universe lift of the free module of rank one are the sections over the
terminal object, by `SheafOfModules.uliftUnitHomEquiv`, and the sections of a pushforward over
`Z_C` are the sections of the original over `F.obj Z_C`, hence over `Z_D`. So the two Hom sets

`uliftForPresentation (unit R) ⟶ M`  and  `uliftForPresentation (unit S) ⟶ (pushforward φ).obj M`

are in bijection, and the bijection is composition with the pushforward functor after a morphism
`uliftForPresentation (unit S) ⟶ (pushforward φ).obj (uliftForPresentation (unit R))` carrying the
canonical generator to the canonical generator. Such a morphism,
`SheafOfModules.uliftUnitPushforward`, exists with no hypothesis on `φ` beyond continuity of `F`.

## Main definitions

* `PresheafOfModules.restrictEquivOfIsIso`: restriction of a presheaf of modules along an
  isomorphism of the site is a bijection on sections.
* `SheafOfModules.uliftUnitPushforward`: the morphism from the universe lift of the free module
  of rank one on `C` to the pushforward of the universe lift of the free module of rank one on
  `D` that carries the canonical generator to the canonical generator.
* `SheafOfModules.pushforwardUliftUnitHomEquiv`: the bijection between the two Hom sets, read
  off the sections over the terminal objects.

## Main results

* `SheafOfModules.restrictEquivOfIsIso_uliftUnitHomEquiv`: the section over a terminal object
  attached to a morphism out of the universe lift restricts to the image of the generator.
* `SheafOfModules.uliftUnitHomEquiv_comp_pushforward_map`: composing with a generator-preserving
  `g` and pushing forward is, on sections over the terminal objects, restriction along
  `F.obj Z_C ⟶ Z_D`.
* `SheafOfModules.bijective_comp_pushforward_map`: for any `g` carrying the generator to the
  generator, `f ↦ g ≫ (pushforward φ).map f` is a bijection.
* `SheafOfModules.bijective_uliftUnitPushforward_comp_pushforward_map` and
  `SheafOfModules.existsUnique_uliftUnitPushforward_comp_pushforward_map`: the same for the
  canonical `g`, with no hypothesis on `φ`, in its bijective and in its unique-lifting form.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ u₁ u₂ u t

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The restriction maps of the underlying presheaf of abelian groups of a presheaf of modules
are the restriction maps of the presheaf of modules. -/
lemma presheaf_map_apply (M : PresheafOfModules.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    M.presheaf.map f x = M.map f x := rfl

/-- **Restriction along an isomorphism of the site is a bijection on sections.** -/
noncomputable def restrictEquivOfIsIso (M : PresheafOfModules.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    [IsIso f] : (M.obj X : Type w) ≃ (M.obj Y : Type w) :=
  Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso (M.presheaf.map f))

/-- `PresheafOfModules.restrictEquivOfIsIso` is the restriction map, by definition. -/
lemma restrictEquivOfIsIso_apply (M : PresheafOfModules.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    [IsIso f] (x : M.obj X) : M.restrictEquivOfIsIso f x = M.map f x := rfl

end PresheafOfModules

namespace SheafOfModules

section

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{u}}

/-- **The section over a terminal object attached to a morphism out of the universe lift of the
free module of rank one restricts to the image of the generator.** -/
lemma restrictEquivOfIsIso_uliftUnitHomEquiv {Z : D} (hZ : IsTerminal Z)
    (M : SheafOfModules.{max t u} R)
    (f : uliftForPresentation.{u₂, v₂, u, u, t} (unit R) ⟶ M) {Y : Dᵒᵖ} (α : op Z ⟶ Y)
    [IsIso α] :
    M.val.restrictEquivOfIsIso α (uliftUnitHomEquiv.{u₂, v₂, u, t} hZ M f) =
      f.val.app Y (uliftUnitGen.{u₂, v₂, u, t} R Y) := by
  have h := PresheafOfModules.naturality_apply f.val α (uliftUnitGen.{u₂, v₂, u, t} R (op Z))
  rw [uliftForPresentation_unit_val_map_uliftUnitGen.{u₂, v₂, u, t} α] at h
  exact h.symm

end

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- **The canonical morphism from the universe lift of the free module of rank one on `C` to the
pushforward of the universe lift of the free module of rank one on `D`**, the morphism
(`SheafOfModules.fromUliftUnit`) prescribed by the generator of the lift over `F.obj Z`, which is a
section of the pushforward over the terminal object `Z`. -/
noncomputable def uliftUnitPushforward {Z : C} (hZ : IsTerminal Z) :
    uliftForPresentation.{u₁, v₁, u, u, t} (unit S) ⟶
      (pushforward.{max t u} φ).obj (uliftForPresentation.{u₂, v₂, u, u, t} (unit R)) :=
  fromUliftUnit.{u₁, v₁, u, t} hZ (uliftUnitGen.{u₂, v₂, u, t} R (op (F.obj Z)))

/-- `SheafOfModules.uliftUnitPushforward` carries the canonical generator to the canonical
generator. -/
lemma uliftUnitHomEquiv_uliftUnitPushforward {Z : C} (hZ : IsTerminal Z) :
    uliftUnitHomEquiv.{u₁, v₁, u, t} hZ
        ((pushforward.{max t u} φ).obj (uliftForPresentation.{u₂, v₂, u, u, t} (unit R)))
        (uliftUnitPushforward.{v₁, v₂, u₁, u₂, u, t} φ hZ) =
      uliftUnitGen.{u₂, v₂, u, t} R (op (F.obj Z)) :=
  (uliftUnitHomEquiv.{u₁, v₁, u, t} hZ _).apply_symm_apply _

/-- **Composing with a generator-preserving `g` and pushing forward is, on sections over the
terminal objects, restriction along a morphism `F.obj Z_C ⟶ Z_D`.** -/
lemma uliftUnitHomEquiv_comp_pushforward_map {Z_C : C} (hZC : IsTerminal Z_C)
    {Z_D : D} (hZD : IsTerminal Z_D) (M : SheafOfModules.{max t u} R)
    (g : uliftForPresentation.{u₁, v₁, u, u, t} (unit S) ⟶
      (pushforward.{max t u} φ).obj (uliftForPresentation.{u₂, v₂, u, u, t} (unit R)))
    (hg : g.val.app (op Z_C) (uliftUnitGen.{u₁, v₁, u, t} S (op Z_C)) =
      uliftUnitGen.{u₂, v₂, u, t} R (op (F.obj Z_C)))
    (α : op Z_D ⟶ op (F.obj Z_C)) [IsIso α]
    (f : uliftForPresentation.{u₂, v₂, u, u, t} (unit R) ⟶ M) :
    uliftUnitHomEquiv.{u₁, v₁, u, t} hZC ((pushforward.{max t u} φ).obj M)
        (g ≫ (pushforward.{max t u} φ).map f) =
      M.val.restrictEquivOfIsIso α (uliftUnitHomEquiv.{u₂, v₂, u, t} hZD M f) := by
  rw [restrictEquivOfIsIso_uliftUnitHomEquiv.{v₂, u₂, u, t} hZD M f α]
  exact congrArg (fun x => f.val.app (op (F.obj Z_C)) x) hg

/-- **The bijection between morphisms out of the two universe-lifted units**, for a continuous
functor carrying a terminal object to a terminal object.  Both sides are the sections of `M` over
a terminal object — over `Z_D` on the left, over `F.obj Z_C` on the right, the pushforward not
changing the sections — and the two are identified by restriction along `F.obj Z_C ≅ Z_D`. -/
noncomputable def pushforwardUliftUnitHomEquiv {Z_C : C} (hZC : IsTerminal Z_C)
    {Z_D : D} (hZD : IsTerminal Z_D) (e : F.obj Z_C ≅ Z_D) (M : SheafOfModules.{max t u} R) :
    (uliftForPresentation.{u₂, v₂, u, u, t} (unit R) ⟶ M) ≃
      (uliftForPresentation.{u₁, v₁, u, u, t} (unit S) ⟶ (pushforward.{max t u} φ).obj M) :=
  (uliftUnitHomEquiv.{u₂, v₂, u, t} hZD M).trans
    ((M.val.restrictEquivOfIsIso e.hom.op).trans
      (uliftUnitHomEquiv.{u₁, v₁, u, t} hZC ((pushforward.{max t u} φ).obj M)).symm)

/-- **Pushing forward is bijective on morphisms out of the universe-lifted unit.**  Let
`F : C ⥤ D` be continuous, `φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R`, let `Z_C`
be terminal in `C` and `Z_D` terminal in `D` with `F.obj Z_C ≅ Z_D`, and let
`g : uliftForPresentation (unit S) ⟶ (pushforward φ).obj (uliftForPresentation (unit R))` carry
the canonical generator over `Z_C` to the canonical generator over `F.obj Z_C`.  Then

`f ↦ g ≫ (pushforward φ).map f`

is a **bijection** from `uliftForPresentation (unit R) ⟶ M` onto
`uliftForPresentation (unit S) ⟶ (pushforward φ).obj M`, for every sheaf of `R`-modules `M`. -/
theorem bijective_comp_pushforward_map {Z_C : C} (hZC : IsTerminal Z_C)
    {Z_D : D} (hZD : IsTerminal Z_D) (e : F.obj Z_C ≅ Z_D) (M : SheafOfModules.{max t u} R)
    (g : uliftForPresentation.{u₁, v₁, u, u, t} (unit S) ⟶
      (pushforward.{max t u} φ).obj (uliftForPresentation.{u₂, v₂, u, u, t} (unit R)))
    (hg : g.val.app (op Z_C) (uliftUnitGen.{u₁, v₁, u, t} S (op Z_C)) =
      uliftUnitGen.{u₂, v₂, u, t} R (op (F.obj Z_C))) :
    Function.Bijective (fun f : uliftForPresentation.{u₂, v₂, u, u, t} (unit R) ⟶ M =>
      g ≫ (pushforward.{max t u} φ).map f) := by
  have key : (fun f : uliftForPresentation.{u₂, v₂, u, u, t} (unit R) ⟶ M =>
      g ≫ (pushforward.{max t u} φ).map f) =
      pushforwardUliftUnitHomEquiv.{v₁, v₂, u₁, u₂, u, t} φ hZC hZD e M := by
    funext f
    refine (uliftUnitHomEquiv.{u₁, v₁, u, t} hZC ((pushforward.{max t u} φ).obj M)).injective ?_
    rw [uliftUnitHomEquiv_comp_pushforward_map.{v₁, v₂, u₁, u₂, u, t} φ hZC hZD M g hg e.hom.op f]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [key]
  exact (pushforwardUliftUnitHomEquiv.{v₁, v₂, u₁, u₂, u, t} φ hZC hZD e M).bijective

/-- **Pushing forward along the canonical morphism is bijective on morphisms out of the
universe-lifted unit**, for a continuous functor carrying a terminal object to a terminal object
and *any* morphism of sheaves of rings `φ`. -/
theorem bijective_uliftUnitPushforward_comp_pushforward_map {Z_C : C} (hZC : IsTerminal Z_C)
    {Z_D : D} (hZD : IsTerminal Z_D) (e : F.obj Z_C ≅ Z_D) (M : SheafOfModules.{max t u} R) :
    Function.Bijective (fun f : uliftForPresentation.{u₂, v₂, u, u, t} (unit R) ⟶ M =>
      uliftUnitPushforward.{v₁, v₂, u₁, u₂, u, t} φ hZC ≫ (pushforward.{max t u} φ).map f) :=
  bijective_comp_pushforward_map.{v₁, v₂, u₁, u₂, u, t} φ hZC hZD e M _
    (uliftUnitHomEquiv_uliftUnitPushforward.{v₁, v₂, u₁, u₂, u, t} φ hZC)

/-- **Every morphism out of the universe-lifted unit of `C` into a pushforward is the pushforward
of a unique morphism out of the universe-lifted unit of `D`.** -/
theorem existsUnique_uliftUnitPushforward_comp_pushforward_map {Z_C : C} (hZC : IsTerminal Z_C)
    {Z_D : D} (hZD : IsTerminal Z_D) (e : F.obj Z_C ≅ Z_D) (M : SheafOfModules.{max t u} R)
    (h : uliftForPresentation.{u₁, v₁, u, u, t} (unit S) ⟶ (pushforward.{max t u} φ).obj M) :
    ∃! f : uliftForPresentation.{u₂, v₂, u, u, t} (unit R) ⟶ M,
      uliftUnitPushforward.{v₁, v₂, u₁, u₂, u, t} φ hZC ≫
        (pushforward.{max t u} φ).map f = h :=
  (bijective_uliftUnitPushforward_comp_pushforward_map.{v₁, v₂, u₁, u₂, u, t}
    φ hZC hZD e M).existsUnique h

end SheafOfModules

end
