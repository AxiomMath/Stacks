module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.HigherDirectImageLocalScalar
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.HigherDirectImageRestrictInvariance
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.PushforwardIdealPowerGradedModule

/-!
# The action of `ℐⁱ` on `R ᵖ f_*(ℐⁿℱ)` over an open of the base

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` a sheaf of `𝒪_X`-modules and `ℐ ⊆ 𝒪_Y` a
quasi-coherent sheaf of ideals. The setup paragraph of [Stacks, Tag 02O7] obtains, "by localizing
and then sheafifying", maps
`ℐⁱ ⊗_{𝒪_Y} R ᵖ f_*(ℐⁿℱ) ⟶ R ᵖ f_*(ℐⁿ⁺ⁱℱ)`
making `⨁ₙ R ᵖ f_*(ℐⁿℱ)` a graded module over `⨁ₙ ℐⁿ` on `Y`. This file builds the localizing
step in **every** degree `p`: the action of a section of `ℐⁱ` over an open `V ⊆ Y` on the
sections over `V` of the `p`-th higher direct image.

`Stacks.Blowup.pushforwardReesGradedModule` is the same structure in degree `p = 0`, where the
sections of `f_*ℳ` over `V` are literally the sections of `ℳ` over `f⁻¹(V)` and nothing below is
needed.

## The construction

A section `r` of `ℐⁱ` over `V` is not a global section of anything on `X`, so it induces no
endomorphism of `ℐⁿℱ`; its inverse image is a section of `ℐⁱ𝒪_X` over `U = f⁻¹(V)` only. What it
does induce is a morphism of sheaves **on `X`**

`ℐⁿℱ ⟶ (j_U)_*((ℐⁿ⁺ⁱℱ)|_U)`,

namely `Stacks.Blowup.mulHom`: the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`
followed by the direct image of multiplication by `r` on the restrictions
(`Stacks.Blowup.mulRestrict`). Since this is a morphism of sheaves on all of `X`, the functor
`R ᵖ f_*` applies to it with no localization of the functor — which is the point: the
compatibility of [Stacks, Tag 01E5] with nested opens of `Y`, unavailable in positive degree, is
never used.

The unit `ℐⁿ⁺ⁱℱ ⟶ (j_U)_*((ℐⁿ⁺ⁱℱ)|_U)` becomes an isomorphism after `R ᵖ f_*` and restriction to
`V` — that is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isIso_restrictFunctor_map_rightDerived_unit` —
so its sections over `V` are invertible (`Stacks.Blowup.isIso_unitDerived_app`), and dividing by
it lands the action back in `R ᵖ f_*(ℐⁿ⁺ⁱℱ)`. That quotient is
`Stacks.Blowup.smulSectionHom`, and `Stacks.Blowup.smulPlus` is it read as a biadditive map on
sections, which is the shape the `smul` field of `SheafOfModules.GradedModule` consumes.

## Main definitions

* `Stacks.Blowup.mulRestrict`: multiplication by a section of `ℐⁱ𝒪_X` over `f⁻¹(V)`, as a
  morphism of the restrictions to `f⁻¹(V)` of the ideal-power multiples of `ℱ`.
* `Stacks.Blowup.mulHom`: **the morphism `ℐⁿℱ ⟶ (j_{f⁻¹V})_*((ℐⁿ⁺ⁱℱ)|_{f⁻¹V})` on `X`.**
* `Stacks.Blowup.smulSectionHom`: **the action of one section of `ℐⁱ𝒪_X` over `f⁻¹(V)` on
  `Γ(V, R ᵖ f_*(ℐⁿℱ))`**, i.e. `R ᵖ f_*(mulHom r)` on sections over `V` divided by the unit.
* `Stacks.Blowup.smulPlus`: the same as a biadditive map in the section of `ℐⁱ` over `V` and the
  section of `R ᵖ f_*(ℐⁿℱ)` over `V`, the inverse image of the former being
  `Stacks.Blowup.reesPieceComapSection`.

## Main results

* `Stacks.Blowup.isIso_unitDerived_app`: the higher direct image of the unit is invertible on
  sections over `V`. This is what makes the division well defined.
* `Stacks.Blowup.smulSectionHom_add` and `Stacks.Blowup.mulHom_add`: additivity in the acting
  section, which is what makes `smulPlus` a biadditive map.
* `Stacks.Blowup.smulSectionHom_smul`: the action is `Γ(Y, V)`-linear in the module variable.
  This is the `smul_smul_left` law of a graded module.
* `Stacks.Blowup.smulSectionHom_smul_right`: the action is `Γ(Y, V)`-linear in the **acting**
  section. This is the `smul_smul_right` law; it rests on
  `Stacks.Blowup.mulRestrict_smul` and, through it, on the identity of the two routes from
  `Γ(Y, V)` to the functions on an open of `f⁻¹(V)`
  (`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.appTop_topIso_inv_restrict`).

## Implementation notes

The degrees are the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`. Every input used here is
`ℕ`-indexed: the invertibility of the unit, the linearity of
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerived_map_pushforward_smul_app`, and
[Stacks, Tag 01E5] as a natural isomorphism. The source states the tag for `p ≥ 0`, so this
loses nothing.

`Stacks.Blowup.reesComapMod` exists only to pin the category: `ℐⁿℱ` is produced as a
`SheafOfModules X.ringCatSheaf` by `Stacks.Blowup.reesMultiple`, while
`AlgebraicGeometry.Scheme.Modules.pushforward` produces an `X.Modules`; the two are the same by
definition but have separate `Category` instances, and a `⟶` whose two sides are spelled
differently picks an instance for which the additive structure on morphisms is not found.

**What is not here.** The two laws of `SheafOfModules.GradedModule` that compare *different*
opens of `Y` or *different* degrees — `smul_naturality`, and the two `HEq` laws `smul_mul` and
`smul_one` — are proved in the sibling module `PushforwardIdealPowerGradedModulePlus`, together
with the graded module itself. They need machinery this file does not: the comparison of the
extensions from two nested opens
(`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrictLE`) and transport along an
equality of degrees.

## References

* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

universe u

namespace Stacks.Blowup

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules)

/-- `ℐⁿℱ` for `ℐ𝒪_X` the inverse image ideal, as an object of `X.Modules`.

This exists only to pin the category; see the implementation notes. -/
public abbrev reesComapMod (n : ℤ) : X.Modules :=
  (reesMultiple (I.comap f) n F).toSheafOfModules

/-! ### Multiplication on the restrictions to `f⁻¹(V)` -/

/-- **Multiplication by a section of `ℐⁱ𝒪_X` over `f⁻¹(V)`**, as a morphism of the restrictions
to `f⁻¹(V)` of the ideal-power multiples of `ℱ`.

Over an open `W` of `f⁻¹(V)` the sections of the restriction are the sections of `ℐⁿℱ` over the
image of `W` in `X`, and the map is the multiplication `Stacks.Blowup.reesMultipleSmul` of the
Rees algebra by the restriction of the given section. Its compatibility with shrinking `W` is
`Stacks.Blowup.reesMultipleSmul_restr`, and its linearity is
`Stacks.Blowup.smul_comm_reesPieceAmbient` read through the comparison of rings of the
restriction, which for the inclusion of an open is the identity
(`AlgebraicGeometry.Scheme.Opens.ι_appIso`). -/
public def mulRestrict (n i : ℤ) (V : Y.Opens)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n) ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F (n + i)) :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        ((reesMultipleSmul (I.comap f) F n i (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop))).flip
          (Stacks.restr (reesPiece (I.comap f) i).val
            (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op r))
      naturality := by
        intro W W' φ
        apply AddCommGrpCat.hom_ext
        ext x
        have hle : (f ⁻¹ᵁ V).ι ''ᵁ W'.unop ≤ (f ⁻¹ᵁ V).ι ''ᵁ W.unop :=
          (f ⁻¹ᵁ V).ι.image_mono (leOfHom φ.unop)
        have hr : Stacks.restr (reesPiece (I.comap f) i).val
              (homOfLE ((f ⁻¹ᵁ V).ι_image_le W'.unop)).op r =
            Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hle).op
              (Stacks.restr (reesPiece (I.comap f) i).val
                (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op r) :=
          (PresheafOfModules.map_comp_apply (reesPiece (I.comap f) i).val
            (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op (homOfLE hle).op r)
        exact Eq.trans (congrArg (fun z => reesMultipleSmul (I.comap f) F n i
            (op ((f ⁻¹ᵁ V).ι ''ᵁ W'.unop))
            (Stacks.restr (reesComapMod f I F n).val (homOfLE hle).op x) z) hr)
          (reesMultipleSmul_restr (I.comap f) F n i hle x _).symm }
    (fun W a x => Subtype.ext
      (smul_comm_reesPieceAmbient F (((f ⁻¹ᵁ V).ι.appIso W.unop).inv a) _ x.1))⟩

/-- `Stacks.Blowup.mulRestrict` on sections. -/
public theorem mulRestrict_app (n i : ℤ) (V : Y.Opens)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) (W : (f ⁻¹ᵁ V).toScheme.Opens)
    (x : (reesComapMod f I F n).val.obj (op ((f ⁻¹ᵁ V).ι ''ᵁ W))) :
    (mulRestrict f I F n i V r).val.app (op W) x =
      reesMultipleSmul (I.comap f) F n i (op ((f ⁻¹ᵁ V).ι ''ᵁ W)) x
        (Stacks.restr (reesPiece (I.comap f) i).val
          (homOfLE ((f ⁻¹ᵁ V).ι_image_le W)).op r) := rfl

/-- `Stacks.Blowup.mulRestrict` is additive in the acting section. -/
public theorem mulRestrict_add (n i : ℤ) (V : Y.Opens)
    (r r' : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    mulRestrict f I F n i V (r + r') =
      mulRestrict f I F n i V r + mulRestrict f I F n i V r' := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  refine Eq.trans (congrArg (fun z => reesMultipleSmul (I.comap f) F n i
      (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) x z)
    (map_add (((reesPiece (I.comap f) i).val.map
      (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op).hom) r r')) ?_
  exact map_add (reesMultipleSmul (I.comap f) F n i (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) x) _ _

variable (p : ℕ)

/-! ### The unit, and its invertibility over `V` -/

/-- The unit `ℐⁿℱ ⟶ (j_{f⁻¹V})_*((ℐⁿℱ)|_{f⁻¹V})` of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. -/
public abbrev unitPlus (n : ℤ) (V : Y.Opens) :
    reesComapMod f I F n ⟶
      (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n)) :=
  (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app _

/-- The `p`-th higher direct image of the unit. -/
public abbrev unitDerived (n : ℤ) (V : Y.Opens) :
    ((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n) ⟶
      ((Scheme.Modules.pushforward f).rightDerived p).obj
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n))) :=
  ((Scheme.Modules.pushforward f).rightDerived p).map (unitPlus f I F n V)

/-- **The higher direct image of the unit is invertible on sections over `V`.** It is invertible
after restriction to `V` by
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isIso_restrictFunctor_map_rightDerived_unit`,
and the sections of the restriction over the top open are the sections over `V.ι ''ᵁ ⊤`, which is
`V`. -/
public instance isIso_unitDerived_app (n : ℤ) (V : Y.Opens) :
    IsIso ((unitDerived f I F p n V).app V) := by
  have main : ∀ (W : Y.Opens), V.ι ''ᵁ ⊤ = W → IsIso ((unitDerived f I F p n V).app W) := by
    rintro W rfl
    exact Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (isIso_restrictFunctor_map_rightDerived_unit f V p (reesComapMod f I F n)) ⊤
  exact main V (Scheme.Opens.ι_image_top V)

/-- The inverse of the unit on sections over `V` is a right inverse. -/
public theorem unitDerived_hom_inv_app (n : ℤ) (V : Y.Opens)
    (z : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n))), V)) :
    (unitDerived f I F p n V).app V (inv ((unitDerived f I F p n V).app V) z) = z := by
  simp

/-- The inverse of the unit on sections over `V` is a left inverse. -/
public theorem unitDerived_inv_hom_app (n : ℤ) (V : Y.Opens)
    (w : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    inv ((unitDerived f I F p n V).app V) ((unitDerived f I F p n V).app V w) = w := by
  simp

/-- The inverse of the unit on sections over `V` is `Γ(Y, V)`-linear: the unit is a morphism of
sheaves of modules, so its sections are linear, and a linear bijection has a linear inverse. -/
public theorem inv_unitDerived_app_smul (n : ℤ) (V : Y.Opens) (ρ : Γ(Y, V))
    (z : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n))), V)) :
    inv ((unitDerived f I F p n V).app V) (ρ • z) =
      ρ • inv ((unitDerived f I F p n V).app V) z := by
  have h1 : (unitDerived f I F p n V).app V
      (ρ • inv ((unitDerived f I F p n V).app V) z) = ρ • z := by
    rw [Scheme.Modules.Hom.app_smul, unitDerived_hom_inv_app]
  rw [← h1, unitDerived_inv_hom_app]

/-! ### The action -/

/-- **The morphism `ℐⁿℱ ⟶ (j_{f⁻¹V})_*((ℐⁿ⁺ⁱℱ)|_{f⁻¹V})` of [Stacks, Tag 02O7]** induced by a
section of `ℐⁱ𝒪_X` over `f⁻¹(V)`.

It is a morphism of sheaves on all of `X`, so `R ᵖ f_*` applies to it; that is the whole point of
extending the target from `f⁻¹(V)` rather than localizing the functor. -/
public def mulHom (n i : ℤ) (V : Y.Opens)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    reesComapMod f I F n ⟶
      (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F (n + i))) :=
  unitPlus f I F n V ≫
    (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map (mulRestrict f I F n i V r)

/-- `Stacks.Blowup.mulHom` is additive in the acting section. -/
public theorem mulHom_add (n i : ℤ) (V : Y.Opens)
    (r r' : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    mulHom f I F n i V (r + r') = mulHom f I F n i V r + mulHom f I F n i V r' := by
  simp only [mulHom, mulRestrict_add, Functor.map_add, Preadditive.comp_add]

/-- **The action of one section of `ℐⁱ𝒪_X` over `f⁻¹(V)` on `Γ(V, R ᵖ f_*(ℐⁿℱ))`**: the sections
over `V` of `R ᵖ f_*(mulHom r)`, divided by the sections over `V` of the higher direct image of
the unit, which `Stacks.Blowup.isIso_unitDerived_app` makes invertible. -/
public def smulSectionHom (n i : ℤ) (V : Y.Opens)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V) ⟶
      Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F (n + i)), V) :=
  (((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i V r)).app V ≫
    inv ((unitDerived f I F p (n + i) V).app V)

/-- `Stacks.Blowup.smulSectionHom` on an element. -/
public theorem smulSectionHom_apply (n i : ℤ) (V : Y.Opens)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V)))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    smulSectionHom f I F p n i V r x =
      inv ((unitDerived f I F p (n + i) V).app V)
        (((((Scheme.Modules.pushforward f).rightDerived p).map
          (mulHom f I F n i V r)).app V) x) := rfl

/-- The action is additive in the acting section. -/
public theorem smulSectionHom_add (n i : ℤ) (V : Y.Opens)
    (r r' : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    smulSectionHom f I F p n i V (r + r') =
      smulSectionHom f I F p n i V r + smulSectionHom f I F p n i V r' := by
  simp only [smulSectionHom, mulHom_add, Functor.map_add, Scheme.Modules.Hom.add_app,
    Preadditive.add_comp]

/-- **The action is `Γ(Y, V)`-linear in the module variable.** This is the `smul_smul_left` law
of a graded module: the sections over `V` of a morphism of sheaves of modules are linear, and so
is the inverse of the unit. -/
public theorem smulSectionHom_smul (n i : ℤ) (V : Y.Opens)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) (ρ : Γ(Y, V))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    smulSectionHom f I F p n i V r (ρ • x) = ρ • smulSectionHom f I F p n i V r x := by
  rw [smulSectionHom_apply, smulSectionHom_apply, Scheme.Modules.Hom.app_smul,
    inv_unitDerived_app_smul]

/-- **The action of `ℐⁱ` on `R ᵖ f_*(ℐⁿℱ)` over an open `V` of `Y`**, as a biadditive map on
sections — the shape the `smul` field of `SheafOfModules.GradedModule` consumes.

A section of `ℐⁱ` over `V` is carried to a section of `ℐⁱ𝒪_X` over `f⁻¹(V)` by
`Stacks.Blowup.reesPieceComapSection`, and that acts by `Stacks.Blowup.smulSectionHom`. -/
public def smulPlus (n i : ℤ) (V : (Opens Y)ᵒᵖ) :
    (((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n)).val.obj V →+
      (reesPiece I i).val.obj V →+
        (((Scheme.Modules.pushforward f).rightDerived p).obj
          (reesComapMod f I F (n + i))).val.obj V :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun r => smulSectionHom f I F p n i V.unop (reesPieceComapSection f I i V r) x)
      (fun r r' => by
        rw [map_add (reesPieceComapSection f I i V) r r',
          smulSectionHom_add f I F p n i V.unop]
        rfl))
    (fun x y => by
      refine AddMonoidHom.ext fun r => ?_
      exact map_add (ConcreteCategory.hom
        (smulSectionHom f I F p n i V.unop (reesPieceComapSection f I i V r))) x y)

/-! ### Linearity in the acting section -/

/-- The inverse image on sections of a homogeneous piece of the Rees algebra is `𝒪_Y`-linear, a
scalar on `Y` acting on the inverse image through `f^♯`. This is `map_smul` for the morphism of
sheaves of `𝒪_Y`-modules `Stacks.Blowup.reesPieceComap`, read through the description of the
scalar action on the sections of a pushforward. -/
public theorem reesPieceComapSection_smul (i : ℤ) (U : (Opens Y)ᵒᵖ)
    (ρ : Y.ringCatSheaf.obj.obj U) (y : (reesPiece I i).val.obj U) :
    reesPieceComapSection f I i U (ρ • y) =
      (show X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ U.unop)) from
        (f.app U.unop) (show Γ(Y, U.unop) from ρ)) • reesPieceComapSection f I i U y :=
  map_smul ((reesPieceComap f I i).val.app U).hom ρ y

/-- **Multiplication on the restrictions to `f⁻¹(V)` is `Γ(Y, V)`-linear in the acting section.**
Scaling the acting section of `ℐⁱ𝒪_X` by the inverse image of `ρ ∈ Γ(Y, V)` is the same as
postcomposing with multiplication by `ρ`, read on the modules over `f⁻¹(V)` through
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.linearOnPreimage`.

The two scalars are the two routes of
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.appTop_topIso_inv_restrict`; the rest is the
`smul_smul_right` law of `Stacks.Blowup.reesGradedModule` and the semilinearity of restriction. -/
public theorem mulRestrict_smul (n i : ℤ) (V : Y.Opens) (ρ : Γ(Y, V))
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    letI := linearOnPreimage f V
    mulRestrict f I F n i V
        ((show X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ V)) from (f.app V) ρ) • r) =
      mulRestrict f I F n i V r ≫ (V.topIso.inv ρ • 𝟙 _) := by
  let := linearOnPreimage f V
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  have hRHS : ((mulRestrict f I F n i V r ≫
        (V.topIso.inv ρ • 𝟙 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
          (reesComapMod f I F (n + i))))).val.app W) x =
      (show X.ringCatSheaf.obj.obj (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) from
          X.presheaf.map (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op ((f.app V) ρ)) •
        reesMultipleSmul (I.comap f) F n i (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) x
          (Stacks.restr (reesPiece (I.comap f) i).val
            (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op r) := by
    refine Eq.trans (smul_app (X := (f ⁻¹ᵁ V).toScheme) ↥Γ(V.toScheme, ⊤)
      (((f ∣_ V).appTop).hom.comp (RingHom.id _)) (V.topIso.inv ρ)
      (𝟙 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F (n + i))))
      W.unop ((mulRestrict f I F n i V r).val.app W x)) ?_
    have hres := Scheme.Modules.smul_restrictAppIso_hom_apply (f := (f ⁻¹ᵁ V).ι)
      (reesComapMod f I F (n + i)) W.unop
      ((f ⁻¹ᵁ V).toScheme.presheaf.map (homOfLE (le_top (a := W.unop))).op
        ((((f ∣_ V).appTop).hom.comp (RingHom.id ↥Γ(V.toScheme, ⊤))) (V.topIso.inv ρ)))
      ((mulRestrict f I F n i V r).val.app W x)
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Modules.restrictAppIso] at hres
    refine hres.trans ?_
    refine Eq.trans (congrArg
      (fun c : X.ringCatSheaf.obj.obj (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) =>
        c • (show (reesComapMod f I F (n + i)).val.obj (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) from
          (mulRestrict f I F n i V r).val.app W x))
      (appTop_topIso_inv_restrict f V W.unop ρ)) ?_
    exact congrArg
      (fun z => (show X.ringCatSheaf.obj.obj (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) from
          X.presheaf.map (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op ((f.app V) ρ)) • z)
      (mulRestrict_app f I F n i V r W.unop x)
  refine Eq.trans (mulRestrict_app f I F n i V _ W.unop x) (Eq.trans ?_ hRHS.symm)
  refine Eq.trans (congrArg (fun t => reesMultipleSmul (I.comap f) F n i
      (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) x t)
    (restr_smul_gamma (reesPiece (I.comap f) i) ((f ⁻¹ᵁ V).ι_image_le W.unop)
      (show Γ(X, f ⁻¹ᵁ V) from (f.app V) ρ) r)) ?_
  exact (reesGradedModule (I.comap f) F).smul_smul_right n i
    (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) _ x _

/-- **The action is `Γ(Y, V)`-linear in the acting section.** This is the `smul_smul_right` law
of a graded module.

Scaling the acting section turns `Stacks.Blowup.mulHom` into its composite with multiplication by
`ρ` on the extension from `f⁻¹(V)` (`mulRestrict_smul`), and
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerived_map_pushforward_smul_app` says
that `R ᵖ f_*` of that multiplication is multiplication by `ρ` on sections over `V`; dividing by
the unit keeps the scalar by `Stacks.Blowup.inv_unitDerived_app_smul`. -/
public theorem smulSectionHom_smul_right (n i : ℤ) (V : Y.Opens) (ρ : Γ(Y, V))
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V)))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    smulSectionHom f I F p n i V
        ((show X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ V)) from (f.app V) ρ) • r) x =
      ρ • smulSectionHom f I F p n i V r x := by
  let := linearOnPreimage f V
  have hA : mulHom f I F n i V
        ((show X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ V)) from (f.app V) ρ) • r) =
      mulHom f I F n i V r ≫ (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map
        (V.topIso.inv ρ • 𝟙 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
          (reesComapMod f I F (n + i)))) := by
    refine Eq.trans (congrArg (fun φ => unitPlus f I F n V ≫
      (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map φ)
      (mulRestrict_smul f I F n i V ρ r)) ?_
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  have key : ((((Scheme.Modules.pushforward f).rightDerived p).map
        (mulHom f I F n i V
          ((show X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ V)) from (f.app V) ρ) • r))).app V) x =
      ρ • ((((Scheme.Modules.pushforward f).rightDerived p).map
        (mulHom f I F n i V r)).app V) x := by
    rw [hA, Functor.map_comp]
    refine Eq.trans (rightDerived_map_pushforward_smul_app f V p
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F (n + i)))
      (V.topIso.inv ρ)
      ((((Scheme.Modules.pushforward f).rightDerived p).map
        (mulHom f I F n i V r)).app V x)) ?_
    rw [Iso.inv_hom_id_apply]
  rw [smulSectionHom_apply, smulSectionHom_apply, key, inv_unitDerived_app_smul]

end Stacks.Blowup

end

end
