module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.PushforwardIdealPowerAction
public import StacksCore.Tactic.StacksAttribute

/-!
# `⨁ₙ R ᵖ f_*(ℐⁿℱ)` as a graded module over `⨁ₙ ℐⁿ`, in every degree

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` a sheaf of `𝒪_X`-modules and `ℐ ⊆ 𝒪_Y` a
quasi-coherent sheaf of ideals. The setup paragraph of [Stacks, Tag 02O7] obtains, "by localizing
and then sheafifying", maps
`ℐⁱ ⊗_{𝒪_Y} R ᵖ f_*(ℐⁿℱ) ⟶ R ᵖ f_*(ℐⁿ⁺ⁱℱ)`
making `ℳ = ⨁_{n ≥ 0} R ᵖ f_*(ℐⁿℱ)` a graded module over `𝒜 = ⨁_{n ≥ 0} ℐⁿ` on `Y`. This file
assembles that graded module, in every cohomological degree `p`.

The action itself is `Stacks.Blowup.smulPlus`, together with the two laws that stay over one open
of `Y` and in one degree. What is left, and what this file does, are the laws that compare
*different* opens and *different* degrees.

## The two remaining laws

**Shrinking the open.** A section `r` of `ℐⁱ` over `V` acts through a morphism of sheaves on `X`
with target the extension `(j_{f⁻¹V})_*((ℐⁿ⁺ⁱℱ)|_{f⁻¹V})`, and that target depends on `V`. For
`V' ⊆ V` the two targets are compared by
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrictLE`, a morphism of sheaves on all
of `X`; applying `R ᵖ f_*` to it gives a morphism of sheaves on `Y`, which therefore commutes with
restriction for free. The two identities it satisfies — it carries the unit at `V` to the unit at
`V'`, and `Stacks.Blowup.mulHom` at `V` to `mulHom` at `V'` for the restricted section — then give
`smul_naturality`. **No compatibility of [Stacks, Tag 01E5] across nested opens is used**; that
compatibility is available in the tree in degree zero only, and this is how the construction
avoids needing it.

**Changing the degree.** The associativity and unit laws of a graded module compare sections in
degrees `(n + i) + j` and `n + (i + j)`, and in `n + 0` and `n`, which are propositionally but not
definitionally equal; `SheafOfModules.GradedModule` therefore states them with `HEq`. The degree
equality is substituted once, in `Stacks.Blowup.heq_inv_unitDerived_unitPlus_comp`, after which
both laws are the corresponding laws of `Stacks.Blowup.reesGradedModule` on `X` — the honest
content, which is multiplicativity and unitality of the Rees algebra.

## Main definitions

* `Stacks.Blowup.pushforwardReesGradedModulePlus`: **the graded `⨁ₙ ℐⁿ`-module
  `⨁ₙ R ᵖ f_*(ℐⁿℱ)` on `Y`**, for every `p`.

## Main results

* `Stacks.Blowup.restrictFunctor_map_mulHom` and `Stacks.Blowup.mulHom_comp_extendRestrictLE`:
  the action is compatible with shrinking the open of the base, at the level of sheaves on `X`.
* `Stacks.Blowup.smulSectionHom_naturality`: the `smul_naturality` law.
* `Stacks.Blowup.smulSectionHom_comp`, `Stacks.Blowup.heq_smulSectionHom_mul` and
  `Stacks.Blowup.heq_smulSectionHom_one`: the `smul_mul` and `smul_one` laws.

## Implementation notes

The degrees are the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, as everywhere in this
chain: the linearity of
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerived_map_pushforward_smul_app` and
[Stacks, Tag 01E5] as a natural isomorphism exist only in that indexing. The source states the
tag for `p ≥ 0`, so this loses nothing.

The graded module is declared here rather than beside the degree-zero
`Stacks.Blowup.pushforwardReesGradedModule` because of the module order: that module defines
`Stacks.Blowup.reesPieceComapSection`, which the action depends on, so it cannot import the
action back.

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

variable {X Y : Scheme.{u}}

/-- **`Stacks.Blowup.mulHom` restricted to a smaller `f⁻¹(V')`** is multiplication on the
restrictions to `f⁻¹(V')` by the restricted section, followed by the restricted unit.

Over an open `W` of `f⁻¹(V')` both sides multiply the restriction of the module section by the
restriction of the acting section to the image of `W` in `X`; the two orders of "restrict, then
multiply" agree by `Stacks.Blowup.reesMultipleSmul_restr`, and the three restrictions of the
acting section collapse by `Stacks.Blowup.restr_restr_opens`. -/
public theorem restrictFunctor_map_mulHom (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules)
    (n i : ℤ) (V V' : Y.Opens) (hU : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).map (mulHom f I F n i V r) =
      mulRestrict f I F n i V'
          (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r) ≫
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).map
          ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app
            (reesComapMod f I F (n + i))) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  have hA : (f ⁻¹ᵁ V).ι ''ᵁ ((f ⁻¹ᵁ V).ι ⁻¹ᵁ ((f ⁻¹ᵁ V').ι ''ᵁ W.unop)) ≤
      (f ⁻¹ᵁ V').ι ''ᵁ W.unop := (f ⁻¹ᵁ V).ι.image_preimage_le _
  have hr : Stacks.restr (reesPiece (I.comap f) i).val
        (homOfLE ((f ⁻¹ᵁ V).ι_image_le ((f ⁻¹ᵁ V).ι ⁻¹ᵁ ((f ⁻¹ᵁ V').ι ''ᵁ W.unop)))).op r =
      Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hA).op
        (Stacks.restr (reesPiece (I.comap f) i).val
          (homOfLE ((f ⁻¹ᵁ V').ι_image_le W.unop)).op
          (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r)) := by
    rw [restr_restr_opens, restr_restr_opens]
  refine Eq.trans (mulRestrict_app f I F n i V r
    ((f ⁻¹ᵁ V).ι ⁻¹ᵁ ((f ⁻¹ᵁ V').ι ''ᵁ W.unop))
    ((unitPlus f I F n V).val.app (op ((f ⁻¹ᵁ V').ι ''ᵁ W.unop)) x)) ?_
  refine Eq.trans ?_ (Eq.symm (congrArg
    (fun z => Stacks.restr (reesComapMod f I F (n + i)).val (homOfLE hA).op z)
    (mulRestrict_app f I F n i V'
      (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r) W.unop x)))
  refine Eq.trans (congrArg (fun t => reesMultipleSmul (I.comap f) F n i
      (op ((f ⁻¹ᵁ V).ι ''ᵁ ((f ⁻¹ᵁ V).ι ⁻¹ᵁ ((f ⁻¹ᵁ V').ι ''ᵁ W.unop))))
      (Stacks.restr (reesComapMod f I F n).val (homOfLE hA).op x) t) hr) ?_
  exact (reesMultipleSmul_restr (I.comap f) F n i hA x
    (Stacks.restr (reesPiece (I.comap f) i).val
      (homOfLE ((f ⁻¹ᵁ V').ι_image_le W.unop)).op
      (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r))).symm

/-- **The action is compatible with shrinking the open of the base.** Following
`Stacks.Blowup.mulHom` at `V` by the comparison of the extensions
(`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrictLE`) gives `mulHom` at `V'` for
the restricted section.

This is `restrictFunctor_map_mulHom` transported across
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` at `f⁻¹(V')`: naturality of its unit turns
the composite into the unit at `V'` followed by the direct image of a morphism of restrictions,
and that morphism is `Stacks.Blowup.mulRestrict` at `V'` because the restricted unit cancels. -/
public theorem mulHom_comp_extendRestrictLE (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules)
    (n i : ℤ) (V V' : Y.Opens) (hU : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    mulHom f I F n i V r ≫ extendRestrictLE hU (reesComapMod f I F (n + i)) =
      mulHom f I F n i V' (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r) := by
  have := isIso_restrictFunctor_map_unit_of_le hU (reesComapMod f I F (n + i))
  have hnat : mulHom f I F n i V r ≫
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V').ι).unit.app
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F (n + i)))) =
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V').ι).unit.app (reesComapMod f I F n) ≫
        (Scheme.Modules.pushforward (f ⁻¹ᵁ V').ι).map
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).map (mulHom f I F n i V r)) :=
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V').ι).unit.naturality _
  rw [extendRestrictLE, ← Category.assoc, hnat, Category.assoc, ← Functor.map_comp,
    restrictFunctor_map_mulHom f I F n i V V' hU r, Category.assoc, IsIso.hom_inv_id]
  rw [show (mulRestrict f I F n i V'
        (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r) ≫
      𝟙 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).obj
        (reesComapMod f I F (n + i)))) = mulRestrict f I F n i V'
          (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r) from
    Category.comp_id _]
  rfl

/-- The higher direct image of the comparison of extensions carries the unit at `V` to the unit
at `V'`. -/
private theorem unitDerived_comp_map_extendRestrictLE (f : X ⟶ Y) (I : Y.IdealSheafData)
    (F : X.Modules) (p : ℕ) (d : ℤ) (V V' : Y.Opens) (hU : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V) :
    unitDerived f I F p d V ≫ ((Scheme.Modules.pushforward f).rightDerived p).map
      (extendRestrictLE hU (reesComapMod f I F d)) = unitDerived f I F p d V' :=
  (Functor.map_comp _ _ _).symm.trans
    (congrArg ((Scheme.Modules.pushforward f).rightDerived p).map
      (unit_comp_extendRestrictLE hU (reesComapMod f I F d)))

/-- The higher direct image of the comparison of extensions carries `Stacks.Blowup.mulHom` at `V`
to `mulHom` at `V'` for the restricted section. -/
private theorem map_mulHom_comp_map_extendRestrictLE (f : X ⟶ Y) (I : Y.IdealSheafData)
    (F : X.Modules) (p : ℕ) (n i : ℤ) (V V' : Y.Opens) (hU : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    ((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i V r) ≫
      ((Scheme.Modules.pushforward f).rightDerived p).map
        (extendRestrictLE hU (reesComapMod f I F (n + i))) =
      ((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i V' (Stacks.restr
        (reesPiece (I.comap f) i).val (homOfLE hU).op r)) :=
  (Functor.map_comp _ _ _).symm.trans
    (congrArg ((Scheme.Modules.pushforward f).rightDerived p).map (mulHom_comp_extendRestrictLE f
      I F n i V V' hU r))

/-- The unit on sections over `V` is injective. -/
private theorem unitDerived_app_injective (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules)
    (p : ℕ) (n : ℤ) (V : Y.Opens) :
    Function.Injective ((unitDerived f I F p n V).app V) := fun a b h =>
  (unitDerived_inv_hom_app f I F p n V a).symm.trans
    ((congrArg (fun z => inv ((unitDerived f I F p n V).app V) z) h).trans
      (unitDerived_inv_hom_app f I F p n V b))

/-- The unit at `V'` of the restriction of the action at `V` is `R ᵖ f_*` of `mulHom` at `V'` on
the restricted section. -/
private theorem unitDerived_app_restr_smulSectionHom (f : X ⟶ Y) (I : Y.IdealSheafData)
    (F : X.Modules) (p : ℕ) (n i : ℤ) (V V' : Y.Opens) (g : (op V : (Opens Y)ᵒᵖ) ⟶ op V')
    (hU : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V)))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    (unitDerived f I F p (n + i) V').app V'
        (Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F (n +
          i))).val g
          (smulSectionHom f I F p n i V r x)) =
      (((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i V' (Stacks.restr
        (reesPiece (I.comap f) i).val (homOfLE hU).op r))).app V'
        (Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F
          n)).val g x) := by
  have step3 : (unitDerived f I F p (n + i) V).app V (smulSectionHom f I F p n i V r x) =
      (((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i V r)).app V x := by
    rw [smulSectionHom_apply, unitDerived_hom_inv_app]
  refine Eq.trans (congrArg (fun ψ : ((Scheme.Modules.pushforward f).rightDerived p).obj
    (reesComapMod f I F (n + i)) ⟶
      ((Scheme.Modules.pushforward f).rightDerived p).obj ((Scheme.Modules.pushforward (f ⁻¹ᵁ
        V').ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).obj (reesComapMod f I F (n + i)))) =>
      ψ.app V' (Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f
        I F (n + i))).val g
        (smulSectionHom f I F p n i V r x)))
    (unitDerived_comp_map_extendRestrictLE f I F p (n + i) V V' hU).symm) ?_
  refine Eq.trans (congrArg (fun z => (((Scheme.Modules.pushforward f).rightDerived p).map
    (extendRestrictLE hU (reesComapMod f I F (n + i)))).app V' z)
    (Stacks.restr_app (unitDerived f I F p (n + i) V).val g
      (smulSectionHom f I F p n i V r x))) ?_
  refine Eq.trans (congrArg (fun z => (((Scheme.Modules.pushforward f).rightDerived p).map
    (extendRestrictLE hU (reesComapMod f I F (n + i)))).app V'
    (Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
        (reesComapMod f I F (n + i))))).val g z)) step3) ?_
  refine Eq.trans (Stacks.restr_app (((Scheme.Modules.pushforward f).rightDerived p).map
    (extendRestrictLE hU (reesComapMod f I F (n + i)))).val g
    ((((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i V r)).app V x)) ?_
  refine Eq.trans (congrArg (fun z => Stacks.restr
    (((Scheme.Modules.pushforward f).rightDerived p).obj ((Scheme.Modules.pushforward (f ⁻¹ᵁ
      V').ι).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).obj
        (reesComapMod f I F (n + i))))).val g z)
    (congrArg (fun ψ : ((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n)
      ⟶
        ((Scheme.Modules.pushforward f).rightDerived p).obj ((Scheme.Modules.pushforward (f ⁻¹ᵁ
          V').ι).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).obj
            (reesComapMod f I F (n + i)))) => ψ.app V x)
      (map_mulHom_comp_map_extendRestrictLE f I F p n i V V' hU r))) ?_
  exact (Stacks.restr_app (((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i
    V' (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r))).val g x).symm

/-- **The action commutes with restriction on the base.** This is the `smul_naturality` law of a
graded module.

No compatibility of [Stacks, Tag 01E5] across nested opens is used, which is the whole point:
`Stacks.Blowup.mulHom` and the unit are morphisms of sheaves on all of `X`, so the comparison of
the two extensions is a morphism of sheaves on `X` too, and `R ᵖ f_*` of it is a morphism of
sheaves on `Y`, hence compatible with restriction for free. The two identities it satisfies —
`unit_comp_extendRestrictLE` and `mulHom_comp_extendRestrictLE` — then force the conclusion,
`Stacks.Blowup.isIso_unitDerived_app` providing the injectivity that cancels the unit at `V'`. -/
public theorem smulSectionHom_naturality (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ)
    (n i : ℤ) (V V' : Y.Opens) (g : (op V : (Opens Y)ᵒᵖ) ⟶ op V')
    (hU : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V)
    (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V)))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F (n +
      i))).val g
        (smulSectionHom f I F p n i V r x) =
      smulSectionHom f I F p n i V' (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r)
        (Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F
          n)).val g x) := by
  refine unitDerived_app_injective f I F p (n + i) V'
    ((unitDerived_app_restr_smulSectionHom f I F p n i V V' g hU r x).trans ?_)
  exact ((congrArg (fun z => (unitDerived f I F p (n + i) V').app V' z)
    (smulSectionHom_apply f I F p n i V'
      (Stacks.restr (reesPiece (I.comap f) i).val (homOfLE hU).op r)
      (Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj
        (reesComapMod f I F n)).val g x))).trans
    (unitDerived_hom_inv_app f I F p (n + i) V' _)).symm

/-- Two morphisms into extensions from `f⁻¹(V)` of ideal-power multiples whose degrees are
propositionally equal and which agree on sections induce heterogeneously equal sections after
`R ᵖ f_*` and division by the unit.

This is the one place where the equality of degrees is substituted; it is what turns the two
`HEq` laws of a graded module into the sectionwise identities of
`Stacks.Blowup.reesGradedModule`. -/
public theorem heq_inv_unitDerived_unitPlus_comp (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules)
    (p : ℕ) (n : ℤ) (V : Y.Opens) {d d' : ℤ} (hdd : d = d')
    (α : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n) ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F d))
    (β : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n) ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F d'))
    (hαβ : ∀ (W : (Opens ↥(f ⁻¹ᵁ V))ᵒᵖ)
      (w : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
        (reesComapMod f I F n)).val.obj W), HEq (α.val.app W w) (β.val.app W w))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    HEq (inv ((unitDerived f I F p d V).app V)
          ((((Scheme.Modules.pushforward f).rightDerived p).map (unitPlus f I F n V ≫
            (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map α)).app V x))
        (inv ((unitDerived f I F p d' V).app V)
          ((((Scheme.Modules.pushforward f).rightDerived p).map (unitPlus f I F n V ≫
            (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map β)).app V x)) := by
  subst hdd
  have hab : α = β := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext w
    exact eq_of_heq (hαβ W w)
  rw [hab]

/-- `R ᵖ f_*` of `Stacks.Blowup.mulHom` is the unit followed by `R ᵖ f_*` of the extension of
`Stacks.Blowup.mulRestrict`. -/
private theorem map_mulHom_eq (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ)
    (n i : ℤ) (V : Y.Opens) (r : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V))) :
    ((Scheme.Modules.pushforward f).rightDerived p).map (mulHom f I F n i V r) =
      unitDerived f I F p n V ≫
        ((Scheme.Modules.pushforward f).rightDerived p).map
          ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map (mulRestrict f I F n i V r)) :=
  (congrArg ((Scheme.Modules.pushforward f).rightDerived p).map (rfl : mulHom f I F n i V r =
    unitPlus f I F n V ≫ (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map
      (mulRestrict f I F n i V r))).trans (Functor.map_comp _ _ _)

/-- **Two successive actions are one `R ᵖ f_*` of a composite of multiplications.** Acting by a
section of `ℐⁱ𝒪_X` and then by one of `ℐʲ𝒪_X` divides by the unit twice, but the second
`Stacks.Blowup.mulHom` begins with that same unit, so the inner division cancels and what is
left is `R ᵖ f_*` of `mulRestrict ≫ mulRestrict`, divided by the unit once. -/
public theorem smulSectionHom_comp (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ)
    (n i j : ℤ) (V : Y.Opens)
    (s : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V)))
    (t : (reesPiece (I.comap f) j).val.obj (op (f ⁻¹ᵁ V)))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    smulSectionHom f I F p (n + i) j V t (smulSectionHom f I F p n i V s x) =
      inv ((unitDerived f I F p (n + i + j) V).app V)
        ((((Scheme.Modules.pushforward f).rightDerived p).map (unitPlus f I F n V ≫
          (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map
          (mulRestrict f I F n i V s ≫ mulRestrict f I F (n + i) j V t))).app V x) := by
  refine Eq.trans (smulSectionHom_apply f I F p (n + i) j V t _) ?_
  refine congrArg (fun z => inv ((unitDerived f I F p (n + i + j) V).app V) z) ?_
  refine Eq.trans (congrArg (fun ψ : ((Scheme.Modules.pushforward f).rightDerived p).obj
    (reesComapMod f I F (n + i)) ⟶
      ((Scheme.Modules.pushforward f).rightDerived p).obj ((Scheme.Modules.pushforward (f ⁻¹ᵁ
        V).ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
          (reesComapMod f I F (n + i + j)))) =>
      ψ.app V (smulSectionHom f I F p n i V s x)) (map_mulHom_eq f I F p (n + i) j V t)) ?_
  refine Eq.trans (congrArg (fun z => (((Scheme.Modules.pushforward f).rightDerived p).map
    ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map
      (mulRestrict f I F (n + i) j V t))).app V z)
    (Eq.trans (congrArg (fun z => (unitDerived f I F p (n + i) V).app V z)
        (smulSectionHom_apply f I F p n i V s x))
      (unitDerived_hom_inv_app f I F p (n + i) V _))) ?_
  have hgamma : mulHom f I F n i V s ≫ (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map
        (mulRestrict f I F (n + i) j V t) =
      unitPlus f I F n V ≫ (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map
        (mulRestrict f I F n i V s ≫ mulRestrict f I F (n + i) j V t) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun χ => unitPlus f I F n V ≫ χ)
        (Functor.map_comp (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι) _ _).symm)
  refine Eq.trans (congrArg (fun ψ : ((Scheme.Modules.pushforward f).rightDerived p).obj
    (reesComapMod f I F n) ⟶
      ((Scheme.Modules.pushforward f).rightDerived p).obj ((Scheme.Modules.pushforward (f ⁻¹ᵁ
        V).ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
          (reesComapMod f I F (n + i + j)))) => ψ.app V x)
    (Functor.map_comp ((Scheme.Modules.pushforward f).rightDerived p) (mulHom f I F n i V s)
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map
        (mulRestrict f I F (n + i) j V t))).symm) ?_
  exact congrArg (fun ψ : reesComapMod f I F n ⟶
      (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
          (reesComapMod f I F (n + i + j))) => (((Scheme.Modules.pushforward f).rightDerived p).map
            ψ).app V x) hgamma

/-- **The action is associative.** This is the `smul_mul` law of a graded module, at the level of
the section-wise action: it is the corresponding law of `Stacks.Blowup.reesGradedModule` on `X`,
carried across by `smulSectionHom_comp` and `heq_inv_unitDerived_unitPlus_comp`. -/
public theorem heq_smulSectionHom_mul (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ)
    (n i j : ℤ) (V : Y.Opens)
    (s : (reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V)))
    (t : (reesPiece (I.comap f) j).val.obj (op (f ⁻¹ᵁ V)))
    (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n), V)) :
    HEq (smulSectionHom f I F p (n + i) j V t (smulSectionHom f I F p n i V s x))
        (smulSectionHom f I F p n (i + j) V
          ((reesMultiplication (I.comap f) i j).app (op (f ⁻¹ᵁ V)) s t) x) := by
  refine HEq.trans (heq_of_eq (smulSectionHom_comp f I F p n i j V s t x)) ?_
  refine HEq.trans ?_ (heq_of_eq (smulSectionHom_apply f I F p n (i + j) V
    ((reesMultiplication (I.comap f) i j).app (op (f ⁻¹ᵁ V)) s t) x).symm)
  refine heq_inv_unitDerived_unitPlus_comp f I F p n V (add_assoc n i j)
    (mulRestrict f I F n i V s ≫ mulRestrict f I F (n + i) j V t)
    (mulRestrict f I F n (i + j) V
      ((reesMultiplication (I.comap f) i j).app (op (f ⁻¹ᵁ V)) s t)) ?_ x
  intro W w
  refine HEq.trans ((reesGradedModule (I.comap f) F).smul_mul n i j
    (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) w
    (Stacks.restr (reesPiece (I.comap f) i).val
      (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op s)
    (Stacks.restr (reesPiece (I.comap f) j).val
      (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op t)) (heq_of_eq ?_)
  exact congrArg (fun z => reesMultipleSmul (I.comap f) F n (i + j)
      (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) w z)
    (Stacks.BilinearMap.restr_bil (reesMultiplication (I.comap f) i j)
      (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op s t).symm

/-- **The unit of the Rees algebra acts as the identity.** This is the `smul_one` law of a graded
module: multiplication by the unit is the identity on the restrictions to `f⁻¹(V)`
(`Stacks.Blowup.reesGradedModule`'s own `smul_one`), so the action is `R ᵖ f_*` of the unit
divided by itself. -/
public theorem heq_smulSectionHom_one (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ)
    (n : ℤ) (V : Y.Opens) (x : Γ(((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod
      f I F n), V)) :
    HEq (smulSectionHom f I F p n 0 V
      ((reesUnit (I.comap f)).eval (op (f ⁻¹ᵁ V))) x) x := by
  refine HEq.trans (heq_of_eq (smulSectionHom_apply f I F p n 0 V
    ((reesUnit (I.comap f)).eval (op (f ⁻¹ᵁ V))) x)) ?_
  refine HEq.trans (heq_inv_unitDerived_unitPlus_comp f I F p n V (add_zero n)
    (mulRestrict f I F n 0 V ((reesUnit (I.comap f)).eval (op (f ⁻¹ᵁ V))))
    (𝟙 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n))) ?_ x)
    (heq_of_eq ?_)
  · intro W w
    refine HEq.trans (heq_of_eq (congrArg (fun z => reesMultipleSmul (I.comap f) F n 0
        (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) w z)
      (Stacks.restr_sections (reesPiece (I.comap f) 0).val (reesUnit (I.comap f))
        (homOfLE ((f ⁻¹ᵁ V).ι_image_le W.unop)).op))) ?_
    exact (reesGradedModule (I.comap f) F).smul_one n (op ((f ⁻¹ᵁ V).ι ''ᵁ W.unop)) w
  · refine Eq.trans (congrArg (fun ψ : reesComapMod f I F n ⟶
        (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n)) =>
        inv ((unitDerived f I F p n V).app V) ((((Scheme.Modules.pushforward f).rightDerived p).map
          ψ).app V x))
      (Eq.trans (congrArg (fun χ => unitPlus f I F n V ≫ χ)
          (CategoryTheory.Functor.map_id (Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι)
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj (reesComapMod f I F n))))
        (Category.comp_id _))) ?_
    exact unitDerived_inv_hom_app f I F p n V x

/-- **[Stacks, Tag 02O7]: the graded `⨁ₙ ℐⁿ`-module `⨁ₙ R ᵖ f_*(ℐⁿℱ)` on the base, in every
degree `p`.**  This is the structure the setup paragraph of the source obtains "by localizing and
then sheafifying": the maps `ℐⁱ ⊗_{𝒪_Y} R ᵖ f_*(ℐⁿℱ) ⟶ R ᵖ f_*(ℐⁿ⁺ⁱℱ)`, presented as the
biadditive maps on sections that `SheafOfModules.GradedModule` consumes, together with the four
laws.

`Stacks.Blowup.pushforwardReesGradedModule` is the same statement for `p = 0`, and is **not**
superseded by this one: there the action is the multiplication of the Rees algebra on sections,
by `rfl`, whereas here it divides by the higher direct image of the unit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, and the two agree at `p = 0` only through
`R ⁰ f_* ≅ f_*`. -/
@[stacks 02O7 "⨁ₙ R ᵖ f_*(ℐⁿℱ) is a graded ⨁ₙ ℐⁿ-module on the base, in every degree p",
  ega "III 3.3.1" "special case"]
public def pushforwardReesGradedModulePlus (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules)
    (p : ℕ) : SheafOfModules.GradedModule (reesGradedAlgebra I) where
  piece n := ((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n)
  smul n i U := smulPlus f I F p n i U
  smul_smul_left n i U r x y :=
    smulSectionHom_smul f I F p n i U.unop (reesPieceComapSection f I i U y) r x
  smul_smul_right n i U r x y :=
    (congrArg (fun z => smulSectionHom f I F p n i U.unop z x)
        (reesPieceComapSection_smul f I i U r y)).trans
      (smulSectionHom_smul_right f I F p n i U.unop r
        (reesPieceComapSection f I i U y) x)
  smul_naturality n i {U V} φ x y := by
    have hU : f ⁻¹ᵁ V.unop ≤ f ⁻¹ᵁ U.unop := fun _ hx => leOfHom φ.unop hx
    refine Eq.trans (smulSectionHom_naturality f I F p n i U.unop V.unop φ hU
      (reesPieceComapSection f I i U y) x) ?_
    exact congrArg (fun z => smulSectionHom f I F p n i V.unop z
        (Stacks.restr (((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F
          n)).val φ x))
      (PresheafOfModules.naturality_apply (reesPieceComap f I i).val φ y).symm
  smul_mul n i j U x y z := by
    refine HEq.trans (heq_smulSectionHom_mul f I F p n i j U.unop
      (reesPieceComapSection f I i U y) (reesPieceComapSection f I j U z) x) ?_
    exact heq_of_eq (congrArg (fun w => smulSectionHom f I F p n (i + j) U.unop w x)
      (reesPieceComap_mul f I i j U.unop y z).symm)
  smul_one n U x := by
    refine HEq.trans (heq_of_eq (congrArg (fun w => smulSectionHom f I F p n 0 U.unop w x)
      (reesPieceComap_one f I U.unop))) ?_
    exact heq_smulSectionHom_one f I F p n U.unop x

/-- The pieces of `pushforwardReesGradedModulePlus` are the `p`-th higher direct images of the
ideal-power multiples of `ℱ`. -/
@[simp] public theorem pushforwardReesGradedModulePlus_piece (f : X ⟶ Y)
    (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ) (n : ℤ) :
    (pushforwardReesGradedModulePlus f I F p).piece n =
      ((Scheme.Modules.pushforward f).rightDerived p).obj (reesComapMod f I F n) :=
  rfl

/-- The action of `pushforwardReesGradedModulePlus` is `Stacks.Blowup.smulPlus`. -/
@[simp] public theorem pushforwardReesGradedModulePlus_smul (f : X ⟶ Y)
    (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ) (n i : ℤ) (V : (Opens Y)ᵒᵖ) :
    (pushforwardReesGradedModulePlus f I F p).smul n i V = smulPlus f I F p n i V :=
  rfl

end Stacks.Blowup

end

end
