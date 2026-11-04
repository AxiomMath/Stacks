module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraComap
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraModule
public import StacksCore.Tactic.StacksAttribute

/-!
# The graded module of ideal-power multiples on the base

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` a sheaf of `𝒪_X`-modules and `ℐ ⊆ 𝒪_Y` a
quasi-coherent sheaf of ideals.  [Stacks, Tag 02O7] constructs, for every cohomological degree
`p`, `𝒪_Y`-module maps
`ℐⁿ ⊗_{𝒪_Y} R ᵖ f_*(ℐᵐℱ) ⟶ R ᵖ f_*(ℐⁿ⁺ᵐℱ)`
and observes that they make `⨁_{n ≥ 0} R ᵖ f_*(ℐⁿℱ)` a graded module over the Rees algebra
`⨁_{n ≥ 0} ℐⁿ` **on `Y`**.

This file builds those maps, and that graded module, in degree `p = 0`, where `R ⁰ f_*` is the
pushforward `f_*` itself; `Stacks.Blowup.pushforwardReesGradedModulePlus` does the same for
every `p`, by a different route (see the implementation notes).

## Main definitions

* `Stacks.Blowup.pushforwardReesSmul`: the map `ℐⁿ ⊗_{𝒪_Y} f_*(ℐᵐℱ) ⟶ f_*(ℐⁿ⁺ᵐℱ)`, presented as
  a biadditive map on sections over an open of `Y` — which is how a map out of a tensor product
  of sheaves of modules is given, and is the `smul` field the graded-module structure below
  consumes.
* `Stacks.Blowup.pushforwardReesGradedModule`: **the graded `⨁ₙ ℐⁿ`-module `⨁ₙ f_*(ℐⁿℱ)` on
  `Y`**, i.e. the structure [Stacks, Tag 02O7] describes, in degree zero.

## Implementation notes

The content is the "localizing" step of the source: over an open `V` of `Y` a section `r` of
`ℐⁿ` is not a section of anything on `X`, but its inverse image is a section of `(ℐ𝒪_X)ⁿ` over
`f⁻¹(V)`, and the multiplication of the Rees algebra of `ℐ𝒪_X` on the ideal-power multiples of
`ℱ` then acts.  The inverse image on sections is `Stacks.Blowup.reesPieceComap`, and it is a
morphism of *sheaves* of `𝒪_Y`-modules, so its compatibility with shrinking `V` is automatic —
that is exactly what makes the family of maps over the opens of `Y` into a map of sheaves on
`Y`, which the source calls "localizing and then sheafifying".

In degree zero no comparison of derived functors is needed, because the sections of `f_*ℳ` over
`V` are literally the sections of `ℳ` over `f⁻¹(V)`
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`, which holds by `rfl`).  Every axiom of
the graded-module structure therefore reduces to the corresponding axiom of
`Stacks.Blowup.reesGradedModule` on `X`, carried across by the multiplicativity and unitality of
`reesPieceComap` (`Stacks.Blowup.reesPieceComap_mul`, `Stacks.Blowup.reesPieceComap_one`); no
mathematics is redone here.

**The same statement in positive degree `p`** is `Stacks.Blowup.pushforwardReesGradedModulePlus`.
It is not a generalisation of the structure here and does not supersede it: there the action of a
section of `ℐⁱ` over `V` is read through the extension `𝒢 ↦ (j_{f⁻¹V})_*(𝒢|_{f⁻¹V})` and divided
by the higher direct image of the unit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, whereas here it is the multiplication of
the Rees algebra on sections, by `rfl`; the two agree at `p = 0` only through `R ⁰ f_* ≅ f_*`.
That construction also does *not* use the comparison
`(R ᵖ f_* ℳ)|_V ≅ R ᵖ (f|_{f⁻¹V})_*(ℳ|_{f⁻¹V})` across nested opens
(`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_zero_ofLE`, which the tree has
in degree zero only); that is precisely what it is arranged to avoid.

## References

* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Blowup

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData)
  (F : SheafOfModules.{u} X.ringCatSheaf)

/-- The inverse image on sections of the degree-`i` piece of the Rees algebra, as an additive
map `ℐⁱ(V) → (ℐ𝒪_X)ⁱ(f⁻¹V)`.  It is `Stacks.Blowup.reesPieceComap` evaluated at `V`, read
through the identification of the sections of a pushforward over `V` with the sections over
`f⁻¹(V)`. -/
public def reesPieceComapSection (i : ℤ) (U : (Opens Y)ᵒᵖ) :
    ((reesPiece I i).val.obj U) →+ ((reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ U.unop))) :=
  ((reesPieceComap f I i).val.app U).hom.toAddMonoidHom

/-- **The map `ℐⁱ ⊗_{𝒪_Y} f_*(ℐⁿℱ) ⟶ f_*(ℐⁿ⁺ⁱℱ)` of [Stacks, Tag 02O7]**, presented on
sections over an open `V` of `Y` as a biadditive map.

A section of `f_*(ℐⁿℱ)` over `V` is a section of `ℐⁿℱ` over `f⁻¹(V)`; a section `r` of `ℐⁱ` over
`V` becomes, by `reesPieceComapSection`, a section of `(ℐ𝒪_X)ⁱ` over `f⁻¹(V)`; and the
multiplication `Stacks.Blowup.reesMultipleSmul` of the Rees algebra of `ℐ𝒪_X` on the
ideal-power multiples of `ℱ` sends the pair to a section of `ℐⁿ⁺ⁱℱ` over `f⁻¹(V)`. -/
public def pushforwardReesSmul (n i : ℤ) (U : (Opens Y)ᵒᵖ) :
    (((SheafOfModules.pushforward f.toRingCatSheafHom).obj
        (reesMultiple (I.comap f) n F).toSheafOfModules).val.obj U) →+
      ((reesPiece I i).val.obj U) →+
        (((SheafOfModules.pushforward f.toRingCatSheafHom).obj
          (reesMultiple (I.comap f) (n + i) F).toSheafOfModules).val.obj U) :=
  AddMonoidHom.mk'
    (fun x => (reesMultipleSmul (I.comap f) F n i (op (f ⁻¹ᵁ U.unop)) x).comp
      (reesPieceComapSection f I i U))
    (fun x y => by
      refine AddMonoidHom.ext fun r => ?_
      exact congrArg (fun φ : _ →+ _ => φ (reesPieceComapSection f I i U r))
        (map_add (reesMultipleSmul (I.comap f) F n i (op (f ⁻¹ᵁ U.unop))) x y))

/-- **[Stacks, Tag 02O7]: the graded `⨁ₙ ℐⁿ`-module `⨁ₙ f_*(ℐⁿℱ)` on the base, in degree
zero.**  The maps `pushforwardReesSmul` make the pushforwards of the ideal-power multiples of
`ℱ` a graded module over the Rees algebra of `ℐ` on `Y`.

Since `f_*` is left exact it is `R ⁰ f_*`, so this is the structure the source puts on
`⨁ₙ R ᵖ f_*(ℐⁿℱ)` for `p = 0`.  Each axiom is the corresponding axiom of
`Stacks.Blowup.reesGradedModule` on `X`, transported along the multiplicativity and unitality of
`Stacks.Blowup.reesPieceComap`; the compatibility with restriction on `Y` is inherited from
`reesPieceComap` being a morphism of sheaves. -/
@[stacks 02O7 "⨁ₙ f_*(ℐⁿℱ) is a graded ⨁ₙ ℐⁿ-module on the base"]
public def pushforwardReesGradedModule : SheafOfModules.GradedModule (reesGradedAlgebra I) where
  piece n := (SheafOfModules.pushforward f.toRingCatSheafHom).obj
    (reesMultiple (I.comap f) n F).toSheafOfModules
  smul n i U := pushforwardReesSmul f I F n i U
  smul_smul_left n i U r x y :=
    (reesGradedModule (I.comap f) F).smul_smul_left n i (op (f ⁻¹ᵁ U.unop)) _ x
      (reesPieceComapSection f I i U y)
  smul_smul_right n i U r x y := by
    refine Eq.trans
      (congrArg (fun t => reesMultipleSmul (I.comap f) F n i (op (f ⁻¹ᵁ U.unop)) x t)
        (map_smul ((reesPieceComap f I i).val.app U).hom r y)) ?_
    exact (reesGradedModule (I.comap f) F).smul_smul_right n i (op (f ⁻¹ᵁ U.unop)) _ x _
  smul_naturality n i {U V} φ x y := by
    have h : V.unop ≤ U.unop := leOfHom φ.unop
    have hpre : f ⁻¹ᵁ V.unop ≤ f ⁻¹ᵁ U.unop := fun _ hx => h hx
    have hg : ConcreteCategory.hom ((reesPiece (I.comap f) i).val.map (homOfLE hpre).op)
          (reesPieceComapSection f I i U y) =
        reesPieceComapSection f I i V (ConcreteCategory.hom ((reesPiece I i).val.map φ) y) :=
      (PresheafOfModules.naturality_apply (reesPieceComap f I i).val φ y).symm
    refine Eq.trans (reesMultipleSmul_restr (I.comap f) F n i hpre x
      (reesPieceComapSection f I i U y)) ?_
    exact congrArg (fun t => reesMultipleSmul (I.comap f) F n i (op (f ⁻¹ᵁ V.unop))
      (Stacks.restr (reesMultiple (I.comap f) n F).toSheafOfModules.val (homOfLE hpre).op x) t) hg
  smul_mul n i j U x y z := by
    refine HEq.trans
      ((reesGradedModule (I.comap f) F).smul_mul n i j (op (f ⁻¹ᵁ U.unop)) x
        (reesPieceComapSection f I i U y) (reesPieceComapSection f I j U z))
      (heq_of_eq ?_)
    exact congrArg (fun t => reesMultipleSmul (I.comap f) F n (i + j) (op (f ⁻¹ᵁ U.unop)) x t)
      (reesPieceComap_mul f I i j U.unop y z).symm
  smul_one n U x := by
    refine HEq.trans (heq_of_eq ?_)
      ((reesGradedModule (I.comap f) F).smul_one n (op (f ⁻¹ᵁ U.unop)) x)
    exact congrArg (fun t => reesMultipleSmul (I.comap f) F n 0 (op (f ⁻¹ᵁ U.unop)) x t)
      (reesPieceComap_one f I U.unop)

/-- The pieces of `pushforwardReesGradedModule` are the pushforwards of the ideal-power
multiples of `ℱ`. -/
@[simp] public theorem pushforwardReesGradedModule_piece (n : ℤ) :
    (pushforwardReesGradedModule f I F).piece n =
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj
        (reesMultiple (I.comap f) n F).toSheafOfModules :=
  rfl

/-- The action of `pushforwardReesGradedModule` is `pushforwardReesSmul`. -/
@[simp] public theorem pushforwardReesGradedModule_smul (n i : ℤ) (U : (Opens Y)ᵒᵖ) :
    (pushforwardReesGradedModule f I F).smul n i U = pushforwardReesSmul f I F n i U :=
  rfl

end Stacks.Blowup

end
