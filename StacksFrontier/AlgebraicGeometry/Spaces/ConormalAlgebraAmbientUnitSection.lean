module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators

/-!
# The ambient factor of the canonical map of conormal algebras on the unit sections

Let
```
Z --i--→ X
         |
         g
         ↓
         X'
```
be a morphism `i : Z ⟶ X` of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, followed by a morphism `g : X ⟶ X'`.  Write `𝓘 = Ker(i^♯) ⊆ 𝒪_X` and
`𝓙 = Ker((i ≫ g)^♯) ⊆ 𝒪_{X'}`.  The ambient factor of the canonical map of
[Stacks Project, Tag 09RS] is built in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean` out of the morphism of
`𝒪_X`-modules

`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap : g^*(𝓙ⁿ) ⟶ 𝓘ⁿ`,

and that morphism is obtained by transposing a chartwise linear map of sections twice: along the
chartwise universal property of the direct image of Stacks 03LU and then along the adjunction
`g^* ⊣ g_*` of Stacks 03D7.  A double transpose says nothing directly about the values of the
morphism on local sections, and
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_transpose` — the characterising
property — describes it only after both transposes have been undone.

This file reads it on sections.  Over a commutative diagram `d` of étale scheme charts over `g`,
with chart `U` of `X` and chart `V` of `X'`, a section `s` of `𝓙ⁿ` over `V` has a canonical image
in `g^*(𝓙ⁿ)` over `U` — the chart component of the unit of the Stacks 03D7 adjunction, which is
`AlgebraicGeometry.Space.modulePullbackUnitSection` — and the content proved here is that
`kernelIdealSheafZPowPullbackMap` carries it to the pullback of the regular function `s` along
the vertical morphism of `d`.  So on the canonical sections the morphism is literally `g^♯`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackHomFMap_kernelIdealSheafZPowPullbackMap`: the chartwise
  transpose of `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` is the chartwise linear
  map of sections `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap` it was built from.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection`:
  **the value of the map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` on a unit section** is the value of the chartwise linear
  map of sections, and
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection_coe`
  spells that out as pullback of regular functions along the vertical morphism of the chart
  diagram.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection_coe` and
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection`: **the
  map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` is multiplicative on the unit sections** — it carries the unit section of a
  product of two homogeneous sections to the product of their images, in the graded algebra of
  the powers of `𝓘`.  This is the arithmetic content of the multiplicativity of the ambient
  factor: on the canonical sections the map is pullback of regular functions, which is a
  homomorphism of rings, and the multiplication of `SheafOfModules.reesGradedAlgebra` is
  multiplication of sections of the structure sheaf.

## Implementation notes

**Why the statement is for arbitrary morphisms and not for immersions.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean`, nothing below uses any
property of `i` or `g`; the statement specialises to the immersions of Stacks 09RS.

**Why the chartwise transpose is identified first.**  The identification of the values of the
chartwise transpose with the values of the morphism on the unit sections is generic — it is
`AlgebraicGeometry.Space.modulePullbackHomFMap_app`, which holds for every morphism out of a
module pullback.  All that is specific to the case at hand is that the chartwise transpose of
`kernelIdealSheafZPowPullbackMap` *is* `kernelIdealSheafZPowFMap`, which is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_transpose` read through the definition
of `AlgebraicGeometry.Space.modulePullbackHomFMap`.  Keeping those two steps apart is what keeps
the proofs short: no unfolding of the two transposes happens at the concrete modules, where the
small étale ringed topos of an algebraic space makes every definitional unfolding expensive.

## What is not proved

* **This is not yet the value on a generator section of the pullback of graded algebras.**  The
  multiplicativity criterion
  `Stacks.Sheaves.GradedAlgebraPullback.homOfMulUnitGeneratorSection` asks for the value of the
  degreewise family on the sections
  `Stacks.Sheaves.GradedAlgebraPullback.generatorSection f B n U (1 ⊗ₜ x)`, with `x` an
  arbitrary local section of the inverse image `g⁻¹(𝓙ⁿ)`.  Reading the unit section proved here
  in that form needs the factorisation of the unit of the Stacks 03D7 adjunction into the unit
  of the inverse image of sheaves of sets followed by the change-of-rings unit
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit`.

  That factorisation *is* available:
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app` of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepTwo.lean` says that the unit
  of `AlgebraicGeometry.Space.modulePullbackAdjunction` is, on underlying sheaves of sets, the
  transpose of `pullbackScalarUnit` along the adjunction of small étale topoi of Stacks 03G2,
  part (3); it is the transported form of
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_modulesPullbackUnit`, and
  the comparison `AlgebraicGeometry.Space.modulePushforwardIso` between the two adjunctions
  contributes nothing, being the identity on underlying sheaves of sets by
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardIso_hom_app`.

  What is still missing is one step further on, and it is geometric rather than a matter of
  reduction: `AlgebraicGeometry.Space.modulePullbackUnitSection` is the *chart component* of the
  unit, that is `AlgebraicGeometry.Space.modulePushforwardCounitApp` applied to it, and the
  transpose above has to be evaluated there.  That asks for a chart-level description of a
  section of an inverse image on the small étale site of an algebraic space — the image of a
  section over a chart of `X'` in `g⁻¹(𝓙ⁿ)` over a chart of `X` — and no such description is
  available for a general `g`: `AlgebraicGeometry.Space.smallToposMorphism_inverseImage_obj_obj`
  of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionInverseImage.lean` supplies one
  only for an étale `g`, and the transposed descriptions
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushedSectionEquiv` and
  `CategoryTheory.sectionEquivSmall` describe sections of a *direct* image as morphisms out of an
  inverse image, not sections of an inverse image.  The locality in `x` that
  `Stacks.Sheaves.GradedAlgebraPullback.homOfMulUnitGeneratorSectionOfLocal` allows is what such
  a description would have to be combined with, and neither half is below.
* **No `@[stacks 09RS]` attribute.**  Stacks 09RS asserts a map of graded `𝒪_Z`-algebras
  `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`; a formula for the ambient degreewise map on the canonical
  sections is not that statement, exactly as the module documentation of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean` records.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' : AlgebraicSpaces B S hS} (i : Z ⟶ X) (g : X ⟶ X')

/-- **The chartwise transpose of the map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` is the chartwise linear map of sections
it was built from.**

`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` is the transpose along the Stacks 03D7
adjunction of the transpose along the chartwise universal property of the direct image of
`AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`, and
`AlgebraicGeometry.Space.modulePullbackHomFMap` undoes exactly those two transposes; this is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_transpose` in that spelling. -/
theorem modulePullbackHomFMap_kernelIdealSheafZPowPullbackMap (n : ℤ) :
    modulePullbackHomFMap B S hS g
        (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules
        (kernelIdealSheafZPowPullbackMap B S hS i g n) =
      kernelIdealSheafZPowFMap B S hS i g n :=
  kernelIdealSheafZPowPullbackMap_transpose B S hS i g n

/-- **The value of the map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` on a unit section.**  On a commutative diagram `d` of
étale scheme charts over `g`, the canonical section of `g^*(𝓙ⁿ)` over the chart of `X` attached
to a section `s` of `𝓙ⁿ` over the chart of `X'` — the chart component of the unit of the
Stacks 03D7 adjunction — is carried by
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` to the value at `d` and `s` of the
chartwise linear map of sections `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`.

The values of the chartwise transpose of a morphism out of a module pullback are its values on
the unit sections (`AlgebraicGeometry.Space.modulePullbackHomFMap_app`), and the chartwise
transpose here is `kernelIdealSheafZPowFMap` by
`AlgebraicGeometry.Space.modulePullbackHomFMap_kernelIdealSheafZPowPullbackMap`. -/
theorem kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection (n : ℤ)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules.val.obj (op d.V)) :
    (kernelIdealSheafZPowPullbackMap B S hS i g n).val.app (op d.U)
        (modulePullbackUnitSection B S hS g
          (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules d s) =
      (kernelIdealSheafZPowFMap B S hS i g n).app d s :=
  (modulePullbackHomFMap_app B S hS g
      (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules
      (kernelIdealSheafZPowPullbackMap B S hS i g n) d s).symm.trans
    (congrArg (fun ξ : ModuleFMap B S hS g
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules
        (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules => ξ.app d s)
      (modulePullbackHomFMap_kernelIdealSheafZPowPullbackMap B S hS i g n))

/-- **The value of the map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` on a unit section is pullback of regular functions.**
On a commutative diagram `d` of étale scheme charts over `g`, the regular function underlying
the value of `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` on the canonical section
of `s` is the pullback of `s` along the vertical morphism of `d`.

This is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection` followed
by the chartwise formula `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap_app_coe`. -/
theorem kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection_coe (n : ℤ)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules.val.obj (op d.V)) :
    ((kernelIdealSheafZPowPullbackMap B S hS i g n).val.app (op d.U)
        (modulePullbackUnitSection B S hS g
          (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules d s)).1 =
      (chartDiagramPullback B S hS g d).hom s.1 :=
  (congrArg Subtype.val
      (kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection B S hS i g n d s)).trans
    (kernelIdealSheafZPowFMap_app_coe B S hS i g n d s)

/-! ### Multiplicativity on the unit sections -/

/-- **The map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` is multiplicative on the unit sections**, read on the underlying
regular functions.  On a commutative diagram `d` of étale scheme charts over `g`, the regular
function underlying the value on the unit section of a product `st` of homogeneous sections of
the graded algebra of the powers of `𝓙` is the product of the two regular functions underlying
the values on the unit sections of `s` and of `t`.

The multiplication of `SheafOfModules.reesGradedAlgebra` is multiplication of sections of the
structure sheaf, and on the unit sections the map is pullback of regular functions along the
vertical morphism of `d`
(`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection_coe`),
which is a homomorphism of rings. -/
theorem kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection_coe (p q : ℤ)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (kernelIdealSheafZPow B S hS (i ≫ g) p).toSheafOfModules.val.obj (op d.V))
    (t : (kernelIdealSheafZPow B S hS (i ≫ g) q).toSheafOfModules.val.obj (op d.V)) :
    SheafOfModules.reesVal (kernelIdealSheaf B S hS i)
        ((kernelIdealSheafZPowPullbackMap B S hS i g (p + q)).val.app (op d.U)
          (modulePullbackUnitSection B S hS g
            (kernelIdealSheafZPow B S hS (i ≫ g) (p + q)).toSheafOfModules d
            (((kernelIdealGradedAlgebra B S hS (i ≫ g)).mul p q).app (op d.V) s t))) =
      SheafOfModules.reesVal (kernelIdealSheaf B S hS i)
          ((kernelIdealSheafZPowPullbackMap B S hS i g p).val.app (op d.U)
            (modulePullbackUnitSection B S hS g
              (kernelIdealSheafZPow B S hS (i ≫ g) p).toSheafOfModules d s)) *
        SheafOfModules.reesVal (kernelIdealSheaf B S hS i)
          ((kernelIdealSheafZPowPullbackMap B S hS i g q).val.app (op d.U)
            (modulePullbackUnitSection B S hS g
              (kernelIdealSheafZPow B S hS (i ≫ g) q).toSheafOfModules d t)) :=
  (kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection_coe B S hS i g (p + q) d
        (((kernelIdealGradedAlgebra B S hS (i ≫ g)).mul p q).app (op d.V) s t)).trans
    ((map_mul (chartDiagramPullback B S hS g d).hom
          (SheafOfModules.reesVal (kernelIdealSheaf B S hS (i ≫ g)) s)
          (SheafOfModules.reesVal (kernelIdealSheaf B S hS (i ≫ g)) t)).trans
      (congrArg₂ (fun a b ↦ a * b)
        (kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection_coe
          B S hS i g p d s).symm
        (kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection_coe
          B S hS i g q d t).symm))

/-- **The map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` is multiplicative on the unit sections**, as an equation in the
graded algebra of the powers of `𝓘`: the value on the unit section of a product is the product,
in `AlgebraicGeometry.Space.kernelIdealGradedAlgebra` for `i`, of the values on the unit sections
of the two factors.

This is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection_coe`, the
two sections of `𝓘^{p+q}` being equal as soon as their underlying regular functions are.

It is the arithmetic content of the multiplicativity of the ambient factor of
[Stacks Project, Tag 09RS].  What stands between it and a homomorphism of sheaves of graded
algebras `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` is the hypothesis of
`Stacks.Sheaves.GradedAlgebraPullback.homOfMulUnitGeneratorSectionOfLocal`, which tests the
degreewise family on the generator sections of the pure tensors `1 ⊗ x` rather than on the unit
sections of a chart diagram; the `What is not proved` section records what identifying the two
is waiting for. -/
theorem kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection (p q : ℤ)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (kernelIdealSheafZPow B S hS (i ≫ g) p).toSheafOfModules.val.obj (op d.V))
    (t : (kernelIdealSheafZPow B S hS (i ≫ g) q).toSheafOfModules.val.obj (op d.V)) :
    (kernelIdealSheafZPowPullbackMap B S hS i g (p + q)).val.app (op d.U)
        (modulePullbackUnitSection B S hS g
          (kernelIdealSheafZPow B S hS (i ≫ g) (p + q)).toSheafOfModules d
          (((kernelIdealGradedAlgebra B S hS (i ≫ g)).mul p q).app (op d.V) s t)) =
      ((kernelIdealGradedAlgebra B S hS i).mul p q).app (op d.U)
        ((kernelIdealSheafZPowPullbackMap B S hS i g p).val.app (op d.U)
          (modulePullbackUnitSection B S hS g
            (kernelIdealSheafZPow B S hS (i ≫ g) p).toSheafOfModules d s))
        ((kernelIdealSheafZPowPullbackMap B S hS i g q).val.app (op d.U)
          (modulePullbackUnitSection B S hS g
            (kernelIdealSheafZPow B S hS (i ≫ g) q).toSheafOfModules d t)) :=
  SheafOfModules.reesPiece_ext (kernelIdealSheaf B S hS i)
    (kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection_coe B S hS i g p q d s t)

end AlgebraicGeometry.Space

end
