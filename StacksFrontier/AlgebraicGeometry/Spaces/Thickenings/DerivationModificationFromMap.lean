module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationModificationStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardSquareZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf

/-!
# The derivation attached to an `𝒪_X`-linear map `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`

Let `X ⊂ X'` and `Y ⊂ Y'` be closed subspaces of algebraic spaces over a scheme `S` contained in
a big fppf site, with `X ⊂ X'` a **first order thickening**, let `a' : X' ⟶ Y'` and
`a : X ⟶ Y` satisfy `i_X ≫ a' = a ≫ i_Y`, and let `p : Y' ⟶ T` be a structure morphism.  An
`𝒪_X`-linear map

`θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`

gives rise to the `𝒪_T`-derivation `D` of [Stacks Project, Tag 04D0], the middle map of the
displayed composite of [Stacks Project, Tag 0619]

`𝒪_{Y'} ⟶ 𝒪_Y ⟶ a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}`.

This file builds `D` in the **direct image** form `𝒪_{Y'} ⟶ (a')_*𝒪_{X'}`, which is the form the
source's displayed composite has and the form in which the sum `α = (a')^♯ + D` of Tag 04D0 is a
homomorphism of sheaves of commutative rings on one site, proves the four sectionwise equations
of `Stacks.Sites.RingSheafDerivation` (additivity, compatibility with restriction, the Leibniz
rule and the vanishing of the products of values, the last being where the first order hypothesis
enters), and assembles them into a `Stacks.Sites.RingSheafDerivation` along `(a')^♯`.

## Main definitions

* `AlgebraicGeometry.Space.conormalPushforwardι`: the coefficient map
  `(i_X ≫ a')_*𝒞_{X/X'} ⟶ (a')_*𝒪_{X'}`, the composition comparison of Stacks 03LU followed by
  the direct image along `a'` of the inclusion
  `AlgebraicGeometry.Space.firstOrderConormalModuleι` of the conormal module of a first order
  thickening into the structure sheaf.
* `AlgebraicGeometry.Space.thickeningDerivationMapOfAmbient`: `θ` read as a map out of
  `(i_X ≫ a')^*Ω_{Y'/T}`, by the composition comparison of inverse images and the canonical map
  `i_Y^*Ω_{Y'/T} ⟶ Ω_{Y/T}` of Stacks 04CX.
* `AlgebraicGeometry.Space.thickeningDerivation`: Equation (0619) —
  `AlgebraicGeometry.Space.derivationDirectImageEquiv` — applied at `X ⟶ Y'` and `p`, giving an
  `𝒪_T`-derivation of `𝒪_{Y'}` with values in `(i_X ≫ a')_*𝒞_{X/X'}`.
* `AlgebraicGeometry.Space.thickeningStructureDerivation`: that derivation postcomposed with the
  coefficient map, so that its values lie in `(a')_*𝒪_{X'}`.
* `AlgebraicGeometry.Space.thickeningDerivationFun`: its sectionwise family.
* `AlgebraicGeometry.Space.thickeningRingSheafDerivation`: `D` as a
  `Stacks.Sites.RingSheafDerivation` along `(a')^♯`.

## Main results

* `AlgebraicGeometry.Space.thickeningDerivationFun_add`,
  `AlgebraicGeometry.Space.thickeningDerivationFun_naturality` and
  `AlgebraicGeometry.Space.thickeningDerivationFun_leibniz`: additivity, compatibility with
  restriction and the Leibniz rule.
* `AlgebraicGeometry.Space.thickeningDerivationFun_mul_eq_zero`: the products of values of `D`
  vanish, by the first order hypothesis.

## Implementation notes

**Why the derivation is taken in the direct image form.**  Tag 04D0 writes
`α = (a')^♯ + D : a^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`, and `Stacks.Sites.RingSheafDerivation` is stated for a
homomorphism of sheaves of commutative rings on one site, so either form could be used.  The
inverse image form cannot: nothing in this development describes the sections of
`(a')^{-1}𝒪_{Y'}`, which is a sheafified left Kan extension, while the direct image form is
exactly what Equation (0619) produces.  The two are adjunct, so no generality is lost.

**Why the equations are proved in the `RingCat` spelling.**  The ring the values live in is the
direct image `(a')_*𝒪_{X'}`, which this development carries in two spellings: the `RingCat`-valued
`AlgebraicGeometry.Space.structureRingSheafDirectImage`, which is the target of
`AlgebraicGeometry.Space.structureSharp` and over which the direct image of modules is taken, and
the `CommRingCat`-valued `(pushforwardCommRingFunctor _).obj 𝒪_{X'}`, which is the target of
`AlgebraicGeometry.Space.structureSharpCommRing` and so of the `fSharp` field of
`AlgebraicGeometry.RingedToposHom`.  The two have the same sections and the same operations, by
`rfl` — but *instance synthesis does not unify the two spellings*, so an `HMul` whose two
arguments are written in different spellings is not found at all.  Every equation here is
therefore written in the `RingCat` spelling, which is the one the module structure of the
direct image is defined over, and the single crossing to the `CommRingCat` spelling is made in
`AlgebraicGeometry.Space.thickeningRingSheafDerivation`, where the goal fixes the types.

**The Leibniz rule is `rfl` on top of Equation (0619).**  The scalar action of `𝒪_{Y'}` on
`(a')_*𝒪_{X'}` is restriction of scalars along `(a')^♯` of the action of `(a')_*𝒪_{X'}` on
itself, and the action of a transported ring on the transported unit module is the transported
multiplication — `CategoryTheory.Sheaf.moduleSMulHom` at `SheafOfModules.unit` *is*
`CategoryTheory.Sheaf.ringMulHom` — so `x • n` and `(a')^♯(x) * n` are the same term.  Nothing
has to be computed.

**The three equations are instantiations of generic ones.**  `Derivation.d_map` and
`Derivation.d_mul` applied directly at the geometric instantiation exhaust the heartbeat budget:
the unifier re-decides that the module `(a')_*𝒪_{X'}` is a module over
`𝒪_{Y'} ⋙ forget₂ CommRingCat RingCat`, which is the unfolding of
`AlgebraicGeometry.Space.smallEtaleRingedSite` that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapStructureSheaf.lean` record as expensive.
Stated once for a *variable* module and a *variable* derivation
(`AlgebraicGeometry.Space.derivation_d_map`, `AlgebraicGeometry.Space.derivation_d_mul`) and then
instantiated, they cost nothing: Lean does not recheck a proved statement's internal defeqs.

**The scalar action of the generic Leibniz rule is named by a `letI`.**  The modules of
`AlgebraicGeometry.Space.derivation_d_mul` are indexed by `Stacks.SheafOfModules.Tensor.ringSheaf`,
a plain `def` which instance search does not unfold, so the scalar action is not found; the
`letI` binds the canonical `CategoryTheory.ModuleCat.isModule`, term-identical to that instance.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' Y' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
  (hZ : IsFirstOrderThickening B S hS X' Z.1) (a' : X' ⟶ Y')

section Chain

/-- The coefficient map of [Stacks Project, Tag 04D0]. -/
noncomputable def conormalPushforwardι :
    (modulePushforward B S hS (subspaceInclusion B S hS X' Z ≫ a')).obj
        (conormalModule B S hS X' Z) ⟶
      (modulePushforward B S hS a').obj (structureUnitModule B S hS X') :=
  (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X' Z) a').inv.app
      (conormalModule B S hS X' Z) ≫
    (modulePushforward B S hS a').map (firstOrderConormalModuleι B S hS Z hZ)

/-- **The inclusion of the conormal module of a first order thickening into the structure sheaf
takes its values in the defining ideal.**  By construction
`AlgebraicGeometry.Space.firstOrderConormalModuleι` is the inverse of
`AlgebraicGeometry.Space.firstOrderConormalModuleIso` followed by the inclusion of the defining
ideal sheaf, so a value of it is the coercion of a section of that subsheaf. -/
theorem firstOrderConormalModuleι_app_mem_definingIdealAt
    (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (s : ((modulePullback B S hS (subspaceInclusion B S hS X' Z) ⋙
      modulePushforward B S hS (subspaceInclusion B S hS X' Z)).obj
        (definingIdealSheaf B S hS X' Z).toSheafOfModules).val.obj U) :
    ((firstOrderConormalModuleι B S hS Z hZ).val.app U) s ∈
      definingIdealAt B S hS X' Z U :=
  (((firstOrderConormalModuleIso B S hS Z hZ).inv.val.app U) s).2

variable {T : AlgebraicSpaces B S hS} (W : ClosedSubspaces B S hS Y'.1) (p : Y' ⟶ T)
  (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W.1.toFunctor, W.2.1⟩)

/-- `θ` read as a map out of the inverse image along `X ⟶ Y'` of `Ω_{Y'/T}`. -/
noncomputable def thickeningDerivationMapOfAmbient
    (hcompat : subspaceInclusion B S hS X' Z ≫ a' = a ≫ subspaceInclusion B S hS Y' W)
    (θ : (modulePullback B S hS a).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS Y' W ≫ p)) ⟶
      conormalModule B S hS X' Z) :
    (modulePullback B S hS (subspaceInclusion B S hS X' Z ≫ a')).obj
        (sheafOfDifferentials B S hS p) ⟶
      conormalModule B S hS X' Z :=
  eqToHom (congrArg (fun k => (modulePullback B S hS k).obj (sheafOfDifferentials B S hS p))
      hcompat) ≫
    (modulePullbackCompIso B S hS a (subspaceInclusion B S hS Y' W)).inv.app
      (sheafOfDifferentials B S hS p) ≫
    (modulePullback B S hS a).map
      (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS Y' W) p) ≫ θ

variable (hcompat : subspaceInclusion B S hS X' Z ≫ a' = a ≫ subspaceInclusion B S hS Y' W)
  (θ : (modulePullback B S hS a).obj
      (sheafOfDifferentials B S hS (subspaceInclusion B S hS Y' W ≫ p)) ⟶
    conormalModule B S hS X' Z)

/-- Equation (0619) at `X ⟶ Y'`: the `𝒪_T`-derivation of `𝒪_{Y'}` attached to `θ`. -/
noncomputable def thickeningDerivation :
    ((modulePushforward B S hS (subspaceInclusion B S hS X' Z ≫ a')).obj
        (conormalModule B S hS X' Z)).val.Derivation'
      (structureSharpInverseImage B S hS p).hom :=
  derivationDirectImageEquiv B S hS (subspaceInclusion B S hS X' Z ≫ a') p
    (conormalModule B S hS X' Z)
    (thickeningDerivationMapOfAmbient B S hS Z a' W p a hcompat θ)

/-- The derivation of `𝒪_{Y'}` with values in `(a')_*(i_X)_*𝒞_{X/X'}`, the direct image along
`a'` of the conormal module read on `X'`.  This is
`AlgebraicGeometry.Space.thickeningDerivation` moved across the composition comparison of
direct images of Stacks 03LU. -/
noncomputable def thickeningConormalDerivation :
    ((modulePushforward B S hS a').obj
        ((modulePushforward B S hS (subspaceInclusion B S hS X' Z)).obj
          (conormalModule B S hS X' Z))).val.Derivation'
      (structureSharpInverseImage B S hS p).hom :=
  (thickeningDerivation B S hS Z a' W p a hcompat θ).postcomp
    ((modulePushforwardCompIso B S hS (subspaceInclusion B S hS X' Z) a').inv.app
      (conormalModule B S hS X' Z)).val

/-- The derivation `D : 𝒪_{Y'} ⟶ (a')_*𝒪_{X'}` of [Stacks Project, Tag 04D0]. -/
noncomputable def thickeningStructureDerivation :
    ((modulePushforward B S hS a').obj (structureUnitModule B S hS X')).val.Derivation'
      (structureSharpInverseImage B S hS p).hom :=
  (thickeningConormalDerivation B S hS Z a' W p a hcompat θ).postcomp
    ((modulePushforward B S hS a').map (firstOrderConormalModuleι B S hS Z hZ)).val

/-- The sectionwise family `D` of [Stacks Project, Tag 04D0]. -/
noncomputable def thickeningDerivationFun (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x : (structureRingSheaf B S hS Y').obj.obj V') :
    ToType ((structureRingSheafDirectImage B S hS a').obj.obj V') :=
  (thickeningStructureDerivation B S hS Z hZ a' W p a hcompat θ).d x

end Chain

section Generic

variable {Y'' T'' : AlgebraicSpaces B S hS} (q : Y'' ⟶ T'')
  (N : Modules.{u, u} B S hS Y''.1 Y''.2)
  (D : N.val.Derivation' (structureSharpInverseImage B S hS q).hom)

/-- **A derivation commutes with restriction**, at a variable module and a variable derivation.
This is `Derivation.d_map`. -/
theorem derivation_d_map {V' V'' : (SmallEtale B S hS Y''.1)ᵒᵖ} (h : V' ⟶ V'')
    (x : (structureRingSheaf B S hS Y'').obj.obj V') :
    D.d (((structureRingSheaf B S hS Y'').obj.map h).hom x) = (N.val.map h) (D.d x) :=
  D.d_map h x

/-- The Leibniz rule, at a variable module and a variable derivation, for the canonical module
structure `CategoryTheory.ModuleCat.isModule` of the section module. -/
theorem derivation_d_mul {V' : (SmallEtale B S hS Y''.1)ᵒᵖ}
    (x y : (structureRingSheaf B S hS Y'').obj.obj V') :
    letI : Module ((structureRingSheaf B S hS Y'').obj.obj V') (N.val.obj V') :=
      (N.val.obj V').isModule
    D.d (x * y) = x • D.d y + y • D.d x :=
  D.d_mul x y

/-- **A derivation kills the image of the inverse image of `𝒪_T`**, at a variable module and a
variable derivation.  This is `Derivation.d_app`. -/
theorem derivation_d_app {V' : (SmallEtale B S hS Y''.1)ᵒᵖ}
    (t : (inverseImageStructureSheaf B S hS q).obj.obj V') :
    D.d ((structureSharpInverseImage B S hS q).hom.app V' t) = 0 :=
  D.d_app t

end Generic

section Fields

variable {X' Y' T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
  (hZ : IsFirstOrderThickening B S hS X' Z.1) (a' : X' ⟶ Y')
  (W : ClosedSubspaces B S hS Y'.1) (p : Y' ⟶ T)
  (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W.1.toFunctor, W.2.1⟩)
  (hcompat : subspaceInclusion B S hS X' Z ≫ a' = a ≫ subspaceInclusion B S hS Y' W)
  (θ : (modulePullback B S hS a).obj
      (sheafOfDifferentials B S hS (subspaceInclusion B S hS Y' W ≫ p)) ⟶
    conormalModule B S hS X' Z)

/-- **Additivity** of the sectionwise family `D` of [Stacks Project, Tag 04D0]: the first
equation of `Stacks.Sites.RingSheafDerivation`. -/
theorem thickeningDerivationFun_add (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x y : (structureRingSheaf B S hS Y').obj.obj V') :
    thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' (x + y) =
      thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' x +
        thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' y :=
  map_add (thickeningStructureDerivation B S hS Z hZ a' W p a hcompat θ).d x y

/-- **The restriction maps agree** whether the direct image of the structure sheaf of `X'` is
read as a sheaf of `𝒪_{Y'}`-modules through `AlgebraicGeometry.Space.modulePushforward` at the
unit module or as the sheaf of rings `(a')_*𝒪_{X'}` of Stacks 03G8. -/
theorem modulePushforward_structureUnitModule_val_map_apply
    {V' V'' : (SmallEtale B S hS Y'.1)ᵒᵖ} (h : V' ⟶ V'')
    (n : ((modulePushforward B S hS a').obj (structureUnitModule B S hS X')).val.obj V') :
    ((((modulePushforward B S hS a').obj
        (structureUnitModule B S hS X')).val.map h) n :
        ToType ((structureRingSheafDirectImage B S hS a').obj.obj V'')) =
      ((structureRingSheafDirectImage B S hS a').obj.map h).hom n := rfl

/-- **Compatibility with restriction** of the sectionwise family `D` of
[Stacks Project, Tag 04D0]: the second equation of `Stacks.Sites.RingSheafDerivation`, read in the
`RingCat` spelling of `(a')_*𝒪_{X'}`. -/
theorem thickeningDerivationFun_naturality {V' V'' : (SmallEtale B S hS Y'.1)ᵒᵖ} (h : V' ⟶ V'')
    (x : (structureRingSheaf B S hS Y').obj.obj V') :
    (((structureRingSheafDirectImage B S hS a').obj.map h).hom
        (thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' x)) =
      thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V''
        (((structureRingSheaf B S hS Y').obj.map h).hom x) :=
  (modulePushforward_structureUnitModule_val_map_apply B S hS a' h
      (thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' x)).symm.trans
    (derivation_d_map B S hS p
      ((modulePushforward B S hS a').obj (structureUnitModule B S hS X'))
      (thickeningStructureDerivation B S hS Z hZ a' W p a hcompat θ) h x).symm

/-- **The Leibniz rule** for the sectionwise family `D` of [Stacks Project, Tag 04D0]:
`D(xy) = (a')^♯(x) D(y) + (a')^♯(y) D(x)`, the third equation of
`Stacks.Sites.RingSheafDerivation`. -/
theorem thickeningDerivationFun_leibniz (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x y : (structureRingSheaf B S hS Y').obj.obj V') :
    thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' (x * y) =
      ((structureSharp B S hS a').hom.app V').hom x *
          thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' y +
        ((structureSharp B S hS a').hom.app V').hom y *
          thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' x :=
  derivation_d_mul B S hS p
    ((modulePushforward B S hS a').obj (structureUnitModule B S hS X'))
    (thickeningStructureDerivation B S hS Z hZ a' W p a hcompat θ) x y

/-- **The derivation's values come from the conormal module**, read through the direct image of
sheaves of sets. -/
theorem thickeningDerivationFun_eq_map (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x : (structureRingSheaf B S hS Y').obj.obj V') :
    thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' x =
      (smallEtaleDirectImage B S hS a' ⋙
          CategoryTheory.Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y'.1) V').map
        ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
          (firstOrderConormalModuleι B S hS Z hZ))
        ((thickeningConormalDerivation B S hS Z a' W p a hcompat θ).d x) :=
  Stacks.Sheaves.ToposPullback.pullbackModuleMap_val_app_apply
    (SmallEtale.topology B S hS Y'.1) (smallEtaleDirectImage B S hS a')
    (structureRingSheaf B S hS X') (firstOrderConormalModuleι B S hS Z hZ) V'
    ((thickeningConormalDerivation B S hS Z a' W p a hcompat θ).d x)

/-- **The sectionwise family `D` of [Stacks Project, Tag 04D0] is `𝒪_T`-linear**: it kills the
image of a section of the inverse image of `𝒪_T` under `p^♯`. -/
theorem thickeningDerivationFun_structureSharpInverseImage (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (t : (inverseImageStructureSheaf B S hS p).obj.obj V') :
    thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V'
        ((structureSharpInverseImage B S hS p).hom.app V' t) = 0 :=
  derivation_d_app B S hS p
    ((modulePushforward B S hS a').obj (structureUnitModule B S hS X'))
    (thickeningStructureDerivation B S hS Z hZ a' W p a hcompat θ) t

/-- **The products of values of `D` vanish**, the fourth equation of
`Stacks.Sites.RingSheafDerivation` and the one where the first order hypothesis enters: both
values come from the conormal module, whose sections lie in the defining ideal, which squares to
zero on a first order thickening. -/
theorem thickeningDerivationFun_mul_eq_zero (V' : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x y : (structureRingSheaf B S hS Y').obj.obj V') :
    thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' x *
        thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ V' y = 0 := by
  rw [thickeningDerivationFun_eq_map B S hS Z hZ a' W p a hcompat θ V' x,
    thickeningDerivationFun_eq_map B S hS Z hZ a' W p a hcompat θ V' y]
  exact CategoryTheory.Sheaf.ringMulObj_map_eq_zero (structureRingSheaf B S hS X')
    (smallEtaleDirectImage B S hS a' ⋙
      CategoryTheory.Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y'.1) V')
    ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
      (firstOrderConormalModuleι B S hS Z hZ))
    (fun U s s' => mul_eq_zero_of_mem_definingIdealAt B S hS Z hZ
      (firstOrderConormalModuleι_app_mem_definingIdealAt B S hS Z hZ U s)
      (firstOrderConormalModuleι_app_mem_definingIdealAt B S hS Z hZ U s')) _ _

/-- **The structure map of `a'` read on sections in the two spellings.**  The `fSharp` field of
`AlgebraicGeometry.RingedToposHom` at `AlgebraicGeometry.Space.smallEtaleRingedToposHom` is the
`CommRingCat`-valued structure map, and on sections it is the `RingCat`-valued one, which is what
the module structure of the direct image is defined over.  This is
`AlgebraicGeometry.Space.structureSharpCommRing_app_apply` at the `fSharp` spelling. -/
theorem smallEtaleRingedToposHom_fSharp_app_apply
    {X'' Y'' : AlgebraicSpaces B S hS} (f : X'' ⟶ Y'')
    (V' : (SmallEtale B S hS Y''.1)ᵒᵖ)
    (x : (structureRingSheaf B S hS Y'').obj.obj V') :
    ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app V').hom x =
      ((structureSharp B S hS f).hom.app V').hom x :=
  structureSharpCommRing_app_apply B S hS f V' x

/-- **The derivation `D` of [Stacks Project, Tag 04D0] as a
`Stacks.Sites.RingSheafDerivation` along the structure map `(a')^♯`.**  Its four equations are
the four theorems above; the only thing done here is the crossing from the `RingCat` spelling of
`(a')_*𝒪_{X'}` to the `CommRingCat` spelling, which the `fSharp` field of
`AlgebraicGeometry.RingedToposHom` is written in. -/
noncomputable def thickeningRingSheafDerivation :
    Stacks.Sites.RingSheafDerivation (smallEtaleRingedToposHom B S hS a').fSharp where
  toFun := thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ
  map_add' := thickeningDerivationFun_add B S hS Z hZ a' W p a hcompat θ
  leibniz V' x y := by
    refine (thickeningDerivationFun_leibniz B S hS Z hZ a' W p a hcompat θ V' x y).trans ?_
    rw [smallEtaleRingedToposHom_fSharp_app_apply B S hS a' V' x,
      smallEtaleRingedToposHom_fSharp_app_apply B S hS a' V' y]
    rfl
  mul_eq_zero := thickeningDerivationFun_mul_eq_zero B S hS Z hZ a' W p a hcompat θ
  naturality := fun h x => thickeningDerivationFun_naturality B S hS Z hZ a' W p a hcompat θ h x

/-- The sectionwise family of `AlgebraicGeometry.Space.thickeningRingSheafDerivation` is
`AlgebraicGeometry.Space.thickeningDerivationFun`. -/
theorem thickeningRingSheafDerivation_toFun :
    (thickeningRingSheafDerivation B S hS Z hZ a' W p a hcompat θ).toFun =
      thickeningDerivationFun B S hS Z hZ a' W p a hcompat θ := rfl

end Fields

end AlgebraicGeometry.Space



end
