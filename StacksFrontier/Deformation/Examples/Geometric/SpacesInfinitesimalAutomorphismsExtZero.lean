module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCanonicalExtZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal

/-!
# `Ext⁰` out of the naive cotangent complex of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `F` be an
`𝒪_X`-module.  The naive cotangent complex `NL_{X/Y}` of Stacks 0D0V is a complex of
`𝒪_X`-modules whose sections live one universe above the structure rings (the objects of the
small étale site of `X` do), so the coefficient of its `Ext` groups is `F` with its sections
raised to that universe.  This file proves

`Ext⁰_{𝒪_X}(NL_{X/Y}, F) = Hom_{𝒪_X}(Ω_{X/Y}, F) = Der_Y(𝒪_X, F)`,

with `Ω_{X/Y}` the sheaf of differentials of Stacks 04CT and `Der_Y` the `f♯`-derivations, all
three as abelian groups.  The first equality is the degree `0` half of Stacks 0D0Y: `NL_{X/Y}`
lives in degrees `-1, 0` and its `H⁰` is the module of differentials of `f♯` (Stacks 08TY); the
second is the universal property of `Ω_{X/Y}`.  The two modules of differentials in play, the
one of Stacks 04BN at the universe of `NL_{X/Y}` and the one of Stacks 04CT at the universe of
the structure rings, are compared through the derivations they corepresent, which do not see the
universe of the sections.

## Main definitions

* `AlgebraicGeometry.Space.differentialsHomAddEquiv`: `Hom(Ω_{X/Y}, F) ≃+ Der_Y(𝒪_X, F)`.
* `AlgebraicGeometry.Space.derivationULiftAddEquiv`: derivations into the universe lift of `F`
  are derivations into `F`.
* `AlgebraicGeometry.Space.naiveCotangentExtZeroAddEquivDerivations`:
  `Ext⁰(NL_{X/Y}, F) ≃+ Der_Y(𝒪_X, F)`.
* `AlgebraicGeometry.Space.naiveCotangentExtZeroAddEquivDifferentialsHom`:
  `Ext⁰(NL_{X/Y}, F) ≃+ Hom(Ω_{X/Y}, F)`.

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- The `f♯`-derivations of `𝒪_X` with values in an `𝒪_X`-module form an abelian group, under
pointwise addition.  This is `AlgebraicGeometry.SheafOfModules.derivationAddCommGroup`, stated at
the spelling of the ring sheaf of `Modules`, which instance search does not unfold. -/
instance derivationAddCommGroupModules.{m} (f : X ⟶ Y) (F : Modules.{u, m} B S hS X.1 X.2) :
    AddCommGroup
      (PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom) :=
  AlgebraicGeometry.SheafOfModules.derivationAddCommGroup (M := F.val) _

/-- **The universal property of `Ω_{X/Y}`, additively.**  Postcomposition with the universal
derivation `d_{X/Y}` is an isomorphism of abelian groups `Hom(Ω_{X/Y}, F) ≃+ Der_Y(𝒪_X, F)`. -/
def differentialsHomAddEquiv (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    (sheafOfDifferentials B S hS f ⟶ F) ≃+
      PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom :=
  { differentialsHomEquiv B S hS f F with
    map_add' := fun g h => by ext U x; rfl }

/-- `differentialsHomAddEquiv` sends `g : Ω_{X/Y} ⟶ F` to the universal derivation `d_{X/Y}`
followed by `g`. -/
theorem differentialsHomAddEquiv_apply (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (g : sheafOfDifferentials B S hS f ⟶ F) :
    differentialsHomAddEquiv B S hS f F g = (universalDerivation B S hS f).postcomp g.val :=
  rfl

/-- **Derivations into a universe lift.**  A derivation of `𝒪_X` over `f⁻¹𝒪_Y` with values in
the sections of `F` raised to a larger universe is a derivation with values in `F`: both are
compatible families of additive maps into the same groups, up to `ULift`. -/
def derivationULiftAddEquiv (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    PresheafOfModulesOfCommRing.Derivation'
        ((Stacks.SheafOfModules.moduleULift.{u + 1, u} _).obj F).val
        (structureSharpInverseImage B S hS f).hom ≃+
      PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom where
  toFun D :=
    { d := fun {U} =>
        { toFun := fun x => (D.d (X := U) x).down
          map_zero' := congrArg ULift.down (D.d (X := U)).map_zero
          map_add' := fun x y => congrArg ULift.down ((D.d (X := U)).map_add x y) }
      d_mul := fun {U} a b => congrArg ULift.down (D.d_mul (X := U) a b)
      d_map := fun {U V} g x => congrArg ULift.down (D.d_map g x)
      d_app := fun {U} a => congrArg ULift.down (D.d_app (X := U) a) }
  invFun D :=
    { d := fun {U} =>
        { toFun := fun x => ULift.up (D.d (X := U) x)
          map_zero' := congrArg ULift.up (D.d (X := U)).map_zero
          map_add' := fun x y => congrArg ULift.up ((D.d (X := U)).map_add x y) }
      d_mul := fun {U} a b => congrArg ULift.up (D.d_mul (X := U) a b)
      d_map := fun {U V} g x => congrArg ULift.up (D.d_map g x)
      d_app := fun {U} a => congrArg ULift.up (D.d_app (X := U) a) }
  left_inv D := by ext U x; rfl
  right_inv D := by ext U x; rfl
  map_add' D E := by ext U x; rfl

/-- The category of sheaves of `𝒪_X`-modules in which the naive cotangent complex of Stacks 0D0V
lives: modules over the structure sheaf of the small étale ringed topos of `X`, with sections one
universe above the structure rings. -/
abbrev NaiveCotangentModules (X : AlgebraicSpaces B S hS) :=
  _root_.SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)

/-- **The universal property of the module of differentials of Stacks 04BN, additively**, at
the structure map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` and the universe of `NL_{X/Y}`. -/
def siteDifferentialsHomAddEquiv (f : X ⟶ Y) (G : NaiveCotangentModules B S hS X) :
    (AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u + 1, u, u}
        (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
        (structureSharpInverseImage B S hS f) ⟶ G) ≃+
      PresheafOfModulesOfCommRing.Derivation' G.val (structureSharpInverseImage B S hS f).hom :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun g => (SheafOfModules.universalDerivationOfSite.{u, u + 1, u, u}
          (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
          (structureSharpInverseImage B S hS f)).postcomp g.val)
      (fun g h => by ext U x; rfl))
    ⟨fun g h hgh => (SheafOfModules.existsUnique_descDerivation.{u, u + 1, u, u} _ _ _ G _).unique
      rfl hgh.symm, fun D => (SheafOfModules.existsUnique_descDerivation.{u, u + 1, u, u} _ _ _ G
      D).exists⟩

/-- The coefficient `F` of the `Ext` groups out of `NL_{X/Y}`: an `𝒪_X`-module with its sections
raised to the universe of `NL_{X/Y}`. -/
abbrev naiveCotangentCoefficient (F : Modules.{u, u} B S hS X.1 X.2) :
    NaiveCotangentModules B S hS X :=
  (Stacks.SheafOfModules.moduleULift.{u + 1, u} _).obj F

variable [HasDerivedCategory.{w} (NaiveCotangentModules B S hS X)]

/-- **`Ext⁰` out of `NL_{X/Y}` is the group of derivations.**  For a morphism `f : X ⟶ Y` of
algebraic spaces and an `𝒪_X`-module `F`, `Ext⁰_{𝒪_X}(NL_{X/Y}, F) = Der_Y(𝒪_X, F)`, the
coefficient of the `Ext` group being `F` with its sections raised to the universe of
`NL_{X/Y}`. -/
def naiveCotangentExtZeroAddEquivDerivations (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (naiveCotangentCoefficient B S hS F)) 0 ≃+
      PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom :=
  ((Stacks.SheafOfModules.naiveCotangentExtZeroAddEquiv.{u, u + 1, u, u, w}
      (SmallEtale.topology B S hS X.1) (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
      (naiveCotangentCoefficient B S hS F)).trans
    (siteDifferentialsHomAddEquiv B S hS f _)).trans
    (derivationULiftAddEquiv B S hS f F)

/-- **The degree `0` identification of Stacks 0D0Y, as maps.**  For a morphism `f : X ⟶ Y` of
algebraic spaces and an `𝒪_X`-module `F`, `Ext⁰_{𝒪_X}(NL_{X/Y}, F) = Hom_{𝒪_X}(Ω_{X/Y}, F)`,
with `Ω_{X/Y}` the sheaf of differentials of Stacks 04CT: both are the `f♯`-derivations of
`𝒪_X` with values in `F`. -/
def naiveCotangentExtZeroAddEquivDifferentialsHom (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (naiveCotangentCoefficient B S hS F)) 0 ≃+
      (sheafOfDifferentials B S hS f ⟶ F) :=
  (naiveCotangentExtZeroAddEquivDerivations B S hS f F).trans
    (differentialsHomAddEquiv B S hS f F).symm

end AlgebraicGeometry.Space

end
