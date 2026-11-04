module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqInverseImage

/-!
# The difference of two lifts as a bundled derivation

`StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation` proves the four equations which
say that the sectionwise difference `f - g` of two homomorphisms `f, g : R ⟶ 𝒪_X` of sheaves of
rings agreeing after `i^♯` is a derivation with values in the defining ideal of the closed
subspace: additivity, the Leibniz rule, the vanishing on a base sheaf of rings and the
compatibility with restriction.  This file packages those four equations as a
`PresheafOfModules.Derivation'`, which is the notion of derivation that the sheaf of relative
differentials of [Stacks Project, Tag 04CT] corepresents and that Equation (0619),
`AlgebraicGeometry.Space.derivationDirectImageEquiv`, consumes.

Only one thing has to be arranged for the bundling: `PresheafOfModules.Derivation'` wants the
differentiated sheaf of rings to be valued in `CommRingCat`, and the coefficients to be a module
over *it*.  So the source is taken to be the sheaf of rings underlying a sheaf of commutative
rings — which is what the inverse image `(b')^{-1}𝒪_{Y'}` of a structure sheaf is — and the
defining ideal is read as a module over it by restricting scalars along `f`, which is exactly
the module structure for which the Leibniz rule of
`AlgebraicGeometry.Space.liftDifference_smul_add_smul` is stated.

## Main definitions

* `AlgebraicGeometry.Space.liftDifferenceCoefficients`: the defining ideal of the closed
  subspace, read as a presheaf of modules over the differentiated sheaf of commutative rings by
  restriction of scalars along `f`.
* `AlgebraicGeometry.Space.liftDifferenceDerivation`: the four equations of
  `AlgebraicGeometry.Space.liftDifference`, bundled.
* `AlgebraicGeometry.Space.liftPairDerivation`: the same at the pair of structure maps of two
  morphisms of a thickening agreeing on its closed subspace, which is the derivation `D` of
  [Stacks Project, Tag 0618].

## Main results

* `AlgebraicGeometry.Space.liftDifferenceDerivation_d` and
  `AlgebraicGeometry.Space.liftPairDerivation_d`: the bundled derivation differentiates a
  section to the difference of the two maps on it, so nothing about it has to be unfolded.

## Implementation notes

The four fields are the four equations proved earlier, applied verbatim; only the restriction-compatibility
needs `Subtype.ext`, because `AlgebraicGeometry.Space.liftDifference_naturality` is stated on the
underlying sections of the structure sheaf while the field is an equation in the defining ideal.

## What is not done here

The bundled derivation differentiates `(b')^{-1}𝒪_{Y'}`, a sheaf of rings on the small étale site
of `X'`, with values in the defining ideal there.  Turning it into a section of the acting sheaf
`AlgebraicGeometry.Space.liftActionSheaf` of [Stacks Project, Tag 061D] — an `𝒪_X`-linear map
`a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` — needs, in addition:

* the transposition of a derivation of an inverse image into a derivation with values in a
  direct image, `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`, at this
  instantiation;
* Equation (0619), `AlgebraicGeometry.Space.derivationDirectImageEquiv`, which turns the
  resulting derivation `𝒪_Y ⟶ a_*𝒞_{X/X'}` into the `𝒪_X`-linear map;
* the identification of the defining ideal with the pushed-forward conormal module, which for a
  first-order thickening is `AlgebraicGeometry.Space.firstOrderConormalModuleIso`, already used
  sectionwise in `AlgebraicGeometry.Space.firstOrderConormalModuleι_liftDifference`;
* the identification of the small étale site of `X` with that of `X'`, which for a thickening is
  `AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The bundling -/

section Bundle

variable {Rc₀ Rc : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (φc : Rc₀ ⟶ Rc)
  (f g : (sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj Rc ⟶ structureRingSheaf B S hS X)

/-- **The defining ideal of a closed subspace, read as a module over the differentiated sheaf of
commutative rings.**  The defining ideal `𝓘_Z ⊆ 𝒪_X` is a module over `𝒪_X`; a derivation of a
sheaf of rings `R` with values in it is linear for the `R`-action obtained by restricting scalars
along `f : R ⟶ 𝒪_X`, which is the action for which
`AlgebraicGeometry.Space.liftDifference_smul_add_smul` states the Leibniz rule. -/
noncomputable def liftDifferenceCoefficients :
    PresheafOfModules.{u} (Rc.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  PresheafOfModules.restrictScalarsObj
    (definingIdealSheaf B S hS X Z).toSubmodule.toPresheafOfModules f.hom

/-- The sections of `AlgebraicGeometry.Space.liftDifferenceCoefficients` over an étale chart are
the defining ideal there, with scalars restricted along `f`. -/
theorem liftDifferenceCoefficients_obj (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (liftDifferenceCoefficients B S hS Z f).obj U =
      (ModuleCat.restrictScalars (f.hom.app U).hom).obj
        (ModuleCat.of ((structureRingSheaf B S hS X).obj.obj U)
          (definingIdealAt B S hS X Z U)) :=
  rfl

/-- **The difference of two lifts, as a bundled derivation.**  For `f, g : R ⟶ 𝒪_X` which agree
after the structure map of a first-order thickening `Z ⊆ X` and which agree on a base sheaf of
rings `R₀`, the sectionwise difference `f - g` is a `Derivation'` of `R` over `R₀` with values in
the defining ideal of `Z`.

Its four fields are `AlgebraicGeometry.Space.liftDifference_add`,
`AlgebraicGeometry.Space.liftDifference_smul_add_smul`,
`AlgebraicGeometry.Space.liftDifference_naturality` and
`AlgebraicGeometry.Space.liftDifference_app_eq_zero`. -/
@[stacks 0618 "the derivation D of the source, bundled as a `PresheafOfModules.Derivation'`, \
for two abstract algebra maps"]
noncomputable def liftDifferenceDerivation (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (hφ : (sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫ f =
      (sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫ g) :
    (liftDifferenceCoefficients B S hS Z f).Derivation' φc.hom where
  d {U} := AddMonoidHom.mk' (fun r ↦ liftDifference B S hS Z f g hfg U r)
    (liftDifference_add B S hS Z f g hfg U)
  d_mul {_} a b := liftDifference_smul_add_smul B S hS Z f g hZ hfg _ a b
  d_map {_ _} m x := Subtype.ext (liftDifference_naturality B S hS Z f g hfg m x).symm
  d_app {_} a := liftDifference_app_eq_zero B S hS Z
    ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map φc) f g hfg hφ _ a

/-- The bundled derivation differentiates a section to the difference of the two maps on it. -/
theorem liftDifferenceDerivation_d (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (hφ : (sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫ f =
      (sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫ g)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : (Rc.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) :
    (liftDifferenceDerivation B S hS Z φc f g hZ hfg hφ).d r =
      liftDifference B S hS Z f g hfg U r :=
  rfl

end Bundle

/-! ### The derivation of two morphisms of a thickening -/

section Restrict

variable {X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')
  (h : IsThickening.inclusion B S hS hG ≫ a' = IsThickening.inclusion B S hS hG ≫ b')

variable {Rc₀ : Sheaf (SmallEtale.topology B S hS X'.1) CommRingCat.{u}}
  (φc : Rc₀ ⟶ inverseImageStructureSheaf B S hS b')

/-- **The derivation `D` of [Stacks Project, Tag 0618].**  Let `G ⊂ X'` be a first-order
thickening of algebraic spaces with inclusion `i : X ⟶ X'` and let `a', b' : X' ⟶ Y'` be two
morphisms with `i ≫ a' = i ≫ b'`, both of them maps of `R₀`-algebras for a sheaf of commutative
rings `R₀` on the small étale site of `X'` — for two morphisms of thickenings over `B` the last
condition is that both are maps of `𝒪_B`-algebras.  Then the difference of the two structure maps
`(a')^♯, (b')^♯ : (b')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`, the first read through
`AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq`, is a derivation of
`(b')^{-1}𝒪_{Y'}` over `R₀` with values in the defining ideal of the thickening.

This is `AlgebraicGeometry.Space.liftDifferenceDerivation` at the pair of structure maps supplied
by `AlgebraicGeometry.Space.inverseImageStructureSharpOfRestrictEq_comp_structureSharp`. -/
@[stacks 0618 "the derivation D of the source, bundled, for the two structure maps of two \
morphisms of a thickening agreeing on its closed subspace"]
noncomputable def liftPairDerivation (hZ : IsFirstOrderThickening B S hS X' G)
    (hφ : (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫
          (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h) =
      (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫
          (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (structureSharpInverseImage B S hS b')) :
    (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
        ((sheafCompose (SmallEtale.topology B S hS X'.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
          (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h))).Derivation' φc.hom :=
  liftDifferenceDerivation B S hS ⟨G, hG.1⟩ φc _ _ hZ
    (inverseImageStructureSharpOfRestrictEq_comp_structureSharp B S hS hG a' b' h) hφ

/-- The derivation of [Stacks Project, Tag 0618] differentiates a section of `(b')^{-1}𝒪_{Y'}` to
the difference of the two structure maps on it, which is
`AlgebraicGeometry.Space.liftPairDifference`. -/
theorem liftPairDerivation_d (hZ : IsFirstOrderThickening B S hS X' G)
    (hφ : (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫
          (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h) =
      (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map φc ≫
          (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (structureSharpInverseImage B S hS b'))
    (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (r : ((inverseImageStructureSheaf B S hS b').obj ⋙
      forget₂ CommRingCat.{u} RingCat.{u}).obj U) :
    (liftPairDerivation B S hS hG a' b' h φc hZ hφ).d r =
      liftPairDifference B S hS hG a' b' h U r :=
  rfl

end Restrict

end AlgebraicGeometry.Space

end
