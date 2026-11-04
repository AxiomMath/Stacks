module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBaseComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitSquare
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# The blowup triangle of de Rham complexes: the objects and the canonical maps

Fix a scheme `S`, a morphism `f : X ⟶ S` and a closed immersion `i : Z ⟶ X`. Write
`b : X' ⟶ X` for the blowing up of `X` along `Z`, `j : E ⟶ X'` for its exceptional divisor and
`p : E ⟶ Z` for the projection of the exceptional divisor onto the centre, so that
`j ≫ b = p ≫ i`. [Stacks, Tag 0FUV] is a distinguished triangle

`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S} ⟶ Ω^•_{X/S}[1]`

in the derived category `D(X, f^{-1}𝒪_S)` of modules over the inverse image of the structure
sheaf of the base, whose first two maps are built from the four canonical maps of Section 07HX.
This file constructs the four objects and the four canonical maps.

## Main definitions

* `Stacks.DeRham.BlowupTriangle.coefficientBlowup`, `coefficientCentre`,
  `coefficientProjection` and `coefficientInclusion`: the morphisms of coefficient ringed spaces
  `(Y, (Y → S)^{-1}𝒪_S)` attached to `b`, `i`, `p` and `j`; the exceptional divisor is read over
  the base through the centre throughout.
* `Stacks.DeRham.BlowupTriangle.chain`: the canonical map of `ℤ`-indexed de Rham complexes
  `Ω^•_{Y/S} ⟶ g_*Ω^•_{Y'/S}` of a morphism `g : Y' ⟶ Y` over `S`.
* `Stacks.DeRham.BlowupTriangle.toBlowUp`, `toCentre`, `blowUpToExceptional`,
  `centreToExceptional`: the four canonical maps.

## Implementation notes

The exceptional divisor has two structure morphisms over `S`, through the blowup and through
the centre; they are equal, and everything here uses the one through the centre, which is the
one `i_*Rp_*Ω^•_{E/S}` is written with. The canonical map `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` is
transported from the structure morphism through the blowup along the equality.

The comparison `Rb_* ∘ Rj_* ≅ Ri_* ∘ Rp_*` in the fourth map is the canonical comparison of a
derived direct image along a composite with the composite of derived direct images, obtained from
the universal property of the former ([Stacks, Tag 0D5T]), at the two factorisations
`j ≫ b = p ≫ i` of one morphism of coefficient ringed spaces. All statements are made for an
arbitrary model of each derived category.

## References

* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

/-! ### Transport along an equality of structure morphisms -/

section Transport

variable {E S : Scheme.{u}} {T : RingedSpace.{u, u}}

/-- Pushing forward the de Rham complex along a morphism of coefficient spaces precomposed with
the identification of two equal structure morphisms. -/
def pushforwardTransportIso {e₁ e₂ : E ⟶ S} (h : e₁ = e₂) (g : inverseImageBase e₁ ⟶ T) :
    ((RingedSpaceModuleAdjunction.modulePushforward
          (eqToHom (congrArg inverseImageBase h.symm) ≫ g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex e₂) ≅
      ((RingedSpaceModuleAdjunction.modulePushforward g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (deRhamCochainComplex e₁) := by
  subst h
  exact eqToIso (by rw [eqToHom_refl, Category.id_comp])

/-- The coefficient-space morphism of a composite, read through equal factorisations. -/
lemma eqToHom_comp_relativeBase {Y X : Scheme.{u}} {a a' : Y ⟶ X} (f : X ⟶ S) (h : a = a') :
    eqToHom (congrArg (fun c : Y ⟶ X => inverseImageBase (c ≫ f)) h.symm) ≫ relativeBase a f =
      relativeBase a' f := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

end Transport

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### The blowup square and its coefficient spaces -/

/-- The blowing-up morphism `b : X' ⟶ X` along `Z`. -/
abbrev blowupMap : Stacks.Blowup.blowUp i.ker ⟶ X := Stacks.Blowup.blowUpToBase i.ker

/-- The inclusion `j : E ⟶ X'` of the exceptional divisor. -/
abbrev exceptionalInclusion : Stacks.Blowup.exceptionalDivisor i.ker ⟶ Stacks.Blowup.blowUp i.ker :=
  (Stacks.Blowup.exceptionalIdeal i.ker).subschemeι

/-- The projection `p : E ⟶ Z` of the exceptional divisor onto the centre. -/
abbrev exceptionalProjection : Stacks.Blowup.exceptionalDivisor i.ker ⟶ Z :=
  Stacks.Blowup.exceptionalToCentre i

/-- The structure morphism `E ⟶ S` of the exceptional divisor, through the centre. -/
abbrev exceptionalStructure : Stacks.Blowup.exceptionalDivisor i.ker ⟶ S :=
  exceptionalProjection i ≫ i ≫ f

/-- The blowup square commutes: `j ≫ b = p ≫ i` as morphisms `E ⟶ X`. -/
lemma exceptionalInclusion_comp_blowupMap :
    exceptionalInclusion i ≫ blowupMap i = exceptionalProjection i ≫ i :=
  Stacks.Blowup.exceptionalToCentre_comp i

/-- The composite `E ⟶ X' ⟶ X ⟶ S` is the structure morphism `exceptionalStructure f i`. -/
lemma exceptionalInclusion_comp :
    exceptionalInclusion i ≫ blowupMap i ≫ f = exceptionalStructure f i := by
  rw [← Category.assoc, exceptionalInclusion_comp_blowupMap, Category.assoc]

/-- The coefficient-space morphism `(X', (X' → S)^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S)` of the blowup. -/
abbrev coefficientBlowup := relativeBase (blowupMap i) f

/-- The coefficient-space morphism `(Z, (Z → S)^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S)` of the centre. -/
abbrev coefficientCentre := relativeBase i f

/-- The coefficient-space morphism of the projection `p : E ⟶ Z`. -/
abbrev coefficientProjection := relativeBase (exceptionalProjection i) (i ≫ f)

/-- The coefficient-space morphism of the inclusion `j : E ⟶ X'`, with the exceptional divisor
read over the base through the centre. -/
abbrev coefficientInclusion :
    inverseImageBase (exceptionalStructure f i) ⟶ inverseImageBase (blowupMap i ≫ f) :=
  eqToHom (congrArg inverseImageBase (exceptionalInclusion_comp f i).symm) ≫
    relativeBase (exceptionalInclusion i) (blowupMap i ≫ f)

/-- **The two factorisations of the coefficient-space morphism of `E ⟶ X` agree.** -/
lemma coefficientInclusion_comp_coefficientBlowup :
    coefficientInclusion f i ≫ coefficientBlowup f i =
      coefficientProjection f i ≫ coefficientCentre f i := by
  rw [coefficientInclusion, Category.assoc, relativeBase_comp, coefficientProjection,
    coefficientCentre, relativeBase_comp]
  exact eqToHom_comp_relativeBase f (exceptionalInclusion_comp_blowupMap i)

/-! ### The canonical maps of de Rham complexes -/

/-- **The canonical map `Ω^•_{Y/S} ⟶ g_*Ω^•_{Y'/S}` of Section 07HX**, for a morphism
`g : Y' ⟶ Y` over `S`, as a map of `ℤ`-indexed complexes of `(Y → S)^{-1}𝒪_S`-modules. -/
def chain {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (s : Y ⟶ S) :
    deRhamCochainComplex s ⟶
      ((RingedSpaceModuleAdjunction.modulePushforward (relativeBase g s)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (deRhamCochainComplex (g ≫ s)) :=
  HomologicalComplex.extendMap (Stacks.DeRhamPullback.deRhamPushforwardChain g s)
      ComplexShape.embeddingUpNat ≫
    (Stacks.DerivedIndexing.mapExtendIso
      (RingedSpaceModuleAdjunction.modulePushforward (relativeBase g s))
      ComplexShape.embeddingUpNat
      (show CochainComplex
          (SheafOfModules.{u} (structureSheafRing (inverseImageBase (g ≫ s)))) ℕ from
        Scheme.Hom.deRhamComplex (g ≫ s))).hom

/-- The canonical map `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}`, with `E` read over `S` through the centre. -/
def inclusionChain :
    deRhamCochainComplex (blowupMap i ≫ f) ⟶
      ((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i)) :=
  chain (exceptionalInclusion i) (blowupMap i ≫ f) ≫
    (pushforwardTransportIso (exceptionalInclusion_comp f i) _).inv

/-! ### The four canonical maps -/

section Derived

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable [HasDerivedCategory (ModuleSheaves (inverseImageBase f))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (exceptionalStructure f i)))]

/-- The unit `g_*K ⟶ Rg_*K` of the derived direct image along a morphism of coefficient spaces,
read on a cochain complex. -/
abbrev unit {A B : RingedSpace.{u, u}} [HasDerivedCategory (ModuleSheaves A)]
    [HasDerivedCategory (ModuleSheaves B)] (g : A ⟶ B) (K : CochainComplex (ModuleSheaves A) ℤ) :=
  StacksDraft.DerivedUnitSquare.unitQ (RingedSpaceModuleAdjunction.modulePushforward g)
    (derivedPushforwardUnit g) K

/-- The canonical comparison `R(g ≫ h)_* ≅ Rg_* ∘ Rh_*` of [Stacks, Tag 0D5T]. -/
def compIso {A B C : RingedSpace.{u, u}} [HasDerivedCategory (ModuleSheaves A)]
    [HasDerivedCategory (ModuleSheaves B)] [HasDerivedCategory (ModuleSheaves C)]
    (g : A ⟶ B) (h : B ⟶ C) :
    derivedPushforward (g ≫ h) ≅ derivedPushforward g ⋙ derivedPushforward h :=
  haveI :=
    Stacks.Cohomology.DerivedPushforwardComposition.isIso_derivedPushforwardComparison_unconditional
      g h (derivedPushforward g) (derivedPushforward h) (derivedPushforward (g ≫ h))
      (derivedPushforwardUnit g) (derivedPushforwardUnit h) (derivedPushforwardUnit (g ≫ h))
  asIso (Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardComparison g h
    (derivedPushforward g) (derivedPushforward h) (derivedPushforward (g ≫ h))
    (derivedPushforwardUnit g) (derivedPushforwardUnit h) (derivedPushforwardUnit (g ≫ h)))

/-- `Ω^•_{X/S}`, in `D(X, f^{-1}𝒪_S)`. -/
abbrev deRham : DerivedCategory (ModuleSheaves (inverseImageBase f)) :=
  DerivedCategory.Q.obj (deRhamCochainComplex f)

/-- `Rb_*Ω^•_{X'/S}`. -/
abbrev blowUpDeRham : DerivedCategory (ModuleSheaves (inverseImageBase f)) :=
  (derivedPushforward (coefficientBlowup f i)).obj
    (DerivedCategory.Q.obj (deRhamCochainComplex (blowupMap i ≫ f)))

/-- `i_*Ω^•_{Z/S}`. -/
abbrev centreDeRham : DerivedCategory (ModuleSheaves (inverseImageBase f)) :=
  (derivedPushforward (coefficientCentre f i)).obj
    (DerivedCategory.Q.obj (deRhamCochainComplex (i ≫ f)))

/-- `i_*Rp_*Ω^•_{E/S}`. -/
abbrev exceptionalDeRham : DerivedCategory (ModuleSheaves (inverseImageBase f)) :=
  (derivedPushforward (coefficientCentre f i)).obj
    ((derivedPushforward (coefficientProjection f i)).obj
      (DerivedCategory.Q.obj (deRhamCochainComplex (exceptionalStructure f i))))

/-- **The canonical map `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}`.** -/
def toBlowUp : deRham f ⟶ blowUpDeRham f i :=
  DerivedCategory.Q.map (chain (blowupMap i) f) ≫
    unit (coefficientBlowup f i) (deRhamCochainComplex (blowupMap i ≫ f))

/-- **The canonical map `Ω^•_{X/S} ⟶ i_*Ω^•_{Z/S}`.** -/
def toCentre : deRham f ⟶ centreDeRham f i :=
  DerivedCategory.Q.map (chain i f) ≫
    unit (coefficientCentre f i) (deRhamCochainComplex (i ≫ f))

/-- **The canonical map `i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S}`**: `i_*` of the canonical map
`Ω^•_{Z/S} ⟶ Rp_*Ω^•_{E/S}`. -/
def centreToExceptional : centreDeRham f i ⟶ exceptionalDeRham f i :=
  (derivedPushforward (coefficientCentre f i)).map
    (DerivedCategory.Q.map (chain (exceptionalProjection i) (i ≫ f)) ≫
      unit (coefficientProjection f i) (deRhamCochainComplex (exceptionalStructure f i)))

/-- **The canonical map `Rb_*Ω^•_{X'/S} ⟶ i_*Rp_*Ω^•_{E/S}`**: `Rb_*` of the canonical map
`Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}`, followed by the canonical comparison
`Rb_*Rj_* ≅ R(j ≫ b)_* = R(p ≫ i)_* ≅ Ri_*Rp_*`. -/
def blowUpToExceptional : blowUpDeRham f i ⟶ exceptionalDeRham f i :=
  (derivedPushforward (coefficientBlowup f i)).map
      (DerivedCategory.Q.map (inclusionChain f i) ≫
        unit (coefficientInclusion f i) (deRhamCochainComplex (exceptionalStructure f i))) ≫
    (compIso (coefficientInclusion f i) (coefficientBlowup f i)).inv.app _ ≫
    eqToHom (congrArg (fun g => (derivedPushforward g).obj
      (DerivedCategory.Q.obj (deRhamCochainComplex (exceptionalStructure f i))))
        (coefficientInclusion_comp_coefficientBlowup f i)) ≫
    (compIso (coefficientProjection f i) (coefficientCentre f i)).hom.app _

end Derived

end Stacks.DeRham.BlowupTriangle

end
