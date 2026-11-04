module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.AmbientSolutionAutomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.SolutionTorsor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat deformations of an algebraic space across a first order thickening (Stacks 0D17)

Let `S` be a scheme, `Y ⊂ Y'` a first order thickening of algebraic spaces over `S` and
`f : X ⟶ Y` a flat morphism of algebraic spaces over `S`. Suppose there is a flat
`f' : X' ⟶ Y'` with an isomorphism `a : X ≅ X' ×_{Y'} Y` over `Y` (a `Deformation f`). Then:

1. the set `Classes f` of isomorphism classes of pairs `(f', a)` is principal homogeneous under
   `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})` (`classes_addTorsor`);
2. the group of automorphisms `φ : X' ⟶ X'` over `Y'` reducing to the identity on
   `X' ×_{Y'} Y` — the automorphism group `Aut D` of the pair in the groupoid of deformations —
   is `Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})` (`Deformation.autMulEquivNaiveCotangentExtZero`).

Here `NL_{X/Y}` is the naive cotangent complex `AlgebraicGeometry.Space.naiveCotangentComplex` of
`f`, a complex of `𝒪_X`-modules on the small étale site of `X`, and `f^*𝒞_{Y/Y'}` is the pullback
of the conormal sheaf of `Y ⊂ Y'`, with sections lifted to the universe `u + 1` of the sections
of `NL_{X/Y}` (`liftedPulledBackConormal`); the `Ext` groups are computed in any model of the
derived category of `𝒪_X`-modules. The automorphism `φ` of part (2) is sent to the automorphism
`(φ^♯)⁻¹` of the solution `0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'} → 𝒪_X → 0` of the extension problem of the
proof (`Deformation.autMulEquivAmbientSolution`), whose automorphisms are `Ext⁰` by Stacks 08UG
(`solutionAutMulEquivExtZero`).

## Main results
* `AlgebraicGeometry.Space.FlatThickeningDeformation.classes_addTorsor_and_autMulEquiv`.

## References
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- The abelian structure of the `𝒪_X`-modules with sections in `Type (u + 1)`, named so that
instance search does not meet the universe constraint posed by competing instances stated at a
maximum of universes. -/
local instance (priority := high) deformationClassificationAbelianLargeModules :
    Abelian (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O)) :=
  SheafOfModules.instAbelian _

variable [HasDerivedCategory.{t} (_root_.SheafOfModules.{u + 1}
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O))]

variable {f} in
/-- **The automorphism group of a flat deformation `(f', a)` of `f` is
`Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`**: `Aut D` (automorphisms `φ : X' ⟶ X'` over `Y'` with
`i ≫ φ = i`, i.e. reducing to the identity on `X' ×_{Y'} Y`) is the automorphism group of the
solution of `D` (`Deformation.autMulEquivAmbientSolution`), which is `Ext⁰` by Stacks 08UG
(`solutionAutMulEquivExtZero`). -/
def Deformation.autMulEquivNaiveCotangentExtZero (D : Deformation f) :
    Aut D ≃* Multiplicative (DerivedCategory.Ext
      (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
      ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 0) :=
  (Deformation.autMulEquivAmbientSolution hZ D).trans
    (solutionAutMulEquivExtZero hZ f (D.ambientSolution hZ))

/-- **[Stacks Project, Tag 0D17]**. Let `S` be a scheme, `Y ⊂ Y'` a first order thickening of
algebraic spaces over `S` (`hZ`) and `f : X ⟶ Y` a flat morphism of algebraic spaces over `S`
(`hf`). If there exists a flat `f' : X' ⟶ Y'` with an isomorphism `a : X ≅ X' ×_{Y'} Y` over `Y`
(`hD`; a `Deformation f` is exactly such a pair, see `Deformation.ofPair`, `Deformation.pairIso`),
then
1. the set `Classes f` of isomorphism classes of pairs `(f', a)` is principal homogeneous under
   `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`, and
2. for every such pair `D`, the group `Aut D` of automorphisms `φ : X' ⟶ X'` over `Y'` reducing to
   the identity on `X' ×_{Y'} Y` is `Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`.

`NL_{X/Y}` is the canonical naive cotangent complex `naiveCotangentComplex B S hS f`; the module
`f^*𝒞_{Y/Y'}` is `liftedPulledBackConormal hZ f` (its sections lifted to the universe of those of
`NL_{X/Y}`); the `Ext` groups are those of any model of the derived category of `𝒪_X`-modules. The
isomorphisms themselves are `classes_addTorsor` and `Deformation.autMulEquivNaiveCotangentExtZero`
(an isomorphism of groups, which in particular identifies the underlying sets). -/
@[stacks 0D17, sga "7 VI 4.16" "special case"]
theorem classes_addTorsor_and_autMulEquiv (hf : IsFlat B S hS f.hom)
    (hD : Nonempty (Deformation f)) :
    Nonempty (AddTorsor
        (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
          ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (Classes f)) ∧
      ∀ D : Deformation f, Nonempty (Aut D ≃* Multiplicative (DerivedCategory.Ext
        (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 0)) :=
  ⟨classes_addTorsor hZ f hf hD.some, fun D => ⟨D.autMulEquivNaiveCotangentExtZero hZ⟩⟩

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
