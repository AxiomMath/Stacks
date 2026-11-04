module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.FibreTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentComplex
public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphismDerivation

/-!
# Automorphisms of a solution of the extension problem of a flat deformation

Let `Y ⊂ Y'` be a first order thickening of algebraic spaces over `S` and `f : X ⟶ Y` a morphism,
and let `problem f` be the square-zero extension problem of [Stacks Project, Tag 08UF] on the
small étale site of `X` attached to `f`, whose prescribed module is `f^*𝒞_{Y/Y'}`; its solutions
are the flat deformations of `f` over `Y'`. **The automorphism group of any solution of
`problem f` is `Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`**, where `NL_{X/Y}` is the naive cotangent
complex `AlgebraicGeometry.Space.naiveCotangentComplex f` of Stacks 0D0V. This is part (2) of
[Stacks Project, Tag 0D17], in the form of part (2) of [Stacks Project, Tag 08UG].

## Main definitions

* `AlgebraicGeometry.Space.FlatThickeningDeformation.liftedPulledBackConormal`: `f^*𝒞_{Y/Y'}`
  with sections lifted to the universe `u + 1` in which `NL_{X/Y}` is formed.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.solutionAutMulEquivExtZero`: the
  automorphism group of a solution of `problem f` is `Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`, as a
  group, at any model of the derived category.

## Implementation notes

The small étale site of `X` has objects in `Type (u + 1)`, so `NL_{X/Y}` is a complex of
`𝒪_X`-modules with sections in `Type (u + 1)`
(see `AlgebraicGeometry.Space.naiveCotangentComplex`),
while `f^*𝒞_{Y/Y'}` has sections in `Type u`; the `Ext` group is formed with the universe lift of
`f^*𝒞_{Y/Y'}`, which does not change its sections up to `ULift`. The `NL_{X/Y}` of
[Stacks Project, Section 0D0U] is the one of [Stacks Project, Section 08UE] for the morphism of
small étale ringed topoi `f_small`, which is how `AlgebraicGeometry.Space.naiveCotangentComplex`
is defined.

The instances `CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat` and
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian`, stated at a maximum of universes, are kept
from being tried first at the universes of the small étale site, where they pose universe
constraints instance search cannot solve.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Deformation.ToposThickening Deformation.ToposThickening.RingedToposExtensionProblem

universe t u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- `f^*𝒞_{Y/Y'}` with its sections lifted to the universe `u + 1` of the sections of
`NL_{X/Y}`. -/
abbrev liftedPulledBackConormal :
    _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O) :=
  CompatibleFirstOrderThickening.liftedModule.{u, u + 1, u, u, u + 1, u} (problem f hZ)

/-- The inverse image along `f` of the reduction `t⁻¹𝒪_{Y'} ⟶ 𝒪_Y` of the thickening is locally
surjective, in the spelling of `problem f`. -/
theorem isLocallySurjective_problem_baseReduction :
    Presheaf.IsLocallySurjective (smallEtaleRingedTopos B S hS X).J
      ((inverseImageCommRingFunctor (problem f hZ).f.toToposHom).map
        (problem f hZ).baseReduction).hom :=
  isLocallySurjective_inverseImage_baseReduction hZ f

/-- The abelian structure of the `𝒪_X`-modules with sections in `Type (u + 1)`. -/
local instance (priority := high) abelianLargeModules :
    Abelian (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O)) :=
  SheafOfModules.instAbelian _

variable [HasDerivedCategory.{t} (_root_.SheafOfModules.{u + 1}
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O))]

/-- **The automorphism group of a solution of `problem f` is
`Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`**, as a group, at any model of the derived category of
`𝒪_X`-modules: an automorphism `φ` of the middle term `𝒪'` of `0 → f^*𝒞_{Y/Y'} → 𝒪' → 𝒪_X → 0`
over the fixed diagram is `id + δ` for a relative derivation `δ` of `𝒪_X` over `f⁻¹𝒪_Y` with
values in `f^*𝒞_{Y/Y'}`, and these are `Hom(Ω_{X/Y}, f^*𝒞_{Y/Y'}) = Ext⁰(NL_{X/Y}, f^*𝒞_{Y/Y'})`.
-/
def solutionAutMulEquivExtZero (P : (problem f hZ).CompatibleFirstOrderThickening) :
    P.AutomorphismGroup ≃* Multiplicative (DerivedCategory.Ext
      (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
      ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 0) :=
  CompatibleFirstOrderThickening.autMulEquivNaiveCotangentExtZero P
    (isLocallySurjective_problem_baseReduction hZ f)

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
