module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.AutomorphismExtZero
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.SolutionSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelNaiveCotangentExt
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentBaseIso
public import StacksFrontier.Deformation.ToposThickening.SolutionClassesNaiveExtTorsor
public import StacksFrontier.Deformation.ToposThickening.SolutionSiteTransport

/-!
# The isomorphism classes of solutions of the extension problem of a flat deformation

Let `Y ⊂ Y'` be a first order thickening of algebraic spaces over `S` and `f : X ⟶ Y` a morphism.
The proof of [Stacks Project, Tag 0D17] reads flat deformations of `f` over `Y'` as solutions of
the square-zero extension problem `problem f` of [Stacks Project, Tag 08UF] on the small étale
site of `X`, and deduces part (1) from [Stacks Project, Tag 08UK]. This file is that deduction on
the side of the extension problem: **if `problem f` has a solution, its isomorphism classes of
solutions are principal homogeneous under `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`**, where `NL_{X/Y}`
is the naive cotangent complex `AlgebraicGeometry.Space.naiveCotangentComplex f` of Stacks 0D0V.

## Main definitions

* `AlgebraicGeometry.Space.FlatThickeningDeformation.modelProblem`: `problem f` moved to the
  `Type u` model of the small étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.FlatThickeningDeformation.solutionClasses_addTorsor`: the
  isomorphism classes of solutions of `problem f` are a principal homogeneous space under
  `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`, at any model of the derived category.

## Implementation notes

[Stacks 08UK] is formalized for ringed topoi whose site, morphisms and structure sheaf all live
in one universe
(`Deformation.ToposThickening.RingedToposExtensionProblem.exists_addTorsor_isomorphismClasses`),
while the small étale site of `X` has objects in `Type (u + 1)`. The proof therefore moves the
problem to the model `SmallModel (SmallEtale X)` of the site along the comparison equivalence
(`Deformation.ToposThickening.RingedToposExtensionProblem.siteTransport`), which does not change
the isomorphism classes of solutions, applies 08UK there, and identifies the acting group of the
model, `Ext¹` out of the naive cotangent complex of the transported structure map, with
`Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`
(`AlgebraicGeometry.Space.smallEtaleModelNaiveCotangentExtAddEquiv`
and `Stacks.SheafOfModules.naiveCotangentExtAddEquivOfBaseIso`).

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Deformation.ToposThickening Deformation.ToposThickening.RingedToposExtensionProblem

universe t t' u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- **`problem f` moved to the `Type u` model of the small étale site of `X`**, along the
comparison equivalence `X_étale ≌ SmallModel X_étale`. -/
abbrev modelProblem :=
  (problem f hZ).siteTransport (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)

/-- The isomorphism classes of solutions of `problem f` and of `modelProblem f` correspond. -/
def modelClassesEquiv :
    CompatibleFirstOrderThickening.IsomorphismClasses.{u, u + 1, u, u, u + 1, u} (problem f hZ) ≃
      CompatibleFirstOrderThickening.IsomorphismClasses.{u, u, u, u, u + 1, u}
        (modelProblem hZ f) :=
  siteTransportIsomorphismClassesEquiv _ _ (problem f hZ)

/-- The solution of `modelProblem f` attached to a solution of `problem f`: its middle term is
the restriction of that of the solution to the model. -/
abbrev modelSolution (P : (problem f hZ).CompatibleFirstOrderThickening) :
    (modelProblem hZ f).CompatibleFirstOrderThickening :=
  siteTransportSolution _ _ (problem f hZ) P

/-- `modelClassesEquiv` sends the class of a solution `P` of `problem f` to the class of
`modelSolution P`. -/
theorem modelClassesEquiv_mk (P : (problem f hZ).CompatibleFirstOrderThickening) :
    modelClassesEquiv hZ f (Quotient.mk _ P) = Quotient.mk _ (modelSolution hZ f P) :=
  rfl

/-- [Stacks 08UK] for `modelProblem f`: if it has a solution, its isomorphism classes of
solutions are principal homogeneous under the `Ext¹` of the model, the class of `P` being carried
to that of `Q` by `ξ` exactly when the obstruction class of `P` and `Q` is `ξ`. -/
theorem modelClasses_addTorsor [hD : HasDerivedCategory.{t'} (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingRestriction (smallEtaleRingedTopos B S hS X).O)))]
    (hne : Nonempty (modelProblem hZ f).CompatibleFirstOrderThickening) :
    ∃ T : AddTorsor (Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t'}
        ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).J
        ((inverseImageCommRingFunctor (modelProblem hZ f).f.toToposHom).obj
          (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)
        ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).O
        (modelProblem hZ f).f.fSharpInverseImage (modelProblem hZ f).G 1)
        (CompatibleFirstOrderThickening.IsomorphismClasses.{u, u, u, u, u + 1, u}
          (modelProblem hZ f)),
      ∀ (ξ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t'}
          ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).J
          ((inverseImageCommRingFunctor (modelProblem hZ f).f.toToposHom).obj
            (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)
          ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).O
          (modelProblem hZ f).f.fSharpInverseImage (modelProblem hZ f).G 1)
        (P Q : (modelProblem hZ f).CompatibleFirstOrderThickening),
        T.vadd ξ (Quotient.mk _ P) = Quotient.mk _ Q ↔
          CompatibleFirstOrderThickening.pairObstruction.{t', u, u, u, u + 1, u} P Q = ξ := by
  have h0 := exists_addTorsor_isomorphismClasses.{t'} (modelProblem hZ f) hne
  rcases h0 with ⟨T, hT, h2⟩
  refine ⟨T, fun ξ P Q => ?_⟩
  exact hT ξ P Q

/-- The obstruction class of [Stacks 08UG] of the transports to the model of two solutions of
`problem f`, in the `Ext¹` of the model. -/
def modelObstruction [hD : HasDerivedCategory.{t'} (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingRestriction (smallEtaleRingedTopos B S hS X).O)))]
    (P Q : (problem f hZ).CompatibleFirstOrderThickening) :
    Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t'}
        ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).J
        ((inverseImageCommRingFunctor (modelProblem hZ f).f.toToposHom).obj
          (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)
        ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).O
        (modelProblem hZ f).f.fSharpInverseImage (modelProblem hZ f).G 1 :=
  CompatibleFirstOrderThickening.pairObstruction.{t', u, u, u, u + 1, u}
    (modelSolution hZ f P) (modelSolution hZ f Q)

/-- The abelian structure of the `𝒪_X`-modules with sections in `Type (u + 1)`, named so that
instance search does not meet the universe constraint posed by competing instances stated at a
maximum of universes. -/
local instance (priority := high) solutionTorsorAbelianLargeModules :
    Abelian (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O)) :=
  SheafOfModules.instAbelian _

variable [HasDerivedCategory.{t} (_root_.SheafOfModules.{u + 1}
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O))]

/-- **The acting group of the model is `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`**: `Ext` out of the
naive cotangent complex of the structure map of the transported morphism into the restricted
module is `Ext` out of `NL_{X/Y}` into `f^*𝒞_{Y/Y'}`, in every degree. -/
def modelExtAddEquiv [hD : HasDerivedCategory.{t'} (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingRestriction (smallEtaleRingedTopos B S hS X).O)))] (n : ℤ) :
    DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) n ≃+
      Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t'}
        ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).J
        ((inverseImageCommRingFunctor (modelProblem hZ f).f.toToposHom).obj
          (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)
        ((smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X)).O
        (modelProblem hZ f).f.fSharpInverseImage (modelProblem hZ f).G n :=
  (smallEtaleModelNaiveCotangentExtAddEquiv (smallEtaleRingedToposHom B S hS f).fSharpInverseImage
      (pulledBackConormal f) n).trans
    (siteTransportNaiveCotangentExtAddEquiv.{u, u + 1, u, u, u, u, u + 1, u, t'}
      (X := smallEtaleRingedTopos B S hS X)
      (B := smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
      (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X) (problem f hZ).f
      (modelProblem hZ f).G n)

/-- **The isomorphism classes of solutions of `problem f` are a principal homogeneous space under
`Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`**, as soon as there is a solution, with the action read on the
model of the small étale site: `ξ` carries the class of `P` to the class of `Q` exactly when the
obstruction class of [Stacks 08UG] of the transported solutions is the image of `ξ` in the `Ext`
group of the model. This is [Stacks 08UK] applied on the model, at any models of the two derived
categories. -/
theorem solutionClasses_addTorsor_vadd_iff [hD : HasDerivedCategory.{t'} (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingRestriction (smallEtaleRingedTopos B S hS X).O)))]
    (hne : Nonempty (problem f hZ).CompatibleFirstOrderThickening) :
    ∃ T : AddTorsor (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (CompatibleFirstOrderThickening.IsomorphismClasses.{u, u + 1, u, u, u + 1, u}
          (problem f hZ)),
      ∀ (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
          ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (P Q : (problem f hZ).CompatibleFirstOrderThickening),
        T.vadd ξ (Quotient.mk _ P) = Quotient.mk _ Q ↔
          modelObstruction (hD := hD) hZ f P Q = modelExtAddEquiv (hD := hD) hZ f 1 ξ := by
  have h0 := modelClasses_addTorsor (hD := hD) hZ f ⟨modelSolution hZ f hne.some⟩
  rcases h0 with ⟨T, hT⟩
  refine ⟨addTorsorTransfer T (modelClassesEquiv hZ f) (modelExtAddEquiv (hD := hD) hZ f 1),
    fun ξ P Q => ?_⟩
  exact (Equiv.symm_apply_eq (modelClassesEquiv hZ f)).trans
    (hT (modelExtAddEquiv (hD := hD) hZ f 1 ξ) (modelSolution hZ f P) (modelSolution hZ f Q))

/-- **The isomorphism classes of solutions of `problem f` are a principal homogeneous space under
`Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`**, as soon as there is a solution, at any model of the derived
category of `𝒪_X`-modules. -/
theorem solutionClasses_addTorsor (hne : Nonempty (problem f hZ).CompatibleFirstOrderThickening) :
    Nonempty (AddTorsor
        (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (CompatibleFirstOrderThickening.IsomorphismClasses.{u, u + 1, u, u, u + 1, u}
          (problem f hZ))) := by
  let := HasDerivedCategory.standard (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingRestriction (smallEtaleRingedTopos B S hS X).O)))
  obtain ⟨T, -⟩ := solutionClasses_addTorsor_vadd_iff (hD := this) hZ f hne
  exact ⟨T⟩

/-- **Part (1) of [Stacks Project, Tag 0D17]**: for a flat `f : X ⟶ Y` admitting a flat deformation
`(f' : X' ⟶ Y', a)` over `Y'`, the set of isomorphism classes of such pairs is principal
homogeneous under `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`, at any model of the derived category of
`𝒪_X`-modules. The classes of pairs are those of solutions of `problem f`
(`classesEquiv`), which are principal homogeneous by `solutionClasses_addTorsor`. -/
theorem classes_addTorsor (hf : IsFlat B S hS f.hom) (D : Deformation f) :
    Nonempty (AddTorsor
      (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
      (Classes f)) := by
  obtain ⟨P, -⟩ := Quotient.exists_rep
    (s := CompatibleFirstOrderThickening.isomorphicSetoid.{u, u + 1, u, u, u + 1, u} (problem f hZ))
    (classesEquiv hZ f hf (Quotient.mk _ D))
  obtain ⟨T⟩ := solutionClasses_addTorsor hZ f ⟨P⟩
  exact ⟨addTorsorTransfer T (classesEquiv hZ f hf) (AddEquiv.refl _)⟩

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
