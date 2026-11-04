module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtZero
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCanonicalExtZero
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionClasses
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceOfFilteredComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The isomorphism classes of solutions are principal homogeneous (Stacks 08UC)

Fix a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` with ideal `𝒥`, a morphism
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, an `𝒪_X`-module `𝒢` and an `f`-map `c : 𝒥 ⟶ 𝒢`, written as the
`𝒪_X`-linear map `c : f^*t^*𝒥 ⟶ 𝒢` it is adjoint to. **Stacks 08UC** says: *if there exists a
solution to (91.7.0.1), then the set of isomorphism classes of solutions is principal homogeneous
under `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)`.*

This file states the tag at **any** model of the derived category `D(𝒪_X)`, with the canonical
group `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` of the library: `Stacks.SheafOfModules.naiveCotangentExt` of the
homomorphism `f⁻¹𝒪_S ⟶ 𝒪_X`, i.e. `Hom(NL_{X/S}, 𝒢[1])` in that model, where
`NL_{X/S} = AlgebraicGeometry.RingedSpace.naiveCotangentComplex f` is the naive cotangent complex
of **Stacks 08TN**.

## The argument

`StacksFrontier/Deformation/RingedSpaceThickening/SolutionClasses.lean` proves the tag in the
standard model `HasDerivedCategory.standard`: the set `SolutionClasses t ht f G c` of
isomorphism classes of solutions (the quotient by `Isomorphic`, the existence of an isomorphism of
solutions) is an `AddTorsor` under `RingedSpaceThickening.extOneNaiveCotangent f G`
(`solutionClassesAddTorsor`). The separating element of two classes is the difference class
`differenceClass Q₁ Q₂` (the class of the square-zero extension of `f⁻¹𝒪_S`-algebras obtained by
pushing `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` out along the difference homomorphism), which vanishes exactly
when the two solutions are isomorphic; and `ξ` acts on the class of `X'` by the class of the
solution `X'_ξ` of the source's proof (`solutionTwist`), the pushout along `ψ`.

Here that torsor is carried to an arbitrary model along the additive identification
`extOneNaiveCotangentModelAddEquiv` of the two `Ext¹` groups, induced by the comparison
triangulated equivalence `StacksDraft.DerivedModel.modelEquiv` of the two models (which commutes
with the shift and with the localization functors `Q`).

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.extOneNaiveCotangentModelAddEquiv`: the
  identification of `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` at the standard model with the same group at an
  arbitrary model.
* `AlgebraicGeometry.RingedSpaceThickening.solutionClassesModelAddTorsor`: the principal
  homogeneous structure at an arbitrary model.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.exists_addTorsor_solutionClasses`:
  **Stacks 08UC**, at any model: if a solution exists, the isomorphism classes of solutions carry
  a structure of principal homogeneous space under `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` whose separating
  element of two classes is (the image of) their difference class and whose action on the class
  of `X'` is the class of the twisted solution `X'_ξ`.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe w u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` at an arbitrary model -/

section Model

variable {X S : RingedSpace.{u, u}}
  [H : HasDerivedCategory.{w} (RingedSpace.siteModules X)]

variable (H) in
/-- **`Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` at the model `H`**: the canonical group
`Stacks.SheafOfModules.naiveCotangentExt` of the homomorphism `f⁻¹𝒪_S ⟶ 𝒪_X` of sheaves of rings
on `X`, in degree one. Its complex is `RingedSpace.naiveCotangentComplex f`, the `NL_{X/S}` of
**Stacks 08TN**. -/
abbrev modelExtOneNaiveCotangent (f : X ⟶ S) (G : RingedSpace.siteModules X) :
    Type w :=
  Stacks.SheafOfModules.naiveCotangentExt (Opens.grothendieckTopology X.carrier)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) G 1

/-- The comparison equivalence from the standard model of `D(𝒪_X)` to the model `H`. -/
abbrev standardModelEquiv :
    @DerivedCategory _ _ _
        (HasDerivedCategory.standard (RingedSpace.siteModules X)) ≌
      @DerivedCategory _ _ _ H :=
  StacksDraft.DerivedModel.modelEquiv
    (HasDerivedCategory.standard (RingedSpace.siteModules X)) H

/-- The comparison of the images of the single complex on `𝒢` in the two models. -/
def standardModelSingleIso (G : RingedSpace.siteModules X) :
    standardModelEquiv.functor.obj
        ((@DerivedCategory.singleFunctor _ _ _
          (HasDerivedCategory.standard (RingedSpace.siteModules X)) 0).obj G) ≅
      (@DerivedCategory.singleFunctor _ _ _ H 0).obj G :=
  standardModelEquiv.functor.mapIso
      ((@DerivedCategory.singleFunctorIsoCompQ _ _ _
        (HasDerivedCategory.standard (RingedSpace.siteModules X)) 0).app G) ≪≫
    (StacksDraft.DerivedModel.modelCompQIso
      (HasDerivedCategory.standard (RingedSpace.siteModules X)) H).app
        ((CochainComplex.singleFunctor _ 0).obj G) ≪≫
    ((@DerivedCategory.singleFunctorIsoCompQ _ _ _ H 0).app G).symm

/-- **`Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` at the standard model and at an arbitrary model.** The group
`extOneNaiveCotangent f 𝒢` of the standard model, in which the torsor of
`SolutionClasses.lean` is built, is identified with the canonical group
`Stacks.SheafOfModules.naiveCotangentExt` of the model `H`: apply the comparison equivalence,
which is additive and commutes with the shift, and then identify the images of `NL_{X/S}` and of
`𝒢` with the corresponding objects of `H` by the comparison of the localization functors. -/
def extOneNaiveCotangentModelAddEquiv (f : X ⟶ S)
    (G : RingedSpace.siteModules X) :
    extOneNaiveCotangent f G ≃+ modelExtOneNaiveCotangent H f G :=
  letI := StacksDraft.DerivedModel.modelEquiv_functor_additive
    (HasDerivedCategory.standard (RingedSpace.siteModules X)) H
  (Stacks.Injectives.shiftedHomMapAddEquiv standardModelEquiv.functor _ _ 1).trans
    (Linear.homCongr ℤ
      ((StacksDraft.DerivedModel.modelCompQIso
        (HasDerivedCategory.standard (RingedSpace.siteModules X)) H).app
          (RingedSpace.naiveCotangentComplex f))
      ((shiftFunctor _ (1 : ℤ)).mapIso (standardModelSingleIso G))).toAddEquiv

end Model

/-! ### The principal homogeneous space -/

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : RingedSpace.siteModules X}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

variable [H : HasDerivedCategory.{w} (RingedSpace.siteModules X)]

variable (t ht f G c) in
/-- **The isomorphism classes of solutions of Stacks 08U7 as a principal homogeneous space under
`Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` at the model `H`**: the torsor `solutionClassesAddTorsor` of the
standard model, carried along `extOneNaiveCotangentModelAddEquiv`. -/
@[instance_reducible, sga "7 VI 4.16" "more general"]
def solutionClassesModelAddTorsor [Nonempty (DeformationSolution t ht f G c)] :
    AddTorsor (modelExtOneNaiveCotangent H f G) (SolutionClasses t ht f G c) :=
  letI := solutionClassesAddTorsor (t := t) (ht := ht) (f := f) (G := G) (c := c)
  Deformation.ToposThickening.addTorsorCongr (extOneNaiveCotangentModelAddEquiv f G).symm
    (Equiv.refl _)

/-- **Stacks Project, Tag 08UC.** If there exists a solution to the deformation problem
(91.7.0.1) of **Stacks 08U7**, then the set of isomorphism classes of solutions is principal
homogeneous under `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)`.

The statement holds at every model `H` of the derived category `D(𝒪_X)`, with the canonical group
`Stacks.SheafOfModules.naiveCotangentExt` of the homomorphism `f⁻¹𝒪_S ⟶ 𝒪_X` in degree one. The
set of isomorphism classes is `SolutionClasses t ht f G c`, the quotient of the solutions by
`Isomorphic` (some morphism of solutions — a morphism of the deformed spaces under `X`, over
`S'`, and the identity on `𝒢` — is an isomorphism). "Principal homogeneous" is Mathlib's
`AddTorsor`: an action of the group which is free and transitive, the unique element carrying
one class to another being `-ᵥ`. The structure is not an arbitrary one: the element separating
the classes of `X'₁` and `X'₂` is the difference class `o(X'₁, X'₂)` of the two solutions (the
class of the square-zero extension of `f⁻¹𝒪_S`-algebras which is their difference, read in the
model `H`), and `ξ` acts on the class of `X'` by the class of the solution `X'_ξ` of the
source's proof. -/
@[stacks 08UC "at any model of D(𝒪_X), with the canonical Ext¹(NL_{X/S}, 𝒢); the separating \
element of two classes is their difference class and ξ acts on [X'] by [X'_ξ]"]
theorem exists_addTorsor_solutionClasses (h : Nonempty (DeformationSolution t ht f G c)) :
    ∃ T : AddTorsor (modelExtOneNaiveCotangent H f G) (SolutionClasses t ht f G c),
      letI := T
      (∀ Q₁ Q₂ : DeformationSolution t ht f G c,
        ((⟦Q₁⟧ : SolutionClasses t ht f G c) -ᵥ ⟦Q₂⟧) =
          extOneNaiveCotangentModelAddEquiv f G (differenceClass Q₁ Q₂)) ∧
      ∀ (ξ : modelExtOneNaiveCotangent H f G) (Q : DeformationSolution t ht f G c),
        ξ +ᵥ (⟦Q⟧ : SolutionClasses t ht f G c) =
          ⟦solutionTwist Q ((extOneNaiveCotangentModelAddEquiv f G).symm ξ)⟧ :=
  have := h
  ⟨solutionClassesModelAddTorsor t ht f G c, fun _ _ => rfl, fun _ _ => rfl⟩

end AlgebraicGeometry.RingedSpaceThickening

end
