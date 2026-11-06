module

public import StacksFrontier.Deformation.ToposThickening.LiftingObstructionPresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialPresheafDerivations
import StacksCore.Tactic.StacksAttribute

/-!
# Step 2 of the proof of Stacks 08UG/08U8: a lift prescribes a factorization

Step 1 (`StacksFrontier/Deformation/ToposThickening/LiftingObstructionPresentation.lean`) attaches
to a `Deformation.ToposThickening.FirstOrderLiftDiagram` the sheaf of sets
`ℰ = 𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}`, the two algebra maps `a` and `b` out of `𝒪_{B'₁}[ℰ]`, and the
obstruction homomorphism `ξ : ℐ/ℐ² ⟶ g_*𝒢₂`.

This file carries out the first half of Step 2. The source reads a morphism `φ` filling the
diagram — a `Deformation.ToposThickening.FirstOrderLiftDiagram.Lift` — as the derivation
`f' ↦ b(f') - φ(a(f'))` of `𝒪_{B'₁}[ℰ]` over `𝒪_{B'₁}`. On the generator `[x]` attached to a
local section `x = (x₁, x₂)` of `ℰ` that derivation takes the value `x₂ - φ(x₁)`, which is
killed by the reduction of the back layer — precisely because the two reductions of `x` agree,
which is the condition defining `ℰ` — and so is a local section of `𝒢₂`.

Those values on the generators are all that is needed: the degree `0` term of `NL(α)` is the
free `𝒪_{X₁}`-module on `ℰ`, so they already determine a morphism out of it. That freeness is
`exists_degreeZeroHom_on_generators`, assembled from the public
`Stacks.SheafOfModules.exists_derivation_of_polynomialVariable` and the corepresentation
`degreeZeroHomEquivDerivation` of the derivations by the degree `0` term;
`reducedPresentation_eq_presentation` records that the reduced presentation of Step 1
is an instance of it.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftPairSection`: the local section
  `x₂ - φ(x₁)` of `𝒢₂` attached to a lift `φ` and a local section `x` of `ℰ` — the value on the
  generator `[x]` of the source's derivation `b - φ ∘ a`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftGeneratorHom`: those values, as a
  morphism of presheaves of sets `ℰ ⟶ g_*𝒢₂`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.reducedDegreeZero`: the degree `0` term
  of `NL(α)` for the reduced presentation of Step 1.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftDegreeZeroHom`: the morphism
  `θ : NL(α)₀ ⟶ g_*𝒢₂` prescribed on the generators by a lift.

## Main results

* `Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_liftPairSection`: the difference
  `x₂ - φ(x₁)` is the image of exactly one local section of `𝒢₂`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftDegreeZeroHom_generator`: `θ` takes the
  prescribed value on the generator attached to a local section of `ℰ`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.FreeAlgebra
open Stacks.Sites.Conormal

universe v u w

namespace Deformation.ToposThickening.FirstOrderLiftDiagram

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)

/-! ### The values of the source's derivation on the generators -/

omit [HasWeakSheafify J CommRingCat] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget AddCommGrpCat)] [HasSheafify J AddCommGrpCat] in
/-- **The value on a generator of the source's derivation `b - φ ∘ a`.** For a lift `φ` and a
local section `x = (x₁, x₂)` of `ℰ`, the difference `x₂ - φ(x₁)` is killed by the reduction of
the back layer, so it is the image of exactly one local section of `𝒢₂`. The two reductions of
`x` agree by the very condition defining `ℰ`, and `φ` is over the comparison `g`; that is what
makes the difference vanish. -/
theorem existsUnique_liftPairSection (p : Lift D) (U : Cᵒᵖ) (x : D.PairSection U) :
    ∃! m : D.back.G.val.obj U,
      D.back.incl m = x.1.2 - p.hom.hom.app U x.1.1 := by
  refine D.back.kernelUniversal U _ ?_
  rw [map_sub, p.reduction_app _ _, ← x.2, sub_self]

/-- The local section of `𝒢₂` attached to a lift and a local section of `ℰ`: the value on the
generator `[x]` of the source's derivation `b - φ ∘ a` of Step 2. -/
def liftPairSection (p : Lift D) (U : Cᵒᵖ) (x : D.PairSection U) : D.back.G.val.obj U :=
  (existsUnique_liftPairSection D p U x).choose

/-- The defining equation of `liftPairSection`. -/
theorem incl_liftPairSection (p : Lift D) (U : Cᵒᵖ) (x : D.PairSection U) :
    D.back.incl (liftPairSection D p U x) = x.1.2 - p.hom.hom.app U x.1.1 :=
  (existsUnique_liftPairSection D p U x).choose_spec.1

/-- `liftPairSection` is compatible with the restriction maps of the site. -/
theorem liftPairSection_map (p : Lift D) {U V : Cᵒᵖ} (h : U ⟶ V) (x : D.PairSection U) :
    liftPairSection D p V (D.pairSectionMap h x) =
      D.back.G.val.map h (liftPairSection D p U x) := by
  refine D.back.incl_injective ?_
  rw [incl_liftPairSection, D.back.incl_naturality, incl_liftPairSection, map_sub]
  show D.back.O'.obj.map h x.1.2 - p.hom.hom.app V (D.front.O'.obj.map h x.1.1) =
    D.back.O'.obj.map h x.1.2 - D.back.O'.obj.map h (p.hom.hom.app U x.1.1)
  rw [sheafHom_naturality_apply]

/-- **The values of the source's derivation on the generators, as a morphism of presheaves of
sets `ℰ ⟶ g_*𝒢₂`.** This is the datum the freeness of the degree `0` term of `NL(α)` on the
generators consumes. -/
def liftGeneratorHom (p : Lift D) :
    pairPresheaf D ⟶ (pushedIdeal D).val.presheaf ⋙ forget AddCommGrpCat.{max u v w} where
  app U := TypeCat.ofHom fun x => liftPairSection D p U x
  naturality {U V} h := by
    ext x
    exact liftPairSection_map D p h x

/-! ### The degree `0` term of `NL(α)`, and the factorization prescribed by a lift -/

/-- The reduced presentation of Step 1 is the library's `presentation` of the family of
generators `α`, so everything the library proves about a presentation applies to it — in
particular the freeness of the degree `0` term of `NL(α)` on the generators. -/
theorem reducedPresentation_eq_presentation :
    Stacks.SheafOfModules.presentation J D.front.OB D.front.O D.front.f
      (pairPresheaf D) (pairAlpha D) = reducedPresentation D := rfl

/-- The degree `0` term of the source's `NL(α)` for the reduced presentation of Step 1, namely
`𝒪_{X₁} ⊗_{𝒪_{B₁}[ℰ]} Ω_{𝒪_{B₁}[ℰ]/𝒪_{B₁}}`. The source's Step 2 factors `ξ` through it; it is
the free `𝒪_{X₁}`-module on `ℰ`. -/
abbrev reducedDegreeZero :
    SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O) :=
  (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, max u v w} J
    D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D)).X₂

/-- The local differential `1 ⊗ d[x]` of the generator attached to a local section of `ℰ`: the
basis element of the degree `0` term of `NL(α)` that a morphism out of it is prescribed on. -/
abbrev reducedGeneratorDifferential (U : Cᵒᵖ) (x : D.PairSection U) :
    (reducedDegreeZero D).val.obj U :=
  tensorDifferential.{v, u, max u v w, max u v w} J D.front.OB
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
    (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D))
    (reducedPresentation D) U
    ((freeAlgebraSheafVariable J D.front.OB (pairPresheaf D)).app U x)

/-- The local section `1 ⊗ d y` of the degree `0` term of `NL(α)` for the reduced presentation
of Step 1. On a variable this is `reducedGeneratorDifferential`. -/
abbrev reducedTensorDifferential (X : Cᵒᵖ)
    (y : (freeAlgebraSheaf J D.front.OB (pairPresheaf D)).obj.obj X) :
    (reducedDegreeZero D).val.obj X :=
  tensorDifferential.{v, u, max u v w, max u v w} J D.front.OB
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
    (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D))
    (reducedPresentation D) X y

/-- The target of a derivation of `𝒪_{B₁}[ℰ]` attached to a sheaf of `𝒪_{X₁}`-modules, read as
a sheaf of `𝒪_{B₁}[ℰ]`-modules through the reduced presentation of Step 1. -/
abbrev reducedPushforwardModule
    (N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O)) :
    SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (freeAlgebraSheaf J D.front.OB (pairPresheaf D))) :=
  (SheafOfModules.pushforward (underlyingRingHomForPullback J
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O (reducedPresentation D))).obj N

/-- **The degree `0` term of `NL(α)` corepresents the derivations of `𝒪_{B₁}[ℰ]` over `𝒪_{B₁}`.**
For the reduced presentation of Step 1, a morphism out of
`𝒪_{X₁} ⊗_{𝒪_{B₁}[ℰ]} Ω_{𝒪_{B₁}[ℰ]/𝒪_{B₁}}` into a sheaf of `𝒪_{X₁}`-modules `N` is a derivation
of `𝒪_{B₁}[ℰ]` over `𝒪_{B₁}` with values in `N`: the identification
`Stacks.Sites.Conormal.tensorDifferentialsIso` of the degree `0` term with an extension of
scalars, the extension/restriction adjunction, and the universal property of the differentials. -/
def degreeZeroHomEquivDerivation
    (N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O)) :
    (reducedDegreeZero D ⟶ N) ≃
      PresheafOfModulesOfCommRing.Derivation' (reducedPushforwardModule D N).val
        (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D)).hom :=
  (tensorDifferentialsIso.{v, u, max u v w, max u v w} J D.front.OB
      (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
      (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D))
      (reducedPresentation D)).homFromEquiv.trans
    (((SheafOfModules.pullbackPushforwardAdjunction
      (underlyingRingHomForPullback J (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
        (reducedPresentation D))).homEquiv _ N).trans
      (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{max u v w} D.front.OB
        (freeAlgebraSheaf J D.front.OB (pairPresheaf D))
        (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D))).corepresentableBy.homEquiv)

/-- The derivation attached to a morphism out of the degree `0` term of `NL(α)` takes a local
section `y` of `𝒪_{B₁}[ℰ]` to the value of the morphism on `1 ⊗ d y`. -/
theorem degreeZeroHomEquivDerivation_d
    (N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O))
    (k : reducedDegreeZero D ⟶ N) (X : Cᵒᵖ)
    (y : (freeAlgebraSheaf J D.front.OB (pairPresheaf D)).obj.obj X) :
    (degreeZeroHomEquivDerivation D N k).d y = k.val.app X (reducedTensorDifferential D X y) := by
  have hco := (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{max u v w} D.front.OB
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D))
    (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D))).corepresentableBy.homEquiv_eq
      (((SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J (freeAlgebraSheaf J D.front.OB (pairPresheaf D))
          D.front.O (reducedPresentation D))).homEquiv _ N)
        ((tensorDifferentialsIso.{v, u, max u v w, max u v w} J D.front.OB
          (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
          (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D))
          (reducedPresentation D)).inv ≫ k))
  refine Eq.trans (congrArg (fun Θ => Θ.d (X := X) y) hco) ?_
  exact congrArg (fun t => k.val.app X t)
    (tensorDifferentialsIso_inv_d.{v, u, max u v w, max u v w} J D.front.OB
      (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
      (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D)) (reducedPresentation D) X y)

/-- The sheafification unit `𝒪_{B₁}(-)[ℰ(-)] ⟶ 𝒪_{B₁}[ℰ]` presenting the free algebra sheaf. -/
abbrev reducedPolynomialUnit :=
  (toSheafification J CommRingCat.{max u v w}).app
    (polynomialPresheaf J D.front.OB (pairPresheaf D))

/-- The sheafification unit `𝒪_{B₁}(-)[ℰ(-)] ⟶ 𝒪_{B₁}[ℰ]` is locally surjective. -/
instance isLocallySurjective_reducedPolynomialUnit :
    Presheaf.IsLocallySurjective J (reducedPolynomialUnit D) :=
  (J.W_toSheafify _).isLocallySurjective

/-- The sheafification unit `𝒪_{B₁}(-)[ℰ(-)] ⟶ 𝒪_{B₁}[ℰ]` is locally injective. -/
instance isLocallyInjective_reducedPolynomialUnit :
    Presheaf.IsLocallyInjective J (reducedPolynomialUnit D) :=
  (J.W_toSheafify _).isLocallyInjective

/-- **The degree `0` term of `NL(α)` is free on the generators**, in the form Step 2 uses: every
morphism of presheaves of sets out of `ℰ` into the sections of a sheaf of `𝒪_{X₁}`-modules is
the restriction to the generators `1 ⊗ d[x]` of a morphism out of the degree `0` term. The
derivation prescribing the values at the variables is
`Stacks.SheafOfModules.exists_derivation_of_polynomialVariable`, and
`degreeZeroHomEquivDerivation` turns it into a morphism. -/
theorem exists_degreeZeroHom_on_generators
    (N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O))
    (k : pairPresheaf D ⟶ N.val.presheaf ⋙ forget AddCommGrpCat.{max u v w}) :
    ∃ l : reducedDegreeZero D ⟶ N,
      ∀ (X : Cᵒᵖ) (e : D.PairSection X), l.val.app X (reducedGeneratorDifferential D X e) =
        k.app X e := by
  obtain ⟨Θ, hΘ⟩ := Stacks.SheafOfModules.exists_derivation_of_polynomialVariable J D.front.OB
    (pairPresheaf D) (reducedPolynomialUnit D) (reducedPushforwardModule D N) k
  let Θ' : PresheafOfModulesOfCommRing.Derivation' (reducedPushforwardModule D N).val
      (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D)).hom := Θ
  refine ⟨(degreeZeroHomEquivDerivation D N).symm Θ', fun X e => ?_⟩
  refine (degreeZeroHomEquivDerivation_d D N _ X _).symm.trans ?_
  refine Eq.trans (congrArg (fun Θ₁ => Θ₁.d (X := X)
    ((freeAlgebraSheafVariable J D.front.OB (pairPresheaf D)).app X e))
    (Equiv.apply_symm_apply _ Θ')) ?_
  exact hΘ X e

/-- **Step 2 of the proof of [Stacks Project, Tag 08U8], first half: a lift prescribes a
morphism out of the degree `0` term of `NL(α)`.** The source's derivation `b - φ ∘ a` of
`𝒪_{B'₁}[ℰ]` takes the value `x₂ - φ(x₁)` on the generator `[x]`, and the degree `0` term is
free on the generators (`exists_degreeZeroHom_on_generators`), so those values are realised by a
morphism `θ : NL(α)₀ ⟶ g_*𝒢₂`. What remains of Step 2 is that this `θ` factors the obstruction
homomorphism `ξ`, i.e. that `d ≫ θ = ξ`. -/
def liftDegreeZeroHom (p : Lift D) : reducedDegreeZero D ⟶ pushedIdeal D :=
  (exists_degreeZeroHom_on_generators D (pushedIdeal D) (liftGeneratorHom D p)).choose

/-- `liftDegreeZeroHom` takes on the generator attached to a local section `x = (x₁, x₂)` of
`ℰ` the value `x₂ - φ(x₁)` prescribed by the lift. -/
theorem liftDegreeZeroHom_generator (p : Lift D) (U : Cᵒᵖ) (x : D.PairSection U) :
    (liftDegreeZeroHom D p).val.app U (reducedGeneratorDifferential D U x) =
      liftPairSection D p U x :=
  (exists_degreeZeroHom_on_generators D (pushedIdeal D) (liftGeneratorHom D p)).choose_spec U x

end Deformation.ToposThickening.FirstOrderLiftDiagram

end
