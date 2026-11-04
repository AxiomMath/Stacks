module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CoefficientChangeProjectionFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnAQuotientRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.AdicQuotientModuleFiltration
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude modulo the powers of a sheaf of ideals

Let `(C, O)` be a ringed site, `I ⊆ O` a sheaf of ideals and `K` an object of `D(O)`. If
`K ⊗^L_O O/I` has Tor amplitude in `[a, b]` as an object of `D(O/I)`, then `K ⊗^L_O O/Iⁿ` has
Tor amplitude in `[a, b]` as an object of `D(O/Iⁿ)`, for every `n`.

## Main results

* `Stacks.Sites.isZero_homologyTensorSingle_of_hasTorAmplitude_adicQuotientOne`: the hypothesis
  read over `O` at a sheaf of `O`-modules killed by `I`.
* `Stacks.Sites.hasTorAmplitude_adicQuotient_of_hasTorAmplitude_adicQuotientOne`:
  **Stacks 0942 part (2).**

## Implementation notes

Both statements are the source's proof read through the projection formula at a change of
coefficient rings, `Stacks.Cohomology.CoefficientChange.projectionFormulaIso`:

`K ⊗^L_O F|_O ≅ ((K ⊗^L_O O/Iⁿ) ⊗^L_{O/Iⁿ} F)|_O`,

together with the fact that restriction of scalars neither creates nor destroys a vanishing
cohomology sheaf,
`Stacks.SheafOfModules.ChangeOfRings.isZero_homology_mapDerivedCategory_restrictScalars_iff`.
Those two move the whole question from `D(O/Iⁿ)` to `D(O)`, where the dévissage is already
carried out: the filtration of a sheaf of `O/Iⁿ`-modules by the powers of `I` reaches zero
(`Stacks.Sites.isZero_homologyTensorSingle_restrictScalars_adicQuotient`), so the vanishing
need only be checked at the sheaves of `O`-modules killed by `I`; and those are exactly the
sheaves of `O/I`-modules read over `O`
(`Stacks.Sites.essImage_restrictScalars_adicQuotientRingHom`), where the projection formula at
`O ⟶ O/I` turns the question back into the hypothesis.

The source phrases the dévissage as "`F` has a finite filtration whose successive quotients are
sheaves of `O/I`-modules" and then identifies `(K ⊗^L_O O/Iⁿ) ⊗^L_{O/Iⁿ} G` with
`(K ⊗^L_O O/I) ⊗^L_{O/I} G` for such a quotient `G`. Here that identification is not made
directly: both sides are compared with `K ⊗^L_O G|_O` instead, which is the same comparison
read over `O` and needs no cancellation of the intermediate ring.

`idealPow I 1 = I` is used at the step that recognises a sheaf killed by `I` as one killed by
`I¹`. It is applied by generalising the sheaf of ideals and substituting rather than by
rewriting: the membership `a ∈ (idealPow I 1).obj U` is stated at a `SetLike` instance whose
elaborated form rewriting does not keep type-correct.

The derived categories are the standard ones. This is inherited from the projection formula,
which rests on the derived pullback of Stacks 06YY and on Stacks 06YS, both of which are
available in this tree only at that choice; the three sheaves of rings `O`, `O/I` and `O/Iⁿ`
are then all read in it.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.DerivedTensorProduct
open Stacks.SheafOfModules.ChangeOfRings

universe u

namespace Stacks.Sites

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
-- `adicQuotientRingedSite` and `quotientRingedSite` are ordinary `def`s, so instance search,
-- which unfolds only up to reducible transparency, cannot see that the underlying site of
-- `(C, O/Iⁿ)` is the given one and never reaches the sheafification and local-bijectivity
-- instances carried by `(C, O)`.  Opening the two definitions to instance search is what
-- `Stacks.Sites.adicDerivedTensorProduct` does for the same reason at its own definition.
attribute [local instance_reducible] quotientRingedSite adicQuotientRingedSite

variable {X : RingedSite.{u, u, u}} [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : IdealSubsheaf.{u, u, u} X.O)

/-- **The hypothesis of Stacks 0942 part (2), read over `O` at a sheaf of modules killed by
`I`.** If `K ⊗^L_O O/I` has Tor amplitude in `[a, b]` over `O/I` and `i` lies outside
`[a, b]`, then the `i`-th cohomology of `K ⊗^L_O G[0]` vanishes for every sheaf of `O`-modules
`G` whose sections are killed by the sections of `I`.

Such a `G` is a sheaf of `O/I`-modules read over `O`, by
`Stacks.Sites.essImage_restrictScalars_adicQuotientRingHom`; the projection formula at
`O ⟶ O/I` then identifies `K ⊗^L_O G[0]` with `((K ⊗^L_O O/I) ⊗^L_{O/I} G[0])|_O`, whose
cohomology vanishes over `O` exactly when it does over `O/I`. -/
theorem isZero_homologyTensorSingle_of_hasTorAmplitude_adicQuotientOne
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, _} X)
    (T₁ : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, _}
      (adicQuotientRingedSite X I 1))
    (K : RingedSite.DerivedModules.{u, u, u, _} X) (a b i : ℤ) (hi : i ∉ Set.Icc a b)
    (h : HasTorAmplitude T₁
      ((Stacks.Cohomology.derivedCoefficientChange (toAdicQuotient I 1)).obj K) a b)
    (G : RingedSite.Modules.{u, u, u} X)
    (hG : ∀ (U : X.Cᵒᵖ) (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
      c ∈ I.obj U → ∀ g : G.val.obj U, c • g = 0) :
    IsZero (homologyTensorSingle T K i G) := by
  have key : ∀ N : IdealSubsheaf.{u, u, u} X.O, N = I →
      ∀ (U : X.Cᵒᵖ) (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
        c ∈ N.obj U → ∀ g : G.val.obj U, c • g = 0 := by
    rintro N rfl U c hc g
    exact hG U c hc g
  obtain ⟨G', ⟨e⟩⟩ := essImage_restrictScalars_adicQuotientRingHom I 1 G
    (key _ (idealPow_one I))
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} X) i).mapIso
      ((T.tensor.obj K).mapIso
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).mapIso e.symm)))
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} X) i).mapIso
      (Stacks.Cohomology.CoefficientChange.projectionFormulaIso (toAdicQuotient I 1)
        T.toRingedSiteDerivedTensorProduct T₁.toRingedSiteDerivedTensorProduct K G'))
  rw [isZero_homology_mapDerivedCategory_restrictScalars_iff]
  exact h G' i hi

/-- **Stacks 0942 part (2).** If `K ⊗^L_O O/I` has Tor amplitude in `[a, b]` as an object of
`D(O/I)`, then `K ⊗^L_O O/Iⁿ` has Tor amplitude in `[a, b]` as an object of `D(O/Iⁿ)`, for
every `n`.

A sheaf `F` of `O/Iⁿ`-modules is tested by moving `(K ⊗^L_O O/Iⁿ) ⊗^L_{O/Iⁿ} F[0]` to `D(O)`:
restriction of scalars reflects a vanishing cohomology sheaf, and the projection formula at
`O ⟶ O/Iⁿ` identifies the restriction with `K ⊗^L_O F|_O`. There the filtration of `F|_O` by
the powers of `I` reaches zero, so the vanishing follows from the one at the sheaves of
`O`-modules killed by `I`, which is the hypothesis. -/
@[stacks 0942 "tor amplitude modulo every power of the ideal"]
theorem hasTorAmplitude_adicQuotient_of_hasTorAmplitude_adicQuotientOne
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, _} X)
    (T₁ : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, _}
      (adicQuotientRingedSite X I 1))
    (n : ℕ)
    (Tₙ : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, _}
      (adicQuotientRingedSite X I n))
    (K : RingedSite.DerivedModules.{u, u, u, _} X) (a b : ℤ)
    (h : HasTorAmplitude T₁
      ((Stacks.Cohomology.derivedCoefficientChange (toAdicQuotient I 1)).obj K) a b) :
    HasTorAmplitude Tₙ
      ((Stacks.Cohomology.derivedCoefficientChange (toAdicQuotient I n)).obj K) a b := by
  intro F i hi
  refine (isZero_homology_mapDerivedCategory_restrictScalars_iff
    (adicQuotientRingHom I n) _ i).mp ?_
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} X) i).mapIso
      (Stacks.Cohomology.CoefficientChange.projectionFormulaIso (toAdicQuotient I n)
        T.toRingedSiteDerivedTensorProduct Tₙ.toRingedSiteDerivedTensorProduct K F).symm)
  exact isZero_homologyTensorSingle_restrictScalars_adicQuotient I n F T K i
    (fun G hG => isZero_homologyTensorSingle_of_hasTorAmplitude_adicQuotientOne
      I T T₁ K a b i hi h G hG)

end Stacks.Sites

end
