module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.CycleSectionChart
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.GlobalSectionHom
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.QuasicoherentModelStandard
public import StacksCore.Tactic.StacksAttribute

/-!
# Detecting a nonzero object of `D_QCoh(𝒪_X)` by twisted hypercohomology

**[Stacks, Tag 0BQR].** Let `X` be a scheme carrying an ample invertible `𝒪_X`-module `L` and let
`K` be a nonzero object of `D_QCoh(𝒪_X)`. Then there are `n ≥ 0` and `p` with

`H^p(X, K ⊗^𝐋_{𝒪_X} L^{⊗ n}[0]) ≠ 0`,

the tensor product being the derived tensor product of [Stacks, Tag 06YH] and the cohomology the
derived hypercohomology — the degree-`p` homology of unbounded derived global sections.

## Main definitions

* `Stacks.AmpleNonvanishing.twistCycleHom`: the cocycle of the tag's argument, as a morphism
  `𝒪_X ⟶ Z^p(K ⊗ L^{⊗ m})`.

## Main results

* `Stacks.AmpleNonvanishing.twistCycleHom_comp_homologyπ_ne_zero`: the class of that cocycle in
  `H^p(K ⊗ L^{⊗ m})` is nonzero.
* `Stacks.AmpleNonvanishing.exists_nonzero_hypercohomology_tensorPower`: **[Stacks, Tag 0BQR]**.

## Implementation notes

Five inputs, assembled in the order of the source's own argument.

1. `Stacks.AmpleNonvanishing.exists_quasicoherentComplex_nonzeroHomology_of_isAmple` is
   [Stacks, Tag 08DB] at the tag's own hypotheses together with the first line of the tag's proof:
   `K` is the class of a cochain complex `H` of quasi-coherent `𝒪_X`-modules, some cohomology
   sheaf `H^p(H)` of which is nonzero.
2. `Stacks.AmpleNonvanishingChart.exists_twistedCycleSection_class_ne_zero` runs the chart
   argument on the **cycles** and returns a global section `ρ` of `Z^p(H) ⊗ L^{⊗ m}` whose class
   in `H^p(H) ⊗ L^{⊗ m}` is nonzero.
3. `Stacks.AmpleNonvanishing.unitHomOfGlobalSection` reads `ρ` as a morphism out of the unit and
   `Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso` crosses from the monoidal `⊗` the
   section-extension results are stated at to `Stacks.SheafOfModules.Tensor.sheafTensor`, the
   spelling `Stacks.AmpleNonvanishing.termwiseTwistCyclesIso` is stated at.
4. `Stacks.AmpleNonvanishing.termwiseTwistCyclesIso_hom_homologyπ` transports the class through
   the twist.
5. `Stacks.AmpleNonvanishing.not_isZero_hypercohomology_derivedTensorSingle_of_cycleHom` turns
   the resulting cocycle into the nonvanishing of the hypercohomology group.

**One spelling throughout, and why.** Every composite below is formed at
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf` and never at `AlgebraicGeometry.Scheme.Modules`.
The two are `rfl`-equal types with different instance provenance — `Preadditive (SheafOfModules R)`
is a global instance, `Preadditive X.Modules` only the local
`Stacks.SectionRingGeometric.schemePreadditive` — and a composite formed at the second spelling
admits no zero morphism and matches no lemma stated at the first. Ascribing an *object* does not
move the morphism type: the `Category` instance comes from the declared type of the variable. So
the fix is at the binder, in
`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/GlobalSectionHom.lean`, and the monoidal objects
are reached by passing them to a binder declared at the chosen spelling.

**`rw` versus `exact`.** Several steps of this cluster cannot be done by `rw`: it compares the
instances carried by `≫`, `▷` and `tensorSection` at *reducible* transparency, where the two
spellings do not meet, and reports a pattern that unifies with the goal term by term. `exact`
compares at default transparency, where they do. So where a rewrite refuses, the step is an
`exact` of a term whose own type fixes the spelling, chained with `Eq.trans` and `congrArg`; see
the implementation notes of
`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/CycleSectionChart.lean` and of
`StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormula.lean`, which record the same thing.

**The two models of the derived category.** `D_QCoh(𝒪_X)` and [Stacks, Tag 08DB] exist only at the
locally small model, and the hypercohomology identification of [Stacks, Tag 08JA] only at
`CategoryTheory.HasDerivedCategory.standard`. The hypothesis is stated at the first and the
conclusion at the second, related by `Stacks.Injectives.grothendieckModelEquiv`, which is the
*identity on objects* and carries `Q` to `Q` on the nose: the object in the conclusion is the very
object `K.1`, read in the other model. Nothing is weakened by the crossing.

**The derived tensor product is written out as `derTensor`,** not as the abbreviation
`Stacks.Duality.derivedTensor X`, whose type is spelled over `X.Modules`; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/DerivedTwistHypercohomology.lean`.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open Stacks.Ample
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.AmpleNonvanishing

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### The cocycle -/

/-- **The cocycle of [Stacks, Tag 0BQR], as a morphism into the cycles of the termwise twist.** A
global section of `Z^p(H) ⊗ L`, read as a morphism out of the unit and transported across the two
spellings of the tensor product into the degree-`p` cycles of
`Stacks.AmpleNonvanishing.termwiseTwist`. -/
def twistCycleHom (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (H : CochainComplex X.Modules ℤ) (p : ℤ) (ρ : Γ(H.cycles p ⊗ L, ⊤)) :
    structureUnit X ⟶ (termwiseTwist X L H).cycles p :=
  unitHomOfGlobalSection ((H.cycles p ⊗ L : X.Modules)) ρ ≫
    (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X (H.cycles p) L).hom ≫
    (termwiseTwistCyclesIso X L H p).inv

/-- **The class of the cocycle is nonzero.** If the class of the global section `ρ` in
`H^p(H) ⊗ L` is nonzero, then the class of `Stacks.AmpleNonvanishing.twistCycleHom` in the
cohomology sheaf `H^p(H ⊗ L)` of the twist is nonzero.

The transport is `Stacks.AmpleNonvanishing.termwiseTwistCyclesIso_hom_homologyπ` — the twist of
the projection of cycles onto cohomology is the projection of the twisted cycles — followed by
the naturality of the tensor-spelling comparison in its left variable; and
`Stacks.AmpleNonvanishing.unitHomOfGlobalSection_comp` identifies the image of the morphism out
of the unit with the morphism attached to the image of the section. -/
theorem twistCycleHom_comp_homologyπ_ne_zero (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (H : CochainComplex X.Modules ℤ) (p : ℤ)
    (ρ : Γ(H.cycles p ⊗ L, ⊤))
    (hρ : Scheme.Modules.Hom.app (H.homologyπ p ▷ L) ⊤ ρ ≠ 0) :
    twistCycleHom X L H p ρ ≫ (termwiseTwist X L H).homologyπ p ≠ 0 := by
  intro hz
  have hρ' : (H.homologyπ p ▷ L).val.app (op (⊤ : X.Opens)) ρ ≠ 0 := hρ
  have h1 : twistCycleHom X L H p ρ ≫
      ((termwiseTwist X L H).homologyπ p ≫ (termwiseTwistHomologyIso X L H p).hom) = 0 := by
    rw [← Category.assoc, hz, zero_comp]
  -- The twist comparison cancels, by `exact` and not by `rw`: the goal below mentions
  -- `termwiseTwist X L H` with `H` at the `CochainComplex X.Modules ℤ` spelling, which is not
  -- type-correct at the `implicit` transparency level that `rw`'s motive check uses.
  have key : (termwiseTwistCyclesIso X L H p).inv ≫
      ((termwiseTwist X L H).homologyπ p ≫ (termwiseTwistHomologyIso X L H p).hom) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
        (H.homologyπ p)).app L :=
    (congrArg (fun z => (termwiseTwistCyclesIso X L H p).inv ≫ z)
          (termwiseTwistCyclesIso_hom_homologyπ X L H p)).symm.trans
      ((termwiseTwistCyclesIso X L H p).inv_hom_id_assoc _)
  -- The reassociation is also done by `exact`: `rw [Category.assoc]` is refused on any term
  -- containing `termwiseTwist X L H`, because `H` is declared at `CochainComplex X.Modules ℤ`
  -- while `termwiseTwist` asks for `Stacks.Duality.TensorComplex X`, so the motive `rw` builds is
  -- not type-correct at the `implicit` transparency level even for `Category.assoc`.
  have key' : ((Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X
          (H.cycles p) L).hom ≫ (termwiseTwistCyclesIso X L H p).inv) ≫
        ((termwiseTwist X L H).homologyπ p ≫ (termwiseTwistHomologyIso X L H p).hom) =
      (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X (H.cycles p) L).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
          (H.homologyπ p)).app L :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X
        (H.cycles p) L).hom ≫ z) key)
  have h2 : unitHomOfGlobalSection ((H.cycles p ⊗ L : X.Modules)) ρ ≫
      ((Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X (H.cycles p) L).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
          (H.homologyπ p)).app L) = 0 :=
    ((congrArg (fun z => unitHomOfGlobalSection ((H.cycles p ⊗ L : X.Modules)) ρ ≫ z)
      key'.symm).trans (Category.assoc _ _ _).symm).trans h1
  -- The naturality of the tensor-spelling comparison, and the compatibility of the morphism out
  -- of the unit with composition, are applied by `exact` and not by `rw`: the comparison's own
  -- statement spells `X.toRingedSpace` unfolded through `Scheme.toLocallyRingedSpace`, which no
  -- rewrite matches against the folded spelling in the goal, although the two are defeq.
  have h3 : unitHomOfGlobalSection ((H.cycles p ⊗ L : X.Modules)) ρ ≫
      ((H.homologyπ p ▷ L) ≫
        (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X (H.homology p) L).hom) =
      0 :=
    (congrArg (fun z => unitHomOfGlobalSection ((H.cycles p ⊗ L : X.Modules)) ρ ≫ z)
      (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso_naturality_left X
        (H.homologyπ p) L)).trans h2
  have h4 : unitHomOfGlobalSection ((H.homology p ⊗ L : X.Modules))
        ((H.homologyπ p ▷ L).val.app (op (⊤ : X.Opens)) ρ) ≫
      (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X (H.homology p) L).hom = 0 :=
    (congrArg (fun z => z ≫
        (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X (H.homology p) L).hom)
      (unitHomOfGlobalSection_comp ρ (H.homologyπ p ▷ L))).symm.trans
        ((Category.assoc _ _ _).trans h3)
  -- Cancelling the comparison is an `exact` of `Iso.cancel_iso_hom_right`, as above.
  exact hρ' (eq_zero_of_unitHomOfGlobalSection_eq_zero ((H.homology p ⊗ L : X.Modules)) _
    ((Iso.cancel_iso_hom_right _ _ (Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso X
      (H.homology p) L)).1 (h4.trans zero_comp.symm)))

/-! ### Stacks 0BQR -/

/-- **[Stacks, Tag 0BQR].** Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module and `K` a
**nonzero** object of `D_QCoh(𝒪_X)`. Then there are an exponent `n` and a degree `p` with

`H^p(X, K ⊗^𝐋_{𝒪_X} L^{⊗ n}[0]) ≠ 0`.

The tensor product is the derived tensor product of [Stacks, Tag 06YH] with the `n`-th tensor
power of `L` placed in degree zero, and the cohomology is the derived hypercohomology, the
degree-`p` homology of unbounded derived global sections. The object the conclusion is about is
`K` itself, read in the standard model of the derived category; see the implementation notes on
the two models. -/
@[stacks 0BQR "the general derived statement: K is an arbitrary nonzero object of D_QCoh(O_X), \
the tensor product is the derived one of Tag 06YH with a tensor power of L in degree zero, and \
the cohomology is the derived hypercohomology of Tag 08JA in degree p. The hypothesis is stated \
at the locally small model of D(O_X), the only model Tag 08DB is available at, and the \
conclusion at the standard model, the only model Tag 08JA is available at; the object in the \
conclusion is K itself, Stacks.Injectives.grothendieckModelEquiv being the identity on objects. \
The degree-zero module case, which this does not subsume because it carries an explicit witness, \
is the separate carrier \
Stacks.AmpleNonvanishingChart.exists_twistedSection_restrict_eq_tensorSection"]
theorem exists_nonzero_hypercohomology_tensorPower (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L)
    (K : (@DerivedCategoryB.derivedCategoryB X.Modules _ _
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory)
    (hK : ¬ IsZero K) :
    ∃ (n : ℕ) (p : ℤ),
      ¬ IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
        ((derivedModuleGlobalSections
            (Stacks.SheafOfModules.ringedSite X.toRingedSpace.sheaf)).obj
          (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj
              ((Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse.obj K.1)).obj
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
                (ComplexShape.up ℤ) 0).obj (tensorPowModule X L (n : ℤ))))))) := by
  obtain ⟨G, p, hGp, ⟨eStd⟩⟩ :=
    exists_quasicoherentComplex_nonzeroHomology_of_isAmple X L hL K hK
  obtain ⟨m, ρ, hρ⟩ := Stacks.AmpleNonvanishingChart.exists_twistedCycleSection_class_ne_zero
    L hL (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G) (fun i => (G.X i).property) p hGp
  exact ⟨m, p, not_isZero_hypercohomology_derivedTensorSingle_of_cycleHom X _ _ p _ eStd _
    (twistCycleHom_comp_homologyπ_ne_zero X _ _ p ρ hρ)⟩

end Stacks.AmpleNonvanishing

end
