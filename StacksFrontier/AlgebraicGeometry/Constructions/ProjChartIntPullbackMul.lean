module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullbackMultiplication
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntDivisionPullback

/-!
# The pullback comparison of Tag 01CU's integer tensor powers is multiplicative

Let `j : Y' ⟶ Y` be a morphism of schemes and `L` an invertible `𝒪_Y`-module.
`Stacks.TensorPowerPullback.pullbackIntPowIso` compares the integer tensor powers of
[Stacks, Tag 01CU] under pullback, `j^*(L ^⊗ d) ≅ (j^*L) ^⊗ d`, in **every** integer degree, and
`Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso` proves it **multiplicative** for the
coherent multiplication of that tag. This file carries both to the scheme-level vocabulary that
`Stacks.TensorPowerDivision` and the charts of Tag 01NK are written in.

## Why anything is needed at all

Two things differ between the two vocabularies, and only two.

* **The spelling of the functor and the powers.** `AlgebraicGeometry.Scheme.Modules.pullback j` is
  `Stacks.RingedSpace.pullbackFunctor j.toLRSHom.toShHom` and
  `Stacks.AmpleProjectiveImmersion.tensorPowerModule Y L d` is
  `Stacks.SheafOfModules.TensorPower.tensorPower Y.presheaf _ L d`, both by `rfl`; the sheaf
  conditions in the two spellings are proofs of one `Prop`. So `intPullIso` below is
  `pullbackIntPowIso` with no transport, and `pullbackIntPowIso_coherentMulIso` is quotable
  verbatim.
* **The monoidal structure.** The known multiplicativity lives where `⊗` **is** the tensor
  product sheaf of [Stacks, Tag 01CA] on the nose. `Stacks.TensorPowerDivision.intMulIso`, which
  is what the division across degrees multiplies by, lives in the localized structure
  `Stacks.SheafInternalHom.schemeMonoidalCategory`, where `⊗` is only *isomorphic* to that sheaf,
  via `Stacks.SheafOfModules.tensorObjIso`. Since
  `Stacks.SheafOfModules.TensorPower.monoidalMulIso` is by definition
  `tensorObjIso ≪≫ coherentMulIso`, the whole difference is one `tensorObjIso` on each side, and
  moving it across is its own naturality.

## Main definitions

* `…ProjChartIntPullbackMul.intPullIso`: the comparison `j^*(L ^⊗ d) ≅ (j^*L) ^⊗ d` at the scheme
  spelling, in every integer degree.
* `…ProjChartIntPullbackMul.intCotensor`: the cotensorator of `j^*` in the **localized** monoidal
  structure, obtained from `Stacks.PullbackTensorCoherence.pullbackTensorComparison` by
  conjugating with `tensorObjIso` on each side.

## Main results

* `…ProjChartIntPullbackMul.intPullIso_intMulIso`: **the comparison carries
  `Stacks.TensorPowerDivision.intMulIso` for `L` to the one for `j^*L`**, through
  `intCotensor`, in every pair of integer degrees and with no hypothesis.

## Implementation notes

`rw` and `simp` are unusable on the categorical structure here: `AlgebraicGeometry.Scheme.Modules`
is a `def`, so neither `CategoryTheory.Functor.map_comp` nor even
`CategoryTheory.Category.assoc` matches a goal that prints character-identically to their
statements. Every step is therefore a term, and the two steps that would need a motive —
reassociating against the known square, and cancelling `tensorObjIso` against its inverse — are
isolated as `assemble` and `cancel_inv`, stated over an abstract category with **every object a
variable**. That is also what keeps the instances resolvable: a `congrArg` whose lambda mentions
`⊗ₘ` forces instance search at the un-schemed spelling of the sheaf of modules, where the
scheme-level monoidal instances do not apply.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.SheafOfModules (tensorObjIso tensorObjIso_naturality sheafifyTensorHom
  sheafifyTensorHom_eq_comparison tensorSheafMapIso_hom_eq)
open Stacks.SheafOfModules.TensorPower (coherentMulIso tensorSheafMapIso)
open Stacks.TensorPowerDivision (intMulIso)
open Stacks.TensorPowerPullback (pullbackIntPowIso pullbackIntPowIso_coherentMulIso)
open Stacks.PullbackTensorCoherence (pullbackTensorComparison)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartIntPullbackMul

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- The assembly of the multiplicativity square, as pure category theory with every object a
variable, so the crossing between the two spellings of the tensor product happens inside a
defeq-tolerant `exact` rather than inside a rewrite. -/
private theorem assemble {C : Type*} [Category C] {W X₁ X₂ Z U V₁ V₂ U' : C}
    (a : W ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ Z) (p : X₁ ⟶ U) (q : U ⟶ V₁) (r : V₁ ⟶ V₂)
    (s : V₂ ⟶ U') (t : U' ⟶ Z) (u : U ⟶ U')
    (h1 : b ≫ c = p ≫ u ≫ t) (h2 : q ≫ r ≫ s = u) :
    (a ≫ b) ≫ c = (a ≫ p ≫ q) ≫ r ≫ s ≫ t := by
  rw [Category.assoc, h1, ← h2]
  simp only [Category.assoc]

/-- Cancelling an isomorphism off the front of a solved square, with every object a variable so
that no instance is sought at a spelling of the tensor product the scheme-level instances do not
cover. -/
private theorem cancel_inv {C : Type*} [Category C] {A B D : C} (e : A ≅ B) (v : A ⟶ D)
    (w : B ⟶ D) (h : v = e.hom ≫ w) : e.inv ≫ v = w := by
  rw [h, e.inv_hom_id_assoc]

/-- Tag 01CU's invertibility class for an invertible module of the ampleness theory. -/
theorem stacksInvertible (Y : Scheme.{u}) (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L).mpr inferInstance

attribute [local instance] stacksInvertible

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y) (L : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y L]

/-- The comparison of Tag 01CU's integer tensor powers under pullback, at the scheme spelling. -/
def intPullIso (d : ℤ) :
    (Scheme.Modules.pullback j).obj (tensorPowerModule Y L d) ≅
      tensorPowerModule Y' ((Scheme.Modules.pullback j).obj L) d :=
  pullbackIntPowIso j.toLRSHom.toShHom L d

/-- The localized intCotensorator, built from the strict one by conjugating with `tensorObjIso`. -/
def intCotensor (A B : Y.Modules) :
    (Scheme.Modules.pullback j).obj (A ⊗ B) ⟶
      (Scheme.Modules.pullback j).obj A ⊗ (Scheme.Modules.pullback j).obj B :=
  (Scheme.Modules.pullback j).map
      (tensorObjIso Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
        A B).hom ≫
    pullbackTensorComparison j.toLRSHom.toShHom A B ≫
    (tensorObjIso Y'.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y')
      ((Scheme.Modules.pullback j).obj A) ((Scheme.Modules.pullback j).obj B)).inv

/-- **The pullback comparison of the integer tensor powers is multiplicative for the monoidal
multiplication of [Stacks, Tag 01CU]**, in every pair of integer degrees and with no hypothesis.

This is `Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso` with one `tensorObjIso`
moved across on each side: `Stacks.TensorPowerDivision.intMulIso` is by definition
`tensorObjIso ≪≫ coherentMulIso`, that square supplies the `coherentMulIso` half, and the
`tensorObjIso` half is `Stacks.SheafOfModules.tensorObjIso_naturality` followed by the
cancellation built into `intCotensor`. -/
theorem intPullIso_intMulIso (k n : ℤ) :
    (Scheme.Modules.pullback j).map (intMulIso L k n).hom ≫ (intPullIso j L (k + n)).hom
      = intCotensor j (tensorPowerModule Y L k) (tensorPowerModule Y L n) ≫
        ((intPullIso j L k).hom ⊗ₘ (intPullIso j L n).hom) ≫
        (intMulIso ((Scheme.Modules.pullback j).obj L) k n).hom := by
  have e1 : (Scheme.Modules.pullback j).map (intMulIso L k n).hom
      = (Scheme.Modules.pullback j).map
          (tensorObjIso Y.presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
            (tensorPowerModule Y L k) (tensorPowerModule Y L n)).hom ≫
        (Scheme.Modules.pullback j).map
          (coherentMulIso Y.presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L k n).hom :=
    (Scheme.Modules.pullback j).map_comp _ _
  have hts : (tensorSheafMapIso Y'.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y')
        (intPullIso j L k) (intPullIso j L n)).hom
      = sheafifyTensorHom Y'.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y')
          (intPullIso j L k).hom (intPullIso j L n).hom :=
    rfl
  have h1 : (Scheme.Modules.pullback j).map
          (coherentMulIso Y.presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) L k n).hom ≫
        (intPullIso j L (k + n)).hom
      = pullbackTensorComparison j.toLRSHom.toShHom
            (tensorPowerModule Y L k) (tensorPowerModule Y L n) ≫
          sheafifyTensorHom Y'.presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y')
            (intPullIso j L k).hom (intPullIso j L n).hom ≫
          (coherentMulIso Y'.presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y')
            ((Scheme.Modules.pullback j).obj L) k n).hom :=
    (pullbackIntPowIso_coherentMulIso j.toLRSHom.toShHom L k n).trans
      (congrArg (fun z => pullbackTensorComparison j.toLRSHom.toShHom
          (tensorPowerModule Y L k) (tensorPowerModule Y L n) ≫ z ≫
        (coherentMulIso Y'.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y')
          ((Scheme.Modules.pullback j).obj L) k n).hom) hts)
  have hnat := tensorObjIso_naturality Y'.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y')
    (intPullIso j L k).hom (intPullIso j L n).hom
  have h2 := cancel_inv _ _ _ hnat
  exact (congrArg (fun z => z ≫ (intPullIso j L (k + n)).hom) e1).trans
    (assemble _ _ _ _ _ _ _ _ _ h1 h2)

end Stacks.AlgebraicGeometry.ProjChartIntPullbackMul

end
