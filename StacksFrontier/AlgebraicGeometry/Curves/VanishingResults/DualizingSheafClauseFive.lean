module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (5) of Tag 0BS2 for the dualizing sheaf of a proper curve

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism with `X` of topological Krull dimension
at most one — the hypotheses of Situation [Stacks, Tag 0B5D]. Clause (5) of [Stacks, Tag 0BS2]
says that the dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` represents the functor
`ℱ ↦ Hom_k(H¹(X, ℱ), k)` on quasi-coherent modules:

  `Hom_{𝒪_X}(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)`,

naturally in `ℱ`. It is proved here from clause (4) — `Stacks.Duality.dualityAddEquivZero` — and
nothing else.

## Main definitions

* `Stacks.Duality.truncLEHomAddEquiv`: for `A` in `D^{≤ n}`, composition with the canonical map
  `τ^{≤ n}X ⟶ X` identifies `Hom(A, τ^{≤ n}X)` with `Hom(A, X)`.
* `Stacks.Duality.singleShiftToDualizingComplex`: the canonical
  `H^{-m}(ω_X^•)[0]⟦m⟧ ⟶ ω_X^•`, and `Stacks.Duality.singleShiftOneToDualizingComplex` its
  `m = 1` case `ω_X[0]⟦1⟧ ⟶ ω_X^•`.
* `Stacks.Duality.stepSingleShift` and `Stacks.Duality.stepTrunc`: the first two of the three
  identifications the proof composes, in degree `-m`; `Stacks.Duality.clauseFiveStepSingle` and
  `Stacks.Duality.clauseFiveStepTrunc` are their `m = 1` cases.
* `Stacks.Duality.dualityAddEquiv`: the whole chain in degree `-m`, which needs only that the
  dualizing complex has no cohomology below degree `-m`. Nothing in it is special to dimension
  one, and at `m = dim(X)` it is the case of [Stacks, Tag 0AWP] over a field; see
  `StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingModuleRepresentability`.
* `Stacks.Duality.clauseFiveAddEquiv`: **clause (5) of [Stacks, Tag 0BS2]**, the preceding at
  `m = 1` with the degree bound supplied by
  `Stacks.Duality.isGE_dualizingComplexOverField`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.firstCohomologyDuality_dualizingSheafOverField`:
  clause (5) packaged as
  `AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyDuality` at the canonical
  dualizing sheaf, which is what discharges that hypothesis for the consumers of this chapter.

## Main results

* `Stacks.Duality.isQuasicoherent_dualizingSheafOverField`: `ω_X` is quasi-coherent.
* `Stacks.Duality.dualityAddEquiv_naturality`: the degree `-m` identification is natural in the
  module, stated in the hypercohomology spelling `H^m(X, ℱ[0])` of its target.
* `Stacks.Duality.clauseFiveAddEquiv_naturality`: clause (5) is natural in the module.
* `Stacks.Duality.clauseFiveNaturalitySquare`: the naturality square of the three identifications
  the proof composes, before the two ends are read as a morphism of `k`-modules.

## The argument

`ω_X^•` lies in `D^{≥ -1}` (`Stacks.Duality.isGE_dualizingComplexOverField`), so its truncation
`τ^{≤ -1}(ω_X^•)` is `ω_X` placed in degree `-1` (`Stacks.Duality.truncLEIsoSingleDualizingSheaf`,
read with the shift on the left as `Stacks.Duality.singleShiftOneIsoTruncLE`). For a module `ℱ`
the object `ℱ[0]⟦1⟧` lies in `D^{≤ -1}`, so:

1. `Hom_{𝒪_X}(ℱ, ω_X) = Hom_{D(𝒪_X)}(ℱ[0]⟦1⟧, ω_X[0]⟦1⟧)`, because `DerivedCategory.singleFunctor`
   is fully faithful and the shift is an equivalence;
2. `Hom_{D(𝒪_X)}(ℱ[0]⟦1⟧, ω_X[0]⟦1⟧) = Hom_{D(𝒪_X)}(ℱ[0]⟦1⟧, ω_X^•)`, by the identification of
   `ω_X[0]⟦1⟧` with `τ^{≤ -1}(ω_X^•)` and `truncLEHomAddEquiv` — this is the step where the
   source is one degree lower than in `Stacks.Duality.eq_zero_of_comp_truncLEι_app_eq_zero`, so
   that composition with the truncation map is not merely injective but bijective;
3. `Hom_{D(𝒪_X)}(ℱ[0]⟦1⟧, ω_X^•) = Hom_k(H⁰(X, ℱ[0]⟦1⟧), k)` is clause (4) in degree zero at
   `ℱ[0]⟦1⟧`, and `H⁰(X, ℱ[0]⟦1⟧) = H¹(X, ℱ[0]) = H¹(X, ℱ)` by
   `Stacks.Duality.derivedCohomologyShiftIso` and
   `Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField`.

**No Cohen--Macaulay hypothesis enters.** Step 2 needs only that `ω_X^•` has no cohomology below
degree `-1`; the identification of `ω_X^•` *itself* with `ω_X[1]`, which is [Stacks, Tag 0BS3]
and asks in addition that `H⁰(ω_X^•)` vanish, is not used and is not available here.

**Clause (5) does not give `dim_k H¹(X, ω_X) = 1`.** At `ℱ = ω_X` it identifies the `k`-linear
dual of `H¹(X, ω_X)` with the ring `End(ω_X)`, and `End(ω_X) = k[t]/(t²)` with `H¹(X, ω_X)` its
dual is a model of clause (5) with its naturality in which that dimension is two; see the module
documentation of
`StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingRiemannRoch`. That dimension is
the separate hypothesis `hone` of the consumers.

## Implementation notes

The `k`-linearity of the comparison in step 3 is why
`Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField` is used rather than
`AlgebraicGeometry.derivedHomStructureSheafEquivCohomologyOverField`: the target of clause (5) is
a space of `k`-linear functionals, and only the former identification is an isomorphism in
`ModuleCat k`.

**The naturality is proved in term mode.** On a goal mentioning an object of
`AlgebraicGeometry.quasiCoherentDerivedCategory X` — here `ℱ[0]⟦1⟧` with its quasi-coherence —
a `rewrite` which unfolds a functor application leaves the goal ill-typed at the transparency
`rewrite` uses, because the topology carried by `(⊤ : X.Opens)` and the one carried by the site
of `X.ringCatSheaf` are definitionally but not reducibly equal. `congrArg` against explicitly
written motives is unaffected, and is what
`StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality` uses for the same reason.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CategoryTheory.Triangulated

universe u

namespace Stacks.Duality

/-! ### Morphisms into a truncation from below the truncation degree -/

/-- **Morphisms out of an object of `D^{≤ n}` do not see the truncation `τ^{≤ n}`**: composition
with `τ^{≤ n}X ⟶ X` is an isomorphism of abelian groups `Hom(A, τ^{≤ n}X) ≅ Hom(A, X)` as soon
as `A` is `≤ n`.

Injectivity is Mathlib's `CategoryTheory.Triangulated.TStructure.to_truncLE_obj_ext` and
surjectivity is `CategoryTheory.Triangulated.TStructure.liftTruncLE`. -/
def truncLEHomAddEquiv {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C) {A X : C}
    (n : ℤ) [t.IsLE A n] : (A ⟶ (t.truncLE n).obj X) ≃+ (A ⟶ X) where
  toFun g := g ≫ (t.truncLEι n).app X
  invFun h := t.liftTruncLE h n
  left_inv _ := t.to_truncLE_obj_ext (t.liftTruncLE_ι _ n)
  right_inv h := t.liftTruncLE_ι h n
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- `Stacks.Duality.truncLEHomAddEquiv` sends `g` to its composite with `τ^{≤ n}X ⟶ X`. -/
theorem truncLEHomAddEquiv_apply {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)
    {A X : C} (n : ℤ) [t.IsLE A n] (g : A ⟶ (t.truncLE n).obj X) :
    truncLEHomAddEquiv t (A := A) (X := X) n g = g ≫ (t.truncLEι n).app X := rfl

/-! ### The dualizing sheaf is quasi-coherent -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **The dualizing sheaf is quasi-coherent**, being a cohomology sheaf of an object of
`D_QCoh(𝒪_X)`. -/
theorem isQuasicoherent_dualizingSheafOverField :
    (dualizingSheafOverField f).IsQuasicoherent :=
  (dualizingComplexOverField f).property (-1)

/-! ### A cohomology sheaf of the dualizing complex, mapped to the complex -/

/-- **The canonical map `H^{-m}(ω_X^•)[0]⟦m⟧ ⟶ ω_X^•`**: the identification of
`H^{-m}(ω_X^•)[0]⟦m⟧` with `τ^{≤ -m}(ω_X^•)` followed by the canonical map of the truncation. It
needs the dualizing complex to have no cohomology below degree `-m`. -/
def singleShiftToDualizingComplex (m : ℤ)
    (hge : (dualizingComplexOverField f).obj.IsGE (-m)) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingModuleOverField f m))⟦m⟧ ⟶
      (dualizingComplexOverField f).obj :=
  (singleShiftIsoTruncLEHomology f m hge).hom ≫
    (DerivedCategory.TStructure.t.truncLEι (-m)).app (dualizingComplexOverField f).obj

/-- **The canonical map `ω_X[0]⟦1⟧ ⟶ ω_X^•`** on a proper curve: this is
`Stacks.Duality.singleShiftToDualizingComplex` at `m = 1`, where
`Stacks.Duality.isGE_dualizingComplexOverField` supplies the degree bound. -/
def singleShiftOneToDualizingComplex (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f))⟦(1 : ℤ)⟧ ⟶
      (dualizingComplexOverField f).obj :=
  singleShiftToDualizingComplex f 1 (isGE_dualizingComplexOverField f hdim)

/-! ### The chain of identifications -/

/-- **A module placed in degree `-m` is `≤ -m`.** -/
theorem isLE_singleShift (F : X.Modules) (m : ℤ) :
    DerivedCategory.TStructure.t.IsLE
      (((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦m⟧) (-m) :=
  DerivedCategory.TStructure.t.isLE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 m (-m) (by ring)

/-- **A module placed in degree `-1` is `≤ -1`.** -/
theorem isLE_singleShiftOne (F : X.Modules) :
    DerivedCategory.TStructure.t.IsLE
      (((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦(1 : ℤ)⟧) (-1) :=
  isLE_singleShift F 1

/-- **`Hom_{𝒪_X}(ℱ, 𝒢) = Hom_{D(𝒪_X)}(ℱ[0]⟦m⟧, 𝒢[0]⟦m⟧)`**: the functor placing a module in
degree `-m` is fully faithful, being the composite of the fully faithful
`DerivedCategory.singleFunctor` with an equivalence. -/
def stepSingleShift (F G : X.Modules) (m : ℤ) :
    (F ⟶ G) ≃+ ((((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦m⟧) ⟶
      (((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦m⟧)) :=
  fullyFaithfulHomAddEquiv
    ((Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor X.Modules 0)).comp
      (Functor.FullyFaithful.ofFullyFaithful
        (shiftFunctor (DerivedCategory X.Modules) m))) F G

/-- `Stacks.Duality.stepSingleShift` sends `φ` to the shift by `m` of `φ` placed in degree zero. -/
theorem stepSingleShift_apply (F G : X.Modules) (m : ℤ) (φ : F ⟶ G) :
    stepSingleShift F G m φ =
      (shiftFunctor (DerivedCategory X.Modules) m).map
        ((DerivedCategory.singleFunctor X.Modules 0).map φ) := rfl

/-- **`Hom_{𝒪_X}(ℱ, 𝒢) = Hom_{D(𝒪_X)}(ℱ[0]⟦1⟧, 𝒢[0]⟦1⟧)`**, the preceding at `m = 1`. -/
def clauseFiveStepSingle (F G : X.Modules) :
    (F ⟶ G) ≃+ ((((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦(1 : ℤ)⟧) ⟶
      (((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧)) :=
  stepSingleShift F G 1

/-- `Stacks.Duality.clauseFiveStepSingle` sends `φ` to the shift by one of `φ` placed in degree
zero. -/
theorem clauseFiveStepSingle_apply (F G : X.Modules) (φ : F ⟶ G) :
    clauseFiveStepSingle F G φ =
      (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor X.Modules 0).map φ) := rfl

/-- **`Hom_{D(𝒪_X)}(A, H^{-m}(ω_X^•)[0]⟦m⟧) = Hom_{D(𝒪_X)}(A, ω_X^•)`** for `A` in `D^{≤ -m}`:
composition with `Stacks.Duality.singleShiftToDualizingComplex`, which is the identification
`H^{-m}(ω_X^•)[0]⟦m⟧ ≅ τ^{≤ -m}(ω_X^•)` followed by the canonical map of the truncation. -/
def stepTrunc (m : ℤ) (hge : (dualizingComplexOverField f).obj.IsGE (-m))
    {A : DerivedCategory X.Modules} [DerivedCategory.TStructure.t.IsLE A (-m)] :
    (A ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj
        (dualizingModuleOverField f m))⟦m⟧)
      ≃+ (A ⟶ (dualizingComplexOverField f).obj) :=
  (homCongrAddEquiv (Iso.refl A) (singleShiftIsoTruncLEHomology f m hge)).trans
    (truncLEHomAddEquiv DerivedCategory.TStructure.t (-m))

/-- `Stacks.Duality.stepTrunc` is composition with
`Stacks.Duality.singleShiftToDualizingComplex`. -/
theorem stepTrunc_apply (m : ℤ) (hge : (dualizingComplexOverField f).obj.IsGE (-m))
    {A : DerivedCategory X.Modules} [DerivedCategory.TStructure.t.IsLE A (-m)]
    (h : A ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj
      (dualizingModuleOverField f m))⟦m⟧) :
    stepTrunc f m hge h = h ≫ singleShiftToDualizingComplex f m hge := by
  simp [stepTrunc, truncLEHomAddEquiv, homCongrAddEquiv_apply, singleShiftToDualizingComplex]

/-- **`Hom_{D(𝒪_X)}(A, ω_X[0]⟦1⟧) = Hom_{D(𝒪_X)}(A, ω_X^•)`** for `A` in `D^{≤ -1}`, the
preceding at `m = 1`. -/
def clauseFiveStepTrunc (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    {A : DerivedCategory X.Modules} [DerivedCategory.TStructure.t.IsLE A (-1)] :
    (A ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingSheafOverField f))⟦(1 : ℤ)⟧)
      ≃+ (A ⟶ (dualizingComplexOverField f).obj) :=
  stepTrunc f 1 (isGE_dualizingComplexOverField f hdim)

/-- `Stacks.Duality.clauseFiveStepTrunc` is composition with
`Stacks.Duality.singleShiftOneToDualizingComplex`. -/
theorem clauseFiveStepTrunc_apply (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    {A : DerivedCategory X.Modules} [DerivedCategory.TStructure.t.IsLE A (-1)]
    (h : A ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj
      (dualizingSheafOverField f))⟦(1 : ℤ)⟧) :
    clauseFiveStepTrunc f hdim h = h ≫ singleShiftOneToDualizingComplex f hdim :=
  stepTrunc_apply f 1 (isGE_dualizingComplexOverField f hdim) h

/-- **The dualizing module in degree `-m` represents `ℱ ↦ Hom_k(H^m(X, ℱ[0]), k)`** on the
quasi-coherent modules, as soon as the dualizing complex has no cohomology below degree `-m`:

  `Hom_{𝒪_X}(ℱ, H^{-m}(ω_X^•)) = Hom_k(H^m(X, ℱ[0]), k)`.

The three steps are `Stacks.Duality.stepSingleShift`, `Stacks.Duality.stepTrunc` and clause (4)
of [Stacks, Tag 0BS2] in degree zero at `ℱ[0]⟦m⟧`, followed by the shift comparison
`H^0(X, ℱ[0]⟦m⟧) = H^m(X, ℱ[0])`. -/
def dualityAddEquiv (m : ℤ) (hge : (dualizingComplexOverField f).obj.IsGE (-m))
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (F ⟶ dualizingModuleOverField f m) ≃+
      (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj F) m ⟶
        ModuleCat.of k k) :=
  letI := isLE_singleShift F m
  (stepSingleShift F (dualizingModuleOverField f m) m).trans <|
    (stepTrunc f m hge).trans <|
    (dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m)).trans <|
    precompAddEquiv (derivedCohomologyShiftIso f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m)

/-- An explicit formula for `Stacks.Duality.dualityAddEquiv`: the image of `φ` is clause (4)
applied to `φ[0]⟦m⟧` composed with `Stacks.Duality.singleShiftToDualizingComplex`, precomposed
with the inverse of the shift comparison `Stacks.Duality.derivedCohomologyShiftIso`. -/
theorem dualityAddEquiv_apply (m : ℤ) (hge : (dualizingComplexOverField f).obj.IsGE (-m))
    (F : X.Modules) (hF : F.IsQuasicoherent) (φ : F ⟶ dualizingModuleOverField f m) :
    dualityAddEquiv f m hge F hF φ =
      (derivedCohomologyShiftIso f
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).inv ≫
        dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m)
          ((shiftFunctor (DerivedCategory X.Modules) m).map
              ((DerivedCategory.singleFunctor X.Modules 0).map φ) ≫
            singleShiftToDualizingComplex f m hge) :=
  let := isLE_singleShift F m
  congrArg (fun z => (derivedCohomologyShiftIso f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).inv ≫
      dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m) z)
    (stepTrunc_apply f m hge ((shiftFunctor (DerivedCategory X.Modules) m).map
      ((DerivedCategory.singleFunctor X.Modules 0).map φ)))

/-- The shift by `m` of a module map placed in degree zero is compatible with composition. -/
private theorem shift_map_single_map_comp_comp {F G H : X.Modules} (m : ℤ) (u : F ⟶ G)
    (φ : G ⟶ H) {Y : DerivedCategory X.Modules}
    (ψ : ((DerivedCategory.singleFunctor X.Modules 0).obj H)⟦m⟧ ⟶ Y) :
    (shiftFunctor (DerivedCategory X.Modules) m).map
        ((DerivedCategory.singleFunctor X.Modules 0).map (u ≫ φ)) ≫ ψ =
      (shiftFunctor (DerivedCategory X.Modules) m).map
          ((DerivedCategory.singleFunctor X.Modules 0).map u) ≫
        (shiftFunctor (DerivedCategory X.Modules) m).map
          ((DerivedCategory.singleFunctor X.Modules 0).map φ) ≫ ψ := by
  simp

/-- Clause (4) in degree zero at `ℱ[0]⟦m⟧`, read through `H⁰(X, -⟦m⟧) = H^m(X, -)`, is natural
in the module. -/
private theorem derivedCohomologyShiftIso_inv_comp_dualityAddEquivZero_naturality (m : ℤ)
    (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
    (ψ : ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦m⟧ ⟶
      (dualizingComplexOverField f).obj) :
    (derivedCohomologyShiftIso f ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).inv ≫
        dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m)
          ((shiftFunctor (DerivedCategory X.Modules) m).map
            ((DerivedCategory.singleFunctor X.Modules 0).map u) ≫ ψ) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) m).map
          ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map u)) ≫
        (derivedCohomologyShiftIso f ((DerivedCategory.singleFunctor X.Modules 0).obj G) m).inv ≫
          dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent G hG 0) m) ψ :=
  Eq.trans
    (congrArg (fun z => (derivedCohomologyShiftIso f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).inv ≫ z)
      (dualityAddEquivZero_naturality f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m)
        (shiftQuasiCoherent (singleQuasiCoherent G hG 0) m)
        ((shiftFunctor (DerivedCategory X.Modules) m).map
          ((DerivedCategory.singleFunctor X.Modules 0).map u)) ψ)) <|
  Eq.trans (Category.assoc _ _ _).symm <|
  Eq.trans
    (congrArg (fun z => z ≫ dualityAddEquivZero f
        (shiftQuasiCoherent (singleQuasiCoherent G hG 0) m) ψ)
      ((derivedCohomologyShiftNatIso f m).inv.naturality
        ((DerivedCategory.singleFunctor X.Modules 0).map u)).symm)
    (Category.assoc _ _ _)

/-- **The identification of `Stacks.Duality.dualityAddEquiv` is natural in the module**:
precomposing a map to `H^{-m}(ω_X^•)` with `u` corresponds to precomposing the functional with
`H^m(X, u[0])`. -/
theorem dualityAddEquiv_naturality (m : ℤ)
    (hge : (dualizingComplexOverField f).obj.IsGE (-m)) (F G : X.Modules)
    (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
    (φ : G ⟶ dualizingModuleOverField f m) :
    dualityAddEquiv f m hge F hF (u ≫ φ) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) m).map
          ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map u)) ≫
        dualityAddEquiv f m hge G hG φ := by
  let := isLE_singleShift F m
  let := isLE_singleShift G m
  refine Eq.trans (dualityAddEquiv_apply f m hge F hF (u ≫ φ)) ?_
  refine Eq.trans (congrArg (fun z => (derivedCohomologyShiftIso f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).inv ≫
      dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) m) z)
    (shift_map_single_map_comp_comp m u φ (singleShiftToDualizingComplex f m hge))) ?_
  refine Eq.trans (derivedCohomologyShiftIso_inv_comp_dualityAddEquivZero_naturality f m F G hF hG
    u _) ?_
  exact congrArg (fun z => (DerivedCategory.homologyFunctor (ModuleCat.{u} k) m).map
      ((derivedGlobalSectionsOver f).map
        ((DerivedCategory.singleFunctor X.Modules 0).map u)) ≫ z)
    (dualityAddEquiv_apply f m hge G hG φ).symm

/-- **Clause (5) of [Stacks, Tag 0BS2] at the dualizing sheaf of a proper curve**: for a
quasi-coherent `ℱ` on a proper `X` of dimension at most one over `k`,

  `Hom_{𝒪_X}(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)`.

This is `Stacks.Duality.dualityAddEquiv` at `m = 1`, followed by the comparison
`H¹(X, ℱ) = H¹(X, ℱ[0])` of `Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField`. -/
@[stacks 0BS2 "clause (5)"]
def clauseFiveAddEquiv (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    (F ⟶ dualizingSheafOverField f) ≃+ (cohomologyOverField k f F 1 →ₗ[k] k) :=
  (dualityAddEquiv f 1 (isGE_dualizingComplexOverField f hdim) F hF).trans <|
    (precompAddEquiv
      (cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).symm).trans
    ModuleCat.homAddEquiv

/-- An explicit formula for `Stacks.Duality.clauseFiveAddEquiv`: the image of `φ` is clause (4)
applied to `φ[0]⟦1⟧` composed with `Stacks.Duality.singleShiftOneToDualizingComplex`, precomposed
with the comparisons `H¹(X, ℱ) = H¹(X, ℱ[0])` and `H¹(X, ℱ[0]) = H⁰(X, ℱ[0]⟦1⟧)`. -/
theorem clauseFiveAddEquiv_apply (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) (φ : F ⟶ dualizingSheafOverField f) :
    clauseFiveAddEquiv f hdim F hF φ =
      ModuleCat.homAddEquiv
        ((cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).hom ≫
          (derivedCohomologyShiftIso f
              ((DerivedCategory.singleFunctor X.Modules 0).obj F) 1).inv ≫
            dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) 1)
              ((shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
                  ((DerivedCategory.singleFunctor X.Modules 0).map φ) ≫
                singleShiftOneToDualizingComplex f hdim)) :=
  congrArg (fun z => ModuleCat.homAddEquiv
      ((cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).hom ≫ z))
    (dualityAddEquiv_apply f 1 (isGE_dualizingComplexOverField f hdim) F hF φ)

/-- **The naturality square of clause (5), before the two ends are read as a morphism of
modules.** The identification of `Hom(ℱ, ω_X)` with the `k`-linear functionals on `H¹(X, ℱ)` is
the composite of clause (4) in degree zero at `ℱ[0]⟦1⟧` with the two comparisons `H⁰(X, -⟦1⟧) =
H¹(X, -)` and `H¹(X, ℱ) = H¹(X, ℱ[0])`, and each of the three is natural in `ℱ`. -/
theorem clauseFiveNaturalitySquare (_hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
    (ψ : ((DerivedCategory.singleFunctor X.Modules 0).obj G)⟦(1 : ℤ)⟧ ⟶
      (dualizingComplexOverField f).obj) :
    (cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).hom ≫
        (derivedCohomologyShiftIso f
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) 1).inv ≫
          dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) 1)
            ((shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
              ((DerivedCategory.singleFunctor X.Modules 0).map u) ≫ ψ) =
      cohomologyOverFieldMap k f u 1 ≫
        (cohomologyOverFieldIsoDerivedCohomologyOverField k f G 1).hom ≫
          (derivedCohomologyShiftIso f
              ((DerivedCategory.singleFunctor X.Modules 0).obj G) 1).inv ≫
            dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent G hG 0) 1) ψ :=
  Eq.trans
      (congrArg (fun z => (cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).hom ≫ z)
        (derivedCohomologyShiftIso_inv_comp_dualityAddEquivZero_naturality f 1 F G hF hG u ψ)) <|
    Eq.trans
      (Category.assoc (cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).map
          ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map u)))
        ((derivedCohomologyShiftIso f
            ((DerivedCategory.singleFunctor X.Modules 0).obj G) 1).inv ≫
          dualityAddEquivZero f
            (shiftQuasiCoherent (singleQuasiCoherent G hG 0) 1) ψ)).symm <|
    Eq.trans
      (congrArg (fun z => z ≫ (derivedCohomologyShiftIso f
            ((DerivedCategory.singleFunctor X.Modules 0).obj G) 1).inv ≫
          dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent G hG 0) 1) ψ)
        (cohomologyOverFieldIsoDerivedCohomologyOverField_cohomologyOverFieldMap
          k f 1 u).symm)
      (Category.assoc (cohomologyOverFieldMap k f u 1)
        (cohomologyOverFieldIsoDerivedCohomologyOverField k f G 1).hom
        ((derivedCohomologyShiftIso f
            ((DerivedCategory.singleFunctor X.Modules 0).obj G) 1).inv ≫
          dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent G hG 0) 1) ψ))

/-- **Clause (5) of [Stacks, Tag 0BS2] is natural in the module**: precomposing a map to `ω_X`
with `u` corresponds to precomposing the functional with `H¹(X, u)`. -/
@[stacks 0BS2 "clause (5): naturality"]
theorem clauseFiveAddEquiv_naturality (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
    (φ : G ⟶ dualizingSheafOverField f) :
    clauseFiveAddEquiv f hdim F hF (u ≫ φ) =
      (clauseFiveAddEquiv f hdim G hG φ).comp (cohomologyOverFieldMap k f u 1).hom := by
  refine Eq.trans (clauseFiveAddEquiv_apply f hdim F hF (u ≫ φ)) ?_
  refine Eq.trans (congrArg (fun z => ModuleCat.homAddEquiv
      ((cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).hom ≫
        (derivedCohomologyShiftIso f
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) 1).inv ≫
        dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) 1) z))
    (shift_map_single_map_comp_comp 1 u φ (singleShiftOneToDualizingComplex f hdim))) ?_
  refine Eq.trans (congrArg (fun z => ModuleCat.homAddEquiv z)
    (clauseFiveNaturalitySquare f hdim F G hF hG u
      ((shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor X.Modules 0).map φ) ≫
        singleShiftOneToDualizingComplex f hdim))) ?_
  rw [clauseFiveAddEquiv_apply]
  rfl

end Stacks.Duality

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

/-- **Clause (5) of [Stacks, Tag 0BS2] holds for the canonical dualizing sheaf
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))`**: for every quasi-coherent `ℱ` on `X` the group `Hom(ℱ, ω_X)`
is the `k`-linear dual of `H¹(X, ℱ)`, naturally in `ℱ`. This discharges the hypothesis
`AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyDuality` at that sheaf.

It is `Stacks.Duality.clauseFiveAddEquiv` together with its naturality
`Stacks.Duality.clauseFiveAddEquiv_naturality`, both derived from clause (4) in degree zero.

Clause (5) of [Stacks, Tag 0BS2] is registered on `Stacks.Duality.clauseFiveAddEquiv` and
`Stacks.Duality.clauseFiveAddEquiv_naturality`, at the source's hypotheses (proper, dimension at
most one); the situation here adds `H⁰(X, 𝒪_X) = k` and dimension exactly one.
-/
public def firstCohomologyDuality_dualizingSheafOverField
    (S : CohenMacaulayCurveSituation.{u}) :
    S.FirstCohomologyDuality (Stacks.Duality.dualizingSheafOverField S.f) where
  dual F hF := Stacks.Duality.clauseFiveAddEquiv S.f (le_of_eq S.dimension_one) F hF
  dual_comp F G hF hG u φ :=
    Stacks.Duality.clauseFiveAddEquiv_naturality S.f (le_of_eq S.dimension_one) F G hF hG u φ

end AlgebraicGeometry.CohenMacaulayCurveSituation

end
