module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyDerived
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.Homology.DerivedCategory.HomologyBiprodSingle

/-!
# Parts (2) and (3) of Stacks 0E1J from the splitting of the derived direct image

Let `f : X → S` be a family of curves (Stacks 0D4Z) with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every
point `s` of `S`. Parts (2) and (3) of Stacks 0E1J say that `R¹f_*𝒪_X` is a finite locally free
`𝒪_S`-module and that its formation commutes with arbitrary base change.

The source's proof reads both off a decomposition `Rf_*𝒪_X = 𝒪_S ⊕ P` in `D(𝒪_S)` with `P`
perfect of Tor amplitude in `[1, ∞)` (Derived Categories of Spaces, Lemma 0E6B, part (b)),
sharpened to `P = H¹(P)[-1]` with `H¹(P)` finite locally free by the vanishing
`H^i(P ⊗^𝐋 κ(s)) = H^i(X_s, 𝒪_{X_s}) = 0` for `i ≥ 2` (Cohomology, Proposition 02UZ, together
with cohomology and base change, Lemma 0CTM part (1)) and by More on Algebra, Lemma 0BCD.

This file carries out the step *after* that sharpening, and the étale case of part (3).

## Main definitions

* `AlgebraicGeometry.CurveFamily.DerivedPushforwardSplitsOffSingle`: the sharpened conclusion of
  Stacks 0E6B part (b) for a family of curves — `𝒪_S ⊕ M[-1] ≅ Rf_*𝒪_X` in `D(𝒪_S)`.

## Main results

* `AlgebraicGeometry.CurveFamily.firstDirectImageIsoOfDerivedPushforwardSplitsOffSingle`:
  a splitting `𝒪_S ⊕ M[-1] ≅ Rf_*𝒪_X` identifies `M` with `R¹f_*𝒪_X`.
* `AlgebraicGeometry.CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of_splitting`:
  **the last step of part (2) of Stacks 0E1J.** If the summand `M` is finite locally free then so
  is `R¹f_*𝒪_X`.
* `AlgebraicGeometry.CurveFamily.firstDirectImageIsoModulePullbackOfIsEtale`: **the étale case of
  part (3) of Stacks 0E1J**: for a morphism of families of curves whose morphism of bases is
  étale, `h^*(R¹f_*𝒪_X) ≅ R¹f'_*𝒪_{X'}`.
* `CurveFamily.isFiniteLocallyFreeOnSite_firstDirectImage_iff_of_isEtale_isSurjective`:
  **part (2) of Stacks 0E1J is étale local on the base**, in the covering-family spelling of
  Stacks 03DL part (2).
* `AlgebraicGeometry.CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of`: part (2) of
  Stacks 0E1J from one explicit input, `hsplit`.

## Implementation notes

The hypothesis `hsplit` of `hasFiniteLocallyFreeFirstHigherDirectImage_of` is the conjunction, as
the source's proof assembles it, of

* Derived Categories of Spaces, Lemma 0E6B part (b) — `Rf_*𝒪_X = 𝒪_S ⊕ P` étale locally on `S`
  with `P` perfect of Tor amplitude in `[1, ∞)`;
* Derived Categories of Spaces, Lemma 0CTM part (1) — `Rf_*𝒪_X` is perfect and its formation
  commutes with arbitrary base change;
* More on Algebra, Lemma 0BCD — a perfect object whose derived fibre is concentrated in degree
  `1` is, locally, a finite free module placed in degree `1`.

The input of the 0BCD step is that the derived fibres of `P` are concentrated in degree `1`, that
is `H^i(P ⊗^𝐋 κ(s)) = H^i(X_s, 𝒪_{X_s}) = 0` for `i ≥ 2`. The vanishing on the right is
`CurveFamily.isZero_rightDerived_globalSectionsFunctor_fiberProduct_fieldValuedPoint`; the
identification is Stacks 0CTM part (1), and Stacks 0E6B part (b) is what produces `P`.

`hsplit` is stated globally on `S` rather than étale locally. On the small étale site of an
algebraic space the class `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` is reached only
through `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_coversTop`, which asks for finite
*freeness* on a family covering the final object, while the étale-local results conclude the
covering-family class `Stacks.SheafOfModules.IsFiniteLocallyFreeOnSite`; in that class
`isFiniteLocallyFreeOnSite_firstDirectImage_iff_of_isEtale_isSurjective` shows part (2) to be
étale local.

The étale case of part (3) follows from the étale base change of higher direct images
(Stacks 03LX, `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso`, specialized to
families of curves by `AlgebraicGeometry.CurveFamily.firstDirectImageIsoOfIsEtale`) and the
comparison of the two readings of the pullback of modules along an étale morphism,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`. The general case is Stacks 0CTM
part (1) read on `H¹`.

**The direction of the isomorphism in `DerivedPushforwardSplitsOffSingle`** is from the
biproduct to `Rf_*𝒪_X`, not the other way round. It has to be: the derived direct image
`AlgebraicGeometry.Space.smallEtaleDerivedModulePushforward` carries its own derived-category
instance, and with it on the left of the `≅` the elaborator has not yet identified the two
categories when it reaches the biproduct and fails to find `HasBinaryBiproduct`.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-! ### The splitting of the derived direct image -/

/-- **`𝒪_S ⊕ M[-1] ≅ Rf_*𝒪_X` in `D(𝒪_S)`** for a family of curves `f : X → S` and an
`𝒪_S`-module `M`.

This is the conclusion of Stacks 0E6B part (b) for a family of curves, sharpened by the vanishing
of the cohomology of the fibres in degrees `≥ 2` and by More on Algebra, Lemma 0BCD: the summand
`P` there, perfect of Tor amplitude in `[1, ∞)`, becomes `M[-1]` for a finite locally free `M`. -/
def DerivedPushforwardSplitsOffSingle (X : CurveFamily B hZ)
    (M : Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2) :
    Prop :=
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  Nonempty ((DerivedCategory.singleFunctor
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
        0).obj (Space.structureSheafModule B integerBase hZ (schemeSpace X.base)) ⊞
      (DerivedCategory.singleFunctor
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
        1).obj M ≅
    (Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
      ((DerivedCategory.singleFunctor
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
        (Space.structureSheafModule B integerBase hZ X.total)))

/-- **A splitting `𝒪_S ⊕ M[-1] ≅ Rf_*𝒪_X` identifies `M` with `R¹f_*𝒪_X`.** Take first
cohomology: that of the biproduct is `M`, because `𝒪_S[0]` has none in degree `1`
(`DerivedCategory.homologyBiprodSingleIso`), and that of `Rf_*𝒪_X` is the first higher direct
image (`AlgebraicGeometry.CurveFamily.homologyDerivedPushforwardIsoFirstHigherDirectImage`). -/
def firstDirectImageIsoOfDerivedPushforwardSplitsOffSingle (X : CurveFamily B hZ)
    (M : Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
    (h : X.DerivedPushforwardSplitsOffSingle M) :
    M ≅ X.firstDirectImage B hZ :=
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  (DerivedCategory.homologyBiprodSingleIso
      (Space.structureSheafModule B integerBase hZ (schemeSpace X.base)) M
      (n := 1) (by norm_num)).symm ≪≫
    (DerivedCategory.homologyFunctor _ 1).mapIso (Classical.choice h) ≪≫
      X.homologyDerivedPushforwardIsoFirstHigherDirectImage

/-- **The last step of part (2) of Stacks 0E1J.** If the derived direct image of the structure
sheaf of a family of curves splits as `𝒪_S ⊕ M[-1]` with `M` a finite locally free `𝒪_S`-module,
then `R¹f_*𝒪_X` is finite locally free: it is isomorphic to `M`. -/
theorem hasFiniteLocallyFreeFirstHigherDirectImage_of_splitting (X : CurveFamily B hZ)
    (M : Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
    (hM : SheafOfModules.IsFiniteLocallyFree M)
    (h : X.DerivedPushforwardSplitsOffSingle M) :
    X.HasFiniteLocallyFreeFirstHigherDirectImage :=
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree M :=
    ⟨hM.exists_isFiniteLocallyFreeData⟩
  ⟨(Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso
    (X.firstDirectImageIsoOfDerivedPushforwardSplitsOffSingle M h)).1⟩

/-! ### The étale case of part (3) -/

/-- **The étale case of part (3) of Stacks 0E1J.** For a morphism of families of curves whose
morphism of bases `h : S' → S` is étale, the pullback `h^*(R¹f_*𝒪_X)` is `R¹f'_*𝒪_{X'}`.

The two readings of the pullback of modules along an étale morphism of algebraic spaces agree
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`), and along the étale reading
this is the étale base change of higher direct images, Stacks 03LX. -/
def firstDirectImageIsoModulePullbackOfIsEtale {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hφ : Space.IsEtale B integerBase hZ (schemeSpaceMap φ.baseMap).hom) :
    (Space.modulePullback B integerBase hZ (schemeSpaceMap φ.baseMap)).obj
        (Y.firstDirectImage B hZ) ≅
      X.firstDirectImage B hZ :=
  (Space.modulePullbackIsoEtaleModulePullback B integerBase hZ
      (schemeSpaceMap φ.baseMap) hφ).app (Y.firstDirectImage B hZ) ≪≫
    (firstDirectImageIsoOfIsEtale φ hφ).symm

/-! ### Part (2) is étale local on the base -/

/-- **Part (2) of Stacks 0E1J is étale local on the base**, in the covering-family spelling of
Stacks 03DL part (2). For a morphism of families of curves whose morphism of bases is étale and
surjective on points, `R¹f_*𝒪_X` is finite locally free exactly when `R¹f'_*𝒪_{X'}` is.

Finite local freeness is étale local on the base by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_etaleModulePullback_iff` (the clause of
Stacks 03DN that the proof of Stacks 03ZU uses), and the étale restriction of `R¹f_*𝒪_X` is
`R¹f'_*𝒪_{X'}` by Stacks 03LX. -/
theorem isFiniteLocallyFreeOnSite_firstDirectImage_iff_of_isEtale_isSurjective
    {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hφ : Space.IsEtale B integerBase hZ (schemeSpaceMap φ.baseMap).hom)
    (hsurj : Space.IsSurjective B integerBase hZ (schemeSpaceMap φ.baseMap).hom) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (Y.firstDirectImage B hZ) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite (X.firstDirectImage B hZ) :=
  (Space.isFiniteLocallyFreeOnSite_etaleModulePullback_iff B integerBase hZ
      (schemeSpaceMap φ.baseMap) hφ hsurj (Y.firstDirectImage B hZ)).trans
    ⟨fun h => SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
        (firstDirectImageIsoOfIsEtale φ hφ).symm h,
      fun h => SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
        (firstDirectImageIsoOfIsEtale φ hφ) h⟩

/-! ### Part (2) from its one remaining input -/

/-- **Part (2) of Stacks 0E1J from one explicit input.** For every family of curves `f : X → S`
with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for all `s ∈ S`, the module `R¹f_*𝒪_X` is finite locally free —
*given* `hsplit`, which produces for each such family a finite locally free `𝒪_S`-module `M` with
`Rf_*𝒪_X ≅ 𝒪_S ⊕ M[-1]` in `D(𝒪_S)`.

`hsplit` is the conjunction of Stacks 0E6B part (b), Stacks 0CTM part (1) and More on Algebra,
Lemma 0BCD, as the source's proof uses them; see the module documentation. -/
theorem hasFiniteLocallyFreeFirstHigherDirectImage_of
    (hsplit : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      ∃ M : Space.Modules.{u, u} B integerBase hZ
          (schemeSpace X.base).1 (schemeSpace X.base).2,
        SheafOfModules.IsFiniteLocallyFree M ∧ X.DerivedPushforwardSplitsOffSingle M)
    (X : CurveFamily B hZ) (hX : X.HasResidueFieldGlobalFunctions) :
    X.HasFiniteLocallyFreeFirstHigherDirectImage :=
  let ⟨M, hM, h⟩ := hsplit X hX
  X.hasFiniteLocallyFreeFirstHigherDirectImage_of_splitting M hM h

end CurveFamily

end AlgebraicGeometry

end
