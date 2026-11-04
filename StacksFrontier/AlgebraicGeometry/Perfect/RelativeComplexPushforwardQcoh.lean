module

public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of a relative complex with quasi-coherent terms

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `K` be a
cochain complex of `f^{-1}𝒪_S`-modules, bounded below, each of whose terms is the restriction of
scalars of a quasi-coherent `𝒪_X`-module; the differentials are only `f^{-1}𝒪_S`-linear, not
`𝒪_X`-linear. Then `Rf_*K`, formed along the morphism of ringed spaces
`(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)`, lies in `D_QCoh(𝒪_S)`: all of its cohomology sheaves are
quasi-coherent.

The argument is the one of the source. A Cartan--Eilenberg resolution of the bounded below
complex produces a spectral sequence whose first page is `R^q f_*K^p`; the quasi-coherent
modules form a weak Serre subcategory, so it suffices that each `R^q f_*K^p` be quasi-coherent,
and that is the quasi-coherence of the higher direct images of a quasi-coherent module along a
quasi-compact quasi-separated morphism.

## Main definitions

* `Stacks.RelativeComplexPushforward.relativeDerivedPushforward`: **`Rf_*K`** for `K` a bounded
  below complex of `f^{-1}𝒪_S`-modules, an object of `D⁺(𝒪_S)`.

## Main results

* `Stacks.RelativeComplexPushforward.isQuasicoherent_homology_relativeDerivedPushforward` and
  `Stacks.RelativeComplexPushforward.derivedCategoryB_relativeDerivedPushforward`: **`Rf_*K` is
  in `D_QCoh(𝒪_S)`**, in its degreewise and its membership form.

## Implementation notes

The quasi-coherent `𝒪_X`-module structure on the terms enters as a family `M : ℤ → X.Modules`
of quasi-coherent modules together with isomorphisms `K.X i ≅ (M i)` of `f^{-1}𝒪_S`-modules,
the right-hand side being the restriction of scalars along the structural `f^{-1}𝒪_S ⟶ 𝒪_X`.
That is the compatibility the source asks of the two module structures on a term, and it is all
the proof uses: flatness of the terms over `f^{-1}𝒪_S` is not needed for quasi-coherence of the
direct image, so it is not assumed here.

The complex is assumed bounded below, with an explicit bound `n`, rather than merely locally
bounded. The bound is what the derived functor used here consumes: `Rf_*` is the right derived
functor on `D⁺`, the Cartan--Eilenberg resolution is produced from the bound, and the bound is
what makes the total complex of the resolution exist, only finitely many of its terms being
nonzero on each antidiagonal.

## References

* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 015I](https://stacks.math.columbia.edu/tag/015I)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.DeRhamDirectImage

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.RelativeComplexPushforward

/- Sheaves of modules on a ringed space form a (Grothendieck) abelian category; instance search
does not cross the abbreviation, so the instances restated at these binders in
`StacksFrontier/AlgebraicGeometry/DeRham/DerivedDirectImage.lean` are put back in scope. -/
attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules
  Stacks.DeRhamDirectImage.isGrothendieckAbelian_modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`Rf_*K`**, the derived direct image of a complex `K` of `f^{-1}𝒪_S`-modules which is
strictly bounded below by `n`: the right derived functor on `D⁺` of the direct image along the
ringed-space morphism `(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)`, applied to `K`. -/
def relativeDerivedPushforward (n : ℤ) (K : CochainComplex (Modules (inverseImageBase f)) ℤ)
    [CochainComplex.IsStrictlyGE K n] : DerivedCategory.Plus (Modules S.toRingedSpace) :=
  (relativePushforward f).rightDerivedFunctorPlus.obj
    (DerivedCategory.Plus.Q.obj ⟨K, n, inferInstance⟩)

/-- **Stacks Project, Tag 0FML, conclusion (2).** Let `f : X ⟶ S` be quasi-compact and
quasi-separated and let `K` be a complex of `f^{-1}𝒪_S`-modules, strictly bounded below, whose
term in degree `i` is the restriction of scalars of a quasi-coherent `𝒪_X`-module `M i`. Then
every cohomology sheaf of `Rf_*K` is quasi-coherent. -/
@[stacks 0FML "conclusion (2), that Ra_* of the complex lies in D_QCoh, degreewise, for a \
complex bounded below with an explicit bound rather than merely locally bounded"]
theorem isQuasicoherent_homology_relativeDerivedPushforward [QuasiCompact f] [QuasiSeparated f]
    (n : ℤ) (K : CochainComplex (Modules (inverseImageBase f)) ℤ)
    [CochainComplex.IsStrictlyGE K n] (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hK : ∀ i, K.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor S.Modules i).obj
      (relativeDerivedPushforward f n K)).IsQuasicoherent := by
  let F := relativePushforward f
  obtain ⟨I, hI⟩ := CochainComplex.exists_cartanEilenbergResolution K n
  have := hI
  let L := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I.bicomplex
  have hp (p : ℤ) (hp : p < n) : IsZero (L.X p) :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex n p hp)
  have hq (p q : ℤ) (hq : q < 0) : IsZero ((L.X p).X q) :=
    F.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q hq)
  have hfinite := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded L n hq hp
  have : HomologicalComplex₂.HasTotal L (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ hfinite
  have hSS := I.exists_homologyIso_rightDerivedPlus F ⟨n, inferInstance⟩
  let P : ObjectProperty (Modules S.toRingedSpace) :=
    _root_.SheafOfModules.isQuasicoherent S.ringCatSheaf
  have : P.IsWeakSerreClass :=
    Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass S
  have hcol (p q : ℤ) : P ((L.X p).homology q) := by
    obtain ⟨e, -⟩ := hSS.1 q
    refine P.prop_of_iso (e p).symm ?_
    refine P.prop_of_iso ((F.rightDerivedPlus q).mapIso (hK p)).symm ?_
    exact isQuasicoherent_relativePushforward_higher f (M p) (hM p) q
  obtain ⟨e⟩ := hSS.2.2 i
  exact P.prop_of_iso e (weakSerre_homology_total L hfinite P hcol i)

/-- **Stacks Project, Tag 0FML, conclusion (2)**, in the membership form: the object property on
`D(𝒪_S)` cutting out the complexes with quasi-coherent cohomology holds of `Rf_*K`. The complex
being bounded below, `Rf_*K` is read in `D⁺(𝒪_S)` and compared with `D(𝒪_S)` along the
inclusion, under which the cohomology functors agree. -/
@[stacks 0FML "conclusion (2), that Ra_* of the complex lies in D_QCoh, as a membership, for a \
complex bounded below with an explicit bound rather than merely locally bounded"]
theorem derivedCategoryB_relativeDerivedPushforward [QuasiCompact f] [QuasiSeparated f]
    (n : ℤ) (K : CochainComplex (Modules (inverseImageBase f)) ℤ)
    [CochainComplex.IsStrictlyGE K n] (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hK : ∀ i, K.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf)
      (DerivedCategory.Plus.ι.obj (relativeDerivedPushforward f n K)) :=
  fun i => isQuasicoherent_homology_relativeDerivedPushforward f n K M hM hK i

end Stacks.RelativeComplexPushforward

end
