module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraAffineSections
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# The vector bundle of a finite locally free module on an algebraic space

Let `W` be an algebraic space over a scheme `S` in a big fppf site `B` and `ℰ` a finite locally
free `𝒪_W`-module. Its vector bundle is the relative spectrum
`E = \underline{Spec}_W(Sym(ℰ)) ⟶ W`. Inside the site of `W` the relative spectrum exists for the
quasi-coherent algebras with fewer than the cutoff many sections over every étale chart
(`AlgebraicGeometry.Space.boundedRelativeSpec`), and `Sym(ℰ)` is one of them
(`AlgebraicGeometry.Space.sectionsBelowCutoff_symmetricAlgebraSheaf`), `ℰ` being quasi-coherent
of finite presentation (Stacks 03DL), so that `E` is an algebraic space of the same site as `W`.

## Main definitions

* `AlgebraicGeometry.Space.symmetricQuasicoherentAlgebra`: `Sym(ℰ)` as a quasi-coherent
  `𝒪_W`-algebra, for `ℰ` locally free.
* `AlgebraicGeometry.Space.vectorBundle`: the vector bundle `\underline{Spec}_W(Sym(ℰ))`, as an
  algebraic space affine over `W`, and `AlgebraicGeometry.Space.vectorBundleProjection` its
  projection to `W`.
* `AlgebraicGeometry.Space.pushforwardAlgebraVectorBundleIso`: the direct image of its structure
  sheaf is `Sym(ℰ)`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_vectorBundleProjection`: the projection is affine.

## Implementation notes

Finite local freeness is `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` (Stacks 01C6). It
gives quasi-coherence through `SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent` and finite
presentation through `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree` and
`SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- A trivialization of `ℰ` over a chart restricts along a morphism of charts. -/
def overFreeIsoOfHom {U V : SmallEtale B S hS W.1} (f : U ⟶ V) {I : Type u}
    (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) I) :
    F.over U ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over U) I :=
  ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS W) f).app F).symm ≪≫
    (SheafOfModules.overMap (structureRingSheaf B S hS W) f).mapIso e ≪≫
      (SheafOfModules.overMapFreeIso (structureRingSheaf B S hS W) f I).symm

/-- **`Sym(ℰ)` as a quasi-coherent `𝒪_W`-algebra**, for a locally free `𝒪_W`-module `ℰ`; its
quasi-coherence is `AlgebraicGeometry.Space.isQuasicoherent_symmetricAlgebraSheaf`. -/
def symmetricQuasicoherentAlgebra [F.IsLocallyFree] : QuasicoherentAlgebra B S hS W :=
  ⟨symmetricAlgebraSheaf B S hS W F, isQuasicoherent_symmetricAlgebraSheaf B S hS W F
    (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)⟩

variable [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]

/-! ### The vector bundle -/

/-- **The vector bundle `E = \underline{Spec}_W(Sym(ℰ))` of a finite locally free
`𝒪_W`-module**, as an algebraic space affine over `W` in the big fppf site of `W`: the bounded
relative spectrum of the quasi-coherent algebra `Sym(ℰ)`, which applies because `Sym(ℰ)` has
fewer than the cutoff many sections over every chart. -/
def vectorBundle : AffineOver B S hS W :=
  boundedRelativeSpec B S hS (symmetricQuasicoherentAlgebra B S hS W F)
    (sectionsBelowCutoff_symmetricAlgebraSheaf B S hS W F
      (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)
      (_root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree F hF)))

/-- The projection `p : E ⟶ W` of the vector bundle. -/
abbrev vectorBundleProjection : (vectorBundle B S hS W F).obj.left ⟶ W :=
  (vectorBundle B S hS W F).obj.hom

/-- **The direct image of the structure sheaf of the vector bundle is `Sym(ℰ)`.** -/
def pushforwardAlgebraVectorBundleIso :
    pushforwardAlgebra B S hS (vectorBundle B S hS W F).obj ≅ symmetricAlgebraSheaf B S hS W F :=
  pushforwardAlgebraBoundedRelativeSpecIso B S hS (symmetricQuasicoherentAlgebra B S hS W F)
    (sectionsBelowCutoff_symmetricAlgebraSheaf B S hS W F
      (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)
      (_root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree F hF)))

/-- The projection of the vector bundle is an affine morphism. -/
theorem isAffineHom_vectorBundleProjection :
    IsAffineHom B S hS (vectorBundleProjection B S hS W F).hom :=
  (vectorBundle B S hS W F).property

end AlgebraicGeometry.Space

end
