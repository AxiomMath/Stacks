module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# The relative Leray spectral sequence as the spectral sequence of a spectral object

For a morphism of ringed spaces `g : Y ⟶ Z` the composite functor
```
D⁺(Mod(𝒪_Y)) ⥤ SpectralObject (D⁺(Mod(𝒪_Y))) EInt ⥤ SpectralObject (D⁺(Mod(𝒪_Z))) EInt
            ⥤ Abelian.SpectralObject (Mod(𝒪_Z)) EInt
```
sends a bounded below complex `M` to the spectral object formed by all truncations of `M`, pushed
forward by `R g_*` and read through `H ⁎`. Applying this to `M = R f_* K` gives the relative Leray
spectral sequence of [Stacks, Tag 01F6], with
```
E₂^{p,q} = H^{p+q}(R g_*(τ_{[q, q+1)} R f_* K))
```
which is `R ᵖ g_*(R^q f_* K)` once the truncation is identified with `H^q(R f_* K)[-q]`.

## Main definitions

* `Stacks.RelativeLeray.spectralObjectFunctor`: the functor
  `D⁺(Mod(𝒪_Y)) ⥤ Abelian.SpectralObject (Mod(𝒪_Z)) EInt` described above.
* `Stacks.RelativeLeray.spectralSequence`: the relative Leray spectral sequence of a bounded
  below complex of `𝒪_X`-modules, as an `E₂CohomologicalSpectralSequence (Mod(𝒪_Z))`.

## Main results

* `Stacks.RelativeLeray.spectralSequenceE₂IsoH`: for any spectral object indexed by `EInt` in any
  abelian category, the object in position `(p, q)` on the second page of its `E₂`-cohomological
  spectral sequence is `H^{p+q}` of the arrow `q ⟶ q + 1`.
* `Stacks.RelativeLeray.spectralObjectFunctor_obj_H_obj`: the value of `H ⁿ` of the spectral
  object at an arrow `a ⟶ b` is `H ⁿ(R g_*(τ_{[a,b)} M))`.
* `Stacks.RelativeLeray.pageTwoIsoTruncation`: the second page of
  `spectralSequence f g K` in position `(p, q)` is `H^{p+q}(R g_*(τ_{[q,q+1)} R f_* K))`.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.ComposableArrows Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeLeray

/-! ### The second page of the spectral sequence of a spectral object -/

section General

variable {C : Type*} [Category C] [Abelian C]

/-- **The second page of the spectral sequence of a spectral object.** The object in position
`(p, q)` on the second page of the `E₂`-cohomological spectral sequence of a spectral object
indexed by `EInt` is `H^{p+q}` of the arrow `q ⟶ q + 1`. -/
noncomputable def spectralSequenceE₂IsoH (Y : SpectralObject C EInt) (p q : ℤ) :
    ((Y.spectralSequence SpectralObject.coreE₂Cohomological).page 2).X (p, q) ≅
      (Y.H (p + q)).obj (mk₁ (homOfLE (show (q : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))) :=
  Y.spectralSequencePageXIso SpectralObject.coreE₂Cohomological 2 le_rfl (p, q)
      (q : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 1 : ℤ) : EInt)
      (by simp) rfl rfl (by congr 1; omega) (p + q - 1) (p + q) (p + q + 1) rfl ≪≫
    Y.EIsoH _ _ _ _

end General

/-! ### The relative Leray spectral object -/

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **The relative Leray spectral object.** For a morphism of ringed spaces `g : Y ⟶ Z`, the
functor sending a bounded below complex `M` of `𝒪_Y`-modules to the spectral object of
`Mod(𝒪_Z)` whose `H ⁿ` at an arrow `a ⟶ b` of `EInt` is `H ⁿ(R g_*(τ_{[a,b)} M))`. It is the
spectral object of the standard t-structure, pushed forward by `R g_*` and read through
cohomology. -/
noncomputable def spectralObjectFunctor {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z) :
    DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      SpectralObject (SheafOfModules.{u} (structureSheafRing Z)) EInt :=
  DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
    Functor.mapTriangulatedSpectralObject
      (modulePushforward g).rightDerivedFunctorPlus EInt ⋙
    Triangulated.SpectralObject.mapHomologicalFunctorFunctor
      (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{u} (structureSheafRing Z)) 0) EInt

/-- The cohomology of the relative Leray spectral object at an arrow `a ⟶ b` of `EInt` is the
cohomology of the derived pushforward of the truncation `τ_{[a,b)} M`. -/
theorem spectralObjectFunctor_obj_H_obj {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z)
    (M : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing Y))) (n : ℤ)
    {a b : EInt} (hab : a ≤ b) :
    (((spectralObjectFunctor g).obj M).H n).obj (mk₁ (homOfLE hab)) =
      ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing Z)) 0).shift n).obj
        ((modulePushforward g).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj a).obj
            ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj b).obj M))) :=
  rfl

/-- **The relative Leray spectral sequence of a bounded below complex.** For composable
morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` and a bounded below complex `K` of
`𝒪_X`-modules, this is the `E₂`-cohomological spectral sequence of the spectral object
`spectralObjectFunctor g` at `R f_* K`. -/
noncomputable def spectralSequence {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    E₂CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Z)) :=
  ((spectralObjectFunctor g).obj
    ((modulePushforward f).rightDerivedFunctorPlus.obj K)).E₂SpectralSequence

/-- **The second page of the relative Leray spectral sequence.** In position `(p, q)` it is
`H^{p+q}(R g_*(τ_{[q,q+1)} R f_* K))`. -/
noncomputable def pageTwoIsoTruncation {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) (p q : ℤ) :
    ((spectralSequence f g K).page 2).X (p, q) ≅
      ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing Z)) 0).shift (p + q)).obj
        ((modulePushforward g).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj (q : EInt)).obj
            ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj
              ((modulePushforward f).rightDerivedFunctorPlus.obj K)))) :=
  spectralSequenceE₂IsoH _ p q

end Stacks.RelativeLeray

end
