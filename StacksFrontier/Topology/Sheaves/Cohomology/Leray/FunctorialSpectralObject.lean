module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.ModuleSheafSpectralSequence

/-!
# The functorial Leray spectral object

[Stacks, Tag 01F2] asks for the Leray spectral sequence as a **functor**
`D⁺(Mod(𝒪_X)) ⥤ E₂CohomologicalSpectralSequence (Γ(Y, 𝒪_Y)-Mod)` whose second page is
identified with `H^p(Y, R^q f_* K)` *naturally* in `K`.  The construction of
[Stacks, Tag 015N] cannot supply this: it chooses a Cartan-Eilenberg resolution
([Stacks, Tag 015I]) of a representative of `Rf_* K`, one complex at a time, and the
development has no functorial Cartan-Eilenberg resolution and no comparison theorem for
Cartan-Eilenberg resolutions out of which to build one (see the implementation notes of
`Stacks.Cohomology.LerayModules`).

This file takes the other classical route to the same spectral sequence, which is functorial
from the start and uses no resolutions at all: the **spectral object of the canonical
(Postnikov) truncation tower**.  For `K` in `D⁺(Mod(𝒪_X))` put `M = Rf_* K` and let
`t` be the canonical t-structure of `D⁺(Mod(𝒪_Y))`.  Mathlib's
`CategoryTheory.Triangulated.TStructure.spectralObjectFunctor` assembles all the truncations
`τ^{≥a} τ^{<b} M` into a spectral object in `D⁺(Mod(𝒪_Y))`, *functorially in `M`*; pushing it
along the triangulated functor `RΓ(Y, -)` and then applying the homological functor `H^0`
gives a spectral object of `Γ(Y, 𝒪_Y)`-modules, again functorially.  Its `E₂`-cohomological
spectral sequence has
```
E_2^{p,q} ≅ H^{p+q}(RΓ(Y, -) (τ^{≥q} τ^{<q+1} (Rf_* K))),
```
and `τ^{≥q} τ^{<q+1} M` is `H^q(M)` placed in degree `q`, so the right-hand side is
`H^p(Y, R^q f_* K)`.

## Main definitions

* `cohomologySpectralObjectFunctor`: for a triangulated functor `Φ : D⁺(ℬ) ⥤ D⁺(𝒞)`, the
  functor `D⁺(ℬ) ⥤ Abelian.SpectralObject 𝒞 EInt` given by the canonical truncation tower.
* `lerayCohomologySpectralObject`: the same for `Φ = RΓ(Y, -)` precomposed with `Rf_*`, i.e.
  the Leray spectral object of a morphism of ringed spaces.

## Main results

* `cohomologySpectralObjectFunctor_H_obj`: the value of the spectral object on an adjacent
  pair `q ≤ q + 1` is `H^n(Φ(τ^{≥q} τ^{<q+1} K))`, on the nose.
* `pageTwoXIso` and `lerayPageTwoXIso`: the second page of the `E₂`-cohomological spectral
  sequence of that spectral object at `(p, q)` is `H^{p+q}(Φ(τ^{≥q} τ^{<q+1} K))`.

## Implementation notes

**Nothing here carries the tag `01F2`**, and this file does not prove it.  What it supplies is
the functorial Leray spectral object and the `E₂` identification at each object.  The further
ingredients are these.

1. A functor `Abelian.SpectralObject 𝒞 EInt ⥤ SpectralSequence 𝒞 c r₀` is
   `CategoryTheory.Abelian.SpectralObject.spectralSequenceFunctor`, together with the natural
   form of the starting-page identification,
   `CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXNatIso`.  (Mathlib has only
   `CategoryTheory.Abelian.SpectralObject.spectralSequence`, on objects.)  So a Leray spectral
   sequence functor is the composite of `lerayCohomologySpectralObject` with that functor.

2. The identification `τ^{≥q} τ^{<q+1} ≅ H^q(-)` placed in degree `q`, as a natural isomorphism
   of functors `D⁺(ℬ) ⥤ D⁺(ℬ)`, is
   `DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor`, with the unbounded
   version `DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor` and the cohomology
   form `truncGELTCompHomologyFunctorIso`.

3. `H^{p}(RG((single 0).obj A)) = (G.rightDerivedPlus p).obj A` holds by definition of
   `CategoryTheory.Functor.rightDerivedPlus`, and for `Φ` commuting with the shift,
   `Plus.singleFunctor ℬ q ⋙ Φ ⋙ Plus.homologyFunctor 𝒞 (p + q)` is identified with
   `Plus.singleFunctor ℬ 0 ⋙ Φ ⋙ Plus.homologyFunctor 𝒞 p` by
   `DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`; for `Φ = RG` the two give
   `Plus.singleFunctor ℬ q ⋙ RG ⋙ Plus.homologyFunctor 𝒞 (p + q) ≅ G.rightDerivedPlus p`.  The
   unbounded shifted identification `H^{m}(Rw(X[a])) ≅ R^n w(X)` for `m - a = n`, against
   Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, is
   `Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived`.

4. For the **abutment** the comparison `R(G ∘ F) ≅ RF ⋙ RG` on `D⁺` is available as data, with
   its naturality square named: `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`, for `F`
   additive and preserving injective objects and `G` additive.

Of the hypotheses, `Φ.CommShift ℤ` and `Φ.IsTriangulated` are what the push-forward of a
spectral object along `Φ` needs; for `Φ = RG` they are
`Functor.IsRightDerivedFunctor.commShift` and
`CategoryTheory.Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus`,
restated below as local instances because the copies in
`Stacks.Cohomology.CechDelta` are module-private.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Triangulated

universe w w' v v' u u'

namespace Stacks.Cohomology.LerayTruncation

/-- In `EInt`, an integer is at most its successor. -/
lemma le_succ_eInt (q : ℤ) : ((q : EInt)) ≤ ((q + 1 : ℤ) : EInt) := by simp

section Generic

variable {B : Type u} {C : Type u'} [Category.{v} B] [Category.{v'} C] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C]

/-- **The cohomology spectral object of a triangulated functor.**  For a triangulated functor
`Φ : D⁺(ℬ) ⥤ D⁺(𝒞)` this is the functor sending `K` in `D⁺(ℬ)` to the spectral object of
`𝒞`-objects whose `H^n` on an arrow `a ≤ b` of `EInt` is `H^n(Φ(τ^{≥a} τ^{<b} K))`.

It is the composite of three functors, each of which Mathlib supplies: the spectral object of
the canonical truncation tower of the t-structure of `D⁺(ℬ)`
(`Triangulated.TStructure.spectralObjectFunctor`), its push-forward along the triangulated
functor `Φ` (`Functor.mapTriangulatedSpectralObject`), and the application of the homological
functor `H^0` of `D⁺(𝒞)` (`Triangulated.SpectralObject.mapHomologicalFunctorFunctor`).  So it
is functorial in `K` with no choices anywhere, which is what distinguishes this construction
from the one of [Stacks, Tag 015N] through a Cartan-Eilenberg resolution. -/
noncomputable def cohomologySpectralObjectFunctor
    (Φ : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] :
    DerivedCategory.Plus B ⥤ Abelian.SpectralObject C EInt :=
  DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
    Φ.mapTriangulatedSpectralObject EInt ⋙
    Triangulated.SpectralObject.mapHomologicalFunctorFunctor
      (DerivedCategory.Plus.homologyFunctor C 0) EInt

/-- **The spectral object on an adjacent pair.**  At the arrow `q ≤ q + 1` of `EInt`, the
`n`-th homology functor of `cohomologySpectralObjectFunctor Φ` applied to `K` is
`H^n(Φ(τ^{≥q} τ^{<q+1} K))`, on the nose. -/
lemma cohomologySpectralObjectFunctor_H_obj
    (Φ : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (K : DerivedCategory.Plus B) (n q : ℤ) :
    (((cohomologySpectralObjectFunctor Φ).obj K).H n).obj
        (ComposableArrows.mk₁ (homOfLE (le_succ_eInt q))) =
      (DerivedCategory.Plus.homologyFunctor C n).obj
        (Φ.obj ((DerivedCategory.Plus.TStructure.t.truncGELT q (q + 1)).obj K)) :=
  rfl

/-- **The second page of the spectral sequence of the cohomology spectral object.**  At
`(p, q)` it is `H^{p+q}(Φ(τ^{≥q} τ^{<q+1} K))`.

This is Mathlib's `CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso` for
the data `coreE₂Cohomological`, whose starting page is the second and whose indices at
`(p, q)` are `i₁ = q`, `i₂ = q + 1` and `deg = p + q`; the hypothesis
`HasSpectralSequence coreE₂Cohomological` holds for every spectral object indexed by `EInt`.

By items (2) and (3) of the implementation notes, for `Φ = RG` the right-hand side is
`R^pG(H^q(K))`, which for `G = Γ(Y, -)` and `K = Rf_* -` is the second page
`H^p(Y, R^q f_* -)` of [Stacks, Tag 01F2].  Naturality in `K` is not asserted here. -/
noncomputable def pageTwoXIso (Φ : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (K : DerivedCategory.Plus B) (p q : ℤ) :
    ((((cohomologySpectralObjectFunctor Φ).obj K).spectralSequence
        Abelian.SpectralObject.coreE₂Cohomological).page 2).X (p, q) ≅
      (DerivedCategory.Plus.homologyFunctor C (p + q)).obj
        (Φ.obj ((DerivedCategory.Plus.TStructure.t.truncGELT q (q + 1)).obj K)) :=
  Abelian.SpectralObject.spectralSequenceFirstPageXIso _ _ (p, q)
    (q : EInt) ((q + 1 : ℤ) : EInt) rfl rfl (p + q) rfl

end Generic

section Leray

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  LerayModules.evaluationAdditive

/-- **`RF` commutes with the shift**, by the universal property of the right derived functor.
This is Mathlib's `Functor.IsRightDerivedFunctor.commShift`; it is restated here because the
copies in `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective` and in
`Stacks.Cohomology.CechDelta` are not visible outside their modules. -/
noncomputable local instance commShiftRightDerivedFunctorPlus {A : Type u} {D : Type u'}
    [Category.{v} A] [Category.{v'} D] [Abelian A] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} D] (F : A ⥤ D) [F.Additive]
    [EnoughInjectives A] : F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _ F.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso A) ℤ

/-- **`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is an exact functor of triangulated categories**, which is
[Stacks, Tag 0159] part (1) applied to `F.rightDerivedFunctorPlus` with its own unit. -/
local instance isTriangulatedRightDerivedFunctorPlus {A : Type u} {D : Type u'}
    [Category.{v} A] [Category.{v'} D] [Abelian A] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} D] (F : A ⥤ D) [F.Additive]
    [EnoughInjectives A] : F.rightDerivedFunctorPlus.IsTriangulated :=
  Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F _
    F.rightDerivedFunctorPlusUnit

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The Leray spectral object of a morphism of ringed spaces.**  The functor sending an
object `K` of `D⁺(Mod(𝒪_X))` to the spectral object of `Γ(Y, 𝒪_Y)`-modules built from the
canonical truncation tower of `Rf_* K` by applying `RΓ(Y, -)` and then `H^0`.

This is `cohomologySpectralObjectFunctor` for `Φ = RΓ(Y, -)`, precomposed with `Rf_*`.  It is
the functorial input [Stacks, Tag 01F2] asks for: there are no resolutions and no choices in
it. -/
noncomputable def lerayCohomologySpectralObject :
    DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X)) ⥤
      Abelian.SpectralObject
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))) EInt :=
  (modulePushforward f).rightDerivedFunctorPlus ⋙
    cohomologySpectralObjectFunctor
      (SheafOfModules.evaluation (structureSheafRing Y)
        (op (⊤ : Opens Y.carrier))).rightDerivedFunctorPlus

/-- **The second page of the Leray spectral sequence of the truncation tower.**  At `(p, q)`
it is `H^{p+q}(RΓ(Y, -) (τ^{≥q} τ^{<q+1} (Rf_* K)))`.

This is `pageTwoXIso` for the Leray spectral object.  Item (2) of the implementation notes
rewrites `τ^{≥q} τ^{<q+1} (Rf_* K)` as `R^q f_* K` placed in degree `q`, after which item (3)
turns the right-hand side into `H^p(Y, R^q f_* K)`, the second page of [Stacks, Tag 01F2]. -/
noncomputable def lerayPageTwoXIso
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) (p q : ℤ) :
    ((((lerayCohomologySpectralObject f).obj K).spectralSequence
        Abelian.SpectralObject.coreE₂Cohomological).page 2).X (p, q) ≅
      (DerivedCategory.Plus.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))) (p + q)).obj
        ((SheafOfModules.evaluation (structureSheafRing Y)
            (op (⊤ : Opens Y.carrier))).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.TStructure.t.truncGELT q (q + 1)).obj
            ((modulePushforward f).rightDerivedFunctorPlus.obj K))) :=
  pageTwoXIso _ _ p q

end Leray

end Stacks.Cohomology.LerayTruncation

end
