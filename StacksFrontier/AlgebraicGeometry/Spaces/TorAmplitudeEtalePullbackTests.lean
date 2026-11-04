module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands

/-!
# Tor amplitude along a separated étale morphism is detected by the pulled-back test modules

Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and let `E` be an object of `D(𝒪_X)` on the small étale ringed site of `X`.
Tor amplitude in `[a, b]` for `E`, Stacks 08FZ, asks that `Hⁱ(E ⊗^L_{𝒪_X} ℳ) = 0` for
`i ∉ [a, b]` and *every* `𝒪_X`-module `ℳ`.  This file shows that the test modules of the form
`f^*𝒩`, for `𝒩` an `𝒪_Y`-module, already suffice.

The reason is Stacks 0HAP, `AlgebraicGeometry.Space.counitSplitEpiOfSeparatedEtale`: for `f`
separated and étale the counit `f^*f_*ℳ ⟶ ℳ` of the adjunction of Stacks 03LU is a split
epimorphism, so every `𝒪_X`-module `ℳ` is a retract of the pulled-back module `f^*(f_*ℳ)`; and
`ℳ ↦ Hⁱ(E ⊗^L_{𝒪_X} ℳ[0])` is a functor, so it carries a retract of an object with zero image
to an object with zero image.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitude_of_forall_modulePullback`: if
  `Hⁱ(E ⊗^L_{𝒪_X} f^*𝒩) = 0` for `i ∉ [a, b]` and every `𝒪_Y`-module `𝒩`, then `E` has Tor
  amplitude in `[a, b]`.
* `AlgebraicGeometry.Space.hasTorAmplitude_iff_forall_modulePullback`: the resulting
  characterisation, the other direction being the specialisation of the quantifier in
  Stacks 08FZ.

## Implementation notes

This is the step of Stacks 08IL that Stacks 0HAP supplies, isolated and stated unconditionally.
In the source's proof of Stacks 08IL the morphism `f` is an étale chart `j : U → X` of a
quasi-separated algebraic space, so that `j` is quasi-compact and separated; the vanishing for
the test modules `j^*𝒩` is obtained from condition (2) on `X` applied to `𝒩 = j_*𝒢` — which is
quasi-coherent by Stacks 03M9 — and flat pullback along `j`, and the retraction of `𝒢` off
`j^*j_*𝒢` is Stacks 0HAP.  Neither quasi-compactness of `f` nor quasi-coherence of the test
modules is needed for the statement proved here, because
`AlgebraicGeometry.Space.counitSplitEpiOfSeparatedEtale` needs neither.

Nothing here is a clause of Stacks 08IL and no `@[stacks 08IL]` attribute is carried.  The
statement quantifies over *all* `𝒪_Y`-modules `𝒩`, whereas condition (2) of Stacks 08IL
quantifies over the quasi-coherent ones; converting the one into the other is the remaining
content of the source's first paragraph, and it needs a transport of the vanishing along the
morphism `j` of small étale ringed sites, which the Tor-amplitude development does not have at
the universe `AlgebraicGeometry.RingedSite.{u + 1, u, u}` of the small étale ringed site of an
algebraic space — see the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/TorAmplitudeQuasiCoherentTests.lean`.

The retraction argument is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/DirectSummands.lean`, where it is a
`private` lemma and so not reusable here; it is restated below.  Unlike Stacks 08G3 it is used
with a retract that is not a biproduct projection, which is exactly what Stacks 0HAP provides.

## References

* [Stacks Project, Lemma 69.11.3 (Tag 0HAP)](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Lemma 75.13.8 (Tag 08IL)](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}
  [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O)
      (ComplexShape.up ℤ)]

/-- **Tor amplitude along a separated étale morphism is detected by the pulled-back test
modules.**  Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces and let `E` be an
object of `D(𝒪_X)`.  If `Hⁱ(E ⊗^L_{𝒪_X} (f^*𝒩)[0]) = 0` for every `𝒪_Y`-module `𝒩` and every
`i ∉ [a, b]`, then `E` has Tor amplitude in `[a, b]`.

An arbitrary `𝒪_X`-module `ℳ` is a retract of `f^*(f_*ℳ)`, the counit of the adjunction of
Stacks 03LU being a split epimorphism by Stacks 0HAP, and
`ℳ ↦ Hⁱ(E ⊗^L_{𝒪_X} ℳ[0])` is a functor.  Neither quasi-compactness of `f` nor quasi-coherence
of the test modules enters, Stacks 0HAP being available here without either. -/
theorem hasTorAmplitude_of_forall_modulePullback (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (a b : ℤ)
    (hE : ∀ (N : Modules.{u, u} B S hS Y.1 Y.2) (i : ℤ), i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        ((T.tensor.obj E).obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
            ((modulePullback B S hS f).obj N))))) :
    DerivedTensorProduct.HasTorAmplitude T E a b := fun M i hi =>
  Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
    (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0 ⋙ T.tensor.obj E ⋙
      DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i)
    (counitSplitEpiOfSeparatedEtale B S hS f het hsep M).section_
    ((modulePullbackAdjunction B S hS f).counit.app M)
    (counitSplitEpiOfSeparatedEtale B S hS f het hsep M).id
    (hE ((modulePushforward B S hS f).obj M) i hi)

/-- **Tor amplitude along a separated étale morphism, tested on the pulled-back modules
alone.**  For `f : X ⟶ Y` separated and étale, an object `E` of `D(𝒪_X)` has Tor amplitude in
`[a, b]` if and only if `Hⁱ(E ⊗^L_{𝒪_X} (f^*𝒩)[0]) = 0` for every `𝒪_Y`-module `𝒩` and every
`i ∉ [a, b]`.

The forward direction is the specialisation of the quantifier of Stacks 08FZ to the test modules
of the form `f^*𝒩`; the converse is
`AlgebraicGeometry.Space.hasTorAmplitude_of_forall_modulePullback`. -/
theorem hasTorAmplitude_iff_forall_modulePullback (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (a b : ℤ) :
    DerivedTensorProduct.HasTorAmplitude T E a b ↔
      ∀ (N : Modules.{u, u} B S hS Y.1 Y.2) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          ((T.tensor.obj E).obj
            ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
              ((modulePullback B S hS f).obj N)))) :=
  ⟨fun hE N i hi => hE ((modulePullback B S hS f).obj N) i hi,
    hasTorAmplitude_of_forall_modulePullback B S hS f het hsep T E a b⟩

end AlgebraicGeometry.Space

end
