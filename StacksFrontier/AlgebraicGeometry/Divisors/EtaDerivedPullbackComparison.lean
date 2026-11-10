module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackDerivedTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackTorsionFree
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedUnconditional
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback commutes with derived décalage

Let `h : Y ⟶ X` be a morphism of schemes, let `D ⊆ X` be an effective Cartier divisor with ideal
sheaf `I = ℐ_D ⊆ 𝒪_X`, and suppose the pullback `E = h^{-1}D` is defined, with ideal sheaf
`J = ℐ_E ⊆ 𝒪_Y`.  This file builds the canonical comparison

`Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)`

in `D(𝒪_Y)`, at an object `M` of `D(𝒪_X)` presented by a complex of `I`-torsion-free
`𝒪_X`-modules, and proves it is an isomorphism when `h` is flat.  This is [Stacks, Tag 0F9X] for
a flat `h`.

## Main definitions

* `Stacks.Divisors.Eta.derivedEtaPullbackComparison`: **the canonical comparison map.**  It is
  the composite of three canonical maps: the identification of the left derived pullback with the
  functor induced by the exact `h^*`, the transported chain-level comparison
  `Stacks.IdealTorsion.Eta.transportedPullbackDerivedEtaMap`, and that identification again,
  backwards.

## Main results

* `Stacks.Divisors.Eta.isIso_derivedEtaPullbackComparison`: **[Stacks, Tag 0F9X] for a flat
  morphism** — the comparison is an isomorphism.
* `Stacks.Divisors.Eta.hasTorsionFreeResolutions_pullbackIdealIncl`: termwise torsion-free
  resolutions exist for the pulled-back ideal, so the derived décalage for it is available
  without a further hypothesis.
* `Stacks.Divisors.Eta.exists_torsionFreeComplex_iso`: **every object of `D(𝒪_X)` is presented by
  a complex of `I`-torsion-free modules**, so presenting `M` that way is no loss of generality.

## What is assumed, and what is not

**Flatness, and why it is named in the tag.**  The source proves tag 0F9X under the hypothesis
that `(X, D, M)` is a *good* triple, by reducing to the affine computation of More on Algebra,
Section 15.98, which uses principality of the determinantal ideals `I_i(M^•, f)`.  The route
taken here is different and gives the comparison for a **flat** `h` instead: flat pullback is
exact, so it carries the fibre product defining each term of the chain-level décalage to the
corresponding fibre product downstairs, which is
`Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap`.  Neither hypothesis implies the other, so the
restriction to flat `h` is recorded in the attribute rather than left silent.

**Nothing of the conclusion is assumed.**  The comparison map is constructed, not posited; the
only data beyond `h`, `D` and the hypothesis that `h^{-1}D` is defined is a presentation of `M`
by a complex of `I`-torsion-free modules, which every object of `D(𝒪_X)` admits
(`Stacks.Divisors.Eta.exists_torsionFreeComplex_iso`).  In particular [Stacks, Tag 0F8Q] is
**not** carried: `Stacks.Divisors.Eta.derivedEtaData` discharges it unconditionally for the ideal
sheaf of an effective Cartier divisor on a scheme, so `Lη_I` here is the honest functor
`Stacks.IdealTorsion.Eta.derivedEta` and not a hypothesis.

## Implementation notes

`Lh^*` is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, the left derived
pullback.  The comparison of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafPullbackDerived.lean` is stated for
`CategoryTheory.Functor.mapDerivedCategory` of the exact functor `h^*` instead, and the two are
identified by `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory`;
`Stacks.IdealTorsion.Eta.etaPullbackModules h` and
`RingedSpaceModuleAdjunction.modulePullback h` are the same functor by definition, so no further
conversion is needed.

The ideal sheaf `ℐ_E` of the inverse image is identified with `h^*ℐ_D`, compatibly with the
inclusions into `𝒪_Y`, by `Stacks.Divisors.pullbackIdealSheafComapIso` — which needs only that
`h^{-1}D` is again an effective Cartier divisor, not flatness — and the décalage is carried
across that identification by
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafIdealTransport.lean`.

The derived category is the standard model throughout, which is where
`Stacks.IdealTorsion.Eta.derivedEta` and the left derived pullback both live.

`Stacks.IdealTorsion.Eta.derivedEta` is applied with its two instance arguments — `Mono ι` and
the invertibility of the ideal — passed explicitly, as `mono_idealSheafι` and
`isInvertible_idealSheaf`; the same is done for the three other callees stated over a ringed
space, `Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl`,
`Stacks.IdealTorsion.Eta.transportedPullbackDerivedEtaMap` and
`Stacks.IdealTorsion.Eta.isIso_transportedPullbackDerivedEtaMap`.  `derivedEta` names the ring
sheaf of its ringed space as
`Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf`, while `Stacks.Divisors.Eta.idealSheafι` and the
two instances about it are stated over
`Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩`.
The two are the same sheaf of rings — `AlgebraicGeometry.SheafedSpace.sheaf` is that anonymous
constructor — but identifying them unfolds a projection, which happens at the transparency at
which an explicit argument is unified and not at the one at which an instance argument is
synthesized.  Supplying the instances explicitly therefore runs the check where it succeeds; the
term is the same one instance search would have produced.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 01WV](https://stacks.math.columbia.edu/tag/01WV)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackIsoMapDerivedCategory)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors.Eta

/-- Sheaves of modules on a ringed space form an abelian category, restated at the
`structureSheafRing` spelling of the structure sheaf that the left derived
pullback is written in.  Instance search does not find `SheafOfModules.instAbelian` at this
spelling once the décalage files are in scope, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackDerived`. -/
instance abelianSheafOfModulesRingSheaf (W : RingedSpace.{u}) :
    Abelian (SheafOfModules.{u} (structureSheafRing W)) :=
  SheafOfModules.instAbelian _

/-- Left exactness of the module pullback, carried from the `Stacks.IdealTorsion.Eta` spelling of
the functor to the `RingedSpaceModuleAdjunction` one.  The two functors are equal by definition,
but their head symbols differ, so instance search does not carry the hypothesis across. -/
instance preservesFiniteLimitsModulePullbackOfEta {A B : RingedSpace.{u}} (f : A ⟶ B)
    [CategoryTheory.Limits.PreservesFiniteLimits
      (Stacks.IdealTorsion.Eta.etaPullbackModules f)] :
    CategoryTheory.Limits.PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback f) :=
  ‹CategoryTheory.Limits.PreservesFiniteLimits (Stacks.IdealTorsion.Eta.etaPullbackModules f)›

/-- Right exactness of the module pullback, carried between the two spellings of the functor;
see `Stacks.Divisors.Eta.preservesFiniteLimitsModulePullbackOfEta`. -/
instance preservesFiniteColimitsModulePullbackOfEta {A B : RingedSpace.{u}} (f : A ⟶ B)
    [CategoryTheory.Limits.PreservesFiniteColimits
      (Stacks.IdealTorsion.Eta.etaPullbackModules f)] :
    CategoryTheory.Limits.PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback f) :=
  ‹CategoryTheory.Limits.PreservesFiniteColimits (Stacks.IdealTorsion.Eta.etaPullbackModules f)›

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **Every object of `D(𝒪_X)` is presented by a complex of `ℐ_D`-torsion-free modules.**  This
is the representability clause of `Stacks.Divisors.Eta.derivedEtaData`, read through
`HomologicalComplex.liftObjectProperty`, which turns a complex of modules together with the
torsion-freeness of its terms into a complex of objects of the full subcategory of torsion-free
modules.  It is what makes the presentation of `M` below no loss of generality. -/
theorem exists_torsionFreeComplex_iso
    (M : DerivedCategory (SheafOfModules.{u} (structureSheaf X.toRingedSpace.sheaf))) :
    ∃ K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ,
      Nonempty (DerivedCategory.Q.obj
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K) ≅
          M) := by
  obtain ⟨F, htf, hiso⟩ := (derivedEtaData D).exists_isIdealTorsionFree_rep M
  exact ⟨HomologicalComplex.liftObjectProperty
    (Stacks.IdealTorsion.Eta.torsionFreeProperty X.toRingedSpace (idealSheafι D)) F htf, hiso⟩

/-- **Termwise torsion-free resolutions exist for the pulled-back ideal `h^*ℐ_D`.**  The pullback
of an invertible sheaf of modules is invertible ([Stacks, Tag 0B8L]) and the inclusion
`h^*ℐ_D ⟶ 𝒪_Y` is a monomorphism for flat `h`, so
`Stacks.IdealTorsion.Eta.hasTorsionFreeResolutions_of_isInvertible` applies. -/
theorem hasTorsionFreeResolutions_pullbackIdealIncl
    (hflat : AlgebraicGeometry.IsFlat h.toLRSHom.toShHom) :
    Stacks.IdealTorsion.Eta.HasTorsionFreeResolutions Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D)) :=
  Stacks.IdealTorsion.Eta.hasTorsionFreeResolutions_of_isInvertible Y.toRingedSpace _ _
    (@Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl _ _ h.toLRSHom.toShHom hflat (idealSheaf D)
      (idealSheafι D) (mono_idealSheafι D))
    (Stacks.IdealTorsion.Eta.isInvertible_pullbackIdeal h.toLRSHom.toShHom (idealSheaf D))

/-- The termwise pullback of a complex of `ℐ_D`-torsion-free modules is a complex of
`h^*ℐ_D`-torsion-free modules, for flat `h`.  This is
`Stacks.IdealTorsion.Eta.isIdealTorsionFree_pullbackComplex_of_isFlat`; the stalks of the
structure sheaf of a scheme are local rings, which is what that statement asks for. -/
theorem isIdealTorsionFree_pullbackComplex
    (hflat : AlgebraicGeometry.IsFlat h.toLRSHom.toShHom)
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ) (n : ℤ) :
    Stacks.IdealTorsion.IsIdealTorsionFree Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D))
      ((Stacks.IdealTorsion.Eta.pullbackComplex h.toLRSHom.toShHom
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)).X
          n) :=
  have := @Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl _ _ h.toLRSHom.toShHom hflat
    (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
  Stacks.IdealTorsion.Eta.isIdealTorsionFree_pullbackComplex_of_isFlat h.toLRSHom.toShHom
    (idealSheaf D) (idealSheafι D) hflat
    ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)
    (Stacks.IdealTorsion.Eta.torsionFreeComplex_torsionFree X.toRingedSpace (idealSheafι D) K) n

/-! ### The comparison -/

section Comparison

variable [CategoryTheory.Limits.PreservesFiniteLimits
    (Stacks.IdealTorsion.Eta.etaPullbackModules h.toLRSHom.toShHom)]
  [CategoryTheory.Limits.PreservesFiniteColimits
    (Stacks.IdealTorsion.Eta.etaPullbackModules h.toLRSHom.toShHom)]
  [hmono : Mono (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
    (idealSheafι D))]
  [hD : Stacks.Divisors.IsPullbackDefined h D]

/-- **The canonical comparison `Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)`**, where `I = ℐ_D`, `J = ℐ_E` is
the ideal sheaf of the inverse image `E = h^{-1}D`, and `M = [G^•]` is presented by a complex
`G^•` of `I`-torsion-free `𝒪_X`-modules.

The composite of three canonical maps: the identification
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory` of the left
derived pullback with the functor induced on derived categories by the exact functor `h^*`, the
transported chain-level comparison
`Stacks.IdealTorsion.Eta.transportedPullbackDerivedEtaMap`, and that identification again,
backwards, inside `Lη_J`.

The two exactness hypotheses and the monomorphy of `h^*I ⟶ 𝒪_Y` are instance binders because
they are not consequences of the data alone; flatness of `h` supplies all three, by
`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat`,
`RingedSpaceModuleAdjunction.preservesColimits_modulePullback` and
`Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl`. -/
def derivedEtaPullbackComparison (hflat : AlgebraicGeometry.IsFlat h.toLRSHom.toShHom)
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ) :
    (derivedPullback h.toLRSHom.toShHom).obj
        ((@Stacks.IdealTorsion.Eta.derivedEta X.toRingedSpace (idealSheaf D) (idealSheafι D)
            (mono_idealSheafι D) (isInvertible_idealSheaf D)
            (hasTorsionFreeResolutions D)).obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) ⟶
      (@Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (D.comap h))
          (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
          (isInvertible_idealSheaf (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).obj
        ((derivedPullback h.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) :=
  (derivedPullbackIsoMapDerivedCategory h.toLRSHom.toShHom hflat).hom.app
      ((@Stacks.IdealTorsion.Eta.derivedEta X.toRingedSpace (idealSheaf D) (idealSheafι D)
          (mono_idealSheafι D) (isInvertible_idealSheaf D)
          (hasTorsionFreeResolutions D)).obj
        (DerivedCategory.Q.obj
          ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K))) ≫
    @Stacks.IdealTorsion.Eta.transportedPullbackDerivedEtaMap _ _ h.toLRSHom.toShHom
      inferInstance inferInstance (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
      (isInvertible_idealSheaf D) hmono
      (idealSheaf (D.comap h)) (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
      (isInvertible_idealSheaf (D.comap h))
      (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
      (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD)
      (hasTorsionFreeResolutions D) (hasTorsionFreeResolutions_pullbackIdealIncl h D hflat)
      (hasTorsionFreeResolutions (D.comap h)) K
      (isIdealTorsionFree_pullbackComplex h D hflat K) ≫
    (@Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (D.comap h))
        (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
        (isInvertible_idealSheaf (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).map
      ((derivedPullbackIsoMapDerivedCategory h.toLRSHom.toShHom hflat).inv.app
        (DerivedCategory.Q.obj
          ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)))

/-- **[Stacks, Tag 0F9X] for a flat morphism.**  Let `X` be a scheme, let `D ⊆ X` be an effective
Cartier divisor with ideal sheaf `I = ℐ_D`, let `h : Y ⟶ X` be a flat morphism of schemes and
suppose the pullback `E = h^{-1}D` is defined, with ideal sheaf `J = ℐ_E`.  Then for every object
`M = [G^•]` of `D(𝒪_X)` presented by a complex of `I`-torsion-free modules, the canonical
comparison `Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)` is an isomorphism.

Two of the three constituents of `Stacks.Divisors.Eta.derivedEtaPullbackComparison` are
components of the natural isomorphism identifying `Lh^*` with the functor induced by `h^*`,
hence isomorphisms; the remaining one is an isomorphism by
`Stacks.IdealTorsion.Eta.isIso_transportedPullbackDerivedEtaMap`, which is where flatness is
used. -/
@[stacks 0F9X "the case of a flat h, which neither implies nor is implied by the source's \
statement: flatness replaces goodness of the triple, and no goodness is used. the general case, \
for an arbitrary h and a good \
triple, is AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullback_derivedEta_iso"]
theorem isIso_derivedEtaPullbackComparison
    (hflat : AlgebraicGeometry.IsFlat h.toLRSHom.toShHom)
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ) :
    IsIso (derivedEtaPullbackComparison h D hflat K) := by
  rw [derivedEtaPullbackComparison]
  have :=
    @Stacks.IdealTorsion.Eta.isIso_transportedPullbackDerivedEtaMap _ _ h.toLRSHom.toShHom
      inferInstance inferInstance (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
      (isInvertible_idealSheaf D) hmono
      (idealSheaf (D.comap h)) (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
      (isInvertible_idealSheaf (D.comap h))
      (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
      (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD) hflat
      (hasTorsionFreeResolutions D) (hasTorsionFreeResolutions_pullbackIdealIncl h D hflat)
      (hasTorsionFreeResolutions (D.comap h)) K
      (isIdealTorsionFree_pullbackComplex h D hflat K)
  exact IsIso.comp_isIso'
    ((derivedPullbackIsoMapDerivedCategory h.toLRSHom.toShHom hflat).app _).isIso_hom
    (IsIso.comp_isIso' this (Functor.mapIso _
      ((derivedPullbackIsoMapDerivedCategory h.toLRSHom.toShHom hflat).app _).symm).isIso_hom)

/-- **[Stacks, Tag 0F9X] for a flat morphism, as an isomorphism.**  The comparison of
`Stacks.Divisors.Eta.derivedEtaPullbackComparison`, packaged as an isomorphism
`Lh^*(Lη_I M) ≅ Lη_J(Lh^* M)` in `D(𝒪_Y)`. -/
def derivedEtaPullbackIso (hflat : AlgebraicGeometry.IsFlat h.toLRSHom.toShHom)
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ) :
    (derivedPullback h.toLRSHom.toShHom).obj
        ((@Stacks.IdealTorsion.Eta.derivedEta X.toRingedSpace (idealSheaf D) (idealSheafι D)
            (mono_idealSheafι D) (isInvertible_idealSheaf D)
            (hasTorsionFreeResolutions D)).obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) ≅
      (@Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (D.comap h))
          (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
          (isInvertible_idealSheaf (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).obj
        ((derivedPullback h.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) :=
  haveI := isIso_derivedEtaPullbackComparison h D hflat K
  asIso (derivedEtaPullbackComparison h D hflat K)

end Comparison

end Stacks.Divisors.Eta

end
