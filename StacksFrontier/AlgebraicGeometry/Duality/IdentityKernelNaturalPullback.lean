module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ClosedImmersionKernel
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelReduction
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackSingleNaturality
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The identity kernel gives a *natural* isomorphism `g^* ≅ 𝟭` on coherent modules

Let `X` be smooth and proper over a field `k`, let `K` be an object of `D(𝒪_{X ×_k X})` whose
Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to the identity, and let
`s : X ⟶ X ×_k X` be a section of the second projection with `K ≅ Rs_*𝒪_X`.  Writing
`g = pr_1 ∘ s`, this file produces an isomorphism of *functors*

`g^* ≅ 𝟭` on the coherent `𝒪_X`-modules.

## Why naturality

`Stacks.Duality.base_eq_self_of_forall_iso_derivedPullback_single` already extracts from the same
hypotheses an isomorphism `g^*ℱ ≅ ℱ` for each coherent `ℱ`, and concludes that `g` fixes every
point of `X`.  It cannot conclude `g = 𝟙 X`, and not for want of effort: a family of
isomorphisms given one module at a time is genuinely too weak.  Over `Spec 𝔽_4`, viewed as a
smooth proper scheme over `𝔽_2`, the Frobenius `σ` is a self-map inducing the identity of the
space, and the Frobenius twist `σ^*M` of any `𝔽_4`-module is abstractly isomorphic to `M`; so the
pointwise hypothesis holds for a `g` that is not the identity.  What fails for Frobenius is
*naturality*: an isomorphism `η : σ^*(-) ≅ 𝟭` would make the square at the endomorphism
"multiplication by `c`" of `𝔽_4` commute, and that square reads `u·σ(c) = c·u` for a unit `u`,
forcing `σ(c) = c`.

So the natural isomorphism is the extra input the last step of the proof of [Stacks, Tag 0G0E]
needs, and it is what this file supplies.  It is manufactured, not assumed: the isomorphism of
functors is already present in the hypothesis `Stacks.Duality.RepresentsIdentityOnPerfect`, and
the chain that the pointwise argument ran through discards it.  Keeping it costs exactly the
naturality of the top-degree comparison `H^0(Lg^*(ℱ[0])) ≅ g^*ℱ`, which is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleNatIso`.

## Main definitions

* `Stacks.Duality.coherentObjects` — the coherent modules on a scheme, as an object property.
* `Stacks.Duality.singleCoherentToPerfect` — placing a coherent module in degree zero, read as a
  functor from the coherent modules to the perfect objects of `D(𝒪_X)`.  This is where regularity
  of `X` enters, through [Stacks, Tag 0658]'s consequence
  `AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`.

## Main results

* `Stacks.Duality.nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect` — `Φ_K` is
  naturally isomorphic to the inclusion of the perfect objects.  This is the hypothesis of
  Tag 0G0E read through the factorization of `AlgebraicGeometry.fourierMukaiOn` through the full
  subcategory.
* `Stacks.Duality.nonempty_natIso_derivedPullback_of_representsIdentityOnPerfect` — the same for
  `L g^*`, by [Stacks, Tag 0FYV]'s identification
  `AlgebraicGeometry.fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id` of the Fourier-Mukai
  functor of `Rs_*𝒪_X` with `L(pr_1 ∘ s)^*`.
* `Stacks.Duality.nonempty_natIso_pullback_coherentObjects_of_representsIdentityOnPerfect` — the
  conclusion: `g^* ≅ 𝟭` on the coherent modules, as an isomorphism of functors.

## Implementation notes

*The descent to modules.*  The natural isomorphism on perfect objects is restricted along
`singleCoherentToPerfect` and then pushed through `H^0`.  Two identifications make that a chain
of whiskerings and nothing more: `ObjectProperty.liftCompιIso`, which is the (reflexive)
factorization `P.lift F h ⋙ P.ι ≅ F`, and
`DerivedCategory.singleFunctorCompHomologyFunctorIso`, which is `H^0 ∘ (-)[0] ≅ 𝟭`.  The
reassociations are definitional, `CategoryTheory.Functor.comp` being associative on the nose, so
no associator appears.

*Why the conclusion is `Nonempty`.*  The hypothesis `Stacks.Duality.RepresentsIdentityOnPerfect`
is itself an existence statement wrapping the isomorphism of functors in `Nonempty`, as Tag 0FYQ
does; the conclusion is read the same way.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Duality

attribute [local instance 100000] HasDerivedCategory.standard

/-- The coherent modules on a scheme, as an object property. -/
def coherentObjects (X : Scheme.{u}) : ObjectProperty X.Modules := fun F => F.IsCoherent

section

variable {X : Scheme.{u}} (hX : IsRegular X)

include hX

/-- The single complex of a coherent module on a regular scheme is a perfect object. -/
@[sga "6 I 5.11" "special case"]
theorem perfectDerivedObjects_single_of_coherentObjects
    (F : (coherentObjects X).FullSubcategory) :
    perfectDerivedObjects X ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj) :=
  have : F.obj.IsCoherent := F.property
  AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular hX F.obj

/-- Placing a coherent module in degree zero, read as a functor to the perfect objects. -/
def singleCoherentToPerfect :
    (coherentObjects X).FullSubcategory ⥤ (perfectDerivedObjects X).FullSubcategory :=
  (perfectDerivedObjects X).lift
    ((coherentObjects X).ι ⋙ DerivedCategory.singleFunctor X.Modules 0)
    (perfectDerivedObjects_single_of_coherentObjects hX)

end

section Kernel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

omit [Smooth f] [IsProper f] in
/-- **`Φ_K` is naturally isomorphic to the inclusion on the perfect objects.**  This is
`Stacks.Duality.RepresentsIdentityOnPerfect` read through the factorization of
`AlgebraicGeometry.fourierMukaiOn` through the full subcategory. -/
theorem nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K) :
    Nonempty ((perfectDerivedObjects X).ι ⋙ fourierMukai f f K ≅
      (perfectDerivedObjects X).ι) := by
  obtain ⟨hperf, ⟨eid⟩⟩ := hΦ
  exact ⟨((perfectDerivedObjects X).liftCompιIso _ hperf).symm ≪≫
    Functor.isoWhiskerRight eid (perfectDerivedObjects X).ι ≪≫
    (perfectDerivedObjects X).ι.leftUnitor⟩

omit [Smooth f] in
/-- **`L g^*` is naturally isomorphic to the inclusion on the perfect objects**, for
`g = pr_1 ∘ s` with `s` a section of `pr_2` whose direct image is the kernel. -/
theorem nonempty_natIso_derivedPullback_of_representsIdentityOnPerfect
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (s : X ⟶ Limits.pullback f f) (hsnd : s ≫ Limits.pullback.snd f f = 𝟙 X)
    (eK : K ≅ (dpush s).obj (derivedUnitObject X)) :
    Nonempty ((perfectDerivedObjects X).ι ⋙ dpull (s ≫ Limits.pullback.fst f f) ≅
      (perfectDerivedObjects X).ι) :=
  (nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect f K hΦ).elim fun e =>
    ⟨Functor.isoWhiskerLeft (perfectDerivedObjects X).ι
      ((fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id f f s hsnd).symm ≪≫
        (Functor.isoWhiskerLeft (fourierMukaiPullback f f)
          (Functor.isoWhiskerRight
            ((derivedTensorProductFunctor (Limits.pullback f f).toRingedSpace.sheaf).flip.mapIso
              eK) (fourierMukaiPushforward f f))).symm) ≪≫ e⟩

/-- **The natural isomorphism `g^* ≅ 𝟭` on coherent modules.**  From the hypotheses of
[Stacks, Tag 0G0E] together with `K ≅ Rs_*𝒪_X` for a section `s` of `pr_2`, the ordinary pullback
along `g = pr_1 ∘ s` is naturally isomorphic to the identity on coherent `𝒪_X`-modules.

This is the pointwise statement of
`Stacks.Duality.base_eq_self_of_forall_iso_derivedPullback_single` upgraded to an isomorphism of
functors, which is what the last step of the source's proof needs: a family of isomorphisms
`g^*ℱ ≅ ℱ` given one module at a time cannot see the difference between the identity and a
Frobenius twist. -/
theorem nonempty_natIso_pullback_coherentObjects_of_representsIdentityOnPerfect
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (s : X ⟶ Limits.pullback f f) (hsnd : s ≫ Limits.pullback.snd f f = 𝟙 X)
    (eK : K ≅ (dpush s).obj (derivedUnitObject X)) :
    Nonempty ((coherentObjects X).ι ⋙
        Scheme.Modules.pullback (s ≫ Limits.pullback.fst f f) ≅ (coherentObjects X).ι) := by
  have hX : IsRegular X := isRegular_of_smooth_over_field f
  refine (nonempty_natIso_derivedPullback_of_representsIdentityOnPerfect f K hΦ s hsnd eK).elim
    fun ν => ⟨?_⟩
  set g := s ≫ Limits.pullback.fst f f
  set sf := DerivedCategory.singleFunctor X.Modules 0 with hsf
  set H := DerivedCategory.homologyFunctor X.Modules 0 with hH
  set S := singleCoherentToPerfect hX with hS
  have e1 : (coherentObjects X).ι ⋙ Scheme.Modules.pullback g ≅
      ((coherentObjects X).ι ⋙ sf) ⋙ (dpull g ⋙ H) :=
    Functor.isoWhiskerLeft (coherentObjects X).ι
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleNatIso
        g.toLRSHom.toShHom 0).symm
  have hlift : S ⋙ (perfectDerivedObjects X).ι ≅ (coherentObjects X).ι ⋙ sf :=
    (perfectDerivedObjects X).liftCompιIso ((coherentObjects X).ι ⋙ sf)
      (perfectDerivedObjects_single_of_coherentObjects hX)
  have e2 : ((coherentObjects X).ι ⋙ sf) ⋙ (dpull g ⋙ H) ≅
      (S ⋙ ((perfectDerivedObjects X).ι ⋙ dpull g)) ⋙ H :=
    Functor.isoWhiskerRight hlift.symm (dpull g ⋙ H)
  have e3 : (S ⋙ ((perfectDerivedObjects X).ι ⋙ dpull g)) ⋙ H ≅
      (S ⋙ (perfectDerivedObjects X).ι) ⋙ H :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft S ν) H
  have e4 : (S ⋙ (perfectDerivedObjects X).ι) ⋙ H ≅ (coherentObjects X).ι ⋙ (sf ⋙ H) :=
    Functor.isoWhiskerRight hlift H
  have e5 : (coherentObjects X).ι ⋙ (sf ⋙ H) ≅ (coherentObjects X).ι ⋙ 𝟭 X.Modules :=
    Functor.isoWhiskerLeft (coherentObjects X).ι
      (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0)
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5 ≪≫ (coherentObjects X).ι.rightUnitor

end Kernel

end Stacks.Duality

end
