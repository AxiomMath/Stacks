module

public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom
import StacksCore.Tactic.StacksAttribute

/-!
# The derived internal Hom out of a perfect sheafification lies in `D_QCoh`

Let `R` be a commutative ring and `X = Spec R`. Part (3)(b) of [Stacks, Tag 0A6H] identifies the
derived internal Hom of two sheafifications with a sheafification,

`R𝓗om_{𝒪_X}(K̃, L̃) ≅ (RHom_R(K, L))~`

for `K` perfect and `L` *arbitrary*; this is
`AlgebraicGeometry.affinePerfectDerivedSheafHomIso`. Part (2) of the same tag draws the
consequence the source draws from it: the derived internal Hom has quasi-coherent cohomology
sheaves. This file proves that consequence on an affine scheme, for the two sheafified arguments
the comparison speaks about.

The conclusion is read off the comparison: every cohomology sheaf of a sheafification is
quasi-coherent, so the right-hand side lies in `D_QCoh(𝒪_X)` and the left-hand side inherits it.
Unlike part (1) there is no lower bound to prove — and none is claimed by the source, since `L`
carries no boundedness hypothesis.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_affinePerfectDerivedSheafHom` — every cohomology
  sheaf of `R𝓗om_{𝒪_X}(K̃, L̃)` is quasi-coherent.
* `AlgebraicGeometry.derivedCategoryB_affinePerfectDerivedSheafHom` — the same read as
  membership of `D_QCoh(𝒪_X)`.

## Implementation notes

What is proved here is part (2) of [Stacks, Tag 0A6H] *for an affine scheme and for arguments
already presented as sheafifications*. The source deduces part (2) in general by localizing and
then invoking part (3); the localization step and the identification of a perfect object of
`D(𝒪_X)` with the sheafification of a perfect object of `D(R)` ([Stacks, Tag 08EB]) are not used
here, so the hypothesis names module-level data rather than deriving it from sheaf-level data.
Those two steps are taken in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffineSheafPerfectHomQuasicoherent.lean` and
in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/SchemeSheafPerfectHomQuasicoherent.lean`.

**Why the derived model is pinned with priority.**
`AlgebraicGeometry.affinePerfectDerivedSheafHomIso` is stated at
`CategoryTheory.HasDerivedCategory.standard`, which its own file selects by a file-level local
instance while importing nothing that reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. This file does reach that file, through
`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`, whose `HasDerivedCategory` instances are
*global*; the local attribute below therefore carries priority `10000`, so that the comparison
remains applicable.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Part (2) of [Stacks, Tag 0A6H], on an affine scheme, for sheafified arguments.** For `K`
perfect and `L` arbitrary in `D(R)`, every cohomology sheaf of `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` is
quasi-coherent.

The comparison `AlgebraicGeometry.affinePerfectDerivedSheafHomIso` of clause (3)(b) identifies
that object with a sheafification, whose cohomology sheaves are quasi-coherent by
[Stacks, Tag 06Z0], and quasi-coherence is closed under isomorphisms. -/
theorem isQuasicoherent_homology_affinePerfectDerivedSheafHom (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.Perfect.IsPerfect K) (n : ℤ) :
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
            (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
              ((tilde.functor R).mapDerivedCategory.obj L))) :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
      (affinePerfectDerivedSheafHomIso R K L hK)).symm
    (isQuasicoherent_homology_mapDerivedCategory_obj R _ n)

/-- **Part (2) of [Stacks, Tag 0A6H] on an affine scheme, for sheafified arguments.** For `K`
perfect and `L` arbitrary in `D(R)`, the derived internal Hom `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` lies in
`D_QCoh(𝒪_{Spec R})`.

No lower bound is asserted, and none holds: `L` is arbitrary, so `R𝓗om_{𝒪_X}(K̃, L̃)` need not be
bounded below. That is the whole difference between part (2) and part (1). -/
theorem derivedCategoryB_affinePerfectDerivedSheafHom (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
            ((tilde.functor R).mapDerivedCategory.obj L)) :=
  fun n => isQuasicoherent_homology_affinePerfectDerivedSheafHom R K L hK n

end AlgebraicGeometry

end
