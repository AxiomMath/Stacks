module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
import StacksCore.Tactic.StacksAttribute

/-!
# Part (2) of Tag 0A6H on an affine scheme

Let `R` be a commutative ring and `X = Spec R`. Part (2) of [Stacks, Tag 0A6H] says that for `E`
a perfect object of `D(𝒪_X)` and `F` an object of `D_QCoh(𝒪_X)` the derived internal Hom
`R𝓗om_{𝒪_X}(E, F)` lies in `D_QCoh(𝒪_X)`.
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePerfectHomQuasicoherent.lean`
proves this on an affine scheme for the two *sheafified* arguments part (3)(b) speaks about,
that is for `E = K̃` with `K` perfect in `D(R)` and `F = L̃` with `L` arbitrary in `D(R)`. This
file removes both hypotheses: `E` may be any perfect object of `D(𝒪_X)` and `F` any object of
`D_QCoh(𝒪_X)`.

The step is the one the source takes with [Stacks, Tag 08EB]. A perfect object of `D(𝒪_X)` is
pseudo-coherent, hence has quasi-coherent cohomology by [Stacks, Tag 08E5], so on an affine
scheme it is the derived sheafification `K̃` of an object `K` of `D(R)` by
[Stacks, Tag 06Z0]; and [Stacks, Tag 08EB] turns the perfectness of `K̃` into
perfectness of `K`. The second argument is handled by [Stacks, Tag 06Z0] alone, with no
boundedness to reflect — which is exactly why part (2) reaches an arbitrary object of
`D_QCoh(𝒪_X)` where part (1) stops at a sheafification.

## Main results

* `AlgebraicGeometry.derivedCategoryB_affineDerivedSheafHom_of_isPerfect` — **part (2) of
  [Stacks, Tag 0A6H] on the spectrum of a ring.**

## Implementation notes

**Why the derived model is pinned with priority.** As in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSheafPseudoCoherentHomQuasicoherent`,
the import closure reaches `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose
`HasDerivedCategory` instances are *global*, while the comparison of clause (3)(b) is stated at
`CategoryTheory.HasDerivedCategory.standard`; the local attribute below therefore carries
priority `10000`.

**Two spellings of perfectness and two of `𝒪_X`-modules.** The hypothesis is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, which is the spelling [Stacks, Tag 08EB] is
proved at, while `AlgebraicGeometry.RingedSpace.IsPerfect` is the one carrying
`AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent`, the cheap route to the
pseudo-coherence [Stacks, Tag 08E5] consumes; the two unfold to the same proposition and the
`have hperf` below is the crossing. Going instead through [Stacks, Tag 08CQ] and
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'` is *not* viable here:
that route exhausts the `whnf` heartbeat budget.
Likewise `AlgebraicGeometry.Scheme.Modules (Spec R)` and
`Stacks.StrictlyPerfect.OXMod (Spec R).toRingedSpace` are the same type but are not interchanged
by typeclass synthesis. As in the pseudo-coherent file, every intermediate step is introduced by
a `have` whose type is *inferred*, so that it elaborates where the instances are found and is
only then checked against the next step at default transparency.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0A6H, part (2), on the spectrum of a ring.** Let `E` be a perfect
object of `D(𝒪_{Spec R})` and let `F` be an object of `D_QCoh(𝒪_{Spec R})`. Then the derived
internal Hom `R𝓗om_{𝒪_{Spec R}}(E, F)` lies in `D_QCoh(𝒪_{Spec R})`.

`E` is pseudo-coherent, hence has quasi-coherent cohomology by [Stacks, Tag 08E5], so by
[Stacks, Tag 06Z0] there is an object `K` of `D(R)` and an isomorphism `K̃ ≅ E`; by
[Stacks, Tag 08EB] that makes `K` perfect. The same tag presents `F` as `L̃` for an
object `L` of `D(R)`, with no condition on `L`.
`AlgebraicGeometry.derivedCategoryB_affinePerfectDerivedSheafHom` then puts
`R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` in `D_QCoh(𝒪_{Spec R})`, and the two variables of the derived internal
Hom carry the isomorphisms to one onto `R𝓗om_{𝒪_{Spec R}}(E, F)`. -/
theorem derivedCategoryB_affineDerivedSheafHom_of_isPerfect (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E)
    (F : DerivedCategory (Spec R).Modules)
    (hF : DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).obj F) := by
  have hperf : RingedSpace.IsPerfect (X := (Spec R).toRingedSpace) E := hE
  obtain ⟨K, ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E
    (isQuasicoherentDerived_of_isPseudoCoherent (Spec R) E hperf.isPseudoCoherent)
  obtain ⟨L, ⟨eL⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R F hF
  have hK := (isPerfect_tilde_iff K).1 (hperf.of_iso eK.symm)
  have h := derivedCategoryB_affinePerfectDerivedSheafHom R K L hK
  have e := ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso eK.symm.op).app
      ((tilde.functor R).mapDerivedCategory.obj L) ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).mapIso eL
  exact fun n => (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (h n)

end AlgebraicGeometry

end
