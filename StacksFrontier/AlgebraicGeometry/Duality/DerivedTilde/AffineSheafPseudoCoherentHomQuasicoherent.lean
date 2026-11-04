module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceBoundedBelow
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# Part (1) of Tag 0A6H on an affine scheme, for a sheaf-level pseudo-coherent first argument

Let `R` be a commutative ring and `X = Spec R`. Part (1) of [Stacks, Tag 0A6H] says that for `E`
a pseudo-coherent object of `D(𝒪_X)` and `F` an object of `D⁺_QCoh(𝒪_X)` the derived internal Hom
`R𝓗om_{𝒪_X}(E, F)` lies in `D⁺_QCoh(𝒪_X)`.
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePseudoCoherentHomQuasicoherent.lean`
proves this on an affine scheme for the two *sheafified* arguments part (3)(a) speaks about, that
is for `E = K̃` with `K` pseudo-coherent in `D(R)` and `F = L̃` with `L` bounded below in `D(R)`.
This file removes the hypothesis on the first argument: `E` may be any pseudo-coherent object of
`D(𝒪_X)`.

The step is the one the source takes with [Stacks, Tag 08E7]. A pseudo-coherent object of
`D(𝒪_X)` has quasi-coherent cohomology by [Stacks, Tag 08E5], so on an affine scheme it is the
derived sheafification `K̃` of an object `K` of `D(R)` by [Stacks, Tag 06Z0]; and [Stacks,
Tag 08E7] turns the pseudo-coherence of `K̃` into pseudo-coherence of `K`. The conclusion is then
read off the sheafified case along the chosen isomorphism `K̃ ≅ E`, which the contravariant
variable of the derived internal Hom carries to an isomorphism of the two internal Homs.

## Main results

* `AlgebraicGeometry.derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent` — for `E` a
  pseudo-coherent object of `D(𝒪_{Spec R})` and `L` bounded below in `D(R)`, the derived internal
  Hom `R𝓗om_{𝒪_{Spec R}}(E, L̃)` lies in `D⁺_QCoh(𝒪_{Spec R})`.

## Implementation notes

**The second argument is still a sheafification.** Replacing `L̃` by an arbitrary object of
`D⁺_QCoh(𝒪_{Spec R})` would need the converse direction of boundedness below across `~`: [Stacks,
Tag 06Z0] presents such an object as `M̃`, but the sheafified case requires `M` itself to be
bounded below, and the library does not have that reflection. The consumers of this file —
part (1) of [Stacks, Tag 0A78] in the affine case, and through it part (2) of that tag and the
coherent half of [Stacks, Tag 0A79] — all supply a sheafification, so nothing is lost to them.

**Why the derived model has to be pinned with priority.**
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePseudoCoherentHomQuasicoherent.lean`
states its results at `CategoryTheory.HasDerivedCategory.standard`, which it selects by a
file-level local instance while importing nothing that reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. This file does reach that file, through
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`, and the
`HasDerivedCategory` instances there are *global*; the local attribute below therefore carries
priority `10000`, as that file's implementation notes require of its importers.

**Three statements, three spellings of pseudo-coherence and of `𝒪_X`-modules.** The hypothesis is
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, which is the spelling [Stacks, Tag 08E5] is
proved at, while [Stacks, Tag 08E7] is stated at
`AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent`; the two are the same
proposition, and
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'` is the translation.
Likewise `AlgebraicGeometry.Scheme.Modules (Spec R)` and
`Stacks.StrictlyPerfect.OXMod (Spec R).toRingedSpace` are the same type but are not interchanged
by typeclass synthesis. Both hazards are met the way
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SideCondition.lean` records: every intermediate
step is introduced by a `have` whose type is *inferred*, so that it elaborates at the spelling
where the instances are found and is only then checked against the next step at default
transparency. Writing any of those types out instead exhausts the `whnf` heartbeat budget.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- `D⁺_QCoh(𝒪_{Spec R})` is closed under isomorphisms. -/
private theorem derivedCategoryBPlus_of_iso {R : CommRingCat.{u}}
    {X Y : DerivedCategory (Spec R).Modules} (e : X ≅ Y)
    (h : DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) X) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) Y :=
  ⟨DerivedCategoryB.isBoundedBelow_of_iso e h.1, fun n =>
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (h.2 n)⟩

/-- **Part (1) of [Stacks, Tag 0A6H] on an affine scheme, for a pseudo-coherent object of
`D(𝒪_{Spec R})`.** Let `E` be a pseudo-coherent object of `D(𝒪_{Spec R})` and let `L` be a
bounded-below object of `D(R)`. Then `R𝓗om_{𝒪_{Spec R}}(E, L̃)` lies in
`D⁺_QCoh(𝒪_{Spec R})`: its cohomology sheaves are quasi-coherent and vanish in sufficiently
negative degrees.

`E` has quasi-coherent cohomology by [Stacks, Tag 08E5], so by [Stacks, Tag 06Z0] there is an
object `K` of `D(R)` and an isomorphism `K̃ ≅ E`; by [Stacks, Tag 08E7] that makes `K`
pseudo-coherent. `AlgebraicGeometry.derivedCategoryBPlus_affinePseudoCoherentDerivedSheafHom`
then puts `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` in `D⁺_QCoh(𝒪_{Spec R})`, and the contravariant variable of
the derived internal Hom carries `K̃ ≅ E` to an isomorphism onto
`R𝓗om_{𝒪_{Spec R}}(E, L̃)`, across which both halves transport. -/
theorem derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E)
    (L : DerivedCategory (ModuleCat.{u} R))
    (hL : DerivedCategoryB.IsBoundedBelow L) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).obj
        ((tilde.functor R).mapDerivedCategory.obj L)) := by
  obtain ⟨K, ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E
    (isQuasicoherentDerived_of_isPseudoCoherent (Spec R) E hE)
  have hK := (isPseudoCoherent_mapDerivedCategory_tilde_iff K).1
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
      (X := (Spec R).toRingedSpace) ((tilde.functor R).mapDerivedCategory.obj K)).2
        (hE.of_iso eK.symm))
  have hL' : (DerivedCategory.TStructure.t).plus L := by
    obtain ⟨n, hn⟩ := hL
    exact ⟨n, (DerivedCategory.isGE_iff L n).2 hn⟩
  have h := derivedCategoryBPlus_affinePseudoCoherentDerivedSheafHom R K L hK hL'
  have e := ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso eK.symm.op).app
    ((tilde.functor R).mapDerivedCategory.obj L)
  exact derivedCategoryBPlus_of_iso e h

/-- **Stacks Project, Tag 0A6H, part (1), on an affine scheme.** For a pseudo-coherent object
`E` of `D(𝒪_{Spec R})`, the derived internal Hom `R𝓗om_{𝒪_{Spec R}}(E, -)` carries
`D⁺_QCoh(𝒪_{Spec R})` into itself.

The second argument is arbitrary in `D⁺_QCoh(𝒪_{Spec R})`, not of the form `L̃`: by
`AlgebraicGeometry.StandardModel.exists_isBoundedBelow_iso_mapDerivedCategory` every object of
`D⁺_QCoh(𝒪_{Spec R})` is isomorphic to `L̃` for a *bounded-below* `L` in `D(R)`, and both halves
of the conclusion transport across that isomorphism. -/
theorem derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent_of_derivedCategoryBPlus
    (R : CommRingCat.{u}) (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E)
    (F : DerivedCategory (Spec R).Modules)
    (hF : DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).obj F) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := StandardModel.exists_isBoundedBelow_iso_mapDerivedCategory R F hF
  have h := derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent R E hE L hL
  have e' := ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).mapIso e
  exact derivedCategoryBPlus_of_iso e' h

end AlgebraicGeometry

end
