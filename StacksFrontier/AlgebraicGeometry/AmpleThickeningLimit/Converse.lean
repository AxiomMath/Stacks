module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningLimit.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Converse
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Affine

/-!
# Stacks Tag 09MW: the converse, with no Noetherian hypothesis

Let `i : Z ⟶ X` be a closed immersion of schemes inducing a homeomorphism of underlying
topological spaces and let `L` be an invertible `𝒪_X`-module. [Stacks, Tag 09MW] asserts

> `i^* L` is ample on `Z` if and only if `L` is ample on `X`.

The implication `L` ample `⟹` `i^* L` ample is
`Stacks.AmpleThickeningLimit.isAmple_modulePullback`. This file proves the converse, with no
hypothesis beyond the source's, and states the biconditional.

## Main results

* `Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph`: the converse
  half of [Stacks, Tag 09MW].
* `Stacks.AmpleThickeningLimit.isAmple_modulePullback_iff_of_isHomeomorph`:
  **[Stacks, Tag 09MW]**, both implications.

## References

* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleThickeningLimit

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The converse half of [Stacks, Tag 09MW].** For a closed immersion `i : Z ⟶ X` inducing a
homeomorphism of underlying spaces and an invertible `𝒪_X`-module `L`, ampleness of `i^* L`
gives ampleness of `L`. There is no Noetherian hypothesis. -/
theorem isAmple_of_isAmple_modulePullback_of_isHomeomorph [IsClosedImmersion i]
    (hi : IsHomeomorph i.base)
    (h : Stacks.Ample.IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L)) :
    Stacks.Ample.IsAmple X L := by
  have hsurj : Surjective i := surjective_of_isHomeomorph_base i hi
  have hX : CompactSpace X :=
    Stacks.AmpleClosedImmersion.compactSpace_of_surjective i inferInstance h.compactSpace
  have hZqs : QuasiSeparatedSpace Z :=
    Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple _ h
  have : QuasiSeparatedSpace X := (quasiSeparatedSpace_congr (hi.homeomorph _)).mp hZqs
  set M := (modulePullback i.toLRSHom.toShHom).obj L
  refine (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr ⟨hX, fun x => ?_⟩
  obtain ⟨J, hJ, U, hU, hcov, ⟨g⟩⟩ :=
    Stacks.AmpleSurjectiveThickening.exists_finite_affine_generator_cover L
  obtain ⟨j₀, hj₀⟩ := hcov x
  obtain ⟨z, rfl⟩ := i.surjective x
  obtain ⟨n, hn, t, haff, hzt, htU⟩ :=
    Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple Z M h z (i ⁻¹ᵁ U j₀) hj₀
  let e : AlgebraicGeometry.Scheme.Modules.tensorPowerModules M (n : ℤ) ≅
      Stacks.Ample.tensorPowModule Z M (n : ℤ) :=
    Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso Z M (n : ℤ)
  set t' := (Stacks.NonvanishingSpelling.sectionsEquiv Z
    (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M (n : ℤ))).symm (e.symm.hom.app ⊤ t)
  have key : Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) _ t' =
      Stacks.AmpleTheory.powNonvanishingOpen Z M n t :=
    TopologicalSpace.Opens.ext
      ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq Z _ _).trans
        (Stacks.Ample.nonvanishingLocus_congr e.symm t))
  obtain ⟨D, hD, s, hs⟩ :=
    Stacks.NilpotentThickeningLift.exists_sections_preimage_nonvanishingOpen_eq
      i L i.surjective U hU hcov g j₀ n hn t' (key.le.trans htU)
  rw [key] at hs
  refine ⟨D, hD, s, (Scheme.Hom.mem_preimage i).mp (hs ▸ hzt), ?_⟩
  exact (Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage
    ⟨inferInstance, i.surjective⟩ _).mpr (hs ▸ haff)

/-- **[Stacks, Tag 09MW].** Let `i : Z ⟶ X` be a closed immersion of schemes inducing a
homeomorphism of underlying topological spaces, and let `L` be an invertible `𝒪_X`-module. Then
`i^* L` is ample on `Z` if and only if `L` is ample on `X`. -/
theorem isAmple_modulePullback_iff_of_isHomeomorph [IsClosedImmersion i]
    (hi : IsHomeomorph i.base) :
    Stacks.Ample.IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔
      Stacks.Ample.IsAmple X L :=
  ⟨isAmple_of_isAmple_modulePullback_of_isHomeomorph i L hi, isAmple_modulePullback i L hi⟩

end Stacks.AmpleThickeningLimit

end
