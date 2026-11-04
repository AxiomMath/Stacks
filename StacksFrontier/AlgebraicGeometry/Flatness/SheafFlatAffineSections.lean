module

public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteFlatLocallyFree
public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.GradedPieces

/-!
# Flatness of a quasi-coherent module and flatness of its modules of sections

Let `X` be a scheme and `F` a quasi-coherent `𝒪_X`-module. This file records the one-step
equivalence between flatness of `F` as a sheaf of modules — a condition on stalks — and flatness
of every module of sections `Γ(F, U)` over `Γ(X, U)` for `U` an affine open.

The forward direction is the input several arguments want: a Čech or Koszul computation over an
affine open works with the `Γ(X, U)`-module `Γ(F, U)` and needs it to be flat, while the
hypothesis available is flatness of the sheaf.

## Main results

* `AlgebraicGeometry.flat_sections_of_isFlat`: a flat quasi-coherent module has flat modules of
  sections over affine opens.
* `AlgebraicGeometry.isFlat_of_forall_flat_sections`: the converse.
* `AlgebraicGeometry.isFlat_iff_forall_flat_sections`: the two combined.
* `AlgebraicGeometry.flat_sections_structureSheafModule` and
  `AlgebraicGeometry.nontrivial_sections_structureSheafModule_specInt`: a named inhabitant of the
  forward statement at a module whose sections are not the zero module.

## Implementation notes

Both directions go through `AlgebraicGeometry.isFlatOver_tfae`, the affine-local criterion of
Stacks Tag 01U4 for an arbitrary morphism, specialised to the identity. Flatness over the
identity is flatness of the sheaf (`AlgebraicGeometry.isFlatOver_id_iff_isFlat`), and the
comparison ring map that the criterion restricts scalars along is the identity for the identity
morphism (`AlgebraicGeometry.Scheme.Hom.id_appLE_hom`), so the scalar action in the criterion is
the plain `Γ(X, U)`-action on `Γ(F, U)`.

Quasi-coherence is not decoration: the criterion of Tag 01U4 is stated for a quasi-coherent
module, and for a general sheaf of modules on a general ringed space flatness of the stalks says
nothing about the modules of sections. That general statement is exactly the one recorded as
false in the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Modules/FlatTensorShortExact.lean`; that note is about a
ringed site with no affine opens and no quasi-coherence, and remains correct. What is proved
here is the scheme-theoretic statement, which is a different assertion.

No `@[stacks 01U4]` attribute is added below. The tag's covering set is
`AlgebraicGeometry.isFlatOver_tfae`, which already states it for an arbitrary morphism of
schemes; everything here is that theorem at `𝟙 X`, so a second registration would add nothing
to the tag's coverage.

## References

* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A flat quasi-coherent module has flat sections over every affine open.** The stalkwise
flatness of `F` is flatness over the identity morphism of `X`, and the affine-local criterion of
Stacks Tag 01U4 for the identity reads off flatness of `Γ(F, U)` over `Γ(X, U)`. -/
theorem flat_sections_of_isFlat {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Flat Γ(X, U) Γ(F, U) :=
  flat_sections_of_isFlatOver_id F ((isFlatOver_id_iff_isFlat F).mpr hF) U hU

/-- **A quasi-coherent module with flat sections over every affine open is flat.** The affine
opens of `X` cover it, and each is covered by itself, so the affine-covering clause of Stacks
Tag 01U4 for the identity morphism is exactly the hypothesis. -/
theorem isFlat_of_forall_flat_sections {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ U : X.Opens, IsAffineOpen U → Module.Flat Γ(X, U) Γ(F, U)) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F := by
  rw [← isFlatOver_id_iff_isFlat]
  refine ((isFlatOver_tfae (𝟙 X : X ⟶ X) F).out 4 1).mp ?_
  refine ⟨X.affineOpens, fun V => V.1, iSup_affineOpens_eq_top X, fun V => V.2, fun V => ?_⟩
  refine ⟨PUnit.{u + 1}, fun _ => V.1, by simp, fun _ => V.2, fun _ => ?_⟩
  intro hUV
  show @Module.Flat _ _ _ _
    (Module.compHom Γ(F, V.1) ((𝟙 X : X ⟶ X).appLE V.1 V.1 hUV).hom)
  rw [Scheme.Hom.id_appLE_hom]
  exact h V.1 V.2

/-- **Stacks Tag 01U4 for the identity morphism.** A quasi-coherent `𝒪_X`-module is flat exactly
when its module of sections over every affine open is flat over the functions on that open. -/
theorem isFlat_iff_forall_flat_sections {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] :
    AlgebraicGeometry.SheafOfModules.IsFlat
        (C := TopologicalSpace.Opens X.toTopCat)
        (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.Flat Γ(X, U) Γ(F, U) :=
  ⟨fun hF _ hU => flat_sections_of_isFlat F hF hU, isFlat_of_forall_flat_sections F⟩

/-- The structure sheaf of a scheme, read as a module over itself, is flat. -/
theorem isFlat_structureSheafModule (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) (structureSheafModule X) :=
  (isFlatOver_id_iff_isFlat _).mp (isFlatOver_structureSheafModule (𝟙 X))

/-- A named inhabitant of `AlgebraicGeometry.flat_sections_of_isFlat`: the structure sheaf of a
scheme, read as a module over itself, is flat and quasi-coherent, so its sections over an affine
open are a flat module. -/
theorem flat_sections_structureSheafModule {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) :
    Module.Flat Γ(X, U) Γ(structureSheafModule X, U) :=
  flat_sections_of_isFlat (structureSheafModule X) (isFlat_structureSheafModule X) hU

/-- Non-degeneracy of `AlgebraicGeometry.flat_sections_structureSheafModule`: the module whose
flatness it asserts is not the zero module. Over `Spec ℤ` the sections of the structure sheaf
module over the whole space are the integers. -/
theorem nontrivial_sections_structureSheafModule_specInt :
    Nontrivial Γ(structureSheafModule (Spec (CommRingCat.of ℤ)),
      (⊤ : (Spec (CommRingCat.of ℤ)).Opens)) :=
  have : Nontrivial Γ(Spec (CommRingCat.of ℤ), (⊤ : (Spec (CommRingCat.of ℤ)).Opens)) :=
    (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  ‹_›

end AlgebraicGeometry

end
