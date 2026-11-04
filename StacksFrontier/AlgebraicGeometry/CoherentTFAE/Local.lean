module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Affine

/-!
# Finite type is local on a scheme, and the affine-open form of a quasi-coherent module

This file assembles the scheme-level half of the affine dictionary behind [Stacks, Tag 01XZ].

Pinned Mathlib has `SheafOfModules.IsQuasicoherent.of_coversTop` but no analogue for
`SheafOfModules.IsFiniteType`, and no `SheafOfModules.LocalGeneratorsData.bind`. The locality
statement proved here needs neither: a `LocalGeneratorsData` already takes its covering in the
base site, so finite generating sections of the *restrictions* `M.restrict (U i).ι` to the
members of an open covering assemble into one directly, once they are transported from the open
subscheme to the slice site.

The second half identifies, for a quasi-coherent module `F` on a scheme and an affine open `U`,
the restriction `F|_U` with the pullback along `U ≅ Spec Γ(X, U)` of the `tilde` of a
`Γ(X, U)`-module, namely the global sections of `F|_U` transported to the spectrum. This is the
shape in which [Stacks, Tag 01XZ] (4) and (5) are stated, and Mathlib records no such
identification for a general affine open of a general scheme.

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsRestrict`: generating sections
  restrict along an open immersion, with the same index type.
* `Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsOver`: generating sections of
  `M.restrict V.ι` give generating sections of `M.over V`, with the same index type.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections`: **finite
  type is local on a scheme**.
* `Stacks.AlgebraicGeometry.CoherentTFAE.specModule`,
  `Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde`: the affine-open form of a
  quasi-coherent module.
* `Stacks.AlgebraicGeometry.CoherentTFAE.finite_moduleSpecΓ_of_generatingSections`: on a
  spectrum, finitely many generating sections of a quasi-coherent module make its global
  sections a finite module.
* `Stacks.AlgebraicGeometry.CoherentTFAE.finite_specModule_of_generatingSections`: the two
  previous items combined, for an affine open of an arbitrary scheme.

## Implementation notes

The transports go through `Stacks.AlgebraicGeometry.AffinePushforward.overInverseIso` and
`overInverseUnitIso`, which were built for presentations; the same two isomorphisms serve
generating sections, because `SheafOfModules.GeneratingSections.map` asks exactly for a
colimit-preserving functor together with an identification of the structure sheaves.

Every `Epi`/`IsIso` argument is passed explicitly and positionally. See the implementation note
of the `Affine` file in this directory for why instance synthesis cannot find them.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

variable {X Y Z : Scheme.{u}}

/-! ### Transport of generating sections -/

/-- **Generating sections restrict along an open immersion**: generating sections of `M` give
generating sections of `M.restrict f`, with the same index type. -/
noncomputable def generatingSectionsRestrict (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (σ : M.GeneratingSections) : (M.restrict f).GeneratingSections :=
  @GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ σ (Scheme.Modules.restrictFunctor f)
    (inferInstance : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f))
    (Scheme.Modules.restrictUnitIso f).symm

/-- The index type of `generatingSectionsRestrict f σ` is that of `σ`. -/
@[simp]
theorem generatingSectionsRestrict_I (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (σ : M.GeneratingSections) : (generatingSectionsRestrict f σ).I = σ.I :=
  rfl

/-- **Generating sections of `M.restrict V.ι` give generating sections of `M.over V`**, with
the same index type. -/
noncomputable def generatingSectionsOver (V : X.Opens) (M : X.Modules)
    (σ : (M.restrict V.ι).GeneratingSections) : (M.over V).GeneratingSections :=
  (GeneratingSections.equivOfIso (AffinePushforward.overInverseIso V M)).symm
    (@GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ σ (Scheme.Modules.overEquiv V).inverse
      (inferInstance : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv V).inverse)
      (AffinePushforward.overInverseUnitIso V))

/-- The index type of `generatingSectionsOver V M σ` is that of `σ`. -/
@[simp]
theorem generatingSectionsOver_I (V : X.Opens) (M : X.Modules)
    (σ : (M.restrict V.ι).GeneratingSections) : (generatingSectionsOver V M σ).I = σ.I :=
  rfl

/-! ### Finite type is local on a scheme -/

/-- Local generators of `M` assembled from generating sections of its restrictions to the
members of an open covering. -/
noncomputable def localGeneratorsDataOfRestrict (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : IsOpenCover U) (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections) :
    M.LocalGeneratorsData where
  I := I
  X := U
  coversTop := (Opens.coversTop_iff _ U).mpr hU
  generators i := generatingSectionsOver (U i) M (σ i)

/-- **Finite type is local on a scheme.** If the restriction of `M` to each member of an open
covering is generated by finitely many sections, then `M` is of finite type. -/
theorem isFiniteType_of_restrict_generatingSections (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : IsOpenCover U) (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections)
    (hσ : ∀ i, Finite (σ i).I) : M.IsFiniteType := by
  have hd : (localGeneratorsDataOfRestrict M U hU σ).IsFiniteType := by
    constructor
    intro i
    exact ⟨hσ i⟩
  constructor
  exact ⟨localGeneratorsDataOfRestrict M U hU σ, hd⟩

/-! ### The affine-open form of a quasi-coherent module -/

/-- Restricting along an isomorphism and back is the identity. -/
noncomputable def restrictIsoSelf (e : Y ≅ Z) (G : Y.Modules) :
    (G.restrict e.inv).restrict e.hom ≅ G :=
  ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app G).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app G ≪≫
    Scheme.Modules.restrictFunctorId.app G

/-- The module `F|_U`, read on `Spec Γ(X, U)` through `hU.isoSpec`, for `U` an affine open. -/
noncomputable abbrev specRestrict (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    (Spec Γ(X, U)).Modules :=
  (F.restrict U.ι).restrict hU.isoSpec.inv

/-- **The `Γ(X, U)`-module attached to a module `F` and an affine open `U`**: the global sections
of `F|_U` read on `Spec Γ(X, U)`. For quasi-coherent `F` this is the module `M` with
`F|_U = M^~` of [Stacks, Tag 01XZ] (4). -/
noncomputable abbrev specModule (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    ModuleCat.{u} Γ(X, U) :=
  moduleSpecΓFunctor.obj (specRestrict F hU)

/-- **A quasi-coherent module is, on an affine open, the pullback of a `tilde`.**
This is the shape of [Stacks, Tag 01XZ] (4): over an affine open `U`, `F|_U` is `M^~` for the
`Γ(X, U)`-module `M = specModule F hU`, transported along the canonical isomorphism
`U ≅ Spec Γ(X, U)`. -/
noncomputable def restrictIsoSpecTilde (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    [F.IsQuasicoherent] :
    F.restrict U.ι ≅
      (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde (specModule F hU)) :=
  have : (specRestrict F hU).IsQuasicoherent := inferInstance
  (restrictIsoSelf hU.isoSpec (F.restrict U.ι)).symm ≪≫
    (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
      (asIso (specRestrict F hU).fromTildeΓ).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _

/-! ### Finiteness of the global sections -/

/-- **On a spectrum, finitely many generating sections of a quasi-coherent module make its
global sections a finite module.** -/
theorem finite_moduleSpecΓ_of_generatingSections {A : CommRingCat.{u}} (N : (Spec A).Modules)
    [N.IsQuasicoherent] (σ : N.GeneratingSections) [Finite σ.I] :
    Module.Finite A (moduleSpecΓFunctor.obj N) := by
  have hiso : IsIso N.fromTildeΓ := inferInstance
  have hp : Epi (σ.π ≫ (asIso N.fromTildeΓ).inv) :=
    @epi_comp _ _ _ _ _ _ σ.epi _
      (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (asIso N.fromTildeΓ)))
  exact finite_of_epi_free_tilde _ (σ.π ≫ (asIso N.fromTildeΓ).inv) hp

/-- **Finitely many generating sections of `F|_U` make `specModule F hU` a finite module**, for
`U` an affine open of an arbitrary scheme and `F` quasi-coherent. -/
theorem finite_specModule_of_generatingSections (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) [F.IsQuasicoherent] (σ : (F.restrict U.ι).GeneratingSections)
    [Finite σ.I] : Module.Finite Γ(X, U) (specModule F hU) :=
  have : (specRestrict F hU).IsQuasicoherent := inferInstance
  have hfin : Finite (generatingSectionsRestrict hU.isoSpec.inv σ).I := ‹Finite σ.I›
  @finite_moduleSpecΓ_of_generatingSections _ _ ‹_›
    (generatingSectionsRestrict hU.isoSpec.inv σ) hfin

end Stacks.AlgebraicGeometry.CoherentTFAE

end
