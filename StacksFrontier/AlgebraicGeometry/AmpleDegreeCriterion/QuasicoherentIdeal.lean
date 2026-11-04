module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness from vanishing of `H¹` on quasi-coherent ideal sheaves

[Stacks, Tag 0B5P] asks, of a quasi-compact scheme `X` and an invertible `𝒪_X`-module `𝓛`,
that *every quasi-coherent sheaf of ideals* `ℐ ⊆ 𝒪_X` admit an `n ≥ 1` with
`H¹(X, ℐ ⊗ 𝓛^{⊗ n}) = 0`, and concludes that `𝓛` is ample. This file states the criterion at
that hypothesis and identifies the ideal sheaf of a closed subscheme as a submodule of the
structure sheaf, which is what makes the two readings of "quasi-coherent sheaf of ideals"
interchangeable.

## Main results

* `Stacks.ClosedImmersion.mem_range_idealSheaf_app_iff`: **the ideal sheaf of a morphism is the
  kernel ideal, as a submodule of `𝒪_X`.** Over any open `W`, a section of `𝒪_X` is in the
  image of the inclusion `ℐ_a ⟶ 𝒪_X` exactly when it is killed by the map on functions.
* `AlgebraicGeometry.Scheme.IdealSheafData.mem_range_idealSheaf_subschemeι_app_iff`: **the
  identification of an ideal sheaf datum with the ideal sheaf of its subscheme.** For
  `I : X.IdealSheafData` and an affine open `U`, the image on sections of
  `ℐ_{I.subschemeι} ⟶ 𝒪_X` over `U` is exactly `I.ideal U`.
* `AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_isZero_h1_quasicoherentIdeal`:
  **[Stacks, Tag 0B5P]**, with its clause (2) read over quasi-coherent submodules of `𝒪_X`.
* `AlgebraicGeometry.Scheme.Modules.forall_isZero_h1_quasicoherentIdeal_of_isAffine` and
  `AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible`: the hypothesis of the
  criterion is **satisfiable**, on every affine scheme and for every invertible module, and the
  criterion **fires** there.

## The two readings of clause (2), and why they agree

A quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` can be read as a quasi-coherent `𝒪_X`-module
together with a monomorphism into `𝒪_X` — which is the reading below — or as Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData`, a family of ideals `I(U) ≤ Γ(X, U)` indexed by the
affine opens. The criterion of `AmpleDegreeCriterion.Basic` quantifies over a third thing: over
closed immersions `i : Z ⟶ X`, using `Stacks.ClosedImmersion.idealSheaf i`, the kernel of
`𝒪_X ⟶ i_*𝒪_Z`.

The first two readings are reconciled here. `mem_range_idealSheaf_app_iff` computes the image
of `ℐ_a ⟶ 𝒪_X` on sections over an arbitrary open as the kernel of the map on functions, and
Mathlib's `Scheme.IdealSheafData.ker_subschemeι_app` says that kernel is `I.ideal U` on an
affine open; together they say that `I` and `ℐ_{I.subschemeι}` are the same submodule of
`𝒪_X`, affine open by affine open. That was the one step the implementation notes of
`AmpleDegreeCriterion.Basic` named as missing.

The passage from the first reading to the third — which is what the criterion consumes, and so
what carries the tag — needs no identification at all: the ideal sheaf of a closed immersion
*is* a quasi-coherent submodule of `𝒪_X`, by `Stacks.Conormal.isQuasicoherent_idealSheaf` and
`CategoryTheory.Limits.kernel.ι`, so the tag's clause (2) specialises to the criterion's
hypothesis directly. Clause (2) of the tag quantifies over a *larger* family than the
criterion's hypothesis does, so the statement below is weaker than
`isAmple_of_forall_exists_isZero_h1_idealSheaf` and is the tag's own statement; the converse
passage, from an arbitrary quasi-coherent ideal subsheaf to a closed immersion cutting it out,
is not needed and is not proved here.

## Implementation notes

**The sections of the ideal sheaf are computed through the sectionwise kernel.**
`Stacks.ClosedImmersion.idealSheaf` is a categorical `kernel`; `SheafOfModules.kerObj` is the
sectionwise one, whose inclusion is the inclusion of a submodule by
`SheafOfModules.kerIota_val_app`. `Stacks.Conormal.idealSheafKerObjIso` identifies the two as
cone points of the same limit, and `idealSheafKerObjIso_hom_comp_kerIota` records that the
identification respects the two inclusions into `𝒪_X` — which is what upgrades an isomorphism
of modules into an equality of submodules.

**The spelling of the module argument is the one `Stacks.ClosedImmersion.idealSheaf` produces**,
namely over `structureSheafRing X.toRingedSpace`. Binding it there rather
than at `structureSheafRing X.toRingedSpace` is
  forced: at the latter spelling
`CategoryTheory.Limits.kernel.ι` does not elaborate, because `HasZeroMorphisms` is not found
for that category, and the instantiation of the hypothesis at a closed immersion would have to
cross the gap in a `Hom` type rather than at an argument position.

**Quasi-coherence crosses only at argument positions.**
`Stacks.Conormal.isQuasicoherent_idealSheaf` is stated over `C.ringCatSheaf`, and
`AlgebraicGeometry.tensorSheaf_isQuasicoherent` over
  `structureSheafRing`; neither is found by instance
search from the other's spelling, so both are supplied by name with their arguments explicit.

**The affine satisfiability witness needs [Stacks, Tag 01XB] at a second spelling.** Serre
vanishing is available as `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, about
`Hgroup`; the criterion's hypothesis is about `(moduleGlobalSections X).rightDerived 1`. The
crossing is `Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup`, applied
at the top open with `R` the `structureSheafRing` spelling of the structure sheaf.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

variable {Z C : Scheme.{u}} (a : Z ⟶ C) (W : C.Opens)

/-- **The identification of the ideal sheaf with the sectionwise kernel respects the two
inclusions into the structure sheaf.** Both are the `ι` leg of a limit cone over the same
parallel pair, so the unique comparison of cone points commutes with them. -/
public theorem idealSheafKerObjIso_hom_comp_kerIota :
    (Stacks.Conormal.idealSheafKerObjIso a).hom ≫
        SheafOfModules.kerIota (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- **On sections, the inclusion of the ideal sheaf into the structure sheaf is the inclusion of
the kernel ideal.** -/
public theorem kernelι_val_app_apply
    (x : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op W)) :
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom)).val.app
        (op W)).hom x =
      (((Stacks.Conormal.idealSheafSectionsIso a W).hom).hom x).val := by
  rw [← idealSheafKerObjIso_hom_comp_kerIota a]
  rfl

/-- **The ideal sheaf of a morphism of schemes is the kernel ideal, as a submodule of the
structure sheaf.** Over any open `W`, a section of `𝒪_C` lies in the image of
`ℐ_a ⟶ 𝒪_C` exactly when the map on functions kills it.

This is the statement that makes "the kernel of `𝒪_C ⟶ a_*𝒪_Z`" and "the sheaf of ideals cut
out by `a`" the same subsheaf of `𝒪_C`, rather than merely isomorphic modules. -/
public theorem mem_range_idealSheaf_app_iff (y : Γ(C, W)) :
    (∃ x : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op W),
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom)).val.app
          (op W)).hom x = y) ↔
      y ∈ RingHom.ker (a.app W).hom := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [kernelι_val_app_apply a W x]
    exact (((Stacks.Conormal.idealSheafSectionsIso a W).hom).hom x).2
  · intro hy
    refine ⟨((Stacks.Conormal.idealSheafSectionsIso a W).inv).hom ⟨y, hy⟩, ?_⟩
    rw [kernelι_val_app_apply a W]
    exact congrArg Subtype.val
      (ModuleCat.hom_inv_apply (Stacks.Conormal.idealSheafSectionsIso a W) ⟨y, hy⟩)

end Stacks.ClosedImmersion

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- **The sections of the ideal sheaf of `I.subscheme` over an affine open are `I.ideal U`.**
`Stacks.Conormal.idealSheafSectionsIso` computes them as the kernel of the map on functions, and
Mathlib's `Scheme.IdealSheafData.ker_subschemeι_app` says that kernel is `I.ideal U`. -/
public def idealSheafSubschemeιSectionsIso :
    (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).val.obj
        (op (U : X.Opens)) ≅
      ModuleCat.of Γ(X, (U : X.Opens)) ↥(I.ideal U) :=
  Stacks.Conormal.idealSheafSectionsIso I.subschemeι (U : X.Opens) ≪≫
    eqToIso (by rw [Scheme.IdealSheafData.ker_subschemeι_app])

/-- **An ideal sheaf datum is the ideal sheaf of its own closed subscheme, as a submodule of the
structure sheaf.** Over an affine open `U`, the image on sections of
`ℐ_{I.subschemeι} ⟶ 𝒪_X` is exactly `I.ideal U`.

This is the step that the implementation notes of `AmpleDegreeCriterion.Basic` named as the
whole remaining gap between the criterion stated over closed immersions and clause (2) of
[Stacks, Tag 0B5P] read over Mathlib's representation of quasi-coherent ideal sheaves. It is
not used by the criterion itself, whose hypothesis is reached from the tag's by specialisation
and needs no identification; it is what says the two representations describe one object. -/
public theorem mem_range_idealSheaf_subschemeι_app_iff (y : Γ(X, (U : X.Opens))) :
    (∃ x : (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).val.obj
          (op (U : X.Opens)),
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          I.subschemeι.toRingCatSheafHom)).val.app (op (U : X.Opens))).hom x = y) ↔
      y ∈ I.ideal U := by
  rw [Stacks.ClosedImmersion.mem_range_idealSheaf_app_iff I.subschemeι (U : X.Opens) y,
    Scheme.IdealSheafData.ker_subschemeι_app]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Modules

/-- **[Stacks, Tag 0B5P].** Let `X` be a quasi-compact scheme and `𝓛` an invertible
`𝒪_X`-module. If every quasi-coherent submodule `𝒥 ⊆ 𝒪_X` admits an `n ≥ 1` with
`H¹(X, 𝒥 ⊗ 𝓛^{⊗ n}) = 0`, then `𝓛` is ample.

The hypothesis is clause (2) of the tag: a quasi-coherent sheaf of ideals is a quasi-coherent
`𝒪_X`-module with a monomorphism into `𝒪_X`. It is specialised at the ideal sheaf of a closed
immersion, which is such a submodule — quasi-coherent by
`Stacks.Conormal.isQuasicoherent_idealSheaf` and included in `𝒪_X` by `kernel.ι` — and the
criterion `isAmple_of_forall_exists_isZero_h1_idealSheaf` then concludes. -/
@[stacks 0B5P, ega "III 2.6.1" "c) => a), absolute"]
public theorem isAmple_of_forall_isZero_h1_quasicoherentIdeal {X : Scheme.{u}} [CompactSpace X]
    (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hvan : ∀ (J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ι : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)), Mono ι →
      J.IsQuasicoherent → ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((moduleGlobalSections X).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (J)).obj
            ((tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ))))))) :
    IsAmple X L :=
  isAmple_of_forall_exists_isZero_h1_idealSheaf L
    (fun {Z} i hi => hvan _ (kernel.ι _) inferInstance
      (@Stacks.Conormal.isQuasicoherent_idealSheaf Z X i hi))

/-- **Serre vanishing in degree one, at the global-sections spelling.** The first right derived
functor of global sections kills every quasi-coherent module on an affine scheme.

This is [Stacks, Tag 01XB] — stated in the library about `Hgroup` — carried across to
`(moduleGlobalSections X).rightDerived 1` by
`Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup`. -/
@[ega "II 5.2.1" "a ⇒ d, a ⇒ d′"]
public theorem isZero_h1_of_isAffine_of_isQuasicoherent {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj F) :=
  Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
    ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)) (⊤ : X.Opens) 1 F
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊤
      (isAffineOpen_top X) 1 Nat.one_pos)

/-- **A tensor power of an invertible module is quasi-coherent.** Invertibility of the power is
`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`, which concludes the
`AlgebraicGeometry` class of Tag 01CS; `Stacks.SheafOfModules.isQuasicoherent_of_isInvertible`
asks for the `Stacks` one, and `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` is the
crossing. -/
public theorem isQuasicoherent_tensorPower_of_isInvertible {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (n : ℤ) :
    (tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L n).IsQuasicoherent := by
  have hstacks : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L n) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
      (tensorPower_isInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L n)
  exact Stacks.SheafOfModules.isQuasicoherent_of_isInvertible (X := X.toRingedSpace) _

/-- **The hypothesis of [Stacks, Tag 0B5P] is satisfiable.** On an affine scheme it holds for
every invertible module, with `n = 1`: the tensor product of a quasi-coherent module with a
power of an invertible one is quasi-coherent ([Stacks, Tag 01CE]), and `H¹` of a quasi-coherent
module on an affine scheme vanishes ([Stacks, Tag 01XB]).

This is a joint-satisfiability witness for `isAmple_of_forall_isZero_h1_quasicoherentIdeal`:
without one, that theorem could be true because nothing inhabits its hypothesis. It does not
exercise the part of the criterion's proof that glues across a non-affine cover; see
`isAmple_of_isAffine_of_isInvertible` for what it does establish. -/
public theorem forall_isZero_h1_quasicoherentIdeal_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    ∀ (J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ι : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)), Mono ι →
      J.IsQuasicoherent → ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((moduleGlobalSections X).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (J)).obj
            ((tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)))))) := by
  intro J ι _ hJ
  refine ⟨1, le_refl 1, ?_⟩
  have htensor : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (J)).obj
      ((tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((1 : ℕ) : ℤ))))).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace J _ hJ
      (isQuasicoherent_tensorPower_of_isInvertible L ((1 : ℕ) : ℤ))
  exact @isZero_h1_of_isAffine_of_isQuasicoherent X _ _ htensor

/-- **The criterion fires.** Every invertible module on an affine scheme is ample, by
[Stacks, Tag 0B5P] fed from `forall_isZero_h1_quasicoherentIdeal_of_isAffine`.

The conclusion is not new — ampleness on an affine scheme is elementary — and that is the point
of the control: a clean `#print axioms` on
`isAmple_of_forall_isZero_h1_quasicoherentIdeal` says nothing about whether its hypothesis can
be met, and this exhibits a family on which it can and reads off a true conclusion. -/
public theorem isAmple_of_isAffine_of_isInvertible {X : Scheme.{u}} [IsAffine X]
    [CompactSpace X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    IsAmple X L :=
  isAmple_of_forall_isZero_h1_quasicoherentIdeal L
    (forall_isZero_h1_quasicoherentIdeal_of_isAffine L)

end AlgebraicGeometry.Scheme.Modules

end
