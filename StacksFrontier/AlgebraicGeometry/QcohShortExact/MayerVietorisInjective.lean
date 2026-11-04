module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto

/-!
# The degree-zero relative Mayer–Vietoris sequence of a flasque module is short exact

Let `X` be a scheme, let `U` and `V` be opens of `X` and write `Φ_W := j_{W,*} j_W^* F` for an
`𝒪_X`-module `F` (`Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushRestrict`). The
degree-zero relative Mayer–Vietoris short complex

`Φ_{U ⊔ V} ⟶ Φ_U ⊞ Φ_V ⟶ Φ_{U ⊓ V}`

is always left exact: that is
`Stacks.AlgebraicGeometry.RelativeMayerVietoris.mayerVietorisIso`, which exhibits `Φ_{U ⊔ V}` as
the kernel of the difference of the two restrictions. This file proves right exactness under the
hypothesis that all restriction maps of `F` are surjective, and in particular for an injective
`F` by [Stacks, Tag 01EA].

This is the degreewise input to [Stacks, Tag 01EC], relative Mayer–Vietoris: applied to the
terms of an injective resolution of an `𝒪_X`-module it gives the short exact sequence of
complexes from which the long exact sequence of the source is obtained.

## Main results

* `Stacks.AlgebraicGeometry.MayerVietorisInjective.epi_of_surjective_app`: a morphism of
  `𝒪_X`-modules that is surjective on sections over every open is an epimorphism.
* `Stacks.AlgebraicGeometry.MayerVietorisInjective.surjective_res_of_injective`: the restriction
  maps of an injective `𝒪_X`-module are surjective, which is [Stacks, Tag 01EA].
* `Stacks.AlgebraicGeometry.MayerVietorisInjective.epi_mvDiff`: the difference of the two
  restrictions is an epimorphism when all restriction maps of `F` are surjective.
* `Stacks.AlgebraicGeometry.MayerVietorisInjective.epi_mvDiff_of_injective`: the same for an
  injective module.
* `Stacks.AlgebraicGeometry.MayerVietorisInjective.mono_mvRes`: the pair of restrictions is a
  monomorphism.
* `Stacks.AlgebraicGeometry.MayerVietorisInjective.shortExact_mv` and
  `shortExact_mv_of_injective`: the short complex is short exact, for a flasque and for an
  injective module respectively.

## Implementation notes

Epimorphisms of sheaves of modules are not detected on sections in general, but surjectivity on
sections over every open is of course sufficient, and the proof is the definition: two morphisms
out of the target that agree after composition agree on sections over each open, because
sections of the structure morphism form an epimorphism of abelian groups there.

The surjectivity used for `epi_mvDiff` is that of a single restriction map of `F`, namely from
`U ⊓ T` down to `U ⊓ V ⊓ T`; a section of `Φ_{U ⊓ V}` over `T` is lifted to a section of `Φ_U`
over `T` and then pushed into the biproduct along the first inclusion, where
`Stacks.AlgebraicGeometry.RelativeMayerVietoris.mvDiff_app_inl` identifies the image with that
restriction.

The injectivity hypothesis is **not** taken as an instance `[Injective I]` for `I : X.Modules`.
`AlgebraicGeometry.Scheme.Modules` and `SheafOfModules X.ringCatSheaf` are the same type with two
`Category` instances that are distinct as terms, and [Stacks, Tag 01EA] is stated for the latter;
reconciling the two exhausts the instance-search heartbeat budget rather than failing outright.
The hypothesis is therefore spelled in the category [Stacks, Tag 01EA] uses, which is also the
category an injective resolution of an `𝒪_X`-module is produced in.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeMayerVietoris

universe u

namespace Stacks.AlgebraicGeometry.MayerVietorisInjective

variable {X : Scheme.{u}}

/-- **A morphism of `𝒪_X`-modules surjective on sections over every open is an epimorphism.** -/
theorem epi_of_surjective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ T : X.Opens, Function.Surjective (φ.app T)) : Epi φ := by
  refine ⟨fun {P} ψ₁ ψ₂ hψ ↦ Scheme.Modules.hom_ext _ _ fun T ↦ ?_⟩
  have hT : φ.app T ≫ ψ₁.app T = φ.app T ≫ ψ₂.app T := by
    rw [← Scheme.Modules.Hom.comp_app, ← Scheme.Modules.Hom.comp_app, hψ]
  have : Epi (φ.app T) := (AddCommGrpCat.epi_iff_surjective _).2 (h T)
  exact (cancel_epi (φ.app T)).1 hT

/-- **The restriction maps of an injective `𝒪_X`-module are surjective.** This is
[Stacks, Tag 01EA], read for the sheaf of rings of a scheme. -/
theorem surjective_res_of_injective (I : X.Modules)
    (hI : Injective (C := SheafOfModules.{u} X.ringCatSheaf) I) {P Q : X.Opens} (h : Q ≤ P) :
    Function.Surjective (res I h) :=
  let := hI
  Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective X.ringCatSheaf I h

/-- **Right exactness of degree-zero relative Mayer–Vietoris for a flasque module.** If every
restriction map of `F` is surjective then the difference of the two restrictions
`Φ_U ⊞ Φ_V ⟶ Φ_{U ⊓ V}` is an epimorphism: a section over `T` of `Φ_{U ⊓ V}`, that is a section
of `F` over `U ⊓ V ⊓ T`, is the restriction of a section of `F` over `U ⊓ T`, which is a section
of `Φ_U` over `T`. -/
theorem epi_mvDiff (F : X.Modules)
    (hF : ∀ {P Q : X.Opens} (h : Q ≤ P), Function.Surjective (res F h)) (U V : X.Opens) :
    Epi (mvDiff F U V) := by
  refine epi_of_surjective_app _ fun T z ↦ ?_
  obtain ⟨x, hx⟩ := hF (image_preimage_mono (inf_le_left (b := V)) T) z
  exact ⟨(mvInl F U V).app T x, (mvDiff_app_inl F U V T x).trans hx⟩

/-- **Right exactness of degree-zero relative Mayer–Vietoris for an injective module**, the
degreewise input to [Stacks, Tag 01EC]. -/
theorem epi_mvDiff_of_injective (I : X.Modules)
    (hI : Injective (C := SheafOfModules.{u} X.ringCatSheaf) I) (U V : X.Opens) :
    Epi (mvDiff I U V) :=
  epi_mvDiff I (fun h ↦ surjective_res_of_injective I hI h) U V

/-- `mvRes` is a monomorphism: it is `mayerVietorisIso` followed by the kernel inclusion. -/
theorem mono_mvRes (F : X.Modules) (U V : X.Opens) : Mono (mvRes F U V) := by
  rw [← mayerVietorisIso_hom_comp_ι F U V]
  infer_instance

/-- **The degree-zero relative Mayer–Vietoris sequence of a flasque module is short exact.** The
left half is `Stacks.AlgebraicGeometry.RelativeMayerVietoris.mayerVietorisIso`, which identifies
`Φ_{U ⊔ V}` with the kernel of `mvDiff`, and the right half is `epi_mvDiff`. -/
theorem shortExact_mv (F : X.Modules)
    (hF : ∀ {P Q : X.Opens} (h : Q ≤ P), Function.Surjective (res F h)) (U V : X.Opens) :
    (ShortComplex.mk (mvRes F U V) (mvDiff F U V) (mvRes_comp_mvDiff F U V)).ShortExact := by
  have e : ShortComplex.mk (mvRes F U V) (mvDiff F U V) (mvRes_comp_mvDiff F U V) ≅
      ShortComplex.mk (kernel.ι (mvDiff F U V)) (mvDiff F U V) (kernel.condition _) :=
    ShortComplex.isoMk (mayerVietorisIso F U V) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; exact mayerVietorisIso_hom_comp_ι F U V)
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
  exact { exact := ShortComplex.exact_of_iso e.symm (ShortComplex.exact_kernel _)
          mono_f := mono_mvRes F U V
          epi_g := epi_mvDiff F hF U V }

/-- **The degree-zero relative Mayer–Vietoris sequence of an injective module is short exact**,
the degreewise input to [Stacks, Tag 01EC]. -/
theorem shortExact_mv_of_injective (I : X.Modules)
    (hI : Injective (C := SheafOfModules.{u} X.ringCatSheaf) I) (U V : X.Opens) :
    (ShortComplex.mk (mvRes I U V) (mvDiff I U V) (mvRes_comp_mvDiff I U V)).ShortExact :=
  shortExact_mv I (fun h ↦ surjective_res_of_injective I hI h) U V

end Stacks.AlgebraicGeometry.MayerVietorisInjective

end
