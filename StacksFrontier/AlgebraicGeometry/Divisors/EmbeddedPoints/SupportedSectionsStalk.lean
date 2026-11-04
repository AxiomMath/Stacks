module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportStalk
public import StacksFrontier.AlgebraicGeometry.TorsionSubsheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LargestSubsheaf

/-!
# Sections supported on the closure of a point

Three auxiliary facts about the submodule of sections supported on a subset and about the largest
quasi-coherent subobject of a subobject.

The first turns the universal property of the largest quasi-coherent subobject of a subobject of
a quasi-coherent module into the plainer statement that the quasi-coherent subobjects below a
given subobject have a greatest element.

The second says that over an affine open, a section whose annihilator-style colon ideal is the
prime of a point `x` is supported on the closure of `x`: at a point `z` of the open outside that
closure the prime of `x` is not contained in the prime of `z`, so some element of the first prime
is a unit in the local ring at `z` and kills the section, forcing its germ there to vanish.

The third says that the submodule of sections supported on a subset has vanishing stalk outside
that subset, since every germ of such a section comes from a section whose germ there is zero.

## Main results

* `Stacks.AlgebraicGeometry.EmbeddedPoints.exists_largest_quasicoherent_subobject`: the
  quasi-coherent subobjects below a given subobject have a greatest element.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.mem_supportedSectionsSubmodule_closure_singleton`: a
  section whose colon ideal is the prime of `x` is supported on the closure of `x`.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.isZero_stalkFunctor_obj_supportedSections`: outside the
  subset, the supported-sections submodule has vanishing stalk.

## References

* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 01QZ](https://stacks.math.columbia.edu/tag/01QZ)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.EmbeddedPoints

variable {X : Scheme.{u}}

/-- Among the quasi-coherent subobjects of a quasi-coherent module contained in a given subobject
there is a greatest one. It is the image in the ambient module of the largest quasi-coherent
subobject of the given subobject. -/
lemma exists_largest_quasicoherent_subobject (F : X.Modules) (hF : F.IsQuasicoherent)
    (G : Subobject F) :
    ∃ L : Subobject F, L ≤ G ∧ (L : X.Modules).IsQuasicoherent ∧
      ∀ P : Subobject F, P ≤ G → (P : X.Modules).IsQuasicoherent → P ≤ L := by
  have := hF
  obtain ⟨H, hH, -⟩ := AlgebraicGeometry.existsUnique_quasicoherentSubobject X F G
  refine ⟨Subobject.mk (H.1.arrow ≫ G.arrow), Subobject.mk_le_of_comm H.1.arrow rfl,
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (H.1.arrow ≫ G.arrow)).symm H.2, fun P hPG hPqc ↦ ?_⟩
  have := hPqc
  obtain ⟨f, hf⟩ := (hH (P : X.Modules)).2 (Subobject.ofLE P G hPG)
  change f ≫ H.1.arrow = Subobject.ofLE P G hPG at hf
  exact Subobject.le_mk_of_comm f
    ((congrArg (fun g ↦ g ≫ G.arrow) hf).trans (Subobject.ofLE_arrow hPG))

/-- Over an affine open, a section whose colon ideal against the zero submodule is the prime ideal
of a point `x` is supported on the closure of `x`.

At a point `z` of the open outside that closure, the prime of `x` is not contained in the prime of
`z`, so there is a section `r` lying in the first and not the second. It annihilates `s` and is a
unit in the local ring at `z`, so the germ of `s` at `z` vanishes. -/
lemma mem_supportedSectionsSubmodule_closure_singleton (F : X.Modules) (U : X.Opens)
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (s : Γ(F, U))
    (hs : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon (Submodule.span Γ(X, U) {s}) =
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    s ∈ (Scheme.Modules.supportedSectionsSubmodule
      (closure ({x} : Set X)) F).toSubmodule.obj (op U) := by
  rw [Scheme.Modules.mem_supportedSectionsSubmodule_iff]
  intro z hz hznot
  set p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  set q := (hU.primeIdealOf ⟨z, hz⟩).asIdeal
  have hpq : ¬ p ≤ q := by
    intro hpq
    refine hznot (specializes_iff_mem_closure.mp ?_)
    have hle : hU.primeIdealOf ⟨x, hx⟩ ≤ hU.primeIdealOf ⟨z, hz⟩ := hpq
    simpa only [hU.fromSpec_primeIdealOf] using
      hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mpr
        ((PrimeSpectrum.le_iff_specializes _ _).mp hle)
  obtain ⟨r, hrp, hrq⟩ := Set.not_subset.mp hpq
  have hrkill : r • s = 0 := by
    have hr : r ∈ (⊥ : Submodule Γ(X, U) Γ(F, U)).colon (Submodule.span Γ(X, U) {s}) := by
      rwa [hs]
    simpa only [Submodule.mem_colon_span_singleton, Submodule.mem_bot] using hr
  let : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hz).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk z) q := hU.isLocalization_stalk ⟨z, hz⟩
  have hu : IsUnit ((algebraMap (Γ(X, U)) (X.presheaf.stalk z)) r) :=
    IsLocalization.map_units (X.presheaf.stalk z) (⟨r, hrq⟩ : q.primeCompl)
  have hsmul := Stacks.AlgebraicGeometry.TorsionSubsheaf.germ_smul F z hz r s
  rw [hrkill, map_zero] at hsmul
  have halg : (X.presheaf.germ U z hz).hom r =
      (algebraMap (Γ(X, U)) (X.presheaf.stalk z)) r := rfl
  rw [halg] at hsmul
  show F.presheaf.germ U z hz s = 0
  exact hu.smul_eq_zero.mp hsmul.symm

/-- Outside the subset on which its sections are supported, the supported-sections submodule has
vanishing stalk: a germ there is represented by a section all of whose germs off the subset are
zero, and the inclusion into the ambient module is injective on stalks. -/
lemma isZero_stalkFunctor_obj_supportedSections (Z : Set X) (F : X.Modules) {x : X}
    (hx : x ∉ Z) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
      (Scheme.Modules.supportedSectionsSubmodule Z F).toSheafOfModules) := by
  let H := Scheme.Modules.supportedSectionsSubmodule Z F
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hz (a : T.obj H.toSheafOfModules) : a = 0 := by
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq H.toSheafOfModules.val.presheaf a
    refine injective_stalkFunctor_map (X := X) (f := H.ι)
      (SheafOfModules.Submodule.instMonoι H) x ?_
    rw [show (T.map H.ι) (TopCat.Presheaf.germ H.toSheafOfModules.val.presheaf U x hxU s) =
        TopCat.Presheaf.germ F.val.presheaf U x hxU (H.ι.val.app (op U) s) from
      TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hxU
        ((SheafOfModules.toSheaf X.ringCatSheaf).map H.ι).hom s,
      show H.ι.val.app (op U) s = s.1 from rfl,
      (Scheme.Modules.mem_supportedSectionsSubmodule_iff Z F U s.1).mp s.2 x hxU hx]
    exact ((T.map H.ι).hom.map_zero).symm
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

end Stacks.AlgebraicGeometry.EmbeddedPoints

end
