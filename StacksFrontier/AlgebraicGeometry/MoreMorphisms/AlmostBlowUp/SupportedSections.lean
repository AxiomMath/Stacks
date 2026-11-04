module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections

/-!
# The ideal of sections supported on a closed subset

The sections of the structure sheaf of a scheme whose germs vanish away from a closed subset
form an ideal sheaf. On an affine open it is the kernel of restriction to the complement.

## Main definitions

* `AlgebraicGeometry.supportedSectionsIdeal` is the ideal of sections supported on a subset.

## Main results

* `AlgebraicGeometry.supportedSectionsIdeal_ideal` identifies that ideal on affine opens with
  the submodule of supported sections.

## Implementation notes

The ideal sheaf is assembled from its values on affine opens with
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals`; the identification on an affine open uses
that the family of supported-section submodules is the kernel of the restriction morphism to
the open complement, which is quasi-compact exactly when that complement is retrocompact.

## References

* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A section restricts to zero on a smaller open exactly when all its germs there vanish. -/
public lemma section_map_eq_zero_iff_germs {X : Scheme.{u}} (F : X.Modules)
    (U W : X.Opens) (hWU : W ≤ U) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE hWU).op s = 0 ↔
      ∀ (x : X) (hx : x ∈ W),
        TopCat.Presheaf.germ F.presheaf U x (hWU hx) s = 0 := by
  refine ⟨fun hs x hx ↦ ?_, fun hs ↦ TopCat.Presheaf.IsSheaf.section_ext F.isSheaf ?_⟩
  · rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hWU) x hx s, hs, map_zero]
  · intro x hx
    have hg : TopCat.Presheaf.germ F.presheaf W x hx
        (F.presheaf.map (homOfLE hWU).op s) = 0 := by
      rw [TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hWU) x hx]
      exact hs x hx
    obtain ⟨V, hxV, iV, iV0, heq⟩ := TopCat.Presheaf.germ_eq F.presheaf x hx hx
      (F.presheaf.map (homOfLE hWU).op s) 0 (by simpa using hg)
    refine ⟨V, iV.le, hxV, ?_⟩
    rw [Subsingleton.elim iV iV0, map_zero] at heq
    exact heq.trans (map_zero _).symm

/-- A section is supported on a closed set exactly when it restricts to zero on the
complement. -/
public lemma supported_iff_restrict_eq_zero {X : Scheme.{u}} (Z : Set X)
    (hZ : IsClosed Z) (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (Scheme.Modules.supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      ((Scheme.Modules.restrictAdjunction
        (Scheme.Opens.ι (X := X) ⟨Zᶜ, hZ.isOpen_compl⟩)).unit.app F).app U s = 0 := by
  let V : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let j : V.toScheme ⟶ X := V.ι
  rw [Scheme.Modules.mem_supportedSectionsSubmodule_iff,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  let W : X.Opens := j ''ᵁ (j ⁻¹ᵁ U)
  have hW : W ≤ U := j.image_preimage_le U
  change (∀ (x : X) (hx : x ∈ U), x ∉ Z →
      TopCat.Presheaf.germ F.presheaf U x hx s = 0) ↔
    F.presheaf.map (homOfLE hW).op s = 0
  rw [section_map_eq_zero_iff_germs F U W hW s]
  have hWmem (x : X) : x ∈ W ↔ x ∈ U ∧ x ∉ Z := by
    change x ∈ Set.image j.base {y : V.toScheme | j.base y ∈ U} ↔ _
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa [j] using hy, y.2⟩
    · exact fun ⟨hxU, hxZ⟩ ↦ ⟨⟨x, hxZ⟩, hxU, rfl⟩
  exact ⟨fun hs x hxW ↦ hs x ((hWmem x).1 hxW).1 ((hWmem x).1 hxW).2,
    fun hs x hxU hxZ ↦ hs x ((hWmem x).2 ⟨hxU, hxZ⟩)⟩

/-- The ideal sheaf of sections of the structure sheaf supported on `Z`. -/
public noncomputable def supportedSectionsIdeal {X : Scheme.{u}} (Z : Set X) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    (Scheme.Modules.supportedSectionsSubmodule Z
      (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1)

/-- On an affine open, the ideal of supported sections is exactly the ideal of
sections whose germs vanish away from `Z`. -/
public theorem supportedSectionsIdeal_ideal {X : Scheme.{u}} (Z : Set X)
    (hZ : IsClosed Z) (hZc : IsRetrocompact Zᶜ) (U : X.affineOpens) :
    (supportedSectionsIdeal Z).ideal U =
      (Scheme.Modules.supportedSectionsSubmodule Z
        (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1) := by
  classical
  let V : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let j : V.toScheme ⟶ X := V.ι
  have : QuasiCompact j := quasiCompact_iff_isSpectralMap.mpr (by
    change IsSpectralMap (Subtype.val : V → X)
    exact (IsRetrocompact_iff_isSpectralMap_subtypeVal).mp hZc)
  let N := Scheme.Modules.supportedSectionsSubmodule Z
    (SheafOfModules.unit X.ringCatSheaf)
  have hN (U : X.affineOpens) : N.toSubmodule.obj (op U.1) =
      RingHom.ker (j.app U.1).hom := by
    ext s
    exact supported_iff_restrict_eq_zero Z hZ (SheafOfModules.unit X.ringCatSheaf) U.1 s
  change (Scheme.IdealSheafData.ofIdeals
      (fun U : X.affineOpens => N.toSubmodule.obj (op U.1))).ideal U =
        N.toSubmodule.obj (op U.1)
  rw [funext hN]
  change j.ker.ideal U = N.toSubmodule.obj (op U.1)
  rw [Scheme.Hom.ker_apply]
  exact (hN U).symm

add_to_stacks 0EV6 "almost_blow_up_square" AlgebraicGeometry.supportedSectionsIdeal_ideal

end AlgebraicGeometry
