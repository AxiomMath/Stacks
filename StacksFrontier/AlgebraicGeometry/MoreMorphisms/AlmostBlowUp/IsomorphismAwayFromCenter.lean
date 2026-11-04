module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.SupportedSections

/-!
# Closed subschemes that are isomorphisms away from a closed subset

For a closed subset `Z` of a scheme `X`, the ideal sheaf of sections of the structure sheaf
supported on `Z` is the kernel of the inclusion of the open complement of `Z`. Consequently the
closed subscheme cut out by a quasi-coherent ideal sheaf `J` restricts to an isomorphism over the
complement of `Z` exactly when `J` is contained in that ideal sheaf, so the supported-sections
ideal cuts out the largest closed subscheme that is an isomorphism away from `Z`.

That is what makes the modification of an almost blowup square an isomorphism away from the
centre of the square: the modification agrees, after removing the sections supported on the
exceptional subscheme, with the blowup of the centre, and both the removal and the blowup are
isomorphisms over the complement of the centre.

## Main results

* `AlgebraicGeometry.supportedSectionsIdeal_eq_complementKernel`: the ideal of sections supported
  on a closed set is the kernel of the inclusion of its open complement.
* `AlgebraicGeometry.restrict_isIso_iff_comap_bot`: the closed immersion cut out by an ideal sheaf
  restricts to an isomorphism over an open exactly when the inverse-image ideal there is trivial.
* `AlgebraicGeometry.isIso_restrict_iff_le_supportedSectionsIdeal`: that restriction is an
  isomorphism over the complement of a closed set exactly when the ideal sheaf is contained in the
  ideal of sections supported on that set.
* `AlgebraicGeometry.isIso_restrict_compl_support`: the modification of an almost blowup square is
  an isomorphism over the complement of the centre of the square.

## Implementation notes

`AlgebraicGeometry.restrict_isIso_iff_comap_bot` compares the closed subscheme of the
inverse-image ideal with the restriction of the closed immersion along the canonical isomorphism
between the inverse image of an ideal sheaf and the pullback of its closed subscheme; both
directions then reduce to the criterion that a closed immersion is an isomorphism exactly when its
kernel vanishes.

`AlgebraicGeometry.isIso_restrict_compl_support` cancels the supported-sections factor out of the
identification that the almost blowup square provides. The identification is of schemes over `X`,
so restricting it over the complement of the centre leaves a commuting triangle in which two of
the three morphisms are known to be isomorphisms: the blowup morphism by
`AlgebraicGeometry.isIso_blowUp_restrict_compl_support`, and the supported-sections closed
immersion by `AlgebraicGeometry.isIso_restrict_iff_le_supportedSectionsIdeal` applied to the
exceptional subscheme, whose complement is the inverse image of the complement of the centre.

## References

* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The ideal of sections supported on a closed set is the kernel of the inclusion of its open
complement. -/
public theorem supportedSectionsIdeal_eq_complementKernel {X : Scheme.{u}} (Z : Set X)
    (hZ : IsClosed Z) :
    supportedSectionsIdeal Z =
      (Scheme.Opens.ι (X := X) ⟨Zᶜ, hZ.isOpen_compl⟩).ker := by
  let U : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let j : U.toScheme ⟶ X := U.ι
  let F := SheafOfModules.unit X.ringCatSheaf
  let N := Scheme.Modules.supportedSectionsSubmodule Z F
  have hN (V : X.affineOpens) : N.toSubmodule.obj (op V.1) =
      RingHom.ker (j.app V.1).hom := by
    ext s
    show s ∈ (Scheme.Modules.supportedSectionsSubmodule Z
      (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op V.1) ↔
        (j.app V.1).hom s = 0
    convert supported_iff_restrict_eq_zero Z hZ
      (SheafOfModules.unit X.ringCatSheaf) V.1 s using 1 <;> rfl
  show Scheme.IdealSheafData.ofIdeals
      (fun V : X.affineOpens => N.toSubmodule.obj (op V.1)) =
    Scheme.IdealSheafData.ofIdeals
      (fun V : X.affineOpens => RingHom.ker (j.app V.1).hom)
  exact congrArg _ (funext hN)

/-- The closed immersion cut out by an ideal sheaf restricts to an isomorphism over an open
exactly when the inverse-image ideal on that open is trivial. -/
public theorem restrict_isIso_iff_comap_bot {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.Opens) :
    IsIso (J.subschemeι ∣_ U) ↔ J.comap U.ι = ⊥ := by
  let e : (J.comap U.ι).subscheme ≅ (J.subschemeι ⁻¹ᵁ U).toScheme :=
    J.comapIso U.ι ≪≫ CategoryTheory.Limits.pullbackSymmetry U.ι J.subschemeι ≪≫
      pullbackRestrictIsoRestrict J.subschemeι U
  have he : e.hom ≫ (J.subschemeι ∣_ U) = (J.comap U.ι).subschemeι := by
    simp [e]
  rw [← isIso_comp_left_iff e.hom (J.subschemeι ∣_ U), he,
    IsClosedImmersion.isIso_iff_ker_eq_bot, Scheme.IdealSheafData.ker_subschemeι]

/-- **Stacks Project, Tag 0EV8.** The closed subscheme cut out by an ideal sheaf is an
isomorphism over the complement of a closed set exactly when the ideal sheaf is contained in the
ideal of sections supported on that set. -/
@[stacks 0EV8 "(1) iff (2)"]
public theorem isIso_restrict_iff_le_supportedSectionsIdeal {X : Scheme.{u}} (Z : Set X)
    (hZ : IsClosed Z) (J : X.IdealSheafData) :
    IsIso (J.subschemeι ∣_ (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens)) ↔
      J ≤ supportedSectionsIdeal Z := by
  rw [restrict_isIso_iff_comap_bot, supportedSectionsIdeal_eq_complementKernel Z hZ,
    ← Scheme.IdealSheafData.map_bot (Scheme.Opens.ι (X := X) ⟨Zᶜ, hZ.isOpen_compl⟩),
    Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff]

/-- **Stacks Project, Tag 0EV6.** The modification of an almost blowup square is an isomorphism
over the complement of the centre of the square. -/
@[stacks 0EV6 "isomorphism_away_from_center"]
public theorem isIso_restrict_compl_support {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) (hb : IsAlmostBlowUpSquare I b) :
    IsIso (b ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)) := by
  let U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  let E := I.comap b
  let J := supportedSectionsIdeal (E.support : Set X')
  let V : X'.Opens := ⟨E.supportᶜ, E.support.isClosed.isOpen_compl⟩
  have hV : b ⁻¹ᵁ U = V := by
    apply Opens.ext
    ext x
    simp [U, V, E, Scheme.IdealSheafData.support_comap]
  have hJ : IsIso (J.subschemeι ∣_ V) := by
    simpa [J, V] using (isIso_restrict_iff_le_supportedSectionsIdeal
      (E.support : Set X') E.support.isClosed J).2 le_rfl
  obtain ⟨e⟩ := hb.blowUp
  have he : e.hom.left ≫ blowUpToBase I = J.subschemeι ≫ b := Over.w e.hom
  have hleft : IsIso e.hom.left := (Over.forget X).map_isIso e.hom
  have hbase : IsIso (blowUpToBase I ∣_ U) := isIso_blowUp_restrict_compl_support I
  have hleft' : IsIso (e.hom.left ∣_ (blowUpToBase I ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hleft _
  have hf : IsIso ((J.subschemeι ≫ b) ∣_ U) := by
    rw [← he, morphismRestrict_comp]
    exact IsIso.comp_isIso' hleft' hbase
  have hJ' : IsIso (J.subschemeι ∣_ (b ⁻¹ᵁ U)) := by rwa [hV]
  rw [morphismRestrict_comp] at hf
  exact (isIso_comp_left_iff (J.subschemeι ∣_ (b ⁻¹ᵁ U)) (b ∣_ U)).mp hf

end AlgebraicGeometry

end
