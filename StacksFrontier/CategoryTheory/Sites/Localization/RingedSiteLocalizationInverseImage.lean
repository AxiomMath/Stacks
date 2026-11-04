module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf of a localized ringed site is the inverse image

Let `(C, O)` be a ringed site and `U` an object of `C`. `AlgebraicGeometry.RingedSite.over`
equips the slice site `C/U` with the restriction `O.over U` as structure sheaf, and
`AlgebraicGeometry.RingedSite.overMorphismOfTopoi` is the localization morphism of topoi
`π : Sh(C/U) ⟶ Sh(C)`, whose inverse image is restriction along `Over.forget U`. This file
identifies the canonical inverse image `π⁻¹O` of the structure sheaf, as a sheaf of rings, with
that restriction, and gives the structure map of `π` in inverse-image and direct-image form.

The sections of `π⁻¹O` over `V ⟶ U` are the sections of `O` over `V`, and the identification is
the identity on underlying sheaves of sets, as is the structure map of the localization. The
direct-image form of the structure map is the adjunct of the inverse-image form under the
adjunction `π⁻¹ ⊣ π_*` on sheaves of rings.

Everything is stated both for the underlying sheaf of rings of the structure sheaf and for the
`CommRingCat`-valued structure sheaf itself.

## Main definitions

* `AlgebraicGeometry.RingedSite.overRingFsharp`: the structure map of the localization in the
  restriction presentation — the identity.
* `AlgebraicGeometry.RingedSite.overInverseImageRingIso`: the identification of the canonical
  ring inverse image `π⁻¹O` with the restriction of `O` to the slice.
* `AlgebraicGeometry.RingedSite.overInverseImageFsharp`: the structure map of the localization
  with the canonical ring inverse image as its domain.
* `AlgebraicGeometry.RingedSite.overFsharpAdjoint`: the same structure map in direct-image
  form, `O ⟶ π_*O_{C/U}`.
* `AlgebraicGeometry.RingedSite.overInverseImageCommRingIso`,
  `.overInverseImageCommRingFsharp`, `.overCommRingFsharpAdjoint`: the same three objects for
  the `CommRingCat`-valued structure sheaf.

## Main results

* `AlgebraicGeometry.RingedSite.overInverseImageRingIso_ringSheafMap` and
  `.overInverseImageFsharp_ringSheafMap`: the identification and the structure map are the
  identity on underlying sheaves of sets.
* `AlgebraicGeometry.RingedSite.overInverseImageFsharp_eq` and
  `.overInverseImageRingIso_inv_comp_overInverseImageFsharp`: the structure map is the
  identification, and identifying the inverse image with restriction recovers the identity
  structure map.
* `AlgebraicGeometry.RingedSite.overFsharpAdjoint_inverseImage`: the ring adjunction recovers
  exactly the inverse-image form of the structure map from the direct-image form.

## References

* [Stacks Project, Tag 00Y0](https://stacks.math.columbia.edu/tag/00Y0)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w}) (U : X.C)

/-- The structure map of the localization at `U`, read on sheaves of rings and in the
presentation of the localized structure sheaf as the restriction of `O`: it is the identity. -/
noncomputable def overRingFsharp :
    ((Over.forget U).sheafPushforwardContinuous RingCat.{max u v w} (X.J.over U) X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) :=
  𝟙 _

/-- The structure map of the localization is the identity map. -/
@[simp]
theorem overRingFsharp_eq : X.overRingFsharp U = 𝟙 _ := rfl

/-- The canonical inverse image of the structure sheaf of a ringed site under the localization
morphism at `U`, as a sheaf of rings, is its restriction to the slice site over `U`. -/
noncomputable def overInverseImageRingIso :
    (inverseImageRingFunctor (X.overMorphismOfTopoi U)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) :=
  restrictionRingIso (X.J.over U) X.J (Over.forget U) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The identification of the canonical ring inverse image with the restriction is the identity
on underlying sheaves of sets. -/
@[simp]
theorem overInverseImageRingIso_ringSheafMap :
    (sheafCompose (X.J.over U) (forget RingCat.{max u v w})).map
        (X.overInverseImageRingIso U).hom =
      𝟙 ((sheafCompose (X.J.over U) (forget RingCat.{max u v w})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) :=
  rfl

/-- The structure map of the localization, with the canonical ring inverse image of the
structure sheaf as its domain. -/
noncomputable def overInverseImageFsharp :
    (inverseImageRingFunctor (X.overMorphismOfTopoi U)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) :=
  (X.overInverseImageRingIso U).hom ≫ X.overRingFsharp U

/-- Under the identification with restriction, the structure map is the identification
itself. -/
@[simp]
theorem overInverseImageFsharp_eq :
    X.overInverseImageFsharp U = (X.overInverseImageRingIso U).hom :=
  Category.comp_id _

/-- Identifying the canonical ring inverse image with the restriction recovers the identity
structure map. -/
@[simp]
theorem overInverseImageRingIso_inv_comp_overInverseImageFsharp :
    (X.overInverseImageRingIso U).inv ≫ X.overInverseImageFsharp U = X.overRingFsharp U := by
  rw [overInverseImageFsharp_eq]
  exact Iso.inv_hom_id _

/-- The structure map of the localization is the identity after forgetting the ring
operations. -/
@[simp]
theorem overInverseImageFsharp_ringSheafMap :
    (sheafCompose (X.J.over U) (forget RingCat.{max u v w})).map
        (X.overInverseImageFsharp U) =
      𝟙 ((sheafCompose (X.J.over U) (forget RingCat.{max u v w})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) := by
  rw [overInverseImageFsharp_eq, overInverseImageRingIso_ringSheafMap]

/-- The structure map of the localization in direct-image form, `O ⟶ π_*O_{C/U}`: the adjunct
of `overInverseImageFsharp` under the adjunction `π⁻¹ ⊣ π_*` on sheaves of rings. -/
noncomputable def overFsharpAdjoint :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (pushforwardRingFunctor (X.overMorphismOfTopoi U)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) :=
  (ringImageAdjunction (X.overMorphismOfTopoi U)).homEquiv _ _ (X.overInverseImageFsharp U)

/-- The ring adjunction recovers exactly the inverse-image form of the localization structure
map from its direct-image form. -/
@[simp]
theorem overFsharpAdjoint_inverseImage :
    ((ringImageAdjunction (X.overMorphismOfTopoi U)).homEquiv _ _).symm
        (X.overFsharpAdjoint U) = X.overInverseImageFsharp U :=
  ((ringImageAdjunction (X.overMorphismOfTopoi U)).homEquiv _ _).symm_apply_apply _

/-- The direct-image form of the structure map is the unit `O ⟶ π_*π⁻¹O` followed by the direct
image of the identification with restriction. -/
theorem overFsharpAdjoint_eq :
    X.overFsharpAdjoint U =
      ringUnit (X.overMorphismOfTopoi U) (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≫
        pullbackRingSheafMap X.J (X.overMorphismOfTopoi U).pushforward
          (X.overInverseImageFsharp U) :=
  (ringImageAdjunction (X.overMorphismOfTopoi U)).homEquiv_unit _ _ _

/-! ## The same, for the `CommRingCat`-valued structure sheaf -/

/-- The canonical inverse image of the `CommRingCat`-valued structure sheaf of a ringed site
under the localization morphism at `U` is its restriction to the slice site over `U`. -/
noncomputable def overInverseImageCommRingIso :
    (inverseImageCommRingFunctor (X.overMorphismOfTopoi U)).obj X.O ≅ X.O.over U :=
  restrictionCommRingIso (X.J.over U) X.J (Over.forget U) X.O

/-- The identification of the canonical inverse image with the restriction is the identity on
underlying sheaves of sets. -/
@[simp]
theorem overInverseImageCommRingIso_hom_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{max u v w})).map
        (X.overInverseImageCommRingIso U).hom =
      𝟙 ((sheafCompose (X.J.over U) (forget CommRingCat.{max u v w})).obj (X.O.over U)) :=
  rfl

/-- The structure map of the localization, with the canonical inverse image of the structure
sheaf as its domain and the structure sheaf of the localized ringed site as its codomain. -/
noncomputable def overInverseImageCommRingFsharp :
    (inverseImageCommRingFunctor (X.overMorphismOfTopoi U)).obj X.O ⟶ (X.over U).O :=
  (X.overInverseImageCommRingIso U).hom ≫ X.overFsharp U

/-- Under the identification with restriction, the structure map is the identification
itself. -/
@[simp]
theorem overInverseImageCommRingFsharp_eq :
    X.overInverseImageCommRingFsharp U = (X.overInverseImageCommRingIso U).hom :=
  Category.comp_id _

/-- Identifying the canonical inverse image with the restriction recovers the identity
structure map. -/
@[simp]
theorem overInverseImageCommRingIso_inv_comp_overInverseImageCommRingFsharp :
    (X.overInverseImageCommRingIso U).inv ≫ X.overInverseImageCommRingFsharp U =
      X.overFsharp U := by
  rw [overInverseImageCommRingFsharp_eq]
  exact Iso.inv_hom_id _

/-- The structure map of the localization is the identity after forgetting the ring
operations. -/
@[simp]
theorem overInverseImageCommRingFsharp_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{max u v w})).map
        (X.overInverseImageCommRingFsharp U) =
      𝟙 ((sheafCompose (X.J.over U) (forget CommRingCat.{max u v w})).obj (X.O.over U)) := by
  rw [overInverseImageCommRingFsharp_eq, overInverseImageCommRingIso_hom_forget]

/-- The structure map of the localization in direct-image form, `O ⟶ π_*O_{C/U}`: the adjunct
of `overInverseImageCommRingFsharp` under the adjunction `π⁻¹ ⊣ π_*` on sheaves of commutative
rings. -/
noncomputable def overCommRingFsharpAdjoint :
    X.O ⟶ (pushforwardCommRingFunctor (X.overMorphismOfTopoi U)).obj (X.over U).O :=
  (commRingImageAdjunction (X.overMorphismOfTopoi U)).homEquiv _ _
    (X.overInverseImageCommRingFsharp U)

/-- The adjunction recovers exactly the inverse-image form of the localization structure map
from its direct-image form. -/
@[simp]
theorem overCommRingFsharpAdjoint_inverseImage :
    ((commRingImageAdjunction (X.overMorphismOfTopoi U)).homEquiv _ _).symm
        (X.overCommRingFsharpAdjoint U) = X.overInverseImageCommRingFsharp U :=
  ((commRingImageAdjunction (X.overMorphismOfTopoi U)).homEquiv _ _).symm_apply_apply _

end AlgebraicGeometry.RingedSite

end
