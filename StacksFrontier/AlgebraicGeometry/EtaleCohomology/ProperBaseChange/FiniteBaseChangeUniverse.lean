module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CoefficientUniverseTransfer
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite base change at every coefficient universe, and Stacks 0A4E

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer` proves
the base change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian sheaves invertible for a finite
morphism `f` ([Stacks, Tag 0959]), with values in `AddCommGrpCat.{u + 1}`, for a cartesian square
drawn from a big étale site. This file removes both restrictions.

* The four schemes of a cartesian square of schemes lie in one big étale site,
  `AlgebraicGeometry.BigEtaleSite.ofSet` (Stacks 000J, 000X), so the square is a square of that
  site.
* An abelian sheaf `F` with values in `AddCommGrpCat.{max (u + 1) v}` is the filtered colimit of
  the sheafifications of its small subpresheaves
  (`Stacks.EtaleCohomology.smallSubpresheafSheafCoconeIsColimit`), each of which is the universe
  lift of a sheaf with values in `AddCommGrpCat.{u + 1}`
  (`Stacks.EtaleCohomology.smallSubpresheafSheafIso`). The comparison commutes with the universe
  lift (`Stacks.EtaleCohomology.etaleAbelianBaseChange_sheafCompose`), and both of its sides
  commute with filtered colimits: inverse image is a left adjoint and the direct image along a
  quasi-compact and quasi-separated morphism commutes with filtered colimits ([Stacks, Tag 09Z1]).
  So the comparison is invertible at `F`. The derived base change map is handled the same way
  (`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isColimit`,
  `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose`).

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_unconditional` — the
  underived comparison is invertible for a cartesian square of schemes with `f` finite, at every
  coefficient universe.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_univ` —
  the derived base change map is invertible at every abelian sheaf.
* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isFinite_univ` —
  **[Stacks, Tag 0A4E]**.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0A4E](https://stacks.math.columbia.edu/tag/0A4E)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Sheaves.UniverseLift

attribute [local instance] HasDerivedCategory.standard

universe u v v₀

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **The underived base change comparison is invertible after a change of coefficients** once
it is invertible before: for a coefficient functor `Φ` compatible with sheafification and with the
inverse images, the comparison at `Φ c` is the comparison at `c` up to the two invertible
comparisons of inverse image with `Φ`
(`Stacks.EtaleCohomology.etaleAbelianBaseChange_sheafCompose`). It is stated at an object `F`
isomorphic to `Φ c`. -/
theorem isIso_etaleAbelianBaseChange_app_of_iso_sheafCompose
    (Φ : AddCommGrpCat.{max (u + 1) v₀} ⥤ AddCommGrpCat.{max (u + 1) v})
    [∀ {S T : Scheme.{u}} (i : T ⟶ S), Φ.PreservesLeftKanExtensions (smallEtaleBaseChange i).op]
    [∀ S : Scheme.{u}, S.smallEtaleTopology.HasSheafCompose Φ]
    [∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification Φ]
    (h : g' ≫ f = f' ≫ g) (c : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀})
    (hc : IsIso ((etaleAbelianBaseChange.{u, v₀} f g g' f' h).app c))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (eF : (sheafCompose X.smallEtaleTopology Φ).obj c ≅ F) :
    IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app F) := by
  refine (NatTrans.isIso_app_iff_of_iso _ eF).mp ?_
  have e := etaleAbelianBaseChange_sheafCompose Φ f g g' f' h c
  have h₁ : IsIso ((etaleAbelianInverseImageCoefficientSquare Φ g).natTrans.app
      ((etaleAbelianDirectImage.{u, v₀} f).obj c)) := NatIso.isIso_app_of_isIso _ _
  have h₂ : IsIso ((etaleAbelianInverseImageCoefficientSquare Φ g').natTrans.app c) :=
    NatIso.isIso_app_of_isIso _ _
  have h₄ : IsIso ((sheafCompose Y'.smallEtaleTopology Φ).map
      ((etaleAbelianBaseChange.{u, v₀} f g g' f' h).app c)) := Functor.map_isIso _ _
  have h₃ : IsIso (((etaleAbelianBaseChange.{u, v} f g g' f' h).app
      ((sheafCompose X.smallEtaleTopology Φ).obj c)) ≫
        (etaleAbelianDirectImage.{u, v} f').map
          ((etaleAbelianInverseImageCoefficientSquare Φ g').natTrans.app c)) := by
    rw [← e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₄
  exact IsIso.of_isIso_comp_right _ ((etaleAbelianDirectImage.{u, v} f').map
    ((etaleAbelianInverseImageCoefficientSquare Φ g').natTrans.app c))

/-- **The direct image along a quasi-compact and quasi-separated morphism commutes with filtered
colimits** of abelian sheaves on the small étale sites ([Stacks, Tag 09Z1]): the case `p = 0` of
`Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs`,
the zeroth right derived functor of the left exact direct image being the direct image. -/
theorem preservesColimitsOfShape_etaleAbelianDirectImage_of_qcqs
    [QuasiCompact f] [QuasiSeparated f] (I : Type (max (u + 1) v)) [SmallCategory I]
    [IsFiltered I] : PreservesColimitsOfShape I (etaleAbelianDirectImage.{u, v} f) := by
  have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs.{v, u} f 0 I
  exact preservesColimitsOfShape_of_natIso
    (Functor.rightDerivedZeroIsoSelf (etaleAbelianDirectImage.{u, v} f))

/-- The underived base change comparison is invertible at the sheafification of a small
subpresheaf of an abelian sheaf, once it is invertible at the coefficients `AddCommGrpCat.{u + 1}`:
that sheaf is a universe lift (`Stacks.EtaleCohomology.smallSubpresheafSheafIso`). -/
theorem isIso_etaleAbelianBaseChange_app_smallSubpresheafSheaf (h : g' ≫ f = f' ≫ g)
    (h0 : IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' h))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (S : SmallSubpresheaf F) :
    IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app
      ((smallSubpresheafSheafDiagram F).obj S)) := by
  have : ∀ S : Scheme.{u}, S.smallEtaleTopology.HasSheafCompose
      AddCommGrpCat.uliftFunctor.{v, u + 1} := fun _ ↦ inferInstance
  have : ∀ {S T : Scheme.{u}} (i : T ⟶ S),
      AddCommGrpCat.uliftFunctor.{v, u + 1}.PreservesLeftKanExtensions
        (smallEtaleBaseChange i).op := fun _ ↦ inferInstance
  have : ∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification
      AddCommGrpCat.uliftFunctor.{v, u + 1} :=
    fun _ ↦ preservesSheafification_uliftFunctor.{u + 1, u, u + 1, v}
  have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    wEqualsLocallyBijective_smallEtaleTopology.{u, 0} X
  exact isIso_etaleAbelianBaseChange_app_of_iso_sheafCompose.{u, v, 0} f g g' f'
    AddCommGrpCat.uliftFunctor.{v, u + 1} h
    ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj S.shrinkPresheaf)
    (NatIso.isIso_app_of_isIso _ _) _ (smallSubpresheafSheafIso F S)

/-- **The underived base change comparison passes to filtered colimits** along a quasi-compact and
quasi-separated morphism: if it is invertible at every object of a filtered diagram of abelian
sheaves, it is invertible at the colimit, and at every sheaf isomorphic to it. Inverse image is a
left adjoint and direct image along `f` and along its base change commutes with filtered colimits
(`preservesColimitsOfShape_etaleAbelianDirectImage_of_qcqs`). -/
theorem isIso_etaleAbelianBaseChange_app_of_isColimit (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] {I : Type (max (u + 1) v)} [SmallCategory I]
    [IsFiltered I] (K : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ i, IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' sq.w).app (K.obj i)))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (e : c.pt ≅ F) :
    IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' sq.w).app F) := by
  refine (NatTrans.isIso_app_iff_of_iso _ e).mp ?_
  have : QuasiCompact f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹_›
  have : QuasiSeparated f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹_›
  have := preservesColimitsOfShape_etaleAbelianDirectImage_of_qcqs f I
  have := preservesColimitsOfShape_etaleAbelianDirectImage_of_qcqs f' I
  have : PreservesColimitsOfShape I (etaleAbelianInverseImage.{u, v} g) := inferInstance
  have : PreservesColimitsOfShape I (etaleAbelianInverseImage.{u, v} g') := inferInstance
  exact Stacks.DerivedCategoryComparisons.isIso_app_of_isColimit _ _
    (etaleAbelianBaseChange.{u, v} f g g' f' sq.w) (isColimitOfPreserves _ hc)
    (isColimitOfPreserves _ hc) hK

/-- The underived base change comparison of a finite morphism is invertible at the
sheafification of every small subpresheaf of an abelian sheaf, at every coefficient universe. -/
theorem forall_isIso_etaleAbelianBaseChange_app_smallSubpresheafSheaf (sq : IsPullback g' f' f g)
    [IsFinite f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (S : SmallSubpresheaf F) :
    IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' sq.w).app
      ((smallSubpresheafSheafDiagram F).obj S)) :=
  isIso_etaleAbelianBaseChange_app_smallSubpresheafSheaf f g g' f' sq.w
    (isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite f g g' f' sq) F S

/-- **The underived base change comparison of a finite morphism is invertible at every coefficient
universe**: for a cartesian square of schemes with `f` finite, `g⁻¹ f_* ⟶ f'_* (g')⁻¹` is an
isomorphism of functors on abelian sheaves with values in `AddCommGrpCat.{max (u + 1) v}`. This
is Stacks 0959 at abelian coefficients, carried from the coefficients `AddCommGrpCat.{u + 1}`
(`isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite`) along the presentation of a sheaf
as the filtered colimit of the universe lifts of its small subsheaves. -/
theorem isIso_etaleAbelianBaseChange_app_of_isFinite_of_isPullback (sq : IsPullback g' f' f g)
    [IsFinite f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' sq.w).app F) := by
  refine isIso_etaleAbelianBaseChange_app_of_isColimit f g g' f' sq (smallSubpresheafSheafDiagram F)
    (smallSubpresheafSheafCoconeIsColimit F) (fun S ↦ ?_) F (Iso.refl _)
  exact forall_isIso_etaleAbelianBaseChange_app_smallSubpresheafSheaf f g g' f' sq F S

/-- **Proper base change for finite morphisms.** Cohomology commutes with base change for a finite
morphism of schemes `f : X ⟶ Y`: for every cartesian square with
`X' = Y' ×_Y X` and every torsion abelian sheaf `F` on `X_étale`, with values in
`AddCommGrpCat.{max (u + 1) v}`, the base change map `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` is an
isomorphism. The torsion hypothesis is not used:
`isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_univ` holds at every abelian
sheaf. -/
@[stacks 0A4E,
  sga "4 XII 5.2" "(iii), special case",
  sga "4½ Th_finitude 5.1.3" "1.3.1, special case"]
theorem cohomologyCommutesWithBaseChange_of_isFinite_univ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] :
    CohomologyCommutesWithBaseChange.{u, v} f :=
  fun _ _ g g' f' sq F _ ↦
    isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_univ f g g' f' sq F

end Stacks.EtaleCohomology

end
