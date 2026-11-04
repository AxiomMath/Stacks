module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DifferentialSections
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Sheaves of absolute differential forms on a scheme

The sheaf of absolute differential `n`-forms `Ω^n_{Y/ℤ}` of a scheme `Y` is the sheaf of relative
differential `n`-forms of the unique morphism from `Y` to the terminal scheme `Spec ℤ`. For a
morphism `f : Y ⟶ X` the square with bottom edge the identity of `Spec ℤ` gives the canonical
map `f^*Ω^n_{X/ℤ} ⟶ Ω^n_{Y/ℤ}` of Stacks Tag 07HX, and these maps compose.

These are the sheaves Section 0FL7 of the Stacks project compares.

## Main definitions

* `AlgebraicGeometry.Scheme.toSpecZ`: the unique morphism to the terminal scheme `Spec ℤ`.
* `AlgebraicGeometry.Scheme.absoluteDifferentialFormsAlgebra` and
  `AlgebraicGeometry.Scheme.absoluteDifferentialForms`: the graded algebra `Ω^•_{Y/ℤ}` and its
  homogeneous pieces `Ω^n_{Y/ℤ}`.
* `AlgebraicGeometry.Scheme.Hom.absoluteFormsMap`: the canonical map
  `f^*Ω^n_{X/ℤ} ⟶ Ω^n_{Y/ℤ}`.
* `AlgebraicGeometry.Scheme.Hom.absoluteFormsPullback`: pulling back a local absolute form along
  `f`, the map `Γ(Ω^n_{X/ℤ}, U) ⟶ Γ(Ω^n_{Y/ℤ}, f⁻¹U)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.absoluteFormsMap_comp` and `absoluteFormsPullback_comp`: the
  canonical maps of a composite `Y' ⟶ Y ⟶ X` compose.
* `AlgebraicGeometry.Scheme.Hom.absoluteFormsMap_id` and `absoluteFormsPullback_id`: the
  canonical map of an identity is the identity law `(𝟙 X)^* ≅ 𝟭`.
* `AlgebraicGeometry.Scheme.Hom.isIso_absoluteFormsMap_of_etale`: for `f` étale, in particular
  an open immersion, the canonical map is an isomorphism.

## References

* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Section 0FL7](https://stacks.math.columbia.edu/tag/0FL7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- The unique morphism from a scheme to the terminal scheme `Spec ℤ`. -/
noncomputable abbrev toSpecZ (Y : Scheme.{u}) : Y ⟶ Spec (.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.from Y

/-- The graded algebra `Ω^•_{Y/ℤ}` of absolute differential forms of a scheme: the relative
differential forms of the morphism to `Spec ℤ`. -/
noncomputable abbrev absoluteDifferentialFormsAlgebra (Y : Scheme.{u}) :
    SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace) :=
  Hom.relativeDifferentialFormsAlgebra Y.toSpecZ

/-- The sheaf `Ω^n_{Y/ℤ}` of absolute differential `n`-forms of a scheme. -/
noncomputable abbrev absoluteDifferentialForms (Y : Scheme.{u}) (n : ℤ) : Y.Modules :=
  (absoluteDifferentialFormsAlgebra Y).piece n

/-- Every morphism of schemes commutes with the morphisms to `Spec ℤ`. -/
theorem comp_toSpecZ {Y X : Scheme.{u}} (f : Y ⟶ X) : f ≫ X.toSpecZ = Y.toSpecZ ≫ 𝟙 _ :=
  specULiftZIsTerminal.hom_ext _ _

namespace Hom

variable {Y' Y X : Scheme.{u}}

/-- **Stacks Project, Tag 07HX, for absolute forms.** The canonical map
`f^*Ω^n_{X/ℤ} ⟶ Ω^n_{Y/ℤ}` of a morphism of schemes `f : Y ⟶ X`: the canonical map on relative
differential forms of the square with bottom edge the identity of `Spec ℤ`. -/
noncomputable def absoluteFormsMap (f : Y ⟶ X) (n : ℤ) :
    (Scheme.Modules.pullback f).obj (absoluteDifferentialForms X n) ⟶
      absoluteDifferentialForms Y n :=
  relativeDifferentialFormsMap f X.toSpecZ Y.toSpecZ (𝟙 _) (comp_toSpecZ f) n

/-- **The canonical maps on absolute forms compose**: for `Y' ⟶ Y ⟶ X` the map of the composite
is the coherence isomorphism `(f' ≫ f)^* ≅ f'^* ∘ f^*`, followed by `f'^*` of the map of `f`,
followed by the map of `f'`. -/
theorem absoluteFormsMap_comp (f : Y ⟶ X) (f' : Y' ⟶ Y) (n : ℤ) :
    (f' ≫ f).absoluteFormsMap n =
      (Scheme.Modules.pullbackComp f' f).inv.app (absoluteDifferentialForms X n) ≫
        (Scheme.Modules.pullback f').map (f.absoluteFormsMap n) ≫ f'.absoluteFormsMap n :=
  relativeDifferentialFormsMap_comp f f' X.toSpecZ Y.toSpecZ Y'.toSpecZ (𝟙 _) (𝟙 _) (𝟙 _)
    (comp_toSpecZ f) (comp_toSpecZ f') (comp_toSpecZ (f' ≫ f)) n

/-- **Pulling back a local absolute differential form** along a morphism of schemes `f : Y ⟶ X`:
the map `Γ(Ω^n_{X/ℤ}, U) ⟶ Γ(Ω^n_{Y/ℤ}, f⁻¹U)`, the unit of `f^* ⊣ f_*` followed by the
canonical map `f^*Ω^n_{X/ℤ} ⟶ Ω^n_{Y/ℤ}`. -/
noncomputable abbrev absoluteFormsPullback (f : Y ⟶ X) (n : ℤ) (U : X.Opens)
    (ω : Γ(absoluteDifferentialForms X n, U)) : Γ(absoluteDifferentialForms Y n, f ⁻¹ᵁ U) :=
  relativeDifferentialFormsPullback f X.toSpecZ Y.toSpecZ (𝟙 _) (comp_toSpecZ f) n U ω

/-- Pulling back a local absolute form is the canonical map `f^*Ω^n_{X/ℤ} ⟶ Ω^n_{Y/ℤ}` applied to
the image of the form under the unit of `f^* ⊣ f_*`. -/
theorem absoluteFormsMap_app_unit (f : Y ⟶ X) (n : ℤ) (U : X.Opens)
    (ω : Γ(absoluteDifferentialForms X n, U)) :
    (f.absoluteFormsMap n).val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (absoluteDifferentialForms X n)).val.app (op U) ω) =
      f.absoluteFormsPullback n U ω :=
  rfl

/-- The canonical map `f^*Ω^n_{X/ℤ} ⟶ Ω^n_{Y/ℤ}` carries the pullback of a local absolute form,
restricted to an open `V ≤ f⁻¹U`, to the restriction of the pulled-back form. -/
theorem absoluteFormsMap_pullbackSection (f : Y ⟶ X) (n : ℤ) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (ω : (absoluteDifferentialForms X n).val.obj (op U)) :
    (f.absoluteFormsMap n).val.app (op V)
        (Scheme.Modules.pullbackSection f (absoluteDifferentialForms X n) U V h ω) =
      (absoluteDifferentialForms Y n).val.map (homOfLE h).op (f.absoluteFormsPullback n U ω) :=
  PresheafOfModules.naturality_apply (f.absoluteFormsMap n).val (homOfLE h).op _

/-- The identity law `(𝟙 X)^* ≅ 𝟭` carries the image of a local section under the unit of
`(𝟙 X)^* ⊣ (𝟙 X)_*` back to that section. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackId_hom_app_unit (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackId X).hom.app M).val.app (op U)
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M).val.app (op U) x) = x :=
  SheafOfModules.Hom.congr_val_app (AlgebraicGeometry.pullbackId_unit M) (op U) x

/-- **The canonical map on absolute forms of an identity morphism is the identity law**
`(𝟙 X)^* ≅ 𝟭`. -/
theorem absoluteFormsMap_id (X : Scheme.{u}) (n : ℤ) :
    absoluteFormsMap (𝟙 X) n = (Scheme.Modules.pullbackId X).hom.app _ := by
  have hd := relativeDifferentialsMap_id_overBase (Over.mk X.toSpecZ)
  refine (relativeDifferentialFormsMap_eq_pullbackComparison (𝟙 X) X.toSpecZ X.toSpecZ (𝟙 _)
    (comp_toSpecZ (𝟙 X)) n).trans ?_
  refine (SheafOfModules.GradedAlgebra.pullbackComparison_unique (Scheme.Hom.toLRSHom (𝟙 X)).toShHom
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials X.toSpecZ))
    ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials X.toSpecZ)).1.comp
      (relativeDifferentialsMap (𝟙 X) X.toSpecZ X.toSpecZ (𝟙 _) (comp_toSpecZ (𝟙 X))))
    (fun m => (Scheme.Modules.pullbackId X).hom.app (absoluteDifferentialForms X m))
    (fun i j U a b => ?_) (fun U => ?_) (fun U s => ?_) n).symm
  · exact (Scheme.Modules.pullbackId_hom_app_unit _ U.unop _).trans
      (congrArg₂ (fun x y => ((absoluteDifferentialFormsAlgebra X).mul i j).app U x y)
        (Scheme.Modules.pullbackId_hom_app_unit _ U.unop a).symm
        (Scheme.Modules.pullbackId_hom_app_unit _ U.unop b).symm)
  · exact Scheme.Modules.pullbackId_hom_app_unit _ U.unop _
  · exact (Scheme.Modules.pullbackId_hom_app_unit _ U.unop _).trans
      (congrArg ((Scheme.Modules.exteriorGenerator (relativeDifferentials X.toSpecZ)).val.app U)
        ((Scheme.Modules.pullbackId_hom_app_unit _ U.unop s).symm.trans
          (SheafOfModules.Hom.congr_val_app hd.symm U _)))

/-- Pulling back a local absolute form along an identity morphism does nothing. -/
theorem absoluteFormsPullback_id (n : ℤ) (U : X.Opens)
    (ω : Γ(absoluteDifferentialForms X n, U)) :
    absoluteFormsPullback (𝟙 X) n U ω = ω :=
  (SheafOfModules.Hom.congr_val_app (absoluteFormsMap_id X n) (op U) _).trans
    (Scheme.Modules.pullbackId_hom_app_unit _ U ω)

/-- **Pulling back local absolute forms is functorial**: pulling back along `f' ≫ f` is pulling
back along `f` and then along `f'`. -/
theorem absoluteFormsPullback_comp (f : Y ⟶ X) (f' : Y' ⟶ Y) (n : ℤ) (U : X.Opens)
    (ω : Γ(absoluteDifferentialForms X n, U)) :
    (f' ≫ f).absoluteFormsPullback n U ω =
      f'.absoluteFormsPullback n (f ⁻¹ᵁ U) (f.absoluteFormsPullback n U ω) := by
  have h1 := SheafOfModules.Hom.congr_val_app (absoluteFormsMap_comp f f' n) (op ((f' ≫ f) ⁻¹ᵁ U))
    (((Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ f)).unit.app
      (absoluteDifferentialForms X n)).val.app (op U) ω)
  have h2 := Scheme.Modules.pullbackComp_inv_unit f' f (absoluteDifferentialForms X n) U ω
  have h3 := Scheme.Modules.unit_app_val_app_naturality f' (f.absoluteFormsMap n) (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (absoluteDifferentialForms X n)).val.app (op U) ω)
  exact h1.trans ((congrArg (fun x => (f'.absoluteFormsMap n).val.app (op (f' ⁻¹ᵁ f ⁻¹ᵁ U))
    (((Scheme.Modules.pullback f').map (f.absoluteFormsMap n)).val.app
      (op (f' ⁻¹ᵁ f ⁻¹ᵁ U)) x)) h2).trans
    (congrArg ((f'.absoluteFormsMap n).val.app (op (f' ⁻¹ᵁ f ⁻¹ᵁ U))) h3))

/-- **The canonical map on absolute forms of an étale morphism is an isomorphism** (Stacks
Tag 0FLV for the square with bottom edge the identity of `Spec ℤ`); in particular this holds for
open immersions. -/
instance isIso_absoluteFormsMap_of_etale (f : Y ⟶ X) [Etale f] (n : ℤ) :
    IsIso (f.absoluteFormsMap n) :=
  isIso_relativeDifferentialFormsMap_of_etale f X.toSpecZ Y.toSpecZ (𝟙 _) (comp_toSpecZ f) n

end Hom

end Scheme

end AlgebraicGeometry
