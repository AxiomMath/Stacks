module

public import StacksFrontier.Algebra.Category.ModuleCat.ExactLinearFunctorFlat
public import StacksFrontier.CategoryTheory.Sites.SheafModuleCatBiproducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedInverseImage

/-!
# Restriction of coefficient modules is the inverse image of sheaves of `Λ`-modules

Let `j : U ⟶ X` be a weakly étale morphism of schemes, for instance an open immersion, and `Λ` a
ring. Two restrictions along `j` are in use for the objects of `D(X_proét, Λ)`:

* `AlgebraicGeometry.ProEtale.coefficientRestriction j Λ`, restriction of sheaves of modules over
  the constant coefficient ring sheaf `\underline{Λ}` along composition with `j`;
* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImage j Λ`, the inverse image of pro-étale
  sheaves of `Λ`-modules.

They agree through the identification `AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv`
of sheaves of `Λ`-modules with sheaves of `\underline{Λ}`-modules. Both are restriction along
composition with `j` up to the sheafification which turns a sheaf of `Λ`-modules into a sheaf of
`\underline{Λ}`-modules; the comparison is the map out of a sheafification adjoint to the
sheafification unit over `X` restricted to `U`, and it is invertible because that unit is, the
underlying abelian presheaf of a sheaf of `Λ`-modules being a sheaf. On derived categories this
identifies the restriction `CoefficientRestriction.derived` of the restriction datum of `j` with
`AlgebraicGeometry.ProEtale.derivedInverseImage j Λ`.

Inverse image along `j` is restriction along composition with `j`, so it commutes with limits;
it also preserves constant sheaves. Hence it sends the completed constant sheaf
`\underline{M}^∧ = limₙ \underline{M/IⁿM}` on `X` to the one on `U`. Finally, for a Noetherian
ring `Λ` with completion `Λ^∧` the tower `(Λ^∧)/Iⁿ(Λ^∧)` is the tower `Λ/Iⁿ`, so the completed
constant sheaf of the free `Λ^∧`-module `(Λ^∧)^t`, read as a `Λ`-module, is the direct sum of `t`
copies of `\underline{Λ}^∧`.

## Main definitions

* `AlgebraicGeometry.ProEtale.coefficientRestrictionIsoInverseImage`: restriction of coefficient
  modules along `j` is `E_X⁻¹ ⋙ j⁻¹ ⋙ E_U`.
* `AlgebraicGeometry.ProEtale.coefficientRestrictionIsoRestriction`: the same with restriction
  along composition with `j` in place of `j⁻¹`.
* `AlgebraicGeometry.ProEtale.constantCoefficientModuleEquivInverseImageIso`: the form
  `E_X ⋙ j^* ≅ j⁻¹ ⋙ E_U`.
* `AlgebraicGeometry.ProEtale.CoefficientRestriction.ofWeaklyEtaleDerivedIso`: the derived
  restriction of the restriction datum of `j` is `AlgebraicGeometry.ProEtale.derivedInverseImage`.
* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageCompletedConstantSheafIso`:
  `j⁻¹ \underline{M}^∧_X ≅ \underline{M}^∧_U`.
* `AlgebraicGeometry.ProEtale.coefficientRestrictionCompletedConstantIso`: the same for the
  completed constant sheaves of coefficient modules.
* `AlgebraicGeometry.ProEtale.completedConstantSheafRestrictPiIso`: the completed constant sheaf
  of `(Λ^∧)^t` is `⨁ᵗ \underline{Λ}^∧`.

## Main results

* `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_proetaleModuleInverseImage_of_weaklyEtale`:
  inverse image along a weakly étale morphism preserves limits.
* `AlgebraicGeometry.ProEtale.bijective_adicQuotientModuleFunctor_map_adicCompletionUnitHom`:
  `Λ/IⁿΛ → Λ^∧/IⁿΛ^∧` is bijective for a finitely generated ideal `I`.
* `AlgebraicGeometry.ProEtale.exists_completedConstantSheaf_iso_biproduct` and
  `AlgebraicGeometry.ProEtale.exists_completedConstantCoefficientSheaf_iso_biproduct`: a direct
  sum of `t` copies of `\underline{Λ}^∧` is the completed constant sheaf of a finite projective
  `Λ^∧`-module.

## References

* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  proetalePostcompose_isContinuous

variable {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] (Λ : Type r) [CommRing Λ]

/-- The unit of sheafification of a sheaf of `Λ`-modules `P` on `X_proét`, read as a presheaf of
modules over the constant presheaf of rings, restricted along composition with `j`: a map from
the restriction of `P` to `U` into the sections of `j^*` of the sheaf of `\underline{Λ}`-modules
attached to `P`. It is linear because the constant coefficient ring sheaves of `U` and `X` are
compatible along `j`. -/
def modulePresheafOverConstantCoefficientsRestrictionUnit
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :
    (modulePresheafOverConstantCoefficientsFunctor.{u, r, w} U Λ).obj
        (((proetalePostcompose j).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).obj P) ⟶
      (SheafOfModules.forget _ ⋙
          PresheafOfModules.restrictScalars (constantCoefficientRingMap.{u, r, w} U Λ)).obj
        ((coefficientRestriction.{u, r, w} j Λ).obj
          ((moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P)) :=
  PresheafOfModules.homMk
    (Functor.whiskerLeft (proetalePostcompose j).op
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
          (constantCoefficientRingMap.{u, r, w} X Λ)).unit.app
            ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P))))
    (fun V a m => by
      have h := congrArg (fun φ => (φ.app V).hom a)
        (toSheafify_comp_constantCoefficientRestrictionComparison.{u, r, w} j Λ)
      refine ((((PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
          (constantCoefficientRingMap.{u, r, w} X Λ)).unit.app
            ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P)).app
              (op ((proetalePostcompose j).obj V.unop))).hom.map_smul a m).trans ?_
      let R := (Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, r, w} X Λ).O).obj.obj
        (op ((proetalePostcompose j).obj V.unop))
      let y : ((PresheafOfModules.sheafification.{max (u + 1) r w}
            (constantCoefficientRingMap.{u, r, w} X Λ)).obj
              ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P)).val.obj
                (op ((proetalePostcompose j).obj V.unop)) :=
        (((PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
          (constantCoefficientRingMap.{u, r, w} X Λ)).unit.app
            ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P)).app
              (op ((proetalePostcompose j).obj V.unop))).hom m
      have h' : ((constantCoefficientRingMap.{u, r, w} X Λ).app
            (op ((proetalePostcompose j).obj V.unop))).hom a =
          ((coefficientRestrictionComparison.{u, r, w} j Λ).hom.app V).hom
            (((constantCoefficientRingMap.{u, r, w} U Λ).app V).hom a) := h.symm
      exact congrArg (fun s : R => s • y) h')

/-- The restricted sheafification unit is invertible: the abelian presheaf underlying a sheaf of
`Λ`-modules is a sheaf. -/
instance isIso_modulePresheafOverConstantCoefficientsRestrictionUnit
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :
    IsIso (modulePresheafOverConstantCoefficientsRestrictionUnit.{u, r, w} j Λ P) := by
  have hP : Presheaf.IsSheaf (Scheme.ProEt.topology X)
      ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P).presheaf :=
    ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w})).obj
      P).property
  have : IsIso (toSheafify (Scheme.ProEt.topology X)
      ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P).presheaf) :=
    isIso_toSheafify _ hP
  have : IsIso ((PresheafOfModules.toPresheaf _).map
      (modulePresheafOverConstantCoefficientsRestrictionUnit.{u, r, w} j Λ P)) :=
    inferInstanceAs (IsIso (Functor.whiskerLeft (proetalePostcompose j).op (toSheafify _
      ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P).presheaf)))
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

/-- The comparison `(P|_U)^♯ ⟶ j^*(P^♯)` between the sheaf of `\underline{Λ}`-modules attached to
the restriction of a sheaf of `Λ`-modules `P` and the restriction of the one attached to `P`:
the map out of the sheafification adjoint to the restricted sheafification unit. -/
def moduleSheafOverConstantCoefficientsRestrictionHom
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :
    (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} U Λ).obj
        (((proetalePostcompose j).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).obj P) ⟶
      (coefficientRestriction.{u, r, w} j Λ).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P) :=
  ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
    (constantCoefficientRingMap.{u, r, w} U Λ)).homEquiv
      ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} U Λ).obj
        (((proetalePostcompose j).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).obj P))
      ((coefficientRestriction.{u, r, w} j Λ).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj P))).symm
    (modulePresheafOverConstantCoefficientsRestrictionUnit.{u, r, w} j Λ P)

/-- The comparison `(P|_U)^♯ ⟶ j^*(P^♯)` is invertible: it is the sheafification of an
isomorphism followed by the invertible counit of sheafification. -/
instance isIso_moduleSheafOverConstantCoefficientsRestrictionHom
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :
    IsIso (moduleSheafOverConstantCoefficientsRestrictionHom.{u, r, w} j Λ P) := by
  unfold moduleSheafOverConstantCoefficientsRestrictionHom
  rw [Adjunction.homEquiv_counit]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) ?_
  infer_instance

/-- **Reading a sheaf of `Λ`-modules over `\underline{Λ}` commutes with restriction along `j`.**
Restricting a sheaf of `Λ`-modules along composition with a weakly étale `j` and then reading it
over `\underline{Λ}_U` is reading it over `\underline{Λ}_X` and then restricting the coefficient
module along `j`. -/
def moduleSheafOverConstantCoefficientsRestrictionIso :
    (proetalePostcompose j).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) ⋙
        moduleSheafOverConstantCoefficientsFunctor.{u, r, w} U Λ ≅
      moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ ⋙
        coefficientRestriction.{u, r, w} j Λ :=
  NatIso.ofComponents
    (fun P => asIso (moduleSheafOverConstantCoefficientsRestrictionHom.{u, r, w} j Λ P))
    (fun {P P'} φ => by
      let adj := PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} U Λ)
      let adjX := PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ)
      change (PresheafOfModules.sheafification.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} U Λ)).map _ ≫ (adj.homEquiv _ _).symm _ =
          (adj.homEquiv _ _).symm _ ≫ _
      rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
      congr 1
      ext V m
      exact congrArg (fun ψ => (ψ.app (op ((proetalePostcompose j).obj V.unop))).hom m)
        (adjX.unit.naturality
          ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).map φ)))

/-- The identification of sheaves of `Λ`-modules with sheaves of `\underline{Λ}`-modules commutes
with restriction along a weakly étale `j`: `E_X ⋙ j^* ≅ (− ∘ j) ⋙ E_U`. -/
def constantCoefficientModuleEquivRestrictionIso :
    (constantCoefficientModuleEquiv.{u, r, w} X Λ).functor ⋙
        coefficientRestriction.{u, r, w} j Λ ≅
      (proetalePostcompose j).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) ⋙
        (constantCoefficientModuleEquiv.{u, r, w} U Λ).functor :=
  Functor.isoWhiskerRight (constantCoefficientModuleEquivFunctorIso.{u, r, w} X Λ) _ ≪≫
    (moduleSheafOverConstantCoefficientsRestrictionIso.{u, r, w} j Λ).symm ≪≫
    Functor.isoWhiskerLeft _ (constantCoefficientModuleEquivFunctorIso.{u, r, w} U Λ).symm

/-- **The identification of sheaves of `Λ`-modules with sheaves of `\underline{Λ}`-modules commutes
with inverse image along a weakly étale `j`**: `E_X ⋙ j^* ≅ j⁻¹ ⋙ E_U`. -/
def constantCoefficientModuleEquivInverseImageIso :
    (constantCoefficientModuleEquiv.{u, r, w} X Λ).functor ⋙
        coefficientRestriction.{u, r, w} j Λ ≅
      proetaleModuleInverseImage.{u, r, w} j Λ ⋙
        (constantCoefficientModuleEquiv.{u, r, w} U Λ).functor :=
  constantCoefficientModuleEquivRestrictionIso.{u, r, w} j Λ ≪≫
    Functor.isoWhiskerRight (proetaleModuleInverseImageIsoRestriction.{u, r, w} Λ j).symm _

/-- Restriction of coefficient modules along a weakly étale `j` is restriction of the
corresponding sheaves of `Λ`-modules along composition with `j`: `j^* ≅ E_X⁻¹ ⋙ (− ∘ j) ⋙ E_U`. -/
def coefficientRestrictionIsoRestriction :
    coefficientRestriction.{u, r, w} j Λ ≅
      (constantCoefficientModuleEquiv.{u, r, w} X Λ).inverse ⋙
        (proetalePostcompose j).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) ⋙
        (constantCoefficientModuleEquiv.{u, r, w} U Λ).functor :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (constantCoefficientModuleEquiv.{u, r, w} X Λ).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (constantCoefficientModuleEquivRestrictionIso.{u, r, w} j Λ)

/-- **Restriction of coefficient modules along a weakly étale `j` is the inverse image of sheaves
of `Λ`-modules**: `j^* ≅ E_X⁻¹ ⋙ j⁻¹ ⋙ E_U`, where `E` is
`AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv`. -/
def coefficientRestrictionIsoInverseImage :
    coefficientRestriction.{u, r, w} j Λ ≅
      (constantCoefficientModuleEquiv.{u, r, w} X Λ).inverse ⋙
        proetaleModuleInverseImage.{u, r, w} j Λ ⋙
        (constantCoefficientModuleEquiv.{u, r, w} U Λ).functor :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (constantCoefficientModuleEquiv.{u, r, w} X Λ).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (constantCoefficientModuleEquivInverseImageIso.{u, r, w} j Λ)

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits in
/-- **The derived restriction of the restriction datum of a weakly étale `j` is
`AlgebraicGeometry.ProEtale.derivedInverseImage j Λ`**: both apply exact functors termwise, and
the functors agree through `AlgebraicGeometry.ProEtale.coefficientRestrictionIsoInverseImage`. -/
def CoefficientRestriction.ofWeaklyEtaleDerivedIso :
    (CoefficientRestriction.ofWeaklyEtale.{u, r, w} j Λ).derived ≅
      derivedInverseImage.{u, r, w} j Λ :=
  letI := (CoefficientRestriction.ofWeaklyEtale.{u, r, w} j Λ).additive
  letI := (CoefficientRestriction.ofWeaklyEtale.{u, r, w} j Λ).preservesFiniteLimits
  letI := (CoefficientRestriction.ofWeaklyEtale.{u, r, w} j Λ).preservesFiniteColimits
  letI : (constantCoefficientModuleEquiv.{u, r, w} X Λ).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (constantCoefficientModuleEquiv.{u, r, w} U Λ).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
      (CoefficientRestriction.ofWeaklyEtale.{u, r, w} j Λ).functor _
      (coefficientRestrictionIsoInverseImage.{u, r, w} j Λ) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _)

/-- **Inverse image along a weakly étale morphism preserves limits**: it is restriction along
composition with the morphism, and limits of sheaves are computed sectionwise. -/
instance preservesLimitsOfShape_proetaleModuleInverseImage_of_weaklyEtale
    (T : Type*) [Category T] [HasLimitsOfShape T (ModuleCat.{max (u + 1) r w} Λ)] :
    PreservesLimitsOfShape T (proetaleModuleInverseImage.{u, r, w} j Λ) :=
  preservesLimitsOfShape_of_natIso (proetaleModuleInverseImageIsoRestriction.{u, r, w} Λ j).symm

section Completed

variable (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

/-- Inverse image along a weakly étale `j` of the completed constant sheaf
`\underline{M}^∧ = limₙ \underline{M/IⁿM}` on `X` is the completed constant sheaf on `U`,
naturally in the module `M`: inverse image preserves the limit and the constant sheaves. -/
def proetaleModuleInverseImageCompletedConstantSheafNatIso :
    adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I ⋙
        (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
          (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ⋙
        lim ⋙ proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ ≅
      adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I ⋙
        (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
          (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ))).obj
          (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)) ⋙ lim :=
  Functor.isoWhiskerLeft (adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I ⋙
      (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
      (preservesLimitNatIso (proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ)) ≪≫
    Functor.isoWhiskerLeft (adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I)
      (Functor.isoWhiskerRight ((Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
        (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ))).mapIso
          (constantSheafCompProetaleModuleInverseImageIso j Λ)) lim)

/-- **Inverse image of a completed constant sheaf**: `j⁻¹ \underline{M}^∧_X ≅ \underline{M}^∧_U`
for a weakly étale `j : U ⟶ X`. -/
def proetaleModuleInverseImageCompletedConstantSheafIso (M : ModuleCat.{max (u + 1) w} Λ) :
    (proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ).obj
        (completedConstantSheaf X Λ I M) ≅ completedConstantSheaf U Λ I M :=
  (proetaleModuleInverseImageCompletedConstantSheafNatIso.{u, w} j Λ I).app M

/-- Restriction of coefficient modules along a weakly étale `j` of the completed constant sheaf
of coefficient modules on `X` is the one on `U`, naturally in the module. -/
def completedConstantCoefficientSheafFunctorCompCoefficientRestrictionIso :
    completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I ⋙
        coefficientRestriction.{u, max (u + 1) w, w} j Λ ≅
      completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} U Λ I :=
  Functor.isoWhiskerLeft (adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I ⋙
      (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ⋙ lim)
      (Functor.isoWhiskerRight
          (constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w} X Λ).symm _ ≪≫
        constantCoefficientModuleEquivInverseImageIso.{u, max (u + 1) w, w} j Λ ≪≫
        Functor.isoWhiskerLeft _
          (constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w} U Λ)) ≪≫
    Functor.isoWhiskerRight (proetaleModuleInverseImageCompletedConstantSheafNatIso.{u, w} j Λ I)
      (moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} U Λ)

/-- **Restriction of a completed constant sheaf of coefficient modules** along a weakly étale
`j : U ⟶ X`: `j^* \underline{M}^∧_X ≅ \underline{M}^∧_U`. -/
def coefficientRestrictionCompletedConstantIso (M : ModuleCat.{max (u + 1) w} Λ) :
    (coefficientRestriction.{u, max (u + 1) w, w} j Λ).obj
        ((completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj M) ≅
      (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} U Λ I).obj M :=
  (completedConstantCoefficientSheafFunctorCompCoefficientRestrictionIso.{u, w} j Λ I).app M

end Completed

section AdicCompletionTower

variable {Λ : Type r} [CommRing Λ] (I : Ideal Λ)

/-- The map `Λ → Λ^∧` to the `I`-adic completion, as a map of `Λ`-modules into `Λ^∧` with its
scalars restricted to `Λ`. -/
def adicCompletionUnitHom :
    Functor.unitModule Λ ⟶ (restrictToCoefficients.{r, r} Λ I).obj
      (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)) :=
  ModuleCat.ofHom
    { toFun := algebraMap Λ (AdicCompletion I Λ)
      map_add' := map_add _
      map_smul' := map_mul _ }

/-- For an ideal `J` of `Λ`, the submodule `J • Λ^∧` of `Λ^∧` is the same whether `Λ^∧` is viewed
as a `Λ`-module through restriction of scalars or through its own `Λ`-module structure. -/
theorem mem_smul_top_restrictToCoefficients_iff (J : Ideal Λ)
    (y : (restrictToCoefficients.{r, r} Λ I).obj
      (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ))) :
    y ∈ (J • ⊤ : Submodule Λ ((restrictToCoefficients.{r, r} Λ I).obj
      (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)))) ↔
      (show AdicCompletion I Λ from y) ∈ (J • ⊤ : Submodule Λ (AdicCompletion I Λ)) := by
  constructor <;> intro hy <;>
  refine Submodule.smul_induction_on hy (fun a ha m _ => ?_) (fun a b ha hb => add_mem ha hb) <;>
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- For a finitely generated ideal `I`, the map `Λ/IⁿΛ → Λ^∧/IⁿΛ^∧` induced by `Λ → Λ^∧` is
bijective: its kernel and cokernel are read on the `n`-th truncation of the completion. -/
theorem bijective_adicQuotientModuleFunctor_map_adicCompletionUnitHom (hI : I.FG) (n : ℕ) :
    Function.Bijective
      (((adicQuotientModuleFunctor.{r, r} Λ I).map (adicCompletionUnitHom I)).app (op n)).hom := by
  let N := (restrictToCoefficients.{r, r} Λ I).obj
    (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ))
  have happ : ∀ x : Λ,
      (((adicQuotientModuleFunctor.{r, r} Λ I).map (adicCompletionUnitHom I)).app (op n)).hom
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (algebraMap Λ (AdicCompletion I Λ) x : N) :
        N ⧸ (I ^ n • ⊤ : Submodule Λ N)) := fun x => rfl
  have heval : ∀ x : Λ, AdicCompletion.eval I Λ n (algebraMap Λ (AdicCompletion I Λ) x) =
      Submodule.Quotient.mk x := fun x => by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply, AdicCompletion.eval_of]
    rfl
  have hker : ∀ z : N, z ∈ (I ^ n • ⊤ : Submodule Λ N) ↔ AdicCompletion.eval I Λ n z = 0 :=
      fun z => by
    rw [mem_smul_top_restrictToCoefficients_iff, AdicCompletion.pow_smul_top_eq_ker_eval hI,
      LinearMap.mem_ker]
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have hab' := (Submodule.Quotient.eq (I ^ n • ⊤ : Submodule Λ N)).mp
      ((happ x).symm.trans (hab.trans (happ y)))
    refine (Submodule.Quotient.eq (I ^ n • ⊤ : Submodule Λ (Functor.unitModule Λ))).mpr ?_
    have h1 := (hker _).mp hab'
    have h2 : AdicCompletion.eval I Λ n (algebraMap Λ (AdicCompletion I Λ) x) -
        AdicCompletion.eval I Λ n (algebraMap Λ (AdicCompletion I Λ) y) = 0 :=
      (map_sub (AdicCompletion.eval I Λ n) _ _).symm.trans h1
    rwa [heval, heval, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero] at h2
  · intro a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _
      (AdicCompletion.eval I Λ n (show AdicCompletion I Λ from y))
    refine ⟨Submodule.Quotient.mk x, (happ x).trans
      ((Submodule.Quotient.eq (I ^ n • ⊤ : Submodule Λ N)).mpr ((hker _).mpr ?_))⟩
    refine (map_sub (AdicCompletion.eval I Λ n) _ _).trans ?_
    rw [heval, hx, sub_self]

/-- For a Noetherian ring `Λ`, the tower `n ↦ Λ/IⁿΛ` is the tower `n ↦ Λ^∧/IⁿΛ^∧`. -/
instance isIso_adicQuotientModuleFunctor_map_adicCompletionUnitHom [IsNoetherianRing Λ] :
    IsIso ((adicQuotientModuleFunctor.{r, r} Λ I).map (adicCompletionUnitHom I)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun n => ?_)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_adicQuotientModuleFunctor_map_adicCompletionUnitHom I
      (IsNoetherian.noetherian I) n.unop)

variable [IsNoetherianRing Λ] {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
  (H : (ℕᵒᵖ ⥤ ModuleCat.{r} Λ) ⥤ D) [H.Additive]

/-- For a Noetherian ring `Λ` and an additive functor `H` of towers of `Λ`-modules, `H` of the
tower of adic quotients of `(Λ^∧)^t`, read as a `Λ`-module, is the direct sum of `t` copies of
`H` of the tower `n ↦ Λ/Iⁿ`. -/
def adicQuotientModuleFunctorCompObjPiIso (t : ℕ) :
    (adicQuotientModuleFunctor.{r, r} Λ I ⋙ H).obj ((restrictToCoefficients.{r, r} Λ I).obj
        (ModuleCat.of (AdicCompletion I Λ) (Fin t → AdicCompletion I Λ))) ≅
      ⨁ fun _ : Fin t => (adicQuotientModuleFunctor.{r, r} Λ I ⋙ H).obj (Functor.unitModule Λ) :=
  (adicQuotientModuleFunctor.{r, r} Λ I ⋙ H).mapIso ((restrictToCoefficients.{r, r} Λ I).mapIso
      (ModuleCat.biproductIsoPi fun _ : Fin t =>
        ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)).symm ≪≫
      (restrictToCoefficients.{r, r} Λ I).mapBiproduct _) ≪≫
    (adicQuotientModuleFunctor.{r, r} Λ I ⋙ H).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ => (H.mapIso (asIso
      ((adicQuotientModuleFunctor.{r, r} Λ I).map (adicCompletionUnitHom I)))).symm

end AdicCompletionTower

section CompletedPi

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)
  [IsNoetherianRing Λ]

/-- **The completed constant sheaf of a finite free `Λ^∧`-module**: for a Noetherian ring `Λ`, the
completed constant sheaf of `(Λ^∧)^t`, read as a `Λ`-module, is the direct sum of `t` copies of
`\underline{Λ}^∧`. -/
def completedConstantSheafRestrictPiIso (t : ℕ) :
    completedConstantSheaf X Λ I ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj
        (ModuleCat.of (AdicCompletion I Λ) (Fin t → AdicCompletion I Λ))) ≅
      ⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ) :=
  adicQuotientModuleFunctorCompObjPiIso I
    ((Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ⋙ lim) t

/-- A direct sum of `t` copies of `\underline{Λ}^∧` is the completed constant sheaf of a finite
projective `Λ^∧`-module, read as a `Λ`-module. -/
theorem exists_completedConstantSheaf_iso_biproduct (t : ℕ) :
    ∃ M : ModuleCat.{max (u + 1) w} (AdicCompletion I Λ),
      Module.Finite (AdicCompletion I Λ) M ∧ Module.Projective (AdicCompletion I Λ) M ∧
        Nonempty (completedConstantSheaf X Λ I
            ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj M) ≅
          ⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) :=
  ⟨ModuleCat.of (AdicCompletion I Λ) (Fin t → AdicCompletion I Λ), inferInstance, inferInstance,
    ⟨completedConstantSheafRestrictPiIso.{u, w} X Λ I t⟩⟩

/-- The completed constant sheaf of coefficient modules of `(Λ^∧)^t`, read as a `Λ`-module, is the
direct sum of `t` copies of `\underline{Λ}^∧`, for a Noetherian ring `Λ`. -/
def completedConstantCoefficientSheafRestrictPiIso (t : ℕ) :
    (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
        ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj
          (ModuleCat.of (AdicCompletion I Λ) (Fin t → AdicCompletion I Λ))) ≅
      ⨁ fun _ : Fin t => (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
        (Functor.unitModule Λ) :=
  adicQuotientModuleFunctorCompObjPiIso I
    ((Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ⋙ lim ⋙
        moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ) t

/-- A direct sum of `t` copies of the completed constant sheaf of coefficient modules
`\underline{Λ}^∧` is the completed constant sheaf of a finite projective `Λ^∧`-module. -/
theorem exists_completedConstantCoefficientSheaf_iso_biproduct (t : ℕ) :
    ∃ M : ModuleCat.{max (u + 1) w} (AdicCompletion I Λ),
      Module.Finite (AdicCompletion I Λ) M ∧ Module.Projective (AdicCompletion I Λ) M ∧
        Nonempty ((completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
            ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj M) ≅
          ⨁ fun _ : Fin t =>
            (completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I).obj
            (Functor.unitModule Λ)) :=
  ⟨ModuleCat.of (AdicCompletion I Λ) (Fin t → AdicCompletion I Λ), inferInstance, inferInstance,
    ⟨completedConstantCoefficientSheafRestrictPiIso.{u, w} X Λ I t⟩⟩

end CompletedPi

end AlgebraicGeometry.ProEtale
