module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.Excision
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparison

/-!
# Vanishing is local for an elementary distinguished square

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces. A sheaf of
`𝒪_W`-modules, or an object of `D(𝒪_W)`, whose restrictions to `U` and to `V` vanish is zero:
in the Mayer–Vietoris sequence
`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0` the first two terms vanish.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_restrict_eds`: the module statement.
* `AlgebraicGeometry.Space.isZero_of_isZero_derivedRestrict_eds`: the derived statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- A sheaf of `𝒪_W`-modules restricting to zero on `U` and on `V` is zero. -/
theorem isZero_of_isZero_restrict_eds (F : Modules.{u, u} B S hS W.1 W.2)
    (hU : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj F))
    (hV : IsZero ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj F)) : IsZero F := by
  have hSE := (mayerVietoris_shortExact_and_mem_distTriang B S hS hsq).1 F
  have hepi : Epi (biprod.desc
      ((etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).counit.app F)
      ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).counit.app F)) := hSE.epi_g
  exact @IsZero.of_epi _ _ _ _ _ _ hepi ((biprod_isZero_iff _ _).2
    ⟨Functor.map_isZero (etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)) hU,
      Functor.map_isZero (etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)) hV⟩)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- An object of `D(𝒪_W)` restricting to zero on `U` and on `V` is zero. -/
theorem isZero_of_isZero_derivedRestrict_eds (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E))
    (hV : IsZero ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)) : IsZero E := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  exact fun n => isZero_of_isZero_restrict_eds B S hS hsq _
    (((DerivedCategory.homologyFunctor _ n).map_isZero hU).of_iso
      (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategoryHomologyIso n).app E).symm)
    (((DerivedCategory.homologyFunctor _ n).map_isZero hV).of_iso
      (((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryHomologyIso n).app E).symm)

end AlgebraicGeometry.Space

end
