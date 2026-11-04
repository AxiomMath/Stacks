module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ResolutionBaseChange

/-!
# The derived base change map along an étale morphism

The degreewise direct image computes the derived one at every K-injective complex. Inverse image
along an étale morphism is restriction, whose left adjoint `j_!` is exact, so it carries
K-injective complexes to K-injective complexes. Hence, for a commutative square whose upper
horizontal morphism is étale, both direct images are computed degreewise at a K-injective
resolution, and the derived base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` is invertible as soon
as the underived comparison is.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_of_isKInjective` — the
  degreewise direct image computes `Rf_*` at a K-injective complex.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_etale` — for an étale base
  change the derived base change map is invertible when the underived one is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **The degreewise direct image computes `Rf_*` at a K-injective complex.** -/
theorem isIso_etaleAbelianDerivedDirectImageUnit_app_of_isKInjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (etaleAbelianPushforwardToDerivedCategory.{u, v} f)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective).2
    DerivedCategory.Qh _ (etaleAbelianDerivedDirectImageUnit.{u, v} f) I hI

/-- **For an étale base change the derived base change map is invertible when the underived one
is.** The derived map is computed at a K-injective resolution, where both degreewise direct
images compute the derived ones: for `f` because the resolution is K-injective, for `f'` because
its inverse image along the étale morphism `g'` is again K-injective (inverse image along an
étale morphism is restriction, whose left adjoint `j_!` is exact). -/
theorem isIso_etaleAbelianDerivedBaseChange_of_etale {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g) [Etale g']
    (hbc : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h)) :
    IsIso (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h) := by
  have hbc' := hbc
  have hall : ∀ Z, IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app Z) := by
    intro Z
    obtain ⟨I, q, hI, hq⟩ := Stacks.DerivedFunctor.exists_quasiIso_isKInjective
      (DerivedCategory.Qh.objPreimage Z).as
    have hq' : HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).map q) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).map q)) :=
      Localization.inverts _ _ _ hq'
    let e : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj I) ≅ Z :=
      (asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).map q))).symm ≪≫
        DerivedCategory.Qh.objObjPreimageIso Z
    have h1 := isIso_etaleAbelianDerivedDirectImageUnit_app_of_isKInjective.{u, v} f I hI
    have : I.IsKInjective := hI
    -- inverse image along the étale `g'` is restriction, whose left adjoint `j_!` is exact,
    -- so it carries the K-injective `I` to a K-injective complex
    have hres : CochainComplex.IsKInjective
        (((etaleRestriction.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
      CochainComplex.isKInjective_mapHomologicalComplex_of_exact (etaleRestriction.{u, v} g')
        (extensionByZero.{u, v} g') (extensionByZeroAdj.{u, v} g') I
    have h2 := isIso_etaleAbelianDerivedDirectImageUnit_app_of_isKInjective.{u, v} f'
      (((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      (CochainComplex.isKInjective_of_iso
        (((NatIso.mapHomologicalComplex (etaleAbelianInverseImageRestrictionIso.{u, v} g')
          (ComplexShape.up ℤ)).app I).symm))
    have : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
            (ComplexShape.up ℤ)).obj I))) :=
      isIso_etaleAbelianDerivedBaseChange_app_Qh_of_isIso.{u, v} f g g' f' h I h1 h2
        fun n => inferInstance
    have hnat := (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).naturality e.hom
    have hrw : (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app Z =
        inv ((etaleAbelianDerivedDirectImage.{u, v} f ⋙
            etaleAbelianDerivedInverseImage.{u, v} g).map e.hom) ≫
          (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
                (ComplexShape.up ℤ)).obj I)) ≫
          (etaleAbelianDerivedInverseImage.{u, v} g' ⋙
            etaleAbelianDerivedDirectImage.{u, v} f').map e.hom := by
      rw [← hnat, IsIso.inv_hom_id_assoc]
    rw [hrw]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Stacks.EtaleCohomology

end
