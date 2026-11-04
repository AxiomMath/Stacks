module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ConeAlgebraMap
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeClosedImmersion

/-!
# The normal cone inside the deformation space

Let `i : Z ⟶ X` be an immersion, `g = i.liftCoborder : Z ⟶ U` its closed-immersion part with
ideal sheaf `ℐ`, and `D = Spec_U(𝒪_U[t⁻¹, ℐt])` the deformation space. The surjection of
algebras `Ψ : 𝒪_U[t⁻¹, ℐt] ⟶ g_* 𝒞_{Z/X,*}` of
`StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ConeAlgebraMap`
induces, by the universal property of the relative spectrum, a morphism

  `κ : C_ZX ⟶ D`

over `g`, and it is a closed immersion.

## Main definitions

* `Stacks.Deformation.normalConeToDeformation`: the morphism `κ`.

## Main results

* `Stacks.Deformation.normalConeToDeformation_toBase`: `κ` lies over `g`.
* `Stacks.Deformation.isClosedImmersion_normalConeToDeformation`: `κ` is a closed immersion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec Stacks.Blowup
  Stacks.Conormal

universe u

namespace Stacks.Deformation

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The ungraded form of `Ψ`, out of the `Stacks.RelativeSpec.ungradedAlgebraSheaf` spelling of
the extended Rees algebra. -/
def toConormalUngradedHom :
    ungradedAlgebraSheaf i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _) ⟶ conormalPushforwardAlgebra i i.liftCoborder :=
  ((ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra (coborderIdeal i))
      (extReesGradedAlgebra_mul_comm _) (conormalPushforwardAlgebra i i.liftCoborder)).trans
    (ungradedCommHomEquiv (extReesGradedAlgebra (coborderIdeal i))
      (extReesGradedAlgebra_mul_comm _) (conormalPushforwardAlgebra i i.liftCoborder))).symm
    (toConormalUnitalHom i)

/-- `Ψ` is the ungraded `Ψ` conjugated by the identifications of ungraded and graded algebra
sheaves on `U` and on `Z`. -/
theorem toConormalAlgebraHom_eq : toConormalAlgebraHom i =
    (ungradedAlgebraSheafIsoGradedAlgebraSheaf i.coborderRange.toScheme
      (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _)).inv ≫
    toConormalUngradedHom i ≫
    (algebraPushforward i.liftCoborder).map (ungradedAlgebraSheafIsoGradedAlgebraSheaf Z
      (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int).hom := rfl

/-- On the ungraded presheaf of the extended Rees algebra, the ungraded `Ψ` is the ungraded
commutative-algebra map induced by `toConormalUnitalHom`. -/
theorem ungradedCommToSheaf_comp_toConormalUngradedHom :
    ungradedCommToSheaf i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _) ≫ (toConormalUngradedHom i).right.hom =
      ungradedCommHom (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _)
        (conormalPushforwardAlgebra i i.liftCoborder) (toConormalUnitalHom i) :=
  congrArg Subtype.val
    ((ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra (coborderIdeal i))
      (extReesGradedAlgebra_mul_comm _)
      (conormalPushforwardAlgebra i i.liftCoborder)).apply_symm_apply
      ((ungradedCommHomEquiv (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _) (conormalPushforwardAlgebra i i.liftCoborder)).symm
        (toConormalUnitalHom i)))

/-- **On a homogeneous section, the ungraded `Ψ` is `toConormalExtAdd`.** -/
theorem toConormalUngradedHom_app_incl (k : ℤ) (W : i.coborderRange.toScheme.Opens)
    (x : ((extReesGradedAlgebra (coborderIdeal i)).piece k).val.obj (op W)) :
    ((toConormalUngradedHom i).right.hom.app (op W)).hom
        (ungradedAlgebraSheafIncl i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
          (extReesGradedAlgebra_mul_comm _) k W x) =
      toConormalExtAdd i k (op W) x :=
  (ConcreteCategory.congr_hom
      (NatTrans.congr_app (ungradedCommToSheaf_comp_toConormalUngradedHom i) (op W))
      ((extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl k x)).trans
    (ungradedTotal_incl (extReesGradedAlgebra (coborderIdeal i))
      (conormalPushforwardAlgebra i i.liftCoborder) (toConormalUnitalHom i) k (op W) x)

/-- The ungraded `Ψ` is surjective on sections over an affine open of `U`. -/
theorem surjective_toConormalUngradedHom_app (W : i.coborderRange.toScheme.affineOpens) :
    Function.Surjective ((toConormalUngradedHom i).right.hom.app (op W.1)).hom := by
  have hW : IsAffineOpen (i.liftCoborder ⁻¹ᵁ W.1) := W.2.preimage i.liftCoborder
  have hsurjg :
      Function.Surjective (i.liftCoborder.appLE W.1 (i.liftCoborder ⁻¹ᵁ W.1) le_rfl).hom := by
    rw [Scheme.Hom.appLE_preimage_self]
    exact i.liftCoborder.app_surjective W.1 W.2
  have key : ∀ s : (conormalAlgebra i).algebra.toPresheafGradedAlgebra.Total
      (op (i.liftCoborder ⁻¹ᵁ W.1)),
      ∃ p, ((toConormalUngradedHom i).right.hom.app (op W.1)).hom p =
        (ungradedCommUnit Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int (i.liftCoborder ⁻¹ᵁ W.1)).hom s := by
    intro s
    induction s using Stacks.GradedAlgebra.incl_induction with
    | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
    | incl n y =>
        rcases lt_or_ge n 0 with hn | hn
        · have hy : y = 0 :=
            Stacks.subsingleton_of_isZero ((conormalAlgebra i).negative_isZero n hn) _ |>.elim _ _
          subst hy
          refine ⟨0, (map_zero _).trans ?_⟩
          exact ((congrArg _ (Stacks.GradedAlgebra.incl_zero _ _)).trans (map_zero _)).symm
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        have : (reesPiece (coborderIdeal i) (m : ℤ)).IsQuasicoherent :=
          reesPiece_isQuasicoherent (coborderIdeal i) (m : ℤ)
        obtain ⟨x, hx⟩ := Stacks.Conormal.pullbackSection_surjective i.liftCoborder
          (reesPiece (coborderIdeal i) (m : ℤ)) le_rfl W.2 hW hsurjg y
        refine ⟨ungradedAlgebraSheafIncl i.coborderRange.toScheme
          (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _) m W.1 x, ?_⟩
        refine (toConormalUngradedHom_app_incl i m W.1 x).trans ?_
        rw [toConormalExtAdd_of_nonneg i (Int.natCast_nonneg m)]
        exact congrArg (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int m (i.liftCoborder ⁻¹ᵁ W.1)) hx
    | add s s' hs hs' =>
        obtain ⟨p, hp⟩ := hs
        obtain ⟨p', hp'⟩ := hs'
        exact ⟨p + p', (map_add _ _ _).trans
          ((congrArg₂ (· + ·) hp hp').trans (map_add _ _ _).symm)⟩
  intro t
  obtain ⟨s, hs⟩ := (bijective_ungradedCommUnit_of_isAffineOpen Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int hW).2 t
  obtain ⟨p, hp⟩ := key s
  exact ⟨p, hp.trans hs⟩

/-- `Ψ` is surjective on sections over an affine open of `U`. -/
theorem surjective_toConormalAlgebraHom_app (W : i.coborderRange.toScheme.affineOpens) :
    Function.Surjective ((toConormalAlgebraHom i).right.hom.app (op W.1)).hom := by
  rw [toConormalAlgebraHom_eq]
  exact surjective_right_app_comp _ _ (op W.1)
    (surjective_right_app_of_iso (ungradedAlgebraSheafIsoGradedAlgebraSheaf
        i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _)).symm (op W.1))
    (surjective_right_app_comp _ _ (op W.1) (surjective_toConormalUngradedHom_app i W)
      (surjective_right_app_of_iso ((algebraPushforward i.liftCoborder).mapIso
        (ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int)) (op W.1)))

/-- The relative-spectrum situation of the extended Rees algebra of `ℐ` on `U`, whose glued
spectrum is the deformation space. -/
abbrev deformationSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  { base := i.coborderRange.toScheme, algebra := extReesAlgebraSheaf (coborderIdeal i) }

/-- The algebra map `Ψ`, composed with the identification of `𝒞_{Z/X,*}` with the pushed-forward
structure sheaf of `C_ZX`. -/
def normalConeToDeformationAlgebraHom :
    extReesAlgebraSheaf (coborderIdeal i) ⟶
      pushforwardAlgebra (normalConeToBase i ≫ i.liftCoborder) :=
  toConormalAlgebraHom i ≫
    (algebraPushforward i.liftCoborder).map (pushforwardAlgebraIso (conormalAlgebraSheaf i)).inv

/-- `normalConeToDeformationAlgebraHom` is surjective on sections over an affine open of `U`. -/
theorem surjective_normalConeToDeformationAlgebraHom_app
    (W : i.coborderRange.toScheme.affineOpens) :
    Function.Surjective ((normalConeToDeformationAlgebraHom i).right.hom.app (op W.1)).hom :=
  surjective_right_app_comp _ _ (op W.1) (surjective_toConormalAlgebraHom_app i W)
    (surjective_right_app_of_iso ((algebraPushforward i.liftCoborder).mapIso
      (pushforwardAlgebraIso (conormalAlgebraSheaf i)).symm) (op W.1))

/-- **The normal cone as the special fibre of the deformation space**: the morphism
`κ : C_ZX ⟶ D` over `g : Z ⟶ U` whose algebra component is `Ψ`. -/
def normalConeToDeformation : normalCone i ⟶ deformationSpace (coborderIdeal i) :=
  pairToHom (s := deformationSituation i)
    ⟨normalConeToBase i ≫ i.liftCoborder,
      (extReesAlgebraSheaf (coborderIdeal i)).pairHomEquiv (normalConeToBase i ≫ i.liftCoborder)
        (normalConeToDeformationAlgebraHom i)⟩

/-- **`κ` lies over `g`.** -/
theorem normalConeToDeformation_toBase :
    normalConeToDeformation i ≫ deformationSpaceToBase (coborderIdeal i) =
      normalConeToBase i ≫ i.liftCoborder :=
  pairToHom_toBase (s := deformationSituation i) _

/-- **The normal cone is a closed subscheme of the deformation space**: `κ` is a closed
immersion. -/
instance isClosedImmersion_normalConeToDeformation :
    IsClosedImmersion (normalConeToDeformation i) :=
  Stacks.RelativeSpec.isClosedImmersion_pairToHom (s := deformationSituation i) _
    (fun W : i.coborderRange.toScheme.affineOpens => W) (iSup_affineOpens_eq_top _)
    (fun W => Stacks.RelativeSpec.isAffineOpen_toBase_preimage (normalConeSituation i)
      ⟨i.liftCoborder ⁻¹ᵁ W.1, W.2.preimage i.liftCoborder⟩)
    (fun W => surjective_normalConeToDeformationAlgebraHom_app i W)

end Stacks.Deformation

end
