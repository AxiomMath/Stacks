module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CoefficientUniverseReduction
public import StacksFrontier.CategoryTheory.Adjunction.MateFullyFaithfulTransport
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# The base change comparison of abelian étale sheaves and the universe lift

Let `U = etaleUlift` be the universe lift of the coefficients of abelian sheaves on small étale
sites, from `AddCommGrpCat.{u + 1}` to `AddCommGrpCat.{max (u + 1) v}`. Direct image commutes
with `U` on the nose (`Stacks.Sheaves.UniverseLift.sheafPushforwardContinuousULiftIso`), so for a
morphism of schemes `k` there is a canonical comparison `λ_k : k⁻¹ ∘ U ⟶ U ∘ k⁻¹`, the mate of
that identification under the two inverse-image/direct-image adjunctions.

This file proves that `λ_k` is invertible, that it is compatible with the identifications of the
inverse image of a composite, and that it intertwines the underived base change comparisons
`Stacks.EtaleCohomology.etaleAbelianBaseChange` of a commutative square at the two coefficient
universes:
`g⁻¹ f_* (U K) ⟶ f'_* (g')⁻¹ (U K) ⟶ f'_* U ((g')⁻¹ K)` is
`g⁻¹ U (f_* K) ⟶ U (g⁻¹ f_* K) ⟶ U (f'_* (g')⁻¹ K)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianInverseImageUliftMate`: the comparison `λ_k`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianInverseImageUliftMate_app`: `λ_k` is invertible.
* `Stacks.EtaleCohomology.etaleAbelianBaseChange_ulift`: the base change comparisons at the two
  coefficient universes are intertwined by `λ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.UniverseLift Stacks.CategoryTheory.MateTransport

universe v u

namespace Stacks.EtaleCohomology

-- the sheafification instance the base change comparison was built with; the coefficient-lift
-- files imported here provide another one, which the kernel could only compare by unfolding
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

section Mate

variable {X Y : Scheme.{u}} (k : X ⟶ Y)

/-- Direct image of abelian étale sheaves commutes with the universe lift of the coefficients
(`Stacks.Sheaves.UniverseLift.sheafPushforwardContinuousULiftIso`, an identity). -/
def etaleAbelianDirectImageUliftIso :
    etaleAbelianDirectImage.{u, 0} k ⋙ etaleUlift.{v} Y ≅
      etaleUlift.{v} X ⋙ etaleAbelianDirectImage.{u, v} k :=
  sheafPushforwardContinuousULiftIso.{v, u + 1} Y.smallEtaleTopology X.smallEtaleTopology
    (smallEtaleBaseChange k)

/-- The components of the forward map of `etaleAbelianDirectImageUliftIso` are identities. -/
@[simp]
theorem etaleAbelianDirectImageUliftIso_hom_app
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianDirectImageUliftIso.{v} k).hom.app M = 𝟙 _ :=
  rfl

/-- The components of the inverse map of `etaleAbelianDirectImageUliftIso` are identities. -/
@[simp]
theorem etaleAbelianDirectImageUliftIso_inv_app
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianDirectImageUliftIso.{v} k).inv.app M = 𝟙 _ :=
  rfl

/-- **Inverse image and the universe lift of the coefficients**: the comparison
`k⁻¹ ∘ U ⟶ U ∘ k⁻¹`, the mate of the identification `U ∘ k_* = k_* ∘ U` of direct images under
the adjunctions `k⁻¹ ⊣ k_*` at the two coefficient universes. -/
def etaleAbelianInverseImageUliftMate :
    etaleUlift.{v} Y ⋙ etaleAbelianInverseImage.{u, v} k ⟶
      etaleAbelianInverseImage.{u, 0} k ⋙ etaleUlift.{v} X :=
  (mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} k)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} k)).symm
      (etaleAbelianDirectImageUliftIso.{v} k).hom

/-- **The comparison `k⁻¹ ∘ U ⟶ U ∘ k⁻¹` is invertible**: the universe lift is fully faithful,
and `k⁻¹ (U M)` is a universe lift (`Stacks.EtaleCohomology.etaleAbelianInverseImageUliftIso`). -/
instance isIso_etaleAbelianInverseImageUliftMate_app
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianInverseImageUliftMate.{v} k).app M) :=
  isIso_mateEquiv_symm_app _ _ _
    (fullyFaithfulUliftSheafFunctor.{v, u + 1} Y.smallEtaleTopology)
    (fullyFaithfulUliftSheafFunctor.{v, u + 1} X.smallEtaleTopology) M
    ((etaleAbelianInverseImageUliftIso.{v} k).app M)

end Mate

section Composite

variable {P Q R : Scheme.{u}} (a : P ⟶ Q) (b : Q ⟶ R)

/-- The unit of the inverse-image/direct-image adjunction of a composite, followed by the direct
image of the identification of the inverse image of the composite, is the unit of the composite
adjunction. -/
theorem etaleAbelianInverseImageCompIso_unit
    (M : Sheaf R.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} (a ≫ b)).unit.app M ≫
        (etaleAbelianDirectImage.{u, v} (a ≫ b)).map
          ((etaleAbelianInverseImageCompIso.{u, v} a b).hom.app M) =
      (etaleAbelianInverseImageDirectImageAdj.{u, v} b).unit.app M ≫
        (etaleAbelianDirectImage.{u, v} b).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).unit.app
            ((etaleAbelianInverseImage.{u, v} b).obj M)) ≫
        (etaleAbelianDirectImageCompIso.{u, v} a b).hom.app _ := by
  refine (Adjunction.unit_leftAdjointUniq_hom_app
    (etaleAbelianInverseImageDirectImageAdj.{u, v} (a ≫ b))
    (((etaleAbelianInverseImageDirectImageAdj.{u, v} b).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} a)).ofNatIsoRight
        (etaleAbelianDirectImageCompIso.{u, v} a b)) M).trans ?_
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id, Adjunction.comp_unit_app]
  simp only [Category.assoc]
  rfl

/-- The identification of the direct image of a composite commutes with the universe lift. -/
theorem etaleAbelianDirectImageCompIso_ulift
    (N : Sheaf P.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianDirectImageCompIso.{u, v} a b).hom.app ((etaleUlift.{v} P).obj N) =
      (etaleUlift.{v} R).map ((etaleAbelianDirectImageCompIso.{u, 0} a b).hom.app N) :=
  rfl

/-- **The comparisons `λ` are compatible with the inverse image of a composite**:
`(a ≫ b)⁻¹ U ≅ a⁻¹ b⁻¹ U ⟶ a⁻¹ U b⁻¹ ⟶ U a⁻¹ b⁻¹` is `λ_{a ≫ b}` followed by `U` of the
identification at the lower coefficient universe. -/
theorem etaleAbelianInverseImageUliftMate_comp
    (M : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImageCompIso.{u, v} a b).hom.app ((etaleUlift.{v} R).obj M) ≫
        (etaleAbelianInverseImage.{u, v} a).map ((etaleAbelianInverseImageUliftMate.{v} b).app M) ≫
          (etaleAbelianInverseImageUliftMate.{v} a).app
            ((etaleAbelianInverseImage.{u, 0} b).obj M) =
      (etaleAbelianInverseImageUliftMate.{v} (a ≫ b)).app M ≫
        (etaleUlift.{v} P).map ((etaleAbelianInverseImageCompIso.{u, 0} a b).hom.app M) :=
  mateEquiv_symm_comp _ _ _ _ _ _ _ _ _
    (etaleAbelianDirectImageCompIso.{u, 0} a b) (etaleAbelianDirectImageCompIso.{u, v} a b)
    (etaleAbelianInverseImageCompIso.{u, 0} a b) (etaleAbelianInverseImageCompIso.{u, v} a b)
    (etaleAbelianInverseImageCompIso_unit.{0} a b) (etaleAbelianInverseImageCompIso_unit.{v} a b)
    (fun N => by
      simp only [etaleAbelianDirectImageUliftIso_hom_app, Category.id_comp, Category.comp_id,
        CategoryTheory.Functor.map_id]
      exact etaleAbelianDirectImageCompIso_ulift a b N) M

/-- `Stacks.EtaleCohomology.etaleAbelianInverseImageUliftMate_comp` with the inverses of the
identifications of the inverse image of a composite. -/
theorem etaleAbelianInverseImageUliftMate_comp_inv
    (M : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImageCompIso.{u, v} a b).inv.app ((etaleUlift.{v} R).obj M) ≫
        (etaleAbelianInverseImageUliftMate.{v} (a ≫ b)).app M =
      (etaleAbelianInverseImage.{u, v} a).map ((etaleAbelianInverseImageUliftMate.{v} b).app M) ≫
        (etaleAbelianInverseImageUliftMate.{v} a).app ((etaleAbelianInverseImage.{u, 0} b).obj M) ≫
          (etaleUlift.{v} P).map ((etaleAbelianInverseImageCompIso.{u, 0} a b).inv.app M) := by
  rw [← cancel_epi
      ((etaleAbelianInverseImageCompIso.{u, v} a b).hom.app ((etaleUlift.{v} R).obj M)),
    Iso.hom_inv_id_app_assoc, reassoc_of% (etaleAbelianInverseImageUliftMate_comp a b M),
    ← Functor.map_comp]
  simp

/-- `Stacks.EtaleCohomology.etaleAbelianInverseImageUliftMate_comp_inv` with the
identifications written as the inverses `(a ≫ b)⁻¹ ≅ b⁻¹ ⋙ a⁻¹` they are. -/
theorem etaleAbelianInverseImageUliftMate_comp_symm
    (M : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImageCompIso.{u, v} a b).symm.hom.app ((etaleUlift.{v} R).obj M) ≫
        (etaleAbelianInverseImageUliftMate.{v} (a ≫ b)).app M =
      (etaleAbelianInverseImage.{u, v} a).map
          (((mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} b)
            (etaleAbelianInverseImageDirectImageAdj.{u, v} b)).symm
              (etaleAbelianDirectImageUliftIso.{v} b).hom).app M) ≫
        (etaleAbelianInverseImageUliftMate.{v} a).app ((etaleAbelianInverseImage.{u, 0} b).obj M) ≫
          (etaleUlift.{v} P).map ((etaleAbelianInverseImageCompIso.{u, 0} a b).symm.hom.app M) :=
  etaleAbelianInverseImageUliftMate_comp_inv a b M

end Composite

section Square

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The base change comparison is the base change map of the square of adjunctions. -/
theorem etaleAbelianBaseChange_app_eq
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianBaseChange.{u, v} f g g' f' h).app K =
      Stacks.CategoryTheory.BaseChange.map (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
        (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
        ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
          eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h)) K := by
  -- `rfl` on the components makes the kernel reduce the projections of the mate; the
  -- definition, as an equality of natural transformations, is one delta step
  have hdef : etaleAbelianBaseChange.{u, v} f g g' f' h =
      Stacks.CategoryTheory.BaseChange.twoSquare (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
        (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
        ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
          eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h)) := rfl
  exact congrArg (fun t => NatTrans.app t K) hdef

/-- `Stacks.CategoryTheory.MateTransport.map_mateEquiv_symm` for the étale base change square
and the universe lift, before the identities of direct images are removed. -/
theorem etaleAbelianBaseChange_ulift_aux
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImage.{u, v} g).map
        ((etaleAbelianDirectImageUliftIso.{v} f).hom.app K) ≫
      Stacks.CategoryTheory.BaseChange.map (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
        (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
        ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
          eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h))
        ((etaleUlift.{v} X).obj K) ≫
      (etaleAbelianDirectImage.{u, v} f').map ((etaleAbelianInverseImageUliftMate.{v} g').app K) =
    (etaleAbelianInverseImageUliftMate.{v} g).app ((etaleAbelianDirectImage.{u, 0} f).obj K) ≫
      (etaleUlift.{v} Y').map (Stacks.CategoryTheory.BaseChange.map
        (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, 0} f')
        (etaleAbelianInverseImageCompIso.{u, 0} f' g).symm
        ((etaleAbelianInverseImageCompIso.{u, 0} g' f).symm ≪≫
          eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, 0} k) h)) K) ≫
      (etaleAbelianDirectImageUliftIso.{v} f').hom.app
        ((etaleAbelianInverseImage.{u, 0} g').obj K) :=
  map_mateEquiv_symm_of_eqToIso (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} f')
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
      (etaleAbelianDirectImageUliftIso.{v} f).hom (etaleAbelianDirectImageUliftIso.{v} f').hom
      (etaleAbelianInverseImageUliftMate.{v} g) (etaleAbelianInverseImageUliftMate.{v} g') h
      (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, 0} k)
      (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k)
      (fun k : X' ⟶ Y ↦ etaleAbelianInverseImageUliftMate.{v} k)
      (etaleAbelianInverseImageCompIso.{u, 0} f' g).symm
      (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
      (etaleAbelianInverseImageCompIso.{u, 0} g' f).symm
      (etaleAbelianInverseImageCompIso.{u, v} g' f).symm
      (etaleAbelianInverseImageUliftMate_comp_symm f' g)
      (etaleAbelianInverseImageUliftMate_comp_symm g' f)
      K

/-- **The base change comparisons at the two coefficient universes are intertwined by the
universe lift.** For a commutative square `g' ≫ f = f' ≫ g` and an abelian sheaf `K` on
`X_étale` with coefficients in `AddCommGrpCat.{u + 1}`, the comparison
`g⁻¹ f_* (U K) ⟶ f'_* (g')⁻¹ (U K)` followed by `f'_*` of `λ_{g'}` is `λ_g` at `f_* K` followed
by the universe lift of the comparison `g⁻¹ f_* K ⟶ f'_* (g')⁻¹ K`. -/
theorem etaleAbelianBaseChange_ulift (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianBaseChange.{u, v} f g g' f' h).app ((etaleUlift.{v} X).obj K) ≫
        (etaleAbelianDirectImage.{u, v} f').map ((etaleAbelianInverseImageUliftMate.{v} g').app K) =
      (etaleAbelianInverseImageUliftMate.{v} g).app ((etaleAbelianDirectImage.{u, 0} f).obj K) ≫
        (etaleUlift.{v} Y').map ((etaleAbelianBaseChange.{u, 0} f g g' f' h).app K) := by
  rw [etaleAbelianBaseChange_app_eq, etaleAbelianBaseChange_app_eq]
  have H := etaleAbelianBaseChange_ulift_aux f g g' f' h K
  have e₁ : (etaleAbelianInverseImage.{u, v} g).map
        ((etaleAbelianDirectImageUliftIso.{v} f).hom.app K) =
      𝟙 _ :=
    (etaleAbelianInverseImage.{u, v} g).map_id _
  have e₂ : (etaleAbelianDirectImageUliftIso.{v} f').hom.app
      ((etaleAbelianInverseImage.{u, 0} g').obj K) =
      𝟙 ((etaleAbelianDirectImage.{u, v} f').obj ((etaleUlift.{v} X').obj
        ((etaleAbelianInverseImage.{u, 0} g').obj K))) :=
    rfl
  rw [e₁, e₂] at H
  exact ((Category.id_comp _).symm.trans H).trans (congrArg (_ ≫ ·) (Category.comp_id _))

end Square

end Stacks.EtaleCohomology

end
