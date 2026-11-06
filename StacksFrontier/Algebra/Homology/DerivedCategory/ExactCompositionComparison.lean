module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The composition comparison of right derived functors along an exact second factor

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors with `G` exact, and let
`e : F ⋙ G ≅ H` identify the composite with a third additive functor `H : 𝒜 ⥤ 𝒞`. We
construct the comparison
$$
RF \circ RG \;\cong\; RH
$$
of functors `D⁺(𝒜) ⥤ D⁺(𝒞)` on bounded below derived categories, and characterize it by its
behaviour on the derived-functor units.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`: the comparison
  `RF ⋙ RG ≅ RH` for exact `G` and `e : F ⋙ G ≅ H`.

## Main results

* `CategoryTheory.Functor.mapHomotopyCategoryPlusNatIso_hom` and
  `CategoryTheory.Functor.mapHomotopyCategoryPlusNatIso_inv`: the action of an isomorphism of
  additive functors on bounded below homotopy categories is
  `Stacks.Cohomology.BaseChange.mapPlus`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac`: the factorization of the
  comparison through the derived-functor units of `RF`, `RG` and `RH`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_inv_app`: the same identity
  for the inverse of the comparison, when the three derived-functor units are invertible.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The action of an isomorphism of functors, degreewise -/

section Bridge

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]

/-- **The action of an isomorphism of additive functors on bounded below homotopy categories
is `Stacks.Cohomology.BaseChange.mapPlus`.** -/
theorem mapHomotopyCategoryPlusNatIso_hom {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    (mapHomotopyCategoryPlusNatIso e).hom = Stacks.Cohomology.BaseChange.mapPlus e.hom := by
  ext K
  rfl

/-- The inverse of the action of an isomorphism of additive functors on bounded below homotopy
categories is `Stacks.Cohomology.BaseChange.mapPlus` of its inverse. -/
theorem mapHomotopyCategoryPlusNatIso_inv {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    (mapHomotopyCategoryPlusNatIso e).inv = Stacks.Cohomology.BaseChange.mapPlus e.inv := by
  ext K
  rfl

end Bridge

/-! ### The comparison for an exact second factor -/

section ExactComposition

variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w''} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (e : F ⋙ G ≅ H)

/-- **The comparison `RF ⋙ RG ≅ RH` for exact `G` and `e : F ⋙ G ≅ H`.** It is the inverse of
the comparison `R(G ∘ F) ≅ RF ⋙ RG` followed by the isomorphism `R(G ∘ F) ≅ RH` induced by
`e`. -/
@[sga "4½ Etat_0 4.3.1" "special case"]
def rightDerivedFunctorPlusCompIsoOfExact :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
      (fun I _ => G.rightAcyclic_of_exact (F.obj I))).symm ≪≫
    rightDerivedFunctorPlusNatIso e

/-- The forward map of `rightDerivedFunctorPlusCompIsoOfExact` is the inverse of the comparison
`R(G ∘ F) ≅ RF ⋙ RG` followed by the isomorphism `R(G ∘ F) ≅ RH` induced by `e`. -/
theorem rightDerivedFunctorPlusCompIsoOfExact_hom :
    (rightDerivedFunctorPlusCompIsoOfExact F G H e).hom =
      (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
          (fun I _ => G.rightAcyclic_of_exact (F.obj I))).inv ≫
        (rightDerivedFunctorPlusNatIso e).hom := rfl

/-- **The characterizing factorization of `rightDerivedFunctorPlusCompIsoOfExact`.** On a
bounded below complex `N`, the derived-functor unit of `RG` at `F(N)` followed by `RG` of the
derived-functor unit of `RF` at `N` and then by the comparison is the degreewise comparison
`e` followed by the derived-functor unit of `RH`. -/
theorem rightDerivedFunctorPlusCompIsoOfExact_fac (N : HomotopyCategory.Plus A) :
    G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj N) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app N) ≫
          (rightDerivedFunctorPlusCompIsoOfExact F G H e).hom.app
            (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).hom.app N) ≫
        H.rightDerivedFunctorPlusUnith.app N := by
  have hhom : (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
      (fun I _ => G.rightAcyclic_of_exact (F.obj I))).hom =
      rightDerivedFunctorPlusComp F G := rfl
  have h1 : G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj N) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app N) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app N) ≫
        (F ⋙ G).rightDerivedFunctorPlusUnith.app N ≫
          (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
            (fun I _ => G.rightAcyclic_of_exact (F.obj I))).hom.app
              (DerivedCategory.Plus.Qh.obj N) := by
    rw [hhom, rightDerivedFunctorPlusComp_fac_app F G N, ← Category.assoc,
      ← DerivedCategory.Plus.Qh.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have h2 := rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctorPlus
    H.rightDerivedFunctorPlus (F ⋙ G).rightDerivedFunctorPlusUnith
    H.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A)
    (isoWhiskerRight (mapHomotopyCategoryPlusNatIso e) DerivedCategory.Plus.Qh).hom N
  have h3 : (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app N ≫
      (mapHomotopyCategoryPlusNatIso e).hom.app N =
      (mapHomotopyCategoryPlusCompIso e).hom.app N := by
    rw [mapHomotopyCategoryPlusNatIso_hom]
    exact Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_hom_comp
      (Stacks.Cohomology.BaseChange.mapPlus e.hom |>.app N)
  rw [rightDerivedFunctorPlusCompIsoOfExact_hom, NatTrans.comp_app, ← Category.assoc,
    ← Category.assoc, h1]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, rightDerivedFunctorPlusNatIso, rightDerivedNatIso_hom, h2,
    ← Category.assoc, isoWhiskerRight_hom, Functor.whiskerRight_app,
    ← DerivedCategory.Plus.Qh.map_comp, h3]

/-- **The characterizing factorization, solved for the inverse of the comparison.** When the
derived-functor units of `RF`, `RG` and `RH` are invertible, the inverse of the comparison
followed by the inverses of the units of `RF` and `RG` is the inverse of the unit of `RH`
followed by the inverse of the degreewise comparison `e`. -/
theorem rightDerivedFunctorPlusCompIsoOfExact_inv_app
    [IsIso F.rightDerivedFunctorPlusUnith] [IsIso G.rightDerivedFunctorPlusUnith]
    [IsIso H.rightDerivedFunctorPlusUnith] (N : HomotopyCategory.Plus A) :
    (rightDerivedFunctorPlusCompIsoOfExact F G H e).inv.app
          (DerivedCategory.Plus.Qh.obj N) ≫
        G.rightDerivedFunctorPlus.map
            ((asIso F.rightDerivedFunctorPlusUnith).inv.app N) ≫
          (asIso G.rightDerivedFunctorPlusUnith).inv.app
            (F.mapHomotopyCategoryPlus.obj N) =
      (asIso H.rightDerivedFunctorPlusUnith).inv.app N ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).inv.app N) := by
  have h : (asIso G.rightDerivedFunctorPlusUnith).hom.app
        (F.mapHomotopyCategoryPlus.obj N) ≫
      G.rightDerivedFunctorPlus.map ((asIso F.rightDerivedFunctorPlusUnith).hom.app N) ≫
        (rightDerivedFunctorPlusCompIsoOfExact F G H e).hom.app
          (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).hom.app N) ≫
        (asIso H.rightDerivedFunctorPlusUnith).hom.app N :=
    rightDerivedFunctorPlusCompIsoOfExact_fac F G H e N
  have : IsIso ((asIso G.rightDerivedFunctorPlusUnith).hom.app
      (F.mapHomotopyCategoryPlus.obj N)) :=
    (Iso.app (asIso G.rightDerivedFunctorPlusUnith) _).isIso_hom
  have : IsIso (G.rightDerivedFunctorPlus.map
      ((asIso F.rightDerivedFunctorPlusUnith).hom.app N)) :=
    (G.rightDerivedFunctorPlus.mapIso
      (Iso.app (asIso F.rightDerivedFunctorPlusUnith) N)).isIso_hom
  have : IsIso ((rightDerivedFunctorPlusCompIsoOfExact F G H e).hom.app
      (DerivedCategory.Plus.Qh.obj N)) :=
    (Iso.app (rightDerivedFunctorPlusCompIsoOfExact F G H e) _).isIso_hom
  rw [← cancel_epi ((asIso G.rightDerivedFunctorPlusUnith).hom.app
    (F.mapHomotopyCategoryPlus.obj N) ≫
      G.rightDerivedFunctorPlus.map ((asIso F.rightDerivedFunctorPlusUnith).hom.app N) ≫
        (rightDerivedFunctorPlusCompIsoOfExact F G H e).hom.app
          (DerivedCategory.Plus.Qh.obj N))]
  conv_rhs => rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc (G.rightDerivedFunctorPlus.map
      ((asIso F.rightDerivedFunctorPlusUnith).hom.app N)),
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
    ← DerivedCategory.Plus.Qh.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rfl

end ExactComposition

end CategoryTheory.Functor

end
