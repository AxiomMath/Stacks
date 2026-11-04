module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence

/-!
# The map `G ⟶ RH ∘ F` attached to an identification `G ≅ H ∘ F` with `F` and `G` exact

Let `A`, `B`, `C` be abelian categories, `F : A ⥤ B` and `G : A ⥤ C` exact functors and
`H : B ⥤ C` an additive functor with a right derived functor `RH : D(B) ⥤ D(C)` on the unbounded
derived categories, and let `Θ : G ≅ F ⋙ H`. The exact functors need no deriving, and `Θ`
induces a canonical transformation

`G ⟶ F ⋙ RH`

of functors `D(A) ⥤ D(C)`: on a complex `P` it is `G P ≅ H(F P) ⟶ RH(F P)`, the second arrow the
unit of `RH`. This is the shape of the map of [Stacks, Tag 0F7G], `g_! K ⟶ Rh_*(f_! K)`, built from
`g_! = h_* ∘ f_!`.

The map is invertible at `P` exactly when the unit of `RH` is invertible at `F P`; when the source
of `H` is Grothendieck abelian this is the case as soon as `H` carries some quasi-isomorphism from
`F P` to a K-injective complex to a quasi-isomorphism.

## Main definitions

* `Stacks.ExactCompDerived.map`: the transformation `G ⟶ F ⋙ RH`.

## Main results

* `Stacks.ExactCompDerived.map_app_Qh`: its value on a complex.
* `Stacks.ExactCompDerived.isIso_map_app_Qh_iff`: it is invertible at a complex `P` iff the unit of
  `RH` is invertible at `F P`.
* `Stacks.ExactCompDerived.isIso_unit_app_of_quasiIso_map`: the unit of `RH` is invertible at a
  complex `L` as soon as `H` carries a K-injective resolution of `L` to a quasi-isomorphism.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace Stacks.ExactCompDerived

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : A ⥤ C) (H : B ⥤ C) [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (Θ : G ≅ F ⋙ H)
  (RH : DerivedCategory B ⥤ DerivedCategory C)
  (αH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)

/-- The transformation `Qh ⋙ G ⟶ Qh ⋙ F ⋙ RH` on the homotopy category of `A` out of which
`Stacks.ExactCompDerived.map` is descended. -/
def mapAux :
    DerivedCategory.Qh ⋙ G.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ F.mapDerivedCategory ⋙ RH :=
  G.mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso Θ.symm (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) αH ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.mapDerivedCategoryFactorsh.inv RH ≫
    (Functor.associator _ _ _).hom

/-- **The transformation `G ⟶ F ⋙ RH`** of functors `D(A) ⥤ D(C)` attached to an identification
`Θ : G ≅ F ⋙ H` with `F` and `G` exact: on a complex `P` it is `G P ≅ H(F P)` followed by the unit
of `RH` at `F P` (`Stacks.ExactCompDerived.map_app_Qh`). -/
def map : G.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ RH :=
  Localization.liftNatTrans DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ _ (mapAux F G H Θ RH αH)

/-- The value of `Stacks.ExactCompDerived.map` on a complex: the identification `G P ≅ H(F P)`
followed by the unit of `RH` at `F P`. -/
theorem map_app_Qh (P : HomotopyCategory A (ComplexShape.up ℤ)) :
    (map F G H Θ RH αH).app (DerivedCategory.Qh.obj P) =
      G.mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso Θ.symm (ComplexShape.up ℤ)).inv.app P) ≫
        αH.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        RH.map (F.mapDerivedCategoryFactorsh.inv.app P) := by
  simp [map, mapAux]

/-- `Stacks.ExactCompDerived.map` is invertible at a complex `P` exactly when the unit of `RH` is
invertible at `F P`. -/
theorem isIso_map_app_Qh_iff (P : HomotopyCategory A (ComplexShape.up ℤ)) :
    IsIso ((map F G H Θ RH αH).app (DerivedCategory.Qh.obj P)) ↔
      IsIso (αH.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj P)) := by
  rw [map_app_Qh]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

/-- `Stacks.ExactCompDerived.map` is invertible as soon as the unit of `RH` is invertible at `F P`
for every complex `P`. -/
theorem isIso_map_of_forall (h : ∀ P : HomotopyCategory A (ComplexShape.up ℤ),
    IsIso (αH.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj P))) :
    IsIso (map F G H Θ RH αH) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K => ?_
  obtain ⟨P, ⟨e⟩⟩ : ∃ P, Nonempty (DerivedCategory.Qh.obj P ≅ K) :=
    ⟨_, ⟨(Localization.essSurj DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).mem_essImage K |>.getIso⟩⟩
  exact (NatTrans.isIso_app_iff_of_iso _ e).1 ((isIso_map_app_Qh_iff F G H Θ RH αH P).2 (h P))

variable [IsGrothendieckAbelian.{w} B]
  [RH.IsRightDerivedFunctor αH (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]

/-- `Qh` sends the class of a quasi-isomorphism of complexes to an isomorphism. -/
private theorem isIso_Qh_map_quotient_map {T : Type*} [Category* T] [Abelian T]
    [HasDerivedCategory T] {X Y : CochainComplex T ℤ} (s : X ⟶ Y) [QuasiIso s] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient T (ComplexShape.up ℤ)).map s)) := by
  rw [← Functor.comp_map]
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso T) s).2 inferInstance

/-- **The unit of `RH` is invertible at a complex `L` whose K-injective resolution `H` carries to a
quasi-isomorphism.** The unit is invertible at the K-injective complex, and natural. -/
theorem isIso_unit_app_of_quasiIso_map {L J : CochainComplex B ℤ} (s : L ⟶ J) [QuasiIso s]
    (hJ : J.IsKInjective) (hs : QuasiIso ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    IsIso (αH.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) := by
  have hJ' := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective.{w}
    (H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh RH αH J hJ
  have hn := αH.naturality ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)) :=
    isIso_Qh_map_quotient_map s
  have h₂ : IsIso ((H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)) :=
    isIso_Qh_map_quotient_map ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s)
  dsimp only [Functor.comp_map] at hn
  have : IsIso (αH.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) ≫
      RH.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s))) := by
    rw [← hn]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₂ hJ'
  exact IsIso.of_isIso_comp_right _ (RH.map (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)))

end Stacks.ExactCompDerived

end
