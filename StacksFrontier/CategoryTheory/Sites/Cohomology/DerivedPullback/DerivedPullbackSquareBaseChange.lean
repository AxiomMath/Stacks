module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomExactPullback

/-!
# The module base change map of a square of ringed topoi, followed by the unit

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi commuting up to a 2-isomorphism `s`. By
`AlgebraicGeometry.RingedToposHom.TwoIso.derivedBaseChange_fac`, the derived base change map at a
K-injective complex `I` is invertible exactly when the localized module base change map
`g^* f_* I ⟶ f'_* (g')^* I` followed by the derived-functor unit of `Rf'_*` is. This file turns
the latter into a statement about complexes: it holds exactly when the module base change map
followed by `f'_*` of a K-injective resolution of `(g')^* I` is a quasi-isomorphism.

## Main results

All in the namespace `Stacks.Cohomology.ProjectionFormulaOfToposHom`.

* `moduleBaseChange_app_eq_map`: the module base change map is
  `Stacks.CategoryTheory.BaseChange.map` of the two adjunctions.
* `isIso_moduleBaseChangeComplex_comp_unit_iff_quasiIso`: the localized module base change map
  followed by the derived-functor unit is invertible exactly when the module base change map
  followed by `f'_*` of a K-injective resolution of `(g')^* I` is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward

namespace Stacks.Cohomology.ProjectionFormulaOfToposHom

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))

/-- Let `u : G ⋙ L' ⟶ L ⋙ RG` be a natural transformation, `φ : A ⟶ G B` and `t : B ⟶ T` with
`L t` and `u_T` invertible. Then `L' φ ≫ u_B` is invertible exactly when `L' (φ ≫ G t)` is. -/
theorem _root_.Stacks.CategoryTheory.isIso_map_comp_app_iff {H H' D D' : Type*} [Category H]
    [Category H'] [Category D] [Category D'] {G : H ⥤ H'} {L : H ⥤ D} {L' : H' ⥤ D'}
    {RG : D ⥤ D'} (u : G ⋙ L' ⟶ L ⋙ RG) {A : H'} {B T : H} (φ : A ⟶ G.obj B) (t : B ⟶ T)
    [IsIso (L.map t)] [IsIso (u.app T)] :
    IsIso (L'.map φ ≫ u.app B) ↔ IsIso (L'.map (φ ≫ G.map t)) := by
  have h : L'.map (φ ≫ G.map t) ≫ u.app T = (L'.map φ ≫ u.app B) ≫ RG.map (L.map t) := by
    have hn := u.naturality t
    simp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [Functor.map_comp, Category.assoc, hn, Category.assoc]
  rw [← isIso_comp_right_iff (L'.map (φ ≫ G.map t)) (u.app T), h,
    isIso_comp_right_iff _ (RG.map (L.map t))]

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- The module base change map of the square is the base change map
`Stacks.CategoryTheory.BaseChange.map` of the adjunctions `f^* ⊣ f_*`, `(f')^* ⊣ f'_*` along the
identification `(f')^* g^* ≅ (g')^* f^*`. -/
theorem moduleBaseChange_app_eq_map
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (RingedToposHom.TwoIso.moduleBaseChange s).app M =
      Stacks.CategoryTheory.BaseChange.map (RingedToposHom.pullbackAdjPushforwardModules f)
        (RingedToposHom.pullbackAdjPushforwardModules f')
        (RingedToposHom.TwoIso.squarePullbackIso s) (Iso.refl _) M := by
  simp only [RingedToposHom.TwoIso.moduleBaseChange, Stacks.CategoryTheory.BaseChange.map,
    Stacks.CategoryTheory.BaseChange.twoSquare, Stacks.CategoryTheory.BaseChange.pullbackComparison,
    Iso.refl_inv, Category.comp_id]

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- **The module base change map of the square followed by the derived-functor unit, at a
complex.** For a complex `I` of `𝒪_𝒞`-modules and a quasi-isomorphism `t : (g')^* I ⟶ T` into a
K-injective complex, the localized module base change map `g^* f_* I ⟶ f'_* (g')^* I` followed by
the derived-functor unit of `Rf'_*` is invertible exactly when the module base change map followed
by `f'_* t` is a quasi-isomorphism. -/
theorem isIso_moduleBaseChangeComplex_comp_unit_iff_quasiIso
    [IsGrothendieckAbelian.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {T : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ℤ}
    (t : (g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T)
    [QuasiIso t] (hT : T.IsKInjective) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (RingedToposHom.TwoIso.moduleBaseChangeComplex s I)) ≫
      ((pushforwardOnHomotopy (X := X') (Y := Y') f').totalRightDerivedUnit DerivedCategory.Qh
          (sourceQuasiIso X')).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ↔
    QuasiIso (RingedToposHom.TwoIso.moduleBaseChangeComplex s I ≫
        ((RingedToposHom.pushforwardModules f').mapHomologicalComplex
          (ComplexShape.up ℤ)).map t) := by
  have hs :
      IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)) :=
    (DerivedCategory.isIso_Qh_map_iff _).2
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (inferInstanceAs (QuasiIso t)))
  have hu : IsIso (((pushforwardOnHomotopy (X := X') (Y := Y') f').totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso X')).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj T)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh _ _ T hT
  exact (Stacks.CategoryTheory.isIso_map_comp_app_iff
    ((pushforwardOnHomotopy (X := X') (Y := Y') f').totalRightDerivedUnit DerivedCategory.Qh
      (sourceQuasiIso X')) _ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)).trans
    ((DerivedCategory.isIso_Qh_map_iff _).trans
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (RingedToposHom.TwoIso.moduleBaseChangeComplex s I ≫
        ((RingedToposHom.pushforwardModules f').mapHomologicalComplex (ComplexShape.up ℤ)).map t)))

end Stacks.Cohomology.ProjectionFormulaOfToposHom
