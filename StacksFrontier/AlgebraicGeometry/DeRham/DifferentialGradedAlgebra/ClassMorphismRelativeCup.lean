module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismCupProduct

/-!
# The morphism `ξ' : Ω^• ⟶ Ω^•[n]` and the relative cup product

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, `Ω^•` the
relative de Rham complex and `ξ' : Ω^• ⟶ Ω^•[n]` the morphism of `D(A)` attached by Remark 0FU7 to
`ξ ∈ H^n_{dR}`. Property (5) of the remark says that `Rf_*ξ'` is compatible with the relative cup
product `μ` of Remark 0FU6 on `Rf_*Ω^•` and the one on `Rf_*Ω^•[n]`.

As in Differential Graded Sheaves, Section 0FU3, this rests on the `Ω^•`-linearity of `ξ'` in the
derived category: `ξ'` is the image of a morphism of `D(Ω^•, d)`, hence of a roof
`Ω^• ⟶ I ⟵ Ω^•[n]` of maps of right differential graded modules, and maps of right differential
graded modules commute with the action `M ⊗^𝐋 Ω^• ⟶ Tot(M ⊗ Ω^•) ⟶ M`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.derivedAction`: the action `M ⊗^𝐋 𝒜 ⟶ M` in `D(𝒪_X)` of a
  right differential graded module.
* `AlgebraicGeometry.SheafOfModules.derivedShiftedMul`: the multiplication
  `𝒜[n] ⊗^𝐋 𝒜 ⟶ 𝒜[n]` of the translate, the shift of the multiplication of `𝒜` (no sign).

## Main results

* `AlgebraicGeometry.SheafOfModules.derivedForgetShiftedHom_derivedAction`: a morphism
  `𝒜 ⟶ 𝒜[n]` of `D(𝒜, d)` is `𝒜`-linear in `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

section Generic

variable {S : RingedSpace.{u, u}}
  (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf S.sheaf))

/-- **The derived action of a right differential graded module**
`M ⊗^𝐋 𝒜 ⟶ Tot(M ⊗ 𝒜) ⟶ M` in `D(𝒪_X)`: the canonical map from the derived to the ordinary
tensor product, followed by the action `AlgebraicGeometry.SheafOfModules.dgAction`. -/
noncomputable def derivedAction (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).obj
        (DerivedCategory.Q.obj M.complex, DerivedCategory.Q.obj 𝒜.complex) ⟶
      DerivedCategory.Q.obj M.complex :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app (M.complex, 𝒜.complex) ≫
    DerivedCategory.Q.map (dgAction M)

/-- **The derived action is natural along maps of right differential graded modules.** -/
theorem derivedAction_naturality
    {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜} (f : M ⟶ N) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (DerivedCategory.Q.map f.toHomologicalComplex ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
        derivedAction 𝒜 N =
      derivedAction 𝒜 M ≫ DerivedCategory.Q.map f.toHomologicalComplex := by
  have hn := (Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).naturality
    (X := (M.complex, 𝒜.complex)) (Y := (N.complex, 𝒜.complex)) (f.toHomologicalComplex ×ₘ 𝟙 _)
  have ha := dgAction_naturality f
  have hid : DerivedCategory.Q.map (𝟙 𝒜.complex) = 𝟙 (DerivedCategory.Q.obj 𝒜.complex) :=
    DerivedCategory.Q.map_id _
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [hid] at hn
  rw [Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map] at hn
  have h4 := (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map ha).trans
    (DerivedCategory.Q.map_comp _ _))
  unfold derivedAction
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h4).trans (Category.assoc _ _ _).symm)))

/-- **The multiplication of a module whose complex is the translate `𝒜[n]`** in `D(𝒪_X)`:
`𝒜[n] ⊗^𝐋 𝒜 ⟶ 𝒜[n]` is the derived action of `N`, read through the identification of the complex
of `N` with `𝒜[n]` and the commutation of the localization with the translation. -/
noncomputable def derivedActionOfShift (n : ℤ)
    (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜)
    (hN : N.complex = 𝒜.complex⟦n⟧) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).obj
        ((DerivedCategory.Q.obj 𝒜.complex)⟦n⟧, DerivedCategory.Q.obj 𝒜.complex) ⟶
      (DerivedCategory.Q.obj 𝒜.complex)⟦n⟧ :=
  (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
      (((DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex ≫
        eqToHom (congrArg DerivedCategory.Q.obj hN.symm)) ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
    derivedAction 𝒜 N ≫ eqToHom (congrArg DerivedCategory.Q.obj hN) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app 𝒜.complex

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **The multiplication `μ_{𝒜[n]}` of the translate `𝒜[n]`** in `D(𝒪_X)`: the derived action of
the right differential graded module `𝒜[n]` (Differential Graded Sheaves, Section 0FRY), on
`(𝒜)[n] ⊗^𝐋 𝒜`. -/
noncomputable def derivedShiftedMul (n : ℤ) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).obj
        ((DerivedCategory.Q.obj 𝒜.complex)⟦n⟧, DerivedCategory.Q.obj 𝒜.complex) ⟶
      (DerivedCategory.Q.obj 𝒜.complex)⟦n⟧ :=
  derivedActionOfShift 𝒜 n
    (_root_.SheafOfModules.DifferentialGradedModule.shiftedModule
      (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n)
    (_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj_complex
      (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜 n
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))

/-- The naturality squares behind `roof_derivedAction`, with every object and morphism a
variable. -/
theorem key_paste {C : Type*} [Category* C] {P Q Q' R W W' : C}
    (Tx : P ⟶ Q') (aI : Q' ⟶ W') (ar : P ⟶ R) (x : R ⟶ W') (TΦ : P ⟶ Q) (Tb : Q ⟶ Q')
    (aN : Q ⟶ W) (b : W ⟶ W') (Φ : R ⟶ W)
    (nx : Tx ≫ aI = ar ≫ x) (nb : Tb ≫ aI = aN ≫ b) (hs : Tx = TΦ ≫ Tb) (hx : x = Φ ≫ b) :
    (TΦ ≫ aN) ≫ b = (ar ≫ Φ) ≫ b := by
  rw [Category.assoc, ← nb, ← Category.assoc, ← hs, nx, hx, Category.assoc]

/-- The cancellation behind `roof_derivedAction`, with every object and morphism a variable. -/
theorem roof_action_paste {C : Type*} [Category* C] (T : C × C ⥤ C)
    {a b b' z : C} (F : a ⟶ b) (ci : b ⟶ b') (h : b' = b') (aN : T.obj (b', z) ⟶ b')
    (e : b' = b') (cH : b' ⟶ b) (ar : T.obj (a, z) ⟶ a)
    (key : T.map ((F ≫ ci) ×ₘ 𝟙 z) ≫ aN = ar ≫ F ≫ ci) (hF : (F ≫ ci) ≫ cH = F) :
    T.map (F ×ₘ 𝟙 z) ≫ T.map ((ci ≫ eqToHom h) ×ₘ 𝟙 z) ≫ aN ≫ eqToHom e ≫ cH = ar ≫ F := by
  rw [eqToHom_refl, Category.comp_id, Category.id_comp, ← Category.assoc,
    ← Functor.map_comp, prod_comp, Category.comp_id, reassoc_of% key]
  simp only [Category.assoc] at hF ⊢
  rw [hF]

/-- **A roof is linear for the derived action.** For `F : 𝒜 ⟶ 𝒜[n]` and a roof as in `roof_cup`,
`F` commutes with the derived action: `(F ⊗ 1) ≫ μ_{𝒜[n]} = μ_𝒜 ≫ F` in `D(𝒪_X)`. -/
theorem roof_derivedAction (n : ℤ)
    (F : DerivedCategory.Q.obj 𝒜.complex ⟶ (DerivedCategory.Q.obj 𝒜.complex)⟦n⟧)
    {I N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜}
    (x : _root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜 ⟶ I) (b : N ⟶ I)
    (hb : QuasiIso b.toHomologicalComplex) (hN : N.complex = 𝒜.complex⟦n⟧)
    (hroof : F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex ≫
      eqToHom (congrArg DerivedCategory.Q.obj hN.symm) ≫
        DerivedCategory.Q.map b.toHomologicalComplex =
          DerivedCategory.Q.map x.toHomologicalComplex) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (F ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫ derivedActionOfShift 𝒜 n N hN =
      derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) ≫ F := by
  obtain ⟨Nc, Nmul, h₁, h₂, h₃⟩ := N
  dsimp only at hN b hb hroof ⊢
  subst hN
  simp only [eqToHom_refl, Category.id_comp] at hroof
  let TX :=
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)
  have hQx : DerivedCategory.Q.map x.toHomologicalComplex =
      (F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex) ≫
        DerivedCategory.Q.map b.toHomologicalComplex :=
    hroof.symm.trans (Category.assoc _ _ _).symm
  have nx := derivedAction_naturality 𝒜 x
  have nb := derivedAction_naturality 𝒜 b
  have hQb : IsIso (DerivedCategory.Q.map b.toHomologicalComplex) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hb
  have hsplit : TX.map (((F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex) ≫
      DerivedCategory.Q.map b.toHomologicalComplex) ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) =
      TX.map ((F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex) ×ₘ
        𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
        TX.map (DerivedCategory.Q.map b.toHomologicalComplex ×ₘ
          𝟙 (DerivedCategory.Q.obj 𝒜.complex)) := by
    rw [← Functor.map_comp, prod_comp, Category.comp_id]
  have hsx : TX.map (DerivedCategory.Q.map x.toHomologicalComplex ×ₘ
      𝟙 (DerivedCategory.Q.obj 𝒜.complex)) =
      TX.map ((F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex) ×ₘ
        𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
        TX.map (DerivedCategory.Q.map b.toHomologicalComplex ×ₘ
          𝟙 (DerivedCategory.Q.obj 𝒜.complex)) :=
    (congrArg (fun g => TX.map (g ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex))) hQx).trans hsplit
  have key : TX.map ((F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex) ×ₘ
        𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫ derivedAction 𝒜 ⟨_, Nmul, h₁, h₂, h₃⟩ =
      derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) ≫
        F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex :=
    (@cancel_mono _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hQb) _ _).1
      (key_paste _ _ _ _ _ _ _ _ _ nx nb hsx hQx)
  have hF : (F ≫ (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app 𝒜.complex = F := by
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id F
  unfold derivedActionOfShift
  exact roof_action_paste TX F _ _ _ _ _ _ key hF

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- The translation functors of `D(𝒜, d)`. -/
noncomputable local instance :
    HasShift (_root_.SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u} 𝒜) ℤ :=
  _root_.SheafOfModules.DifferentialGradedModule.derivedCategoryHasShift
    (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **A morphism `𝒜 ⟶ 𝒜[n]` of `D(𝒜, d)` is `𝒜`-linear in `D(𝒪_X)`**: its underlying morphism
`F` of `D(𝒪_X)` satisfies `(F ⊗ 1) ≫ μ_{𝒜[n]} = μ_𝒜 ≫ F`, for the derived actions
`μ_𝒜 : 𝒜 ⊗^𝐋 𝒜 ⟶ 𝒜` and `μ_{𝒜[n]} : 𝒜[n] ⊗^𝐋 𝒜 ⟶ 𝒜[n]` of the regular module and of its
translate. -/
theorem derivedForgetShiftedHom_derivedAction (n : ℤ)
    (g : (_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u} 𝒜).obj
        ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient 𝒜).obj
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)) ⟶
      ((_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u} 𝒜).obj
        ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient 𝒜).obj
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)))⟦n⟧) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (_root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom
          (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n g ×ₘ
          𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫ derivedShiftedMul 𝒜 n =
      derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) ≫
        _root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom
          (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n g := by
  obtain ⟨I, x, b, hb, hroof⟩ :=
    _root_.SheafOfModules.DifferentialGradedModule.exists_derivedForgetShiftedHom_comp_eq
      (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜 n g
  exact roof_derivedAction 𝒜 n _ x b hb _ hroof

/-- The pasting behind `relativeCupProduct_derivedForgetShiftedHom`, with every object and morphism
a variable. -/
theorem relative_paste {C D : Type*} [Category* C] [Category* D] (P : C ⥤ D) {Z₁ Z₂ K₁ K₂ : C}
    {Y₁ Y₂ : D} (t t₀ : Y₁ ⟶ Y₂) (r : Y₁ ⟶ P.obj Z₁) (r' : Y₂ ⟶ P.obj Z₂) (Tk : Z₁ ⟶ Z₂)
    (m' : Z₂ ⟶ K₂) (m : Z₁ ⟶ K₁) (k : K₁ ⟶ K₂) (ht : t = t₀) (hn : t₀ ≫ r' = r ≫ P.map Tk)
    (hl : Tk ≫ m' = m ≫ k) : t ≫ r' ≫ P.map m' = (r ≫ P.map m) ≫ P.map k := by
  subst ht
  rw [← Category.assoc, hn, Category.assoc, ← P.map_comp, hl, P.map_comp, Category.assoc]

variable {Y : RingedSpace.{u, u}} (f : S ⟶ Y)

/-- **An `𝒜`-linear morphism `𝒜 ⟶ 𝒜[n]` is compatible with the relative cup products.** For a
morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and a morphism `F : 𝒜 ⟶ 𝒜[n]` of `D(𝒪_X)`
with `(F ⊗ 1) ≫ μ_{𝒜[n]} = μ_𝒜 ≫ F`, the square

`Rf_*𝒜 ⊗^𝐋 Rf_*𝒜 --μ--> Rf_*𝒜`, `Rf_*𝒜[n] ⊗^𝐋 Rf_*𝒜 --μ--> Rf_*𝒜[n]`

with vertical maps `Rf_*F ⊗ 1` and `Rf_*F` commutes in `D(𝒪_Y)`, where `μ` is the relative cup
product of Tag 0B68 followed by `Rf_*` of the derived action of `𝒜`, resp. of its translate. -/
theorem relativeCupProduct_comp_of_derivedAction (n : ℤ)
    (F : DerivedCategory.Q.obj 𝒜.complex ⟶ (DerivedCategory.Q.obj 𝒜.complex)⟦n⟧)
    (hF : (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (F ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫ derivedShiftedMul 𝒜 n =
      derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) ≫ F) :
    Eq ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map F ×ₘ
          𝟙 ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj
            (DerivedCategory.Q.obj 𝒜.complex))) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f
          ((DerivedCategory.Q.obj 𝒜.complex)⟦n⟧) (DerivedCategory.Q.obj 𝒜.complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (derivedShiftedMul 𝒜 n))
      ((Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f
          (DerivedCategory.Q.obj 𝒜.complex) (DerivedCategory.Q.obj 𝒜.complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map F) := by
  have hn := Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural f F
    (𝟙 (DerivedCategory.Q.obj 𝒜.complex))
  exact relative_paste _ _ _ _ _ _ _ _ _
    (congrArg (fun g => (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map F ×ₘ g))
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map_id _).symm)
    hn hF

end Generic

end AlgebraicGeometry.SheafOfModules
