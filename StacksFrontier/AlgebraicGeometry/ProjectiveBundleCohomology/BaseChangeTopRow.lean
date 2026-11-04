module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeTop
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DualTensorBaseChange

/-!
# The row `q = n` of Tag 01XX under base change

Let `g : S' ⟶ S` be a morphism of schemes, `E` finite locally free of constant rank `n + 1` with
`n ≥ 1`, `E' ≅ g^*E`, and `b : 𝐏(E') ⟶ 𝐏(E)` the morphism of projective bundles over `g`. The base
change map `g^* Rⁿ π_* 𝒪(d) ⟶ Rⁿ π'_* 𝒪'(d)` corresponds, under the identifications
`Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`, to the dual base-change map along
`g^*(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E) ≅ Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section PFSquare

/-- The diagram chase behind `projectionFormula_baseChange_iso`. -/
private theorem pf_chase {C C' : Type*} [Category C] [Category C'] (F : C' ⥤ C)
    {P₂ P₃ P₄ P₅ P₆ P₇ : C} {M N₁ N₂ N₃ : C'} {gP : P₂ ⟶ P₃} {cmp : P₃ ⟶ P₄}
    {tL : P₄ ⟶ P₇} {t₁ : P₄ ⟶ P₅} {t₂ : P₅ ⟶ P₆} {t₃ : P₆ ⟶ P₇} {bcM : P₂ ⟶ F.obj M}
    {T : M ⟶ N₃} {cs : M ⟶ N₁} {θ₁ : N₁ ⟶ N₂} {d₁ : N₂ ⟶ N₃} {pf₁ : F.obj N₁ ⟶ P₅}
    {pf₂ : F.obj N₂ ⟶ P₆} {pf₃ : F.obj N₃ ⟶ P₇}
    (hT : T = cs ≫ θ₁ ≫ d₁) (hTL : tL = t₁ ≫ t₂ ≫ t₃)
    (hPF : gP ≫ cmp ≫ t₁ = bcM ≫ F.map cs ≫ pf₁) (hNF : F.map θ₁ ≫ pf₂ = pf₁ ≫ t₂)
    (hNG : pf₂ ≫ t₃ = F.map d₁ ≫ pf₃) :
    bcM ≫ F.map T ≫ pf₃ = gP ≫ cmp ≫ tL := by
  subst hT hTL
  rw [reassoc_of% hPF, ← reassoc_of% hNF, hNG]
  simp only [Functor.map_comp, Category.assoc]

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g) {G : S.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] {G' : S'.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G']
  (γ : (Scheme.Modules.pullback g).obj G ≅ G') {F : X.Modules} {F' : X'.Modules}
  (θ : (Scheme.Modules.pullback g').obj F ≅ F') (q : ℕ)

/-- **The projection formula under base change**, along identifications `g'^* F ≅ F'` and
`g^* G ≅ G'`. -/
public theorem projectionFormula_baseChange_iso :
    Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat f g f' g' w q
        ((Stacks.ProjectionFormula.tensorRightInvertible X
          ((Scheme.Modules.pullback f).obj G)).obj F) ≫
      ((Scheme.Modules.pushforward f').rightDerived q).map
        (tensorPullbackIsoT g' θ (squarePullbackIso f g f' g' w G ≪≫
          (Scheme.Modules.pullback f').mapIso γ)).hom ≫
      (projectionFormulaDeltaApp f' G' F' q).hom =
    (Scheme.Modules.pullback g).map (projectionFormulaDeltaApp f G F q).hom ≫
      Stacks.RingedSpace.comparison g.toLRSHom.toShHom
        (((Scheme.Modules.pushforward f).rightDerived q).obj F) G ≫
      tensorMap (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
        f g f' g' w q F ≫ ((Scheme.Modules.pushforward f').rightDerived q).map θ.hom) γ.hom := by
  have hT : (tensorPullbackIsoT g' θ (squarePullbackIso f g f' g' w G ≪≫
        (Scheme.Modules.pullback f').mapIso γ)).hom =
      (Stacks.RingedSpace.comparison g'.toLRSHom.toShHom F ((Scheme.Modules.pullback f).obj G) ≫
        tensorMap (𝟙 _) (squarePullbackIso f g f' g' w G).hom) ≫
      (Stacks.ProjectionFormula.tensorRightInvertible X'
          ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj G))).map θ.hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.toRingedSpace.sheaf).flip.map
          ((Scheme.Modules.pullback f').map γ.hom)).app F' :=
    congrArg (Stacks.RingedSpace.comparison g'.toLRSHom.toShHom F _ ≫ ·)
      ((congrArg (tensorMap θ.hom) (rfl : (squarePullbackIso f g f' g' w G ≪≫
        (Scheme.Modules.pullback f').mapIso γ).hom = _)).trans (tensorMap_split₂ _ _ _))
  exact pf_chase ((Scheme.Modules.pushforward f').rightDerived q) hT
    (tensorMap_split₁ (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
        f g f' g' w q F) (((Scheme.Modules.pushforward f').rightDerived q).map θ.hom) γ.hom)
    (projectionFormula_higherBaseChangeNat f g f' g' w G q F)
    (projectionFormulaDeltaApp_naturality f' ((Scheme.Modules.pullback g).obj G) q θ.hom)
    (projectionFormulaDeltaApp_naturality_right f' γ.hom F' q)

end PFSquare

section Chase

/-- A square whose top row is a composite, one of whose factors is pulled back. -/
private theorem curry_square {C₁ C₂ C D : Type*} [Category C₁] [Category C₂] [Category C]
    [Category D] (G : C ⥤ D) (R : C₁ ⥤ C) (R' : C₂ ⥤ D) (Bf : C₁ ⥤ C₂)
    {M₀ M₁ M₂ : C₁} {N₀ N₁ N₂ : C₂} {c₁ : M₀ ⟶ M₁} {c₂ : M₁ ⟶ M₂} {c₁' : N₀ ⟶ N₁}
    {c₂' : N₁ ⟶ N₂} {θ : Bf.obj M₀ ⟶ N₀} {T : Bf.obj M₂ ⟶ N₂}
    {h₀ : G.obj (R.obj M₀) ⟶ R'.obj (Bf.obj M₀)} {h₂ : G.obj (R.obj M₂) ⟶ R'.obj (Bf.obj M₂)}
    (hnat : G.map (R.map (c₁ ≫ c₂)) ≫ h₂ = h₀ ≫ R'.map (Bf.map (c₁ ≫ c₂)))
    (hc : Bf.map (c₁ ≫ c₂) ≫ T = θ ≫ c₁' ≫ c₂') :
    G.map (R.map c₁) ≫ G.map (R.map c₂) ≫ h₂ ≫ R'.map T =
      (h₀ ≫ R'.map θ) ≫ R'.map c₁' ≫ R'.map c₂' := by
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, reassoc_of% hnat, ← Functor.map_comp, hc]
  simp only [Functor.map_comp, Category.assoc]

/-- A square along two isomorphisms, read backwards. -/
private theorem inv_square {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')
    {X Y : C} {P P' Q R : C'} {i : X ⟶ Y} {i' : Y ⟶ X} (hi : i' ≫ i = 𝟙 Y) {j : Q ⟶ R}
    {j' : R ⟶ Q} (hj : j ≫ j' = 𝟙 Q) {a₁ : F.obj X ⟶ P} {a₂ : P ⟶ Q} {c₁ : F.obj Y ⟶ P'}
    {c₂ : P' ⟶ R} (h : a₁ ≫ a₂ ≫ j = F.map i ≫ c₁ ≫ c₂) :
    F.map i' ≫ a₁ ≫ a₂ = (c₁ ≫ c₂) ≫ j' := by
  calc F.map i' ≫ a₁ ≫ a₂ = F.map i' ≫ a₁ ≫ a₂ ≫ j ≫ j' := by rw [hj, Category.comp_id]
    _ = F.map i' ≫ F.map i ≫ c₁ ≫ c₂ ≫ j' := by rw [reassoc_of% h]
    _ = (c₁ ≫ c₂) ≫ j' := by
      rw [← F.map_comp_assoc, hi, F.map_id, Category.id_comp, Category.assoc]

/-- A square whose top row is a composite of two squares. -/
private theorem comp_square {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')
    {X₀ X₁ X₂ : C} {Y₀ Y₁ Y₂ : C'} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {a' : Y₀ ⟶ Y₁}
    {b' : Y₁ ⟶ Y₂} {v₀ : F.obj X₀ ⟶ Y₀} {v₁ : F.obj X₁ ⟶ Y₁} {v₂ : F.obj X₂ ⟶ Y₂}
    (h₁ : F.map a ≫ v₁ = v₀ ≫ a') (h₂ : F.map b ≫ v₂ = v₁ ≫ b') :
    F.map (a ≫ b) ≫ v₂ = v₀ ≫ a' ≫ b' := by
  rw [Functor.map_comp_assoc, h₂, reassoc_of% h₁]

/-- A family of squares, transported along an equality of indices. -/
private theorem map_eqToHom_square {ι C₁ C₂ C C' : Type*} [Category C₁] [Category C₂] [Category C]
    [Category C'] (G : C ⥤ C') (R : C₁ ⥤ C) (R' : C₂ ⥤ C') (P : ι → C₁) (P' : ι → C₂)
    (v : ∀ i, G.obj (R.obj (P i)) ⟶ R'.obj (P' i)) {i j : ι} (h : i = j) (h₁ : P i = P j)
    (h₂ : P' i = P' j) :
    G.map (R.map (eqToHom h₁)) ≫ v j = v i ≫ R'.map (eqToHom h₂) := by
  subst h
  simp

end Chase

section TensorSquare

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The isomorphism `tensorPullbackIsoT` is the comparison followed by the tensor product of the
two identifications. -/
public theorem tensorPullbackIsoT_hom {M L₁ : Y.Modules} {N L₁' : X.Modules}
    (a : (Scheme.Modules.pullback f).obj M ≅ N) (l : (Scheme.Modules.pullback f).obj L₁ ≅ L₁') :
    (tensorPullbackIsoT f a l).hom =
      Stacks.RingedSpace.comparison f.toLRSHom.toShHom M L₁ ≫ tensorMap a.hom l.hom :=
  rfl

/-- A tensor product of morphisms on the base, against the comparison of Tag 01CD. -/
public theorem pullback_tensorMap_left_square {A₁ A₂ B : Y.Modules} {A₁' A₂' B' : X.Modules}
    (x : A₁ ⟶ A₂) (x' : A₁' ⟶ A₂') (α₁ : (Scheme.Modules.pullback f).obj A₁ ⟶ A₁')
    (α₂ : (Scheme.Modules.pullback f).obj A₂ ⟶ A₂') (γ : (Scheme.Modules.pullback f).obj B ⟶ B')
    (hx : (Scheme.Modules.pullback f).map x ≫ α₂ = α₁ ≫ x') :
    (Scheme.Modules.pullback f).map (tensorMap x (𝟙 B)) ≫
        Stacks.RingedSpace.comparison f.toLRSHom.toShHom A₂ B ≫ tensorMap α₂ γ =
      (Stacks.RingedSpace.comparison f.toLRSHom.toShHom A₁ B ≫ tensorMap α₁ γ) ≫
        tensorMap x' (𝟙 B') := by
  have hx' : (pullbackFunctor f.toLRSHom.toShHom).map x ≫ α₂ = α₁ ≫ x' := hx
  have h := comparison_naturality_assoc f.toLRSHom.toShHom x (𝟙 B) (tensorMap α₂ γ)
  refine h.trans ((congrArg (_ ≫ ·) ((tensorMap_comp _ α₂ _ γ).trans
    ((congrArg₂ (fun u v => tensorMap u v) hx'
      ((congrArg (· ≫ γ) (CategoryTheory.Functor.map_id _ B)).trans
      ((Category.id_comp γ).trans (Category.comp_id γ).symm))).trans
        (tensorMap_comp α₁ x' γ (𝟙 B')).symm))).trans (Category.assoc _ _ _).symm)

end TensorSquare

section TopRow

/-- `Sym^k(E) ⊗ ⋀ⁿ⁺¹ E` is finite locally free when both factors are. -/
private theorem isFiniteLocallyFree_symDet {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (n k : ℕ)
    [hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))]
    [hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := S.ringCatSheaf)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj
              ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))).obj
            (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)))) := by
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := S.ringCatSheaf)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)) :=
    ⟨hP.exists_isFiniteLocallyFreeData⟩
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := S.ringCatSheaf)
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) := ⟨hN.exists_isFiniteLocallyFreeData⟩
  exact ⟨(AlgebraicGeometry.isFiniteLocallyFree_tensorObj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).exists_isFiniteLocallyFreeData⟩

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- `g^*(Sym^j(E) ⊗ ⋀ⁿ⁺¹ E) ≅ Sym^j(E') ⊗ ⋀ⁿ⁺¹ E'`. -/
public abbrev symDetBaseIso (n : ℕ) (j : ℤ) :
    (Scheme.Modules.pullback g).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece j)).obj
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨S'.toRingedSpace.presheaf, S'.toRingedSpace.IsSheaf⟩).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece j)).obj
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))) :=
  tensorPullbackIsoT g
    (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app j)
      (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE j))
    (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ))

/-- The dual base-change map of `Sym^j(E) ⊗ ⋀ⁿ⁺¹ E`:
`g^* SheafHom(Sym^j(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S) ⟶ SheafHom(g^*(Sym^j(E) ⊗ ⋀ⁿ⁺¹ E), 𝒪_{S'})
≅ SheafHom(Sym^j(E') ⊗ ⋀ⁿ⁺¹ E', 𝒪_{S'})`. -/
public def symDetDualBaseChange (n : ℕ) (j : ℤ) :
    (Scheme.Modules.pullback g).obj (dualSheaf ((Stacks.ProjectionFormula.tensorRightInvertible S
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece j))) ⟶
      dualSheaf ((Stacks.ProjectionFormula.tensorRightInvertible S'
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece j)) :=
  Stacks.Chow.pullbackDualMap g ((Stacks.ProjectionFormula.tensorRightInvertible S
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece j)) ≫
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S').map
      (symDetBaseIso g E hqc E' hqc' hE n j).inv.op

/-- **The base change map of the target of the row `q = n`**:
`g^* SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S) ⟶ SheafHom(g^*(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E), 𝒪_{S'})
≅ SheafHom(Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E', 𝒪_{S'})`. -/
public def topRowTargetBaseChange (n : ℕ) (d : ℤ) :
    (Scheme.Modules.pullback g).obj (topRowTarget E hqc n d) ⟶ topRowTarget E' hqc' n d :=
  symDetDualBaseChange g E hqc E' hqc' hE n (-(n : ℤ) - 1 - d)

/-- The dual base-change map of `Sym^j(E) ⊗ ⋀ⁿ⁺¹ E` is compatible with a change of the index
`j`. -/
public theorem dualSymDet_reindex (n : ℕ) (j₁ j₂ : ℤ) (h : j₁ = j₂)
    (h₁ : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece j₂ =
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece j₁)
    (h₂ : (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece j₂ =
      (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece j₁)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece j₁)).obj
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))))) :
    (Scheme.Modules.pullback g).map ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S).map
        ((Stacks.ProjectionFormula.tensorRightInvertible S
            (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).map (eqToHom h₁)).op) ≫
        Stacks.Chow.pullbackDualMap g ((Stacks.ProjectionFormula.tensorRightInvertible S
              (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece j₂)) ≫
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S').map
          (symDetBaseIso g E hqc E' hqc' hE n j₂).inv.op =
      (pullbackDualIsoOf g _ (symDetBaseIso g E hqc E' hqc' hE n j₁) hM).hom ≫
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S').map
          ((Stacks.ProjectionFormula.tensorRightInvertible S'
              (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).map (eqToHom h₂)).op := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, op_id, Category.id_comp, Category.comp_id]
  rfl

variable (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))

/-- Transport of the base change map of the twists along an equality of degrees. -/
public theorem twistBaseChangeNat_eqToHom (q : ℕ) (e₁ e₂ : ℤ) (h : e₁ = e₂)
    (h₁ : D.algebra.piece e₁ = D.algebra.piece e₂)
    (h₂ : D'.algebra.piece e₁ = D'.algebra.piece e₂) :
    (Scheme.Modules.pullback g).map (((bundlePushforward E hqc).rightDerived q).map (eqToHom h₁)) ≫
        (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
          (D.algebra.piece e₂) ≫
          ((bundlePushforward E' hqc').rightDerived q).map
            (thetaSharp g E hqc E' hqc' hE D D' e₂)) =
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
        (D.algebra.piece e₁) ≫
          ((bundlePushforward E' hqc').rightDerived q).map
            (thetaSharp g E hqc E' hqc' hE D D' e₁)) ≫
        ((bundlePushforward E' hqc').rightDerived q).map (eqToHom h₂) :=
  map_eqToHom_square (Scheme.Modules.pullback g) ((bundlePushforward E hqc).rightDerived q)
    ((bundlePushforward E' hqc').rightDerived q) D.algebra.piece D'.algebra.piece
    (fun e => Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
        (D.algebra.piece e) ≫
      ((bundlePushforward E' hqc').rightDerived q).map (thetaSharp g E hqc E' hqc' hE D D' e))
    h h₁ h₂

/-- The first half of `higherDirectImageSheafHomIso`:
`Rⁿ π_* SheafHom(π^* Sym^k(E), 𝒪(-n-1)) ≅ Rⁿ π_*(𝒪(-n-1) ⊗ π^* Sym^k(E)^∨) ≅
Rⁿ π_* 𝒪(-n-1) ⊗ Sym^k(E)^∨`, by the projection formula. -/
private def sheafHomIsoHead (n k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))] :=
  ((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).map
      ((sheafHomIsoTensorDual ((Scheme.Modules.pullback
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
          (D.algebra.piece (-(n : ℤ) - 1))).hom ≫
        tensorMap (𝟙 (D.algebra.piece (-(n : ℤ) - 1)))
          (Stacks.FundamentalGroup.pullbackDualSheafIso
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)) inferInstance).inv) ≫
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase) n).inv.app
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj
          (D.algebra.piece (-(n : ℤ) - 1))).obj ((Scheme.Modules.pullback
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))))) ≫
    (projectionFormulaDeltaApp
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase
        (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
        (D.algebra.piece (-(n : ℤ) - 1)) n).hom

/-- The second half of `higherDirectImageSheafHomIso`:
`Rⁿ π_* 𝒪(-n-1) ⊗ Sym^k(E)^∨ ≅ (⋀ⁿ⁺¹ E)^∨ ⊗ Sym^k(E)^∨ ≅ SheafHom(Sym^k(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`,
with `k = -n-1-d`. -/
private def sheafHomIsoTail (n : ℕ) (hn : 1 ≤ n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) (k : ℕ) (d : ℤ)
    (hd : (k : ℤ) + d = -(n : ℤ) - 1)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))] :=
  tensorMap (((bundlePushforward E hqc).rightDerived n).map
      (eqToHom (congrArg D.algebra.piece
        (show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring))) ≫
      (topTwistIsoDualDet E hqc D hn hfree).hom)
    (𝟙 (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))) ≫
    (dualTensorIso ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).inv ≫
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S).map
      ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).map
        (eqToHom (congrArg (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece
          (show -(n : ℤ) - 1 - d = (k : ℤ) by omega)))).op

/-- The base change map between the middle terms of `higherDirectImageSheafHomIso`:
`g^*(Rⁿ π_* 𝒪(-n-1) ⊗ Sym^k(E)^∨) ⟶ Rⁿ π'_* 𝒪'(-n-1) ⊗ Sym^k(E')^∨`. -/
private def topRowMid (n k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))] :=
  Stacks.RingedSpace.comparison g.toLRSHom.toShHom
      (((bundlePushforward E hqc).rightDerived n).obj (D.algebra.piece (-(n : ℤ) - 1)))
      (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))) ≫
    tensorMap (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) n
        (D.algebra.piece (-(n : ℤ) - 1)) ≫
      ((bundlePushforward E' hqc').rightDerived n).map
        (thetaSharp g E hqc E' hqc' hE D D' (-(n : ℤ) - 1)))
      (pullbackDualIsoOf (A' := ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ)))
        g ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))
        (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (k : ℤ))
          (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (k : ℤ)))
        inferInstance).hom

/-- Two commuting squares whose vertical maps agree, pasted along a composite. -/
private theorem ladder_halves {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')
    {X₀ X₁ X₂ X₃ : C} {Y₀ Y₁ Y₂ Y₃ : C'} {a₁ : X₀ ⟶ X₁} {h : X₁ ⟶ X₂} {t : X₂ ⟶ X₃}
    {v₀ : F.obj X₀ ⟶ Y₀} {b₁ : Y₀ ⟶ Y₁} {h' : Y₁ ⟶ Y₂} {t' : Y₂ ⟶ Y₃} {m : F.obj X₂ ⟶ Y₂}
    {v₃ : F.obj X₃ ⟶ Y₃} (hA : F.map (a₁ ≫ h) ≫ m = v₀ ≫ b₁ ≫ h') (hB : F.map t ≫ v₃ = m ≫ t') :
    v₀ ≫ b₁ ≫ h' ≫ t' = F.map (a₁ ≫ h ≫ t) ≫ v₃ := by
  rw [← Category.assoc a₁, F.map_comp, Category.assoc, hB, reassoc_of% hA]

/-- Three commuting squares, whose consecutive vertical maps agree. -/
private theorem ladder_head {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')
    {X₀ X₁ X₂ X₃ X₄ : C} {Y₀ Y₁ Y₂ Y₃ Y₄ : C'} {a₁ : X₀ ⟶ X₁} {a₂ : X₁ ⟶ X₂} {a₃ : X₂ ⟶ X₃}
    {a₄ : X₃ ⟶ X₄} {b₁ : Y₀ ⟶ Y₁} {b₂ : Y₁ ⟶ Y₂} {b₃ : Y₂ ⟶ Y₃} {b₄ : Y₃ ⟶ Y₄}
    {v₀ : F.obj X₀ ⟶ Y₀} {v₂ v₂' : F.obj X₂ ⟶ Y₂} {v₃ v₃' : F.obj X₃ ⟶ Y₃} {v₄ : F.obj X₄ ⟶ Y₄}
    (s₂ : F.map a₁ ≫ F.map a₂ ≫ v₂ = v₀ ≫ b₁ ≫ b₂) (s₃ : F.map a₃ ≫ v₃ = v₂' ≫ b₃)
    (s₄ : F.map a₄ ≫ v₄ = v₃' ≫ b₄) (e₂ : v₂ = v₂') (e₃ : v₃ = v₃') :
    F.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ v₄ = v₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ := by
  subst e₂ e₃
  simp only [Functor.map_comp, Category.assoc]
  rw [s₄, reassoc_of% s₃, reassoc_of% s₂]

/-- Three commuting squares, whose consecutive vertical maps agree. -/
private theorem ladder_tail {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')
    {X₄ X₅ X₆ X₇ : C} {Y₄ Y₅ Y₆ Y₇ : C'} {a₅ : X₄ ⟶ X₅} {a₆ : X₅ ⟶ X₆} {a₇ : X₆ ⟶ X₇}
    {b₅ : Y₄ ⟶ Y₅} {b₆ : Y₅ ⟶ Y₆} {b₇ : Y₆ ⟶ Y₇} {v₄ : F.obj X₄ ⟶ Y₄} {v₅ v₅' : F.obj X₅ ⟶ Y₅}
    {v₆ v₆' : F.obj X₆ ⟶ Y₆} {v₇ : F.obj X₇ ⟶ Y₇}
    (s₅ : F.map a₅ ≫ v₅ = v₄ ≫ b₅) (s₆ : F.map a₆ ≫ v₆ = v₅' ≫ b₆) (s₇ : F.map a₇ ≫ v₇ = v₆' ≫ b₇)
    (e₅ : v₅ = v₅') (e₆ : v₆ = v₆') :
    F.map (a₅ ≫ a₆ ≫ a₇) ≫ v₇ = v₄ ≫ b₅ ≫ b₆ ≫ b₇ := by
  subst e₅ e₆
  simp only [Functor.map_comp, Category.assoc]
  rw [s₇, reassoc_of% s₆, reassoc_of% s₅]

/-- **The first half of the row `q = n` under base change**: the multiplication pairing followed
by the projection formula commutes with base change. -/
private theorem sheafHomIsoHead_baseChange (n k : ℕ) (d : ℤ) (he : d + k = -(n : ℤ) - 1)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ)))] :
    (Scheme.Modules.pullback g).map (((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).map
          (twistPairingCurry E hqc D k d (-(n : ℤ) - 1) he) ≫ sheafHomIsoHead E hqc D n k) ≫
        topRowMid g E hqc E' hqc' hE D D' n k =
      twistBaseChange g E hqc E' hqc' hE D D' n d ≫
        ((bundlePushforward E' hqc').rightDerivedPlus (n : ℤ)).map
          (twistPairingCurry E' hqc' D' k d (-(n : ℤ) - 1) he) ≫
        sheafHomIsoHead E' hqc' D' n k := by
  have s₂ := curry_square (Scheme.Modules.pullback g)
    ((bundlePushforward E hqc).rightDerivedPlus (n : ℤ))
    ((bundlePushforward E' hqc').rightDerivedPlus (n : ℤ))
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE))
    (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChange_naturality
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) n
      (twistPairingCurry E hqc D k d (-(n : ℤ) - 1) he ≫
        (sheafHomIsoTensorDual _ (D.algebra.piece (-(n : ℤ) - 1))).hom ≫
        tensorMap (𝟙 (D.algebra.piece (-(n : ℤ) - 1)))
          (Stacks.FundamentalGroup.pullbackDualSheafIso
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase _
            inferInstance).inv))
    (twistPairingCurry_baseChange g E hqc E' hqc' hE D D' k d (-(n : ℤ) - 1) he)
  have s₃ := inv_square (Scheme.Modules.pullback g)
    (Iso.inv_hom_id_app (Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase) n)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj
          (D.algebra.piece (-(n : ℤ) - 1))).obj ((Scheme.Modules.pullback
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))))))
    (Iso.hom_inv_id_app (Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase) n)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(bundle E' hqc').toRingedSpace.presheaf, (bundle E' hqc').toRingedSpace.IsSheaf⟩).obj
          (D'.algebra.piece (-(n : ℤ) - 1))).obj ((Scheme.Modules.pullback
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ)))))))
    (higherBaseChangeNat_comp_rightDerivedIso
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) n
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj
          (D.algebra.piece (-(n : ℤ) - 1))).obj ((Scheme.Modules.pullback
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))))))
      (tensorPullbackIsoT (bundleBaseChange g E hqc E' hqc' hE)
        (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' (-(n : ℤ) - 1))
          (isIso_thetaSharp g E hqc E' hqc' hE D D' (-(n : ℤ) - 1)))
        (symDualSquareIso g E hqc E' hqc' hE (k : ℤ))).hom)
  have s₄ := (projectionFormula_baseChange_iso
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
    (pullbackDualIsoOf (A' := ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ)))
      g ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))
      (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (k : ℤ))
        (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (k : ℤ)))
      inferInstance)
    (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' (-(n : ℤ) - 1))
      (isIso_thetaSharp g E hqc E' hqc' hE D D' (-(n : ℤ) - 1))) n).symm.trans
    (Category.assoc _ _ _).symm
  have L := ladder_head (Scheme.Modules.pullback g) s₂ s₃ s₄ (by rfl) (by rfl)
  exact L

variable {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1))

include hn hfree hfree' in
/-- **The second half of the row `q = n` under base change**: `Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨` and
`(G ⊗ N)^∨ ≅ N^∨ ⊗ G^∨` commute with base change. -/
private theorem sheafHomIsoTail_baseChange (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -(n : ℤ) - 1)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ))] :
    (Scheme.Modules.pullback g).map (sheafHomIsoTail E hqc D n hn hfree k d hd) ≫
        topRowTargetBaseChange g E hqc E' hqc' hE n d =
      topRowMid g E hqc E' hqc' hE D D' n k ≫ sheafHomIsoTail E' hqc' D' n hn hfree' k d hd := by
  have := isFiniteLocallyFree_of_rank E hfree
  have := isFiniteLocallyFree_of_rank E' hfree'
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E (n + 1)
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E' (n + 1)
  have hT := isFiniteLocallyFree_symDet E hqc n k
  have hT' := isFiniteLocallyFree_symDet E' hqc' n k
  have hx := comp_square (Scheme.Modules.pullback g)
    (twistBaseChangeNat_eqToHom g E hqc E' hqc' hE D D' n (-(n : ℤ) - 1) (-((n + 1 : ℕ) : ℤ))
      (by push_cast; ring) (congrArg D.algebra.piece (by push_cast; ring))
      (congrArg D'.algebra.piece (by push_cast; ring)))
    (topTwistIsoDualDet_baseChange g E hqc E' hqc' hE D D' hn hfree hfree')
  have s₅ := pullback_tensorMap_left_square g _ _ _ _
    (pullbackDualIsoOf (A' := ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ))) g
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))
      (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (k : ℤ))
        (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (k : ℤ)))
      inferInstance).hom hx
  have s₆ := (dualTensorIso_inv_pullback g
      (G := ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
      (N := (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)))
      (G' := ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ)))
      (N' := (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ)))
      (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (k : ℤ))
        (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (k : ℤ)))
      (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ))).trans
    (congrArg (· ≫ (dualTensorIso
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ))
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).inv)
      (tensorPullbackIsoT_hom g _ _))
  have s₇ := dualSymDet_reindex g E hqc E' hqc' hE n (k : ℤ) (-(n : ℤ) - 1 - d) (by omega)
    (congrArg (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (by omega))
    (congrArg (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (by omega)) hT
  have L := ladder_tail (Scheme.Modules.pullback g) s₅ s₆ s₇ (by rfl) (by rfl)
  exact L

include hn hfree in
/-- `higherDirectImageSheafHomIso` as the composite of its two halves. -/
private theorem higherDirectImageSheafHomIso_hom (k : ℕ) (d : ℤ)
    (hd : (k : ℤ) + d = -(n : ℤ) - 1)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))] :
    (higherDirectImageSheafHomIso E hqc D hn hfree k d hd).hom =
      sheafHomIsoHead E hqc D n k ≫ sheafHomIsoTail E hqc D n hn hfree k d hd :=
  rfl

include hn hfree hfree' in
/-- **The row `q = n` under base change, for `d ≤ -n - 1`**, along the pairing that defines it. -/
public theorem topRowIso_baseChange_of_le (k : ℕ) (d : ℤ) (he : d + k = -(n : ℤ) - 1)
    (hd : (k : ℤ) + d = -(n : ℤ) - 1) :
    twistBaseChange g E hqc E' hqc' hE D D' n d ≫
        ((bundlePushforward E' hqc').rightDerivedPlus (n : ℤ)).map
          (twistPairingCurry E' hqc' D' k d (-(n : ℤ) - 1) he) ≫
        (higherDirectImageSheafHomIso E' hqc' D' hn hfree' k d hd).hom =
      (Scheme.Modules.pullback g).map (((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).map
          (twistPairingCurry E hqc D k d (-(n : ℤ) - 1) he) ≫
          (higherDirectImageSheafHomIso E hqc D hn hfree k d hd).hom) ≫
        topRowTargetBaseChange g E hqc E' hqc' hE n d := by
  have := isFiniteLocallyFree_of_rank E hfree
  have := isFiniteLocallyFree_of_rank E' hfree'
  have hP := isFiniteLocallyFree_piece E hqc hfree k
  have hP' := isFiniteLocallyFree_piece E' hqc' hfree' k
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _ hP
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _ hP'
  rw [higherDirectImageSheafHomIso_hom, higherDirectImageSheafHomIso_hom]
  exact ladder_halves (Scheme.Modules.pullback g)
    (sheafHomIsoHead_baseChange g E hqc E' hqc' hE D D' n k d he)
    (sheafHomIsoTail_baseChange g E hqc E' hqc' hE D D' hn hfree hfree' k d hd)

include hn hfree hfree' in
/-- **The row `q = n` under base change**: for every integer `d`, the base change map
`g^* Rⁿ π_* 𝒪(d) ⟶ Rⁿ π'_* 𝒪'(d)` corresponds, under
`Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` and its analogue for `E'`, to the dual
base-change map along `g^*(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E) ≅ Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E'`. -/
public theorem topRowIso_baseChange (d : ℤ) :
    twistBaseChange g E hqc E' hqc' hE D D' n d ≫ (topRowIso E' hqc' D' hn hfree' d).hom =
      (Scheme.Modules.pullback g).map (topRowIso E hqc D hn hfree d).hom ≫
        topRowTargetBaseChange g E hqc E' hqc' hE n d := by
  by_cases h : d ≤ -(n : ℤ) - 1
  · simp only [topRowIso, dif_pos h, Iso.trans_hom, asIso_hom]
    exact topRowIso_baseChange_of_le g E hqc E' hqc' hE D D' hn hfree hfree' _ d (by omega)
      (by omega)
  · exact (isZero_topRow_of_le E' hqc' D' hn hfree' (d := d) (by omega)).2.eq_of_tgt _ _

end TopRow

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
