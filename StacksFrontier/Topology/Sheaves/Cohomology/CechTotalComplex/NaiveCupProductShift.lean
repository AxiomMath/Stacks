module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareSections

/-!
# The naive cup product on sections, componentwise

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings, `V` an open subset and
`𝒦^•`, `ℒ^•` complexes of `𝒪_X`-modules.  On the summand `Γ(V, 𝒦ᵃ) ⊗ Γ(V, ℒᵇ)` of
`Tot(Γ(V, 𝒦^•) ⊗ Γ(V, ℒ^•))` the naive cup product
`Stacks.Cech.SheafTensorPairing.naiveCupProductEval` is the map

`Γ(V, 𝒦ᵃ) ⊗ Γ(V, ℒᵇ) ⟶ Γ(V, 𝒦ᵃ ⊗ ℒᵇ) ⟶ Γ(V, Tot(𝒦^• ⊗ ℒ^•)ⁿ)`

of sections followed by the inclusion of the summand.  This file names the first arrow, proves
that it is natural in the two sheaves, and compares the naive cup products of `𝒦^•[t]`, `ℒ^•` and
of `𝒦^•`, `ℒ^•[t]` with that of `𝒦^•`, `ℒ^•` through the identifications of the total complex of
shifted complexes with the shifted total complex.

## Main definitions

* `Stacks.Cech.SheafTensorPairing.pairEval`: the map `Γ(V, ℱ) ⊗ Γ(V, 𝒢) ⟶ Γ(V, ℱ ⊗ 𝒢)` on
  sections over `V`.

## Main results

* `Stacks.Cech.SheafTensorPairing.ι_naiveCupProductEval_f`: the naive cup product on a summand.
* `Stacks.Cech.SheafTensorPairing.pairEval_naturality`: `pairEval` is natural in the two sheaves.
* `Stacks.Cech.SheafTensorPairing.cycles_naiveCupProductEval_shift₂`: on cocycles, the naive cup
  product of `𝒦^•` and `ℒ^•[t]` is `(-1)^{it}` times that of `𝒦^•` and `ℒ^•`.
* `Stacks.Cech.SheafTensorPairing.cycles_naiveCupProductEval_shift₁`: on cocycles, the naive cup
  product of `𝒦^•[t]` and `ℒ^•` is that of `𝒦^•` and `ℒ^•`.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (sectionsTerminalFunctorIso)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor sectionsFunctor)
open Stacks.Cech.CupProduct (tensorModules)
open scoped CategoryTheory.Prod
open CategoryTheory.MonoidalCategory

universe u

/-! ### Cocycles of a shifted complex -/

namespace Stacks.Cohomology.DerivedGlobalCupProduct

/-- **A family of cocycles of `Y[n]` in degree `a`, read as cocycles of `Y` in degree
`n + a`**: the identification of the two short complexes `(Y[n]).sc a ≅ Y.sc (n + a)` on cycles. -/
def shiftCycles {R : Type u} [Ring R] {M : ModuleCat.{u} R} (Y : CochainComplex (ModuleCat.{u} R) ℤ)
    {n a : ℤ} (a' : ℤ) (h : n + a = a') (z : M ⟶ (Y⟦n⟧).cycles a) : M ⟶ Y.cycles a' :=
  z ≫ ShortComplex.cyclesMap ((CochainComplex.shiftShortComplexFunctorIso _ n a a' h).hom.app Y)

/-- `shiftCycles` is the identity on the underlying elements of the term in degree `a`. -/
theorem shiftCycles_iCycles {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (Y : CochainComplex (ModuleCat.{u} R) ℤ) {n a : ℤ} (a' : ℤ) (h : n + a = a')
    (z : M ⟶ (Y⟦n⟧).cycles a) :
    shiftCycles Y a' h z ≫ Y.iCycles a' =
      z ≫ (Y⟦n⟧).iCycles a ≫ (Y.shiftFunctorObjXIso n a a' (by omega)).hom := by
  rw [shiftCycles]
  refine (Category.assoc _ _ _).trans (congrArg (z ≫ ·) ((ShortComplex.cyclesMap_i _).trans ?_))
  simp [CochainComplex.shiftShortComplexFunctorIso]
  rfl

/-- The class of a cocycle of `Y[n]`, moved to `Hⁿ⁺ᵃ(Y)` by the identification of homologies, is
the class of `shiftCycles`. -/
theorem homologyπ_shiftIso {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (Y : CochainComplex (ModuleCat.{u} R) ℤ) {n a : ℤ} (a' : ℤ) (h : n + a = a')
    (z : M ⟶ (Y⟦n⟧).cycles a) :
    z ≫ (Y⟦n⟧).homologyπ a ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).shiftIso
          n a a' h).hom.app Y =
      shiftCycles Y a' h z ≫ Y.homologyπ a' := by
  rw [shiftCycles]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (z ≫ ·) ?_
  have e := (ShortComplex.homologyπ_naturality
    ((CochainComplex.shiftShortComplexFunctorIso _ n a a' h).hom.app Y))
  refine Eq.trans ?_ e
  exact congrArg ((Y⟦n⟧).homologyπ a ≫ ·)
    (CochainComplex.ShiftSequence.shiftIso_hom_app n a a' h Y)

/-- An additive functor carries the identification `(T[t])ⁿ ≅ Tⁿ⁺ᵗ` of a complex to that of its
image. -/
theorem map_shiftFunctorObjXIso_hom {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] (T : CochainComplex C ℤ) (t n n' : ℤ)
    (h : n' = n + t) :
    F.map (T.shiftFunctorObjXIso t n n' h).hom =
      (CochainComplex.shiftFunctorObjXIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T)
        t n n' h).hom := by
  subst h
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

/-- An additive functor carries the inverse of the identification `(T[t])ⁿ ≅ Tⁿ⁺ᵗ` of a complex
to that of its image. -/
theorem map_shiftFunctorObjXIso_inv {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] (T : CochainComplex C ℤ) (t n n' : ℤ)
    (h : n' = n + t) :
    F.map (T.shiftFunctorObjXIso t n n' h).inv =
      (CochainComplex.shiftFunctorObjXIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T)
        t n n' h).inv := by
  subst h
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

/-- The two identifications `(T[t])ⁿ ≅ Tⁿ⁺ᵗ`, of a complex and of its image under an additive
functor, cancel. -/
@[reassoc]
theorem map_shiftFunctorObjXIso_inv_comp_hom {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] (T : CochainComplex C ℤ)
    (t n n' : ℤ) (h : n' = n + t) :
    F.map (T.shiftFunctorObjXIso t n n' h).inv ≫
      (CochainComplex.shiftFunctorObjXIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T)
        t n n' h).hom = 𝟙 _ := by
  rw [map_shiftFunctorObjXIso_inv, Iso.inv_hom_id]

end Stacks.Cohomology.DerivedGlobalCupProduct

namespace Stacks.Cech.SheafTensorPairing

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] (V : Opens X)

/-- **The map of sections `Γ(V, ℱ) ⊗ Γ(V, 𝒢) ⟶ Γ(V, ℱ ⊗ 𝒢)`** of two sheaves of `𝒪_X`-modules,
`A = 𝒪_X(V)`: the sheaf-tensor pairing at the terminal object of the slice over `V`, read through
the identification of sections at that object with sections over `V`. -/
def pairEval (F G : SheafOfModules.{u} (ringSheaf.{u, u, u} O)) :
    ((tensorModules (CoeffRing O V)).obj
        ((SheafOfModules.evaluation (ringSheaf O) (op V)).obj F)).obj
        ((SheafOfModules.evaluation (ringSheaf O) (op V)).obj G) ⟶
      (SheafOfModules.evaluation (ringSheaf O) (op V)).obj (((sheafTensor O).obj F).obj G) :=
  ((tensorModules (CoeffRing O V)).map
      ((sectionsTerminalFunctorIso (R := ringSheaf O) V).inv.app F)).app _ ≫
    ((tensorModules (CoeffRing O V)).obj _).map
      ((sectionsTerminalFunctorIso (R := ringSheaf O) V).inv.app G) ≫
    (sheafTensorPairing O V F G).app (op (Over.mk (𝟙 V))) ≫
    (sectionsTerminalFunctorIso (R := ringSheaf O) V).hom.app (((sheafTensor O).obj F).obj G)

variable (K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ)

/-- **The naive cup product on a summand** is the map of sections followed by the inclusion of
the summand into the total complex. -/
theorem ι_naiveCupProductEval_f (p q n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ) p q n h ≫ (naiveCupProductEval O V K L).f n =
      pairEval O V (K.X p) (L.X q) ≫ (SheafOfModules.evaluation (ringSheaf O) (op V)).map
        (HomologicalComplex.ιMapBifunctor K L (sheafTensor O) (up ℤ) p q n h) := by
  rw [naiveCupProductEval_ι, pairEval]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((sectionsTerminalFunctorIso (R := ringSheaf O) V).hom.naturality _)).trans
      (Category.assoc _ _ _).symm)

/-- **The map of sections is natural in the two sheaves.** -/
theorem pairEval_naturality {F F' G G' : SheafOfModules.{u} (ringSheaf.{u, u, u} O)}
    (f : F ⟶ F') (g : G ⟶ G') :
    ((tensorModules (CoeffRing O V)).map
        ((SheafOfModules.evaluation (ringSheaf O) (op V)).map f)).app _ ≫
        ((tensorModules (CoeffRing O V)).obj _).map
          ((SheafOfModules.evaluation (ringSheaf O) (op V)).map g) ≫ pairEval O V F' G' =
      pairEval O V F G ≫ (SheafOfModules.evaluation (ringSheaf O) (op V)).map
        ((((sheafTensor O).map f).app G) ≫ ((sheafTensor O).obj F').map g) := by
  have hl := congrArg (fun t => NatTrans.app t (op (Over.mk (𝟙 V))))
    (sheafTensorPairing_naturality_left O V f G)
  have hr := congrArg (fun t => NatTrans.app t (op (Over.mk (𝟙 V))))
    (sheafTensorPairing_naturality_right O V F' g)
  simp only [NatTrans.comp_app] at hl hr
  have nf := (sectionsTerminalFunctorIso (R := ringSheaf O) V).inv.naturality f
  have ng := (sectionsTerminalFunctorIso (R := ringSheaf O) V).inv.naturality g
  have nh := (sectionsTerminalFunctorIso (R := ringSheaf O) V).hom.naturality
    ((((sheafTensor O).map f).app G) ≫ ((sheafTensor O).obj F').map g)
  let T := Stacks.Cohomology.CechSheaf.sectionsTerminalFunctor (R := ringSheaf O) V
  let tM := tensorModules (CoeffRing O V)
  let E := SheafOfModules.evaluation (ringSheaf O) (op V)
  let ι := sectionsTerminalFunctorIso (R := ringSheaf O) V
  let P := fun (A B : SheafOfModules.{u} (ringSheaf.{u, u, u} O)) =>
    (sheafTensorPairing O V A B).app (op (Over.mk (𝟙 V)))
  have hl' : (tM.map (T.map f)).app (T.obj G) ≫ P F' G =
      P F G ≫ T.map (((sheafTensor O).map f).app G) := hl
  have hr' : (tM.obj (T.obj F')).map (T.map g) ≫ P F' G' =
      P F' G ≫ T.map (((sheafTensor O).obj F').map g) := hr
  have hx : ∀ {A A' : ModuleCat.{u} (CoeffRing O V)} {B B' : ModuleCat.{u} (CoeffRing O V)}
      (a : A ⟶ A') (b : B ⟶ B'), (tM.map a).app B ≫ (tM.obj A').map b =
        (tM.obj A).map b ≫ (tM.map a).app B' := fun a b => ((tM.map a).naturality b).symm
  have key : (tM.map (E.map f)).app (E.obj G) ≫ (tM.obj (E.obj F')).map (E.map g) ≫
        (tM.map (ι.inv.app F')).app (E.obj G') ≫ (tM.obj (T.obj F')).map (ι.inv.app G') =
      (tM.map (ι.inv.app F)).app (E.obj G) ≫ (tM.obj (T.obj F)).map (ι.inv.app G) ≫
        (tM.map (T.map f)).app (T.obj G) ≫ (tM.obj (T.obj F')).map (T.map g) := by
    rw [← Category.assoc ((tM.obj (E.obj F')).map (E.map g)), ← hx, Category.assoc,
      ← Functor.map_comp, ng, Functor.map_comp, ← Category.assoc ((tM.map (E.map f)).app (E.obj G)),
      ← NatTrans.comp_app, ← Functor.map_comp, nf, Functor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [← Category.assoc ((tM.map (T.map f)).app (E.obj G)), hx, Category.assoc]
  have key' := (reassoc_of% key) (P F' G' ≫ ι.hom.app (((sheafTensor O).obj F').obj G'))
  rw [pairEval, pairEval]
  simp only [Category.assoc]
  refine key'.trans ?_
  have h1 := congrArg ((tM.map (T.map f)).app (T.obj G) ≫ ·)
    ((reassoc_of% hr') (ι.hom.app (((sheafTensor O).obj F').obj G')))
  have h2 := (reassoc_of% hl') (T.map (((sheafTensor O).obj F').map g) ≫
    ι.hom.app (((sheafTensor O).obj F').obj G'))
  have h3 : T.map (((sheafTensor O).map f).app G) ≫ T.map (((sheafTensor O).obj F').map g) ≫
        ι.hom.app (((sheafTensor O).obj F').obj G') =
      ι.hom.app (((sheafTensor O).obj F).obj G) ≫
        E.map ((((sheafTensor O).map f).app G) ≫ ((sheafTensor O).obj F').map g) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (T.map_comp _ _).symm).trans nh)
  have core := h1.trans (h2.trans (congrArg (P F G ≫ ·) h3))
  exact congrArg (fun t => (tM.map (ι.inv.app F)).app (E.obj G) ≫
    (tM.obj (T.obj F)).map (ι.inv.app G) ≫ t)
      ((Category.assoc _ _ _).trans (core.trans (Category.assoc _ _ _).symm))

/-! ### The naive cup product and the shift -/

/-- **The naive cup product and the shift of the second factor**, on a summand: followed by the
identification `Tot(𝒦^• ⊗ ℒ^•[t]) ≅ Tot(𝒦^• ⊗ ℒ^•)[t]` of `CochainComplex.mapBifunctorShift₂Iso`,
the naive cup product of `𝒦^•` and `ℒ^•[t]` on the summand `(p, q)` is `(-1)^{pt}` times the
naive cup product of `𝒦^•` and `ℒ^•` on the summand `(p, q + t)`. -/
@[reassoc]
theorem ι_naiveCupProductEval_shift₂ (t p q n : ℤ) (h : p + q = n) (q' n' : ℤ)
    (hq : q' = q + t) (hn : n' = n + t) :
    HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
        (tensorModules (CoeffRing O V)) (up ℤ) p q n h ≫ (naiveCupProductEval O V K (L⟦t⟧)).f n ≫
        (SheafOfModules.evaluation (ringSheaf O) (op V)).map
          ((CochainComplex.mapBifunctorShift₂Iso K L (sheafTensor O) t).hom.f n) =
      (p * t).negOnePow • (((tensorModules (CoeffRing O V)).obj _).map
          ((SheafOfModules.evaluation (ringSheaf O) (op V)).map
            (L.shiftFunctorObjXIso t q q' hq).hom) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) p q' n' (by
            change p + q' = n'; omega) ≫
        (naiveCupProductEval O V K L).f n' ≫
        (SheafOfModules.evaluation (ringSheaf O) (op V)).map
          (CochainComplex.shiftFunctorObjXIso
            (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)) t n n' hn).inv) := by
  rw [← Category.assoc, ι_naiveCupProductEval_f, Category.assoc, ← Functor.map_comp,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f K L (sheafTensor O) t p q n h q' n' hq hn]
  have hn := pairEval_naturality O V (𝟙 (K.X p)) (L.shiftFunctorObjXIso t q q' hq).hom
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hn
  have hι := ι_naiveCupProductEval_f O V K L p q' n' (by change p + q' = n'; omega)
  rw [Functor.map_units_smul, Linear.comp_units_smul, Functor.map_comp, Functor.map_comp,
    ← Category.assoc]
  refine congrArg ((p * t).negOnePow • ·) ?_
  exact (congrArg (· ≫ _) hn.symm).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hι.symm)).trans
      (Category.assoc _ _ _))))

/-- **The naive cup product and the shift of the first factor**, on a summand: followed by the
identification `Tot(𝒦^•[t] ⊗ ℒ^•) ≅ Tot(𝒦^• ⊗ ℒ^•)[t]` of `CochainComplex.mapBifunctorShift₁Iso`,
which involves no sign, the naive cup product of `𝒦^•[t]` and `ℒ^•` on the summand `(p, q)` is
the naive cup product of `𝒦^•` and `ℒ^•` on the summand `(p + t, q)`. -/
@[reassoc]
theorem ι_naiveCupProductEval_shift₁ (t p q n : ℤ) (h : p + q = n) (p' n' : ℤ)
    (hp : p' = p + t) (hn : n' = n + t) :
    HomologicalComplex.ιMapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ) p q n h ≫ (naiveCupProductEval O V (K⟦t⟧) L).f n ≫
        (SheafOfModules.evaluation (ringSheaf O) (op V)).map
          ((CochainComplex.mapBifunctorShift₁Iso K L (sheafTensor O) t).hom.f n) =
      ((tensorModules (CoeffRing O V)).map
          ((SheafOfModules.evaluation (ringSheaf O) (op V)).map
            (K.shiftFunctorObjXIso t p p' hp).hom)).app _ ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) p' q n' (by
            change p' + q = n'; omega) ≫
        (naiveCupProductEval O V K L).f n' ≫
        (SheafOfModules.evaluation (ringSheaf O) (op V)).map
          (CochainComplex.shiftFunctorObjXIso
            (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)) t n n' hn).inv := by
  rw [← Category.assoc, ι_naiveCupProductEval_f, Category.assoc, ← Functor.map_comp,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f K L (sheafTensor O) t p q n h p' n' hp hn]
  have hn := pairEval_naturality O V (K.shiftFunctorObjXIso t p p' hp).hom (𝟙 (L.X q))
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id] at hn
  have hι := ι_naiveCupProductEval_f O V K L p' q n' (by change p' + q = n'; omega)
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc]
  exact (congrArg (· ≫ _) hn.symm).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hι.symm)).trans
      (Category.assoc _ _ _))))

/-! ### On cocycles -/

open Stacks.Cohomology.DerivedGlobalCupProduct (shiftCycles shiftCycles_iCycles
  map_shiftFunctorObjXIso_hom map_shiftFunctorObjXIso_inv map_shiftFunctorObjXIso_inv_comp_hom)

/-- The tensor product of two morphisms of modules, for the bifunctor `tensorModules`. -/
abbrev tensorMap {A A' B B' : ModuleCat.{u} (CoeffRing O V)} (a : A ⟶ A') (b : B ⟶ B') :
    ((tensorModules (CoeffRing O V)).obj A).obj B ⟶
      ((tensorModules (CoeffRing O V)).obj A').obj B' :=
  ((tensorModules (CoeffRing O V)).map a).app B ≫ ((tensorModules (CoeffRing O V)).obj A').map b

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The tensor product of two morphisms for the bifunctor `tensorModules` is their tensor product
for the monoidal structure of modules. -/
theorem tensorMap_eq_tensorHom {A A' B B' : ModuleCat.{u} (CoeffRing O V)} (a : A ⟶ A')
    (b : B ⟶ B') : tensorMap O V a b = (a ⊗ₘ b : MonoidalCategory.tensorObj A B ⟶ _) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rfl

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `tensorMap` is compatible with composition in each variable. -/
theorem tensorMap_comp {A A' A'' B B' B'' : ModuleCat.{u} (CoeffRing O V)} (a : A ⟶ A')
    (a' : A' ⟶ A'') (b : B ⟶ B') (b' : B' ⟶ B'') :
    tensorMap O V a b ≫ tensorMap O V a' b' = tensorMap O V (a ≫ a') (b ≫ b') := by
  simp [tensorMap]

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The cocycles of `Γ(V, T[t])` and of `Γ(V, T)[t]` agree: the commutation of sections with the
shift is the identity in each degree. -/
@[reassoc]
theorem cyclesMap_commShiftIso_iCycles
    (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ) (t n : ℤ) :
    HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
        (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app T) n ≫
      HomologicalComplex.iCycles ((CategoryTheory.shiftFunctor (CochainComplex
        (ModuleCat.{u} (CoeffRing O V)) ℤ) t).obj (evalComplex O V T)) n =
      HomologicalComplex.iCycles (evalComplex O V (T⟦t⟧)) n :=
  (HomologicalComplex.cyclesMap_i _ _).trans (Category.comp_id _)

/-- Sections of the identification `(T[t])ⁿ ≅ Tⁿ⁺ᵗ` of a total tensor complex cancel against the
identification for the complex of sections. -/
theorem eval_shiftFunctorObjXIso_inv_comp_hom (t n n' : ℤ) (h : n' = n + t) :
    (SheafOfModules.evaluation (ringSheaf O) (op V)).map
        (CochainComplex.shiftFunctorObjXIso
          (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)) t n n' h).inv ≫
      (CochainComplex.shiftFunctorObjXIso
        (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) t n n'
          h).hom =
      𝟙 _ := by
  subst h
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

private theorem shift_paste {C : Type*} [Category* C] [Preadditive C]
    {a b c d e f g h k l m r s : C} (tz : a ⟶ b) (tw : b ⟶ c) (t1 : c ⟶ d) (t2 : d ⟶ e)
    (ι' : e ⟶ f) (nf' : f ⟶ g) (sf : g ⟶ h) (xh : h ⟶ m) (mE : e ⟶ k) (ι : k ⟶ l)
    (nf : l ⟶ m) (exinv : m ⟶ h) (tsc : b ⟶ r) (z₀ : r ⟶ s) (cMiC : s ⟶ m) (t12' : r ⟶ k)
    (u : ℤˣ)
    (H1 : ι' ≫ nf' ≫ sf = u • (mE ≫ ι ≫ nf ≫ exinv)) (H2 : exinv ≫ xh = 𝟙 _)
    (H3 : tw ≫ t1 ≫ t2 ≫ mE = tsc ≫ t12') (H4 : z₀ ≫ cMiC = t12' ≫ ι ≫ nf) :
    tz ≫ tw ≫ t1 ≫ t2 ≫ ι' ≫ nf' ≫ sf ≫ xh = u • (tz ≫ tsc ≫ z₀ ≫ cMiC) := by
  have e0 : tz ≫ tw ≫ t1 ≫ t2 ≫ ι' ≫ nf' ≫ sf ≫ xh = tz ≫ tw ≫ t1 ≫ t2 ≫ (ι' ≫ nf' ≫ sf) ≫ xh := by
    simp only [Category.assoc]
  rw [e0, H1, Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [H2, Category.comp_id, Linear.comp_units_smul, Linear.comp_units_smul,
    Linear.comp_units_smul, Linear.comp_units_smul, H4, ← reassoc_of% H3]

/-- The naive cup product of `𝒦^•` and `ℒ^•[t]` on the summand `(i, j)`, followed by
`mapBifunctorShift₂Iso` and read in degree `i + (j + t)`, is `(-1)^{it}` times the naive cup
product of `𝒦^•` and `ℒ^•` on `(i, j + t)`. -/
theorem ι_naiveCupProductEval_shift₂_X (t i j : ℤ) :
    HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
        (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl ≫
      (naiveCupProductEval O V K (L⟦t⟧)).f (i + j) ≫
      (SheafOfModules.evaluation (ringSheaf O) (op V)).map
        ((CochainComplex.mapBifunctorShift₂Iso K L (sheafTensor O) t).hom.f (i + j)) ≫
      (CochainComplex.shiftFunctorObjXIso
        (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) t (i + j)
          (i + (j + t)) (by omega)).hom =
      (i * t).negOnePow • (((tensorModules (CoeffRing O V)).obj _).map
          ((SheafOfModules.evaluation (ringSheaf O) (op V)).map
            (L.shiftFunctorObjXIso t j (j + t) rfl).hom) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) i (j + t) (i + (j + t)) rfl ≫
        (naiveCupProductEval O V K L).f (i + (j + t))) := by
  rw [ι_naiveCupProductEval_shift₂_assoc O V K L t i j (i + j) rfl (j + t) (i + (j + t)) rfl
      (by omega), Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [map_shiftFunctorObjXIso_inv, Iso.inv_hom_id, Category.comp_id]

/-- The naive cup product of cocycles `z` of `Γ(V, 𝒦^•)` and `w` of `Γ(V, ℒ^•[t])`, carried to
`Tot(𝒦^• ⊗ ℒ^•)[t]` and read in the term of degree `i + (j + t)`, factors through the summand
`(i, j)` of `Tot(Γ(V, 𝒦^•) ⊗ Γ(V, ℒ^•[t]))`. -/
theorem cycles_naiveCupProductEval_shift₂_aux (t i j : ℤ) {A B : ModuleCat.{u} (CoeffRing O V)}
    (z : A ⟶ (evalComplex O V K).cycles i) (w : B ⟶ (evalComplex O V (L⟦t⟧)).cycles j)
    (z₀' : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V K).cycles i)).obj
        ((evalComplex O V (L⟦t⟧)).cycles j) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles (i + j))
    (hz₀' : z₀' ≫ (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles (i + j) =
      tensorMap O V ((evalComplex O V K).iCycles i) ((evalComplex O V (L⟦t⟧)).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
          (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl)
:
    shiftCycles (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)))
        (i + (j + t)) (by omega) (tensorMap O V z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V K (L⟦t⟧)) (i + j) ≫
          HomologicalComplex.cyclesMap (((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex
            (up ℤ)).map (CochainComplex.mapBifunctorShift₂Iso K L (sheafTensor O) t).hom) (i + j) ≫
          HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app
              (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) (i + j)) ≫
        (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).iCycles
          (i + (j + t)) =
      tensorMap O V z w ≫ tensorMap O V ((evalComplex O V K).iCycles i)
          ((evalComplex O V (L⟦t⟧)).iCycles j) ≫
        (HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
          (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl ≫
        (naiveCupProductEval O V K (L⟦t⟧)).f (i + j) ≫
        (SheafOfModules.evaluation (ringSheaf O) (op V)).map
          ((CochainComplex.mapBifunctorShift₂Iso K L (sheafTensor O) t).hom.f (i + j)) ≫
        (CochainComplex.shiftFunctorObjXIso
          (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) t (i + j)
            (i + (j + t)) (by omega)).hom) := by
  rw [shiftCycles_iCycles]
  simp only [Category.assoc]
  rw [cyclesMap_commShiftIso_iCycles_assoc, HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.cyclesMap_i_assoc, reassoc_of% hz₀', Functor.mapHomologicalComplex_map_f]

/-- A cocycle `w` of `Γ(V, T[t])` in degree `n`, read through `(T[t])ⁿ ≅ Tⁿ⁺ᵗ`, is the cocycle
`shiftCycles` of `Γ(V, T)`. -/
private theorem comp_iCycles_shiftFunctorObjXIso_hom {B : ModuleCat.{u} (CoeffRing O V)}
    (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ) (t n n' : ℤ)
    (h : n' = n + t) (w : B ⟶ (evalComplex O V (T⟦t⟧)).cycles n) :
    w ≫ (evalComplex O V (T⟦t⟧)).iCycles n ≫
      (SheafOfModules.evaluation (ringSheaf O) (op V)).map (T.shiftFunctorObjXIso t n n' h).hom =
      shiftCycles (evalComplex O V T) n' (by omega)
        (w ≫ HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
          (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app T) n) ≫
        (evalComplex O V T).iCycles n' := by
  -- mention the section-variable instance, so it is not flagged as unused
  have _ := ‹(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}›
  rw [shiftCycles_iCycles, Category.assoc, cyclesMap_commShiftIso_iCycles_assoc,
    map_shiftFunctorObjXIso_hom]

/-- The naive cup product of `z` and of `w` read as a cocycle of `Γ(V, ℒ^•)` in degree `j + t`,
read in the term of degree `i + (j + t)`, factors through the summand `(i, j + t)` of
`Tot(Γ(V, 𝒦^•) ⊗ Γ(V, ℒ^•))`. -/
theorem cycles_naiveCupProductEval_shift₂_aux' (t i j : ℤ) {A B : ModuleCat.{u} (CoeffRing O V)}
    (z : A ⟶ (evalComplex O V K).cycles i) (w : B ⟶ (evalComplex O V (L⟦t⟧)).cycles j)
    (z₀ : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V K).cycles i)).obj
        ((evalComplex O V L).cycles (j + t)) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles (i + (j + t)))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles (i + (j + t)) =
      tensorMap O V ((evalComplex O V K).iCycles i) ((evalComplex O V L).iCycles (j + t)) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) i (j + t) (i + (j + t)) rfl) :
    tensorMap O V z w ≫ tensorMap O V ((evalComplex O V K).iCycles i)
        ((evalComplex O V (L⟦t⟧)).iCycles j) ≫
      ((tensorModules (CoeffRing O V)).obj ((evalComplex O V K).X i)).map
          ((SheafOfModules.evaluation (ringSheaf O) (op V)).map
            (L.shiftFunctorObjXIso t j (j + t) rfl).hom) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) i (j + t) (i + (j + t)) rfl ≫
        (naiveCupProductEval O V K L).f (i + (j + t)) =
      (tensorMap O V z (shiftCycles (evalComplex O V L) (j + t) (by omega)
          (w ≫ HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app L) j)) ≫ z₀ ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V K L) (i + (j + t))) ≫
        (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).iCycles
          (i + (j + t)) := by
  simp only [Category.assoc]
  rw [HomologicalComplex.cyclesMap_i, reassoc_of% hz₀]
  have nat1 := ((tensorModules (CoeffRing O V)).map ((evalComplex O V K).iCycles i)).naturality w
  have nat2 := ((tensorModules (CoeffRing O V)).map ((evalComplex O V K).iCycles i)).naturality
    (shiftCycles (evalComplex O V L) (j + t) (by omega)
        (w ≫ HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
          (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app L) j))
  rw [reassoc_of% nat1, reassoc_of% nat2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, Category.assoc,
    comp_iCycles_shiftFunctorObjXIso_hom O V L t j (j + t) rfl w]

/-- **The naive cup product of cocycles and the shift of the second factor.** For cocycles `z` of
`Γ(V, 𝒦^•)` and `w` of `Γ(V, ℒ^•[t])`, the naive cup product of `z` and `w`, carried to
`Tot(𝒦^• ⊗ ℒ^•)[t]` by `mapBifunctorShift₂Iso` and read in degree `i + (j + t)`, is `(-1)^{it}`
times the naive cup product of `z` and of `w` read as a cocycle of `Γ(V, ℒ^•)` in degree `j + t`.
Here `z₀'` and `z₀` are the tensorings of cocycles. -/
theorem cycles_naiveCupProductEval_shift₂ (t i j : ℤ) {A B : ModuleCat.{u} (CoeffRing O V)}
    (z : A ⟶ (evalComplex O V K).cycles i) (w : B ⟶ (evalComplex O V (L⟦t⟧)).cycles j)
    (z₀' : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V K).cycles i)).obj
        ((evalComplex O V (L⟦t⟧)).cycles j) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles (i + j))
    (hz₀' : z₀' ≫ (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles (i + j) =
      tensorMap O V ((evalComplex O V K).iCycles i) ((evalComplex O V (L⟦t⟧)).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V (L⟦t⟧))
          (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl)
    (z₀ : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V K).cycles i)).obj
        ((evalComplex O V L).cycles (j + t)) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles (i + (j + t)))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles (i + (j + t)) =
      tensorMap O V ((evalComplex O V K).iCycles i) ((evalComplex O V L).iCycles (j + t)) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) i (j + t) (i + (j + t)) rfl) :
    shiftCycles (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)))
        (i + (j + t)) (by omega) (tensorMap O V z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V K (L⟦t⟧)) (i + j) ≫
          HomologicalComplex.cyclesMap (((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex
            (up ℤ)).map (CochainComplex.mapBifunctorShift₂Iso K L (sheafTensor O) t).hom) (i + j) ≫
          HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app
              (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) (i + j)) =
      (i * t).negOnePow • (tensorMap O V z (shiftCycles (evalComplex O V L) (j + t)
          (by omega) (w ≫ HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app L) j)) ≫ z₀ ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V K L) (i + (j + t))) := by
  refine (cancel_mono ((evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O)
    (up ℤ))).iCycles (i + (j + t)))).1 ?_
  refine (cycles_naiveCupProductEval_shift₂_aux O V K L t i j z w z₀' hz₀').trans ?_
  refine (congrArg (fun x => tensorMap O V z w ≫ tensorMap O V ((evalComplex O V K).iCycles i)
    ((evalComplex O V (L⟦t⟧)).iCycles j) ≫ x)
      (ι_naiveCupProductEval_shift₂_X O V K L t i j)).trans ?_
  rw [Linear.comp_units_smul, Linear.comp_units_smul, Linear.units_smul_comp]
  exact congrArg ((i * t).negOnePow • ·)
    (cycles_naiveCupProductEval_shift₂_aux' O V K L t i j z w z₀ hz₀)

/-! ### The shift of the first factor, on cocycles -/

/-- The naive cup product of `𝒦^•[t]` and `ℒ^•` on the summand `(i, j)`, followed by
`mapBifunctorShift₁Iso` and read in degree `(i + t) + j`, is the naive cup product of `𝒦^•` and
`ℒ^•` on `(i + t, j)`. -/
theorem ι_naiveCupProductEval_shift₁_X (t i j : ℤ) :
    HomologicalComplex.ιMapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl ≫
      (naiveCupProductEval O V (K⟦t⟧) L).f (i + j) ≫
      (SheafOfModules.evaluation (ringSheaf O) (op V)).map
        ((CochainComplex.mapBifunctorShift₁Iso K L (sheafTensor O) t).hom.f (i + j)) ≫
      (CochainComplex.shiftFunctorObjXIso
        (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) t (i + j)
          ((i + t) + j) (by omega)).hom =
      ((tensorModules (CoeffRing O V)).map ((SheafOfModules.evaluation (ringSheaf O) (op V)).map
        (K.shiftFunctorObjXIso t i (i + t) rfl).hom)).app _ ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) (i + t) j ((i + t) + j) rfl ≫
        (naiveCupProductEval O V K L).f ((i + t) + j) := by
  rw [ι_naiveCupProductEval_shift₁_assoc O V K L t i j (i + j) rfl (i + t) ((i + t) + j) rfl
      (by omega), map_shiftFunctorObjXIso_inv, Iso.inv_hom_id, Category.comp_id]

/-- The naive cup product of cocycles `z` of `Γ(V, 𝒦^•[t])` and `w` of `Γ(V, ℒ^•)`, carried to
`Tot(𝒦^• ⊗ ℒ^•)[t]` and read in the term of degree `(i + t) + j`, factors through the summand
`(i, j)` of `Tot(Γ(V, 𝒦^•[t]) ⊗ Γ(V, ℒ^•))`. -/
theorem cycles_naiveCupProductEval_shift₁_aux (t i j : ℤ) {A B : ModuleCat.{u} (CoeffRing O V)}
    (z : A ⟶ (evalComplex O V (K⟦t⟧)).cycles i) (w : B ⟶ (evalComplex O V L).cycles j)
    (z₀' : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V (K⟦t⟧)).cycles i)).obj
        ((evalComplex O V L).cycles j) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles (i + j))
    (hz₀' : z₀' ≫ (HomologicalComplex.mapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles (i + j) =
      tensorMap O V ((evalComplex O V (K⟦t⟧)).iCycles i) ((evalComplex O V L).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl) :
    shiftCycles (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)))
        ((i + t) + j) (by omega) (tensorMap O V z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V (K⟦t⟧) L) (i + j) ≫
          HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ))).map
            (CochainComplex.mapBifunctorShift₁Iso K L (sheafTensor O) t).hom) (i + j) ≫
          HomologicalComplex.cyclesMap (((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ))).commShiftIso t).hom.app
              (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) (i + j)) ≫
        (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).iCycles
          ((i + t) + j) =
      tensorMap O V z w ≫ tensorMap O V ((evalComplex O V (K⟦t⟧)).iCycles i)
          ((evalComplex O V L).iCycles j) ≫
        (HomologicalComplex.ιMapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl ≫
        (naiveCupProductEval O V (K⟦t⟧) L).f (i + j) ≫
        (SheafOfModules.evaluation (ringSheaf O) (op V)).map
          ((CochainComplex.mapBifunctorShift₁Iso K L (sheafTensor O) t).hom.f (i + j)) ≫
        (CochainComplex.shiftFunctorObjXIso
          (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) t (i + j)
          ((i + t) + j) (by omega)).hom) := by
  rw [shiftCycles_iCycles]
  simp only [Category.assoc]
  rw [cyclesMap_commShiftIso_iCycles_assoc, HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.cyclesMap_i_assoc, reassoc_of% hz₀', Functor.mapHomologicalComplex_map_f]

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `tensorModules` applied to a morphism in the first variable is a tensor product of
morphisms. -/
theorem tensorModules_map_app_eq_tensorMap {A A' : ModuleCat.{u} (CoeffRing O V)} (a : A ⟶ A')
    (B : ModuleCat.{u} (CoeffRing O V)) :
    ((tensorModules (CoeffRing O V)).map a).app B = tensorMap O V a (𝟙 B) := by
  simp only [tensorMap, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem shift₁_glue {C : Type*} [Category* C] {a₀ a₁ a₂ a₃ ι₀ n₀ d₁ z₁ c₁ : C}
    (a : a₀ ⟶ a₁) (b : a₁ ⟶ a₂) (c : a₂ ⟶ a₃) (ι : a₃ ⟶ ι₀) (nf : ι₀ ⟶ n₀) (m : a₀ ⟶ a₃)
    (d : a₀ ⟶ d₁) (e : d₁ ⟶ a₃) (z₀ : d₁ ⟶ z₁) (iT : z₁ ⟶ ι₀) (cM : z₁ ⟶ c₁) (iC : c₁ ⟶ n₀)
    (hL : a ≫ b ≫ c = m) (hR : d ≫ e = m) (h₀ : z₀ ≫ iT = e ≫ ι) (hc : cM ≫ iC = iT ≫ nf) :
    a ≫ b ≫ c ≫ ι ≫ nf = (d ≫ z₀ ≫ cM) ≫ iC := by
  simp only [Category.assoc]
  rw [hc, reassoc_of% h₀, ← Category.assoc d e, hR, ← hL]
  simp only [Category.assoc]

/-- The naive cup product of `z` read as a cocycle of `Γ(V, 𝒦^•)` in degree `i + t` and of `w`,
read in the term of degree `(i + t) + j`, factors through the summand `(i + t, j)` of
`Tot(Γ(V, 𝒦^•) ⊗ Γ(V, ℒ^•))`. -/
theorem cycles_naiveCupProductEval_shift₁_aux' (t i j : ℤ) {A B : ModuleCat.{u} (CoeffRing O V)}
    (z : A ⟶ (evalComplex O V (K⟦t⟧)).cycles i) (w : B ⟶ (evalComplex O V L).cycles j)
    (z₀ : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V K).cycles (i + t))).obj
        ((evalComplex O V L).cycles j) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles ((i + t) + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles ((i + t) + j) =
      tensorMap O V ((evalComplex O V K).iCycles (i + t)) ((evalComplex O V L).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) (i + t) j ((i + t) + j) rfl) :
    tensorMap O V z w ≫ tensorMap O V ((evalComplex O V (K⟦t⟧)).iCycles i)
        ((evalComplex O V L).iCycles j) ≫
      ((tensorModules (CoeffRing O V)).map ((SheafOfModules.evaluation (ringSheaf O) (op V)).map
        (K.shiftFunctorObjXIso t i (i + t) rfl).hom)).app _ ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) (i + t) j ((i + t) + j) rfl ≫
        (naiveCupProductEval O V K L).f ((i + t) + j) =
      (tensorMap O V (shiftCycles (evalComplex O V K) (i + t) (by omega)
          (z ≫ HomologicalComplex.cyclesMap (((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ))).commShiftIso t).hom.app K) i)) w ≫ z₀ ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V K L) ((i + t) + j)) ≫
        (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))).iCycles
          ((i + t) + j) := by
  have hL : tensorMap O V z w ≫ tensorMap O V ((evalComplex O V (K⟦t⟧)).iCycles i)
        ((evalComplex O V L).iCycles j) ≫
      ((tensorModules (CoeffRing O V)).map ((SheafOfModules.evaluation (ringSheaf O) (op V)).map
        (K.shiftFunctorObjXIso t i (i + t) rfl).hom)).app _ =
      tensorMap O V (shiftCycles (evalComplex O V K) (i + t) (by omega)
          (z ≫ HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ)).commShiftIso t).hom.app K) i) ≫
          (evalComplex O V K).iCycles (i + t)) (w ≫ (evalComplex O V L).iCycles j) := by
    rw [tensorModules_map_app_eq_tensorMap, tensorMap_comp, tensorMap_comp, Category.comp_id,
      comp_iCycles_shiftFunctorObjXIso_hom O V K t i (i + t) rfl z]
    rfl
  exact shift₁_glue _ _ _ _ _ _ _ _ _ _ _ _ hL (tensorMap_comp O V _ _ _ _) hz₀
    (HomologicalComplex.cyclesMap_i _ _)

/-- **The naive cup product of cocycles and the shift of the first factor.** For cocycles `z` of
`Γ(V, 𝒦^•[t])` and `w` of `Γ(V, ℒ^•)`, the naive cup product of `z` and `w`, carried to
`Tot(𝒦^• ⊗ ℒ^•)[t]` by `mapBifunctorShift₁Iso` and read in degree `(i + t) + j`, is the naive cup
product of `z`, read as a cocycle of `Γ(V, 𝒦^•)` in degree `i + t`, and of `w`. There is no sign.
Here `z₀'` and `z₀` are the tensorings of cocycles. -/
theorem cycles_naiveCupProductEval_shift₁ (t i j : ℤ) {A B : ModuleCat.{u} (CoeffRing O V)}
    (z : A ⟶ (evalComplex O V (K⟦t⟧)).cycles i) (w : B ⟶ (evalComplex O V L).cycles j)
    (z₀' : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V (K⟦t⟧)).cycles i)).obj
        ((evalComplex O V L).cycles j) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles (i + j))
    (hz₀' : z₀' ≫ (HomologicalComplex.mapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles (i + j) =
      tensorMap O V ((evalComplex O V (K⟦t⟧)).iCycles i) ((evalComplex O V L).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V (K⟦t⟧)) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) i j (i + j) rfl)
    (z₀ : ((tensorModules (CoeffRing O V)).obj ((evalComplex O V K).cycles (i + t))).obj
        ((evalComplex O V L).cycles j) ⟶
      (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).cycles ((i + t) + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor (evalComplex O V K) (evalComplex O V L)
        (tensorModules (CoeffRing O V)) (up ℤ)).iCycles ((i + t) + j) =
      tensorMap O V ((evalComplex O V K).iCycles (i + t)) ((evalComplex O V L).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (evalComplex O V K) (evalComplex O V L)
          (tensorModules (CoeffRing O V)) (up ℤ) (i + t) j ((i + t) + j) rfl) :
    shiftCycles (evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)))
        ((i + t) + j) (by omega) (tensorMap O V z w ≫ z₀' ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V (K⟦t⟧) L) (i + j) ≫
          HomologicalComplex.cyclesMap ((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ))).map
            (CochainComplex.mapBifunctorShift₁Iso K L (sheafTensor O) t).hom) (i + j) ≫
          HomologicalComplex.cyclesMap (((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ))).commShiftIso t).hom.app
              (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ))) (i + j)) =
      tensorMap O V (shiftCycles (evalComplex O V K) (i + t) (by omega)
          (z ≫ HomologicalComplex.cyclesMap (((((SheafOfModules.evaluation (ringSheaf O)
            (op V)).mapHomologicalComplex (up ℤ))).commShiftIso t).hom.app K) i)) w ≫ z₀ ≫
          HomologicalComplex.cyclesMap (naiveCupProductEval O V K L) ((i + t) + j) := by
  refine (cancel_mono ((evalComplex O V (HomologicalComplex.mapBifunctor K L (sheafTensor O)
    (up ℤ))).iCycles ((i + t) + j))).1 ?_
  refine (cycles_naiveCupProductEval_shift₁_aux O V K L t i j z w z₀' hz₀').trans ?_
  refine (congrArg (fun x => tensorMap O V z w ≫ tensorMap O V ((evalComplex O V (K⟦t⟧)).iCycles i)
    ((evalComplex O V L).iCycles j) ≫ x)
      (ι_naiveCupProductEval_shift₁_X O V K L t i j)).trans ?_
  exact cycles_naiveCupProductEval_shift₁_aux' O V K L t i j z w z₀ hz₀

end Stacks.Cech.SheafTensorPairing

end
