module

public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismGluing
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassRestriction
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow

/-!
# Descending a factorization to a compatible morphism (Step 3 of Stacks 08U8)

Continuation of `StacksFrontier/Deformation/RingedSpaceThickening/CompatibleMorphismGluing.lean`:
from a factorization `Δ = θ ∘ d_N` of the difference homomorphism through the degree `0` term of
`N`, the `S`-morphism `Y' ⟶ X'` compatible with `g` and `c` is glued from the local values
`e' + θ(d[s], d[e'])`, `e'` a local lift of `g^♯(s mod ℱ)` to `𝒪_{Y'}`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.LiftGluing.compatibleMorphismOfFactorization`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal conormalClass tensorDifferential)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheafCoefficientMap freeAlgebraSheafVariable_comp_desc)

universe u v₁ u₁

namespace AlgebraicGeometry.RingedSpaceThickening.LiftGluing

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} (g : Y ⟶ X)
  {F : SheafOfModules.{u} (structureSheafRing X)} {G : SheafOfModules.{u} (structureSheafRing Y)}
  (P : SquareZeroAlgebraExtension f F) (Q : SquareZeroAlgebraExtension (g ≫ f) G)
  (c : F ⟶ (modulePushforward g).obj G)

/-- Evaluating a composite of morphisms of sheaves of modules on a section. -/
theorem comp_app_apply' {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N L : SheafOfModules.{u} R} (a : M ⟶ N) (b : N ⟶ L)
    (V : Cᵒᵖ) (x : M.val.obj V) : (a ≫ b).val.app V x = b.val.app V (a.val.app V x) := by
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app]
  rfl

/-- Evaluating a difference of morphisms of sheaves of modules on a section. -/
theorem sub_app_apply' {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (a b : M ⟶ N)
    (V : Cᵒᵖ) (x : M.val.obj V) : (a - b).val.app V x = a.val.app V x - b.val.app V x :=
  rfl

theorem map_id_apply' {Z : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    (V : Opens Z) (x : A.obj.obj (op V)) : (A.obj.map (𝟙 (op V))).hom x = x := by
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem map_comp_apply' {Z : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    {V₁ V₂ V₃ : Opens Z} (i : V₁ ⟶ V₂) (j : V₂ ⟶ V₃) (x : A.obj.obj (op V₃)) :
    (A.obj.map i.op).hom ((A.obj.map j.op).hom x) = (A.obj.map (i ≫ j).op).hom x := by
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- Sections of a sheaf of rings agreeing locally on a covering sieve are equal. -/
theorem sheaf_eq_of_sieve {Z : TopCat.{u}}
    (A : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    {V : Opens Z} (T : Sieve V) (hT : T ∈ Opens.grothendieckTopology Z V) (x y : A.obj.obj (op V))
    (h : ∀ (W : Opens Z) (i : W ⟶ V), T i → (A.obj.map i.op).hom x = (A.obj.map i.op).hom y) :
    x = y :=
  ((isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose (Opens.grothendieckTopology Z)
    (forget CommRingCat.{u})).obj A).property _ hT).isSeparatedFor.ext fun W i hi ↦ h W i hi

/-! ### Sections of fibre products of sheaves of modules -/

section PullbackMk

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B Z : SheafOfModules.{u} R} (φ : A ⟶ Z) (ψ : B ⟶ Z)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem pullbackMk_congr {V : Cᵒᵖ} {a a' : A.val.obj V} {b b' : B.val.obj V}
    (h : φ.val.app V a = ψ.val.app V b) (h' : φ.val.app V a' = ψ.val.app V b')
    (ha : a = a') (hb : b = b') :
    SheafOfModules.pullbackMk φ ψ V a b h = SheafOfModules.pullbackMk φ ψ V a' b' h' := by
  subst ha hb
  rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem pullbackMk_add {V : Cᵒᵖ} (a a' : A.val.obj V) (b b' : B.val.obj V)
    (h : φ.val.app V a = ψ.val.app V b) (h' : φ.val.app V a' = ψ.val.app V b')
    (h'' : φ.val.app V (a + a') = ψ.val.app V (b + b')) :
    SheafOfModules.pullbackMk φ ψ V (a + a') (b + b') h'' =
      SheafOfModules.pullbackMk φ ψ V a b h + SheafOfModules.pullbackMk φ ψ V a' b' h' := by
  refine SheafOfModules.pullback_section_ext _ _ _ ?_ ?_
  · rw [map_add, SheafOfModules.pullback_fst_pullbackMk, SheafOfModules.pullback_fst_pullbackMk,
      SheafOfModules.pullback_fst_pullbackMk]
  · rw [map_add, SheafOfModules.pullback_snd_pullbackMk, SheafOfModules.pullback_snd_pullbackMk,
      SheafOfModules.pullback_snd_pullbackMk]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem pullbackMk_smul {V : Cᵒᵖ} (r : R.obj.obj V) (a : A.val.obj V) (b : B.val.obj V)
    (h : φ.val.app V a = ψ.val.app V b) (h' : φ.val.app V (r • a) = ψ.val.app V (r • b)) :
    SheafOfModules.pullbackMk φ ψ V (r • a) (r • b) h' =
      r • SheafOfModules.pullbackMk φ ψ V a b h := by
  refine SheafOfModules.pullback_section_ext _ _ _ ?_ ?_
  · rw [map_smul, SheafOfModules.pullback_fst_pullbackMk, SheafOfModules.pullback_fst_pullbackMk]
  · rw [map_smul, SheafOfModules.pullback_snd_pullbackMk, SheafOfModules.pullback_snd_pullbackMk]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem pullbackMk_zero {V : Cᵒᵖ} (h : φ.val.app V 0 = ψ.val.app V 0) :
    SheafOfModules.pullbackMk φ ψ V 0 0 h = 0 := by
  refine SheafOfModules.pullback_section_ext _ _ _ ?_ ?_
  · rw [map_zero, SheafOfModules.pullback_fst_pullbackMk]
  · rw [map_zero, SheafOfModules.pullback_snd_pullbackMk]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem pullbackMk_map {V V' : Cᵒᵖ} (j : V ⟶ V') (a : A.val.obj V) (b : B.val.obj V)
    (h : φ.val.app V a = ψ.val.app V b)
    (h' : φ.val.app V' (A.val.map j a) = ψ.val.app V' (B.val.map j b)) :
    (pullback φ ψ).val.map j (SheafOfModules.pullbackMk φ ψ V a b h) =
      SheafOfModules.pullbackMk φ ψ V' (A.val.map j a) (B.val.map j b) h' := by
  refine SheafOfModules.pullback_section_ext φ ψ V' ?_ ?_
  · rw [PresheafOfModules.naturality_apply (pullback.fst φ ψ).val j,
      SheafOfModules.pullback_fst_pullbackMk]
    exact (SheafOfModules.pullback_fst_pullbackMk φ ψ V' _ _ h').symm
  · rw [PresheafOfModules.naturality_apply (pullback.snd φ ψ).val j,
      SheafOfModules.pullback_snd_pullbackMk]
    exact (SheafOfModules.pullback_snd_pullbackMk φ ψ V' _ _ h').symm

end PullbackMk

/-! ### Variables -/

section Variables

/-- The variable `[s]` of `f⁻¹𝒪_S[𝒪_{X'}]` at a local section `s` of `𝒪_{X'}`. -/
def varX (U : Opens X.carrier) (s : P.sheaf.obj.obj (op U)) : (FX P).obj.obj (op U) :=
  (freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    P.generators).app (op U) s

/-- The variable `[e]` of `(g ∘ f)⁻¹𝒪_S[𝒪_{Y'}]`. -/
def varβ (W : Opens Y.carrier) (e : Q.sheaf.obj.obj (op W)) : (Fβ g Q).obj.obj (op W) :=
  (freeAlgebraSheafVariable (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) Q.generators).app (op W) e

variable (f) in
/-- The variable `[y]` of `(g ∘ f)⁻¹𝒪_S[𝒪_Y]`. -/
def varY (W : Opens Y.carrier) (y : Y.sheaf.obj.obj (op W)) : (FY f g).obj.obj (op W) :=
  (freeAlgebraSheafVariable (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) (Y.sheaf.obj ⋙ forget CommRingCat)).app (op W) y

/-- `g^♯(s mod ℱ)`. -/
abbrev redX (U : Opens X.carrier) (s : P.sheaf.obj.obj (op U)) :
    Y.sheaf.obj.obj (op ((Opens.map g.hom.base).obj U)) :=
  (g.hom.c.app (op U)).hom ((P.reduction.hom.app (op U)).hom s)

theorem ΦX_varX (U : Opens X.carrier) (s : P.sheaf.obj.obj (op U)) :
    ((ΦX g P).hom.app (op U)).hom (varX P U s) =
      varY f g ((Opens.map g.hom.base).obj U) (redX g P U s) :=
  congrArg (fun t : P.generators ⟶ (Opens.map g.hom.base).op ⋙
      underlyingPresheaf (Opens.grothendieckTopology Y.carrier) (FY f g) ↦ t.app (op U) s)
    (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap g.hom.base
      (inverseImageBaseRing f) P.generators (inverseImageBaseRing (g ≫ f))
      (Y.sheaf.obj ⋙ forget CommRingCat) (baseRingPushMap g f) (εX g P))

theorem Φβ_varβ (W : Opens Y.carrier) (e : Q.sheaf.obj.obj (op W)) :
    ((Φβ g Q).hom.app (op W)).hom (varβ g Q W e) =
      varY f g W ((Q.reduction.hom.app (op W)).hom e) :=
  congrArg (fun t : Q.generators ⟶
      underlyingPresheaf (Opens.grothendieckTopology Y.carrier) (FY f g) ↦ t.app (op W) e)
    (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMap _ _ _ _ _)

theorem map_varY {W W' : Opens Y.carrier} (i : W' ⟶ W) (y : Y.sheaf.obj.obj (op W)) :
    ((FY f g).obj.map i.op).hom (varY f g W y) = varY f g W' ((Y.sheaf.obj.map i.op).hom y) := by
  have h := NatTrans.naturality_apply (freeAlgebraSheafVariable
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f))
    (Y.sheaf.obj ⋙ forget CommRingCat)) i.op y
  simp only [underlyingPresheaf, Functor.comp_map] at h
  exact h.symm

theorem lift_varX (U : Opens X.carrier) (s : P.sheaf.obj.obj (op U)) :
    (P.lift.hom.app (op U)).hom (varX P U s) = s := by
  have h := congrArg (fun t : P.generators ⟶ P.generators ↦ t.app (op U) s)
    (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_canonicalPresentation
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf P.base)
  simp only [NatTrans.comp_app_apply, Functor.whiskerRight_app, NatTrans.id_app,
    types_id_apply] at h
  exact h

theorem lift_varβ (W : Opens Y.carrier) (e : Q.sheaf.obj.obj (op W)) :
    (Q.lift.hom.app (op W)).hom (varβ g Q W e) = e := by
  have h := congrArg (fun t : Q.generators ⟶ Q.generators ↦ t.app (op W) e)
    (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_canonicalPresentation
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.sheaf Q.base)
  simp only [NatTrans.comp_app_apply, Functor.whiskerRight_app, NatTrans.id_app,
    types_id_apply] at h
  exact h

theorem pres_varX (U : Opens X.carrier) (s : P.sheaf.obj.obj (op U)) :
    (P.presentation.hom.app (op U)).hom (varX P U s) = (P.reduction.hom.app (op U)).hom s := by
  have h := congrArg (fun t : P.generators ⟶ _ ↦ t.app (op U) s)
    (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) X.sheaf P.generators (structureRingMap f) P.generatorsMap)
  simp only [NatTrans.comp_app_apply, Functor.whiskerRight_app] at h
  exact h

theorem pres_varβ (W : Opens Y.carrier) (e : Q.sheaf.obj.obj (op W)) :
    (Q.presentation.hom.app (op W)).hom (varβ g Q W e) = (Q.reduction.hom.app (op W)).hom e := by
  have h := congrArg (fun t : Q.generators ⟶ _ ↦ t.app (op W) e)
    (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology Y.carrier)
      (inverseImageBaseRing (g ≫ f)) Y.sheaf Q.generators (structureRingMap (g ≫ f))
      Q.generatorsMap)
  simp only [NatTrans.comp_app_apply, Functor.whiskerRight_app] at h
  exact h

theorem map_varX {U U' : Opens X.carrier} (k : U' ⟶ U) (s : P.sheaf.obj.obj (op U)) :
    ((FX P).obj.map k.op).hom (varX P U s) = varX P U' ((P.sheaf.obj.map k.op).hom s) := by
  have h := NatTrans.naturality_apply (freeAlgebraSheafVariable
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.generators) k.op s
  simp only [underlyingPresheaf, Functor.comp_map] at h
  exact h.symm

theorem map_varβ {W W' : Opens Y.carrier} (i : W' ⟶ W) (e : Q.sheaf.obj.obj (op W)) :
    ((Fβ g Q).obj.map i.op).hom (varβ g Q W e) = varβ g Q W' ((Q.sheaf.obj.map i.op).hom e) := by
  have h := NatTrans.naturality_apply (freeAlgebraSheafVariable
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.generators) i.op e
  simp only [underlyingPresheaf, Functor.comp_map] at h
  exact h.symm

end Variables

/-- A section of `𝒪_X` over `U`, mapped by `g^♯` to a scalar of `𝒪_Y` over `g⁻¹U`. -/
abbrev gScalar (U : Opens X.carrier) (r : X.sheaf.obj.obj (op U)) :
    (structureSheafRing Y).obj.obj (op ((Opens.map g.hom.base).obj U)) :=
  (g.hom.c.app (op U)).hom r

/-- A section of `𝒪_Y`, read as a scalar of `𝒪_Y`-modules. -/
abbrev yScalar {V : (Opens Y.carrier)ᵒᵖ} (r : Y.sheaf.obj.obj V) :
    (structureSheafRing Y).obj.obj V :=
  r

/-! ### The pairs -/

section Pairs

variable (U : Opens X.carrier) {W : Opens Y.carrier} (i : W ⟶ (Opens.map g.hom.base).obj U)

/-- The restriction to `W` of the image under the unit of `1 ⊗ d z`. -/
def restrDiffX (z : (FX P).obj.obj (op U)) :
    ((modulePullback g).obj (bX P)).val.obj (op W) :=
  ((modulePullback g).obj (bX P)).val.map i.op (unitDiffX g P U z)

theorem diffY_map {V W' : (Opens Y.carrier)ᵒᵖ} (j : V ⟶ W') (z : (FY f g).obj.obj V) :
    diffY g W' (((FY f g).obj.map j).hom z) =
      (bY f g).val.map j
        (diffY g V z) := by
  have h := Stacks.Sites.Conormal.tensorDifferential_map.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (FY f g) Y.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) (presY f g) j z
  unfold diffY
  exact h

theorem diffβ_map {V W' : (Opens Y.carrier)ᵒᵖ} (j : V ⟶ W') (z : (Fβ g Q).obj.obj V) :
    diffβ g Q W' (((Fβ g Q).obj.map j).hom z) = (bβ g Q).val.map j (diffβ g Q V z) := by
  have h := Stacks.Sites.Conormal.tensorDifferential_map.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Fβ g Q) Y.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) Q.presentation j z
  unfold diffβ bβ
  exact h

theorem ψ₁_restrDiffX (z : (FX P).obj.obj (op U)) :
    (ψ₁ g P).val.app (op W) (restrDiffX g P U i z) =
      diffY g (op W) (((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z)) := by
  have h1 := PresheafOfModules.naturality_apply (ψ₁ g P).val i.op (unitDiffX g P U z)
  rw [ψ₁_unitDiffX] at h1
  unfold restrDiffX
  exact h1.trans (diffY_map g i.op _).symm

theorem unitDiffX_add (z₁ z₂ : (FX P).obj.obj (op U)) :
    unitDiffX g P U (z₁ + z₂) = unitDiffX g P U z₁ + unitDiffX g P U z₂ := by
  have h := Stacks.Sites.Conormal.tensorDifferential_add.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (FX P) X.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) P.presentation (op U) z₁ z₂
  unfold unitDiffX
  rw [h]
  exact unitSec_add g _ U _ _

theorem restrDiffX_add (z₁ z₂ : (FX P).obj.obj (op U)) :
    restrDiffX g P U i (z₁ + z₂) = restrDiffX g P U i z₁ + restrDiffX g P U i z₂ := by
  unfold restrDiffX
  rw [unitDiffX_add]
  exact map_add _ _ _

theorem diffβ_add (W' : (Opens Y.carrier)ᵒᵖ) (w₁ w₂ : (Fβ g Q).obj.obj W') :
    diffβ g Q W' (w₁ + w₂) = diffβ g Q W' w₁ + diffβ g Q W' w₂ := by
  have h := Stacks.Sites.Conormal.tensorDifferential_add.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Fβ g Q) Y.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) Q.presentation W' w₁ w₂
  unfold diffβ
  exact h

theorem unitDiffX_mul (z₁ z₂ : (FX P).obj.obj (op U)) :
    unitDiffX g P U (z₁ * z₂) =
      gScalar g U ((P.presentation.hom.app (op U)).hom z₁) • unitDiffX g P U z₂ +
        gScalar g U ((P.presentation.hom.app (op U)).hom z₂) • unitDiffX g P U z₁ := by
  have h := Stacks.Sites.Conormal.tensorDifferential_mul.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (FX P) X.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) P.presentation (op U) z₁ z₂
  unfold unitDiffX
  rw [h]
  exact (unitSec_add g _ U _ _).trans (congrArg₂ (· + ·) (unitSec_smul g _ U _ _)
    (unitSec_smul g _ U _ _))

theorem restrDiffX_mul (z₁ z₂ : (FX P).obj.obj (op U)) :
    restrDiffX g P U i (z₁ * z₂) =
      yScalar ((Y.sheaf.obj.map i.op).hom
        ((g.hom.c.app (op U)).hom ((P.presentation.hom.app (op U)).hom z₁))) •
          restrDiffX g P U i z₂ +
      yScalar ((Y.sheaf.obj.map i.op).hom
        ((g.hom.c.app (op U)).hom ((P.presentation.hom.app (op U)).hom z₂))) •
          restrDiffX g P U i z₁ := by
  unfold restrDiffX
  rw [unitDiffX_mul, map_add]
  exact congrArg₂ (· + ·) (PresheafOfModules.map_smul _ _ _ _)
    (PresheafOfModules.map_smul _ _ _ _)

theorem diffβ_mul (W' : (Opens Y.carrier)ᵒᵖ) (w₁ w₂ : (Fβ g Q).obj.obj W') :
    diffβ g Q W' (w₁ * w₂) =
      yScalar ((Q.presentation.hom.app W').hom w₁) • diffβ g Q W' w₂ +
        yScalar ((Q.presentation.hom.app W').hom w₂) • diffβ g Q W' w₁ := by
  have h := Stacks.Sites.Conormal.tensorDifferential_mul.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Fβ g Q) Y.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) Q.presentation W' w₁ w₂
  unfold diffβ
  exact h

/-- The pair `(d z, d w) ∈ N₁(W)` of local differentials with the same image. -/
def dpair (z : (FX P).obj.obj (op U)) (w : (Fβ g Q).obj.obj (op W))
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w) : (N₁ g P Q).val.obj (op W) :=
  SheafOfModules.pullbackMk (ψ₁ g P) (ιβ₁ g Q) (op W) (restrDiffX g P U i z)
    (diffβ g Q (op W) w)
    ((ψ₁_restrDiffX g P U i z).trans ((congrArg (diffY g (op W)) h).trans
      (ιβ₁_diffβ g Q (op W) w).symm))

theorem unitSec_map (M : SheafOfModules.{u} (structureSheafRing X)) {U U' : Opens X.carrier}
    (k : U' ⟶ U) (m : M.val.obj (op U)) :
    unitSec g M U' (M.val.map k.op m) =
      ((modulePullback g).obj M).val.map ((Opens.map g.hom.base).map k).op (unitSec g M U m) :=
  PresheafOfModules.naturality_apply ((modulePullbackPushforwardAdjunction g).unit.app M).val k.op m

theorem unitDiffX_map {U' : Opens X.carrier} (k : U' ⟶ U) (z : (FX P).obj.obj (op U)) :
    unitDiffX g P U' (((FX P).obj.map k.op).hom z) =
      ((modulePullback g).obj (bX P)).val.map ((Opens.map g.hom.base).map k).op
        (unitDiffX g P U z) := by
  have h := Stacks.Sites.Conormal.tensorDifferential_map.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (FX P) X.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) P.presentation k.op z
  unfold unitDiffX
  rw [h]
  exact unitSec_map g (bX P) k _

theorem restrDiffX_map {U' : Opens X.carrier} (k : U' ⟶ U) {W' : Opens Y.carrier}
    (i' : W' ⟶ (Opens.map g.hom.base).obj U') (z : (FX P).obj.obj (op U)) :
    restrDiffX g P U' i' (((FX P).obj.map k.op).hom z) =
      restrDiffX g P U (i' ≫ (Opens.map g.hom.base).map k) z := by
  unfold restrDiffX
  rw [unitDiffX_map]
  exact (((modulePullback g).obj (bX P)).val.map_comp_apply _ _ _).symm

theorem match_comp {U' : Opens X.carrier} (k : U' ⟶ U) {W' : Opens Y.carrier}
    (i' : W' ⟶ (Opens.map g.hom.base).obj U') {z : (FX P).obj.obj (op U)}
    {w : (Fβ g Q).obj.obj (op W')}
    (h : ((FY f g).obj.map i'.op).hom (((ΦX g P).hom.app (op U')).hom
      (((FX P).obj.map k.op).hom z)) = ((Φβ g Q).hom.app (op W')).hom w) :
    ((FY f g).obj.map (i' ≫ (Opens.map g.hom.base).map k).op).hom
      (((ΦX g P).hom.app (op U)).hom z) = ((Φβ g Q).hom.app (op W')).hom w := by
  refine Eq.trans ?_ h
  rw [NatTrans.naturality_apply (ΦX g P).hom k.op z]
  exact (map_comp_apply' (FY f g) _ _ _).symm

theorem dpair_add (z₁ z₂ : (FX P).obj.obj (op U)) (w₁ w₂ : (Fβ g Q).obj.obj (op W))
    (h₁ : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z₁) =
      ((Φβ g Q).hom.app (op W)).hom w₁)
    (h₂ : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z₂) =
      ((Φβ g Q).hom.app (op W)).hom w₂)
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom (z₁ + z₂)) =
      ((Φβ g Q).hom.app (op W)).hom (w₁ + w₂)) :
    dpair g P Q U i (z₁ + z₂) (w₁ + w₂) h =
      dpair g P Q U i z₁ w₁ h₁ + dpair g P Q U i z₂ w₂ h₂ := by
  refine SheafOfModules.pullback_section_ext _ _ _ ?_ ?_
  · rw [map_add]
    unfold dpair
    rw [SheafOfModules.pullback_fst_pullbackMk, SheafOfModules.pullback_fst_pullbackMk,
      SheafOfModules.pullback_fst_pullbackMk]
    exact restrDiffX_add g P U i z₁ z₂
  · rw [map_add]
    unfold dpair
    rw [SheafOfModules.pullback_snd_pullbackMk, SheafOfModules.pullback_snd_pullbackMk,
      SheafOfModules.pullback_snd_pullbackMk]
    exact diffβ_add g Q (op W) w₁ w₂

/-- The restriction to `W` of the image under the unit of a local conormal class. -/
def restrClassX (z : kernelIdeal P.presentation.hom (op U)) :
    ((modulePullback g).obj (cX P)).val.obj (op W) :=
  ((modulePullback g).obj (cX P)).val.map i.op (unitClassX g P U z)

theorem classY_map {V W' : (Opens Y.carrier)ᵒᵖ} (j : V ⟶ W') (z : kernelIdeal (presY f g).hom V)
    (z' : kernelIdeal (presY f g).hom W') (hz : z'.1 = ((FY f g).obj.map j).hom z.1) :
    classY g W' z' =
      (cY f g).val.map j
        (classY g V z) := by
  have h := Stacks.Sites.Conormal.conormalClass_map.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (FY f g) Y.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) (presY f g) j z z' hz
  unfold classY
  exact h

theorem ψ₀_restrClassX (z : kernelIdeal P.presentation.hom (op U))
    (z' : kernelIdeal (presY f g).hom (op W))
    (hz : z'.1 = ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z.1)) :
    (ψ₀ g P).val.app (op W) (restrClassX g P U i z) = classY g (op W) z' := by
  have h1 := PresheafOfModules.naturality_apply (ψ₀ g P).val i.op (unitClassX g P U z)
  rw [ψ₀_unitClassX] at h1
  unfold restrClassX
  refine h1.trans ?_
  unfold pushClassY
  exact (classY_map g i.op _ z' hz).symm

theorem ιβ₀_classβ' (w : kernelIdeal Q.presentation.hom (op W))
    (z' : kernelIdeal (presY f g).hom (op W))
    (hz : z'.1 = ((Φβ g Q).hom.app (op W)).hom w.1) :
    (ιβ₀ g Q).val.app (op W) (classβ g Q (op W) w) = classY g (op W) z' :=
  (ιβ₀_classβ g Q (op W) w).trans (congrArg (classY g (op W)) (Subtype.ext hz.symm))

/-- The pair of local conormal classes `([z], [w]) ∈ N₀(W)`. -/
def cpair (z : kernelIdeal P.presentation.hom (op U)) (w : kernelIdeal Q.presentation.hom (op W))
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z.1) =
      ((Φβ g Q).hom.app (op W)).hom w.1) : (N₀ g P Q).val.obj (op W) :=
  SheafOfModules.pullbackMk (ψ₀ g P) (ιβ₀ g Q) (op W) (restrClassX g P U i z)
    (classβ g Q (op W) w)
    ((ψ₀_restrClassX g P U i z ⟨_, Stacks.Sites.Conormal.kernelIdeal_le_comap
        Q.presentation.hom (presY f g).hom (Φβ g Q).hom
        (Stacks.Sites.Conormal.hom_of_comp_eq (Φβ_comp_presY g Q)) (op W) w.2⟩ h.symm).trans
      (ιβ₀_classβ' g Q w _ rfl).symm)

/-- A local conormal class of the presentation of `𝒪_X` by `𝒪_{X'}`. -/
def classX (z : kernelIdeal P.presentation.hom (op U)) :
    (cX P).val.obj (op U) :=
  conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (FX P) X.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
    P.presentation (op U) z

/-- A local differential of the presentation of `𝒪_X` by `𝒪_{X'}`. -/
def diffX (z : (FX P).obj.obj (op U)) :
    (bX P).val.obj (op U) :=
  tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (FX P) X.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
    P.presentation (op U) z

theorem unitClassX_eq (z : kernelIdeal P.presentation.hom (op U)) :
    unitClassX g P U z =
      unitSec g (cX P) U
        (classX P U z) := rfl

theorem unitDiffX_eq (z : (FX P).obj.obj (op U)) :
    unitDiffX g P U z =
      unitSec g (bX P) U
        (diffX P U z) := rfl

theorem dX_classX (z : kernelIdeal P.presentation.hom (op U)) :
    (dX P).val.app (op U) (classX P U z) = diffX P U z.1 := by
  have h := Stacks.Sites.Conormal.conormalSequence_f_class.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (FX P) X.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) P.presentation (op U) z
  unfold dX classX diffX
  exact h

theorem dβ_classβ (W' : (Opens Y.carrier)ᵒᵖ) (w : kernelIdeal Q.presentation.hom W') :
    (dβ g Q).val.app W' (classβ g Q W' w) = diffβ g Q W' w.1 := by
  have h := Stacks.Sites.Conormal.conormalSequence_f_class.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Fβ g Q) Y.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) Q.presentation W' w
  unfold dβ classβ diffβ
  exact h

theorem dN_fst : dN g P Q ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ (modulePullback g).map (dX P) := by
  unfold dN
  exact pullback.lift_fst _ _ _

theorem dN_snd : dN g P Q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ dβ g Q := by
  unfold dN
  exact pullback.lift_snd _ _ _

theorem dN_cpair (z : kernelIdeal P.presentation.hom (op U))
    (w : kernelIdeal Q.presentation.hom (op W))
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z.1) =
      ((Φβ g Q).hom.app (op W)).hom w.1) :
    (dN g P Q).val.app (op W) (cpair g P Q U i z w h) = dpair g P Q U i z.1 w.1 h := by
  refine SheafOfModules.pullback_section_ext _ _ _ ?_ ?_
  · refine (comp_app_apply' _ _ _ _).symm.trans ?_
    refine (congrArg (fun t : N₀ g P Q ⟶ _ ↦ t.val.app (op W) (cpair g P Q U i z w h))
      (dN_fst g P Q)).trans ?_
    refine (comp_app_apply' _ _ _ _).trans ?_
    refine (congrArg (((modulePullback g).map (dX P)).val.app (op W))
      (SheafOfModules.pullback_fst_pullbackMk _ _ _ _ _ _)).trans ?_
    refine Eq.trans ?_ (SheafOfModules.pullback_fst_pullbackMk _ _ _ _ _ _).symm
    unfold restrClassX restrDiffX
    refine (PresheafOfModules.naturality_apply ((modulePullback g).map (dX P)).val i.op
      (unitClassX g P U z)).trans (congrArg _ ?_)
    rw [unitClassX_eq, unitDiffX_eq, map_unitSec, dX_classX]
  · refine (comp_app_apply' _ _ _ _).symm.trans ?_
    refine (congrArg (fun t : N₀ g P Q ⟶ _ ↦ t.val.app (op W) (cpair g P Q U i z w h))
      (dN_snd g P Q)).trans ?_
    refine (comp_app_apply' _ _ _ _).trans ?_
    refine (congrArg ((dβ g Q).val.app (op W))
      (SheafOfModules.pullback_snd_pullbackMk _ _ _ _ _ _)).trans ?_
    refine Eq.trans ?_ (SheafOfModules.pullback_snd_pullbackMk _ _ _ _ _ _).symm
    exact dβ_classβ g Q (op W) w

theorem δX_classX (z : kernelIdeal P.presentation.hom (op U)) :
    (δX P).val.app (op U) (classX P U z) =
      P.ideal.app (op U) ⟨(P.lift.hom.app (op U)).hom z.1, P.lift_mem_kernelIdeal (op U) z⟩ := by
  have h := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule.{u, u, u, u} P.presentation F
    P.idealRestriction (op U) z
  unfold δX classX
  exact h.trans (P.idealRestriction_app (op U) z)

theorem δβ_classβ (W' : (Opens Y.carrier)ᵒᵖ) (w : kernelIdeal Q.presentation.hom W') :
    (δβ g Q).val.app W' (classβ g Q W' w) =
      Q.ideal.app W' ⟨(Q.lift.hom.app W').hom w.1, Q.lift_mem_kernelIdeal W' w⟩ := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      Q.presentation.hom := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  have h := Stacks.Sites.Conormal.conormalDesc_toAssociatedModule.{u, u, u, u} Q.presentation G
    Q.idealRestriction W' w
  unfold δβ classβ
  exact h.trans (Q.idealRestriction_app W' w)

/-- `c(ρ_X(z))` for a relation `z` of `α_X`, restricted to `W`: the first half of `Δ`. -/
def cValue (z : kernelIdeal P.presentation.hom (op U)) : G.val.obj (op W) :=
  G.val.map i.op (c.val.app (op U) (P.ideal.app (op U)
      ⟨(P.lift.hom.app (op U)).hom z.1, P.lift_mem_kernelIdeal (op U) z⟩))

theorem Δ_cpair (z : kernelIdeal P.presentation.hom (op U))
    (w : kernelIdeal Q.presentation.hom (op W))
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z.1) =
      ((Φβ g Q).hom.app (op W)).hom w.1) :
    (Δ g P Q c).val.app (op W) (cpair g P Q U i z w h) =
      cValue g P c U i z - Q.ideal.app (op W)
        ⟨(Q.lift.hom.app (op W)).hom w.1, Q.lift_mem_kernelIdeal (op W) w⟩ := by
  unfold Δ
  refine (sub_app_apply' _ _ _ _).trans (congrArg₂ (· - ·) ?_ ?_)
  · refine (comp_app_apply' _ _ _ _).trans ?_
    refine (comp_app_apply' _ _ _ _).trans ?_
    refine (congrArg (fun x ↦ (cAdj g c).val.app (op W) (((modulePullback g).map (δX P)).val.app
      (op W) x)) (SheafOfModules.pullback_fst_pullbackMk _ _ _ _ _ _)).trans ?_
    unfold restrClassX
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, unitClassX_eq,
      map_unitSec]
    unfold cAdj
    rw [homEquiv_symm_unitSec, δX_classX]
    rfl
  · refine (comp_app_apply' _ _ _ _).trans ?_
    refine (congrArg ((δβ g Q).val.app (op W))
      (SheafOfModules.pullback_snd_pullbackMk _ _ _ _ _ _)).trans ?_
    exact δβ_classβ g Q (op W) w

theorem θ_dpair (θ : N₁ g P Q ⟶ G) (hθ : dN g P Q ≫ θ = Δ g P Q c)
    (z : kernelIdeal P.presentation.hom (op U))
    (w : kernelIdeal Q.presentation.hom (op W))
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z.1) =
      ((Φβ g Q).hom.app (op W)).hom w.1) :
    θ.val.app (op W) (dpair g P Q U i z.1 w.1 h) =
      cValue g P c U i z - Q.ideal.app (op W)
        ⟨(Q.lift.hom.app (op W)).hom w.1, Q.lift_mem_kernelIdeal (op W) w⟩ := by
  rw [← dN_cpair g P Q U i z w h, ← Δ_cpair g P Q c U i z w h, ← comp_app_apply', hθ]

theorem dpair_map {U' : Opens X.carrier} (k : U' ⟶ U) {W' : Opens Y.carrier}
    (i' : W' ⟶ (Opens.map g.hom.base).obj U') {z : (FX P).obj.obj (op U)}
    {w : (Fβ g Q).obj.obj (op W')}
    (h : ((FY f g).obj.map i'.op).hom (((ΦX g P).hom.app (op U')).hom
      (((FX P).obj.map k.op).hom z)) = ((Φβ g Q).hom.app (op W')).hom w) :
    dpair g P Q U' i' (((FX P).obj.map k.op).hom z) w h =
      dpair g P Q U (i' ≫ (Opens.map g.hom.base).map k) z w (match_comp g P Q U k i' h) := by
  unfold dpair
  exact pullbackMk_congr _ _ _ _ (restrDiffX_map g P U k i' z) rfl

theorem dpair_congr {z z' : (FX P).obj.obj (op U)} {w w' : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w)
    (h' : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z') =
      ((Φβ g Q).hom.app (op W)).hom w') (hz : z = z') (hw : w = w') :
    dpair g P Q U i z w h = dpair g P Q U i z' w' h' := by
  subst hz hw
  rfl

theorem cValue_eq_zero (z : kernelIdeal P.presentation.hom (op U))
    (hz : (P.lift.hom.app (op U)).hom z.1 = 0) : cValue g P c U i z = 0 := by
  unfold cValue
  rw [show (⟨(P.lift.hom.app (op U)).hom z.1, P.lift_mem_kernelIdeal (op U) z⟩ :
      kernelIdeal P.reduction.hom (op U)) = 0 from Subtype.ext hz, map_zero, map_zero]
  exact map_zero (G.val.map i.op).hom

theorem θ_dpair_eq_zero (θ : N₁ g P Q ⟶ G) (hθ : dN g P Q ≫ θ = Δ g P Q c)
    (z : kernelIdeal P.presentation.hom (op U))
    (w : kernelIdeal Q.presentation.hom (op W))
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z.1) =
      ((Φβ g Q).hom.app (op W)).hom w.1)
    (hz : (P.lift.hom.app (op U)).hom z.1 = 0) (hw : (Q.lift.hom.app (op W)).hom w.1 = 0) :
    θ.val.app (op W) (dpair g P Q U i z.1 w.1 h) = 0 := by
  rw [θ_dpair g P Q c U i θ hθ z w h, cValue_eq_zero g P c U i z hz,
    show (⟨(Q.lift.hom.app (op W)).hom w.1, Q.lift_mem_kernelIdeal (op W) w⟩ :
      kernelIdeal Q.reduction.hom (op W)) = 0 from Subtype.ext hw, map_zero, sub_zero]

end Pairs

/-! ### Values of pairs of polynomials -/

section PairValues

variable (U : Opens X.carrier) {W : Opens Y.carrier} (i : W ⟶ (Opens.map g.hom.base).obj U)

theorem presX_eq (z : (FX P).obj.obj (op U)) :
    (P.presentation.hom.app (op U)).hom z =
      (P.reduction.hom.app (op U)).hom ((P.lift.hom.app (op U)).hom z) :=
  (congrArg (fun t : FX P ⟶ X.sheaf ↦ (t.hom.app (op U)).hom z) P.lift_comp_reduction).symm

theorem presβ_eq (w : (Fβ g Q).obj.obj (op W)) :
    (Q.presentation.hom.app (op W)).hom w =
      (Q.reduction.hom.app (op W)).hom ((Q.lift.hom.app (op W)).hom w) :=
  (congrArg (fun t : Fβ g Q ⟶ Y.sheaf ↦ (t.hom.app (op W)).hom w) Q.lift_comp_reduction).symm

theorem presβ_of_match {z : (FX P).obj.obj (op U)} {w : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w) :
    (Q.presentation.hom.app (op W)).hom w = (Y.sheaf.obj.map i.op).hom
      ((g.hom.c.app (op U)).hom ((P.presentation.hom.app (op U)).hom z)) := by
  have h1 := congrArg (fun t : Fβ g Q ⟶ Y.sheaf ↦ (t.hom.app (op W)).hom w) (Φβ_comp_presY g Q)
  have h2 := congrArg (fun t : FX P ⟶ _ ↦ (t.hom.app (op U)).hom z) (ΦX_comp_presY g P)
  have h3 := NatTrans.naturality_apply (presY f g).hom i.op (((ΦX g P).hom.app (op U)).hom z)
  refine h1.symm.trans ((congrArg _ h.symm).trans (h3.trans (congrArg _ h2)))

theorem match_sub {z z' : (FX P).obj.obj (op U)} {w w' : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w)
    (h' : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z') =
      ((Φβ g Q).hom.app (op W)).hom w') :
    ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom (z - z')) =
      ((Φβ g Q).hom.app (op W)).hom (w - w') := by
  rw [map_sub, map_sub]
  exact (map_sub _ _ _).trans (congrArg₂ (· - ·) h h')

theorem match_add {z z' : (FX P).obj.obj (op U)} {w w' : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w)
    (h' : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z') =
      ((Φβ g Q).hom.app (op W)).hom w') :
    ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom (z + z')) =
      ((Φβ g Q).hom.app (op W)).hom (w + w') := by
  rw [map_add, map_add]
  exact (map_add _ _ _).trans (congrArg₂ (· + ·) h h')

theorem match_mul {z z' : (FX P).obj.obj (op U)} {w w' : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w)
    (h' : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z') =
      ((Φβ g Q).hom.app (op W)).hom w') :
    ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom (z * z')) =
      ((Φβ g Q).hom.app (op W)).hom (w * w') := by
  rw [map_mul, map_mul]
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) h h')

theorem dpair_mul {z₁ z₂ : (FX P).obj.obj (op U)} {w₁ w₂ : (Fβ g Q).obj.obj (op W)}
    (h₁ : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z₁) =
      ((Φβ g Q).hom.app (op W)).hom w₁)
    (h₂ : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z₂) =
      ((Φβ g Q).hom.app (op W)).hom w₂) :
    dpair g P Q U i (z₁ * z₂) (w₁ * w₂) (match_mul g P Q U i h₁ h₂) =
      yScalar ((Q.presentation.hom.app (op W)).hom w₁) • dpair g P Q U i z₂ w₂ h₂ +
        yScalar ((Q.presentation.hom.app (op W)).hom w₂) • dpair g P Q U i z₁ w₁ h₁ := by
  refine SheafOfModules.pullback_section_ext _ _ _ ?_ ?_
  · rw [map_add, map_smul, map_smul]
    unfold dpair
    rw [SheafOfModules.pullback_fst_pullbackMk, SheafOfModules.pullback_fst_pullbackMk,
      SheafOfModules.pullback_fst_pullbackMk, restrDiffX_mul, presβ_of_match g P Q U i h₁,
      presβ_of_match g P Q U i h₂]
  · rw [map_add, map_smul, map_smul]
    unfold dpair
    rw [SheafOfModules.pullback_snd_pullbackMk, SheafOfModules.pullback_snd_pullbackMk,
      SheafOfModules.pullback_snd_pullbackMk]
    exact diffβ_mul g Q (op W) w₁ w₂

/-- The coefficient `t ∈ f⁻¹𝒪_S(U)` in `f⁻¹𝒪_S[𝒪_{X'}](U)`. -/
abbrev coefX (t : (inverseImageBaseRing f).obj.obj (op U)) : (FX P).obj.obj (op U) :=
  ((freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) P.generators).hom.app (op U)).hom t

/-- The coefficient `t ∈ (g ∘ f)⁻¹𝒪_S(W)` in `(g ∘ f)⁻¹𝒪_S[𝒪_{Y'}](W)`. -/
abbrev coefβ {W' : (Opens Y.carrier)ᵒᵖ} (t : (inverseImageBaseRing (g ≫ f)).obj.obj W') :
    (Fβ g Q).obj.obj W' :=
  ((freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) Q.generators).hom.app W').hom t

theorem restrDiffX_coefX (t : (inverseImageBaseRing f).obj.obj (op U)) :
    restrDiffX g P U i (coefX P U t) = 0 := by
  have h := Stacks.Sites.Conormal.tensorDifferential_coefficient.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (FX P) X.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) P.presentation (op U) t
  unfold restrDiffX unitDiffX
  rw [h]
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem diffβ_coefβ (W' : (Opens Y.carrier)ᵒᵖ) (t : (inverseImageBaseRing (g ≫ f)).obj.obj W') :
    diffβ g Q W' (coefβ g Q t) = 0 :=
  Stacks.Sites.Conormal.tensorDifferential_coefficient.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) (Fβ g Q) Y.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) Q.presentation W' t

theorem dpair_eq_zero {z : (FX P).obj.obj (op U)} {w : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w)
    (hz : restrDiffX g P U i z = 0) (hw : diffβ g Q (op W) w = 0) :
    dpair g P Q U i z w h = 0 := by
  refine SheafOfModules.pullback_section_ext _ _ _ ?_ ?_
  · rw [map_zero]
    unfold dpair
    rw [SheafOfModules.pullback_fst_pullbackMk]
    exact hz
  · rw [map_zero]
    unfold dpair
    rw [SheafOfModules.pullback_snd_pullbackMk]
    exact hw

variable (θ : N₁ g P Q ⟶ G) (hθ : dN g P Q ≫ θ = Δ g P Q c)

/-- The value `α'(w) + θ(d z, d w)` of a pair of polynomials with the same image. -/
def pairValue (z : (FX P).obj.obj (op U)) (w : (Fβ g Q).obj.obj (op W))
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w) : Q.sheaf.obj.obj (op W) :=
  (Q.lift.hom.app (op W)).hom w + Q.incl (op W) (θ.val.app (op W) (dpair g P Q U i z w h))

include hθ in
/-- **The value of a pair only depends on the image of the first polynomial in `𝒪_{X'}`.** -/
theorem pairValue_eq {z z' : (FX P).obj.obj (op U)} {w w' : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w)
    (h' : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z') =
      ((Φβ g Q).hom.app (op W)).hom w')
    (hl : (P.lift.hom.app (op U)).hom z = (P.lift.hom.app (op U)).hom z') :
    pairValue g P Q U i θ z w h = pairValue g P Q U i θ z' w' h' := by
  have hmX : z - z' ∈ kernelIdeal P.presentation.hom (op U) := by
    change (P.presentation.hom.app (op U)).hom _ = 0
    rw [presX_eq, map_sub, hl, sub_self, map_zero]
  have hd := match_sub g P Q U i h h'
  have hmβ : w - w' ∈ kernelIdeal Q.presentation.hom (op W) := by
    change (Q.presentation.hom.app (op W)).hom _ = 0
    rw [presβ_of_match g P Q U i hd,
      show (P.presentation.hom.app (op U)).hom (z - z') = 0 from hmX]
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have hθ0 := θ_dpair g P Q c U i θ hθ ⟨_, hmX⟩ ⟨_, hmβ⟩ hd
  rw [cValue_eq_zero g P c U i _ (show (P.lift.hom.app (op U)).hom (z - z') = 0 by
    rw [map_sub, hl, sub_self]), zero_sub] at hθ0
  have hsplit : dpair g P Q U i z w h = dpair g P Q U i z' w' h' + dpair g P Q U i _ _ hd := by
    rw [← dpair_add g P Q U i _ _ _ _ h' hd]
    · exact dpair_congr g P Q U i _ _ (add_sub_cancel _ _).symm (add_sub_cancel _ _).symm
    · rw [add_sub_cancel, add_sub_cancel]
      exact h
  unfold pairValue
  rw [hsplit, map_add, hθ0, Q.incl_add, Q.incl_neg]
  have := Q.incl_ideal (op W) ⟨_, Q.lift_mem_kernelIdeal (op W) ⟨_, hmβ⟩⟩
  simp only at this
  rw [this, map_sub]
  abel

theorem pairValue_add {z z' : (FX P).obj.obj (op U)} {w w' : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w)
    (h' : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z') =
      ((Φβ g Q).hom.app (op W)).hom w') :
    pairValue g P Q U i θ (z + z') (w + w') (match_add g P Q U i h h') =
      pairValue g P Q U i θ z w h + pairValue g P Q U i θ z' w' h' := by
  unfold pairValue
  rw [dpair_add g P Q U i z z' w w' h h', map_add, map_add, Q.incl_add]
  abel

theorem incl_yScalar_smul (w : (Fβ g Q).obj.obj (op W)) (t : G.val.obj (op W)) :
    Q.incl (op W) (yScalar ((Q.presentation.hom.app (op W)).hom w) • t) =
      (Q.lift.hom.app (op W)).hom w * Q.incl (op W) t := by
  rw [← Q.incl_smul]
  exact congrArg (fun r ↦ Q.incl (op W) (yScalar r • t)) (presβ_eq g Q w)

theorem pairValue_mul {z₁ z₂ : (FX P).obj.obj (op U)} {w₁ w₂ : (Fβ g Q).obj.obj (op W)}
    (h₁ : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z₁) =
      ((Φβ g Q).hom.app (op W)).hom w₁)
    (h₂ : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z₂) =
      ((Φβ g Q).hom.app (op W)).hom w₂) :
    pairValue g P Q U i θ (z₁ * z₂) (w₁ * w₂) (match_mul g P Q U i h₁ h₂) =
      pairValue g P Q U i θ z₁ w₁ h₁ * pairValue g P Q U i θ z₂ w₂ h₂ := by
  unfold pairValue
  rw [dpair_mul g P Q U i h₁ h₂, map_add, map_smul, map_smul, Q.incl_add, incl_yScalar_smul,
    incl_yScalar_smul, map_mul]
  linear_combination -(Q.incl_mul_incl (op W) (θ.val.app (op W) (dpair g P Q U i z₁ w₁ h₁))
    (θ.val.app (op W) (dpair g P Q U i z₂ w₂ h₂)))

theorem pairValue_of_dpair_eq_zero {z : (FX P).obj.obj (op U)} {w : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w) (h0 : dpair g P Q U i z w h = 0) :
    pairValue g P Q U i θ z w h = (Q.lift.hom.app (op W)).hom w := by
  unfold pairValue
  rw [h0, map_zero, Q.incl_zero, add_zero]

theorem pairValue_map {U' : Opens X.carrier} (k : U' ⟶ U) {W' : Opens Y.carrier}
    (i' : W' ⟶ (Opens.map g.hom.base).obj U') {z : (FX P).obj.obj (op U)}
    {w : (Fβ g Q).obj.obj (op W')}
    (h : ((FY f g).obj.map i'.op).hom (((ΦX g P).hom.app (op U')).hom
      (((FX P).obj.map k.op).hom z)) = ((Φβ g Q).hom.app (op W')).hom w) :
    pairValue g P Q U' i' θ (((FX P).obj.map k.op).hom z) w h =
      pairValue g P Q U (i' ≫ (Opens.map g.hom.base).map k) θ z w (match_comp g P Q U k i' h) := by
  unfold pairValue
  rw [dpair_map g P Q U k i' h]

end PairValues

/-! ### The local values -/

section Values

variable (θ : N₁ g P Q ⟶ G) (hθ : dN g P Q ≫ θ = Δ g P Q c)
  {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) {W : Opens Y.carrier}
  (i : W ⟶ (Opens.map g.hom.base).obj U)

/-- `e` is a lift over `W` of `g^♯(s mod ℱ)`. -/
abbrev IsLift (e : Q.sheaf.obj.obj (op W)) : Prop :=
  (Q.reduction.hom.app (op W)).hom e = (Y.sheaf.obj.map i.op).hom (redX g P U s)

theorem match_var {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) :
    ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom (varX P U s)) =
      ((Φβ g Q).hom.app (op W)).hom (varβ g Q W e) := by
  rw [ΦX_varX, map_varY, Φβ_varβ, he]

/-- The pair `(d[s], d[e]) ∈ N₁(W)` of a lift `e`. -/
def npair {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) : (N₁ g P Q).val.obj (op W) :=
  dpair g P Q U i (varX P U s) (varβ g Q W e) (match_var g P Q s i he)

/-- The local value `e + θ(d[s], d[e])`. -/
def value {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) : Q.sheaf.obj.obj (op W) :=
  e + Q.incl (op W) (θ.val.app (op W) (npair g P Q s i he))

/-- The local value is the value of the pair of variables `([s], [e])`. -/
private theorem value_eq_pairValue_aux {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) :
    value g P Q θ s i he =
      pairValue g P Q U i θ (varX P U s) (varβ g Q W e) (match_var g P Q s i he) := by
  unfold value pairValue npair
  rw [lift_varβ]

include hθ in
/-- **The local value does not depend on the lift.** -/
theorem value_eq {e e' : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e)
    (he' : IsLift g P Q s i e') : value g P Q θ s i he = value g P Q θ s i he' := by
  rw [value_eq_pairValue_aux g P Q θ s i he, value_eq_pairValue_aux g P Q θ s i he']
  exact pairValue_eq g P Q c U i θ hθ _ _ rfl

theorem isLift_map {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) {W' : Opens Y.carrier}
    (j : W' ⟶ W) : IsLift g P Q s (j ≫ i) ((Q.sheaf.obj.map j.op).hom e) := by
  unfold IsLift at he ⊢
  rw [NatTrans.naturality_apply Q.reduction.hom j.op e, he, op_comp, Functor.map_comp]
  rfl

theorem npair_map {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) {W' : Opens Y.carrier}
    (j : W' ⟶ W) : (N₁ g P Q).val.map j.op (npair g P Q s i he) =
      npair g P Q s (j ≫ i) (isLift_map g P Q s i he j) := by
  unfold npair dpair
  rw [pullbackMk_map _ _ j.op _ _ _ (by
    rw [PresheafOfModules.naturality_apply (ψ₁ g P).val j.op,
      PresheafOfModules.naturality_apply (ιβ₁ g Q).val j.op]
    exact congrArg _ ((ψ₁_restrDiffX g P U i _).trans ((congrArg (diffY g (op W))
      (match_var g P Q s i he)).trans (ιβ₁_diffβ g Q (op W) _).symm)))]
  refine pullbackMk_congr _ _ _ _ ?_ ?_
  · unfold restrDiffX
    exact (((modulePullback g).obj (bX P)).val.map_comp_apply i.op j.op _).symm
  · rw [← diffβ_map, map_varβ]

/-- **The local values restrict.** -/
theorem map_value {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) {W' : Opens Y.carrier}
    (j : W' ⟶ W) : (Q.sheaf.obj.map j.op).hom (value g P Q θ s i he) =
      value g P Q θ s (j ≫ i) (isLift_map g P Q s i he j) := by
  unfold value
  rw [map_add, Q.incl_map]
  exact congrArg (fun x ↦ (Q.sheaf.obj.map j.op).hom e + Q.incl (op W') x)
    ((PresheafOfModules.naturality_apply θ.val j.op (npair g P Q s i he)).symm.trans
      (congrArg (θ.val.app (op W')) (npair_map g P Q s i he j)))

include hθ in
theorem value_eq' {i i' : W ⟶ (Opens.map g.hom.base).obj U} {e e' : Q.sheaf.obj.obj (op W)}
    (he : IsLift g P Q s i e) (he' : IsLift g P Q s i' e') :
    value g P Q θ s i he = value g P Q θ s i' he' := by
  obtain rfl : i = i' := Subsingleton.elim _ _
  exact value_eq g P Q c θ hθ s i he he'

theorem value_eq_pairValue {e : Q.sheaf.obj.obj (op W)} (he : IsLift g P Q s i e) :
    value g P Q θ s i he =
      pairValue g P Q U i θ (varX P U s) (varβ g Q W e) (match_var g P Q s i he) :=
  value_eq_pairValue_aux g P Q θ s i he

theorem isLift_of_match {z : (FX P).obj.obj (op U)} (hz : (P.lift.hom.app (op U)).hom z = s)
    {w : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w) :
    IsLift g P Q s i ((Q.lift.hom.app (op W)).hom w) := by
  refine (presβ_eq g Q w).symm.trans ((presβ_of_match g P Q U i h).trans ?_)
  rw [presX_eq, hz]

end Values

/-! ### Gluing the local values -/

section Glue

variable (θ : N₁ g P Q ⟶ G) (hθ : dN g P Q ≫ θ = Δ g P Q c)

/-- The sheaf of sets underlying `𝒪_{Y'}`. -/
abbrev typeSheafQ : Sheaf (Opens.grothendieckTopology Y.carrier) (Type u) :=
  (sheafCompose (Opens.grothendieckTopology Y.carrier) (forget CommRingCat.{u})).obj Q.sheaf

theorem isSheaf_typeSheafQ : Presieve.IsSheaf (Opens.grothendieckTopology Y.carrier)
    (typeSheafQ g Q).obj :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (typeSheafQ g Q).property

theorem imageSieve_mem_lift {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) :
    Presheaf.imageSieve Q.reduction.hom (redX g P U s) ∈
      Opens.grothendieckTopology Y.carrier ((Opens.map g.hom.base).obj U) := by
  have := Q.reduction_surjective
  exact Presheaf.imageSieve_mem _ Q.reduction.hom (redX g P U s)

/-- The family of local values on the sieve of opens over which a lift exists. -/
def valueFamily {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) :
    Presieve.FamilyOfElements (typeSheafQ g Q).obj
      (Presheaf.imageSieve Q.reduction.hom (redX g P U s)).arrows :=
  fun _ i hi ↦ value g P Q θ s i (e := hi.choose) hi.choose_spec

include hθ in
theorem valueFamily_compatible {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) :
    (valueFamily g P Q θ s).Compatible := by
  intro W₁ W₂ W' j₁ j₂ i₁ i₂ h₁ h₂ _
  change (Q.sheaf.obj.map j₁.op).hom (value g P Q θ s i₁ h₁.choose_spec) =
    (Q.sheaf.obj.map j₂.op).hom (value g P Q θ s i₂ h₂.choose_spec)
  rw [map_value g P Q θ, map_value g P Q θ]
  exact value_eq' g P Q c θ hθ s _ _

/-- **The glued value** of a section `s` of `𝒪_{X'}` over `U`, a section of `𝒪_{Y'}` over
`g⁻¹U`. -/
def glued {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) :
    Q.sheaf.obj.obj (op ((Opens.map g.hom.base).obj U)) :=
  (isSheaf_typeSheafQ g Q _ (imageSieve_mem_lift g P Q s)).amalgamate (valueFamily g P Q θ s)
    (valueFamily_compatible g P Q c θ hθ s)

include hθ in
/-- **The glued value restricts to the local values.** -/
theorem map_glued {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) {W : Opens Y.carrier}
    (i : W ⟶ (Opens.map g.hom.base).obj U) {e : Q.sheaf.obj.obj (op W)}
    (he : IsLift g P Q s i e) :
    (Q.sheaf.obj.map i.op).hom (glued g P Q c θ hθ s) = value g P Q θ s i he := by
  have hi : Presheaf.imageSieve Q.reduction.hom (redX g P U s) i := ⟨e, he⟩
  refine ((isSheaf_typeSheafQ g Q _ (imageSieve_mem_lift g P Q s)).valid_glue
    (valueFamily_compatible g P Q c θ hθ s) i hi).trans ?_
  exact value_eq' g P Q c θ hθ s _ _

include hθ in
/-- **The glued value restricts to the value of any pair of polynomials over it.** -/
theorem map_glued_pair {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) {W : Opens Y.carrier}
    (i : W ⟶ (Opens.map g.hom.base).obj U) {z : (FX P).obj.obj (op U)}
    (hz : (P.lift.hom.app (op U)).hom z = s) {w : (Fβ g Q).obj.obj (op W)}
    (h : ((FY f g).obj.map i.op).hom (((ΦX g P).hom.app (op U)).hom z) =
      ((Φβ g Q).hom.app (op W)).hom w) :
    (Q.sheaf.obj.map i.op).hom (glued g P Q c θ hθ s) = pairValue g P Q U i θ z w h := by
  rw [map_glued g P Q c θ hθ s i (isLift_of_match g P Q s i hz h), value_eq_pairValue]
  exact pairValue_eq g P Q c U i θ hθ _ _ ((lift_varX P U s).trans hz.symm)

/-- The sieve of opens over which both of two sections have lifts. -/
abbrev liftSieve₂ {U : Opens X.carrier} (s₁ s₂ : P.sheaf.obj.obj (op U)) :
    Sieve ((Opens.map g.hom.base).obj U) :=
  Presheaf.imageSieve Q.reduction.hom (redX g P U s₁) ⊓
    Presheaf.imageSieve Q.reduction.hom (redX g P U s₂)

theorem liftSieve₂_mem {U : Opens X.carrier} (s₁ s₂ : P.sheaf.obj.obj (op U)) :
    liftSieve₂ g P Q s₁ s₂ ∈
      Opens.grothendieckTopology Y.carrier ((Opens.map g.hom.base).obj U) :=
  (Opens.grothendieckTopology Y.carrier).intersection_covering (imageSieve_mem_lift g P Q s₁)
    (imageSieve_mem_lift g P Q s₂)

include hθ in
theorem glued_add {U : Opens X.carrier} (s₁ s₂ : P.sheaf.obj.obj (op U)) :
    glued g P Q c θ hθ (s₁ + s₂) = glued g P Q c θ hθ s₁ + glued g P Q c θ hθ s₂ := by
  refine sheaf_eq_of_sieve Q.sheaf _ (liftSieve₂_mem g P Q s₁ s₂) _ _ ?_
  rintro W i ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩
  have m₁ := match_var g P Q s₁ i (e := e₁) he₁
  have m₂ := match_var g P Q s₂ i (e := e₂) he₂
  rw [map_add, map_glued_pair g P Q c θ hθ s₁ i (lift_varX P U s₁) m₁,
    map_glued_pair g P Q c θ hθ s₂ i (lift_varX P U s₂) m₂,
    map_glued_pair g P Q c θ hθ (s₁ + s₂) i
      (by rw [map_add, lift_varX, lift_varX]) (match_add g P Q U i m₁ m₂)]
  exact pairValue_add g P Q U i θ m₁ m₂

include hθ in
theorem glued_mul {U : Opens X.carrier} (s₁ s₂ : P.sheaf.obj.obj (op U)) :
    glued g P Q c θ hθ (s₁ * s₂) = glued g P Q c θ hθ s₁ * glued g P Q c θ hθ s₂ := by
  refine sheaf_eq_of_sieve Q.sheaf _ (liftSieve₂_mem g P Q s₁ s₂) _ _ ?_
  rintro W i ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩
  have m₁ := match_var g P Q s₁ i (e := e₁) he₁
  have m₂ := match_var g P Q s₂ i (e := e₂) he₂
  rw [map_mul, map_glued_pair g P Q c θ hθ s₁ i (lift_varX P U s₁) m₁,
    map_glued_pair g P Q c θ hθ s₂ i (lift_varX P U s₂) m₂,
    map_glued_pair g P Q c θ hθ (s₁ * s₂) i
      (by rw [map_mul, lift_varX, lift_varX]) (match_mul g P Q U i m₁ m₂)]
  exact pairValue_mul g P Q U i θ m₁ m₂

include hθ in
/-- Over all of `g⁻¹U`, the glued value is the value of any pair of polynomials. -/
theorem glued_eq_pair {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U))
    {z : (FX P).obj.obj (op U)} (hz : (P.lift.hom.app (op U)).hom z = s)
    {w : (Fβ g Q).obj.obj (op ((Opens.map g.hom.base).obj U))}
    (h : ((FY f g).obj.map (𝟙 ((Opens.map g.hom.base).obj U)).op).hom
      (((ΦX g P).hom.app (op U)).hom z) = ((Φβ g Q).hom.app (op _)).hom w) :
    glued g P Q c θ hθ s = pairValue g P Q U (𝟙 _) θ z w h :=
  (map_id_apply' Q.sheaf _ _).symm.trans (map_glued_pair g P Q c θ hθ s (𝟙 _) hz h)

include hθ in
theorem glued_one (U : Opens X.carrier) : glued g P Q c θ hθ (1 : P.sheaf.obj.obj (op U)) = 1 := by
  have h : ((FY f g).obj.map (𝟙 ((Opens.map g.hom.base).obj U)).op).hom
      (((ΦX g P).hom.app (op U)).hom 1) = ((Φβ g Q).hom.app (op _)).hom 1 :=
    (congrArg _ (map_one _)).trans ((map_one _).trans (map_one _).symm)
  rw [glued_eq_pair g P Q c θ hθ 1 (map_one _) h, pairValue_of_dpair_eq_zero g P Q U _ θ h
    (dpair_eq_zero g P Q U _ h ((congrArg (restrDiffX g P U _) (map_one _).symm).trans
      (restrDiffX_coefX g P U _ 1)) ((congrArg (diffβ g Q _) (map_one _).symm).trans
        (diffβ_coefβ g Q _ 1)))]
  exact map_one _

include hθ in
/-- **The glued values extend `c` on the ideal.** -/
theorem glued_incl (U : Opens X.carrier) (y : F.val.obj (op U)) :
    glued g P Q c θ hθ (P.incl (op U) y) =
      Q.incl (op ((Opens.map g.hom.base).obj U)) (c.val.app (op U) y) := by
  have he : IsLift g P Q (P.incl (op U) y) (𝟙 _) 0 := by
    refine (map_zero _).trans ?_
    exact ((congrArg _ ((congrArg _ (P.reduction_incl (op U) y)).trans (map_zero _))).trans
      (map_zero _)).symm
  rw [(map_id_apply' Q.sheaf _ _).symm.trans (map_glued g P Q c θ hθ _ (𝟙 _) he)]
  unfold value npair
  have hz : varX P U (P.incl (op U) y) ∈ kernelIdeal P.presentation.hom (op U) := by
    change (P.presentation.hom.app (op U)).hom _ = 0
    rw [pres_varX, P.reduction_incl]
  have hw : varβ g Q _ 0 ∈ kernelIdeal Q.presentation.hom (op ((Opens.map g.hom.base).obj U)) := by
    change (Q.presentation.hom.app _).hom _ = 0
    rw [pres_varβ, map_zero]
  rw [θ_dpair g P Q c U (𝟙 _) θ hθ ⟨_, hz⟩ ⟨_, hw⟩]
  unfold cValue
  rw [show (⟨(P.lift.hom.app (op U)).hom (varX P U (P.incl (op U) y)),
      P.lift_mem_kernelIdeal (op U) ⟨_, hz⟩⟩ : kernelIdeal P.reduction.hom (op U)) =
      ⟨P.incl (op U) y, P.incl_mem (op U) y⟩ from Subtype.ext (lift_varX P U _), P.ideal_incl,
    show (⟨(Q.lift.hom.app _).hom (varβ g Q _ 0), Q.lift_mem_kernelIdeal _ ⟨_, hw⟩⟩ :
      kernelIdeal Q.reduction.hom (op ((Opens.map g.hom.base).obj U))) = 0 from
      Subtype.ext (lift_varβ g Q _ 0), map_zero]
  refine (zero_add _).trans (congrArg (Q.incl _) ((sub_zero _).trans ?_))
  rw [op_id, PresheafOfModules.map_id]
  rfl

include hθ in
/-- **The glued values are compatible with the structure maps over `S`.** -/
theorem glued_base (U : Opens X.carrier) (t : (inverseImageBaseRing f).obj.obj (op U)) :
    glued g P Q c θ hθ ((P.base.hom.app (op U)).hom t) =
      (Q.base.hom.app (op ((Opens.map g.hom.base).obj U))).hom
        (((baseRingPushMap g f).hom.app (op U)).hom t) := by
  have hz : (P.lift.hom.app (op U)).hom (coefX P U t) = (P.base.hom.app (op U)).hom t :=
    congrArg (fun φ : inverseImageBaseRing f ⟶ P.sheaf ↦ (φ.hom.app (op U)).hom t)
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf P.base)
  have hl : (Q.lift.hom.app _).hom (coefβ g Q (((baseRingPushMap g f).hom.app (op U)).hom t)) =
      (Q.base.hom.app (op ((Opens.map g.hom.base).obj U))).hom
        (((baseRingPushMap g f).hom.app (op U)).hom t) :=
    congrArg (fun φ : inverseImageBaseRing (g ≫ f) ⟶ Q.sheaf ↦ (φ.hom.app _).hom
        (((baseRingPushMap g f).hom.app (op U)).hom t))
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap
        (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.sheaf Q.base)
  have h1 := congrArg (fun φ : inverseImageBaseRing f ⟶ _ ↦ (φ.hom.app (op U)).hom t)
    (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap g.hom.base
      (inverseImageBaseRing f) P.generators (inverseImageBaseRing (g ≫ f))
      (Y.sheaf.obj ⋙ forget CommRingCat) (baseRingPushMap g f) (εX g P))
  have h2 := congrArg (fun φ : inverseImageBaseRing (g ≫ f) ⟶ FY f g ↦ (φ.hom.app _).hom
      (((baseRingPushMap g f).hom.app (op U)).hom t))
    (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap
      (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.generators
      (Y.sheaf.obj ⋙ forget CommRingCat) Q.generatorsMap)
  have h : ((FY f g).obj.map (𝟙 ((Opens.map g.hom.base).obj U)).op).hom
      (((ΦX g P).hom.app (op U)).hom (coefX P U t)) =
        ((Φβ g Q).hom.app (op _)).hom (coefβ g Q (((baseRingPushMap g f).hom.app (op U)).hom t)) :=
    (map_id_apply' (FY f g) _ _).trans (h1.trans h2.symm)
  rw [glued_eq_pair g P Q c θ hθ _ hz h, pairValue_of_dpair_eq_zero g P Q U _ θ h
    (dpair_eq_zero g P Q U _ h (restrDiffX_coefX g P U _ t) (diffβ_coefβ g Q _ _))]
  exact hl

include hθ in
/-- **The glued values are natural in `U`.** -/
theorem glued_map {U U' : Opens X.carrier} (k : U' ⟶ U) (s : P.sheaf.obj.obj (op U)) :
    glued g P Q c θ hθ ((P.sheaf.obj.map k.op).hom s) =
      (Q.sheaf.obj.map ((Opens.map g.hom.base).map k).op).hom (glued g P Q c θ hθ s) := by
  refine sheaf_eq_of_sieve Q.sheaf _ (imageSieve_mem_lift g P Q ((P.sheaf.obj.map k.op).hom s))
    _ _ ?_
  rintro W i ⟨e, he⟩
  have m := match_var g P Q _ i (e := e) he
  rw [← map_varX] at m
  have hz : (P.lift.hom.app (op U')).hom (((FX P).obj.map k.op).hom (varX P U s)) =
      (P.sheaf.obj.map k.op).hom s := by
    rw [NatTrans.naturality_apply P.lift.hom k.op, lift_varX]
  rw [map_glued_pair g P Q c θ hθ _ i hz m, pairValue_map g P Q U θ k i m, map_comp_apply',
    map_glued_pair g P Q c θ hθ s _ (lift_varX P U s) (match_comp g P Q U k i m)]

include hθ in
/-- **The glued values lie over `g^♯`.** -/
theorem glued_reduction {U : Opens X.carrier} (s : P.sheaf.obj.obj (op U)) :
    (Q.reduction.hom.app (op ((Opens.map g.hom.base).obj U))).hom (glued g P Q c θ hθ s) =
      redX g P U s := by
  refine sheaf_eq_of_sieve Y.sheaf _ (imageSieve_mem_lift g P Q s) _ _ ?_
  rintro W i ⟨e, he⟩
  rw [← NatTrans.naturality_apply Q.reduction.hom i.op, map_glued g P Q c θ hθ s i he]
  unfold value
  rw [map_add, Q.reduction_incl, add_zero]
  exact he

end Glue

/-! ### The compatible morphism -/

section Morphism

variable (θ : N₁ g P Q ⟶ G) (hθ : dN g P Q ≫ θ = Δ g P Q c)

/-- The glued values as a ring homomorphism `𝒪_{X'}(U) ⟶ 𝒪_{Y'}(g⁻¹U)`. -/
def gluedHom (U : Opens X.carrier) :
    P.sheaf.obj.obj (op U) →+* Q.sheaf.obj.obj (op ((Opens.map g.hom.base).obj U)) :=
  RingHom.mk' ⟨⟨glued g P Q c θ hθ, glued_one g P Q c θ hθ U⟩, glued_mul g P Q c θ hθ⟩
    (glued_add g P Q c θ hθ)

/-- **The comorphism `𝒪_{X'} ⟶ g_*𝒪_{Y'}`** glued from the local values `e' + θ(d[s], d[e'])`. -/
def gluedSheafHom : P.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Q.sheaf :=
  ObjectProperty.homMk
    { app := fun U ↦ CommRingCat.ofHom (gluedHom g P Q c θ hθ U.unop)
      naturality := fun {_V _U} k ↦ CommRingCat.hom_ext (RingHom.ext fun s ↦
        glued_map g P Q c θ hθ k.unop s) }

theorem gluedSheafHom_app (U : Opens X.carrier) (s : P.sheaf.obj.obj (op U)) :
    ((gluedSheafHom g P Q c θ hθ).hom.app (op U)).hom s = glued g P Q c θ hθ s :=
  rfl

theorem gluedSheafHom_reduction : gluedSheafHom g P Q c θ hθ ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.reduction =
    P.reduction ≫ (ObjectProperty.homMk g.hom.c : X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Y.sheaf) :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext fun s ↦
    glued_reduction g P Q c θ hθ (U := U.unop) s)))

theorem base_comp_gluedSheafHom : P.base ≫ gluedSheafHom g P Q c θ hθ =
    baseRingPushMap g f ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.base :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext fun t ↦
    glued_base g P Q c θ hθ U.unop t)))

theorem gluedSheafHom_base_comm :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _ P.base ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (gluedSheafHom g P Q c θ hθ) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (g ≫ f).hom.base).homEquiv _ _
        Q.base := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv_naturality_right _ _).symm.trans ?_
  refine (congrArg _ (base_comp_gluedSheafHom g P Q c θ hθ)).trans ?_
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ _) (homEquiv_baseRingPushMap g f)).trans ?_
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (g ≫ f).hom.base).homEquiv_unit _ _ _).symm

/-- **Stacks 08U8, Step 3 of the proof**: a factorization `Δ = θ ∘ d_N` of the difference
homomorphism `N₀ ⟶ 𝒢` through the differential `d_N : N₀ ⟶ N₁` gives an `S`-morphism `Y' ⟶ X'`
compatible with `g` and `c`, with comorphism `s ↦ e' + θ(d[s], d[e'])` on local lifts `e'` of
`g^♯(s mod ℱ)`. -/
def compatibleMorphismOfFactorization (θ : N₁ g P Q ⟶ G) (hθ : dN g P Q ≫ θ = Δ g P Q c) :
    CompatibleMorphism P Q c where
  hom := gluedSheafHom g P Q c θ hθ
  reduction_comm := gluedSheafHom_reduction g P Q c θ hθ
  base_comm := gluedSheafHom_base_comm g P Q c θ hθ
  ideal_comm U s := glued_incl g P Q c θ hθ U s

end Morphism

end AlgebraicGeometry.RingedSpaceThickening.LiftGluing

end
