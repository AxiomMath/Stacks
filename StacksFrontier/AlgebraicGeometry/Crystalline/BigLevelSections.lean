module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.ThickeningNilpotence
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleDirectImageInclusion

/-!
# Global sections over `CRIS(X/S)` are the limit of global sections over the levels

Let `X/S` be a global crystalline situation with affine base, `S_e ⊂ S` its finite divided power
levels and, for a sheaf `N` of `𝒪_{X/S}`-modules on `CRIS(X/S)`, `N_e` its restriction to
`CRIS(X/S_e)`.  This file proves the underived half of [Stacks, Tag 07MV] at module coefficients
on the big crystalline site:

`Γ(CRIS(X/S), N) = lim_e Γ(CRIS(X/S_e), N_e)`,

because every object of `CRIS(X/S)` is Zariski locally an object of some `CRIS(X/S_e)`: on an
affine open of its ambient scheme some power of `p` vanishes
(`...Thickening.exists_isAffineOpen_mem_and_pow_eq_zero`), and an object on whose ambient global
sections `p^e` vanishes lies in the image of `CRIS(X/S_e)` (`...levelLift`).

## Main definitions

* `Crystalline.GlobalCrystallineSituation.levelSectionsFunctor` — `N ↦ Γ(CRIS(X/S_e), N_e)`, as
  an `A`-module.
* `Crystalline.GlobalCrystallineSituation.levelSectionsTrans` — `Γ(CRIS(X/S), N) ⟶
  Γ(CRIS(X/S_e), N_e)`.
* `Crystalline.GlobalCrystallineSituation.levelSectionsTransition` — the transition
  `Γ(CRIS(X/S_e), N_e) ⟶ Γ(CRIS(X/S_m), N_m)`, `m ≤ e`.
* `Crystalline.GlobalCrystallineSituation.levelSectionsTower` and
  `Crystalline.GlobalCrystallineSituation.levelSectionsCone` — the tower `n ↦ Γ(N_{e(n)})` and
  the cone over it with vertex `Γ(CRIS(X/S), N)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.coversTop_levelChangeBase` — the images of the
  `CRIS(X/S_e)` cover the final object of the topos of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.isLimitLevelSectionsCone` — **`Γ(CRIS(X/S), N)` is the
  limit of the `Γ(CRIS(X/S_e), N_e)`.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

open DividedPowerScheme SmallSite

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme]

/-! ### The global sections at the levels -/

/-- **`N ↦ Γ(CRIS(X/S_e), N_e)`**, as a module over `A = Γ(S, 𝒪_S)` through `A ⟶ A/p^eA`. -/
abbrev levelSectionsFunctor {e : ℕ} (he : S.IsLevel e) :
    BigModuleSheaf S ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  S.levelPullback he ⋙ bigBaseModuleGlobalSections (S.levelSituation he) ⋙
    ModuleCat.restrictScalars (baseChangeRingHom (S.levelProj he))

/-- **The restriction `Γ(CRIS(X/S), N) ⟶ Γ(CRIS(X/S_e), N_e)`**: a global section read at the
images of the objects of `CRIS(X/S_e)`. -/
abbrev levelSectionsTrans {e : ℕ} (he : S.IsLevel e) :
    bigBaseModuleGlobalSections S ⟶ S.levelSectionsFunctor he :=
  changeBaseBigBaseGlobalSectionsTrans (S.levelProj he) (𝟙 S.X) (S.levelProj_condition he)

/-- The ring map `A ⟶ A/p^mA` factors through `A ⟶ A/p^eA`, for `m ≤ e`. -/
theorem baseChangeRingHom_levelProj_eq {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e)
    (hme : m ≤ e) :
    baseChangeRingHom (S.levelProj hm) =
      (baseChangeRingHom (S.levelTransition hm he hme)).comp
        (baseChangeRingHom (S.levelProj he)) := by
  rw [← S.levelTransition_comp_levelProj hm he hme]
  rfl

/-- Restriction of scalars along `A ⟶ A/p^eA ⟶ A/p^mA` is restriction of scalars along
`A ⟶ A/p^mA`. -/
abbrev levelRestrictScalarsComp {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom (S.levelTransition hm he hme)) ⋙
        ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom (S.levelProj he)) ⟶
      ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom (S.levelProj hm)) :=
  (ModuleCat.restrictScalarsComp' _ _ _ (S.baseChangeRingHom_levelProj_eq hm he hme)).inv

/-- **The transition `Γ(CRIS(X/S_e), N_e) ⟶ Γ(CRIS(X/S_m), N_m)`**, `m ≤ e`: the comparison of
global sections along `S_m ⟶ S_e` at `N_e`, followed by the identification of the restriction of
`N_e` to `CRIS(X/S_m)` with `N_m`. -/
def levelSectionsTransition {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    S.levelSectionsFunctor he ⟶ S.levelSectionsFunctor hm :=
  Functor.whiskerLeft (S.levelPullback he)
      (Functor.whiskerRight (changeBaseBigBaseGlobalSectionsTrans (S.levelTransition hm he hme)
        (𝟙 S.X) (S.levelTransition_condition hm he hme))
        (ModuleCat.restrictScalars (baseChangeRingHom (S.levelProj he)))) ≫
    Functor.whiskerRight (S.levelPullbackCompIso hm he hme).hom
      (bigBaseModuleGlobalSections (S.levelSituation hm) ⋙
        ModuleCat.restrictScalars (baseChangeRingHom (S.levelTransition hm he hme)) ⋙
          ModuleCat.restrictScalars (baseChangeRingHom (S.levelProj he))) ≫
    Functor.whiskerLeft (S.levelPullback hm ⋙ bigBaseModuleGlobalSections (S.levelSituation hm))
      (S.levelRestrictScalarsComp hm he hme)

/-- The comparison of the two images in `CRIS(X/S)` of an object of `CRIS(X/S_m)`, `m ≤ e`. -/
abbrev levelStepCompIso {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    S.levelStepChangeBase hm he hme ⋙ S.levelChangeBase he ≅ S.levelChangeBase hm :=
  changeBaseCompIso (S.levelSituation hm) (S.levelSituation he) S (S.levelTransition hm he hme)
    (𝟙 S.X) (S.levelTransition_condition hm he hme) (S.levelProj he) (𝟙 S.X)
    (S.levelProj_condition he) (S.levelProj_condition hm)
    (S.levelTransition_comp_levelProj hm he hme) (Category.comp_id _)

/-- The transition on global sections, pointwise: the value at an object `B` of `CRIS(X/S_m)` is
the value at its image in `CRIS(X/S_e)`, read through the comparison of the two images of `B` in
`CRIS(X/S)`. -/
theorem levelSectionsTransition_app_val {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e)
    (hme : m ≤ e) (N : BigModuleSheaf S) (x : (S.levelSectionsFunctor he).obj N)
    (B : (Thickening (S.levelSituation hm))ᵒᵖ) :
    (((S.levelSectionsTransition hm he hme).app N).hom x).val B =
      N.val.map ((S.levelStepCompIso hm he hme).inv.app B.unop).op
        (x.val (op ((S.levelStepChangeBase hm he hme).obj B.unop))) :=
  rfl

/-- **The restrictions to the levels are compatible with the transitions**: restricting a global
section of `N` to `CRIS(X/S_e)` and then to `CRIS(X/S_m)` is restricting it to `CRIS(X/S_m)`. -/
@[reassoc]
theorem levelSectionsTrans_comp_levelSectionsTransition {m e : ℕ} (hm : S.IsLevel m)
    (he : S.IsLevel e) (hme : m ≤ e) :
    S.levelSectionsTrans he ≫ S.levelSectionsTransition hm he hme = S.levelSectionsTrans hm := by
  refine NatTrans.ext (funext fun N => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  refine Subtype.ext (funext fun B => ?_)
  show N.val.map ((S.levelStepCompIso hm he hme).inv.app B.unop).op
      (x.val (op ((S.levelChangeBase he).obj ((S.levelStepChangeBase hm he hme).obj B.unop)))) =
    x.val (op ((S.levelChangeBase hm).obj B.unop))
  exact x.2 _

/-! ### The tower and the cone -/

section Tower

/-- **A tower of finite divided power levels of the base**: a nondecreasing unbounded sequence
`n ↦ e(n)` of levels, along which the levels `S_{e(n)}` exhaust `S`. -/
structure LevelSequence where
  /-- The exponent of the `n`-th level. -/
  seq : ℕ → ℕ
  /-- Every term is a finite divided power level. -/
  isLevel : ∀ n, S.IsLevel (seq n)
  /-- The levels increase. -/
  monotone : Monotone seq
  /-- The levels are unbounded. -/
  unbounded : ∀ k, ∃ n, k ≤ seq n

variable {S} (hN : S.LevelSequence)

omit [IsAffine S.S.scheme] in
/-- The tower of levels has its transitions from `n + 1` to `n`. -/
theorem LevelSequence.le_succ (n : ℕ) : hN.seq n ≤ hN.seq (n + 1) := hN.monotone (Nat.le_succ n)

variable (S)

/-- **The tower `n ↦ Γ(CRIS(X/S_{e(n)}), N_{e(n)})`** of `A`-modules. -/
def levelSectionsTower (N : BigModuleSheaf S) : ℕᵒᵖ ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  Functor.ofOpSequence (X := fun n => (S.levelSectionsFunctor (hN.isLevel n)).obj N)
    (fun n => (S.levelSectionsTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)).app N)

/-- The transition of the tower from `n + 1` to `n`. -/
theorem levelSectionsTower_map_succ (N : BigModuleSheaf S) (n : ℕ) :
    (S.levelSectionsTower hN N).map (homOfLE (Nat.le_succ n)).op =
      (S.levelSectionsTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)).app N :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The cone `Γ(CRIS(X/S), N) ⟶ Γ(CRIS(X/S_{e(n)}), N_{e(n)})`** over the tower of levels. -/
def levelSectionsCone (N : BigModuleSheaf S) : Cone (S.levelSectionsTower hN N) where
  pt := (bigBaseModuleGlobalSections S).obj N
  π := NatTrans.ofOpSequence (F := (Functor.const _).obj ((bigBaseModuleGlobalSections S).obj N))
    (fun n => (S.levelSectionsTrans (hN.isLevel n)).app N) (fun n =>
      (Category.id_comp _).trans ((NatTrans.congr_app
        (S.levelSectionsTrans_comp_levelSectionsTransition (hN.isLevel n) (hN.isLevel (n + 1))
          (hN.le_succ n))
          N).symm.trans (congrArg (fun φ => (S.levelSectionsTrans (hN.isLevel (n + 1))).app N ≫ φ)
            (S.levelSectionsTower_map_succ hN N n).symm)))

/-- The legs of the cone are the restrictions to the levels. -/
@[simp]
theorem levelSectionsCone_π_app (N : BigModuleSheaf S) (n : ℕ) :
    (S.levelSectionsCone hN N).π.app (op n) = (S.levelSectionsTrans (hN.isLevel n)).app N := rfl

/-- **The images of the levels cover the final object of the topos of `CRIS(X/S)`.**  An object
`(U, T, δ)` is covered by its restrictions to affine opens of `T` on which a power `p^k` vanishes
(`...Thickening.exists_isAffineOpen_mem_and_pow_eq_zero`); such a restriction has `p^{e(n)} = 0`
on its global sections, so lies in the image of `CRIS(X/S_{e(n)})` for `e(n) ≥ k`
(`...levelLift`). -/
theorem coversTop_levelChangeBase :
    (topology S).CoversTop (fun i : Σ n : ℕ, Thickening (S.levelSituation (hN.isLevel n)) =>
      (S.levelChangeBase (hN.isLevel i.1)).obj i.2) := by
  show ∀ V, _
  intro V
  choose W hW hmem k hk using fun t : ULift.{u + 1} V.thickening.target.scheme =>
    Thickening.exists_isAffineOpen_mem_and_pow_eq_zero V t.down
  have hE := V.isZariskiCovering_restrictOpenCover W (fun x => ⟨⟨x⟩, hmem ⟨x⟩⟩)
  refine (topology S).superset_covering ?_ (zariskiCovering_mem_topology S _ hE)
  rintro Z g ⟨Y, a, b, ⟨i⟩, rfl⟩
  obtain ⟨n, hn⟩ := hN.unbounded (k i)
  have hp : ((S.p : ℕ) : Γ((V.restrictOpen (W i)).thickening.target.scheme, ⊤)) ^ hN.seq n =
      0 := by
    have h0 : ((S.p : ℕ) : Γ((V.restrictOpen (W i)).thickening.target.scheme, ⊤)) ^ k i = 0 := by
      have := congrArg (W i).topIso.inv.hom (hk i)
      rwa [map_pow, map_natCast, map_zero] at this
    exact pow_eq_zero_of_le hn h0
  refine ⟨⟨n, (V.restrictOpen (W i)).levelLiftVia S (hN.isLevel n)
    (S.levelLift (hN.isLevel n) (V.restrictOpen (W i)).toBase hp)
    (S.levelLift_comp_levelProj (hN.isLevel n) _ hp)⟩,
    ⟨a ≫ ((V.restrictOpen (W i)).levelLiftViaIso S
      (hN.isLevel n) _ (S.levelLift_comp_levelProj (hN.isLevel n) _ hp)).inv⟩⟩

end Tower


/-! ### Values of a section of `N_e` at an object of `CRIS(X/S)` lying over `S_e` -/

/-- The presheaf of sets underlying a sheaf of modules on `CRIS(X/S)`. -/
abbrev bigModuleTypes (N : BigModuleSheaf S) : (Thickening S)ᵒᵖ ⥤ Type (u + 1) :=
  N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}

section Value

variable {e : ℕ} (he : S.IsLevel e) (N : BigModuleSheaf S)

/-- The value at an object `Z` of `CRIS(X/S)` whose structure morphism factors through `S_e` of a
global section `x` of `N_e`: the value of `x` at the lift of `Z`, transported to `Z`. -/
def levelValue (x : (S.levelSectionsFunctor he).obj N) (Z : Thickening S)
    (φ : Z.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = Z.toBase) :
    (S.bigModuleTypes N).obj (op Z) :=
  (S.bigModuleTypes N).map (Z.levelLiftViaIso S he φ hφ).inv.op
    (x.val (op (Z.levelLiftVia S he φ hφ)))

/-- **The value of a section of `N_e` along a morphism into the image of `u_e`.** -/
theorem map_val_eq_levelValue (x : (S.levelSectionsFunctor he).obj N) {Z : Thickening S}
    {B : Thickening (S.levelSituation he)} (f : Z ⟶ (S.levelChangeBase he).obj B) :
    (S.bigModuleTypes N).map f.op (x.val (op B)) =
      S.levelValue he N x Z (f.targetHom ≫ B.toBase)
        ((Category.assoc f.targetHom B.toBase (S.levelProj he)).trans f.base_naturality) := by
  have hφ := (Category.assoc f.targetHom B.toBase (S.levelProj he)).trans f.base_naturality
  have hf : f = (Z.levelLiftViaIso S he _ hφ).inv ≫
      (S.levelChangeBase he).map (Z.levelLiftOfHomHom S he f) := by
    apply Thickening.Hom.ext <;> exact (Category.id_comp _).symm.trans (Category.id_comp _).symm
  calc (S.bigModuleTypes N).map f.op (x.val (op B))
      = (S.bigModuleTypes N).map ((Z.levelLiftViaIso S he _ hφ).inv ≫
          (S.levelChangeBase he).map (Z.levelLiftOfHomHom S he f)).op (x.val (op B)) :=
        congrArg (fun g : Z ⟶ (S.levelChangeBase he).obj B =>
          (S.bigModuleTypes N).map g.op (x.val (op B))) hf
    _ = (S.bigModuleTypes N).map (Z.levelLiftViaIso S he _ hφ).inv.op
          ((S.bigModuleTypes N).map ((S.levelChangeBase he).map (Z.levelLiftOfHomHom S he f)).op
            (x.val (op B))) := FunctorToTypes.map_comp_apply _ _ _ _
    _ = _ := congrArg ((S.bigModuleTypes N).map (Z.levelLiftViaIso S he _ hφ).inv.op)
          (x.2 (Z.levelLiftOfHomHom S he f).op)

/-- The value does not depend on the factorization, which is unique. -/
theorem levelValue_congr (x : (S.levelSectionsFunctor he).obj N) (Z : Thickening S)
    (φ φ' : Z.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = Z.toBase)
    (hφ' : φ' ≫ S.levelProj he = Z.toBase) :
    S.levelValue he N x Z φ hφ = S.levelValue he N x Z φ' hφ' := by
  obtain rfl : φ = φ' := (cancel_mono (S.levelProj he)).1 (hφ.trans hφ'.symm)
  rfl

end Value

/-- A factorization through `S_m` gives one through `S_e`, `m ≤ e`. -/
private theorem comp_levelTransition_comp_levelProj {m e : ℕ} (hm : S.IsLevel m)
    (he : S.IsLevel e) (hme : m ≤ e) {Z : Thickening S}
    {φ : Z.thickening.target ⟶ (S.levelSituation hm).S} (hφ : φ ≫ S.levelProj hm = Z.toBase) :
    (φ ≫ S.levelTransition hm he hme) ≫ S.levelProj he = Z.toBase :=
  (Category.assoc _ _ _).trans
    ((congrArg (φ ≫ ·) (S.levelTransition_comp_levelProj hm he hme)).trans hφ)

/-- **The value of a section of `N_e` at an object over `S_m`, `m ≤ e`, is the value of its
transition**. -/
theorem levelValue_levelSectionsTransition {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e)
    (hme : m ≤ e) (N : BigModuleSheaf S) (x : (S.levelSectionsFunctor he).obj N)
    (Z : Thickening S) (φ : Z.thickening.target ⟶ (S.levelSituation hm).S)
    (hφ : φ ≫ S.levelProj hm = Z.toBase) :
    S.levelValue hm N (((S.levelSectionsTransition hm he hme).app N).hom x) Z φ hφ =
      S.levelValue he N x Z (φ ≫ S.levelTransition hm he hme)
        ((Category.assoc _ _ _).trans
          ((congrArg (φ ≫ ·) (S.levelTransition_comp_levelProj hm he hme)).trans hφ)) := by
  have hφ' := S.comp_levelTransition_comp_levelProj hm he hme hφ
  let L := Z.levelLiftVia S hm φ hφ
  let L' := Z.levelLiftVia S he (φ ≫ S.levelTransition hm he hme) hφ'
  let j : (S.levelStepChangeBase hm he hme).obj L ⟶ L' :=
    { sourceHom := 𝟙 _
      targetHom := 𝟙 _
      immersion_naturality := (Category.comp_id _).trans (Category.id_comp _).symm
      base_naturality := Category.id_comp _
      toX_naturality := (Category.id_comp _).trans (Category.comp_id _).symm }
  let F := S.bigModuleTypes N
  have e₁ : x.val (op ((S.levelStepChangeBase hm he hme).obj L)) =
      F.map ((S.levelChangeBase he).map j).op (x.val (op L')) := (x.2 j.op).symm
  have e₂ : (Z.levelLiftViaIso S hm φ hφ).inv ≫ (S.levelStepCompIso hm he hme).inv.app L ≫
      (S.levelChangeBase he).map j = (Z.levelLiftViaIso S he _ hφ').inv := by
    apply Thickening.Hom.ext
    all_goals
      show 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
  calc S.levelValue hm N (((S.levelSectionsTransition hm he hme).app N).hom x) Z φ hφ
      = F.map (Z.levelLiftViaIso S hm φ hφ).inv.op
          (F.map ((S.levelStepCompIso hm he hme).inv.app L).op
            (x.val (op ((S.levelStepChangeBase hm he hme).obj L)))) := rfl
    _ = F.map (Z.levelLiftViaIso S hm φ hφ).inv.op
          (F.map ((S.levelStepCompIso hm he hme).inv.app L).op
            (F.map ((S.levelChangeBase he).map j).op (x.val (op L')))) :=
        congrArg (fun y => F.map (Z.levelLiftViaIso S hm φ hφ).inv.op
          (F.map ((S.levelStepCompIso hm he hme).inv.app L).op y)) e₁
    _ = F.map ((Z.levelLiftViaIso S hm φ hφ).inv ≫ (S.levelStepCompIso hm he hme).inv.app L ≫
          (S.levelChangeBase he).map j).op (x.val (op L')) :=
        ((FunctorToTypes.map_comp_apply F _ _ _).trans
          (congrArg _ (FunctorToTypes.map_comp_apply F _ _ _))).symm
    _ = _ := congrArg (fun g : Z ⟶ (S.levelChangeBase he).obj L' => F.map g.op (x.val (op L')))
          e₂


/-! ### `Γ(CRIS(X/S), N) = lim_e Γ(CRIS(X/S_e), N_e)` -/

section Limit

variable {S} (hN : S.LevelSequence) (N : BigModuleSheaf S)

variable (S)

/-- Going up the tower from level `e(m)` to level `e(m + d)` does not change the value of a
compatible family of sections at an object lying over `S_{e(m)}`. -/
theorem levelValue_tower (s : ∀ n, (S.levelSectionsFunctor (hN.isLevel n)).obj N)
    (hs : ∀ n, ((S.levelSectionsTransition (hN.isLevel n) (hN.isLevel (n + 1))
      (hN.le_succ n)).app N).hom
      (s (n + 1)) = s n)
    (m d : ℕ) (Z : Thickening S) (φ : Z.thickening.target ⟶ (S.levelSituation (hN.isLevel m)).S)
    (hφ : φ ≫ S.levelProj (hN.isLevel m) = Z.toBase)
    (φ' : Z.thickening.target ⟶ (S.levelSituation (hN.isLevel (m + d))).S)
    (hφ' : φ' ≫ S.levelProj (hN.isLevel (m + d)) = Z.toBase) :
    S.levelValue (hN.isLevel m) N (s m) Z φ hφ =
      S.levelValue (hN.isLevel (m + d)) N (s (m + d)) Z φ' hφ' := by
  induction d with
  | zero => exact S.levelValue_congr (hN.isLevel m) N (s m) Z φ φ' hφ hφ'
  | succ d ih =>
    have hψ := S.comp_levelTransition_comp_levelProj (hN.isLevel m) (hN.isLevel (m + d))
      (hN.monotone (by omega)) hφ
    refine (ih _ hψ).trans ?_
    refine (congrArg (fun y => S.levelValue (hN.isLevel (m + d)) N y Z _ hψ)
      (hs (m + d)).symm).trans ?_
    refine (S.levelValue_levelSectionsTransition (hN.isLevel (m + d)) (hN.isLevel (m + d + 1))
      (hN.le_succ _)
      N (s (m + d + 1)) Z _ hψ).trans ?_
    exact S.levelValue_congr (hN.isLevel (m + d + 1)) N (s (m + d + 1)) Z _ φ' _ hφ'

/-- **Stacks Project, Tag 07MV, underived, at module coefficients on the big crystalline site.**
For a global crystalline situation `X/S` with affine base, an unbounded nondecreasing sequence of
finite divided power levels `S_{e(n)} ⊂ S` and a sheaf `N` of `𝒪_{X/S}`-modules on `CRIS(X/S)`,
the restrictions `Γ(CRIS(X/S), N) ⟶ Γ(CRIS(X/S_{e(n)}), N_{e(n)})` exhibit `Γ(CRIS(X/S), N)` as
the limit of the
tower of global sections over the levels.

Every object of `CRIS(X/S)` is Zariski locally an object of some `CRIS(X/S_e)`
(`coversTop_levelChangeBase`), so a compatible family of sections over the levels is a compatible
family on objects covering the final object, which amalgamates uniquely. -/
def isLimitLevelSectionsCone : IsLimit (S.levelSectionsCone hN N) := by
  let F := S.bigModuleTypes N
  have hF : Presheaf.IsSheaf (topology S) F := SmallSite.isSheafType_bigModule S N
  refine isLimitOfReflects (CategoryTheory.forget (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)))
    (Classical.choice ((Types.isLimit_iff _).2 fun s hs => ?_))
  let t : ∀ n, (S.levelSectionsFunctor (hN.isLevel n)).obj N := fun n => s (op n)
  have ht : ∀ n, ((S.levelSectionsTransition (hN.isLevel n) (hN.isLevel (n + 1))
      (hN.le_succ n)).app N).hom
      (t (n + 1)) = t n := fun n =>
    (congrArg (fun g => ModuleCat.Hom.hom g (t (n + 1)))
      (S.levelSectionsTower_map_succ hN N n)).symm.trans (hs (homOfLE (Nat.le_succ n)).op)
  let Y : (Σ n : ℕ, Thickening (S.levelSituation (hN.isLevel n))) → Thickening S :=
    fun i => (S.levelChangeBase (hN.isLevel i.1)).obj i.2
  let x : Presheaf.FamilyOfElementsOnObjects F Y := fun i => (t i.1).val (op i.2)
  have hx : x.IsCompatible := by
    intro Z i j f g
    change F.map f.op ((t i.1).val (op i.2)) = F.map g.op ((t j.1).val (op j.2))
    rw [S.map_val_eq_levelValue (hN.isLevel i.1) N (t i.1) f,
      S.map_val_eq_levelValue (hN.isLevel j.1) N (t j.1) g]
    rcases le_total i.1 j.1 with h | h
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      obtain ⟨j₁, j₂⟩ := j
      dsimp only at hd g ⊢
      subst hd
      exact S.levelValue_tower hN N t ht _ d Z _ _ _ _
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      obtain ⟨i₁, i₂⟩ := i
      dsimp only at hd f ⊢
      subst hd
      exact (S.levelValue_tower hN N t ht _ d Z _ _ _ _).symm
  let σ := hx.section_ (S.coversTop_levelChangeBase hN) hF
  refine ⟨σ, fun n => ?_, fun y hy => ?_⟩
  · exact Subtype.ext (funext fun B =>
      hx.section_apply (S.coversTop_levelChangeBase hN) hF ⟨n.unop, B.unop⟩)
  · refine (S.coversTop_levelChangeBase hN).sections_ext ⟨F, hF⟩ fun i => ?_
    change y.val (op (Y i)) = σ.val (op (Y i))
    rw [hx.section_apply (S.coversTop_levelChangeBase hN) hF i]
    exact congrArg (fun z : (S.levelSectionsFunctor (hN.isLevel i.1)).obj N => z.val (op i.2))
      (hy (op i.1))

end Limit

end Crystalline.GlobalCrystallineSituation
