module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleBarResolution
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleBarFunctorial
public import StacksFrontier.CategoryTheory.Abelian.ExactOnHom
public import StacksFrontier.CategoryTheory.Adjunction.Mates
import StacksCore.Tactic.StacksAttribute

/-!
# The complex `0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …` of a ringed augmentation

Let `S` be a simplicial-site situation (Stacks 09WE), `a` an augmentation of `S` towards a site
`(D, K)` (Stacks 0D6Z) and `A` a ringed augmentation (Stacks 0D9D): sheaves of rings `O` on the
total site and `O_D` on `(D, K)` with `a^♯ : O_D ⟶ a_*O`, so that
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` and `a_n = a ∘ g_n` are morphisms of ringed topoi.
Stacks 0D7D asserts that for an `O`-module `F` there is a canonical complex of
`O_D`-modules

`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ a_{2,*}F_2 ⟶ …`

which is exact in degrees `-1` and `0`, and which, when `F` is an injective `O`-module, is exact
in every degree and stays exact after `Hom_{O_D}(G, -)` for every `O_D`-module `G`.

## The construction

It is the source's. By Yoneda it suffices to give, functorially in `G`, the complex
`0 ⟶ Hom(G, a_*F) ⟶ Hom(G, a_{0,*}F_0) ⟶ Hom(G, a_{1,*}F_1) ⟶ …`, and that is `Hom_O(-, F)`
applied to the exact complex `… ⟶ g_{1!}(a_1^*G) ⟶ g_{0!}(a_0^*G) ⟶ a^*G ⟶ 0` of Stacks 0D7C,
read through the adjunctions `g_{n!}a_n^* ⊣ a_{n,*}g_n^*` and `a^* ⊣ a_*`.

The resolution of Stacks 0D7C is
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.moduleResolution`: the
simplex-coefficient resolution `B_•(a^*G)` of `a^*G`, whose terms are identified with the
`g_{n!}(a_n^*G)`. The Yoneda step needs it as a functor of `G`: `G ↦ B_n(a^*G)` is a functor
(`barTerm`), its differentials and augmentation are natural (`barD`, `barAug`, which at each `G`
*are* those of `moduleResolution G`), and the identification with `g_{n!}(a_n^*G)` is natural
(`barTermIso`). So `barTerm n` is a left adjoint of `a_{n,*}g_n^*` (`barTermAdjunction`), `a^*` is
a left adjoint of `a_*`, and the differentials of the complex of this file are the *conjugates*
of those of the resolution (`cechAug`, `cechD`): transposed along the adjunctions, `h ≫ d` is the
differential of the resolution followed by the transpose of `h` (`homEquiv_cechAug`,
`homEquiv_cechD`).

Exactness is then the source's argument: `Hom_O(-, F)` is left exact, and the resolution is exact
at its two right-hand terms, which gives degrees `-1` and `0` for every `F`; for an injective `F`
the functor `Hom_O(-, F)` is exact; and a complex of sheaves of modules is exact as soon as
`Hom(G, -)` of it is exact for every `G` (`Stacks.CategoryTheory.ExactOnHom`).

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentPushforwardModules`:
  `F ↦ a_{n,*}F_n`.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.barTermAdjunction`: the adjunction
  `B_n(a^*(-)) ⊣ a_{n,*}g_n^*`, the left adjoint being identified with `g_{n!}a_n^*`.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.moduleCechComplex`: the complex of
  Stacks 0D7D.

## Main results

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.moduleCechComplex_spec`:
  **Stacks 0D7D**.

## Implementation notes

The complex is indexed by `ℕ`, with `a_*F` in degree `0` and `a_{n,*}F_n` in degree `n + 1`, so
the source's degrees `-1` and `0` are the Lean degrees `0` and `1`.

The adjunctions are `@[irreducible]`: everything below uses them only through their
transposition, and elaboration otherwise unfolds the lower shriek and the sheafifications inside
them while comparing types.

## References

* [Stacks Project, Tag 0D7D](https://stacks.math.columbia.edu/tag/0D7D)
* [Stacks Project, Tag 0D7C](https://stacks.math.columbia.edu/tag/0D7C)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Section 85.11 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent

/-- Conjugating a 2-cell whose components vanish gives a 2-cell whose components vanish. -/
theorem _root_.CategoryTheory.conjugateEquiv_app_eq_zero {C₁ C₂ : Type*} [Category C₁]
    [Category C₂] [Preadditive C₁] [Preadditive C₂] {L₁ L₂ : C₁ ⥤ C₂} {R₁ R₂ : C₂ ⥤ C₁}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (hα : ∀ X, α.app X = 0) (Y : C₂) :
    (conjugateEquiv adj₁ adj₂ α).app Y = 0 := by
  have : R₂.IsRightAdjoint := adj₂.isRightAdjoint
  rw [conjugateEquiv_apply_app, hα, Functor.map_zero, zero_comp, comp_zero]

/-- A short complex which is exact with an epimorphic second map stays exact after `Hom(-, Y)`,
for any `Y`: its second map is a cokernel of its first. -/
theorem _root_.CategoryTheory.ShortComplex.Exact.function_exact_precomp_of_epi {C : Type*}
    [Category C] [Abelian C] {T : ShortComplex C} (hT : T.Exact) [Epi T.g] (Y : C) :
    Function.Exact (fun h : T.X₃ ⟶ Y => T.g ≫ h) (fun h : T.X₂ ⟶ Y => T.f ≫ h) := by
  intro y
  constructor
  · intro hy
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hT.gIsCokernel y hy
    exact ⟨l, hl⟩
  · rintro ⟨h, rfl⟩
    simp

namespace RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-! ### The terms and their left adjoints -/

/-- The degree-`n` term `F ↦ a_{n,*}F_n` of the complex: restriction to the degree-`n`
component followed by the direct image along `a_n = a ∘ g_n`. -/
abbrev componentPushforwardModules (n : SimplexCategory) :
    (S.totalRingedTopos A.O).Modules ⥤ A.augmentationRingedTopos.Modules :=
  S.componentModulesRestriction A.O n ⋙ (A.componentRingedHom n).pushforwardModules

/-- The left adjoint `G ↦ g_{n!}(a_n^*G)` of `a_{n,*}g_n^*`: the degree-`n` term of the
resolution of Stacks 0D7C. -/
abbrev componentPullbackLowerShriek (n : SimplexCategory) :
    A.augmentationRingedTopos.Modules ⥤ (S.totalRingedTopos A.O).Modules :=
  (A.componentRingedHom n).toModulesHom.pullbackModules ⋙
    S.componentModuleLowerShriek (S.totalRingSheaf A.O) n

/-- The adjunction `g_{n!}a_n^* ⊣ a_{n,*}g_n^*`, composite of Stacks 03D7 for `a_n` and of
Stacks 0D72 for `g_n`. -/
@[irreducible] def componentPullbackLowerShriekAdjunction (n : SimplexCategory) :
    A.componentPullbackLowerShriek n ⊣ A.componentPushforwardModules n :=
  (A.componentRingedHom n).pullbackAdjPushforwardModules.comp
    (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf A.O) n)

/-- The degree-`n` term `G ↦ B_n(a^*G)` of the resolution of Stacks 0D7C
(`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.moduleResolution`), as a functor of
the coefficient module. -/
abbrev barTerm (n : ℕ) :
    A.augmentationRingedTopos.Modules ⥤ (S.totalRingedTopos A.O).Modules :=
  A.totalRingedHom.toModulesHom.pullbackModules ⋙
    moduleBarSheafFunctor (S.totalRingSheaf A.O) ⦋n⦌

/-- The canonical map `g_{n!}((a^*G)|_n) ⟶ B_n(a^*G)` is an isomorphism, naturally in `G`, since
`a^*G` is cartesian. -/
instance isIso_whiskerLeft_moduleBarLowerShriekNatTrans (n : SimplexCategory) :
    IsIso (Functor.whiskerLeft A.totalRingedHom.toModulesHom.pullbackModules
      (moduleBarLowerShriekNatTrans A.O n)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  exact isIso_moduleBarLowerShriekMap A.O _ (A.isCartesianModule_totalPullbackModule G) n

/-- **The terms of the resolution of Stacks 0D7C, naturally in the coefficient module**:
`B_n(a^*G) ≅ g_{n!}(a_n^*G)`, built from the same two comparisons as the identification
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.moduleBarResolutionTermIso` of the
terms of `moduleResolution G`: the canonical map `g_{n!}((a^*G)|_n) ⟶ B_n(a^*G)`, invertible as
`a^*G` is cartesian, and `(a^*G)|_n = a_n^*G`. -/
@[irreducible] def barTermIso (n : ℕ) : A.barTerm n ≅ A.componentPullbackLowerShriek ⦋n⦌ :=
  (asIso (Functor.whiskerLeft A.totalRingedHom.toModulesHom.pullbackModules
      (moduleBarLowerShriekNatTrans A.O ⦋n⦌))).symm ≪≫
    Functor.isoWhiskerLeft A.totalRingedHom.toModulesHom.pullbackModules
      (Functor.isoWhiskerRight (componentPullbackModulesRestrictionIso S A.O ⦋n⦌).symm
        (S.componentModuleLowerShriek (S.totalRingSheaf A.O) ⦋n⦌)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (A.componentPullbackModulesIso ⦋n⦌).symm
      (S.componentModuleLowerShriek (S.totalRingSheaf A.O) ⦋n⦌)

/-- **The adjunction `(G ↦ B_n(a^*G)) ⊣ a_{n,*}g_n^*`.** -/
@[irreducible] def barTermAdjunction (n : ℕ) : A.barTerm n ⊣ A.componentPushforwardModules ⦋n⦌ :=
  (A.componentPullbackLowerShriekAdjunction ⦋n⦌).ofNatIsoLeft (A.barTermIso n).symm

/-- The adjunction `a^* ⊣ a_*` of Stacks 03D7. -/
abbrev totalAdjunction :=
  A.totalRingedHom.pullbackAdjPushforwardModules

/-! ### The differentials of the resolution, natural in the coefficient module -/

/-- The differential `B_{n+1}(a^*G) ⟶ B_n(a^*G)` of the resolution of Stacks 0D7C, natural in
the coefficient module `G`: at `G` it is the differential of `moduleResolution G`. -/
def barD (n : ℕ) : A.barTerm (n + 1) ⟶ A.barTerm n where
  app G := (A.moduleResolution G).complex.d (n + 1) n
  naturality _ _ g := (moduleBarComplex_d_naturality (O := S.totalRingSheaf A.O)
    (A.totalRingedHom.toModulesHom.pullbackModules.map g) (n + 1) n).symm

/-- The augmentation `B_0(a^*G) ⟶ a^*G` of the resolution of Stacks 0D7C, natural in the
coefficient module `G`: at `G` it is the augmentation of `moduleResolution G`. -/
def barAug : A.barTerm 0 ⟶ A.totalRingedHom.toModulesHom.pullbackModules where
  app G := (A.moduleResolution G).augmentation
  naturality _ _ g := moduleBarAugmentation_naturality (O := S.totalRingSheaf A.O)
    (A.totalRingedHom.toModulesHom.pullbackModules.map g) ⦋0⦌

/-- Two consecutive differentials `barD` of the resolution compose to zero. -/
theorem barD_comp_barD_app (n : ℕ) (G : A.augmentationRingedTopos.Modules) :
    (A.barD (n + 1) ≫ A.barD n).app G = 0 :=
  (A.moduleResolution G).complex.d_comp_d _ _ _

/-- The differential `barD 0` followed by the augmentation `barAug` is zero. -/
theorem barD_comp_barAug_app (G : A.augmentationRingedTopos.Modules) :
    (A.barD 0 ≫ A.barAug).app G = 0 :=
  (A.moduleResolution G).augmentation_comp

/-! ### The complex -/

variable (F : (S.totalRingedTopos A.O).Modules)

/-- The differential `a_{n,*}F_n ⟶ a_{n+1,*}F_{n+1}`: the conjugate of the differential of the
resolution of Stacks 0D7C. -/
abbrev cechD (n : ℕ) :
    (A.componentPushforwardModules ⦋n⦌).obj F ⟶ (A.componentPushforwardModules ⦋n + 1⦌).obj F :=
  (conjugateEquiv (A.barTermAdjunction n) (A.barTermAdjunction (n + 1)) (A.barD n)).app F

/-- The differential `a_*F ⟶ a_{0,*}F_0`: the conjugate of the augmentation of the resolution of
Stacks 0D7C. -/
abbrev cechAug :
    A.totalRingedHom.pushforwardModules.obj F ⟶ (A.componentPushforwardModules ⦋0⦌).obj F :=
  (conjugateEquiv A.totalAdjunction (A.barTermAdjunction 0) A.barAug).app F

/-- Two consecutive differentials `a_{n,*}F_n ⟶ a_{n+1,*}F_{n+1} ⟶ a_{n+2,*}F_{n+2}` compose to
zero. -/
theorem cechD_comp_cechD (n : ℕ) : A.cechD F n ≫ A.cechD F (n + 1) = 0 :=
  (NatTrans.comp_app _ _ F).symm.trans
    ((congrArg (fun t => t.app F) (conjugateEquiv_comp (A.barTermAdjunction n)
      (A.barTermAdjunction (n + 1)) (A.barTermAdjunction (n + 1 + 1))
      (A.barD n) (A.barD (n + 1)))).trans
      (conjugateEquiv_app_eq_zero _ _ _ (A.barD_comp_barD_app n) F))

/-- The composite `a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1` is zero. -/
theorem cechAug_comp_cechD : A.cechAug F ≫ A.cechD F 0 = 0 :=
  (NatTrans.comp_app _ _ F).symm.trans
    ((congrArg (fun t => t.app F) (conjugateEquiv_comp A.totalAdjunction
      (A.barTermAdjunction 0) (A.barTermAdjunction (0 + 1))
      A.barAug (A.barD 0))).trans
      (conjugateEquiv_app_eq_zero _ _ _ A.barD_comp_barAug_app F))

/-- The complex `a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …`, without its augmentation. -/
def componentCechComplex : CochainComplex A.augmentationRingedTopos.Modules ℕ :=
  CochainComplex.of (fun n => (A.componentPushforwardModules ⦋n⦌).obj F) (A.cechD F)
    (A.cechD_comp_cechD F)

/-- The differential of `componentCechComplex F` from degree `n` to degree `n + 1` is `cechD`. -/
theorem componentCechComplex_d (n : ℕ) :
    (A.componentCechComplex F).d n (n + 1) = A.cechD F n := by
  delta componentCechComplex
  exact CochainComplex.of_d (fun n => (A.componentPushforwardModules ⦋n⦌).obj F) (A.cechD F) n

/-- **The complex `0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …` of Stacks 0D7D**: `a_*F` in
degree `0`, `a_{n,*}F_n` in degree `n + 1`, and as differentials the conjugates, along
`a^* ⊣ a_*` and `g_{n!}a_n^* ⊣ a_{n,*}g_n^*`, of the augmentation and of the differentials of the
resolution `… ⟶ g_{1!}(a_1^*G) ⟶ g_{0!}(a_0^*G) ⟶ a^*G` of Stacks 0D7C. -/
def moduleCechComplex : CochainComplex A.augmentationRingedTopos.Modules ℕ :=
  (A.componentCechComplex F).augment (A.cechAug F) (by
    rw [componentCechComplex_d]
    exact A.cechAug_comp_cechD F)

/-- The degree-`0` term of `moduleCechComplex F` is `a_*F`. -/
theorem moduleCechComplex_X_zero :
    (A.moduleCechComplex F).X 0 = A.totalRingedHom.pushforwardModules.obj F :=
  rfl

/-- The degree-`(n + 1)` term of `moduleCechComplex F` is `a_{n,*}F_n`. -/
theorem moduleCechComplex_X_succ (n : ℕ) :
    (A.moduleCechComplex F).X (n + 1) =
      (A.componentRingedHom ⦋n⦌).pushforwardModules.obj
        ((S.componentModulesRestriction A.O ⦋n⦌).obj F) :=
  rfl

/-- The differential of `moduleCechComplex F` from degree `0` to degree `1` is `cechAug`. -/
theorem moduleCechComplex_d_zero : (A.moduleCechComplex F).d 0 1 = A.cechAug F :=
  rfl

/-- The differential of `moduleCechComplex F` from degree `n + 1` to degree `n + 2` is
`cechD F n`. -/
theorem moduleCechComplex_d_succ (n : ℕ) :
    (A.moduleCechComplex F).d (n + 1) (n + 2) = A.cechD F n := by
  delta moduleCechComplex
  exact (CochainComplex.augment_d_succ_succ _ _ _ n (n + 1)).trans
    (A.componentCechComplex_d F n)

/-! ### The differentials, transposed -/

/-- **The first differential is the transpose of the augmentation of Stacks 0D7C.** For
`f : a^*G ⟶ F`, the transpose along `g_{0!}a_0^* ⊣ a_{0,*}g_0^*` of the augmentation followed by
`f` is the transpose of `f` along `a^* ⊣ a_*` followed by the differential
`a_*F ⟶ a_{0,*}F_0`. -/
theorem homEquiv_cechAug (G : A.augmentationRingedTopos.Modules)
    (f : (A.totalRingedHom.toModulesHom.pullbackModules).obj G ⟶ F) :
    (A.barTermAdjunction 0).homEquiv G F ((A.moduleResolution G).augmentation ≫ f) =
      A.totalAdjunction.homEquiv G F f ≫ A.cechAug F :=
  Stacks.CategoryTheory.homEquiv_conjugate' A.totalAdjunction (A.barTermAdjunction 0)
    A.barAug f

/-- **The higher differentials are the transposes of those of Stacks 0D7C.** For
`f : g_{n!}(a_n^*G) ⟶ F`, the transpose of the differential of the resolution followed by `f` is
the transpose of `f` followed by the differential `a_{n,*}F_n ⟶ a_{n+1,*}F_{n+1}`. -/
theorem homEquiv_cechD (n : ℕ) (G : A.augmentationRingedTopos.Modules)
    (f : (A.barTerm n).obj G ⟶ F) :
    (A.barTermAdjunction (n + 1)).homEquiv G F ((A.moduleResolution G).complex.d (n + 1) n ≫ f) =
      (A.barTermAdjunction n).homEquiv G F f ≫ A.cechD F n :=
  Stacks.CategoryTheory.homEquiv_conjugate' (A.barTermAdjunction n)
    (A.barTermAdjunction (n + 1)) (A.barD n) f

/-! ### Exactness on hom-groups -/

/-- `Hom(-, F)` of the right end `B_1(a^*G) ⟶ B_0(a^*G) ⟶ a^*G ⟶ 0` of the resolution is exact:
`Hom(-, F)` is left exact. -/
theorem function_exact_resolution_zero (G : A.augmentationRingedTopos.Modules) :
    Function.Exact (fun h : (A.totalRingedHom.toModulesHom.pullbackModules).obj G ⟶ F =>
        A.barAug.app G ≫ h)
      (fun h : (A.barTerm 0).obj G ⟶ F => (A.barD 0).app G ≫ h) := by
  have := (A.moduleResolution G).augmentation_epi
  exact (A.moduleResolution G).exact_zero.function_exact_precomp_of_epi F

/-- The resolution `moduleResolution G` is exact at `B_{j+1}(a^*G)`. -/
theorem moduleResolution_exact_succ (G : A.augmentationRingedTopos.Modules) (j : ℕ) :
    (ShortComplex.mk ((A.moduleResolution G).complex.d (j + 2) (j + 1))
      ((A.moduleResolution G).complex.d (j + 1) j)
      ((A.moduleResolution G).complex.d_comp_d _ _ _)).Exact := by
  have h := (A.moduleResolution G).exact_positive (j + 1) (Nat.succ_pos j)
  rwa [HomologicalComplex.exactAt_iff' (A.moduleResolution G).complex (j + 2) (j + 1) j
    (by simp) (by simp)] at h

/-- `Hom(-, F)` of the resolution is exact at `B_{j+1}(a^*G)` when `F` is injective. -/
theorem function_exact_resolution_succ [Injective F] (j : ℕ)
    (G : A.augmentationRingedTopos.Modules) :
    Function.Exact (fun h : (A.barTerm j).obj G ⟶ F => (A.barD j).app G ≫ h)
      (fun h : (A.barTerm (j + 1)).obj G ⟶ F => (A.barD (j + 1)).app G ≫ h) :=
  @Stacks.CategoryTheory.ExactOnHom.function_exact_hom_of_exact _ _ _ _
    (A.moduleResolution_exact_succ G j) F ‹_›

/-- The functor `G ↦ B_n(a^*G)` is additive. -/
instance additive_barTerm (n : ℕ) : (A.barTerm n).Additive :=
  Stacks.CategoryTheory.ExactOnHom.additive_of_adjunction (A.barTermAdjunction n)

/-- **`Hom(G, -)` of the complex is injective at `a_*F`**, for every `F`. -/
theorem injective_comp_cechAug (G : A.augmentationRingedTopos.Modules) :
    Function.Injective (fun h : G ⟶ A.totalRingedHom.pushforwardModules.obj F =>
      h ≫ A.cechAug F) := by
  intro h₁ h₂ hh
  have : Epi (A.barAug.app G) := (A.moduleResolution G).augmentation_epi
  have e₁ := Stacks.CategoryTheory.homEquiv_conjugate' A.totalAdjunction (A.barTermAdjunction 0)
    A.barAug ((A.totalAdjunction.homEquiv G F).symm h₁)
  have e₂ := Stacks.CategoryTheory.homEquiv_conjugate' A.totalAdjunction (A.barTermAdjunction 0)
    A.barAug ((A.totalAdjunction.homEquiv G F).symm h₂)
  rw [Equiv.apply_symm_apply] at e₁ e₂
  have h : A.barAug.app G ≫ (A.totalAdjunction.homEquiv G F).symm h₁ =
      A.barAug.app G ≫ (A.totalAdjunction.homEquiv G F).symm h₂ :=
    ((A.barTermAdjunction 0).homEquiv G F).injective (e₁.trans (hh.trans e₂.symm))
  exact (A.totalAdjunction.homEquiv G F).symm.injective ((cancel_epi _).1 h)

/-- **`Hom(G, -)` of the complex is exact at `a_{0,*}F_0`**, for every `F`. -/
theorem function_exact_comp_cechAug_cechD (G : A.augmentationRingedTopos.Modules) :
    Function.Exact (fun h : G ⟶ A.totalRingedHom.pushforwardModules.obj F => h ≫ A.cechAug F)
      (fun h : G ⟶ (A.componentPushforwardModules ⦋0⦌).obj F => h ≫ A.cechD F 0) := by
  refine Stacks.CategoryTheory.ExactOnHom.function_exact_of_conjugate A.totalAdjunction
    (A.barTermAdjunction 0) (A.barTermAdjunction 1)
    (conjugateEquiv A.totalAdjunction (A.barTermAdjunction 0) A.barAug)
    (conjugateEquiv (A.barTermAdjunction 0) (A.barTermAdjunction 1) (A.barD 0))
    G F ?_
  simp only [Equiv.symm_apply_apply]
  exact A.function_exact_resolution_zero F G

/-- **`Hom(G, -)` of the complex is exact at `a_{j+1,*}F_{j+1}`** when `F` is injective. -/
theorem function_exact_comp_cechD_cechD [Injective F] (j : ℕ)
    (G : A.augmentationRingedTopos.Modules) :
    Function.Exact (fun h : G ⟶ (A.componentPushforwardModules ⦋j⦌).obj F => h ≫ A.cechD F j)
      (fun h : G ⟶ (A.componentPushforwardModules ⦋j + 1⦌).obj F =>
        h ≫ A.cechD F (j + 1)) := by
  refine Stacks.CategoryTheory.ExactOnHom.function_exact_of_conjugate
    (A.barTermAdjunction j) (A.barTermAdjunction (j + 1)) (A.barTermAdjunction (j + 2))
    (conjugateEquiv (A.barTermAdjunction j) (A.barTermAdjunction (j + 1)) (A.barD j))
    (conjugateEquiv (A.barTermAdjunction (j + 1)) (A.barTermAdjunction (j + 2)) (A.barD (j + 1)))
    G F ?_
  simp only [Equiv.symm_apply_apply]
  exact A.function_exact_resolution_succ F j G

/-- The differential of `moduleCechComplex F` from degree `1` to degree `2` is `cechD F 0`. -/
theorem moduleCechComplex_d_one : (A.moduleCechComplex F).d 1 2 = A.cechD F 0 :=
  A.moduleCechComplex_d_succ F 0

/-! ### Exactness -/

/-- Exactness of `Hom(G, -)` of a cochain complex above degree `0`, as exactness of hom-sets. -/
theorem _root_.CategoryTheory.exactAt_succ_preadditiveCoyoneda_iff {𝒜 : Type*} [Category 𝒜]
    [Preadditive 𝒜] (C : CochainComplex 𝒜 ℕ) (G : 𝒜) (j : ℕ) :
    (((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex _).obj C).ExactAt (j + 1) ↔
      Function.Exact (fun h : G ⟶ C.X j => h ≫ C.d j (j + 1))
        (fun h : G ⟶ C.X (j + 1) => h ≫ C.d (j + 1) (j + 2)) := by
  rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
    (CochainComplex.next ℕ (j + 1)), ShortComplex.ab_exact_iff_function_exact]
  rfl

/-- Exactness of `Hom(G, -)` of a cochain complex in degree `0`, as injectivity on hom-sets. -/
theorem _root_.CategoryTheory.exactAt_zero_preadditiveCoyoneda_iff {𝒜 : Type*} [Category 𝒜]
    [Preadditive 𝒜] (C : CochainComplex 𝒜 ℕ) (G : 𝒜) :
    (((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex _).obj C).ExactAt 0 ↔
      Function.Injective (fun h : G ⟶ C.X 0 => h ≫ C.d 0 1) := by
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
    (CochainComplex.next ℕ 0), ShortComplex.exact_iff_mono _
      ((((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex _).obj C).shape 0 0 (by simp)),
    AddCommGrpCat.mono_iff_injective]
  rfl

/-- **`Hom(G, -)` of the complex is exact in degrees `-1` and `0`**, for every `F`. -/
theorem moduleCechComplex_hom_exactAt_le_one (G : A.augmentationRingedTopos.Modules) (k : ℕ)
    (hk : k ≤ 1) :
    (((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex _).obj
      (A.moduleCechComplex F)).ExactAt k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact (exactAt_zero_preadditiveCoyoneda_iff _ G).2 (A.injective_comp_cechAug F G)
  · refine (exactAt_succ_preadditiveCoyoneda_iff _ G 0).2 ?_
    rw [moduleCechComplex_d_zero, moduleCechComplex_d_one]
    exact A.function_exact_comp_cechAug_cechD F G

/-- **`Hom(G, -)` of the complex is exact in every degree when `F` is injective.** -/
theorem moduleCechComplex_hom_exactAt_of_injective [Injective F]
    (G : A.augmentationRingedTopos.Modules) (k : ℕ) :
    (((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex _).obj
      (A.moduleCechComplex F)).ExactAt k := by
  match k with
  | 0 => exact A.moduleCechComplex_hom_exactAt_le_one F G 0 (Nat.zero_le 1)
  | 1 => exact A.moduleCechComplex_hom_exactAt_le_one F G 1 le_rfl
  | j + 2 =>
    refine (exactAt_succ_preadditiveCoyoneda_iff _ G (j + 1)).2 ?_
    have h₁ : (A.moduleCechComplex F).d (j + 1) (j + 1 + 1) = A.cechD F j :=
      A.moduleCechComplex_d_succ F j
    have h₂ : (A.moduleCechComplex F).d (j + 1 + 1) (j + 1 + 2) = A.cechD F (j + 1) :=
      A.moduleCechComplex_d_succ F (j + 1)
    rw [h₁, h₂]
    exact A.function_exact_comp_cechD_cechD F j G

/-- A cochain complex of `O_D`-modules is exact at a term as soon as `Hom(G, -)` of it is exact
there for every `G`. -/
theorem exactAt_of_forall_hom_exactAt (C : CochainComplex A.augmentationRingedTopos.Modules ℕ)
    (k : ℕ) (h : ∀ G : A.augmentationRingedTopos.Modules,
      (((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex _).obj C).ExactAt k) :
    C.ExactAt k := by
  match k with
  | 0 =>
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
      (CochainComplex.next ℕ 0)]
    refine (ShortComplex.exact_iff_mono _ (C.shape 0 0 (by simp))).2 ⟨fun {Z} g g' hg => ?_⟩
    exact (exactAt_zero_preadditiveCoyoneda_iff C Z).1 (h Z) hg
  | j + 1 =>
    rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
      (CochainComplex.next ℕ (j + 1))]
    exact Stacks.CategoryTheory.ExactOnHom.exact_of_forall_function_exact _ _ (C.d_comp_d _ _ _)
      fun G => (exactAt_succ_preadditiveCoyoneda_iff C G j).1 (h G)

/-- With the notation of Stacks 0D9D, let `F` be a sheaf of `O`-modules on the
total site. The canonical complex of `O_D`-modules

`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ a_{2,*}F_2 ⟶ …`

(`moduleCechComplex`, with `a_*F` in degree `0` and `a_{n,*}F_n` in degree `n + 1`) is exact in
degrees `-1` and `0` (the Lean degrees `0` and `1`). If `F` is an injective `O`-module, the
complex is exact in all degrees and remains exact on applying `Hom_{O_D}(G, -)` for any
`O_D`-module `G`.

The complex is the source's: its differentials are the transposes, along the adjunctions
`a^* ⊣ a_*` and `g_{n!}a_n^* ⊣ a_{n,*}g_n^*`, of the augmentation and of the differentials of the
resolution `… ⟶ g_{1!}(a_1^*G) ⟶ g_{0!}(a_0^*G) ⟶ a^*G ⟶ 0` of Stacks 0D7C
(`homEquiv_cechAug`, `homEquiv_cechD`), so `Hom(G, -)` of it is `Hom(-, F)` of that resolution;
`Hom(-, F)` is left exact, and exact when `F` is injective. -/
@[stacks 0D7D]
theorem moduleCechComplex_spec :
    (A.moduleCechComplex F).X 0 = A.totalRingedHom.pushforwardModules.obj F ∧
    (∀ n : ℕ, (A.moduleCechComplex F).X (n + 1) =
      (A.componentRingedHom ⦋n⦌).pushforwardModules.obj
        ((S.componentModulesRestriction A.O ⦋n⦌).obj F)) ∧
    (A.moduleCechComplex F).ExactAt 0 ∧ (A.moduleCechComplex F).ExactAt 1 ∧
    (Injective F →
      (∀ k : ℕ, (A.moduleCechComplex F).ExactAt k) ∧
      ∀ (G : A.augmentationRingedTopos.Modules) (k : ℕ),
        (((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex _).obj
          (A.moduleCechComplex F)).ExactAt k) :=
  ⟨rfl, fun _ => rfl,
    A.exactAt_of_forall_hom_exactAt _ 0 fun G =>
      A.moduleCechComplex_hom_exactAt_le_one F G 0 (Nat.zero_le 1),
    A.exactAt_of_forall_hom_exactAt _ 1 fun G =>
      A.moduleCechComplex_hom_exactAt_le_one F G 1 le_rfl,
    fun _ => ⟨fun k => A.exactAt_of_forall_hom_exactAt _ k fun G =>
        A.moduleCechComplex_hom_exactAt_of_injective F G k,
      A.moduleCechComplex_hom_exactAt_of_injective F⟩⟩

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
