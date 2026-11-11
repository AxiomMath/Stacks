module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalFirstOrderComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelReductionFaithful
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelFirstOrderBaseChange

/-!
# The reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG], assembled

`Crystalline.GlobalCrystallineSituation.SmallSite.LevelReduction07JG` is the datum the functor of
[Stacks, Lemma 60.17.3, Tag 07JG] is built from, and five of its eleven fields —
`thickeningRingHom`, `thickeningRingHom_p0`, `baseChange`, `baseChange_tmul` and `comparison_eq`
— were constructed nowhere.  The previous two modules built the ring map of a level and the base
change `(D + Omega) tensor Gamma(T_e, F) -> Gamma(T'_e, F)`, with its bijectivity.  **This module
assembles the datum**, and with it a term of `...SmallSite.Reduction07JG`, the bundle
[Stacks, Proposition 60.17.4, Tag 07JH] and [Stacks, Proposition 60.21.3, Tag 07LG] are stated
against.

The step that was missing between the two is the comparison datum of a crystal *at a single
level*, over `D` and the differentials.  `Crystalline.FirstOrderComparison` asks for a map out of
the sections of the level into their base change; the site offers the restriction of a section
along the second projection; and the base change being bijective is exactly what reads the second
as the first.  So `...SmallSite.LevelForms07JG.levelComparison` is the restriction along the
second projection read back through the base change, and its three clauses come out of three
normalisations: additivity of that restriction, the retraction of the diagonal by the first
projection, and the fact that the ring map of the level carries the second divided power section
of `D` to restriction along the second projection.  Its compatibility with the restrictions of the
system and its naturality in the crystal — the hypotheses `hc` and `hnat` of
`...SmallSite.levelComparison07JGOfLevelwise` — come out of the functoriality of the first-order
universal thickening of [Stacks, Tag 07J2], which this module transports from `CRIS(X/S)` to
`Cris(X/S)` as `...SmallSite.firstOrderThickeningCrysMap`.

On the limit module of the tag the base change is the one of the level after the level projection
of `Crystalline.levelTensorProj`, and the recipe of the tag — the field `comparison_eq` — is
`Crystalline.levelTensorProj_levelComparisonFun` combined with the defining property of
`...levelComparison`.

## Main definitions

* `...SmallSite.firstOrderThickeningCrysMap` — the functoriality of the first-order universal
  thickening on `Cris(X/S)`, with its two relations.
* `...SmallSite.crystalHomApp` — a morphism of crystals on the sections over an object.
* `...SmallSite.LevelForms07JG.levelComparison` — **the comparison datum of a crystal at a
  level**, over `D` and the module of differentials of the tag.
* `...SmallSite.LevelForms07JG.limitBaseChange` — the field
  `...SmallSite.LevelReduction07JG.baseChange` on the limit module.
* `...SmallSite.LevelBaseChangeData` — the two inputs the base change needs to be bijective at
  every level.
* `...SmallSite.levelReduction07JGOfLevelwise` — **the datum of [Stacks, Tag 07JG] over a system
  of levels**, all eleven fields supplied.
* `...SmallSite.reduction07JGWholeSpaceOfLevelwise` — **the same at the system of levels of
  [Stacks, Proposition 60.21.1, Tag 07JN]**, which is a term of `...SmallSite.Reduction07JG`.

## Main results

* `...SmallSite.LevelForms07JG.levelSectionsiota_levelBaseChange`,
  `...levelBaseChange_smul`, `...levelBaseChange_lTensor_levelRestrict` and
  `...levelBaseChange_lTensor_levelSectionsMap` — the four normalisations of the base change that
  the comparison datum of a level is checked against.
* `...SmallSite.LevelForms07JG.levelComparison_restrict` and `...levelComparison_naturality` —
  the hypotheses `hc` and `hnat` of `...SmallSite.levelComparison07JGOfLevelwise`, **proved**.
* `...SmallSite.LevelForms07JG.limitBaseChange_tmul` and
  `...limitBaseChange_comparisonOfLevels` — the fields `baseChange_tmul` and `comparison_eq`.
* `...SmallSite.nonempty_reduction07JG_of_levelwise` — the hypothesis bundle of
  [Stacks, Tag 07JH] is inhabited, from the inputs below.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module.**  [Stacks, Tag 07JG], [Stacks, Tag 07JH] and
[Stacks, Tag 07LG] are `...SmallSite.crystalPairFunctor`,
`...SmallSite.crystalPairFunctor_isEquivalence` and
`...SmallSite.crystalPairDeRhamDerivedPlusIso`, built directly from the whole-space
system of [Stacks, Tag 07JN] and not through the datum of this module. `Functor.IsEquivalence` of
the functor of this module is not mentioned below; by `...SmallSite.faithful_functor07JG_iff` even
its faithfulness is the faithfulness half of the conclusion of [Stacks, Tag 07JH], whose remaining
content is analysed in
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFaithfulSurjectivity.lean`.

What the assembled datum consumes is, in full:

1. `...SmallSite.LevelForms07JG`, the reduction of the module of differentials of the tag to the
   differentials of each level.  See the module documentation of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelThickeningRingHom.lean`.
2. `...SmallSite.LevelBaseChangeData.omegaBasis` with `omegaBasis_apply`, that those reductions
   present the differentials of each level as the base change along the reduction of `D`.  This is
   the hypothesis of the tensor identification; it needs a basis, and the basis carries
   `[Fintype iota]`, which is **not** removable: the module of differentials of
   [Stacks, Tag 07J9] is a completed direct sum, and on an infinite basis the interchange of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelComparisonInterchange.lean` is
   genuinely non-surjective.
3. `...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap`, bijectivity of the base
   change of scalars along the first projection at each level.  This is the affine content of
   [Stacks, Tag 07J6] and it is proved nowhere in the tree.
4. The source's two coefficient computations over `D(1)` and `D(2)` — `theta`, `thetaPow`,
   `hfam`, `hco`, `hfin` — which items (07JD) and (07JE) are derived from in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelComparisonTaylor.lean` and which
   were
   carried before this module too.

Item (07JB) is **not** carried at the system of [Stacks, Tag 07JN]: it is
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, with the shift
`N = Crystalline.uniformLevel (...affineSituation S hp)`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {ι : Type uI}

/-! ### The first-order universal thickening is functorial on `Cris(X/S)` -/

/-- **The morphism `T' ⟶ T₁'` of `Cris(X/S)` induced by a morphism `T ⟶ T₁`**, the functoriality
datum of [Stacks, Tag 07J2] read in the small crystalline category.  It is
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap`, the small category being
full. -/
def firstOrderThickeningCrysMap {B C : CrystallineThickening S} (f : B ⟶ C) :
    firstOrderThickeningCrysObject S B ⟶ firstOrderThickeningCrysObject S C :=
  ObjectProperty.homMk (firstOrderThickeningSiteMap ((CrystallineThickening.ι S).map f))

/-- **The functoriality datum commutes with the first projection**, in `Cris(X/S)`. -/
theorem firstOrderThickeningCrysMap_comp_P₀ {B C : CrystallineThickening S} (f : B ⟶ C) :
    firstOrderThickeningCrysMap f ≫ firstOrderThickeningCrysP₀ S C =
      firstOrderThickeningCrysP₀ S B ≫ f :=
  ObjectProperty.hom_ext _ (firstOrderThickeningSiteMap_comp_P₀ _)

/-- **The functoriality datum commutes with the second projection**, in `Cris(X/S)`. -/
theorem firstOrderThickeningCrysMap_comp_P₁ {B C : CrystallineThickening S} (f : B ⟶ C) :
    firstOrderThickeningCrysMap f ≫ firstOrderThickeningCrysP₁ S C =
      firstOrderThickeningCrysP₁ S B ≫ f :=
  ObjectProperty.hom_ext _ (firstOrderThickeningSiteMap_comp_P₁ _)

/-- Restricting a section along two composable morphisms only depends on their composite. -/
private theorem map_op_map_op_eq {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules R) {X Y Z W : C} {u : X ⟶ Y} {v : Y ⟶ W} {u' : X ⟶ Z} {v' : Z ⟶ W}
    (h : u ≫ v = u' ≫ v') (x : M.obj (op W)) :
    M.map u.op (M.map v.op x) = M.map u'.op (M.map v'.op x) := by
  rw [← M.map_comp_apply, ← M.map_comp_apply, ← op_comp, ← op_comp, h]

/-! ### The restrictions of the sections of a crystal over the thickenings of the levels -/

namespace LevelScalars07JG

variable (L : LevelScalars07JG S D) (F : QuasiCoherentCrystal S)

/-- **The restriction of sections along the second projection `p₁ : T'_e ⟶ T_e`.** -/
abbrev levelSectionsP₁ (e : ℕ) :
    L.levelSections F e →
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e))) :=
  F.obj.val.map (firstOrderThickeningCrysP₁ S (L.levelSystem.obj e)).op

/-- **The restriction of sections along the diagonal `i : T_e ⟶ T'_e`.** -/
abbrev levelSectionsι (e : ℕ) :
    F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e))) →
      L.levelSections F e :=
  F.obj.val.map (firstOrderThickeningCrysι S (L.levelSystem.obj e)).op

/-- **The restriction of sections along the step `T'_e ⟶ T'_{e + 1}`** of the system of
first-order thickenings of the levels. -/
abbrev firstOrderLevelRestrict (e : ℕ) :
    F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj (e + 1)))) →
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e))) :=
  F.obj.val.map
    (firstOrderThickeningCrysMap (L.levelSystem.map (homOfLE (Nat.le_succ e)))).op

/-- Restricting along `p₀` and then along the diagonal `i` is the identity on `Γ(T_e, ℱ)`. -/
theorem levelSectionsι_levelSectionsP₀ (e : ℕ) (x : L.levelSections F e) :
    L.levelSectionsι F e (L.levelSectionsP₀ F e x) = x :=
  map_crysι_crysP₀ F.obj.val (L.levelSystem.obj e) x

/-- Restricting along `p₁` and then along the diagonal `i` is the identity on `Γ(T_e, ℱ)`. -/
theorem levelSectionsι_levelSectionsP₁ (e : ℕ) (x : L.levelSections F e) :
    L.levelSectionsι F e (L.levelSectionsP₁ F e x) = x :=
  map_crysι_crysP₁ F.obj.val (L.levelSystem.obj e) x

/-- Restriction along the diagonal `i` maps `0` to `0`. -/
theorem levelSectionsι_zero (e : ℕ) :
    L.levelSectionsι F e 0 = 0 :=
  map_zero _

/-- Restriction along the diagonal `i` is additive. -/
theorem levelSectionsι_add (e : ℕ)
    (x y : F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))) :
    L.levelSectionsι F e (x + y) = L.levelSectionsι F e x + L.levelSectionsι F e y :=
  map_add _ x y

/-- Restriction along the step `T'_e ⟶ T'_{e + 1}` maps `0` to `0`. -/
theorem firstOrderLevelRestrict_zero (e : ℕ) :
    L.firstOrderLevelRestrict F e 0 = 0 :=
  map_zero _

/-- Restriction along the step `T'_e ⟶ T'_{e + 1}` is additive. -/
theorem firstOrderLevelRestrict_add (e : ℕ)
    (x y : F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj (e + 1))))) :
    L.firstOrderLevelRestrict F e (x + y) =
      L.firstOrderLevelRestrict F e x + L.firstOrderLevelRestrict F e y :=
  map_add _ x y

/-- Restriction along the second projection `p₁` is additive. -/
theorem levelSectionsP₁_add (e : ℕ) (x y : L.levelSections F e) :
    L.levelSectionsP₁ F e (x + y) = L.levelSectionsP₁ F e x + L.levelSectionsP₁ F e y :=
  map_add _ x y

/-- Restriction along the second projection `p₁` is semilinear for the restriction of scalars
along `p₁`. -/
theorem levelSectionsP₁_smul (e : ℕ) (a : crysSheafRing S (L.levelSystem.obj e).obj)
    (x : L.levelSections F e) :
    L.levelSectionsP₁ F e (a • x) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S (L.levelSystem.obj e).obj) a •
        L.levelSectionsP₁ F e x :=
  F.obj.val.map_smul (firstOrderThickeningCrysP₁ S (L.levelSystem.obj e)).op a x

/-- Restriction along the diagonal `i` is semilinear for the restriction of scalars along `i`. -/
theorem levelSectionsι_smul (e : ℕ)
    (t : crysSheafRing S (firstOrderThickeningObject S (L.levelSystem.obj e).obj))
    (x : F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))) :
    L.levelSectionsι F e (t • x) =
      crysSheafRingMap (firstOrderThickeningSiteι S (L.levelSystem.obj e).obj) t •
        L.levelSectionsι F e x :=
  F.obj.val.map_smul (firstOrderThickeningCrysι S (L.levelSystem.obj e)).op t x

/-- **Restriction along the step of the system of first-order thickenings commutes with `p₀`**,
by the relation `...SmallSite.firstOrderThickeningCrysMap_comp_P₀`. -/
theorem firstOrderLevelRestrict_levelSectionsP₀ (e : ℕ) (x : L.levelSections F (e + 1)) :
    L.firstOrderLevelRestrict F e (L.levelSectionsP₀ F (e + 1) x) =
      L.levelSectionsP₀ F e (L.levelRestrict F e x) :=
  map_op_map_op_eq F.obj.val
    (firstOrderThickeningCrysMap_comp_P₀ (L.levelSystem.map (homOfLE (Nat.le_succ e)))) x

/-- **Restriction along the step of the system of first-order thickenings commutes with `p₁`**,
by the relation `...SmallSite.firstOrderThickeningCrysMap_comp_P₁`. -/
theorem firstOrderLevelRestrict_levelSectionsP₁ (e : ℕ) (x : L.levelSections F (e + 1)) :
    L.firstOrderLevelRestrict F e (L.levelSectionsP₁ F (e + 1) x) =
      L.levelSectionsP₁ F e (L.levelRestrict F e x) :=
  map_op_map_op_eq F.obj.val
    (firstOrderThickeningCrysMap_comp_P₁ (L.levelSystem.map (homOfLE (Nat.le_succ e)))) x

/-- Restriction along the step `T'_e ⟶ T'_{e + 1}` is semilinear for the restriction of scalars
along that step. -/
theorem firstOrderLevelRestrict_smul (e : ℕ)
    (t : crysSheafRing S (firstOrderThickeningObject S (L.levelSystem.obj (e + 1)).obj))
    (x : F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj (e + 1))))) :
    L.firstOrderLevelRestrict F e (t • x) =
      crysSheafRingMap (firstOrderThickeningSiteMap (L.levelStep e)) t •
        L.firstOrderLevelRestrict F e x :=
  F.obj.val.map_smul
    (firstOrderThickeningCrysMap (L.levelSystem.map (homOfLE (Nat.le_succ e)))).op t x

end LevelScalars07JG

/-! ### A morphism of crystals on the sections over an object -/

/-- **A morphism of crystals read on the sections over an object of `Cris(X/S)`.**  This is the
component of the induced morphism of presheaves of modules; at a level it is
`...SmallSite.LevelScalars07JG.levelSectionsMap`. -/
abbrev crystalHomApp {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (B : CrystallineThickening S)
    (x : F.obj.val.obj (op B)) : G.obj.val.obj (op B) :=
  (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val (op B)).hom x

/-- The component of a morphism of crystals over an object is linear over the section ring of
that object. -/
theorem crystalHomApp_smul {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (B : CrystallineThickening S) (t : crysSheafRing S B.obj) (x : F.obj.val.obj (op B)) :
    crystalHomApp psi B (t • x) = t • crystalHomApp psi B x :=
  map_smul _ t x

/-- The component of a morphism of crystals over an object maps `0` to `0`. -/
theorem crystalHomApp_zero {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (B : CrystallineThickening S) : crystalHomApp psi B 0 = 0 :=
  map_zero _

/-- The component of a morphism of crystals over an object is additive. -/
theorem crystalHomApp_add {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (B : CrystallineThickening S) (x y : F.obj.val.obj (op B)) :
    crystalHomApp psi B (x + y) = crystalHomApp psi B x + crystalHomApp psi B y :=
  map_add _ x y

/-- The component of a morphism of crystals over a first-order thickening is linear over the
section ring of that thickening, written in the spelling the ring map of a level produces. -/
theorem crystalHomApp_smul_firstOrder {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (B : CrystallineThickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S B.obj))
    (x : F.obj.val.obj (op (firstOrderThickeningCrysObject S B))) :
    crystalHomApp psi (firstOrderThickeningCrysObject S B) (t • x) =
      t • crystalHomApp psi (firstOrderThickeningCrysObject S B) x :=
  map_smul _ t x

/-- The components of a morphism of crystals commute with restriction along a morphism `f : B ⟶ C`
of `Cris(X/S)`. -/
theorem crystalHomApp_naturality {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    {B C : CrystallineThickening S} (f : B ⟶ C) (x : F.obj.val.obj (op C)) :
    crystalHomApp psi B (F.obj.val.map f.op x) =
      G.obj.val.map f.op (crystalHomApp psi C x) :=
  PresheafOfModules.naturality_apply ((quasiCoherentCrystalι S).map psi).val f.op x

/-! ### The four properties of the base change that the comparison datum needs -/

namespace LevelForms07JG

variable {L : LevelScalars07JG S D} (R : LevelForms07JG S A D g Omega d L)

/-- **The base change over a level is semilinear for the ring map of the level**: the action of
`D ⊕ Ω` on `(D ⊕ Ω) ⊗_D Γ(T_e, ℱ)` is on the left factor, and the base change reads it through
`ψ_e`. -/
theorem levelBaseChange_smul (F : QuasiCoherentCrystal S) (e : ℕ)
    (b' : firstOrderExtension D Omega)
    (z : firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F e) :
    R.levelBaseChange F e (b' • z) =
      R.thickeningRingHom e b' • R.levelBaseChange F e z := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
      rw [TensorProduct.smul_tmul', R.levelBaseChange_tmul, R.levelBaseChange_tmul,
        smul_eq_mul, map_mul, smul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **Restricting the base change along the diagonal is the reduction modulo `Ω`.**  The square-
zero summand dies under `i` and `p₀` retracts it, so `i^*(ψ_e(b) · p₀^* m)` is the reduction of
`b` acting on `m`; this is what makes the comparison datum of the level reduce to the identity. -/
theorem levelSectionsι_levelBaseChange (F : QuasiCoherentCrystal S) (e : ℕ)
    (z : firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F e) :
    L.levelSectionsι F e (R.levelBaseChange F e z) =
      firstOrderReduction D Omega (L.levelSections F e) z := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
      rw [R.levelBaseChange_tmul, L.levelSectionsι_smul, R.thickeningRingHom_ι,
        L.levelSectionsι_levelSectionsP₀, firstOrderReduction_tmul]
      rfl
  | add x y hx hy => rw [map_add, L.levelSectionsι_add, hx, hy, map_add]

/-- **The base changes of the levels are compatible with the restrictions of the system**: the
base change at the level `e` of a restricted element is the restriction of the base change at the
level `e + 1`.  This uses the compatibility of the ring maps of the levels,
`...SmallSite.LevelForms07JG.thickeningRingHom_restrict`, and the relation
`...SmallSite.firstOrderThickeningCrysMap_comp_P₀`. -/
theorem levelBaseChange_lTensor_levelRestrict (F : QuasiCoherentCrystal S) (e : ℕ)
    (z : firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F (e + 1)) :
    R.levelBaseChange F e
        (LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) z) =
      L.firstOrderLevelRestrict F e (R.levelBaseChange F (e + 1) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b y =>
      rw [LinearMap.lTensor_tmul, R.levelBaseChange_tmul, R.levelBaseChange_tmul,
        L.firstOrderLevelRestrict_smul, R.thickeningRingHom_restrict,
        L.firstOrderLevelRestrict_levelSectionsP₀]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, L.firstOrderLevelRestrict_add, hx, hy]

/-- **The base changes are natural in the crystal.** -/
theorem levelBaseChange_lTensor_levelSectionsMap {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (e : ℕ) (z : firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F e) :
    R.levelBaseChange G e
        (LinearMap.lTensor (firstOrderExtension D Omega) (L.levelSectionsMap psi e) z) =
      crystalHomApp psi (firstOrderThickeningCrysObject S (L.levelSystem.obj e))
        (R.levelBaseChange F e z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
      rw [LinearMap.lTensor_tmul, R.levelBaseChange_tmul, R.levelBaseChange_tmul,
        crystalHomApp_smul_firstOrder]
      exact congrArg (fun y ↦ R.thickeningRingHom e b • y)
        (crystalHomApp_naturality psi (firstOrderThickeningCrysP₀ S (L.levelSystem.obj e)) m).symm
  | add x y hx hy => rw [map_add, map_add, map_add, crystalHomApp_add, hx, hy]

/-! ### The comparison datum of a crystal at a level -/

/-- The inverse of the base change over a level, where it is bijective. -/
def levelBaseChangeSymm (F : QuasiCoherentCrystal S) (e : ℕ)
    (hbij : Function.Bijective (R.levelBaseChange F e))
    (t : F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))) :
    firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F e :=
  (Equiv.ofBijective _ hbij).symm t

/-- The base change over a level applied to its inverse is the identity. -/
@[simp] theorem levelBaseChange_levelBaseChangeSymm (F : QuasiCoherentCrystal S) (e : ℕ)
    (hbij : Function.Bijective (R.levelBaseChange F e))
    (t : F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))) :
    R.levelBaseChange F e (R.levelBaseChangeSymm F e hbij t) = t :=
  (Equiv.ofBijective _ hbij).apply_symm_apply t

/-- **The first-order comparison datum of a crystal at a level**, over `D` and `Ω`: the
restriction `p₁^* s` of a section along the second projection, read inside the base change
`(D ⊕ Ω) ⊗_D Γ(T_e, ℱ)` through the bijection of
`...SmallSite.LevelForms07JG.bijective_levelBaseChange`.

This is the datum `Crystalline.FirstOrderComparison` at the single object `T_e`, which
`...SmallSite.levelComparison07JGOfLevelwise` consumes and which the tree had nowhere: the site
offers the comparison isomorphism `...SmallSite.firstOrderComparison` of sheaves of modules, and
reading it as a map into `(D ⊕ Ω) ⊗_D Γ(T_e, ℱ)` is exactly what the ring map of the level and
the tensor identification of the differentials supply.

The three clauses are checked by applying the base change, which is injective: additivity because
`p₁^*` is additive, reduction to the identity because `i^*` retracts both projections — this is
`...SmallSite.LevelForms07JG.levelSectionsι_levelBaseChange` — and semilinearity for `p₁` because
the ring map of the level carries `p₁ : D ⟶ D ⊕ Ω` to the restriction along the second
projection, which is `...SmallSite.LevelForms07JG.thickeningRingHom_p₁`. -/
def levelComparison (F : QuasiCoherentCrystal S) (e : ℕ)
    (hbij : Function.Bijective (R.levelBaseChange F e)) :
    FirstOrderComparison A D g Omega d (L.levelSections F e) where
  toFun s := R.levelBaseChangeSymm F e hbij (L.levelSectionsP₁ F e s)
  map_add' s s' := hbij.1 (by
    rw [map_add]
    simp only [R.levelBaseChange_levelBaseChangeSymm]
    rw [L.levelSectionsP₁_add])
  reduction' s := by
    rw [← R.levelSectionsι_levelBaseChange F e, R.levelBaseChange_levelBaseChangeSymm,
      L.levelSectionsι_levelSectionsP₁]
  semilinear' a s := hbij.1 (by
    rw [R.levelBaseChange_levelBaseChangeSymm, R.levelBaseChange_smul,
      R.levelBaseChange_levelBaseChangeSymm, R.thickeningRingHom_p₁,
      show (a • s : L.levelSections F e) = L.levelCrysRingHom e a • s from rfl,
      L.levelSectionsP₁_smul])

/-- **The comparison datum of a level is the one with the prescribed base change**, which is
what determines it. -/
@[simp] theorem levelBaseChange_levelComparison (F : QuasiCoherentCrystal S) (e : ℕ)
    (hbij : Function.Bijective (R.levelBaseChange F e)) (s : L.levelSections F e) :
    R.levelBaseChange F e (R.levelComparison F e hbij s) = L.levelSectionsP₁ F e s :=
  R.levelBaseChange_levelBaseChangeSymm F e hbij _

/-- **The comparison data of the levels are compatible with the restrictions of the system**,
which is the hypothesis `hc` of `...SmallSite.levelComparison07JGOfLevelwise`. -/
theorem levelComparison_restrict (F : QuasiCoherentCrystal S) (e : ℕ)
    (hbij : ∀ e : ℕ, Function.Bijective (R.levelBaseChange F e))
    (x : L.levelSections F (e + 1)) :
    LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e)
        (R.levelComparison F (e + 1) (hbij (e + 1)) x) =
      R.levelComparison F e (hbij e) (L.levelRestrict F e x) := by
  refine (hbij e).1 ?_
  rw [R.levelBaseChange_lTensor_levelRestrict, R.levelBaseChange_levelComparison,
    R.levelBaseChange_levelComparison, L.firstOrderLevelRestrict_levelSectionsP₁]

/-- **The comparison data of the levels are natural in the crystal**, which is the hypothesis
`hnat` of `...SmallSite.levelComparison07JGOfLevelwise`. -/
theorem levelComparison_naturality {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (e : ℕ)
    (hF : Function.Bijective (R.levelBaseChange F e))
    (hG : Function.Bijective (R.levelBaseChange G e)) (x : L.levelSections F e) :
    R.levelComparison G e hG (L.levelSectionsMap psi e x) =
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelSectionsMap psi e)
        (R.levelComparison F e hF x) := by
  refine hG.1 ?_
  rw [R.levelBaseChange_levelComparison, R.levelBaseChange_lTensor_levelSectionsMap,
    R.levelBaseChange_levelComparison]
  exact (crystalHomApp_naturality psi (firstOrderThickeningCrysP₁ S (L.levelSystem.obj e)) x).symm

/-! ### The base change on the limit module -/

/-- **The base change `(D ⊕ Ω) ⊗_D M ⟶ Γ(T'_e, ℱ)` on the limit module `M = lim_e Γ(T_e, ℱ)`**,
the field `...SmallSite.LevelReduction07JG.baseChange`: project the base change to the level `e`
and apply the base change over that level.  It is a map and not an identification, the base
change of the limit not being the limit of the base changes. -/
def limitBaseChange (F : QuasiCoherentCrystal S) (e : ℕ) :
    (firstOrderExtension D Omega ⊗[(D : Type u)] L.sections F) →+
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e))) :=
  (R.levelBaseChange F e).comp
    (levelTensorProj (L.sections F) (L.levelSections F) (L.levelRestrict F)
      (L.sectionsInvLimitEquiv F) e).toAddMonoidHom

/-- **The base change on the limit module on a pure tensor**: `b ⊗ m ↦ ψ_e(b) · p₀^* m_e`, which
is the field `...SmallSite.LevelReduction07JG.baseChange_tmul`. -/
theorem limitBaseChange_tmul (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : firstOrderExtension D Omega) (m : L.sections F) :
    R.limitBaseChange F e (b ⊗ₜ[(D : Type u)] m) =
      R.thickeningRingHom e b • L.levelSectionsP₀ F e ((L.sectionsEquiv F m).val e) := by
  change R.levelBaseChange F e
      (levelTensorProj (L.sections F) (L.levelSections F) (L.levelRestrict F)
        (L.sectionsInvLimitEquiv F) e (b ⊗ₜ[(D : Type u)] m)) = _
  rw [levelTensorProj_apply, LinearMap.lTensor_tmul, R.levelBaseChange_tmul]
  rfl

variable [Fintype ι]

/-- **The recipe of [Stacks, Tag 07JG] on the limit module**, the field
`...SmallSite.LevelReduction07JG.comparison_eq`: read at the level `e` inside the base change, the
comparison datum assembled from the levels is the restriction along the second projection.

It holds for any family of comparison data on the levels whose base change is `p₁^*`, which is
`...SmallSite.LevelForms07JG.levelBaseChange_levelComparison`; the passage from the levels to the
limit is `Crystalline.levelTensorProj_levelComparisonFun`. -/
theorem limitBaseChange_comparisonOfLevels (F : QuasiCoherentCrystal S) (e : ℕ)
    (c : ∀ e : ℕ, FirstOrderComparison A D g Omega d (L.levelSections F e))
    (hc : ∀ (e : ℕ) (x : L.levelSections F (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) (c (e + 1) x) =
        c e (L.levelRestrict F e x))
    (b : Module.Basis ι (D : Type u) Omega)
    (hcs : ∀ (e : ℕ) (x : L.levelSections F e),
      R.levelBaseChange F e (c e x) = L.levelSectionsP₁ F e x)
    (m : L.sections F) :
    R.limitBaseChange F e (L.comparisonOfLevels F c hc b m) =
      L.levelSectionsP₁ F e ((L.sectionsEquiv F m).val e) := by
  change R.levelBaseChange F e
      (levelTensorProj (L.sections F) (L.levelSections F) (L.levelRestrict F)
        (L.sectionsInvLimitEquiv F) e (L.comparisonOfLevels F c hc b m)) = _
  rw [show L.comparisonOfLevels F c hc b m =
      levelComparisonFun (L.sections F) (L.levelSections F) (L.levelRestrict F)
        (L.sectionsInvLimitEquiv F) c hc b m from rfl,
    levelTensorProj_levelComparisonFun, hcs]
  rfl

end LevelForms07JG

/-! ### The datum of [Stacks, Tag 07JG] over a system of levels -/

/-- **The two inputs the base change over the levels needs to be bijective.**

`omegaBasis` with `omegaBasis_apply` is the statement that the differentials of each level are the
base change of `Ω` — the tensor identification
`...SmallSite.LevelForms07JG.levelOmegaTensorEquiv` — and
`bijective_extensionSectionsMap` is bijectivity of the base change of scalars along `p₀` at each
level, the affine input of [Stacks, Tag 07J6], which **nothing in this module proves**. -/
structure LevelBaseChangeData {L : LevelScalars07JG S D} (R : LevelForms07JG S A D g Omega d L)
    (b : Module.Basis ι (D : Type u) Omega) where
  /-- A basis of the differentials of the level over its own section ring. -/
  omegaBasis : ∀ e : ℕ, Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
    (crysDiffSections (L.levelSystem.obj e).obj)
  /-- It is the image of the chosen basis of `Ω`, so the differentials of the level are the base
  change of `Ω`. -/
  omegaBasis_apply : ∀ (e : ℕ) (i : ι), omegaBasis e i = R.omegaMap e (b i)
  /-- **Carried.**  The base change of scalars along `p₀` at each level is bijective. -/
  bijective_extensionSectionsMap : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
    Function.Bijective (L.levelExtensionSectionsMap F e)

namespace LevelBaseChangeData

variable {L : LevelScalars07JG S D} {R : LevelForms07JG S A D g Omega d L}
  {b : Module.Basis ι (D : Type u) Omega}

/-- The base change over each level is bijective. -/
theorem bijective (E : LevelBaseChangeData R b) (F : QuasiCoherentCrystal S) (e : ℕ) :
    Function.Bijective (R.levelBaseChange F e) :=
  R.bijective_levelBaseChange F e b (E.omegaBasis e) (E.omegaBasis_apply e)
    (E.bijective_extensionSectionsMap F e)

/-- The comparison datum of a crystal at a level. -/
def comparison (E : LevelBaseChangeData R b) (F : QuasiCoherentCrystal S) (e : ℕ) :
    FirstOrderComparison A D g Omega d (L.levelSections F e) :=
  R.levelComparison F e (E.bijective F e)

/-- The base change of the comparison datum at a level is the restriction along the second
projection `p₁`. -/
theorem levelBaseChange_comparison (E : LevelBaseChangeData R b) (F : QuasiCoherentCrystal S)
    (e : ℕ) (x : L.levelSections F e) :
    R.levelBaseChange F e (E.comparison F e x) = L.levelSectionsP₁ F e x :=
  R.levelBaseChange_levelComparison F e (E.bijective F e) x

/-- The comparison data of the levels are compatible with the restrictions of the system. -/
theorem comparison_restrict (E : LevelBaseChangeData R b) (F : QuasiCoherentCrystal S) (e : ℕ)
    (x : L.levelSections F (e + 1)) :
    LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e)
        (E.comparison F (e + 1) x) =
      E.comparison F e (L.levelRestrict F e x) :=
  R.levelComparison_restrict F e (fun e ↦ E.bijective F e) x

/-- The comparison data of the levels are natural in the crystal. -/
theorem comparison_naturality (E : LevelBaseChangeData R b) {F G : QuasiCoherentCrystal S}
    (psi : F ⟶ G) (e : ℕ) (x : L.levelSections F e) :
    E.comparison G e (L.levelSectionsMap psi e x) =
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelSectionsMap psi e)
        (E.comparison F e x) :=
  R.levelComparison_naturality psi e (E.bijective F e) (E.bijective G e) x

end LevelBaseChangeData

variable {p : ℕ} {dx : ι → Omega} [Fintype ι]

/-- **The reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG] without its level condition,
assembled from the levels.**

All eleven fields of `...SmallSite.LevelReduction07JG` are supplied.  The six of
`...SmallSite.LevelComparison07JG` come from `...SmallSite.levelComparison07JGOfLevelwise`, whose
level-by-level comparison datum is now **constructed** — it is
`...SmallSite.LevelForms07JG.levelComparison`, the restriction along the second projection read
inside the base change — and the five that were constructed nowhere are:

* `thickeningRingHom` and `thickeningRingHom_p₀`, which are
  `...SmallSite.LevelForms07JG.thickeningRingHom` and its value on the `D` summand;
* `baseChange` and `baseChange_tmul`, which are
  `...SmallSite.LevelForms07JG.limitBaseChange` and its value on a pure tensor;
* `comparison_eq`, which is `...SmallSite.LevelForms07JG.limitBaseChange_comparisonOfLevels`.

What is consumed beyond the datum `...SmallSite.LevelForms07JG` of the differentials of the levels
is the record `...SmallSite.LevelBaseChangeData` — the tensor identification of those
differentials together with bijectivity of the base change of scalars at each level, which is
**not** proved anywhere in this module — the basis of `Ω` with `[Fintype ι]`, the source's two
coefficient computations `theta`, `thetaPow`, `hfam`, `hco`, `hfin`, and the annihilation `hann`
of item (07JB).

**No `@[stacks]` attribute is placed and neither [Stacks, Tag 07JG] nor
[Stacks, Proposition 60.17.4, Tag 07JH] is proved**: like `...SmallSite.PreReduction07JG` this
bundle says nothing about the system of levels, so no tag may be stated against it; narrowing it
to the source's own system is `...SmallSite.Reduction07JG.ofWholeSpaceSystem` applied to
`...SmallSite.LevelReduction07JG.toPreReduction07JG`. -/
def levelReduction07JGOfLevelwise {L : LevelScalars07JG S D}
    (R : LevelForms07JG S A D g Omega d L) {b : Module.Basis ι (D : Type u) Omega}
    (E : LevelBaseChangeData R b) (N : ℕ) (hdx : ∀ i, dx i = b i)
    (theta : ∀ F : QuasiCoherentCrystal S, ι → (L.sections F → L.sections F))
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily (L.sections F) (theta F) (thetaPow F))
    (hco : ∀ F : QuasiCoherentCrystal S, IsCoordinateExpansion p (D : Type u) Omega dx
      ((L.comparisonOfLevels F (E.comparison F) (E.comparison_restrict F)
        b).completedConnection p) (theta F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : L.sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite)
    (hann : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (x : L.levelSections F e),
      ((p : (D : Type u)) ^ (N + e)) • x = 0) :
    LevelReduction07JG S A D g Omega d p dx L where
  toLevelComparison07JG :=
    levelComparison07JGOfLevelwise L N (fun F ↦ E.comparison F)
      (fun F ↦ E.comparison_restrict F) (fun psi e x ↦ E.comparison_naturality psi e x) b hdx
      theta thetaPow hfam hco hfin hann
  thickeningRingHom e := R.thickeningRingHom e
  thickeningRingHom_p₀ e a := R.thickeningRingHom_p₀ e a
  baseChange F e := R.limitBaseChange F e
  baseChange_tmul F e b' m := R.limitBaseChange_tmul F e b' m
  comparison_eq F e m :=
    R.limitBaseChange_comparisonOfLevels F e (E.comparison F) (E.comparison_restrict F) b
      (fun e x ↦ E.levelBaseChange_comparison F e x) m

/-- **The datum of [Stacks, Tag 07JG] over a system of levels is inhabited**, from the inputs
listed in `...SmallSite.levelReduction07JGOfLevelwise`.  Stated as a nonemptiness so that the
inputs are visible as the hypotheses they are. -/
theorem nonempty_levelReduction07JG {L : LevelScalars07JG S D}
    (R : LevelForms07JG S A D g Omega d L) {b : Module.Basis ι (D : Type u) Omega}
    (E : LevelBaseChangeData R b) (N : ℕ) (hdx : ∀ i, dx i = b i)
    (theta : ∀ F : QuasiCoherentCrystal S, ι → (L.sections F → L.sections F))
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily (L.sections F) (theta F) (thetaPow F))
    (hco : ∀ F : QuasiCoherentCrystal S, IsCoordinateExpansion p (D : Type u) Omega dx
      ((L.comparisonOfLevels F (E.comparison F) (E.comparison_restrict F)
        b).completedConnection p) (theta F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : L.sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite)
    (hann : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (x : L.levelSections F e),
      ((p : (D : Type u)) ^ (N + e)) • x = 0) :
    Nonempty (LevelReduction07JG S A D g Omega d p dx L) :=
  ⟨levelReduction07JGOfLevelwise R E N hdx theta thetaPow hfam hco hfin hann⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### At the system of levels of [Stacks, Proposition 60.21.1, Tag 07JN] -/

universe uI'

section WholeSpace

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme] {A : Type u} [CommRing A]
  {g : A →+* (wholeSpaceSystemEnvelope hp 0).ring} {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp 0).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp 0).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp 0).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp 0).ring g Omega}
  {ι : Type uI'} [Fintype ι] {dx : ι → Omega}

/-- **The reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG] at the system of levels of
[Stacks, Proposition 60.21.1, Tag 07JN]**, which is the hypothesis bundle
[Stacks, Proposition 60.17.4, Tag 07JH] and [Stacks, Proposition 60.21.3, Tag 07LG] are stated
against.

The annihilation of item (07JB) is not a hypothesis here: it is
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, with the shift
`N = Crystalline.uniformLevel (...affineSituation S hp)`.  The system of levels is the
degree-zero member of `...SmallSite.wholeSpaceSystem` on the nose, so the field
`...SmallSite.Reduction07JG.levelSystem_isLevel` is discharged by the identity isomorphism and
**the bundle is no longer satisfied by anything degenerate**: by
`...SmallSite.levelSystem_obj_ne_botObject` no level of it is the empty object.

What it consumes is the datum `...SmallSite.LevelForms07JG` of the differentials of the levels,
the record `...SmallSite.LevelBaseChangeData` — whose field `bijective_extensionSectionsMap`,
bijectivity of the base change of scalars along `p₀` at each level, is **proved nowhere in this
module** — the basis of `Ω` on the chosen differentials with `[Fintype ι]`, and the source's two
coefficient computations.

**No `@[stacks]` attribute is placed**: this is a term of a bundle of hypotheses, and neither
[Stacks, Tag 07JH] nor [Stacks, Tag 07LG] is proved. -/
def reduction07JGWholeSpaceOfLevelwise
    (R : LevelForms07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d
      (wholeSpaceLevelScalars hp 0))
    {b : Module.Basis ι ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega}
    (E : LevelBaseChangeData R b) (hdx : ∀ i, dx i = b i)
    (theta : ∀ F : QuasiCoherentCrystal S, ι → ((wholeSpaceLevelScalars hp 0).sections F →
      (wholeSpaceLevelScalars hp 0).sections F))
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) →
      ((wholeSpaceLevelScalars hp 0).sections F → (wholeSpaceLevelScalars hp 0).sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily ((wholeSpaceLevelScalars hp 0).sections F) (theta F) (thetaPow F))
    (hco : ∀ F : QuasiCoherentCrystal S,
      IsCoordinateExpansion S.p ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega dx
        (((wholeSpaceLevelScalars hp 0).comparisonOfLevels F (E.comparison F)
          (E.comparison_restrict F) b).completedConnection S.p) (theta F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : (wholeSpaceLevelScalars hp 0).sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul S.p
        ((wholeSpaceSystemEnvelope hp 0).ring : Type u)
        ((wholeSpaceLevelScalars hp 0).sections F)}.Finite) :
    Reduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d S.p dx hp :=
  (levelReduction07JGOfLevelwise R E
      (_root_.Crystalline.uniformLevel (affineSituation S hp)) hdx theta thetaPow hfam hco hfin
      (fun F e ↦ pow_smul_eq_zero_wholeSpaceLevelSections hp 0 e F)).toReduction07JG rfl

/-- **The hypothesis bundle of [Stacks, Proposition 60.17.4, Tag 07JH] is inhabited**, from the
inputs of `...SmallSite.reduction07JGWholeSpaceOfLevelwise`.

This is the point of the whole construction: before it, the only inhabitant of the clauses of
[Stacks, Tag 07JG] anywhere was the degenerate datum `...SmallSite.preReduction07JGBot` over the
empty open of `X`, which `...SmallSite.not_levelSystem_isLevel_preReduction07JGBot` shows is
**not** a `...SmallSite.Reduction07JG`. -/
theorem nonempty_reduction07JG_of_levelwise
    (R : LevelForms07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d
      (wholeSpaceLevelScalars hp 0))
    {b : Module.Basis ι ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega}
    (E : LevelBaseChangeData R b) (hdx : ∀ i, dx i = b i)
    (theta : ∀ F : QuasiCoherentCrystal S, ι → ((wholeSpaceLevelScalars hp 0).sections F →
      (wholeSpaceLevelScalars hp 0).sections F))
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) →
      ((wholeSpaceLevelScalars hp 0).sections F → (wholeSpaceLevelScalars hp 0).sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily ((wholeSpaceLevelScalars hp 0).sections F) (theta F) (thetaPow F))
    (hco : ∀ F : QuasiCoherentCrystal S,
      IsCoordinateExpansion S.p ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega dx
        (((wholeSpaceLevelScalars hp 0).comparisonOfLevels F (E.comparison F)
          (E.comparison_restrict F) b).completedConnection S.p) (theta F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : (wholeSpaceLevelScalars hp 0).sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul S.p
        ((wholeSpaceSystemEnvelope hp 0).ring : Type u)
        ((wholeSpaceLevelScalars hp 0).sections F)}.Finite) :
    Nonempty (Reduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d S.p dx hp) :=
  ⟨reduction07JGWholeSpaceOfLevelwise hp R E hdx theta thetaPow hfam hco hfin⟩

end WholeSpace

end Crystalline.GlobalCrystallineSituation.SmallSite

end
