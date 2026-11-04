module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ClosedPointsOfBaseChangeToPoint

/-!
# The product square of an open immersion over an extension of the base field

Let `L/K` be an extension of fields, `j : U ⟶ X` a quasi-compact quasi-separated morphism of
schemes over `K`, `Y` a scheme over `K` and `𝓕` an abelian sheaf on `U_étale` annihilated by an
integer `n` invertible in `K`. Base change to `L` gives `j_L : U_L ⟶ X_L`, `Y_L` and
`𝓕_L = 𝓕|_{U_L}`, and the product square
```
Y_L ×_L X_L  ←-h_L-  Y_L ×_L U_L
     |q_L                  |p_L
    X_L       ←-j_L-      U_L
```
over `L`. The proof of [Stacks, Tag 0F1H] says: *"The restriction of the map to
`(X ×_K Y)_{K^{sep}}` is the corresponding map for the diagram of the lemma base changed to
`K^{sep}`. Thus we may and do assume `K` is separably algebraically closed."* This file proves
that step, stalk by stalk, for any extension `L/K`.

Writing `π : Y_L ×_L X_L ⟶ Y ×_K X` for the projection, the inverse image along `π` of the base
change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible exactly when the base change map
`q_L⁻¹ R^i j_{L,*} 𝓕_L ⟶ R^i h_{L,*} p_L⁻¹ 𝓕_L` is, and the same holds after taking the stalk at
any geometric point of `Y_L ×_L X_L`. Both are read off the rectangle `Y_L ×_L U_L ⟶ U` over
`X`, pasted in two ways; the two auxiliary squares are base changes to `L` of `j` and of `h`,
whose base change maps are invertible by [Stacks, Tag 0F1C].

## Main results

* `Stacks.EtaleCohomology.OpenImmersionProductSquare.isIso_map_higherBaseChangeMapAb_extension_iff`
  — the comparison, after any functor.
* `Stacks.EtaleCohomology.OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_extension` —
  if the base change map over `L` is invertible, so is the one over `K`.
* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_extension_iff`
  — the comparison of stalks at a geometric point `w̄` of `Y_L ×_L X_L` and at its image in
  `Y ×_K X`.
* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_extension_of_not_isClosed`
  — invertibility on the stalks at the geometric points over non-closed points passes from `K`
  to `L`, for `X` and `Y` locally of finite type over `K`.

## Implementation notes

The base change maps of the two auxiliary squares are invertible on the bounded below derived
categories, by `Stacks.EtaleCohomology.FieldExtensionBaseChange.isIso_of_isPullback` with
[Stacks, Tag 0F09] discharged by `Stacks.EtaleCohomology.smoothLimitBaseChange_holds`. That
comparison, `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, is formed for the standard
model of the derived categories, which fixes the model in the proofs here; the statements involve
no derived category.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenImmersionProductSquare

attribute [local instance] HasDerivedCategory.standard

open FieldExtensionBaseChange

variable (K L : Type u) [Field K] [Field L] [Algebra K L] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) (hj : j ≫ sX = sU)

/-- The morphism `Spec L ⟶ Spec K` of an extension of fields. -/
abbrev extensionMap : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- The projection `π : Y_L ×_L S_L ⟶ Y ×_K S`, for `S_L = Spec L ×_K S` and
`Y_L = Spec L ×_K Y`. -/
abbrev extensionProdMap (S : Scheme.{u}) (sS : S ⟶ Spec (.of K)) :
    pullback (pullback.fst (extensionMap K L) sY) (pullback.fst (extensionMap K L) sS) ⟶
      pullback sY sS :=
  pullback.map _ _ sY sS (pullback.snd (extensionMap K L) sY) (pullback.snd (extensionMap K L) sS)
    (extensionMap K L) pullback.condition pullback.condition

/-- `Y_L ×_L S_L` is the fibre product of `Y ×_K S ⟶ S` and `S_L ⟶ S`. -/
theorem isPullback_extensionProdMap_snd (S : Scheme.{u}) (sS : S ⟶ Spec (.of K)) :
    IsPullback (extensionProdMap K L sY S sS)
      (pullback.snd (pullback.fst (extensionMap K L) sY) (pullback.fst (extensionMap K L) sS))
      (pullback.snd sY sS) (pullback.snd (extensionMap K L) sS) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback sY sS)
  have e : pullback.snd (extensionMap K L) sS ≫ sS =
      pullback.fst (extensionMap K L) sS ≫ extensionMap K L := pullback.condition.symm
  rw [pullback.lift_fst, e]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ sY).flip

/-- `Y_L ×_L S_L` is the base change `Spec L ×_K (Y ×_K S)`. -/
theorem isPullback_extensionProdMap (S : Scheme.{u}) (sS : S ⟶ Spec (.of K)) :
    IsPullback
      (pullback.snd (pullback.fst (extensionMap K L) sY) (pullback.fst (extensionMap K L) sS) ≫
        pullback.fst (extensionMap K L) sS)
      (extensionProdMap K L sY S sS) (extensionMap K L) (pullback.snd sY sS ≫ sS) :=
  ((isPullback_extensionProdMap_snd K L sY S sS).paste_vert
    (IsPullback.of_hasPullback (extensionMap K L) sS).flip).flip

/-- The base change `j_L : U_L ⟶ X_L` of `j` to `L`. -/
abbrev extensionOpen : pullback (extensionMap K L) sU ⟶ pullback (extensionMap K L) sX :=
  FieldExtensionBaseChange.baseChangeMap (extensionMap K L) sX sU j hj

/-- `j_L : U_L ⟶ X_L` is a morphism over `Spec L`. -/
theorem extensionOpen_fst :
    extensionOpen K L sX sU j hj ≫ pullback.fst (extensionMap K L) sX =
      pullback.fst (extensionMap K L) sU :=
  FieldExtensionBaseChange.baseChangeMap_fst _ _ _ _ _

/-- The projection `π` intertwines `h_L` and `h`. -/
theorem h_extensionProdMap :
    h (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
        (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
        (extensionOpen_fst K L sX sU j hj) ≫ extensionProdMap K L sY X sX =
      extensionProdMap K L sY U sU ≫ h sX sU sY j hj :=
  pullback.hom_ext (by simp [h]) (by simp [h])

variable {K L sX sU sY j hj} in
/-- **The comparison over an extension of the base field.** Let `L/K` be an extension of fields,
`j` quasi-compact and quasi-separated and `𝓕` annihilated by an integer `n` invertible in `K`.
After any functor `Φ`, the base change map `q_L⁻¹ R^i j_{L,*} 𝓕_L ⟶ R^i h_{L,*} p_L⁻¹ 𝓕_L` of
the base changed square is invertible exactly when the inverse image along
`π : Y_L ×_L X_L ⟶ Y ×_K X` of the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is. -/
theorem isIso_map_higherBaseChangeMapAb_extension_iff [QuasiCompact j] [QuasiSeparated j]
    (i : ℕ) (n : ℤ) (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (Opposite.op V)), n • x = 0) {C : Type*} [Category* C]
    (Φ : Sheaf (smallEtaleTopology (pullback (pullback.fst (extensionMap K L) sY)
      (pullback.fst (extensionMap K L) sX))) Ab.{u + 1} ⥤ C) :
    IsIso (Φ.map ((higherBaseChangeMapAb
        (q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sY))
        (extensionOpen K L sX sU j hj)
        (h (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj))
        (p (pullback.fst (extensionMap K L) sU) (pullback.fst (extensionMap K L) sY))
        (h_comp_q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj)) i).app
        ((smallEtalePullbackAb (pullback.snd (extensionMap K L) sU)).obj 𝓕))) ↔
      IsIso (Φ.map ((smallEtalePullbackAb (extensionProdMap K L sY X sX)).map
        ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
          (h_comp_q sX sU sY j hj) i).app 𝓕))) := by
  have hQC : QuasiCompact (h sX sU sY j hj) :=
    MorphismProperty.of_isPullback (isPullback sX sU sY j hj).flip ‹_›
  have hQS : QuasiSeparated (h sX sU sY j hj) :=
    MorphismProperty.of_isPullback (isPullback sX sU sY j hj).flip ‹_›
  have hprime : ∀ {V : Scheme.{u}} (G : Sheaf (smallEtaleTopology V) Ab.{u + 1}),
      (∀ (W : V.Etale) (x : G.obj.obj (Opposite.op W)), n • x = 0) → ∀ r : ℤ,
      Stacks.Torsion.IsPrimeToCharacteristicTorsion _ (ringExpChar K)
        ((DerivedCategory.Plus.homologyFunctor _ r).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) := fun G hG =>
    BaseChangeOverField.isPrimeToCharacteristicTorsion_homology_single G
      (BaseChangeOverField.isPrimeToCharacteristicTorsion_of_zsmul_eq_zero K hn G hG)
  have hlow : IsIso ((higherBaseChangeMapAb (pullback.snd (extensionMap K L) sX) j
      (extensionOpen K L sX sU j hj) (pullback.snd (extensionMap K L) sU)
      (FieldExtensionBaseChange.baseChangeMap_snd _ sX sU j hj) i).app 𝓕) :=
    isIso_higherBaseChangeMapAb_app_of_isIso_derived _ _ _ _ _ 𝓕
      (isIso_smallEtaleDerivedBaseChangeAb_baseChange K L sX sU j hj
        smoothLimitBaseChange_holds _ (hprime 𝓕 h𝓕)) i
  have hhg : h sX sU sY j hj ≫ pullback.snd sY sX ≫ sX = pullback.snd sY sU ≫ sU := by
    rw [← Category.assoc, h_comp_q, Category.assoc, hj]
  have hgq : h (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
        (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
        (extensionOpen_fst K L sX sU j hj) ≫
        pullback.snd (pullback.fst (extensionMap K L) sY) (pullback.fst (extensionMap K L) sX) ≫
          pullback.fst (extensionMap K L) sX =
      pullback.snd (pullback.fst (extensionMap K L) sY) (pullback.fst (extensionMap K L) sU) ≫
        pullback.fst (extensionMap K L) sU := by
    rw [← Category.assoc, h_comp_q, Category.assoc, extensionOpen_fst]
  have hup : IsIso ((higherBaseChangeMapAb (extensionProdMap K L sY X sX) (h sX sU sY j hj)
      (h (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
        (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
        (extensionOpen_fst K L sX sU j hj))
      (extensionProdMap K L sY U sU) (h_extensionProdMap K L sX sU sY j hj) i).app
      ((smallEtalePullbackAb (p sU sY)).obj 𝓕)) :=
    isIso_higherBaseChangeMapAb_app_of_isIso_derived _ _ _ _ _ _
      (isIso_of_isPullback K L (pullback.snd sY sX ≫ sX) (pullback.snd sY sU ≫ sU)
        (h sX sU sY j hj) hhg smoothLimitBaseChange_holds
        (isPullback_extensionProdMap K L sY X sX) (isPullback_extensionProdMap K L sY U sU)
        _ hgq (h_extensionProdMap K L sX sU sY j hj) _
        (hprime _ (SmoothBaseChange.zsmul_pullbackAb_eq_zero (p sU sY) 𝓕 n h𝓕))) i
  have h₁ : IsIso ((smallEtalePullbackAb (pullback.snd (pullback.fst (extensionMap K L) sY)
      (pullback.fst (extensionMap K L) sX))).map
      ((higherBaseChangeMapAb (pullback.snd (extensionMap K L) sX) j
        (extensionOpen K L sX sU j hj) (pullback.snd (extensionMap K L) sU)
        (FieldExtensionBaseChange.baseChangeMap_snd _ sX sU j hj) i).app 𝓕)) := inferInstance
  rw [← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_first j
    (extensionOpen K L sX sU j hj) _ (pullback.snd (extensionMap K L) sX) _
    (pullback.snd (extensionMap K L) sU) _ (FieldExtensionBaseChange.baseChangeMap_snd _ sX sU j hj)
    (h_comp_q _ _ _ _ _)
    i 𝓕 Φ h₁,
    ← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_second j (h sX sU sY j hj) _
    (q sX sY) (extensionProdMap K L sY X sX) (p sU sY) (extensionProdMap K L sY U sU)
    (h_comp_q sX sU sY j hj) (h_extensionProdMap K L sX sU sY j hj) i 𝓕 Φ hup]
  exact isIso_map_higherBaseChangeMapAb_app_congr j _ (by simp) (by simp) _ _ i 𝓕 Φ

/-- The morphism `Spec L ⟶ Spec K` of an extension of fields is surjective. -/
instance surjective_extensionMap : Surjective (extensionMap K L) :=
  ⟨fun _ ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- The projection `π : Y_L ×_L S_L ⟶ Y ×_K S` is surjective. -/
instance surjective_extensionProdMap (S : Scheme.{u}) (sS : S ⟶ Spec (.of K)) :
    Surjective (extensionProdMap K L sY S sS) :=
  MorphismProperty.of_isPullback (isPullback_extensionProdMap K L sY S sS) inferInstance

variable {K L sX sU sY j hj} in
/-- **"Thus we may and do assume `K` is separably algebraically closed"** ([Stacks, Tag 0F1H]),
for any extension `L/K`. If the base change map of the product square base changed to `L` is
invertible at `𝓕_L`, then `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible: its inverse image along
the surjection `π : Y_L ×_L X_L ⟶ Y ×_K X` is, and that inverse image reflects isomorphisms. -/
theorem isIso_higherBaseChangeMapAb_of_extension [QuasiCompact j] [QuasiSeparated j]
    (i : ℕ) (n : ℤ) (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (Opposite.op V)), n • x = 0)
    (H : IsIso ((higherBaseChangeMapAb
        (q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sY))
        (extensionOpen K L sX sU j hj)
        (h (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj))
        (p (pullback.fst (extensionMap K L) sU) (pullback.fst (extensionMap K L) sY))
        (h_comp_q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj)) i).app
        ((smallEtalePullbackAb (pullback.snd (extensionMap K L) sU)).obj 𝓕))) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) :=
  isIso_of_isIso_smallEtalePullbackAb_map (extensionProdMap K L sY X sX) _
    ((isIso_map_higherBaseChangeMapAb_extension_iff i n hn 𝓕 h𝓕 (𝟭 _)).1 H)

variable {K L sX sU sY j hj} in
/-- **The comparison over an extension of the base field, stalk by stalk.** In the situation of
`isIso_map_higherBaseChangeMapAb_extension_iff`, for a geometric point `w̄` of `Y_L ×_L X_L`, the
stalk at `w̄` of the base change map of the base changed square is invertible exactly when the
stalk of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` at the image geometric point `π(w̄)` is. -/
theorem isIso_stalk_higherBaseChangeMapAb_extension_iff [QuasiCompact j] [QuasiSeparated j]
    (i : ℕ) (n : ℤ) (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (Opposite.op V)), n • x = 0)
    (w : GeometricPoint (pullback (pullback.fst (extensionMap K L) sY)
      (pullback.fst (extensionMap K L) sX))) :
    IsIso ((smallEtaleStalkAb w.hom).map ((higherBaseChangeMapAb
        (q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sY))
        (extensionOpen K L sX sU j hj)
        (h (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj))
        (p (pullback.fst (extensionMap K L) sU) (pullback.fst (extensionMap K L) sY))
        (h_comp_q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj)) i).app
        ((smallEtalePullbackAb (pullback.snd (extensionMap K L) sU)).obj 𝓕))) ↔
      IsIso ((smallEtaleStalkAb (w.hom ≫ extensionProdMap K L sY X sX)).map
        ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
          (h_comp_q sX sU sY j hj) i).app 𝓕)) :=
  (isIso_map_higherBaseChangeMapAb_extension_iff i n hn 𝓕 h𝓕 (smallEtaleStalkAb w.hom)).trans
    (NatIso.isIso_map_iff (smallEtalePullbackStalkAbIso (extensionProdMap K L sY X sX) w.hom) _)

/-- A point of `Y_L ×_L X_L` over a closed point of `Y ×_K X` is closed, for `X` and `Y` locally of
finite type over `K`. -/
theorem isClosed_singleton_of_isClosed_extensionProdMap [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY]
    (w : ↥(pullback (pullback.fst (extensionMap K L) sY) (pullback.fst (extensionMap K L) sX)))
    (hw : IsClosed ({extensionProdMap K L sY X sX w} : Set ↥(pullback sY sX))) :
    IsClosed ({w} : Set _) := by
  obtain ⟨hY, hX⟩ := (isClosed_singleton_pullback_iff sY sX _).1 hw
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply] at hY
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply] at hX
  exact (isClosed_singleton_pullback_iff _ _ w).2
    ⟨isClosed_singleton_of_isClosed_singleton_snd _ sY _ hY,
      isClosed_singleton_of_isClosed_singleton_snd _ sX _ hX⟩

variable {K L sX sU sY j hj} in
/-- **Invertibility off the closed points passes to an extension of the base field.** Let `X` and
`Y` be locally of finite type over `K`, `j` quasi-compact and quasi-separated and `𝓕` annihilated
by an integer `n` invertible in `K`. If the stalks of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` are
invertible at the geometric points of `Y ×_K X` lying over non-closed points, then the stalks of
the base change map of the square base changed to `L` are invertible at the geometric points of
`Y_L ×_L X_L` lying over non-closed points. -/
theorem isIso_stalk_higherBaseChangeMapAb_extension_of_not_isClosed [QuasiCompact j]
    [QuasiSeparated j] [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (i : ℕ) (n : ℤ) (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (Opposite.op V)), n • x = 0)
    (H : ∀ z : GeometricPoint (pullback sY sX), ¬ IsClosed ({z.hom default} : Set _) →
      IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj)
        (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)))
    (w : GeometricPoint (pullback (pullback.fst (extensionMap K L) sY)
      (pullback.fst (extensionMap K L) sX)))
    (hw : ¬ IsClosed ({w.hom default} : Set _)) :
    IsIso ((smallEtaleStalkAb w.hom).map ((higherBaseChangeMapAb
        (q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sY))
        (extensionOpen K L sX sU j hj)
        (h (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj))
        (p (pullback.fst (extensionMap K L) sU) (pullback.fst (extensionMap K L) sY))
        (h_comp_q (pullback.fst (extensionMap K L) sX) (pullback.fst (extensionMap K L) sU)
          (pullback.fst (extensionMap K L) sY) (extensionOpen K L sX sU j hj)
          (extensionOpen_fst K L sX sU j hj)) i).app
        ((smallEtalePullbackAb (pullback.snd (extensionMap K L) sU)).obj 𝓕))) := by
  refine (isIso_stalk_higherBaseChangeMapAb_extension_iff i n hn 𝓕 h𝓕 w).2 ?_
  refine H ⟨w.residueField, w.hom ≫ extensionProdMap K L sY X sX⟩ fun hc => hw ?_
  refine isClosed_singleton_of_isClosed_extensionProdMap K L sX sY _ ?_
  rwa [Scheme.Hom.comp_apply] at hc

end Stacks.EtaleCohomology.OpenImmersionProductSquare

end
