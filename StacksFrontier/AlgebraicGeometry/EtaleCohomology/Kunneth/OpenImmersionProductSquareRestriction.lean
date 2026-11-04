module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedInputs

/-!
# The base change map of the product square of an open immersion, restricted to étale pieces

Let `K` be a field, `j : U ⟶ X` a morphism of schemes over `K`, `Y` a scheme over `K` and `𝓕` an
abelian sheaf on `U_étale`. The proof of [Stacks, Tag 0F1H] studies the base change map
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` of the square
```
Y ×_K X  ←-h-  Y ×_K U
   |q              |p
   X     ←-j-      U
```
and says *"since it is enough to prove the isomorphism locally, we may assume `X` and `Y` are
affine"*, and later replaces `Y` by a scheme `Y'` containing it as an open subscheme. This file
proves the two facts behind those sentences.

* The base change map restricts correctly: for étale morphisms `X' ⟶ X` and `Y' ⟶ Y`, with
  `U' = X' ×_X U`, the inverse image of the base change map to `Y' ×_K X'` is invertible exactly
  when the base change map of the square of `j' : U' ⟶ X'` and `Y'` is.
* The base change map is invertible as soon as it is over the members of étale coverings of `X`
  and of `Y`, in particular over affine opens of `X` and of `Y`.

Every statement is made in one degree `i`, with the same degree in hypothesis and conclusion.

## Main results

* `Stacks.EtaleCohomology.isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_first` and
  `Stacks.EtaleCohomology.isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_second` — the two
  cancellations of the pasting law of the base change map, after any functor.
* `OpenImmersionProductSquare.isIso_map_higherBaseChangeMapAb_iff_of_etale_left`
  and its consequence `isIso_higherBaseChangeMapAb_of_etale_left` — restriction to `Y' ×_K X`
  along an étale `Y' ⟶ Y`.
* `OpenImmersionProductSquare.isIso_map_higherBaseChangeMapAb_iff_of_etale_right`
  and its consequence `isIso_higherBaseChangeMapAb_of_etale_right` — restriction to `Y ×_K X'`
  along an étale `X' ⟶ X`.
* `OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_etaleCover_left`
  and `OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_etaleCover_right` — locality on
  `Y` and on `X`.
* `OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_affineOpens` — *"we may assume `X`
  and `Y` are affine"*.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The two cancellations of the pasting law -/

section Paste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
  (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
  (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1})
  {C : Type*} [Category* C] (Φ : Sheaf (smallEtaleTopology S₂) Ab.{u + 1} ⥤ C)

/-- **Cancelling the first square of a pasting.** For two horizontally composable commutative
squares, if the inverse image along `u₂` of the degree-`q` base change map of the first square
is invertible at `F`, then, after any functor `Φ`, the base change map of the rectangle is
invertible at `F` exactly when that of the second square is invertible at the inverse image of
`F`. This is the pasting law `Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app`. -/
theorem isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_first
    (h₁ : IsIso ((smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F))) :
    IsIso (Φ.map ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
        (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F)) ↔
      IsIso (Φ.map ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app
        ((smallEtalePullbackAb v₁).obj F))) := by
  rw [higherBaseChangeMapAb_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F]
  simp only [Functor.map_comp]
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Cancelling the second square of a pasting.** For two horizontally composable commutative
squares, if the degree-`q` base change map of the second square is invertible at the inverse
image of `F`, then, after any functor `Φ`, the base change map of the rectangle is invertible at
`F` exactly when the inverse image along `u₂` of that of the first square is. -/
theorem isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_second
    (h₂ : IsIso ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F))) :
    IsIso (Φ.map ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
        (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F)) ↔
      IsIso (Φ.map ((smallEtalePullbackAb u₂).map
        ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F))) := by
  rw [higherBaseChangeMapAb_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F]
  simp only [Functor.map_comp]
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

/-- Invertibility of the base change map after a functor depends on the two inverse-image legs
of the square only through the morphisms themselves. -/
theorem isIso_map_higherBaseChangeMapAb_app_congr {X' Y S T : Scheme.{u}} {f₁ f₂ : X' ⟶ S}
    (g : T ⟶ S) (h : Y ⟶ X') {e₁ e₂ : Y ⟶ T} (hf : f₁ = f₂) (he : e₁ = e₂)
    (w₁ : h ≫ f₁ = e₁ ≫ g) (w₂ : h ≫ f₂ = e₂ ≫ g) (q : ℕ)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) {C : Type*} [Category* C]
    (Φ : Sheaf (smallEtaleTopology X') Ab.{u + 1} ⥤ C) :
    IsIso (Φ.map ((higherBaseChangeMapAb f₁ g h e₁ w₁ q).app G)) ↔
      IsIso (Φ.map ((higherBaseChangeMapAb f₂ g h e₂ w₂ q).app G)) := by
  subst hf he
  rfl

end Paste

namespace OpenImmersionProductSquare

variable {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) (hj : j ≫ sX = sU)

/-! ### Restriction along an étale morphism to `Y` -/

section Left

variable {Y' : Scheme.{u}} (b : Y' ⟶ Y)

/-- The morphism `b × id_X : Y' ×_K X ⟶ Y ×_K X` for `b : Y' ⟶ Y`. -/
abbrev leftMap (S : Scheme.{u}) (sS : S ⟶ Spec (.of K)) :
    pullback (b ≫ sY) sS ⟶ pullback sY sS :=
  pullback.map (b ≫ sY) sS sY sS b (𝟙 S) (𝟙 _) (by simp) (by simp)

/-- `Y' ×_K S` is the fibre product of `b : Y' ⟶ Y` and the first projection of `Y ×_K S`. -/
theorem isPullback_leftMap (S : Scheme.{u}) (sS : S ⟶ Spec (.of K)) :
    IsPullback (pullback.fst (b ≫ sY) sS) (leftMap sY b S sS) b (pullback.fst sY sS) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback sY sS)
  simpa using IsPullback.of_hasPullback (b ≫ sY) sS

/-- The square of `h` for `Y'` over the square of `h` for `Y` is cartesian. -/
theorem isPullback_h_leftMap :
    IsPullback (h sX sU (b ≫ sY) j hj) (leftMap sY b U sU) (leftMap sY b X sX)
      (h sX sU sY j hj) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback sX sU sY j hj)
  · simpa using isPullback sX sU (b ≫ sY) j hj
  · exact pullback.hom_ext (by simp [h]) (by simp [h])

variable [Etale b]

/-- For étale `b : Y' ⟶ Y`, the morphism `b × id_S : Y' ×_K S ⟶ Y ×_K S` is étale. -/
instance etale_leftMap (S : Scheme.{u}) (sS : S ⟶ Spec (.of K)) :
    Etale (leftMap sY b S sS) :=
  MorphismProperty.of_isPullback (isPullback_leftMap sY b S sS) ‹_›

/-- **Restriction along an étale `b : Y' ⟶ Y`.** The inverse image along
`b × id_X : Y' ×_K X ⟶ Y ×_K X` of the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is
invertible, after any functor `Φ`, exactly when the base change map of the square of `j` and `Y'`
is. The square of `b × id` over `h` is cartesian with étale legs, so its base change map is
invertible ([Stacks, Tag 0EZR]); the claim is then the pasting law. -/
theorem isIso_map_higherBaseChangeMapAb_iff_of_etale_left (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}) {C : Type*} [Category* C]
    (Φ : Sheaf (smallEtaleTopology (pullback (b ≫ sY) sX)) Ab.{u + 1} ⥤ C) :
    IsIso (Φ.map ((smallEtalePullbackAb (leftMap sY b X sX)).map
        ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
          (h_comp_q sX sU sY j hj) i).app 𝓕))) ↔
      IsIso (Φ.map ((higherBaseChangeMapAb (q sX (b ≫ sY)) j (h sX sU (b ≫ sY) j hj)
        (p sU (b ≫ sY)) (h_comp_q sX sU (b ≫ sY) j hj) i).app 𝓕)) := by
  have w₂ : h sX sU (b ≫ sY) j hj ≫ leftMap sY b X sX =
      leftMap sY b U sU ≫ h sX sU sY j hj := (isPullback_h_leftMap sX sU sY j hj b).w
  have h₂ := SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale
    SmoothBaseChange.etaleLocalHigherBaseChange (leftMap sY b X sX) (h sX sU (b ≫ sY) j hj)
    (leftMap sY b U sU) (h sX sU sY j hj) (isPullback_h_leftMap sX sU sY j hj b)
    ((smallEtalePullbackAb (p sU sY)).obj 𝓕) i
  rw [← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_second j (h sX sU sY j hj)
    (h sX sU (b ≫ sY) j hj) (q sX sY) (leftMap sY b X sX) (p sU sY) (leftMap sY b U sU)
    (h_comp_q sX sU sY j hj) w₂ i 𝓕 Φ h₂]
  exact isIso_map_higherBaseChangeMapAb_app_congr j _ (by simp) (by simp) _ _ i 𝓕 Φ

/-- **The base change map restricts along an étale `b : Y' ⟶ Y`**: if
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible for `Y`, it is invertible for `Y'`. -/
theorem isIso_higherBaseChangeMapAb_of_etale_left (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (H : IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕)) :
    IsIso ((higherBaseChangeMapAb (q sX (b ≫ sY)) j (h sX sU (b ≫ sY) j hj)
      (p sU (b ≫ sY)) (h_comp_q sX sU (b ≫ sY) j hj) i).app 𝓕) :=
  (isIso_map_higherBaseChangeMapAb_iff_of_etale_left sX sU sY j hj b i 𝓕 (𝟭 _)).1
    (inferInstanceAs (IsIso ((smallEtalePullbackAb (leftMap sY b X sX)).map _)))

/-- Invertibility of a component of a natural transformation at an abelian sheaf passes to its
inverse image along the identity. -/
theorem isIso_app_smallEtalePullbackAb_id_obj {U : Scheme.{u}} {C : Type*} [Category* C]
    {F G : Sheaf (smallEtaleTopology U) Ab.{u + 1} ⥤ C} (α : F ⟶ G)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}) (h : IsIso (α.app 𝓕)) :
    IsIso (α.app ((smallEtalePullbackAb (𝟙 U)).obj 𝓕)) :=
  (NatTrans.isIso_app_iff_of_iso α ((smallEtalePullbackAbIdOf (𝟙 U) rfl).app 𝓕)).2 h

/-- **Locality on `Y`**, with the hypothesis at the inverse image of `𝓕` along `𝟙 U`. Let
`{bₖ : Yₖ ⟶ Y}` be a jointly surjective family of étale morphisms. If the base change map of the
square of `j` and `Yₖ` is invertible at the inverse image of `𝓕` along `𝟙 U` for every `k`, then
the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` of the square of `j` and `Y` is invertible. -/
private theorem isIso_higherBaseChangeMapAb_of_etaleCover_left_aux {ι : Type*} {Y' : ι → Scheme.{u}}
    (b : ∀ k, Y' k ⟶ Y) [∀ k, Etale (b k)] (hb : ∀ y : Y, ∃ k, y ∈ Set.range (b k)) (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (H : ∀ k, IsIso ((higherBaseChangeMapAb (q sX (b k ≫ sY)) j (h sX sU (b k ≫ sY) j hj)
      (p sU (b k ≫ sY)) (h_comp_q sX sU (b k ≫ sY) j hj) i).app
        ((smallEtalePullbackAb (𝟙 U)).obj 𝓕))) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  have hcov : Presieve.ofArrows (fun k => pullback (b k ≫ sY) sX)
      (fun k => leftMap sY (b k) X sX) ∈ Scheme.etalePrecoverage (pullback sY sX) := by
    refine AlgebraicGeometry.ofArrows_mem_etalePrecoverage_iff.2
      ⟨fun z => ?_, fun k => inferInstance⟩
    obtain ⟨k, y, hy⟩ := hb (pullback.fst sY sX z)
    refine ⟨k, ?_⟩
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨y, hy⟩, ⟨pullback.snd sY sX z, rfl⟩⟩
  let D : EtaleLocalBaseChangeData Ab.{u + 1} :=
    { X := pullback sY sX, Y := pullback sY sU, S := X, T := U, f := q sX sY,
      h := h sX sU sY j hj, e := p sU sY, g := j, cartesian := isPullback sX sU sY j hj,
      I := ι, U := fun k => pullback (b k ≫ sY) sX, u := fun k => leftMap sY (b k) X sX,
      cover := hcov, V := fun _ => X, v := fun _ => 𝟙 X, etale_v := fun _ => inferInstance,
      f_i := fun k => q sX (b k ≫ sY), factorization := fun k => by simp,
      Y_i := fun k => pullback (b k ≫ sY) sU, h_i := fun k => h sX sU (b k ≫ sY) j hj,
      toY_i := fun k => leftMap sY (b k) U sU,
      upper_cartesian := fun k => isPullback_h_leftMap sX sU sY j hj (b k),
      T_i := fun _ => U, g_i := fun _ => j, toT_i := fun _ => 𝟙 U,
      lower_cartesian := fun _ => IsPullback.id_vert j,
      e_i := fun k => p sU (b k ≫ sY), e_i_compatible := fun k => by simp,
      local_cartesian := fun k => isPullback sX sU (b k ≫ sY) j hj, F := 𝓕 }
  exact isIso_higherBaseChangeMapAb_app_of_isIso_local D i H

/-- **Locality on `Y`.** Let `{bₖ : Yₖ ⟶ Y}` be a jointly surjective family of étale morphisms. If
the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` of the square of `j` and `Yₖ` is invertible
for every `k`, then so is the base change map of the square of `j` and `Y`. This is
[Stacks, Tag 0EZR] for the covering `{Yₖ ×_K X ⟶ Y ×_K X}`, whose local squares are the squares
of `j` and the `Yₖ`. -/
theorem isIso_higherBaseChangeMapAb_of_etaleCover_left {ι : Type*} {Y' : ι → Scheme.{u}}
    (b : ∀ k, Y' k ⟶ Y) [∀ k, Etale (b k)] (hb : ∀ y : Y, ∃ k, y ∈ Set.range (b k)) (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (H : ∀ k, IsIso ((higherBaseChangeMapAb (q sX (b k ≫ sY)) j (h sX sU (b k ≫ sY) j hj)
      (p sU (b k ≫ sY)) (h_comp_q sX sU (b k ≫ sY) j hj) i).app 𝓕)) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) :=
  isIso_higherBaseChangeMapAb_of_etaleCover_left_aux sX sU sY j hj b hb i 𝓕
    fun k => isIso_app_smallEtalePullbackAb_id_obj _ 𝓕 (H k)

end Left

/-! ### Restriction along an étale morphism to `X` -/

section Right

/-- The morphism `id_Y × a : Y ×_K S' ⟶ Y ×_K S` for `a : S' ⟶ S`. -/
abbrev rightMap {S S' : Scheme.{u}} (sS : S ⟶ Spec (.of K)) (a : S' ⟶ S) :
    pullback sY (a ≫ sS) ⟶ pullback sY sS :=
  pullback.map sY (a ≫ sS) sY sS (𝟙 Y) a (𝟙 _) (by simp) (by simp)

/-- `Y ×_K S'` is the fibre product of `a : S' ⟶ S` and the second projection of `Y ×_K S`. -/
theorem isPullback_rightMap {S S' : Scheme.{u}} (sS : S ⟶ Spec (.of K)) (a : S' ⟶ S) :
    IsPullback (pullback.snd sY (a ≫ sS)) (rightMap sY sS a) a (pullback.snd sY sS) := by
  refine (IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback sY sS)).flip
  simpa using IsPullback.of_hasPullback sY (a ≫ sS)

variable {X' U' : Scheme.{u}} (a : X' ⟶ X) (j' : U' ⟶ X') (c : U' ⟶ U)
  (hU : IsPullback j' c a j)

include hj hU in
/-- The structure morphisms of `U' = X' ×_X U` are compatible. -/
theorem comp_comp_eq : j' ≫ a ≫ sX = c ≫ sU := by
  rw [← Category.assoc, hU.w, Category.assoc, hj]

/-- The square of `h` for `j'` over the square of `h` for `j` is cartesian. -/
theorem isPullback_h_rightMap :
    IsPullback (h (a ≫ sX) (c ≫ sU) sY j' (comp_comp_eq sX sU j hj a j' c hU))
      (rightMap sY sU c) (rightMap sY sX a) (h sX sU sY j hj) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback sX sU sY j hj)
  · simpa using
      (isPullback (a ≫ sX) (c ≫ sU) sY j' (comp_comp_eq sX sU j hj a j' c hU)).paste_vert hU
  · exact pullback.hom_ext (by simp [h]) (by simp [h, hU.w])

variable [Etale a]

/-- For étale `a : S' ⟶ S`, the morphism `id_Y × a : Y ×_K S' ⟶ Y ×_K S` is étale. -/
instance etale_rightMap {S S' : Scheme.{u}} (sS : S ⟶ Spec (.of K)) (a : S' ⟶ S) [Etale a] :
    Etale (rightMap sY sS a) :=
  MorphismProperty.of_isPullback (isPullback_rightMap sY sS a) ‹_›

/-- **Restriction along an étale `a : X' ⟶ X`.** Let `U' = X' ×_X U`, with projections
`j' : U' ⟶ X'` and `c : U' ⟶ U`. The inverse image along `id_Y × a : Y ×_K X' ⟶ Y ×_K X` of the
base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible, after any functor `Φ`, exactly
when the base change map of the square of `j'` and `Y` is invertible at `c⁻¹ 𝓕`. Both are read off
the rectangle `Y ×_K U' ⟶ U'` over `X`, pasted in two ways from squares of which one is cartesian
with étale legs ([Stacks, Tag 0EZR]). -/
theorem isIso_map_higherBaseChangeMapAb_iff_of_etale_right (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}) {C : Type*} [Category* C]
    (Φ : Sheaf (smallEtaleTopology (pullback sY (a ≫ sX))) Ab.{u + 1} ⥤ C) :
    IsIso (Φ.map ((smallEtalePullbackAb (rightMap sY sX a)).map
        ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
          (h_comp_q sX sU sY j hj) i).app 𝓕))) ↔
      IsIso (Φ.map ((higherBaseChangeMapAb (q (a ≫ sX) sY) j'
        (h (a ≫ sX) (c ≫ sU) sY j' (comp_comp_eq sX sU j hj a j' c hU))
        (p (c ≫ sU) sY) (h_comp_q (a ≫ sX) (c ≫ sU) sY j'
          (comp_comp_eq sX sU j hj a j' c hU)) i).app ((smallEtalePullbackAb c).obj 𝓕))) := by
  have hj' := comp_comp_eq sX sU j hj a j' c hU
  have hup := isPullback_h_rightMap sX sU sY j hj a j' c hU
  have h₂ := SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale
    SmoothBaseChange.etaleLocalHigherBaseChange (rightMap sY sX a) (h (a ≫ sX) (c ≫ sU) sY j' hj')
    (rightMap sY sU c) (h sX sU sY j hj) hup ((smallEtalePullbackAb (p sU sY)).obj 𝓕) i
  have hlow := SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale
    SmoothBaseChange.etaleLocalHigherBaseChange a j' c j hU 𝓕 i
  have h₁ : IsIso ((smallEtalePullbackAb (q (a ≫ sX) sY)).map
      ((higherBaseChangeMapAb a j j' c hU.w i).app 𝓕)) := inferInstance
  rw [← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_second j (h sX sU sY j hj)
    (h (a ≫ sX) (c ≫ sU) sY j' hj') (q sX sY) (rightMap sY sX a) (p sU sY) (rightMap sY sU c)
    (h_comp_q sX sU sY j hj) hup.w i 𝓕 Φ h₂,
    ← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_first j j'
    (h (a ≫ sX) (c ≫ sU) sY j' hj') a (q (a ≫ sX) sY) c (p (c ≫ sU) sY) hU.w
    (h_comp_q (a ≫ sX) (c ≫ sU) sY j' hj') i 𝓕 Φ h₁]
  exact isIso_map_higherBaseChangeMapAb_app_congr j _ (by simp) (by simp) _ _ i 𝓕 Φ

/-- **The base change map restricts along an étale `a : X' ⟶ X`**: if
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible for `j`, then the base change map of the square of
`j' : U' = X' ×_X U ⟶ X'` and `Y` is invertible at the restriction of `𝓕` to `U'`. -/
theorem isIso_higherBaseChangeMapAb_of_etale_right (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (H : IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕)) :
    IsIso ((higherBaseChangeMapAb (q (a ≫ sX) sY) j'
        (h (a ≫ sX) (c ≫ sU) sY j' (comp_comp_eq sX sU j hj a j' c hU))
        (p (c ≫ sU) sY) (h_comp_q (a ≫ sX) (c ≫ sU) sY j'
          (comp_comp_eq sX sU j hj a j' c hU)) i).app ((smallEtalePullbackAb c).obj 𝓕)) :=
  (isIso_map_higherBaseChangeMapAb_iff_of_etale_right sX sU sY j hj a j' c hU i 𝓕 (𝟭 _)).1
    (inferInstanceAs (IsIso ((smallEtalePullbackAb (rightMap sY sX a)).map _)))

end Right

/-- **Locality on `X`.** Let `{aₖ : Xₖ ⟶ X}` be a jointly surjective family of étale morphisms,
and `Uₖ = Xₖ ×_X U` with projections `jₖ : Uₖ ⟶ Xₖ` and `cₖ : Uₖ ⟶ U`. If for every `k` the base
change map of the square of `jₖ` and `Y` is invertible at `cₖ⁻¹ 𝓕`, then the base change map
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible. This is [Stacks, Tag 0EZR] for the covering
`{Y ×_K Xₖ ⟶ Y ×_K X}`, whose local squares are the squares of the `jₖ` and `Y`. -/
theorem isIso_higherBaseChangeMapAb_of_etaleCover_right {ι : Type*} {X' U' : ι → Scheme.{u}}
    (a : ∀ k, X' k ⟶ X) [∀ k, Etale (a k)] (hcov : ∀ x : X, ∃ k, x ∈ Set.range (a k))
    (j' : ∀ k, U' k ⟶ X' k) (c : ∀ k, U' k ⟶ U) (hU : ∀ k, IsPullback (j' k) (c k) (a k) j)
    (i : ℕ) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (H : ∀ k, IsIso ((higherBaseChangeMapAb (q (a k ≫ sX) sY) (j' k)
        (h (a k ≫ sX) (c k ≫ sU) sY (j' k) (comp_comp_eq sX sU j hj (a k) (j' k) (c k) (hU k)))
        (p (c k ≫ sU) sY) (h_comp_q (a k ≫ sX) (c k ≫ sU) sY (j' k)
          (comp_comp_eq sX sU j hj (a k) (j' k) (c k) (hU k))) i).app
        ((smallEtalePullbackAb (c k)).obj 𝓕))) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  have hcov' : Presieve.ofArrows (fun k => pullback sY (a k ≫ sX))
      (fun k => rightMap sY sX (a k)) ∈ Scheme.etalePrecoverage (pullback sY sX) := by
    refine AlgebraicGeometry.ofArrows_mem_etalePrecoverage_iff.2
      ⟨fun z => ?_, fun k => inferInstance⟩
    obtain ⟨k, x, hx⟩ := hcov (pullback.snd sY sX z)
    refine ⟨k, ?_⟩
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨pullback.fst sY sX z, rfl⟩, ⟨x, hx⟩⟩
  let D : EtaleLocalBaseChangeData Ab.{u + 1} :=
    { X := pullback sY sX, Y := pullback sY sU, S := X, T := U, f := q sX sY,
      h := h sX sU sY j hj, e := p sU sY, g := j, cartesian := isPullback sX sU sY j hj,
      I := ι, U := fun k => pullback sY (a k ≫ sX), u := fun k => rightMap sY sX (a k),
      cover := hcov', V := X', v := a, etale_v := fun _ => inferInstance,
      f_i := fun k => q (a k ≫ sX) sY, factorization := fun k => by simp,
      Y_i := fun k => pullback sY (c k ≫ sU),
      h_i := fun k => h (a k ≫ sX) (c k ≫ sU) sY (j' k)
        (comp_comp_eq sX sU j hj (a k) (j' k) (c k) (hU k)),
      toY_i := fun k => rightMap sY sU (c k),
      upper_cartesian := fun k => isPullback_h_rightMap sX sU sY j hj (a k) (j' k) (c k) (hU k),
      T_i := U', g_i := j', toT_i := c, lower_cartesian := hU,
      e_i := fun k => p (c k ≫ sU) sY, e_i_compatible := fun k => by simp,
      local_cartesian := fun k => isPullback (a k ≫ sX) (c k ≫ sU) sY (j' k)
        (comp_comp_eq sX sU j hj (a k) (j' k) (c k) (hU k)), F := 𝓕 }
  exact isIso_higherBaseChangeMapAb_app_of_isIso_local D i H

/-- **"Since it is enough to prove the isomorphism locally, we may assume `X` and `Y` are
affine"** ([Stacks, Tag 0F1H]). If for every affine open `V ⊆ X` and every affine open `W ⊆ Y`
the base change map of the square of `j|_V : j⁻¹(V) ⟶ V` and `W` is invertible at the restriction
of `𝓕` to `j⁻¹(V)`, then the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible. -/
theorem isIso_higherBaseChangeMapAb_of_affineOpens (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (H : ∀ (V : X.affineOpens) (W : Y.affineOpens),
      IsIso ((higherBaseChangeMapAb (q ((V : X.Opens).ι ≫ sX) ((W : Y.Opens).ι ≫ sY))
        (j ∣_ (V : X.Opens))
        (h ((V : X.Opens).ι ≫ sX) ((j ⁻¹ᵁ (V : X.Opens)).ι ≫ sU) ((W : Y.Opens).ι ≫ sY)
          (j ∣_ (V : X.Opens)) (comp_comp_eq sX sU j hj _ _ _
            (isPullback_morphismRestrict j (V : X.Opens))))
        (p ((j ⁻¹ᵁ (V : X.Opens)).ι ≫ sU) ((W : Y.Opens).ι ≫ sY))
        (h_comp_q ((V : X.Opens).ι ≫ sX) ((j ⁻¹ᵁ (V : X.Opens)).ι ≫ sU) ((W : Y.Opens).ι ≫ sY)
          (j ∣_ (V : X.Opens)) (comp_comp_eq sX sU j hj _ _ _
            (isPullback_morphismRestrict j (V : X.Opens)))) i).app
        ((smallEtalePullbackAb (j ⁻¹ᵁ (V : X.Opens)).ι).obj 𝓕))) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  refine isIso_higherBaseChangeMapAb_of_etaleCover_right sX sU sY j hj
    (fun V : X.affineOpens => (V : X.Opens).ι) (fun x => ?_) (fun V => j ∣_ (V : X.Opens))
    (fun V => (j ⁻¹ᵁ (V : X.Opens)).ι) (fun V => isPullback_morphismRestrict j (V : X.Opens)) i 𝓕
    fun V => ?_
  · obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨⟨V, hV⟩, by rwa [Scheme.Opens.range_ι]⟩
  · refine isIso_higherBaseChangeMapAb_of_etaleCover_left _ _ sY _ _
      (fun W : Y.affineOpens => (W : Y.Opens).ι) (fun y => ?_) i _ fun W => H V W
    obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top y)
    exact ⟨⟨W, hW⟩, by rwa [Scheme.Opens.range_ι]⟩

end OpenImmersionProductSquare

end Stacks.EtaleCohomology

end
