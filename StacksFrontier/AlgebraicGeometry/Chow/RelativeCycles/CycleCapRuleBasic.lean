module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRule

/-!
# Elementary properties of rules compatible with pushforward, pullback and Gysin maps

Let `c` be a rule as in Stacks 0H6G (`Stacks.Chow.CompatibleCycleCapRule`), or only one compatible
with proper pushforward and flat pullback (`Stacks.Chow.CycleCapRule`). This file records the
special cases of the compatibilities which are used to compute the coefficients of `c ∩ β`:

* restriction to an open subscheme of a test scheme, the case of an open immersion of the flat
  compatibility;
* pushforward along a closed immersion of test schemes, the case of a closed immersion of the
  proper compatibility;
* independence of the presentation of a test scheme: equal morphisms to `Y` give the same
  coefficients;
* the Gysin compatibility read in `X' = T ×_Y X`, that is, after pushing forward along the zero
  schemes.

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {p : X ⟶ Y} [LocallyOfFiniteType p] {r : ℕ}

namespace CycleCapRule

variable (c : CycleCapRule C sY p r)

/-- **Restriction to an open subscheme of a test scheme.** For an open immersion `o : V ⟶ T`, the
coefficients of `c ∩ β|_V` are those of `c ∩ β` at the corresponding points of `T ×_Y X`. This is
the flat compatibility along `o`, which is flat of relative dimension zero. -/
theorem cap_cycleGroupRestrict_apply {T V : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (o : V ⟶ T) [IsOpenImmersion o] (e : ℤ) (β : CycleGroup C (g ≫ sY) e)
    (w : ↥(pullback p (o ≫ g))) :
    (c.cap (o ≫ g) e (cycleGroupRestrict C (g ≫ sY) ((o ≫ g) ≫ sY) o
        (Category.assoc o g sY).symm e β)).1 w =
      (c.cap g e β).1 ((bivariantBaseChangeMap p g o).base w) := by
  have hd := relativeDimension_of_isOpenImmersion o
  have : IsOpenImmersion (bivariantBaseChangeMap p g o) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g o)
      (P := @IsOpenImmersion) inferInstance
  have h := c.cap_flatPullback g o 0 hd e β
  rw [c.cap_val_congr (o ≫ g) (by simp : e = e + ((0 : ℕ) : ℤ)) _
    (flatPullback C ((o ≫ g) ≫ sY) (g ≫ sY) o (Category.assoc o g sY).symm 0 hd e β)
    (cycleGroupRestrict_eq_flatPullback C _ _ o _ hd e β), h]
  have h' := cycleGroupRestrict_eq_flatPullback C (pullback.fst p g ≫ p ≫ sY)
    (pullback.fst p (o ≫ g) ≫ p ≫ sY) (bivariantBaseChangeMap p g o)
    (bivariantBaseChangeMap_comp_structure sY p g o)
    (relativeDimension_of_isOpenImmersion _) ((r : ℤ) + e) (c.cap g e β)
  rw [← h', cycleGroupRestrict_apply]

/-- **Pushforward along a closed immersion of test schemes.** For a closed immersion
`i : Z ⟶ T`, the coefficient of `c ∩ i_*β` at the image of a point of `Z ×_Y X` is the coefficient
of `c ∩ β` there. -/
theorem cap_properPushforward_apply {T Z : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (i : Z ⟶ T) [IsClosedImmersion i] (e : ℤ) (β : CycleGroup C ((i ≫ g) ≫ sY) e)
    (z : ↥(pullback p (i ≫ g))) :
    (c.cap g e (properPushforward C ((i ≫ g) ≫ sY) (g ≫ sY) i (Category.assoc i g sY).symm e
        β)).1 ((bivariantBaseChangeMap p g i).base z) = (c.cap (i ≫ g) e β).1 z := by
  rw [← c.properPushforward_cap g i e β]
  exact properPushforward_apply_image_of_isClosedImmersion C _ _ _ _ _ _ z

/-- Away from the image of `Z ×_Y X` the cycle `c ∩ i_*β` vanishes, for a closed immersion
`i : Z ⟶ T`. -/
theorem cap_properPushforward_apply_eq_zero {T Z : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (i : Z ⟶ T) [IsClosedImmersion i] (e : ℤ)
    (β : CycleGroup C ((i ≫ g) ≫ sY) e) (w : ↥(pullback p g))
    (hw : w ∉ Set.range (bivariantBaseChangeMap p g i).base) :
    (c.cap g e (properPushforward C ((i ≫ g) ≫ sY) (g ≫ sY) i (Category.assoc i g sY).symm e
        β)).1 w = 0 := by
  rw [← c.properPushforward_cap g i e β, properPushforward_apply_of_isClosedImmersion]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun z hz ↦ absurd ⟨z, hz⟩ hw

/-- **Independence of the presentation of a test scheme.** Two equal morphisms `g₁ = g₂ : T ⟶ Y`
give the same coefficients, read through the induced identification of the base changes. -/
theorem cap_congr_hom {T : Scheme.{u}} {g₁ g₂ : T ⟶ Y} [LocallyOfFiniteType g₁]
    [LocallyOfFiniteType g₂] (h : g₁ = g₂) (e : ℤ) (β₁ : CycleGroup C (g₁ ≫ sY) e)
    (β₂ : CycleGroup C (g₂ ≫ sY) e) (hβ : β₁.1 = β₂.1) (x : ↥(pullback p g₁)) :
    (c.cap g₁ e β₁).1 x = (c.cap g₂ e β₂).1 ((pullback.congrHom rfl h).hom.base x) := by
  subst h
  rw [Subtype.ext hβ]
  simp

end CycleCapRule

namespace CompatibleCycleCapRule

variable (c : CompatibleCycleCapRule C sY p r)

/-- **The Gysin compatibility read in `X' = T ×_Y X`.** For an invertible module `L` on a test
scheme `T` and a section `s` whose zero scheme carries a trivial restriction of `L`,
`c ∩ i_* i^* β = j_* j^*(c ∩ β)` as cycles on `T ×_Y X`. -/
theorem cap_gysinCycleMapPushforward {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (e : ℤ) (β : CycleGroup C (g ≫ sY) (e + 1)) :
    c.cap g e (gysinCycleMapPushforward C (g ≫ sY) e L s htriv β) =
      gysinCycleMapPushforward C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e)
        (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s)
        (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
          (pullback.snd p g) L s htriv)
        (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm (c.cap g (e + 1) β)) := by
  rw [← properPushforward_gysinCycleMapAlong_eq C (g ≫ sY) e L s htriv
      (Stacks.Divisors.zeroScheme T L s).subschemeι
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) (Category.assoc _ g sY).symm
      (Scheme.IdealSheafData.ker_subschemeι _) β,
    ← c.properPushforward_cap, c.cap_gysin,
    properPushforward_gysinCycleMapAlong_eq]

end CompatibleCycleCapRule

end Stacks.Chow

end
