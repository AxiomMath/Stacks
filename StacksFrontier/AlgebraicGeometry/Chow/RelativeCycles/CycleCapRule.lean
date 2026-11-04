module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RelativeCycleBivariant

/-!
# Operations on cycles compatible with proper pushforward, flat pullback and Gysin maps

Let `(S, δ)` be as in Section 0H65 of the Stacks Project, let `p : X ⟶ Y` be a morphism of
schemes locally of finite type over `S` and let `r ≥ 0`. Stacks 0H6G considers a rule `c`
that to every morphism `g : Y' ⟶ Y` locally of finite type and every `e ∈ ℤ` associates an
operation

  `c ∩ - : Z_e(Y') ⟶ Z_{r + e}(X')`,   `X' = Y' ×_Y X`,

compatible with proper pushforward, flat pullback, and Gysin maps as in Lemma 0H6E. This file
makes that hypothesis precise as the structure `Stacks.Chow.CompatibleCycleCapRule`, and records
that the rule `g ↦ g^*α ∩ -` of a relative `r`-cycle `α` is one (Lemmas 0H6B, 0H68, 0H6E).

## Main definitions

* `Stacks.Chow.CompatibleCycleCapRule` — the rules of Stacks 0H6G.
* `Stacks.Chow.relativeCycleCompatibleRule` — the rule `g ↦ g^*α ∩ -` of a relative cycle.

## Implementation notes

The base change `X' = Y' ×_Y X` is the chosen fibre product `pullback p g`, over the base through
`pullback.fst p g ≫ p ≫ sY`, which is the spelling of `Stacks.Chow.relativeCycleCap`. A morphism
`h : Y'' ⟶ Y'` of test schemes induces the canonical map `bivariantBaseChangeMap p g h` of base
changes, and the three compatibilities are stated along it:

* proper pushforward, for `h` proper (Lemma 0H6B);
* flat pullback, for `h` flat of relative dimension `d` (Lemma 0H68); the two degrees
  `r + (e + d)` and `(r + e) + d` are equal integers, not equal terms, so the compatibility is an
  equality of underlying cycles;
* Gysin maps (Lemma 0H6E): for an invertible module `L` on `Y'` and a section `s` whose zero
  scheme `D` carries a trivial restriction of `L`, `c ∩ i^*β = j^*(c ∩ β)`, where `i^*` and `j^*`
  are the Gysin maps on cycles of Chow Homology, Remark 0B6Z, and `j` presents the zero scheme of
  the pulled-back section on `X'` by the base change of `D ⟶ Y'`
  (`Stacks.Chow.ker_bivariantBaseChangeMap_subschemeι`).

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
* [Stacks Project, Tag 0H6E](https://stacks.math.columbia.edu/tag/0H6E)
* [Stacks Project, Tag 0H6B](https://stacks.math.columbia.edu/tag/0H6B)
* [Stacks Project, Tag 0H68](https://stacks.math.columbia.edu/tag/0H68)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The canonical map `T' ×_Y X ⟶ T ×_Y X` is the pasting isomorphism followed by the first
projection of `(T ×_Y X) ×_T T'`. -/
theorem pullbackLeftPullbackSndIso_inv_fst_eq_bivariantBaseChangeMap {X Y T T' : Scheme.{u}}
    (p : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T) :
    (pullbackLeftPullbackSndIso p g h).inv ≫ pullback.fst (pullback.snd p g) h =
      bivariantBaseChangeMap p g h := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst, bivariantBaseChangeMap_fst]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
      (isPullback_bivariantBaseChangeMap p g h).w]

/-- **Stacks 0B6Y for the base change of the zero scheme.** The canonical map
`D ×_Y X ⟶ T ×_Y X` induced by the closed immersion of the zero scheme `D` of a section `s` of an
invertible module on `T` cuts out the zero scheme of the pulled-back section. -/
theorem ker_bivariantBaseChangeMap_subschemeι {X Y T : Scheme.{u}} (p : X ⟶ Y) (g : T ⟶ Y)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (bivariantBaseChangeMap p g (Stacks.Divisors.zeroScheme T L s).subschemeι).ker =
      bivariantPullbackZeroScheme p g L s := by
  rw [← pullbackLeftPullbackSndIso_inv_fst_eq_bivariantBaseChangeMap,
    Scheme.Hom.ker_comp_of_isIso]
  exact (Stacks.Divisors.zeroScheme_pullback (pullback.snd p g) L s).symm

/-- The canonical map `T' ×_Y X ⟶ T ×_Y X` is a morphism over the base. -/
theorem bivariantBaseChangeMap_comp_structure {X Y T T' : Scheme.{u}} {S : Scheme.{u}}
    (sY : Y ⟶ S) (p : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T) :
    bivariantBaseChangeMap p g h ≫ pullback.fst p g ≫ p ≫ sY =
      pullback.fst p (h ≫ g) ≫ p ≫ sY := by
  rw [← Category.assoc, bivariantBaseChangeMap_fst]

section Rule

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ)

/-- A rule `c` that to every morphism `g : Y' ⟶ Y` locally of finite type and every `e ∈ ℤ`
associates an operation `c ∩ - : Z_e(Y') ⟶ Z_{r + e}(X')`, where `X' = Y' ×_Y X`, compatible with
proper pushforward and flat pullback. The Gysin compatibility of Stacks 0H6G is added by
`Stacks.Chow.CompatibleCycleCapRule`. -/
structure CycleCapRule : Type (u + 1) where
  /-- The operation `c ∩ - : Z_e(Y') ⟶ Z_{r + e}(Y' ×_Y X)` on the cycles of a test scheme. -/
  cap : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ),
    CycleGroup C (g ≫ sY) e →+ CycleGroup C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e)
  /-- Compatibility with proper pushforward (Lemma 0H6B): for a proper morphism `h : T' ⟶ T` of
  test schemes, `h'_*(c ∩ β) = c ∩ h_*β`, where `h' : T' ×_Y X ⟶ T ×_Y X` is its base change. -/
  properPushforward_cap : ∀ {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [IsProper h] (e : ℤ) (β : CycleGroup C ((h ≫ g) ≫ sY) e),
    properPushforward C (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY)
        (bivariantBaseChangeMap p g h) (bivariantBaseChangeMap_comp_structure sY p g h)
        ((r : ℤ) + e) (cap (h ≫ g) e β) =
      cap g e (properPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (Category.assoc h g sY).symm e β)
  /-- Compatibility with flat pullback (Lemma 0H68): for a morphism `h : T' ⟶ T` of test schemes
  which is flat of relative dimension `d`, `c ∩ h^*β = h'^*(c ∩ β)`, where
  `h' : T' ×_Y X ⟶ T ×_Y X` is its base change. -/
  cap_flatPullback : ∀ {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension h d) (e : ℤ) (β : CycleGroup C (g ≫ sY) e),
    letI : LocallyOfFiniteType (bivariantBaseChangeMap p g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g h)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (bivariantBaseChangeMap p g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g h) (P := @Flat)
        inferInstance
    (cap (h ≫ g) (e + d)
        (flatPullback C ((h ≫ g) ≫ sY) (g ≫ sY) h (Category.assoc h g sY).symm d hd e β)).1 =
      (flatPullback C (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY)
        (bivariantBaseChangeMap p g h) (bivariantBaseChangeMap_comp_structure sY p g h) d
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap p g h) hd)
        ((r : ℤ) + e) (cap g e β)).1
/-- **The hypothesis of Stacks 0H6G.** A rule `c` that to every morphism `g : Y' ⟶ Y` locally of
finite type and every `e ∈ ℤ` associates an operation `c ∩ - : Z_e(Y') ⟶ Z_{r + e}(X')`, where
`X' = Y' ×_Y X`, compatible with proper pushforward, flat pullback, and Gysin maps as in
Lemma 0H6E. See the module documentation for the reading of the three compatibilities. -/
structure CompatibleCycleCapRule extends CycleCapRule C sY p r where
  /-- Compatibility with Gysin maps (Lemma 0H6E): for an invertible module `L` on a test scheme
  `T` and a section `s` whose zero scheme `D` carries a trivial restriction of `L`,
  `c ∩ i^*β = j^*(c ∩ β)`, where `i^* : Z_{e+1}(T) ⟶ Z_e(D)` and
  `j^* : Z_{r+e+1}(T ×_Y X) ⟶ Z_{r+e}(D ×_Y X)` are the Gysin maps on cycles of Remark 0B6Z, the
  latter read along the base change `D ×_Y X ⟶ T ×_Y X`, which cuts out the zero scheme of the
  pulled-back section. -/
  cap_gysin : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (e : ℤ) (β : CycleGroup C (g ≫ sY) (e + 1)),
    cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) e
        (gysinCycleMapAlong C (g ≫ sY) (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY)
          e L s (Stacks.Divisors.zeroScheme T L s).subschemeι htriv
          (Category.assoc _ g sY).symm (Scheme.IdealSheafData.ker_subschemeι _) β) =
      gysinCycleMapAlong C (pullback.fst p g ≫ p ≫ sY)
        (pullback.fst p ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ p ≫ sY)
        ((r : ℤ) + e) (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s)
        (bivariantBaseChangeMap p g (Stacks.Divisors.zeroScheme T L s).subschemeι)
        (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
          (pullback.snd p g) L s htriv)
        (bivariantBaseChangeMap_comp_structure sY p g _)
        (ker_bivariantBaseChangeMap_subschemeι p g L s)
        (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm (cap g (e + 1) β))

variable {C sY p r} in
/-- The underlying cycles of two operations of a rule agree when the degrees are equal and the
cycles are. -/
theorem CycleCapRule.cap_val_congr (c : CycleCapRule C sY p r) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] {e e' : ℤ} (he : e = e') (β : CycleGroup C (g ≫ sY) e)
    (β' : CycleGroup C (g ≫ sY) e') (hβ : β.1 = β'.1) :
    (c.cap g e β).1 = (c.cap g e' β').1 := by
  subst he
  rw [Subtype.ext hβ]

/-- The base change `D ×_Y X ⟶ T ×_Y X` of a closed immersion is a closed immersion. -/
instance isClosedImmersion_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y)
    (g : T ⟶ Y) (h : T' ⟶ T) [IsClosedImmersion h] :
    IsClosedImmersion (bivariantBaseChangeMap f g h) :=
  MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h)
    (P := @IsClosedImmersion) inferInstance

/-- **Lemmas 0H6B and 0H68.** The rule `g ↦ g^*α ∩ -` of a family `α` of `r`-cycles on the fibres
of `X/Y` is compatible with proper pushforward and flat pullback. -/
def CycleCapRule.ofFamily (α : FamilyOfCycles p r) : CycleCapRule C sY p r where
  cap g _ e := relativeCycleCap C sY p r α g e
  properPushforward_cap g _ h _ e β :=
    properPushforward_relativeCycleCap C sY p r α g h (bivariantBaseChangeMap p g h)
      (isPullback_bivariantBaseChangeMap p g h) (bivariantBaseChangeMap_fst p g h) e β
  cap_flatPullback g _ h _ _ d hd e β := by
    let : LocallyOfFiniteType (bivariantBaseChangeMap p g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g h)
        (P := @LocallyOfFiniteType) inferInstance
    let : Flat (bivariantBaseChangeMap p g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g h) (P := @Flat)
        inferInstance
    exact Function.locallyFinsuppWithin.ext fun x ↦
      relativeCycleCap_flatPullback_apply C sY p r α g h d hd (bivariantBaseChangeMap p g h)
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap p g h) hd)
        (isPullback_bivariantBaseChangeMap p g h) (bivariantBaseChangeMap_fst p g h) e β x

/-- The operations of the rule of a family are `g ↦ g^*α ∩ -`. -/
@[simp]
theorem CycleCapRule.ofFamily_cap (α : FamilyOfCycles p r) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (e : ℤ) :
    (CycleCapRule.ofFamily C sY p r α).cap g e = relativeCycleCap C sY p r α g e :=
  rfl

/-- **Lemmas 0H6B, 0H68 and 0H6E.** The rule `g ↦ g^*α ∩ -` of a relative `r`-cycle `α` on `X/Y`
is compatible with proper pushforward, flat pullback, and Gysin maps. -/
def relativeCycleCompatibleRule (α : FamilyOfCycles p r)
    (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      IsRelativeCycle p r α) : CompatibleCycleCapRule C sY p r where
  toCycleCapRule := CycleCapRule.ofFamily C sY p r α
  cap_gysin {T} g _ L _ s htriv e β := by
    change relativeCycleCap C sY p r α _ e _ =
      gysinCycleMapAlong C _ _ _ _ _ _ _ _ _ (cycleGroupCongr C _ _
        (relativeCycleCap C sY p r α g (e + 1) β))
    apply properPushforward_injective_of_isClosedImmersion C _ (pullback.fst p g ≫ p ≫ sY)
      (bivariantBaseChangeMap p g (Stacks.Divisors.zeroScheme T L s).subschemeι)
      (bivariantBaseChangeMap_comp_structure sY p g _)
    have hprop := properPushforward_relativeCycleCap C sY p r α g
      (Stacks.Divisors.zeroScheme T L s).subschemeι
      (bivariantBaseChangeMap p g (Stacks.Divisors.zeroScheme T L s).subschemeι)
      (isPullback_bivariantBaseChangeMap p g _) (bivariantBaseChangeMap_fst p g _) e
      (gysinCycleMapAlong C (g ≫ sY) (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY)
        e L s (Stacks.Divisors.zeroScheme T L s).subschemeι htriv (Category.assoc _ g sY).symm
        (Scheme.IdealSheafData.ker_subschemeι _) β)
    rw [properPushforward_gysinCycleMapAlong_eq C (g ≫ sY) e L s htriv
        (Stacks.Divisors.zeroScheme T L s).subschemeι
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) (Category.assoc _ g sY).symm
        (Scheme.IdealSheafData.ker_subschemeι _) β,
      relativeCycleCap_gysinCycleMapPushforward C sY p r α hα g L s htriv e β] at hprop
    refine hprop.trans ?_
    rw [properPushforward_gysinCycleMapAlong_eq C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e)
      (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s) _
      (bivariantBaseChangeMap p g (Stacks.Divisors.zeroScheme T L s).subschemeι)
      (pullback.fst p ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ p ≫ sY)
      (bivariantBaseChangeMap_comp_structure sY p g _)
      (ker_bivariantBaseChangeMap_subschemeι p g L s)]

/-- The operations of the rule of a relative cycle are `g ↦ g^*α ∩ -`. -/
@[simp]
theorem relativeCycleCompatibleRule_cap (α : FamilyOfCycles p r)
    (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      IsRelativeCycle p r α) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ) :
    (relativeCycleCompatibleRule C sY p r α hα).cap g e = relativeCycleCap C sY p r α g e :=
  rfl

variable {C sY p r} in
/-- The difference of two rules compatible with proper pushforward and flat pullback is one. -/
instance : Sub (CycleCapRule C sY p r) where
  sub c₁ c₂ :=
    { cap := fun g _ e ↦ c₁.cap g e - c₂.cap g e
      properPushforward_cap := fun g _ h _ e β ↦ by
        simp only [AddMonoidHom.sub_apply]
        rw [properPushforward_sub, c₁.properPushforward_cap, c₂.properPushforward_cap]
      cap_flatPullback := fun g _ h _ _ d hd e β ↦ by
        simp only [AddMonoidHom.sub_apply, map_sub, AddSubgroup.coe_sub]
        rw [c₁.cap_flatPullback, c₂.cap_flatPullback] }

variable {C sY p r} in
/-- The operations of a difference of rules are the differences of their operations. -/
@[simp]
theorem CycleCapRule.sub_cap (c₁ c₂ : CycleCapRule C sY p r) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (e : ℤ) : (c₁ - c₂).cap g e = c₁.cap g e - c₂.cap g e :=
  rfl

variable {C sY p r} in
/-- The difference of two rules compatible with proper pushforward, flat pullback and Gysin maps
is one. -/
instance : Sub (CompatibleCycleCapRule C sY p r) where
  sub c₁ c₂ :=
    { toCycleCapRule := c₁.toCycleCapRule - c₂.toCycleCapRule
      cap_gysin := fun g _ L _ s htriv e β ↦ by
        simp only [CycleCapRule.sub_cap, AddMonoidHom.sub_apply, map_sub]
        rw [c₁.cap_gysin, c₂.cap_gysin] }

variable {C sY p r} in
/-- The operations of a difference of compatible rules are the differences of their operations. -/
@[simp]
theorem CompatibleCycleCapRule.sub_cap (c₁ c₂ : CompatibleCycleCapRule C sY p r)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ) :
    (c₁ - c₂).cap g e = c₁.cap g e - c₂.cap g e :=
  rfl

end Rule

end Stacks.Chow

end
