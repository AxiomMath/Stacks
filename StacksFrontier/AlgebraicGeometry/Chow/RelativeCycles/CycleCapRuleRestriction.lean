module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleBasic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.TestSchemeAction

/-!
# Restricting a rule compatible with pushforward, pullback and Gysin maps

Let `c` be a rule as in Stacks 0H6G for a morphism `p : X ⟶ Y` locally of finite type over the
base: to every test scheme `g : T ⟶ Y` and every `e ∈ ℤ` it assigns an operation
`c ∩ - : Z_e(T) ⟶ Z_{r + e}(T ×_Y X)`, compatible with proper pushforward, flat pullback, and
Gysin maps. For a morphism `w : T₀ ⟶ Y` locally of finite type, a test scheme `h : T ⟶ T₀` of the
base change `T₀ ×_Y X ⟶ T₀` is a test scheme `h ≫ w` of `p`, and the pasting isomorphism
`T ×_{T₀} (T₀ ×_Y X) ≅ T ×_Y X` turns the operations of `c` at `h ≫ w` into operations for the
base change. This is the restriction `c|_{T₀}` used in the proof of Stacks 0H6G, and it is again a
rule of the same kind.

## Main definitions

* `Stacks.Chow.CycleCapRule.restrict` — the restriction of a rule compatible with proper
  pushforward and flat pullback along `w : T₀ ⟶ Y`.
* `Stacks.Chow.CompatibleCycleCapRule.restrict` — the restriction of a rule as in Stacks 0H6G.

## Main results

* `Stacks.Chow.CycleCapRule.restrict_cap_apply` — the coefficients of the restricted rule are
  those of `c` at `h ≫ w`, read through the pasting isomorphism.
* `Stacks.Chow.gysinCycleMapPushforward_congr_zeroScheme` — the composite `i_* ∘ i^*` of the
  Gysin map on cycles depends on the invertible module and its section only through the zero
  scheme.

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of cycles along equal structure morphisms -/

/-- Cycle groups for two equal structure morphisms to the base are the same group. -/
def cycleGroupStructureCongr (C : ChowSituation.{u}) {X : Scheme.{u}} {f f' : X ⟶ C.S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hf : f = f') (k : ℤ) :
    CycleGroup C f k ≃+ CycleGroup C f' k where
  toFun z := ⟨z.1, (mem_cyclesOfDimension_congr C hf rfl _).1 z.2⟩
  invFun z := ⟨z.1, (mem_cyclesOfDimension_congr C hf rfl _).2 z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The identification of cycle groups for equal structure morphisms does not change the
underlying cycle. -/
@[simp]
theorem cycleGroupStructureCongr_apply_coe (C : ChowSituation.{u}) {X : Scheme.{u}}
    {f f' : X ⟶ C.S} [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hf : f = f') (k : ℤ)
    (z : CycleGroup C f k) : (cycleGroupStructureCongr C hf k z).1 = z.1 :=
  rfl

/-- Proper pushforward of cycles depends on the structure morphisms and the degree only through
their values and the underlying cycle. -/
theorem properPushforward_val_congr_structure (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hsA : sA = sA')
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (hsB : sB = sB')
    (f : A ⟶ B) [IsProper f] (hf : f ≫ sB = sA) (hf' : f ≫ sB' = sA') (k k' : ℤ)
    (c : CycleGroup C sA k) (c' : CycleGroup C sA' k') (hc : c.1 = c'.1) :
    (properPushforward C sA sB f hf k c).1 = (properPushforward C sA' sB' f hf' k' c').1 := by
  subst hsA hsB
  change AlgebraicCycle.map f _ _ c.1 = AlgebraicCycle.map f _ _ c'.1
  rw [hc]

/-- Flat pullback of cycles depends on the structure morphisms only through their values and the
underlying cycle. -/
theorem flatPullback_val_congr_structure (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hsA : sA = sA')
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (hsB : sB = sB')
    (w : A ⟶ B) [LocallyOfFiniteType w] [Flat w] (hw : w ≫ sB = sA) (hw' : w ≫ sB' = sA')
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension w d) (k : ℤ) (c : CycleGroup C sB k)
    (c' : CycleGroup C sB' k) (hc : c.1 = c'.1) :
    (flatPullback C sA sB w hw d hd k c).1 = (flatPullback C sA' sB' w hw' d hd k c').1 := by
  subst hsA hsB
  rw [Subtype.ext hc]

/-! ### The Gysin map depends only on the zero scheme -/

section ZeroScheme

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  {L L' : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  {s : Γ(L, ⊤)} {s' : Γ(L', ⊤)}
  (hLs : Stacks.Divisors.zeroScheme X L s = Stacks.Divisors.zeroScheme X L' s')

include hLs in
/-- The Gysin map on cycles read along a presentation `i` depends on the invertible module and its
section only through their zero scheme: the rules of Stacks 0B6Z only ask whether an integral
closed subscheme lies inside it. -/
theorem gysinCycleMapAlong_congr_zeroScheme {Z : Scheme.{u}} (q : Z ⟶ C.S)
    [LocallyOfFiniteType q] (i : Z ⟶ X) [IsClosedImmersion i]
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    (htriv' : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L' s').subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L' s').subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L' s').subschemeι).obj L'))
    (hq : i ≫ p = q) (hker : i.ker = Stacks.Divisors.zeroScheme X L s)
    (hker' : i.ker = Stacks.Divisors.zeroScheme X L' s') :
    gysinCycleMapAlong C p q k L s i htriv hq hker =
      gysinCycleMapAlong C p q k L' s' i htriv' hq hker' := by
  have hcyc : gysinCycleMapComponentAlong C p q k L s i =
      gysinCycleMapComponentAlong C p q k L' s' i := by
    funext W hW hDim
    by_cases hle : Stacks.Divisors.zeroScheme X L s ≤ W
    · rw [gysinCycleMapComponentAlong_of_le C p q k L s i W hW hDim hle,
        gysinCycleMapComponentAlong_of_le C p q k L' s' i W hW hDim (hLs ▸ hle)]
    · rw [gysinCycleMapComponentAlong_of_not_le C p q k L s i W hW hDim hle,
        gysinCycleMapComponentAlong_of_not_le C p q k L' s' i W hW hDim (hLs ▸ hle)]
  have hrule : gysinCycleMapRuleAlong C p q k L s i = gysinCycleMapRuleAlong C p q k L' s' i := by
    have key : ∀ R₁ R₂ : IntegralComponentRule C p q i k, R₁.cycle = R₂.cycle → R₁ = R₂ := by
      rintro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ (rfl : c₁ = c₂)
      rfl
    exact key _ _ hcyc
  change (gysinCycleMapRuleAlong C p q k L s i).extendCycleGroup =
    (gysinCycleMapRuleAlong C p q k L' s' i).extendCycleGroup
  rw [hrule]

include hLs in
/-- The composite `i_* ∘ i^*` of the Gysin map on cycles with the pushforward to the ambient
scheme depends on the invertible module and its section only through their zero scheme. -/
theorem gysinCycleMapPushforward_congr_zeroScheme
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    (htriv' : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L' s').subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L' s').subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L' s').subschemeι).obj L')) :
    gysinCycleMapPushforward C p k L s htriv = gysinCycleMapPushforward C p k L' s' htriv' := by
  refine AddMonoidHom.ext fun β ↦ ?_
  have hker' : (Stacks.Divisors.zeroScheme X L s).subschemeι.ker =
      Stacks.Divisors.zeroScheme X L' s' := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hLs]
  rw [← properPushforward_gysinCycleMapAlong_eq C p k L s htriv
      (Stacks.Divisors.zeroScheme X L s).subschemeι _ rfl
      (Scheme.IdealSheafData.ker_subschemeι _) β,
    ← properPushforward_gysinCycleMapAlong_eq C p k L' s' htriv'
      (Stacks.Divisors.zeroScheme X L s).subschemeι _ rfl hker' β,
    gysinCycleMapAlong_congr_zeroScheme C p k hLs _ _ htriv htriv' rfl
      (Scheme.IdealSheafData.ker_subschemeι _) hker']

end ZeroScheme

/-! ### The pasting isomorphism over the base -/

/-- The pasting isomorphism `T ×_Y X ≅ T ×_{T₀} (T₀ ×_Y X)` is a morphism over the base. -/
theorem pullbackLeftPullbackSndIso_inv_comp_structure {S X Y T₀ T : Scheme.{u}} (sY : Y ⟶ S)
    (p : X ⟶ Y) (w : T₀ ⟶ Y) (h : T ⟶ T₀) :
    (pullbackLeftPullbackSndIso p w h).inv ≫ pullback.fst (pullback.snd p w) h ≫
        pullback.snd p w ≫ w ≫ sY =
      pullback.fst p (h ≫ w) ≫ p ≫ sY := by
  rw [← pullback.condition_assoc, ← Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst_eq_bivariantBaseChangeMap,
    bivariantBaseChangeMap_comp_structure]

/-- The pasting isomorphism `T ×_{T₀} (T₀ ×_Y X) ≅ T ×_Y X` is a morphism over the base. -/
theorem pullbackLeftPullbackSndIso_hom_comp_structure {S X Y T₀ T : Scheme.{u}} (sY : Y ⟶ S)
    (p : X ⟶ Y) (w : T₀ ⟶ Y) (h : T ⟶ T₀) :
    (pullbackLeftPullbackSndIso p w h).hom ≫ pullback.fst p (h ≫ w) ≫ p ≫ sY =
      pullback.fst (pullback.snd p w) h ≫ pullback.snd p w ≫ w ≫ sY := by
  rw [← pullbackLeftPullbackSndIso_inv_comp_structure sY p w h, Iso.hom_inv_id_assoc]

/-- The pasting isomorphisms are natural in the test scheme: they intertwine the two canonical
maps of base changes induced by `h : T' ⟶ T`. -/
theorem bivariantBaseChangeMap_comp_pullbackLeftPullbackSndIso_hom {X Y T₀ T T' : Scheme.{u}}
    (p : X ⟶ Y) (w : T₀ ⟶ Y) (g : T ⟶ T₀) (h : T' ⟶ T) :
    bivariantBaseChangeMap (pullback.snd p w) g h ≫ (pullbackLeftPullbackSndIso p w g).hom =
      ((pullbackLeftPullbackSndIso p w (h ≫ g)).hom ≫
        (pullback.congrHom rfl (Category.assoc h g w)).hom) ≫
        bivariantBaseChangeMap p (g ≫ w) h := by
  apply pullback.hom_ext <;> simp

section Rule

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {p : X ⟶ Y} [LocallyOfFiniteType p] {r : ℕ}

namespace CycleCapRule

variable (c : CycleCapRule C sY p r) {T₀ : Scheme.{u}} (w : T₀ ⟶ Y) [LocallyOfFiniteType w]

/-- The operation of the restriction of a rule to `w : T₀ ⟶ Y` on a test scheme `h : T ⟶ T₀`:
the operation of the rule at `h ≫ w`, transported along the pasting isomorphism
`T ×_Y X ≅ T ×_{T₀} (T₀ ×_Y X)`. -/
def restrictCap {T : Scheme.{u}} (h : T ⟶ T₀) [LocallyOfFiniteType h] (e : ℤ) :
    CycleGroup C (h ≫ w ≫ sY) e →+
      CycleGroup C (pullback.fst (pullback.snd p w) h ≫ pullback.snd p w ≫ w ≫ sY)
        ((r : ℤ) + e) :=
  (properPushforwardHom C (pullback.fst p (h ≫ w) ≫ p ≫ sY) _
    (pullbackLeftPullbackSndIso p w h).inv
    (pullbackLeftPullbackSndIso_inv_comp_structure sY p w h) ((r : ℤ) + e)).comp
    ((c.cap (h ≫ w) e).comp
      (cycleGroupStructureCongr C (Category.assoc h w sY).symm e).toAddMonoidHom)

/-- The restricted operation is the pushforward along the pasting isomorphism of the operation
at `h ≫ w`. -/
theorem restrictCap_eq {T : Scheme.{u}} (h : T ⟶ T₀) [LocallyOfFiniteType h] (e : ℤ)
    (β : CycleGroup C (h ≫ w ≫ sY) e) :
    c.restrictCap w h e β =
      properPushforward C (pullback.fst p (h ≫ w) ≫ p ≫ sY) _
        (pullbackLeftPullbackSndIso p w h).inv
        (pullbackLeftPullbackSndIso_inv_comp_structure sY p w h) ((r : ℤ) + e)
        (c.cap (h ≫ w) e (cycleGroupStructureCongr C (Category.assoc h w sY).symm e β)) :=
  rfl

/-- The coefficients of the restricted operation are those of the operation at `h ≫ w`, read
through the pasting isomorphism. -/
theorem restrictCap_apply {T : Scheme.{u}} (h : T ⟶ T₀) [LocallyOfFiniteType h] (e : ℤ)
    (β : CycleGroup C (h ≫ w ≫ sY) e) (β' : CycleGroup C ((h ≫ w) ≫ sY) e) (hβ : β.1 = β'.1)
    (z : ↥(pullback (pullback.snd p w) h)) :
    (c.restrictCap w h e β).1 z =
      (c.cap (h ≫ w) e β').1 ((pullbackLeftPullbackSndIso p w h).hom z) := by
  rw [restrictCap_eq, show cycleGroupStructureCongr C (Category.assoc h w sY).symm e β = β' from
    Subtype.ext hβ]
  exact properPushforward_apply_of_isIso_inv C _ _ (pullbackLeftPullbackSndIso p w h).symm _ _ _ z

/-- The coefficients of the restricted operation at a composite `h ≫ g` are those of the operation
at `h ≫ g ≫ w`, read through the pasting isomorphism and the reassociation of `h ≫ g ≫ w`. -/
private theorem restrictCap_comp_apply {T T' : Scheme.{u}} (g : T ⟶ T₀) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] (e : ℤ) (β : CycleGroup C ((h ≫ g) ≫ w ≫ sY) e)
    (β' : CycleGroup C ((h ≫ g ≫ w) ≫ sY) e) (hβ : β.1 = β'.1)
    (x : ↥(pullback (pullback.snd p w) (h ≫ g))) :
    (c.restrictCap w (h ≫ g) e β).1 x =
      (c.cap (h ≫ g ≫ w) e β').1
        (((pullbackLeftPullbackSndIso p w (h ≫ g)).trans
          (pullback.congrHom rfl (Category.assoc h g w))).hom x) := by
  rw [c.restrictCap_apply w (h ≫ g) e β
      (cycleGroupStructureCongr C (Category.assoc (h ≫ g) w sY).symm e β) rfl,
    c.cap_congr_hom (Category.assoc h g w) e
      (cycleGroupStructureCongr C (Category.assoc (h ≫ g) w sY).symm e β) β' hβ]
  rfl

/-- **Stacks 0H6B for the restricted rule.** -/
theorem properPushforward_restrictCap {T T' : Scheme.{u}} (g : T ⟶ T₀) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [IsProper h] (e : ℤ) (β : CycleGroup C ((h ≫ g) ≫ w ≫ sY) e) :
    properPushforward C (pullback.fst (pullback.snd p w) (h ≫ g) ≫ pullback.snd p w ≫ w ≫ sY)
        (pullback.fst (pullback.snd p w) g ≫ pullback.snd p w ≫ w ≫ sY)
        (bivariantBaseChangeMap (pullback.snd p w) g h)
        (bivariantBaseChangeMap_comp_structure (w ≫ sY) (pullback.snd p w) g h)
        ((r : ℤ) + e) (c.restrictCap w (h ≫ g) e β) =
      c.restrictCap w g e (properPushforward C ((h ≫ g) ≫ w ≫ sY) (g ≫ w ≫ sY) h
        (Category.assoc h g (w ≫ sY)).symm e β) := by
  have hg' : (h ≫ g) ≫ w = h ≫ g ≫ w := Category.assoc h g w
  have hs : (h ≫ g) ≫ w ≫ sY = (h ≫ g ≫ w) ≫ sY := by simp
  set β'' : CycleGroup C ((h ≫ g ≫ w) ≫ sY) e := cycleGroupStructureCongr C hs e β
  apply Subtype.ext
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  refine (properPushforward_congr_iso C _ _ (pullback.fst p (h ≫ g ≫ w) ≫ p ≫ sY)
    (pullback.fst p (g ≫ w) ≫ p ≫ sY) (bivariantBaseChangeMap (pullback.snd p w) g h)
    (bivariantBaseChangeMap p (g ≫ w) h) _ (bivariantBaseChangeMap_comp_structure sY p (g ≫ w) h)
    ((pullbackLeftPullbackSndIso p w (h ≫ g)).trans (pullback.congrHom rfl hg'))
    (pullbackLeftPullbackSndIso p w g) ?_ ?_ ?_ ((r : ℤ) + e) ((r : ℤ) + e) _
    (c.cap (h ≫ g ≫ w) e β'') ?_ y).trans ?_
  · rw [Iso.trans_hom, Category.assoc, ← pullbackLeftPullbackSndIso_hom_comp_structure sY p w]
    simp
  · exact pullbackLeftPullbackSndIso_hom_comp_structure sY p w g
  · exact bivariantBaseChangeMap_comp_pullbackLeftPullbackSndIso_hom p w g h
  · exact c.restrictCap_comp_apply w g h e β β'' rfl
  · rw [c.properPushforward_cap (g ≫ w) h e β'']
    refine (c.restrictCap_apply w g e _ _ ?_ y).symm
    exact properPushforward_val_congr_structure C (by simp) (by simp) h _ _ e e β β'' rfl

/-- The base change of a morphism locally of finite type between two base changes. -/
private instance locallyOfFiniteType_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y)
    (g : T ⟶ Y) (h : T' ⟶ T) [LocallyOfFiniteType h] :
    LocallyOfFiniteType (bivariantBaseChangeMap f g h) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (isPullback_bivariantBaseChangeMap f g h) inferInstance

/-- The base change of a flat morphism between two base changes. -/
private instance flat_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (h : T' ⟶ T) [Flat h] : Flat (bivariantBaseChangeMap f g h) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_bivariantBaseChangeMap f g h)
    inferInstance

/-- **Stacks 0H68 for the restricted rule.** -/
theorem restrictCap_flatPullback {T T' : Scheme.{u}} (g : T ⟶ T₀) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension h d) (e : ℤ) (β : CycleGroup C (g ≫ w ≫ sY) e) :
    letI : LocallyOfFiniteType (bivariantBaseChangeMap (pullback.snd p w) g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (pullback.snd p w) g h)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (bivariantBaseChangeMap (pullback.snd p w) g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (pullback.snd p w) g h)
        (P := @Flat) inferInstance
    (c.restrictCap w (h ≫ g) (e + d)
        (flatPullback C ((h ≫ g) ≫ w ≫ sY) (g ≫ w ≫ sY) h (Category.assoc h g (w ≫ sY)).symm d
          hd e β)).1 =
      (flatPullback C (pullback.fst (pullback.snd p w) (h ≫ g) ≫ pullback.snd p w ≫ w ≫ sY)
        (pullback.fst (pullback.snd p w) g ≫ pullback.snd p w ≫ w ≫ sY)
        (bivariantBaseChangeMap (pullback.snd p w) g h)
        (bivariantBaseChangeMap_comp_structure (w ≫ sY) (pullback.snd p w) g h) d
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap (pullback.snd p w) g h) hd)
        ((r : ℤ) + e) (c.restrictCap w g e β)).1 := by
  have hg' : (h ≫ g) ≫ w = h ≫ g ≫ w := Category.assoc h g w
  set i := (pullbackLeftPullbackSndIso p w (h ≫ g)).trans (pullback.congrHom rfl hg') with hi
  set j := pullbackLeftPullbackSndIso p w g with hj
  set β₀ : CycleGroup C ((g ≫ w) ≫ sY) e :=
    cycleGroupStructureCongr C (Category.assoc g w sY).symm e β
  have hsq : bivariantBaseChangeMap p (g ≫ w) h ≫ j.inv =
      i.inv ≫ bivariantBaseChangeMap (pullback.snd p w) g h := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (bivariantBaseChangeMap_comp_pullbackLeftPullbackSndIso_hom p w g h).symm
  have hu₁ : i.inv ≫ pullback.fst (pullback.snd p w) (h ≫ g) ≫ pullback.snd p w ≫ w ≫ sY =
      pullback.fst p (h ≫ g ≫ w) ≫ p ≫ sY := by
    rw [hi, Iso.trans_inv, Category.assoc, pullbackLeftPullbackSndIso_inv_comp_structure]
    simp
  have key := flatPullback_properPushforward_of_isIso C (pullback.fst p (g ≫ w) ≫ p ≫ sY)
    (pullback.fst p (h ≫ g ≫ w) ≫ p ≫ sY)
    (pullback.fst (pullback.snd p w) g ≫ pullback.snd p w ≫ w ≫ sY)
    (pullback.fst (pullback.snd p w) (h ≫ g) ≫ pullback.snd p w ≫ w ≫ sY) j.inv
    (pullbackLeftPullbackSndIso_inv_comp_structure sY p w g) i.inv hu₁
    (bivariantBaseChangeMap p (g ≫ w) h) (bivariantBaseChangeMap_comp_structure sY p (g ≫ w) h)
    (bivariantBaseChangeMap (pullback.snd p w) g h)
    (bivariantBaseChangeMap_comp_structure (w ≫ sY) (pullback.snd p w) g h) hsq d
    (AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_bivariantBaseChangeMap p (g ≫ w) h) hd)
    (AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_bivariantBaseChangeMap (pullback.snd p w) g h) hd) ((r : ℤ) + e)
    (c.cap (g ≫ w) e β₀)
  have hflat := c.cap_flatPullback (g ≫ w) h d hd e β₀
  change _ = (flatPullback C _ _ (bivariantBaseChangeMap (pullback.snd p w) g h) _ d _ ((r : ℤ) + e)
    (c.restrictCap w g e β)).1
  rw [c.restrictCap_eq w g e β, key]
  refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
  rw [c.restrictCap_comp_apply w g h (e + d) _ _
    (flatPullback_val_congr_structure C (by simp) (by simp) h
      (Category.assoc h g (w ≫ sY)).symm (Category.assoc h (g ≫ w) sY).symm d hd e β β₀ rfl)]
  refine (congrArg (fun z : AlgebraicCycle _ ℤ ↦ z (i.hom x)) hflat).trans ?_
  exact (properPushforward_apply_of_isIso_inv C _ _ i.symm hu₁ _ _ x).symm

end CycleCapRule

/-- **The restriction of a rule.** For a morphism `w : T₀ ⟶ Y` locally of finite type, a rule
compatible with proper pushforward and flat pullback for `p : X ⟶ Y` restricts to one for the
base change `T₀ ×_Y X ⟶ T₀`: on a test scheme `h : T ⟶ T₀` it is the operation at `h ≫ w`, read
through the pasting isomorphism `T ×_{T₀} (T₀ ×_Y X) ≅ T ×_Y X`. -/
def CycleCapRule.restrict (c : CycleCapRule C sY p r) {T₀ : Scheme.{u}} (w : T₀ ⟶ Y)
    [LocallyOfFiniteType w] : CycleCapRule C (w ≫ sY) (pullback.snd p w) r where
  cap h _ e := c.restrictCap w h e
  properPushforward_cap g _ h _ e β := c.properPushforward_restrictCap w g h e β
  cap_flatPullback g _ h _ _ d hd e β := c.restrictCap_flatPullback w g h d hd e β

/-- The operations of the restricted rule. -/
theorem CycleCapRule.restrict_cap (c : CycleCapRule C sY p r) {T₀ : Scheme.{u}} (w : T₀ ⟶ Y)
    [LocallyOfFiniteType w] {T : Scheme.{u}} (h : T ⟶ T₀) [LocallyOfFiniteType h] (e : ℤ) :
    (c.restrict w).cap h e = c.restrictCap w h e :=
  rfl

/-- The coefficients of the restricted rule on a test scheme `h : T ⟶ T₀` are those of the rule at
`h ≫ w`, read through the pasting isomorphism `T ×_{T₀} (T₀ ×_Y X) ≅ T ×_Y X`. -/
theorem CycleCapRule.restrict_cap_apply (c : CycleCapRule C sY p r)
    {T₀ : Scheme.{u}} (w : T₀ ⟶ Y) [LocallyOfFiniteType w] {T : Scheme.{u}} (h : T ⟶ T₀)
    [LocallyOfFiniteType h] (e : ℤ) (β : CycleGroup C (h ≫ w ≫ sY) e)
    (β' : CycleGroup C ((h ≫ w) ≫ sY) e) (hβ : β.1 = β'.1)
    (z : ↥(pullback (pullback.snd p w) h)) :
    ((c.restrict w).cap h e β).1 z =
      (c.cap (h ≫ w) e β').1 ((pullbackLeftPullbackSndIso p w h).hom z) :=
  c.restrictCap_apply w h e β β' hβ z

/-- **From `i_* ∘ i^*` to the Gysin compatibility.** A rule compatible with proper pushforward
which commutes with the composites `i_* ∘ i^*` on every test scheme is compatible with the Gysin
maps, in the form of `Stacks.Chow.CompatibleCycleCapRule`. This is the converse of
`Stacks.Chow.CompatibleCycleCapRule.cap_gysinCycleMapPushforward`. -/
theorem CycleCapRule.cap_gysin_of_cap_gysinCycleMapPushforward (c : CycleCapRule C sY p r)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (e : ℤ) (β : CycleGroup C (g ≫ sY) (e + 1))
    (hc : c.cap g e (gysinCycleMapPushforward C (g ≫ sY) e L s htriv β) =
      gysinCycleMapPushforward C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e)
        (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s)
        (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
          (pullback.snd p g) L s htriv)
        (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm (c.cap g (e + 1) β))) :
    c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) e
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
        (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm (c.cap g (e + 1) β)) := by
  apply properPushforward_injective_of_isClosedImmersion C _ (pullback.fst p g ≫ p ≫ sY)
    (bivariantBaseChangeMap p g (Stacks.Divisors.zeroScheme T L s).subschemeι)
    (bivariantBaseChangeMap_comp_structure sY p g _)
  rw [c.properPushforward_cap g (Stacks.Divisors.zeroScheme T L s).subschemeι e,
    properPushforward_gysinCycleMapAlong_eq C (g ≫ sY) e L s htriv
      (Stacks.Divisors.zeroScheme T L s).subschemeι
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sY) (Category.assoc _ g sY).symm
      (Scheme.IdealSheafData.ker_subschemeι _) β, hc,
    properPushforward_gysinCycleMapAlong_eq C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e)
      (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s) _
      (bivariantBaseChangeMap p g (Stacks.Divisors.zeroScheme T L s).subschemeι)
      (pullback.fst p ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ p ≫ sY)
      (bivariantBaseChangeMap_comp_structure sY p g _)
      (ker_bivariantBaseChangeMap_subschemeι p g L s)]

/-- **Stacks 0H6E for the restricted rule, read in `T ×_{T₀} (T₀ ×_Y X)`.** The restriction of a
rule as in Stacks 0H6G commutes with the composites `i_* ∘ i^*` of the Gysin maps on cycles. -/
theorem CompatibleCycleCapRule.restrictCap_gysinCycleMapPushforward
    (c : CompatibleCycleCapRule C sY p r) {T₀ : Scheme.{u}} (w : T₀ ⟶ Y) [LocallyOfFiniteType w]
    {T : Scheme.{u}} (g : T ⟶ T₀) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (e : ℤ) (β : CycleGroup C (g ≫ w ≫ sY) (e + 1)) :
    c.toCycleCapRule.restrictCap w g e (gysinCycleMapPushforward C (g ≫ w ≫ sY) e L s htriv β) =
      gysinCycleMapPushforward C
        (pullback.fst (pullback.snd p w) g ≫ pullback.snd p w ≫ w ≫ sY) ((r : ℤ) + e)
        (bivariantPullbackModule (pullback.snd p w) g L)
        (bivariantPullbackSection (pullback.snd p w) g L s)
        (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
          (pullback.snd (pullback.snd p w) g) L s htriv)
        (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm
          (c.toCycleCapRule.restrictCap w g (e + 1) β)) := by
  set j := pullbackLeftPullbackSndIso p w g with hj
  set β₀ : CycleGroup C ((g ≫ w) ≫ sY) (e + 1) :=
    cycleGroupStructureCongr C (Category.assoc g w sY).symm (e + 1) β
  have hconv : cycleGroupStructureCongr C (Category.assoc g w sY).symm e
        (gysinCycleMapPushforward C (g ≫ w ≫ sY) e L s htriv β) =
      gysinCycleMapPushforward C ((g ≫ w) ≫ sY) e L s htriv β₀ :=
    Subtype.ext (gysinCycleMapPushforward_congr C _ e L s htriv _ (Category.assoc g w sY).symm β
      β₀ rfl)
  set γ := c.cap (g ≫ w) (e + 1) β₀
  have hcp : cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm
        (properPushforward C (pullback.fst p (g ≫ w) ≫ p ≫ sY) _ j.inv
          (pullbackLeftPullbackSndIso_inv_comp_structure sY p w g) ((r : ℤ) + (e + 1)) γ) =
      properPushforward C (pullback.fst p (g ≫ w) ≫ p ≫ sY) _ j.inv
        (pullbackLeftPullbackSndIso_inv_comp_structure sY p w g) ((r : ℤ) + e + 1)
        (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm γ) :=
    rfl
  have hZ : Stacks.Divisors.zeroScheme (pullback p (g ≫ w)) (bivariantPullbackModule p (g ≫ w) L)
        (bivariantPullbackSection p (g ≫ w) L s) =
      Stacks.Divisors.zeroScheme (pullback p (g ≫ w))
        ((Scheme.Modules.pullback j.inv).obj (bivariantPullbackModule (pullback.snd p w) g L))
        (pullbackGlobalSections j.inv _ (bivariantPullbackSection (pullback.snd p w) g L s)) := by
    rw [Stacks.Divisors.zeroScheme_pullback j.inv, Stacks.Divisors.zeroScheme_pullback,
      Stacks.Divisors.zeroScheme_pullback, ← Scheme.IdealSheafData.comap_comp, hj,
      pullbackLeftPullbackSndIso_inv_snd_snd]
  rw [c.toCycleCapRule.restrictCap_eq w g e, c.toCycleCapRule.restrictCap_eq w g (e + 1), hconv,
    c.cap_gysinCycleMapPushforward (g ≫ w) L s htriv e β₀, hcp,
    gysinCycleMapPushforward_properPushforward C _ ((r : ℤ) + e) _ _ _ _ j.inv
      (pullbackLeftPullbackSndIso_inv_comp_structure sY p w g),
    gysinCycleMapPushforward_congr_zeroScheme C _ ((r : ℤ) + e) hZ]

/-- **The restriction of a rule as in Stacks 0H6G.** For a morphism `w : T₀ ⟶ Y` locally of finite
type, a rule compatible with proper pushforward, flat pullback and Gysin maps for `p : X ⟶ Y`
restricts to one for the base change `T₀ ×_Y X ⟶ T₀`. -/
def CompatibleCycleCapRule.restrict (c : CompatibleCycleCapRule C sY p r) {T₀ : Scheme.{u}}
    (w : T₀ ⟶ Y) [LocallyOfFiniteType w] :
    CompatibleCycleCapRule C (w ≫ sY) (pullback.snd p w) r where
  toCycleCapRule := c.toCycleCapRule.restrict w
  cap_gysin g _ L _ s htriv e β :=
    (c.toCycleCapRule.restrict w).cap_gysin_of_cap_gysinCycleMapPushforward g L s htriv e β
      (c.restrictCap_gysinCycleMapPushforward w g L s htriv e β)

/-- The underlying rule of the restriction is the restriction of the underlying rule. -/
@[simp]
theorem CompatibleCycleCapRule.restrict_toCycleCapRule (c : CompatibleCycleCapRule C sY p r)
    {T₀ : Scheme.{u}} (w : T₀ ⟶ Y) [LocallyOfFiniteType w] :
    (c.restrict w).toCycleCapRule = c.toCycleCapRule.restrict w :=
  rfl

end Rule

end Stacks.Chow

end
