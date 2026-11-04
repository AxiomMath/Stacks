module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ElementCap
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Lift

/-!
# The bivariant class of a divisor whose complement is flat of relative dimension one

Let `π : W ⟶ X` be locally of finite type over the base of chapter 42, let `j : U ⟶ W` be an open
immersion with `U ⟶ X` flat of relative dimension one, and let `Z(s) ⊆ W` be the zero scheme of a
section of an invertible module with trivial normal bundle whose complement is `U`. Capping a lift
with the Gysin class `i^* ∈ A¹(Z(s) ⟶ W)` of Stacks 0B79 defines a bivariant class
`C ∈ A⁰(Z(s) ⟶ X)`: `C ∩ α = i^* β` for any lift `β` of `α`. This is the construction of
Stacks 0F9J, carried out for an arbitrary such divisor.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.infinityCap` — the cap operation `α ↦ i^* β`.
* `Stacks.Chow.GysinAtInfinity.infinityClass` — the bivariant class.

## Main results

* `Stacks.Chow.GysinAtInfinity.infinityCap_eq_of_isLift` — the cap operation is computed by any
  lift.
* `Stacks.Chow.GysinAtInfinity.infinityCap_properChowPushforward`,
  `infinityCap_flatPullbackChow`, `infinityCap_gysin` — the three conditions of Stacks 0B76.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

/-! ### Transport lemmas along equalities of degrees -/

/-- The Gysin map `G.onChow q M t n` respects heterogeneous equality along an equality `n = n'`
of degrees. -/
theorem onChow_heq {C : ChowSituation.{u}} (G : GysinSystem C) {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) {n n' : ℤ} (h : n = n') {x : chowGroup C q (n + 1)}
    {x' : chowGroup C q (n' + 1)} (hx : x ≍ x') : G.onChow q M t n x ≍ G.onChow q M t n' x' := by
  subst h
  cases hx
  rfl

/-- Proper pushforward of cycle classes respects heterogeneous equality along an equality
`n = n'` of degrees. -/
theorem properChowPushforward_heq (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (q : A ⟶ B) [IsProper q]
    (hq : q ≫ sB = sA) {n n' : ℤ} (h : n = n')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq n)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq n')
    {x : chowGroup C sA n} {x' : chowGroup C sA n'} (hx : x ≍ x') :
    properChowPushforward C sA sB q hq n hfac x ≍ properChowPushforward C sA sB q hq n' hfac' x' :=
        by
  subst h
  cases hx
  rfl

/-- Transport `Eq.mp h x` along an equality `α n = α n'` is heterogeneously equal to `x`. -/
theorem eqMp_heq {α : ℤ → Type u} {n n' : ℤ} (h : α n = α n') (x : α n) : Eq.mp h x ≍ x :=
  (cast_heq h x)

section Class

variable (C : ChowSituation.{u}) {X W U : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))

/-- The capping operation `x ↦ i_∞^* x` of the divisor, read on `Z(s) ×_X T`. -/
abbrev divisorMiddleCap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (m : ℤ) :=
  middleCap C (gysinSystemOfInvertible C) (gysinTripleInclusion L s ≫ (π ≫ f)) (π ≫ f)
    (gysinTripleInclusion L s) π rfl 1 (divisorClass C f π L s) g m

/-- A chosen lift of `α` to the cycle classes of `W ×_X T`, as in `exists_isLift`. -/
def chosenLift {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ f) k) : chowGroup C (testStr C f π g) (k + 1) :=
  (exists_isLift C f π j hU g k α).choose

/-- `chosenLift C f π j hU g k α` is a lift of `α`. -/
theorem isLift_chosenLift {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ f) k) : IsLift C f π j hU g k α (chosenLift C f π j hU g k α) :=
  (exists_isLift C f π j hU g k α).choose_spec

include hcompl htriv in
/-- Any two lifts `β`, `β'` of `α` have the same image under `divisorMiddleCap`. -/
theorem divisorMiddleCap_eq_of_isLift {T : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g]
    {k : ℤ} {α : chowGroup C (g ≫ f) k} {β β' : chowGroup C (testStr C f π g) (k + 1)}
    (hβ : IsLift C f π j hU g k α β) (hβ' : IsLift C f π j hU g k α β') :
    divisorMiddleCap C f π L s g (k + 1) β = divisorMiddleCap C f π L s g (k + 1) β' := by
  rw [divisorMiddleCap, middleCap_apply, middleCap_apply,
    IsLift.cap_eq C f π j hU L s hcompl htriv hβ hβ']

/-- The cap operation of the class at infinity: `α ↦ i_∞^* β` for a lift `β` of `α`. -/
def infinityCap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ f) k →+
      chowGroup C (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
        (gysinTripleInclusion L s ≫ (π ≫ f))) (k - 0) where
  toFun α := chowGroupDegreeEquiv C _ (by ring : k + 1 - 1 = k - 0)
    (divisorMiddleCap C f π L s g (k + 1) (chosenLift C f π j hU g k α))
  map_zero' := by
    rw [divisorMiddleCap_eq_of_isLift C f π j hU L s hcompl htriv
      (isLift_chosenLift C f π j hU g k 0) (isLift_zero C f π j hU g k), map_zero, map_zero]
  map_add' α α' := by
    rw [divisorMiddleCap_eq_of_isLift C f π j hU L s hcompl htriv
      (isLift_chosenLift C f π j hU g k (α + α'))
      ((isLift_chosenLift C f π j hU g k α).add C f π j hU (isLift_chosenLift C f π j hU g k α')),
      map_add, map_add]

/-- For any lift `β` of `α`, `infinityCap` sends `α` to the image of `β` under
`divisorMiddleCap`. -/
theorem infinityCap_eq_of_isLift {T : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g]
    {k : ℤ} {α : chowGroup C (g ≫ f) k} {β : chowGroup C (testStr C f π g) (k + 1)}
    (hβ : IsLift C f π j hU g k α β) :
    infinityCap C f π j hU L s hcompl htriv g k α =
      chowGroupDegreeEquiv C _ (by ring : k + 1 - 1 = k - 0)
        (divisorMiddleCap C f π L s g (k + 1) β) := by
  show chowGroupDegreeEquiv C _ _ (divisorMiddleCap C f π L s g (k + 1) _) = _
  rw [divisorMiddleCap_eq_of_isLift C f π j hU L s hcompl htriv
    (isLift_chosenLift C f π j hU g k α) hβ]

include hcompl htriv in
/-- `infinityCap` commutes with proper pushforward along `h : T' ⟶ T`. -/
theorem infinityCap_properChowPushforward {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback (gysinTripleInclusion L s ≫ π) (h ≫ g) ⟶
      pullback (gysinTripleInclusion L s ≫ π) g)
    (sq : IsPullback (pullback.snd (gysinTripleInclusion L s ≫ π) (h ≫ g)) h' h
      (pullback.snd (gysinTripleInclusion L s ≫ π) g))
    (hfst : h' ≫ pullback.fst (gysinTripleInclusion L s ≫ π) g =
      pullback.fst (gysinTripleInclusion L s ≫ π) (h ≫ g)) (k : ℤ)
    (α : chowGroup C ((h ≫ g) ≫ f) k) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    infinityCap C f π j hU L s hcompl htriv g k
        (properChowPushforward C ((h ≫ g) ≫ f) (g ≫ f) h (by simp [Category.assoc]) k
          (properPushforwardDescends C _ _ _ _ _) α) =
      properChowPushforward C (pullback.fst (gysinTripleInclusion L s ≫ π) (h ≫ g) ≫
          (gysinTripleInclusion L s ≫ (π ≫ f)))
        (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫ (gysinTripleInclusion L s ≫ (π ≫ f)))
        h' (by rw [← Category.assoc, hfst]) (k - 0) (properPushforwardDescends C _ _ _ _ _)
        (infinityCap C f π j hU L s hcompl htriv (h ≫ g) k α) := by
  have hprop : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have hl := IsLift.properChowPushforward C f π j hU h (isLift_chosenLift C f π j hU (h ≫ g) k α)
  refine (infinityCap_eq_of_isLift C f π j hU L s hcompl htriv hl).trans ?_
  rw [divisorMiddleCap, middleCap_properChowPushforward C (gysinSystemOfInvertible C)
    (gysinTripleInclusion L s ≫ (π ≫ f)) (π ≫ f) (gysinTripleInclusion L s) π rfl 1
    (divisorClass C f π L s) g h h' sq hfst (k + 1)]
  exact chowGroupDegreeEquiv_properChowPushforward_comp C _ _ h' _ (by ring : k + 1 - 1 = k - 0)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _

include hcompl htriv in
/-- `infinityCap` commutes with flat pullback along `h : T' ⟶ T` of relative dimension `r`. -/
theorem infinityCap_flatPullbackChow {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback (gysinTripleInclusion L s ≫ π) (h ≫ g) ⟶
      pullback (gysinTripleInclusion L s ≫ π) g)
    (sq : IsPullback (pullback.snd (gysinTripleInclusion L s ≫ π) (h ≫ g)) h' h
      (pullback.snd (gysinTripleInclusion L s ≫ π) g))
    (hfst : h' ≫ pullback.fst (gysinTripleInclusion L s ≫ π) g =
      pullback.fst (gysinTripleInclusion L s ≫ π) (h ≫ g)) (k : ℤ)
    (α : chowGroup C (g ≫ f) k) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    infinityCap C f π j hU L s hcompl htriv (h ≫ g) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ f) (g ≫ f) h (by simp [Category.assoc]) r hr k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) ≍
      flatPullbackChow C (pullback.fst (gysinTripleInclusion L s ≫ π) (h ≫ g) ≫
          (gysinTripleInclusion L s ≫ (π ≫ f)))
        (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫ (gysinTripleInclusion L s ≫ (π ≫ f)))
        h' (by rw [← Category.assoc, hfst]) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (k - 0)
        (flatPullbackDescends C _ _ _ _ _ _ _)
        (infinityCap C f π j hU L s hcompl htriv g k α) := by
  have hfth' : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hflh' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hl := IsLift.flatPullbackChow C f π j hU h r hr (isLift_chosenLift C f π j hU g k α)
  rw [infinityCap_eq_of_isLift C f π j hU L s hcompl htriv hl]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (heq_map_index (by ring : k + (r : ℤ) + 1 = k + 1 + (r : ℤ))
    (chowGroupDegreeEquiv_heq C _ _ _) fun n x ↦ divisorMiddleCap C f π L s (h ≫ g) n x).trans ?_
  refine (middleCap_flatPullbackChow C (gysinSystemOfInvertible C)
    (gysinTripleInclusion L s ≫ (π ≫ f)) (π ≫ f) (gysinTripleInclusion L s) π rfl 1
    (divisorClass C f π L s) g h r hr h' sq hfst (k + 1) _).trans ?_
  exact flatPullbackChow_heq_of_degree C _ _ h' _ r _ (by ring : k + 1 - 1 = k - 0) _ _
    (chowGroupDegreeEquiv_heq C _ _ _).symm

include hcompl htriv in
/-- `infinityCap` commutes with the Gysin map `i_D^*` of the zero scheme `D = Z(t)` of a section
`t` of an invertible module `M` on `T`, transported to `E` through `e`. -/
theorem infinityCap_gysin {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T M t
    let L' := (Scheme.Modules.pullback (pullback.snd (gysinTripleInclusion L s ≫ π) g)).obj M
    let s' := AlgebraicGeometry.pullbackGlobalSections
      (pullback.snd (gysinTripleInclusion L s ≫ π) g) M t
    let E := Stacks.Divisors.zeroScheme (pullback (gysinTripleInclusion L s ≫ π) g) L' s'
    ∀ (e : pullback (gysinTripleInclusion L s ≫ π) (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι =
        bivariantBaseChangeMap (gysinTripleInclusion L s ≫ π) g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
          (gysinTripleInclusion L s ≫ (π ≫ f))) =
        pullback.fst (gysinTripleInclusion L s ≫ π) (D.subschemeι ≫ g) ≫
          (gysinTripleInclusion L s ≫ (π ≫ f)))
      (α : chowGroup C (g ≫ f) (k + 1)),
      properChowPushforward C (pullback.fst (gysinTripleInclusion L s ≫ π) (D.subschemeι ≫ g) ≫
          (gysinTripleInclusion L s ≫ (π ≫ f)))
          (E.subschemeι ≫ pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
            (gysinTripleInclusion L s ≫ (π ≫ f))) e.hom hbase (k - 0)
          (properPushforwardDescends C _ _ _ _ _)
          (infinityCap C f π j hU L s hcompl htriv (D.subschemeι ≫ g) k
            ((gysinSystemOfInvertible C).onChow (g ≫ f) M t k α)) =
        (gysinSystemOfInvertible C).onChow (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
            (gysinTripleInclusion L s ≫ (π ≫ f))) L' s' (k - 0)
          (Eq.mp (congrArg (chowGroup C (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
              (gysinTripleInclusion L s ≫ (π ≫ f)))) (by omega : (k + 1) - 0 = (k - 0) + 1))
            (infinityCap C f π j hU L s hcompl htriv g (k + 1) α)) := by
  dsimp only
  intro e he hbase α
  have hl := IsLift.gysin C f π j hU M t (isLift_chosenLift C f π j hU g (k + 1) α)
  have e1 := infinityCap_eq_of_isLift C f π j hU L s hcompl htriv hl
  have hx : properChowPushforward C _ _ (bivariantDivisorBaseChangeIso π g M t).hom
      (bivariantDivisorBaseChangeIso_hom_comp_structure (π ≫ f) π g M t) (k + 1)
      (properPushforwardDescends C _ _ _ _ _)
      (chowPushforwardOfIso C ((testDivisor π g M t).subschemeι ≫ testStr C f π g)
        (testStr C f π ((Stacks.Divisors.zeroScheme T M t).subschemeι ≫ g))
            (bivariantDivisorBaseChangeIso π g M t).inv
        (by rw [Iso.inv_comp_eq, testStr, testStr,
          bivariantDivisorBaseChangeIso_hom_comp_structure]) (k + 1)
        ((gysinSystemOfInvertible C).onChow (testStr C f π g)
          ((Scheme.Modules.pullback (pullback.snd π g)).obj M)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd π g) M t) (k + 1) (chosenLift C f
              π j hU g (k + 1) α))) =
      (gysinSystemOfInvertible C).onChow (testStr C f π g)
          ((Scheme.Modules.pullback (pullback.snd π g)).obj M)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd π g) M t) (k + 1) (chosenLift C f
              π j hU g (k + 1) α) := by
    have h1 := (chowGroupEquivOfIso C ((testDivisor π g M t).subschemeι ≫ testStr C f π g)
      (testStr C f π ((Stacks.Divisors.zeroScheme T M t).subschemeι ≫ g))
          (bivariantDivisorBaseChangeIso π g M t).inv
      (by rw [Iso.inv_comp_eq, testStr, testStr,
        bivariantDivisorBaseChangeIso_hom_comp_structure]) (k + 1)).left_inv
      ((gysinSystemOfInvertible C).onChow (testStr C f π g)
        ((Scheme.Modules.pullback (pullback.snd π g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd π g) M t) (k + 1) (chosenLift C f π
            j hU g (k + 1) α))
    refine Eq.trans ?_ h1
    exact congrFun (congrArg DFunLike.coe (chowPushforwardOfIso_congr C _ _
        (bivariantDivisorBaseChangeIso π g M t).hom
      (inv (bivariantDivisorBaseChangeIso π g M t).inv) (by simp) _ _ (k + 1))) _
  have hmid := middleCap_gysin C (gysinSystemOfInvertible C)
    (gysinTripleInclusion L s ≫ (π ≫ f)) (π ≫ f) (gysinTripleInclusion L s) π rfl 1
    (divisorClass C f π L s) f rfl (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) g M t (k + 1) _ (chosenLift C
        f π j hU g (k + 1) α) hx e he
    hbase (properPushforwardDescends C _ _ _ _ _)
  refine (congrArg (properChowPushforward C _ _ e.hom hbase (k - 0)
    (properPushforwardDescends C _ _ _ _ _)) e1).trans ?_
  refine (chowGroupDegreeEquiv_properChowPushforward_comp C _ _ e.hom hbase
    (by ring : k + 1 - 1 = k - 0) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).symm.trans ?_
  refine (congrArg (chowGroupDegreeEquiv C _ (by ring : k + 1 - 1 = k - 0)) hmid).trans ?_
  refine (GysinSystem.onChow_chowGroupDegreeEquiv (gysinSystemOfInvertible C) _ _ _
    (by ring : k + 1 - 1 = k - 0) (by ring) _).trans ?_
  refine congrArg _ (eq_of_heq ?_)
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (cast_heq _ _).trans ?_
  refine HEq.trans ?_ (cast_heq _ _).symm
  exact (chowGroupDegreeEquiv_heq C _ _ _).symm

include hcompl htriv in
/-- The bivariant class `C ∈ A⁰(Z(s) ⟶ X)` capping by `α ↦ i^* β` for every lift `β` of `α` over
`U`. -/
def infinityClass :
    BivariantClass C (gysinSystemOfInvertible C) (gysinTripleInclusion L s ≫ (π ≫ f)) f
      (gysinTripleInclusion L s ≫ π) (Category.assoc _ _ _) 0 where
  cap g _ k := infinityCap C f π j hU L s hcompl htriv g k
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    exact infinityCap_properChowPushforward C f π j hU L s hcompl htriv g h h' sq hfst k α
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ r hr h' sq hfst k α
    exact infinityCap_flatPullbackChow C f π j hU L s hcompl htriv g h r hr h' sq hfst k α
  cap_gysin := by
    intro T g _ M _ t k
    exact infinityCap_gysin C f π j hU L s hcompl htriv g M t k

end Class

end GysinAtInfinity

end Stacks.Chow

end
