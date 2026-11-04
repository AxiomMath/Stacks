module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class

/-!
# Capping a class on the middle fibre product

Let `a ∈ A^p(X ⟶ Y)` be a bivariant class and `g : Y ⟶ Z` a morphism, all locally of finite type
over the base of chapter 42. For a test scheme `t : T ⟶ Z` and a class `x` on `T ×_Z Y`, the class
`a ∩ x` lives on `(T ×_Z Y) ×_Y X`, which is `T ×_Z X` by the associativity of fibre products.
This file records how `x ↦ a ∩ x`, read on `T ×_Z X`, behaves under the three operations of
Stacks 0B76 applied to `x` along the base change of a morphism of test schemes. These are the
three naturality conditions of the composite of Stacks 0B75 with the inner class removed: they
hold for an arbitrary class `x` on the middle fibre product, not only for one of the form `b ∩ α`.
They are what is needed to build a bivariant class from `a` and a family of classes on the middle
fibre products that is natural only up to the kernel of `a ∩ -`, as in Stacks 0F9J.

## Main definitions

* `Stacks.Chow.middleCap` — the operation `x ↦ a ∩ x`, read on `T ×_Z X`.

## Main results

* `Stacks.Chow.middleCap_properChowPushforward`, `Stacks.Chow.middleCap_flatPullbackChow` and
  `Stacks.Chow.middleCap_gysin` — the three compatibilities.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Middle

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p : ℤ)
  (a : BivariantClass C G sX sY f hf p)

/-- Capping a class on the middle fibre product `T ×_Z Y` with `a`, read on `T ×_Z X` through the
associativity isomorphism of fibre products. -/
def middleCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (m : ℤ) :
    chowGroup C (pullback.fst g t ≫ sY) m →+ chowGroup C (pullback.fst (f ≫ g) t ≫ sX) (m - p) :=
  (properChowPushforward C (pullback.fst f (pullback.fst g t) ≫ sX)
      (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (m - p)
      (properPushforwardDescends C _ _ _ _ _)).comp
    (a.cap (pullback.fst g t) m)

omit [LocallyOfFiniteType g] in
/-- `middleCap` applied to `x` is the pushforward of `a ∩ x` along the associativity isomorphism
`(T ×_Z Y) ×_Y X ≅ T ×_Z X`. -/
theorem middleCap_apply {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (m : ℤ)
    (x : chowGroup C (pullback.fst g t ≫ sY) m) :
    middleCap C G sX sY f g hf p a t m x =
      properChowPushforward C (pullback.fst f (pullback.fst g t) ≫ sX)
        (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) (m - p)
        (properPushforwardDescends C _ _ _ _ _) (a.cap (pullback.fst g t) m x) :=
  rfl

/-- Local finite type and flatness are stable under base change. -/
private theorem lft_and_flat_of_isPullback {P Q R S : Scheme.{u}} {a : P ⟶ Q} {b : P ⟶ R}
    {c : Q ⟶ S} {d : R ⟶ S} (sq : IsPullback a b c d) [LocallyOfFiniteType c] [Flat c] :
    LocallyOfFiniteType b ∧ Flat b :=
  ⟨MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance,
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance⟩

omit [LocallyOfFiniteType g] in
/-- **Proper pushforward.** For a proper morphism `h : T' ⟶ T` of test schemes, capping commutes
with pushforward along the base changes of `h`. -/
theorem middleCap_properChowPushforward {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h]
    (h' : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t)
    (sq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) h' h (pullback.snd (f ≫ g) t))
    (hfst : h' ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t)) (m : ℤ)
    (x : chowGroup C (pullback.fst g (h ≫ t) ≫ sY) m) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    letI : IsProper (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h) (P := @IsProper)
        inferInstance
    middleCap C G sX sY f g hf p a t m
        (properChowPushforward C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY)
          (compositeMiddleBaseChange g t h)
          (by rw [← Category.assoc, compositeMiddleBaseChange_fst]) m
          (properPushforwardDescends C _ _ _ _ _) x) =
      properChowPushforward C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
        (pullback.fst (f ≫ g) t ≫ sX) h' (by rw [← Category.assoc, hfst]) (m - p)
        (properPushforwardDescends C _ _ _ _ _)
        (middleCap C G sX sY f g hf p a (h ≫ t) m x) := by
  have hprop : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have sqM := isPullback_bivariantBaseChangeMap g t h
  have hpropM : IsProper (compositeMiddleBaseChange g t h) :=
    MorphismProperty.of_isPullback sqM (P := @IsProper) inferInstance
  have sqT := isPullback_baseChangeMapOfEq f (pullback.fst g t) (compositeMiddleBaseChange g t h)
    (pullback.fst g (h ≫ t)) (compositeMiddleBaseChange_fst g t h)
  have hpropT : IsProper (compositeTopBaseChange f g t h) :=
    MorphismProperty.of_isPullback sqT (P := @IsProper) inferInstance
  rw [middleCap_apply, middleCap_apply,
    a.proper_naturality_of_test_eq (pullback.fst g t) (compositeMiddleBaseChange g t h)
      (pullback.fst g (h ≫ t)) (compositeMiddleBaseChange_fst g t h)
      (compositeTopBaseChange f g t h) sqT
      (baseChangeMapOfEq_fst f (pullback.fst g t) (compositeMiddleBaseChange g t h)
        (pullback.fst g (h ≫ t)) (compositeMiddleBaseChange_fst g t h))
      m (by rw [← Category.assoc, compositeMiddleBaseChange_fst])
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  exact properChowPushforward_comp_eq C
    (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX) (pullback.fst f (pullback.fst g t) ≫ sX)
    (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX)
    (compositeTopBaseChange f g t h) (pullbackRightPullbackFstIso g t f).hom
    (pullbackRightPullbackFstIso g (h ≫ t) f).hom h'
    (compositeTopBaseChange_comp_pullbackRightPullbackFstIso f g t h h' sq hfst)
    (baseChangeMapOfEq_comp_structure sX f (pullback.fst g t)
      (compositeMiddleBaseChange g t h) (pullback.fst g (h ≫ t))
      (compositeMiddleBaseChange_fst g t h))
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t)
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g (h ≫ t))
    (by rw [← Category.assoc, hfst]) (m - p) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (a.cap (pullback.fst g (h ≫ t)) m x)

omit [LocallyOfFiniteType g] in
/-- **Flat pullback.** For a flat morphism `h : T' ⟶ T` of test schemes of relative dimension
`r`, capping commutes with flat pullback along the base changes of `h`. -/
theorem middleCap_flatPullbackChow {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback (f ≫ g) (h ≫ t) ⟶ pullback (f ≫ g) t)
    (sq : IsPullback (pullback.snd (f ≫ g) (h ≫ t)) h' h (pullback.snd (f ≫ g) t))
    (hfst : h' ≫ pullback.fst (f ≫ g) t = pullback.fst (f ≫ g) (h ≫ t)) (m : ℤ)
    (x : chowGroup C (pullback.fst g t ≫ sY) m) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    letI : LocallyOfFiniteType (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (compositeMiddleBaseChange g t h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap g t h) (P := @Flat)
        inferInstance
    middleCap C G sX sY f g hf p a (h ≫ t) (m + (r : ℤ))
        (flatPullbackChow C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY)
          (compositeMiddleBaseChange g t h)
          (by rw [← Category.assoc, compositeMiddleBaseChange_fst]) r
          (AlgebraicGeometry.RelativeDimension.of_isPullback
            (isPullback_bivariantBaseChangeMap g t h) hr) m
          (flatPullbackDescends C _ _ _ _ _ _ _) x) ≍
      flatPullbackChow C (pullback.fst (f ≫ g) (h ≫ t) ≫ sX)
        (pullback.fst (f ≫ g) t ≫ sX) h' (by rw [← Category.assoc, hfst]) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (m - p)
        (flatPullbackDescends C _ _ _ _ _ _ _)
        (middleCap C G sX sY f g hf p a t m x) := by
  have hr' := AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
  obtain ⟨hfth', hflh'⟩ := lft_and_flat_of_isPullback sq
  have sqM := isPullback_bivariantBaseChangeMap g t h
  obtain ⟨hftM, hflM⟩ := lft_and_flat_of_isPullback sqM
  have hrM : AlgebraicGeometry.RelativeDimension (compositeMiddleBaseChange g t h) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sqM hr
  have hMfst := compositeMiddleBaseChange_fst g t h
  have sqT := isPullback_baseChangeMapOfEq f (pullback.fst g t) (compositeMiddleBaseChange g t h)
    (pullback.fst g (h ≫ t)) hMfst
  obtain ⟨hftT, hflT⟩ := lft_and_flat_of_isPullback sqT
  have hrT : AlgebraicGeometry.RelativeDimension (compositeTopBaseChange f g t h) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sqT hrM
  have hTfst := baseChangeMapOfEq_fst f (pullback.fst g t) (compositeMiddleBaseChange g t h)
    (pullback.fst g (h ≫ t)) hMfst
  have hbQt := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t
  have hbQht := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g (h ≫ t)
  have hbT := baseChangeMapOfEq_comp_structure sX f (pullback.fst g t)
    (compositeMiddleBaseChange g t h) (pullback.fst g (h ≫ t)) hMfst
  have hbM : compositeMiddleBaseChange g t h ≫ (pullback.fst g t ≫ sY) =
      pullback.fst g (h ≫ t) ≫ sY := by rw [← Category.assoc, hMfst]
  have hbh' : h' ≫ (pullback.fst (f ≫ g) t ≫ sX) = pullback.fst (f ≫ g) (h ≫ t) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hsqIso := compositeTopBaseChange_comp_pullbackRightPullbackFstIso f g t h h' sq hfst
  have hfacT := flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C
    (pullback.fst f (pullback.fst g t) ≫ sX)
    (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX)
    (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullbackRightPullbackFstIso g t f).hom hbQt
    (pullbackRightPullbackFstIso g (h ≫ t) f).hom hbQht (compositeTopBaseChange f g t h) hbT
    h' hbh' hsqIso r hrT hr' (m - p) (flatPullbackDescends C _ _ _ _ _ _ _)
  have ha := a.flat_naturality_of_test_eq (pullback.fst g t)
    (compositeMiddleBaseChange g t h) r hrM
    (pullback.fst g (h ≫ t)) hMfst (compositeTopBaseChange f g t h) sqT hTfst m hbM hrT
    (flatPullbackDescends C _ _ _ _ _ _ _) hfacT x
  have hidx₂ : (m + (r : ℤ)) - p = (m - p) + (r : ℤ) := by omega
  have hres := heq_map_index hidx₂ ha fun n x ↦
    properChowPushforward C (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX)
      (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullbackRightPullbackFstIso g (h ≫ t) f).hom
      hbQht n (properPushforwardDescends C _ _ _ _ _) x
  refine hres.trans (heq_of_eq ?_)
  exact (flatPullbackChow_chowPushforwardOfIso C (pullback.fst f (pullback.fst g t) ≫ sX)
    (pullback.fst f (pullback.fst g (h ≫ t)) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX)
    (pullback.fst (f ≫ g) (h ≫ t) ≫ sX) (pullbackRightPullbackFstIso g t f).hom hbQt
    (pullbackRightPullbackFstIso g (h ≫ t) f).hom hbQht (compositeTopBaseChange f g t h) hbT
    h' hbh' hsqIso r hrT hr' (m - p) hfacT (flatPullbackDescends C _ _ _ _ _ _ _)
    (a.cap (pullback.fst g t) m x)).symm

/-- **The Gysin map of a divisor on the test scheme.** Let `D = Z(s)` be the zero scheme of a
section of an invertible module on `T`, let `x` be a class on `T ×_Z Y` and `x_D` a class on
`D ×_Z Y` whose image under the identification of Stacks 0B6Y is the Gysin image of `x`. Then the
Gysin image of `a ∩ x` is `a ∩ x_D`, read through the identification of the base change of `D`
with the zero scheme on `T ×_Z X`. -/
theorem middleCap_gysin (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (hg : g ≫ sZ = sY) (hgys :
    G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback (f ≫ g) t).sheaf.obj
      (pullback (f ≫ g) t).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)]
    (s : Γ(L, ⊤)) (m : ℤ)
    (xD : chowGroup C (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
      m)
    (x : chowGroup C (pullback.fst g t ≫ sY) (m + 1))
    (hx : properChowPushforward C
        (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
        ((Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY)
        (bivariantDivisorBaseChangeIso g t L s).hom
        (bivariantDivisorBaseChangeIso_hom_comp_structure sY g t L s) m
        (properPushforwardDescends C _ _ _ _ _) xD =
      G.onChow (pullback.fst g t ≫ sY) ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) m x) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s
    let E := Stacks.Divisors.zeroScheme (pullback (f ≫ g) t) L' s'
    ∀ (e : pullback (f ≫ g) (D.subschemeι ≫ t) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap (f ≫ g) t D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) =
        pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
        (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) e.hom hbase (m - p)),
      properChowPushforward C (pullback.fst (f ≫ g) (D.subschemeι ≫ t) ≫ sX)
          (E.subschemeι ≫ pullback.fst (f ≫ g) t ≫ sX) e.hom hbase (m - p) hfac
          (middleCap C G sX sY f g hf p a (D.subschemeι ≫ t) m xD) =
        G.onChow (pullback.fst (f ≫ g) t ≫ sX) L' s' (m - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst (f ≫ g) t ≫ sX))
            (by omega : (m + 1) - p = (m - p) + 1))
            (middleCap C G sX sY f g hf p a t (m + 1) x)) := by
  dsimp only
  intro e he hbase hfac
  have hidx : (m + 1) - p = (m - p) + 1 := by omega
  have hMfst := bivariantDivisorBaseChangeIso_hom_comp_fst g t L s
  have sqX := isPullback_baseChangeMapOfEq f
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst
  have hpropX := MorphismProperty.of_isPullback sqX (P := @IsProper) inferInstance
  have hQ := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t
  have hQD := pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)
  have hpA := compositeInnerSnd_comp_structure sX sY sZ f g t hf hg
  have hpB := compositeOuterSnd_comp_structure sX sY sZ f g t hf hg
  have hMbase := bivariantDivisorBaseChangeIso_hom_comp_structure sY g t L s
  have hXfst := baseChangeMapOfEq_fst f
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst
  have hXbase := baseChangeMapOfEq_comp_structure sX f
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst
  have hEbase := bivariantDivisorBaseChangeIso_hom_subschemeι f (pullback.fst g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)
  have hAbase := bivariantDivisorBaseChangeIso_hom_comp_structure sX f (pullback.fst g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)
  have hzcbase := zeroScheme_pullback_comp_eqToHom_comp_structure sX f g t L s
  have hvbase := compositeDivisorComparisonMiddle_comp_structure sX f g t L s
  have hwbase := compositeDivisorComparison_comp_structure sX f g t L s
  have hjbase := comp_comp_of_comp (zeroSchemePullbackIso_hom_subschemeι
    (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd (f ≫ g) t)
    (pullbackRightPullbackFstIso g t f).hom (pullbackRightPullbackFstIso_hom_snd g t f) L s) hQ
  have ha := a.proper_naturality_of_test_eq
    ((Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t) (bivariantDivisorBaseChangeIso g t L s).hom
    (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t)) hMfst _ sqX hXfst
    m hMbase (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) xD
  have hagys := a.gysin_naturality (pullback.fst g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) m
    (bivariantDivisorBaseChangeIso f (pullback.fst g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)) hEbase hAbase
    (properPushforwardDescends C _ _ _ _ _) x
  have hcomp := hgysc (pullback.snd f (pullback.fst g t)) (pullback.snd g t)
    (pullback.fst f (pullback.fst g t) ≫ sX) L s (m - p)
    (Eq.mp (congrArg (chowGroup C (pullback.fst f (pullback.fst g t) ≫ sX)) hidx)
      (a.cap (pullback.fst g t) (m + 1) x))
  have hgysApplied := GysinSystem.onChow_baseChangeIso hgys (t ≫ sZ)
    (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd (f ≫ g) t)
    (pullback.fst f (pullback.fst g t) ≫ sX) (pullback.fst (f ≫ g) t ≫ sX) hpA hpB
    (pullbackRightPullbackFstIso g t f).hom (pullbackRightPullbackFstIso_hom_snd g t f) hQ L s
    (m - p)
    (zeroSchemePullbackIso (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t)
      (pullback.snd (f ≫ g) t) (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_snd g t f) L s).hom
    (zeroSchemePullbackIso_hom_subschemeι
      (pullback.snd f (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd (f ≫ g) t)
      (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_snd g t f) L s) hjbase
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (Eq.mp (congrArg (chowGroup C (pullback.fst f (pullback.fst g t) ≫ sX)) hidx)
      (a.cap (pullback.fst g t) (m + 1) x))
  refine gysinNaturalityAssemble C hQD hbase hwbase hjbase hQ
    (compositeDivisorIso_square f g t L s e he) hidx (properPushforwardDescends C _ _ _ _ _)
    hfac (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (middleCap_apply C G sX sY f g hf p a
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) m xD)
    (middleCap_apply C G sX sY f g hf p a t (m + 1) x) ?_ hgysApplied
  exact gysinInnerLegAssemble C hXbase hAbase hzcbase hvbase hwbase (m - p) m
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) ha hx hagys hcomp

end Middle

end Stacks.Chow

end
