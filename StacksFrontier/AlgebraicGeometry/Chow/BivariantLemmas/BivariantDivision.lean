module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ElementCap
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent

/-!
# Dividing a bivariant class by one that is bijective on Chow groups

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S`, let `a ∈ A^p(X ⟶ Y)` and
let `b ∈ A^{p+q}(X ⟶ Z)`. Suppose that for every test scheme `T ⟶ Z` locally of finite type
capping with `a` is a bijection

  `a ∩ - : A_m(T ×_Z Y) ⟶ A_{m-p}(T ×_Z X)`

(read on `T ×_Z X` through the associativity of fibre products). Then the rule

  `α ↦ (a ∩ -)⁻¹ (b ∩ α)`

is a bivariant class `c ∈ A^q(Y ⟶ Z)`, and it is the unique bivariant class with `a ∘ c = b`.
This is the formal step of the construction preceding Stacks 0FBK: there `a = p^*` is the flat
pullback along the projection of a vector bundle, bijective on Chow groups by Stacks 02TY, and
`b = i_* ∘ j^* ∘ C`; the source's "since both `i_* ∘ j^* ∘ C` and `p^*` are bivariant classes we
can use the equation `i_* ∘ j^* ∘ C = p^* ∘ c` to define `c` as a bivariant class" is
`Stacks.Chow.bivariantQuotient` below.

Each of the three conditions of Stacks 0B76 for the rule is deduced from the same condition for
`b`, the corresponding compatibility of capping with `a` on the middle fibre products
(`Stacks.Chow.middleCap_properChowPushforward`, `Stacks.Chow.middleCap_flatPullbackChow`,
`Stacks.Chow.middleCap_gysin`), and the injectivity of `a ∩ -`.

## Main definitions

* `Stacks.Chow.quotientCap` — the cap operation `α ↦ (a ∩ -)⁻¹ (b ∩ α)`.
* `Stacks.Chow.bivariantQuotient` — the bivariant class `c ∈ A^q(Y ⟶ Z)` with `a ∘ c = b`.

## Main results

* `Stacks.Chow.isBivariantClassComposition_bivariantQuotient` — `a ∘ c = b`, in the form of the
  characterization `Stacks.Chow.IsBivariantClassComposition` of the composite.
* `Stacks.Chow.eq_bivariantQuotient_of_isBivariantClassComposition` — `c` is the only bivariant
  class with `a ∘ c = b`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Proper pushforward along an isomorphism over the base is bijective on Chow groups. -/
theorem properChowPushforward_bijective_of_isIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k) :
    Function.Bijective (properChowPushforward C sA sB u hu k hfac) := by
  rw [properChowPushforward_eq_chowPushforwardOfIso]
  refine ⟨chowPushforwardOfIso_injective C sA sB u hu k, fun y ↦ ?_⟩
  have hinv : inv u ≫ sA = sB := by
    rw [← hu, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  refine ⟨chowPushforwardOfIso C sB sA (inv u) hinv k y, ?_⟩
  rw [chowPushforwardOfIso_comp_apply C sB sA sB (inv u) u hinv hu k y,
    chowPushforwardOfIso_congr_apply C sB sB (inv u ≫ u) (𝟙 B) (by simp) _
      (Category.id_comp sB) k, chowPushforwardOfIso_id]

/-- Proper pushforward along the identification of Stacks 0B6Y is bijective on Chow groups. -/
private theorem properChowPushforward_bijective_divisorBaseChangeIso (C : ChowSituation.{u})
    {Y Z T : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (t : T ⟶ Z) [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    Function.Bijective (properChowPushforward C
      (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
      ((Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY)
      (bivariantDivisorBaseChangeIso g t L s).hom
      (bivariantDivisorBaseChangeIso_hom_comp_structure sY g t L s) k
      (properPushforwardDescends C _ _ _ _ _)) :=
  properChowPushforward_bijective_of_isIso C _ _ _ _ k _

section Quotient

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p q : ℤ)
  (a : BivariantClass C G sX sY f hf p)
  (b : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q))
  (hbij : ∀ {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (m : ℤ),
    Function.Bijective (middleCap C G sX sY f g hf p a t m))

/-- The cap operation `α ↦ (a ∩ -)⁻¹ (b ∩ α)` of the quotient of `b` by `a`. -/
def quotientCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (t ≫ sZ) k →+ chowGroup C (pullback.fst g t ≫ sY) (k - q) :=
  (AddEquiv.ofBijective _ (hbij t (k - q))).symm.toAddMonoidHom.comp
    ((chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX)
      (by ring : k - (p + q) = k - q - p)).toAddMonoidHom.comp (b.cap t k))

/-- Capping the quotient with `a` gives back `b`. -/
theorem middleCap_quotientCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    middleCap C G sX sY f g hf p a t (k - q)
        (quotientCap C G sX sY sZ f g hf hg p q a b hbij t k α) =
      chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX)
        (by ring : k - (p + q) = k - q - p) (b.cap t k α) :=
  (AddEquiv.ofBijective _ (hbij t (k - q))).apply_symm_apply _

omit [LocallyOfFiniteType g] in
/-- A morphism of test schemes over `Z` determines the map of base changes along `g`. -/
theorem eq_compositeMiddleBaseChange {T T' : Scheme.{u}} (t : T ⟶ Z) (h : T' ⟶ T)
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) :
    h' = compositeMiddleBaseChange g t h := by
  refine pullback.hom_ext ?_ ?_
  · rw [hfst, compositeMiddleBaseChange_fst]
  · rw [← sq.w, compositeMiddleBaseChange_snd]

/-- **Stacks 0B76 (1)** for the quotient: it commutes with proper pushforward. -/
theorem quotientCap_properChowPushforward {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h]
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ)
    (α : chowGroup C ((h ≫ t) ≫ sZ) k) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    quotientCap C G sX sY sZ f g hf hg p q a b hbij t k
        (properChowPushforward C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) k
          (properPushforwardDescends C _ _ _ _ _) α) =
      properChowPushforward C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) (k - q) (properPushforwardDescends C _ _ _ _ _)
        (quotientCap C G sX sY sZ f g hf hg p q a b hbij (h ≫ t) k α) := by
  obtain rfl := eq_compositeMiddleBaseChange g t h h' sq hfst
  have hprop : IsProper (compositeMiddleBaseChange g t h) :=
    MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have sqT := isPullback_bivariantBaseChangeMap (f ≫ g) t h
  have hpropT : IsProper (bivariantBaseChangeMap (f ≫ g) t h) :=
    MorphismProperty.of_isPullback sqT (P := @IsProper) inferInstance
  apply (hbij t (k - q)).1
  rw [middleCap_quotientCap, middleCap_properChowPushforward C G sX sY f g hf p a t h
    (bivariantBaseChangeMap (f ≫ g) t h) sqT (bivariantBaseChangeMap_fst (f ≫ g) t h) (k - q),
    middleCap_quotientCap,
    b.proper_naturality t h (bivariantBaseChangeMap (f ≫ g) t h) sqT
      (bivariantBaseChangeMap_fst (f ≫ g) t h) k (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) α]
  exact chowGroupDegreeEquiv_properChowPushforward_comp C _ _ _ _ _ _ _ _

omit [LocallyOfFiniteType g] in
include hbij in
/-- Capping with `a` detects heterogeneous equality across two readings of the degree. -/
theorem heq_of_middleCap_heq {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] {m m' : ℤ}
    (hm : m = m') {x : chowGroup C (pullback.fst g t ≫ sY) m}
    {y : chowGroup C (pullback.fst g t ≫ sY) m'}
    (h : middleCap C G sX sY f g hf p a t m x ≍ middleCap C G sX sY f g hf p a t m' y) :
    x ≍ y := by
  subst hm
  exact heq_of_eq ((hbij t m).1 (eq_of_heq h))

/-- **Stacks 0B76 (2)** for the quotient: it commutes with flat pullback. -/
theorem quotientCap_flatPullbackChow {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    quotientCap C G sX sY sZ f g hf hg p q a b hbij (h ≫ t) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) r hr k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) ≍
      flatPullbackChow C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (k - q)
        (flatPullbackDescends C _ _ _ _ _ _ _)
        (quotientCap C G sX sY sZ f g hf hg p q a b hbij t k α) := by
  obtain rfl := eq_compositeMiddleBaseChange g t h h' sq hfst
  have hftM : LocallyOfFiniteType (compositeMiddleBaseChange g t h) :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hflM : Flat (compositeMiddleBaseChange g t h) :=
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have sqT := isPullback_bivariantBaseChangeMap (f ≫ g) t h
  have hftT : LocallyOfFiniteType (bivariantBaseChangeMap (f ≫ g) t h) :=
    MorphismProperty.of_isPullback sqT (P := @LocallyOfFiniteType) inferInstance
  have hflT : Flat (bivariantBaseChangeMap (f ≫ g) t h) :=
    MorphismProperty.of_isPullback sqT (P := @Flat) inferInstance
  have hrT := AlgebraicGeometry.RelativeDimension.of_isPullback sqT hr
  refine heq_of_middleCap_heq C G sX sY f g hf p a hbij (h ≫ t)
    (by ring : k + (r : ℤ) - q = k - q + (r : ℤ)) ?_
  rw [middleCap_quotientCap]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (b.flat_naturality t h r hr (bivariantBaseChangeMap (f ≫ g) t h) sqT
    (bivariantBaseChangeMap_fst (f ≫ g) t h) k hrT (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) α).trans ?_
  refine HEq.trans ?_ (middleCap_flatPullbackChow C G sX sY f g hf p a t h r hr
    (bivariantBaseChangeMap (f ≫ g) t h) sqT (bivariantBaseChangeMap_fst (f ≫ g) t h) (k - q)
    (quotientCap C G sX sY sZ f g hf hg p q a b hbij t k α)).symm
  rw [middleCap_quotientCap]
  exact flatPullbackChow_heq_of_degree C _ _ _ _ r _ (by ring : k - (p + q) = k - q - p) _ _
    (chowGroupDegreeEquiv_heq C _ _ _).symm

include hbij in
/-- **Stacks 0B76 (3)** for the quotient: it commutes with the Gysin map of a divisor on the test
scheme. -/
theorem quotientCap_gysin (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd g t)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s
    let E := Stacks.Divisors.zeroScheme (pullback g t) L' s'
    ∀ (e : pullback g (D.subschemeι ≫ t) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap g t D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst g t ≫ sY) =
        pullback.fst g (D.subschemeι ≫ t) ≫ sY)
      (α : chowGroup C (t ≫ sZ) (k + 1)),
      properChowPushforward C (pullback.fst g (D.subschemeι ≫ t) ≫ sY)
          (E.subschemeι ≫ pullback.fst g t ≫ sY) e.hom hbase (k - q)
          (properPushforwardDescends C _ _ _ _ _)
          (quotientCap C G sX sY sZ f g hf hg p q a b hbij (D.subschemeι ≫ t) k
            (G.onChow (t ≫ sZ) L s k α)) =
        G.onChow (pullback.fst g t ≫ sY) L' s' (k - q)
          (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
            (by omega : (k + 1) - q = (k - q) + 1))
            (quotientCap C G sX sY sZ f g hf hg p q a b hbij t (k + 1) α)) := by
  intro D L' s' E e he hbase α
  have he' : e = bivariantDivisorBaseChangeIso g t L s := by
    ext1
    rw [← cancel_mono E.subschemeι, he, bivariantDivisorBaseChangeIso_hom_subschemeι]
  subst he'
  have hidx : (k + 1) - q = (k - q) + 1 := by omega
  set x'' := Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY)) hidx)
    (quotientCap C G sX sY sZ f g hf hg p q a b hbij t (k + 1) α) with hx''
  obtain ⟨xD, hxD⟩ := (properChowPushforward_bijective_divisorBaseChangeIso C sY g t L s
    (k - q)).2 (G.onChow (pullback.fst g t ≫ sY) L' s' (k - q) x'')
  rw [← hxD]
  congr 1
  apply (hbij (D.subschemeι ≫ t) (k - q)).1
  refine (middleCap_quotientCap C G sX sY sZ f g hf hg p q a b hbij (D.subschemeι ≫ t) k
    (G.onChow (t ≫ sZ) L s k α)).trans ?_
  apply (properChowPushforward_bijective_divisorBaseChangeIso C sX (f ≫ g) t L s
    (k - q - p)).1
  rw [middleCap_gysin C G sX sY f g hf p a sZ hg hgys hgysc t L s (k - q) xD x'' hxD
    (bivariantDivisorBaseChangeIso (f ≫ g) t L s)
    (bivariantDivisorBaseChangeIso_hom_subschemeι (f ≫ g) t L s)
    (bivariantDivisorBaseChangeIso_hom_comp_structure sX (f ≫ g) t L s)
    (properPushforwardDescends C _ _ _ _ _)]
  rw [← chowGroupDegreeEquiv_properChowPushforward_comp C _ _ _ _
    (by ring : k - (p + q) = k - q - p) (properPushforwardDescends C _ _ _ _ _),
    b.gysin_naturality t L s k (bivariantDivisorBaseChangeIso (f ≫ g) t L s)
      (bivariantDivisorBaseChangeIso_hom_subschemeι (f ≫ g) t L s)
      (bivariantDivisorBaseChangeIso_hom_comp_structure sX (f ≫ g) t L s)
      (properPushforwardDescends C _ _ _ _ _) α,
    GysinSystem.onChow_chowGroupDegreeEquiv G _ _ _ (by ring : k - (p + q) = k - q - p)
      (by ring)]
  congr 1
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine (heq_eq_mp_index (by omega : (k + 1) - (p + q) = (k - (p + q)) + 1) _).symm.trans ?_
  refine HEq.trans ?_ (heq_eq_mp_index (by omega : (k - q + 1) - p = (k - q - p) + 1) _)
  refine HEq.trans (chowGroupDegreeEquiv_heq C _ (by ring : (k + 1) - (p + q) = (k + 1) - q - p)
    (b.cap t (k + 1) α)).symm ?_
  rw [← middleCap_quotientCap C G sX sY sZ f g hf hg p q a b hbij t (k + 1) α]
  exact heq_map_index hidx (heq_eq_mp_index hidx _) fun n y ↦
    middleCap C G sX sY f g hf p a t n y

/-- The quotient `c ∈ A^q(Y ⟶ Z)` of `b ∈ A^{p+q}(X ⟶ Z)` by a class `a ∈ A^p(X ⟶ Y)` which is
bijective on the Chow groups of every test scheme: the bivariant class with cap operation
`α ↦ (a ∩ -)⁻¹ (b ∩ α)`. It is the unique class with `a ∘ c = b`. -/
def bivariantQuotient (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) : BivariantClass C G sY sZ g hg q where
  cap t _ k := quotientCap C G sX sY sZ f g hf hg p q a b hbij t k
  cap_properPushforward := by
    intro T T' t _ h _ h' sq hfst k α
    exact quotientCap_properChowPushforward C G sX sY sZ f g hf hg p q a b hbij t h h' sq hfst k α
  cap_flatPullbackChow := by
    intro T T' t _ h _ _ r hr h' sq hfst k α
    exact quotientCap_flatPullbackChow C G sX sY sZ f g hf hg p q a b hbij t h r hr h' sq hfst k α
  cap_gysin := by
    intro T t _ L _ s k D L' s' E e he hbase α
    exact quotientCap_gysin C G sX sY sZ f g hf hg p q a b hbij hgys hgysc t L s k e he hbase α

/-- The quotient caps by `α ↦ (a ∩ -)⁻¹ (b ∩ α)`, by construction. -/
theorem bivariantQuotient_cap (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (k : ℤ) :
    (bivariantQuotient C G sX sY sZ f g hf hg p q a b hbij hgys hgysc).cap t k =
      quotientCap C G sX sY sZ f g hf hg p q a b hbij t k :=
  rfl

/-- The quotient `c` of `b` by `a` satisfies `a ∘ c = b`, in the form of the characterization of
the composite of Stacks 0FE0. -/
theorem isBivariantClassComposition_bivariantQuotient (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    IsBivariantClassComposition C G sX sY sZ f g hf hg (properPushforwardDescends C) p q a
      (bivariantQuotient C G sX sY sZ f g hf hg p q a b hbij hgys hgysc) b := by
  intro T t _ k α
  refine HEq.trans ?_ (heq_of_eq (middleCap_quotientCap C G sX sY sZ f g hf hg p q a b hbij t k
    α).symm)
  exact (chowGroupDegreeEquiv_heq C _ _ _).symm

/-- The quotient is the only bivariant class `c` with `a ∘ c = b`. -/
theorem eq_bivariantQuotient_of_isBivariantClassComposition
    (hgys : G.IsNaturalUnderBaseChangeIso) (hgysc : G.IsNaturalUnderPullbackCompPushforward)
    (c : BivariantClass C G sY sZ g hg q)
    (hc : IsBivariantClassComposition C G sX sY sZ f g hf hg (properPushforwardDescends C) p q a
      c b) :
    c = bivariantQuotient C G sX sY sZ f g hf hg p q a b hbij hgys hgysc := by
  refine BivariantClass.ext C G sY sZ g hg q ?_
  intro T t _ k α
  apply (hbij t (k - q)).1
  refine Eq.trans ?_ (middleCap_quotientCap C G sX sY sZ f g hf hg p q a b hbij t k α).symm
  exact (eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans (hc t k α))).symm

end Quotient

end Stacks.Chow

end
