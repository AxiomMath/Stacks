module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleConeEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity

/-!
# Division of bivariant Chow classes by a class with bijective cap operations

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S`, and let `a ∈ A^p(X ⟶ Y)` be
a bivariant class whose cap operation `a ∩ - : A_m(T') ⟶ A_{m-p}(T' ×_Y X)` is bijective for
every test scheme `T' ⟶ Y` locally of finite type. Then for every `E ∈ A^e(X ⟶ Z)` and every
`q` with `p + q = e` there is a unique `c ∈ A^q(Y ⟶ Z)` with

  `a ∘ c = E`,

the composition being that of Stacks 0B75 (`Stacks.Chow.bivariantCompositeOfInvertible`, whose
cap operation is "cap with `c`, then with `a`"). On a test scheme `t : T ⟶ Z` the class `c` sends
`α ∈ A_k(T)` to the unique `β ∈ A_{k-q}(T ×_Z Y)` with `a ∩ β = E ∩ α`, the two sides being
compared on `T ×_Z X` through the associativity isomorphism `(T ×_Z Y) ×_Y X ≅ T ×_Z X`.

This is the step of the proof of Stacks 0FBK that *defines* the class `c(Z ⟶ X, 𝒩)`: there `a`
is the flat pullback `p^*` along the projection of the vector bundle `N ⟶ Z`, bijective on Chow
groups by Stacks 02TY, and `E = i_* ∘ j^* ∘ C`, so that the source's "we can use the equation
`i_* ∘ j^* ∘ C = p^* ∘ c(Z ⟶ X, 𝒩)` to define `c(Z ⟶ X, 𝒩)` as a bivariant class" is
`Stacks.Chow.bivariantDivision` with `p = -r`, `q = r` and `e = 0`.

The three naturality conditions of Stacks 0B76 for the quotient hold by cancelling `a`: in each of
them both sides become equal after the outer cap operation
`Stacks.Chow.bivariantCompositeOuterCap` of `a`, which is injective. After that operation the
left-hand side is the corresponding side for `E`, by the defining property of the quotient and the
condition for `E`, and the right-hand side is the same by the naturality of the outer cap
operation of a composite, which uses the conditions for `a` alone. In the Gysin condition the zero
scheme of the pulled-back section is identified with the base change of the zero scheme by an
isomorphism that the condition quantifies over; the square it is required to make pins it down to
`Stacks.Chow.bivariantDivisorBaseChangeIso`.

The degrees are `p` for `a`, `e` for `E` and `q` for the quotient, related by the hypothesis
`p + q = e`; the composite `a ∘ c` has degree `p + q`, and the equality `a ∘ c = E` is stated
through `Stacks.Chow.BivariantClass.copy` along that hypothesis. For Stacks 0FBK this reads
`p^* ∘ c(Z ⟶ X, 𝒩) = i_* ∘ j^* ∘ C` with `p = -r`, `q = r`, `e = 0`. The construction is at the
Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class rule, where
composition of bivariant classes needs no hypothesis.

## Main definitions

* `Stacks.Chow.BivariantClass.CapBijective` — every cap operation of a bivariant class is
  bijective.
* `Stacks.Chow.bivariantDivisionCap` — the cap operation `α ↦ (a ∩ -)⁻¹ (E ∩ α)`.
* `Stacks.Chow.bivariantDivision` — the bivariant class `c ∈ A^q(Y ⟶ Z)` with `a ∘ c = E`.

## Main results

* `Stacks.Chow.isBivariantClassComposition_bivariantDivision` and
  `Stacks.Chow.bivariantCompositeOfInvertible_bivariantDivision` — the composite of `a` with the
  quotient is `E`.
* `Stacks.Chow.eq_bivariantDivision_iff` and
  `Stacks.Chow.existsUnique_bivariantCompositeOfInvertible_eq` — the quotient is the only class
  whose composite with `a` is `E`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Bijective cap operations -/

/-- A bivariant class *has bijective cap operations* if every one of its cap operations
`A_k(T) ⟶ A_{k-p}(T ×_Y X)` is bijective. For the flat pullback along a vector bundle projection
this is Stacks 02TY. -/
def BivariantClass.CapBijective {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ} (c : BivariantClass C G sX sY f hf p) :
    Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ), Function.Bijective (c.cap g k)

/-- A class with bijective cap operations has injective cap operations. -/
theorem BivariantClass.CapBijective.capInjective {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    {c : BivariantClass C G sX sY f hf p} (hc : c.CapBijective) : c.CapInjective :=
  fun g _ k ↦ (hc g k).1

/-! ### The cap operation of the quotient -/

/-- A base change `h'` of `h` along `pullback.snd g t` compatible with the first projections is
`compositeMiddleBaseChange g t h`. -/
private theorem eq_compositeMiddleBaseChange {Y Z T T' : Scheme.{u}} (g : Y ⟶ Z) (t : T ⟶ Z)
    (h : T' ⟶ T)
    (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) :
    h' = compositeMiddleBaseChange g t h := by
  refine pullback.hom_ext ?_ ?_
  · rw [hfst, compositeMiddleBaseChange_fst]
  · rw [compositeMiddleBaseChange_snd, ← sq.w]

section Division

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p q e : ℤ) (hpqe : p + q = e)
  (a : BivariantClass C G sX sY f hf p) (ha : a.CapBijective)
  (E : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) e)

omit [LocallyOfFiniteType g] in
include ha in
/-- The outer cap operation of a composite with first factor `a` is bijective when the cap
operations of `a` are. -/
theorem bivariantCompositeOuterCap_bijective {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (m : ℤ) :
    Function.Bijective
      (bivariantCompositeOuterCap C G sX sY f g hf (properPushforwardDescends C) p a t m) :=
  ⟨bivariantCompositeOuterCap_injective C G sX sY f g hf (properPushforwardDescends C) p a t m
      (ha (pullback.fst g t) m).1,
    bivariantCompositeOuterCap_surjective C G sX sY f g hf (properPushforwardDescends C) p a t m
      (ha (pullback.fst g t) m).2⟩

include hpqe in
/-- The degree bookkeeping of the quotient: a class of degree `k - e` is one of degree
`(k - q) - p`. -/
theorem sub_eq_sub_sub_of_add_eq (k : ℤ) : k - e = k - q - p := by
  omega

include ha in
/-- The cap operation of the quotient of `E` by `a`: on a test scheme `t : T ⟶ Z` it sends `α` to
the unique `β` on `T ×_Z Y` whose cap with `a`, read on `T ×_Z X`, is `E ∩ α`. -/
def bivariantDivisionCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (t ≫ sZ) k →+ chowGroup C (pullback.fst g t ≫ sY) (k - q) :=
  (AddEquiv.ofBijective
      (bivariantCompositeOuterCap C G sX sY f g hf (properPushforwardDescends C) p a t (k - q))
      (bivariantCompositeOuterCap_bijective C G sX sY f g hf p a ha t
        (k - q))).symm.toAddMonoidHom.comp
    ((chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX)
      (sub_eq_sub_sub_of_add_eq p q e hpqe k)).toAddMonoidHom.comp (E.cap t k))

/-- The defining property of the quotient: capping the quotient's cap with `a` gives the cap with
`E`, read through the associativity isomorphism of pullbacks and the equality of degrees
`k - e = (k - q) - p`. -/
theorem bivariantCompositeOuterCap_bivariantDivisionCap {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    bivariantCompositeOuterCap C G sX sY f g hf (properPushforwardDescends C) p a t (k - q)
        (bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E t k α) =
      chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX)
        (sub_eq_sub_sub_of_add_eq p q e hpqe k) (E.cap t k α) :=
  (AddEquiv.ofBijective _ (bivariantCompositeOuterCap_bijective C G sX sY f g hf p a ha t
    (k - q))).apply_symm_apply _

/-- The quotient's cap operation is the only one with its defining property. -/
theorem eq_bivariantDivisionCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) (β : chowGroup C (pullback.fst g t ≫ sY) (k - q))
    (hβ : bivariantCompositeOuterCap C G sX sY f g hf (properPushforwardDescends C) p a t (k - q)
        β = chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX)
          (sub_eq_sub_sub_of_add_eq p q e hpqe k) (E.cap t k α)) :
    β = bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E t k α :=
  (bivariantCompositeOuterCap_bijective C G sX sY f g hf p a ha t (k - q)).1
    (hβ.trans (bivariantCompositeOuterCap_bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe
      a ha E t k α).symm)

/-- The cap operation of the quotient commutes with proper pushforward along a morphism of test
schemes, the base change of the morphism being the one the proper-pushforward condition
quantifies over [Stacks, Tag 0B76] (1). -/
theorem bivariantDivisionCap_proper_naturality {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h] (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sZ) (t ≫ sZ) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) (k - q))
      (α : chowGroup C ((h ≫ t) ≫ sZ) k),
      bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E t k
          (properChowPushforward C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) k
            hfac α) =
        properChowPushforward C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
          (by rw [← Category.assoc, hfst]) (k - q) hfac'
          (bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E (h ≫ t) k α) := by
  intro hfac hfac' α
  have hprop : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  obtain rfl := eq_compositeMiddleBaseChange g t h h' sq hfst
  have sqE := isPullback_bivariantBaseChangeMap (f ≫ g) t h
  have hpropE : IsProper (compositeMiddleBaseChange (f ≫ g) t h) :=
    MorphismProperty.of_isPullback sqE (P := @IsProper) inferInstance
  refine (bivariantCompositeOuterCap_bijective C G sX sY f g hf p a ha t (k - q)).1 ?_
  rw [bivariantCompositeOuterCap_bivariantDivisionCap,
    bivariantCompositeOuterCap_proper_naturality C G sX sY f g hf (properPushforwardDescends C) p
      a t h (compositeMiddleBaseChange (f ≫ g) t h) sqE
      (compositeMiddleBaseChange_fst (f ≫ g) t h),
    bivariantCompositeOuterCap_bivariantDivisionCap,
    E.proper_naturality t h (compositeMiddleBaseChange (f ≫ g) t h) sqE
      (compositeMiddleBaseChange_fst (f ≫ g) t h) k hfac (properPushforwardDescends C _ _ _ _ _) α]
  exact chowGroupDegreeEquiv_properChowPushforward_comp C _ _ _ _
    (sub_eq_sub_sub_of_add_eq p q e hpqe k) _ _ _

/-- The cap operation of the quotient commutes with flat pullback of fixed relative dimension
along a morphism of test schemes [Stacks, Tag 0B76] (2). -/
theorem bivariantDivisionCap_flat_naturality {T T' : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (h' : pullback g (h ≫ t) ⟶ pullback g t)
    (sq : IsPullback (pullback.snd g (h ≫ t)) h' h (pullback.snd g t))
    (hfst : h' ≫ pullback.fst g t = pullback.fst g (h ≫ t)) (k : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sZ) (t ≫ sZ) h
        (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
        (by rw [← Category.assoc, hfst]) r hr' (k - q))
      (α : chowGroup C (t ≫ sZ) k),
      HEq
        (bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E (h ≫ t) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ t) ≫ sZ) (t ≫ sZ) h (by simp [Category.assoc]) r hr k
            hfac α))
        (flatPullbackChow C (pullback.fst g (h ≫ t) ≫ sY) (pullback.fst g t ≫ sY) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - q) hfac'
          (bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E t k α)) := by
  intro hr' hfac hfac' α
  have hfth' : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hflh' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  obtain rfl := eq_compositeMiddleBaseChange g t h h' sq hfst
  have sqE := isPullback_bivariantBaseChangeMap (f ≫ g) t h
  have hftE : LocallyOfFiniteType (compositeMiddleBaseChange (f ≫ g) t h) :=
    MorphismProperty.of_isPullback sqE (P := @LocallyOfFiniteType) inferInstance
  have hflE : Flat (compositeMiddleBaseChange (f ≫ g) t h) :=
    MorphismProperty.of_isPullback sqE (P := @Flat) inferInstance
  have hrE : AlgebraicGeometry.RelativeDimension (compositeMiddleBaseChange (f ≫ g) t h) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sqE hr
  have hdeg := sub_eq_sub_sub_of_add_eq p q e hpqe k
  -- the flat-pullback condition of `E`
  have hE := E.flat_naturality t h r hr (compositeMiddleBaseChange (f ≫ g) t h) sqE
    (compositeMiddleBaseChange_fst (f ≫ g) t h) k hrE hfac (flatPullbackDescends C _ _ _ _ _ _ _) α
  -- the flat-pullback condition of the outer cap operation
  have ho := bivariantCompositeOuterCap_flat_naturality C G sX sY f g hf
    (properPushforwardDescends C) p a t h r hr (compositeMiddleBaseChange (f ≫ g) t h) sqE
    (compositeMiddleBaseChange_fst (f ≫ g) t h) (k - q) hrE hfac'
    (flatPullbackDescends C _ _ _ _ _ _ _)
    (bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E t k α)
  refine heq_of_injective_heq
    (fun n x ↦ bivariantCompositeOuterCap C G sX sY f g hf (properPushforwardDescends C) p a
      (h ≫ t) n x)
    (fun n ↦ (bivariantCompositeOuterCap_bijective C G sX sY f g hf p a ha (h ≫ t) n).1)
    (by omega : (k + (r : ℤ)) - q = (k - q) + (r : ℤ)) ?_
  refine (heq_of_eq (bivariantCompositeOuterCap_bivariantDivisionCap C G sX sY sZ f g hf hg p q e
    hpqe a ha E (h ≫ t) (k + (r : ℤ)) _)).trans ?_
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans (hE.trans ?_)
  refine (flatPullbackChow_heq_of_degree C _ _ (compositeMiddleBaseChange (f ≫ g) t h) _ r hrE
    hdeg (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (chowGroupDegreeEquiv_heq C _ hdeg (E.cap t k α)).symm).trans ?_
  rw [← bivariantCompositeOuterCap_bivariantDivisionCap C G sX sY sZ f g hf hg p q e hpqe a ha E t
    k α]
  exact ho.symm

include hpqe in
/-- In the Gysin condition for the quotient, the class on `D ×_Z Y` is determined: if `ξ'` pushes
forward, along the identification of `D ×_Z Y` with the zero scheme of the pulled-back section, to
the Gysin map of the quotient's cap at `t`, then `ξ'` is the quotient's cap at the test scheme
`D ⟶ T ⟶ Z`. -/
private theorem eq_bivariantDivisionCap_gysin
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback g t).sheaf.obj
      (pullback g t).ringCatSheaf.property ((Scheme.Modules.pullback (pullback.snd g t)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ)
    (hbase : (bivariantDivisorBaseChangeIso g t L s).hom ≫
        ((Stacks.Divisors.zeroScheme (pullback g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY) =
      pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
    (α : chowGroup C (t ≫ sZ) (k + 1))
    (ξ' : chowGroup C (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
      (k - q))
    (hξ' : chowGroupEquivOfIso C
        (pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
        ((Stacks.Divisors.zeroScheme (pullback g t)
            ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t ≫ sY)
        (bivariantDivisorBaseChangeIso g t L s).hom hbase (k - q) ξ' =
      (gysinSystemOfInvertible C).onChow (pullback.fst g t ≫ sY)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) (k - q)
        (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
          (by omega : (k + 1) - q = (k - q) + 1))
          (bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha E
            t (k + 1) α))) :
    ξ' = bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe
      a ha E ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k
      ((gysinSystemOfInvertible C).onChow (t ≫ sZ) L s k α) := by
  have hdeg := sub_eq_sub_sub_of_add_eq p q e hpqe k
  have hdeg₁ := sub_eq_sub_sub_of_add_eq p q e hpqe (k + 1)
  -- the Gysin condition of the outer cap operation, applied to `ξ'`
  have ho := bivariantCompositeOuterCap_gysin_naturality C (gysinSystemOfInvertible C) sX sY sZ
    f g hf hg (properPushforwardDescends C) p a
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) t L s (k - q)
    ((k + 1) - q) (by omega) ξ'
    (bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha E t
      (k + 1) α) hξ'
    (bivariantDivisorBaseChangeIso (f ≫ g) t L s)
    (bivariantDivisorBaseChangeIso_hom_subschemeι (f ≫ g) t L s)
    (bivariantDivisorBaseChangeIso_hom_comp_structure sX (f ≫ g) t L s)
    (properPushforwardDescends C _ _ _ _ _)
  -- the Gysin condition of `E`
  have hE := E.gysin_naturality t L s k (bivariantDivisorBaseChangeIso (f ≫ g) t L s)
    (bivariantDivisorBaseChangeIso_hom_subschemeι (f ≫ g) t L s)
    (bivariantDivisorBaseChangeIso_hom_comp_structure sX (f ≫ g) t L s)
    (properPushforwardDescends C _ _ _ _ _) α
  have hinj : Function.Injective (properChowPushforward C
      (pullback.fst (f ≫ g) ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sX)
      ((Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
          ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
        pullback.fst (f ≫ g) t ≫ sX)
      (bivariantDivisorBaseChangeIso (f ≫ g) t L s).hom
      (bivariantDivisorBaseChangeIso_hom_comp_structure sX (f ≫ g) t L s) (k - q - p)
      (properPushforwardDescends C _ _ _ _ _)) :=
    chowPushforwardOfIso_injective C _ _ _ _ _
  refine (bivariantCompositeOuterCap_bijective C (gysinSystemOfInvertible C) sX sY f g hf p a
    ha ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) (k - q)).1 (hinj ?_)
  have hcomm := chowGroupDegreeEquiv_properChowPushforward_comp C
    (pullback.fst (f ≫ g) ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sX)
    ((Stacks.Divisors.zeroScheme (pullback (f ≫ g) t)
        ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s)).subschemeι ≫
      pullback.fst (f ≫ g) t ≫ sX)
    (bivariantDivisorBaseChangeIso (f ≫ g) t L s).hom
    (bivariantDivisorBaseChangeIso_hom_comp_structure sX (f ≫ g) t L s) hdeg
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (E.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k
      ((gysinSystemOfInvertible C).onChow (t ≫ sZ) L s k α))
  refine ho.trans (Eq.symm ?_)
  refine ((congrArg _ (bivariantCompositeOuterCap_bivariantDivisionCap C
    (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha E
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) k _)).trans hcomm.symm).trans ?_
  refine (congrArg _ hE).trans ?_
  refine (GysinSystem.onChow_chowGroupDegreeEquiv (gysinSystemOfInvertible C)
    (pullback.fst (f ≫ g) t ≫ sX) ((Scheme.Modules.pullback (pullback.snd (f ≫ g) t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (f ≫ g) t) L s) hdeg
    (by omega) _).trans ?_
  refine congrArg _ (eq_of_heq ?_)
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans
    ((heq_eq_mp_index (by omega : (k + 1) - e = (k - e) + 1) _).symm.trans ?_)
  refine HEq.trans ?_ (heq_eq_mp_index (by omega : (k + 1) - q - p = (k - q - p) + 1) _)
  refine HEq.trans ?_ (heq_of_eq (bivariantCompositeOuterCap_bivariantDivisionCap C
    (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha E t (k + 1) α).symm)
  exact (chowGroupDegreeEquiv_heq C _ hdeg₁ _).symm

/-- At the Gysin system of the first Chern class rule, the cap operation of the quotient commutes
with the Gysin map of the zero scheme of a section of an invertible module on a test scheme, the
base change of the zero scheme being identified with the zero scheme of the pulled-back section by
the isomorphism the Gysin condition quantifies over [Stacks, Tag 0B76] (3). -/
theorem bivariantDivisionCap_gysin_naturality
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback g t).sheaf.obj
      (pullback g t).ringCatSheaf.property ((Scheme.Modules.pullback (pullback.snd g t)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd g t)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s
    let E' := Stacks.Divisors.zeroScheme (pullback g t) L' s'
    ∀ (ε : pullback g (D.subschemeι ≫ t) ≅ E'.subscheme)
      (_hε : ε.hom ≫ E'.subschemeι = bivariantBaseChangeMap g t D.subschemeι)
      (hbase : ε.hom ≫ (E'.subschemeι ≫ pullback.fst g t ≫ sY) =
        pullback.fst g (D.subschemeι ≫ t) ≫ sY)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst g (D.subschemeι ≫ t) ≫ sY) (E'.subschemeι ≫ pullback.fst g t ≫ sY)
        ε.hom hbase (k - q))
      (α : chowGroup C (t ≫ sZ) (k + 1)),
      properChowPushforward C (pullback.fst g (D.subschemeι ≫ t) ≫ sY)
          (E'.subschemeι ≫ pullback.fst g t ≫ sY) ε.hom hbase (k - q) hfac
          (bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha
            E (D.subschemeι ≫ t) k ((gysinSystemOfInvertible C).onChow (t ≫ sZ) L s k α)) =
        (gysinSystemOfInvertible C).onChow (pullback.fst g t ≫ sY) L' s' (k - q)
          (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
            (by omega : (k + 1) - q = (k - q) + 1))
            (bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a
              ha E t (k + 1) α)) := by
  dsimp only
  intro ε hε hbase hfac α
  obtain rfl : ε = bivariantDivisorBaseChangeIso g t L s := by
    refine Iso.ext ?_
    rw [← cancel_mono (Stacks.Divisors.zeroScheme (pullback g t)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι, hε,
      bivariantDivisorBaseChangeIso_hom_subschemeι]
  -- the class `ξ'` on `D ×_Z Y` whose pushforward to the pulled-back divisor is the Gysin map of
  -- the quotient's cap at `t`
  obtain ⟨ξ', hξ'⟩ := (chowGroupEquivOfIso C (pullback.fst g
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ sY)
    ((Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
      pullback.fst g t ≫ sY)
    (bivariantDivisorBaseChangeIso g t L s).hom hbase (k - q)).surjective
    ((gysinSystemOfInvertible C).onChow (pullback.fst g t ≫ sY)
      ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s) (k - q)
      (Eq.mp (congrArg (chowGroup C (pullback.fst g t ≫ sY))
        (by omega : (k + 1) - q = (k - q) + 1))
        (bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha E
          t (k + 1) α)))
  have hξ := eq_bivariantDivisionCap_gysin C sX sY sZ f g hf hg p q e hpqe a ha E t L s k hbase
    α ξ' hξ'
  exact (congrArg (properChowPushforward C _ _ (bivariantDivisorBaseChangeIso g t L s).hom hbase
    (k - q) hfac) hξ).symm.trans hξ'

/-! ### The quotient -/

/-- The quotient of `E ∈ A^e(X ⟶ Z)` by `a ∈ A^p(X ⟶ Y)`, for `a` with bijective cap operations
and `p + q = e`: the unique bivariant class `c ∈ A^q(Y ⟶ Z)` with `a ∘ c = E`, with cap operation
`Stacks.Chow.bivariantDivisionCap`, `α ↦ (a ∩ -)⁻¹ (E ∩ α)`. This is the construction by which the
proof of Stacks 0FBK defines `c(Z ⟶ X, 𝒩)` from `p^* ∘ c(Z ⟶ X, 𝒩) = i_* ∘ j^* ∘ C`. -/
def bivariantDivision (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e) :
    BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q where
  cap t _ k :=
    bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha E t k
  cap_properPushforward t _ h _ h' sq hfst k α :=
    bivariantDivisionCap_proper_naturality C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e
      hpqe a ha E t h h' sq hfst k _ _ α
  cap_flatPullbackChow t _ h _ _ r hr h' sq hfst k α :=
    bivariantDivisionCap_flat_naturality C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e
      hpqe a ha E t h r hr h' sq hfst k _ _ _ α
  cap_gysin := by
    intro T t _ L _ s k
    dsimp only
    intro e' he hbase α
    exact bivariantDivisionCap_gysin_naturality C sX sY sZ f g hf hg p q e hpqe a ha E t L s k e'
      he hbase _ α

/-- The quotient caps by `Stacks.Chow.bivariantDivisionCap`. -/
@[simp]
theorem bivariantDivision_cap (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    (bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E).cap t k α =
      bivariantDivisionCap C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q e hpqe a ha E t k
        α :=
  rfl

/-- The composite of `a` with the quotient is `E`, in the form of the composition formula of
Stacks 0FE0: `E`, read in degree `p + q`, caps as `a ∩ (c ∩ -)`. -/
theorem isBivariantClassComposition_bivariantDivision
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e) :
    IsBivariantClassComposition C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
      (properPushforwardDescends C) p q a (bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E)
      (BivariantClass.copy C (gysinSystemOfInvertible C) sX sZ rfl
        (comp_comp_structureMorphism_eq hf hg) (comp_comp_structureMorphism_eq hf hg) hpqe.symm
        E) := by
  intro T t _ k α
  refine (BivariantClass.copy_cap C _ sX sZ rfl _ _ hpqe.symm E t k α).trans ?_
  rw [bivariantCompositeCap_eq_outerCap, bivariantDivision_cap,
    bivariantCompositeOuterCap_bivariantDivisionCap]
  exact (chowGroupDegreeEquiv_heq C _ _ _).symm

/-- The composite of `a` with the quotient is `E`: `a ∘ c = E` in `A^{p+q}(X ⟶ Z)`, with `E` read
in degree `p + q = e`. For Stacks 0FBK, with `a = p^*`, this is
`p^* ∘ c(Z ⟶ X, 𝒩) = i_* ∘ j^* ∘ C`. -/
theorem bivariantCompositeOfInvertible_bivariantDivision
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e) :
    bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a
        (bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E) =
      BivariantClass.copy C (gysinSystemOfInvertible C) sX sZ rfl
        (comp_comp_structureMorphism_eq hf hg) (comp_comp_structureMorphism_eq hf hg) hpqe.symm
        E :=
  eq_of_isBivariantClassComposition (hpp := properPushforwardDescends C)
    (isBivariantClassComposition_bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a _)
    (isBivariantClassComposition_bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E)

/-- A class `c ∈ A^q(Y ⟶ Z)` is the quotient of `E` by `a` exactly when `a ∘ c = E`; only
injectivity of the cap operations of `a` enters the converse direction. -/
theorem eq_bivariantDivision_iff
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e)
    (c : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    c = bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E ↔
      bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a c =
        BivariantClass.copy C (gysinSystemOfInvertible C) sX sZ rfl
          (comp_comp_structureMorphism_eq hf hg) (comp_comp_structureMorphism_eq hf hg)
          hpqe.symm E := by
  constructor
  · rintro rfl
    exact bivariantCompositeOfInvertible_bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E
  · intro h
    have hc : IsBivariantClassComposition C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
        (properPushforwardDescends C) p q a c
        (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a c) :=
      isBivariantClassComposition_bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a c
    rw [h] at hc
    exact eq_of_isBivariantClassComposition_left (hpp := properPushforwardDescends C)
      ha.capInjective hc
      (isBivariantClassComposition_bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E)

/-- Division by a class with bijective cap operations: for `a ∈ A^p(X ⟶ Y)` with bijective cap
operations and `E ∈ A^e(X ⟶ Z)` there is exactly one `c ∈ A^q(Y ⟶ Z)`, `p + q = e`, with
`a ∘ c = E`. -/
theorem existsUnique_bivariantCompositeOfInvertible_eq
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (ha : a.CapBijective)
    (E : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) e) :
    ∃! c : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q,
      bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a c =
        BivariantClass.copy C (gysinSystemOfInvertible C) sX sZ rfl
          (comp_comp_structureMorphism_eq hf hg) (comp_comp_structureMorphism_eq hf hg)
          hpqe.symm E :=
  ⟨bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E,
    bivariantCompositeOfInvertible_bivariantDivision C sX sY sZ f g hf hg p q e hpqe a ha E,
    fun c hc ↦ (eq_bivariantDivision_iff C sX sY sZ f g hf hg p q e hpqe a ha E c).2 hc⟩

end Division

end Stacks.Chow

end
