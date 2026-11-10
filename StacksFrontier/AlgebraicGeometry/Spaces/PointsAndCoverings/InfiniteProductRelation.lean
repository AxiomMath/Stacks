module

public import StacksFrontier.AlgebraicGeometry.Limits.SigmaDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.InfiniteProduct
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice

/-!
# The étale equivalence relation of the infinite product example

Let `k` be a ring, `S = Spec k`, let `U = Spec (∏_{n ∈ ℕ} k)` and let `f_n : S ⟶ U` be the
morphism of the `n`-th coordinate projection. Stacks 02Z8 forms

  `R = U ⨿ ∐_{(n, m) ∈ ℕ², n ≠ m} S`

with the morphism to `U ×_S U` which is the diagonal on the summand `U` and the pair
`(f_n, f_m)` on the summand indexed by `(n, m)`. The scheme `R` and that morphism are
`AlgebraicGeometry.Space.InfiniteProduct.relation` and
`AlgebraicGeometry.Space.InfiniteProduct.relationMap`. This file proves what the source
asserts of them: the two projections are étale, and the pair is an equivalence relation.

## Main definitions

* `AlgebraicGeometry.Space.InfiniteProduct.relationTarget` and
  `AlgebraicGeometry.Space.InfiniteProduct.relationSource`: the two projections `R ⟶ U`,
  the components of `relationMap`.
* `AlgebraicGeometry.Space.InfiniteProduct.relationSymm`: the involution of `R` exchanging
  them.
* `AlgebraicGeometry.Space.InfiniteProduct.relationOver` and
  `AlgebraicGeometry.Space.InfiniteProduct.spaceOver`: `R` and `U` as schemes over `S`, and
  `AlgebraicGeometry.Space.InfiniteProduct.preRelation`: the pre-relation they carry.

## Main results

* `AlgebraicGeometry.Space.InfiniteProduct.isOpenImmersion_coordinate` and
  `AlgebraicGeometry.Space.InfiniteProduct.isClosedImmersion_coordinate`: each coordinate
  morphism `f_n : S ⟶ U` is an open and closed immersion.
* `AlgebraicGeometry.Space.InfiniteProduct.isEmpty_of_coordinate_eq`: two distinct
  coordinate morphisms have no common test point.
* `AlgebraicGeometry.Space.InfiniteProduct.etale_relationTarget` and
  `AlgebraicGeometry.Space.InfiniteProduct.etale_relationSource`: the projections `s` and `t`
  are étale.
* `AlgebraicGeometry.Space.InfiniteProduct.isEquivalenceRelation_relation`: the projections
  are an internal equivalence relation of schemes, and
  `AlgebraicGeometry.Space.InfiniteProduct.isEtaleEquivalenceRelation_preRelation`: the
  pre-relation over `S` is an étale equivalence relation.

## Implementation notes

Both of the two conditions with content — joint monicity and transitivity — are proved by
splitting a test scheme over the summands of `R`, twice, which is
`AlgebraicGeometry.hom_ext_of_sigma_cases` and
`AlgebraicGeometry.exists_lift_of_sigma_cases`. The index type of `R` is infinite, so the
binary extensivity of the category of schemes is not enough and the infinitary form proved
in `StacksFrontier.AlgebraicGeometry.Limits.SigmaDescent` is used instead.

The geometric input is that distinct coordinate morphisms are disjoint: a test scheme
mapping to `S` in two ways whose composites with `f_n` and with `f_m` agree, for `n ≠ m`, is
empty. This is proved with the idempotent supported at `n`, whose basic open pulls back to
all of `S` along `f_n` and to nothing along `f_m`; no description of the points of the
product ring is needed.

The equivalence relation is proved in the category of schemes and transported to the slice
over `S` by `CategoryTheory.isEquivalenceRelation_of_left`.

## References

* [Stacks Project, Tag 02Z8](https://stacks.math.columbia.edu/tag/02Z8)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.InfiniteProduct

variable (k : Type u) [CommRing k]

/-! ### The coordinate morphisms are disjoint open and closed immersions -/

/-- **Stacks 02Z8.** Each coordinate projection of the product ring defines an open immersion
`S ⟶ U`: it is the localization of the product at the idempotent supported at `n`. -/
@[stacks 02Z8 "the coordinate morphisms are open immersions"]
instance isOpenImmersion_coordinate (n : ℕ) : IsOpenImmersion (coordinate k n) :=
  inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ℕ ↦ k) n))))

/-- **Stacks 02Z8.** Each coordinate projection of the product ring defines a closed immersion
`S ⟶ U`: the projection is a surjective ring homomorphism. -/
@[stacks 02Z8 "the coordinate morphisms are closed immersions"]
instance isClosedImmersion_coordinate (n : ℕ) : IsClosedImmersion (coordinate k n) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ℕ ↦ k) n)) (Function.surjective_eval n)

/-- The idempotent of the product ring supported at `n`. -/
def idem (n : ℕ) : productRing k := Function.update (0 : ℕ → k) n 1

/-- The basic open of the idempotent supported at `n` pulls back to all of `S` along the
`n`-th coordinate morphism. -/
theorem coordinate_preimage_basicOpen_self (n : ℕ) :
    coordinate k n ⁻¹ᵁ PrimeSpectrum.basicOpen (idem k n) = ⊤ := by
  change PrimeSpectrum.basicOpen ((Pi.evalRingHom (fun _ : ℕ ↦ k) n) (idem k n)) = ⊤
  simp [idem]

/-- The basic open of the idempotent supported at `n` pulls back to the empty open along the
`m`-th coordinate morphism, for `m ≠ n`. -/
theorem coordinate_preimage_basicOpen_of_ne {n m : ℕ} (h : m ≠ n) :
    coordinate k m ⁻¹ᵁ PrimeSpectrum.basicOpen (idem k n) = ⊥ := by
  change PrimeSpectrum.basicOpen ((Pi.evalRingHom (fun _ : ℕ ↦ k) m) (idem k n)) = ⊥
  simp [idem, Function.update_of_ne h]

/-- **Stacks 02Z8.** Distinct coordinate morphisms are disjoint: a scheme mapping to `S` in
two ways whose composites with `f_n` and with `f_m` agree is empty when `n ≠ m`. -/
@[stacks 02Z8 "distinct coordinate morphisms are disjoint"]
theorem isEmpty_of_coordinate_eq {T : Scheme.{u}} {n m : ℕ} (hnm : n ≠ m) (a b : T ⟶ base k)
    (h : a ≫ coordinate k n = b ≫ coordinate k m) : IsEmpty T := by
  have h₁ : a ⁻¹ᵁ (coordinate k n ⁻¹ᵁ PrimeSpectrum.basicOpen (idem k n)) = ⊤ := by
    rw [coordinate_preimage_basicOpen_self]
    rfl
  have h₂ : b ⁻¹ᵁ (coordinate k m ⁻¹ᵁ PrimeSpectrum.basicOpen (idem k n)) = ⊥ := by
    rw [coordinate_preimage_basicOpen_of_ne k (Ne.symm hnm)]
    rfl
  have key : (⊤ : T.Opens) = ⊥ := by
    rw [← h₁, ← h₂]
    exact congrArg (fun φ : T ⟶ space k ↦ φ ⁻¹ᵁ PrimeSpectrum.basicOpen (idem k n)) h
  exact ⟨fun t ↦ by simpa [key] using (show t ∈ (⊤ : T.Opens) from trivial)⟩

/-- Two morphisms out of a scheme which maps to `S` in two ways with equal composites into
distinct coordinates agree, the source being empty. -/
theorem hom_ext_of_coordinate_eq {T Z : Scheme.{u}} {n m : ℕ} (hnm : n ≠ m) (a b : T ⟶ base k)
    (h : a ≫ coordinate k n = b ≫ coordinate k m) (x y : T ⟶ Z) : x = y :=
  have : IsEmpty T := isEmpty_of_coordinate_eq k hnm a b h
  isInitialOfIsEmpty.hom_ext x y

/-! ### The two projections of the relation -/

/-- The target projection `R ⟶ U`: the identity on the summand `U` and the morphism `f_n` on
the summand indexed by `(n, m)`. -/
@[implicit_reducible]
noncomputable def relationTarget : relation k ⟶ space k :=
  Sigma.desc fun i ↦ match i with
    | .inl _ => 𝟙 (space k)
    | .inr p => coordinate k p.1.1

/-- The source projection `R ⟶ U`: the identity on the summand `U` and the morphism `f_m` on
the summand indexed by `(n, m)`. -/
@[implicit_reducible]
noncomputable def relationSource : relation k ⟶ space k :=
  Sigma.desc fun i ↦ match i with
    | .inl _ => 𝟙 (space k)
    | .inr p => coordinate k p.1.2

/-- The target projection restricts to the identity on the summand `U`. -/
@[reassoc (attr := simp)]
theorem ι_inl_relationTarget (x : Unit) :
    Sigma.ι (relationComponent k) (.inl x) ≫ relationTarget k = 𝟙 (space k) :=
  Sigma.ι_comp_desc _ _

/-- The target projection restricts to `f_n` on the summand indexed by `(n, m)`. -/
@[reassoc (attr := simp)]
theorem ι_inr_relationTarget (p : OffDiagonal) :
    Sigma.ι (relationComponent k) (.inr p) ≫ relationTarget k = coordinate k p.1.1 :=
  Sigma.ι_comp_desc _ _

/-- The source projection restricts to the identity on the summand `U`. -/
@[reassoc (attr := simp)]
theorem ι_inl_relationSource (x : Unit) :
    Sigma.ι (relationComponent k) (.inl x) ≫ relationSource k = 𝟙 (space k) :=
  Sigma.ι_comp_desc _ _

/-- The source projection restricts to `f_m` on the summand indexed by `(n, m)`. -/
@[reassoc (attr := simp)]
theorem ι_inr_relationSource (p : OffDiagonal) :
    Sigma.ι (relationComponent k) (.inr p) ≫ relationSource k = coordinate k p.1.2 :=
  Sigma.ι_comp_desc _ _

/-- The target projection is the first component of the morphism to `U ×_S U`. -/
@[reassoc (attr := simp)]
theorem relationMap_comp_fst :
    relationMap k ≫ pullback.fst (structureMap k) (structureMap k) = relationTarget k := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  cases i with
  | inl x => simp [relationComponentMap]
  | inr p => simp [relationComponentMap]

/-- The source projection is the second component of the morphism to `U ×_S U`. -/
@[reassoc (attr := simp)]
theorem relationMap_comp_snd :
    relationMap k ≫ pullback.snd (structureMap k) (structureMap k) = relationSource k := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  cases i with
  | inl x => simp [relationComponentMap]
  | inr p => simp [relationComponentMap]

/-- **Stacks 02Z8.** The target projection of the relation is étale: it is the identity on
one summand and an open immersion on each of the others. -/
@[stacks 02Z8 "the target projection is étale"]
theorem etale_relationTarget : Etale (relationTarget k) := by
  refine etale_sigmaDesc _ fun i ↦ ?_
  cases i with
  | inl x => exact inferInstanceAs (Etale (𝟙 (space k)))
  | inr p => exact inferInstanceAs (Etale (coordinate k p.1.1))

/-- **Stacks 02Z8.** The source projection of the relation is étale: it is the identity on
one summand and an open immersion on each of the others. -/
@[stacks 02Z8 "the source projection is étale"]
theorem etale_relationSource : Etale (relationSource k) := by
  refine etale_sigmaDesc _ fun i ↦ ?_
  cases i with
  | inl x => exact inferInstanceAs (Etale (𝟙 (space k)))
  | inr p => exact inferInstanceAs (Etale (coordinate k p.1.2))

/-! ### The relation is an equivalence relation -/

/-- The involution of `R` which exchanges the two projections: the identity on the summand
`U` and the exchange of the summand indexed by `(n, m)` with the one indexed by `(m, n)`. -/
@[implicit_reducible]
noncomputable def relationSymm : relation k ⟶ relation k :=
  Sigma.desc fun i ↦ match i with
    | .inl x => Sigma.ι (relationComponent k) (.inl x)
    | .inr p => Sigma.ι (relationComponent k) (.inr ⟨p.1.swap, fun h ↦ p.2 h.symm⟩)

/-- The involution of `R` fixes the summand `U`. -/
@[reassoc (attr := simp)]
theorem ι_inl_relationSymm (x : Unit) :
    Sigma.ι (relationComponent k) (.inl x) ≫ relationSymm k =
      Sigma.ι (relationComponent k) (.inl x) :=
  Sigma.ι_comp_desc _ _

/-- The involution of `R` sends the summand indexed by `(n, m)` identically to the summand
indexed by `(m, n)`. -/
@[reassoc (attr := simp)]
theorem ι_inr_relationSymm (p : OffDiagonal) :
    Sigma.ι (relationComponent k) (.inr p) ≫ relationSymm k =
      Sigma.ι (relationComponent k) (.inr ⟨p.1.swap, fun h ↦ p.2 h.symm⟩) :=
  Sigma.ι_comp_desc _ _

/-- The involution exchanges the target projection with the source projection. -/
@[reassoc (attr := simp)]
theorem relationSymm_comp_relationTarget :
    relationSymm k ≫ relationTarget k = relationSource k := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  cases i <;> simp

/-- The involution exchanges the source projection with the target projection. -/
@[reassoc (attr := simp)]
theorem relationSymm_comp_relationSource :
    relationSymm k ≫ relationSource k = relationTarget k := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  cases i <;> simp

/-- **The two projections of the relation are jointly monic.** Two morphisms into `R` with
the same target and the same source agree: splitting both over the summands of `R` leaves
the comparison of two coordinate morphisms, which forces the test scheme to be empty unless
the two summands coincide. -/
theorem jointlyMono₂_relation : JointlyMono₂ (relationTarget k) (relationSource k) := by
  constructor
  intro T f g ht hs
  refine hom_ext_of_sigma_cases f _ _ fun i W p a hp ↦ ?_
  refine hom_ext_of_sigma_cases (p ≫ g) _ _ fun j Z q b hq ↦ ?_
  have hgoal : q ≫ p ≫ f = q ≫ a ≫ Sigma.ι (relationComponent k) i := by rw [hp]
  have key : ∀ z z' : relation k ⟶ space k, f ≫ z = g ≫ z' →
      q ≫ a ≫ Sigma.ι (relationComponent k) i ≫ z = b ≫ Sigma.ι (relationComponent k) j ≫ z' :=
    fun z z' e ↦ by
      simpa [reassoc_of% hp, reassoc_of% hq] using congrArg (fun w ↦ q ≫ p ≫ w) e
  cases i with
  | inl x =>
    cases j with
    | inl y =>
      have e : q ≫ a = b := by
        simpa using key _ _ ht
      cases x
      cases y
      rw [hgoal, hq, ← Category.assoc, e]
    | inr q' =>
      have et : q ≫ a = b ≫ coordinate k q'.1.1 := by
        simpa using key _ _ ht
      have es : q ≫ a = b ≫ coordinate k q'.1.2 := by
        simpa using key _ _ hs
      exact hom_ext_of_coordinate_eq k q'.2 b b (et.symm.trans es) _ _
  | inr p' =>
    cases j with
    | inl y =>
      have et : q ≫ a ≫ coordinate k p'.1.1 = b := by
        simpa using key _ _ ht
      have es : q ≫ a ≫ coordinate k p'.1.2 = b := by
        simpa using key _ _ hs
      refine hom_ext_of_coordinate_eq k p'.2 (q ≫ a) (q ≫ a) ?_ _ _
      rw [Category.assoc, Category.assoc, et, es]
    | inr q' =>
      have et : q ≫ a ≫ coordinate k p'.1.1 = b ≫ coordinate k q'.1.1 := by
        simpa using key _ _ ht
      have es : q ≫ a ≫ coordinate k p'.1.2 = b ≫ coordinate k q'.1.2 := by
        simpa using key _ _ hs
      by_cases hfst : p'.1.1 = q'.1.1
      · rw [hfst] at et
        have hab : q ≫ a = b :=
          (cancel_mono (coordinate k q'.1.1)).mp ((Category.assoc _ _ _).trans et)
        by_cases hsnd : p'.1.2 = q'.1.2
        · have hpq : p' = q' := Subtype.ext (Prod.ext hfst hsnd)
          rw [hgoal, hq, ← Category.assoc, hab, hpq]
        · refine hom_ext_of_coordinate_eq k hsnd (q ≫ a) (q ≫ a) ?_ _ _
          rw [Category.assoc, Category.assoc, es, ← Category.assoc, hab]
      · exact hom_ext_of_coordinate_eq k hfst (q ≫ a) b ((Category.assoc _ _ _).trans et) _ _

/-- **The two projections of the relation compose.** Given a test scheme with a pair of
morphisms into `R` whose source and target agree, there is a third morphism into `R` whose
target is the target of the first and whose source is the source of the second. -/
theorem exists_lift_relation {T : Scheme.{u}} (f g : T ⟶ relation k)
    (h : f ≫ relationSource k = g ≫ relationTarget k) :
    ∃ l : T ⟶ relation k, l ≫ relationTarget k = f ≫ relationTarget k ∧
      l ≫ relationSource k = g ≫ relationSource k := by
  refine exists_lift_of_sigma_cases f _ _ _ _ fun i W p a hp ↦ ?_
  cases i with
  | inl x =>
    refine ⟨p ≫ g, ?_, Category.assoc _ _ _⟩
    have h₁ : p ≫ g ≫ relationTarget k = a := by
      rw [← h]
      simp [reassoc_of% hp]
    have h₂ : p ≫ f ≫ relationTarget k = a := by simp [reassoc_of% hp]
    rw [Category.assoc, h₁, h₂]
  | inr p' =>
    refine exists_lift_of_sigma_cases (p ≫ g) _ _ _ _ fun j Z q b hq ↦ ?_
    have htgt : q ≫ p ≫ f ≫ relationTarget k = q ≫ a ≫ coordinate k p'.1.1 := by
      simp [reassoc_of% hp]
    cases j with
    | inl y =>
      refine ⟨q ≫ p ≫ f, ?_, ?_⟩
      · rw [Category.assoc, Category.assoc]
      · have e₁ : q ≫ p ≫ f ≫ relationSource k = b := by
          simp [h, reassoc_of% hq]
        have e₂ : q ≫ p ≫ g ≫ relationSource k = b := by
          simp [reassoc_of% hq]
        rw [Category.assoc, Category.assoc, e₁, e₂]
    | inr q' =>
      have hcomp : q ≫ a ≫ coordinate k p'.1.2 = b ≫ coordinate k q'.1.1 := by
        simpa [reassoc_of% hp, reassoc_of% hq] using congrArg (fun z ↦ q ≫ p ≫ z) h
      have hsrc : q ≫ p ≫ g ≫ relationSource k = b ≫ coordinate k q'.1.2 := by
        simp [reassoc_of% hq]
      by_cases hmid : p'.1.2 = q'.1.1
      · rw [hmid] at hcomp
        have hab : q ≫ a = b :=
          (cancel_mono (coordinate k q'.1.1)).mp ((Category.assoc _ _ _).trans hcomp)
        by_cases hdiag : p'.1.1 = q'.1.2
        · refine ⟨(q ≫ a) ≫ coordinate k p'.1.1 ≫
            Sigma.ι (relationComponent k) (.inl ()), ?_, ?_⟩
          · simp only [Category.assoc, ι_inl_relationTarget, Category.comp_id]
            exact htgt.symm
          · simp only [Category.assoc, ι_inl_relationSource, Category.comp_id]
            rw [hsrc, ← Category.assoc, hab, hdiag]
        · refine ⟨(q ≫ a) ≫ Sigma.ι (relationComponent k) (.inr ⟨(p'.1.1, q'.1.2), hdiag⟩),
            ?_, ?_⟩
          · simp only [Category.assoc, ι_inr_relationTarget]
            exact htgt.symm
          · simp only [Category.assoc, ι_inr_relationSource]
            rw [hsrc, ← Category.assoc, hab]
      · have hempty : IsEmpty Z := isEmpty_of_coordinate_eq k hmid (q ≫ a) b
          ((Category.assoc _ _ _).trans hcomp)
        exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _,
          isInitialOfIsEmpty.hom_ext _ _⟩

/-- **Stacks 02Z8.** The two projections of `R` are an internal equivalence relation on `U`
in the category of schemes. -/
@[stacks 02Z8 "the relation is an equivalence relation"]
theorem isEquivalenceRelation_relation :
    IsEquivalenceRelation (relationTarget k) (relationSource k) := by
  obtain ⟨c, hc₁, hc₂⟩ := exists_lift_relation k
    (pullback.fst (relationSource k) (relationTarget k))
    (pullback.snd (relationSource k) (relationTarget k)) pullback.condition
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := jointlyMono₂_relation k
      r := Sigma.ι (relationComponent k) (.inl ())
      reflexivity₁ := ι_inl_relationTarget k ()
      reflexivity₂ := ι_inl_relationSource k ()
      s := relationSymm k
      symmetry₁ := relationSymm_comp_relationTarget k
      symmetry₂ := relationSymm_comp_relationSource k
      c := pullback.cone (relationSource k) (relationTarget k)
      isLimit := pullback.isLimit (relationSource k) (relationTarget k)
      t := c
      transitivity₁ := hc₁
      transitivity₂ := hc₂ }

/-! ### The relation over the base -/

/-- The structure morphism of `R` over `S`: the structure morphism of `U` on the summand `U`
and the identity on each of the other summands. -/
@[implicit_reducible]
noncomputable def relationStructure : relation k ⟶ base k :=
  Sigma.desc fun i ↦ match i with
    | .inl _ => structureMap k
    | .inr _ => 𝟙 (base k)

/-- The structure morphism of `R` restricts to that of `U` on the summand `U`. -/
@[reassoc (attr := simp)]
theorem ι_inl_relationStructure (x : Unit) :
    Sigma.ι (relationComponent k) (.inl x) ≫ relationStructure k = structureMap k :=
  Sigma.ι_comp_desc _ _

/-- The structure morphism of `R` restricts to the identity on the summand indexed by
`(n, m)`. -/
@[reassoc (attr := simp)]
theorem ι_inr_relationStructure (p : OffDiagonal) :
    Sigma.ι (relationComponent k) (.inr p) ≫ relationStructure k = 𝟙 (base k) :=
  Sigma.ι_comp_desc _ _

/-- The target projection lies over `S`. -/
theorem relationTarget_comp_structureMap :
    relationTarget k ≫ structureMap k = relationStructure k := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  cases i <;> simp

/-- The source projection lies over `S`. -/
theorem relationSource_comp_structureMap :
    relationSource k ≫ structureMap k = relationStructure k := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  cases i <;> simp

/-- The scheme `U` as a scheme over `S`. -/
noncomputable abbrev spaceOver : Over (base k) := Over.mk (structureMap k)

/-- The scheme `R` as a scheme over `S`. -/
noncomputable abbrev relationOver : Over (base k) := Over.mk (relationStructure k)

/-- The target projection as a morphism of schemes over `S`. -/
noncomputable def targetOver : relationOver k ⟶ spaceOver k :=
  Over.homMk (relationTarget k) (relationTarget_comp_structureMap k)

/-- The source projection as a morphism of schemes over `S`. -/
noncomputable def sourceOver : relationOver k ⟶ spaceOver k :=
  Over.homMk (relationSource k) (relationSource_comp_structureMap k)

/-- **Stacks 02Z8.** The pre-relation of the example: the morphism `R ⟶ U ×_S U` with
components the two projections, in the shape Stacks 022P asks for. -/
noncomputable def preRelation :
    Stacks.Groupoids.PreRelation (relationOver k) (spaceOver k) :=
  prod.lift (targetOver k) (sourceOver k)

/-- The target of the pre-relation is the target projection over `S`. -/
@[simp]
theorem preRelation_target : (preRelation k).target = targetOver k := prod.lift_fst _ _

/-- The source of the pre-relation is the source projection over `S`. -/
@[simp]
theorem preRelation_source : (preRelation k).source = sourceOver k := prod.lift_snd _ _

/-- **Stacks 02Z8.** The pre-relation of the example is an étale equivalence relation over
`S`: this is the hypothesis under which Stacks 02WW produces the algebraic space `X = U/R`. -/
@[stacks 02Z8 "the pre-relation is an étale equivalence relation"]
theorem isEtaleEquivalenceRelation_preRelation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (preRelation k) where
  isEquivalenceRelation := by
    rw [preRelation_target, preRelation_source]
    have : IsEquivalenceRelation (targetOver k).left (sourceOver k).left :=
      isEquivalenceRelation_relation k
    exact isEquivalenceRelation_of_left (targetOver k) (sourceOver k)
  etale_source := by
    rw [preRelation_source]
    exact etale_relationSource k
  etale_target := by
    rw [preRelation_target]
    exact etale_relationTarget k

end AlgebraicGeometry.Space.InfiniteProduct

end
