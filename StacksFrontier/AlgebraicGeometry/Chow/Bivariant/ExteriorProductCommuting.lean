module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductBivariant

/-!
# The exterior product as the cap product of a bivariant class towards the base

Let `(S, δ)` be a base situation whose base is a point, so that the exterior product
`α × β ∈ CH_{n+m}(X ×_S Y)` of Stacks 0FBV is defined. **Stacks 0FBY** asserts, for
`u : Y ⟶ Z` a morphism of schemes locally of finite type over `S` and `c ∈ A^p(Y ⟶ Z)` a
bivariant class,

  `α × (c ∩ β) = c ∩ (α × β)`

in `CH_*(X ×_S Y)`. The equation is stated as `Stacks.Chow.CommutesExteriorProductCap` in
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductBivariant`. This module states the
exterior-product form of Stacks 0FBW and the transport lemmas around it.

## Main definitions

* `Stacks.Chow.pullbackBaseChangeOfTestIso` — the base change along `f : X ⟶ Y` of an
  isomorphism of test schemes over `Y`, pinned down by its two projections.
* `Stacks.Chow.BivariantClass.capBase` — the cap operation of a bivariant class towards the base,
  read on the structure morphism of the test scheme itself rather than on `sT ≫ 𝟙 S`.
* `Stacks.Chow.IsExteriorProductBivariantClass` — **Stacks 0FBW in its exterior-product form**:
  the assertion that a given class `c ∈ A^{-n}(X ⟶ S)` caps as the exterior product with a given
  `α ∈ CH_n(X)`.
* `Stacks.Chow.ExteriorProductRepresentedByBivariantClasses` — the same assertion quantified over
  every `X` and every `α`.

## Main results

* `Stacks.Chow.BivariantClass.cap_chowPushforwardOfTestIso` — **the isomorphism case of condition
  (1) of Stacks 0B76**: the cap operation of a bivariant class commutes with pushforward along an
  isomorphism of test schemes.
* `Stacks.Chow.BivariantClass.capBase_chowPushforwardOfTestIso` — the same for a class towards the
  base, with the `sT ≫ 𝟙 S` bookkeeping discharged.
* `Stacks.Chow.IsExteriorProductBivariantClass.unique` — at most one bivariant class towards the
  base caps as the exterior product with `α`.

## References

* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport bookkeeping -/

/-- Pushforward along an isomorphism over the base commutes with the transport of a Chow group
along equalities of the structure morphisms of its source and its target. -/
theorem chowPushforwardOfIso_chowGroupCongr (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (hA : sA = sA')
    (hB : sB = sB') (v : A ⟶ B) [IsIso v] (hv : v ≫ sB = sA) (hv' : v ≫ sB' = sA') (k : ℤ)
    (x : chowGroup C sA k) :
    chowGroupCongr C hB k (chowPushforwardOfIso C sA sB v hv k x) =
      chowPushforwardOfIso C sA' sB' v hv' k (chowGroupCongr C hA k x) := by
  subst hA hB
  rfl

/-- Transport along an equality of structure morphisms turns a heterogeneous equality of Chow
classes into an equality. -/
theorem chowGroupCongr_eq_iff_heq (C : ChowSituation.{u}) {A : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hA : sA = sA')
    (k : ℤ) (x : chowGroup C sA k) (y : chowGroup C sA' k) :
    chowGroupCongr C hA k x = y ↔ x ≍ y := by
  subst hA
  exact ⟨heq_of_eq, eq_of_heq⟩

/-- Pushforward along the identity between two structure morphisms that are equal is the transport
along their equality. -/
theorem chowPushforwardOfIso_id_eq_chowGroupCongr (C : ChowSituation.{u}) {A : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    (h : 𝟙 A ≫ sA = sA') (k : ℤ) (x : chowGroup C sA' k) :
    chowPushforwardOfIso C sA' sA (𝟙 A) h k x =
      chowGroupCongr C (h.symm.trans (Category.id_comp sA)) k x := by
  obtain rfl : sA' = sA := h.symm.trans (Category.id_comp sA)
  exact chowPushforwardOfIso_id C _ k x

/-! ### The base change of an isomorphism of test schemes -/

/-- The base change along `f : X ⟶ Y` of an isomorphism `ι : T' ⟶ T` of test schemes over `Y`,
the source test morphism being presented as a morphism `g'` together with `hι : ι ≫ g = g'`: the
identification `X ×_Y T' ≅ X ×_Y T` that is the identity on the factor `X`. -/
def pullbackBaseChangeOfTestIso {X Y T T' : Scheme.{u}} (f : X ⟶ Y) {g : T ⟶ Y} {g' : T' ⟶ Y}
    (ι : T' ⟶ T) [IsIso ι] (hι : ι ≫ g = g') :
    (pullback f g' : Scheme.{u}) ≅ (pullback f g : Scheme.{u}) :=
  asIso (pullback.map f g' f g (𝟙 X) ι (𝟙 Y) (by simp) (by simp [hι]))

/-- The base change of an isomorphism of test schemes commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeOfTestIso_hom_fst {X Y T T' : Scheme.{u}} (f : X ⟶ Y) {g : T ⟶ Y}
    {g' : T' ⟶ Y} (ι : T' ⟶ T) [IsIso ι] (hι : ι ≫ g = g') :
    (pullbackBaseChangeOfTestIso f ι hι).hom ≫ pullback.fst f g = pullback.fst f g' := by
  simp [pullbackBaseChangeOfTestIso]

/-- The base change of an isomorphism `ι` of test schemes followed by the second projection is the
second projection followed by `ι`. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeOfTestIso_hom_snd {X Y T T' : Scheme.{u}} (f : X ⟶ Y) {g : T ⟶ Y}
    {g' : T' ⟶ Y} (ι : T' ⟶ T) [IsIso ι] (hι : ι ≫ g = g') :
    (pullbackBaseChangeOfTestIso f ι hι).hom ≫ pullback.snd f g = pullback.snd f g' ≫ ι := by
  simp [pullbackBaseChangeOfTestIso]

/-- The base change of an isomorphism of test schemes is a morphism over any scheme that the
factor `X` lies over. -/
theorem pullbackBaseChangeOfTestIso_hom_comp {X Y T T' W : Scheme.{u}} (f : X ⟶ Y) {g : T ⟶ Y}
    {g' : T' ⟶ Y} (ι : T' ⟶ T) [IsIso ι] (hι : ι ≫ g = g') (w : X ⟶ W) :
    (pullbackBaseChangeOfTestIso f ι hι).hom ≫ (pullback.fst f g ≫ w) =
      pullback.fst f g' ≫ w := by
  rw [← Category.assoc, pullbackBaseChangeOfTestIso_hom_fst]

/-- The first projection of a base change along an identity is the inverse of the canonical
identification. -/
theorem pullbackIdIso_inv_eq_fst {X Z : Scheme.{u}} (i : Z ⟶ X) :
    (pullbackIdIso i).inv = pullback.fst i (𝟙 X) :=
  Iso.inv_ext (pullbackIdIso_hom_fst i)

/-- The first projection of a base change along an identity is an isomorphism. -/
instance isIso_pullbackFstId {X Z : Scheme.{u}} (i : Z ⟶ X) : IsIso (pullback.fst i (𝟙 X)) :=
  pullbackIdIso_inv_eq_fst i ▸ inferInstance

/-! ### Cap product against a pushforward along an isomorphism of test schemes -/

section CapIso

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- **The isomorphism case of condition (1) of Stacks 0B76.** The cap operation of a bivariant
class commutes with pushforward along an isomorphism `ι : T' ⟶ T` of test schemes: capping a class
pushed forward along `ι` is the pushforward, along the base change of `ι`, of the cap at `T'`.
The source test morphism is presented as a morphism `m` together with `hι : ι ≫ g = m`. -/
theorem BivariantClass.cap_chowPushforwardOfTestIso (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] {m : T' ⟶ Y}
    [LocallyOfFiniteType m] (ι : T' ⟶ T) [IsIso ι] (hι : ι ≫ g = m) (k : ℤ)
    (x : chowGroup C (m ≫ sY) k) :
    c.cap g k (chowPushforwardOfIso C (m ≫ sY) (g ≫ sY) ι
        (by rw [← Category.assoc, hι]) k x) =
      chowPushforwardOfIso C (pullback.fst f m ≫ sX) (pullback.fst f g ≫ sX)
        (pullbackBaseChangeOfTestIso f ι hι).hom
        (pullbackBaseChangeOfTestIso_hom_comp f ι hι sX) (k - p) (c.cap m k x) := by
  have h : ι ≫ g ≫ sY = m ≫ sY := by rw [← Category.assoc, hι]
  exact c.proper_naturality_of_test_eq g ι m hι (pullbackBaseChangeOfTestIso f ι hι).hom
    (IsPullback.of_vert_isIso ⟨(pullbackBaseChangeOfTestIso_hom_snd f ι hι).symm⟩)
    (pullbackBaseChangeOfTestIso_hom_fst f ι hι) k h
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ ι h k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _
      (pullbackBaseChangeOfTestIso_hom_comp f ι hι sX) (k - p)) x

end CapIso

/-! ### The cap operation of a class towards the base, read on a structure morphism -/

section CapBase

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-- The cap operation of a bivariant class `c ∈ A^p(X ⟶ S)` towards the base, read on the
structure morphism `sT` of the test scheme itself rather than on `sT ≫ 𝟙 S`. -/
def BivariantClass.capBase (c : bivariantToBase C G sX p) {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (k : ℤ) :
    chowGroup C sT k →+ chowGroup C (pullback.fst sX sT ≫ sX) (k - p) :=
  (c.cap sT k).comp (chowGroupCongr C (Category.comp_id sT).symm k).toAddMonoidHom

/-- The cap operation of a class towards the base, applied to `x`, is the cap operation of the
class applied to `x` transported to the index `sT ≫ 𝟙 S`. -/
theorem BivariantClass.capBase_apply (c : bivariantToBase C G sX p) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) (x : chowGroup C sT k) :
    c.capBase C G sX p sT k x =
      c.cap sT k (chowGroupCongr C (Category.comp_id sT).symm k x) :=
  rfl

/-- The cap operation of a class towards the base is the cap operation of the class, up to the
transport that presents the test morphism as `sT ≫ 𝟙 S`. -/
theorem BivariantClass.cap_eq_capBase (c : bivariantToBase C G sX p) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) (x : chowGroup C (sT ≫ 𝟙 C.S) k) :
    c.cap sT k x = c.capBase C G sX p sT k (chowGroupCongr C (Category.comp_id sT) k x) := by
  rw [BivariantClass.capBase_apply, chowGroupCongr_chowGroupCongr]
  rfl

/-- **The isomorphism case of condition (1) of Stacks 0B76, for a class towards the base.** -/
theorem BivariantClass.capBase_chowPushforwardOfTestIso (c : bivariantToBase C G sX p)
    {T T' : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {sT' : T' ⟶ C.S}
    [LocallyOfFiniteType sT'] (ι : T' ⟶ T) [IsIso ι] (hι : ι ≫ sT = sT') (k : ℤ)
    (x : chowGroup C sT' k) :
    c.capBase C G sX p sT k (chowPushforwardOfIso C sT' sT ι hι k x) =
      chowPushforwardOfIso C (pullback.fst sX sT' ≫ sX) (pullback.fst sX sT ≫ sX)
        (pullbackBaseChangeOfTestIso sX ι hι).hom
        (pullbackBaseChangeOfTestIso_hom_comp sX ι hι sX) (k - p)
        (c.capBase C G sX p sT' k x) := by
  rw [BivariantClass.capBase_apply, BivariantClass.capBase_apply,
    chowPushforwardOfIso_chowGroupCongr C (Category.comp_id sT').symm (Category.comp_id sT).symm
      ι hι (by rw [← Category.assoc, hι]) k x,
    BivariantClass.cap_chowPushforwardOfTestIso C G sX (𝟙 C.S) sX (Category.comp_id sX) p c sT ι
      hι k]

end CapBase

/-! ### Stacks 0FBW in its exterior-product form -/

section Presentation

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (hfp : FlatPullbackDescends C)
  (n : ℤ)

/-- **Stacks 0FBW in its exterior-product form**, as a predicate on a class
`c ∈ A^{-n}(X ⟶ S)` and a class `α ∈ CH_n(X)`: the cap operation of `c` at every test scheme
`sT : T ⟶ S` is the exterior product with `α`,

  `c ∩ γ = α × γ`   for every `γ ∈ CH_k(T)`.

The two sides live on `X ×_S T` in the degrees `k - (-n)` and `n + k`, which are the same integer
written two ways and are matched by `Stacks.Chow.chowGroupDegreeEquiv`. -/
def IsExteriorProductBivariantClass (α : chowGroup C sX n) (c : bivariantToBase C G sX (-n)) :
    Prop :=
  ∀ {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) (γ : chowGroup C sT k),
    c.capBase C G sX (-n) sT k γ =
      chowGroupDegreeEquiv C (pullback.fst sX sT ≫ sX) (by ring : n + k = k - -n)
        (chowExteriorProduct C hδ sX sT n k (TensorProduct.tmul ℤ α γ))

include hfp in
/-- At most one bivariant class towards the base caps as the exterior product with `α`. -/
theorem IsExteriorProductBivariantClass.unique {α : chowGroup C sX n}
    {c d : bivariantToBase C G sX (-n)}
    (hc : IsExteriorProductBivariantClass C hδ G sX n α c)
    (hd : IsExteriorProductBivariantClass C hδ G sX n α d) : c = d := by
  refine BivariantClass.ext C G sX (𝟙 C.S) sX (Category.comp_id sX) (-n) ?_
  intro T g _ k x
  rw [c.cap_eq_capBase C G sX (-n) g k x, d.cap_eq_capBase C G sX (-n) g k x,
    hc g k _, hd g k _]

end Presentation

section Quantified

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  (hfp : FlatPullbackDescends C)

/-- **Stacks 0FBW in its exterior-product form**, quantified: every Chow class on every scheme
locally of finite type over the base is the cap operation of a bivariant class towards the base,
namely the exterior product with it. -/
def ExteriorProductRepresentedByBivariantClasses : Prop :=
  ∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (n : ℤ) (α : chowGroup C sX n),
    ∃ c : bivariantToBase C G sX (-n), IsExteriorProductBivariantClass C hδ G sX n α c

end Quantified

end Stacks.Chow

end
