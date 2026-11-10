module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Restriction of bivariant Chow classes along a base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` and let `h : Y' ⟶ Y` be another such
morphism. Write `X' = X ×_Y Y'`. A scheme locally of finite type over `Y'` is in particular one
over `Y`, so a bivariant class `c ∈ A^p(X ⟶ Y)` operates on the Chow groups of test schemes over
`Y'`, and **Stacks 0F9Z** reads that operation as the restriction

  `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')`,   `c ↦ res(c)`,   `res(c) ∩ α = c ∩ α`,

compatibly with composition of base changes.

The restricted class is `Stacks.Chow.bivariantRestriction` and the restriction map is
`Stacks.Chow.bivariantRestrictionAddHom`. The construction carries one hypothesis, the
isomorphism case of Stacks 02TA for the Gysin system the classes are stated against; that
hypothesis is not an artefact but a necessity, and the implementation notes say why.

The cap operation of a bivariant class lands in the *chosen* categorical pullback, so the two
sides of `res(c) ∩ α = c ∩ α` live on the two fibre products `(X ×_Y Y') ×_{Y'} T` and `X ×_Y T`
of a test scheme `T ⟶ Y'`; they are identified by the canonical isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, and the restricted cap operation is the
original one pushed forward along it.

## Main definitions

* `Stacks.Chow.chowGroupCongr` — transport of a Chow group along an equality of structure
  morphisms over the base.
* `Stacks.Chow.restrictionCompIso`, `Stacks.Chow.restrictionBaseChange` — the comparison
  isomorphism `(X ×_Y Y') ×_{Y'} T' ≅ X ×_Y T'` at a composite test morphism, and the base change
  of a morphism of test schemes transported along it. These are what the proper-pushforward axiom
  of a restricted class is proved from.
* `Stacks.Chow.bivariantRestrictionCap` — **Stacks 0F9Z**, the cap operation `res(c) ∩ -` of the
  restriction of `c` along `h`.
* `Stacks.Chow.IsBivariantRestriction` — the assertion that a bivariant class for `X' ⟶ Y'` is
  the restriction of `c` along `h`, namely that it caps by that operation.
* `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` — the isomorphism case of Stacks 02TA for
  a Gysin system: on two isomorphic base changes of a test scheme its Gysin maps agree.
* `Stacks.Chow.zeroSchemePullbackIso` — Stacks 0B6Y for two isomorphic base changes: the
  identification of the zero schemes of the two pulled-back sections.
* `Stacks.Chow.bivariantRestriction` — **Stacks 0F9Z**, the restricted class `res(c)`.
* `Stacks.Chow.bivariantRestrictionAddHom` — **Stacks 0F9Z**, the restriction map
  `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')`.
* `Stacks.Chow.iteratedRestrictionIso` — the comparison isomorphism identifying the base change
  along `h` followed by the one along `h'` with the base change along `h' ≫ h`.

## Main results

* `Stacks.Chow.eq_of_isBivariantRestriction` — the cap formula determines the restriction: two
  bivariant classes that both restrict `c` along `h` are equal.
* `Stacks.Chow.IsBivariantRestriction.add`, `.neg`, `.zero` — the restriction is additive, in the
  sense that the characterization transports along the group operations. With the uniqueness
  above, this is the assertion that `res` is a homomorphism of groups wherever it is defined.
* `Stacks.Chow.bivariantRestrictionCap_proper_naturality`,
  `Stacks.Chow.bivariantRestrictionCap_flat_naturality`,
  `Stacks.Chow.bivariantRestrictionCap_gysin_naturality` — the three axioms of Stacks 0B76 for
  the restricted cap operation, which is what makes `Stacks.Chow.bivariantRestriction` a
  bivariant class.
* `Stacks.Chow.bivariantRestriction_cap`,
  `Stacks.Chow.isBivariantRestriction_bivariantRestriction` — the restricted class caps by the
  restricted cap operation, so it is the unique class that does.
* `Stacks.Chow.bivariantRestriction_add`, `_neg`, `_zero` — restriction is a homomorphism of
  groups.
* `Stacks.Chow.bivariantRestrictionCap_comp`, `Stacks.Chow.bivariantRestriction_comp` —
  **Stacks 0F9Z**, compatibility with compositions: restricting along `h` and then along
  `h' : Y'' ⟶ Y'` agrees with restricting along `h' ≫ h`, modulo the canonical isomorphism of the
  two iterated fibre products. The first is stated for any class satisfying the characterization,
  the second for the restriction itself.

## Implementation notes

### What the cap operation needs, and what it does not

Pushing forward along the comparison isomorphism needs an instance of Stacks 02S2 for that
isomorphism, and that case of Stacks 02S2 is proved outright in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport`
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isIso`). So
`Stacks.Chow.bivariantRestrictionCap` and everything stated in terms of it — the
characterization, its uniqueness, its additivity and the composition law — carry no hypotheses
beyond those of Stacks 0F9Z itself.

### The three axioms, and the one hypothesis the construction carries

The cap operation above is not by itself a bivariant class; the content of the construction is
the three naturality axioms of `Stacks.Chow.BivariantClass` for it. They are of three different
kinds, and it is worth recording which, since the analogous question for Stacks 0B77 and 0B7H is
recorded as open in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic`.

* The **proper** axiom is proved, as
  `Stacks.Chow.bivariantRestrictionCap_proper_naturality`. It needs only the axiom of `c`,
  functoriality of proper pushforward on Chow groups (Stacks 02R5,
  `Stacks.Chow.properChowPushforward_comp`) and Stacks 02S2 for the comparison isomorphisms; the
  bookkeeping is `Stacks.Chow.restrictionBaseChange` and
  `Stacks.Chow.bivariantRestrictionCap_eq` below.
* The **flat** axiom is proved, as `Stacks.Chow.bivariantRestrictionCap_flat_naturality`. It
  needs flat pullback to commute with proper pushforward along an isomorphism, which is the
  isomorphism case of Stacks 02RG; that case is proved in
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange`, on cycles and on Chow
  groups, together with the transport of Stacks 02S1 to the base-changed flat morphism that
  invoking the axiom of `c` requires.
* The **Gysin** axiom, `Stacks.Chow.bivariantRestrictionCap_gysin_naturality`, is different in
  kind: it cannot hold for an arbitrary `Stacks.Chow.GysinSystem`. The restricted cap operation
  lands on a base change of `f` over `Y'`, while `c` caps into a base change of `f` over `Y`, and
  the two are isomorphic and not equal; `G.chern` at two isomorphic schemes is unrelated data, so
  no axiom of `c` and no property of the pullback constrains the two Gysin maps to agree. What is
  needed is exactly `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`, the isomorphism case
  of Stacks 02TA for `G` — the same content that `Stacks.Chow.GysinCompatibleWithPushforward`
  (`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward`) supplies for 02TA on integral
  components. It is a `Prop`, so it is a hypothesis of the construction rather than a parameter of
  the group, in the style of `Stacks.Chow.ProperPushforwardDescends`; substituting the genuine
  first Chern class rule for `G` discharges it, and Stacks 0F9Z is then recovered verbatim.

The identification of the zero schemes that the Gysin axiom needs is
`Stacks.Chow.zeroSchemePullbackIso`, which is Stacks 0B6Y — proved in this repository as
`Stacks.Divisors.zeroScheme_pullback` — for the special case of two isomorphic base changes of a
test scheme, where `Scheme.IdealSheafData.comap_comp` reduces it to the base change of an ideal
sheaf along an isomorphism.

`Stacks.Chow.eq_of_isBivariantRestriction` is what ties the construction to the formula: the cap
formula pins the restricted class down, so `Stacks.Chow.bivariantRestriction` is the only class
satisfying it, and its additivity follows from the additivity of the formula.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport along an equality of structure morphisms -/

/-- Transport between the Chow groups of two structure morphisms that are equal. The cap
operation of a bivariant class on a test scheme `T ⟶ Y'` is indexed by `g ≫ (h ≫ sY)` while the
class it comes from is indexed by `(g ≫ h) ≫ sY`; these are the same morphism and not the same
term. -/
def chowGroupCongr (C : ChowSituation.{u}) {X : Scheme.{u}} {q q' : X ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') (k : ℤ) :
    chowGroup C q k ≃+ chowGroup C q' k := by
  subst hq
  exact AddEquiv.refl _

/-! ### Pushforward bookkeeping -/

/-- Proper pushforward on Chow groups along a morphism presented as a composite is the composite
of the two proper pushforwards. -/
theorem properChowPushforward_comp_apply (C : ChowSituation.{u}) {A B D : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (u : A ⟶ B) [IsProper u] (v : B ⟶ D) [IsProper v]
    (w : A ⟶ D) [IsProper w] (huv : u ≫ v = w) (hu : u ≫ sB = sA) (hv : v ≫ sD = sB)
    (hw : w ≫ sD = sA) (k : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfacw : ProperPushforwardFactorsThroughRationalEquivalence C sA sD w hw k)
    (α : chowGroup C sA k) :
    properChowPushforward C sA sD w hw k hfacw α =
      properChowPushforward C sB sD v hv k hfacv
        (properChowPushforward C sA sB u hu k hfacu α) := by
  subst huv
  exact (DFunLike.congr_fun
    (properChowPushforward_comp C sA sB sD u v hu hv k hfacu hfacv) α).symm

/-- Proper pushforward commutes with the transport of Chow groups along equalities of the
structure morphisms of its source and of its target. -/
theorem properChowPushforward_chowGroupCongr (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    (hA : sA = sA') (hB : sB = sB') (u : A ⟶ B) [IsProper u] (hu : u ≫ sB = sA)
    (hu' : u ≫ sB' = sA') (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' u hu' k)
    (α : chowGroup C sA k) :
    chowGroupCongr C hB k (properChowPushforward C sA sB u hu k hfac α) =
      properChowPushforward C sA' sB' u hu' k hfac' (chowGroupCongr C hA k α) := by
  subst hA
  subst hB
  rfl

/-- Factoring through rational equivalence is unchanged by replacing the structure morphisms of
the source and of the target with equal ones. -/
theorem properPushforwardFactorsThroughRationalEquivalence_congr_base (C : ChowSituation.{u})
    {A B : Scheme.{u}} {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    (hA : sA = sA') (hB : sB = sB') (u : A ⟶ B) [IsProper u] (hu : u ≫ sB = sA)
    (hu' : u ≫ sB' = sA') (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k) :
    ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' u hu' k := by
  subst hA
  subst hB
  exact hfac


/-- Transport of a heterogeneous equality of Chow classes through a family of maps indexed by the
degree. -/
theorem heq_map_index {α β : ℤ → Type u} {i j : ℤ} (hij : i = j) {x : α i} {y : α j}
    (hxy : HEq x y) (F : ∀ n, α n → β n) : HEq (F i x) (F j y) := by
  cases hij
  cases hxy
  rfl

/-- Flat pullback of cycles factoring through rational equivalence is unchanged by replacing the
structure morphisms of the source and of the target with equal ones. -/
theorem flatPullbackFactorsThroughRationalEquivalence_congr_base (C : ChowSituation.{u})
    {A B : Scheme.{u}} {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    (hA : sA = sA') (hB : sB = sB') (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v]
    (hv : v ≫ sB = sA) (hv' : v ≫ sB' = sA') (r : ℕ)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr k) :
    FlatPullbackFactorsThroughRationalEquivalence C sA' sB' v hv' r hvr k := by
  subst hA
  subst hB
  exact hfac

/-- Flat pullback on Chow groups commutes with the transport of Chow groups along equalities of
the structure morphisms of its source and of its target. -/
theorem flatPullbackChow_chowGroupCongr (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    (hA : sA = sA') (hB : sB = sB') (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v]
    (hv : v ≫ sB = sA) (hv' : v ≫ sB' = sA') (r : ℕ)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA' sB' v hv' r hvr k)
    (α : chowGroup C sB k) :
    chowGroupCongr C hA (k + (r : ℤ)) (flatPullbackChow C sA sB v hv r hvr k hfac α) =
      flatPullbackChow C sA' sB' v hv' r hvr k hfac' (chowGroupCongr C hB k α) := by
  subst hA
  subst hB
  rfl

/-- Proper pushforward on Chow groups along an isomorphism over the base does not depend on which
instance of Stacks 02S2 it is given: it is always `Stacks.Chow.chowPushforwardOfIso`. -/
theorem properChowPushforward_eq_chowPushforwardOfIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k) :
    properChowPushforward C sA sB u hu k hfac = chowPushforwardOfIso C sA sB u hu k :=
  rfl

/-! ### The isomorphism case of Stacks 02RG on cycles -/

/-- Transport of a Chow class along an equality of structure morphisms changes nothing. -/
theorem chowGroupCongr_heq (C : ChowSituation.{u}) {X : Scheme.{u}} {q q' : X ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') (k : ℤ)
    (α : chowGroup C q k) :
    HEq (chowGroupCongr C hq k α) α := by
  subst hq
  rfl

/-- Proper pushforward on Chow groups commutes with the transport along an equality of degrees. -/
theorem properChowPushforward_cast (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (w : A ⟶ B) [IsProper w]
    (hw : w ≫ sB = sA) {i j : ℤ} (hij : i = j)
    (hfaci : ProperPushforwardFactorsThroughRationalEquivalence C sA sB w hw i)
    (hfacj : ProperPushforwardFactorsThroughRationalEquivalence C sA sB w hw j)
    (α : chowGroup C sA i) :
    Eq.mp (congrArg (chowGroup C sB) hij) (properChowPushforward C sA sB w hw i hfaci α) =
      properChowPushforward C sA sB w hw j hfacj
        (Eq.mp (congrArg (chowGroup C sA) hij) α) := by
  cases hij
  rfl

/-- **Stacks 02R5, 0GU8.** Two factorizations of one proper morphism over the base push forward
Chow classes the same way. -/
theorem properChowPushforward_comp_eq (C : ChowSituation.{u}) {A B D E : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (sE : E ⟶ C.S) [LocallyOfFiniteType sE]
    (u : A ⟶ B) [IsProper u] (v : B ⟶ E) [IsProper v] (w : A ⟶ D) [IsProper w] (z : D ⟶ E)
    [IsProper z] (hcomp : u ≫ v = w ≫ z) (hu : u ≫ sB = sA) (hv : v ≫ sE = sB)
    (hw : w ≫ sD = sA) (hz : z ≫ sE = sD) (k : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sE v hv k)
    (hfacw : ProperPushforwardFactorsThroughRationalEquivalence C sA sD w hw k)
    (hfacz : ProperPushforwardFactorsThroughRationalEquivalence C sD sE z hz k)
    (α : chowGroup C sA k) :
    properChowPushforward C sB sE v hv k hfacv (properChowPushforward C sA sB u hu k hfacu α) =
      properChowPushforward C sD sE z hz k hfacz
        (properChowPushforward C sA sD w hw k hfacw α) :=
  (properChowPushforward_comp_apply C sA sB sE u v (u ≫ v) rfl hu hv
      (by rw [Category.assoc, hv, hu]) k hfacu hfacv
      (properPushforwardFactorsThroughRationalEquivalence_comp C sA sB sE u v hu hv k hfacu
        hfacv) α).symm.trans
    (properChowPushforward_comp_apply C sA sD sE w z (u ≫ v) hcomp.symm hw hz
      (by rw [Category.assoc, hv, hu]) k hfacw hfacz
      (properPushforwardFactorsThroughRationalEquivalence_comp C sA sB sE u v hu hv k hfacu
        hfacv) α)

/-! ### Comparison of the two base changes -/

section Comparison

/-- The induced morphism of fibre products is compatible with the first projections. -/
@[reassoc (attr := simp)]
theorem pullbackMap_fst {W X Y Z S T : Scheme.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

/-- The induced morphism of fibre products is compatible with the second projections. -/
@[reassoc (attr := simp)]
theorem pullbackMap_snd {W X Y Z S T : Scheme.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y' ⟶ Y)

/-- The comparison isomorphism `(X ×_Y Y') ×_{Y'} T' ≅ X ×_Y T'` for a test scheme `g : T ⟶ Y'`
and a morphism `r : T' ⟶ T`, taken over the composite `r ≫ g ≫ h`. -/
def restrictionCompIso {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T) :
    pullback (pullback.snd f h) (r ≫ g) ≅ pullback f (r ≫ g ≫ h) :=
  (pullbackLeftPullbackSndIso f h (r ≫ g)).trans (pullback.congrHom rfl (Category.assoc r g h))

/-- The comparison isomorphism is compatible with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem restrictionCompIso_hom_fst {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T) :
    (restrictionCompIso f h g r).hom ≫ pullback.fst f (r ≫ g ≫ h) =
      pullback.fst (pullback.snd f h) (r ≫ g) ≫ pullback.fst f h := by
  simp [restrictionCompIso]

/-- The comparison isomorphism is compatible with the projections to the test scheme. -/
@[reassoc (attr := simp)]
theorem restrictionCompIso_hom_snd {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T) :
    (restrictionCompIso f h g r).hom ≫ pullback.snd f (r ≫ g ≫ h) =
      pullback.snd (pullback.snd f h) (r ≫ g) := by
  simp [restrictionCompIso]

/-- The inverse comparison isomorphism is compatible with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem restrictionCompIso_inv_fst_fst {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T) :
    (restrictionCompIso f h g r).inv ≫
        pullback.fst (pullback.snd f h) (r ≫ g) ≫ pullback.fst f h =
      pullback.fst f (r ≫ g ≫ h) := by
  rw [← restrictionCompIso_hom_fst f h g r, Iso.inv_hom_id_assoc]

/-- The base change of `r : T' ⟶ T` to the fibre products of `f` over `Y`, transported along the
comparison isomorphisms from a base change `r'` of `r` to the fibre products of
`pullback.snd f h` over `Y'`. It is used for both a proper and a flat `r`. -/
def restrictionBaseChange {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T)
    (r' : pullback (pullback.snd f h) (r ≫ g) ⟶ pullback (pullback.snd f h) g) :
    pullback f (r ≫ g ≫ h) ⟶ pullback f (g ≫ h) :=
  (restrictionCompIso f h g r).inv ≫ r' ≫ (pullbackLeftPullbackSndIso f h g).hom

/-- The transported base change, followed by the inverse comparison isomorphism, is the given
base change. -/
theorem restrictionBaseChange_comp_inv {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T)
    (r' : pullback (pullback.snd f h) (r ≫ g) ⟶ pullback (pullback.snd f h) g) :
    restrictionBaseChange f h g r r' ≫ (pullbackLeftPullbackSndIso f h g).inv =
      (restrictionCompIso f h g r).inv ≫ r' := by
  simp [restrictionBaseChange]

/-- The transported base change is compatible with the projections to `X`. -/
theorem restrictionBaseChange_fst {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T)
    (r' : pullback (pullback.snd f h) (r ≫ g) ⟶ pullback (pullback.snd f h) g)
    (hfst : r' ≫ pullback.fst (pullback.snd f h) g =
      pullback.fst (pullback.snd f h) (r ≫ g)) :
    restrictionBaseChange f h g r r' ≫ pullback.fst f (g ≫ h) =
      pullback.fst f (r ≫ g ≫ h) := by
  calc restrictionBaseChange f h g r r' ≫ pullback.fst f (g ≫ h)
      = (restrictionCompIso f h g r).inv ≫ r' ≫
          pullback.fst (pullback.snd f h) g ≫ pullback.fst f h := by
        simp [restrictionBaseChange]
    _ = (restrictionCompIso f h g r).inv ≫
          pullback.fst (pullback.snd f h) (r ≫ g) ≫ pullback.fst f h := by
        rw [reassoc_of% hfst]
    _ = pullback.fst f (r ≫ g ≫ h) := restrictionCompIso_inv_fst_fst f h g r

/-- The transported base change is again a base change of `r`. -/
theorem restrictionBaseChange_isPullback {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T)
    (r' : pullback (pullback.snd f h) (r ≫ g) ⟶ pullback (pullback.snd f h) g)
    (sq : IsPullback (pullback.snd (pullback.snd f h) (r ≫ g)) r' r
      (pullback.snd (pullback.snd f h) g)) :
    IsPullback (pullback.snd f (r ≫ g ≫ h)) (restrictionBaseChange f h g r r') r
      (pullback.snd f (g ≫ h)) := by
  refine sq.of_iso (restrictionCompIso f h g r) (Iso.refl _)
    (pullbackLeftPullbackSndIso f h g) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [restrictionBaseChange]
  · simp
  · simp

/-- The inverse comparison isomorphism is compatible with the projections to the test scheme. -/
@[reassoc (attr := simp)]
theorem restrictionCompIso_inv_snd {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T) :
    (restrictionCompIso f h g r).inv ≫ pullback.snd (pullback.snd f h) (r ≫ g) =
      pullback.snd f (r ≫ g ≫ h) := by
  rw [← restrictionCompIso_hom_snd f h g r, Iso.inv_hom_id_assoc]

end Comparison

/-! ### Zero schemes of two isomorphic base changes -/

/-- The closed immersion of the subscheme cut out by quasi-coherent ideal sheaf data is unchanged
by the transport along an equality of the data. -/
theorem subschemeι_eqToHom {X : Scheme.{u}} {I J : X.IdealSheafData} (hIJ : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme hIJ) ≫ J.subschemeι = I.subschemeι := by
  cases hIJ
  simp

/-- **Stacks 0B6Y.** For an isomorphism `u : A ⟶ B` over a scheme `T` carrying an invertible
module `L` with a global section `s`, the zero scheme of the section pulled back to `A` is the
inverse image under `u` of the zero scheme of the section pulled back to `B`. -/
theorem zeroScheme_pullback_comap {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T) (u : A ⟶ B)
    (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s) =
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).comap u := by
  rw [Stacks.Divisors.zeroScheme_pullback qA L s, Stacks.Divisors.zeroScheme_pullback qB L s,
    ← Scheme.IdealSheafData.comap_comp, hu]

/-- **Stacks 0B6Y for two isomorphic base changes.** The isomorphism between the zero schemes of
the two pulled-back sections induced by an isomorphism `u : A ⟶ B` over `T`. -/
def zeroSchemePullbackIso {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T) (u : A ⟶ B) [IsIso u]
    (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ≅
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme :=
  (eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (zeroScheme_pullback_comap qA qB u hu L s))).trans
    (((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).comapIso u).trans
      (asIso (pullback.snd u _)))

/-- The isomorphism of zero schemes of pulled-back sections lies over the isomorphism of the two
base changes. -/
theorem zeroSchemePullbackIso_hom_subschemeι {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T)
    (u : A ⟶ B) [IsIso u] (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (zeroSchemePullbackIso qA qB u hu L s).hom ≫
        (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
      (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u := by
  rw [zeroSchemePullbackIso, Iso.trans_hom, Iso.trans_hom, asIso_hom, eqToIso.hom, Category.assoc,
    Category.assoc, ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    ← Category.assoc, subschemeι_eqToHom (zeroScheme_pullback_comap qA qB u hu L s)]

/-- The inverse isomorphism of zero schemes of pulled-back sections lies over the inverse
isomorphism of the two base changes. -/
theorem zeroSchemePullbackIso_inv_subschemeι {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T)
    (u : A ⟶ B) [IsIso u] (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (zeroSchemePullbackIso qA qB u hu L s).inv ≫
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι =
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ inv u := by
  rw [Iso.inv_comp_eq, ← Category.assoc, zeroSchemePullbackIso_hom_subschemeι, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-! ### Naturality of a Gysin system under a base-change isomorphism -/

/-- The Gysin map of a Gysin system commutes with the transport of Chow groups along an equality
of the structure morphism of the test scheme. -/
theorem GysinSystem.onChow_chowGroupCongr {C : ChowSituation.{u}} (G : GysinSystem C)
    {T : Scheme.{u}} {q q' : T ⟶ C.S} [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (hq : q = q') (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    [LocallyOfFiniteType ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q)]
    [LocallyOfFiniteType ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q')]
    (hqD : (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q =
      (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q')
    (α : chowGroup C q (k + 1)) :
    chowGroupCongr C hqD k (G.onChow q L s k α) =
      G.onChow q' L s k (chowGroupCongr C hq (k + 1) α) := by
  subst hq
  rfl

/-- **The isomorphism case of Stacks 02TA for a Gysin system**: on two isomorphic base changes
of a test scheme the Gysin maps of the pulled-back divisor agree.

The morphism `j` of the two zero schemes is quantified over and constrained by the square of
Remark 0B6Y, `hjsq`, as well as by its commutativity over the base, `hj`, which is what
`Stacks.Chow.properChowPushforward` needs; `Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion`
constrains its open immersion the same way. Both are required: the structure morphism of the
target is not a monomorphism, so `hj` alone would leave the quantification ranging over morphisms
unrelated to the square, which no form of Stacks 02TA constrains; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem`. With the square,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso` discharges the predicate for the
Gysin system of the first Chern class rule. -/
def GysinSystem.IsNaturalUnderBaseChangeIso {C : ChowSituation.{u}} (G : GysinSystem C) : Prop :=
  ∀ {A B T : Scheme.{u}} (t : T ⟶ C.S) [LocallyOfFiniteType t] (qA : A ⟶ T)
    [LocallyOfFiniteType qA] (qB : B ⟶ T) [LocallyOfFiniteType qB] (u : A ⟶ B) [IsIso u]
    (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback qA).obj L)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
      ((Scheme.Modules.pullback qB).obj L)]
    (j : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme)
    [IsProper j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ (qB ≫ t)) =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ (qA ≫ t))
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ (qA ≫ t))
      ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ (qB ≫ t)) j hj k)
    (α : chowGroup C (qA ≫ t) (k + 1)),
    G.onChow (qB ≫ t) ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) k
        (chowPushforwardOfIso C (qA ≫ t) (qB ≫ t) u
          (by rw [← Category.assoc, hu]) (k + 1) α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ (qA ≫ t))
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ (qB ≫ t)) j hj k hfac
        (G.onChow (qA ≫ t) ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s) k α)

/-- **The isomorphism case of Stacks 02TA for a Gysin system**, read against structure morphisms
presented by equalities rather than as literal composites. -/
theorem GysinSystem.onChow_baseChangeIso {C : ChowSituation.{u}} {G : GysinSystem C}
    (hgys : G.IsNaturalUnderBaseChangeIso) {A B T : Scheme.{u}} (t : T ⟶ C.S)
    [LocallyOfFiniteType t] (qA : A ⟶ T) [LocallyOfFiniteType qA] (qB : B ⟶ T)
    [LocallyOfFiniteType qB] (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (hpA : qA ≫ t = pA) (hpB : qB ≫ t = pB) (u : A ⟶ B) [IsIso u]
    (hu : u ≫ qB = qA) (hup : u ≫ pB = pA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (j : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme)
    [IsProper j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
      ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) j hj k)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C pA pB u hup (k + 1))
    (α : chowGroup C pA (k + 1)) :
    G.onChow pB ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) k
        (properChowPushforward C pA pB u hup (k + 1) hfacu α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) j hj k hfac
        (G.onChow pA ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s) k α) := by
  subst hpA
  subst hpB
  exact hgys t qA qB u hu L s k j hjsq hj hfac α

/-! ### Pasting commuting squares -/

/-- Pasting a commuting square onto a further morphism over the base. -/
theorem comp_comp_of_comp {A B C D E : Scheme.{u}} {j : A ⟶ B} {ib : B ⟶ C} {ia : A ⟶ D}
    {u : D ⟶ C} (h1 : j ≫ ib = ia ≫ u) {v : C ⟶ E} {w : D ⟶ E} (h2 : u ≫ v = w) :
    j ≫ (ib ≫ v) = ia ≫ w := by
  rw [← Category.assoc, h1, Category.assoc, h2]

/-- Pasting an identity of composites onto a further morphism over the base. -/
theorem comp_comp_of_eq {A B C E : Scheme.{u}} {j : A ⟶ B} {ib : B ⟶ C} {m : A ⟶ C}
    (h1 : j ≫ ib = m) {v : C ⟶ E} {w : A ⟶ E} (h2 : m ≫ v = w) :
    j ≫ (ib ≫ v) = w := by
  rw [← Category.assoc, h1, h2]

/-- Reassociating a composite of three morphisms and collapsing it in two steps. -/
theorem comp_comp_comp_of_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
    {m : B ⟶ D} {t : A ⟶ D} (h1 : b ≫ c = m) (h2 : a ≫ m = t) : (a ≫ b) ≫ c = t := by
  rw [Category.assoc, h1, h2]

/-- Pasting a commuting square into a longer composite. -/
theorem comp_square_comp {A B C D E : Scheme.{u}} {a : A ⟶ B} {c : B ⟶ C} {d : C ⟶ E}
    {b : B ⟶ D} {u : D ⟶ E} {m : A ⟶ D} (h1 : c ≫ d = b ≫ u) (h2 : a ≫ b = m) :
    a ≫ (c ≫ d) = m ≫ u := by
  rw [h1, ← Category.assoc, h2]

/-- The formal core of the Gysin naturality of a restricted bivariant class: the cap product of
the restriction pushes forward to the Gysin map of the pulled-back divisor, assembled from the
Gysin naturality upstairs (`hc`), the naturality of the Gysin map under the comparison
isomorphism (`hgys`), the two descriptions of the restricted cap products (`hcapD`, `hcapg`) and
the functoriality of proper pushforward. -/
theorem gysinNaturalityAssemble (C : ChowSituation.{u}) {A B D' O' SO' SN' : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    {sD : D' ⟶ C.S} [LocallyOfFiniteType sD] {sO : O' ⟶ C.S} [LocallyOfFiniteType sO]
    {so : SO' ⟶ C.S} [LocallyOfFiniteType so] {sn : SN' ⟶ C.S} [LocallyOfFiniteType sn]
    {u : A ⟶ B} [IsProper u] {v : B ⟶ D'} [IsProper v] {w : A ⟶ O'} [IsProper w]
    {z : O' ⟶ D'} [IsProper z] {b : SO' ⟶ SN'} [IsProper b]
    (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sO = sA) (hz : z ≫ sD = sO)
    (hb : b ≫ sn = so) (hcomp : u ≫ v = w ≫ z) {m i j : ℤ} (hij : i = j)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu m)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv m)
    (hfacw : ProperPushforwardFactorsThroughRationalEquivalence C sA sO w hw m)
    (hfacz : ProperPushforwardFactorsThroughRationalEquivalence C sO sD z hz m)
    (hfacbi : ProperPushforwardFactorsThroughRationalEquivalence C so sn b hb i)
    (hfacbj : ProperPushforwardFactorsThroughRationalEquivalence C so sn b hb j)
    {x : chowGroup C sA m} {y : chowGroup C so i} {capD : chowGroup C sB m}
    {capg : chowGroup C sn i} {Φ : chowGroup C sn j →+ chowGroup C sD m} {Z : chowGroup C sO m}
    (hcapD : capD = properChowPushforward C sA sB u hu m hfacu x)
    (hcapg : capg = properChowPushforward C so sn b hb i hfacbi y)
    (hc : properChowPushforward C sA sO w hw m hfacw x = Z)
    (hgys : Φ (properChowPushforward C so sn b hb j hfacbj
        (Eq.mp (congrArg (chowGroup C so) hij) y)) =
      properChowPushforward C sO sD z hz m hfacz Z) :
    properChowPushforward C sB sD v hv m hfacv capD =
      Φ (Eq.mp (congrArg (chowGroup C sn) hij) capg) := by
  subst hcapD
  subst hcapg
  rw [properChowPushforward_cast C so sn b hb hij hfacbi hfacbj y, hgys, ← hc]
  exact properChowPushforward_comp_eq C sA sB sO sD u v w z hcomp hu hv hw hz m hfacu hfacv
    hfacw hfacz x
/-! ### The cap operation of a restriction -/

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (h : Y' ⟶ Y) [LocallyOfFiniteType h] (p : ℤ)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f]
  [LocallyOfFiniteType h] in
include hf in
/-- The structure morphism of `X' = Y' ×_Y X` over the base factors the one of `Y'` through the
base change of `f`. -/
theorem pullbackSnd_comp_structureMorphism_eq :
    pullback.snd f h ≫ (h ≫ sY) = pullback.fst f h ≫ sX := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, hf]

/-- **Stacks 0F9Z.** The cap operation `res(c) ∩ -` of the restriction of a bivariant class `c`
of degree `p` for `f : X ⟶ Y` along `h : Y' ⟶ Y`: on a test scheme `g : T ⟶ Y'` it is the cap
operation of `c` at `g ≫ h`, pushed forward along the canonical isomorphism
`T ×_Y X ≅ (Y' ×_Y X) ×_{Y'} T`. -/
@[stacks 0F9Z "the cap operation of the restriction"]
def bivariantRestrictionCap (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y')
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ (h ≫ sY)) k →+
      chowGroup C (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) (k - p) :=
  (chowPushforwardOfIso C (pullback.fst f (g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
      (pullbackLeftPullbackSndIso f h g).inv (by simp) (k - p)).comp
    ((c.cap (g ≫ h) k).comp
      (chowGroupCongr C (Category.assoc g h sY).symm k).toAddMonoidHom)

/-- The cap operation of a restriction, read on an element. -/
theorem bivariantRestrictionCap_apply (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (h ≫ sY)) k) :
    bivariantRestrictionCap C G sX sY f hf h p c g k α =
      chowPushforwardOfIso C (pullback.fst f (g ≫ h) ≫ sX)
        (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
        (pullbackLeftPullbackSndIso f h g).inv (by simp) (k - p)
        (c.cap (g ≫ h) k (chowGroupCongr C (Category.assoc g h sY).symm k α)) :=
  rfl

/-- The cap operation of the restriction, read through any identification of the base change of
`pullback.snd f h` along `g` with the base change of `f` along a morphism equal to `g ≫ h`. -/
theorem bivariantRestrictionCap_eq (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y') [LocallyOfFiniteType g] (m : T ⟶ Y) [LocallyOfFiniteType m]
    (hm : g ≫ h = m) (hmY : g ≫ (h ≫ sY) = m ≫ sY)
    (w : pullback (pullback.snd f h) g ≅ pullback f m)
    (hwfst : w.hom ≫ pullback.fst f m = pullback.fst (pullback.snd f h) g ≫ pullback.fst f h)
    (hwsnd : w.hom ≫ pullback.snd f m = pullback.snd (pullback.snd f h) g) (k : ℤ)
    (hbase : w.inv ≫ (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) =
      pullback.fst f m ≫ sX)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f m ≫ sX)
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) w.inv hbase (k - p))
    (β : chowGroup C (g ≫ (h ≫ sY)) k) :
    bivariantRestrictionCap C G sX sY f hf h p c g k β =
      properChowPushforward C (pullback.fst f m ≫ sX)
        (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) w.inv hbase (k - p) hfac
        (c.cap m k (chowGroupCongr C hmY k β)) := by
  subst hm
  have hw : w = pullbackLeftPullbackSndIso f h g := by
    refine Iso.ext (pullback.hom_ext ?_ ?_)
    · rw [pullbackLeftPullbackSndIso_hom_fst]; exact hwfst
    · rw [pullbackLeftPullbackSndIso_hom_snd]; exact hwsnd
  subst hw
  rfl

/-- The comparison isomorphism `T ×_Y X ≅ (Y' ×_Y X) ×_{Y'} T` is compatible with the structure
morphisms over the base. -/
private theorem pullbackLeftPullbackSndIso_inv_base {X Y Y' T S : Scheme.{u}} (sX : X ⟶ S)
    (f : X ⟶ Y) (h : Y' ⟶ Y) (g : T ⟶ Y') :
    (pullbackLeftPullbackSndIso f h g).inv ≫
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) =
        pullback.fst f (g ≫ h) ≫ sX := by
  simp

/-- The comparison isomorphism at a composite test morphism is compatible with the structure
morphisms over the base. -/
private theorem restrictionCompIso_inv_base {X Y Y' T T' S : Scheme.{u}} (sX : X ⟶ S)
    (f : X ⟶ Y) (h : Y' ⟶ Y) (g : T ⟶ Y') (r : T' ⟶ T) :
    (restrictionCompIso f h g r).inv ≫
      (pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX)) =
        pullback.fst f (r ≫ g ≫ h) ≫ sX := by
  simp

/-- A base change `r'` of `r` compatible with the first projections is compatible with the
structure morphisms over the base. -/
private theorem restrictionBaseChange_source_base {X Y Y' T T' S : Scheme.{u}} (sX : X ⟶ S)
    (f : X ⟶ Y) (h : Y' ⟶ Y) (g : T ⟶ Y') (r : T' ⟶ T)
    (r' : pullback (pullback.snd f h) (r ≫ g) ⟶ pullback (pullback.snd f h) g)
    (hfst : r' ≫ pullback.fst (pullback.snd f h) g = pullback.fst (pullback.snd f h) (r ≫ g)) :
    r' ≫ (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) =
      pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX) :=
  comp_comp_of_eq hfst rfl

/-- The transported base change is compatible with the structure morphisms over the base. -/
private theorem restrictionBaseChange_base {X Y Y' T T' S : Scheme.{u}} (sX : X ⟶ S)
    (f : X ⟶ Y) (h : Y' ⟶ Y) (g : T ⟶ Y') (r : T' ⟶ T)
    (r' : pullback (pullback.snd f h) (r ≫ g) ⟶ pullback (pullback.snd f h) g)
    (hfst : r' ≫ pullback.fst (pullback.snd f h) g = pullback.fst (pullback.snd f h) (r ≫ g)) :
    restrictionBaseChange f h g r r' ≫ (pullback.fst f (g ≫ h) ≫ sX) =
      pullback.fst f (r ≫ g ≫ h) ≫ sX :=
  comp_comp_of_eq (restrictionBaseChange_fst f h g r r' hfst) rfl

/-- The cap operation of the restriction at `g`, as the cap operation of `c` at `g ≫ h`
pushed forward along the comparison isomorphism. -/
private theorem bivariantRestrictionCap_eq_pushforward (c : BivariantClass C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f (g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
      (pullbackLeftPullbackSndIso f h g).inv (pullbackLeftPullbackSndIso_inv_base sX f h g)
      (k - p))
    (β : chowGroup C (g ≫ (h ≫ sY)) k) :
    bivariantRestrictionCap C G sX sY f hf h p c g k β =
      properChowPushforward C (pullback.fst f (g ≫ h) ≫ sX)
        (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
        (pullbackLeftPullbackSndIso f h g).inv (pullbackLeftPullbackSndIso_inv_base sX f h g)
        (k - p) hfac (c.cap (g ≫ h) k (chowGroupCongr C (Category.assoc g h sY).symm k β)) :=
  bivariantRestrictionCap_eq C G sX sY f hf h p c g (g ≫ h) rfl (Category.assoc g h sY).symm
    (pullbackLeftPullbackSndIso f h g) (by simp) (by simp) k _ hfac β

/-- The cap operation of the restriction at `r ≫ g`, as the cap operation of `c` at `r ≫ g ≫ h`
pushed forward along the comparison isomorphism. -/
private theorem bivariantRestrictionCap_eq_pushforward_comp (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y') (r : T' ⟶ T) [LocallyOfFiniteType g]
    [LocallyOfFiniteType r] (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f (r ≫ g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX))
      (restrictionCompIso f h g r).inv (restrictionCompIso_inv_base sX f h g r) (k - p))
    (β : chowGroup C ((r ≫ g) ≫ (h ≫ sY)) k) :
    bivariantRestrictionCap C G sX sY f hf h p c (r ≫ g) k β =
      properChowPushforward C (pullback.fst f (r ≫ g ≫ h) ≫ sX)
        (pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX))
        (restrictionCompIso f h g r).inv (restrictionCompIso_inv_base sX f h g r) (k - p) hfac
        (c.cap (r ≫ g ≫ h) k (chowGroupCongr C (by simp only [Category.assoc]) k β)) :=
  bivariantRestrictionCap_eq C G sX sY f hf h p c (r ≫ g) (r ≫ g ≫ h) (Category.assoc r g h)
    (by simp only [Category.assoc]) (restrictionCompIso f h g r) (by simp) (by simp) k _ hfac β

/-! ### The proper-pushforward axiom of a restriction -/

/-- **Stacks 0F9Z.** The cap operation of the restriction of `c` along `h` commutes with proper
pushforward: the proper-pushforward axiom of Stacks 0B76 for the restricted class, proved from
that axiom for `c`, the functoriality of proper pushforward on Chow groups and Stacks 02S2 for
the comparison isomorphisms. -/
theorem bivariantRestrictionCap_proper_naturality (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (r : T' ⟶ T) [IsProper r]
    (r' : pullback (pullback.snd f h) (r ≫ g) ⟶ pullback (pullback.snd f h) g)
    (sq : IsPullback (pullback.snd (pullback.snd f h) (r ≫ g)) r' r
      (pullback.snd (pullback.snd f h) g))
    (hfst : r' ≫ pullback.fst (pullback.snd f h) g = pullback.fst (pullback.snd f h) (r ≫ g))
    (k : ℤ) :
    letI : IsProper r' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((r ≫ g) ≫ (h ≫ sY))
        (g ≫ (h ≫ sY)) r (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX))
        (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) r'
        (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C ((r ≫ g) ≫ (h ≫ sY)) k),
      bivariantRestrictionCap C G sX sY f hf h p c g k
          (properChowPushforward C ((r ≫ g) ≫ (h ≫ sY)) (g ≫ (h ≫ sY)) r
            (by simp [Category.assoc]) k hfac α) =
        properChowPushforward C
          (pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX))
          (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) r'
          (by rw [← Category.assoc, hfst]) (k - p) hfac'
          (bivariantRestrictionCap C G sX sY f hf h p c (r ≫ g) k α) := by
  intro hfac hfac' α
  have hassoc : (r ≫ g) ≫ (h ≫ sY) = (r ≫ g ≫ h) ≫ sY := by simp only [Category.assoc]
  have hrbase : r ≫ ((g ≫ h) ≫ sY) = (r ≫ g ≫ h) ≫ sY := by simp only [Category.assoc]
  have hdfst := restrictionBaseChange_fst f h g r r' hfst
  have sq' := restrictionBaseChange_isPullback f h g r r' sq
  have : IsProper r' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have : IsProper (restrictionBaseChange f h g r r') :=
    MorphismProperty.of_isPullback sq' (P := @IsProper) inferInstance
  have he₀base := pullbackLeftPullbackSndIso_inv_base sX f h g
  have he₁base := restrictionCompIso_inv_base sX f h g r
  have he₀hom : (pullbackLeftPullbackSndIso f h g).hom ≫ (pullback.fst f (g ≫ h) ≫ sX) =
      pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX) := by simp
  have hr'base := restrictionBaseChange_source_base sX f h g r r' hfst
  have hdbase := restrictionBaseChange_base sX f h g r r' hfst
  have hdcbase : (restrictionBaseChange f h g r r' ≫
        (pullbackLeftPullbackSndIso f h g).inv) ≫
          (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) =
      pullback.fst f (r ≫ g ≫ h) ≫ sX := by rw [Category.assoc, he₀base, hdbase]
  have hface₀ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ he₀base (k - p)
  have hface₁ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ he₁base (k - p)
  have hfacr : ProperPushforwardFactorsThroughRationalEquivalence C ((r ≫ g ≫ h) ≫ sY)
      ((g ≫ h) ≫ sY) r hrbase k :=
    properPushforwardFactorsThroughRationalEquivalence_congr_base C hassoc
      (Category.assoc g h sY).symm r _ hrbase k hfac
  have hfacd : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f (r ≫ g ≫ h) ≫ sX) (pullback.fst f (g ≫ h) ≫ sX)
      (restrictionBaseChange f h g r r') hdbase (k - p) :=
    properPushforwardFactorsThroughRationalEquivalence_isIso_comp_isIso C
      (pullback.fst f (r ≫ g ≫ h) ≫ sX) (pullback.fst f (g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX))
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
      (restrictionCompIso f h g r).inv r' (pullbackLeftPullbackSndIso f h g).hom
      he₁base hr'base he₀hom (k - p) hfac'
  have hfacdc := properPushforwardFactorsThroughRationalEquivalence_comp C
    (pullback.fst f (r ≫ g ≫ h) ≫ sX) (pullback.fst f (g ≫ h) ≫ sX)
    (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
    (restrictionBaseChange f h g r r') (pullbackLeftPullbackSndIso f h g).inv
    hdbase he₀base (k - p) hfacd hface₀
  rw [bivariantRestrictionCap_eq_pushforward C G sX sY f hf h p c g k hface₀,
    bivariantRestrictionCap_eq_pushforward_comp C G sX sY f hf h p c g r k hface₁,
    properChowPushforward_chowGroupCongr C hassoc (Category.assoc g h sY).symm r _ hrbase k
      hfac hfacr α,
    c.proper_naturality (g ≫ h) r (restrictionBaseChange f h g r r') sq' hdfst k
      hfacr hfacd,
    ← properChowPushforward_comp_apply C (pullback.fst f (r ≫ g ≫ h) ≫ sX)
      (pullback.fst f (g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
      (restrictionBaseChange f h g r r') (pullbackLeftPullbackSndIso f h g).inv
      (restrictionBaseChange f h g r r' ≫ (pullbackLeftPullbackSndIso f h g).inv) rfl
      hdbase he₀base hdcbase (k - p) hfacd hface₀ hfacdc,
    properChowPushforward_comp_apply C (pullback.fst f (r ≫ g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) (r ≫ g) ≫ (pullback.fst f h ≫ sX))
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
      (restrictionCompIso f h g r).inv r'
      (restrictionBaseChange f h g r r' ≫ (pullbackLeftPullbackSndIso f h g).inv)
      (restrictionBaseChange_comp_inv f h g r r').symm he₁base hr'base hdcbase (k - p)
      hface₁ hfac' hfacdc]

/-! ### The flat-pullback axiom of a restriction -/

/-- **Stacks 0F9Z.** The cap operation of the restriction of `c` along `h` commutes with flat
pullback of fixed relative dimension: the flat naturality axiom of
`Stacks.Chow.BivariantClass` for `Stacks.Chow.bivariantRestrictionCap`.

The degrees are `(k + r) - p` on the left and `(k - p) + r` on the right, the same integer
written two ways, which is why the conclusion is an `HEq`. -/
theorem bivariantRestrictionCap_flat_naturality (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (h₂ : T' ⟶ T)
    [LocallyOfFiniteType h₂] [Flat h₂] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h₂ r)
    (h₂' : pullback (pullback.snd f h) (h₂ ≫ g) ⟶ pullback (pullback.snd f h) g)
    (sq : IsPullback (pullback.snd (pullback.snd f h) (h₂ ≫ g)) h₂' h₂
      (pullback.snd (pullback.snd f h) g))
    (hfst : h₂' ≫ pullback.fst (pullback.snd f h) g =
      pullback.fst (pullback.snd f h) (h₂ ≫ g)) (k : ℤ) :
    letI : LocallyOfFiniteType h₂' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h₂' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hrd' : AlgebraicGeometry.RelativeDimension h₂' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h₂ ≫ g) ≫ (h ≫ sY))
        (g ≫ (h ≫ sY)) h₂ (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst (pullback.snd f h) (h₂ ≫ g) ≫ (pullback.fst f h ≫ sX))
        (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) h₂'
        (by rw [← Category.assoc, hfst]) r hrd' (k - p))
      (α : chowGroup C (g ≫ (h ≫ sY)) k),
      HEq
        (bivariantRestrictionCap C G sX sY f hf h p c (h₂ ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((h₂ ≫ g) ≫ (h ≫ sY)) (g ≫ (h ≫ sY)) h₂
            (by simp [Category.assoc]) r hr k hfac α))
        (flatPullbackChow C
          (pullback.fst (pullback.snd f h) (h₂ ≫ g) ≫ (pullback.fst f h ≫ sX))
          (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) h₂'
          (by rw [← Category.assoc, hfst]) r hrd' (k - p) hfac'
          (bivariantRestrictionCap C G sX sY f hf h p c g k α)) := by
  intro hrd' hfac hfac' α
  have hft' : LocallyOfFiniteType h₂' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hfl' : Flat h₂' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hassoc : (h₂ ≫ g) ≫ (h ≫ sY) = (h₂ ≫ g ≫ h) ≫ sY := by simp only [Category.assoc]
  have hgY : g ≫ (h ≫ sY) = (g ≫ h) ≫ sY := (Category.assoc g h sY).symm
  have hrY : h₂ ≫ ((g ≫ h) ≫ sY) = (h₂ ≫ g ≫ h) ≫ sY := by simp only [Category.assoc]
  have hvY : h₂ ≫ (g ≫ (h ≫ sY)) = (h₂ ≫ g) ≫ (h ≫ sY) := by simp only [Category.assoc]
  have hdfst := restrictionBaseChange_fst f h g h₂ h₂' hfst
  have sq' := restrictionBaseChange_isPullback f h g h₂ h₂' sq
  have hftd : LocallyOfFiniteType (restrictionBaseChange f h g h₂ h₂') :=
    MorphismProperty.of_isPullback sq' (P := @LocallyOfFiniteType) inferInstance
  have hfld : Flat (restrictionBaseChange f h g h₂ h₂') :=
    MorphismProperty.of_isPullback sq' (P := @Flat) inferInstance
  have hdr : AlgebraicGeometry.RelativeDimension (restrictionBaseChange f h g h₂ h₂') r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq' hr
  have he₀base := pullbackLeftPullbackSndIso_inv_base sX f h g
  have he₁base := restrictionCompIso_inv_base sX f h g h₂
  have hvbase := restrictionBaseChange_source_base sX f h g h₂ h₂' hfst
  have hdbase := restrictionBaseChange_base sX f h g h₂ h₂' hfst
  have hsqd := restrictionBaseChange_comp_inv f h g h₂ h₂'
  have hface₀ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ he₀base (k - p)
  have hface₁ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ he₁base
    (k + (r : ℤ) - p)
  have hfacG : FlatPullbackFactorsThroughRationalEquivalence C ((h₂ ≫ g ≫ h) ≫ sY)
      ((g ≫ h) ≫ sY) h₂ hrY r hr k :=
    flatPullbackFactorsThroughRationalEquivalence_congr_base C hassoc hgY h₂ hvY hrY r hr k hfac
  have hfacd := flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C
    (pullback.fst f (g ≫ h) ≫ sX)
    (pullback.fst f (h₂ ≫ g ≫ h) ≫ sX)
    (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
    (pullback.fst (pullback.snd f h) (h₂ ≫ g) ≫ (pullback.fst f h ≫ sX))
    (pullbackLeftPullbackSndIso f h g).inv he₀base (restrictionCompIso f h g h₂).inv he₁base
    (restrictionBaseChange f h g h₂ h₂') hdbase h₂' hvbase hsqd r hdr hrd' (k - p) hfac'
  have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
  have hc := c.flat_naturality (g ≫ h) h₂ r hr (restrictionBaseChange f h g h₂ h₂') sq' hdfst k
    hdr hfacG hfacd (chowGroupCongr C hgY k α)
  rw [bivariantRestrictionCap_eq_pushforward_comp C G sX sY f hf h p c g h₂ (k + (r : ℤ)) hface₁,
    bivariantRestrictionCap_eq_pushforward C G sX sY f hf h p c g k hface₀,
    flatPullbackChow_chowGroupCongr C hassoc hgY h₂ hvY hrY r hr k hfac hfacG α,
    properChowPushforward_eq_chowPushforwardOfIso C _ _ (pullbackLeftPullbackSndIso f h g).inv
      he₀base (k - p) hface₀,
    flatPullbackChow_chowPushforwardOfIso C (pullback.fst f (g ≫ h) ≫ sX)
      (pullback.fst f (h₂ ≫ g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
      (pullback.fst (pullback.snd f h) (h₂ ≫ g) ≫ (pullback.fst f h ≫ sX))
      (pullbackLeftPullbackSndIso f h g).inv he₀base (restrictionCompIso f h g h₂).inv he₁base
      (restrictionBaseChange f h g h₂ h₂') hdbase h₂' hvbase hsqd r hdr hrd' (k - p) hfacd
      hfac',
    properChowPushforward_eq_chowPushforwardOfIso C _ _ (restrictionCompIso f h g h₂).inv
      he₁base (k + (r : ℤ) - p) hface₁]
  exact heq_map_index hidx hc
    (fun n x => chowPushforwardOfIso C (pullback.fst f (h₂ ≫ g ≫ h) ≫ sX)
      (pullback.fst (pullback.snd f h) (h₂ ≫ g) ≫ (pullback.fst f h ≫ sX))
      (restrictionCompIso f h g h₂).inv he₁base n x)

/-! ### The Gysin axiom of a restriction -/

/-- **Stacks 0F9Z.** The cap operation of the restriction of `c` along `h` commutes with the
Gysin map of the zero scheme of a section of an invertible module on a test scheme: the third
naturality condition of Stacks 0B76 for the restricted class.

Unlike the proper and the flat axiom, this one is not a consequence of the axioms of `c`: the
restricted cap operation lands on a base change of `f` over `Y'` while `c` caps into one over
`Y`, and the first Chern class rules a `Stacks.Chow.GysinSystem` provides at two isomorphic
schemes are unrelated data. The hypothesis is the isomorphism case of Stacks 02TA for the
system. -/
theorem bivariantRestrictionCap_gysin_naturality (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y')
    [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback (pullback.snd f h) g).sheaf.obj
      (pullback (pullback.snd f h) g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd (pullback.snd f h) g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd (pullback.snd f h) g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (pullback.snd f h) g) L s
    let E := Stacks.Divisors.zeroScheme (pullback (pullback.snd f h) g) L' s'
    ∀ (e : pullback (pullback.snd f h) (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι =
        bivariantBaseChangeMap (pullback.snd f h) g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (pullback.snd f h) g ≫
          (pullback.fst f h ≫ sX)) =
        pullback.fst (pullback.snd f h) (D.subschemeι ≫ g) ≫ (pullback.fst f h ≫ sX))
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (pullback.snd f h) (D.subschemeι ≫ g) ≫ (pullback.fst f h ≫ sX))
        (E.subschemeι ≫ pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
        e.hom hbase (k - p))
      (α : chowGroup C (g ≫ (h ≫ sY)) (k + 1)),
      properChowPushforward C
          (pullback.fst (pullback.snd f h) (D.subschemeι ≫ g) ≫ (pullback.fst f h ≫ sX))
          (E.subschemeι ≫ pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX))
          e.hom hbase (k - p) hfac
          (bivariantRestrictionCap C G sX sY f hf h p c (D.subschemeι ≫ g) k
            (G.onChow (g ≫ (h ≫ sY)) L s k α)) =
        G.onChow (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C
            (pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX)))
            (by omega : (k + 1) - p = (k - p) + 1))
            (bivariantRestrictionCap C G sX sY f hf h p c g (k + 1) α)) := by
  dsimp only
  intro e he hbase hfac α
  have hidx : (k + 1) - p = (k - p) + 1 := by omega
  have hSO : pullback.snd f (g ≫ h) ≫ (g ≫ (h ≫ sY)) = pullback.fst f (g ≫ h) ≫ sX := by
    rw [← Category.assoc g h sY, ← Category.assoc,
      ← pullback.condition (f := f) (g := g ≫ h), Category.assoc, hf]
  have hSN : pullback.snd (pullback.snd f h) g ≫ (g ≫ (h ≫ sY)) =
      pullback.fst (pullback.snd f h) g ≫ (pullback.fst f h ≫ sX) := by
    rw [← Category.assoc, ← pullback.condition (f := pullback.snd f h) (g := g),
      Category.assoc, pullbackSnd_comp_structureMorphism_eq C sX sY f hf h]
  have hqo : (pullbackLeftPullbackSndIso f h g).inv ≫ pullback.snd (pullback.snd f h) g =
      pullback.snd f (g ≫ h) := by simp
  have hbBase := pullbackLeftPullbackSndIso_inv_base sX f h g
  have hjj := zeroSchemePullbackIso_hom_subschemeι _ _ _ hqo L s
  have hjjinv := zeroSchemePullbackIso_inv_subschemeι _ _ _ hqo L s
  rw [show inv (pullbackLeftPullbackSndIso f h g).inv =
    (pullbackLeftPullbackSndIso f h g).hom from by simp] at hjjinv
  have hjBase := comp_comp_of_comp hjj hbBase
  have hbcm : bivariantBaseChangeMap f (g ≫ h) (Stacks.Divisors.zeroScheme T L s).subschemeι ≫
      (pullback.fst f (g ≫ h) ≫ sX) =
      pullback.fst f ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ h) ≫ sX := by
    simp [bivariantBaseChangeMap]
  have hbcmComp :
      (restrictionCompIso f h g (Stacks.Divisors.zeroScheme T L s).subschemeι).inv ≫
        (bivariantBaseChangeMap (pullback.snd f h) g
            (Stacks.Divisors.zeroScheme T L s).subschemeι ≫
          (pullbackLeftPullbackSndIso f h g).hom) =
        bivariantBaseChangeMap f (g ≫ h) (Stacks.Divisors.zeroScheme T L s).subschemeι := by
    apply pullback.hom_ext
    · simp [bivariantBaseChangeMap]
    · simp [bivariantBaseChangeMap]
  have heOld :
      (((restrictionCompIso f h g (Stacks.Divisors.zeroScheme T L s).subschemeι).symm.trans
          e).trans (zeroSchemePullbackIso _ _ _ hqo L s).symm).hom ≫
          (Stacks.Divisors.zeroScheme _ _ _).subschemeι =
        bivariantBaseChangeMap f (g ≫ h) (Stacks.Divisors.zeroScheme T L s).subschemeι := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [comp_square_comp hjjinv he]
    exact hbcmComp
  have hbaseOld := comp_comp_of_eq heOld hbcm
  have hmid : (((restrictionCompIso f h g
          (Stacks.Divisors.zeroScheme T L s).subschemeι).symm.trans e).trans
        (zeroSchemePullbackIso _ _ _ hqo L s).symm).hom ≫
          (zeroSchemePullbackIso _ _ _ hqo L s).hom =
      (restrictionCompIso f h g (Stacks.Divisors.zeroScheme T L s).subschemeι).inv ≫ e.hom := by
    simp
  have hmY : ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ (h ≫ sY) =
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ h) ≫ sY := by
    simp only [Category.assoc]
  have hbD := restrictionCompIso_inv_base sX f h g (Stacks.Divisors.zeroScheme T L s).subschemeι
  have hfacBD := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hbD (k - p)
  have hfacb := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hbBase
    ((k + 1) - p)
  have hfacb' := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hbBase
    ((k - p) + 1)
  have hfacOld := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hbaseOld
    (k - p)
  have hfacJ := properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ hjBase (k - p)
  have hc := c.gysin_naturality (g ≫ h) L s k
    (((restrictionCompIso f h g (Stacks.Divisors.zeroScheme T L s).subschemeι).symm.trans
      e).trans (zeroSchemePullbackIso _ _ _ hqo L s).symm) heOld hbaseOld hfacOld α
  have hgysApplied := GysinSystem.onChow_baseChangeIso hgys (g ≫ (h ≫ sY))
    (pullback.snd f (g ≫ h)) (pullback.snd (pullback.snd f h) g) _ _ hSO hSN
    (pullbackLeftPullbackSndIso f h g).inv hqo hbBase L s (k - p)
    (zeroSchemePullbackIso _ _ _ hqo L s).hom
    (zeroSchemePullbackIso_hom_subschemeι _ _ _ hqo L s) hjBase hfacJ hfacb'
    (Eq.mp (congrArg (chowGroup C (pullback.fst f (g ≫ h) ≫ sX)) hidx)
      (c.cap (g ≫ h) (k + 1) α))
  have hcgg : chowGroupCongr C (Category.assoc g h sY).symm (k + 1) α = α :=
    eq_of_heq (chowGroupCongr_heq C (Category.assoc g h sY).symm (k + 1) α)
  have hcgD : chowGroupCongr C hmY k (G.onChow (g ≫ (h ≫ sY)) L s k α) =
      G.onChow ((g ≫ h) ≫ sY) L s k α :=
    (GysinSystem.onChow_chowGroupCongr G (Category.assoc g h sY).symm L s k hmY α).trans
      (congrArg (G.onChow ((g ≫ h) ≫ sY) L s k) hcgg)
  have hcapD := (bivariantRestrictionCap_eq_pushforward_comp C G sX sY f hf h p c g
      (Stacks.Divisors.zeroScheme T L s).subschemeι k hfacBD
      (G.onChow (g ≫ (h ≫ sY)) L s k α)).trans
    (DFunLike.congr_arg (properChowPushforward C _ _ _ hbD (k - p) hfacBD)
      (DFunLike.congr_arg (c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g ≫ h) k)
        hcgD))
  have hcapg := (bivariantRestrictionCap_eq_pushforward C G sX sY f hf h p c g (k + 1) hfacb
      α).trans
    (DFunLike.congr_arg (properChowPushforward C _ _ _ hbBase ((k + 1) - p) hfacb)
      (DFunLike.congr_arg (c.cap (g ≫ h) (k + 1)) hcgg))
  exact gysinNaturalityAssemble C hbD hbase hbaseOld hjBase hbBase hmid.symm hidx hfacBD hfac
    hfacOld hfacJ hfacb hfacb' hcapD hcapg hc hgysApplied

/-! ### The restricted class -/

/-- **Stacks 0F9Z.** The restriction `res(c)` of a bivariant class `c` of degree `p` for
`f : X ⟶ Y` along `h : Y' ⟶ Y`: the bivariant class of degree `p` for the base change
`X ×_Y Y' ⟶ Y'` with `res(c) ∩ α = c ∩ α`. Together with
`Stacks.Chow.bivariantRestriction_add`, `_neg` and `_zero` this is the restriction map
`A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')` of the tag.

The Gysin axiom of a restricted class is not a consequence of the axioms of `c`, so the
construction carries the isomorphism case of Stacks 02TA for the Gysin system; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction`. -/
@[stacks 0F9Z]
def bivariantRestriction (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sX sY f hf p) :
    BivariantClass C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p where
  cap g _ k := bivariantRestrictionCap C G sX sY f hf h p c g k
  cap_properPushforward := by
    intro T₀ T₀' g₀ _ w₀ _ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantRestrictionCap_proper_naturality C G sX sY f hf h p c)
      g₀ w₀ w₀' sq₀ hfst₀ k₀ _ _ α₀
  cap_flatPullbackChow := by
    intro T₀ T₀' g₀ _ w₀ _ _ r₀ hr₀ w₀' sq₀ hfst₀ k₀ α₀
    exact (bivariantRestrictionCap_flat_naturality C G sX sY f hf h p c)
      g₀ w₀ r₀ hr₀ w₀' sq₀ hfst₀ k₀ _ _ _ α₀
  cap_gysin := by
    intro T₀ g₀ _ L₀ _ s₀ k₀ _ _ _ _ ε₀ hε₀ hbase₀ α₀
    exact (bivariantRestrictionCap_gysin_naturality C G sX sY f hf h p hgys c)
      g₀ L₀ s₀ k₀ ε₀ hε₀ hbase₀ _ α₀

/-- **Stacks 0F9Z.** The restriction caps by the restricted cap operation: `res(c) ∩ α = c ∩ α`,
after the canonical identification of the two fibre products. -/
@[simp]
theorem bivariantRestriction_cap (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (h ≫ sY)) k) :
    (bivariantRestriction C G sX sY f hf h p hgys c).cap g k α =
      bivariantRestrictionCap C G sX sY f hf h p c g k α :=
  rfl

/-! ### The characterization of the restriction -/

/-- **Stacks 0F9Z.** The assertion that a bivariant class for the base change `X ×_Y Y' ⟶ Y'` is
the restriction of `c` along `h : Y' ⟶ Y`: on every test scheme its cap operation is that of `c`,
transported along the canonical comparison isomorphism of the two fibre products. -/
def IsBivariantRestriction (c : BivariantClass C G sX sY f hf p)
    (c' : BivariantClass C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ (h ≫ sY)) k),
    c'.cap g k α = bivariantRestrictionCap C G sX sY f hf h p c g k α

/-! ### Uniqueness and additivity of the restriction -/

/-- **Stacks 0F9Z.** The cap formula determines the restriction: two bivariant classes that are
both the restriction of `c` along `h` are equal. -/
theorem eq_of_isBivariantRestriction {c : BivariantClass C G sX sY f hf p}
    {c' d' : BivariantClass C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p}
    (hc' : IsBivariantRestriction C G sX sY f hf h p c c')
    (hd' : IsBivariantRestriction C G sX sY f hf h p c d') : c' = d' := by
  refine BivariantClass.ext C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p ?_
  intro T g _ k α
  rw [hc' g k α, hd' g k α]

namespace IsBivariantRestriction

/-- Restriction is additive: the restriction of a sum is the sum of the restrictions. -/
theorem add {c d : BivariantClass C G sX sY f hf p}
    {c' d' : BivariantClass C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p}
    (hc : IsBivariantRestriction C G sX sY f hf h p c c')
    (hd : IsBivariantRestriction C G sX sY f hf h p d d') :
    IsBivariantRestriction C G sX sY f hf h p (c + d) (c' + d') := by
  intro T g _ k α
  rw [BivariantClass.add_cap, hc g k α, hd g k α]
  simp only [bivariantRestrictionCap_apply, BivariantClass.add_cap, map_add]

/-- Restriction negates: the restriction of a negated class is the negated restriction. -/
theorem neg {c : BivariantClass C G sX sY f hf p}
    {c' : BivariantClass C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p}
    (hc : IsBivariantRestriction C G sX sY f hf h p c c') :
    IsBivariantRestriction C G sX sY f hf h p (-c) (-c') := by
  intro T g _ k α
  rw [BivariantClass.neg_cap, hc g k α]
  simp only [bivariantRestrictionCap_apply, BivariantClass.neg_cap, map_neg]

/-- The restriction of the zero class is zero. -/
theorem zero : IsBivariantRestriction C G sX sY f hf h p 0 0 := by
  intro T g _ k α
  rw [BivariantClass.zero_cap]
  simp only [bivariantRestrictionCap_apply, BivariantClass.zero_cap, map_zero]

end IsBivariantRestriction


/-- **Stacks 0F9Z.** The restriction of `c` along `h` is the restriction of `c` along `h`: the
construction satisfies the characterization, so it is the unique class that does. -/
theorem isBivariantRestriction_bivariantRestriction (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sX sY f hf p) :
    IsBivariantRestriction C G sX sY f hf h p c
      (bivariantRestriction C G sX sY f hf h p hgys c) := by
  intro T g _ k α
  rfl

/-- **Stacks 0F9Z.** Restriction along `h` is additive. -/
theorem bivariantRestriction_add (hgys : G.IsNaturalUnderBaseChangeIso)
    (c d : BivariantClass C G sX sY f hf p) :
    bivariantRestriction C G sX sY f hf h p hgys (c + d) =
      bivariantRestriction C G sX sY f hf h p hgys c +
        bivariantRestriction C G sX sY f hf h p hgys d :=
  eq_of_isBivariantRestriction C G sX sY f hf h p
    (isBivariantRestriction_bivariantRestriction C G sX sY f hf h p hgys (c + d))
    (IsBivariantRestriction.add C G sX sY f hf h p
      (isBivariantRestriction_bivariantRestriction C G sX sY f hf h p hgys c)
      (isBivariantRestriction_bivariantRestriction C G sX sY f hf h p hgys d))

/-- **Stacks 0F9Z.** Restriction along `h` commutes with negation. -/
theorem bivariantRestriction_neg (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sX sY f hf p) :
    bivariantRestriction C G sX sY f hf h p hgys (-c) =
      -bivariantRestriction C G sX sY f hf h p hgys c :=
  eq_of_isBivariantRestriction C G sX sY f hf h p
    (isBivariantRestriction_bivariantRestriction C G sX sY f hf h p hgys (-c))
    (IsBivariantRestriction.neg C G sX sY f hf h p
      (isBivariantRestriction_bivariantRestriction C G sX sY f hf h p hgys c))

/-- **Stacks 0F9Z.** Restriction along `h` carries the zero class to the zero class. -/
theorem bivariantRestriction_zero (hgys : G.IsNaturalUnderBaseChangeIso) :
    bivariantRestriction C G sX sY f hf h p hgys 0 = 0 :=
  eq_of_isBivariantRestriction C G sX sY f hf h p
    (isBivariantRestriction_bivariantRestriction C G sX sY f hf h p hgys 0)
    (IsBivariantRestriction.zero C G sX sY f hf h p)

/-- **Stacks 0F9Z.** The restriction map `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')` along `h : Y' ⟶ Y`, as a
homomorphism of groups. -/
@[stacks 0F9Z]
def bivariantRestrictionAddHom (hgys : G.IsNaturalUnderBaseChangeIso) :
    BivariantClass C G sX sY f hf p →+
      BivariantClass C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p where
  toFun c := bivariantRestriction C G sX sY f hf h p hgys c
  map_zero' := bivariantRestriction_zero C G sX sY f hf h p hgys
  map_add' := bivariantRestriction_add C G sX sY f hf h p hgys

/-! ### Transports and pushforwards along isomorphisms -/

/-- Two successive transports along equalities of structure morphisms compose to the transport
along the composite equality. -/
theorem chowGroupCongr_chowGroupCongr {Z : Scheme.{u}} {q q' q'' : Z ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] [LocallyOfFiniteType q''] (hq : q = q')
    (hq' : q' = q'') (k : ℤ) (α : chowGroup C q k) :
    chowGroupCongr C hq' k (chowGroupCongr C hq k α) = chowGroupCongr C (hq.trans hq') k α := by
  subst hq
  subst hq'
  rfl

/-- Pushforward on Chow groups along the identity is the identity. -/
theorem chowPushforwardOfIso_id {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (k : ℤ)
    (α : chowGroup C sZ k) :
    chowPushforwardOfIso C sZ sZ (𝟙 Z) (Category.id_comp sZ) k α = α := by
  have h := properChowPushforward_id C sZ k
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sZ sZ (𝟙 Z)
      (Category.id_comp sZ) k)
  exact congrFun (congrArg DFunLike.coe h) α

/-- Pushforward on Chow groups along isomorphisms over the base is functorial: the
isomorphism case of the functoriality of proper pushforward. -/
theorem chowPushforwardOfIso_comp_apply {Z Z' Z'' : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (sZ'' : Z'' ⟶ C.S)
    [LocallyOfFiniteType sZ''] (u : Z ⟶ Z') [IsIso u] (v : Z' ⟶ Z'') [IsIso v]
    (hu : u ≫ sZ' = sZ) (hv : v ≫ sZ'' = sZ') (k : ℤ) (α : chowGroup C sZ k) :
    chowPushforwardOfIso C sZ' sZ'' v hv k (chowPushforwardOfIso C sZ sZ' u hu k α) =
      chowPushforwardOfIso C sZ sZ'' (u ≫ v) (by rw [Category.assoc, hv, hu]) k α := by
  have h := properChowPushforward_comp C sZ sZ' sZ'' u v hu hv k
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sZ sZ' u hu k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sZ' sZ'' v hv k)
  exact congrFun (congrArg DFunLike.coe h) α

/-- Pushforwards on Chow groups along two equal isomorphisms over the base agree. -/
theorem chowPushforwardOfIso_congr_apply {Z Z' : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (u v : Z ⟶ Z') [IsIso u]
    [IsIso v] (huv : u = v) (hu : u ≫ sZ' = sZ) (hv : v ≫ sZ' = sZ) (k : ℤ)
    (α : chowGroup C sZ k) :
    chowPushforwardOfIso C sZ sZ' u hu k α = chowPushforwardOfIso C sZ sZ' v hv k α := by
  subst huv
  rfl

/-- The cap operations of a bivariant class at two equal test morphisms are carried to one
another by the pushforward along the comparison isomorphism of the two base changes. -/
theorem chowPushforwardOfIso_congrHom_cap (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    {g₁ g₂ : T ⟶ Y} [LocallyOfFiniteType g₁] [LocallyOfFiniteType g₂] (e : g₁ = g₂)
    (hbase : (pullback.congrHom (rfl : f = f) e).hom ≫ (pullback.fst f g₂ ≫ sX) =
      pullback.fst f g₁ ≫ sX)
    (k : ℤ) {q : T ⟶ C.S} [LocallyOfFiniteType q] (α : chowGroup C q k) (h₁ : q = g₁ ≫ sY)
    (h₂ : q = g₂ ≫ sY) :
    chowPushforwardOfIso C (pullback.fst f g₁ ≫ sX) (pullback.fst f g₂ ≫ sX)
        (pullback.congrHom rfl e).hom hbase (k - p)
        (c.cap g₁ k (chowGroupCongr C h₁ k α)) =
      c.cap g₂ k (chowGroupCongr C h₂ k α) := by
  cases e
  rw [chowPushforwardOfIso_congr_apply C (pullback.fst f g₁ ≫ sX) (pullback.fst f g₁ ≫ sX)
    (pullback.congrHom rfl rfl).hom (𝟙 _) (by simp) hbase (Category.id_comp _) (k - p),
    chowPushforwardOfIso_id]

/-! ### Compatibility with composition of base changes -/

section Composition

variable {Y'' : Scheme.{u}} (h' : Y'' ⟶ Y') [LocallyOfFiniteType h']

/-- The comparison isomorphism of the two iterated base changes of `f : X ⟶ Y` over a test scheme
`g : T ⟶ Y''`: restricting along `h : Y' ⟶ Y` and then along `h' : Y'' ⟶ Y'` produces the same
fibre product as restricting along `h' ≫ h`. -/
def iteratedRestrictionIso {T : Scheme.{u}} (g : T ⟶ Y'') :
    pullback (pullback.snd (pullback.snd f h) h') g ≅ pullback (pullback.snd f (h' ≫ h)) g :=
  (pullbackLeftPullbackSndIso (pullback.snd f h) h' g).trans
    ((pullbackLeftPullbackSndIso f h (g ≫ h')).trans
      ((pullback.congrHom rfl (Category.assoc g h' h)).trans
        (pullbackLeftPullbackSndIso f (h' ≫ h) g).symm))

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [LocallyOfFiniteType h]
  [LocallyOfFiniteType h'] in
/-- The comparison isomorphism of the two iterated base changes is compatible with the structure
morphisms over the base. -/
theorem iteratedRestrictionIso_hom_comp {T : Scheme.{u}} (g : T ⟶ Y'') :
    (iteratedRestrictionIso f h h' g).hom ≫
        (pullback.fst (pullback.snd f (h' ≫ h)) g ≫ (pullback.fst f (h' ≫ h) ≫ sX)) =
      pullback.fst (pullback.snd (pullback.snd f h) h') g ≫
        (pullback.fst (pullback.snd f h) h' ≫ (pullback.fst f h ≫ sX)) := by
  simp [iteratedRestrictionIso]

/-- **Stacks 0F9Z.** Restriction of a bivariant class is compatible with composition of base
changes: if `c'` is the restriction of `c` along `h`, then the restriction of `c'` along `h'` caps
exactly as the restriction of `c` along `h' ≫ h`, after the canonical identification of the two
iterated fibre products. -/
@[stacks 0F9Z "compatibility with compositions, on cap operations"]
theorem bivariantRestrictionCap_comp (c : BivariantClass C G sX sY f hf p)
    (c' : BivariantClass C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p)
    (hc' : IsBivariantRestriction C G sX sY f hf h p c c') {T : Scheme.{u}} (g : T ⟶ Y'')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (h' ≫ (h ≫ sY))) k) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.snd (pullback.snd f h) h') g ≫
          (pullback.fst (pullback.snd f h) h' ≫ (pullback.fst f h ≫ sX)))
        (pullback.fst (pullback.snd f (h' ≫ h)) g ≫ (pullback.fst f (h' ≫ h) ≫ sX))
        (iteratedRestrictionIso f h h' g).hom
        (iteratedRestrictionIso_hom_comp C sX f h h' g) (k - p)
        (bivariantRestrictionCap C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) h' p c' g k α) =
      bivariantRestrictionCap C G sX sY f hf (h' ≫ h) p c g k
        (chowGroupCongr C (congrArg (g ≫ ·) (Category.assoc h' h sY).symm) k α) := by
  simp only [bivariantRestrictionCap_apply]
  rw [hc' (g ≫ h') k (chowGroupCongr C (Category.assoc g h' (h ≫ sY)).symm k α)]
  simp only [bivariantRestrictionCap_apply, chowGroupCongr_chowGroupCongr]
  rw [chowPushforwardOfIso_comp_apply C _ _ _ (pullbackLeftPullbackSndIso f h (g ≫ h')).inv
      (pullbackLeftPullbackSndIso (pullback.snd f h) h' g).inv,
    chowPushforwardOfIso_comp_apply C _ _ _
      ((pullbackLeftPullbackSndIso f h (g ≫ h')).inv ≫
        (pullbackLeftPullbackSndIso (pullback.snd f h) h' g).inv)
      (iteratedRestrictionIso f h h' g).hom,
    ← chowPushforwardOfIso_congrHom_cap C G sX sY f hf p c (Category.assoc g h' h)
      (by simp) k α (by simp) (by simp),
    chowPushforwardOfIso_comp_apply C _ _ _
      (pullback.congrHom (rfl : f = f) (Category.assoc g h' h)).hom
      (pullbackLeftPullbackSndIso f (h' ≫ h) g).inv]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _
    (by simp [iteratedRestrictionIso]) _ _ (k - p) _


/-- **Stacks 0F9Z.** Restriction is compatible with composition of base changes: restricting
along `h` and then along `h'` agrees with restricting along `h' ≫ h`, after the canonical
identification of the two iterated fibre products. -/
@[stacks 0F9Z]
theorem bivariantRestriction_comp (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y'')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (h' ≫ (h ≫ sY))) k) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.snd (pullback.snd f h) h') g ≫
          (pullback.fst (pullback.snd f h) h' ≫ (pullback.fst f h ≫ sX)))
        (pullback.fst (pullback.snd f (h' ≫ h)) g ≫ (pullback.fst f (h' ≫ h) ≫ sX))
        (iteratedRestrictionIso f h h' g).hom
        (iteratedRestrictionIso_hom_comp C sX f h h' g) (k - p)
        ((bivariantRestriction C G (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) h' p hgys
          (bivariantRestriction C G sX sY f hf h p hgys c)).cap g k α) =
      (bivariantRestriction C G sX sY f hf (h' ≫ h) p hgys c).cap g k
        (chowGroupCongr C (congrArg (g ≫ ·) (Category.assoc h' h sY).symm) k α) := by
  rw [bivariantRestriction_cap, bivariantRestriction_cap]
  exact bivariantRestrictionCap_comp C G sX sY f hf h p h' c
    (bivariantRestriction C G sX sY f hf h p hgys c)
    (isBivariantRestriction_bivariantRestriction C G sX sY f hf h p hgys c) g k α

end Composition

end Stacks.Chow

end
