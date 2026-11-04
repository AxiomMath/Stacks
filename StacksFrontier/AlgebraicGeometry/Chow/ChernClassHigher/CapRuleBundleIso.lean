module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapRuleIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange

/-!
# The relation of Stacks 02U6 along an isomorphism of projective bundles

`Stacks.Chow.ChernCapPresentation` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapRuleIsoInvariance` reads the relation of
Stacks 02U6 at a projective bundle over a test scheme, and
`Stacks.Chow.HigherChernCapRule.respectsIso_of_hasCommonPresentation` derives the iso-invariance
of a Chern cap rule from the rule solving that relation at a presentation serving two isomorphic
modules at once. That one presentation serves both is the formal shadow of a geometric fact: the
projective bundles `P(ℰ)` and `P(ℰ')` of two isomorphic modules are isomorphic over the base, by
an isomorphism carrying `O(1)` to `O(1)`.

This file removes the need to identify the two presentations. It transports the relation of
Stacks 02U6 along an isomorphism of bundles over a fixed test scheme whose twists correspond, so
that a cap rule solving the relation at a presentation of `ℰ` solves it at any isomorphic
presentation, and in particular at the one of `ℰ'`.

The transport is the operation argument of
`Stacks.Chow.operation_isChernCapFamily` at the *identity* of the test scheme: only the bundle
moves. So there is no change of degree anywhere, the family of classes on the test scheme is
literally unchanged, and the whole content is that pushforward along the bundle isomorphism
carries each summand `c₁(O_P(1))^i ∩ π^*(-)` of the relation to the corresponding summand for the
other bundle. That is the flat-pullback half of Stacks 02RG for two isomorphism legs, which
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso` supplies, together with the correspondence of
the two twists.

## Main definitions

* `Stacks.Chow.ChernCapOperator.CorrespondsUnder` — that two first Chern class cap operators
  correspond under an isomorphism over the base: pushforward along it intertwines the two cap
  operations. For the projective bundles of two isomorphic modules this is the statement that the
  isomorphism carries `O(1)` to `O(1)`.
* `Stacks.Chow.ChernCapPresentation.IsoOver` — an isomorphism of presentations over a test
  scheme: an isomorphism of bundles commuting with the projections whose twists correspond.
* `Stacks.Chow.HigherChernCapRule.HasIsomorphicPresentations` — that any two isomorphic modules
  of rank `r` admit presentations, isomorphic over the test scheme, at which the rule solves the
  relation of Stacks 02U6.

## Main results

* `Stacks.Chow.ChernCapPresentation.solves_of_isoOver` — a cap rule solving the relation of
  Stacks 02U6 at a presentation solves it at any isomorphic presentation.
* `Stacks.Chow.HigherChernCapRule.respectsIso_of_hasIsomorphicPresentations` —
  **`Stacks.Chow.HigherChernCapRule.RespectsIso` from the relation of Stacks 02U6 at merely
  isomorphic presentations.** This is
  `Stacks.Chow.HigherChernCapRule.respectsIso_of_hasCommonPresentation` with the common
  presentation weakened to two isomorphic ones, which is what the geometry provides.

## Implementation notes

The correspondence of the two twists is a hypothesis, and must be: a
`Stacks.Chow.ChernCapOperator` is bare data in this repository and no declaration relates two of
them, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass` record. It
is the only hypothesis of the transport that is not available, and it is the Chow-theoretic shadow
of `O(1)` being carried to `O(1)`.

The relation is transported by applying the pushforward along the bundle isomorphism to it, which
is injective by `Stacks.Chow.chowPushforwardOfIso_injective`, though injectivity is not needed:
the direction used is the one that produces the new relation from the old. Every equality below
is in a Chow group of a bundle in a fixed degree, and the only degree transports are the
`Stacks.Chow.chowGroupCast` already present in the summands of the relation.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U1](https://stacks.math.columbia.edu/tag/02U1)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Corresponding first Chern class cap operators -/

section Operator

variable {C : ChowSituation.{u}} {A B : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
  {sB : B ⟶ C.S} [LocallyOfFiniteType sB]

/-- That two first Chern class cap operators **correspond** under an isomorphism `e : A ≅ B` over
the base of the Chow situation: pushforward along `e` intertwines the two cap operations
`A_{m+1} ⟶ A_m`.

For the projective bundles of two isomorphic finite locally free modules, with `e` the induced
isomorphism, this is the statement that `e` carries `O(1)` to `O(1)`. -/
def ChernCapOperator.CorrespondsUnder (O : ChernCapOperator C sA) (O' : ChernCapOperator C sB)
    (e : A ≅ B) (he : e.hom ≫ sB = sA) : Prop :=
  ∀ (m : ℤ) (x : chowGroup C sA (m + 1)),
    chowPushforwardOfIso C sA sB e.hom he m (O.capOnChow C sA m x) =
      O'.capOnChow C sB m (chowPushforwardOfIso C sA sB e.hom he (m + 1) x)

/-- The iterated cap products of two corresponding first Chern class cap operators correspond:
pushforward along the isomorphism carries `c₁(O_A(1))^i ∩ -` to `c₁(O_B(1))^i ∩ -`. -/
theorem chernCapIterate_chowPushforwardOfIso {O : ChernCapOperator C sA}
    {O' : ChernCapOperator C sB} {e : A ≅ B} {he : e.hom ≫ sB = sA}
    (hOO' : O.CorrespondsUnder O' e he) :
    ∀ (i : ℕ) (k : ℤ) (x : chowGroup C sA (k + (i : ℤ))),
      chowPushforwardOfIso C sA sB e.hom he k (chernCapIterate C sA O i k x) =
        chernCapIterate C sB O' i k
          (chowPushforwardOfIso C sA sB e.hom he (k + (i : ℤ)) x) := by
  intro i
  induction i with
  | zero =>
    intro k x
    rw [chernCapIterate_zero_apply, chernCapIterate_zero_apply,
      ← chowPushforwardOfIso_chowGroupCast]
  | succ i ih =>
    intro k x
    rw [chernCapIterate_succ_apply, chernCapIterate_succ_apply, hOO', ih,
      ← chowPushforwardOfIso_chowGroupCast]

end Operator

/-! ### Isomorphisms of presentations -/

section Presentation

variable {C : ChowSituation.{u}} {r : ℕ} {T : Scheme.{u}} {q : T ⟶ C.S}
  [LocallyOfFiniteType q]

/-- A morphism of bundles commuting with the projections lies over the base of the Chow
situation. -/
theorem ChernCapPresentation.hom_comp_str (p p' : ChernCapPresentation C r q)
    (u : p.bundle ⟶ p'.bundle) (hu : p.proj = u ≫ p'.proj) : u ≫ p'.str = p.str := by
  rw [← p.comp, hu, ← p'.comp, Category.assoc]

/-- An **isomorphism of presentations** over the test scheme: an isomorphism of the two bundles
commuting with their projections, whose twists correspond.

This is what the projective bundles of two isomorphic modules provide. -/
structure ChernCapPresentation.IsoOver (p p' : ChernCapPresentation C r q) where
  /-- The isomorphism of bundles. -/
  bundleIso : p.bundle ≅ p'.bundle
  /-- It commutes with the projections to the test scheme. -/
  comp_proj : p.proj = bundleIso.hom ≫ p'.proj
  /-- The two twists correspond under it. -/
  twistCorrespondsUnder : p.twist.CorrespondsUnder p'.twist bundleIso
    (ChernCapPresentation.hom_comp_str p p' bundleIso.hom comp_proj)

variable {p p' : ChernCapPresentation C r q}

/-- Every presentation is isomorphic over the test scheme to itself, by the identity: pushforward
along the identity is the identity, so the twists correspond. -/
def ChernCapPresentation.isoOverSelf (p : ChernCapPresentation C r q) : p.IsoOver p where
  bundleIso := Iso.refl p.bundle
  comp_proj := by simp
  twistCorrespondsUnder := by
    have hid : ∀ (n : ℤ) (y : chowGroup C p.str n),
        chowPushforwardOfIso C p.str p.str (Iso.refl p.bundle).hom
          (ChernCapPresentation.hom_comp_str p p (Iso.refl p.bundle).hom (by simp)) n y = y :=
      fun n y ↦ chowPushforwardOfIso_id C p.str n y
    intro m x
    rw [hid, hid]

/-- The flat pullback along the projection of the bundle, pushed forward along an isomorphism of
presentations, is the flat pullback along the projection of the other bundle. This is the case of
Stacks 02RG with two isomorphism legs, one of them the identity of the test scheme. -/
theorem ChernCapPresentation.IsoOver.projectiveBundlePullback (u : p.IsoOver p') (m : ℤ)
    (x : chowGroup C q m) :
    chowPushforwardOfIso C p.str p'.str u.bundleIso.hom
        (ChernCapPresentation.hom_comp_str p p' u.bundleIso.hom u.comp_proj)
        (m + ((r - 1 : ℕ) : ℤ))
        (Stacks.Chow.projectiveBundlePullback C q p.str p.proj p.comp r p.relativeDimension
          p.factors m x) =
      Stacks.Chow.projectiveBundlePullback C q p'.str p'.proj p'.comp r p'.relativeDimension
        p'.factors m x := by
  have h := flatPullbackChow_chowPushforwardOfIso C q p.str q p'.str (𝟙 T) (Category.id_comp q)
    u.bundleIso.hom (ChernCapPresentation.hom_comp_str p p' u.bundleIso.hom u.comp_proj)
    p.proj p.comp p'.proj p'.comp
    (show p.proj ≫ 𝟙 T = u.bundleIso.hom ≫ p'.proj by rw [Category.comp_id, u.comp_proj])
    (r - 1) p.relativeDimension p'.relativeDimension m (p.factors m) (p'.factors m) x
  rw [chowPushforwardOfIso_id] at h
  exact h.symm

/-- Pushforward along an isomorphism of presentations carries the `i`-th summand
`c₁(O_P(1))^i ∩ π^*(-)` of the relation of Stacks 02U6 to the `i`-th summand for the other
bundle, at the **same** class on the test scheme. -/
theorem ChernCapPresentation.IsoOver.projectiveBundleChernTerm (u : p.IsoOver p') (k : ℤ)
    (i : ℕ) (hi : i ≤ r) (x : chowGroup C q (k - ((r - i : ℕ) : ℤ))) :
    chowPushforwardOfIso C p.str p'.str u.bundleIso.hom
        (ChernCapPresentation.hom_comp_str p p' u.bundleIso.hom u.comp_proj)
        (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
        (Stacks.Chow.projectiveBundleChernTerm C q p.str p.proj p.comp r p.relativeDimension
          p.factors p.twist k i hi x) =
      Stacks.Chow.projectiveBundleChernTerm C q p'.str p'.proj p'.comp r p'.relativeDimension
        p'.factors p'.twist k i hi x := by
  rw [projectiveBundleChernTerm_eq_chernCapIterate, projectiveBundleChernTerm_eq_chernCapIterate,
    chernCapIterate_chowPushforwardOfIso u.twistCorrespondsUnder,
    ← chowPushforwardOfIso_chowGroupCast, u.projectiveBundlePullback]

/-- The relation of Stacks 02U6 transports along an isomorphism of presentations, at the same
family of classes on the test scheme. -/
theorem ChernCapPresentation.IsoOver.projectiveBundleChernRelation (u : p.IsoOver p') (k : ℤ)
    (d : ∀ j : Fin (r + 1), chowGroup C q (k - (j : ℤ)))
    (hd : ProjectiveBundleChernRelation C q p.str p.proj p.comp r p.relativeDimension p.factors
      p.twist k d) :
    ProjectiveBundleChernRelation C q p'.str p'.proj p'.comp r p'.relativeDimension p'.factors
      p'.twist k d := by
  have h := congrArg (chowPushforwardOfIso C p.str p'.str u.bundleIso.hom
    (ChernCapPresentation.hom_comp_str p p' u.bundleIso.hom u.comp_proj)
    (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))) hd
  simp only [map_sum, map_zsmul, map_zero, u.projectiveBundleChernTerm] at h
  exact h

/-- The characterization of Stacks 02U6 transports along an isomorphism of presentations: the
condition on the zeroth member does not mention the bundle, and the relation transports. -/
theorem ChernCapPresentation.IsoOver.isChernCapFamily (u : p.IsoOver p') (k : ℤ)
    (α : chowGroup C q k) (d : ∀ j : Fin (r + 1), chowGroup C q (k - (j : ℤ)))
    (hd : IsChernCapFamily C q p.str p.proj p.comp r p.relativeDimension p.factors p.twist k α
      d) :
    IsChernCapFamily C q p'.str p'.proj p'.comp r p'.relativeDimension p'.factors p'.twist k α
      d :=
  ⟨hd.1, u.projectiveBundleChernRelation k d hd.2⟩

/-- **A cap rule solving the relation of Stacks 02U6 at a presentation solves it at any
isomorphic presentation.** -/
theorem ChernCapPresentation.solves_of_isoOver (u : p.IsoOver p')
    {cap : HigherChernCapRule C r} {F : T.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (hF : p.Solves cap F) : p'.Solves cap F := fun k α ↦
  u.isChernCapFamily k α _ (hF k α)

end Presentation

/-! ### Iso-invariance from isomorphic presentations -/

/-- That any two **isomorphic** modules of rank `r` on a test scheme admit presentations,
isomorphic over that scheme, at which the cap rule solves the relation of Stacks 02U6.

This is the source's situation with nothing identified by hand: `P(ℰ)` and `P(ℰ')` are two
bundles, isomorphic over `T` by an isomorphism carrying `O(1)` to `O(1)`, and the rule solves the
relation at each — which is Stacks 02U0, the definition of the cap product. It is weaker than
`Stacks.Chow.HigherChernCapRule.HasCommonPresentation`, which is the case of one presentation and
the identity isomorphism. -/
def HigherChernCapRule.HasIsomorphicPresentations (C : ChowSituation.{u}) (r : ℕ)
    (cap : HigherChernCapRule C r) : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F F' : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r],
    (F ≅ F') → ∃ (p p' : ChernCapPresentation C r q) (_ : p.IsoOver p'),
      p.Solves cap F ∧ p'.Solves cap F'

/-- A common presentation is a pair of isomorphic ones, by the identity isomorphism. This is why
`Stacks.Chow.HigherChernCapRule.HasIsomorphicPresentations` is the weaker hypothesis. -/
theorem HigherChernCapRule.hasIsomorphicPresentations_of_hasCommonPresentation
    {C : ChowSituation.{u}} {r : ℕ} {cap : HigherChernCapRule C r}
    (h : HigherChernCapRule.HasCommonPresentation C r cap) :
    HigherChernCapRule.HasIsomorphicPresentations C r cap := by
  intro T q _ F F' _ _ e
  obtain ⟨p, hF, hF'⟩ := h q F F' e
  exact ⟨p, p, p.isoOverSelf, hF, hF'⟩

/-- **Iso-invariance of the Chern cap rule from the relation of Stacks 02U6 at isomorphic
presentations.** A `Stacks.Chow.HigherChernCapRule` which solves the relation of Stacks 02U6 at
presentations of two isomorphic modules that are themselves isomorphic over the test scheme takes
equal values at the two modules — that is, it satisfies
`Stacks.Chow.HigherChernCapRule.RespectsIso`.

This is `Stacks.Chow.HigherChernCapRule.respectsIso_of_hasCommonPresentation` with the two
presentations no longer required to be the same one: the isomorphism of bundles, carrying `O(1)`
to `O(1)`, is what the projective bundles of two isomorphic modules provide, and the relation of
Stacks 02U6 transports along it. It remains a reduction and not a discharge — a
`Stacks.Chow.HigherChernCapRule` is unconstrained data, and no declaration of this repository
relates one to the families of Stacks 02U6. -/
theorem HigherChernCapRule.respectsIso_of_hasIsomorphicPresentations {C : ChowSituation.{u}}
    {r : ℕ} {cap : HigherChernCapRule C r}
    (h : HigherChernCapRule.HasIsomorphicPresentations C r cap) :
    HigherChernCapRule.RespectsIso C r cap := by
  intro T q _ F F' _ _ e k j
  obtain ⟨p, p', u, hF, hF'⟩ := h q F F' e
  exact p'.cap_eq_of_solves (p.solves_of_isoOver u hF) hF' k j

end Stacks.Chow

end
