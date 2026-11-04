module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepBranch
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingUnitsSequence
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingUnitsSequence
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian

/-!
# The squishing half of the one-step classification of [Stacks, Tag 0C1L]

This file proves `Stacks.GlueSquishFactor.IsSquishingProducer`, the one statement which
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepBranch` left standing
between this tree and [Stacks, Tag 0C1L]: the `DualNumber k` twin of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod`. With it the
lemma is unconditional, and `Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain` is it.

## Main definitions

* `Stacks.GlueSquishFactor.epsilonCoefficientSheafHom` is the quotient map
  `f_*𝒪_{X'} ⟶ (k, +)_x` of the sequence of [Stacks, Tag 0C1K]: the coefficient of `ε` along a
  tangent vector, assembled from the stalk at the contracted point across the stalk-skyscraper
  adjunction.

## Main results

* `Stacks.GlueSquishFactor.epsilonCoefficientSheafHom_app` — that quotient map **is** the
  `ε`-coefficient on the sections over every neighbourhood of the contracted point, which is the
  clause of `AlgebraicGeometry.IsSquishingTangentVector` pinning it down.
* `Stacks.GlueSquishFactor.shortExact_epsilonCoefficient` — **the short exact sequence**
  `0 → 𝒪_X → f_*𝒪_{X'} → (k, +)_x → 0`.
* `Stacks.GlueSquishFactor.isClosedImmersion_pointOfStalkHom` — **the tangent vector is a closed
  immersion**.
* `Stacks.GlueSquishFactor.isSquishingTangentVector_pointOfStalkHom` and
  `Stacks.GlueSquishFactor.isSquishingProducer` — `IsSquishingProducer` in full.
* `Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain` — **[Stacks, Tag 0C1L]**.

## Implementation notes

The squishing side is **not** a transcription of the glueing side.
`AlgebraicGeometry.IsGlueingTwoPoints` states its short exact sequence in germ-local form, so on
that side the stalk-level clauses of the fibre sequence are its conclusion verbatim;
`AlgebraicGeometry.IsSquishingTangentVector` asks instead for an honest
`CategoryTheory.ShortComplex.ShortExact` in the category of sheaves of abelian groups on `X`, for
an existentially quantified but value-pinned map into `AlgebraicGeometry.skyscraperAddSheaf`, and
for `IsClosedImmersion θ`, which has no counterpart on the glueing side at all. So three things
are built here and nothing is transported.

* *The map.* It is produced from the stalk at the contracted point by
  `StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf`, the stalk map being
  `CategoryTheory.Limits.colimit.desc` of the cocone of `ε`-coefficients
  (`Stacks.GlueSquishFactor.epsilonCoefficientCocone`); the `ε`-coefficient is additive because
  it is the `ε`-part of a ring homomorphism. This is the construction
  `Stacks.SquishSheafSequence.epsilonLogDerivSheafHom` performs for the units sequence of
  Tag 0C1N, and its description on sections is read off
  `StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk` in the same way.
* *Exactness.* `TopCat.Sheaf.shortExact_of_local` reduces it to three germ-local conditions on
  sections, which is the right reduction here and not `TopCat.Sheaf.shortExact_of_stalk`: the
  sections of these additive sheaves are the sections of the sheaves of rings on the nose, so no
  stalk of `f_*𝒪_{X'}` in `AddCommGrpCat` ever has to be compared with the stalk in
  `CommRingCat`. Each condition splits by whether the point is the contracted one: there the
  stalk-level clauses `Stacks.GlueSquishFactor.exists_algebraMap_eq_of_dualNumber_snd_eq_zero`
  and `Stacks.GlueSquishFactor.exists_dualNumber_snd_eq` apply, carried to the germs by
  `Stacks.GlueSquishFactor.epsilonCoefficientAt_pointOfStalkHom` and
  `Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range`; elsewhere `f` is an isomorphism on a
  neighbourhood and the skyscraper has no sections.
* *The closed immersion.* `Spec k[ε]` is a one-point scheme
  (`Stacks.GlueSquishFactor.subsingleton_spec_dualNumber`), so by
  `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion` only two things are needed. Being a
  preimmersion is formal: `Spec χ` is a closed immersion because `χ` is surjective, and
  `Stacks.GlueSquishFactor.fromSpecPushforwardStalk` is a preimmersion because the germ map
  presents the stalk as a localisation
  (`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`) and
  `AlgebraicGeometry.IsAffineOpen.fromSpec` is an open immersion. Closedness of the image comes
  from the `k`-rational point `Spec k[ε] ⟶ X'` precomposed with `Spec` of `k[ε] ⟶ k`: it is a
  section of the structure morphism, hence a closed immersion by
  `AlgebraicGeometry.isClosedImmersion_of_comp_eq_id`, and its range is the one point. In
  particular **no** surjectivity on sections over a small affine open is needed, contrary to what
  the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.MinimalStep` used to predict.

The germ dictionary of `MinimalStep` is used at the target `DualNumber k` rather than `k`, which
is why `Stacks.GlueSquishFactor.germ_stalkClosedPointTo_pointOfStalkHom_of_mem` and
`AlgebraicGeometry.germ_stalkClosedPointTo_appLE` are stated there for an arbitrary local ring.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1K](https://stacks.math.columbia.edu/tag/0C1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SquishSheafSequence

universe u

namespace Stacks.GlueSquishFactor

/-! ### The `ε`-coefficient as a map of additive groups -/

/-- The `ε`-coefficient along a tangent vector is unchanged by restricting a section to a
smaller open set still containing the contracted point. -/
theorem epsilonCoefficientAt_res {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (hV : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ V) (s : Γ(X, U)) :
    epsilonCoefficientAt θ V hV ((X.presheaf.map (homOfLE hVU).op).hom s) =
      epsilonCoefficientAt θ U (hVU hV) s :=
  congrArg TrivSqZeroExt.snd (sectionsToDualNumber_res θ hVU hV s)

/-- The `ε`-coefficient along a tangent vector, as a homomorphism of additive groups: it is the
`ε`-part of a ring homomorphism. -/
def epsilonCoefficientAddHom {k : Type u} [Field k] {X : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X) (U : X.Opens)
    (hθ : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) : Γ(X, U) →+ k where
  toFun := epsilonCoefficientAt θ U hθ
  map_zero' := by
    change (sectionsToDualNumber θ U hθ 0).snd = 0
    rw [map_zero, TrivSqZeroExt.snd_zero]
  map_add' s t := by
    change (sectionsToDualNumber θ U hθ (s + t)).snd = _
    rw [map_add, TrivSqZeroExt.snd_add]
    rfl

/-! ### The quotient map of the sequence of [Stacks, Tag 0C1K] -/

/-- The `ε`-coefficient on the neighbourhoods of the contracted point, as a cocone on the
diagram computing the stalk of `f_*𝒪_{X'}` there. -/
def epsilonCoefficientCocone {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') :
    Cocone ((OpenNhds.inclusion
        (f.base (θ.base (IsLocalRing.closedPoint (DualNumber k))))).op ⋙
      (pushforwardAddSheaf f).presheaf) := by
  refine ⟨AddCommGrpCat.of k, ?_, ?_⟩
  · intro U
    exact AddCommGrpCat.ofHom (epsilonCoefficientAddHom θ (f ⁻¹ᵁ U.unop.1) (by
      change f.base (θ.base (IsLocalRing.closedPoint (DualNumber k))) ∈ U.unop.1
      exact U.unop.2))
  · intro U V inc
    have hVU : V.unop.1 ≤ U.unop.1 := inc.unop.le
    have hpre : f ⁻¹ᵁ V.unop.1 ≤ f ⁻¹ᵁ U.unop.1 := fun z hz => hVU hz
    have hpt : θ.base (IsLocalRing.closedPoint (DualNumber k)) ∈ f ⁻¹ᵁ V.unop.1 := V.unop.2
    ext s
    change epsilonCoefficientAt θ (f ⁻¹ᵁ V.unop.1) hpt
        ((X'.presheaf.map (homOfLE hpre).op).hom s) =
      epsilonCoefficientAt θ (f ⁻¹ᵁ U.unop.1) (hpre hpt) s
    exact epsilonCoefficientAt_res θ hpre hpt s

/-- The `ε`-coefficient on the stalk of `f_*𝒪_{X'}` at the contracted point. -/
def epsilonCoefficientStalkMap {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') :
    (pushforwardAddSheaf f).presheaf.stalk
        ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) ⟶ AddCommGrpCat.of k :=
  colimit.desc _ (epsilonCoefficientCocone f θ)

/-- The stalk `ε`-coefficient computes the `ε`-coefficient on germs. -/
theorem epsilonCoefficientStalkMap_germ {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') (U : X.Opens)
    (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (s : Γ(X', f ⁻¹ᵁ U)) :
    epsilonCoefficientStalkMap f θ
        ((pushforwardAddSheaf f).presheaf.germ U
          ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx s) =
      epsilonCoefficientAt θ (f ⁻¹ᵁ U) hx s := by
  let J := (OpenNhds.inclusion
    (f.base (θ.base (IsLocalRing.closedPoint (DualNumber k))))).op ⋙
      (pushforwardAddSheaf f).presheaf
  change ((colimit.ι J (op ⟨U, hx⟩) ≫ colimit.desc J (epsilonCoefficientCocone f θ)) s) = _
  rw [colimit.ι_desc]
  rfl

/-- **The quotient map `f_*𝒪_{X'} ⟶ (k, +)_x` of the sequence of [Stacks, Tag 0C1K]**: the
`ε`-coefficient along the squished tangent vector, transposed across the stalk-skyscraper
adjunction. -/
def epsilonCoefficientSheafHom {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') :
    pushforwardAddSheaf f ⟶ skyscraperAddSheaf (k := k) X
      ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) := by
  classical
  change pushforwardAddSheaf f ⟶
    skyscraperSheaf ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
      (AddCommGrpCat.of k)
  exact ⟨StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf _
    (epsilonCoefficientStalkMap f θ)⟩

/-- Composing the quotient map with the identification of the skyscraper's sections with the
ground field gives the germ followed by the stalk `ε`-coefficient. -/
private theorem epsilonCoefficientSheafHom_app_comp {k : Type u} [Field k] {X' X : Scheme.{u}}
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X') (U : X.Opens)
    (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) :
    (epsilonCoefficientSheafHom f θ).hom.app (op U) ≫
        eqToHom (skyscraperAddSheaf_obj_eq (k := k) X
          ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx) =
      (pushforwardAddSheaf f).presheaf.germ U _ hx ≫ epsilonCoefficientStalkMap f θ := by
  classical
  change (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
      ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
      (epsilonCoefficientStalkMap f θ)).app (op U) ≫ _ = _
  have h := StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk
    ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
      ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)))
      (epsilonCoefficientStalkMap f θ)) U hx
  rw [StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper] at h
  exact h.symm

/-- **The quotient map of the sequence of [Stacks, Tag 0C1K] is the `ε`-coefficient** on the
sections over every neighbourhood of the contracted point. This is the clause of
`AlgebraicGeometry.IsSquishingTangentVector` which pins the map down. -/
theorem epsilonCoefficientSheafHom_app {k : Type u} [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X') (U : X.Opens)
    (hx : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ U) (s : Γ(X', f ⁻¹ᵁ U)) :
    (epsilonCoefficientSheafHom f θ).hom.app (op U) s =
      skyscraperAddSheafMk X ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx
        (epsilonCoefficientAt θ (f ⁻¹ᵁ U) hx s) := by
  apply (ConcreteCategory.bijective_of_isIso
    (eqToHom (skyscraperAddSheaf_obj_eq (k := k) X
      ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx))).1
  refine Eq.trans ?_ (eqToHom_skyscraperAddSheafMk X _ hx
    (epsilonCoefficientAt θ (f ⁻¹ᵁ U) hx s)).symm
  refine ((CategoryTheory.comp_apply ((epsilonCoefficientSheafHom f θ).hom.app (op U))
      (eqToHom (skyscraperAddSheaf_obj_eq (k := k) X
        ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hx)) s).symm.trans
    (congrArg (fun m => (ConcreteCategory.hom m) s)
      (epsilonCoefficientSheafHom_app_comp f θ U hx))).trans ?_
  exact (CategoryTheory.comp_apply
    ((pushforwardAddSheaf f).presheaf.germ U _ hx) (epsilonCoefficientStalkMap f θ) s).trans
      (epsilonCoefficientStalkMap_germ f θ U hx s)

/-! ### The `ε`-coefficient at the tangent vector attached to a map out of the stalk -/

/-- **The stalk-to-germ dictionary for the `ε`-coefficient.** The `ε`-coefficient, at the
tangent vector `Stacks.GlueSquishFactor.pointOfStalkHom f hU hx χ`, of a section of `𝒪_{X'}`
over `f ⁻¹ᵁ W` is the `ε`-part of `χ` applied to its germ in `(f_*𝒪_{X'})_x`.

This is the `DualNumber k` analogue of `Stacks.GlueSquishFactor.sectionAt_pointOfStalkHom`, and
it is what carries the stalk-level clauses of the fibre sequence of a squishing to the sections
on which `AlgebraicGeometry.epsilonCoefficientAt` is defined. -/
theorem epsilonCoefficientAt_pointOfStalkHom {k : Type u} [Field k] {X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk x ⟶ CommRingCat.of (DualNumber k))
    {W : X.Opens} (hxW : x ∈ W) (s : Γ(X', f ⁻¹ᵁ W)) :
    epsilonCoefficientAt (pointOfStalkHom f hU hx χ) (f ⁻¹ᵁ W)
        (pointOfStalkHom_mem_preimage_of_mem f hU hx χ hxW
          (IsLocalRing.closedPoint (DualNumber k))) s =
      (χ.hom ((f.base _* X'.presheaf).germ W x hxW s)).snd :=
  congrArg TrivSqZeroExt.snd
    (ConcreteCategory.congr_hom (germ_stalkClosedPointTo_pointOfStalkHom_of_mem f hU hx χ hxW) s)

/-- **The `ε`-coefficient kills the sections pulled back from the base.** A germ at `x` is a
constant modulo the maximal ideal, and `χ` being a `k`-algebra map sends it to the corresponding
element of `k ⊆ k[ε]`, which has no `ε`-part. This is the stalk-level clause
`Stacks.GlueSquishFactor.dualNumber_snd_eq_zero_of_algebraMap` of the fibre sequence, read on
sections; it needs only that `χ` is defined over `k`, not minimality of the extension. -/
theorem epsilonCoefficientAt_app_eq_zero {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f] (x : Spec (.of k) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : basePoint x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of (DualNumber k))
    (hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k (DualNumber k)))
    {W : X.Opens} (hxW : basePoint x ∈ W) (t : Γ(X, W)) :
    epsilonCoefficientAt (pointOfStalkHom f hU hxU χ) (f ⁻¹ᵁ W)
        (pointOfStalkHom_mem_preimage_of_mem f hU hxU χ hxW
          (IsLocalRing.closedPoint (DualNumber k))) ((f.app W).hom t) = 0 := by
  rw [epsilonCoefficientAt_pointOfStalkHom f hU hxU χ hxW]
  have hgerm := ConcreteCategory.congr_hom (app_comp_germ_pushforward f W (basePoint x) hxW) t
  have hval := ConcreteCategory.congr_hom hχ (X.presheaf.germ W (basePoint x) hxW t)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hgerm hval
  rw [hgerm, hval]
  change (algebraMap k (DualNumber k) _).snd = 0
  rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

/-- The point of `X` to which the tangent vector attached to a `k`-algebra map out of the fibre
is contracted is the base point of `x`. -/
theorem pointOfStalkHom_comp_base {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f] (x : Spec (.of k) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : basePoint x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of (DualNumber k))
    (hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k (DualNumber k))) :
    (pointOfStalkHom f hU hxU χ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) =
      basePoint x := by
  refine (congrArg
    (fun g : Spec (.of (DualNumber k)) ⟶ X =>
      g.base (IsLocalRing.closedPoint (DualNumber k)))
    (pointOfStalkHom_comp f x hU hxU
      (CommRingCat.ofHom (algebraMap k (DualNumber k))) χ hχ)).trans ?_
  change x.base ((Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))).base _) = _
  exact congrArg x.base (Subsingleton.elim _ _)

/-! ### The short exact sequence of additive sheaves -/

/-- **The two maps of the sequence of [Stacks, Tag 0C1K] compose to zero.** Over an open
containing the contracted point this is
`Stacks.GlueSquishFactor.epsilonCoefficientAt_app_eq_zero`; over an open missing it the
skyscraper has no sections. -/
theorem comp_epsilonCoefficientSheafHom_eq_zero {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f] (x : Spec (.of k) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : basePoint x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of (DualNumber k))
    (hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k (DualNumber k))) :
    structureToPushforwardAddSheaf f ≫
        epsilonCoefficientSheafHom f (pointOfStalkHom f hU hxU χ) = 0 := by
  classical
  set θ := pointOfStalkHom f hU hxU χ with hθ
  apply Sheaf.hom_ext
  ext V t
  obtain ⟨V⟩ := V
  change X.Opens at V
  change (epsilonCoefficientSheafHom f θ).hom.app (op V) ((f.app V).hom t) = 0
  by_cases hz : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ V
  · rw [epsilonCoefficientSheafHom_app f θ V hz ((f.app V).hom t)]
    refine Eq.trans (congrArg
      (skyscraperAddSheafMk X ((θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))) hz) ?_)
      (skyscraperAddSheafMk_zero X _ hz)
    exact epsilonCoefficientAt_app_eq_zero f x hU hxU χ hχ
      (pointOfStalkHom_comp_base f x hU hxU χ hχ ▸ hz) t
  · exact skyscraperAddSheaf_eq_zero X _ V hz _

/-- **The short exact sequence of additive sheaves of a squishing.** Let `f : X' ⟶ X` be an
affine morphism of `k`-schemes which is an isomorphism away from the base point of a rational
point `x`, let `χ : (f_*𝒪_{X'})_x ⟶ k[ε]` be a `k`-algebra map out of the stalk, and suppose the
`ε`-part of `χ` has the image of `𝒪_{X, x}` as its kernel and all of `k` as its image. Then

`0 → 𝒪_X → f_*𝒪_{X'} → (k, +)_x → 0`

is short exact, the second map being the `ε`-coefficient along the tangent vector `χ` defines.

This is the clause of `AlgebraicGeometry.IsSquishingTangentVector` which has no counterpart on
the glueing side: `AlgebraicGeometry.IsGlueingTwoPoints` states its sequence in germ-local form,
whereas here an honest `CategoryTheory.ShortComplex.ShortExact` in the category of sheaves of
abelian groups on `X` is asked for. The three germ-local conditions of
`TopCat.Sheaf.shortExact_of_local` are what the hypotheses supply: injectivity of `f.app` is
`hinj`; exactness in the middle is `hker` at the point, carried to the germs by
`Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range`, and the surjectivity of `f.app` on
the isomorphism locus away from it; and surjectivity onto the skyscraper is `hsurj` at the
point, there being no section to hit away from it. -/
theorem shortExact_epsilonCoefficient {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X.Over (Spec (.of k))] (f : X' ⟶ X) [IsAffineHom f] (x : Spec (.of k) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : basePoint x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of (DualNumber k))
    (hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k (DualNumber k)))
    (hinj : ∀ W : X.Opens, Function.Injective (f.app W).hom)
    {W₀ : X.Opens} (hW₀ : (W₀ : Set X) = {basePoint x}ᶜ) [IsIso (f ∣_ W₀)]
    (hker : ∀ b : (f.base _* X'.presheaf).stalk (basePoint x), (χ.hom b).snd = 0 →
      ∃ a : X.presheaf.stalk (basePoint x),
        (stalkPushforwardMap f (basePoint x)).hom a = b)
    (hsurj : ∀ c : k, ∃ b : (f.base _* X'.presheaf).stalk (basePoint x), (χ.hom b).snd = c) :
    (ShortComplex.mk (structureToPushforwardAddSheaf f)
        (epsilonCoefficientSheafHom f (pointOfStalkHom f hU hxU χ))
        (comp_epsilonCoefficientSheafHom_eq_zero f x hU hxU χ hχ)).ShortExact := by
  classical
  set θ := pointOfStalkHom f hU hxU χ with hθdef
  have hpt : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) = basePoint x :=
    pointOfStalkHom_comp_base f x hU hxU χ hχ
  have hmemW₀ : ∀ y : X, y ∈ W₀ ↔ y ≠ basePoint x := by
    intro y
    change y ∈ (W₀ : Set X) ↔ _
    rw [hW₀]
    rfl
  have hnotW₀ : basePoint x ∉ W₀ := fun hy => (hmemW₀ _).1 hy rfl
  have hz : ∀ {V : X.Opens}, basePoint x ∈ V →
      (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∈ V := fun h => hpt ▸ h
  have hinf : ∀ {V : X.Opens} {y : X}, y ∈ V → y ≠ basePoint x → y ∈ V ⊓ W₀ :=
    fun hy hne => ⟨hy, (hmemW₀ _).2 hne⟩
  apply TopCat.Sheaf.shortExact_of_local
  · intro V t ht _ hy
    refine ⟨V, 𝟙 V, hy, ?_⟩
    have h0 : t = 0 := hinj V (show (f.app V).hom t = (f.app V).hom 0 from
      ht.trans (map_zero _).symm)
    rw [h0]
    exact map_zero _
  · intro V s hs y hy
    by_cases hyz : y = basePoint x
    · subst hyz
      have hzV := hz hy
      have hcoef : epsilonCoefficientAt θ (f ⁻¹ᵁ V) hzV s = 0 := by
        refine skyscraperAddSheafMk_injective X _ hzV ?_
        rw [← epsilonCoefficientSheafHom_app f θ V hzV s, skyscraperAddSheafMk_zero]
        exact hs
      have hsnd : (χ.hom ((f.base _* X'.presheaf).germ V (basePoint x) hy s)).snd = 0 := by
        rw [← epsilonCoefficientAt_pointOfStalkHom f hU hxU χ hy s]
        exact hcoef
      obtain ⟨V', hV'V, hyV', t, ht⟩ :=
        exists_app_eq_of_germ_mem_range f V hy s (hker _ hsnd)
      exact ⟨V', homOfLE hV'V, hyV', t, ht.symm⟩
    · have : IsIso (f.app (V ⊓ W₀)) :=
        isIso_app_of_isIso_morphismRestrict f W₀ (V ⊓ W₀) inf_le_right
      refine ⟨V ⊓ W₀, homOfLE inf_le_left, hinf hy hyz,
        CategoryTheory.inv (f.app (V ⊓ W₀))
          ((X'.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : V ⊓ W₀ ≤ V))).op).hom s), ?_⟩
      exact CategoryTheory.IsIso.inv_hom_id_apply (f.app (V ⊓ W₀)) _
  · intro V s y hy
    by_cases hyz : y = basePoint x
    · subst hyz
      have hzV := hz hy
      obtain ⟨b, hb⟩ := hsurj ((eqToHom (skyscraperAddSheaf_obj_eq (k := k) X _ hzV)) s)
      obtain ⟨W, hxW, s', hs'⟩ := (f.base _* X'.presheaf).exists_germ_eq b
      have hxVW : basePoint x ∈ V ⊓ W := ⟨hy, hxW⟩
      have hzVW := hz hxVW
      refine ⟨V ⊓ W, homOfLE inf_le_left, hxVW,
        (X'.presheaf.map
          (homOfLE (f.preimage_mono (inf_le_right : V ⊓ W ≤ W))).op).hom s', ?_⟩
      refine (ConcreteCategory.bijective_of_isIso
        (eqToHom (skyscraperAddSheaf_obj_eq (k := k) X _ hzVW))).1 ?_
      rw [epsilonCoefficientSheafHom_app f θ (V ⊓ W) hzVW, eqToHom_skyscraperAddSheafMk]
      have hres : epsilonCoefficientAt θ (f ⁻¹ᵁ (V ⊓ W)) hzVW
          ((X'.presheaf.map
            (homOfLE (f.preimage_mono (inf_le_right : V ⊓ W ≤ W))).op).hom s') =
          (χ.hom ((f.base _* X'.presheaf).germ W (basePoint x) hxW s')).snd :=
        (epsilonCoefficientAt_pointOfStalkHom f hU hxU χ hxVW _).trans
          (congrArg (fun c : (f.base _* X'.presheaf).stalk (basePoint x) => (χ.hom c).snd)
            (TopCat.Presheaf.germ_res_apply (f.base _* X'.presheaf)
              (homOfLE (inf_le_right : V ⊓ W ≤ W)) (basePoint x) hxVW s'))
      refine hres.trans ((congrArg (fun c : (f.base _* X'.presheaf).stalk (basePoint x) =>
        (χ.hom c).snd) hs').trans (hb.trans ?_))
      exact (congrArg (fun g : AddCommGrpCat.Hom _ _ => g.hom s)
        (Stacks.GlueSquishUnits.skyscraperPresheaf_map_comp _ (AddCommGrpCat.of k)
          (homOfLE (inf_le_left : V ⊓ W ≤ V)) hzVW)).symm
    · have hnot : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) ∉ V ⊓ W₀ :=
        fun hmem => hnotW₀ (hpt ▸ hmem.2)
      exact ⟨V ⊓ W₀, homOfLE inf_le_left, hinf hy hyz, 0,
        (map_zero _).trans (skyscraperAddSheaf_eq_zero X _ (V ⊓ W₀) hnot _).symm⟩

/-! ### The tangent vector is a closed immersion -/

/-- **`Spec k[ε]` is a one-point scheme.** Every prime of `k[ε]` is the maximal ideal: it is
contained in it because a prime is proper, and contains it because every element of it squares to
zero. -/
theorem subsingleton_spec_dualNumber (k : Type u) [Field k] :
    Subsingleton (Spec (.of (DualNumber k))) := by
  have key : ∀ p : PrimeSpectrum (DualNumber k),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber k) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top) fun y hy => ?_
    have hfst : y.fst = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal y).mp hy
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hne))
    have hsq : y ^ 2 = 0 := by
      rw [pow_two]
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [TrivSqZeroExt.fst_mul, hfst, mul_zero, TrivSqZeroExt.fst_zero]
      · rw [TrivSqZeroExt.snd_mul, hfst, TrivSqZeroExt.snd_zero, op_smul_eq_mul, smul_eq_mul,
          zero_mul, mul_zero, add_zero]
    exact p.2.mem_of_pow_mem 2 (hsq ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

/-- **The morphism out of `Spec (f_*𝒪_{X'})_x` is a preimmersion.** The germ map presents the
stalk of the pushforward as a localisation of the sections over `f ⁻¹ᵁ U`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`), so its spectrum is a
preimmersion, and `AlgebraicGeometry.IsAffineOpen.fromSpec` is an open immersion.

This is why no germ-level surjectivity is needed for the closed-immersion clause of
`AlgebraicGeometry.IsSquishingTangentVector`: only the image has to be shown closed. -/
theorem isPreimmersion_fromSpecPushforwardStalk {X' X : Scheme.{u}} (f : X' ⟶ X) [IsAffineHom f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    IsPreimmersion (fromSpecPushforwardStalk f hU hx) := by
  let : Algebra Γ(X, U) Γ(X', f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x) :=
    ((f.base _* X'.presheaf).germ U x hx).hom.toAlgebra
  have := hU.isLocalization_pushforwardStalk f hx
  have : IsPreimmersion (Spec.map ((f.base _* X'.presheaf).germ U x hx)) :=
    IsPreimmersion.of_isLocalization (S := (f.base _* X'.presheaf).stalk x)
      (Algebra.algebraMapSubmonoid Γ(X', f ⁻¹ᵁ U)
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
  rw [fromSpecPushforwardStalk]
  infer_instance

/-- **The tangent vector attached to a surjective map out of the stalk is a closed immersion.**
Its source is a one-point scheme, so being a closed immersion is being a preimmersion with
closed image; the first is
`Stacks.GlueSquishFactor.isPreimmersion_fromSpecPushforwardStalk` together with the surjectivity
of `χ`, and the second holds because the image point carries a `k`-rational point of `X'`, namely
the tangent vector composed with `Spec` of the projection `k[ε] ⟶ k`, and a section of a
morphism out of a one-point scheme is a closed immersion
(`AlgebraicGeometry.isClosedImmersion_of_comp_eq_id`). -/
theorem isClosedImmersion_pointOfStalkHom {k : Type u} [Field k] {X' X : Scheme.{u}}
    [X'.Over (Spec (.of k))] (f : X' ⟶ X)
    [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk x ⟶ CommRingCat.of (DualNumber k))
    (hsurj : Function.Surjective χ.hom)
    (hover : pointOfStalkHom f hU hx χ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k) :
    IsClosedImmersion (pointOfStalkHom f hU hx χ) := by
  have := subsingleton_spec_dualNumber k
  set θ := pointOfStalkHom f hU hx χ with hθdef
  have : IsPreimmersion θ := by
    rw [hθdef, pointOfStalkHom]
    have : IsClosedImmersion (Spec.map χ) := IsClosedImmersion.spec_of_surjective χ hsurj
    have := isPreimmersion_fromSpecPushforwardStalk f hU hx
    infer_instance
  refine IsClosedImmersion.of_isPreimmersion θ ?_
  set p : Spec (.of (DualNumber k)) := IsLocalRing.closedPoint (DualNumber k) with hp
  have hconst : ∀ t, θ.base t = θ.base p := fun t => congrArg θ.base (Subsingleton.elim t p)
  rw [Set.range_eq_singleton hconst]
  set ι : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom with hι
  have hidring : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫ ι =
      𝟙 (CommRingCat.of k) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    change (TrivSqZeroExt.fstHom k k k) (algebraMap k (DualNumber k) c) = c
    rw [(TrivSqZeroExt.fstHom k k k).commutes c]
    rfl
  have hsec : (Spec.map ι ≫ θ) ≫ (X' ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) := by
    rw [Category.assoc, hover, dualNumberToBase, ← Spec.map_comp, hidring, Spec.map_id]
  have := isClosedImmersion_of_comp_eq_id (X' ↘ Spec (.of k)) (Spec.map ι ≫ θ) hsec
  have hrange' : Set.range (Spec.map ι ≫ θ).base = {θ.base p} :=
    Set.range_eq_singleton fun t => hconst _
  exact hrange' ▸ (Spec.map ι ≫ θ).isClosedEmbedding.isClosed_range

/-! ### The squishing predicate in full -/

/-- **The squishing of a tangent vector, assembled.** Let `f` be a finite morphism of algebraic
`k`-schemes which is injective on structure sheaves and an isomorphism over the complement of the
base point of a rational point `x`, and let `χ : (f_*𝒪_{X'})_x ⟶ k[ε]` be a surjective
`k`-algebra map out of the stalk whose `ε`-part has the image of `𝒪_{X, x}` as its kernel and all
of `k` as its image. Then `f` squishes the tangent vector `χ` defines.

Every clause of `AlgebraicGeometry.IsSquishingTangentVector` is discharged here: the data and the
two equations by `Stacks.GlueSquishFactor.pointOfStalkHom_comp` and
`Stacks.GlueSquishFactor.comp_structureMorphism_of_comp_eq`, the closed immersion by
`Stacks.GlueSquishFactor.isClosedImmersion_pointOfStalkHom`, and the short exact sequence with
its `ε`-coefficient description by
`Stacks.GlueSquishFactor.shortExact_epsilonCoefficient` and
`Stacks.GlueSquishFactor.epsilonCoefficientSheafHom_app`. -/
theorem isSquishingTangentVector_pointOfStalkHom {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X)
    [IsFinite f] (hf : f.IsOver (Spec (.of k))) (x : Spec (.of k) ⟶ X)
    (hx : x.IsOver (Spec (.of k)))
    (hX'ft : LocallyOfFiniteType (X' ↘ Spec (.of k)))
    (hX'qc : QuasiCompact (X' ↘ Spec (.of k)))
    (hXft : LocallyOfFiniteType (X ↘ Spec (.of k)))
    (hXqc : QuasiCompact (X ↘ Spec (.of k)))
    (hinj : ∀ W : X.Opens, Function.Injective (f.app W).hom)
    {W₀ : X.Opens} (hW₀ : (W₀ : Set X) = {basePoint x}ᶜ) (hW₀iso : IsIso (f ∣_ W₀))
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : basePoint x ∈ U)
    (χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of (DualNumber k))
    (hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k (DualNumber k)))
    (hχsurj : Function.Surjective χ.hom)
    (hker : ∀ b : (f.base _* X'.presheaf).stalk (basePoint x), (χ.hom b).snd = 0 →
      ∃ a : X.presheaf.stalk (basePoint x),
        (stalkPushforwardMap f (basePoint x)).hom a = b)
    (hsurj : ∀ c : k, ∃ b : (f.base _* X'.presheaf).stalk (basePoint x), (χ.hom b).snd = c) :
    IsSquishingTangentVector f (pointOfStalkHom f hU hxU χ) := by
  have := hW₀iso
  set θ := pointOfStalkHom f hU hxU χ with hθdef
  have hcontract : θ ≫ f = dualNumberToBase k ≫ x :=
    pointOfStalkHom_comp f x hU hxU (CommRingCat.ofHom (algebraMap k (DualNumber k))) χ hχ
  have hover : θ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k :=
    comp_structureMorphism_of_comp_eq hf hx hcontract
  have hpt : (θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k)) = basePoint x :=
    pointOfStalkHom_comp_base f x hU hxU χ hχ
  refine ⟨hf, hX'ft, hX'qc, hXft, hXqc,
    isClosedImmersion_pointOfStalkHom f hU hxU χ hχsurj hover, hover, x, hx, hcontract,
    inferInstance, ⟨W₀, by rw [hW₀, hpt], hW₀iso⟩,
    epsilonCoefficientSheafHom f θ, comp_epsilonCoefficientSheafHom_eq_zero f x hU hxU χ hχ,
    shortExact_epsilonCoefficient f x hU hxU χ hχ hinj hW₀ hker hsurj, ?_⟩
  intro V hxV s
  exact epsilonCoefficientSheafHom_app f θ V hxV s

/-- **The squishing half of the one-step classification of [Stacks, Tag 0C1L]**, which
`Stacks.GlueSquishFactor.IsSquishingProducer` names: the `DualNumber k` twin of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod`.

The character `χ` is the one of
`Stacks.GlueSquishFactor.exists_tangentVector_of_fibre_algEquiv_dualNumber` — the quotient onto
the fibre followed by the given identification of it with `k[ε]` — so it is surjective, and the
two exactness inputs of the sheaf sequence are the stalk-level clauses
`Stacks.GlueSquishFactor.exists_algebraMap_eq_of_dualNumber_snd_eq_zero` and
`Stacks.GlueSquishFactor.exists_dualNumber_snd_eq`, which is where minimality of the stalk
extension is used. -/
theorem isSquishingProducer (k : Type u) [Field k] [IsAlgClosed k] : IsSquishingProducer k := by
  intro X' X _ _ f _ hf x hx hX'ft hX'qc hXft hXqc hmono hiso
  let : Algebra (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (basePoint x)) :=
    (stalkConstMap X (basePoint x)).hom.toAlgebra
  let : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    ((stalkPushforwardMap f (basePoint x)).hom.comp
      (stalkConstMap X (basePoint x)).hom).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite (X.presheaf.stalk (basePoint x))
      ((f.base _* X'.presheaf).stalk (basePoint x)) :=
    module_finite_stalk_pushforward f (basePoint x)
  intro hne hmin e
  obtain ⟨W₀, hW₀, hW₀iso⟩ := hiso
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show basePoint x ∈ (⊤ : X.Opens) from trivial)
  set χ : (f.base _* X'.presheaf).stalk (basePoint x) ⟶ CommRingCat.of (DualNumber k) :=
    CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)))) with hχdef
  have hχ : stalkPushforwardMap f (basePoint x) ≫ χ =
      Scheme.stalkClosedPointTo x ≫ CommRingCat.ofHom (algebraMap k (DualNumber k)) :=
    stalkPushforwardMap_comp_eq_of_fibreAlgHom f x hx (DualNumber k) e.toAlgHom
  refine ⟨pointOfStalkHom f hU hxU χ,
    isSquishingTangentVector_pointOfStalkHom f hf x hx hX'ft hX'qc hXft hXqc
      (fun W => injective_app_of_mono_hom_pushforwardAlgebra f hmono W) hW₀ hW₀iso hU hxU χ hχ
      (fun t => ?_) (fun b hb => ?_) fun c => ?_⟩
  · obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e.symm t)
    exact ⟨b, by
      change e (Ideal.Quotient.mk (stalkFibreIdeal f (basePoint x)) b) = t
      rw [hb, e.apply_symm_apply]⟩
  · exact exists_algebraMap_eq_of_dualNumber_snd_eq_zero k _ _ hne hmin e hb
  · exact exists_dualNumber_snd_eq k _ _ e c

/-- **[Stacks, Tag 0C1L].** A finite morphism of algebraic `k`-schemes which is injective on
structure sheaves and an isomorphism away from a finite set of points is a composite of glueings
of two rational points and squishings of tangent vectors. -/
@[stacks 0C1L]
theorem IsAlmostIso.isElementaryChain {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (Spec (.of k))} (f : X' ⟶ X) (hf : IsAlmostIso f) : IsElementaryChain k f :=
  isElementaryChain_of_isAlmostIso_of_isSquishingProducer (isSquishingProducer k) f hf

end Stacks.GlueSquishFactor

end
