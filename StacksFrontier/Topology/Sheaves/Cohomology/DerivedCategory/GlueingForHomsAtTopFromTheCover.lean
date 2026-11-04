module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtOneOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsFromTheSheafCondition
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomPresheafValueRestrictionSquare
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOverOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGluingInSituation0D67

/-!
# The glueing of morphisms at the whole space, from the covering hypotheses

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation [Stacks, Tag 0D67].  `Stacks.DerivedGlueing.HasGluingForHomsAt S ⊤`
is the sheaf condition of [Stacks, Tag 0D66] part (2) read at the whole space; it is the one
granted hypothesis of `Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasGluingForHomsAtTop`,
the uniqueness half of [Stacks, Tag 0D6C].  It cannot hold for an arbitrary collection — see
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtTopNecessity` — so a
discharge must consume hypotheses (1) and (2) of Tag 0D6C: that the collection covers `X` and that
the intersection of two members is a union of members.

This file builds the dictionary between the two vocabularies in which the two halves of that
discharge are stated, and reduces the discharge to a single equation.

The sheaf condition of Tag 0D66 part (2) is available unconditionally, through
`Stacks.DerivedGlueing.existsUnique_hom_restrict_of_sSup_covered_of_valueEquivMap` with its
hypothesis `hmap` discharged by
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv_map`.  But it is
stated for *global* objects `K`, `L` of `D(𝒪_X)`, for their restrictions
`SheafOfModules.overFunctor` to the slices of the ringed site, and for the restriction of morphisms
`AlgebraicGeometry.RingedSite.restrictDerivedHom` along an arrow of that site, whereas
`HasGluingForHomsAt S ⊤` quantifies over objects of `OpenDerivedCategory X ⊤` and states its family
and compatibility through the system's own displayed restriction and
`Stacks.DerivedGlueing.restrictHomBelow`.

The objects are matched by `Stacks.DerivedGlueing.topRestrictionIso`, which is
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension` at `O = ⊤`: an object over the open
subspace `⊤` is extended by zero to `X`, and the restriction of that extension to a member, read
in the open-subspace model, is the object's displayed restriction.  The morphisms are then matched
by `Stacks.DerivedGlueing.topHomEquiv`, because the passage between the two models of modules on an
open is fully faithful on derived categories
(`Stacks.DerivedGlueing.full_sliceToSubspace_mapDerivedCategory` and
`Stacks.DerivedGlueing.faithful_sliceToSubspace_mapDerivedCategory`).

What is **not** proved here is that this bijection carries one restriction of morphisms to the
other.  That single equation is isolated as the predicate
`Stacks.DerivedGlueing.HasHomRestrictionDictionary`, and
`Stacks.DerivedGlueing.hasGluingForHomsAt_top_of_covers_of_dictionary` derives the full glueing
condition at `⊤` from it together with hypotheses (1) and (2); everything else that discharge needs
— the transport of the negative-`Ext` hypothesis, the identification of a morphism over `⊤` with a
morphism of the site-side restriction to `⊤`, the application of the sheaf condition and the
transport of its unique existence back — is proved.  So the predicate is exactly the residual
obligation.  The intended comparison for it is
`Stacks.DerivedGlueing.sliceRestrictOverIso`, whose docstring records that it identifies the
restriction of morphisms of a system of locally given derived objects with the restriction of
morphisms along an arrow of the ringed site; what is missing is the coherence of that comparison
with `Stacks.DerivedGlueing.LocallyGiven.restrictionComp` and with
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`.

## Main definitions

* `Stacks.DerivedGlueing.globalObjOfTop`: an object over the open subspace `⊤`, extended by zero
  to an object of `D(𝒪_X)`.
* `Stacks.DerivedGlueing.topRestrictionIso`: the restriction of that extension to an open, read in
  the open-subspace model, is the displayed restriction of the original object.
* `Stacks.DerivedGlueing.topHomEquiv`: the induced bijection between the morphisms of the two
  restrictions in the ringed-site vocabulary and the morphisms of the two displayed restrictions.
* `Stacks.DerivedGlueing.topSelfHomEquiv`: the same at `⊤`, where the displayed restriction from
  `⊤` to `⊤` is the identity.
* `Stacks.DerivedGlueing.HasHomRestrictionDictionary`: the residual obligation — that
  `Stacks.DerivedGlueing.topHomEquiv` carries
  `AlgebraicGeometry.RingedSite.restrictDerivedHom` to
  `Stacks.DerivedGlueing.restrictHomBelow`.

## Main results

* `Stacks.DerivedGlueing.subsingleton_shiftedHom_siteRestrictOfTop`: the negative-`Ext` hypothesis
  of Situation 0D67 transports to the ringed-site vocabulary.
* `Stacks.DerivedGlueing.topHomEquiv_top_symm`: under
  `Stacks.DerivedGlueing.topHomEquiv` at `⊤`, a morphism over `⊤` goes to its own displayed
  restriction from `⊤` to `⊤`.
* `Stacks.DerivedGlueing.restrictDerivedHom_topSelfHomEquiv_symm`: granted the dictionary, the
  site-side restriction of the morphism attached to `ψ : K ⟶ L` is the morphism attached to the
  displayed restriction of `ψ`.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_top_of_covers_of_dictionary`: granted the dictionary,
  the glueing of morphisms at `⊤` holds for a collection that covers `X` and whose pairwise
  intersections are unions of members — hypotheses (1) and (2) of [Stacks, Tag 0D6C].

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)

Tags covered: none.  These statements build a dictionary between two vocabularies of the
development and isolate one residual equation; they are not clauses of a tag's statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules
open Stacks.SheafOfModules (ringedSite)
open Stacks.Cohomology.UnboundedHigherDirectImage (derivedPreimageHomPresheafValueEquiv_map)

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The two vocabularies, on objects -/

/-- **An object given over the open subspace `⊤`, read as an object of `D(𝒪_X)`.** Extension by
zero along `⊤` is fully faithful on derived categories, by
`Stacks.DerivedGlueing.faithful_jShriekTop_mapDerivedCategory`, so nothing is lost; this is
`Stacks.DerivedGlueing.Solution.globalObj` for an arbitrary object rather than for the global
object of a solution. -/
abbrev globalObjOfTop (K : OpenDerivedCategory X ⊤) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K

/-- **The restriction of `Stacks.DerivedGlueing.globalObjOfTop` to the slice over an open.** This
is the object the sheaf condition of [Stacks, Tag 0D66] part (2) speaks about. -/
abbrev siteRestrictOfTop (W : Opens X.carrier) (K : OpenDerivedCategory X ⊤) :=
  (SheafOfModules.overFunctor.{u} (structureSheafRing X) W).mapDerivedCategory.obj
    (globalObjOfTop K)

/-- **The object dictionary at `⊤`.** The restriction to an open `W` of the extension by zero of
`K`, read in the open-subspace model of `W`, is the displayed restriction of `K` from `⊤` to `W`.

This is `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension` at `O = ⊤`; the crossing
between the two spellings of restriction of modules is paid there, once, by
`Stacks.DerivedGlueing.openModuleRestriction_eq`. -/
def topRestrictionIso (S : LocallyGiven X) (W : Opens X.carrier)
    (K : OpenDerivedCategory X ⊤) :
    (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory.obj
        (siteRestrictOfTop W K) ≅
      (S.restriction W ⊤ le_top).obj K :=
  S.restrictionIsoOfExtension ⊤ W le_top K

/-! ### The two vocabularies, on morphisms -/

/-- **The morphism dictionary at `⊤`.** A morphism between the restrictions to the slice over `W`
of the extensions by zero of `K` and `L` is the same thing as a morphism between the displayed
restrictions of `K` and `L` from `⊤` to `W`.

Both steps are formal: the passage between the two models of modules on `W` is fully faithful on
derived categories, and `Stacks.DerivedGlueing.topRestrictionIso` identifies the two readings of
the objects. -/
def topHomEquiv (S : LocallyGiven X) (W : Opens X.carrier) (K L : OpenDerivedCategory X ⊤) :
    (siteRestrictOfTop W K ⟶ siteRestrictOfTop W L) ≃
      ((S.restriction W ⊤ le_top).obj K ⟶ (S.restriction W ⊤ le_top).obj L) :=
  (Stacks.DerivedGlueing.sliceToSubspaceDerivedFullyFaithful W).homEquiv.trans
    (Iso.homCongr (topRestrictionIso S W K) (topRestrictionIso S W L))

/-- **The morphism dictionary at `W = ⊤`, with the displayed restriction from `⊤` to `⊤` removed.**
A morphism between the restrictions to the slice over `⊤` of the extensions by zero of `K` and `L`
is the same thing as a morphism `K ⟶ L`, by
`Stacks.DerivedGlueing.restrictionSelfIso`. -/
def topSelfHomEquiv (S : LocallyGiven X) (K L : OpenDerivedCategory X ⊤) :
    (siteRestrictOfTop (⊤ : Opens X.carrier) K ⟶ siteRestrictOfTop (⊤ : Opens X.carrier) L) ≃
      (K ⟶ L) :=
  (topHomEquiv S ⊤ K L).trans
    (Iso.homCongr ((restrictionSelfIso S ⊤ le_top).app K)
      ((restrictionSelfIso S ⊤ le_top).app L))

/-- **The morphism dictionary, written out.** The bijection is the derived action of the passage
between the two models of modules on `W`, conjugated by the object dictionary; it holds by
definition, and it is the form in which the residual obligation below is usable. -/
theorem topHomEquiv_apply (S : LocallyGiven X) (W : Opens X.carrier)
    (K L : OpenDerivedCategory X ⊤) (ξ : siteRestrictOfTop W K ⟶ siteRestrictOfTop W L) :
    topHomEquiv S W K L ξ =
      (topRestrictionIso S W K).inv ≫
        (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory.map ξ ≫
        (topRestrictionIso S W L).hom :=
  rfl

/-! ### The negative-`Ext` hypothesis, transported -/

/-- **The vanishing of a negative shifted `Hom` group transports from the vocabulary of Situation
0D67 to the ringed-site vocabulary.** The passage between the two models of modules on `W` is
faithful on derived categories, so it reflects the vanishing, and
`Stacks.DerivedGlueing.topRestrictionIso` identifies the two readings of the objects.  This is the
argument of `Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self`, run at an arbitrary
object instead of at the global object of a solution. -/
theorem subsingleton_shiftedHom_siteRestrictOfTop (S : LocallyGiven X) (W : Opens X.carrier)
    (K L : OpenDerivedCategory X ⊤) (i : ℤ)
    (h : Subsingleton (ShiftedHom ((S.restriction W ⊤ le_top).obj K)
      ((S.restriction W ⊤ le_top).obj L) i)) :
    Subsingleton (ShiftedHom (siteRestrictOfTop W K) (siteRestrictOfTop W L) i) := by
  have := faithful_sliceToSubspace_mapDerivedCategory (underlyingRingSheaf X) W
  exact subsingleton_shiftedHom_of_faithful
    (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory _ _ i
    (subsingleton_shiftedHom_of_iso (topRestrictionIso S W K) (topRestrictionIso S W L) i h)

/-! ### The displayed restriction from `⊤` to `⊤`, read through the dictionary -/

/-- **Restriction from an open to itself carries a morphism to its conjugate by
`Stacks.DerivedGlueing.restrictionSelfIso`.** Only the naturality of that isomorphism is
involved; this is `Stacks.DerivedGlueing.restrictionSelfIso_naturality` with the comparison on the
target cancelled. -/
theorem restrictionSelf_conj_eq_map (S : LocallyGiven X) (U : Opens X.carrier) (hUU : U ≤ U)
    {K L : OpenDerivedCategory X U} (f : K ⟶ L) :
    ((restrictionSelfIso S U hUU).app K).hom ≫ f ≫ ((restrictionSelfIso S U hUU).app L).inv =
      (S.restriction U U hUU).map f := by
  refine (cancel_mono ((restrictionSelfIso S U hUU).app L).hom).mp ?_
  rw [restrictionSelfIso_naturality S U hUU f]
  simp

/-- The value of `Stacks.DerivedGlueing.topSelfHomEquiv` is the value of
`Stacks.DerivedGlueing.topHomEquiv` at `⊤` followed by the conjugation by
`Stacks.DerivedGlueing.restrictionSelfIso`; it holds by definition. -/
theorem topSelfHomEquiv_symm_apply (S : LocallyGiven X) (K L : OpenDerivedCategory X ⊤)
    (ψ : K ⟶ L) :
    (topSelfHomEquiv S K L).symm ψ =
      (topHomEquiv S ⊤ K L).symm
        (((restrictionSelfIso S ⊤ le_top).app K).hom ≫ ψ ≫
          ((restrictionSelfIso S ⊤ le_top).app L).inv) :=
  rfl

/-- **Under the dictionary at `⊤`, a morphism `K ⟶ L` is its own displayed restriction from `⊤` to
`⊤`.** -/
theorem topHomEquiv_top_symm (S : LocallyGiven X) (K L : OpenDerivedCategory X ⊤) (ψ : K ⟶ L) :
    topHomEquiv S ⊤ K L ((topSelfHomEquiv S K L).symm ψ) =
      (S.restriction (⊤ : Opens X.carrier) ⊤ le_top).map ψ := by
  rw [topSelfHomEquiv_symm_apply, Equiv.apply_symm_apply, restrictionSelf_conj_eq_map]

/-! ### The residual obligation -/

/-- **The restriction dictionary: the residual obligation of the discharge of the glueing of
morphisms at `⊤`.** It says that the bijection `Stacks.DerivedGlueing.topHomEquiv` carries the
restriction of morphisms along an arrow of the ringed site,
`AlgebraicGeometry.RingedSite.restrictDerivedHom`, to the restriction of morphisms of a system of
locally given derived objects, `Stacks.DerivedGlueing.restrictHomBelow` — that is, that the two
presheaves of morphism groups attached to a pair of objects over `⊤` are identified by the
dictionary, and not merely isomorphic open by open.

Nothing else is missing: `Stacks.DerivedGlueing.hasGluingForHomsAt_top_of_covers_of_dictionary`
derives `Stacks.DerivedGlueing.HasGluingForHomsAt S ⊤` from this together with hypotheses (1) and
(2) of [Stacks, Tag 0D6C].

The intended proof is `Stacks.DerivedGlueing.sliceRestrictOverIso` — the comparison identifying
the two restrictions of morphisms — together with the coherence of that comparison with
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp`, pinned down by the field
`restrictionCompFactors` of `Stacks.DerivedGlueing.LocallyGiven`, and with
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`, computed on the image of the
localization functor by
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso_hom_app_Q`.  Both sides are
natural transformations between functors that factor through the localization, so the coherence is
determined by its values on the image of a complex. -/
def HasHomRestrictionDictionary (S : LocallyGiven X) : Prop :=
  ∀ (K L : OpenDerivedCategory X ⊤) (T W : Opens X.carrier) (hTW : T ≤ W)
      (χ : siteRestrictOfTop W K ⟶ siteRestrictOfTop W L),
    topHomEquiv S T K L (AlgebraicGeometry.RingedSite.restrictDerivedHom (ringedSite X.sheaf)
        hTW.hom (globalObjOfTop K) (globalObjOfTop L) χ) =
      restrictHomBelow S hTW le_top (topHomEquiv S W K L χ)

/-- **The restriction dictionary, written out.** The two bijections are unfolded by
`Stacks.DerivedGlueing.topHomEquiv_apply`, so this holds by definition; it is the form in which
the obligation is attacked, both sides being composites of named comparisons. -/
theorem hasHomRestrictionDictionary_iff (S : LocallyGiven X) :
    HasHomRestrictionDictionary S ↔
      ∀ (K L : OpenDerivedCategory X ⊤) (T W : Opens X.carrier) (hTW : T ≤ W)
          (χ : siteRestrictOfTop W K ⟶ siteRestrictOfTop W L),
        (topRestrictionIso S T K).inv ≫
            (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
              (AlgebraicGeometry.RingedSite.restrictDerivedHom (ringedSite X.sheaf) hTW.hom
                (globalObjOfTop K) (globalObjOfTop L) χ) ≫
            (topRestrictionIso S T L).hom =
          restrictHomBelow S hTW le_top
            ((topRestrictionIso S W K).inv ≫
              (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory.map χ ≫
              (topRestrictionIso S W L).hom) :=
  Iff.rfl

/-! ### A criterion for the dictionary -/

section Generic

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C₁ : Type u₃} [Category.{v₃} C₁] {E₁ : Type u₄} [Category.{v₄} E₁]
  {E₂ : Type u₅} [Category.{v₅} E₂]

/-- **Conjugating the action of two isomorphic functors gives the same map on morphisms.** Let
`δ : Φ₁ ≅ Φ₂` and let `χ : A ⟶ B`.  If the two chosen comparisons at the source agree after `δ`,
and the two at the target agree before `δ`, then conjugating `Φ₁.map χ` by the first pair is
conjugating `Φ₂.map χ` by the second.

Every category, functor and morphism is a variable, so a consumer pays one `isDefEq` per crossing
and no `rw` has to fire on a goal mixing two spellings; the two factors on each side are kept
separate because that is the shape the two restrictions of morphisms of this development have
after their definitions are unfolded.  This is the mechanism by which a comparison of the
restriction *functors* yields a comparison of the restrictions of *morphisms*. -/
theorem conj_eq_conj_of_natIso {Φ₁ Φ₂ : C ⥤ D} (δ : Φ₁ ≅ Φ₂) {A B : C}
    {P P₁ P₂ Q Q₁ Q₂ : D}
    {p₁ : P ⟶ P₁} {q₁ : P₁ ⟶ Φ₁.obj A} {r₁ : Φ₁.obj B ⟶ Q₁} {s₁ : Q₁ ⟶ Q}
    {p₂ : P ⟶ P₂} {q₂ : P₂ ⟶ Φ₂.obj A} {r₂ : Φ₂.obj B ⟶ Q₂} {s₂ : Q₂ ⟶ Q}
    (ha : (p₁ ≫ q₁) ≫ δ.hom.app A = p₂ ≫ q₂)
    (hb : δ.hom.app B ≫ r₂ ≫ s₂ = r₁ ≫ s₁) (χ : A ⟶ B) :
    p₁ ≫ q₁ ≫ Φ₁.map χ ≫ r₁ ≫ s₁ = p₂ ≫ q₂ ≫ Φ₂.map χ ≫ r₂ ≫ s₂ :=
  calc p₁ ≫ q₁ ≫ Φ₁.map χ ≫ r₁ ≫ s₁
      = p₁ ≫ q₁ ≫ Φ₁.map χ ≫ δ.hom.app B ≫ r₂ ≫ s₂ := by rw [hb]
    _ = p₁ ≫ q₁ ≫ δ.hom.app A ≫ Φ₂.map χ ≫ r₂ ≫ s₂ := by rw [reassoc_of% (δ.hom.naturality χ)]
    _ = ((p₁ ≫ q₁) ≫ δ.hom.app A) ≫ Φ₂.map χ ≫ r₂ ≫ s₂ := by simp only [Category.assoc]
    _ = p₂ ≫ q₂ ≫ Φ₂.map χ ≫ r₂ ≫ s₂ := by rw [ha, Category.assoc]

/-- **The same, with both functor actions factored through an intermediate category.** This is
`Stacks.DerivedGlueing.conj_eq_conj_of_natIso` at `Φ₁ = Ψ ⋙ G` and `Φ₂ = Θ ⋙ H`, stated in the
shape the two restrictions of morphisms of this development have: each is a morphism
`m₁ ≫ Ψ.map χ ≫ m₂` of the intermediate category carried along a functor `G` and conjugated by a
comparison of objects.

Every category, functor, object and morphism is a variable, so a consumer pays exactly one
`isDefEq` at `default` transparency for the crossing between its two spellings of a sheaf of
rings, and no `rw` or `simp only` has to fire on a goal mixing them — which, in this cone, they
do not. -/
theorem conj_functor_eq_conj_functor_of_natIso (Ψ : C₁ ⥤ E₁) (G : E₁ ⥤ D) (Θ : C₁ ⥤ E₂)
    (H : E₂ ⥤ D) (δ : Ψ ⋙ G ≅ Θ ⋙ H) {A B : C₁} {P Q : D} {X₁ Y₁ : E₁} {X₂ Y₂ : E₂}
    {eA : P ⟶ G.obj X₁} {m₁ : X₁ ⟶ Ψ.obj A} {m₂ : Ψ.obj B ⟶ Y₁} {eB : G.obj Y₁ ⟶ Q}
    {cA : P ⟶ H.obj X₂} {n₁ : X₂ ⟶ Θ.obj A} {n₂ : Θ.obj B ⟶ Y₂} {cB : H.obj Y₂ ⟶ Q}
    (ha : (eA ≫ G.map m₁) ≫ δ.hom.app A = cA ≫ H.map n₁)
    (hb : δ.hom.app B ≫ H.map n₂ ≫ cB = G.map m₂ ≫ eB) (χ : A ⟶ B) :
    eA ≫ G.map (m₁ ≫ Ψ.map χ ≫ m₂) ≫ eB = cA ≫ H.map (n₁ ≫ Θ.map χ ≫ n₂) ≫ cB := by
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    conj_eq_conj_of_natIso δ ha hb χ

end Generic

section Comparison

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.hasSheafifyOverOpen
  Stacks.Topology.RingedSpaceSheafifyOpens.wEqualsLocallyBijectiveOverOpen

/-- Restriction of modules along an inclusion of opens is additive, being a pushforward. -/
local instance additiveOverMapOpen {T W : Opens X.carrier} (hTW : T ≤ W) :
    (SheafOfModules.overMap.{u} (structureSheafRing X) hTW.hom).Additive :=
  inferInstanceAs (SheafOfModules.pushforward.{u}
    ((Sheaf.pushforwardOverMapIso (structureSheafRing X) hTW.hom).inv)).Additive

/-- Restriction of modules along an inclusion of opens preserves finite limits. -/
local instance preservesFiniteLimitsOverMapOpen {T W : Opens X.carrier} (hTW : T ≤ W) :
    Limits.PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (structureSheafRing X) hTW.hom) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits hTW.hom

/-- Restriction of modules along an inclusion of opens preserves finite colimits. -/
local instance preservesFiniteColimitsOverMapOpen {T W : Opens X.carrier} (hTW : T ≤ W) :
    Limits.PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (structureSheafRing X) hTW.hom) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits hTW.hom

/-- **A criterion for the restriction dictionary.** Suppose given, for each inclusion `T ≤ W` of
opens, an isomorphism `δ` between the two readings of restriction from `W` to `T` on derived
categories — restriction along the arrow of the ringed site followed by the passage to the
open-subspace model of `T`, against the passage to the open-subspace model of `W` followed by the
system's own displayed restriction — and suppose that `δ` is compatible with the object dictionary
`Stacks.DerivedGlueing.topRestrictionIso` at the source and at the target, in the sense of `hsrc`
and `htgt`.  Then the dictionary holds.

This is `Stacks.DerivedGlueing.conj_eq_conj_of_natIso` applied after unfolding the two
restrictions of morphisms, `AlgebraicGeometry.RingedSite.restrictDerivedHom` and
`Stacks.DerivedGlueing.restrictHomBelow`; both are a conjugation of a functor action by a
comparison of restriction in one and in two steps, so the content is entirely in `δ`, `hsrc` and
`htgt`, none of which mentions a morphism between the objects being restricted.

The isomorphism `δ` is the derived form of `Stacks.DerivedGlueing.sliceRestrictOverIso`, whose
source is the composite of functors on modules that
`Stacks.DerivedGlueing.overFunctor_comp_overMap_comp_sliceToSubspace` identifies with restriction
to the open subspace `T`.  For `hsrc` and `htgt` the comparison
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp` may be replaced by the canonical one, the
counit of extension by zero on the middle open, by
`Stacks.DerivedGlueing.restrictionComp_eq_mapDerivedCategoryComp`. -/
theorem hasHomRestrictionDictionary_of_comparison (S : LocallyGiven X)
    (δ : ∀ (T W : Opens X.carrier) (hTW : T ≤ W),
      (SheafOfModules.overMap.{u} (structureSheafRing X) hTW.hom).mapDerivedCategory ⋙
          (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory ≅
        (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory ⋙
          S.restriction T W hTW)
    (hsrc : ∀ (K : OpenDerivedCategory X ⊤) (T W : Opens X.carrier) (hTW : T ≤ W),
      ((topRestrictionIso S T K).inv ≫
            (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
              ((AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso
                (ringedSite X.sheaf) hTW.hom).inv.app (globalObjOfTop K))) ≫
          (δ T W hTW).hom.app (siteRestrictOfTop W K) =
        (S.restrictionComp T W ⊤ hTW le_top).hom.app K ≫
          (S.restriction T W hTW).map (topRestrictionIso S W K).inv)
    (htgt : ∀ (L : OpenDerivedCategory X ⊤) (T W : Opens X.carrier) (hTW : T ≤ W),
      (δ T W hTW).hom.app (siteRestrictOfTop W L) ≫
          (S.restriction T W hTW).map (topRestrictionIso S W L).hom ≫
            (S.restrictionComp T W ⊤ hTW le_top).inv.app L =
        (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
            ((AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso
              (ringedSite X.sheaf) hTW.hom).hom.app (globalObjOfTop L)) ≫
          (topRestrictionIso S T L).hom) :
    HasHomRestrictionDictionary S :=
  (hasHomRestrictionDictionary_iff S).mpr fun K L T W hTW χ =>
    conj_functor_eq_conj_functor_of_natIso
      (SheafOfModules.overMap.{u} (structureSheafRing X) hTW.hom).mapDerivedCategory
      (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory
      (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory
      (S.restriction T W hTW) (δ T W hTW) (hsrc K T W hTW) (htgt L T W hTW) χ

end Comparison

/-! ### The glueing of morphisms at `⊤`, granted the dictionary -/

/-- **Granted the dictionary, the site-side restriction to `W` of the morphism attached to
`ψ : K ⟶ L` is the morphism attached to the displayed restriction of `ψ` to `W`.** This is the
dictionary read at the pair `W ≤ ⊤`, followed by
`Stacks.DerivedGlueing.topHomEquiv_top_symm` and
`Stacks.DerivedGlueing.restrictHomBelow_map`: restricting the displayed restriction of a morphism
is its displayed restriction. -/
theorem restrictDerivedHom_topSelfHomEquiv_symm (S : LocallyGiven X)
    (hdict : HasHomRestrictionDictionary S) (K L : OpenDerivedCategory X ⊤)
    (W : Opens X.carrier) (hWT : W ≤ ⊤) (ψ : K ⟶ L) :
    AlgebraicGeometry.RingedSite.restrictDerivedHom (ringedSite X.sheaf) hWT.hom
        (globalObjOfTop K) (globalObjOfTop L) ((topSelfHomEquiv S K L).symm ψ) =
      (topHomEquiv S W K L).symm ((S.restriction W ⊤ hWT).map ψ) := by
  refine (topHomEquiv S W K L).injective ?_
  rw [Equiv.apply_symm_apply, hdict K L W ⊤ hWT ((topSelfHomEquiv S K L).symm ψ),
    topHomEquiv_top_symm, restrictHomBelow_map]

/-- **The glueing of morphisms at the whole space, from hypotheses (1) and (2) of
[Stacks, Tag 0D6C], granted the restriction dictionary.**

In Situation [Stacks, Tag 0D67], assume that the displayed collection covers `X` and that the
intersection of two members is the union of the members contained in it.  Then the sheaf condition
of [Stacks, Tag 0D66] part (2) holds at `⊤`: a family of morphisms between the displayed
restrictions of two objects over `⊤`, indexed by the members of the collection and compatible with
`Stacks.DerivedGlueing.restrictHomBelow`, comes from a unique morphism over `⊤`.

Both hypotheses on the collection are genuinely consumed — they are what
`Stacks.DerivedGlueing.existsUnique_hom_restrict_of_sSup_covered_of_valueEquivMap` needs — and they
are necessary: `Stacks.DerivedGlueing.subsingleton_hom_of_hasGluingForHomsAt_top` shows that the
conclusion fails outright at a collection with no members.  Nothing else is granted except the
dictionary `Stacks.DerivedGlueing.HasHomRestrictionDictionary`; in particular the hypothesis
`hmap` carried by the sheaf condition is discharged here by
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv_map`.

The proof transports the whole problem across the dictionary: the negative-`Ext` hypothesis by
`Stacks.DerivedGlueing.subsingleton_shiftedHom_siteRestrictOfTop`, the family and its
compatibility by `Stacks.DerivedGlueing.topHomEquiv` and the dictionary, and the unique morphism
produced over `⊤` back by `Stacks.DerivedGlueing.topSelfHomEquiv`, whose compatibility with the
restrictions is `Stacks.DerivedGlueing.restrictDerivedHom_topSelfHomEquiv_symm`. -/
theorem hasGluingForHomsAt_top_of_covers_of_dictionary (S : LocallyGiven X)
    (hdict : HasHomRestrictionDictionary S) (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) :
    HasGluingForHomsAt S ⊤ := by
  intro K L hExt φ hφ
  obtain ⟨Ψ, hΨ, huniq⟩ :=
    exists_unique_restrictDerivedHom_of_sSup_covered (globalObjOfTop K) (globalObjOfTop L)
      S.opens hcover hinter
      (fun W hW i hi =>
        subsingleton_shiftedHom_siteRestrictOfTop S W K L i (hExt W hW le_top i hi))
      (fun _Y f _V _V' hV s =>
        derivedPreimageHomPresheafValueEquiv_map f (globalObjOfTop K) (globalObjOfTop L) hV s)
      ⊤ (top_eq_sSup_covered_of_sSup_eq_top S hcover)
      (fun W hW hWT => (topHomEquiv S W K L).symm (φ W hW hWT))
      (by
        intro W W' hW hW' h hWT
        refine (topHomEquiv S W' K L).injective ?_
        rw [hdict K L W' W h ((topHomEquiv S W K L).symm (φ W hW hWT))]
        simpa only [Equiv.apply_symm_apply] using hφ W W' hW hW' h hWT)
  obtain ⟨ψ, rfl⟩ : ∃ ψ : K ⟶ L, Ψ = (topSelfHomEquiv S K L).symm ψ :=
    ⟨topSelfHomEquiv S K L Ψ, (Equiv.symm_apply_apply _ _).symm⟩
  refine ⟨ψ, fun W hW hWT => ?_, fun ψ' hψ' => ?_⟩
  · have h1 := hΨ W hW hWT
    rw [restrictDerivedHom_topSelfHomEquiv_symm S hdict K L W hWT] at h1
    exact (topHomEquiv S W K L).symm.injective h1
  · refine (topSelfHomEquiv S K L).symm.injective ?_
    refine huniq _ fun W hW hWT => ?_
    rw [restrictDerivedHom_topSelfHomEquiv_symm S hdict K L W hWT]
    exact congrArg (topHomEquiv S W K L).symm (hψ' W hW hWT)

end Stacks.DerivedGlueing

end
