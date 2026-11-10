module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Reverse

/-!
# A sieve-indexed descent datum, read as a family-indexed one

`CategoryTheory.Functor.SieveDescentDatum` (Stacks 026B, sieve-indexed) attaches an object of the
fibre to every arrow of a sieve and glues them by an isomorphism for every pair of morphisms into
two of the sources agreeing over the base. `CategoryTheory.Functor.DescentDatum` (Stacks 026B,
family-indexed, the form condition (3) of Stacks 02ZI quantifies over) attaches an object to every
member of a covering *family* and glues them over *given* fibre products of the overlaps, with the
cocycle condition over given triple overlaps.

`CategoryTheory.Functor.DescentDatum.toSieve`
(`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/ToSieve.lean`) reads a family-indexed datum
as a sieve-indexed one. This file does the converse for the *tautological* family of a sieve — the
family of **all** of its arrows, whose generated sieve is the sieve itself
(`CategoryTheory.Sieve.ofArrows_category`) and whose index type lies in `Type (max u₁ v₁)`. Over a
base with fibre products that family has all the overlaps the family-indexed notion needs, taken as
`CategoryTheory.Limits.pullback`, and every piece of gluing data is a value of the sieve-indexed
datum's own `iso` field.

## Why this is the whole of the remaining translation

The gluing data of the family-indexed notion are given over the chosen overlaps only, while the
sieve-indexed `iso` is given over an arbitrary object mapping into two sources. So the construction
below only *selects*: no new isomorphism is built. The three conditions that are not immediate are
the two `IsRestrictionOf` clauses and the cocycle, and each is one value of the sieve-indexed
datum's own axioms:

* the `IsRestrictionOf` clauses are
  `CategoryTheory.Functor.isRestrictionOf_pullbackRestriction` together with
  `CategoryTheory.Functor.SieveDescentDatum.baseChangeFiberMor_iso`, which is the base-change axiom
  `iso_pullback` read through `CategoryTheory.Functor.baseChangeFiberMor`;
* the cocycle condition is the `cocycle` axiom at the three projections of the triple overlap.

## What is not done here

This file stops at the translation. What it does not contain is the transport of *effectivity*
back: from `CategoryTheory.Functor.DescentDatum.IsEffective` of
`CategoryTheory.Functor.SieveDescentDatum.toFamilyDatum` to
`CategoryTheory.Functor.SieveDescentDatum.IsEffective` of the datum one started from, which is what
would give `CategoryTheory.Functor.HasEffectiveDescent` and, with
`CategoryTheory.Functor.isMorSheaf_of_isStackInGroupoids`, the full reverse bridge
`IsStackInGroupoids.{max u₁ v₁} → IsStack`. The library's producer for that last step is
`CategoryTheory.Functor.SieveDescentDatum.isEffective_of_fiberIso`
(`StacksFrontier/CategoryTheory/Sites/Stackification/StageThreeEffectiveDescent.lean`), whose
hypothesis is the compatibility of the comparison isomorphisms with the contractions of the datum
for an *arbitrary* morphism into a source; the family-indexed effectivity supplies it over the
chosen overlaps only, and `baseChangeFiberMor_iso` is the lemma that propagates it, a pair of
morphisms into two sources agreeing over the base factoring through their fibre product. That step
is not done here.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.ArrowIndex`, `.arrowSrc`, `.arrowHom`: the tautological
  covering family of a sieve.
* `CategoryTheory.Functor.SieveDescentDatum.toFamilyDatum`: the family-indexed descent datum
  attached to a sieve-indexed one.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.baseChangeFiberMor_iso`: the base change of a gluing
  isomorphism is the gluing isomorphism at the base-changed pair of morphisms.

## Implementation notes

*Universes.* The object universes and the two hom universes are independent: the hom universe of
the total category `𝒳` is unrelated to that of the base `𝒞`. The index universe `max u₁ v₁` of the
tautological covering family is built from the base alone, being the universe of the type of
arrows of a sieve on an object of `𝒞`.

## References

* [Stacks 026B](https://stacks.math.columbia.edu/tag/026B)
* [Stacks 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]

/-- **The base-change axiom of a sieve-indexed descent datum, read through
`CategoryTheory.Functor.baseChangeFiberMor`.** The base change along `γ` of the gluing isomorphism
at a pair `(ε, ε')` is the gluing isomorphism at the pair `(γ ≫ ε, γ ≫ ε')`, the two composites
being given names `mx`, `my` so that the identity can be compared with data presented at those
names. This is the form in which the family-indexed conditions of Stacks 02ZI consume
`CategoryTheory.Functor.SieveDescentDatum.iso_pullback`. -/
lemma SieveDescentDatum.baseChangeFiberMor_iso {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum p R)
    {V W Z Z' : 𝒞} {a : V ⟶ U} (ha : R.arrows a) {b : W ⟶ U} (hb : R.arrows b)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ a = ε' ≫ b) (γ : Z' ⟶ Z)
    {mx : Z' ⟶ V} {my : Z' ⟶ W} (hmx : mx = γ ≫ ε) (hmy : my = γ ≫ ε') :
    baseChangeFiberMor (D.iso ha hb ε ε' heq).hom γ mx hmx.symm my hmy.symm =
      (D.iso ha hb mx my (by
        rw [hmx, hmy, Category.assoc, Category.assoc, heq])).hom := by
  subst hmx
  subst hmy
  rw [← baseChangeFiberMor_eq_iso_pullback]
  exact D.iso_pullback ha hb ε ε' heq γ

namespace SieveDescentDatum

/-! ### The tautological covering family of a sieve -/

section Tautological

variable {U : 𝒞} (R : Sieve U)

/-- The index type of the tautological covering family of a sieve: its arrows. It lies in
`Type (max u₁ v₁)`, which is why condition (3) of Stacks 02ZI at that index universe applies to
every covering sieve with no reindexing. -/
abbrev ArrowIndex := R.arrows.category

/-- The source of a member of the tautological covering family. -/
abbrev arrowSrc (i : ArrowIndex R) : 𝒞 := i.obj.left

/-- A member of the tautological covering family. -/
abbrev arrowHom (i : ArrowIndex R) : arrowSrc R i ⟶ U := i.obj.hom

/-- Every member of the tautological covering family is an arrow of the sieve. -/
lemma arrowHom_mem (i : ArrowIndex R) : R.arrows (arrowHom R i) := i.property

variable [HasPullbacks 𝒞]

/-- The overlap of two members of the tautological covering family, taken as the chosen fibre
product of the base. -/
noncomputable abbrev overlap (i j : ArrowIndex R) : 𝒞 :=
  Limits.pullback (arrowHom R i) (arrowHom R j)

/-- The triple overlap of three members of the tautological covering family, taken as the chosen
fibre product `(Vᵢ ×_U Vⱼ) ×_{Vⱼ} (Vⱼ ×_U V_k)`, which is the standard model of
`Vᵢ ×_U Vⱼ ×_U V_k`. -/
noncomputable abbrev tripleOverlap (i j k : ArrowIndex R) : 𝒞 :=
  Limits.pullback (Limits.pullback.snd (arrowHom R i) (arrowHom R j))
    (Limits.pullback.fst (arrowHom R j) (arrowHom R k))

variable (i j k : ArrowIndex R)

/-- The projection of the triple overlap to the source of the first member. -/
noncomputable abbrev tripleProj₁ : tripleOverlap R i j k ⟶ arrowSrc R i :=
  Limits.pullback.fst _ _ ≫ Limits.pullback.fst (arrowHom R i) (arrowHom R j)

/-- The projection of the triple overlap to the source of the second member. -/
noncomputable abbrev tripleProj₂ : tripleOverlap R i j k ⟶ arrowSrc R j :=
  Limits.pullback.fst _ _ ≫ Limits.pullback.snd (arrowHom R i) (arrowHom R j)

/-- The projection of the triple overlap to the source of the third member. -/
noncomputable abbrev tripleProj₃ : tripleOverlap R i j k ⟶ arrowSrc R k :=
  Limits.pullback.snd _ _ ≫ Limits.pullback.snd (arrowHom R j) (arrowHom R k)

/-- The first two projections of the triple overlap agree over the base. -/
lemma tripleProj_cond₁₂ :
    tripleProj₁ R i j k ≫ arrowHom R i = tripleProj₂ R i j k ≫ arrowHom R j := by
  simp only [tripleProj₁, tripleProj₂, Category.assoc]
  rw [Limits.pullback.condition (f := arrowHom R i) (g := arrowHom R j)]

/-- The last two projections of the triple overlap agree over the base. The step with content is
that the triple overlap is a *genuine* fibre product over the source of the middle member, so its
two legs agree there. -/
lemma tripleProj_cond₂₃ :
    tripleProj₂ R i j k ≫ arrowHom R j = tripleProj₃ R i j k ≫ arrowHom R k := by
  simp only [tripleProj₂, tripleProj₃, Category.assoc]
  rw [← Limits.pullback.condition (f := arrowHom R j) (g := arrowHom R k), ← Category.assoc,
    Limits.pullback.condition, Category.assoc]

/-- The outer two projections of the triple overlap agree over the base, which is what makes the
comparison into the `(i, k)` overlap exist. -/
lemma tripleProj_cond₁₃ :
    tripleProj₁ R i j k ≫ arrowHom R i = tripleProj₃ R i j k ≫ arrowHom R k :=
  (tripleProj_cond₁₂ R i j k).trans (tripleProj_cond₂₃ R i j k)

end Tautological

/-! ### The translation -/

variable [HasPullbacks 𝒞] {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum p R)

/-- **A sieve-indexed descent datum, read as a descent datum relative to the tautological covering
family of the sieve.** The objects are the datum's own objects at the arrows of the sieve, the
restrictions are the chosen pullbacks
(`CategoryTheory.Functor.pullbackRestriction`), and every gluing isomorphism — over an overlap and
over a triple overlap alike — is a value of the datum's own `iso` field at the relevant pair of
projections. Nothing is constructed: the family-indexed notion asks for gluing data over the chosen
overlaps only, and the sieve-indexed one supplies it over an arbitrary object. -/
noncomputable def toFamilyDatum :
    DescentDatum p (arrowSrc R) (arrowHom R) (overlap R)
      (fun _ _ => Limits.pullback.fst _ _) (fun _ _ => Limits.pullback.snd _ _)
      (fun _ _ => IsPullback.of_hasPullback _ _)
      (tripleOverlap R)
      (fun _ _ _ => Limits.pullback.fst _ _) (fun _ _ _ => Limits.pullback.snd _ _)
      (fun _ _ _ => IsPullback.of_hasPullback _ _)
      (tripleProj₁ R) (tripleProj₂ R) (tripleProj₃ R)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) where
  x i := (D.obj _ (arrowHom_mem R i)).1
  hx i := (D.obj _ (arrowHom_mem R i)).2
  xrij i j := pullbackRestriction (D.obj _ (arrowHom_mem R i)) (Limits.pullback.fst _ _)
  xrji i j := pullbackRestriction (D.obj _ (arrowHom_mem R j)) (Limits.pullback.snd _ _)
  φ i j := Fiber.fiberInclusion.map
    (D.iso (arrowHom_mem R i) (arrowHom_mem R j) (Limits.pullback.fst _ _)
      (Limits.pullback.snd _ _) Limits.pullback.condition).hom
  φ_fibreHom i j := fibreHom_of_fiberHom _
  φ_iso i j := (Fiber.fiberInclusion.mapIso _).isIso_hom
  wi i j k := pullbackRestriction (D.obj _ (arrowHom_mem R i)) (tripleProj₁ R i j k)
  wj i j k := pullbackRestriction (D.obj _ (arrowHom_mem R j)) (tripleProj₂ R i j k)
  wk i j k := pullbackRestriction (D.obj _ (arrowHom_mem R k)) (tripleProj₃ R i j k)
  αij i j k := Fiber.fiberInclusion.map
    (D.iso (arrowHom_mem R i) (arrowHom_mem R j) (tripleProj₁ R i j k) (tripleProj₂ R i j k)
      (tripleProj_cond₁₂ R i j k)).hom
  αjk i j k := Fiber.fiberInclusion.map
    (D.iso (arrowHom_mem R j) (arrowHom_mem R k) (tripleProj₂ R i j k) (tripleProj₃ R i j k)
      (tripleProj_cond₂₃ R i j k)).hom
  αik i j k := Fiber.fiberInclusion.map
    (D.iso (arrowHom_mem R i) (arrowHom_mem R k) (tripleProj₁ R i j k) (tripleProj₃ R i j k)
      (tripleProj_cond₁₃ R i j k)).hom
  αij_restr i j k := by
    have h := isRestrictionOf_pullbackRestriction
      (x := D.obj _ (arrowHom_mem R i)) (y := D.obj _ (arrowHom_mem R j))
      (Limits.pullback.fst (arrowHom R i) (arrowHom R j))
      (Limits.pullback.snd (arrowHom R i) (arrowHom R j))
      (Limits.pullback.fst (Limits.pullback.snd (arrowHom R i) (arrowHom R j))
        (Limits.pullback.fst (arrowHom R j) (arrowHom R k)))
      (rfl : tripleProj₁ R i j k = _) (rfl : tripleProj₂ R i j k = _)
      (D.iso (arrowHom_mem R i) (arrowHom_mem R j) _ _ Limits.pullback.condition).hom
    rwa [D.baseChangeFiberMor_iso (arrowHom_mem R i) (arrowHom_mem R j) _ _
      Limits.pullback.condition _ rfl rfl] at h
  αjk_restr i j k := by
    have h := isRestrictionOf_pullbackRestriction
      (x := D.obj _ (arrowHom_mem R j)) (y := D.obj _ (arrowHom_mem R k))
      (Limits.pullback.fst (arrowHom R j) (arrowHom R k))
      (Limits.pullback.snd (arrowHom R j) (arrowHom R k))
      (Limits.pullback.snd (Limits.pullback.snd (arrowHom R i) (arrowHom R j))
        (Limits.pullback.fst (arrowHom R j) (arrowHom R k)))
      (Limits.pullback.condition :
        tripleProj₂ R i j k = _ ≫ Limits.pullback.fst (arrowHom R j) (arrowHom R k))
      (rfl : tripleProj₃ R i j k = _)
      (D.iso (arrowHom_mem R j) (arrowHom_mem R k) _ _ Limits.pullback.condition).hom
    rwa [D.baseChangeFiberMor_iso (arrowHom_mem R j) (arrowHom_mem R k) _ _
      Limits.pullback.condition _ Limits.pullback.condition rfl] at h
  s₁₃ i j k := Limits.pullback.lift (tripleProj₁ R i j k) (tripleProj₃ R i j k)
    (tripleProj_cond₁₃ R i j k)
  hs₁₃₁ i j k := Limits.pullback.lift_fst _ _ _
  hs₁₃₂ i j k := Limits.pullback.lift_snd _ _ _
  αik_restr i j k := by
    have h := isRestrictionOf_pullbackRestriction
      (x := D.obj _ (arrowHom_mem R i)) (y := D.obj _ (arrowHom_mem R k))
      (Limits.pullback.fst (arrowHom R i) (arrowHom R k))
      (Limits.pullback.snd (arrowHom R i) (arrowHom R k))
      (Limits.pullback.lift (tripleProj₁ R i j k) (tripleProj₃ R i j k)
        (tripleProj_cond₁₃ R i j k))
      (Limits.pullback.lift_fst _ _ _).symm (Limits.pullback.lift_snd _ _ _).symm
      (D.iso (arrowHom_mem R i) (arrowHom_mem R k) _ _ Limits.pullback.condition).hom
    rwa [D.baseChangeFiberMor_iso (arrowHom_mem R i) (arrowHom_mem R k) _ _
      Limits.pullback.condition _ (Limits.pullback.lift_fst _ _ _).symm
      (Limits.pullback.lift_snd _ _ _).symm] at h
  cocycle i j k := by
    have h2 : Fiber.fiberInclusion.map
          (D.iso (arrowHom_mem R i) (arrowHom_mem R k) (tripleProj₁ R i j k)
            (tripleProj₃ R i j k) (tripleProj_cond₁₃ R i j k)).hom =
        Fiber.fiberInclusion.map
          (D.iso (arrowHom_mem R i) (arrowHom_mem R j) (tripleProj₁ R i j k)
            (tripleProj₂ R i j k) (tripleProj_cond₁₂ R i j k)).hom ≫
        Fiber.fiberInclusion.map
          (D.iso (arrowHom_mem R j) (arrowHom_mem R k) (tripleProj₂ R i j k)
            (tripleProj₃ R i j k) (tripleProj_cond₂₃ R i j k)).hom := by
      rw [← Fiber.fiberInclusion.map_comp,
        D.cocycle (arrowHom_mem R i) (arrowHom_mem R j) (arrowHom_mem R k)
          (tripleProj₁ R i j k) (tripleProj₂ R i j k) (tripleProj₃ R i j k)
          (tripleProj_cond₁₂ R i j k) (tripleProj_cond₂₃ R i j k)
          (tripleProj_cond₁₃ R i j k)]
    exact h2

end SieveDescentDatum

end Functor

end CategoryTheory

end
