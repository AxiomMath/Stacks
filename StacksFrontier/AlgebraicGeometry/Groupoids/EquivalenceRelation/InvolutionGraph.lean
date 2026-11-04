module

public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelationFromInvolution
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagonal together with the graph of an involution on a part of a scheme

Let `U` be a scheme, let `i : V ⟶ U` be a morphism and let `τ` be an involution of `U` carried
by `i` to a self-map `τ'` of `V`. The two morphisms

    `p = coprod.desc (𝟙 U) i`,    `q = coprod.desc (𝟙 U) (i ≫ τ)`

out of `U ⨿ V` present the union of the diagonal of `U` with the graph of `τ` over `V`. This
file proves that such a pair is an internal equivalence relation as soon as it is jointly monic,
and transports an internal equivalence relation from the underlying schemes of a pre-relation
over a base to the slice category over that base.

## Main results

* `AlgebraicGeometry.jointlyMono₂_of_mono_prodLift`: a pair of morphisms is jointly monic as
  soon as the morphism it induces to the product of its targets is a monomorphism.
* `AlgebraicGeometry.isEquivalenceRelation_coprodDesc_involutionGraph`: the diagonal together
  with the graph of an involution over a part of a scheme is an internal equivalence relation,
  once it is a relation at all.
* `Stacks.Groupoids.isEquivalenceRelation_of_left`: a pre-relation over a base scheme is an
  internal equivalence relation as soon as its two underlying morphisms of schemes are.

## Implementation notes

`AlgebraicGeometry.isEquivalenceRelation_coprodDesc_involutionGraph` is the case of
`AlgebraicGeometry.isEquivalenceRelation_of_coprod_involution` where the pair is given by
`coprod.desc`.

Joint monicity is a hypothesis of `isEquivalenceRelation_coprodDesc_involutionGraph` rather than
a conclusion: that the graph of the involution is disjoint from the diagonal over `V` is a
condition on `V`. It is taken in the form `CategoryTheory.JointlyMono₂` rather than as monicity
of a morphism to a product because the absolute product of schemes and the fibre product over a
base give different such morphisms and the same joint monicity.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.EquivalenceRelation

variable {C : Type*} [Category C] {R U : C} {p q : R ⟶ U}

/-- The relation which an internal equivalence relation induces on the morphisms from a fixed
object to `U` is an equivalence relation. -/
@[sga "3 IV 3.1.1" "more general"]
theorem equivalence_rel (e : EquivalenceRelation p q) (T : C) :
    _root_.Equivalence (fun x y : T ⟶ U => ∃ r : T ⟶ R, r ≫ p = x ∧ r ≫ q = y) := by
  constructor
  · intro x
    exact ⟨x ≫ e.r, by simp, by simp⟩
  · rintro x y ⟨r, hr₁, hr₂⟩
    exact ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁, hr₂],
      by rw [Category.assoc, e.symmetry₂, hr₁]⟩
  · rintro x y z ⟨r, hr₁, hr₂⟩ ⟨r', hr₁', hr₂'⟩
    refine ⟨PullbackCone.IsLimit.lift e.isLimit r r' (hr₂.trans hr₁'.symm) ≫ e.t, ?_, ?_⟩
    · rw [Category.assoc, e.transitivity₁, ← Category.assoc,
        PullbackCone.IsLimit.lift_fst, hr₁]
    · rw [Category.assoc, e.transitivity₂, ← Category.assoc,
        PullbackCone.IsLimit.lift_snd, hr₂']

end CategoryTheory.EquivalenceRelation

namespace AlgebraicGeometry

/-- A pair of morphisms with a common source is jointly monic as soon as the morphism it induces
to the product of its two targets is a monomorphism. -/
theorem jointlyMono₂_of_mono_prodLift {C : Type*} [Category C] {R X₁ X₂ : C}
    (p₁ : R ⟶ X₁) (p₂ : R ⟶ X₂) [HasBinaryProduct X₁ X₂] (hmono : Mono (prod.lift p₁ p₂)) :
    JointlyMono₂ p₁ p₂ := by
  have := hmono
  refine ⟨fun {T} f g h₁ h₂ => ?_⟩
  refine (cancel_mono (prod.lift p₁ p₂)).1 (prod.hom_ext ?_ ?_)
  · simpa only [Category.assoc, prod.lift_fst] using h₁
  · simpa only [Category.assoc, prod.lift_snd] using h₂

/-- **The diagonal together with the graph of an involution over a part of a scheme is an
internal equivalence relation.** Let `τ` be an involution of a scheme `U` and let `i : V ⟶ U`
be a morphism carrying a self-map `τ'` of `V` to `τ`. If the pair `coprod.desc (𝟙 U) i`,
`coprod.desc (𝟙 U) (i ≫ τ)` is jointly monic — equivalently, by
`AlgebraicGeometry.jointlyMono₂_of_mono_prodLift`, if the morphism it induces to a product
`U ⨯ U` is a monomorphism — then that pair is an internal equivalence relation. -/
theorem isEquivalenceRelation_coprodDesc_involutionGraph {U V : Scheme.{u}}
    (i : V ⟶ U) (τ : U ⟶ U) (τ' : V ⟶ V) (hτ : τ ≫ τ = 𝟙 U) (hτ' : τ' ≫ i = i ≫ τ)
    (hjm : JointlyMono₂ (coprod.desc (𝟙 U) i) (coprod.desc (𝟙 U) (i ≫ τ))) :
    IsEquivalenceRelation (coprod.desc (𝟙 U) i) (coprod.desc (𝟙 U) (i ≫ τ)) :=
  have := hjm
  isEquivalenceRelation_of_coprod_involution i τ τ' _ _ (coprod.inl_desc _ _)
    (coprod.inr_desc _ _) (coprod.inl_desc _ _) (coprod.inr_desc _ _) hτ' hτ

end AlgebraicGeometry

namespace Stacks.Groupoids

open AlgebraicGeometry

/-- A pre-relation over a base scheme is an internal equivalence relation as soon as its two
underlying morphisms of schemes are. -/
theorem isEquivalenceRelation_of_left {S : Scheme.{u}} {R U : Over S} (j : PreRelation R U)
    (h : IsEquivalenceRelation j.target.left j.source.left) :
    IsEquivalenceRelation j.target j.source := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  refine (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mpr ⟨⟨?_⟩, ?_⟩
  · intro T f g hfg
    exact Over.OverMorphism.ext (e.right_cancellation f.left g.left
      (by simpa [PreRelation.target] using congrArg (fun v => Over.Hom.left (v ≫ prod.fst)) hfg)
      (by simpa [PreRelation.source] using congrArg (fun v => Over.Hom.left (v ≫ prod.snd)) hfg))
  · intro T
    have hrel (x y : T ⟶ U) : j.Rel x y ↔
        ∃ r : T.left ⟶ R.left, r ≫ j.target.left = x.left ∧ r ≫ j.source.left = y.left := by
      refine ⟨fun ⟨r, h₁, h₂⟩ => ⟨r.left, ?_, ?_⟩, fun ⟨r, h₁, h₂⟩ => ?_⟩
      · simpa using congrArg Over.Hom.left h₁
      · simpa using congrArg Over.Hom.left h₂
      · have hw : r ≫ R.hom = T.hom := by
          rw [← Over.w j.target, ← Category.assoc, h₁, Over.w x]
        exact ⟨Over.homMk r hw, Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩
    have he := e.equivalence_rel T.left
    exact ⟨fun x => (hrel x x).mpr (he.refl x.left),
      fun hxy => (hrel _ _).mpr (he.symm ((hrel _ _).mp hxy)),
      fun hxy hyz => (hrel _ _).mpr (he.trans ((hrel _ _).mp hxy) ((hrel _ _).mp hyz))⟩

end Stacks.Groupoids

end
