module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.CategoryTheory.EquivalenceRelation.FreeInvolution

/-!
# The étale equivalence relation of a free involution on an open subscheme

Let `U` be a scheme, `V ⊆ U` an open subscheme and `a : U ⟶ U` an automorphism with
`a ∘ a = id` which preserves `V` and acts freely on it. The diagonal of `U` together with the
graph of `a` over `V`,

  `R = U ⨿ V ⇉ U`,  `coprod.desc (𝟙 U) V.ι`  and  `coprod.desc (𝟙 U) (V.ι ≫ a)`,

is then an étale equivalence relation on `U`. Its quotient is the algebraic space obtained by
glueing `U` to itself along `a` over `V`; it is a scheme only when `V = U`, because the two
copies of a point of `U ∖ V` in the closure of `V` cannot be separated.

This is the shape of the counterexamples of Stacks 02Z1, Stacks 087I and Stacks 088W; they
differ only in the choice of `U`, `V` and `a`.

## Main definitions

* `AlgebraicGeometry.OpenInvolution.relationScheme`: the relation scheme `U ⨿ V`.
* `AlgebraicGeometry.OpenInvolution.relationTarget` and
  `AlgebraicGeometry.OpenInvolution.relationSource`: its two projections to `U`.
* `AlgebraicGeometry.OpenInvolution.overTerminal`: a scheme as an object over the terminal
  scheme.
* `AlgebraicGeometry.OpenInvolution.preRelation`: the two projections packaged as a
  pre-relation over the terminal scheme, in the shape Stacks 022P asks for.

## Main results

* `AlgebraicGeometry.OpenInvolution.etale_relationTarget` and
  `AlgebraicGeometry.OpenInvolution.etale_relationSource`: both projections are étale.
* `AlgebraicGeometry.OpenInvolution.isEtaleEquivalenceRelation_preRelation`: the pre-relation
  is an étale equivalence relation.
* `AlgebraicGeometry.OpenInvolution.quasiCompact_relationSource`: when `U` and `V` are
  quasi-compact, so is the source projection.

## Implementation notes

Freeness of the action is asked for in the test-scheme form: a scheme mapping to `V` which
the inclusion and the inclusion followed by `a` cannot tell apart is empty. That is what the
monomorphism condition on an internal relation needs, and it is how it is verified in
practice — on `Spec` of a ring in which `2` is invertible, by inverting a coordinate equal to
its own negative.

The equivalence-relation property is proved in the category of schemes, which is finitary
extensive, by `CategoryTheory.isEquivalenceRelation_coprod_desc_of_free_involution`, and then
transported to the slice over the terminal scheme along the inverse of
`CategoryTheory.Over.equivalenceOfIsTerminal`, using Mathlib's transport of the reflexive,
symmetric and transitive parts along a functor. The joint monicity needed for that transport
is read off from the underlying morphisms, a morphism of a slice category being determined by
the morphism it covers.

Étaleness of the two projections is checked summand by summand with
`AlgebraicGeometry.etale_coprod`: on the diagonal summand both projections are the identity,
and on the graph summand the target projection is an open immersion and the source projection
is an open immersion followed by an automorphism.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 087I](https://stacks.math.columbia.edu/tag/087I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.OpenInvolution

variable {U : Scheme.{u}} (V : U.Opens) (a : U ⟶ U)

/-- The relation scheme `R = U ⨿ V` of a free involution on an open subscheme: the diagonal
summand together with the graph summand. -/
noncomputable abbrev relationScheme : Scheme.{u} := U ⨿ V.toScheme

/-- The target projection `R ⟶ U`: the identity on the diagonal summand and the inclusion on
the graph summand. -/
noncomputable def relationTarget : relationScheme V ⟶ U := coprod.desc (𝟙 U) V.ι

/-- The source projection `R ⟶ U`: the identity on the diagonal summand and the inclusion
followed by the involution on the graph summand. -/
noncomputable def relationSource : relationScheme V ⟶ U := coprod.desc (𝟙 U) (V.ι ≫ a)

/-- On the diagonal summand `U` the target projection is the identity. -/
@[simp]
theorem inl_comp_relationTarget :
    (coprod.inl : U ⟶ relationScheme V) ≫ relationTarget V = 𝟙 U := coprod.inl_desc _ _

/-- On the graph summand the target projection is the inclusion of `V`. -/
@[simp]
theorem inr_comp_relationTarget :
    (coprod.inr : V.toScheme ⟶ relationScheme V) ≫ relationTarget V = V.ι :=
  coprod.inr_desc _ _

/-- On the diagonal summand `U` the source projection is the identity. -/
@[simp]
theorem inl_comp_relationSource :
    (coprod.inl : U ⟶ relationScheme V) ≫ relationSource V a = 𝟙 U := coprod.inl_desc _ _

/-- On the graph summand the source projection is the inclusion of `V` followed by `a`. -/
@[simp]
theorem inr_comp_relationSource :
    (coprod.inr : V.toScheme ⟶ relationScheme V) ≫ relationSource V a = V.ι ≫ a :=
  coprod.inr_desc _ _

/-- The target projection of the relation is étale: it is the identity on one summand and an
open immersion on the other. -/
theorem etale_relationTarget : Etale (relationTarget V) :=
  etale_coprod _ _ inferInstance inferInstance

/-- The source projection of the relation is étale: it is the identity on one summand and an
open immersion followed by an automorphism on the other. -/
theorem etale_relationSource [IsIso a] : Etale (relationSource V a) :=
  etale_coprod _ _ inferInstance inferInstance

/-- **The relation of a free involution on an open subscheme is an equivalence relation**, as
a pair of morphisms of schemes.

The hypotheses are that `a` is an involution, that it preserves `V` — in the form of an
endomorphism `b` of `V` lifting `V.ι ≫ a` — and that it acts freely on `V`. -/
theorem isEquivalenceRelation_relation (hinv : a ≫ a = 𝟙 U)
    (b : V.toScheme ⟶ V.toScheme) (hb : b ≫ V.ι = V.ι ≫ a)
    (hfree : ∀ {T : Scheme.{u}} (f : T ⟶ V.toScheme),
      f ≫ V.ι = f ≫ V.ι ≫ a → IsEmpty T) :
    IsEquivalenceRelation (relationTarget V) (relationSource V a) :=
  isEquivalenceRelation_coprod_desc_of_free_involution V.ι a hinv b hb fun {T} f hf => by
    have : IsEmpty T := hfree f hf
    exact ⟨fun _ _ => isInitialOfIsEmpty.hom_ext _ _⟩

/-- A scheme as an object over the terminal scheme. -/
noncomputable abbrev overTerminal (X : Scheme.{u}) : Over (⊤_ Scheme.{u}) :=
  Over.mk (terminal.from X)

/-- **The relation of a free involution on an open subscheme, as a pre-relation over the
terminal scheme.** This is the datum Stacks 022P attaches to a relation: a morphism from the
relation scheme to the self-product of `U`. -/
noncomputable def preRelation :
    Stacks.Groupoids.PreRelation (overTerminal (relationScheme V)) (overTerminal U) :=
  prod.lift (Over.homMk (relationTarget V) (by simp))
    (Over.homMk (relationSource V a) (by simp))

/-- The target of `preRelation V a` is `relationTarget V`, as a morphism over the terminal
scheme. -/
@[simp]
theorem preRelation_target :
    (preRelation V a).target = Over.homMk (relationTarget V) (by simp) :=
  prod.lift_fst _ _

/-- The source of `preRelation V a` is `relationSource V a`, as a morphism over the terminal
scheme. -/
@[simp]
theorem preRelation_source :
    (preRelation V a).source = Over.homMk (relationSource V a) (by simp) :=
  prod.lift_snd _ _

/-- **The relation of a free involution on an open subscheme is an étale equivalence
relation** over the terminal scheme.

The equivalence-relation property is `isEquivalenceRelation_relation`, transported from the
category of schemes along the inverse of `CategoryTheory.Over.equivalenceOfIsTerminal`. -/
theorem isEtaleEquivalenceRelation_preRelation [IsIso a] (hinv : a ≫ a = 𝟙 U)
    (b : V.toScheme ⟶ V.toScheme) (hb : b ≫ V.ι = V.ι ≫ a)
    (hfree : ∀ {T : Scheme.{u}} (f : T ⟶ V.toScheme),
      f ≫ V.ι = f ≫ V.ι ≫ a → IsEmpty T) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (preRelation V a) where
  isEquivalenceRelation := by
    obtain ⟨E⟩ := (isEquivalenceRelation_relation V a hinv b hb
      hfree).nonempty_equivalenceRelation
    let F := (Over.equivalenceOfIsTerminal (terminalIsTerminal (C := Scheme.{u}))).inverse
    have : JointlyMono₂ (F.map (relationTarget V)) (F.map (relationSource V a)) := ⟨by
      intro T f g ht hs
      refine Over.OverMorphism.ext (E.right_cancellation f.left g.left ?_ ?_)
      · exact congrArg (fun z => Over.Hom.left z) ht
      · exact congrArg (fun z => Over.Hom.left z) hs⟩
    rw [preRelation_target, preRelation_source]
    exact EquivalenceRelation.isEquivalenceRelation
      { __ := E.toReflexiveRelation.map F
        __ := E.toSymmetricRelation.map F
        __ := E.toTransitiveRelation.map F }
  etale_source := by
    rw [preRelation_source]
    exact etale_relationSource V a
  etale_target := by
    rw [preRelation_target]
    exact etale_relationTarget V

/-- The relation scheme of a free involution on an open subscheme is quasi-compact as soon as
`U` and `V` are: it is their coproduct. -/
theorem compactSpace_relationScheme [CompactSpace U] [CompactSpace V.toScheme] :
    CompactSpace (relationScheme V) :=
  (AlgebraicGeometry.coprodMk U V.toScheme).compactSpace

/-- **The source projection of the relation is quasi-compact** when `U` and `V` are
quasi-compact and `U` is quasi-separated. -/
theorem quasiCompact_relationSource [CompactSpace U] [CompactSpace V.toScheme]
    [QuasiSeparatedSpace U] : QuasiCompact (relationSource V a) :=
  have := compactSpace_relationScheme V
  quasiCompact_of_compactSpace _

end AlgebraicGeometry.OpenInvolution

end
