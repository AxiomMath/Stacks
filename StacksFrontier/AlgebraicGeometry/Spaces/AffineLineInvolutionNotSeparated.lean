module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion

/-!
# The involution relation on the affine line is not a closed immersion

Let `k` be a field, let `U = 𝐀¹_k` and let `R = Δ ⨿ Γ°` be the relation scheme of
`AlgebraicGeometry.AffineLineInvolution.relationScheme`: the disjoint union of a copy of the
affine line, carrying the diagonal, and of the punctured affine line, carrying the graph of
negation. **The pre-relation `j : R ⟶ U ×_k U` is not a closed immersion.**

This is the geometric content of the assertion that the quotient `U/R` is not separated: for a
quotient which is an algebraic space the relation is the kernel pair of the quotient map
(Stacks 02WV), so the relation is a base change of the diagonal of `U/R` and inherits every
property of it which is stable under base change.

The argument is the restriction to the second summand. On `Γ°` the pre-relation is the graph
of negation restricted to the puncture, which factors as the open immersion
`Γ° ⟶ U` followed by the graph `U ⟶ U ×_k U` of negation. The graph is a split
monomorphism — `Limits.prod.fst` retracts it — hence a separated morphism, and the inclusion of
a summand of a coproduct is a closed immersion; so if `j` were a closed immersion, the open
immersion `Γ° ⟶ U` would be one too, by
`AlgebraicGeometry.IsClosedImmersion.of_comp`. Its range is then a closed subset of `|U|`,
and it is a nonempty open subset of an irreducible space, hence dense; so it is all of `|U|`.
That is refuted by the origin: the coordinate pulls back to `0` along the zero section, so the
zero section has empty preimage in the puncture, while it has nonempty preimage in `U`.

Only the restriction to the second summand enters, so the argument proves more: *no* morphism
out of `R` whose restriction to `Γ°` factors through a separated morphism from `U` is a closed
immersion.

## Main results

* `AlgebraicGeometry.isClosedImmersion_coprod_inr`: the second inclusion of a binary coproduct
  of schemes is a closed immersion, the counterpart of
  `AlgebraicGeometry.isClosedImmersion_coprod_inl`.
* `AlgebraicGeometry.left_coprod_inr`: a property of scheme morphisms which respects
  isomorphisms holds for the underlying morphism of the second coproduct inclusion in
  `CategoryTheory.Over S` as soon as it holds for the second coproduct inclusion of the
  underlying schemes.
* `AlgebraicGeometry.AffineLineInvolution.not_isClosedImmersion_puncturedAffineLineOpen_ι`:
  the inclusion of the punctured affine line into the affine line is not a closed immersion.
* `AlgebraicGeometry.AffineLineInvolution.not_isClosedImmersion_of_inr_left_comp_eq`: a
  morphism out of the relation scheme of Stacks 02Z1 whose restriction to the second summand
  factors as the inclusion of the puncture followed by a separated morphism from the affine
  line is not a closed immersion.
* `AlgebraicGeometry.AffineLineInvolution.not_isClosedImmersion_involutionRelation`: the
  pre-relation of Stacks 02Z1 is not a closed immersion.

## Implementation notes

Nothing here carries the tag 02Z1. The assertion of that tag is about the *quotient* — that
`U/R` is not locally separated, and in particular not separated — and passing from the relation
to the quotient needs the kernel-pair description of Stacks 02WV, which is not used here.

The statements are about the morphism of schemes underlying the pre-relation rather than about
the pre-relation itself, because that is the form in which the separation axioms of a morphism
of algebraic spaces are tested: they ask for a property of the morphism of schemes representing
a base change.

Irreducibility of the affine line is not found by instance search through the
`CategoryTheory.Over` wrapper of `AlgebraicGeometry.AffineLineInvolution.affineLine`, so it is
named here as `AlgebraicGeometry.AffineLineInvolution.irreducibleSpace_affineLine`.

## References

* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism property which respects isomorphisms holds for `h` if it holds for `f` and
`f ≫ g = h` with `g` an isomorphism. -/
private theorem of_comp_isIso_eq {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso g] (e : f ≫ g = h)
    (hf : P f) : P h :=
  e ▸ MorphismProperty.RespectsIso.postcomp P g f hf

/-- The second inclusion of a scheme into a binary coproduct is a closed immersion. This is
`AlgebraicGeometry.isClosedImmersion_coprod_inl` transported along the braiding of the
coproduct. -/
theorem isClosedImmersion_coprod_inr (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inr : Y ⟶ X ⨿ Y) :=
  of_comp_isIso_eq (P := @IsClosedImmersion.{u})
    (g := (coprod.braiding Y X).hom) (coprod.inl_desc _ _) (isClosedImmersion_coprod_inl Y X)

/-- A morphism property which respects isomorphisms holds for the underlying morphism of the
second coproduct inclusion in `CategoryTheory.Over S` as soon as it holds for the second
coproduct inclusion of the underlying schemes. This is the counterpart for the inclusions of
`AlgebraicGeometry.left_coprod_desc`. -/
theorem left_coprod_inr {S : Scheme.{u}} (X Y : Over S) (P : MorphismProperty Scheme.{u})
    (hP : P.RespectsIso) (h : P (coprod.inr : Y.left ⟶ X.left ⨿ Y.left)) :
    P ((coprod.inr : Y ⟶ X ⨿ Y).left) :=
  have : IsIso (coprodComparison (Over.forget S) X Y) :=
    (PreservesColimitPair.iso (Over.forget S) X Y).isIso_hom
  haveI := hP
  of_comp_isIso_eq (coprodComparison_inr (Over.forget S) X Y) h

namespace AffineLineInvolution

variable (k : Type u) [Field k]

/-! ### Constant sections of the affine line -/

/-- The section of the affine line over `Spec k` with constant coordinate `a`. -/
noncomputable def constSection (a : Γ(Spec (CommRingCat.of k), ⊤)) :
    Spec (CommRingCat.of k) ⟶ (affineLine k).left :=
  AffineSpace.homOfVector (𝟙 _) (fun _ : PUnit.{u + 1} => a)

/-- The constant section with coordinate `a` pulls the coordinate function of the affine line
back to `a`. -/
@[simp]
theorem constSection_appTop_coord (a : Γ(Spec (CommRingCat.of k), ⊤)) :
    (constSection k a).appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = a :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The preimage of the punctured affine line under the constant section with coordinate `a`
is the basic open of `a`. -/
theorem preimage_puncturedAffineLineOpen (a : Γ(Spec (CommRingCat.of k), ⊤)) :
    (constSection k a) ⁻¹ᵁ (puncturedAffineLineOpen k)
      = (Spec (CommRingCat.of k)).basicOpen a := by
  rw [show puncturedAffineLineOpen k
        = (affineLine k).left.basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit) from rfl,
    Scheme.preimage_basicOpen]
  exact congrArg _ (constSection_appTop_coord k a)

/-- The affine line over a field is irreducible. -/
theorem irreducibleSpace_affineLine : IrreducibleSpace (affineLine k).left := by
  change IrreducibleSpace (AffineSpace PUnit.{u + 1} (Spec (.of k)))
  infer_instance

/-! ### The puncture is not closed -/

/-- **The inclusion of the punctured affine line into the affine line is not a closed
immersion.** Its range is a nonempty open subset of an irreducible space, hence dense; were it
also closed it would be everything, which the origin refutes. -/
theorem not_isClosedImmersion_puncturedAffineLineOpen_ι :
    ¬ IsClosedImmersion (puncturedAffineLineOpen k).ι := by
  intro h
  have hirr := irreducibleSpace_affineLine k
  set U : (affineLine k).left.Opens := puncturedAffineLineOpen k with hU
  have hclosed : IsClosed ((U : (affineLine k).left.Opens) : Set (affineLine k).left) := by
    rw [← Scheme.Opens.range_ι]
    exact (Scheme.Hom.isClosedEmbedding U.ι).isClosed_range
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of k)))
  have hone : (constSection k 1) ⁻¹ᵁ U = ⊤ := by
    rw [hU, preimage_puncturedAffineLineOpen, Scheme.basicOpen_one]
  have hne : ((U : (affineLine k).left.Opens) : Set (affineLine k).left).Nonempty := by
    refine ⟨(constSection k 1).base x, ?_⟩
    have hx : x ∈ (constSection k 1) ⁻¹ᵁ U := by rw [hone]; trivial
    exact hx
  have hdense : Dense ((U : (affineLine k).left.Opens) : Set (affineLine k).left) := by
    rw [dense_iff_inter_open]
    intro V hV hVne
    have hint := (IrreducibleSpace.isIrreducible_univ (affineLine k).left).2 V U hV U.2
      (by simpa using hVne) (by simpa using hne)
    simpa using hint
  have htop : U = ⊤ := by
    refine TopologicalSpace.Opens.ext ?_
    simpa using (hclosed.closure_eq).symm.trans hdense.closure_eq
  have hzero : (constSection k 0) ⁻¹ᵁ U = ⊥ := by
    rw [hU, preimage_puncturedAffineLineOpen, Scheme.basicOpen_zero]
  rw [htop] at hzero
  have hx : x ∈ (⊥ : (Spec (CommRingCat.of k)).Opens) := by
    rw [← hzero]; trivial
  simp at hx

/-! ### The relation is not a closed immersion -/

/-- The graph of negation on the affine line, as a morphism to the product over the ground
field. -/
noncomputable abbrev negGraph : affineLine k ⟶ affineLine k ⨯ affineLine k :=
  prod.lift (𝟙 (affineLine k)) (affineLineNeg k)

/-- On the second summand of the relation scheme the pre-relation of Stacks 02Z1 is the graph
of negation restricted to the puncture. -/
theorem inr_comp_involutionRelation :
    (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) ≫ involutionRelation k
      = puncturedAffineLineInclusion k ≫ negGraph k := by
  refine prod.hom_ext ?_ ?_ <;>
    simp [involutionRelation, negGraph, coprod.inr_desc]

/-- The graph of negation is a split monomorphism, retracted by the first projection; so its
underlying morphism of schemes is a monomorphism. -/
theorem isSplitMono_negGraph_left : IsSplitMono ((negGraph k).left) :=
  ⟨⟨{ retraction := (prod.fst : affineLine k ⨯ affineLine k ⟶ affineLine k).left
      id := by rw [← Over.comp_left, prod.lift_fst, Over.id_left] }⟩⟩

/-- **A morphism out of the relation scheme of Stacks 02Z1 which restricts on the second
summand to the inclusion of the puncture followed by a separated morphism from the affine line
is not a closed immersion.** Were it one, so would be its restriction to the second summand,
the inclusion of a summand of a coproduct being a closed immersion; and then the inclusion of
the punctured affine line would be a closed immersion too, by
`AlgebraicGeometry.IsClosedImmersion.of_comp`. -/
theorem not_isClosedImmersion_of_inr_left_comp_eq {Z : Scheme.{u}}
    (m : (relationScheme k).left ⟶ Z) (n : (affineLine k).left ⟶ Z) (hn : IsSeparated n)
    (h : (coprod.inr : puncturedAffineLine k ⟶ relationScheme k).left ≫ m =
      (puncturedAffineLineOpen k).ι ≫ n) :
    ¬ IsClosedImmersion m := by
  intro hm
  have hinr : IsClosedImmersion ((coprod.inr :
      puncturedAffineLine k ⟶ relationScheme k).left) :=
    left_coprod_inr (affineLine k) (puncturedAffineLine k)
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      IsClosedImmersion.respectsIso (isClosedImmersion_coprod_inr _ _)
  have hcomp : IsClosedImmersion ((puncturedAffineLineOpen k).ι ≫ n) := by
    rw [← h]
    exact @IsClosedImmersion.comp _ _ _ _ _ hinr hm
  exact not_isClosedImmersion_puncturedAffineLineOpen_ι k
    (@IsClosedImmersion.of_comp _ _ _ (puncturedAffineLineOpen k).ι n hcomp hn)

/-- **The pre-relation of Stacks 02Z1 is not a closed immersion.** Restricting to the second
summand of the relation scheme would make the inclusion of the punctured affine line a closed
immersion, which it is not. -/
theorem not_isClosedImmersion_involutionRelation :
    ¬ IsClosedImmersion ((involutionRelation k).left) := by
  have : Mono ((negGraph k).left) := (isSplitMono_negGraph_left k).mono
  refine not_isClosedImmersion_of_inr_left_comp_eq k ((involutionRelation k).left)
    ((negGraph k).left) inferInstance ?_
  rw [← Over.comp_left, inr_comp_involutionRelation, Over.comp_left,
    puncturedAffineLineInclusion_left]

end AffineLineInvolution

end AlgebraicGeometry

end
