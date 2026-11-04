module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleUnique

/-!
# Relative Proj as a functor: the comparison of two strictly equivalent quadruples, as data

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN) and `d` an integer. Strict
equivalence of two quadruples over a test scheme (Section 01NS) is recorded as an *existential*
statement, `...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent`, and
`...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_witness_unique` says that the witness it
asserts the existence of is unique. This file turns that pair of facts into **data**: a named
isomorphism `Quadruple.witness` attached to a proof of strict equivalence, and the three
groupoid laws it satisfies.

## Why the laws are free

`witness` is extracted by choice, so by itself it satisfies no identity. Uniqueness supplies
every identity at once: two comparisons of the same pair of quadruples are equal, so a composite
of comparisons, which is again a comparison, must be *the* comparison. That is
`Quadruple.witness_trans`, and `Quadruple.witness_refl` and `Quadruple.witness_symm` are the
same argument for the identity and for the inverse.

The three laws are exactly the data a glueing argument consumes. For a family of quadruples given
on the members of an open covering of a test scheme, pairwise strictly equivalent on the
overlaps, `witness` gives an isomorphism of the invertible modules over each overlap,
`witness_trans` is the cocycle condition on the triple overlaps and `witness_refl` the unit
condition — none of which has to be imposed as a hypothesis, because the comparisons are not
chosen but determined.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.witness`: **the canonical
  isomorphism `β : L ≅ L'` of the invertible modules of two strictly equivalent quadruples.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.laurentWitness`: the accompanying
  isomorphism `γ` of their Laurent algebras.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.witness_eq` and
  `...Quadruple.laurentWitness_eq`: **any witness of the strict equivalence is the canonical
  one**, which is the only way these definitions are ever used.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.twisting_app_comp_laurentWitness`:
  the canonical comparison carries `ψ` to `ψ'` in every integral degree.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.witness_refl`,
  `...Quadruple.witness_trans`, `...Quadruple.witness_symm`: **the comparisons compose, and the
  comparison of a quadruple with itself is the identity.**

## Implementation notes

`witness` and `laurentWitness` take the *proof* of strict equivalence as an argument, and are
defined from it by `Exists.choose`. That is harmless: strict equivalence is a `Prop`, so any two
proofs of it are equal, and the comparison therefore depends only on the two quadruples. It is
also why the statements below quantify over the proofs separately — `witness_trans` takes three
unrelated proofs rather than deriving the third from the first two — without that making them
weaker.

## No tag is claimed

Section 01NS states strict equivalence as an existential; that the witness is canonical is
`...Quadruple.strictlyEquivalent_witness_unique`, which already carries what there is to carry.
Nothing new about the source is proved here, only packaged.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {P Q R : Quadruple f A d}

/-- **The canonical isomorphism of the invertible modules of two strictly equivalent
quadruples.** Section 01NS asserts that some isomorphism `β : L ≅ L'` carries `ψ` to `ψ'`; this
is that isomorphism, which is unique by
`...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_witness_unique`. -/
def witness (h : StrictlyEquivalent P Q) : P.L ≅ Q.L := h.choose

/-- **The canonical isomorphism of the Laurent algebras of two strictly equivalent
quadruples**, whose degree-one component is `Quadruple.witness`. -/
def laurentWitness (h : StrictlyEquivalent P Q) : laurent P.L ≅ laurent Q.L :=
  h.choose_spec.choose

/-- The degree-one component of the canonical isomorphism of the Laurent algebras is the
canonical isomorphism of the invertible modules, read through the identification `L^{⊗ 1} = L`
of Tag 01CU. -/
theorem laurentWitness_app_one (h : StrictlyEquivalent P Q) :
    (laurentWitness h).hom.app 1 = (pieceOneIso (witness h)).hom :=
  h.choose_spec.choose_spec.1

/-- **The canonical comparison carries `ψ` to `ψ'` in every integral degree.** -/
theorem twisting_app_comp_laurentWitness (h : StrictlyEquivalent P Q) (n : ℤ) :
    P.twisting.app n ≫ (laurentWitness h).hom.app n = Q.twisting.app n :=
  h.choose_spec.choose_spec.2 n

/-- **Any witness of a strict equivalence is the canonical one.** This is how `witness` is
consumed: a comparison built by hand is identified with `witness`, and thereby with every other
comparison of the same two quadruples. -/
theorem witness_eq (h : StrictlyEquivalent P Q) {β : P.L ≅ Q.L}
    {γ : laurent P.L ≅ laurent Q.L} (h1 : γ.hom.app 1 = (pieceOneIso β).hom)
    (hψ : ∀ n : ℤ, P.twisting.app n ≫ γ.hom.app n = Q.twisting.app n) : witness h = β :=
  (strictlyEquivalent_witness_unique (laurentWitness_app_one h)
    (twisting_app_comp_laurentWitness h) h1 hψ).1

/-- **Any witness of a strict equivalence is the canonical one**, in the Laurent-algebra
component. -/
theorem laurentWitness_eq (h : StrictlyEquivalent P Q) {β : P.L ≅ Q.L}
    {γ : laurent P.L ≅ laurent Q.L} (h1 : γ.hom.app 1 = (pieceOneIso β).hom)
    (hψ : ∀ n : ℤ, P.twisting.app n ≫ γ.hom.app n = Q.twisting.app n) : laurentWitness h = γ :=
  (strictlyEquivalent_witness_unique (laurentWitness_app_one h)
    (twisting_app_comp_laurentWitness h) h1 hψ).2

/-- **The canonical comparison of a quadruple with itself is the identity.** -/
@[simp] theorem witness_refl (h : StrictlyEquivalent P P) : witness h = Iso.refl P.L :=
  witness_eq h (γ := Iso.refl (laurent P.L)) (by simp) (by simp)

/-- **The canonical comparison of the Laurent algebras of a quadruple with itself is the
identity.** -/
@[simp] theorem laurentWitness_refl (h : StrictlyEquivalent P P) :
    laurentWitness h = Iso.refl (laurent P.L) :=
  laurentWitness_eq h (β := Iso.refl P.L) (by simp) (by simp)

/-- **The canonical comparisons compose.** For a family of quadruples on the members of an open
covering which are pairwise strictly equivalent on the overlaps, this is the cocycle condition
on the triple overlaps, and it holds with no hypothesis beyond the pairwise equivalences. -/
theorem witness_trans (h : StrictlyEquivalent P Q) (h' : StrictlyEquivalent Q R)
    (h'' : StrictlyEquivalent P R) : witness h ≪≫ witness h' = witness h'' :=
  eq_trans_of_witness (laurentWitness_app_one h) (twisting_app_comp_laurentWitness h)
    (laurentWitness_app_one h') (twisting_app_comp_laurentWitness h')
    (laurentWitness_app_one h'') (twisting_app_comp_laurentWitness h'')

/-- **The canonical comparison in the opposite direction is the inverse.** -/
theorem witness_symm (h : StrictlyEquivalent P Q) (h' : StrictlyEquivalent Q P) :
    witness h' = (witness h).symm := by
  have hid : witness h ≪≫ witness h' = Iso.refl P.L :=
    (witness_trans h h' (strictlyEquivalent_equivalence.refl P)).trans (witness_refl _)
  refine Iso.ext ?_
  rw [← Category.id_comp (witness h').hom, ← (witness h).inv_hom_id, Category.assoc]
  exact congrArg _ (congrArg Iso.hom hid)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

end
