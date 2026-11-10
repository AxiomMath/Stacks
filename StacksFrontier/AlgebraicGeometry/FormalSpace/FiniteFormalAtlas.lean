module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproductEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FiniteCoproducts

/-!
# A finite formal atlas, and the equivalence of conditions (2) and (3) of Stacks 0AJ9

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AJ9** states that three
conditions on a formal algebraic space `X` over `S` are equivalent:

1. the reduction of `X` is a quasi-compact algebraic space,
2. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM with a finite index type,
3. there is a morphism `Y ⟶ X` representable by algebraic spaces, étale and surjective whose
   source `Y` is an affine formal algebraic space.

This file defines condition (2), `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas`, and
proves it equivalent to condition (3),
`AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`. Both implications are a matter of
coproducts alone: (3) ⇒ (2) reads the single morphism of condition (3) as a covering indexed by
a one-point type, and (2) ⇒ (3) takes `Y` to be the coproduct of the finitely many members of
the covering. Neither mentions a reduction of `X`, which is why they are separated from the
implications relating condition (1) — those, and the equivalence of all three, are in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria`, which imports this file.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas`: condition (2) of Stacks 0AJ9.
* `AlgebraicGeometry.FormalSpace.FiniteCoproductsAffineFormal`,
  `AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`: the two assertions about
  coproducts which the implication (2) ⇒ (3) rests on. Both are proved below,
  `AlgebraicGeometry.FormalSpace.finiteCoproductsAffineFormal` and
  `AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale'`.

## Main results

* `AlgebraicGeometry.FormalSpace.finiteCoproductsAffineFormal`: a coproduct of finitely many
  affine formal algebraic spaces is an affine formal algebraic space -- the affineness half of
  the implication (2) ⇒ (3).
* `AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale'`: a morphism out of a coproduct
  of finitely many fppf sheaves is representable by algebraic spaces and étale as soon as its
  restriction to each summand is -- the étale half of the implication (2) ⇒ (3).
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace.hasFiniteFormalAtlas`:
  **Stacks 0AJ9**, the implication (3) ⇒ (2).
* `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas.isQuasiCompactSpace`:
  **Stacks 0AJ9**, the implication (2) ⇒ (3).

## What is assumed

Nothing: both implications are proved here, with no hypothesis beyond the condition being
converted.

The index type is finite in both assertions about coproducts, because the big fppf site of `S`
is closed under finite coproducts only, so an infinite coproduct of algebraic spaces need have
no atlas inside the site.

The affineness assertion is `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma`
of `StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct`: a presentation of the
coproduct is formed over the product of the index preorders of presentations of the summands,
its stage at a point `λ` of that product being the coproduct `∐ᵢ (D i)(λ i)` of stages.

## Implementation notes

Condition (2) repeats the set-theoretic condition of Stacks 0AIS, since Definition 0AIM asks
for it, so `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas` is exactly
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` with a finite index type for the atlas.
The index type lives in `Type (u + 1)`, the universe in which the sheaves of a presentation
live, as it does in Definition 0AIM.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (2) of Stacks 0AJ9 -/

/-- **Stacks 0AJ9, condition (2).** An fppf sheaf on the big fppf site of `S` *has a finite
formal atlas* when it satisfies the set-theoretic condition of Stacks 0AIS and admits an atlas
as in Definition 0AIM, by finitely many affine formal algebraic spaces: a family of maps into
it indexed by a finite type, whose sources are affine formal algebraic spaces, each of which
is representable by algebraic spaces and étale, and whose induced map from the coproduct is a
surjection of sheaves. -/
abbrev HasFiniteFormalAtlas' (X : FppfSheaf B S hS) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  SatisfiesSetTheoreticCondition B S hS X ∧
    ∃ (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X),
      Finite I ∧
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
      (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) ∧
      Sheaf.IsLocallySurjective (Sigma.desc f)

/-- A sheaf with a finite formal atlas is a formal algebraic space over `S`: forgetting the
finiteness of the index type leaves exactly the data of Definition 0AIM. -/
theorem HasFiniteFormalAtlas.isFormalAlgebraicSpace' {X : FppfSheaf B S hS}
    (h : HasFiniteFormalAtlas' B S hS X) : IsFormalAlgebraicSpace B S hS X := by
  obtain ⟨hset, I, Xi, f, -, haffine, hetale, hsurjective⟩ := h
  exact ⟨hset, I, Xi, f, haffine, hetale, hsurjective⟩

/-! ### The auxiliary assertions about coproducts -/

/-- The assertion that a coproduct of finitely many affine formal algebraic spaces over `S` is
an affine formal algebraic space over `S`. -/
abbrev FiniteCoproductsAffineFormal' : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∀ (I : Type (u + 1)) (Z : I → FppfSheaf B S hS), Finite I →
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i)) →
    IsAffineFormalAlgebraicSpace B S hS (∐ Z)

/-- **A coproduct of finitely many affine formal algebraic spaces over `S` is an affine formal
algebraic space over `S`.** This is `FiniteCoproductsAffineFormal`, the assertion the
implication (2) ⇒ (3) of Stacks 0AJ9 rests on.

A presentation of the coproduct is formed over the product of the index preorders of
presentations of the summands, with the coproduct `∐ᵢ (D i)(λ i)` of stages at a point `λ` of
that product; this is
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma`. -/
theorem finiteCoproductsAffineFormal' : FiniteCoproductsAffineFormal' B S hS := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro I Z hI hZ
  exact isAffineFormalAlgebraicSpace_sigma B S hS Z hZ

/-- The assertion that a morphism out of a coproduct of finitely many fppf sheaves is
representable by algebraic spaces and étale as soon as its restriction to every summand is. -/
abbrev CoproductsRepresentableEtale' : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∀ (I : Type (u + 1)) (Z : I → FppfSheaf B S hS) (W : FppfSheaf B S hS) (g : ∀ i, Z i ⟶ W),
    Finite I →
    (∀ i, ∃ hgi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g i).hom hgi) →
    ∃ hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (Sigma.desc g).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (Sigma.desc g).hom hg

/-- **A morphism out of a coproduct of finitely many fppf sheaves is representable by algebraic
spaces and étale as soon as its restriction to every summand is.** This is
`CoproductsRepresentableEtale`, the étale assertion the implication (2) ⇒ (3) of Stacks 0AJ9
rests on.

The base change along a scheme-valued point of the target decomposes as the coproduct of the
base changes of the restrictions, each of which is an algebraic space and étale over the point;
the coproduct of those is an algebraic space by Stacks 02WQ in this value universe and is étale
over the point because étaleness of a morphism out of a coproduct may be checked on the
summands. All of that is
`AlgebraicGeometry.Space.isRepresentableEtale_of_isColimit_cofan`; what is supplied here is the
coproduct cocone and the coproduct of the chosen atlases inside the site, which exists because
the index type is finite. -/
theorem coproductsRepresentableEtale' : CoproductsRepresentableEtale' B S hS := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro I Z W g hfinite hetale
  refine Space.isRepresentableEtale_of_isColimit_cofan.{u + 1, u + 1, u} B S hS (Sigma.ι Z)
    (coproductIsCoproduct Z) (Sigma.desc g) (fun U => ⟨∐ U, Sigma.ι U, ⟨coproductIsCoproduct U⟩⟩)
    fun i => ?_
  rw [Sigma.ι_comp_desc]
  exact hetale i

/-! ### The implication (3) ⇒ (2) -/

/-- **Stacks 0AJ9, the implication (3) ⇒ (2).** A quasi-compact formal algebraic space over
`S` has a finite formal atlas: the one affine formal algebraic space surjecting onto it is an
atlas as in Definition 0AIM indexed by a one-point type, the induced map from the coproduct
over that type being the given map up to the coproduct inclusion, which is a split
epimorphism. -/
@[stacks 0AJ9 "the implication (3) ⇒ (2)"]
theorem IsQuasiCompactSpace.hasFiniteFormalAtlas' {X : FppfSheaf B S hS}
    (h : IsQuasiCompactSpace B S hS X) : HasFiniteFormalAtlas' B S hS X := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, Z, c, haffine, hetale, hsurjective⟩ := h
  refine ⟨hset, PUnit.{u + 2}, fun _ ↦ Z, fun _ ↦ c, inferInstance, fun _ ↦ haffine,
    fun _ ↦ hetale, ?_⟩
  have : Epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit ≫
      Sigma.desc (fun _ : PUnit.{u + 2} ↦ c)) := by
    rw [Sigma.ι_comp_desc]
    exact (Sheaf.isLocallySurjective_iff_epi c).mp hsurjective
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr
    (epi_of_epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit) _)

/-! ### The implication (2) ⇒ (3) -/

/-- **Stacks 0AJ9, the implication (2) ⇒ (3).** A sheaf with a finite formal atlas is a
quasi-compact formal algebraic space over `S`: the coproduct of the finitely many members of
the atlas is an affine formal algebraic space, and the induced morphism from it is
representable by algebraic spaces, étale and a surjection of sheaves. -/
@[stacks 0AJ9 "the implication (2) ⇒ (3)"]
theorem HasFiniteFormalAtlas.isQuasiCompactSpace'
    {X : FppfSheaf B S hS} (h : HasFiniteFormalAtlas' B S hS X) :
    IsQuasiCompactSpace B S hS X := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, I, Xi, f, hfinite, haffine, hetale, hsurjective⟩ := h
  exact ⟨hset, ∐ Xi, Sigma.desc f, finiteCoproductsAffineFormal' B S hS I Xi hfinite haffine,
    coproductsRepresentableEtale' B S hS I Xi X f hfinite hetale, hsurjective⟩

end AlgebraicGeometry.FormalSpace

end
