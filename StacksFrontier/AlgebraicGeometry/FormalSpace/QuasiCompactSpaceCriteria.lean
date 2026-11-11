module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# Criteria for a formal algebraic space to be quasi-compact

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. **Stacks 0AJ9** states that the following three conditions on `X` are equivalent:

1. the reduction of `X` is a quasi-compact algebraic space,
2. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM with a finite index type,
3. there is a morphism `Y ⟶ X` representable by algebraic spaces, étale and surjective whose
   source `Y` is an affine formal algebraic space.

Condition (3) is `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`, condition (2) is
`AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas`, and condition (1) is quasi-compactness
of a reduction of `X` in the sense of Stacks 03E3.

The implication (3) ⇒ (2) needs nothing: the single morphism of condition (3) is a covering as
in Definition 0AIM indexed by a one-point type, which is finite. The implication (3) ⇒ (1)
goes through the reduction `Y_red` of the affine formal algebraic space `Y`: the composite
`Y_red ⟶ Y ⟶ X` comes from a reduced algebraic space, so it factors through the reduction of
`X`, the resulting morphism `Y_red ⟶ X_red` is surjective and étale because `Y ⟶ X` is, and
`Y_red` is quasi-compact because it is the reduction of a stage of the presentation of `Y`;
composing a quasi-compact surjective étale chart of `Y_red` with `Y_red ⟶ X_red` is then a
quasi-compact surjective étale chart of `X_red`. The implication (1) ⇒ (2) shrinks a covering
as in Definition 0AIM to a finite one using quasi-compactness of the reduction, and the
implication (2) ⇒ (3) takes `Y` to be the coproduct of the finitely many members of such a
covering, which is again an affine formal algebraic space.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas`: condition (2) of Stacks 0AJ9.
* `AlgebraicGeometry.FormalSpace.AffineReductionsQuasiCompact`,
  `AlgebraicGeometry.FormalSpace.ReductionsOfEtaleSurjectionsEtaleSurjective`,
  `AlgebraicGeometry.FormalSpace.FiniteCoproductsAffineFormal`,
  `AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`: the four auxiliary assertions
  about reductions and about coproducts which the equivalence rests on. The third of them is
  a theorem of this library, `finiteCoproductsAffineFormal` below; the other three are
  hypotheses here and are proved in other files of the library.

## Main results

* `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace.hasFiniteFormalAtlas`: the implication
  (3) ⇒ (2) of Stacks 0AJ9.
* `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas.isQuasiCompactSpace`: the implication
  (2) ⇒ (3).
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction`: the
  implication (3) ⇒ (1), on the hypotheses `hAffineReduction` and `hReductionEtaleSurjective`.
* `AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace`: the equivalence of the three
  conditions on the hypotheses below; the unconditional form is
  `AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace_unconditional`.

## The hypotheses of the declarations below

The declarations of this file take steps of the proof of Stacks 0AJ9 as hypotheses. The
equivalence of the three conditions with nothing assumed beyond the source's hypotheses is
`AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace_unconditional`, for every reduction
`i : Xred ⟶ X` of `X`. A reduction exists for every formal algebraic space by
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace` (Stacks 0AIN), and
condition (1) is phrased here, as Stacks 0GB8 and Stacks 0CB9 are in this library, through a
reduction `i : Xred ⟶ X`, which needs no choice.

Three assertions are hypotheses of `tfae_isQuasiCompactSpace`; a fourth,
`FiniteCoproductsAffineFormal`, is no longer one, being proved here as
`AlgebraicGeometry.FormalSpace.finiteCoproductsAffineFormal`.

* `hAffineReduction`, of the shape `AffineReductionsQuasiCompact`, says that a reduction of an
  affine formal algebraic space is a quasi-compact algebraic space. This is the content of the
  affine case of Stacks 0AIN beyond what
  `AlgebraicGeometry.FormalSpace.exists_isReduction_of_isAffineFormalAlgebraicSpace` records,
  namely that the reduction produced there is the reduction of a stage of the presentation and
  so is an affine scheme.
* `hReductionEtaleSurjective`, of the shape
  `ReductionsOfEtaleSurjectionsEtaleSurjective`, says that the morphism of reductions induced
  by a morphism of formal algebraic spaces which is representable by algebraic spaces, étale
  and surjective is itself surjective and étale. Surjectivity alone is Stacks 0GB8, which is
  available as
  `AlgebraicGeometry.FormalSpace.hasPropertyULift_isSurjectiveULift_iff_isSurjectiveULift_red`;
  étaleness is the step of the proof of Stacks 0AIN which identifies a reduction of a fibre
  product `Xᵢ ×_X X_red` with the reduction of `Xᵢ`.
* `hCoproductEtale`, of the shape `CoproductsRepresentableEtale`, says that a morphism out of a
  coproduct of finitely many sheaves whose restriction to each summand is representable by
  algebraic spaces and étale is itself representable by algebraic spaces and étale. The index
  type is finite there, as it is in `FiniteCoproductsAffineFormal`, because the big fppf site
  of `S` is closed under finite coproducts only, so an infinite coproduct of algebraic spaces
  need have no atlas inside the site.

Finally the implication (1) ⇒ (2) is the hypothesis `hFiniteRefinement` of
`tfae_isQuasiCompactSpace`: it is the step of the proof of Stacks 0AJ9 which extracts from a
covering as in Definition 0AIM a finite subfamily which is still surjective, using that the
induced morphisms of reductions form an étale covering of the quasi-compact algebraic space
`Xred`.

## Implementation notes

Condition (2) repeats the set-theoretic condition of Stacks 0AIS, since Definition 0AIM asks
for it, so `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas` is exactly
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` with a finite index type for the atlas.
The index type lives in `Type (u + 1)`, the universe in which the sheaves of a presentation
live, as it does in Definition 0AIM.

Quasi-compactness of the reduction is `AlgebraicGeometry.Space.IsQuasiCompactSpaceULift`, the
condition of Stacks 03E3 for a value universe independent of the universe of the schemes,
since the sheaves carrying formal algebraic spaces take values in `Type (u + 1)`.

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
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
abbrev HasFiniteFormalAtlas (X : FppfSheaf B S hS) : Prop :=
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
theorem HasFiniteFormalAtlas.isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (h : HasFiniteFormalAtlas B S hS X) : IsFormalAlgebraicSpace B S hS X := by
  obtain ⟨hset, I, Xi, f, -, haffine, hetale, hsurjective⟩ := h
  exact ⟨hset, I, Xi, f, haffine, hetale, hsurjective⟩

/-! ### The auxiliary assertions about reductions and about coproducts -/

/-- The assertion that a reduction of an affine formal algebraic space over `S` is a
quasi-compact algebraic space. For an affine formal algebraic space the reduction is the
reduction of any stage of its presentation, hence an affine scheme. -/
abbrev AffineReductionsQuasiCompact : Prop :=
  ∀ (Y Yred : FppfSheaf B S hS) (iY : Yred ⟶ Y),
    IsAffineFormalAlgebraicSpace B S hS Y → IsReduction B S hS Y Yred iY →
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Yred.obj

/-- The assertion that the morphism of reductions induced by a morphism of fppf sheaves which
is representable by algebraic spaces, étale and a surjection of sheaves is itself surjective
and étale. -/
abbrev ReductionsOfEtaleSurjectionsEtaleSurjective : Prop :=
  ∀ (Y Z Yred Zred : FppfSheaf B S hS) (c : Y ⟶ Z) (iY : Yred ⟶ Y) (iZ : Zred ⟶ Z)
    (g : Yred ⟶ Zred),
    IsReduction B S hS Y Yred iY → IsReduction B S hS Z Zred iZ →
    (∃ hc : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) c.hom hc) →
    Sheaf.IsLocallySurjective c → g ≫ iZ = iY ≫ c →
    Space.HasSchemePropertyULift.{u + 1} B S hS
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) g.hom ∧
      Space.IsEtaleULift.{u + 1} B S hS g.hom

/-- The assertion that a coproduct of finitely many affine formal algebraic spaces over `S` is
an affine formal algebraic space over `S`. -/
abbrev FiniteCoproductsAffineFormal : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∀ (I : Type (u + 1)) (Z : I → FppfSheaf B S hS), Finite I →
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i)) →
    IsAffineFormalAlgebraicSpace B S hS (∐ Z)

/-- A coproduct of finitely many affine formal algebraic spaces over `S` is an affine formal
algebraic space over `S`: the assertion `FiniteCoproductsAffineFormal`, proved in
`StacksFrontier/AlgebraicGeometry/FormalSpace/AffineCoproduct.lean`.

This carries no `@[stacks]` registration: the Stacks project invokes it inside the proof of
Stacks 0AQD as the bare assertion that a finite union of formal affine algebraic spaces is a
formal affine algebraic space, with no tag of its own, and omits the argument. -/
theorem finiteCoproductsAffineFormal : FiniteCoproductsAffineFormal B S hS :=
  fun _ Z _ hZ ↦ isAffineFormalAlgebraicSpace_sigma B S hS Z hZ

/-- The assertion that a morphism out of a coproduct of finitely many fppf sheaves is
representable by algebraic spaces and étale as soon as its restriction to every summand is. -/
abbrev CoproductsRepresentableEtale : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∀ (I : Type (u + 1)) (Z : I → FppfSheaf B S hS) (W : FppfSheaf B S hS) (g : ∀ i, Z i ⟶ W),
    Finite I →
    (∀ i, ∃ hgi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g i).hom hgi) →
    ∃ hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (Sigma.desc g).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (Sigma.desc g).hom hg

/-! ### The implication (3) ⇒ (2) -/

/-- **Stacks 0AJ9, the implication (3) ⇒ (2).** A quasi-compact formal algebraic space over
`S` has a finite formal atlas: the one affine formal algebraic space surjecting onto it is an
atlas as in Definition 0AIM indexed by a one-point type, the induced map from the coproduct
over that type being the given map up to the coproduct inclusion, which is a split
epimorphism. -/
theorem IsQuasiCompactSpace.hasFiniteFormalAtlas {X : FppfSheaf B S hS}
    (h : IsQuasiCompactSpace B S hS X) : HasFiniteFormalAtlas B S hS X := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, Z, c, haffine, hetale, hsurjective⟩ := h
  refine ⟨hset, PUnit.{u + 2}, fun _ ↦ Z, fun _ ↦ c, inferInstance, fun _ ↦ haffine,
    fun _ ↦ hetale, ?_⟩
  have hc : Epi c := (Sheaf.isLocallySurjective_iff_epi c).mp hsurjective
  have hcomp : Epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit ≫
      Sigma.desc (fun _ : PUnit.{u + 2} ↦ c)) := by
    rw [Sigma.ι_comp_desc]
    exact hc
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr
    (epi_of_epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit) _)

/-! ### The implication (2) ⇒ (3) -/

/-- **Stacks 0AJ9, the implication (2) ⇒ (3).** A sheaf with a finite formal atlas is a
quasi-compact formal algebraic space over `S`: the coproduct of the finitely many members of
the atlas is an affine formal algebraic space, and the induced morphism from it is
representable by algebraic spaces, étale and a surjection of sheaves. -/
theorem HasFiniteFormalAtlas.isQuasiCompactSpace
    (hCoproductEtale : CoproductsRepresentableEtale B S hS)
    {X : FppfSheaf B S hS} (h : HasFiniteFormalAtlas B S hS X) :
    IsQuasiCompactSpace B S hS X := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, I, Xi, f, hfinite, haffine, hetale, hsurjective⟩ := h
  exact ⟨hset, ∐ Xi, Sigma.desc f, finiteCoproductsAffineFormal B S hS I Xi hfinite haffine,
    hCoproductEtale I Xi X f hfinite hetale, hsurjective⟩

/-! ### The implication (3) ⇒ (1) -/

/-- **Stacks 0AJ9, the implication (3) ⇒ (1).** Let `X` be a quasi-compact formal algebraic
space over `S` and let `i : Xred ⟶ X` be a reduction of `X`. Then `Xred` is a quasi-compact
algebraic space. Indeed, the affine formal algebraic space `Y` surjecting onto `X` has a
reduction `iY : Yred ⟶ Y`, the composite `Yred ⟶ Y ⟶ X` factors through `i` because `Yred` is
a reduced algebraic space, and the resulting morphism `Yred ⟶ Xred` is surjective and étale;
composing a quasi-compact surjective étale chart of `Yred` with it gives one of `Xred`. -/
theorem IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction
    (hAffineReduction : AffineReductionsQuasiCompact B S hS)
    (hReductionEtaleSurjective : ReductionsOfEtaleSurjectionsEtaleSurjective B S hS)
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    (h : IsQuasiCompactSpace B S hS X) :
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj := by
  obtain ⟨-, Y, c, haffine, hetale, hsurjective⟩ := h
  obtain ⟨Yred, iY, hiY⟩ := exists_isReduction_of_isAffineFormalAlgebraicSpace B S hS Y haffine
  obtain ⟨g, hg, -⟩ := hi.universal Yred hiY.algebraic hiY.reduced (iY ≫ c)
  obtain ⟨hgSurjective, hgEtale⟩ :=
    hReductionEtaleSurjective Y X Yred Xred c iY i g hiY hi hetale hsurjective hg
  obtain ⟨U, φ, hUcompact, hφSurjective, hφEtale⟩ := hAffineReduction Y Yred iY haffine hiY
  exact ⟨U, φ ≫ g.hom, hUcompact,
    MorphismProperty.comp_mem _ _ _ hφSurjective hgSurjective,
    isEtaleULift_comp B S hS hφEtale hgEtale⟩

/-! ### The equivalence of the three conditions -/

/-- **Stacks 0AJ9.** Let `X` be a formal algebraic space over `S` and let `i : Xred ⟶ X` be a
reduction of `X`. The following are equivalent:

1. `Xred` is a quasi-compact algebraic space,
2. `X` admits an atlas as in Definition 0AIM indexed by a finite type,
3. `X` receives a morphism from an affine formal algebraic space which is representable by
   algebraic spaces, étale and a surjection of sheaves. -/
theorem tfae_isQuasiCompactSpace
    (hAffineReduction : AffineReductionsQuasiCompact B S hS)
    (hReductionEtaleSurjective : ReductionsOfEtaleSurjectionsEtaleSurjective B S hS)
    (hCoproductEtale : CoproductsRepresentableEtale B S hS)
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (_hX : IsFormalAlgebraicSpace B S hS X) (hi : IsReduction B S hS X Xred i)
    (hFiniteRefinement : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj →
      HasFiniteFormalAtlas B S hS X) :
    [Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj,
      HasFiniteFormalAtlas B S hS X,
      IsQuasiCompactSpace B S hS X].TFAE := by
  tfae_have 1 → 2 := hFiniteRefinement
  tfae_have 2 → 3 := HasFiniteFormalAtlas.isQuasiCompactSpace B S hS hCoproductEtale
  tfae_have 3 → 1 := IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction B S hS
    hAffineReduction hReductionEtaleSurjective hi
  tfae_finish

/-! ### Stacks 0AJA, the definition

**Stacks 0AJA** defines a formal algebraic space to be *quasi-compact* when the equivalent
conditions of Stacks 0AJ9 hold. The library's predicate for that notion is
`AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`, condition (3) of the lemma; the equivalence
with conditions (1) and (2), which is what makes the choice of condition immaterial and so makes
this a definition rather than a choice, is `tfae_isQuasiCompactSpace` above. -/

add_to_stacks 0AJA "the definition, realized by condition (3) of Stacks 0AJ9, \
`AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`; the equivalence with conditions (1) and \
(2) that makes the choice of condition immaterial is `tfae_isQuasiCompactSpace`, which carries \
the two hypotheses standing for the steps of the omitted proof of Stacks 0AJ9"
  AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace

end AlgebraicGeometry.FormalSpace

end
