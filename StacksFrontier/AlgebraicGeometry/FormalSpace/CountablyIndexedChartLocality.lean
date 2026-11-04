module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferEtale

/-!
# Countable indexing is étale local on a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AKX** says, for each of the
five types of affine formal algebraic space of Stacks 0AIJ and Stacks 0AID, that the two
conditions

1. every affine formal algebraic space representable étale over `X` has the type, and
2. `X` admits an atlas as in Definition 0AIM all of whose members have the type

are equivalent for a formal algebraic space `X` over `S`. The equivalence for an abstract
property is
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`
of `StacksFrontier/AlgebraicGeometry/FormalSpace/TypeTransfer.lean`, which carries the refinement
step of the source's proof of the implication (2) ⟹ (1) as the hypothesis
`AlgebraicGeometry.FormalSpace.HasAffineEtaleRefinementWithProperty`. This file discharges that
hypothesis for the *countably indexed* property, and so proves the implication (2) ⟹ (1) of
Stacks 0AKX in that case outright.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasFormalAffineChartPullbacks`: **Stacks 0AJ2** in the shape
  the proof of Stacks 0AKX consumes — the fibre product of an affine étale chart of a formal
  algebraic space with a representable étale morphism from an affine formal algebraic space is
  a formal algebraic space — quantified over the morphism, since the refinement step is.
* `AlgebraicGeometry.FormalSpace.PropertyOfFiniteDisjointUnions`: the passage of a property of
  affine formal algebraic spaces to a finite disjoint union, the step the source records as a
  "small detail omitted".

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma`: a coproduct of finitely many
  countably indexed affine formal algebraic spaces over `S` is countably indexed, which is
  `PropertyOfFiniteDisjointUnions` for countable indexing.
* `AlgebraicGeometry.FormalSpace.hasAffineEtaleRefinementWithProperty_of_descends`: the
  refinement step in the proof of Stacks 0AKX, for any property descending along a
  representable étale morphism and passing to a finite disjoint union. This is the architecture
  the four other properties of the source's list share; see "The four other properties" below.
* `AlgebraicGeometry.FormalSpace.hasAffineEtaleRefinementWithProperty_isCountablyIndexed`: the
  refinement step in the proof of Stacks 0AKX, for the countably indexed property.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentableEtale`: **Stacks 0AKX**,
  the implication (2) ⟹ (1) for the countably indexed property. This is the statement that
  `AlgebraicGeometry.FormalSpace.isTaut_tfae_isRepresentableByAlgebraicSpaces` of
  `StacksFrontier/AlgebraicGeometry/FormalSpace/TautMorphismRepresentability.lean` and
  `AlgebraicGeometry.FormalSpace.isAdic_of_isTaut_of_isLocallyAdicStar` of
  `StacksFrontier/AlgebraicGeometry/FormalSpace/AdicMorphism.lean` carry as the hypothesis
  `h0AKX`.
* `FormalSpace.isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas`:
  the same implication asked of every fppf sheaf carrying such an atlas, at the same four
  inputs. This is the shape
  `AlgebraicGeometry.FormalSpace.HasAffineEtaleChartPropertyOfAtlas` of
  `StacksFrontier/AlgebraicGeometry/FormalSpace/FibreProductTypes.lean`, which the clauses of
  Stacks 0GBB there consume and which the result above cannot supply.

## Implementation notes

`AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma` is the step the source of Stacks 0AKX
records as a "small detail omitted on finite disjoint unions of affine formal algebraic
spaces". It carries no `@[stacks]` registration, for the same reason as its companion
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/AffineCoproduct.lean`: it is an unnumbered step
inside a proof and not a tagged statement. Its proof reuses that companion's machinery for
finite coproducts in the big affine fppf category, and is the simpler for being indexed by one
copy of `ℕ` rather than by a product of the index preorders of the summands: the presentations
of the summands are already indexed by the *same* preorder, so no finality of a projection out
of a product is needed, and the combined system `n ↦ ∐ᵢ (Dᵢ) n` is again indexed by `ℕ`. That
is exactly what the countably indexed property asks for, and what
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma` on its own does not give,
its combined system being indexed by the product.

### What remains assumed

Of the five steps of the source's refinement argument — Stacks 0AJ2 for the fibre products of
the members of the atlas with the chart, the coverings of Definition 0AIM refining those fibre
products, quasi-compactness of the chart cutting the resulting family down to a finite one,
Stacks 0AKQ along the étale maps to the members of the atlas, and the passage of the property
to a finite disjoint union — four are now theorems of this library. Quasi-compactness is
`AlgebraicGeometry.FormalSpace.exists_finite_subcover_of_isAffineFormalAlgebraicSpace`,
Stacks 0AKQ in the countably indexed case is
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentable`, which takes no hypothesis
beyond the source's, the disjoint union is `isCountablyIndexed_sigma` here, and the
assembly of the finite subfamily into one morphism out of the coproduct is
`AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/CoproductRepresentableEtale.lean`. One remains a
hypothesis:

* `h0AJ2`, of the shape `HasFormalAffineChartPullbacks`. Stacks 0AJ2 is available in this
  library only from
  `FormalSpace.isFormalAlgebraicSpace_pullback_of_representable_of_isAffineFormal`,
  which grants Stacks 0AIU in the shape
  `AlgebraicGeometry.FormalSpace.ColimitOfThickeningsIsFormalAlgebraicSpace`; the library's own
  Stacks 0AIU assumes the whole chart system of the source's proof and so rests in turn on
  Stacks 05ZH, carried here only at a first-order thickening, and on Stacks 07VT.

The declarations below nonetheless take the assembly as the binder `hCoproductEtale`, of the
shape `AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`, because they are stated
upstream of its proof. Variants with it discharged are
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentableEtale_unconditional` and
`FormalSpace.isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas_unconditional`,
in that same file.

The transfer of countable indexing along the resulting surjective flat morphism is Stacks
0AKS, `AlgebraicGeometry.FormalSpace.isCountablyIndexed_iff_of_surjective_flat`, which takes no
hypothesis beyond the source's.

### The four other properties

For countably indexed and classical, weakly adic, adic\* and Noetherian the architecture is
`hasAffineEtaleRefinementWithProperty_of_descends` again, with Stacks 0AKQ supplied by
`AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_of_isRepresentable`,
`AlgebraicGeometry.FormalSpace.isWeaklyAdic_of_isRepresentable`,
`AlgebraicGeometry.FormalSpace.isAdicStar_of_isRepresentable` and
`AlgebraicGeometry.FormalSpace.isNoetherian_of_isRepresentable`, and the transfer by Stacks 0GXR,
0GXS, 0AKT and 0AKW. The input `PropertyOfFiniteDisjointUnions` holds for all four:
`AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_sigma`,
`AlgebraicGeometry.FormalSpace.isWeaklyAdic_sigma`,
`AlgebraicGeometry.FormalSpace.isAdicStar_sigma` and
`AlgebraicGeometry.FormalSpace.isNoetherian_sigma`. What those supply, and what the four properties
need where countable indexing does not, is a presenting ring of a finite coproduct: each of them is
a condition on a presenting ring of the space (Stacks 0AID, the four abbreviations of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/Types.lean`), and the ring is the product
`∀ i, Aᵢ` of presenting rings of the summands, identified with a presenting ring of `∐ᵢ Zᵢ` by
`AlgebraicGeometry.FormalSpace.isAdicStar_sigma` and its companions. Countable indexing needs none
of this, being a condition on the *index* of the presentation rather than on a presenting ring,
which is why `isCountablyIndexed_sigma` can be proved here and its four siblings are proved only
after that identification.

## References

* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A finite coproduct of countably indexed affine formal algebraic spaces -/

/-! ### Stacks 0AKX, the implication (2) ⟹ (1) for countable indexing -/

/-- **Stacks 0AJ2** in the shape the proof of Stacks 0AKX consumes: the fibre product of an
affine étale chart `v : V ⟶ T` of a sheaf with a representable étale morphism `f : U ⟶ T` from
an affine formal algebraic space is a formal algebraic space. The refinement step of that proof
forms these fibre products for a chart `f` of the target of an unspecified morphism, so the
assertion is quantified over `f` as well as over `v`. -/
abbrev HasFormalAffineChartPullbacks : Prop :=
  ∀ {U T : FppfSheaf B S hS} (f : U ⟶ T), IsAffineFormalAlgebraicSpace B S hS U →
    IsRepresentableEtale B S hS f →
    ∀ (V : FppfSheaf B S hS) (v : V ⟶ T), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f)

/-- **The passage of a property of affine formal algebraic spaces to a finite disjoint union**: the
step the source of Stacks 0AKX records as a "small detail omitted on finite disjoint unions of
affine formal algebraic spaces". For the countably indexed property it is the theorem
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma` above; for the four other properties of
the source's list it is `AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_sigma`,
`AlgebraicGeometry.FormalSpace.isWeaklyAdic_sigma`,
`AlgebraicGeometry.FormalSpace.isAdicStar_sigma` and
`AlgebraicGeometry.FormalSpace.isNoetherian_sigma`, which identify the presenting ring of a finite
coproduct as the product of the members' presenting rings. -/
abbrev PropertyOfFiniteDisjointUnions (P : FppfSheaf B S hS → Prop) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∀ (I : Type (u + 1)) (Z : I → FppfSheaf B S hS), Finite I →
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i)) → (∀ i, P (Z i)) → P (∐ Z)

/-- **The refinement step in the proof of Stacks 0AKX**, for a property `P` of affine formal
algebraic spaces which descends along a representable étale morphism (`h0AKQ`, which is
Stacks 0AKQ for `P`) and passes to a finite disjoint union (`hPsigma`). Given an atlas
`{Xᵢ ⟶ X}` as in Definition 0AIM all of whose members satisfy `P` and an affine formal
algebraic space `Y` representable étale over `X`, the space `Y` receives a surjective
representable étale morphism from an affine formal algebraic space satisfying `P`.

The fibre products `Xᵢ ×_X Y` are formal algebraic spaces by `h0AJ2`, so each has an atlas
`{Xᵢⱼ ⟶ Xᵢ ×_X Y}` as in Definition 0AIM. The composite `Xᵢⱼ ⟶ Xᵢ` is representable étale, so
`Xᵢⱼ` satisfies `P` by `h0AKQ`. The composites `Xᵢⱼ ⟶ Y` form a covering of `Y` as in
Definition 0AIM, which quasi-compactness of `Y` cuts down to a finite subfamily by
`AlgebraicGeometry.FormalSpace.exists_finite_subcover_of_isAffineFormalAlgebraicSpace`; the
coproduct of that subfamily is an affine formal algebraic space by
`AlgebraicGeometry.FormalSpace.finiteCoproductsAffineFormal`, satisfies `P` by `hPsigma`, and
maps to `Y` by a representable étale surjection, the representable étaleness by
`hCoproductEtale`. -/
theorem hasAffineEtaleRefinementWithProperty_of_descends (P : FppfSheaf B S hS → Prop)
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    (hCoproductEtale : CoproductsRepresentableEtale B S hS)
    (h0AKQ : ∀ {U V : FppfSheaf B S hS} (f : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS f → P V → P U)
    (hPsigma : PropertyOfFiniteDisjointUnions B S hS P) :
    HasAffineEtaleRefinementWithProperty B S hS P := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro X I Xi fi hXiaff hXiet hXisurj hXici Y g hY hg
  -- the atlases of the fibre products of the members of the atlas with the chart
  choose K Zc c hZaff hZet hZsurj using fun j ↦
    (h0AJ2 g hY hg (Xi j) (fi j) (hXiaff j) (hXiet j)).2
  have hfst : ∀ j, IsRepresentableEtale B S hS (pullback.fst (fi j) g) := fun j ↦
    isRepresentableEtale_pullback_fst B S hS (fi j) g hg
  have hsnd : ∀ j, IsRepresentableEtale B S hS (pullback.snd (fi j) g) := fun j ↦
    isRepresentableEtale_pullback_snd B S hS (fi j) g (hXiet j)
  -- each member of the refined family satisfies `P`, by Stacks 0AKQ
  have hZci : ∀ (j : I) (k : K j), P (Zc j k) := fun j k ↦
    h0AKQ (c j k ≫ pullback.fst (fi j) g) (hZaff j k) (hXiaff j)
      (IsRepresentableEtale.comp B S hS (hZet j k) (hfst j)) (hXici j)
  -- and the refined family covers `Y`
  have hcov : Sheaf.IsLocallySurjective
      (Sigma.desc fun p : Σ j, K j ↦ c p.1 p.2 ≫ pullback.snd (fi p.1) g) :=
    Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (fun j ↦ pullback.snd (fi j) g) c
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd g fi hXisurj) hZsurj
  obtain ⟨σ, hfinite, κ, hsub⟩ :=
    exists_finite_subcover_of_isAffineFormalAlgebraicSpace B S hS Y
      (fun p : Σ j, K j ↦ Zc p.1 p.2)
      (fun p ↦ c p.1 p.2 ≫ pullback.snd (fi p.1) g) hY
      ⟨fun p ↦ hZaff p.1 p.2,
        fun p ↦ IsRepresentableEtale.comp B S hS (hZet p.1 p.2) (hsnd p.1), hcov⟩
  have hce := hCoproductEtale σ _ Y _ hfinite hsub.2.1
  exact ⟨∐ fun s ↦ Zc (κ s).1 (κ s).2,
    Sigma.desc fun s ↦ c (κ s).1 (κ s).2 ≫ pullback.snd (fi (κ s).1) g,
    finiteCoproductsAffineFormal B S hS σ _ hfinite hsub.1,
    hPsigma σ _ hfinite hsub.1 (fun s ↦ hZci (κ s).1 (κ s).2), hce.1,
    isSurjective_of_isLocallySurjective B S hS hsub.2.2,
    IsRepresentableFlat.of_isRepresentableEtale B S hS _ hce,
    IsLocallyOfFiniteType.of_isRepresentableEtale B S hS _ hce⟩

/-- The passage of countable indexing to a finite disjoint union, from
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma`. -/
theorem propertyOfFiniteDisjointUnions_isCountablyIndexed :
    PropertyOfFiniteDisjointUnions B S hS (IsCountablyIndexed B S hS) := by
  intro I Z hfinite _ hP
  have := hfinite
  exact isCountablyIndexed_sigma B S hS Z hP

/-- **The refinement step in the proof of Stacks 0AKX, for the countably indexed property.**
Of the two inputs of `hasAffineEtaleRefinementWithProperty_of_descends` beyond `h0AJ2` and
`hCoproductEtale`, Stacks 0AKQ for countable indexing is
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentable`, and the finite disjoint
union is
`propertyOfFiniteDisjointUnions_isCountablyIndexed`. -/
theorem hasAffineEtaleRefinementWithProperty_isCountablyIndexed
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    (hCoproductEtale : CoproductsRepresentableEtale B S hS) :
    HasAffineEtaleRefinementWithProperty B S hS (IsCountablyIndexed B S hS) :=
  hasAffineEtaleRefinementWithProperty_of_descends B S hS _ h0AJ2 hCoproductEtale
    (fun f hU hV hf hVP ↦
      isCountablyIndexed_of_isRepresentable B S hS f hU hV hf.1 hVP)
    (propertyOfFiniteDisjointUnions_isCountablyIndexed B S hS)

/-- **Stacks 0AKX, the implication (2) ⟹ (1) for countable indexing.** Let `Z` be a locally
countably indexed formal algebraic space over `S`, that is one admitting an atlas as in
Definition 0AIM by countably indexed affine formal algebraic spaces. Then every affine formal
algebraic space representable étale over `Z` is countably indexed.

This is the content that
`AlgebraicGeometry.FormalSpace.isTaut_tfae_isRepresentableByAlgebraicSpaces` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/TautMorphismRepresentability.lean` and
`AlgebraicGeometry.FormalSpace.isAdic_of_isTaut_of_isLocallyAdicStar` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/AdicMorphism.lean` carry as the hypothesis `h0AKX`.
-/
theorem isCountablyIndexed_of_isRepresentableEtale
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    (hCoproductEtale : CoproductsRepresentableEtale B S hS)
    {Z U : FppfSheaf B S hS} (a : U ⟶ Z)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (ha : IsRepresentableEtale B S hS a) :
    IsCountablyIndexed B S hS U :=
  (hasAffineEtaleChartProperty_iff_of_refinement_of_transfer B S hS Z
    (IsCountablyIndexed B S hS) hZ.1
    (hasAffineEtaleRefinementWithProperty_isCountablyIndexed B S hS h0AJ2 hCoproductEtale)
    (fun w hW hW' hw hwsurj hwflat _ ↦
      isCountablyIndexed_iff_of_surjective_flat B S hS w hW hW' hw hwsurj hwflat)).2 hZ.2 U a hU ha

/-- **Stacks 0AKX, the implication (2) ⟹ (1) for countable indexing, from the atlas alone.**
If an fppf sheaf `T` on the big fppf site of `S` admits an atlas as in Definition 0AIM by
countably indexed affine formal algebraic spaces, then every affine formal algebraic space
representable étale over `T` is countably indexed.

This differs from `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentableEtale`
above only in asking the atlas of condition (2) of its subject and nothing else, where that
result asks `AlgebraicGeometry.FormalSpace.IsLocallyCountablyIndexed`, which also carries
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` and so the set-theoretic condition of
Stacks 0AIS. The two have the same three hypotheses, the saving coming from
`hasAffineEtaleChartProperty_of_hasAffineEtaleAtlasWithProperty` in place of the full
equivalence: only the implication (1) ⟹ (2) needs the subject to be a formal algebraic space.

This is the shape that a consumer quantifying over every sheaf carrying such an atlas needs —
`AlgebraicGeometry.FormalSpace.HasAffineEtaleChartPropertyOfAtlas` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/FibreProductTypes.lean`, the hypothesis `h0AKX` of
the five clauses of Stacks 0GBB there, is this statement at the five properties of the
source's list. -/
theorem isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    (hCoproductEtale : CoproductsRepresentableEtale B S hS) :
    ∀ T : FppfSheaf B S hS,
      HasAffineEtaleAtlasWithProperty B S hS T (IsCountablyIndexed B S hS) →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ T), IsAffineFormalAlgebraicSpace B S hS U →
        IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U :=
  hasAffineEtaleChartProperty_of_hasAffineEtaleAtlasWithProperty B S hS
    (IsCountablyIndexed B S hS)
    (hasAffineEtaleRefinementWithProperty_isCountablyIndexed B S hS h0AJ2 hCoproductEtale)
    (fun w hW hW' hw hwsurj hwflat _ ↦
      isCountablyIndexed_iff_of_surjective_flat B S hS w hW hW' hw hwsurj hwflat)

end AlgebraicGeometry.FormalSpace

end
