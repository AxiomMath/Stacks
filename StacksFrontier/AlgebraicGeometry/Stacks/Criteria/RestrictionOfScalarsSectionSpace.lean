module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsFiniteLocallyFree

/-!
# The space of sections is the restriction of scalars over the base

Let `Z` be an object of the big fppf site of a scheme `U`, let `W` be an algebraic space over `U`
and let `w : W ⟶ yoneda.obj Z` be a morphism of presheaves. Two constructions in this library
attach a presheaf on the site of `U` to this datum:

* `AlgebraicGeometry.Space.sectionSpace`, the functor of sections of `W_T → Z_T` whose existence
  is the first assertion of Stacks 05XR, and
* `AlgebraicGeometry.Space.restrictionOfScalars`, the restriction of scalars `Res_{Z/Q}(W)` of
  Stacks 05YA, taken along the structure morphism of `Z` over a base `Q`.

This file identifies them in the case that concerns the finite Hilbert stack: when the base `Q`
is the final algebraic space `AlgebraicGeometry.Space.terminalSpace` of the site, the case in
which `Res_{Z/Q}(W)` is literally a space of sections rather than a space of relative morphisms.

The identification is the one recorded as missing in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.AbsoluteOverBase`, where it is what stands
between the library's Stacks 05YF,
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree`, and the
shape `AlgebraicGeometry.Stack.RestrictionOfScalarsIsAlgebraicSpace` in which the relative
representability of Stacks 05YJ consumes Stacks 05YF.

## The comparison

Over a final object the two notions of section agree once the two shapes of the ambient fibre
product are compared. A section at `T` in the sense of Stacks 05XR is a morphism `T ⨯ Z ⟶ W`
over `Z` (`AlgebraicGeometry.Space.SectionsOver`); a pair at `T` in the sense of Stacks 05Y9 is a
morphism `a : T ⟶ Q` together with a morphism `T ×_{a,Q} Z ⟶ W` over `Z`
(`AlgebraicGeometry.Space.RestrictionPair`). When `Q` is final the first component carries no
information and the fibre product is the product, which is
`AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal`.

That comparison is stated for an arbitrary pair of morphisms into a final object rather than for
the canonical ones, which is why it is not an instance of Mathlib's
`CategoryTheory.Limits.prodIsoPullback`: the first component of a pair is a bound variable, equal
to the canonical morphism but not syntactically so, and reducing it first would leave the
transport `CategoryTheory.Limits.pullback.congrHom` in every subsequent computation. With the
comparison available for the bound first component, its compatibility with base change in the
test object is `AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal_hom_comp_map`, and that one
lemma carries the whole naturality of the identification.

The two directions of the identification are given as separate definitions,
`AlgebraicGeometry.Space.sectionsOverOfRestrictionPair` and
`AlgebraicGeometry.Space.restrictionPairOfSectionsOver`, and every proof about them is a term
rather than a rewrite. That is not a style choice: the first component of a pair has a type in
which the ambient fibre product is indexed, so a rewrite along
`AlgebraicGeometry.Space.RestrictionPair.restrict_base` is not type-correct on its own, and the
two spellings of the category of presheaves that the first component and the comparison arrive
with make `rw` fail its motive check even where the statement is sound. Associativity and
`congrArg` are enough, because the first component of a base-changed pair *is* the composite and
its second component *is* the induced map of fibre products.

`AlgebraicGeometry.Space.sectionSpace` is `Classical.choose`n, so the comparison is made through
`AlgebraicGeometry.Space.sectionSpaceEquiv` and its naturality lemma
`AlgebraicGeometry.Space.sectionSpaceEquiv_map`, not by `rfl`. On the restriction-of-scalars side
the naturality of `AlgebraicGeometry.Space.RestrictionOfScalarsConstruction.pairEquiv` is stated
as a base-change relation rather than as an equality, and is turned into one by
`AlgebraicGeometry.Space.RestrictionPair.eq_restrict_of_isPullbackAlong`.

## Main definitions

* `AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal`: a fibre product over a final object,
  taken along arbitrary morphisms, is the product.
* `AlgebraicGeometry.Space.restrictionPairEquivSectionsOver`: at a fixed test object, a pair for
  the restriction of scalars over the final algebraic space is a section.
* `AlgebraicGeometry.Space.restrictionOfScalarsIsoSectionSpace`: the two presheaves agree.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_fibreSections`:
  **Stacks 05YF for the space of sections.** The functor of sections of `w : W ⟶ yoneda.obj Z`
  is an algebraic space over `U` when `Z` is finite locally free over `U`, inheriting the three
  hypotheses of
  `AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree`.

## Implementation notes

The three hypotheses of
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree` are
inherited rather than discharged: `h05XR_X` and `h05XR_Z` ask for Stacks 05XR in the predicate
shape of `AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale`, and `hrepresentable` asks for
Stacks 05Y6 for algebraic spaces. Both are available elsewhere:

* The two 05XR slots hold outright, by `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale`,
  and the Stacks 05XQ predicate `AlgebraicGeometry.Space.IsFibreSectionsSurjective` that an
  earlier form of this statement also asked for holds by
  `AlgebraicGeometry.Space.isFibreSectionsSurjective`. Both predicates also hold for a finite
  `z`, by
  `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale_of_isFinite` and
  `AlgebraicGeometry.Space.isFibreSectionsSurjective_of_isFinite`
  (`Spaces/IsFibreSectionsGeneral.lean:251,268`), and a finite locally free morphism of algebraic
  spaces is finite by `AlgebraicGeometry.Space.isFinite_of_isFiniteLocallyFree`
  (`Spaces/FiniteLocallyFreeIsFinite.lean:222`), so they follow from `hz`. That is what
  `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_hom`
  (`Stacks/Criteria/SectionSpaceFiniteLocallyFree.lean:128`) does with them. The separated case
  over an arbitrary base, which needs none of this, is
  `AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isSeparated`
  (`Spaces/IsFibreSectionsSeparated.lean:488`) with its étale companion at `:527`, and two of
  the three clauses of the general case are
  `AlgebraicGeometry.Space.isSheaf_restrictionOfScalars` and
  `relativelyRepresentable_diag_restrictionOfScalars` (`Spaces/IsFibreSectionsSheaf.lean:70,80`),
  carrying no separatedness.
* For `hrepresentable`, Stacks 05Y6 for algebraic spaces at representable data is
  `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_representableBy`
  (`Spaces/RelativeHomSchemeComparison.lean:698`), resting on the explicit 0BL2 ↔ 05Y2
  comparison `relativeMorphismEquivRelativeHom` (`:403`). In the case this file is about the base
  is the final algebraic space of the site of `U`, which is the presheaf represented by `U`, and
  the source is represented by `Z`, so the target of `hrepresentable` is representable too and
  `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank`
  (`Stacks/Criteria/RelativeMorphismsRepresentableTarget.lean:279`) settles it from finite local
  freeness of rank `d` of the morphism of schemes underlying the structure morphism of `Z`
  together with `AlgebraicGeometry.Space.RelativeHomRepresentingContained` (`:152`), a condition
  on the site which `AlgebraicGeometry.Space.relativeHomRepresentingContained`
  (`Stacks/Criteria/RelativeMorphismsSiteSize.lean:91`) proves. Stacks 03ZU enters only in
  reconciling the Stacks 03ZV reading of `hz` with the Section 03HA reading that the scheme-side
  representability consumes, and at a fixed rank that reconciliation is
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank`
  (`Spaces/FiniteLocallyFreeIsFinite.lean:238`), which carries no hypothesis. The assembled
  statement is
  `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank`
  (`Stacks/Criteria/SectionSpaceFiniteLocallyFreeOfRank.lean:105`).

What this file supplies is the identification, which is independent of all three:
`AlgebraicGeometry.Space.restrictionOfScalarsIsoSectionSpace` carries no hypothesis beyond the
algebraicity of `W` that the restriction of scalars needs in order to be defined at all.

Nothing here carries a `@[stacks]` attribute. The identification is not an assertion of the
source, and the transported Stacks 05YF is conditional, so the tag stays on the library's own
Stacks 05YF.

## References

* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05Y9](https://stacks.math.columbia.edu/tag/05Y9)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u₁ u

namespace AlgebraicGeometry.Space


/-! ### A fibre product over a final object is the product -/

/-- **A fibre product over a final object is the product.** The commutation condition defining
the comparison morphism is automatic, both of its sides being morphisms into a final object, so
the comparison is available for arbitrary `base` and `g` and not only for the canonical
morphisms out of the two factors.

This is the generality Mathlib's `CategoryTheory.Limits.prodIsoPullback` does not have: there the
two legs are `CategoryTheory.Limits.terminal.from` out of a chosen final object. -/
@[simps]
noncomputable def prodIsoPullbackOfIsTerminal {C : Type u₁} [Category.{v} C] {A Y Q : C}
    (hQ : IsTerminal Q) (base : A ⟶ Q) (g : Y ⟶ Q) [HasBinaryProduct A Y]
    [HasPullback base g] : A ⨯ Y ≅ pullback base g where
  hom := pullback.lift prod.fst prod.snd (hQ.hom_ext _ _)
  inv := prod.lift (pullback.fst base g) (pullback.snd base g)
  hom_inv_id := by
    apply prod.hom_ext <;>
      simp
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp

/-- **The comparison of a fibre product over a final object with the product is compatible with
base change in the first factor.** This is the single computation behind the naturality of
`AlgebraicGeometry.Space.restrictionOfScalarsIsoSectionSpace`: the map of fibre products induced
by `f` on the first factor becomes `CategoryTheory.Limits.prod.map f (𝟙 _)`. -/
theorem prodIsoPullbackOfIsTerminal_hom_comp_map {C : Type u₁} [Category.{v} C] {A A' Y Q : C}
    (hQ : IsTerminal Q) (base : A ⟶ Q) (g : Y ⟶ Q) (f : A' ⟶ A) [HasBinaryProduct A Y]
    [HasBinaryProduct A' Y] [HasPullback base g] [HasPullback (f ≫ base) g]
    (eq₁ : (f ≫ base) ≫ 𝟙 Q = f ≫ base) (eq₂ : g ≫ 𝟙 Q = 𝟙 Y ≫ g) :
    (prodIsoPullbackOfIsTerminal hQ (f ≫ base) g).hom ≫
        pullback.map (f ≫ base) g base g f (𝟙 Y) (𝟙 Q) eq₁ eq₂ =
      prod.map f (𝟙 Y) ≫ (prodIsoPullbackOfIsTerminal hQ base g).hom := by
  apply pullback.hom_ext <;>
    simp

/-! ### The restriction of scalars over the final algebraic space -/

namespace SectionSpaceRestriction

variable (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U)

/-- The presheaf underlying the final algebraic space over `U` is a final presheaf. This is
`AlgebraicGeometry.Space.baseTerminal_yonedaIsTerminal` with the object spelled as the one the
restriction of scalars mentions, which is what keeps the first component of a pair and the
comparison `AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal` at the same type without an
unfolding of `AlgebraicGeometry.Space.terminalSpace`. -/
noncomputable def terminalSpaceObjIsTerminal : IsTerminal (terminalSpace B U hU).obj :=
  baseTerminal_yonedaIsTerminal B U hU

/-- `W`, as an algebraic space over `U`. -/
abbrev source (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B U hU W) :
    AlgebraicSpaces B U hU :=
  ⟨W, hW⟩

/-- `Z`, as an algebraic space over `U`. -/
noncomputable abbrev cover (Z : BigFppfOver B U hU) : AlgebraicSpaces B U hU :=
  schemeSpace Z

/-- `w : W ⟶ yoneda.obj Z`, as a morphism of algebraic spaces over `U`. -/
noncomputable abbrev toCover (Z : BigFppfOver B U hU)
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B U hU W)
    (w : W ⟶ yoneda.obj Z) : source B U hU W hW ⟶ cover B U hU Z :=
  ObjectProperty.homMk w

/-- The structure morphism of `Z` to the final algebraic space over `U`. -/
noncomputable abbrev toBase (Z : BigFppfOver B U hU) :
    cover B U hU Z ⟶ terminalSpace B U hU :=
  ObjectProperty.homMk ((terminalSpaceObjIsTerminal B U hU).from (yoneda.obj Z))

end SectionSpaceRestriction

open SectionSpaceRestriction

variable (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U)
  (Z : BigFppfOver B U hU) (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u)
  (hW : IsAlgebraicSpace B U hU W) (w : W ⟶ yoneda.obj Z)

/-- **A pair lies over `Z` exactly when the section it names does.** The second component of a
pair lies over `Z` by definition; read through
`AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal` that says the corresponding morphism out of
the product is a section. -/
theorem comp_eq_prod_snd_of_restrictionPair (T : BigFppfOver B U hU)
    (p : RestrictionPair B U hU (toCover B U hU Z W hW w) (toBase B U hU Z) (yoneda.obj T)) :
    ((prodIsoPullbackOfIsTerminal (terminalSpaceObjIsTerminal B U hU) p.base
        (toBase B U hU Z).hom).hom ≫ p.lift) ≫ w = prod.snd :=
  (Category.assoc _ _ _).trans ((congrArg _ p.over).trans (pullback.lift_snd _ _ _))

/-- **The section attached to a pair for the restriction of scalars over the final algebraic
space.** The second component of the pair is a morphism out of the fibre product of the test
object with `Z` over the final object, which
`AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal` identifies with their product. -/
noncomputable def sectionsOverOfRestrictionPair (T : BigFppfOver B U hU)
    (p : RestrictionPair B U hU (toCover B U hU Z W hW w) (toBase B U hU Z) (yoneda.obj T)) :
    SectionsOver B U hU Z T W w :=
  ⟨(prodIsoPullbackOfIsTerminal (terminalSpaceObjIsTerminal B U hU) p.base
      (toBase B U hU Z).hom).hom ≫ p.lift,
    comp_eq_prod_snd_of_restrictionPair B U hU Z W hW w T p⟩

/-- The morphism underlying `AlgebraicGeometry.Space.sectionsOverOfRestrictionPair`. -/
@[simp]
theorem sectionsOverOfRestrictionPair_coe (T : BigFppfOver B U hU)
    (p : RestrictionPair B U hU (toCover B U hU Z W hW w) (toBase B U hU Z) (yoneda.obj T)) :
    (sectionsOverOfRestrictionPair B U hU Z W hW w T p).1 =
      (prodIsoPullbackOfIsTerminal (terminalSpaceObjIsTerminal B U hU) p.base
        (toBase B U hU Z).hom).hom ≫ p.lift :=
  rfl

/-- **The morphism out of the fibre product attached to a section lies over `Z`.** This is the
second component of the pair that `AlgebraicGeometry.Space.restrictionPairOfSectionsOver`
builds. -/
theorem comp_eq_pullback_snd_of_sectionsOver (T : BigFppfOver B U hU)
    (σ : SectionsOver B U hU Z T W w) :
    ((prodIsoPullbackOfIsTerminal (terminalSpaceObjIsTerminal B U hU)
          ((terminalSpaceObjIsTerminal B U hU).from (yoneda.obj T))
          (toBase B U hU Z).hom).inv ≫ σ.1) ≫ (toCover B U hU Z W hW w).hom =
      pullback.snd ((terminalSpaceObjIsTerminal B U hU).from (yoneda.obj T))
        (toBase B U hU Z).hom :=
  (Category.assoc _ _ _).trans ((congrArg _ σ.2).trans (prod.lift_snd _ _))

/-- **The pair attached to a section.** Its first component is the unique morphism to the final
object, which carries no information. -/
noncomputable def restrictionPairOfSectionsOver (T : BigFppfOver B U hU)
    (σ : SectionsOver B U hU Z T W w) :
    RestrictionPair B U hU (toCover B U hU Z W hW w) (toBase B U hU Z) (yoneda.obj T) :=
  ⟨(terminalSpaceObjIsTerminal B U hU).from (yoneda.obj T),
    (prodIsoPullbackOfIsTerminal (terminalSpaceObjIsTerminal B U hU)
        ((terminalSpaceObjIsTerminal B U hU).from (yoneda.obj T))
        (toBase B U hU Z).hom).inv ≫ σ.1,
    comp_eq_pullback_snd_of_sectionsOver B U hU Z W hW w T σ⟩

/-- **A pair for the restriction of scalars over the final algebraic space is a section.** The
two directions are `AlgebraicGeometry.Space.sectionsOverOfRestrictionPair` and
`AlgebraicGeometry.Space.restrictionPairOfSectionsOver`; that they are inverse is the two
triangle identities of `AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal`, together with the
uniqueness of a morphism to the final object for the first component. -/
noncomputable def restrictionPairEquivSectionsOver (T : BigFppfOver B U hU) :
    RestrictionPair B U hU (toCover B U hU Z W hW w) (toBase B U hU Z) (yoneda.obj T) ≃
      SectionsOver B U hU Z T W w where
  toFun := sectionsOverOfRestrictionPair B U hU Z W hW w T
  invFun := restrictionPairOfSectionsOver B U hU Z W hW w T
  left_inv p := by
    have hbase : ((terminalSpaceObjIsTerminal B U hU).from (yoneda.obj T)) = p.base :=
      (terminalSpaceObjIsTerminal B U hU).hom_ext _ _
    refine RestrictionPair.ext_of_base_eq hbase ?_
    have h : (prodIsoPullbackOfIsTerminal (terminalSpaceObjIsTerminal B U hU)
          ((terminalSpaceObjIsTerminal B U hU).from (yoneda.obj T))
          (toBase B U hU Z).hom).inv ≫
        (prodIsoPullbackOfIsTerminal (terminalSpaceObjIsTerminal B U hU) p.base
          (toBase B U hU Z).hom).hom =
          (pullback.congrHom hbase rfl).hom := by
      apply pullback.hom_ext <;>
        simp
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p.lift) h)
  right_inv σ := Subtype.ext (Iso.hom_inv_id_assoc _ _)

/-- `AlgebraicGeometry.Space.restrictionPairEquivSectionsOver` is
`AlgebraicGeometry.Space.sectionsOverOfRestrictionPair`. -/
@[simp]
theorem restrictionPairEquivSectionsOver_apply (T : BigFppfOver B U hU)
    (p : RestrictionPair B U hU (toCover B U hU Z W hW w) (toBase B U hU Z) (yoneda.obj T)) :
    restrictionPairEquivSectionsOver B U hU Z W hW w T p =
      sectionsOverOfRestrictionPair B U hU Z W hW w T p :=
  rfl

/-- **The identification turns base change of pairs into restriction of sections.** Both sides
are the comparison with the product followed by the second component of the pair, and the two
comparisons differ by the map of fibre products that
`AlgebraicGeometry.Space.prodIsoPullbackOfIsTerminal_hom_comp_map` computes.

The proof is in terms rather than by rewriting: the first component of a base-changed pair *is*
the composite and its second component *is* the induced map of fibre products, so associativity
and one `congrArg` suffice, where a rewrite along
`AlgebraicGeometry.Space.RestrictionPair.restrict_base` would not even be type-correct. -/
@[simp]
theorem sectionsOverOfRestrictionPair_restrict {T T' : BigFppfOver B U hU} (f : T' ⟶ T)
    (p : RestrictionPair B U hU (toCover B U hU Z W hW w) (toBase B U hU Z) (yoneda.obj T)) :
    (sectionsOverOfRestrictionPair B U hU Z W hW w T'
        (RestrictionPair.restrict (yoneda.map f) p)).1 =
      prod.map (yoneda.map f) (𝟙 (yoneda.obj Z)) ≫
        (sectionsOverOfRestrictionPair B U hU Z W hW w T p).1 :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ p.lift)
        (prodIsoPullbackOfIsTerminal_hom_comp_map (terminalSpaceObjIsTerminal B U hU)
          p.base (toBase B U hU Z).hom (yoneda.map f) _ _)).trans
      (Category.assoc _ _ _))

/-! ### The identification of the two presheaves -/

/-- The comparison of the two presheaves at a single test object: a point of the restriction of
scalars is a pair, a pair is a section, and a section is a point of the space of sections. -/
noncomputable def sectionSpaceEquivRestrictionOfScalars (T : BigFppfOver B U hU) :
    (restrictionOfScalars B U hU (toCover B U hU Z W hW w)
        (toBase B U hU Z)).presheaf.obj (op T) ≃
      (sectionSpace B U hU Z W w).obj (op T) :=
  (((restrictionOfScalars B U hU (toCover B U hU Z W hW w)
          (toBase B U hU Z)).pairEquiv T).trans
      (restrictionPairEquivSectionsOver B U hU Z W hW w T)).trans
    (sectionSpaceEquiv B U hU Z T W w).symm

/-- The section underlying a value of
`AlgebraicGeometry.Space.sectionSpaceEquivRestrictionOfScalars`. -/
@[simp]
theorem sectionSpaceEquiv_sectionSpaceEquivRestrictionOfScalars (T : BigFppfOver B U hU)
    (v : (restrictionOfScalars B U hU (toCover B U hU Z W hW w)
      (toBase B U hU Z)).presheaf.obj (op T)) :
    sectionSpaceEquiv B U hU Z T W w
        (sectionSpaceEquivRestrictionOfScalars B U hU Z W hW w T v) =
      restrictionPairEquivSectionsOver B U hU Z W hW w T
        ((restrictionOfScalars B U hU (toCover B U hU Z W hW w)
          (toBase B U hU Z)).pairEquiv T v) :=
  (sectionSpaceEquiv B U hU Z T W w).apply_symm_apply _

/-- **The comparison is natural.** The restriction maps on both sides are base change: on the
restriction-of-scalars side by
`AlgebraicGeometry.Space.RestrictionPair.eq_restrict_of_isPullbackAlong` applied to the
base-change relation that `AlgebraicGeometry.Space.RestrictionOfScalarsConstruction.pairEquiv`
satisfies, on the section side by `AlgebraicGeometry.Space.sectionSpaceEquiv_map`, and the two
agree by `AlgebraicGeometry.Space.sectionsOverOfRestrictionPair_restrict`. -/
theorem sectionSpaceEquivRestrictionOfScalars_naturality {T T' : BigFppfOver B U hU} (f : T' ⟶ T)
    (v : (restrictionOfScalars B U hU (toCover B U hU Z W hW w)
      (toBase B U hU Z)).presheaf.obj (op T)) :
    sectionSpaceEquivRestrictionOfScalars B U hU Z W hW w T'
        ((restrictionOfScalars B U hU (toCover B U hU Z W hW w)
          (toBase B U hU Z)).presheaf.map f.op v) =
      (sectionSpace B U hU Z W w).map f.op
        (sectionSpaceEquivRestrictionOfScalars B U hU Z W hW w T v) := by
  refine (sectionSpaceEquiv B U hU Z T' W w).injective (Subtype.ext ?_)
  simp only [sectionSpaceEquiv_map, sectionSpaceEquiv_sectionSpaceEquivRestrictionOfScalars,
    restrictionPairEquivSectionsOver_apply,
    RestrictionPair.eq_restrict_of_isPullbackAlong
      ((restrictionOfScalars B U hU (toCover B U hU Z W hW w) (toBase B U hU Z)).natural f v),
    sectionsOverOfRestrictionPair_restrict]

/-- **The restriction of scalars over the final algebraic space is the space of sections.** The
two presheaves are compared test object by test object by
`AlgebraicGeometry.Space.sectionSpaceEquivRestrictionOfScalars`, which is natural by
`AlgebraicGeometry.Space.sectionSpaceEquivRestrictionOfScalars_naturality`. -/
noncomputable def restrictionOfScalarsIsoSectionSpace :
    (restrictionOfScalars B U hU (toCover B U hU Z W hW w) (toBase B U hU Z)).presheaf ≅
      sectionSpace B U hU Z W w :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (sectionSpaceEquivRestrictionOfScalars B U hU Z W hW w T.unop))
    (by
      intro T T' g
      ext v
      exact sectionSpaceEquivRestrictionOfScalars_naturality B U hU Z W hW w g.unop v)

/-- **Stacks 05YF for the space of sections.** Let `Z` be an object of the big fppf site of a
scheme `U` whose structure morphism to the final algebraic space is finite locally free, let `W`
be an algebraic space over `U` and let `w : W ⟶ yoneda.obj Z`. Then the functor of sections of
`W_T → Z_T` is an algebraic space over `U`.

This is the library's Stacks 05YF,
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree`,
transported along `AlgebraicGeometry.Space.restrictionOfScalarsIsoSectionSpace`. Its three
hypotheses are inherited; see the module documentation. -/
theorem isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_fibreSections
    (hz : IsFiniteLocallyFree B U hU (toBase B U hU Z))
    (h05XR_X : ∀ (V : BigFppfOver B U hU) (c : yoneda.obj V ⟶ W),
      IsFibreSectionsAlgebraicEtale B U hU
        (ObjectProperty.homMk c :
          (schemeSpace V : AlgebraicSpaces B U hU) ⟶
            source B U hU W hW)
        (toBase B U hU Z))
    (h05XR_Z : ∀ (V : BigFppfOver B U hU) (c : yoneda.obj V ⟶ yoneda.obj Z),
      IsFibreSectionsAlgebraicEtale B U hU
        (ObjectProperty.homMk c :
          (schemeSpace V : AlgebraicSpaces B U hU) ⟶
            cover B U hU Z)
        (toBase B U hU Z))
    (hrepresentable : ∀ (V : BigFppfOver B U hU)
      (u : yoneda.obj V ⟶ (terminalSpace B U hU).obj),
      IsAlgebraicSpace B U hU
        (relativeHom B U hU (yoneda.obj Z) (yoneda.obj V) (terminalSpace B U hU).obj
          (toBase B U hU Z).hom u (isAlgebraicSpace_yoneda B U hU Z)
          (isAlgebraicSpace_yoneda B U hU V) (terminalSpace B U hU).property)) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) :=
  isAlgebraicSpace_of_iso B U hU (restrictionOfScalarsIsoSectionSpace B U hU Z W hW w)
    (isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree B U hU
      (toCover B U hU Z W hW w) (toBase B U hU Z) hz
      h05XR_X h05XR_Z hrepresentable)

end AlgebraicGeometry.Space

end
