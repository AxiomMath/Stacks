module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMRelativePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Locally quasi-finite 1-morphisms and locally quasi-finite flat covers (Stacks 06UF)

**Stacks 06UF** is a four-way equivalence for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S`:

1. `f` is locally quasi-finite (**Stacks 06PU**);
2. `f` is quasi-DM (**Stacks 04YW**) and for every algebraic space `𝒱` over `𝒴` every locally
   quasi-finite 1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` out of an algebraic space has locally quasi-finite
   composite `𝒰 ⟶ 𝒱`;
3. for every algebraic space `𝒱` over `𝒴` there is a surjective, flat, locally finitely
   presented and locally quasi-finite 1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` out of an algebraic space whose
   composite `𝒰 ⟶ 𝒱` is locally quasi-finite;
4. one algebraic space `𝒱` surjective, flat and locally of finite presentation over `𝒴` carries
   such a cover of `𝒳 ×_𝒴 𝒱`.

**This file is a partial delivery of Stacks 06UF: it proves the chain (1) ⟹ (2) ⟹ (3) ⟹ (4),
and the quasi-DM conjunct of (4) ⟹ (1), and nothing more.** The remaining content of
(4) ⟹ (1) — local finite type and the discreteness of the field-valued fibres, the latter
through a finite extension `k'/k` splitting the chart over a field-valued point — needs the
fppf descent of local finite type along `𝒱 ⟶ 𝒴` and the comparison of `|𝒳_{k'}|` with
`|𝒳_k|` along a finite locally free surjection, neither of which is in this library. Every
attribute below is therefore suffixed with exactly the implication it carries.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasLocallyQuasiFiniteFlatSpaceCoverOver`: the cover
  condition of clauses (3) and (4) over one algebraic space `𝒱` over `𝒴`.
* `...TransfersLocalQuasiFinitenessOnSpaceBaseChanges`: the second conjunct of clause (2).
* `...LocallyQuasiFiniteCoverOnEverySpaceBaseChange`: clause (3).
* `...LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange`: clause (4).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_of_isLocallyQuasiFinite_hom`: a
  1-morphism representable by algebraic spaces which is locally quasi-finite in the sense of
  Properties of Stacks, Section 04XB is locally quasi-finite in the sense of **Stacks 06PU**.
  This is **Stacks 06UA** together with **Stacks 050E**.
* `...isQuasiDM_and_transfersLocalQuasiFiniteness_of_isLocallyQuasiFinite`: **Stacks 06UF**,
  (1) ⟹ (2).
* `...locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers`: **Stacks 06UF**,
  (2) ⟹ (3).
* `...locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange_of_onEverySpaceBaseChange`:
  **Stacks 06UF**, (3) ⟹ (4).
* `...isQuasiDM_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange`: **Stacks 06UF**, the
  quasi-DM conjunct of (4) ⟹ (1).

## Implementation notes

Local quasi-finiteness of each 1-morphism named in the four clauses is read as
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite`, the general notion of
**Stacks 06PU** for a 1-morphism of algebraic stacks, which is the source's Definition 101.23.2
and applies to all of them. For the covers `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` and the composites `𝒰 ⟶ 𝒱`, whose
source is an algebraic space and which are therefore representable by algebraic spaces, it
agrees with the Section 04XB notion `AlgebraicGeometry.Stack.IsLocallyQuasiFinite` used by
**Stacks 06UE** — that is **Stacks 06UA**, proved in this library, and the passage between the
two readings is `isLocallyQuasiFinite_of_isLocallyQuasiFinite_hom` in one direction and
`AlgebraicGeometry.Stack.isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology` in
the other.

One hypothesis is carried, in the spelling the rest of this corner of the library already uses:
`hPresentation`, the substantial direction of **Stacks 06MF**
(`AlgebraicGeometry.Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM`), carried in this
library wherever it is used — at **Stacks 06MF** itself and at **Stacks 06UE**. It is used only
for (2) ⟹ (3), through **Stacks 06UE**. The implication (1) ⟹ (2) is the composition of two
locally quasi-finite 1-morphisms, **Stacks 06UD**, which is unconditional.

The containment of the terminal scheme in the site, which the absolute quasi-DM condition of
**Stacks 050D** part (6) needs, is not carried: `AlgebraicGeometry.BigFppfSite.contains_terminal`
discharges it for every big fppf site, and `hPresentation` is stated at that witness exactly as
in **Stacks 06UE**.

## References

* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UA](https://stacks.math.columbia.edu/tag/06UA)
* [Stacks Project, Tag 06UB](https://stacks.math.columbia.edu/tag/06UB)
* [Stacks Project, Tag 06UD](https://stacks.math.columbia.edu/tag/06UD)
* [Stacks Project, Tag 06UE](https://stacks.math.columbia.edu/tag/06UE)
* [Stacks Project, Tag 06UF](https://stacks.math.columbia.edu/tag/06UF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A representable 1-morphism locally quasi-finite in the sense of Section 04XB is locally
quasi-finite in the sense of Stacks 06PU.** The quasi-DM conjunct is automatic for a 1-morphism
representable by algebraic spaces, which is Deligne–Mumford and hence quasi-DM
(**Stacks 050E**); the other two conjuncts are the right-hand side of **Stacks 06UA**. -/
theorem isLocallyQuasiFinite_of_isLocallyQuasiFinite_hom
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hf : Stack.IsLocallyQuasiFinite B S hS f.hom) :
    IsLocallyQuasiFinite B S hS f :=
  ⟨(isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).2
      (isQuasiDM_of_isDM B S hS
        (Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f hrep)),
    Stack.isLocallyOfFiniteType_and_discreteTopology_of_isLocallyQuasiFinite
      B S hS f hrep hf⟩

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism from an algebraic space to an algebraic stack is representable by algebraic
spaces. -/
private theorem isRepresentableByAlgebraicSpaces_hom_of_source
    {𝒰 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰.val) (p : 𝒰 ⟶ 𝒵) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom.hom :=
  Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒵.property h𝒰 p.hom

/-- **The cover condition of clauses (3) and (4) of Stacks 06UF over one algebraic space.** The
base change `𝒳 ×_𝒴 𝒱` of `f` along `g : 𝒱 ⟶ 𝒴` receives a surjective, flat, locally finitely
presented and locally quasi-finite 1-morphism from an algebraic space whose composite with the
projection to `𝒱` is locally quasi-finite. -/
abbrev HasLocallyQuasiFiniteFlatSpaceCoverOver (f : 𝒳 ⟶ 𝒴)
    {𝒱 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒴) : Prop :=
  ∃ (𝒰 : Stack.AlgebraicStacks.{u, w} B S hS)
    (_h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰.val)
    (h : 𝒰 ⟶ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt),
    IsSurjective B S hS h ∧ IsFlat B S hS h ∧ IsLocallyOfFinitePresentation B S hS h ∧
      IsLocallyQuasiFinite B S hS h ∧
      IsLocallyQuasiFinite B S hS
        (h ≫ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd)

/-- **The second conjunct of clause (2) of Stacks 06UF.** For every algebraic space `𝒱` over
`𝒴`, every locally quasi-finite 1-morphism to `𝒳 ×_𝒴 𝒱` out of an algebraic space has locally
quasi-finite composite with the projection to `𝒱`. -/
abbrev TransfersLocalQuasiFinitenessOnSpaceBaseChanges (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒱 : Stack.AlgebraicStacks.{u, w} B S hS),
    IsRepresentableByAlgebraicSpace B S hS 𝒱.val → ∀ (g : 𝒱 ⟶ 𝒴)
      (𝒰 : Stack.AlgebraicStacks.{u, w} B S hS),
      IsRepresentableByAlgebraicSpace B S hS 𝒰.val →
        ∀ h : 𝒰 ⟶ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt,
          IsLocallyQuasiFinite B S hS h →
            IsLocallyQuasiFinite B S hS
              (h ≫ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd)

/-- **Clause (3) of Stacks 06UF.** Every base change of `f` along an algebraic space over `𝒴`
has a locally quasi-finite flat cover by an algebraic space which is locally quasi-finite over
that algebraic space. -/
abbrev LocallyQuasiFiniteCoverOnEverySpaceBaseChange (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒱 : Stack.AlgebraicStacks.{u, w} B S hS),
    IsRepresentableByAlgebraicSpace B S hS 𝒱.val → ∀ g : 𝒱 ⟶ 𝒴,
      HasLocallyQuasiFiniteFlatSpaceCoverOver B S hS f g

/-- **Clause (4) of Stacks 06UF.** Some algebraic space surjective, flat and locally of finite
presentation over `𝒴` carries a base change of `f` with a locally quasi-finite flat cover by an
algebraic space which is locally quasi-finite over it. -/
abbrev LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (𝒱 : Stack.AlgebraicStacks.{u, w} B S hS)
    (_h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val) (g : 𝒱 ⟶ 𝒴),
    IsSurjective B S hS g ∧ IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g ∧
      HasLocallyQuasiFiniteFlatSpaceCoverOver B S hS f g

/-- **Stacks 06UF, (1) ⟹ (2).** A locally quasi-finite 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` is quasi-DM, and for every algebraic space `𝒱` over `𝒴` a locally quasi-finite
1-morphism `𝒰 ⟶ 𝒳 ×_𝒴 𝒱` out of an algebraic space has locally quasi-finite composite
`𝒰 ⟶ 𝒱`.

The quasi-DM conjunct is the first conjunct of **Stacks 06PU**. For the second, the projection
`𝒳 ×_𝒴 𝒱 ⟶ 𝒱` is a base change of `f` and so locally quasi-finite by **Stacks 06UB**, and
**Stacks 06UD** composes it with the given 1-morphism. -/
@[stacks 06UF "the implication (1) => (2)"]
theorem isQuasiDM_and_transfersLocalQuasiFiniteness_of_isLocallyQuasiFinite
    (f : 𝒳 ⟶ 𝒴) (hf : IsLocallyQuasiFinite B S hS f) :
    IsQuasiDM B S hS f ∧ TransfersLocalQuasiFinitenessOnSpaceBaseChanges B S hS f := by
  refine ⟨(isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).1 hf.1, ?_⟩
  intro 𝒱 _h𝒱 g 𝒰 _h𝒰 h hh
  have hbc : IsLocallyQuasiFinite B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    isLocallyQuasiFinite_baseChange B S hS f g
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).swap
      (Bicategory.isTwoFibreProduct_swap
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g))
      hf
  exact isLocallyQuasiFinite_comp B S hS h
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd hh hbc

/-- **Stacks 06UF, (2) ⟹ (3).** If `f` is quasi-DM and transfers local quasi-finiteness to the
projections of its algebraic-space base changes, then each of those base changes has a
surjective, flat, locally finitely presented and locally quasi-finite cover by an algebraic
space which is locally quasi-finite over the base.

The cover is the one **Stacks 06UE** produces from the quasi-DM condition; it is locally
quasi-finite in the sense of Properties of Stacks, Section 04XB, hence in the sense of
**Stacks 06PU** by **Stacks 06UA**, and the second conjunct of clause (2) then makes its
composite to the base locally quasi-finite. -/
@[stacks 06UF "the implication (2) => (3), granted the substantial direction of Tag 06MF as
  `hPresentation`, which is how Tag 06UE is carried in this library"]
theorem locallyQuasiFiniteCoverOnEverySpaceBaseChange_of_isQuasiDM_of_transfers
    (hPresentation : Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM.{u, w} B S hS
      (BigFppfSite.contains_terminal B))
    (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiDM B S hS f)
    (htr : TransfersLocalQuasiFinitenessOnSpaceBaseChanges B S hS f) :
    LocallyQuasiFiniteCoverOnEverySpaceBaseChange B S hS f := by
  intro 𝒱 h𝒱 g
  obtain ⟨𝒰, h𝒰, p, hpS, hpF, hpL, hpQ⟩ :=
    hasQuasiFiniteFlatSpaceCoverOnEveryBaseChange_of_isQuasiDM B S hS
      (BigFppfSite.contains_terminal B) hPresentation f hf 𝒱 h𝒱 g
  have hprep := isRepresentableByAlgebraicSpaces_hom_of_source B S hS h𝒰 p
  have hp : IsLocallyQuasiFinite B S hS p :=
    isLocallyQuasiFinite_of_isLocallyQuasiFinite_hom B S hS p hprep hpQ
  exact ⟨𝒰, h𝒰, p, hpS, hpF, hpL, hp, htr 𝒱 h𝒱 g 𝒰 h𝒰 p hp⟩

/-- **Stacks 06UF, (3) ⟹ (4).** Every algebraic stack has a smooth surjective chart by a scheme
of the site, and a smooth 1-morphism is flat and locally of finite presentation, so the
universal clause (3) applied to that chart is clause (4). -/
@[stacks 06UF "the implication (3) => (4), unconditionally"]
theorem locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange_of_onEverySpaceBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : LocallyQuasiFiniteCoverOnEverySpaceBaseChange B S hS f) :
    LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f := by
  obtain ⟨U, a, haSmooth, haSurj⟩ := Stack.exists_smooth_surjective_schemeStack B S hS 𝒴
  exact ⟨Stack.schemeStack.{u, w} B S hS U,
    Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U, a, haSurj,
    isFlat_of_isSmooth B S hS a haSmooth,
    isLocallyOfFinitePresentation_of_isSmooth B S hS a haSmooth,
    hf _ (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) a⟩

/-- **Stacks 06UF, the quasi-DM conjunct of (4) ⟹ (1).** A locally quasi-finite flat cover of
`𝒳 ×_𝒴 𝒱` by an algebraic space over one algebraic space `𝒱` surjective, flat and locally of
finite presentation over `𝒴` makes `f` quasi-DM.

The cover is locally quasi-finite in the sense of **Stacks 06PU**, hence in the sense of
Properties of Stacks, Section 04XB by **Stacks 06UA**, which is clause (3) of **Stacks 06UE**;
that lemma's implication (3) ⟹ (1) is the conclusion. -/
@[stacks 06UF "the quasi-DM conjunct of the conclusion of (4) => (1), unconditionally. The
  local finite type and field-valued-fibre conjuncts of (4) => (1) are NOT carried"]
theorem isQuasiDM_of_locallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : LocallyQuasiFiniteCoverOnSomeFlatSpaceBaseChange B S hS f) :
    IsQuasiDM B S hS f := by
  obtain ⟨𝒱, h𝒱, g, hgS, hgF, hgL, 𝒰, h𝒰, p, hpS, hpF, hpL, hpQ, -⟩ := hf
  have hprep := isRepresentableByAlgebraicSpaces_hom_of_source B S hS h𝒰 p
  refine isQuasiDM_of_hasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange B S hS
    (BigFppfSite.contains_terminal B) f
    ⟨𝒱, h𝒱, g, hgS, hgF, hgL, 𝒰, h𝒰, p, hpS, hpF, hpL, ?_⟩
  exact Stack.isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology B S hS p hprep
    hpQ.2.1 hpQ.2.2

end AlgebraicGeometry.Stack.AlgebraicStacks

end
