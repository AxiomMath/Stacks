module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.UnramifiedConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Factor
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Immersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Scheme
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified

/-!
# The conormal sheaf of an unramified local complete intersection morphism of spaces

Let `f : X ⟶ Y` be a local complete intersection morphism of algebraic spaces over a scheme `S`
which is formally unramified, and let `X ⊂ X'` be a universal first-order thickening of `X`
over `Y`.  The conormal sheaf `𝒞_{X/Y}` of Stacks 0607 is then finite locally free on the small
étale site of `X`.  This is the second clause of Stacks 06CB.

## Main definitions

* `AlgebraicGeometry.Space.RepresentableConormalSheafComparison`: the comparison between the
  conormal sheaf of a formally unramified morphism of *representable* algebraic spaces and the
  conormal sheaf of the corresponding morphism of schemes, which this development does not have;
  the section *What is not proved here* below says exactly what is missing.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_isLocalCompleteIntersection`:
  **Stacks 06CB, second clause**, granted that comparison.

## Implementation notes

The argument is the étale localization of the source.  Formal unramifiedness is not a
hypothesis: it is a field of the universal first-order thickening, which Stacks 0606 produces
for every formally unramified morphism, and the statement is about an arbitrary such thickening,
so nothing is chosen out of an existence statement.

Choose a surjective étale scheme chart `V` of `Y` and lift it, by Stacks 02X1, to a surjective
étale scheme chart `W' ⟶ X'` together with `W' ⟶ V` over `Y`.  Let `W ⊂ W'` be the inverse image
of `X ⊂ X'`.  Three things then hold at once, and they are what makes the chart usable:

* `W` is a *scheme*, being a closed subspace of one — so both `W` and `V` are representable,
  which is what the comparison is about.  This is the reason the chart is taken upstairs, on the
  ambient space of the thickening, and pulled back: an étale chart of `X` extended across the
  thickening would give a representable `W` but an only-algebraic `W'`, and Stacks 05ZR, which
  would make `W'` a scheme, is not available here.
* `W ⊂ W'` is a universal first-order thickening of `W` over `V`, by Stacks 060D (2), and
  `𝒞_{X/Y}` restricts along `W ⟶ X` to `𝒞_{W/V}`, by Stacks 060D (3).
* `W ⟶ V` is, up to the identification of `W` with a chart of `X`, the scheme morphism induced
  by `f` on a square of étale charts, so it is a local complete intersection morphism by the
  definition of Stacks 06C4 (1) and formally unramified by Stacks 04G8 (1) ⇒ (2).

Finite local freeness on the small étale site is insensitive to all of that localization, by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_iff` and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalModule_preimage_iff`, so the clause
reduces to the representable case, where the scheme-level statement
`AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection`
(Stacks 06B9) supplies the mathematics.

## What is not proved here

What separates the representable case from the scheme-level statement is a comparison of two
kinds, and **neither half exists in this library**:

1. finite local freeness of a module on the small étale site of a representable algebraic space
   against `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of the corresponding module on
   the Zariski site of the representing scheme;
2. the conormal sheaf of Stacks 0607 of a formally unramified morphism of representable
   algebraic spaces against `Stacks.Thickenings.universalConormalSheaf` of Stacks 04F4 of the
   corresponding morphism of schemes.

For (1) the comparison functor `AlgebraicGeometry.SmallEtale.associatedModule` (Stacks 03DU (4)
at `τ = étale`) and its adjunction are available, and the property transfer across it is proved
only for finite type, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteType.lean`; the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteLocallyFreeFpqcDescent.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteLocallyFreeOfRankEtaleLocal.lean` both record that
reflecting finite local freeness along it is not done, and
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteLocallyFreeRepresentable.lean` carries the same
comparison as a named hypothesis rather than proving it, for Stacks 03ZU.  For (2) every
co-occurrence of `AlgebraicGeometry.Space.conormalModule` with the scheme-level conormal sheaves
in the tree is prose: `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` compares the two
*conventions* and states nothing, and the identification of the two universal first-order
thickenings of a representable morphism, which clause (2) would need first, is nowhere stated.

So the two are carried together as the single named hypothesis
`AlgebraicGeometry.Space.RepresentableConormalSheafComparison` below, quantified over arbitrary
representable algebraic spaces and arbitrary universal first-order thickenings.  It is a
comparison and not the conclusion: its antecedent is the scheme-level finite local freeness,
which is discharged here by Stacks 06B9, and it says nothing about local complete
intersections.

## References

* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
* [Stacks Project, Tag 06B9](https://stacks.math.columbia.edu/tag/06B9)
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The missing comparison with the scheme-level conormal sheaf -/

/-- The comparison this development lacks: for a formally unramified morphism `g : V ⟶ U` of
algebraic spaces over `S` whose source and target are both representable by schemes, finite
local freeness of the conormal sheaf of Stacks 04F4 of the corresponding morphism of schemes
implies finite local freeness, on the small étale site, of the conormal sheaf of Stacks 0607 of
`g` relative to any universal first-order thickening.

Nothing about local complete intersections enters, and the conclusion of Stacks 06CB is not
granted: the antecedent carries the whole mathematical content.  The section *What is not proved
here* of this file says which two identifications are missing and which files record their
absence. -/
public abbrev RepresentableConormalSheafComparison : Prop :=
  ∀ {V U : AlgebraicSpaces B S hS} [V.1.IsRepresentable] [U.1.IsRepresentable] {g : V ⟶ U}
      (s : UniversalFirstOrderThickening B S hS g)
      [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (V.1.reprW.hom ≫ g.hom ≫ U.1.reprW.inv)))],
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (Stacks.Thickenings.universalConormalSheaf ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (V.1.reprW.hom ≫ g.hom ≫ U.1.reprW.inv)))) →
      SheafOfModules.IsFiniteLocallyFreeOnSite (conormalSheaf B S hS s)

/-! ### The clause at one étale chart of the thickening -/

/-- The second clause of Stacks 06CB, read at a given square of étale charts of the structure
morphism of the thickening whose chart of the ambient space is surjective on points. -/
private theorem isFiniteLocallyFreeOnSite_conormalSheaf_of_chart
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (t : UniversalFirstOrderThickening B S hS f)
    (hf : IsLocalCompleteIntersection B S hS f.hom)
    (hcmp : RepresentableConormalSheafComparison B S hS)
    (W' U' : AlgebraicSpaces B S hS)
    (hW'rep : W'.1.IsRepresentable) (hU'rep : U'.1.IsRepresentable)
    (g : W' ⟶ t.ambient) (r : W' ⟶ U') (φ : U' ⟶ Y)
    (hgEt : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g.hom)
    (hgSurj : IsSurjective B S hS g.hom)
    (hφEt : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf φ.hom)
    (hrφ : r ≫ φ = g ≫ t.toBase) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (conormalSheaf B S hS t) := by
  have hgE : IsEtale B S hS g.hom := isEtale_of_presheaf_etale B S hS hgEt
  have hφE : IsEtale B S hS φ.hom := isEtale_of_presheaf_etale B S hS hφEt
  -- The inverse image of the thickened subspace in the chart, a closed subspace of the chart.
  have hW : IsClosedSubspace B S hS (t.sub.preimage g.hom) :=
    isClosedSubspace_preimage B S hS g.hom t.sub t.ambient.2 W'.2 t.closedSub.2
  have hsq : IsPullback (t.sub.fromPreimage g.hom) (t.sub.preimage g.hom).ι t.sub.ι g.hom :=
    Subfunctor.isPullback_preimage g.hom t.sub
  have hsqS : IsPullback
      (ObjectProperty.homMk (t.sub.fromPreimage g.hom) :
        (⟨(t.sub.preimage g.hom).toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨t.sub.toFunctor, t.closedSub.2.1⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (t.sub.preimage g.hom).ι)
      (ObjectProperty.homMk t.sub.ι) g :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) hsq
  have hcE : IsEtale B S hS (t.sub.fromPreimage g.hom) :=
    isEtale_of_isPullback B S hS _ _ g _ hsqS.flip hgE
  -- The structure morphism of the thickening, read through the identification of the source.
  have hsubι : t.sub.ι ≫ t.toBase.hom = t.sourceIso.inv ≫ f.hom := by
    rw [← t.sourceIso_ι_toBase, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hrφh : r.hom ≫ φ.hom = g.hom ≫ t.toBase.hom :=
    congrArg (fun k : W' ⟶ Y => k.hom) hrφ
  have hkey : (t.sub.preimage g.hom).ι ≫ r.hom ≫ φ.hom
      = t.sub.fromPreimage g.hom ≫ t.sourceIso.inv ≫ f.hom := by
    rw [hrφh, ← hsubι, ← Category.assoc, ← hsq.w, Category.assoc]
  -- The chart morphism is formally unramified.
  have hιFU : FormallyUnramified (t.sub.preimage g.hom).ι :=
    formallyUnramified_of_isImmersion B S hS _ (isImmersion_of_isClosedImmersion B S hS hW.2)
  have hcompFU : FormallyUnramified ((t.sub.preimage g.hom).ι ≫ r.hom ≫ φ.hom) := by
    rw [hrφh]
    exact formallyUnramified_comp _ _ hιFU (formallyUnramified_comp _ _
      (formallyUnramified_of_etale B S hS g.hom hgEt)
      (formallyUnramified_of_isUniversalFirstOrderThickening B S hS t.sub t.toBase
        t.isUniversal))
  have hfuW : FormallyUnramified ((t.sub.preimage g.hom).ι ≫ r.hom) :=
    formallyUnramified_left_of_comp _ φ.hom
      (formallyUnramified_of_etale B S hS φ.hom hφEt) (by simpa using hcompFU)
  -- Every étale chart of the chart morphism is an étale chart of `f`.
  have hchart : ∀ P : MorphismProperty Scheme.{u}, HoldsOnEveryEtaleChart B S hS P f.hom →
      HoldsOnEveryEtaleChart B S hS P ((t.sub.preimage g.hom).ι ≫ r.hom) := by
    have hinv : IsIso t.sourceIso.inv :=
      ⟨t.sourceIso.hom, t.sourceIso.inv_hom_id, t.sourceIso.hom_inv_id⟩
    intro P hP U₁ V₁ a₁ b₁ h ha₁ hb₁ hc₁
    refine hP U₁ V₁ (a₁ ≫ t.sub.fromPreimage g.hom ≫ t.sourceIso.inv) (b₁ ≫ φ.hom) h ?_ ?_ ?_
    · have h₁ := isEtale_of_isIso B S hS t.sourceIso.inv U₁ _ (hcE U₁ a₁ ha₁)
      simpa using h₁
    · exact hφE V₁ b₁ hb₁
    · calc yoneda.map h ≫ b₁ ≫ φ.hom
          = (yoneda.map h ≫ b₁) ≫ φ.hom := by rw [Category.assoc]
        _ = (a₁ ≫ (t.sub.preimage g.hom).ι ≫ r.hom) ≫ φ.hom := by rw [hc₁]
        _ = a₁ ≫ (t.sub.preimage g.hom).ι ≫ r.hom ≫ φ.hom := by simp
        _ = a₁ ≫ t.sub.fromPreimage g.hom ≫ t.sourceIso.inv ≫ f.hom := by rw [hkey]
        _ = (a₁ ≫ t.sub.fromPreimage g.hom ≫ t.sourceIso.inv) ≫ f.hom := by simp
  -- The chart thickening, which Stacks 060D (2) provides.
  let htW : UniversalFirstOrderThickening B S hS
      (ObjectProperty.homMk ((t.sub.preimage g.hom).ι ≫ r.hom) :
        (⟨(t.sub.preimage g.hom).toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ U') :=
    { formallyUnramified := hfuW
      ambient := W'
      toBase := r
      sub := t.sub.preimage g.hom
      isUniversal := IsUniversalFirstOrderThickening.etaleLocalization B S hS t.sub t.toBase
        t.isUniversal φ hφE g hgE r hrφ (t.sub.preimage g.hom)
        (t.sub.fromPreimage g.hom) hsq
      sourceIso := Iso.refl _
      sourceIso_ι_toBase := by simp }
  -- Both sides are representable, so the comparison applies.
  have hWrep : (t.sub.preimage g.hom).toFunctor.IsRepresentable :=
    isRepresentable_of_isClosedSubspace B S hS hW hW'rep
  have := hU'rep
  have hfuScheme := map_of_holdsOnEveryEtaleChart_of_representable B S hS _ _
    (holdsOnEveryEtaleChart_of_formallyUnramified B S hS _ hfuW)
  have hlci := map_of_holdsOnEveryEtaleChart_of_representable B S hS _ _
    (hchart (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u}) hf)
  refine (isFiniteLocallyFreeOnSite_conormalSheaf_iff B S hS t).2 ?_
  refine (isFiniteLocallyFreeOnSite_conormalModule_preimage_iff B S hS t.closedSub g hgE
    hgSurj).2 ?_
  refine (isFiniteLocallyFreeOnSite_conormalSheaf_iff B S hS htW).1 ?_
  exact @hcmp (⟨(t.sub.preimage g.hom).toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) U' hWrep
    hU'rep (ObjectProperty.homMk ((t.sub.preimage g.hom).ι ≫ r.hom)) htW hfuScheme
    (@isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection _ _ _
      hfuScheme hlci)

/-! ### The second clause of Stacks 06CB -/

/-- **Stacks 06CB, second clause.**  For a local complete intersection morphism `f : X ⟶ Y` of
algebraic spaces over `S` which is formally unramified, the conormal sheaf `𝒞_{X/Y}` of
Stacks 0607 is finite locally free on the small étale site of `X`.

Formal unramifiedness is a field of the universal first-order thickening, and the statement is
about an arbitrary one.  The hypothesis `hcmp` is the comparison with the scheme-level
Stacks 06B9 which this library lacks; see the section *What is not proved here* of this file. -/
@[stacks 06CB "the conormal sheaf is finite locally free"]
public theorem isFiniteLocallyFreeOnSite_conormalSheaf_of_isLocalCompleteIntersection
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (t : UniversalFirstOrderThickening B S hS f)
    (hf : IsLocalCompleteIntersection B S hS f.hom)
    (hcmp : RepresentableConormalSheafComparison B S hS) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (conormalSheaf B S hS t) := by
  obtain ⟨Vst, q, hqSurj, hqEt⟩ := Y.2.exists_atlas
  obtain ⟨Ust, p, α, hcomm, hpSurj, hpEt⟩ :=
    exists_surjective_etale_presentation_lift B S hS t.ambient.2 Y.2 t.toBase.hom Vst q
      hqSurj hqEt
  refine isFiniteLocallyFreeOnSite_conormalSheaf_of_chart B S hS t hf hcmp
    ⟨yoneda.obj Ust, isAlgebraicSpace_yoneda B S hS Ust⟩
    ⟨yoneda.obj Vst, isAlgebraicSpace_yoneda B S hS Vst⟩ inferInstance inferInstance
    (ObjectProperty.homMk p) (ObjectProperty.homMk (yoneda.map α)) (ObjectProperty.homMk q)
    hpEt (isSurjective_of_presheafSurjective B S hS p hpSurj) hqEt
    (ObjectProperty.hom_ext _ hcomm.symm)

end AlgebraicGeometry.Space

end
