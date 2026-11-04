module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyLiftingSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFromMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductPasting
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Residual gerbes of quasi-DM algebraic stacks (Stacks 06UI)

**Stacks 06UI** says that a quasi-DM algebraic stack `𝒳` has a residual gerbe at every point
`x ∈ |𝒳|`. Existence of the residual gerbe at `x` is, by **Stacks 06MU**, condition (1) of
**Stacks 06MT**, which this library spells `AlgebraicGeometry.Stack.HasSingletonPointMonomorphism`:
some algebraic stack `𝒵` admits a monomorphism `𝒵 ⟶ 𝒳` with `|𝒵|` a singleton mapping to `x`.

## The source's argument

By **Stacks 06MF** there is a scheme `W` with a surjective, flat, locally finitely presented and
locally quasi-finite 1-morphism `f : W ⟶ 𝒳`. Pick `w ∈ W` over `x` and let `u = Spec κ(w)`, so that
`ι : u ⟶ W` is a monomorphism. The self-intersection `R' = u ×_𝒳 u` of the point `ι ≫ f` has
target projection `R' ⟶ u` which factors as

* `R' ⟶ u ×_𝒳 W`, a base change of `ι`, hence a monomorphism, followed by
* `u ×_𝒳 W ⟶ u`, a base change of `f`, hence locally quasi-finite;

so `R' ⟶ u` is locally quasi-finite by **Stacks 06S1**, hence locally of finite type, hence locally
of finite presentation (**Stacks 06G4**, `u` being Noetherian), and flat because `u` is the
spectrum of a field. The quotient `[u/R']` is then an algebraic stack mapping fully faithfully to
`𝒳` (**Stacks 06FI**, **Stacks 04T4**), covered surjectively by `u`; full faithfulness gives a
monomorphism (**Stacks 04ZZ**), and the surjection from the one-point `u` makes its space of
points the singleton `{x}`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_relationTarget_of_mono`: the target projection of
  the self-intersection of `ι ≫ f` is locally quasi-finite, given Stacks 06S1.
* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_relationTarget_of_mono`: it is locally of
  finite presentation.
* `AlgebraicGeometry.Stack.exists_fullyFaithful_fieldSpectrumCover_of_isAbsolutelyQuasiDM_of`:
  every point of a quasi-DM algebraic stack is the image of a fully faithful 1-morphism from a
  one-point algebraic stack covered flatly and locally of finite presentation by the spectrum of a
  field.
* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_isAbsolutelyQuasiDM_of` and
  `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of`: the residual gerbe
  of a quasi-DM algebraic stack exists at every point, as condition (1) of Stacks 06MT and as the
  strictly full subcategory of Stacks 06MU, from the two inputs below.

## Implementation notes

The factorization of the target projection is computed on representing algebraic spaces. The
base change `Q = u ×_𝒳 W` of `f` is a 2-fibre product, and so is the base change
`T = Q ×_W u` of `ι`; pasting them (**Stacks 003Q**,
`CategoryTheory.Bicategory.isTwoFibreProduct_paste`) exhibits `T` as a second 2-fibre product of
the cospan `(ι ≫ f, ι ≫ f)`, so the comparison 1-morphism from the canonical self-intersection
to `T` given by terminality induces a split monomorphism of representing spaces
(`AlgebraicGeometry.Stack.representingMap_congr_twoIso`). The square of representing spaces of
`T` is cartesian over the represented cospan `Q ⟶ W ⟵ u`
(`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare`), so the projection
`T ⟶ Q` is a pullback of the monomorphism `yoneda.map ι`; the projection `Q ⟶ u` is locally
quasi-finite by the bridge of **Stacks 04XB** applied to the base change of `f`.

The source's quotient stack `[u/R']` is replaced by the strictly full subcategory of the objects
of `𝒳` lifting locally along `u ⟶ 𝒳`, which is algebraic by **Stacks 05UM** and the bootstrap
theorem **Stacks 04S6**
(`AlgebraicGeometry.Stack.exists_isAlgebraicStack_locallyLifts_of_fieldSpectrum`)
and is the essential image of `[u/R']`; so **Stacks 06FI**, and with it Artin's theorem, is not
used. This is `AlgebraicGeometry.Stack.hasFullyFaithfulFieldPointPresentationsOfRelation`.

The theorems above take two universally quantified statements as arguments: the implication
(1) ⟹ (2) of **Stacks 06MF**
(`AlgebraicGeometry.Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM`)
and **Stacks 06S1** (`AlgebraicGeometry.Stack.MonoLocallyQuasiFiniteOverField`). None of them is
registered against Stacks 06UI.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 06MX](https://stacks.math.columbia.edu/tag/06MX)
* [Stacks Project, Tag 06S1](https://stacks.math.columbia.edu/tag/06S1)
* [Stacks Project, Tag 06UI](https://stacks.math.columbia.edu/tag/06UI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06S1, as a statement.** A monomorphism of algebraic spaces into an algebraic space
locally quasi-finite over the spectrum of a field has source locally quasi-finite over that
field. -/
abbrev MonoLocallyQuasiFiniteOverField : Prop :=
  ∀ (F : FieldSpectrum B S hS) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
    IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
    ∀ (m : X ⟶ Y) (_ : Mono m) (q : Y ⟶ yoneda.obj F.base),
      Space.IsLocallyQuasiFinite B S hS q → Space.IsLocallyQuasiFinite B S hS (m ≫ q)

/-- The algebraic space represented by the spectrum of a field. -/
abbrev fieldSpectrumSpace (F : FieldSpectrum B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj F.base, isAlgebraicSpace_yoneda B S hS F.base⟩

/-- **The self-intersection of a residue-field point of a locally quasi-finite chart is locally
quasi-finite over the field.** Let `f : W ⟶ 𝒳` be a locally quasi-finite 1-morphism from a scheme
of the site to an algebraic stack and let `ι : Spec k ⟶ W` be a monomorphism out of the spectrum
of a field. Given Stacks 06S1, the target projection `R ⟶ Spec k` of the self-intersection
`R = Spec k ×_𝒳 Spec k` of `ι ≫ f` is locally quasi-finite.

It factors through the base change `Spec k ×_𝒳 W ⟶ Spec k` of `f`, which is locally quasi-finite,
by a monomorphism; see the module docstring. -/
theorem isLocallyQuasiFinite_relationTarget_of_mono
    (hmono : MonoLocallyQuasiFiniteOverField B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (W : BigFppfOver B S hS)
    (f : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (hf : IsLocallyQuasiFinite B S hS f.hom)
    (F : FieldSpectrum B S hS) (ι : F.base ⟶ W) [Mono ι]
    (R : AlgebraicSpaces B S hS)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS F.base) 𝒳.val
        (schemeStackMap.{u, w} B S hS ι ≫ f).hom.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p) :
    Space.IsLocallyQuasiFinite B S hS
      (SelfIntersection.relationTarget (U := fieldSpectrumSpace B S hS F)
        (PresheafOfCategories.sliceElementsEquivalenceOver F.base) eR).hom := by
  let k := schemeFibredCategory B S hS F.base
  let Wc := schemeFibredCategory B S hS W
  let ι' : k ⟶ Wc := schemeFibredCategoryMap B S hS ι
  let fc : Wc ⟶ 𝒳.val := f.hom
  let g : k ⟶ 𝒳.val := ι' ≫ fc
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver F.base
  let eW := PresheafOfCategories.sliceElementsEquivalenceOver W
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS fc.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) fc
  -- the base change `Q = k ×_{g, 𝒳, f} W` of the chart along the point
  let Qsq := twoFibreSquare g fc
  have hQ := isTwoFibreSquare g fc
  obtain ⟨Qs, hQs, ⟨eQ⟩⟩ :=
    isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS fc g hfrep
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base)
  have hQlqf := (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ h => Space.IsLocallyQuasiFinite B S hS h.hom)
    Qsq.fst _ Qs (yoneda.obj F.base) hQs (isAlgebraicSpace_yoneda B S hS F.base) eQ eU).mp
    (hasRelativeProperty_baseChange.{u, u, u + 1} B S hS
      (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ h => Space.IsLocallyQuasiFinite B S hS h.hom)
      Wc 𝒳.val k fc g Qsq hQ hfrep hf)
  -- the base change `T = Q ×_W k` of the point along the second projection
  let Tsq := twoFibreSquare Qsq.snd ι'
  obtain ⟨Ts, hTs, ⟨eT⟩⟩ :=
    isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS ι' Qsq.snd
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS ι) ⟨Qs, hQs, ⟨eQ⟩⟩
  have hfib : (twoFibreProductStructureFunctor B S hS Qsq.pt k Wc Qsq.snd ι').IsFibered :=
    Tsq.pt.property.isFibered
  have hpb := isPullback_representingMap_twoFibreProductSquare B S hS Qsq.pt k Wc Qs
    (yoneda.obj F.base) (yoneda.obj W) eQ eU eW Qsq.snd ι' Ts eT
  rw [representingMap_schemeFibredCategoryMap] at hpb
  have hmonoT : Mono (representingMap B S hS Tsq.pt Qsq.pt Ts Qs eT eQ Tsq.fst) :=
    hpb.mono_fst_of_mono
  -- the pasted rectangle is a 2-fibre product of `(g, g)`, as is the self-intersection
  let P : Bicategory.TwoCommSq g g := Qsq.paste Tsq
  have hP : Bicategory.IsTwoFibreProduct P :=
    Bicategory.isTwoFibreProduct_paste hQ (isTwoFibreSquare Qsq.snd ι')
  let C := twoFibreSquare g g
  have hC := isTwoFibreSquare g g
  let A := Bicategory.twoFibreProductPreHom hP C
  let D := Bicategory.twoFibreProductPreHom hC P
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hC (A.comp D)
    (Bicategory.TwoCommSq.PreHom.id C)
  have hsplit : representingMap B S hS C.pt Tsq.pt R.obj Ts eR eT A.hom ≫
      representingMap B S hS Tsq.pt C.pt Ts R.obj eT eR D.hom = 𝟙 R.obj := by
    refine (representingMap_comp B S hS R.obj Ts R.obj eR eT eR A.hom D.hom).symm.trans ?_
    refine (representingMap_congr_twoIso B S hS R.obj R.obj eR eR θ).trans ?_
    exact representingMap_id B S hS C.pt R.obj eR
  have hmonoA : Mono (representingMap B S hS C.pt Tsq.pt R.obj Ts eR eT A.hom) :=
    (IsSplitMono.mk' ⟨_, hsplit⟩).mono
  have hfact : representingMap B S hS C.pt k R.obj (yoneda.obj F.base) eR eU C.fst =
      (representingMap B S hS C.pt Tsq.pt R.obj Ts eR eT A.hom ≫
        representingMap B S hS Tsq.pt Qsq.pt Ts Qs eT eQ Tsq.fst) ≫
        representingMap B S hS Qsq.pt k Qs (yoneda.obj F.base) eQ eU Qsq.fst := by
    have h1 : representingMap B S hS C.pt k R.obj (yoneda.obj F.base) eR eU C.fst =
        representingMap B S hS C.pt k R.obj (yoneda.obj F.base) eR eU (A.hom ≫ P.fst) :=
      representingMap_congr_twoIso (𝒜 := C.pt) (𝒞 := k) (a := C.fst) (a' := A.hom ≫ P.fst)
        B S hS R.obj (yoneda.obj F.base) eR eU A.isoFst
    have h2 := representingMap_comp B S hS R.obj Ts (yoneda.obj F.base) eR eT eU A.hom P.fst
    have h3 := representingMap_comp B S hS Ts Qs (yoneda.obj F.base) eT eQ eU Tsq.fst Qsq.fst
    exact h1.trans (h2.trans ((congrArg
      (representingMap B S hS C.pt Tsq.pt R.obj Ts eR eT A.hom ≫ ·) h3).trans
      (Category.assoc _ _ _).symm))
  exact (congrArg (Space.IsLocallyQuasiFinite B S hS) hfact).mpr (hmono F R.property hQs
    (representingMap B S hS C.pt Tsq.pt R.obj Ts eR eT A.hom ≫
      representingMap B S hS Tsq.pt Qsq.pt Ts Qs eT eQ Tsq.fst) (mono_comp _ _) _ hQlqf)

/-- **The self-intersection of a residue-field point of a locally quasi-finite chart is locally
of finite presentation over the field.** It is locally quasi-finite by
`AlgebraicGeometry.Stack.isLocallyQuasiFinite_relationTarget_of_mono`, hence locally of finite
type, hence locally of finite presentation by **Stacks 06G4** part (1), the spectrum of a field
being Noetherian. -/
theorem isLocallyOfFinitePresentation_relationTarget_of_mono
    (hmono : MonoLocallyQuasiFiniteOverField B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (W : BigFppfOver B S hS)
    (f : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (hf : IsLocallyQuasiFinite B S hS f.hom)
    (F : FieldSpectrum B S hS) (ι : F.base ⟶ W) [Mono ι]
    (R : AlgebraicSpaces B S hS)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS F.base) 𝒳.val
        (schemeStackMap.{u, w} B S hS ι ≫ f).hom.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p) :
    Space.IsLocallyOfFinitePresentation B S hS
      (SelfIntersection.relationTarget (U := fieldSpectrumSpace B S hS F)
        (PresheafOfCategories.sliceElementsEquivalenceOver F.base) eR).hom :=
  Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS R.property
    (isAlgebraicSpace_yoneda B S hS F.base) _
    (hasEtaleLocalProperty_isLocallyNoetherian_fieldSpectrum B S hS F)
    (Space.holdsOnEveryEtaleChart_mono B S hS (fun _ h => h.1)
      (isLocallyQuasiFinite_relationTarget_of_mono B S hS hmono 𝒳 W f hf F ι R eR))

/-- **The fully faithful presentation of a field-valued point whose self-intersection is locally
of finite presentation over the field, as a statement.** Let `g : Spec k ⟶ 𝒳` be a 1-morphism from
the algebraic stack of the spectrum of a field, whose self-intersection `R = Spec k ×_𝒳 Spec k` is
represented by an algebraic space with target projection `R ⟶ Spec k` locally of finite
presentation. Then `g` factors, up to 2-isomorphism, as a surjective flat 1-morphism, locally of
finite presentation, onto an algebraic stack followed by a fully faithful 1-morphism.

In the source this is the quotient stack `[Spec k/R]`: algebraic by **Stacks 06FI**, its
projections being flat over the field and locally of finite presentation, covered surjectively by
`Spec k` (**Stacks 06FH**) and mapping fully faithfully to `𝒳` (**Stacks 04T4** part (6)). -/
abbrev HasFullyFaithfulFieldPointPresentationsOfRelation : Prop :=
  ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (g : schemeStack.{u, w} B S hS F.base ⟶ 𝒳) (R : AlgebraicSpaces B S hS)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS F.base) 𝒳.val
        g.hom.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p),
    Space.IsLocallyOfFinitePresentation B S hS
        (SelfIntersection.relationTarget (U := fieldSpectrumSpace B S hS F)
          (PresheafOfCategories.sliceElementsEquivalenceOver F.base) eR).hom →
      ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (i : 𝒵 ⟶ 𝒳)
        (z : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
        (CatFiberedInGroupoids.homFunctor i.hom).Full ∧
          (CatFiberedInGroupoids.homFunctor i.hom).Faithful ∧
            AlgebraicStacks.IsLocallyOfFinitePresentation B S hS z ∧
              IsSurjective B S hS z ∧ AlgebraicStacks.IsFlat B S hS z ∧ Nonempty (z ≫ i ≅ g)

/-- **The fully faithful presentation of a field-valued point whose self-intersection is locally
of finite presentation over the field.** The algebraic stack is the strictly full subcategory of
the objects of `𝒳` lifting locally along `g`, which is algebraic by **Stacks 05UM** and the
bootstrap theorem **Stacks 04S6** (`AlgebraicGeometry.Stack`
`.exists_isAlgebraicStack_locallyLifts_of_fieldSpectrum`), so that **Stacks 06FI** is not needed;
the fully faithful 1-morphism is its inclusion. The hypothesis on the target projection
`R ⟶ Spec k` is turned into the relative property of the first projection of the
self-intersection by the bridge of **Stacks 04XB**. -/
theorem hasFullyFaithfulFieldPointPresentationsOfRelation :
    HasFullyFaithfulFieldPointPresentationsOfRelation.{u, w} B S hS := by
  intro 𝒳 F g R eR hlfp
  have hrep := isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom g.hom).fst
    ⟨R.obj, R.property, ⟨eR⟩⟩ (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base)
  obtain ⟨hP, z, hz, hzlfp, hzsurj, hzflat⟩ :=
    exists_isAlgebraicStack_locallyLifts_of_fieldSpectrum 𝒳 F g
      ⟨hrep, (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS _ _ hrep R.obj
        (yoneda.obj F.base) R.property (isAlgebraicSpace_yoneda B S hS F.base) eR
        (PresheafOfCategories.sliceElementsEquivalenceOver F.base)).2 hlfp⟩
  exact ⟨_, fullSubcategoryInclusion 𝒳 _ hP, z, ObjectProperty.full_ι _,
    ObjectProperty.faithful_ι _, hzlfp, hzsurj, hzflat, ⟨eqToIso hz⟩⟩

/-- Every point of the target of a surjective 1-morphism from the stack of the spectrum of a field
is the image of the unique point of that stack. -/
private theorem eq_pointsMap_fieldSpectrumPoint_of_isSurjective
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (z : schemeStack.{u, w} B S hS F.base ⟶ 𝒵) (hz : IsSurjective B S hS z)
    (z' : AlgebraicStacks.points B S hS 𝒵) :
    z' = AlgebraicStacks.pointsMap B S hS z
      (pointClass B S hS _ _ (fieldSpectrumPoint.{u, w} B S hS F)) := by
  obtain ⟨p', rfl⟩ := hz z'
  exact congrArg _ ((subsingleton_points_fieldSpectrumStack.{u, w} B S hS F).elim _ _)

/-- **A point of a quasi-DM algebraic stack is the image of a fully faithful one-point
presentation, from two inputs of the source's argument.** Let `𝒳` be a quasi-DM algebraic
stack over `S` and `x ∈ |𝒳|`. Given the implication (1) ⟹ (2) of **Stacks 06MF** and
**Stacks 06S1**, there are an algebraic stack `𝒵`, a fully faithful 1-morphism `i : 𝒵 ⟶ 𝒳`
whose image on points is `{x}`, and a surjective, flat 1-morphism, locally of finite
presentation, from the algebraic stack of the spectrum of a field to `𝒵`.

This is the source's proof of **Stacks 06UI**, run at a single point `w` of the chart over `x`
rather than over the disjoint union of all of them. The chart `f : W ⟶ 𝒳` of Stacks 06MF is
surjective, so some point `q` of `|W|` maps to `x`; `w` is the point of the scheme `W` it names,
and `ι : Spec κ(w) ⟶ W` its residue field, a monomorphism. The self-intersection of `ι ≫ f` is
locally of finite presentation over `κ(w)` by
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_relationTarget_of_mono`, so `ι ≫ f` factors
as `z : Spec κ(w) ⟶ 𝒵` followed by a fully faithful `i : 𝒵 ⟶ 𝒳`. The space `|𝒵|` is the image of
the one point of `Spec κ(w)`, and that point maps to `q` in `|W|`, by the naturality of the
identification of the points of a represented stack with those of its scheme, hence to `x`. -/
theorem exists_fullyFaithful_fieldSpectrumCover_of_isAbsolutelyQuasiDM_of
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hpresentation : ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM.{u, w} B S hS hZ)
    (hmono : MonoLocallyQuasiFiniteOverField B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (i : 𝒵 ⟶ 𝒳),
      (CatFiberedInGroupoids.homFunctor i.hom).Full ∧
        (CatFiberedInGroupoids.homFunctor i.hom).Faithful ∧
          HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵 ∧
            Set.range (AlgebraicStacks.pointsMap B S hS i) = {x} := by
  obtain ⟨W, f, hsurj, -, -, hlqf⟩ := hpresentation 𝒳 h𝒳
  obtain ⟨q, hq⟩ := hsurj x
  let _ := pointTopology B S hS (schemeFibredCategory B S hS W)
  let w := pointsHomeomorphScheme B S hS W q
  have hκ := B.residueField_spec_contains W.left.property w
  let F := residueFieldSpectrum B S hS W w hκ
  let ι := residueFieldInclusion B S hS W w hκ
  have : Mono ι := mono_residueFieldInclusion B S hS W w hκ
  let g := schemeStackMap.{u, w} B S hS ι ≫ f
  obtain ⟨Rf, hRf, ⟨eR⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (schemeFibredCategory B S hS F.base) 𝒳.val g.hom.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base)
  obtain ⟨𝒵, i, z, hfull, hfaith, hzlfp, hzsurj, hzflat, ⟨α⟩⟩ :=
    hasFullyFaithfulFieldPointPresentationsOfRelation B S hS 𝒳 F g ⟨Rf, hRf⟩ eR
    (isLocallyOfFinitePresentation_relationTarget_of_mono B S hS hmono 𝒳 W f hlqf F ι
      ⟨Rf, hRf⟩ eR)
  let p₀ : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base) :=
    pointClass B S hS _ _ (fieldSpectrumPoint.{u, w} B S hS F)
  have hι : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ι) p₀ = q := by
    let _ := pointTopology B S hS (schemeFibredCategory B S hS F.base)
    refine (pointsHomeomorphScheme B S hS W).injective ?_
    refine (pointsHomeomorphScheme_naturality B S hS ι p₀).trans ?_
    have hmap : (BigFppfOver.toScheme B S hS).map ι =
        ((BigFppfOver.toScheme B S hS).obj W).fromSpecResidueField w :=
      B.inclusion.map_preimage _
    exact (congrArg (fun φ => φ (pointsHomeomorphScheme B S hS F.base p₀)) hmap).trans
      (Scheme.fromSpecResidueField_apply _ _)
  have hx : AlgebraicStacks.pointsMap B S hS i (AlgebraicStacks.pointsMap B S hS z p₀) = x :=
    calc AlgebraicStacks.pointsMap B S hS i (AlgebraicStacks.pointsMap B S hS z p₀)
        = AlgebraicStacks.pointsMap B S hS (z ≫ i) p₀ :=
          (congrFun (AlgebraicStacks.pointsMap_comp B S hS z i) p₀).symm
      _ = AlgebraicStacks.pointsMap B S hS g p₀ := by
          rw [AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS α.hom]
      _ = AlgebraicStacks.pointsMap B S hS f
            (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ι) p₀) :=
          congrFun (AlgebraicStacks.pointsMap_comp B S hS _ f) p₀
      _ = x := by rwa [hι]
  refine ⟨𝒵, i, hfull, hfaith, ⟨F, z, hzlfp, hzsurj, hzflat⟩,
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hx⟩, ?_⟩⟩
  rintro - ⟨z', rfl⟩
  rw [eq_pointsMap_fieldSpectrumPoint_of_isSurjective B S hS 𝒵 F z hzsurj z']
  exact hx

/-- **The residual gerbe of a quasi-DM algebraic stack exists, as condition (1) of Stacks 06MT,
from two inputs of the source's argument.** The fully faithful 1-morphism of
`AlgebraicGeometry.Stack.exists_fullyFaithful_fieldSpectrumCover_of_isAbsolutelyQuasiDM_of` is a
monomorphism by the implication (2) ⟹ (1) of **Stacks 04ZZ**, and its source has one point, lying
over `x`. -/
theorem hasSingletonPointMonomorphism_of_isAbsolutelyQuasiDM_of
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hpresentation : ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM.{u, w} B S hS hZ)
    (hmono : MonoLocallyQuasiFiniteOverField B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)) :
    HasSingletonPointMonomorphism B S hS 𝒳 x := by
  obtain ⟨𝒵, i, hfull, hfaith, ⟨F, z, -, hzsurj, -⟩, himg⟩ :=
    exists_fullyFaithful_fieldSpectrumCover_of_isAbsolutelyQuasiDM_of B S hS hZ hpresentation
      hmono 𝒳 h𝒳 x
  let p₀ : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base) :=
    pointClass B S hS _ _ (fieldSpectrumPoint.{u, w} B S hS F)
  refine ⟨𝒵, i, AlgebraicStacks.isMonomorphism_of_full_and_faithful B S hS i hfull hfaith,
    AlgebraicStacks.pointsMap B S hS z p₀,
    eq_pointsMap_fieldSpectrumPoint_of_isSurjective B S hS 𝒵 F z hzsurj, ?_⟩
  · have : AlgebraicStacks.pointsMap B S hS i (AlgebraicStacks.pointsMap B S hS z p₀) ∈
        Set.range (AlgebraicStacks.pointsMap B S hS i) := ⟨_, rfl⟩
    rwa [himg] at this

/-- **The residual gerbe of a quasi-DM algebraic stack exists, from two inputs of the source's
argument.** Let `𝒳` be a quasi-DM algebraic stack over `S` and `x ∈ |𝒳|`. Some strictly
full subcategory of `𝒳` is the residual gerbe of `𝒳` at `x` in the sense of **Stacks 06MU**: it
meets the specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT**.

This is the last step of the source's proof: the source `𝒵` of the fully faithful 1-morphism of
`AlgebraicGeometry.Stack.exists_fullyFaithful_fieldSpectrumCover_of_isAbsolutelyQuasiDM_of` is
covered by the spectrum of a field flatly, surjectively and locally of finite presentation, so it
is reduced and locally Noetherian with one point (**Stacks 06MP**), and its essential image in `𝒳`
is the residual gerbe at `x` (**Stacks 06MX**,
`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_full_of_faithful`). -/
theorem exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hpresentation : ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM.{u, w} B S hS hZ)
    (hmono : MonoLocallyQuasiFiniteOverField B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P := by
  obtain ⟨𝒵, i, hfull, hfaith, hcov, himg⟩ :=
    exists_fullyFaithful_fieldSpectrumCover_of_isAbsolutelyQuasiDM_of B S hS hZ hpresentation
      hmono 𝒳 h𝒳 x
  obtain ⟨P, -, hP, -⟩ :=
    exists_isResidualGerbeAt_of_full_of_faithful B S hS 𝒳 𝒵 i hfull hfaith hcov x himg
  exact ⟨P, hP⟩

end AlgebraicGeometry.Stack

end
