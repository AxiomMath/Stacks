module

public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSiteLimitCone
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
import all StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Properness over an affine base object of the site, with no bound on the index

Let `B` be a big fppf site over a scheme `S`, let `T_i` be an object of the big fppf site of `S`
whose underlying scheme is affine, and let `z : Z ⟶ h_{T_i}` be a quasi-compact algebraic space
over the representable presheaf of `T_i`. This file collects what properness of the base change
of `z` along a morphism `m : T_j ⟶ T_i` of affine objects needs, with **no cardinality
hypothesis** and no `AlgebraicGeometry.Space.ChartsBounded` hypothesis.

Properness is separatedness, finite type and universal closedness
(`AlgebraicGeometry.Space.IsProper`). Over an affine base object the finite-type conjunct needs
no descent at all: the base change of `z` is locally of finite type because `z` is, and it is
quasi-compact because its source is quasi-compact and its target is a representable affine,
hence quasi-separated. That is the content of
`AlgebraicGeometry.Space.isFiniteType_pullback_fst_of_isAffine` below.

The universally-closed conjunct **does** descend, and that is the main content of this file. It
is reached through Chow's lemma, which asks for its base object to be presented with underlying
scheme *literally* `Spec A` (`AlgebraicGeometry.Space.exists_chowSchemeCover_over_base`); that
presentation hypothesis is removed here, an object of the site whose underlying scheme is merely
`IsAffine` being isomorphic to such a presentation because `Spec Γ` of a contained affine scheme
is contained (`AlgebraicGeometry.Space.contains_specGammaTop`, `Scheme.size` being an
isomorphism invariant). Chow's lemma then produces a proper surjective cover of `Z` by a scheme
of the site which is separated, quasi-compact and locally of finite type over the base; base
changing that cover turns universal closedness at the limit into **properness of a morphism of
schemes** at the limit, where the cutoff-free scheme-level Stacks 081F applies, and Stacks 03XD
and 08AJ carry the conclusion back.

In the bounded development universal closedness descent is not proved at all: it sits on the
unproved hypothesis `AlgebraicGeometry.Space.HasUniversallyClosedStageDescent` of
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/ProperMorphismDescent.lean`. So the
results below are not a reindexing of something the library has; they discharge that input in
the affine-base setting, and need neither Stacks 0850 nor any bound on the index category.

**What is assumed rather than proved: separatedness at the starting stage.** Chow's lemma
consumes separatedness of `z`, and the affine-base size-free form of Stacks 0851 is not
developed here, so `z` is assumed separated. That hypothesis is genuinely needed by the route
and is available in the intended application, where the family at the stage is of finite
presentation, flat and proper over the affine base. Separatedness is *not* a property of the
form `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, so the chart reduction that gives the
flatness and relative-dimension analogues over an affine base cannot give it.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_pullback_fst_of_isAffine`: the base change of a
  locally-of-finite-type morphism from a quasi-compact algebraic space to a representable affine
  base object is of finite type, at every stage and with no descent.
* `AlgebraicGeometry.Space.exists_specPresentation_of_isAffine`: an object of the big fppf
  category over `S` with affine underlying scheme is isomorphic to one whose underlying scheme
  is literally the spectrum of a ring contained in the site.
* `AlgebraicGeometry.Space.exists_chowSchemeCover_over_isAffine_base`: **Stacks 089J over a base
  object of the site with affine underlying scheme**, with no presentation hypothesis.
* `AlgebraicGeometry.Space.exists_universallyClosed_pullback_fst_of_limit`: universal closedness
  descends from the limit to a stage, with no cardinality hypothesis, for a morphism separated
  at the starting stage. This is the input the bounded development leaves open.
* `AlgebraicGeometry.Space.exists_isProper_pullback_fst_of_isProper_limit` and
  `AlgebraicGeometry.Space.exists_isProper_isPullback_of_isProper_limit`: the affine-base,
  size-free form of **Stacks 08K1** with separatedness at the starting stage assumed, in the
  chosen-pullback and arbitrary-cartesian-square shapes.

## Implementation notes

The conclusion of `AlgebraicGeometry.Space.exists_chowSchemeCover_over_isAffine_base` records
separatedness, quasi-compactness and local finite type of the morphism of schemes underlying
`ψ` rather than the H-quasi-projectivity that
`AlgebraicGeometry.Space.exists_chowSchemeCover_over_base` produces. Those three are its
consequences and are what consumers use; unlike H-quasi-projectivity, whose definition names a
relative projective space over the base, they are visibly invariant under composition with the
isomorphism transporting the base object, so no comparison of projective spaces is needed.

The base change of the Chow cover along a morphism of the system is built exactly as the chart
of a base change is built in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineBasePropertyDescent.lean`; the three
category-theoretic lemmas that construction and the comparison with the `Over`-category shape of
the scheme-level descent need are taken from
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/DescendingMorphismProperties.lean`, namely
`AlgebraicGeometry.Space.isPullback_chart_baseChange`,
`CategoryTheory.prop_snd_iff_of_isPullback` and
`CategoryTheory.prop_overPullback_map_left_iff_pullback_snd`.

Because the stage produced by the universal-closedness descent already carries the other two
conjuncts — separatedness by base change from the hypothesis, finite type at every stage — no
common upper bound in the index category has to be taken, unlike in the bounded development.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

section AffineRepresentable

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

variable {Ti Tj : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

include hZ in
/-- **The base change of a quasi-compact algebraic space along a morphism of affine objects of
the site is quasi-compact.** -/
theorem isQuasiCompactSpace_pullback_yoneda_map_of_isAffine
    (hTi : IsAffine ((BigFppfOver.toScheme B S hS).obj Ti))
    (hTj : IsAffine ((BigFppfOver.toScheme B S hS).obj Tj))
    (z : Z ⟶ yoneda.obj Ti) (hZalg : IsAlgebraicSpace B S hS Z)
    (hqc : IsQuasiCompactSpace B S hS Z) (m : Tj ⟶ Ti) :
    IsQuasiCompactSpace B S hS (pullback (yoneda.map m) z) :=
  isQuasiCompactSpace_pullback B S hS hZ (yoneda.map m) z
    (isAlgebraicSpace_yoneda B S hS Tj) (isAlgebraicSpace_yoneda B S hS Ti)
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS Tj hTj) hqc
    (isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS hZ Ti hTi)

include hZ in
/-- **A locally-of-finite-type morphism from a quasi-compact algebraic space to a representable
affine base object is of finite type.** Quasi-compactness of the morphism is Stacks 073B part
(3): every base change along a morphism from a quasi-compact algebraic space has quasi-compact
source, the source being quasi-compact and the target quasi-separated. -/
theorem isFiniteType_of_isAffine_target
    (hTi : IsAffine ((BigFppfOver.toScheme B S hS).obj Ti))
    (z : Z ⟶ yoneda.obj Ti) (hZalg : IsAlgebraicSpace B S hS Z)
    (hqc : IsQuasiCompactSpace B S hS Z) (hft : IsLocallyOfFiniteType B S hS z) :
    IsFiniteType B S hS z := by
  refine ⟨hft, ?_⟩
  intro W hWalg hWqc g
  exact isQuasiCompactSpace_pullback B S hS hZ g z hWalg
    (isAlgebraicSpace_yoneda B S hS Ti) hWqc hqc
    (isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS hZ Ti hTi)

include hZ in
/-- **The finite-type conjunct of properness over an affine base object needs no descent.**

Let `z : Z ⟶ h_{T_i}` be a locally-of-finite-type morphism from a quasi-compact algebraic space
to the presheaf represented by an object of the site with affine underlying scheme, and let
`m : T_j ⟶ T_i` be a morphism to it from another such object. Then the base change of `z` along
`h_m` is of finite type.

It is locally of finite type as a base change of `z` (Stacks 03XH), and quasi-compact by
Stacks 073B part (3): its source is quasi-compact, being a base change of the quasi-compact `Z`
along a morphism between representable affines, and its target `h_{T_j}` is quasi-separated,
being representable by an affine scheme. No property of the system of bases is used, so this
holds at *every* stage of any inverse system of affine objects, and in particular needs no bound
on the index category. -/
theorem isFiniteType_pullback_fst_of_isAffine
    (hTi : IsAffine ((BigFppfOver.toScheme B S hS).obj Ti))
    (hTj : IsAffine ((BigFppfOver.toScheme B S hS).obj Tj))
    (z : Z ⟶ yoneda.obj Ti) (hZalg : IsAlgebraicSpace B S hS Z)
    (hqc : IsQuasiCompactSpace B S hS Z) (hft : IsLocallyOfFiniteType B S hS z)
    (m : Tj ⟶ Ti) :
    IsFiniteType B S hS (pullback.fst (yoneda.map m) z) := by
  exact isFiniteType_of_isAffine_target B S hS hZ hTj _
    (isAlgebraicSpace_pullback B S hS (yoneda.map m) z (isAlgebraicSpace_yoneda B S hS Tj) hZalg
      (isAlgebraicSpace_yoneda B S hS Ti))
    (isQuasiCompactSpace_pullback_yoneda_map_of_isAffine B S hS hZ hTi hTj z hZalg hqc m)
    (IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback (yoneda.map m) z)
      hZalg (isAlgebraicSpace_yoneda B S hS Ti) hft)

end AffineRepresentable

/-! ### Chow's lemma over a base object of the site with affine underlying scheme -/

section ChowAffineBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The site contains `Spec Γ` of an object with affine underlying scheme, and that spectrum
is the underlying scheme of an object of the site isomorphic to the given one.**

`AlgebraicGeometry.Space.exists_chowSchemeCover_over_base` asks for its base object to be
presented as `Over.mk (h : B.obj hA ⟶ B.obj hS)` with underlying scheme *literally* `Spec A`.
An object `T` of the big fppf category over `S` whose underlying scheme is merely `IsAffine` is
isomorphic to such a presentation: `Spec Γ(T, ⊤)` lies in the site because it is isomorphic to
the underlying scheme of `T`, which lies in the site, and `Scheme.size` is an isomorphism
invariant (`AlgebraicGeometry.Space.contains_specGammaTop`). -/
theorem exists_specPresentation_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    ∃ (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (h : B.obj hA ⟶ B.obj hS)
      (ι : T ⟶ Over.mk h), IsIso ι := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  set V : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj T
  refine ⟨Γ(V, ⊤), contains_specGammaTop B V T.left.2,
    ObjectProperty.homMk (V.isoSpec.inv ≫ B.inclusion.map T.hom), ?_⟩
  refine ⟨Over.homMk (ObjectProperty.homMk V.isoSpec.hom) ?_, ?_⟩
  · exact ObjectProperty.hom_ext _ (V.isoSpec.hom_inv_id_assoc _)
  · exact ⟨Over.homMk (ObjectProperty.homMk V.isoSpec.inv) (ObjectProperty.hom_ext _ rfl),
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ V.isoSpec.hom_inv_id),
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ V.isoSpec.inv_hom_id)⟩

/-- **Chow's lemma for algebraic spaces over a base object of the site whose underlying scheme
is affine, [Stacks, Tag 089J].**

Let `T` be an object of the big fppf category over `S` whose underlying scheme is affine, and
let `X` be an algebraic space over `S` with a separated morphism of finite type `g : X ⟶ h_T`.
Then there are an object `X'` of the site, a morphism `ψ : X' ⟶ T` and a proper surjective
morphism `p : h_{X'} ⟶ X` with `p ≫ g = h_ψ`, such that the morphism of schemes underlying
`ψ` is separated, quasi-compact and locally of finite type.

This removes the presentation hypothesis of
`AlgebraicGeometry.Space.exists_chowSchemeCover_over_base`, which asks for the underlying
scheme of the base object to be literally `Spec A`: the given object is transported along the
isomorphism of `AlgebraicGeometry.Space.exists_specPresentation_of_isAffine` to such a
presentation, Chow's lemma is applied there, and the resulting cover is transported back.
Separatedness and finite type of `g` travel across an isomorphism of arrows by
`AlgebraicGeometry.Space.isSeparated_of_arrowIso` and
`AlgebraicGeometry.Space.isFiniteType_of_arrowIso`.

The three conclusions about `ψ` replace the H-quasi-projectivity that
`AlgebraicGeometry.Space.exists_chowSchemeCover_over_base` produces: they are its consequences
(`AlgebraicGeometry.IsHQuasiProjective.isSeparated`, `.quasiCompact` and
`.locallyOfFiniteType`), they are what consumers of Chow's lemma use, and unlike
H-quasi-projectivity they are visibly invariant under composition with the transporting
isomorphism. -/
theorem exists_chowSchemeCover_over_isAffine_base (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj T) (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g) :
    ∃ (X' : BigFppfOver B S hS) (ψ : X' ⟶ T) (p : yoneda.obj X' ⟶ X),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ g = yoneda.map ψ ∧
        _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map ψ) ∧
        _root_.AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map ψ) ∧
        _root_.AlgebraicGeometry.LocallyOfFiniteType
          ((BigFppfOver.toScheme B S hS).map ψ) := by
  obtain ⟨A, hA, h, ι, hιiso⟩ := exists_specPresentation_of_isAffine B S hS T hT
  have := hιiso
  have : IsIso (yoneda.map ι) := inferInstance
  -- transport `g` to a morphism to the `Spec A` presentation of the base
  have hsep' : IsSeparated B S hS (g ≫ yoneda.map ι) :=
    isSeparated_of_arrowIso B S hS g (g ≫ yoneda.map ι) (𝟙 X) (yoneda.map ι)
      (by rw [Category.id_comp]) hsep
  have hft' : IsFiniteType B S hS (g ≫ yoneda.map ι) :=
    isFiniteType_of_arrowIso B S hS g (g ≫ yoneda.map ι) (𝟙 X) (yoneda.map ι)
      (by rw [Category.id_comp]) hft
  obtain ⟨X', ψ', p, hp, hpsurj, hpψ, hqp⟩ :=
    exists_chowSchemeCover_over_base B S hS A hA h hX (g ≫ yoneda.map ι) hsep' hft'
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨X', ψ' ≫ inv ι, p, hp, hpsurj, ?_, ?_, ?_, ?_⟩
  · rw [yoneda.map_comp, ← hpψ]
    simp
  all_goals
    rw [Functor.map_comp]
    have : IsIso ((BigFppfOver.toScheme B S hS).map (inv ι)) := Functor.map_isIso _ _
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u}) _ _).mpr hqp.isSeparated
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (@_root_.AlgebraicGeometry.QuasiCompact.{u}) _ _).mpr hqp.quasiCompact
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u}) _ _).mpr hqp.locallyOfFiniteType

end ChowAffineBase

section CoverOverAffineBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Ti Tj : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X' : BigFppfOver B S hS}

/-- **The base change along `h_m` of a cover `p : h_{X'} ⟶ Z` of an algebraic space over the
representable base `h_{T_i}`.** Its source is the representable `h_{X' ×_{T_i} T_j}`, formed in
the site. -/
private noncomputable def baseChangeCover (z : Z ⟶ yoneda.obj Ti) (p : yoneda.obj X' ⟶ Z)
    (ψ : X' ⟶ Ti) (hψ : yoneda.map ψ = p ≫ z) (m : Tj ⟶ Ti) :
    yoneda.obj (pullback ψ m) ⟶ pullback (yoneda.map m) z :=
  pullback.lift (yoneda.map (pullback.snd ψ m)) (yoneda.map (pullback.fst ψ m) ≫ p) (by
    rw [Category.assoc, ← hψ, ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition])

/-- The base change of the cover is a base change of the cover. -/
private theorem isPullback_baseChangeCover (z : Z ⟶ yoneda.obj Ti) (p : yoneda.obj X' ⟶ Z)
    (ψ : X' ⟶ Ti) (hψ : yoneda.map ψ = p ≫ z) (m : Tj ⟶ Ti) :
    IsPullback (yoneda.map (pullback.fst ψ m)) (baseChangeCover z p ψ hψ m) p
      (pullback.snd (yoneda.map m) z) := by
  have h : IsPullback (yoneda.map (pullback.snd ψ m)) (yoneda.map (pullback.fst ψ m))
      (yoneda.map m) (p ≫ z) := by
    rw [← hψ]
    exact ((IsPullback.of_hasPullback ψ m).flip).map yoneda
  exact isPullback_chart_baseChange p z (yoneda.map m) _ _ h

/-- The base change of the cover lies over the base change of the structure morphism. -/
private theorem baseChangeCover_comp_fst (z : Z ⟶ yoneda.obj Ti) (p : yoneda.obj X' ⟶ Z)
    (ψ : X' ⟶ Ti) (hψ : yoneda.map ψ = p ≫ z) (m : Tj ⟶ Ti) :
    baseChangeCover z p ψ hψ m ≫ pullback.fst (yoneda.map m) z =
      yoneda.map (pullback.snd ψ m) :=
  pullback.lift_fst _ _ _

variable (B) (S) (hS)

end CoverOverAffineBase

/-! ### Universal closedness and properness descend at an affine base, given separatedness -/

section ProperDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) {c : Cone D}

include hZ in
/-- **Universal closedness descends from the limit to a stage at an affine base, with no
cardinality hypothesis, for a morphism which is already separated at the starting stage.**

Let `D` be a cofiltered inverse system of affine objects of the big fppf site over `S` whose
cone `c` has a limiting cone of underlying schemes, let `i` be a stage, and let
`z : Z ⟶ T_i` be a quasi-compact algebraic space over the representable presheaf `T_i` attached
to `D.obj i`, with `z` separated and locally of finite type. If the base change of `z` along the
leg of `c` at `i` is universally closed, then its base change along `D.map g` is universally
closed for some `g : j ⟶ i`.

This is the input that the bounded development lacks outright: there, universal closedness
descent is an unproved hypothesis,
`AlgebraicGeometry.Space.HasUniversallyClosedStageDescent` of
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/ProperMorphismDescent.lean`. The
route taken here needs neither Stacks 0850 nor any bound on the index category.

Separatedness and finite type of `z` let Chow's lemma over the affine base object
(`AlgebraicGeometry.Space.exists_chowSchemeCover_over_isAffine_base`) produce a scheme `X'` of
the site, a morphism `ψ : X' ⟶ T_i` which is separated, quasi-compact and locally of finite type
on underlying schemes, and a proper surjective `p : h_{X'} ⟶ Z` over `T_i`. Base changing `p`
along a morphism of the system gives a proper surjective cover of the base change of `z`, lying
over the base change of `ψ`. At the limit, universal closedness of the base change of `z`
composes with properness of that cover to make the base change of `ψ` universally closed, and
with separatedness and local finite type — which are base changes of the corresponding
properties of `ψ` — that base change is a **proper morphism of schemes**. The cutoff-free
scheme-level Stacks 081F
(`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit`) then descends properness of `ψ` to a
stage, and Stacks 03XD together with Stacks 08AJ
(`AlgebraicGeometry.Space.universallyClosed_of_isSurjective_comp`) push universal closedness
back from the cover to the base change of `z` at that stage. -/
theorem exists_universallyClosed_pullback_fst_of_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZalg : IsAlgebraicSpace B S hS Z) (hqc : IsQuasiCompactSpace B S hS Z)
    (hft : IsLocallyOfFiniteType B S hS z) (hsep : IsSeparated B S hS z)
    (huc : UniversallyClosed B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) z)) :
    ∃ (j : I) (g : j ⟶ i), UniversallyClosed B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) := by
  classical
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : EssentiallySmall.{u} I := inferInstance
  have hTiAff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) := (D.obj i).property
  -- Chow's lemma at the stage `i`
  obtain ⟨X', ψ, p, hp, hpsurj, hpψ, hψsep, hψqc, hψft⟩ :=
    exists_chowSchemeCover_over_isAffine_base B S hS
      ((BigAffineFppf.inclusion B S hS).obj (D.obj i)) hTiAff hZalg z hsep
      (isFiniteType_of_isAffine_target B S hS hZ hTiAff z hZalg hqc hft)
  have hpb : ∀ {Tm : BigFppfOver B S hS}
      (m : Tm ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      IsAlgebraicSpace B S hS (pullback (yoneda.map m) z) := fun m ↦
    isAlgebraicSpace_pullback B S hS (yoneda.map m) z (isAlgebraicSpace_yoneda B S hS _) hZalg
      (isAlgebraicSpace_yoneda B S hS _)
  -- the base change of the cover along any morphism of the site into the stage
  have hcover : ∀ {Tm : BigFppfOver B S hS}
      (m : Tm ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      UniversallyClosed B S hS (baseChangeCover z p ψ hpψ.symm m) ∧
        IsSurjective B S hS (baseChangeCover z p ψ hpψ.symm m) := by
    intro Tm m
    have hsq := isPullback_baseChangeCover z p ψ hpψ.symm m
    exact ⟨(isProper_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS X') (hpb m) hZalg hsq hp).2.2,
      isSurjective_of_isPullback_presheaf (isAlgebraicSpace_yoneda B S hS X') (hpb m) hZalg hsq
        hpsurj⟩
  -- the scheme-level descent problem at the stage
  set Y₀ : Over ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) :=
    Over.mk (𝟙 ((D ⋙ BigAffineFppf.toScheme B S hS).obj i)) with hY₀
  set X₀ : Over ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) :=
    Over.mk ((BigFppfOver.toScheme B S hS).map ψ) with hX₀
  set f₀ : X₀ ⟶ Y₀ := Over.homMk ((BigFppfOver.toScheme B S hS).map ψ) with hf₀
  -- the two directions of the comparison between the scheme-level base change and `ψ` at a
  -- morphism of the site
  have hcompare : ∀ {Tm : BigFppfOver B S hS}
      (m : Tm ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i))
      (t : (BigFppfOver.toScheme B S hS).obj Tm ⟶
        (D ⋙ BigAffineFppf.toScheme B S hS).obj i),
      t = (BigFppfOver.toScheme B S hS).map m →
      (_root_.AlgebraicGeometry.IsProper ((Over.pullback t).map f₀).left ↔
        _root_.AlgebraicGeometry.IsProper
          ((BigFppfOver.toScheme B S hS).map (pullback.snd ψ m))) := by
    intro Tm m t ht
    subst ht
    rw [CategoryTheory.prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsProper.{u})
      ((BigFppfOver.toScheme B S hS).map ψ) ((BigFppfOver.toScheme B S hS).map m)]
    exact CategoryTheory.prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsProper.{u})
      (IsPullback.of_hasPullback _ _)
      ((IsPullback.of_hasPullback ψ m).map (BigFppfOver.toScheme B S hS))
  -- separatedness and local finite type of every base change of `ψ`, at the scheme level
  have hbase : ∀ {Tm : BigFppfOver B S hS}
      (m : Tm ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      _root_.AlgebraicGeometry.IsSeparated
          ((BigFppfOver.toScheme B S hS).map (pullback.snd ψ m)) ∧
        _root_.AlgebraicGeometry.LocallyOfFiniteType
          ((BigFppfOver.toScheme B S hS).map (pullback.snd ψ m)) := by
    intro Tm m
    have hsq := (IsPullback.of_hasPullback ψ m).map (BigFppfOver.toScheme B S hS)
    exact ⟨MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsSeparated.{u})
        hsq hψsep,
      MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.LocallyOfFiniteType.{u})
        hsq hψft⟩
  -- at the limit, the base change of `ψ` is a proper morphism of schemes
  have hlimProper : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd ψ ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))) := by
    obtain ⟨hcucLim, -⟩ := hcover ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
    have hcomp : UniversallyClosed B S hS
        (yoneda.map (pullback.snd ψ ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))) := by
      rw [← baseChangeCover_comp_fst z p ψ hpψ.symm
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i))]
      exact universallyClosed_comp B S hS
        (hpb _) (isAlgebraicSpace_yoneda B S hS _) _ _ hcucLim huc
    have hucScheme : _root_.AlgebraicGeometry.UniversallyClosed
        ((BigFppfOver.toScheme B S hS).map
          (pullback.snd ψ ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))) :=
      (presheaf_yoneda_map_iff B S hS
        (P := @_root_.AlgebraicGeometry.UniversallyClosed.{u}) inferInstance _).mp
        ((presheaf_universallyClosed_iff B S hS (isAlgebraicSpace_yoneda B S hS _)
          (isAlgebraicSpace_yoneda B S hS _)
          (Functor.relativelyRepresentable.map yoneda _)).mpr hcomp)
    obtain ⟨hs, hl⟩ := hbase ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
    exact (_root_.AlgebraicGeometry.isProper_iff _).mpr ⟨hs, hucScheme, hl⟩
  -- the scheme-level descent, Stacks 081F
  have hEaff : ∀ k : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj k) := fun k ↦
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj k)
  have : ∀ {k l : I} (g : k ⟶ l),
      _root_.AlgebraicGeometry.IsAffineHom ((D ⋙ BigAffineFppf.toScheme B S hS).map g) := by
    intro k l g
    have := hEaff k
    have := hEaff l
    exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  have : IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) := hEaff i
  have : CompactSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) :=
    Scheme.compactSpace_of_isAffine _
  have : QuasiSeparatedSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) := inferInstance
  have : IsAffine Y₀.left := hEaff i
  have : CompactSpace Y₀.left := Scheme.compactSpace_of_isAffine _
  have : QuasiSeparatedSpace Y₀.left := inferInstance
  have := hψqc
  have : CompactSpace X₀.left :=
    _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map ψ)
  have := hψsep
  have : QuasiSeparatedSpace X₀.left :=
    _root_.AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map ψ)
  have : _root_.AlgebraicGeometry.LocallyOfFiniteType f₀.left := hψft
  have : _root_.AlgebraicGeometry.IsProper
      ((Over.pullback (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i)).map f₀).left :=
    (hcompare ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) _ rfl).mpr hlimProper
  obtain ⟨j, g, hjProper⟩ := AlgebraicGeometry.exists_isProper_baseChange_of_isLimit
    (D ⋙ BigAffineFppf.toScheme B S hS) ((BigAffineFppf.toScheme B S hS).mapCone c) i
    hc X₀ Y₀ f₀
  -- push universal closedness back from the cover to the base change of `z`
  refine ⟨j, g, ?_⟩
  have hjScheme : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd ψ ((BigAffineFppf.inclusion B S hS).map (D.map g)))) :=
    (hcompare ((BigAffineFppf.inclusion B S hS).map (D.map g)) _ rfl).mp hjProper
  have := hjScheme
  obtain ⟨hcucj, hsurjj⟩ := hcover ((BigAffineFppf.inclusion B S hS).map (D.map g))
  have hcompj : UniversallyClosed B S hS
      (baseChangeCover z p ψ hpψ.symm ((BigAffineFppf.inclusion B S hS).map (D.map g)) ≫
        pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) := by
    rw [baseChangeCover_comp_fst]
    exact universallyClosed_yoneda_map B S hS _ inferInstance
  exact universallyClosed_of_isSurjective_comp B S hS (isAlgebraicSpace_yoneda B S hS _)
    (hpb _) (isAlgebraicSpace_yoneda B S hS _) _ _ hcompj hsurjj

include hZ in
/-- **Properness descends from the limit to a stage at an affine base, with no cardinality
hypothesis, for a morphism which is already separated at the starting stage.** This is the
affine-base, size-free form of **Stacks 08K1**, with separatedness at the starting stage taken
as a hypothesis.

Let `D` be a cofiltered inverse system of affine objects of the big fppf site over `S` whose
cone `c` has a limiting cone of underlying schemes, let `i` be a stage, and let `z : Z ⟶ T_i` be
a quasi-compact algebraic space over the representable presheaf `T_i` attached to `D.obj i`,
with `z` separated and locally of finite type. If the base change of `z` along the leg of `c` at
`i` is proper, then its base change along `D.map g` is proper for some `g : j ⟶ i`.

There is no cardinality hypothesis on `I` and no `AlgebraicGeometry.Space.ChartsBounded`
hypothesis.

Of the three conjuncts of properness, separatedness holds at every stage because it is assumed
at the starting stage and is stable under base change; finite type holds at every stage by
`AlgebraicGeometry.Space.isFiniteType_pullback_fst_of_isAffine`, with no descent; and universal
closedness descends by
`AlgebraicGeometry.Space.exists_universallyClosed_pullback_fst_of_limit`. So all three
conclusions are available at the one stage that universal closedness produces, and no common
upper bound in the index category has to be taken.

**The separatedness hypothesis is the one thing not proved here.** It is exactly the input the
bounded development gets from Stacks 0851
(`MorphismDescentSystemOfChartsBounded.exists_isSeparated_mapAt_of_isSeparated_mapLimit`),
whose proof rests on a bound on the index category; the affine-base size-free form of that
statement is not part of this file. Note that the hypothesis is on `z` itself, at the starting
stage, not at the limit: it is what Chow's lemma consumes. -/
theorem exists_isProper_pullback_fst_of_isProper_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZalg : IsAlgebraicSpace B S hS Z) (hqc : IsQuasiCompactSpace B S hS Z)
    (hft : IsLocallyOfFiniteType B S hS z) (hsep : IsSeparated B S hS z)
    (hproper : IsProper B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) z)) :
    ∃ (j : I) (g : j ⟶ i), IsProper B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) := by
  obtain ⟨j, g, huc⟩ := exists_universallyClosed_pullback_fst_of_limit B S hS hZ D hc i z
    hZalg hqc hft hsep hproper.2.2
  refine ⟨j, g, isSeparated_pullback_fst_of_snd B S hS z _
      (isSeparated_pullback B S hS z _ hsep),
    isFiniteType_pullback_fst_of_isAffine B S hS hZ (D.obj i).property (D.obj j).property z
      hZalg hqc hft _, huc⟩

include hZ in
/-- **The affine-base, size-free form of Stacks 08K1 stated over an arbitrary cartesian square,
for a morphism already separated at the starting stage.** The base change of `fi` to the vertex
of the cone is presented by any cartesian square over the cone leg rather than by the canonical
fibre product, and the conclusion produces the stage, the morphism `s : k ⟶ i` of the index
category, and a cartesian square over `D.map s`.

This is the shape in which
`AlgebraicGeometry.Space.exists_isFlat_isPullback_of_isFlat_limit` and
`AlgebraicGeometry.Space.exists_hasRelativeDimensionLE_isPullback_of_limit` state their
conclusions, and the shape a client with a cartesian square of structure morphisms in hand
needs. -/
theorem exists_isProper_isPullback_of_isProper_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fi : Zi ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZi : IsAlgebraicSpace B S hS Zi) (hqc : IsQuasiCompactSpace B S hS Zi)
    (hft : IsLocallyOfFiniteType B S hS fi) (hsep : IsSeparated B S hS fi)
    {ZT : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fT : ZT ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)) (gT : ZT ⟶ Zi)
    (hsq : IsPullback fT gT
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi)
    (hproper : IsProper B S hS fT) :
    ∃ (k : I) (s : k ⟶ i) (Zk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fk : Zk ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (hk : Zk ⟶ Zi),
      IsPullback fk hk
          (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) fi ∧
        IsProper B S hS fk := by
  have hiso : hsq.isoPullback.inv ≫ fT =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi := by
    rw [Iso.inv_comp_eq]
    exact hsq.isoPullback_hom_fst.symm
  have hlim : IsProper B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi) := by
    rw [← hiso]
    exact (isProper_isIso_comp_iff B S hS hsq.isoPullback.inv fT).2 hproper
  obtain ⟨k, s, h⟩ := exists_isProper_pullback_fst_of_isProper_limit B S hS hZ D hc i fi hZi
    hqc hft hsep hlim
  exact ⟨k, s, _, _, _, IsPullback.of_hasPullback _ _, h⟩

end ProperDescent

end AlgebraicGeometry.Space

end
