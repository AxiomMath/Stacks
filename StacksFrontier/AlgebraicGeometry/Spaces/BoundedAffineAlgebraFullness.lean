module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFull
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicAffineOpenSeparated

/-!
# Fullness of the direct-image functor of Stacks 081V

The declarations here belong to the development of Stacks 081V and are used for Stacks 0823.
The functor-level statements `AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor`,
registered under Stacks 081V, and
`AlgebraicGeometry.Space.full_boundedPushforwardAlgebraFunctor` are not part of this file.
Where the notes below name `AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence` or the
functor-level statements, they refer to declarations outside this file and its imports.

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `Y` and `Z` be algebraic
spaces affine over `X`, and let `φ : Z_* 𝒪_Z ⟶ Y_* 𝒪_Y` be a morphism of the direct-image algebras
of `AlgebraicGeometry.Space.pushforwardAlgebra`.  **This file produces a morphism `f : Y ⟶ Z` over
`X` with `f_* = φ`**, and so proves the direct-image functor
`AlgebraicGeometry.Space.quasicoherentPushforwardAlgebraFunctor` full.  Together with
`AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor` this is the full faithfulness
of the anti-equivalence clause of Stacks 081V; its essential surjectivity, which needs the
relative spectrum of a quasi-coherent algebra, is still not proved anywhere here.

Two steps separate `φ` from `f`, and both are taken here.  The *inputs* are
`AlgebraicGeometry.Space.exists_chartHom_of_algebraHom`, which reads `φ` at an affine étale chart
`V` of `X` as a morphism `Y ×_X V ⟶ Z ×_X V`, and
`AlgebraicGeometry.Space.chartPoint_eq`, which says that the point of `Z` such a chart morphism
assigns to a point of `Y` does not depend on which affine chart the point of `Y` was factored
through.

## Main results

* `AlgebraicGeometry.Space.sheafHom_eq_of_affineChart`: **a morphism of sheaves of commutative
  rings on the small étale site of an algebraic space is determined by its components at the
  affine charts.**  Every chart is covered by the affine opens of its scheme, which are again
  charts, so this is separatedness of the target against
  `AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology` at the affine opens.
* `AlgebraicGeometry.Space.exists_overHom_of_algebraHom`: **the amalgamation.**  There is a
  morphism `d : Y ⟶ Z` of sheaves on the big fppf site, over `X`, whose composite with every
  cartesian projection `Y ×_X V ⟶ Y` at an affine chart `V` is a chart morphism of `φ`.
* `AlgebraicGeometry.Space.pushforwardAlgebraMap_eq_of_affineChartHom`: **the recognition
  principle at the affine charts.**  A morphism `f : Y ⟶ Z` over `X` whose composites with the
  cartesian projections at the *affine* charts are chart morphisms of `φ` has `φ` for its
  direct-image map.  This weakens the hypothesis of
  `AlgebraicGeometry.Space.pushforwardAlgebraMap_eq_of_appTop_smallBaseChangeOverMap_eq`, which
  asks the chart identity at every chart.
* `AlgebraicGeometry.Space.exists_pushforwardAlgebraMap_eq`: **surjectivity of `f ↦ f_*`**, the
  right-hand side of `AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor_iff`.
* `AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor` and
  `AlgebraicGeometry.Space.full_boundedPushforwardAlgebraFunctor`: **fullness**, for the
  unrestricted direct-image functor and for the one cut down to the bounded quasi-coherent
  algebras.  The size condition bears on neither, by
  `AlgebraicGeometry.Space.full_boundedPushforwardAlgebraFunctor_iff`.

## Implementation notes

**Where the amalgamation happens, and why it is the big fppf site.**  A point of `Y` with values
in an object `T` of the site factors through an affine étale chart of `X` only locally on `T`:
that is `AlgebraicGeometry.Space.generate_affineChartPresieve_mem`, a statement about the *big
fppf* topology, and it is the only covering available, there being no affine surjective étale
atlas of an algebraic space in this development
(`AlgebraicGeometry.Space.exists_isSurjective_chart` is not affine).  So `d` is built one point at
a time, by amalgamating over a covering sieve of `T` the local points that
`AlgebraicGeometry.Space.chartPoint_eq` shows to be well defined, `Z` being a sheaf on that site.
The covering by the affine opens of a chart, used for
`AlgebraicGeometry.Space.sheafHom_eq_of_affineChart`, lives in the *small étale* topology of `X`
instead and cannot serve here; conversely the big fppf covering says nothing about the sections of
a sheaf on the small étale site, which is what the passage from the affine charts to all charts
needs.  The two steps use the two topologies and neither covering does the other's work.

**The sieve is replaced by a sieve of lifts.**  Membership of the sieve
`AlgebraicGeometry.Space.generate_affineChartPresieve_mem` produces is a nested existential —
`CategoryTheory.Sieve.generate` of a presieve that is itself an existential over charts — so a
family of elements indexed by it needs choice twice over and a compatibility stated at the inner
witnesses.  `AlgebraicGeometry.Space.affineChartLiftSieve` is the larger collection of arrows `h`
along which the point of `Y` lifts through *some* cartesian projection at an affine chart.  That
collection is already downward closed, hence a sieve with no `CategoryTheory.Sieve.generate` in
it, and it is covering because it contains the other one; its membership is one existential, over
a pair consisting of a chart and a lift, which is what
`AlgebraicGeometry.Space.affineChartLocalFamily` chooses.  Every lemma about the family is then
stated at an *arbitrary* chart, lift and chart morphism rather than at the chosen ones
(`AlgebraicGeometry.Space.affineChartLocalFamily_eq`), so the choice is never unfolded again.

**Naturality of the amalgamation comes from separatedness, not from the construction.**  The
amalgamated points are assembled into a morphism of presheaves by proving, for an arbitrary arrow
`h` of the sieve of lifts, that the restriction of the amalgamation along `h` is the local point
there — `CategoryTheory.Presieve.IsSheafFor.valid_glue` — and then reading that statement at `h`
and at a composite.  Both readings are needed: the one at the identity gives the chart identity
and the one at a composite gives naturality, by
`CategoryTheory.Presieve.IsSeparatedFor.ext` over the sieve of lifts of the restricted point.
That the amalgamation lies over `X` is `AlgebraicGeometry.Space.hom_ext_of_affineChartBaseChange`,
the uniqueness half of the same descent, applied to the two composites `Y ⟶ X`.

**One spelling throughout.**  Everything stays inside
`CategoryTheory.Functor.relativelyRepresentable.pullback` and
`AlgebraicGeometry.Space.smallBaseChange`, the spelling of
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` and
`AlgebraicGeometry.Space.exists_chartHom_of_algebraHom`, for the reason recorded in the
implementation notes of `AlgebraicGeometry.Space.smallBaseChangeOverMap_naturality`: the chart
morphisms are taken as data satisfying their universal property, and
`AlgebraicGeometry.Space.eq_smallBaseChangeOverMap` is what identifies a chart morphism of `φ`
with the base change of the morphism built from it.  No route through
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom`, the scheme-level universal property, is
taken: that would additionally need the chart restriction of the space-level direct-image algebra
identified with the scheme-level `Stacks.pushforwardAlgebra` of the base-changed morphism, and
that identification is absent, as the notes of
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartRestriction` record.

**Morphisms in `Type`.** The components of a morphism of presheaves of types are bundled, so the
amalgamation is turned into such a component by `CategoryTheory.TypeCat.ofHom` and read back by
`CategoryTheory.TypeCat.ofHom_apply`.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Separatedness of a sheaf on the small étale site at the affine charts -/

/-- **A morphism of sheaves of commutative rings on the small étale site of an algebraic space is
determined by its components at the affine étale charts.**

Two morphisms `A ⟶ C` of sheaves of commutative rings on the small étale site of `F` whose
components at every chart with affine underlying scheme agree are equal.

The affine opens of the scheme of a chart `V` cover it and each cuts out an étale chart of `F`
again, by `AlgebraicGeometry.Space.openChart`; so the two components at `V` agree after every
restriction of a covering family of `V`, by
`AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology` at the affine opens, whose
supremum is `⊤` by `AlgebraicGeometry.iSup_affineOpens_eq_top`.  Separatedness of `C` then
identifies them sectionwise, which is
`AlgebraicGeometry.Space.eq_of_openChart_restriction_eq_commRingCat`; what carries a section
across is the naturality of each of the two morphisms. -/
theorem sheafHom_eq_of_affineChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A C : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}} {ψ φ : A ⟶ C}
    (h : ∀ V : SmallEtale B S hS F,
      IsAffineOver B S hS ((SmallEtale.toOver B S hS F).obj V) →
        ψ.hom.app (op V) = φ.hom.app (op V)) :
    ψ = φ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Vop => ?_))
  obtain ⟨V⟩ := Vop
  refine ConcreteCategory.hom_ext _ _ fun r => ?_
  refine eq_of_openChart_restriction_eq_commRingCat B S hS F C.obj C.property V fun O hO => ?_
  have hψ := ConcreteCategory.congr_hom
    (ψ.hom.naturality (openChartInclusion B S hS F V O).op) r
  have hφ := ConcreteCategory.congr_hom
    (φ.hom.naturality (openChartInclusion B S hS F V O).op) r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hψ hφ
  rw [← hψ, ← hφ, h (openChart B S hS F V O) hO]

/-! ### The sieve of arrows along which a point of `Y` lifts to an affine chart -/

variable {X : AlgebraicSpaces B S hS} {Y : Over X}

/-- **The arrows along which a point of `Y` lifts to the base change of `Y` at an affine étale
chart of `X`.**

For `y` a point of `Y` with values in an object `T` of the big fppf site, these are the arrows
`h : T' ⟶ T` for which the restriction of `y` along `h` factors through some cartesian projection
`Y ×_X V ⟶ Y` with `V` an affine étale chart of `X`.  They are downward closed — a lift composes
with any further arrow — so they are a sieve, not merely a presieve, which is what spares the
family of local points below a `CategoryTheory.Sieve.generate` and a second choice. -/
private def affineChartLiftSieve (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {T : BigFppfOver B S hS} (y : Y.left.1.obj (op T)) : Sieve T where
  arrows := fun T' h =>
    ∃ Vc : (V : SmallEtale B S hS X.1) × (T' ⟶ hY.pullback V.1.hom),
      IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj Vc.1) ∧
        yoneda.map Vc.2 ≫ hY.fst Vc.1.1.hom = yoneda.map h ≫ yonedaEquiv.symm y
  downward_closed := by
    rintro T' T'' h ⟨⟨V, c⟩, hV, hc⟩ k
    refine ⟨⟨V, k ≫ c⟩, hV, ?_⟩
    rw [yoneda.map_comp, Category.assoc, hc, yoneda.map_comp, Category.assoc]

/-- **A point of `Y` lifts to an affine chart on a covering sieve.**

`AlgebraicGeometry.Space.affineChartLiftSieve` contains the covering sieve of
`AlgebraicGeometry.Space.generate_affineChartPresieve_mem`: over a member of the latter the image
point of `X` factors through an affine étale chart, and that factorization together with the
restricted point of `Y` is a cone on the cartesian square, so the point of `Y` lifts. -/
private theorem affineChartLiftSieve_mem (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {T : BigFppfOver B S hS} (y : Y.left.1.obj (op T)) :
    affineChartLiftSieve B S hS hY y ∈ BigFppfOver.topology B S hS T := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (generate_affineChartPresieve_mem B S hS X (Y.hom.hom.app (op T) y))
  rintro T' h ⟨T'', e₁, e₂, ⟨-, W, hW, g, heq⟩, rfl⟩
  have hcone : (yoneda.map (e₁ ≫ e₂) ≫ yonedaEquiv.symm y) ≫ Y.hom.hom =
      yoneda.map (e₁ ≫ g) ≫ W.1.hom := by
    rw [Category.assoc, yonedaEquiv_symm_naturality_right,
      yonedaEquiv_symm_naturality_left, op_comp, Functor.map_comp_apply, heq,
      ← Functor.map_comp_apply, ← op_comp,
      ← yonedaEquiv_symm_naturality_left, Equiv.symm_apply_apply]
  exact ⟨⟨W, hY.lift _ (e₁ ≫ g) hcone⟩, hW, hY.lift_fst _ _ hcone⟩

/-! ### The family of local points of `Z` -/

/-- **The local points of `Z` a family of chart morphisms assigns to a point of `Y`.**

Over a member of `AlgebraicGeometry.Space.affineChartLiftSieve` a lift of the point of `Y` to
`Y ×_X V` is chosen, and the value of the family is its image under the chart morphism `m₀ V`
followed by the cartesian projection `Z ×_X V ⟶ Z`.  The choice is never unfolded: what is used
downstream is `AlgebraicGeometry.Space.affineChartLocalFamily_eq`, which computes the value from
*any* chart, lift and chart morphism. -/
private def affineChartLocalFamily (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (m₀ : ∀ V : SmallEtale B S hS X.1,
      IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) →
        (hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom))
    {T : BigFppfOver B S hS} (y : Y.left.1.obj (op T)) :
    Presieve.FamilyOfElements Z.obj.left.1 (affineChartLiftSieve B S hS hY y).arrows :=
  fun _T' _h hh => yonedaEquiv (yoneda.map hh.choose.2 ≫
    yoneda.map (m₀ hh.choose.1 hh.choose_spec.1) ≫ hZ.fst hh.choose.1.1.hom)

/-- **Any chart morphism of `φ` at any affine chart computes the family.**

If the chart morphisms `m₀` all induce the chart values of `φ` on global regular functions, then
the value of `AlgebraicGeometry.Space.affineChartLocalFamily` over a member of the sieve is
computed by every other affine chart, lift and chart morphism of `φ` there as well.  This is
`AlgebraicGeometry.Space.chartPoint_eq` read at the two lifts, which lie over the same point of
`Y`. -/
private theorem affineChartLocalFamily_eq (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y)
    (m₀ : ∀ V : SmallEtale B S hS X.1,
      IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) →
        (hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom))
    (hm₀ : ∀ (V : SmallEtale B S hS X.1)
      (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V)),
      ((BigFppfOver.toScheme B S hS).map (m₀ V hV)).appTop =
        (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
          φ.right.hom.app (op V) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)
    {T : BigFppfOver B S hS} (y : Y.left.1.obj (op T)) {T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (hh : (affineChartLiftSieve B S hS hY y).arrows h)
    {V : SmallEtale B S hS X.1}
    (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V))
    (m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom)
    (hm : ((BigFppfOver.toScheme B S hS).map m).appTop =
      (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
        φ.right.hom.app (op V) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)
    (c : T' ⟶ hY.pullback V.1.hom)
    (hc : yoneda.map c ≫ hY.fst V.1.hom = yoneda.map h ≫ yonedaEquiv.symm y) :
    affineChartLocalFamily B S hS Z hY hZ m₀ y h hh =
      yonedaEquiv (yoneda.map c ≫ yoneda.map m ≫ hZ.fst V.1.hom) :=
  congrArg yonedaEquiv (chartPoint_eq B S hS Z hY hZ φ hh.choose_spec.1 hV
    (m₀ hh.choose.1 hh.choose_spec.1) (hm₀ hh.choose.1 hh.choose_spec.1) m hm
    hh.choose.2 c (hh.choose_spec.2.trans hc.symm))

/-- **The family of local points is compatible**, so it can be amalgamated.

Two members of the sieve dominated by a common object carry lifts of one and the same point of
`Y` there, after composing each lift with the dominating arrow, so
`AlgebraicGeometry.Space.chartPoint_eq` identifies the two local points.  What turns the
restriction of a local point into a local point again is the naturality of
`CategoryTheory.yonedaEquiv`: no base change intervenes, the lift is simply precomposed. -/
private theorem affineChartLocalFamily_compatible (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y)
    (m₀ : ∀ V : SmallEtale B S hS X.1,
      IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) →
        (hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom))
    (hm₀ : ∀ (V : SmallEtale B S hS X.1)
      (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V)),
      ((BigFppfOver.toScheme B S hS).map (m₀ V hV)).appTop =
        (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
          φ.right.hom.app (op V) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)
    {T : BigFppfOver B S hS} (y : Y.left.1.obj (op T)) :
    (affineChartLocalFamily B S hS Z hY hZ m₀ y).Compatible := by
  intro T₁ T₂ T₃ g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  obtain ⟨⟨V₁, c₁⟩, hV₁, hc₁⟩ := id h₁
  obtain ⟨⟨V₂, c₂⟩, hV₂, hc₂⟩ := id h₂
  rw [affineChartLocalFamily_eq B S hS Z hY hZ φ m₀ hm₀ y f₁ h₁ hV₁ (m₀ V₁ hV₁) (hm₀ V₁ hV₁)
      c₁ hc₁,
    affineChartLocalFamily_eq B S hS Z hY hZ φ m₀ hm₀ y f₂ h₂ hV₂ (m₀ V₂ hV₂) (hm₀ V₂ hV₂)
      c₂ hc₂,
    yonedaEquiv_naturality, yonedaEquiv_naturality]
  refine congrArg yonedaEquiv ?_
  rw [← Category.assoc (yoneda.map g₁), ← Category.assoc (yoneda.map g₂),
    ← yoneda.map_comp, ← yoneda.map_comp]
  refine chartPoint_eq B S hS Z hY hZ φ hV₁ hV₂ (m₀ V₁ hV₁) (hm₀ V₁ hV₁) (m₀ V₂ hV₂)
    (hm₀ V₂ hV₂) (g₁ ≫ c₁) (g₂ ≫ c₂) ?_
  rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hc₁, hc₂,
    ← Category.assoc, ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, hcomm]

/-! ### Amalgamating the chart morphisms to a morphism over `X` -/

/-- **The chart morphisms of a morphism of direct-image algebras amalgamate to a morphism over
`X`.**

Let `Y` be an object of `CategoryTheory.Over X` with representable structure morphism, let `Z` be
affine over `X` and let `φ : Z_* 𝒪_Z ⟶ Y_* 𝒪_Y`.  There is a morphism `d : Y ⟶ Z` of sheaves on
the big fppf site, over `X`, such that at every affine étale chart `V` of `X` the composite of `d`
with the cartesian projection `Y ×_X V ⟶ Y` is *every* chart morphism of `φ` at `V` followed by
the cartesian projection `Z ×_X V ⟶ Z`.

This is the step the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFull` record as missing.  A point of `Y`
factors through an affine étale chart of `X` only locally, by
`AlgebraicGeometry.Space.generate_affineChartPresieve_mem`, and
`AlgebraicGeometry.Space.chartPoint_eq` says the resulting point of `Z` does not depend on the
factorization; `Z` being a sheaf on the big fppf site, those local points amalgamate.  The
amalgamations are natural because the restriction of one along any arrow of
`AlgebraicGeometry.Space.affineChartLiftSieve` is the local point there, and that it lies over `X`
is `AlgebraicGeometry.Space.hom_ext_of_affineChartBaseChange` applied to the two composites
`Y ⟶ X`, the chart-local triangle being the commutation of a chart morphism with the two
cartesian projections to `V`.

Affineness of `Y` is not assumed; only representability of its structure morphism is, which is
what makes `Y ×_X V` a scheme. -/
theorem exists_overHom_of_algebraHom (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y) :
    ∃ d : Y.left.1 ⟶ Z.obj.left.1, d ≫ Z.obj.hom.hom = Y.hom.hom ∧
      ∀ (V : SmallEtale B S hS X.1),
        IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) →
        ∀ m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom,
          ((BigFppfOver.toScheme B S hS).map m).appTop =
              (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
                φ.right.hom.app (op V) ≫
                (pushforwardAlgebraSectionsIso B S hS Y hY V).hom →
            hY.fst V.1.hom ≫ d = yoneda.map m ≫ hZ.fst V.1.hom := by
  have hZt : Presieve.IsSheaf (BigFppfOver.topology B S hS) Z.obj.left.1 :=
    (isSheaf_iff_isSheaf_of_type _ _).mp Z.obj.left.property.isSheaf
  choose m₀ hm₀ hm₀snd using fun (V : SmallEtale B S hS X.1)
    (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V)) =>
      exists_chartHom_of_algebraHom B S hS Z hY hZ φ V hV
  -- The amalgamation at each point of `Y`, with the restriction of every local point it glues.
  obtain ⟨pt, hpt⟩ : ∃ pt : ∀ T : BigFppfOver B S hS,
      Y.left.1.obj (op T) → Z.obj.left.1.obj (op T),
      ∀ (T : BigFppfOver B S hS) (y : Y.left.1.obj (op T)) (T' : BigFppfOver B S hS)
        (h : T' ⟶ T) (hh : (affineChartLiftSieve B S hS hY y).arrows h)
        (V : SmallEtale B S hS X.1)
        (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V))
        (m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom),
        ((BigFppfOver.toScheme B S hS).map m).appTop =
            (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
              φ.right.hom.app (op V) ≫
              (pushforwardAlgebraSectionsIso B S hS Y hY V).hom →
          ∀ c : T' ⟶ hY.pullback V.1.hom,
            yoneda.map c ≫ hY.fst V.1.hom = yoneda.map h ≫ yonedaEquiv.symm y →
            Z.obj.left.1.map h.op (pt T y) =
              yonedaEquiv (yoneda.map c ≫ yoneda.map m ≫ hZ.fst V.1.hom) :=
    ⟨fun T y => (hZt _ (affineChartLiftSieve_mem B S hS hY y)).amalgamate
        (affineChartLocalFamily B S hS Z hY hZ m₀ y)
        (affineChartLocalFamily_compatible B S hS Z hY hZ φ m₀ hm₀ y),
      fun T y T' h hh V hV m hm c hc =>
        ((hZt _ (affineChartLiftSieve_mem B S hS hY y)).valid_glue _ h hh).trans
          (affineChartLocalFamily_eq B S hS Z hY hZ φ m₀ hm₀ y h hh hV m hm c hc)⟩
  -- The amalgamations are natural: both sides restrict to the same local points.
  have hptnat : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (y : Y.left.1.obj (op T)),
      Z.obj.left.1.map h.op (pt T y) = pt T' (Y.left.1.map h.op y) := by
    intro T T' h y
    refine ((hZt _ (affineChartLiftSieve_mem B S hS hY
      (Y.left.1.map h.op y))).isSeparatedFor.ext ?_).symm
    intro T'' h' hh'
    obtain ⟨⟨V, c⟩, hV, hc⟩ := id hh'
    have hcomp : yoneda.map c ≫ hY.fst V.1.hom =
        yoneda.map (h' ≫ h) ≫ yonedaEquiv.symm y := by
      rw [hc, yoneda.map_comp, Category.assoc,
        yonedaEquiv_symm_naturality_left h Y.left.1 y]
    have hmem : (affineChartLiftSieve B S hS hY y).arrows (h' ≫ h) := ⟨⟨V, c⟩, hV, hcomp⟩
    rw [hpt T' (Y.left.1.map h.op y) T'' h' hh' V hV (m₀ V hV) (hm₀ V hV) c hc,
      ← Functor.map_comp_apply, ← op_comp,
      hpt T y T'' (h' ≫ h) hmem V hV (m₀ V hV) (hm₀ V hV) c hcomp]
  obtain ⟨d, hd⟩ : ∃ d : Y.left.1 ⟶ Z.obj.left.1,
      ∀ (T : BigFppfOver B S hS) (y : Y.left.1.obj (op T)), d.app (op T) y = pt T y :=
    ⟨{ app := fun Top => TypeCat.ofHom (pt Top.unop)
       naturality := fun Top Top' f => ConcreteCategory.hom_ext _ _ fun y => by
         rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
           TypeCat.ofHom_apply]
         exact (hptnat Top.unop Top'.unop f.unop y).symm },
      fun _ _ => TypeCat.ofHom_apply _ _⟩
  -- The chart identity: the tautological point of `Y ×_X V` lifts along the identity.
  have hchart : ∀ (V : SmallEtale B S hS X.1),
      IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) →
      ∀ m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom,
        ((BigFppfOver.toScheme B S hS).map m).appTop =
            (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
              φ.right.hom.app (op V) ≫
              (pushforwardAlgebraSectionsIso B S hS Y hY V).hom →
          hY.fst V.1.hom ≫ d = yoneda.map m ≫ hZ.fst V.1.hom := by
    intro V hV m hm
    refine yonedaEquiv.injective ?_
    have hc : yoneda.map (𝟙 (hY.pullback V.1.hom)) ≫ hY.fst V.1.hom =
        yoneda.map (𝟙 (hY.pullback V.1.hom)) ≫
          yonedaEquiv.symm (yonedaEquiv (hY.fst V.1.hom)) := by
      rw [Equiv.symm_apply_apply]
    have hmem : (affineChartLiftSieve B S hS hY
        (yonedaEquiv (hY.fst V.1.hom))).arrows (𝟙 (hY.pullback V.1.hom)) :=
      ⟨⟨V, 𝟙 _⟩, hV, hc⟩
    have hres := hpt (hY.pullback V.1.hom) (yonedaEquiv (hY.fst V.1.hom))
      (hY.pullback V.1.hom) (𝟙 _) hmem V hV m hm (𝟙 _) hc
    rw [op_id, Functor.map_id_apply, yoneda.map_id, Category.id_comp] at hres
    rw [yonedaEquiv_comp, hd, hres]
  refine ⟨d, ?_, hchart⟩
  refine hom_ext_of_affineChartBaseChange B S hS Y hY X.property.isSheaf ?_
  intro V hV
  rw [← Category.assoc, hchart V hV (m₀ V hV) (hm₀ V hV), Category.assoc, hZ.w V.1.hom,
    ← Category.assoc, ← yoneda.map_comp, hm₀snd V hV]
  exact (hY.w V.1.hom).symm

/-! ### Recognising `φ` as a direct-image map from the affine charts -/

/-- **A morphism over `X` whose cartesian projections at the affine charts are chart morphisms of
`φ` has `φ` for its direct-image map.**

This weakens the hypothesis of
`AlgebraicGeometry.Space.pushforwardAlgebraMap_eq_of_appTop_smallBaseChangeOverMap_eq` from every
étale chart of `X` to the affine ones, which is where
`AlgebraicGeometry.Space.exists_chartHom_of_algebraHom` produces chart morphisms at all, and it
asks the chart condition as an identity of morphisms of the site rather than of maps of regular
functions.

Two things are consumed.  At an affine chart the chart morphism of `φ` *is* the base change of
`f`, by `AlgebraicGeometry.Space.eq_smallBaseChangeOverMap`: it commutes with the cartesian
projections to `Y` and to `Z` by hypothesis and by
`AlgebraicGeometry.Space.exists_chartHom_of_algebraHom`, which pins the base change down.  So the
chart values of `AlgebraicGeometry.Space.pushforwardRingMap f` and of `φ` agree at the affine
charts, by `AlgebraicGeometry.Space.pushforwardRingMap_app_eq`; and
`AlgebraicGeometry.Space.sheafHom_eq_of_affineChart` is what extends that to all charts, the
direct-image algebra being a sheaf on the small étale site of `X`. -/
theorem pushforwardAlgebraMap_eq_of_affineChartHom (Z : AffineOver B S hS X) (f : Y ⟶ Z.obj)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y)
    (hchart : ∀ (V : SmallEtale B S hS X.1),
      IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) →
      ∀ m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom,
        ((BigFppfOver.toScheme B S hS).map m).appTop =
            (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
              φ.right.hom.app (op V) ≫
              (pushforwardAlgebraSectionsIso B S hS Y hY V).hom →
          hY.fst V.1.hom ≫ f.left.hom = yoneda.map m ≫ hZ.fst V.1.hom) :
    pushforwardAlgebraMap B S hS f = φ := by
  refine AlgebraSheaf.Hom.ext (sheafHom_eq_of_affineChart B S hS fun V hV => ?_)
  obtain ⟨m, hm, hmsnd⟩ := exists_chartHom_of_algebraHom B S hS Z hY hZ φ V hV
  have hmeq : m = smallBaseChangeOverMap B S hS f hY hZ V :=
    eq_smallBaseChangeOverMap B S hS f hY hZ V m (hchart V hV m hm).symm hmsnd
  refine (Iso.cancel_iso_hom_right _ _ (pushforwardAlgebraSectionsIso B S hS Y hY V)).mp
    ((Iso.cancel_iso_inv_left (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V) _ _).mp
      ((pushforwardRingMap_app_eq B S hS f hY hZ V).trans ?_))
  rw [← hmeq]
  exact hm

/-! ### Fullness -/

/-- **The direct-image map of Stacks 081V is surjective onto the morphisms of direct-image
algebras.**

For `Y` and `Z` affine over `X` every morphism `φ : Z_* 𝒪_Z ⟶ Y_* 𝒪_Y` of their direct-image
algebras is `f_*` for a morphism `f : Y ⟶ Z` over `X`.  This is the right-hand side of
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor_iff`, and the two steps above
composed: `AlgebraicGeometry.Space.exists_overHom_of_algebraHom` builds `f` from the chart
morphisms of `φ` and `AlgebraicGeometry.Space.pushforwardAlgebraMap_eq_of_affineChartHom`
recognises `φ` as its direct-image map.

Affineness of `Y` is used only to know that its structure morphism is representable, by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`, which is what makes `Y ×_X V` a
scheme; affineness of `Y` as a scheme is never needed.  Affineness of `Z` is used for its base
changes at the affine charts, which have to be affine schemes for
`AlgebraicGeometry.Space.exists_chartHom_of_algebraHom` to produce a chart morphism at all. -/
theorem exists_pushforwardAlgebraMap_eq (Y Z : AffineOver B S hS X)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y.obj) :
    ∃ f : Y.obj ⟶ Z.obj, pushforwardAlgebraMap B S hS f = φ := by
  have hY : yoneda.relativelyRepresentable Y.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS Y.obj.hom Y.property
  have hZ : yoneda.relativelyRepresentable Z.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS Z.obj.hom Z.property
  obtain ⟨d, hdover, hdchart⟩ := exists_overHom_of_algebraHom B S hS Z hY hZ φ
  exact ⟨Over.homMk (ObjectProperty.homMk d) (ObjectProperty.hom_ext _ hdover),
    pushforwardAlgebraMap_eq_of_affineChartHom B S hS Z _ hY hZ φ hdchart⟩

end AlgebraicGeometry.Space

end
