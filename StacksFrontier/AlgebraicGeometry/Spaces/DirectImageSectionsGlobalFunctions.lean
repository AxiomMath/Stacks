module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRing
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedGlobalFunctionsIntegral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pushforward of the structure sheaf along a universally closed morphism is integral

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and universally closed morphism of
algebraic spaces over a scheme `S` of a big fppf site.  Stacks 0A0Q asserts that `f_*𝒪_X` is
integral over `𝒪_Y`, and — in other words — that the normalization of `Y` in `X` is the
factorization `X ⟶ \underline{Spec}_Y(f_*𝒪_X) ⟶ Y` of Stacks 081X.  The first assertion is
proved here, at universal closedness of `f` alone, together with its consequence that the
integral closure of `𝒪_Y` in `f_*𝒪_X` is `f_*𝒪_X` itself (by way of
`StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral`); the identification of
the normalization of `Y` in `X` with the factorization of Stacks 081X is drawn from it in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversallyClosed`.

The assertion is étale local on `Y`, as the source says: integrality of `f_*𝒪_X` means
integrality of its structure-algebra map on every affine étale scheme chart `V` of `Y`.  The
sections of `f_*𝒪_X` over `V` are the limit of the regular functions on the étale scheme charts
of `X` above the algebraic space `W = X ×_Y V`, and the étale scheme charts of `W` are among
those — a chart of `W` is étale over `X` through the étale structure morphism of `W` — so a
section of `f_*𝒪_X` over `V` restricts to a compatible family of regular functions on the
charts of `W`, that is, to a global regular function on `W`.  This restriction is the bridge
the two descriptions of the sections were waiting on; it is injective because a single
surjective étale chart of `W` already determines a section, and it carries the
structure-algebra map to pullback of functions along the projection `W ⟶ V`.  The projection is
universally closed, being a base change of `f`, so
`AlgebraicGeometry.Space.isIntegral_globalFunctions_of_universallyClosed` makes that pullback
integral, and integrality descends along the injection by `RingHom.IsIntegral.tower_bot`.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeSpace` is `X ×_Y V` as an algebraic space, and
  `AlgebraicGeometry.Space.chartBaseChangeProjection` is its projection to `V`.
* `AlgebraicGeometry.Space.baseChangeSpaceChart`,
  `AlgebraicGeometry.Space.baseChangeSpaceChartHom`,
  `AlgebraicGeometry.Space.baseChangeSpaceChartMap` and
  `AlgebraicGeometry.Space.baseChangeSpaceChartIndex` read an étale scheme chart of `X ×_Y V`, and
  a morphism of such charts, as an étale scheme chart of `X` above `X ×_Y V` and a morphism of
  those — that is, as an index object of the limit describing the sections of `f_*𝒪_X` over `V`.
* `AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`: **the bridge**, the
  homomorphism from the sections of `f_*𝒪_X` over `V` to the global regular functions on
  `X ×_Y V`.

## Main results

* `AlgebraicGeometry.Space.chartProjection_naturality` and
  `AlgebraicGeometry.Space.directImageChartProjection_naturality`: the chart projections are
  natural in the chart of `X`, being the legs of a limit cone.
* `AlgebraicGeometry.Space.singleton_baseChangeSpaceChartHom_mem_topology`: **Stacks 03H7** in
  singleton form — a surjective étale scheme chart of `X ×_Y V` covers it in the spaces-étale
  site of `X`.
* `AlgebraicGeometry.Space.injective_directImageSectionsToGlobalFunctions` and
  `AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions_algebraMap`: the bridge is
  injective and carries the structure-algebra map to pullback along the projection.
* `AlgebraicGeometry.Space.universallyClosed_chartBaseChangeProjection`: **Stacks 03IS** at the
  base change of Stacks 03G2, part (1).
* `AlgebraicGeometry.Space.isIntegral_pushforwardAlgebra_of_universallyClosed`: **the first
  assertion of Stacks 0A0Q**.
* `AlgebraicGeometry.Space.isIso_integralClosureInclusion_pushforwardAlgebra_of_universallyClosed`:
  the integral closure `𝒪'` of `𝒪_Y` in `f_*𝒪_X` is all of `f_*𝒪_X`, the algebra-level form
  of the second assertion of Stacks 0A0Q.

## Implementation notes

The sections of `f_*𝒪_X` over `V` carry the ring structure transported along the direct image,
and the chart projections are natural transformations of *set*-valued sections functors;
`AlgebraicGeometry.Space.directImageChartProjectionRingHom` is the homomorphism of rings they
induce, and it is what the bridge is assembled from, componentwise.  The ring structure on the
global functions of an algebraic space is pointwise on compatible families, so the four
homomorphism properties of the bridge are the four of each component.

The index objects are built, and compared, exactly as in the proof of Stacks 03H7
(`AlgebraicGeometry.Space.exists_scheme_chart_cover`): a chart of `X ×_Y V` is the chart of `X`
whose structure morphism is the composite with the étale structure morphism of `X ×_Y V`, and
the morphism to `X ×_Y V` is the chart itself.  Because the construction is the same, the
underlying object of the big fppf category is unchanged, and the regular functions on the two
readings of the chart are the same type on the nose.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03IS](https://stacks.math.columbia.edu/tag/03IS)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- An étale scheme chart of `X ×_Y V` is an étale scheme chart of `X`: its structure morphism
is composed with the étale structure morphism of `X ×_Y V` over `X`. -/
noncomputable def baseChangeSpaceChart (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk (c.obj.hom ≫
      ((SpacesEtale.inclusion B S hS X).obj (chartBaseChange B S hS f V)).hom.hom),
    presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS
      (isEtale_of_presheaf_etale B S hS c.2) (chartBaseChange B S hS f V).property)⟩

/-- The morphism of algebraic spaces over `X` from the chart of `X` attached to an étale
scheme chart of `X ×_Y V` to `X ×_Y V`. -/
noncomputable def baseChangeSpaceChartHom (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj) :
    (comparisonFunctor B S hS X).obj (baseChangeSpaceChart B S hS f V c) ⟶
      chartBaseChange B S hS f V :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk c.obj.hom) rfl)

/-- The index object of the limit of chart sections attached to an étale scheme chart of
`X ×_Y V`. -/
noncomputable def baseChangeSpaceChartIndex (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj) :
    StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk (baseChangeSpaceChartHom B S hS f V c).op

/-- A morphism of étale scheme charts of `X ×_Y V`, read as a morphism of the corresponding
étale scheme charts of `X`. -/
noncomputable def baseChangeSpaceChartMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {c c' : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj} (g : c ⟶ c') :
    baseChangeSpaceChart B S hS f V c ⟶ baseChangeSpaceChart B S hS f V c' :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    ((SmallEtale.toOver B S hS (chartBaseChangeSpace B S hS f V).obj).map g)
    (by
      exact congrArg (fun k => k ≫
        ((SpacesEtale.inclusion B S hS X).obj (chartBaseChange B S hS f V)).hom.hom)
        (CostructuredArrow.w g.hom)))

/-- Reading a morphism of charts of `X ×_Y V` as a morphism of charts of `X` leaves the
underlying morphism of the big fppf category unchanged. -/
theorem toOver_map_baseChangeSpaceChartMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {c c' : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj} (g : c ⟶ c') :
    (SmallEtale.toOver B S hS X.1).map (baseChangeSpaceChartMap B S hS f V g) =
      (SmallEtale.toOver B S hS (chartBaseChangeSpace B S hS f V).obj).map g :=
  rfl

/-- The morphisms to `X ×_Y V` attached to two charts of `X ×_Y V` are compatible with a
morphism of those charts. -/
theorem comparisonFunctor_map_baseChangeSpaceChartMap_comp (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    {c c' : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj} (g : c ⟶ c') :
    (comparisonFunctor B S hS X).map (baseChangeSpaceChartMap B S hS f V g) ≫
        baseChangeSpaceChartHom B S hS f V c' = baseChangeSpaceChartHom B S hS f V c := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
  show ((SpacesEtale.toSpaces B S hS X).map
      ((comparisonFunctor B S hS X).map (baseChangeSpaceChartMap B S hS f V g))).hom ≫
    c'.obj.hom = c.obj.hom
  rw [toSpaces_comparisonFunctor_map_hom B S hS X (baseChangeSpaceChartMap B S hS f V g),
    toOver_map_baseChangeSpaceChartMap]
  exact CostructuredArrow.w g.hom

/-- The morphism of index objects attached to a morphism of étale scheme charts of
`X ×_Y V`. -/
noncomputable def baseChangeSpaceChartIndexMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {c c' : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj} (g : c ⟶ c') :
    baseChangeSpaceChartIndex B S hS f V c' ⟶ baseChangeSpaceChartIndex B S hS f V c :=
  StructuredArrow.homMk (baseChangeSpaceChartMap B S hS f V g).op
    (congrArg Quiver.Hom.op
      (comparisonFunctor_map_baseChangeSpaceChartMap_comp B S hS f V g))

/-- **The chart projections of the direct image are natural in the chart of `X`.**  This is
`AlgebraicGeometry.Space.chartProjection_naturality` for
`AlgebraicGeometry.Space.smallEtaleDirectImage` rather than its Kan extension form. -/
theorem directImageChartProjection_naturality (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j₁ ⟶ j₂)
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj
        (structureSetSheaf B S hS X)) :
    (structureSetSheaf B S hS X).obj.map φ.right
        ((directImageChartProjection B S hS f V j₁).app (structureSetSheaf B S hS X) a) =
      (directImageChartProjection B S hS f V j₂).app (structureSetSheaf B S hS X) a := by
  rw [directImageChartProjection_app_apply, directImageChartProjection_app_apply]
  exact (chartProjection_naturality B S hS f V φ _).symm

/-- **A surjective étale scheme chart of `X ×_Y V` covers it in the spaces-étale site of `X`.**
This is the singleton-family form of Stacks 03H7 for the chart attached to an atlas. -/
theorem singleton_baseChangeSpaceChartHom_mem_topology (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj)
    (hc : IsSurjective B S hS c.obj.hom) :
    Sieve.generate (Presieve.singleton (baseChangeSpaceChartHom B S hS f V c)) ∈
      SpacesEtale.topology B S hS X (chartBaseChange B S hS f V) := by
  have hE : SpacesEtale.IsCovering B S hS X
      ⟨chartBaseChange B S hS f V,
        PreZeroHypercover.singleton (baseChangeSpaceChartHom B S hS f V c)⟩ := by
    intro x
    obtain ⟨y, hy⟩ := hc x
    exact ⟨default, y, hy⟩
  rw [show Presieve.singleton (baseChangeSpaceChartHom B S hS f V c) =
    (PreZeroHypercover.singleton (baseChangeSpaceChartHom B S hS f V c)).presieve₀ from
    (PreZeroHypercover.presieve₀_singleton _).symm]
  exact Precoverage.generate_mem_toGrothendieck ⟨_, rfl, hE⟩

/-- **A section of `f_*𝒪_X` over an étale chart of `Y` is determined by one covering chart of
`X` above `X ×_Y V`**, for the direct image rather than its Kan extension form. -/
theorem injective_directImageChartProjection_of_singleton_covering (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj : Sieve.generate (Presieve.singleton j.hom.unop) ∈
      SpacesEtale.topology B S hS X (chartBaseChange B S hS f V)) :
    Function.Injective ((directImageChartProjection B S hS f V j).app
      (structureSetSheaf B S hS X)) := by
  have hcancel : ∀ z : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj
        (structureSetSheaf B S hS X),
      ((smallEtaleDirectImageRanIso B S hS f).inv.app (structureSetSheaf B S hS X)).hom.app
          (op V)
        (((smallEtaleDirectImageRanIso B S hS f).hom.app
          (structureSetSheaf B S hS X)).hom.app (op V) z) = z := fun z =>
    Sheaf.hom_congr_app_apply
      (((smallEtaleDirectImageRanIso B S hS f).app (structureSetSheaf B S hS X)).hom_inv_id)
      (op V) z
  intro a b h
  rw [directImageChartProjection_app_apply, directImageChartProjection_app_apply] at h
  exact Function.LeftInverse.injective hcancel
    (injective_chartProjection_of_singleton_covering B S hS f V j hj h)

/-- **The sections of `f_*𝒪_X` over an étale scheme chart `V` of `Y`, read as global regular
functions on `X ×_Y V`.**  A section of the direct image over `V` is a compatible family of
regular functions on the étale scheme charts of `X` above `X ×_Y V`, and the étale scheme
charts of the algebraic space `X ×_Y V` are among those, so a section restricts to a compatible
family of regular functions on them, which is a global regular function on `X ×_Y V`. -/
noncomputable def directImageSectionsToGlobalFunctions (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V) →+*
      globalFunctions B S hS (chartBaseChangeSpace B S hS f V).obj where
  toFun a := ⟨fun c => (directImageChartProjectionRingHom B S hS f V
      (baseChangeSpaceChartIndex B S hS f V c.unop)).hom a,
    fun {_ _} g => directImageChartProjection_naturality B S hS f V
      (baseChangeSpaceChartIndexMap B S hS f V g.unop) a⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

/-- On an étale scheme chart of `X ×_Y V` the bridge is the chart projection of the direct
image at the corresponding chart of `X`. -/
@[simp]
theorem directImageSectionsToGlobalFunctions_val (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (a : (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V))
    (c : (SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj)ᵒᵖ) :
    (directImageSectionsToGlobalFunctions B S hS f V a).val c =
      (directImageChartProjectionRingHom B S hS f V
        (baseChangeSpaceChartIndex B S hS f V c.unop)).hom a :=
  rfl

/-- **A section of `f_*𝒪_X` over an étale chart of `Y` is determined by its global function on
`X ×_Y V`**: a surjective étale scheme chart of `X ×_Y V` covers it, and a section of the
direct image is determined by its projection to a covering chart. -/
theorem injective_directImageSectionsToGlobalFunctions (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    Function.Injective (directImageSectionsToGlobalFunctions B S hS f V) := by
  obtain ⟨T, a, hsurj, hetale⟩ := (chartBaseChangeSpace B S hS f V).property.exists_atlas
  obtain ⟨c₀, hc₀⟩ : ∃ c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj,
      IsSurjective B S hS c.obj.hom :=
    ⟨⟨CostructuredArrow.mk a, hetale⟩,
      (surjective_iff_surjective_pointsMap B S hS (chartBaseChangeSpace B S hS f V).obj
        (chartBaseChangeSpace B S hS f V).property T a).1 hsurj⟩
  intro x y h
  exact injective_directImageChartProjection_of_singleton_covering B S hS f V
    (baseChangeSpaceChartIndex B S hS f V c₀)
    (singleton_baseChangeSpaceChartHom_mem_topology B S hS f V c₀ hc₀)
    (congrFun (congrArg Subtype.val h) (op c₀))

/-- The morphism of charts `c ⟶ V` attached to an index object coming from an étale scheme
chart `c` of `X ×_Y V` is the one induced by the projection `X ×_Y V ⟶ V`. -/
theorem chartBaseChangeMap_baseChangeSpaceChartIndex (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj) :
    chartBaseChangeMap B S hS f V (baseChangeSpaceChartIndex B S hS f V c) =
      smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS f V).hom c :=
  rfl

/-- **The structure-algebra map of `f_*𝒪_X` on the chart `V`, read as a global function on
`X ×_Y V`, is pullback of functions along the projection.** -/
theorem directImageSectionsToGlobalFunctions_algebraMap (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj)
    (r : (structureSheaf B S hS Y.1 Y.2).obj.obj (op V)) :
    (directImageSectionsToGlobalFunctions B S hS f V
        ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V) r)).val (op c) =
      ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS
        (chartBaseChangeProjection B S hS f V).hom c)).appTop.hom r := by
  have h1 : (pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op V) r =
      ((structureSharp B S hS f).hom.app (op V)).hom r :=
    (congrArg (fun φ : (structureSheaf B S hS Y.1 Y.2).obj.obj (op V) →+*
        (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V) => φ r)
      (pushforwardAlgebra_algebraMap B S hS (Over.mk f) (op V))).trans
      (fSharp_app_apply B S hS f (op V) r)
  rw [directImageSectionsToGlobalFunctions_val, h1]
  refine Eq.trans (congrArg (fun φ : (structureRingSheaf B S hS Y).obj.obj (op V) →+*
      (structureRingSheaf B S hS X).obj.obj
        (baseChangeSpaceChartIndex B S hS f V c).right => φ r)
    (hom_structureSharp_comp_directImageChartProjectionRingHom B S hS f V
      (baseChangeSpaceChartIndex B S hS f V c))) ?_
  rw [chartPullbackRingHom, chartBaseChangeMap_baseChangeSpaceChartIndex]
  rfl

/-- **The projection `X ×_Y V ⟶ V` of a universally closed morphism is universally closed**:
it is a base change of `f`, by Stacks 03G2, part (1), and universal closedness is stable under
base change by Stacks 03IS. -/
theorem universallyClosed_chartBaseChangeProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (huc : UniversallyClosed B S hS f.hom) :
    UniversallyClosed B S hS (chartBaseChangeProjection B S hS f V).hom :=
  universallyClosed_of_isPullback B S hS (chartBaseChangeSpace B S hS f V).property
    X.property ((SpacesEtale.toSpaces B S hS Y).obj
      ((comparisonFunctor B S hS Y).obj V)).property Y.property f.hom _ huc
    (isPullback_chartBaseChangeProjection B S hS f V)

/-- **Stacks 0A0Q, first assertion.**  For a universally closed morphism `f : X ⟶ Y` of
algebraic spaces over `S`, the direct image `f_*𝒪_X` is integral over `𝒪_Y`.

The assertion is étale local on `Y`: on an affine étale scheme chart `V` of `Y` the sections of
`f_*𝒪_X` are the global regular functions on the algebraic space `X ×_Y V`
(`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions`, which is injective), the
projection `X ×_Y V ⟶ V` is universally closed because `f` is, and the global functions of a
universally closed algebraic space over an affine base are integral over the base
(`AlgebraicGeometry.Space.isIntegral_globalFunctions_of_universallyClosed`). -/
@[stacks 0A0Q "first sentence: f_*O_X is integral over O_Y; only universal closedness of f \
is used", ega "II 7.3.11" "Integrality of Γ(X"]
theorem isIntegral_pushforwardAlgebra_of_universallyClosed (f : X ⟶ Y)
    (huc : UniversallyClosed B S hS f.hom) :
    (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral := by
  intro V hV
  refine RingHom.IsIntegral.tower_bot _ (directImageSectionsToGlobalFunctions B S hS f V)
    (injective_directImageSectionsToGlobalFunctions B S hS f V) ?_
  refine isIntegral_globalFunctions_of_universallyClosed B S hS
    (W := chartBaseChangeSpace B S hS f V) (V := (SmallEtale.toOver B S hS Y.1).obj V) hV
    (chartBaseChangeProjection B S hS f V).hom
    (universallyClosed_chartBaseChangeProjection B S hS f V huc) _ ?_
  intro c
  exact RingHom.ext fun r => directImageSectionsToGlobalFunctions_algebraMap B S hS f V c r

/-- **The integral closure of `𝒪_Y` in `f_*𝒪_X` is all of `f_*𝒪_X`** for a universally closed
morphism `f : X ⟶ Y` of algebraic spaces: the inclusion of the integral closure `𝒪'` of
Stacks 0821 is an isomorphism of algebra sheaves.  This is the algebra-level content of the
second sentence of Stacks 0A0Q. -/
theorem isIso_integralClosureInclusion_pushforwardAlgebra_of_universallyClosed (f : X ⟶ Y)
    (huc : UniversallyClosed B S hS f.hom) :
    IsIso (AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f))) :=
  isIso_integralClosureInclusion_pushforwardAlgebra B S hS f
    (isIntegral_pushforwardAlgebra_of_universallyClosed B S hS f huc)

end AlgebraicGeometry.Space

end
