module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Étale charts of an algebraic space (Stacks 03EC, 02X1)

A *chart* of an algebraic space `F` over `S` is a morphism `yoneda.obj U ⟶ F` out of a
representable presheaf which is étale in the representable sense, i.e. all of whose
represented base changes are étale morphisms of schemes. This file collects the elementary
calculus of such charts:

* an étale morphism of the site followed by an étale chart is an étale chart (Tag 03EC);
* a morphism of the site between two étale charts of the same presheaf is an étale morphism
  of schemes (Tag 03EC);
* étaleness of a chart descends along a surjective étale morphism of the site (Tag 03EC);
* a surjective étale chart of the target of a morphism of algebraic spaces can be lifted to
  a surjective étale chart of the source (Tag 02X1).

The three statements of Tag 03EC are the three uses the tag is put to in the Stacks Project;
each is a consequence of the corresponding scheme-level fact, applied after base changing
along the atlas of the algebraic space.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.presheaf_etale_id`: the identity of a represented presheaf is an
  étale chart of it.
* `AlgebraicGeometry.Space.etale_comp_of_scheme`: **Stacks 03EC**.
* `AlgebraicGeometry.Space.etale_of_etale_charts`: **Stacks 03EC**.
* `AlgebraicGeometry.Space.etale_of_comp_surjective_etale`: **Stacks 03EC**.
* `AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`: **Stacks 02X1**.

## Implementation notes

Schemes over the base are objects of the big fppf site of `S`, and a chart is a morphism out
of the Yoneda presheaf of such an object. Étaleness and surjectivity of a chart are the
relatively representable properties `MorphismProperty.presheaf` of the inverse images of
`AlgebraicGeometry.Etale` and `AlgebraicGeometry.Surjective` along
`AlgebraicGeometry.BigFppfOver.toScheme`. These inverse images are stable under base change
because the functor to schemes preserves fibre products, which is
`AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme`, registered as an
instance below; that is what lets the relative calculus of
`CategoryTheory.MorphismProperty` be used throughout.

The descent statement of Tag 03EC is the étale case of Tag 02KM applied to the base change of
the chart along the atlas of the algebraic space: the chart is representable, because the
diagonal of an algebraic space is, and the pasting of the two cartesian squares exhibits the
base-changed morphism of schemes as surjective étale with étale composite.

The scheme-level fact the three statements rest on is
`Stacks.Etale.etale_of_comp_surjective_etale`, the étale case of Tag 02KM, which lives in
`StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent` alongside the descent of the
other properties along a surjective étale morphism of sources.

## References

* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- The canonical functor from the big fppf site of `S` to schemes preserves fibre products,
-- being the composite of the forgetful functor of a slice with the inclusion of a
-- size-bounded full subcategory of schemes. The relative calculus of
-- `CategoryTheory.MorphismProperty` is used throughout this file and downstream of it, so the
-- fact is registered as an instance here rather than applied by hand at each use.
attribute [instance] preservesLimitsOfShape_walkingCospan_toScheme

/-- The inverse image along `AlgebraicGeometry.BigFppfOver.toScheme` of a base-change stable
property of morphisms of schemes is stable under base change. -/
theorem inverseImage_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun hsq hg ↦ hP.of_isPullback (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩

/-- The inverse image along `AlgebraicGeometry.BigFppfOver.toScheme` of a composition stable
property of morphisms of schemes is stable under composition. -/
theorem inverseImage_isStableUnderComposition {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderComposition) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- Étaleness of morphisms of schemes is stable under composition. -/
theorem etale_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun f g hf hg ↦ have := hf; have := hg; AlgebraicGeometry.Etale.etale_comp f g⟩

/-- Étaleness of a chart is stable under base change. -/
private theorem etale_presheaf_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  inverseImage_isStableUnderBaseChange B S hS AlgebraicGeometry.Etale.etale_isStableUnderBaseChange

/-- A morphism of the site has a base-change stable property `P` after Yoneda precisely when
the underlying morphism of schemes has `P`. -/
theorem presheaf_yoneda_map_iff {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) {U V : BigFppfOver B S hS} (φ : U ⟶ V) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map φ) ↔
      P ((BigFppfOver.toScheme B S hS).map φ) :=
  have := inverseImage_isStableUnderBaseChange B S hS hP
  MorphismProperty.relative_map_iff (F := yoneda)

/-- A morphism between two representable presheaves on the big fppf site of `S` with a
base-change stable property `P` comes from a morphism of the site with `P`. -/
theorem prop_preimage_of_presheaf {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) {U V : BigFppfOver B S hS}
    (r : yoneda.obj U ⟶ yoneda.obj V)
    (h : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r) :
    P ((BigFppfOver.toScheme B S hS).map (yoneda.preimage r)) :=
  (presheaf_yoneda_map_iff B S hS hP (yoneda.preimage r)).1
    (by rw [yoneda.map_preimage]; exact h)

/-- A morphism of the site is étale after Yoneda precisely when the underlying morphism of
schemes is étale. -/
theorem presheaf_yoneda_map_etale_iff {U V : BigFppfOver B S hS} (φ : U ⟶ V) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map φ) ↔
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ) :=
  presheaf_yoneda_map_iff B S hS AlgebraicGeometry.Etale.etale_isStableUnderBaseChange φ

/-- The identity of a represented presheaf is étale as a morphism of presheaves: it is its own
base change along every morphism, and the identity of a scheme is étale. -/
theorem presheaf_etale_id (T : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T)) := by
  have : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists
    (fun W g ↦ ⟨W, g, 𝟙 W, IsPullback.of_vert_isIso (by simp), ?_⟩)
  show Etale ((BigFppfOver.toScheme B S hS).map (𝟙 W))
  simpa using (inferInstance : Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj W)))

/-- **Stacks 03EC.** An étale morphism of the big fppf site of `S` followed by an étale chart
of an algebraic space is again an étale chart. -/
@[stacks 03EC "composition"]
theorem etale_comp_of_scheme {U U' : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ U') (g : yoneda.obj U' ⟶ F)
    (hf : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f))
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map f ≫ g) := by
  have := etale_presheaf_isStableUnderBaseChange B S hS
  exact MorphismProperty.comp_mem _ _ _ ((presheaf_yoneda_map_etale_iff B S hS f).2 hf) hg

/-- **Stacks 03EC.** A morphism of the big fppf site of `S` between two étale charts of a
presheaf is an étale morphism of schemes.

The ambient presheaf need not be an algebraic space, so the statement covers the source one:
the second chart is étale and hence relatively representable, which is all that is used. The
morphism factors through the fibre product of the two charts, as a section of one projection
followed by the other. Both projections are étale by cancellation against the étale charts,
and a section of an étale morphism is étale by
`CategoryTheory.MorphismProperty.of_postcomp`, so no descent along an atlas is required. -/
@[stacks 03EC "morphism_between_charts"]
theorem etale_of_etale_charts {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U U' : BigFppfOver B S hS}
    (φ : yoneda.obj U ⟶ F) (φ' : yoneda.obj U' ⟶ F)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hφ' : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ')
    (χ : U ⟶ U') (hχ : yoneda.map χ ≫ φ' = φ) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map χ) := by
  let T := BigFppfOver.toScheme B S hS
  have hsnd : AlgebraicGeometry.Etale (T.map (hφ'.rep.snd φ)) :=
    hφ'.property φ (yoneda.map (hφ'.rep.fst' φ)) (hφ'.rep.snd φ) (hφ'.rep.isPullback' φ)
  have hfst : AlgebraicGeometry.Etale (T.map (hφ'.rep.fst' φ)) :=
    hφ.property φ' (yoneda.map (hφ'.rep.snd φ)) (hφ'.rep.fst' φ) (hφ'.rep.isPullback' φ).flip
  have hcomm : yoneda.map χ ≫ φ' = yoneda.map (𝟙 U) ≫ φ := by simpa using hχ
  have hsection : hφ'.rep.lift' χ (𝟙 U) hcomm ≫ hφ'.rep.snd φ = 𝟙 U :=
    hφ'.rep.lift'_snd _ _ _
  have hprojection : hφ'.rep.lift' χ (𝟙 U) hcomm ≫ hφ'.rep.fst' φ = χ :=
    hφ'.rep.lift'_fst _ _ _
  have hlift : AlgebraicGeometry.Etale (T.map (hφ'.rep.lift' χ (𝟙 U) hcomm)) := by
    refine MorphismProperty.of_postcomp
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) _
      (T.map (hφ'.rep.snd φ)) hsnd ?_
    rw [← T.map_comp, hsection, T.map_id]
    infer_instance
  rw [← hprojection, T.map_comp]
  infer_instance

/-- **Stacks 03EC.** Étaleness of a chart of an algebraic space descends along a surjective
étale morphism of the big fppf site of `S`: if `χ : U ⟶ U'` is surjective étale and
`yoneda.map χ ≫ φ'` is an étale chart, then so is `φ'`. -/
@[stacks 03EC "descent_from_chart"]
theorem etale_of_comp_surjective_etale {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U U' : BigFppfOver B S hS} (χ : U ⟶ U')
    [AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map χ)]
    [AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map χ)]
    (φ' : yoneda.obj U' ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map χ ≫ φ')) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ' := by
  set q := BigFppfOver.toScheme B S hS with hq
  set P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) q with hP
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : P.IsStableUnderBaseChange := etale_presheaf_isStableUnderBaseChange B S hS
  have hrep : yoneda.relativelyRepresentable φ' :=
    (Functor.relativelyRepresentable.diag_iff).1 hX.diagonal_representable φ'
  apply MorphismProperty.relative_of_snd (P := P) hrep
  intro A g
  set d := hrep.fst' g with hd
  set s := hrep.snd g with hs
  have hpb : IsPullback (pullback.fst d χ) (pullback.snd d χ) d χ :=
    IsPullback.of_hasPullback (f := d) (g := χ)
  have hcompPB : IsPullback (yoneda.map (pullback.snd d χ))
      (yoneda.map (pullback.fst d χ) ≫ yoneda.map s) (yoneda.map χ ≫ φ') g :=
    (hpb.map yoneda).flip.paste_vert (by rw [hrep.map_fst' g]; exact hrep.isPullback g)
  have : AlgebraicGeometry.Surjective (q.map (pullback.fst d χ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb.map q).flip
      (show AlgebraicGeometry.Surjective (q.map χ) from inferInstance)
  have : AlgebraicGeometry.Etale (q.map (pullback.fst d χ)) :=
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.of_isPullback (hpb.map q).flip
      (show AlgebraicGeometry.Etale (q.map χ) from inferInstance)
  have : AlgebraicGeometry.Etale (q.map (pullback.fst d χ) ≫ q.map s) := by
    rw [← Functor.map_comp]
    exact hφ.property g (yoneda.map (pullback.snd d χ)) (pullback.fst d χ ≫ s) hcompPB
  exact Stacks.Etale.etale_of_comp_surjective_etale
    (q.map (pullback.fst d χ)) (q.map s)

/-- **Stacks 02X1.** A surjective étale chart of the target of a morphism of algebraic spaces
lifts to a surjective étale chart of the source, together with a morphism of the site making
the square commute.

The lift is the base change along the given chart `q` of an arbitrary surjective étale atlas
`t` of the source: that base change is representable because `q` is, and both surjectivity
and étaleness are stable under base change and composition. Only the source need be an
algebraic space; the version without any hypothesis on the target is
`AlgebraicGeometry.Space.exists_surjective_etale_chart_lift`, and the tag is registered there,
in `StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocal`, whose module is the one the tag is the
subject of. The two statements are the same existential; this one additionally takes `_hG`,
which as its underscore records is never used. -/
theorem exists_surjective_etale_presentation_lift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (_hG : IsAlgebraicSpace B S hS G)
    (a : F ⟶ G) (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ G)
    (hq_surjective : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hq_etale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F) (α : U ⟶ V),
      p ≫ a = yoneda.map α ≫ q ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  set QSurjective := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hQS
  set QEtale := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hQE
  have : QSurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : QEtale.IsStableUnderBaseChange := etale_presheaf_isStableUnderBaseChange B S hS
  obtain ⟨W, t, ht_surjective, ht_etale⟩ := hF.exists_atlas
  obtain ⟨U, αW, fst, hpb⟩ := hq_etale.1 (t ≫ a)
  refine ⟨U, yoneda.map αW ≫ t, yoneda.preimage fst, ?_, ?_, ?_⟩
  · simpa only [yoneda.map_preimage, Category.assoc] using hpb.w.symm
  · exact MorphismProperty.comp_mem QSurjective.presheaf _ _
      (MorphismProperty.relative_map (F := yoneda)
        (hq_surjective.2 (t ≫ a) fst αW hpb)) ht_surjective
  · exact MorphismProperty.comp_mem QEtale.presheaf _ _
      (MorphismProperty.relative_map (F := yoneda)
        (hq_etale.2 (t ≫ a) fst αW hpb)) ht_etale

end AlgebraicGeometry.Space

end
