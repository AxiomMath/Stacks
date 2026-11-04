module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.TerminalSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.CategoryTheory.Limits.CartesianTransformationLimit
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Absolute Noetherian approximation: the open `W = f⁻¹(U)` and the transport lemmas

The inductive step of the proof of Stacks 07SU starts from an étale neighbourhood
`f : V ⟶ X` of a closed subspace complementary to a quasi-compact open `U ⊆ X` that already
has a Noetherian approximation. This file proves the parts of that step that do not involve
the approximations: the inverse image `W = f⁻¹(U)` is an open subscheme of `V`, quasi-compact and
quasi-separated.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.liftOfContains`: a functor to schemes whose values all lie in
  the site, as a functor to the big fppf site of the terminal scheme.
* `AlgebraicGeometry.BigFppfOver.natTransOfToScheme`: a natural transformation of the
  underlying scheme-valued functors, as a natural transformation of functors to that site.

## Main results

* `AlgebraicGeometry.Space.exists_openSiteObject_isPullback`: the inverse image `W = f⁻¹(U)`
  of an open subspace along a morphism from a representable presheaf is represented by an open
  subscheme of the source.
* `AlgebraicGeometry.Space.compactSpace_of_isPullback_yoneda` and
  `AlgebraicGeometry.Space.quasiSeparatedSpace_openSiteObject`: `W` is quasi-compact and
  quasi-separated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})} {C : Type*} [Category* C]

/-- A functor to schemes all of whose values lie in the site, as a functor to the big fppf site
of the terminal scheme. -/
noncomputable def liftOfContains (F : C ⥤ Scheme.{u}) (hF : ∀ c, B.Contains (F.obj c)) :
    C ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ where
  obj c := Over.mk (Y := B.obj (hF c)) (ObjectProperty.homMk (terminal.from (F.obj c)))
  map φ := homOfScheme B hZ (F.map φ)
  map_id c := (toScheme B (⊤_ Scheme.{u}) hZ).map_injective (F.map_id c)
  map_comp φ ψ := (toScheme B (⊤_ Scheme.{u}) hZ).map_injective (F.map_comp φ ψ)

/-- The functor `AlgebraicGeometry.BigFppfOver.liftOfContains` lifts the given functor. -/
theorem liftOfContains_comp_toScheme (F : C ⥤ Scheme.{u}) (hF : ∀ c, B.Contains (F.obj c)) :
    liftOfContains (hZ := hZ) F hF ⋙ toScheme B (⊤_ Scheme.{u}) hZ = F :=
  rfl

/-- A natural transformation between the scheme-valued functors underlying two functors to the
big fppf site of the terminal scheme, as a natural transformation of the latter. -/
noncomputable def natTransOfToScheme {F G : C ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (α : F ⋙ toScheme B (⊤_ Scheme.{u}) hZ ⟶ G ⋙ toScheme B (⊤_ Scheme.{u}) hZ) : F ⟶ G where
  app c := homOfScheme B hZ (α.app c)
  naturality _ _ φ := (toScheme B (⊤_ Scheme.{u}) hZ).map_injective (α.naturality φ)

/-- The components of `AlgebraicGeometry.BigFppfOver.natTransOfToScheme` lie over the given
ones. -/
@[simp]
theorem toScheme_map_natTransOfToScheme_app {F G : C ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (α : F ⋙ toScheme B (⊤_ Scheme.{u}) hZ ⟶ G ⋙ toScheme B (⊤_ Scheme.{u}) hZ) (c : C) :
    (toScheme B (⊤_ Scheme.{u}) hZ).map ((natTransOfToScheme α).app c) = α.app c :=
  rfl

/-- Over the terminal scheme, a commutative square of the site whose underlying square of
schemes is cartesian is cartesian. -/
theorem isPullback_of_isPullback_toScheme {P X Y Z : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback ((toScheme B (⊤_ Scheme.{u}) hZ).map fst)
      ((toScheme B (⊤_ Scheme.{u}) hZ).map snd) ((toScheme B (⊤_ Scheme.{u}) hZ).map f)
      ((toScheme B (⊤_ Scheme.{u}) hZ).map g)) :
    IsPullback fst snd f g :=
  IsPullback.of_map _ ((toScheme B (⊤_ Scheme.{u}) hZ).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact H.w)) H

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry

/-- **A quasi-compact scheme locally of finite type over `Spec ℤ` lies in every big fppf site
containing `Spec ℤ`**: its size is at most that of `Spec ℤ` (Stacks 04T7). -/
theorem BigFppfSite.contains_of_locallyOfFiniteType (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : Scheme.{u}) [LocallyOfFiniteType (terminal.from X)]
    [CompactSpace X] : B.Contains X :=
  (Scheme.size_le_of_locallyOfFiniteType (terminal.from X)).trans_lt hZ

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteTypeApproximation

attribute [local instance] indexPreorder

variable {I : Type u} [Preorder I] {D : Iᵒᵈ ⥤ Scheme.{u}} {S : Scheme.{u}} {U : S.Opens}
  {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D} (Q : FiniteTypeApproximation D S U p)

/-- **The reindexed original system is cartesian over the ambient system**, through the
comparison isomorphisms and the open immersions. -/
theorem isPullback_comparison_inv_inclusion {j j' : Q.indexTypeᵒᵈ} (f : j ⟶ j') :
    IsPullback ((Q.index.monotone.dual.functor ⋙ D).map f)
      (Q.comparison.inv.app j ≫ Q.inclusion.app j) (Q.comparison.inv.app j' ≫ Q.inclusion.app j')
      (Q.ambient.map f) :=
  (IsPullback.of_vert_isIso ⟨Q.comparison.inv.naturality f⟩).paste_vert
    (Q.transition_isPullback f)

/-- **The given open subscheme is the inverse image of each stage of the reindexed original
system**, when the index of the approximation is directed. -/
theorem isPullback_p_app [IsDirected Q.indexType (· ≤ ·)] (j : Q.indexTypeᵒᵈ) :
    IsPullback (p.app (Q.index.monotone.dual.functor.obj j)) U.ι
      (Q.comparison.inv.app j ≫ Q.inclusion.app j) (Q.ambientCone.app j) := by
  have : Nonempty Q.indexType := Q.indexNonempty
  have h := isPullback_of_isLimit_of_cartesian Q.inclusion (fun g => Q.transition_isPullback g)
    Q.openCone_isLimit Q.ambientCone_isLimit U.ι (fun x => (Q.inclusion_compatibility x).symm) j
  refine h.of_iso (Iso.refl _) (Q.comparison.app j) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
    simp [Q.comparison_compatibility]

end AlgebraicGeometry.Scheme.FiniteTypeApproximation

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **The inverse image of an open subspace along a morphism from a representable presheaf is
an open subscheme.** For an open immersion `U ⟶ X` and `f : h_V ⟶ X`, the base change of `U`
along `f` is represented by the object of the site attached to an open subscheme of `V`. -/
theorem exists_openSiteObject_isPullback {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (U : Subfunctor X) (hU : IsOpenImmersion B (⊤_ Scheme.{u}) hZ U.ι)
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (f : yoneda.obj V ⟶ X) :
    ∃ (O : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V).Opens)
      (gW : yoneda.obj (openSiteObject B (⊤_ Scheme.{u}) hZ V O) ⟶ U.toFunctor),
      IsPullback (yoneda.map (openSiteObjectHom B (⊤_ Scheme.{u}) hZ V O)) gW f U.ι := by
  have hrep := MorphismProperty.relative.rep hU
  let snd := hrep.snd f
  have hsnd : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map snd) :=
    MorphismProperty.relative.property_snd hU f
  let O := ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map snd).opensRange
  let e := ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map snd).isoOpensRange
  let eS : openSiteObject B (⊤_ Scheme.{u}) hZ V O ≅ hrep.pullback f :=
    (BigFppfOver.toSchemeFullyFaithfulOfTerminal B hZ).preimageIso e.symm
  let k := eS.hom
  have hk : k ≫ snd = openSiteObjectHom B (⊤_ Scheme.{u}) hZ V O :=
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective (by
      rw [Functor.map_comp]
      exact Scheme.Hom.isoOpensRange_inv_comp _)
  have h₁ : IsPullback (yoneda.map k) (yoneda.map (openSiteObjectHom B (⊤_ Scheme.{u}) hZ V O))
      (yoneda.map snd) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [← Functor.map_comp, hk, Category.comp_id]⟩
  have h := h₁.paste_horiz (hrep.isPullback f)
  rw [Category.id_comp] at h
  exact ⟨O, _, h.flip⟩

/-- **The inverse image of a quasi-compact open is quasi-compact.** If `X` is quasi-separated,
`U ⊆ X` a quasi-compact open subspace and `V` a quasi-compact scheme mapping to `X`, the
representing scheme of `V ×_X U` is quasi-compact. -/
theorem compactSpace_of_isPullback_yoneda {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hXqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    {U : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hUqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ U) (ι : U ⟶ X)
    {V W : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : yoneda.obj V ⟶ X)
    (hVc : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))
    (ιW : W ⟶ V) (gW : yoneda.obj W ⟶ U) (hW : IsPullback (yoneda.map ιW) gW f ι) :
    CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W) := by
  have hpb := isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hX hXqs hUqc ι
    (yoneda.obj V) (isAlgebraicSpace_yoneda B _ hZ V)
    (isQuasiCompact_yoneda_of_compact B _ hZ V hVc) f
  exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B _ hZ
    (isQuasiCompactSpace_of_iso B _ hZ hW.isoPullback.symm hpb)

/-- An open subscheme of a quasi-separated scheme of the site is quasi-separated. -/
theorem quasiSeparatedSpace_openSiteObject {S : Scheme.{u}} {hS : B.Contains S}
    (V : BigFppfOver B S hS) [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj V)]
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS V O)) :=
  O.ι.isOpenEmbedding.quasiSeparatedSpace

end AlgebraicGeometry.Space

end
