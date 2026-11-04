module

public import Mathlib
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SmallApproximationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationInduction
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureFGSubalgebraDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFromEtaleCover
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.AlgebraMapSections
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.QuasiCompactReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.FinitePresentationCase

/-!
# Schemes descend along purely transcendental field extensions

The finite field case, by approximation with spaces of finite presentation on an enlarged
site, and **Stacks 0B85**:
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_purelyTranscendental_baseChange`.

This is part of `StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace PurelyTranscendentalDescent

attribute [local instance] MorphismProperty.IsMultiplicative.toContainsIdentities
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- **The finite field case, given a small approximation by spaces of finite presentation.** Let
`k` be finite, `A` a finitely generated `k`-subalgebra of a purely transcendental extension `K`,
and `F` an algebraic space over `k` with `F_A` a scheme. If `F` is the limit of a directed system
of algebraic spaces of finite presentation over `k` with affine transition morphisms, indexed by a
set smaller than the cofinality of the site's cutoff, then `F` is a scheme: by Stacks 07SR some
stage `G` has `G_A` a scheme, so `G` is a scheme (its closed points are in its schematic locus),
and `F` is affine over `G`. -/
private theorem isRepresentable_of_fg_baseChange_of_finite_of_approximation
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] [Finite k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (A : Subalgebra k K) (hA : A.FG) (hAspec : B.Contains (Spec (.of A)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hAspec ⟶ B.obj hk)).obj F).IsRepresentable)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (D : Iᵒᵖ ⥤ ((AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u))
    (p : (Functor.const Iᵒᵖ).obj F ⟶ D) (hp : IsLimit (Cone.mk F p))
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk (D.obj i))
    (hfp : ∀ i, AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of k)) hk
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from (D.obj i)))
    (haff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B (Spec (.of k)) hk (D.map g)) :
    F.IsRepresentable := by
  let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
      B.obj hAspec ⟶ B.obj hk)
  obtain ⟨G, hG, f, g, hfpG, hg, hGbase⟩ :=
    exists_finitePresentation_model_of_isRepresentable_baseChange k B hk F hF T
      (inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))))) hbase hI D p hp hD hfp haff
  have hGrep := isRepresentable_of_fg_baseChange_of_finitePresentation
    k K B hk A hA hAspec G hG f hfpG hGbase
  have hrel := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B (Spec (.of k)) hk
    g hF hG).out 2 1).mp hg
  exact isRepresentable_of_relativelyRepresentable_of_isRepresentable g hrel.1 hGrep

/-- After enlarging the big fppf site to one whose cutoff has cofinality above the old cutoff, a
quasi-compact, absolutely quasi-separated algebraic space over `Spec k`, viewed over `Spec ℤ`, has
a small Noetherian approximation: its étale atlas by a scheme of the old site is small for the new
site. -/
private theorem hasSmallNoetherianApproximation_viewOverIntegers_changeBigSite
    (k : Type u) [Field k]
    (B B' : AlgebraicGeometry.BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B')
    (hcof : B.cutoff < B'.cutoff.ord.cof) (hk : B.Contains (Spec (.of k)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B (Spec (.of k)) hk F)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk
      B.contains_terminal F) :
    AlgebraicGeometry.Space.HasSmallNoetherianApproximation B' (⊤_ Scheme.{u})
      B'.contains_terminal B'.contains_terminal
      (AlgebraicGeometry.Space.viewOverIntegers B' (Spec (.of k)) (largerContains h hk)
        B'.contains_terminal
        ((AlgebraicGeometry.changeBigSite B B' h (Spec (.of k)) hk).obj ⟨F, hF⟩).obj) := by
  let hk' : B'.Contains (Spec (.of k)) := largerContains h hk
  let X : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨F, hF⟩
  let X' := (AlgebraicGeometry.changeBigSite B B' h (Spec (.of k)) hk).obj X
  have hX'qc := AlgebraicGeometry.changeBigSite_isQuasiCompactSpace B B' h _ hk X hqc
  have hX'qs := AlgebraicGeometry.changeBigSite_isAbsolutelyQuasiSeparated B B' h _ hk X hqc hqs
  let hZ' : B'.Contains (⊤_ Scheme.{u}) := B'.contains_terminal
  let g' : B'.obj hk' ⟶ B'.obj hZ' := ⟨terminal.from _⟩
  have hXZalg := AlgebraicGeometry.isAlgebraicSpace_viewOver B' (Spec (.of k)) (⊤_ Scheme.{u})
    hk' hZ' g' X'.obj X'.property
  have hXZqc := AlgebraicGeometry.Space.isQuasiCompactSpace_relocalize B' (Spec (.of k)) hk' hZ' g'
    hX'qc
  have hXZqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_viewOverIntegers B'
    (Spec (.of k)) hk' hZ' X'.obj hX'qs
  obtain ⟨U, a, has, hae, hsize⟩ : ∃ (U : AlgebraicGeometry.BigFppfOver B' (⊤_ Scheme.{u}) hZ')
      (a : yoneda.obj U ⟶ AlgebraicGeometry.Space.viewOverIntegers B' (Spec (.of k)) hk' hZ'
        X'.obj),
      (MorphismProperty.inverseImage (@Surjective.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B' (⊤_ Scheme.{u}) hZ')).presheaf a ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B' (⊤_ Scheme.{u}) hZ')).presheaf a ∧
      ((AlgebraicGeometry.BigFppfOver.toScheme B' (⊤_ Scheme.{u}) hZ').obj U).size <
        B'.cutoff.ord.cof := by
    obtain ⟨U, q, -, hqsurj, hqet⟩ :=
      (AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B
        (Spec (.of k)) hk F hF).1 hqc
    obtain ⟨R, s, t, q', hq's, hq'e, -, -⟩ := AlgebraicGeometry.changeBigSite_atlas B B' h _ hk X
      q hqsurj ((AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda B _ hk q).1 hqet)
    exact ⟨_, AlgebraicGeometry.relocalizeChart B' (Spec (.of k)) (⊤_ Scheme.{u}) hk' hZ' g' q',
      (AlgebraicGeometry.presheaf_relocalizeChart_iff B' (Spec (.of k)) (⊤_ Scheme.{u}) hk' hZ'
        g' _ q').2 hq's,
      (AlgebraicGeometry.presheaf_relocalizeChart_iff B' (Spec (.of k)) (⊤_ Scheme.{u}) hk' hZ'
        g' _ q').2 hq'e, U.left.property.trans hcof⟩
  exact AlgebraicGeometry.Space.hasSmallNoetherianApproximation_of_etaleAtlas hXZalg hXZqc hXZqs
    U a has ((AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda B' _ hZ' a).mpr hae) hsize

/-- **The finite field case.** The approximation of `F` by spaces of finite presentation, with an
index set small for the site, exists on an enlargement of the big fppf site in which `F` is
small (Stacks 09NS); the argument of `isRepresentable_of_fg_baseChange_of_finite_of_approximation`
runs there, and representability comes back along the enlargement. -/
private theorem isRepresentable_of_fg_baseChange_of_finite
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] [Finite k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (A : Subalgebra k K) (hA : A.FG) (hAspec : B.Contains (Spec (.of A)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B (Spec (.of k)) hk F)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk
      B.contains_terminal F)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hAspec ⟶ B.obj hk)).obj F).IsRepresentable) :
    F.IsRepresentable := by
  obtain ⟨B', h, hcof⟩ := AlgebraicGeometry.BigFppfSite.exists_isContained_lt_cof B B.cutoff
  let hk' : B'.Contains (Spec (.of k)) := largerContains h hk
  let hAspec' : B'.Contains (Spec (.of A)) := largerContains h hAspec
  let X : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨F, hF⟩
  let X' := (AlgebraicGeometry.changeBigSite B B' h (Spec (.of k)) hk).obj X
  let φ : B.obj hAspec ⟶ B.obj hk :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk := Over.mk φ
  have hFT : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk (F ⨯ yoneda.obj T) :=
    AlgebraicGeometry.isAlgebraicSpace_prod B (Spec (.of k)) hk hF
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk T)
  have h2 := (AlgebraicGeometry.isRepresentable_prod_yoneda_iff_changeBigSite B B' h _ hk X T
    hFT).2 (isRepresentable_prod_of_relocalizeRestrict φ F hbase)
  let φ' : B'.obj hAspec' ⟶ B'.obj hk' :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  have h3 : ((OverShriek.relocalizeRestrict φ').obj X'.obj).IsRepresentable :=
    isRepresentable_relocalizeRestrict_of_prod φ' X'.obj h2
  have := locallyOfFiniteType_terminal_from_spec_of_finiteType k
  have hSfp := locallyOfFinitePresentation_terminal_from (Spec (.of k))
  obtain ⟨I, _, _, _, hI, D, p, ⟨hp⟩, hD, hfp, haff⟩ :=
    AlgebraicGeometry.Space.exists_finitePresentation_system_of_hasSmallNoetherianApproximation
      B' (Spec (.of k)) hk' hSfp X'.property
      (hasSmallNoetherianApproximation_viewOverIntegers_changeBigSite k B B' h hcof hk F hF hqc hqs)
  have hfp' : ∀ i, AlgebraicGeometry.Space.IsFinitePresentation B' (Spec (.of k)) hk'
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from (D.obj i)) := fun i => by
    rw [(IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).hom_ext
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from (D.obj i))
      (AlgebraicGeometry.Space.toYonedaId B' (Spec (.of k)) hk' (D.obj i))]
    exact hfp i
  exact AlgebraicGeometry.isRepresentable_of_isRepresentable_changeBigSite B B' h _ hk X
    (isRepresentable_of_fg_baseChange_of_finite_of_approximation k K B' hk' A hA hAspec' X'.obj
      X'.property h3 hI D p hp hD hfp' haff)

end PurelyTranscendentalDescent

namespace Space

/-- **Stacks 0B85.** Let `k` be a field and `X` a quasi-separated algebraic space over `k`. If
there is a purely transcendental field extension `K/k` such that `X_K` is a scheme, then `X` is a
scheme. Here `X_K` is the restriction of `X` to the big fppf site over `Spec K`. -/
@[stacks 0B85]
theorem isRepresentable_of_isRepresentable_purelyTranscendental_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K]
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hqs : AlgebraicGeometry.Space.IsQuasiSeparatedOver B (Spec (.of k)) hk F)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          B.obj hK ⟶ B.obj hk)).obj F).IsRepresentable) :
    F.IsRepresentable := by
  obtain ⟨I, U, hcover, hqc⟩ :=
    PurelyTranscendentalDescent.exists_zariski_cover_with_quasiCompact_members B (Spec (.of k)) hk
      F hF
  apply PurelyTranscendentalDescent.isRepresentable_of_zariskiCover B (Spec (.of k)) hk F hF I U
    hcover
  intro i
  have hUi := (hcover.1 i).1
  have hUi_qs := PurelyTranscendentalDescent.isQuasiSeparated_subfunctor_of_isQuasiSeparated
    B (Spec (.of k)) hk (U i) hqs
  let g : B.obj hK ⟶ B.obj hk := ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hUi_base : ((OverShriek.relocalizeRestrict g).obj
      (U i).toFunctor).IsRepresentable := by
    have hrel := (PurelyTranscendentalDescent.presheaf_property_restrict B (Spec (.of K))
      (Spec (.of k)) hK hk g (U i).ι (@AlgebraicGeometry.IsOpenImmersion.{u}) (hcover.1 i).2).1
    exact PurelyTranscendentalDescent.isRepresentable_of_relativelyRepresentable_of_isRepresentable
      ((OverShriek.relocalizeRestrict g).map (U i).ι) hrel hbase
  have hUi_qs' := PurelyTranscendentalDescent.isQuasiSeparated_absolute_of_relative B
    (Spec (.of k)) hk B.contains_terminal (U i).toFunctor hUi hUi_qs
  obtain ⟨A, hA⟩ := AlgebraicGeometry.Space.exists_fgSubalgebra_isRepresentable_relocalizeRestrict
    k K B hk hK (U i).toFunctor hUi (hqc i) hUi_qs' hUi_base
  have hAspec := AlgebraicGeometry.Space.contains_spec_subalgebra k K B hK (A : Subalgebra k K)
  cases finite_or_infinite k with
  | inr hkInfinite =>
    exact PurelyTranscendentalDescent.isRepresentable_of_fg_baseChange_of_infinite k K B hk A.1 A.2
      hAspec (U i).toFunctor hA
  | inl hkFinite =>
    exact PurelyTranscendentalDescent.isRepresentable_of_fg_baseChange_of_finite k K B hk A.1 A.2
      hAspec (U i).toFunctor hUi (hqc i) hUi_qs' hA

end Space

end AlgebraicGeometry

end
