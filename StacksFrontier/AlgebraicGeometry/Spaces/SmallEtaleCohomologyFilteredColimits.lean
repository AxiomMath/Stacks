module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianPushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.FilteredColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FilteredColimitsAndCohomology
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite

/-!
# Filtered colimits and étale cohomology of an algebraic space

On a quasi-compact and quasi-separated algebraic space `X` over `S`, cohomology of abelian
sheaves on the small étale site commutes with filtered colimits: for every filtered diagram
`F` of abelian sheaves on `X_étale` and every degree `p`, the canonical comparison
`colim_i H^p(X, F_i) ⟶ H^p(X, colim_i F_i)` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections` is
  **Stacks 073E**.

## Implementation notes

Cohomology is `Functor.rightDerived` of the global sections functor `Sheaf.Γ` on the small
étale site, and the comparison map is `CategoryTheory.Limits.colimit.post`.

The proof specialises the site-level statement
`Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections` (Stacks 0739) to the
collection `B` of objects of the étale site of `X` which are quasi-compact and
quasi-separated, with the finite coverings by such objects as the cofinal family. That `B` is
stable under the iterated fibre products appearing in those coverings is Stacks 073B; that
finite coverings by members of `B` are cofinal uses quasi-compactness of the point space
(Stacks 03E4) together with the affine Zariski-refined étale atlases of
`AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas`.

Three changes of presentation separate that statement from the one proved here. First, the
site-level statement is for an index category and a sheaf universe matching the site, so it is
transported along `AddCommGrpCat.uliftFunctor` and along `AsSmall` to an arbitrary filtered
index category. Second, it is stated for sections over an object, which is converted to global
sections through the terminal object `X ⟶ X` of the étale site of spaces over `X`. Third, the
site of algebraic spaces étale over `X` is replaced by the small étale site of schemes étale
over `X` along the dense-subsite comparison of Stacks 03G1.

## References

* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section

universe v

/-- Universe lifting of abelian groups preserves injective objects: an abelian group is
injective exactly when it is injective as a `ℤ`-module, and the universe lift of modules
preserves injective modules. -/
private lemma ab_ulift_preservesInjectiveObjects :
    AddCommGrpCat.uliftFunctor.{w, u}.PreservesInjectiveObjects where
  injective_obj {M} hM := by
    apply (AddCommGrpCat.injective_as_module_iff _).mp
    have := (AddCommGrpCat.injective_as_module_iff M).mpr hM
    exact (ModuleCat.uliftFunctor.{w, u} ℤ).injective_obj (ModuleCat.of ℤ M)

/-- A limit-preserving functor commutes with the right adjoint of evaluation at an object of a
small category: the cofree diagram on `a` at `c`, pushed along `G`, is the cofree diagram on
`G.obj a` at `c`. -/
private noncomputable def evaluationRightAdjointCompIso
    {C : Type u} [SmallCategory C] {A D : Type*} [Category* A] [Category* D]
    [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u} D]
    (G : A ⥤ D) [PreservesLimitsOfSize.{u, u} G] (c : C) (a : A) :
    (evaluationRightAdjoint A c).obj a ⋙ G ≅
      (evaluationRightAdjoint D c).obj (G.obj a) := by
  refine NatIso.ofComponents (fun t ↦ PreservesProduct.iso G (fun _ : t ⟶ c ↦ a))
    fun f ↦ Pi.hom_ext _ _ fun g ↦ ?_
  dsimp [evaluationRightAdjoint, getLimitCone]
  simp only [Category.assoc, piComparison_comp_π, limit.lift_π,
    ← G.map_comp, Fan.mk_π_app]

/-- Postcomposition on a functor category with a limit-preserving functor which preserves
injective objects again preserves injective objects: an injective functor is a retract of a
product of cofree diagrams, and products and cofree diagrams are both preserved. -/
lemma whiskeringRight_preservesInjectiveObjects
    {C : Type u} [SmallCategory C] {A D : Type*} [Category* A] [Category* D]
    [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u} D] [EnoughInjectives A]
    (G : A ⥤ D) [G.PreservesInjectiveObjects] [PreservesLimitsOfSize.{u, u} G] :
    ((Functor.whiskeringRight C A D).obj G).PreservesInjectiveObjects := by
  classical
  let W := (Functor.whiskeringRight C A D).obj G
  refine ⟨fun {F} hF ↦ ?_⟩
  let Q (c : C) := (evaluationRightAdjoint A c).obj (Injective.under (F.obj c))
  let a (c : C) : F ⟶ Q c :=
    ((evaluationAdjunctionLeft A c).homEquiv F _)
      (Injective.ι (F.obj c))
  let i : F ⟶ ∏ᶜ Q := Pi.lift a
  have hi (c : C) : i.app c ≫ (Pi.π Q c).app c ≫
      (evaluationAdjunctionLeft A c).counit.app (Injective.under (F.obj c)) =
        Injective.ι (F.obj c) := by
    rw [← Category.assoc]
    have hh := congrArg (fun k : F ⟶ Q c ↦ k.app c) (Pi.lift_comp_π a c)
    change i.app c ≫ (Pi.π Q c).app c = (a c).app c at hh
    rw [hh]
    show ((evaluationAdjunctionLeft A c).homEquiv F _).symm (a c) =
      Injective.ι (F.obj c)
    exact ((evaluationAdjunctionLeft A c).homEquiv F _).symm_apply_apply
      (Injective.ι (F.obj c))
  have : Mono i := by
    have (c : C) : Mono (i.app c) := mono_of_mono_fac (hi c)
    exact NatTrans.mono_of_mono_app i
  have := hF
  let r : Retract F (∏ᶜ Q) :=
    ⟨i, Injective.factorThru (𝟙 F) i, Injective.comp_factorThru (𝟙 F) i⟩
  have hQ (c : C) : Injective (W.obj (Q c)) := by
    have : Injective ((evaluationRightAdjoint D c).obj
        (G.obj (Injective.under (F.obj c)))) :=
      (evaluationAdjunctionLeft D c).map_injective _ inferInstance
    exact Injective.of_iso (evaluationRightAdjointCompIso G c _).symm inferInstance
  have := hQ
  have : Injective (W.obj (∏ᶜ Q)) :=
    Injective.of_iso (asIso (piComparison W Q)).symm inferInstance
  exact (r.map W).injective

/-- Postcomposition on sheaves with a limit-preserving functor which preserves injective
objects again preserves injective objects: an injective sheaf is injective as a presheaf, and
injectivity of a presheaf is preserved by postcomposition. -/
lemma sheafCompose_preservesInjectiveObjects
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {A D : Type*} [Category* A] [Category* D]
    [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u} D] [EnoughInjectives A]
    [HasSheafify J A] [HasSheafify J D]
    (G : A ⥤ D) [G.PreservesInjectiveObjects] [PreservesLimitsOfSize.{u, u} G] :
    (sheafCompose J G).PreservesInjectiveObjects := by
  have := whiskeringRight_preservesInjectiveObjects (C := Cᵒᵖ) G
  refine ⟨fun {F} hF ↦ ?_⟩
  have : Injective F.obj := (sheafificationAdjunction J A).map_injective _ hF
  have : Injective (F.obj ⋙ G) :=
    ((Functor.whiskeringRight Cᵒᵖ A D).obj G).injective_obj F.obj
  exact Functor.injective_of_map_injective (sheafToPresheaf J D) this

/-- A functor out of a reflective subcategory preserves colimits of a given shape as soon as
its composite with the reflector does: every object is the reflection of its image. -/
private lemma preservesColimitsOfShape_of_reflective
    {P S T I : Type*} [Category* P] [Category* S] [Category* T] [Category* I]
    {L : P ⥤ S} {R : S ⥤ P} (adj : L ⊣ R) [R.Full] [R.Faithful]
    [HasColimitsOfShape I P] (G : S ⥤ T) [PreservesColimitsOfShape I (L ⋙ G)] :
    PreservesColimitsOfShape I G where
  preservesColimit {F} := by
    have := adj.leftAdjoint_preservesColimits
    let e : (F ⋙ R) ⋙ L ≅ F := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ Functor.rightUnitor F
    have : PreservesColimit ((F ⋙ R) ⋙ L) G :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit (F ⋙ R)))
        (isColimitOfPreserves (L ⋙ G) (colimit.isColimit (F ⋙ R)))
    exact preservesColimit_of_iso_diagram G e

/-- Postcomposition on sheaves with a functor which preserves colimits of a given shape and
preserves sheafification again preserves those colimits. -/
lemma sheafCompose_preservesColimitsOfShape
    {C I : Type*} [Category* C] [Category* I] (J : GrothendieckTopology C)
    {A D : Type*} [Category* A] [Category* D]
    [HasColimitsOfShape I A] [HasSheafify J A] [HasSheafify J D]
    (G : A ⥤ D) [J.HasSheafCompose G] [J.PreservesSheafification G]
    [PreservesColimitsOfShape I G] : PreservesColimitsOfShape I (sheafCompose J G) := by
  have : PreservesColimitsOfShape I (presheafToSheaf J A ⋙ sheafCompose J G) :=
    preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J G (sheafificationAdjunction J A) (sheafificationAdjunction J D))
  exact preservesColimitsOfShape_of_reflective (sheafificationAdjunction J A) _

/-- Postcomposition on sheaves with a functor which preserves limits of a given shape again
preserves those limits, since limits of sheaves are computed in presheaves. -/
lemma sheafCompose_preservesLimitsOfShape
    {C I : Type*} [Category* C] [Category* I] (J : GrothendieckTopology C)
    {A D : Type*} [Category* A] [Category* D]
    [HasLimitsOfShape I A] [HasSheafify J A] [HasSheafify J D]
    (G : A ⥤ D) [J.HasSheafCompose G] [PreservesLimitsOfShape I G] :
    PreservesLimitsOfShape I (sheafCompose J G) := by
  have : PreservesLimitsOfShape I (sheafCompose J G ⋙ sheafToPresheaf J D) :=
    inferInstanceAs (PreservesLimitsOfShape I
      (sheafToPresheaf J A ⋙ (Functor.whiskeringRight Cᵒᵖ A D).obj G))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J D)

/-- Presheaves of abelian groups whose sections lie above the universe of a small site admit a
left exact sheafification. -/
private theorem largeAbSheafify {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) : HasSheafify J Ab.{max u w} :=
  have _ : EssentiallySmall.{max u w} C := essentiallySmall_lift.{w, u} C
  hasSheafify_addCommGrpCat_of_essentiallySmall.{max u w, u, u} J

attribute [local instance] largeAbSheafify

/-- Universe lifting of abelian groups preserves sheafification on a small site: the
underlying-set functor preserves limits and filtered colimits in either universe. -/
private lemma ulift_preservesSheafification {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{w, u} := by
  have : PreservesLimitsOfSize.{u, u} (forget Ab.{max u w}) :=
    preservesLimitsOfSize_shrink (forget Ab.{max u w})
  have : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{max u w}) :=
    preservesFilteredColimitsOfSize_shrink (forget Ab.{max u w})
  have (X : C) : PreservesColimitsOfShape (J.Cover X)ᵒᵖ
      (forget Ab.{max u w}) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
  exact GrothendieckTopology.instPreservesSheafification J AddCommGrpCat.uliftFunctor.{w, u}

/-- Reindexing a diagram along an equivalence of index categories does not change whether the
comparison `colimit.post` is an isomorphism. -/
private lemma isIso_colimit_post_rightDerived_sheafSections_anySize
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (PreZeroHypercover.{v} U))
    (hCov : ∀ U E, Cov U E → E.sieve₀ ∈ J U)
    (hfinite : ∀ U E, Cov U E → Stacks.Cohomology.HasIntersectionsIn B E)
    (hcofinal : ∀ U, B U → ∀ S ∈ J U, ∃ E, Cov U E ∧ E.sieve₀ ≤ S)
    (p : ℕ) (U : C) (hU : B U)
    {I : Type w} [SmallCategory I] [IsFiltered I] [HasColimitsOfShape I Ab.{u}]
    (F : I ⥤ Sheaf J Ab.{u}) :
    letI : EnoughInjectives (Sheaf J Ab.{u}) := IsGrothendieckAbelian.enoughInjectives
    IsIso (colimit.post F (((sheafSections J Ab.{u}).obj (Opposite.op U)).rightDerived p)) := by
  let : EnoughInjectives (Sheaf J Ab.{u}) := IsGrothendieckAbelian.enoughInjectives
  let : EnoughInjectives (Sheaf J Ab.{max u w}) :=
    (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u w} J Ab.{max u w}).enoughInjectives
  let G := AddCommGrpCat.uliftFunctor.{w, u}
  have : G.PreservesInjectiveObjects := ab_ulift_preservesInjectiveObjects
  have : J.PreservesSheafification G := ulift_preservesSheafification J
  let L := sheafCompose J G
  have : L.Additive := ⟨rfl⟩
  have : L.PreservesInjectiveObjects := sheafCompose_preservesInjectiveObjects J G
  have : PreservesFiniteLimits L :=
    ⟨fun _ _ _ ↦ sheafCompose_preservesLimitsOfShape J G⟩
  have : PreservesFiniteColimits L :=
    ⟨fun _ _ _ ↦ sheafCompose_preservesColimitsOfShape J G⟩
  have : PreservesColimitsOfShape I L := sheafCompose_preservesColimitsOfShape J G
  let H := (sheafSections J Ab.{u}).obj (Opposite.op U)
  let H' := (sheafSections J Ab.{max u w}).obj (Opposite.op U)
  let eI : I ≌ AsSmall.{u} I := AsSmall.equiv
  have : IsFiltered (AsSmall.{u} I) := IsFiltered.of_equivalence eI
  have : IsIso (colimit.post (eI.symm.functor ⋙ (F ⋙ L)) (H'.rightDerived p)) :=
    Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients J B Cov
      hCov hfinite hcofinal p U hU (eI.symm.functor ⋙ (F ⋙ L))
  have : IsIso (colimit.post (F ⋙ L) (H'.rightDerived p)) :=
    Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_of_equivalence_reindex eI.symm
      (F ⋙ L) (H'.rightDerived p)
  have : IsIso (colimit.post F (L ⋙ H'.rightDerived p)) := by
    rw [← colimit.post_post]
    infer_instance
  let a : L ⋙ H'.rightDerived p ≅ H.rightDerived p ⋙ G :=
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L H' p).symm ≪≫
      Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso (Iso.refl _) p ≪≫
        Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso H G p
  have : IsIso (colimit.post F (H.rightDerived p ⋙ G)) :=
    Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _ a
  have : IsIso (G.map (colimit.post F (H.rightDerived p))) := by
    have : IsIso (colimit.post (F ⋙ H.rightDerived p) G ≫
        G.map (colimit.post F (H.rightDerived p))) := by
      rw [colimit.post_post]
      infer_instance
    exact IsIso.of_isIso_comp_left (colimit.post (F ⋙ H.rightDerived p) G) _
  exact isIso_of_reflects_iso (colimit.post F (H.rightDerived p)) G

end

/-- Every object of the site of algebraic spaces étale over `X` is covered by affine schemes
étale over it, and a scheme which is affine is quasi-compact and quasi-separated as an
algebraic space. -/
private lemma exists_quasiCompact_quasiSeparated_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (U : SpacesEtale B S hS X) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      SpacesEtale.IsCovering B S hS X ⟨U, E⟩ ∧
      ∀ i, IsQuasiCompactSpace B S hS (E.X i).obj.left.obj ∧
        IsAbsolutelyQuasiSeparated B S hS hZ (E.X i).obj.left.obj := by
  classical
  obtain ⟨I, V, hV, hdata⟩ := exists_zariski_cover_affine_etale_atlas
    B S hS U.obj.left.obj U.obj.left.property
  choose T f W hAff hSurj hEt hW hbase using hdata
  let g (i : I) := f i ≫ (V i).ι
  have hg (i : I) : IsEtale B S hS (g i) := by
    have hi : IsEtale B S hS (V i).ι := by
      apply isEtale_of_presheaf_etale
      apply MorphismProperty.relative_monotone (P :=
        MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
          (BigFppfOver.toScheme B S hS)) ?_ _ (hV.1 i).2
      intro A D k hk
      have : AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map k) := hk
      show AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k)
      infer_instance
    intro A φ hφ
    exact hi A (φ ≫ f i) (isEtale_of_presheaf_etale B S hS (hEt i) A φ hφ)
  let Y (i : I) : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (T i), isAlgebraicSpace_yoneda B S hS (T i)⟩
  let Z (i : I) : SpacesEtale B S hS X :=
    ⟨Over.mk (ObjectProperty.homMk (g i ≫ U.obj.hom.hom) : Y i ⟶ X), by
      intro A φ hφ
      simpa [Category.assoc] using U.property A (φ ≫ g i) (hg i A φ hφ)⟩
  let k (i : I) : Z i ⟶ U :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (g i)) rfl)
  let E : PreZeroHypercover.{u + 1} U :=
    ⟨ULift.{u + 1} I, fun i ↦ Z i.down, fun i ↦ k i.down⟩
  refine ⟨E, ?_, ?_⟩
  · intro x
    have hx : x ∈ ⋃ i, Set.range (pointsMap B S hS (V i).toFunctor (V i).ι) := by
      rw [(isZariskiCover_iff_iUnion_points
        B S hS U.obj.left.obj U.obj.left.property I V hV.1).mp hV]
      trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda
      B S hS (V i).toFunctor (hV.1 i).1 (T i) (f i)).mp (hSurj i) y
    refine ⟨⟨i⟩, z, ?_⟩
    show pointsMap B S hS (yoneda.obj (T i)) (f i ≫ (V i).ι) z = x
    rw [pointsMap_comp, Function.comp_apply, hz]
    exact hy
  · rintro ⟨i⟩
    show IsQuasiCompactSpace B S hS (yoneda.obj (T i)) ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i))
    have := hAff i
    constructor
    · refine ⟨T i, 𝟙 _, inferInstance, ?_, ?_⟩
      · have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
            (BigFppfOver.toScheme B S hS)).RespectsIso :=
          MorphismProperty.RespectsIso.inverseImage _ _
        apply MorphismProperty.relative.of_exists
        intro A φ
        refine ⟨A, φ, 𝟙 A, ?_, ?_⟩
        · simpa using IsPullback.id_vert φ
        · show AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map (𝟙 A))
          simpa using (inferInstance : AlgebraicGeometry.Surjective (𝟙 _))
      · intro A φ hφ
        simpa using hφ
    · exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
        ⟨T i, inferInstance, ⟨Functor.RepresentableBy.yoneda (T i)⟩⟩

/-- Every covering sieve of the site of algebraic spaces étale over `X` is refined by a
covering family, by induction on the generation of the topology from the precoverage. -/
private lemma spacesEtale_exists_covering_refining_sieve
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    {U : SpacesEtale B S hS X} {R : Sieve U}
    (hR : R ∈ SpacesEtale.topology B S hS X U) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      SpacesEtale.IsCovering B S hS X ⟨U, E⟩ ∧ E.presieve₀ ≤ R := by
  classical
  rw [SpacesEtale.topology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of U P hP =>
      obtain ⟨E, hEq, hE⟩ := hP
      exact ⟨E, hE, by rw [hEq]; exact Sieve.le_generate _⟩
  | top U =>
      exact ⟨PreZeroHypercover.singleton (𝟙 U),
        (SpacesEtale.isSite B S hS X).1 (𝟙 U), fun _ _ _ ↦ trivial⟩
  | pullback U R hR V f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ :=
        (SpacesEtale.isSite B S hS X).2.2 ⟨U, E⟩ hE V f
      let F : PreZeroHypercover.{u + 1} V := ⟨E.I₀, P, p₂⟩
      refine ⟨F, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive U R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      have hlocal (i : E.I₀) := ihRQ (hle _ _ ⟨i⟩)
      choose F hF hFle using hlocal
      have hEF : SpacesEtale.IsCovering B S hS X ⟨U, E.bind F⟩ :=
        (SpacesEtale.isSite B S hS X).2.1 ⟨U, E⟩ hE
          (fun i ↦ ⟨E.X i, F i⟩) hF (fun _ ↦ rfl)
      refine ⟨E.bind F, hEF, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      exact hFle i _ _ ⟨j⟩

/-- A covering family of a quasi-compact object of the site of algebraic spaces étale over `X`
has a finite subfamily which still covers: the ranges on points are open, by Stacks 03IR, and
cover the compact point space of Stacks 03E4. -/
private lemma exists_finite_subcover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    {U : SpacesEtale B S hS X}
    (hU : IsQuasiCompactSpace B S hS U.obj.left.obj)
    (E : PreZeroHypercover.{u + 1} U)
    (hE : SpacesEtale.IsCovering B S hS X ⟨U, E⟩) :
    ∃ t : Finset E.I₀,
      SpacesEtale.IsCovering B S hS X
        ⟨U, ⟨(t : Set E.I₀), fun i ↦ E.X i.1, fun i ↦ E.f i.1⟩⟩ := by
  classical
  have : CompactSpace (points B S hS U.obj.left.obj) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS U.obj.left.obj
      U.obj.left.property).mp hU
  let V (i : E.I₀) : Set (points B S hS U.obj.left.obj) :=
    Set.range (pointsMap B S hS (E.X i).obj.left.obj (E.f i).hom.left.hom)
  have hV (i : E.I₀) : IsOpen (V i) :=
    (isOpenMap_pointsMap_of_isEtale B S hS (E.f i).hom.left.hom
      (E.X i).obj.left.property U.obj.left.property
      (isEtale_of_isEtale_over B S hS
        (E.X i).obj.left.property U.obj.left.property X.property
        (E.f i).hom.left.hom (E.X i).obj.hom.hom U.obj.hom.hom
        (E.X i).property U.property
        (congrArg (fun f ↦ f.hom) (E.f i).hom.w))).isOpen_range
  have hcover : Set.univ ⊆ ⋃ i, V i := fun x _ ↦ Set.mem_iUnion.mpr (hE x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  refine ⟨t, fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hit, y, hy⟩ := Set.mem_iUnion.mp hi
  exact ⟨⟨i, hit⟩, y, hy⟩

/-- Every covering sieve of a quasi-compact object of the site of algebraic spaces étale over
`X` is refined by a finite covering family all of whose members are quasi-compact and
quasi-separated. -/
private lemma exists_finite_quasiCompact_quasiSeparated_refinement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    {U : SpacesEtale B S hS X}
    (hU : IsQuasiCompactSpace B S hS U.obj.left.obj)
    (R : Sieve U) (hR : R ∈ SpacesEtale.topology B S hS X U) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      E.sieve₀ ∈ SpacesEtale.topology B S hS X U ∧
      Finite E.I₀ ∧
      (∀ i, IsQuasiCompactSpace B S hS (E.X i).obj.left.obj ∧
        IsAbsolutelyQuasiSeparated B S hS hZ (E.X i).obj.left.obj) ∧ E.sieve₀ ≤ R := by
  classical
  obtain ⟨E, hE, hle⟩ := spacesEtale_exists_covering_refining_sieve B S hS X hR
  choose F hF hqcqs using fun i ↦
    exists_quasiCompact_quasiSeparated_cover B S hS hZ X (E.X i)
  have hEF : SpacesEtale.IsCovering B S hS X ⟨U, E.bind F⟩ :=
    (SpacesEtale.isSite B S hS X).2.1 ⟨U, E⟩ hE
      (fun i ↦ ⟨E.X i, F i⟩) hF (fun _ ↦ rfl)
  obtain ⟨t, ht⟩ := exists_finite_subcover B S hS X hU (E.bind F) hEF
  let H : PreZeroHypercover.{u + 1} U :=
    ⟨(t : Set (E.bind F).I₀), fun i ↦ (E.bind F).X i.1, fun i ↦ (E.bind F).f i.1⟩
  refine ⟨H, ?_, inferInstance, ?_, ?_⟩
  · exact (SpacesEtale.precoverage B S hS X).le_toPrecoverage_toGrothendieck
      _ ⟨H, rfl, ht⟩
  · rintro ⟨⟨i, j⟩, hij⟩
    exact hqcqs i j
  · show Sieve.generate H.presieve₀ ≤ R
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    rintro ⟨⟨i, j⟩, hij⟩
    exact R.downward_closed (hle _ _ ⟨i⟩) ((F i).f j)

/-- Two morphisms of the site of algebraic spaces étale over `X` are equal as soon as the
underlying morphisms of presheaves are. -/
private lemma spacesEtale_hom_ext
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS}
    {U V : SpacesEtale B S hS X} {f g : U ⟶ V}
    (h : f.hom.left.hom = g.hom.left.hom) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ h))

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Two morphisms of the site of algebraic spaces étale over `X` with a common quasi-separated
target, out of quasi-compact and quasi-separated sources, have a fibre product in that site
which is again quasi-compact and quasi-separated; this is Stacks 073B, part (3). -/
private lemma exists_quasiCompact_quasiSeparated_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    {U V W : SpacesEtale B S hS X} (f : U ⟶ W) (g : V ⟶ W)
    (hUqc : IsQuasiCompactSpace B S hS U.obj.left.obj)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.obj.left.obj)
    (hVqc : IsQuasiCompactSpace B S hS V.obj.left.obj)
    (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.obj.left.obj)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.obj.left.obj) :
    ∃ t : PullbackCone f g, Nonempty (IsLimit t) ∧
      IsQuasiCompactSpace B S hS t.pt.obj.left.obj ∧
      IsAbsolutelyQuasiSeparated B S hS hZ t.pt.obj.left.obj := by
  classical
  let P := AlgebraicSpaces.fiberProduct B S hS f.hom.left g.hom.left
  let a : P ⟶ U.obj.left := ObjectProperty.homMk (pullback.fst f.hom.left.hom g.hom.left.hom)
  let b : P ⟶ V.obj.left := ObjectProperty.homMk (pullback.snd f.hom.left.hom g.hom.left.hom)
  have hab : IsPullback a b f.hom.left g.hom.left :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f.hom.left g.hom.left
  have hg : IsEtale B S hS g.hom.left.hom :=
    isEtale_of_isEtale_over B S hS V.obj.left.property W.obj.left.property
      X.property g.hom.left.hom V.obj.hom.hom W.obj.hom.hom V.property W.property
      (congrArg (fun f ↦ f.hom) g.hom.w)
  have ha : IsEtale B S hS a.hom :=
    isEtale_of_isPullback B S hS b a g.hom.left f.hom.left hab.flip hg
  let Q : SpacesEtale B S hS X :=
    ⟨Over.mk (a ≫ U.obj.hom), by
      intro A φ hφ
      simpa [Category.assoc] using U.property A (φ ≫ a.hom) (ha A φ hφ)⟩
  let a' : Q ⟶ U := ObjectProperty.homMk (Over.homMk a rfl)
  let b' : Q ⟶ V := ObjectProperty.homMk (Over.homMk b (by
    show b ≫ V.obj.hom = a ≫ U.obj.hom
    rw [← g.hom.w, ← f.hom.w, ← Category.assoc, ← Category.assoc, hab.w]))
  have hab' : a' ≫ f = b' ≫ g :=
    spacesEtale_hom_ext pullback.condition
  let t := PullbackCone.mk a' b' hab'
  refine ⟨t, ⟨?_⟩, ?_, ?_⟩
  · let lift (s : PullbackCone f g) : s.pt ⟶ Q :=
      ObjectProperty.homMk (Over.homMk
        (ObjectProperty.homMk (pullback.lift s.fst.hom.left.hom s.snd.hom.left.hom
          (congrArg (fun f ↦ f.hom.left.hom) s.condition))) (by
            apply ObjectProperty.hom_ext
            show pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ U.obj.hom.hom) = _
            rw [← Category.assoc, pullback.lift_fst]
            exact congrArg (fun f ↦ f.hom) s.fst.hom.w))
    refine PullbackCone.IsLimit.mk hab' lift
      (fun _ ↦ spacesEtale_hom_ext (pullback.lift_fst _ _ _))
      (fun _ ↦ spacesEtale_hom_ext (pullback.lift_snd _ _ _))
      fun s m hm₁ hm₂ ↦ spacesEtale_hom_ext (pullback.hom_ext ?_ ?_)
    · show m.hom.left.hom ≫ pullback.fst f.hom.left.hom g.hom.left.hom =
        pullback.lift s.fst.hom.left.hom s.snd.hom.left.hom _ ≫
          pullback.fst f.hom.left.hom g.hom.left.hom
      rw [pullback.lift_fst]
      exact congrArg (fun f ↦ f.hom.left.hom) hm₁
    · show m.hom.left.hom ≫ pullback.snd f.hom.left.hom g.hom.left.hom =
        pullback.lift s.fst.hom.left.hom s.snd.hom.left.hom _ ≫
          pullback.snd f.hom.left.hom g.hom.left.hom
      rw [pullback.lift_snd]
      exact congrArg (fun f ↦ f.hom.left.hom) hm₂
  · exact isQuasiCompactSpace_pullback B S hS hZ f.hom.left.hom g.hom.left.hom
      U.obj.left.property W.obj.left.property hUqc hVqc hWqs
  · exact isAbsolutelyQuasiSeparated_pullback B S hS hZ f.hom.left.hom g.hom.left.hom
      U.obj.left.property V.obj.left.property W.obj.left.property hUqs hVqs

-- The wide-pullback induction is
-- `Stacks.Cohomology.exists_widePullback_in` of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/FilteredColimits/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/FilteredColimits/SectionsOnALocallySmallSite.lean` (line 91); the private copy that used to stand here was
-- the same statement.

/-- Abelian sheaves on the site of algebraic spaces étale over `X` have enough injectives. -/
private noncomputable local instance spacesSheaf_enoughInjectives
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    EnoughInjectives (Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives

/-- Sections over an object of the site of algebraic spaces étale over `X` are additive. -/
private noncomputable local instance spacesSections_additive
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X) :
    ((sheafSections (SpacesEtale.topology B S hS X) Ab.{u + 1}).obj
      (Opposite.op U)).Additive where
  map_add := rfl

/-- Stacks 073E for sections over a quasi-compact and quasi-separated object of the site of
algebraic spaces étale over `X`: the quasi-compact and quasi-separated objects of that site,
with the finite coverings by such objects, satisfy the hypotheses of Stacks 0739. -/
private lemma isIso_colimit_post_rightDerived_spacesSections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (U : SpacesEtale B S hS X)
    (hUqc : IsQuasiCompactSpace B S hS U.obj.left.obj)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.obj.left.obj)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (F : I ⥤ Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1}) :
    IsIso (colimit.post F
      (((sheafSections (SpacesEtale.topology B S hS X) Ab.{u + 1}).obj
        (Opposite.op U)).rightDerived p)) := by
  let Q : Set (SpacesEtale B S hS X) := fun V ↦
    IsQuasiCompactSpace B S hS V.obj.left.obj ∧
      IsAbsolutelyQuasiSeparated B S hS hZ V.obj.left.obj
  let Cov : ∀ V : SpacesEtale B S hS X, Set (PreZeroHypercover.{u + 1} V) :=
    fun V E ↦ E.sieve₀ ∈ SpacesEtale.topology B S hS X V ∧
      Q V ∧ Finite E.I₀ ∧ ∀ i, Q (E.X i)
  apply isIso_colimit_post_rightDerived_sheafSections_anySize
    (SpacesEtale.topology B S hS X) Q Cov
    (fun _ _ h ↦ h.1) ?_ ?_ p U ⟨hUqc, hUqs⟩ F
  · intro V E hE
    exact ⟨hE.2.2.1, hE.2.1, hE.2.2.2, fun n a ↦
      Stacks.Cohomology.exists_widePullback_in Q
        (fun f g hV hW hT ↦ exists_quasiCompact_quasiSeparated_pullback B S hS hZ X f g
          hV.1 hV.2 hW.1 hW.2 hT.2) hE.2.1 (n + 1)
        (fun i ↦ E.X (a i)) (fun i ↦ E.f (a i)) (fun i ↦ hE.2.2.2 (a i))⟩
  · intro V hV R hR
    obtain ⟨E, hE, hfin, hqcqs, hle⟩ :=
      exists_finite_quasiCompact_quasiSeparated_refinement B S hS hZ X hV.1 R hR
    exact ⟨E, ⟨hE, hV, hfin, hqcqs⟩, hle⟩

/-- The identity of `X`, as an object of the site of algebraic spaces étale over `X`. -/
public def spacesTerminal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) : SpacesEtale B S hS X :=
  ⟨Over.mk (𝟙 X), by
    intro U φ hφ
    simpa using hφ⟩

/-- The identity of `X` is a terminal object of the site of algebraic spaces étale over `X`:
every object of that site carries a unique morphism to `X`. -/
private def spacesTerminal_isTerminal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    IsTerminal (spacesTerminal B S hS X) := by
  apply IsTerminal.ofUniqueHom
    (fun U ↦ ObjectProperty.homMk (Over.homMk U.obj.hom (by
      change U.obj.hom ≫ 𝟙 X = U.obj.hom
      exact Category.comp_id _)))
  intro U f
  apply spacesEtale_hom_ext
  have h : f.hom.left.hom ≫ 𝟙 X.obj = U.obj.hom.hom := congrArg (fun f ↦ f.hom) f.hom.w
  change f.hom.left.hom = U.obj.hom.hom
  exact (Category.comp_id _).symm.trans h

/-- Pushforward of sheaves along the inclusion of a dense subsite commutes with global
sections: composing it with the constant sheaf functor of the larger site gives the constant
sheaf functor of the subsite, so the two right adjoints agree. -/
private noncomputable local instance spacesGlobalSections_additive
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    (Sheaf.Γ (SpacesEtale.topology B S hS X) Ab.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Stacks 073E for global sections on the site of algebraic spaces étale over a quasi-compact
and quasi-separated `X`: global sections are sections over the terminal object `X ⟶ X`. -/
private lemma isIso_colimit_post_rightDerived_spacesGlobalSections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.obj)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (F : I ⥤ Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (SpacesEtale.topology B S hS X) Ab.{u + 1}).rightDerived p)) := by
  have := (spacesTerminal_isTerminal B S hS X).hasTerminal
  have := isIso_colimit_post_rightDerived_spacesSections B S hS hZ X
    (spacesTerminal B S hS X) hqc hqs p F
  exact Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _
    (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Sheaf.ΓNatIsoSheafSections (SpacesEtale.topology B S hS X)
        Ab.{u + 1} (spacesTerminal_isTerminal B S hS X)).symm p)

set_option maxHeartbeats 1000000 in
/-- Stacks 073E on the small étale site of schemes étale over `X`: that site is a dense
subsite of the site of algebraic spaces étale over `X` by Stacks 03G1, so the two categories of
abelian sheaves are equivalent compatibly with global sections. -/
private lemma isIso_colimit_post_rightDerived_smallGlobalSections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (F : I ⥤ Sheaf (SmallEtale.topology B S hS X) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (SmallEtale.topology B S hS X) Ab.{u + 1}).rightDerived p)) := by
  let Xalg : AlgebraicSpaces B S hS := ⟨X, hX⟩
  have : (comparisonFunctor B S hS Xalg).IsContinuous (SmallEtale.topology B S hS X)
      (SpacesEtale.topology B S hS Xalg) := comparisonFunctor_isContinuous B S hS Xalg
  have : (comparisonFunctor B S hS Xalg).IsDenseSubsite (SmallEtale.topology B S hS X)
      (SpacesEtale.topology B S hS Xalg) := comparisonFunctor_isDenseSubsite B S hS Xalg
  have : (Sheaf.Γ (SmallEtale.topology B S hS X) Ab.{u + 1}).Additive :=
    smallEtaleGamma_additive B S hS X
  open Stacks.Cohomology.ColimitsOfCohomology in
  exact isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite
    (SmallEtale.topology B S hS X) (SpacesEtale.topology B S hS Xalg)
    (comparisonFunctor B S hS Xalg) Ab.{u + 1} p F
    (isIso_colimit_post_rightDerived_spacesGlobalSections B S hS hZ Xalg hqc hqs p _)


/-- **Stacks 073E.** On a quasi-compact and quasi-separated algebraic space,
the canonical map from a filtered colimit of étale cohomology groups to the
étale cohomology of the filtered colimit is an isomorphism. -/
@[stacks 073E, sga "4 VII 3.3"]
theorem isIso_colimit_post_rightDerived_globalSections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (F : I ⥤ Sheaf (SmallEtale.topology B S hS X) (Ab.{u + 1})) :
    IsIso (colimit.post F
      ((Sheaf.Γ (SmallEtale.topology B S hS X)
        (Ab.{u + 1})).rightDerived p)) :=
  isIso_colimit_post_rightDerived_smallGlobalSections B S hS hZ X hX hqc hqs p F

/-! ### Higher direct images of a quasi-compact and quasi-separated morphism -/

open Stacks.Cohomology.HigherDirectImage Stacks.Topos.AbelianInverseImage
open Stacks.Topos.AbelianPushforward

/-- The direct image of abelian sheaves along a continuous functor is additive: it is
restriction along the functor, so it is additive on sections. -/
private noncomputable local instance sheafPushforwardContinuous_additive
    {C D : Type*} [Category* C] [Category* D] (v : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [v.IsContinuous J K] :
    (v.sheafPushforwardContinuous Ab.{w} J K).Additive where
  map_add := rfl

/-- The base change along a quasi-compact and quasi-separated `f : X ⟶ Y` of a quasi-compact
and quasi-separated object of the site of algebraic spaces étale over `Y` is again
quasi-compact and quasi-separated: quasi-compactness of the base change is the definition of
quasi-compactness of `f`, and quasi-separatedness of the projection is Stacks 03KL, whence
quasi-separatedness of its source by Stacks 04ZH, part (2). -/
private lemma spacesBaseChange_quasiCompact_quasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (W : SpacesEtale B S hS Y)
    (hWqc : IsQuasiCompactSpace B S hS W.obj.left.obj)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.obj.left.obj) :
    IsQuasiCompactSpace B S hS
        (((spacesBaseChange B S hS f).functor.obj W).obj.left.obj) ∧
      IsAbsolutelyQuasiSeparated B S hS hZ
        (((spacesBaseChange B S hS f).functor.obj W).obj.left.obj) := by
  have sq := (spacesBaseChange B S hS f).isPullback W
  refine ⟨isQuasiCompactSpace_of_iso B S hS
      (AlgebraicSpaces.isPullback_hom B S hS sq).isoPullback.symm
      (hqc W.obj.left.obj W.obj.left.property hWqc W.obj.hom.hom), ?_⟩
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    ((spacesBaseChange B S hS f).functor.obj W).obj.left.property hWqs
    ((isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback sq.flip hqs)

/-- **Stacks 07U6 on the sites of algebraic spaces étale over `X` and `Y`.** For a
quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, the degree-`p`
higher direct image along the base-change morphism of sites of Stacks 03G2, part (1), commutes
with filtered colimits of abelian sheaves.

This is Stacks 0H7B applied to that morphism of sites: every object of the site of algebraic
spaces étale over `Y` has a covering by affine schemes étale over `Y`, which are quasi-compact
and quasi-separated, their base changes along `f` are again quasi-compact and quasi-separated,
and over such a base change the comparison for cohomology is an isomorphism by Stacks 073E. -/
private lemma isIso_colimit_post_rightDerived_spacesPushforward
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (F : I ⥤ Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1}) :
    IsIso (colimit.post F
      (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous Ab.{u + 1}
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).rightDerived p)) := by
  apply isIso_colimit_post_rightDerived_sheafPushforwardContinuous
  intro V
  obtain ⟨E, hE, hqcqs⟩ := exists_quasiCompact_quasiSeparated_cover B S hS hZ Y V
  refine ⟨E, (SpacesEtale.precoverage B S hS Y).le_toPrecoverage_toGrothendieck _ ⟨E, rfl, hE⟩,
    fun i ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := spacesBaseChange_quasiCompact_quasiSeparated B S hS hZ f hqc hqs
    (E.X i) (hqcqs i).1 (hqcqs i).2
  exact isIso_colimit_post_rightDerived_spacesSections B S hS hZ X _ h₁ h₂ p F

/-! ### Transport to the small étale sites -/

section AbelianComparison

attribute [local instance 5000] CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory

attribute [local instance 5000]
  CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory

attribute [local instance 3000] instCartesianMonoidalCategorySheafType_stacksFrontier

attribute [local instance 3000] instBraidedCategorySheafType_stacksFrontier

/-- **Stacks 03G1 as a morphism of topoi.** The comparison equivalence between the spaces-étale
topos of an algebraic space and its small étale topos, packaged as a morphism of topoi whose
inverse image is the restriction functor along
`AlgebraicGeometry.Space.comparisonFunctor`. -/
noncomputable def comparisonToposMorphism (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) :
    MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS X.obj) (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) where
  pushforward := (smallEtaleToposEquiv B S hS X).inverse
  inverseImage := (smallEtaleToposEquiv B S hS X).functor
  adj := (smallEtaleToposEquiv B S hS X).toAdjunction
  preservesFiniteLimits := inferInstance

/-- The comparison equivalence of Stacks 03G1 on commutative group objects, read as an
equivalence of the two categories of abelian sheaves. It is only used to prove that the inverse
image of abelian sheaves along `AlgebraicGeometry.Space.comparisonToposMorphism` is an
equivalence, which is the form the transport below consumes. -/
private noncomputable def comparisonAbelianEquivalenceAux (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1} ≌
      Sheaf (SmallEtale.topology B S hS X.obj) Ab.{u + 1} :=
  let : (smallEtaleToposEquiv B S hS X).functor.Braided := .ofChosenFiniteProducts _
  let : (smallEtaleToposEquiv B S hS X).inverse.Braided := .ofChosenFiniteProducts _
  (Sites.AbelianSheaf.equivalence (SpacesEtale.topology B S hS X)).trans
    ((Equivalence.mapCommGrp (smallEtaleToposEquiv B S hS X)).trans
      (Sites.AbelianSheaf.equivalence (SmallEtale.topology B S hS X.obj)).symm)

/-- **Stacks 03G1 at abelian coefficients.** The inverse image of abelian sheaves along the
comparison morphism of topoi is an equivalence: it is, definitionally, the conjugate by the
identification of abelian sheaves with commutative group objects of the image under
`CategoryTheory.Equivalence.mapCommGrp` of the comparison equivalence of sheaves of sets. -/
instance isEquivalence_abelianInverseImage_comparisonToposMorphism (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS) :
    (Sites.abelianInverseImage (comparisonToposMorphism B S hS X)).IsEquivalence := by
  have h : (comparisonAbelianEquivalenceAux B S hS X).functor =
      Sites.abelianInverseImage (comparisonToposMorphism B S hS X) := rfl
  rw [← h]
  infer_instance

end AbelianComparison

/-- **Stacks 03G1 at abelian coefficients**, as an equivalence of categories whose forward
functor is the inverse image of abelian sheaves along
`AlgebraicGeometry.Space.comparisonToposMorphism`. -/
noncomputable def comparisonAbelianEquivalence (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1} ≌
      Sheaf (SmallEtale.topology B S hS X.obj) Ab.{u + 1} :=
  (Sites.abelianInverseImage (comparisonToposMorphism B S hS X)).asEquivalence

/-! The comparison lemma across equivalences is not restated here:
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_of_equivalences`
of `CategoryTheory/Sites/Cohomology/FilteredColimits/GlobalCohomologyOnALargeSite.lean`
is the same statement, public, and already imported by this file. -/

/-- The direct image of abelian sheaves along the base-change morphism of *topoi* agrees with
the direct image of abelian sheaves along the base-change morphism of *sites*: both are right
adjoint to the abelian inverse image, which is the abelian sheaf pullback by Stacks 04JC. -/
private noncomputable def abelianPushforwardSpacesIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    abelianPushforward (SpacesEtale.topology B S hS X)
        (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous Ab.{u + 1}
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) :=
  Adjunction.rightAdjointUniq
    (abelianInverseImageAdjPushforward (SpacesEtale.topology B S hS X)
      (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi)
    (((spacesBaseChange B S hS f).functor.sheafAdjunctionContinuous Ab.{u + 1}
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).ofNatIsoLeft
        (Stacks.Sites.AbelianPullback.sheafPullbackAbIsoAbelianInverseImage
          (spacesBaseChange_isMorphismOfSites B S hS f)))

/-- **Stacks 07U6.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces over `S`. For every degree `p` and every filtered diagram `F` of abelian
sheaves on the small étale site of `X`, the canonical map from the colimit of the degree-`p`
higher direct images to the degree-`p` higher direct image of the colimit is an isomorphism:
`R^p f_* (colim F_i) = colim R^p f_* F_i`.

The direct image is the direct image of abelian sheaves along the morphism of small étale topoi
of Stacks 03G2, part (3). It is transported, along the comparison equivalence of Stacks 03G1 at
abelian coefficients, to the direct image along the base-change morphism of *sites* of
Stacks 03G2, part (1), where the statement is
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_spacesPushforward`. -/
@[stacks 07U6, sga "4 VI 5.1" "étale alg. spaces"]
theorem isIso_colimit_post_rightDerived_smallEtaleAbelianPushforward
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u + 1}]
    (F : I ⥤ Sheaf (SmallEtale.topology B S hS X.obj) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((abelianPushforward (SmallEtale.topology B S hS X.obj)
        (smallToposMorphism B S hS f)).rightDerived p)) := by
  have : HasColimitsOfShape I (Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1}) :=
    inferInstance
  have : HasColimitsOfShape I (Sheaf (SpacesEtale.topology B S hS Y) Ab.{u + 1}) :=
    inferInstance
  have : HasColimitsOfShape I (Sheaf (SmallEtale.topology B S hS X.obj) Ab.{u + 1}) :=
    inferInstance
  have : HasColimitsOfShape I (Sheaf (SmallEtale.topology B S hS Y.obj) Ab.{u + 1}) :=
    inferInstance
  have : HasInjectiveResolutions (Sheaf (SpacesEtale.topology B S hS X) Ab.{u + 1}) :=
    inferInstance
  have : HasInjectiveResolutions (Sheaf (SmallEtale.topology B S hS X.obj) Ab.{u + 1}) :=
    inferInstance
  have hspaces := isIso_colimit_post_rightDerived_spacesPushforward B S hS hZ f hqc hqs p
    (F ⋙ (comparisonAbelianEquivalence B S hS X).symm.functor)
  have hF : IsIso (colimit.post (F ⋙ (comparisonAbelianEquivalence B S hS X).symm.functor)
      ((abelianPushforward (SpacesEtale.topology B S hS X)
        (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi).rightDerived p)) :=
    Stacks.Cohomology.isIso_colimit_post_of_natIso _ _ _
      (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
        (abelianPushforwardSpacesIso B S hS f).symm p)
  have α : (comparisonAbelianEquivalence B S hS X).functor ⋙
        abelianPushforward (SmallEtale.topology B S hS X.obj) (smallToposMorphism B S hS f) ≅
      abelianPushforward (SpacesEtale.topology B S hS X)
          (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi ⋙
        (comparisonAbelianEquivalence B S hS Y).functor :=
    StacksTag03LR.abelianBaseChangeIso (comparisonToposMorphism B S hS X)
      (smallToposMorphism B S hS f)
      (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi
      (comparisonToposMorphism B S hS Y) (smallToposMorphism_comparison B S hS f)
  exact Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_of_equivalences
    (comparisonAbelianEquivalence B S hS X) (comparisonAbelianEquivalence B S hS Y)
    (abelianPushforward (SpacesEtale.topology B S hS X)
      (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi)
    (abelianPushforward (SmallEtale.topology B S hS X.obj) (smallToposMorphism B S hS f))
    α p F hF

end AlgebraicGeometry.Space

end

/-! ### Public interface -/

public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-- On a small site, the universe lift of abelian groups preserves sheafification, and
postcomposition of sheaves with it preserves injective objects. These are the two hypotheses the
comparison of cohomology across coefficient universes needs; the proofs are the ones above. -/
public theorem sheafCompose_uliftFunctor_properties.{u, w} {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{w, u} ∧
      (sheafCompose J AddCommGrpCat.uliftFunctor.{w, u}).PreservesInjectiveObjects := by
  have : HasSheafify J Ab.{max u w} := largeAbSheafify J
  have : AddCommGrpCat.uliftFunctor.{w, u}.PreservesInjectiveObjects :=
    ab_ulift_preservesInjectiveObjects
  exact ⟨ulift_preservesSheafification J, sheafCompose_preservesInjectiveObjects J _⟩

/-- Postcomposition of abelian sheaves with the universe lift preserves finite limits. -/
public theorem sheafCompose_uliftFunctor_preservesFiniteLimits.{u, w, u₀, v₀}
    {C : Type u₀} [Category.{v₀} C]
    (J : GrothendieckTopology C) [HasSheafify J Ab.{u}] [HasSheafify J Ab.{max u w}] :
    PreservesFiniteLimits (sheafCompose J AddCommGrpCat.uliftFunctor.{w, u}) :=
  ⟨fun _ _ _ => sheafCompose_preservesLimitsOfShape J _⟩

/-- Postcomposition of abelian sheaves with the universe lift preserves finite colimits, as soon
as the universe lift is compatible with sheafification. -/
public theorem sheafCompose_uliftFunctor_preservesFiniteColimits.{u, w, u₀, v₀}
    {C : Type u₀} [Category.{v₀} C]
    (J : GrothendieckTopology C) [HasSheafify J Ab.{u}] [HasSheafify J Ab.{max u w}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{w, u}] :
    PreservesFiniteColimits (sheafCompose J AddCommGrpCat.uliftFunctor.{w, u}) :=
  ⟨fun _ _ _ => sheafCompose_preservesColimitsOfShape J _⟩

end AlgebraicGeometry.Space

end
