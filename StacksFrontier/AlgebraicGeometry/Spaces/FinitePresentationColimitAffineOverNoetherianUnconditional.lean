module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationColimitAffineOverNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Stacks 07UW without carried inputs

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` with `Y` Noetherian.
**Stacks 07UW** asserts that every quasi-coherent `𝒪_X`-module is a filtered colimit of
`𝒪_X`-modules of finite presentation.

`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationColimitAffineOverNoetherian` carries the
source's proof from five general inputs.  This file proves each of them and assembles the tag
under exactly the source's hypotheses.

* The Noetherian case (Stacks 07UV with Stacks 07UB): on a Noetherian algebraic space a
  quasi-coherent module is the filtered colimit of its coherent submodules
  (`AlgebraicGeometry.Space.isFiltered_and_nonempty_isColimit_coherentSubobjectCocone`), a
  coherent module is of finite presentation
  (`AlgebraicGeometry.Space.isCoherent_iff_isFinitePresentationOnSite` and
  `SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'`), and the poset of
  coherent submodules is essentially small, because the modules on the small étale site form a
  Grothendieck abelian category, which is well-powered.  This is
  `AlgebraicGeometry.Space.exists_isFiltered_isColimit_isFinitePresentation_of_isNoetherian`.
* The direct image along an affine morphism preserves quasi-coherence: Stacks 07U8,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom`.
* The pullback preserves quasi-coherence (Stacks 03GA,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`) and
  finite presentation (Stacks 03DO (7),
  `AlgebraicGeometry.Space.isFinitePresentation_modulePullback`).
* Step 3 of the source's proof, the surjectivity of the counit `f^*f_*F ⟶ F` for an affine `f`
  and a quasi-coherent `F`:
  `AlgebraicGeometry.Space.epi_modulePullbackAdjunction_counit_app_of_isAffineHom`.
* A space affine over a quasi-compact quasi-separated space is quasi-compact and
  quasi-separated:
  `AlgebraicGeometry.Space.isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom`.

## Step 3 of the proof

The source checks the surjectivity of `f^*f_*F ⟶ F` étale locally, reducing to an affine
morphism of schemes.  Here it is read off Stacks 08AI instead.  The direct image
`f_* = Mod(𝒪_X) ⥤ Mod(𝒪_Y)` is the direct image over `𝒜 = f_*𝒪_X` followed by restriction of
scalars along `𝒪_Y ⟶ 𝒜`, which is faithful; and the direct image over `𝒜` has a left adjoint
whose counit is invertible at quasi-coherent modules when `f` is affine
(`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_of_isAffineHom`).
For an adjunction `L ⊣ I ⋙ G` with `G` faithful and `I` having a left adjoint whose counit is
invertible at `M`, the counit at `M` is an epimorphism
(`CategoryTheory.Adjunction.epi_counit_app_of_faithful_of_isIso_counit_app`).

## References

* [Stacks Project, Tag 07UW](https://stacks.math.columbia.edu/tag/07UW)
* [Stacks Project, Tag 07UV](https://stacks.math.columbia.edu/tag/07UV)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Let `L ⊣ I ⋙ G` be an adjunction whose right adjoint is a composite with a faithful functor
`G`, and let `H ⊣ I` be an adjunction whose counit is invertible at `M`.  Then the counit of
`L ⊣ I ⋙ G` at `M` is an epimorphism.

Two maps out of `M` which agree after the counit have the same image under `I ⋙ G`, hence under
`I` because `G` is faithful, hence agree after the counit of `H ⊣ I`, which is invertible. -/
theorem epi_counit_app_of_faithful_of_isIso_counit_app {L : C ⥤ D} {I : D ⥤ E} {G : E ⥤ C}
    {H : E ⥤ D} [G.Faithful] (adj : L ⊣ I ⋙ G) (adj' : H ⊣ I) (M : D)
    [IsIso (adj'.counit.app M)] : Epi (adj.counit.app M) where
  left_cancellation {Z} g h hgh := by
    have key : ∀ k : M ⟶ Z, adj.homEquiv _ _ (adj.counit.app M ≫ k) = (I ⋙ G).map k := by
      intro k
      rw [adj.homEquiv_naturality_right, Adjunction.homEquiv_unit,
        adj.right_triangle_components, Category.id_comp]
    have h1 : (I ⋙ G).map g = (I ⋙ G).map h := by
      rw [← key g, ← key h, hgh]
    have e : ∀ k : M ⟶ Z, adj'.counit.app M ≫ k = H.map (I.map k) ≫ adj'.counit.app Z :=
      fun k => (adj'.counit_naturality k).symm
    rw [← cancel_epi (adj'.counit.app M), e g, e h, G.map_injective h1]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Step 3 of the proof of Stacks 07UW.**  Let `f : X ⟶ Y` be an affine morphism of algebraic
spaces and `F` a quasi-coherent `𝒪_X`-module.  Then the counit `f^*f_*F ⟶ F` of the adjunction
of Stacks 03LU is an epimorphism of `𝒪_X`-modules.

The direct image `f_*` is the direct image over `f_*𝒪_X` followed by the faithful restriction of
scalars along `𝒪_Y ⟶ f_*𝒪_X`, and the counit of the adjunction of Stacks 03D4 for the direct
image over `f_*𝒪_X` is invertible at quasi-coherent modules (Stacks 08AI). -/
theorem epi_modulePullbackAdjunction_counit_app_of_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    Epi ((modulePullbackAdjunction B S hS f).counit.app F) := by
  have := isIso_directImageAlgebraPullbackAdjunction_counit_app_of_isAffineHom B S hS f hf F hF
  exact Adjunction.epi_counit_app_of_faithful_of_isIso_counit_app
    (G := SheafOfModules.restrictScalars (structureSharp B S hS f))
    (modulePullbackAdjunction B S hS f) (directImageAlgebraPullbackAdjunction B S hS f) F

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- An algebraic space affine over a quasi-compact and quasi-separated algebraic space is
quasi-compact and quasi-separated: an affine morphism is quasi-compact and separated, hence
quasi-separated, and both properties pass from the target to the source. -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) :
    IsQuasiCompactSpace B S hS X.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ X.1 :=
  ⟨isQuasiCompactSpace_of_isQuasiCompact B S hS Y.2 hYqc f.hom
      (isQuasiCompact_of_isAffineHom' B S hS f.hom X.2 Y.2 hf),
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2 hYqs
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isAffineHom B S hS f.hom X.2 Y.2 hf))⟩

section Noetherian

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against `Modules.{u, u}`; the abelian structure used here is the
one at the pinned universes, as in the proof of Stacks 07UV. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **The Noetherian case of Stacks 07UW**, Stacks 07UV with Stacks 07UB: on a Noetherian
algebraic space every quasi-coherent module is a filtered colimit of modules of finite
presentation, indexed by a small category.

The diagram is that of the coherent submodules (Stacks 07UV), each of which is of finite
presentation (Stacks 07UB, (1) ⟹ (3)); it is reindexed along a small model of the poset of
coherent submodules, which is essentially small because the modules on the small étale site form
a well-powered Grothendieck abelian category. -/
theorem exists_isFiltered_isColimit_isFinitePresentation_of_isNoetherian
    (Z : AlgebraicSpaces B S hS) (hZN : IsNoetherian B S hS hZ Z.1)
    (N : Modules.{u, u} B S hS Z.1 Z.2) (hN : N.IsQuasicoherentOnSite) :
    ∃ (I : Type u) (inst : SmallCategory I),
      let _ := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS Z.1 Z.2)
        (φ : D ⟶ (Functor.const I).obj N),
        (∀ i, (D.obj i).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk N φ)) := by
  have := hN
  have : Fact (HasEtaleLocalProperty B S hS Z.1
      (fun V : Scheme.{u} => AlgebraicGeometry.IsLocallyNoetherian V)) := ⟨hZN.2.2⟩
  obtain ⟨hfil, ⟨hcol⟩⟩ := isFiltered_and_nonempty_isColimit_coherentSubobjectCocone hZ hZN N
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS Z.1 Z.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS Z.1)
    infer_instance
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Z.1 Z.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have : Small.{u} (CoherentSubobject B S hS Z.1 Z.2 N) :=
    small_of_injective (f := fun G : CoherentSubobject B S hS Z.1 Z.2 N => G.obj)
      fun G G' h => by ext1; exact h
  let e := equivSmallModel.{u} (CoherentSubobject B S hS Z.1 Z.2 N)
  have : IsFiltered (SmallModel.{u} (CoherentSubobject B S hS Z.1 Z.2 N)) :=
    IsFiltered.of_equivalence e
  refine ⟨SmallModel.{u} (CoherentSubobject B S hS Z.1 Z.2 N), inferInstance, inferInstance,
    e.inverse ⋙ coherentSubobjectFunctor B S hS Z.1 Z.2 N,
    ((coherentSubobjectCocone B S hS Z.1 Z.2 N).whisker e.inverse).ι, fun i => ?_,
    ⟨hcol.whiskerEquivalence e.symm⟩⟩
  have hcoh : IsCoherent B S hS Z.1 Z.2
      ((coherentSubobjectFunctor B S hS Z.1 Z.2 N).obj (e.inverse.obj i)) :=
    (e.inverse.obj i).property
  exact SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
    ((isCoherent_iff_isFinitePresentationOnSite B S hS Z.1 Z.2 _).1 hcoh)

end Noetherian

/-- **Stacks 07UW.**  Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme
`S` with `Y` Noetherian.  Then every quasi-coherent `𝒪_X`-module is a filtered colimit of
`𝒪_X`-modules of finite presentation.

This is `AlgebraicGeometry.Space.isFilteredColimit_isFinitePresentation_of_isAffineHom` with its
five inputs proved: the Noetherian case
(`AlgebraicGeometry.Space.exists_isFiltered_isColimit_isFinitePresentation_of_isNoetherian`),
Stacks 07U8 for the direct image, Stacks 03GA and 03DO (7) for the pullback, the surjectivity of
the counit (`AlgebraicGeometry.Space.epi_modulePullbackAdjunction_counit_app_of_isAffineHom`) and
the quasi-compactness and quasi-separatedness of `X`
(`AlgebraicGeometry.Space.isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom`).

The index category is the category of triples `(i, j, α)` that the source's proof constructs,
whose objects carry a morphism of `𝒪_X`-modules, and so lives in `Type (u + 1)` with Hom-types in
`Type u`. -/
@[stacks 07UW "every quasi-coherent 𝒪_X-module is a filtered colimit of finitely presented \
𝒪_X-modules, for f : X ⟶ Y affine with Y Noetherian"]
theorem exists_isFiltered_isColimit_isFinitePresentation_of_isAffineHom_of_isNoetherian
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hY : IsNoetherian B S hS hZ Y.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ∃ (K : Type (u + 1)) (inst : Category.{u} K),
      let _ := inst
      ∃ (_ : IsFiltered K) (D : K ⥤ Modules.{u, u} B S hS X.1 X.2)
        (φ : D ⟶ (Functor.const K).obj F),
        (∀ k, (D.obj k).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk F φ)) :=
  isFilteredColimit_isFinitePresentation_of_isAffineHom B S hS hZ
    (exists_isFiltered_isColimit_isFinitePresentation_of_isNoetherian B S hS hZ)
    (fun _ _ g hg N hN => isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS g hg N hN)
    (fun _ _ g N => ⟨isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g N,
      isFinitePresentation_modulePullback g N⟩)
    (fun _ _ g hg N hN => epi_modulePullbackAdjunction_counit_app_of_isAffineHom B S hS g hg N hN)
    (fun _ _ g hg hW => isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom
      B S hS hZ g hg hW.1 hW.2.1)
    f hf hY F hF

end AlgebraicGeometry.Space

end
