module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentColimitFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismQuasiSeparatedAbs
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact

/-!
# Quasi-coherent modules on a Noetherian algebraic stack are filtered colimits of coherent ones

**Stacks 0GRF**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`):
*Let `𝒳` be a Noetherian algebraic stack. Every quasi-coherent `𝒪_𝒳`-module is the filtered
colimit of its coherent submodules.*  This file restates it in the two forms used downstream: a
colimit presentation over a small filtered category with monomorphic colimit maps and coherent
terms, and `ObjectProperty.ind.{u}` of `AlgebraicGeometry.Stack.coherentQuasicoherent`.  Both come
from the coherent submodules of `AlgebraicGeometry.Stack.AlgebraicStacks.CoherentSubobject`, which
form a small set (a coherent submodule is determined by its sections over a Noetherian chart).

The source proves Stacks 0GRF on a groupoid presentation: choose a surjective smooth morphism
`U → 𝒳` from an affine scheme (Stacks 04YC) and let `(U, R, s, t, c)` be its groupoid,
`R = U ×_𝒳 U` (Stacks 04T4, 04T5); Stacks 0GRC identifies `QCoh(𝒪_𝒳)` with `QCoh(U, R, s, t, c)`
and the coherent modules on both sides, and Stacks 0GPS applies once its assumptions are checked.
This file also checks these assumptions (the last paragraph of the source's proof):

* `U` is Noetherian: affine, and locally Noetherian because `𝒳` is (Stacks 04YF);
* `s`, `t` are flat (indeed smooth, Stacks 04T5, 04WY);
* `s` is quasi-compact and quasi-separated: the base changes of `U → 𝒳`, which is quasi-compact
  (Stacks 075S part (1), read through Stacks 050T) and quasi-separated (Stacks 050N, 04YT) because
  `𝒳` is quasi-separated;
* `R` is Noetherian: quasi-compact and quasi-separated over the affine `U`, and locally of finite
  type over the locally Noetherian `U`.

## Main results

* `AlgebraicGeometry.Stack.exists_flatPresentation_isNoetherian`: a Noetherian algebraic stack has
  a flat presentation whose groupoid satisfies the assumptions of Stacks 0GPS.
* `AlgebraicGeometry.Stack.AlgebraicStacks.small_coherentSubobject`: the coherent submodules of a
  quasi-coherent module on a Noetherian algebraic stack form a small set.
* `AlgebraicGeometry.Stack.exists_colimitPresentation_mono_coherentQuasicoherent`: Stacks 0GRF as
  a colimit presentation of every quasi-coherent `𝒪_𝒳`-module `M`, indexed by a small filtered
  category, whose colimit maps are monomorphisms (a filtered system of submodules of `M`), whose
  terms are coherent, and which is cofinal among the coherent submodules of `M`.
* `AlgebraicGeometry.Stack.ind_coherentQuasicoherent`: Stacks 0GRF in the form
  `ObjectProperty.ind.{u}` of `AlgebraicGeometry.Stack.coherentQuasicoherent`, the hypothesis
  `hgen` of the extension theorem of Stacks 0GRJ.

## References

* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
* [Stacks Project, Tag 0GRC](https://stacks.math.columbia.edu/tag/0GRC)
* [Stacks Project, Tag 0GPS](https://stacks.math.columbia.edu/tag/0GPS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.Stack

namespace SelfIntersection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {F : 𝒰 ⟶ 𝒳}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 F.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- **The source projection of the groupoid of a presentation has every relative property of the
presentation** (Stacks 04XC read at the leg exchange of the canonical 2-fibre product square),
for any property `P` of morphisms of algebraic spaces stable under base change and fppf local on
the target. -/
theorem prop_selfIntersectionPresentation_source
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    P (selfIntersectionPresentation eU eR h𝒳).groupoid.source :=
  (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS P F hF).mp
    hP 𝒰 ⟨U.obj, U.property, ⟨eU⟩⟩ F
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} F F))
    R.obj U.obj R.property U.property eR eU

end SelfIntersection

open SelfIntersection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The site contains the terminal scheme**: it is isomorphic to `Spec(ULift ℤ)`, which lies in
every big fppf site (`AlgebraicGeometry.Stack.contains_specULiftZ`). -/
alias contains_terminal := BigFppfSite.contains_terminal

/-- **A Noetherian algebraic stack has a flat presentation whose groupoid satisfies the
assumptions of Stacks 0GPS** (the last paragraph of the proof of Stacks 0GRF).  There is an
algebraic space `U` (indeed an affine scheme) and a surjective, flat 1-morphism `f : U → 𝒳`,
locally of finite presentation, whose groupoid `(U, R, s, t, c)` has `U` and `R` Noetherian, `s`
flat, quasi-compact and quasi-separated, and `t` flat. -/
theorem exists_flatPresentation_isNoetherian (h𝒳 : IsNoetherianStack.{u, w, w} B S hS 𝒳) :
    ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
      (f : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳)
      (_hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
      (_hflat : AlgebraicStacks.IsFlat B S hS f) (_ : IsSurjective B S hS f),
      Space.IsNoetherian B S hS (contains_terminal B)
          (flatPresentationGroupoid B S hS 𝒳 F hF f).objects.1 ∧
        Space.IsNoetherian B S hS (contains_terminal B)
          (flatPresentationGroupoid B S hS 𝒳 F hF f).arrows.1 ∧
        Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom ∧
        Space.IsQuasiCompact B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom ∧
        Space.IsQuasiSeparated B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom ∧
        Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).target.hom := by
  classical
  have hZ := contains_terminal B
  -- an affine scheme `U` with a surjective smooth 1-morphism to `𝒳` (Stacks 04YC)
  obtain ⟨U, hU, g, hgSurj, hgSmooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 h𝒳.1
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  let F := yoneda.obj U
  have hF : IsAlgebraicSpace B S hS F := isAlgebraicSpace_yoneda B S hS U
  -- read as a 1-morphism from the algebraic space `U`
  let e := schemeFibredCategoryEquivalence B S hS U
  let f : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp e.inverse g.hom.hom))
  let _ : Functor.IsEquivalence e.inverse.toFunctor := e.equiv.isEquivalence_inverse
  let _ : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  have hsurj : IsSurjective B S hS f := by
    intro x
    obtain ⟨y, hy⟩ := hgSurj x
    obtain ⟨z, hz⟩ := pointsMap_surjective_of_basedEquivalence B S hS
      (𝒜 := fibredCategory B S hS F) (𝒞 := schemeFibredCategory B S hS U) e.symm y
    refine ⟨z, ?_⟩
    change pointsMap B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property
      𝒳.val.property (BasedFunctor.comp e.inverse g.hom.hom) z = x
    rw [← pointsMap_comp B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property
      (schemeFibredCategory B S hS U).property 𝒳.val.property e.inverse g.hom.hom z]
    rw [show pointsMap B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property
        (schemeFibredCategory B S hS U).property e.inverse z = y from hz]
    exact hy
  have hrelSmooth : IsRelativelySmooth B S hS f.hom :=
    isRelativelySmooth_of_equivalences B S hS
      (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp e.inverse g.hom.hom) :
        fibredCategory B S hS F ⟶ 𝒳.val)
      g.hom e.inverse (BasedFunctor.id 𝒳.val.val) (Iso.refl _) hgSmooth
  have hsmooth : AlgebraicStacks.IsSmooth B S hS f :=
    hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) f.hom F hF
      (StacksRepresentableCFG.EquivalenceOver.refl _) hrelSmooth (Space.isSmooth_id B S hS hF)
  have hflat : AlgebraicStacks.IsFlat B S hS f :=
    AlgebraicStacks.isFlat_of_isSmooth B S hS f hsmooth
  have hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f :=
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hsmooth
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom := hrelSmooth.1
  -- `U` is Noetherian
  have hUaff : Space.IsAffineSpace B S hS F := ⟨U, hU, ⟨Iso.refl _⟩⟩
  have hFqc : Space.IsQuasiCompactSpace B S hS F := hUaff.isQuasiCompactSpace
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hFnoeth : Space.HasEtaleLocalProperty B S hS F
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    (exists_space_atlas_iff_forall_space.{u, w} B S hS _ 𝒳).1
      ((exists_scheme_atlas_iff_exists_space_atlas.{u, w} B S hS _ 𝒳).1 h𝒳.2.2) F hF f hsmooth
  have hUnoeth : Space.IsNoetherian B S hS hZ F :=
    ⟨hFqc, Space.IsAffineSpace.isAbsolutelyQuasiSeparated B S hS hZ hUaff, hFnoeth⟩
  -- `s` and `t` are flat and smooth (Stacks 04WY, 04T5)
  let flatP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsFlat B S hS h
  let : (spaceProperty B S hS flatP).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u + 1} B S hS) :=
    Space.isFlat_isLocalAtTarget_fpqc B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hrelFlat := hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS flatP
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f.hom hrep hflat
  have hsflat : Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom :=
    isFlat_selfIntersectionPresentation_source _ _ hrep hrelFlat 𝒳.property
  have htflat : Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).target.hom :=
    isFlat_selfIntersectionPresentation_target _ _ hrep hrelFlat 𝒳.property
  have hssmooth : Space.IsSmooth B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom :=
    isSmooth_selfIntersectionPresentation_source _ _ hrep hrelSmooth.2 𝒳.property
  -- `s` is quasi-compact: `f` is (Stacks 075S part (1), Stacks 050T)
  have hqcm : IsQuasiCompactMorphism.{u, w} B S hS f :=
    isQuasiCompactMorphism_of_isQuasiCompactStack_of_isQuasiSeparatedAbs.{u, w} B S hS f
      (isQuasiCompactStack_fibredCategory B S hS F hF hFqc _) h𝒳.2.1
  have hrelqc : IsQuasiCompact B S hS f.hom :=
    (isQuasiCompact_iff_baseChange_quasiCompact B S hS f hrep).2 hqcm
  have : (Space.quasiCompactProperty B S hS).IsStableUnderBaseChange :=
    ⟨fun sq hg => Space.isQuasiCompact_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS sq) hg⟩
  have hsqc : Space.IsQuasiCompact B S hS
      (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom :=
    prop_selfIntersectionPresentation_source _ _ (Space.quasiCompactProperty B S hS) hrep hrelqc
      𝒳.property
  -- `s` is quasi-separated: `f` is (Stacks 050N, 04YT)
  have h𝒳over : IsQuasiSeparatedOver.{u, w} B S hS 𝒳 :=
    AlgebraicStacks.isQuasiSeparatedOver_of_isQuasiSeparatedOver_changeBase B S _ hS
      (contains_specULiftZ B) (toIntObject B S hS) 𝒳 h𝒳.2.1
  have hgqs : AlgebraicStacks.IsQuasiSeparated B S hS g :=
    AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver B S hS g
      (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS U hU) h𝒳over.2
  have hfqs : AlgebraicStacks.IsQuasiSeparated B S hS f :=
    AlgebraicStacks.isQuasiSeparated_of_equivalence B S hS g f e.inverse (Iso.refl _)
      inferInstance hgqs
  have hrelqs : IsQuasiSeparated B S hS f.hom :=
    (isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS f hrep).1
      ((AlgebraicStacks.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S hS f hrep).1
        hfqs)
  have hsqs : Space.IsQuasiSeparated B S hS
      (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom :=
    prop_selfIntersectionPresentation_source _ _ (Space.quasiSeparatedProperty B S hS) hrep
      hrelqs 𝒳.property
  -- `R` is Noetherian
  have hRnoeth : Space.IsNoetherian B S hS hZ
      (flatPresentationGroupoid B S hS 𝒳 F hF f).arrows.1 :=
    ⟨Space.isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS _ hUaff hsqc,
      Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ _
        (flatPresentationGroupoid B S hS 𝒳 F hF f).arrows.2 hUaff hsqs,
      Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
        (flatPresentationGroupoid B S hS 𝒳 F hF f).arrows.2 hF _
        (Space.isLocallyOfFiniteType_of_isSmooth B S hS hssmooth) hFnoeth⟩
  exact ⟨F, hF, f, hlfp, hflat, hsurj, hUnoeth, hRnoeth, hsflat, hsqc, hsqs, htflat⟩

/-- **Noetherianity does not depend on the descent universe of the view over `Spec(ℤ)`.**  The
universe `w'` at which `AlgebraicGeometry.Stack.IsNoetherianStack` views `𝒳` over `Spec(ULift ℤ)`
to read its quasi-separatedness only enters through the stack condition of the view, which no
part of the definition of quasi-separatedness uses. -/
theorem isNoetherianStack_univ (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳) :
    IsNoetherianStack.{u, w, w} B S hS 𝒳 :=
  h𝒳

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicStacks

variable {B S hS 𝒳}

/-- **The coherent submodules of a quasi-coherent module on a Noetherian algebraic stack form a
small set**: a subobject is determined by the image of its sections over the Noetherian chart of
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_noetherian_chart`. -/
theorem small_coherentSubobject (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (F : quasicoherentModules B S hS 𝒳) : Small.{u} (CoherentSubobject B S hS 𝒳 F) := by
  obtain ⟨U, a, hsm, hsurj, hu, hN⟩ := exists_noetherian_chart h𝒳
  let x := chartObject a
  let T : CoherentSubobject B S hS 𝒳 F → Set (F.obj.val.obj (Opposite.op x)) :=
    fun P => Set.range (P.1.arrow.hom.val.app (Opposite.op x))
  have hle : ∀ {P Q : CoherentSubobject B S hS 𝒳 F}, T P = T Q → P.1 ≤ Q.1 := by
    intro P Q h
    refine le_of_forall_exists_eq hsm hsurj hu fun y => ?_
    have : P.1.arrow.hom.val.app (Opposite.op x) y ∈ T Q := by
      rw [← h]
      exact ⟨y, rfl⟩
    exact this
  exact small_of_injective fun P Q h => Subtype.ext (le_antisymm (hle h) (hle h.symm))

/-- The coherent submodules of a quasi-coherent module on a Noetherian algebraic stack form an
essentially small category. -/
private theorem essentiallySmall_coherentSubobject (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (F : quasicoherentModules B S hS 𝒳) : EssentiallySmall.{u} (CoherentSubobject B S hS 𝒳 F) :=
  have := small_coherentSubobject h𝒳 F
  essentiallySmall_of_small_of_locallySmall _

end AlgebraicStacks

open AlgebraicStacks

/-- **Stacks 0GRF as a colimit presentation over a small filtered category**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`).
For a quasi-coherent `𝒪_𝒳`-module `M` on a Noetherian algebraic stack there is a small filtered
category `I` and a colimit presentation `M = colim_{i ∈ I} M_i` in `QCoh(𝒪_𝒳)` such that

* every colimit map `M_i ⟶ M` is a monomorphism, i.e. the `M_i` are submodules of `M`;
* every `M_i` is coherent;
* the system is cofinal among all coherent submodules of `M`: every coherent `N` with a
  monomorphism `N ⟶ M` factors through some `M_i ⟶ M`.

The `M_i` are the coherent submodules of `M`, indexed by a small model of
`AlgebraicGeometry.Stack.AlgebraicStacks.CoherentSubobject M`; a map `N ⟶ M` out of a coherent
module factors through its image, which is a coherent submodule. -/
theorem exists_colimitPresentation_mono_coherentQuasicoherent
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (pres : ColimitPresentation I M),
      (∀ i, Mono (pres.ι.app i)) ∧ (∀ i, coherentQuasicoherent B S hS 𝒳 (pres.diag.obj i)) ∧
        ∀ (N : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids) (j : N ⟶ M), Mono j →
          coherentQuasicoherent B S hS 𝒳 N →
            ∃ (i : I) (k : N ⟶ pres.diag.obj i), k ≫ pres.ι.app i = j := by
  obtain ⟨_, ⟨hc⟩⟩ := isFiltered_coherentSubobject_and_isColimit h𝒳 M
  have := essentiallySmall_coherentSubobject h𝒳 M
  let e := equivSmallModel.{u} (CoherentSubobject B S hS 𝒳 M)
  have : IsFiltered (SmallModel.{u} (CoherentSubobject B S hS 𝒳 M)) := IsFiltered.of_equivalence e
  obtain ⟨U, a, hsm, hsurj, hu, hN⟩ := exists_noetherian_chart h𝒳
  refine ⟨SmallModel.{u} (CoherentSubobject B S hS 𝒳 M), inferInstance, inferInstance,
    ⟨e.inverse ⋙ coherentSubobjectDiagram B S hS 𝒳 M,
      ((coherentSubobjectCocone B S hS 𝒳 M).whisker e.inverse).ι, hc.whiskerEquivalence e.symm⟩,
    fun i => inferInstanceAs (Mono (e.inverse.obj i).1.arrow), fun i => (e.inverse.obj i).2,
    fun N j _ hNc => ?_⟩
  let Q : CoherentSubobject B S hS 𝒳 M :=
    ⟨imageSubobject j, isCoherent_imageSubobject hsm hsurj hu h𝒳.2.2 j hNc⟩
  have hQ : Q.1 ≤ (e.inverse.obj (e.functor.obj Q)).1 := leOfHom (e.unitIso.hom.app Q)
  exact ⟨e.functor.obj Q, factorThruImageSubobject j ≫ Subobject.ofLE _ _ hQ,
    (Category.assoc _ _ _).trans ((congrArg (factorThruImageSubobject j ≫ ·)
      (Subobject.ofLE_arrow hQ)).trans (imageSubobject_arrow_comp j))⟩

/-- **Stacks 0GRF in the form `ObjectProperty.ind.{u}`**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`):
on a Noetherian algebraic stack every quasi-coherent module is a filtered colimit, over an
essentially small filtered category, of coherent modules (its coherent submodules).  This is the
hypothesis `hgen` of `AlgebraicGeometry.Stack.existsUnique_tensorExtension_of_coherentGeneration`
(Stacks 0GRJ). -/
theorem ind_coherentQuasicoherent (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    (coherentQuasicoherent B S hS 𝒳).ind.{u} M := by
  obtain ⟨_, ⟨hc⟩⟩ := isFiltered_coherentSubobject_and_isColimit h𝒳 M
  have := essentiallySmall_coherentSubobject h𝒳 M
  exact ObjectProperty.of_essentiallySmall_index
    ⟨coherentSubobjectDiagram B S hS 𝒳 M, (coherentSubobjectCocone B S hS 𝒳 M).ι, hc⟩
    fun P => P.2

end AlgebraicGeometry.Stack

end
