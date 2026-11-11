module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionCollections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# Characterizing affine algebraic spaces (Stacks 07VS, 07VT)

A surjective morphism of algebraic spaces with affine source has affine target as soon as it
is finite (Stacks 07VS) or, more generally, universally closed (Stacks 07VT). Both follow the
route of the source: the target is separated by Stacks 05Z2 and quasi-compact by Stacks 040W,
the morphism is presented as a directed limit of finite morphisms of finite presentation, and
one late stage of that limit is still affine and surjective onto the target.

## Main definitions

* `AlgebraicGeometry.Space.IntegralFiniteSystem` is a presentation of a morphism of algebraic
  spaces as a directed inverse limit of finite morphisms of finite presentation over its
  target.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite`: the target of a finite
  surjection with affine source is affine, under the hypotheses described below; Stacks 07VS
  itself is `AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection`.
* `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`: the target of a
  surjective universally closed morphism with affine source is affine, under the hypotheses
  described below; Stacks 07VT itself is
  `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`.

## Implementation notes

Both results reduce, by the argument carried out here, to the case of a morphism which is
finite *and of finite presentation*, and that case is an explicit hypothesis of both: it is
the content of the third paragraph of the proof of Stacks 07VS, which runs through Stacks 07SU,
Stacks 07SK, Stacks 084Z, Stacks 07SN and Stacks 07VP. Two further explicit hypotheses supply
the inverse system and the affine stage, namely the conclusions of Stacks 07VR for Stacks 07VS
and of Stacks 09YA for Stacks 07VT, and the conclusion of Stacks 07SQ for both.

No carried hypothesis is the universally quantified form of the conclusion it serves. Stacks
07SQ, Stacks 07VR and Stacks 09YA conclude about inverse systems, not about affineness of a
target. The finite-presentation case is a strict special case of both results: a finite
morphism need not be of finite presentation — the closed immersion cut out by a non-finitely
generated ideal is finite and not of finite presentation — and a universally closed morphism
need not be finite, an integral morphism which is not locally of finite type being universally
closed by Stacks 0415 and not finite by Stacks 0414.

The data of Stacks 07VR and Stacks 09YA is bundled as
`AlgebraicGeometry.Space.IntegralFiniteSystem` rather than written out as an iterated
existential, because every field of it is used: the system supplies the
`AlgebraicGeometry.Space.DescentSituation` that Stacks 07SQ consumes, while the affineness of
its transition morphisms, the quasi-compactness and the quasi-separatedness of its stages are
*not* fields of the presentation and are derived here, from Stacks 081Z, Stacks 06G5 and
Stacks 03DY respectively.

Containment of the terminal scheme in the site, against which the absolute separation
properties of Stacks 03BS are read, is never a hypothesis: `Spec ℤ` has size `ℵ₀` and the
cutoff of a big fppf site is uncountable, which is
`AlgebraicGeometry.BigFppfSite.contains_terminal`.

## References

* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 081Z](https://stacks.math.columbia.edu/tag/081Z)
* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presentation of a morphism `f : X ⟶ Y` of algebraic spaces over `S` as a directed
inverse limit of finite morphisms of finite presentation over `Y`: a directed system of
algebraic spaces over `Y`, each finite and of finite presentation over it, whose limit is `X`
compatibly with `f`.

This is the shape of the conclusion of Stacks 07VR for a finite morphism and of Stacks 09YA
for an integral one. -/
structure IntegralFiniteSystem {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) where
  /-- The directed index preorder, in the universe of the values of the site's presheaves. -/
  indexType : Type u
  [indexPreorder : Preorder indexType]
  [indexNonempty : Nonempty indexType]
  [indexDirected : IsDirected indexType (· ≤ ·)]
  /-- The inverse system of algebraic spaces over `S`. -/
  diagram : indexTypeᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- The compatible family of morphisms from the stages to the target. -/
  structureMap : diagram ⟶ (Functor.const indexTypeᵒᵖ).obj Y
  /-- The compatible family of morphisms from the source to the stages. -/
  limitCone : (Functor.const indexTypeᵒᵖ).obj X ⟶ diagram
  /-- Every stage recovers `f` from the two families. -/
  compatible : ∀ i, f = limitCone.app i ≫ structureMap.app i
  /-- The source is the limit of the system. -/
  isLimit : IsLimit (Cone.mk X limitCone)
  /-- Every stage is an algebraic space over `S`. -/
  stageAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (diagram.obj i)
  /-- Every stage is finite over the target. -/
  stageFinite : ∀ i, IsFinite B S hS (structureMap.app i)
  /-- Every stage is of finite presentation over the target. -/
  stageFinitePresentation : ∀ i, IsFinitePresentation B S hS (structureMap.app i)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The target of a surjective universally closed morphism with affine source is quasi-compact,
separated and quasi-separated: an affine algebraic space is quasi-compact and separated by
Stacks 08GR, quasi-compactness of the target is Stacks 040W, separatedness of it is Stacks 05Z2 and
quasi-separatedness follows by Stacks 03DY. -/
private theorem target_isQuasiCompact_and_isAbsolutelyQuasiSeparated (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsurj : IsSurjective B S hS f) (hclosed : UniversallyClosed B S hS f)
    (haff : IsAffineSpace B S hS X) :
    IsQuasiCompactSpace B S hS Y ∧ IsAbsolutelySeparated B S hS B.contains_terminal Y ∧
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let V : SpacesEtale B S hS Xs := ⟨Over.mk (𝟙 Xs), fun U φ hφ ↦ hφ⟩
  have hXqcsep : IsQuasiCompactSeparated B S hS hZ X :=
    isQuasiCompactSeparated_of_isAffineSpace B S hS hZ Xs V haff
  have hYsep := isAbsolutelySeparated_of_isSurjective_of_universallyClosed B S hS hZ hX hY f
    hsurj hclosed hXqcsep.2
  exact ⟨IsQuasiCompactSpace.of_isSurjective B S hS hX hY hsurj hXqcsep.1, hYsep,
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ Y hYsep⟩

/-- Affineness of the target of a surjection presented as a directed limit of finite morphisms
of finite presentation.

The transition morphisms of the system are finite by Stacks 081Z, because each composite to
the target is finite and the target leg of the composite is separated, and finite morphisms
are affine; the stages are quasi-compact by Stacks 06G5 and quasi-separated by Stacks 03DY.
The system is therefore a `AlgebraicGeometry.Space.DescentSituation` with affine limit, so
`h07SQ` produces an affine stage, which is surjective onto the target because the given
morphism factors through it, and `hFinitePresentation` applies to it. -/
private theorem isAffineSpace_of_integralFiniteSystem (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsurj : IsSurjective B S hS f) (haff : IsAffineSpace B S hS X)
    (p : IntegralFiniteSystem B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    IsAffineSpace B S hS Y := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let : Preorder p.indexType := p.indexPreorder
  let : Nonempty p.indexType := p.indexNonempty
  let : IsDirected p.indexType (· ≤ ·) := p.indexDirected
  have htransition : ∀ {i j : p.indexTypeᵒᵖ} (g : i ⟶ j),
      IsAffineHom B S hS (p.diagram.map g) := by
    intro i j g
    have hsep : IsSeparated B S hS (p.structureMap.app j) :=
      isSeparated_of_isFinite B S hS (p.structureMap.app j) (p.stageAlgebraicSpace j) hY
        (p.stageFinite j)
    have hfin : IsFinite B S hS (p.diagram.map g ≫ p.structureMap.app j) := by
      rw [p.structureMap.naturality g]
      simpa using p.stageFinite i
    exact IsFinite.isAffineHom
      (isFinite_of_comp_of_isSeparated B S hS (p.diagram.map g) (p.structureMap.app j) hfin hsep)
  let D : DescentSituation B S hS hZ p.indexType :=
    { system := p.diagram
      algebraicSpace := fun i ↦ p.stageAlgebraicSpace (Opposite.op i)
      transition_affine := htransition
      quasiCompact := fun i ↦
        isQuasiCompactSpace_of_isFinitePresentation B S hS
          (p.structureMap.app (Opposite.op i)) hY hYqc
          (p.stageFinitePresentation (Opposite.op i))
      quasiSeparated := fun i ↦
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
          (p.stageAlgebraicSpace (Opposite.op i)) hYqs
          (p.stageFinitePresentation (Opposite.op i)).2.2
      limitCone := Cone.mk X p.limitCone
      isLimit := p.isLimit
      limitAlgebraicSpace := hX
      base := Classical.choice p.indexNonempty }
  obtain ⟨i, -, hstageAffine⟩ := h07SQ D haff
  have hfactor : f = p.limitCone.app (Opposite.op i) ≫ p.structureMap.app (Opposite.op i) :=
    p.compatible (Opposite.op i)
  have hstageSurj : IsSurjective B S hS (p.structureMap.app (Opposite.op i)) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨pointsMap B S hS X (p.limitCone.app (Opposite.op i)) x, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B S hS _ (p.structureMap.app (Opposite.op i))),
      ← pointsMap_comp, ← hfactor]
    exact hx
  exact hFinitePresentation (p.structureMap.app (Opposite.op i))
    (p.stageAlgebraicSpace (Opposite.op i)) hY (p.stageFinite (Opposite.op i))
    (p.stageFinitePresentation (Opposite.op i)) hstageSurj hstageAffine

/-- **Stacks 07VS.** Let `f : X ⟶ Y` be a surjective finite morphism of algebraic spaces over
`S`. If `X` is affine, then so is `Y`.

A finite morphism is affine and universally closed by Stacks 0414 and Stacks 0415, so the
target is separated by Stacks 05Z2 and quasi-compact by Stacks 040W. Writing `f` as a directed
limit of finite morphisms of finite presentation, a late stage is affine and is surjective onto
`Y`, which reduces the claim to the case of a morphism of finite presentation.

This form carries `h07VR`, `h07SQ` and `hFinitePresentation` as hypotheses; the Stacks 07VS tag
is carried by `AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`, which
proves the statement with none of them. -/
theorem isAffineSpace_of_isSurjective_of_isFinite (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsurj : IsSurjective B S hS f) (hfin : IsFinite B S hS f)
    (haff : IsAffineSpace B S hS X)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    IsAffineSpace B S hS Y := by
  obtain ⟨hYqc, -, hYqs⟩ :=
    target_isQuasiCompact_and_isAbsolutelyQuasiSeparated B S hS f hX hY hsurj
      (universallyClosed_of_isFinite B S hS hX hY hfin) haff
  exact isAffineSpace_of_integralFiniteSystem B S hS f hX hY hsurj haff
    (h07VR f hX hY hfin hYqc hYqs) hYqc hYqs h07SQ hFinitePresentation

/-- A surjective universally closed morphism `f : X ⟶ Y` of algebraic spaces over `S` with `X`
affine has affine target, granted the conclusions of Stacks 09YA and Stacks 07SQ and the case of
a finite morphism of finite presentation. Stacks 07VT itself, with none of these hypotheses, is
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`.

The target is separated by Stacks 05Z2 and quasi-compact by Stacks 040W, so `f` is affine by
Stacks 08GB and hence integral by Stacks 0415. Writing `f` as a directed limit of finite
morphisms of finite presentation, a late stage is affine and is surjective onto `Y`, which
reduces the claim to the case of a morphism which is finite and of finite presentation. -/
theorem isAffineSpace_of_isSurjective_of_universallyClosed (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsurj : IsSurjective B S hS f) (hclosed : UniversallyClosed B S hS f)
    (haff : IsAffineSpace B S hS X)
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    IsAffineSpace B S hS Y := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  obtain ⟨hYqc, hYsep, hYqs⟩ :=
    target_isQuasiCompact_and_isAbsolutelyQuasiSeparated B S hS f hX hY hsurj hclosed haff
  -- Stacks 08GB, part (4): a morphism from an affine space to a separated space is affine.
  have haffHom : IsAffineHom B S hS f := by
    obtain ⟨T, hT, ⟨e⟩⟩ := haff
    have h : IsAffineHom B S hS (e.inv ≫ f) :=
      isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ ⟨T, hT⟩ (e.inv ≫ f) hYsep
    have h' : IsAffineHom B S hS (e.hom ≫ e.inv ≫ f) := isAffineHom_iso_comp e.hom h
    rwa [← Category.assoc, e.hom_inv_id, Category.id_comp] at h'
  -- Stacks 0415: an affine universally closed morphism is integral.
  have hint : IsIntegralHom B S hS f :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hX hY f).2 ⟨haffHom, hclosed⟩
  exact isAffineSpace_of_integralFiniteSystem B S hS f hX hY hsurj haff
    (h09YA f hX hY hint hYqc hYqs) hYqc hYqs h07SQ hFinitePresentation

end AlgebraicGeometry.Space

end
