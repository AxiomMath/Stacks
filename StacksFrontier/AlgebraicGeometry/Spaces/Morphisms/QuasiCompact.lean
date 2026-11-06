module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# Quasi-compact morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is quasi-compact when every base change of it
along a morphism from a quasi-compact algebraic space has quasi-compact source. For a
representable morphism this agrees with quasi-compactness of all of its represented base changes.
Quasi-compactness of a morphism can be cancelled from a composite whose second factor is
quasi-separated, descends along a surjection, along an étale covering of the target and along a
universally open surjective base change, and is characterized by six local criteria. Every
morphism out of a quasi-separated algebraic space is quasi-separated, and a fibre product of
quasi-compact, respectively quasi-separated, algebraic spaces is again quasi-compact,
respectively quasi-separated.

## Main results

* `AlgebraicGeometry.Space.presheaf_quasiCompact_iff_isQuasiCompact`: for a representable
  morphism the two readings of quasi-compactness agree.
* `AlgebraicGeometry.Space.isQuasiCompact_of_comp_of_isQuasiSeparated`: if a composite is
  quasi-compact and its second factor is quasi-separated, then its first factor is
  quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isSurjective` and
  `AlgebraicGeometry.Space.isQuasiCompact_of_comp_surjective`: descent of quasi-compactness
  along a surjection.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isEtaleCovering` and
  `AlgebraicGeometry.Space.isQuasiCompact_tfae`: descent of quasi-compactness along an étale
  covering of the target, and the six local criteria for quasi-compactness of a morphism.
* `AlgebraicGeometry.Space.isQuasiCompact_of_universallyOpen_isSurjective`: descent of
  quasi-compactness along a universally open surjection.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source`: a morphism
  out of a quasi-separated algebraic space is quasi-separated.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_pullback` and
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_pullback`: a fibre product of
  quasi-compact, respectively quasi-separated, algebraic spaces is quasi-compact, respectively
  quasi-separated.

## Implementation notes

The two readings of quasi-compactness are compared for an arbitrary representable morphism of
presheaves, with no algebraicity hypothesis. The represented reading implies the other by
`AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact`; for the converse,
`Stacks.SeparationLocal.presheaf_of_affine` reduces the represented base changes to those along
a test object with affine underlying scheme, which is a quasi-compact algebraic space.

The local criteria all reduce to descent along an étale covering of the target, which holds
because an étale covering is an fpqc covering and quasi-compactness is fpqc local on the base.

Quasi-separatedness of an algebraic space is the absolute notion, over the terminal scheme.
The quasi-compactness half of the statement about morphisms out of a quasi-separated algebraic
space is `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace`.

## References

* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 04ZJ](https://stacks.math.columbia.edu/tag/04ZJ)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.SeparationLocal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-! ### The two readings of quasi-compactness -/


/-- If every base change of a representable morphism `f` along a morphism from a quasi-compact
algebraic space has quasi-compact source, then every represented base change of `f` is a
quasi-compact morphism of schemes. -/
theorem presheaf_quasiCompact_of_isQuasiCompact {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (hf : yoneda.relativelyRepresentable f) (h : IsQuasiCompact B S hS f) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have : AlgebraicGeometry.IsZariskiLocalAtTarget (@AlgebraicGeometry.QuasiCompact.{u}) :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fppfPrecoverage
  refine presheaf_of_affine B S hS hf fun a ha k => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj a) := ha
  exact quasiCompact_of_compactSpace_of_isAffine _ ha
    (compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      ((h (yoneda.obj a) (isAlgebraicSpace_yoneda B S hS a)
          (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) k).of_iso B S hS
        ((hf.isPullback k).flip.isoPullback).symm))

/-- For a representable morphism of algebraic spaces over `S` the two readings of
quasi-compactness agree: every represented base change of it is a quasi-compact morphism of
schemes exactly when every base change of it along a morphism from a quasi-compact algebraic
space has quasi-compact source. -/
@[stacks 03HD]
theorem presheaf_quasiCompact_iff_isQuasiCompact {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.QuasiCompact.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      IsQuasiCompact B S hS f :=
  ⟨isQuasiCompact_of_presheaf_quasiCompact B S hS,
    presheaf_quasiCompact_of_isQuasiCompact B S hS hf⟩

/-! ### Permanence -/

/-- The source of a quasi-compact morphism to a quasi-compact algebraic space is quasi-compact. -/
private theorem isQuasiCompactSpace_of_isQuasiCompact_of_isQuasiCompactSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompactSpace B S hS X :=
  isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 Y) f)) (hf Y hY hYqc (𝟙 Y))

/-- If a composite of morphisms of algebraic spaces over `S` is quasi-compact and its second
factor is quasi-separated, then its first factor is quasi-compact. -/
@[stacks 03KS, ega "IV 1.2.4"]
theorem isQuasiCompact_of_comp_of_isQuasiSeparated {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H) (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) (hgf : IsQuasiCompact B S hS (f ≫ g))
    (hg : IsQuasiSeparated B S hS g) :
    IsQuasiCompact B S hS f := by
  intro Z hZ hZqc k
  exact isQuasiCompactSpace_of_isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hZqc
    (pullback.mapDesc k f g ≫ pullback.fst (k ≫ g) (f ≫ g)) <|
    isQuasiCompact_comp B S hS
      (isAlgebraicSpace_pullback B S hS (k ≫ g) (f ≫ g) hZ hF hH) hZ _ _
      (isQuasiCompact_mapDesc B S hS k f g hg)
      (isQuasiCompact_of_isPullback B S hS
        (IsPullback.of_hasPullback (k ≫ g) (f ≫ g)).flip hgf)

/-- Quasi-compactness, as a morphism property of algebraic spaces over `S`, is stable under
composition. -/
instance quasiCompactMorphismProperty_isStableUnderComposition :
    (quasiCompactProperty B S hS).IsStableUnderComposition where
  comp_mem := fun {_ Y' Z'} k l hk hl =>
    isQuasiCompact_comp B S hS Y'.property Z'.property k.hom l.hom hk hl

/-! ### Descent along a surjection -/

section Surjective

attribute [local instance] pointTopology

/-- The image of a quasi-compact algebraic space over `S` under a surjective morphism of
algebraic spaces over `S` is quasi-compact. -/
@[stacks 040W "part (1)"]
theorem isQuasiCompactSpace_of_isSurjective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsSurjective B S hS f) (hFqc : IsQuasiCompactSpace B S hS F) :
    IsQuasiCompactSpace B S hS G :=
  isQuasiCompactSpace_of_finite_jointly_surjective B S hS (I := PUnit.{1}) (fun _ ↦ hF) hG
    (fun _ ↦ f) ((isJointlySurjective_const_iff B S hS f).mpr hf) fun _ ↦ hFqc

/-- In a commuting triangle `p = f ≫ q` of morphisms of algebraic
spaces over `S` whose horizontal morphism `f` is surjective, quasi-compactness of `p` implies
quasi-compactness of `q`. -/
@[stacks 040W "part (2)"]
theorem isQuasiCompact_of_comp_surjective {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (f : F ⟶ G) (p : F ⟶ H) (q : G ⟶ H) (hcomm : p = f ≫ q)
    (hf : IsSurjective B S hS f) (hp : IsQuasiCompact B S hS p) :
    IsQuasiCompact B S hS q := by
  intro Z hZ hZqc g
  have hbase : IsAlgebraicSpace B S hS (pullback g q) :=
    isAlgebraicSpace_pullback B S hS g q hZ hG hH
  refine isQuasiCompactSpace_of_isSurjective B S hS
    (isAlgebraicSpace_pullback B S hS f (pullback.snd g q) hF hbase hG) hbase
    (pullback.snd f (pullback.snd g q))
    (isSurjective_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
        (ObjectProperty.homMk (pullback.snd g q) :
          (⟨pullback g q, hbase⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩))
      hf)
    (isQuasiCompactSpace_of_iso B S hS
      (pullback.congrHom rfl hcomm ≪≫ (pullbackLeftPullbackSndIso g q f).symm ≪≫
        pullbackSymmetry (pullback.snd g q) f) (hp Z hZ hZqc g))

end Surjective

/-! ### Local criteria -/

/-- Quasi-compactness of a morphism of algebraic spaces over `S` descends along an étale
covering of the target. -/
theorem isQuasiCompact_of_isEtaleCovering {I : Type u}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    {Gi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : ∀ i, Gi i ⟶ G}
    (hcov : IsEtaleCovering B S hS Gi g)
    (hlocal : ∀ i, IsQuasiCompact B S hS (pullback.fst (g i) f)) :
    IsQuasiCompact B S hS f := by
  let Y : AlgebraicSpaces B S hS := ⟨G, hG⟩
  let fM : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y := ObjectProperty.homMk f
  let Gi' : I → AlgebraicSpaces B S hS := fun i ↦ ⟨Gi i, hcov.source_isAlgebraicSpace i⟩
  let gM : ∀ i, Gi' i ⟶ Y := fun i ↦ ObjectProperty.homMk (g i)
  have hR : Presieve.ofArrows Gi' gM ∈ Topology.precoverage.{u, u} .fpqc B S hS Y :=
    ⟨I, Gi', gM, rfl, hG, hcov.source_isAlgebraicSpace,
      isFpqcCovering_of_isEtaleCovering B S hS Gi g hcov⟩
  have _ : (quasiCompactProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, u} .fpqc B S hS) := quasiCompact_isLocalAtTarget_fpqc B S hS
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := quasiCompactProperty B S hS)
    (K := Topology.precoverage.{u, u} .fpqc B S hS) (f := fM) hR ?_
  rintro V k _ ⟨i⟩
  exact (quasiCompactMorphismProperty_pullback_snd_iff B S hS fM (gM i)).mpr
    (isQuasiCompact_pullback_snd_of_fst B S hS f (g i) (hlocal i))

/-- For a morphism `f : F ⟶ G` of algebraic spaces over `S` the following six
conditions are equivalent: `f` is quasi-compact; the base change of `f` along every morphism
to `G` from a presheaf represented by an object of the site is quasi-compact; for every such
object with affine underlying scheme the fibre product is a quasi-compact algebraic space;
the base change of `f` along some surjective étale morphism to `G` from a represented
presheaf is quasi-compact; the same for some surjective étale morphism from an arbitrary
algebraic space; and there is a Zariski covering of `G` along each member of which the base
change of `f` is quasi-compact. -/
@[stacks 03KG]
theorem isQuasiCompact_tfae {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE
      [IsQuasiCompact B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
          IsQuasiCompact B S hS (pullback.fst g f),
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
          IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
            IsQuasiCompactSpace B S hS (pullback g f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            IsQuasiCompact B S hS (pullback.fst g f),
        ∃ (G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS G')
          (g : G' ⟶ G), IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            IsQuasiCompact B S hS (pullback.fst g f),
        ∃ (I : Type u) (U : I → Subfunctor G) (_ : IsZariskiCover B S hS I U),
          ∀ i, IsQuasiCompact B S hS (pullback.fst (U i).ι f)] := by
  classical
  tfae_have 1 → 2 := fun hf Z g ↦
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hf
  tfae_have 2 → 3 := by
    intro h Z g haffine
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) := haffine
    exact isQuasiCompactSpace_of_isQuasiCompact_of_isQuasiCompactSpace B S hS
      (isAlgebraicSpace_yoneda B S hS Z)
      ((isQuasiCompactSpace_iff_compactSpace_points B S hS _
        (isAlgebraicSpace_yoneda B S hS Z)).mpr (compactSpace_points_yoneda B S hS Z))
      _ (h Z g)
  tfae_have 3 → 1 := fun h ↦
    isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hF hG f fun T hT g ↦ h T g hT
  tfae_have 2 → 4 := by
    intro h
    obtain ⟨V, g, hgsurj, hgetale⟩ := hG.exists_atlas
    exact ⟨V, g, (surjective_iff_surjective_pointsMap B S hS G hG V g).mp hgsurj,
      isEtale_of_presheaf_etale B S hS hgetale,
      h V g⟩
  tfae_have 4 → 5 := fun ⟨V, g, hgsurj, hgetale, hqc⟩ ↦
    ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V, g, hgsurj, hgetale, hqc⟩
  tfae_have 5 → 1 := by
    rintro ⟨G', hG', g, hgsurj, hgetale, hqc⟩
    exact isQuasiCompact_of_isEtaleCovering B S hS hF hG f
      (Gi := fun _ : PUnit.{u + 1} ↦ G') (g := fun _ ↦ g)
      ⟨hG, fun _ ↦ hG', fun _ ↦ hgetale,
        (isJointlySurjective_const_iff B S hS g).mpr hgsurj⟩ fun _ ↦ hqc
  tfae_have 1 → 6 := by
    intro hf
    refine ⟨PUnit.{u + 1}, fun _ ↦ ((openSubspacesOrderIso B S hS G hG).symm ⊤).1, ?_,
      fun _ ↦ isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback _ f).flip hf⟩
    refine (isZariskiCover_iff_iUnion_points B S hS G hG PUnit.{u + 1} _
      fun _ ↦ ((openSubspacesOrderIso B S hS G hG).symm ⊤).2).2 ?_
    have hrange : Set.range (pointsMap B S hS
        ((openSubspacesOrderIso B S hS G hG).symm ⊤).1.toFunctor
        ((openSubspacesOrderIso B S hS G hG).symm ⊤).1.ι) = Set.univ := by
      rw [← openSubspacesOrderIso_apply B S hS G hG ((openSubspacesOrderIso B S hS G hG).symm ⊤)]
      simp
    simpa [hrange] using Set.iUnion_const (ι := PUnit.{u + 1}) (Set.univ : Set (points B S hS G))
  tfae_have 6 → 1 := by
    rintro ⟨I, U, hcover, hlocal⟩
    have hpoints :=
      (isZariskiCover_iff_iUnion_points B S hS G hG I U fun i ↦ hcover.1 i).mp hcover
    exact isQuasiCompact_of_isEtaleCovering B S hS hF hG f
      (isEtaleCovering_of_isZariskiCovering B S hS hG (fun i ↦ (hcover.1 i).1)
        ⟨fun i ↦ (hcover.1 i).2, Set.iUnion_eq_univ_iff.mp hpoints⟩) hlocal
  tfae_finish

/-! ### Descent along a universally open surjection -/

section UniversallyOpen

attribute [local instance] pointTopology

/-- Let `g : G' ⟶ G` be a universally open surjective morphism of algebraic spaces over `S`.
If the base change of `f : F ⟶ G` along `g` is quasi-compact, then so is `f`. -/
@[stacks 04ZJ]
theorem isQuasiCompact_of_universallyOpen_isSurjective
    {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hG' : IsAlgebraicSpace B S hS G') (f : F ⟶ G)
    (g : G' ⟶ G) (hgopen : UniversallyOpen B S hS g) (hgsurj : IsSurjective B S hS g)
    (hf : IsQuasiCompact B S hS (pullback.fst g f)) :
    IsQuasiCompact B S hS f := by
  classical
  intro Z hZ hZqc z
  have hT : IsAlgebraicSpace B S hS (pullback z g) :=
    isAlgebraicSpace_pullback B S hS z g hZ hG' hG
  have hπopen : IsOpenMorphism B S hS (pullback.fst z g) := hgopen Z hZ z
  have hπsurj : IsSurjective B S hS (pullback.fst z g) :=
    surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback z g).flip hgsurj
  have _ : CompactSpace (points B S hS Z) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS Z hZ).mp hZqc
  choose V hVsub hVqc v hVpt using fun t : points B S hS (pullback z g) ↦
    exists_isOpenSubspace_isQuasiCompactSpace_pointsMap_eq B S hS hT t
  have hVopen (t : points B S hS (pullback z g)) :
      IsOpen (Set.range (pointsMap B S hS (V t).toFunctor (V t).ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS (V t).ι (hVsub t).2
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun t ↦ pointsMap B S hS (pullback z g) (pullback.fst z g) ''
      Set.range (pointsMap B S hS (V t).toFunctor (V t).ι))
    (fun t ↦ hπopen _ (hVopen t)) fun y _ ↦ by
      obtain ⟨t, ht⟩ := hπsurj y
      exact Set.mem_iUnion.2 ⟨t, ⟨t, ⟨v t, hVpt t⟩, ht⟩⟩
  obtain ⟨W, hWsub, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hT
    (⋃ t ∈ s, Set.range (pointsMap B S hS (V t).toFunctor (V t).ι))
    (isOpen_biUnion fun t _ ↦ hVopen t)
  choose i hi using fun t : {t // t ∈ s} ↦
    (factorsThrough_openSubspace_iff_points B S hS hT (hVsub t.1).1 W hWsub
      (V t.1).ι).2 (by rw [hWrange]; exact fun _ hx ↦ Set.mem_biUnion t.2 hx)
  have hWinj : Function.Injective (pointsMap B S hS W.toFunctor W.ι) :=
    (isEmbedding_pointsMap_of_isImmersion B S hS hT W.ι
      (isImmersion_of_isOpenImmersion B S hS hWsub.2)).injective
  have hWqc : IsQuasiCompactSpace B S hS W.toFunctor := by
    rw [isQuasiCompactSpace_iff_compactSpace_points B S hS W.toFunctor hWsub.1]
    refine ⟨?_⟩
    rw [← Set.eq_univ_of_univ_subset (s := ⋃ t : {t // t ∈ s},
      Set.range (pointsMap B S hS (V t.1).toFunctor (i t))) fun x _ ↦ ?_]
    · refine isCompact_iUnion fun t ↦ ?_
      have _ : CompactSpace (points B S hS (V t.1).toFunctor) :=
        (isQuasiCompactSpace_iff_compactSpace_points B S hS _ (hVsub t.1).1).mp (hVqc t.1)
      exact isCompact_range (continuous_pointsMap B S hS (i t))
    · obtain ⟨t, ht, w, hw⟩ := Set.mem_iUnion₂.1
        (hWrange ▸ Set.mem_range_self (f := pointsMap B S hS W.toFunctor W.ι) x)
      exact Set.mem_iUnion.2
        ⟨⟨t, ht⟩, w, hWinj (by rw [← pointsMap_comp_apply, hi ⟨t, ht⟩, hw])⟩
  have hWsurj : IsSurjective B S hS (W.ι ≫ pullback.fst z g) := by
    intro y
    obtain ⟨t, ht, tpt, ⟨w, hw⟩, hty⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    have hwW : pointsMap B S hS W.toFunctor W.ι
        (pointsMap B S hS (V t).toFunctor (i ⟨t, ht⟩) w) = tpt := by
      rw [← pointsMap_comp_apply, hi ⟨t, ht⟩, hw]
    exact ⟨pointsMap B S hS (V t).toFunctor (i ⟨t, ht⟩) w, by
      rw [pointsMap_comp_apply, hwW, hty]⟩
  have hP : IsAlgebraicSpace B S hS (pullback z f) :=
    isAlgebraicSpace_pullback B S hS z f hZ hF hG
  refine isQuasiCompactSpace_of_isSurjective B S hS
    (isAlgebraicSpace_pullback B S hS (W.ι ≫ pullback.fst z g) (pullback.fst z f)
      hWsub.1 hP hZ)
    hP (pullback.snd (W.ι ≫ pullback.fst z g) (pullback.fst z f))
    (surjective_pointsMap_of_isPullback B S hS
      (IsPullback.of_hasPullback (W.ι ≫ pullback.fst z g) (pullback.fst z f)) hWsurj)
    (isQuasiCompactSpace_of_iso B S hS
      (pullbackRightPullbackFstIso g f (W.ι ≫ pullback.snd z g) ≪≫
        pullback.congrHom (by rw [Category.assoc, Category.assoc, ← pullback.condition]) rfl ≪≫
        (pullbackRightPullbackFstIso z f (W.ι ≫ pullback.fst z g)).symm)
      (hf W.toFunctor hWsub.1 hWqc (W.ι ≫ pullback.snd z g)))

end UniversallyOpen

/-! ### Quasi-compact and quasi-separated algebraic spaces -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Every morphism of algebraic spaces over `S` out of a quasi-separated algebraic space is
quasi-separated. -/
@[stacks 073B "part (2): quasi-separated"]
theorem isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F) (f : F ⟶ G) :
    IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_isQuasiSeparatedOver B S hS
    (isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ hF hFqs) f

/-- A fibre product of quasi-compact algebraic spaces over `S` over a quasi-separated
algebraic space is quasi-compact. -/
@[stacks 073B "part (3): quasi-compact"]
theorem isQuasiCompactSpace_pullback {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H)
    (g : G ⟶ H) (hF : IsAlgebraicSpace B S hS F) (hH : IsAlgebraicSpace B S hS H)
    (hFqc : IsQuasiCompactSpace B S hS F) (hGqc : IsQuasiCompactSpace B S hS G)
    (hHqs : IsAbsolutelyQuasiSeparated B S hS hZ H) :
    IsQuasiCompactSpace B S hS (pullback f g) :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hH hHqs hGqc g F hF hFqc f

/-- A fibre product of quasi-separated algebraic spaces over `S` is quasi-separated. -/
@[stacks 073B "part (3): quasi-separated"]
theorem isAbsolutelyQuasiSeparated_pullback {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H)
    (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (hGqs : IsAbsolutelyQuasiSeparated B S hS hZ G) :
    IsAbsolutelyQuasiSeparated B S hS hZ (pullback f g) :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    (isAlgebraicSpace_pullback B S hS f g hF hG hH) hGqs
    (isQuasiSeparated_pullback B S hS f g
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hF hFqs f))

end AlgebraicGeometry.Space

end
