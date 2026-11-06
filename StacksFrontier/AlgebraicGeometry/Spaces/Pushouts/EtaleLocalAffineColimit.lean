module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Detecting a colimit of algebraic spaces on étale sites and affine charts

Let `B` be an algebraic space over a scheme `S`, let `i ↦ X i` be a diagram of algebraic
spaces over `B`, and let `c` be a cocone on it in the algebraic spaces over `B`. Suppose that
base change along the cocone legs is an equivalence from the small étale site of the vertex to
the limit of the small étale sites of the `X i`, and that for every affine `B'` étale over `B`,
every affine `Z` over `B'` and every affine `U` étale over the vertex and lying over `B'`, a
cocone of morphisms `U ×_X X i ⟶ Z` over `B'` descends uniquely to a morphism `U ⟶ Z` over
`B'`. Then the cocone is a colimit in *all* algebraic spaces over `B`.

## Main definitions

* `AlgebraicGeometry.Space.CompatibleEtaleDiagram` is an object of the limit of the small
  étale sites of the members of the diagram: a diagram of algebraic spaces étale over the
  members, whose transition squares are cartesian.
* `AlgebraicGeometry.Space.EtaleRealization` is an algebraic space étale over the vertex of
  the cocone together with cartesian identifications of all of its base changes along the
  cocone legs with a given compatible diagram.
* `AlgebraicGeometry.Space.EtaleComparisonIsEquivalence` is the first hypothesis: the base
  change comparison is essentially surjective and fully faithful.

## Main results

* `AlgebraicGeometry.Space.isColimit_of_etale_local_affine_descent`: **Stacks 0GHL**, the
  cocone is a colimit in the category of algebraic spaces over `B`.

## Implementation notes

The limit of the small étale sites of the members of the diagram is not constructed: an
object of it is recorded as `AlgebraicGeometry.Space.CompatibleEtaleDiagram`, a diagram `E` of
algebraic spaces with a natural transformation to the diagram which is étale in each component
and equifibered, equifiberedness being exactly cartesianness of the transition squares. An
object of the small étale site of the vertex together with an identification of its image in
that limit is `AlgebraicGeometry.Space.EtaleRealization`. Essential surjectivity and full
faithfulness of the base change comparison are then expressed on these data, which avoids
choosing pullbacks and coherence isomorphisms for a strict diagram of sites.

In the source, the second hypothesis is stated for an étale morphism `U ⟶ X ×_B B'` with `U`
affine. Here it is stated for an étale realization `r` with affine total space together with a
morphism `u : r.U ⟶ B'` over `B`; the two agree, because `X ×_B B' ⟶ X` is étale, so a
morphism to `X ×_B B'` is étale exactly when its composite with that projection is. Stating it
on a realization also supplies the fibre products `U ×_X X i` on which the given cocone
`f i : U_i ⟶ Z` lives.

Affineness of an algebraic space is `AlgebraicGeometry.Space.IsAffineSpace`, which is
representability by an object of the site with affine underlying scheme; it is applied to the
underlying presheaf of an object of `AlgebraicGeometry.AlgebraicSpaces`.

The site is named `site` throughout, so that `B` is free for the base algebraic space as in
the source.

## References

* [Stacks Project, Tag 0GHL](https://stacks.math.columbia.edu/tag/0GHL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (site : BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_EtaleLocalAffineColimit
    {X Y Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Objects of the limit of the étale sites and their realizations -/

/-- A cartesian family of algebraic spaces étale over the members of a diagram of algebraic
spaces over `B`. This is an object of the limit of the small étale sites of the members. -/
structure CompatibleEtaleDiagram {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} (D : I ⥤ Over B) where
  /-- The diagram of algebraic spaces étale over the members of `D`. -/
  U : I ⥤ AlgebraicSpaces site S hS
  /-- The structure morphisms to the members of `D`. -/
  projection : U ⟶ D ⋙ Over.forget B
  /-- Each structure morphism is étale. -/
  etale : ∀ i, IsEtale site S hS (projection.app i).hom
  /-- The transition squares of the family are cartesian. -/
  cartesian : NatTrans.Equifibered projection

/-- An algebraic space étale over the vertex of a cocone, together with cartesian
identifications of its base changes along the cocone legs with a given compatible family. -/
structure EtaleRealization {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B} (c : Cocone D)
    (E : CompatibleEtaleDiagram site S hS D) where
  /-- The algebraic space over the vertex. -/
  U : AlgebraicSpaces site S hS
  /-- Its structure morphism to the vertex. -/
  toX : U ⟶ c.pt.left
  /-- The structure morphism is étale. -/
  etale : IsEtale site S hS toX.hom
  /-- The identification of the members of the family with the base changes. -/
  baseChange : E.U ⟶ (Functor.const I).obj U
  /-- The identifications are compatible with the two morphisms to the vertex. -/
  overX : ∀ i, E.projection.app i ≫ (c.ι.app i).left = baseChange.app i ≫ toX
  /-- Each identification square is cartesian. -/
  isPullback : ∀ i, IsPullback (E.projection.app i) (baseChange.app i)
    (c.ι.app i).left toX

/-- The base change comparison from the small étale site of the vertex of a cocone to the
limit of the small étale sites of the members of the diagram is an equivalence: every
compatible family is realized, and realizations reproduce the morphisms of families. -/
structure EtaleComparisonIsEquivalence {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (c : Cocone D) : Prop where
  /-- Every compatible family of étale spaces over the diagram is realized over the vertex. -/
  essentiallySurjective : ∀ E : CompatibleEtaleDiagram site S hS D,
    Nonempty (EtaleRealization site S hS c E)
  /-- A morphism of compatible families lifts uniquely to a morphism of realizations. -/
  fullyFaithful :
    ∀ (E F : CompatibleEtaleDiagram site S hS D)
      (r : EtaleRealization site S hS c E)
      (s : EtaleRealization site S hS c F)
      (α : E.U ⟶ F.U),
      α ≫ F.projection = E.projection →
        ∃! f : r.U ⟶ s.U,
          (f ≫ s.toX = r.toX) ∧
            (∀ i, r.baseChange.app i ≫ f = α.app i ≫ s.baseChange.app i)

/-- Unique descent of a cocone of morphisms to an affine space over an affine étale base,
along an affine étale realization. This is the second hypothesis of Stacks 0GHL. -/
private abbrev AffineDescent
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B} (c : Cocone D) :=
  ∀ (B' : AlgebraicSpaces site S hS) (b : B' ⟶ B),
    IsAffineSpace site S hS B'.1 → IsEtale site S hS b.hom →
    ∀ (Z : AlgebraicSpaces site S hS) (z : Z ⟶ B'),
      IsAffineSpace site S hS Z.1 →
      ∀ (E : CompatibleEtaleDiagram site S hS D)
        (r : EtaleRealization site S hS c E),
        IsAffineSpace site S hS r.U.1 → ∀ (u : r.U ⟶ B'),
          r.toX ≫ c.pt.hom = u ≫ b →
          ∀ (fᵢ : E.U ⟶ (Functor.const I).obj Z),
            (∀ i, fᵢ.app i ≫ z = r.baseChange.app i ≫ u) →
            ∃! f : r.U ⟶ Z, (f ≫ z = u) ∧
              (∀ i, r.baseChange.app i ≫ f = fᵢ.app i)

/-- Two morphisms from an affine realization to an affine space over an affine étale base
which agree over that base and on the given diagram are equal: this is the uniqueness half of
the affine descent condition, applied to the family obtained by postcomposition. -/
private lemma affine_realization_hom_ext
    {I : Type v} [Category.{w} I]
    {B B' : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (c : Cocone D)
    (h₂ : AffineDescent site S hS c)
    (b : B' ⟶ B) (hb' : IsAffineSpace site S hS B'.1)
    (hbe : IsEtale site S hS b.hom)
    (Z : AlgebraicSpaces site S hS) (z : Z ⟶ B')
    (hZ : IsAffineSpace site S hS Z.1)
    (E : CompatibleEtaleDiagram site S hS D)
    (r : EtaleRealization site S hS c E)
    (hr : IsAffineSpace site S hS r.U.1)
    (u : r.U ⟶ B') (hu : r.toX ≫ c.pt.hom = u ≫ b)
    {f g : r.U ⟶ Z}
    (hfz : f ≫ z = u) (hgz : g ≫ z = u)
    (hfi : ∀ i, r.baseChange.app i ≫ f = r.baseChange.app i ≫ g) :
    f = g := by
  let fᵢ : E.U ⟶ (Functor.const I).obj Z :=
    r.baseChange ≫ (Functor.const I).map f
  have hcompat : ∀ i, fᵢ.app i ≫ z = r.baseChange.app i ≫ u := by
    intro i
    simpa [fᵢ, Category.assoc] using
      congrArg (fun k => r.baseChange.app i ≫ k) hfz
  have h := h₂ B' b hb' hbe Z z hZ E r hr u hu fᵢ hcompat
  apply h.unique
  · refine ⟨hfz, ?_⟩
    intro i
    simp [fᵢ]
  · refine ⟨hgz, ?_⟩
    intro i
    simpa [fᵢ] using (hfi i).symm

/-! ### Base changing a diagram along an étale morphism -/

/-- The base change of a cocone of algebraic spaces along an étale morphism, recorded as a
compatible family together with the second projections of its cartesian squares. -/
private structure PullbackEtaleDiagramData
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (X Z : AlgebraicSpaces site S hS)
    (η : D ⋙ Over.forget B ⟶ (Functor.const I).obj X)
    (z : Z ⟶ X) where
  /-- The base changed family, étale over the diagram. -/
  diagram : CompatibleEtaleDiagram site S hS D
  /-- The second projections of the base change squares. -/
  second : diagram.U ⟶ (Functor.const I).obj Z
  /-- The base change squares are cartesian. -/
  isPullback : ∀ i, IsPullback (diagram.projection.app i)
    (second.app i) (η.app i) z

/-- Base changing an étale morphism `z : Z ⟶ X` along a cocone `η` with vertex `X` produces a
compatible family over the diagram, by stability of étaleness and of cartesian squares. -/
private noncomputable def pullbackEtaleDiagram
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (X Z : AlgebraicSpaces site S hS)
    (η : D ⋙ Over.forget B ⟶ (Functor.const I).obj X)
    (z : Z ⟶ X) (hz : IsEtale site S hS z.hom) :
    PullbackEtaleDiagramData site S hS X Z η z := by
  classical
  let C := AlgebraicSpaces site S hS
  let D' : I ⥤ C := D ⋙ Over.forget B
  let ζ := (Functor.const I).map z
  let U : I ⥤ C := pullback η ζ
  let projection : U ⟶ D' := pullback.fst η ζ
  let second : U ⟶ (Functor.const I).obj Z := pullback.snd η ζ
  let hp (i : I) : IsPullback (projection.app i) (second.app i) (η.app i) z :=
    (IsPullback.of_hasPullback η ζ).app i
  let E : CompatibleEtaleDiagram site S hS D := by
    refine { U := U, projection := projection, etale := ?_, cartesian := ?_ }
    · intro i
      exact isEtale_of_isPullback site S hS
        (X' := U.obj i) (X := Z) (Z := D'.obj i) (Y := X)
        (p := second.app i) (f' := projection.app i) (f := z) (g := η.app i)
        (hp i).flip hz
    · intro i j f
      have hη : D'.map f ≫ η.app j = η.app i := by simp
      refine IsPullback.of_right ?_ ?_ (hp j).flip
      · rw [hη]
        have hs : U.map f ≫ second.app j = second.app i := by
          simp
        simpa only [Category.assoc, hs] using (hp i).flip
      · exact projection.naturality f
  exact ⟨E, second, hp⟩

/-! ### Jointly surjective étale families -/

/-- Two morphisms out of an algebraic space agreeing on the members of an fpqc covering of it
are equal: an algebraic space is an fpqc sheaf. -/
private lemma hom_ext_of_fpqc_covering
    {A : Type u} {X Z : AlgebraicSpaces site S hS}
    (U : A → AlgebraicSpaces site S hS)
    (p : ∀ a, U a ⟶ X)
    (hp : IsFpqcCovering site S hS (fun a => (p a).hom))
    {f g : X ⟶ Z}
    (h : ∀ a, p a ≫ f = p a ≫ g) : f = g := by
  have hcompat (a b : A) :
      (ObjectProperty.homMk (pullback.fst (p a).hom (p b).hom) :
        AlgebraicSpaces.fiberProduct site S hS (p a) (p b) ⟶ U a) ≫
          (p a ≫ f) =
      (ObjectProperty.homMk (pullback.snd (p a).hom (p b).hom) :
        AlgebraicSpaces.fiberProduct site S hS (p a) (p b) ⟶ U b) ≫
          (p b ≫ f) :=
    ObjectProperty.hom_ext _ (congrArg (fun q => q ≫ f.hom) pullback.condition)
  obtain ⟨q, hq, hq_unique⟩ :=
    existsUnique_desc_of_fpqcCovering site S hS p hp Z (fun a => p a ≫ f) hcompat
  exact (hq_unique f (fun _ => rfl)).trans
    (hq_unique g (fun a => (h a).symm)).symm

/-- A jointly surjective family of étale morphisms of algebraic spaces is an fpqc covering. -/
private lemma etale_family_fpqc_of_points_surjective
    {A : Type u} (U : A → AlgebraicSpaces site S hS)
    {X : AlgebraicSpaces site S hS}
    (p : ∀ a, U a ⟶ X)
    (hp : ∀ a, IsEtale site S hS (p a).hom)
    (hsurj : ∀ x : points site S hS X.1,
      ∃ a, ∃ y : points site S hS (U a).1,
        pointsMap site S hS (U a).1 (p a).hom y = x) :
    IsFpqcCovering site S hS (fun a => (p a).hom) := by
  refine isFpqcCovering_of_isEtaleCovering site S hS (fun a => (U a).1) (fun a => (p a).hom)
    ⟨X.2, fun a => (U a).2, hp, Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  obtain ⟨a, y, hy⟩ := hsurj x
  exact Set.mem_iUnion.mpr ⟨a, y, hy⟩

/-- An algebraic space is covered by an étale family of affine objects of the site: refine an
étale surjective chart of it by the affine open cover of that chart. -/
private theorem exists_affine_etale_covering
    (F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace site S hS F) :
    ∃ (A : Type u) (U : A → BigFppfOver site S hS)
      (g : ∀ a, yoneda.obj (U a) ⟶ F),
      (∀ a, IsAffine ((BigFppfOver.toScheme site S hS).obj (U a))) ∧
      IsEtaleCovering site S hS (fun a => yoneda.obj (U a)) g := by
  obtain ⟨V, v, hvSurj, hvEtale⟩ := hF.exists_atlas
  obtain ⟨A, W, π, hW, hcov⟩ := exists_affine_isEtaleCovering_yoneda site S hS V
  have h := isEtaleCovering_comp site S hS (fun _ : PUnit.{u + 1} => A)
    (fun _ => yoneda.obj V) (fun _ => v)
    (fun _ a => yoneda.obj (W a)) (fun _ a => yoneda.map (π a))
    (isEtaleCovering_atlas site S hS hF hvSurj hvEtale) (fun _ => hcov)
  exact ⟨A, W, fun a => yoneda.map (π a) ≫ v, hW,
    IsEtaleCovering.reindex site S hS h
      (σ := fun a : A => (⟨PUnit.unit, a⟩ : (_ : PUnit.{u + 1}) × A))
      (fun ij => ⟨ij.2, rfl⟩)⟩

/-! ### The identity realization -/

/-- The diagram itself, regarded as a compatible family of étale spaces over itself. -/
private abbrev identityDiagram {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} (D : I ⥤ Over B) :
    CompatibleEtaleDiagram site S hS D where
  U := D ⋙ Over.forget B
  projection := 𝟙 _
  etale := fun _ => isEtale_id site S hS _
  cartesian := NatTrans.Equifibered.of_isIso (𝟙 _)

/-- The vertex of a cocone, regarded as a realization of the diagram itself. -/
private abbrev identityRealization {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B} (c : Cocone D) :
    EtaleRealization site S hS c (identityDiagram site S hS D) where
  U := c.pt.left
  toX := 𝟙 _
  etale := isEtale_id site S hS _
  baseChange := ((Over.forget B).mapCocone c).ι
  overX i := by simp [identityDiagram]
  isPullback i := IsPullback.of_id_fst

/-- An open subspace of the vertex of a cocone through which every cocone leg factors is the
whole vertex: full faithfulness of the comparison splits the inclusion of the subspace. -/
private lemma open_subspace_eq_top_of_cocone_maps_factor
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (c : Cocone D) (h₁ : EtaleComparisonIsEquivalence site S hS c)
    (W : OpenSubspaces site S hS c.pt.left.1)
    (maps : ∀ i, ((D.obj i).left ⟶ ⟨W.1.toFunctor, W.2.1⟩))
    (hmaps : ∀ i,
      maps i ≫ ObjectProperty.homMk W.1.ι = (c.ι.app i).left) :
    W.1 = ⊤ := by
  let E := identityDiagram site S hS D
  let rX : EtaleRealization site S hS c E := identityRealization site S hS c
  let incl : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces site S hS) ⟶ c.pt.left :=
    ObjectProperty.homMk W.1.ι
  have hmaps0 (k : I) : (maps k).hom ≫ W.1.ι = (c.ι.app k).left.hom :=
    congrArg (fun q => q.hom) (hmaps k)
  let rW : EtaleRealization site S hS c E :=
    { U := ⟨W.1.toFunctor, W.2.1⟩
      toX := incl
      etale := isEtale_of_presheaf_etale site S hS
        (presheaf_etale_of_isOpenImmersion site S hS W.2.2)
      baseChange :=
        { app := maps
          naturality := by
            intro i j f
            apply ObjectProperty.hom_ext
            apply (cancel_mono W.1.ι).1
            calc
              (D.map f).left.hom ≫ (maps j).hom ≫ W.1.ι =
                  (D.map f).left.hom ≫ (c.ι.app j).left.hom := by
                    rw [hmaps0 j]
              _ = (c.ι.app i).left.hom :=
                congrArg (fun q => q.left.hom) (c.ι.naturality f)
              _ = (maps i).hom ≫ W.1.ι :=
                (hmaps0 i).symm }
      overX := by
        intro i
        show E.projection.app i ≫ (c.ι.app i).left =
          maps i ≫ incl
        simpa [E] using (hmaps i).symm
      isPullback := by
        intro i
        refine IsPullback.mk' ?_ ?_ ?_
        · simpa [E] using (hmaps i).symm
        · intro T a b hab hba
          simpa [E] using hab
        · intro T a b hab
          refine ⟨a, ?_, ?_⟩
          · simp [E]
          apply ObjectProperty.hom_ext
          apply (cancel_mono W.1.ι).1
          have hab0 := congrArg (fun q => q.hom) hab
          change a.hom ≫ (c.ι.app i).left.hom = b.hom ≫ W.1.ι at hab0
          change a.hom ≫ (maps i).hom ≫ W.1.ι = _
          rw [hmaps0 i]
          exact hab0 }
  obtain ⟨f, hf, _⟩ := h₁.fullyFaithful E E rX rW (𝟙 E.U) (by simp)
  refine le_antisymm le_top fun T x _ => ?_
  have hy : (f.hom.app T x).1 = x := congrArg (fun q => q.hom.app T x) hf.1
  exact hy ▸ (f.hom.app T x).2

/-- An étale family over the vertex of a cocone whose image on points contains the images of
all the cocone legs is jointly surjective, hence an fpqc covering of the vertex: the open
subspace it cuts out receives every cocone leg, so it is everything. -/
private lemma etale_family_covers_of_cocone_basechange_cover
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (c : Cocone D) (h₁ : EtaleComparisonIsEquivalence site S hS c) {A : Type u}
    (U : A → AlgebraicSpaces site S hS)
    (g : ∀ a, U a ⟶ c.pt.left)
    (hg : ∀ a, IsEtale site S hS (g a).hom)
    (hcover : ∀ (i : I) (x : points site S hS (D.obj i).left.1),
      ∃ a, ∃ y : points site S hS (U a).1,
        pointsMap site S hS (U a).1 (g a).hom y =
          pointsMap site S hS (D.obj i).left.1 (c.ι.app i).left.hom x) :
    (∀ x : points site S hS c.pt.left.1,
      ∃ a, ∃ y : points site S hS (U a).1,
        pointsMap site S hS (U a).1 (g a).hom y = x) ∧
      IsFpqcCovering site S hS (fun a => (g a).hom) := by
  have hopen_range (a : A) : IsOpen
      (Set.range (pointsMap site S hS (U a).1 (g a).hom)) :=
    isOpen_range_pointsMap_of_isEtale site S hS (g a).hom (U a).property
      c.pt.left.property (hg a)
  let V : TopologicalSpace.Opens (points site S hS c.pt.left.1) :=
    ⟨⋃ a, Set.range (pointsMap site S hS (U a).1 (g a).hom),
      isOpen_iUnion hopen_range⟩
  let e := openSubspacesOrderIso site S hS c.pt.left.1 c.pt.left.property
  let W : OpenSubspaces site S hS c.pt.left.1 := e.symm V
  have hWrange : V.1 =
      Set.range (pointsMap site S hS W.1.toFunctor W.1.ι) := by
    have heW : e W = V := e.apply_symm_apply V
    rw [← heW]
    exact openSubspacesOrderIso_apply site S hS c.pt.left.1 c.pt.left.property W
  have hfactor (i : I) : ∃ m : (D.obj i).left ⟶
      ⟨W.1.toFunctor, W.2.1⟩,
      m ≫ ObjectProperty.homMk W.1.ι = (c.ι.app i).left := by
    obtain ⟨m, hm⟩ :=
      (factorsThrough_openSubspace_iff_points site S hS
        c.pt.left.property (D.obj i).left.property W.1 W.2
        (c.ι.app i).left.hom).2 (by
          intro z hz
          obtain ⟨x, rfl⟩ := hz
          obtain ⟨a, y, hy⟩ := hcover i x
          have hV : pointsMap site S hS (D.obj i).left.1
              (c.ι.app i).left.hom x ∈ V.1 := by
            show pointsMap site S hS (D.obj i).left.1
                (c.ι.app i).left.hom x ∈
              ⋃ a, Set.range (pointsMap site S hS (U a).1 (g a).hom)
            exact Set.mem_iUnion.mpr ⟨a, Set.mem_range.mpr ⟨y, hy⟩⟩
          rw [hWrange] at hV
          exact hV)
    exact ⟨ObjectProperty.homMk m, ObjectProperty.hom_ext _ hm⟩
  let maps : ∀ i, (D.obj i).left ⟶ ⟨W.1.toFunctor, W.2.1⟩ :=
    fun i => Classical.choose (hfactor i)
  have hmaps' (i : I) : maps i ≫ ObjectProperty.homMk W.1.ι =
      (c.ι.app i).left := Classical.choose_spec (hfactor i)
  have hWtop : W.1 = ⊤ :=
    open_subspace_eq_top_of_cocone_maps_factor site S hS c h₁ W maps hmaps'
  have hW : e.symm ⊤ ≤ W := by
    show (e.symm ⊤).1 ≤ W.1
    rw [hWtop]
    exact le_top
  have hVtop : V = ⊤ := by
    apply top_unique
    calc
      ⊤ = e (e.symm ⊤) := (e.apply_symm_apply ⊤).symm
      _ ≤ e W := e.monotone hW
      _ = V := e.apply_symm_apply V
  have hsurj : ∀ x : points site S hS c.pt.left.1,
      ∃ a, ∃ y : points site S hS (U a).1,
        pointsMap site S hS (U a).1 (g a).hom y = x := by
    intro x
    have hx : x ∈ V.1 := by rw [hVtop]; exact Set.mem_univ x
    rcases Set.mem_iUnion.mp hx with ⟨a, ha⟩
    exact ⟨a, Set.mem_range.mp ha⟩
  exact ⟨hsurj,
    etale_family_fpqc_of_points_surjective site S hS U g hg hsurj⟩

/-- A family of realizations whose members cover the diagram on points covers the vertex of
the cocone on points, and is an fpqc covering of it. -/
private lemma realizations_cover_of_compatible_cover
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (c : Cocone D) (h₁ : EtaleComparisonIsEquivalence site S hS c)
    {A : Type u}
    (E : A → CompatibleEtaleDiagram site S hS D)
    (r : ∀ a, EtaleRealization site S hS c (E a))
    (hcover : ∀ (i : I) (x : points site S hS (D.obj i).left.1),
      ∃ a, ∃ y : points site S hS ((E a).U.obj i).1,
        pointsMap site S hS ((E a).U.obj i).1
          ((E a).projection.app i).hom y = x) :
    (∀ x : points site S hS c.pt.left.1,
      ∃ a, ∃ y : points site S hS (r a).U.1,
        pointsMap site S hS (r a).U.1 (r a).toX.hom y = x) ∧
      IsFpqcCovering site S hS (fun a => (r a).toX.hom) := by
  have hcover' : ∀ (i : I) (x : points site S hS (D.obj i).left.1),
      ∃ a, ∃ y : points site S hS (r a).U.1,
        pointsMap site S hS (r a).U.1 (r a).toX.hom y =
          pointsMap site S hS (D.obj i).left.1
            (c.ι.app i).left.hom x := by
    intro i x
    obtain ⟨a, y, hy⟩ := hcover i x
    refine ⟨a, pointsMap site S hS ((E a).U.obj i).1
      ((r a).baseChange.app i).hom y, ?_⟩
    have hleft := congrFun (pointsMap_comp site S hS ((E a).U.obj i).1
      ((r a).baseChange.app i).hom (r a).toX.hom) y
    have hright := congrFun (pointsMap_comp site S hS ((E a).U.obj i).1
      ((E a).projection.app i).hom ((c.ι.app i).left.hom)) y
    calc
      pointsMap site S hS (r a).U.1 (r a).toX.hom
          (pointsMap site S hS ((E a).U.obj i).1
            ((r a).baseChange.app i).hom y) =
          pointsMap site S hS ((E a).U.obj i).1
            (((r a).baseChange.app i).hom ≫ (r a).toX.hom) y := hleft.symm
      _ = pointsMap site S hS ((E a).U.obj i).1
            (((E a).projection.app i).hom ≫ (c.ι.app i).left.hom) y := by
          have hover := congrArg (fun f => f.hom) ((r a).overX i)
          change ((E a).projection.app i).hom ≫ (c.ι.app i).left.hom =
            ((r a).baseChange.app i).hom ≫ (r a).toX.hom at hover
          rw [← hover]
      _ = pointsMap site S hS (D.obj i).left.1
            ((c.ι.app i).left.hom)
            (pointsMap site S hS ((E a).U.obj i).1
              ((E a).projection.app i).hom y) := hright
      _ = pointsMap site S hS (D.obj i).left.1
            ((c.ι.app i).left.hom) x := by rw [hy]
  exact etale_family_covers_of_cocone_basechange_cover site S hS c h₁
    (fun a => (r a).U) (fun a => (r a).toX)
    (fun a => (r a).etale) hcover'

/-- Realizations of the base changes of an étale family covering a cocone on points cover the
vertex of the cocone on points, and form an fpqc covering of it. -/
private lemma pullback_realizations_cover
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (c : Cocone D) (h₁ : EtaleComparisonIsEquivalence site S hS c)
    (Y : AlgebraicSpaces site S hS)
    (η : D ⋙ Over.forget B ⟶ (Functor.const I).obj Y)
    {A : Type u} (Z : A → AlgebraicSpaces site S hS)
    (z : ∀ a, Z a ⟶ Y)
    (hz : ∀ a, IsEtale site S hS (z a).hom)
    (hsurj : ∀ (i : I) (x : points site S hS (D.obj i).left.1),
      ∃ a, ∃ y : points site S hS (Z a).1,
        pointsMap site S hS (Z a).1 (z a).hom y =
          pointsMap site S hS (D.obj i).left.1 (η.app i).hom x)
    (r : ∀ a, EtaleRealization site S hS c
      (pullbackEtaleDiagram site S hS Y (Z a) η (z a) (hz a)).diagram) :
    (∀ x : points site S hS c.pt.left.1,
      ∃ a, ∃ y : points site S hS (r a).U.1,
        pointsMap site S hS (r a).U.1 (r a).toX.hom y = x) ∧
      IsFpqcCovering site S hS (fun a => (r a).toX.hom) := by
  apply realizations_cover_of_compatible_cover site S hS c h₁
    (fun a => (pullbackEtaleDiagram site S hS Y (Z a) η (z a) (hz a)).diagram) r
  intro i x
  obtain ⟨a, y, hy⟩ := hsurj i x
  obtain ⟨wp, hw₁, hw₂⟩ := exists_point_of_isPullback site S hS
    ((pullbackEtaleDiagram site S hS Y (Z a) η (z a) (hz a)).isPullback i)
    x y (by simpa using hy.symm)
  refine ⟨a, wp, ?_⟩
  simpa using hw₁

/-! ### Globalizing the descent -/

section Globalization

variable {site S hS}

/-- A family of morphisms of algebraic spaces with common target is jointly surjective when
every point of the target is the image of a point of some member. -/
private abbrev JointlySurjective {A : Type u} {X : AlgebraicSpaces site S hS}
    {U : A → AlgebraicSpaces site S hS} (p : ∀ a, U a ⟶ X) :=
  ∀ x : points site S hS X.1, ∃ a,
    ∃ y : points site S hS (U a).1,
      pointsMap site S hS (U a).1 (p a).hom y = x

/-- Every algebraic space has a jointly surjective étale family of affine algebraic spaces
over it. -/
private lemma affine_cover (X : AlgebraicSpaces site S hS) :
    ∃ (A : Type u) (U : A → AlgebraicSpaces site S hS) (p : ∀ a, U a ⟶ X),
      (∀ a, IsAffineSpace site S hS (U a).1) ∧
      (∀ a, IsEtale site S hS (p a).hom) ∧ JointlySurjective p := by
  obtain ⟨A, V, p, hV, hp⟩ := exists_affine_etale_covering site S hS X.1 X.2
  refine ⟨A, fun a => ⟨yoneda.obj (V a), hp.source_isAlgebraicSpace a⟩,
    fun a => ObjectProperty.homMk (p a), fun a => ⟨V a, hV a, ⟨Iso.refl _⟩⟩, hp.etale,
    fun x => ?_⟩
  have hx : x ∈ ⋃ a, Set.range (pointsMap site S hS (yoneda.obj (V a)) (p a)) := by
    rw [hp.jointly_surjective]
    trivial
  simpa only [Set.mem_iUnion, Set.mem_range, ObjectProperty.homMk_hom] using hx

variable {I : Type v} [Category.{w} I] {B : AlgebraicSpaces site S hS}
  {D : I ⥤ Over B}

/-- The legs of a cocone of algebraic spaces over `B`, as morphisms of algebraic spaces. -/
private abbrev coconeLegs (c : Cocone D) : D ⋙ Over.forget B ⟶
    (Functor.const I).obj c.pt.left := ((Over.forget B).mapCocone c).ι

/-- A cocone leg is a morphism over `B`. -/
private lemma cocone_w (c : Cocone D) (i : I) :
    (c.ι.app i).left ≫ c.pt.hom = (D.obj i).hom := (c.ι.app i).w

/-- The morphism to a fibre product induced by a pair of natural transformations to the two
factors agreeing over the base. -/
private noncomputable def pullbackNatTrans
    {X Y Z W : AlgebraicSpaces site S hS}
    {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}
    (hp : IsPullback p q f g)
    {U : I ⥤ AlgebraicSpaces site S hS}
    (α : U ⟶ (Functor.const I).obj X) (β : U ⟶ (Functor.const I).obj Y)
    (h : ∀ i, α.app i ≫ f = β.app i ≫ g) : U ⟶ (Functor.const I).obj W where
  app i := hp.lift (α.app i) (β.app i) (h i)
  naturality {i j} a := by
    apply hp.hom_ext
    · simpa only [Category.assoc, IsPullback.lift_fst, Functor.const_obj_map,
        Functor.const_obj_obj, Category.id_comp, Category.comp_id] using α.naturality a
    · simpa only [Category.assoc, IsPullback.lift_snd, Functor.const_obj_map,
        Functor.const_obj_obj, Category.id_comp, Category.comp_id] using β.naturality a

/-- An étale algebraic space over the vertex of a cocone, realizing the compatible family
obtained by base changing it along the cocone legs. -/
private noncomputable abbrev canonicalRealization (c : Cocone D)
    (V : AlgebraicSpaces site S hS)
    (p : V ⟶ c.pt.left) (hp : IsEtale site S hS p.hom) :
    EtaleRealization site S hS c
      (pullbackEtaleDiagram site S hS c.pt.left V (coconeLegs c) p hp).diagram where
  U := V
  toX := p
  etale := hp
  baseChange := (pullbackEtaleDiagram site S hS c.pt.left V (coconeLegs c) p hp).second
  overX i := (pullbackEtaleDiagram site S hS c.pt.left V
    (coconeLegs c) p hp).isPullback i |>.w
  isPullback i := (pullbackEtaleDiagram site S hS c.pt.left V
    (coconeLegs c) p hp).isPullback i

/-- A natural transformation to the total space of a realization, compatible with the
morphisms to the vertex, lifts to a morphism of compatible families. -/
private noncomputable abbrev liftToRealization {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (s : EtaleRealization site S hS c F)
    (t : E.U ⟶ (Functor.const I).obj s.U)
    (ht : ∀ i, t.app i ≫ s.toX = E.projection.app i ≫ (c.ι.app i).left) :
    E.U ⟶ F.U where
  app i := (s.isPullback i).lift (E.projection.app i) (t.app i) (ht i).symm
  naturality {i j} a := by
    apply (s.isPullback j).hom_ext
    · simp only [Category.assoc, IsPullback.lift_fst, F.projection.naturality,
        IsPullback.lift_fst_assoc]
      exact E.projection.naturality a
    · simp only [Category.assoc, IsPullback.lift_snd,
        s.baseChange.naturality, Functor.const_obj_map, Functor.const_obj_obj,
        Category.comp_id]
      exact t.naturality a

/-- The lift of a natural transformation to a realization is a morphism of families over the
diagram. -/
private lemma liftToRealization_projection {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (s : EtaleRealization site S hS c F)
    (t : E.U ⟶ (Functor.const I).obj s.U)
    (ht : ∀ i, t.app i ≫ s.toX = E.projection.app i ≫ (c.ι.app i).left) :
    liftToRealization s t ht ≫ F.projection = E.projection :=
  NatTrans.ext <| funext fun i => (s.isPullback i).lift_fst _ _ _

/-- The lift of a natural transformation to a realization recovers that transformation on the
base change identifications. -/
private lemma liftToRealization_baseChange {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (s : EtaleRealization site S hS c F)
    (t : E.U ⟶ (Functor.const I).obj s.U)
    (ht : ∀ i, t.app i ≫ s.toX = E.projection.app i ≫ (c.ι.app i).left)
    (i : I) : (liftToRealization s t ht).app i ≫ s.baseChange.app i = t.app i :=
  (s.isPullback i).lift_snd _ _ _

/-- The morphism of compatible families induced by a morphism of their realizations over the
vertex of the cocone. -/
private noncomputable abbrev realizationMap {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    (f : r.U ⟶ s.U) (hf : f ≫ s.toX = r.toX) : E.U ⟶ F.U :=
  liftToRealization s (r.baseChange ≫ (Functor.const I).map f) (by
    intro i
    change (r.baseChange.app i ≫ f) ≫ s.toX = _
    rw [Category.assoc, hf]
    exact (r.overX i).symm)

/-- The morphism of families induced by a morphism of realizations is a morphism over the
diagram. -/
private lemma realizationMap_projection {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    (f : r.U ⟶ s.U) (hf : f ≫ s.toX = r.toX) :
    realizationMap r s f hf ≫ F.projection = E.projection :=
  liftToRealization_projection s _ _

/-- The morphism of families induced by a morphism of realizations is compatible with the
base change identifications. -/
private lemma realizationMap_baseChange {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    (f : r.U ⟶ s.U) (hf : f ≫ s.toX = r.toX) (i : I) :
    (realizationMap r s f hf).app i ≫ s.baseChange.app i =
      r.baseChange.app i ≫ f :=
  liftToRealization_baseChange s _ _ i

/-- `realizationMap_baseChange`, with a further morphism composed on the right. -/
private lemma realizationMap_baseChange_assoc {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    (f : r.U ⟶ s.U) (hf : f ≫ s.toX = r.toX) (i : I) {Y : AlgebraicSpaces site S hS}
    (k : s.U ⟶ Y) :
    (realizationMap r s f hf).app i ≫ s.baseChange.app i ≫ k = r.baseChange.app i ≫ f ≫ k := by
  rw [← Category.assoc, realizationMap_baseChange, Category.assoc]

/-- Two morphisms of realizations over the vertex of the cocone which agree on the base
change identifications are equal, by full faithfulness of the comparison. -/
private lemma realization_hom_ext_over {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c)
    {E F : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    {f g : r.U ⟶ s.U} (hf : f ≫ s.toX = r.toX) (hg : g ≫ s.toX = r.toX)
    (h : ∀ i, r.baseChange.app i ≫ f = r.baseChange.app i ≫ g) : f = g :=
  (h₁.fullyFaithful E F r s (realizationMap r s f hf)
    (realizationMap_projection r s f hf)).unique
    ⟨hf, fun i => (realizationMap_baseChange r s f hf i).symm⟩
    ⟨hg, fun i => (h i).symm.trans (realizationMap_baseChange r s f hf i).symm⟩

/-- A natural transformation from a compatible family to the total space of a realization,
compatible with the morphisms to the vertex, descends to a morphism of realizations. -/
private lemma realization_lift {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c)
    {E F : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    (t : E.U ⟶ (Functor.const I).obj s.U)
    (ht : ∀ i, t.app i ≫ s.toX = E.projection.app i ≫ (c.ι.app i).left) :
    ∃ f : r.U ⟶ s.U, f ≫ s.toX = r.toX ∧
      ∀ i, r.baseChange.app i ≫ f = t.app i := by
  obtain ⟨f, hf, _⟩ := h₁.fullyFaithful E F r s _ (liftToRealization_projection s t ht)
  exact ⟨f, hf.1, fun i => (hf.2 i).trans (liftToRealization_baseChange s t ht i)⟩

/-- The square comparing a morphism of realizations with the induced morphism of families is
cartesian. -/
private lemma realizationMap_isPullback {c : Cocone D}
    {E F : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    (f : r.U ⟶ s.U) (hf : f ≫ s.toX = r.toX) (i : I) :
    IsPullback ((realizationMap r s f hf).app i) (r.baseChange.app i)
      (s.baseChange.app i) f := by
  apply IsPullback.of_right (t := s.isPullback i)
  · show IsPullback (((realizationMap r s f hf).app i) ≫ F.projection.app i)
      (r.baseChange.app i) (c.ι.app i).left (f ≫ s.toX)
    rw [IsPullback.lift_fst, hf]
    exact r.isPullback i
  · exact realizationMap_baseChange r s f hf i

/-- Two morphisms from a realization to an affine space over an affine étale base which agree
over that base and on the base change identifications are equal: pass to an affine étale cover
of the realization, where the affine descent condition applies. -/
private lemma affine_target_hom_ext {c : Cocone D}
    (h₂ : AffineDescent site S hS c)
    {E : CompatibleEtaleDiagram site S hS D} (r : EtaleRealization site S hS c E)
    {B' Z : AlgebraicSpaces site S hS} (b : B' ⟶ B)
    (hb : IsAffineSpace site S hS B'.1)
    (hbe : IsEtale site S hS b.hom) (z : Z ⟶ B')
    (hZ : IsAffineSpace site S hS Z.1)
    {f g : r.U ⟶ Z}
    (hf : f ≫ z ≫ b = r.toX ≫ c.pt.hom) (hg : f ≫ z = g ≫ z)
    (hi : ∀ i, r.baseChange.app i ≫ f = r.baseChange.app i ≫ g) : f = g := by
  obtain ⟨A, V, p, hV, hp, hcover⟩ := affine_cover r.U
  apply hom_ext_of_fpqc_covering site S hS V p
    (etale_family_fpqc_of_points_surjective site S hS V p hp hcover)
  intro a
  let s := canonicalRealization c (V a) (p a ≫ r.toX)
    (isEtale_comp site S hS (hp a) r.etale)
  apply affine_realization_hom_ext site S hS c h₂ b hb hbe Z z hZ _ s (hV a)
    (p a ≫ f ≫ z)
  · simpa only [s, canonicalRealization, Category.assoc] using
      (congrArg (fun k => p a ≫ k) hf).symm
  · simp only [Category.assoc]
  · simpa only [Category.assoc] using congrArg (fun k => p a ≫ k) hg.symm
  · intro i
    simp only [← realizationMap_baseChange_assoc s r (p a) rfl i, hi]

/-- A cocone of morphisms from a compatible family to an algebraic space étale over `B`
descends uniquely to a morphism from a realization: the base change of the vertex along the
étale morphism is realized, and the comparison is fully faithful. -/
private lemma etale_target_desc {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c)
    {E : CompatibleEtaleDiagram site S hS D} (r : EtaleRealization site S hS c E)
    {B' : AlgebraicSpaces site S hS} (b : B' ⟶ B) (hb : IsEtale site S hS b.hom)
    (t : E.U ⟶ (Functor.const I).obj B')
    (ht : ∀ i, t.app i ≫ b = E.projection.app i ≫ (D.obj i).hom) :
    ∃! f : r.U ⟶ B', (f ≫ b = r.toX ≫ c.pt.hom) ∧
      ∀ i, r.baseChange.app i ≫ f = t.app i := by
  let W := pullback c.pt.hom b
  let p : W ⟶ c.pt.left := pullback.fst _ _
  let q : W ⟶ B' := pullback.snd _ _
  have hw : IsPullback p q c.pt.hom b := IsPullback.of_hasPullback _ _
  have hp : IsEtale site S hS p.hom :=
    isEtale_of_isPullback site S hS q p b c.pt.hom hw.flip hb
  let s := canonicalRealization c W p hp
  let l : E.U ⟶ (Functor.const I).obj W :=
    pullbackNatTrans hw (E.projection ≫ coconeLegs c) t (by
      intro i
      simpa only [NatTrans.comp_app, coconeLegs, Functor.mapCocone_ι_app,
        Over.forget_map, Category.assoc, cocone_w c i] using (ht i).symm)
  obtain ⟨f, hf, hfi⟩ := realization_lift h₁ r s l (fun i => hw.lift_fst _ _ _)
  refine ⟨f ≫ q, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hw.w, ← Category.assoc, hf]
  · intro i
    rw [← Category.assoc, hfi]
    exact hw.lift_snd _ _ _
  · intro g hg
    let k := hw.lift r.toX g hg.1.symm
    have hk : k = f := by
      apply realization_hom_ext_over h₁ r s (hw.lift_fst _ _ _) hf
      intro i
      rw [hfi]
      apply hw.hom_ext
      · simpa only [Category.assoc, k, IsPullback.lift_fst, l, pullbackNatTrans,
          NatTrans.comp_app, Functor.const_map_app, coconeLegs,
          Functor.mapCocone_ι_app, Over.forget_map] using (r.overX i).symm
      · simpa only [Category.assoc, k, IsPullback.lift_snd, l, pullbackNatTrans,
          NatTrans.comp_app, Functor.const_map_app] using hg.2 i
    exact (hw.lift_snd r.toX g hg.1.symm).symm.trans (congrArg (fun k => k ≫ q) hk)

/-- Two morphisms from a realization to an algebraic space étale over `B` which agree over `B`
and on the base change identifications are equal. -/
private lemma etale_target_hom_ext {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c)
    {E : CompatibleEtaleDiagram site S hS D} (r : EtaleRealization site S hS c E)
    {B' : AlgebraicSpaces site S hS} (b : B' ⟶ B) (hb : IsEtale site S hS b.hom)
    {f g : r.U ⟶ B'} (hf : f ≫ b = r.toX ≫ c.pt.hom)
    (hg : g ≫ b = r.toX ≫ c.pt.hom)
    (hi : ∀ i, r.baseChange.app i ≫ f = r.baseChange.app i ≫ g) : f = g := by
  let t := r.baseChange ≫ (Functor.const I).map f
  have ht i : t.app i ≫ b = E.projection.app i ≫ (D.obj i).hom := by
    dsimp [t]
    rw [Category.assoc, hf, ← Category.assoc, ← r.overX, Category.assoc, cocone_w c i]
  exact (etale_target_desc h₁ r b hb t ht).unique ⟨hf, fun _ => rfl⟩
    ⟨hg, fun i => (hi i).symm⟩

/-- An affine étale chart of an algebraic space over `B`, together with an affine étale chart
of `B` through which it factors. -/
private structure AffineBaseChart {Y : AlgebraicSpaces site S hS} (y : Y ⟶ B) where
  /-- The affine étale chart of the base. -/
  base : AlgebraicSpaces site S hS
  /-- Its structure morphism to the base. -/
  toBase : base ⟶ B
  /-- The chart of the base is affine. -/
  base_affine : IsAffineSpace site S hS base.1
  /-- The chart of the base is étale. -/
  base_etale : IsEtale site S hS toBase.hom
  /-- The affine étale chart of the space. -/
  source : AlgebraicSpaces site S hS
  /-- Its structure morphism to the space. -/
  map : source ⟶ Y
  /-- The chart of the space is affine. -/
  source_affine : IsAffineSpace site S hS source.1
  /-- The chart of the space is étale. -/
  map_etale : IsEtale site S hS map.hom
  /-- The factorization of the chart through the chart of the base. -/
  structureMap : source ⟶ base
  /-- The factorization is compatible with the structure morphisms to the base. -/
  comm : map ≫ y = structureMap ≫ toBase

/-- An algebraic space over `B` is covered, jointly surjectively, by affine étale charts each
factoring through an affine étale chart of `B`. -/
private lemma affine_base_charts {Y : AlgebraicSpaces site S hS} (y : Y ⟶ B) :
    ∃ (A : Type u) (C : A → AffineBaseChart y),
      JointlySurjective (fun a => (C a).map) := by
  classical
  obtain ⟨A, V, b, hV, hb, hs⟩ := affine_cover B
  let W a := pullback y (b a)
  let p a : W a ⟶ Y := pullback.fst _ _
  let q a : W a ⟶ V a := pullback.snd _ _
  have hw a : IsPullback (p a) (q a) y (b a) := IsPullback.of_hasPullback _ _
  choose J Z z hZ hz hsurj using (fun a => affine_cover (W a))
  let C : (a : A) → J a → AffineBaseChart y := fun a j =>
    { base := V a, toBase := b a, base_affine := hV a, base_etale := hb a,
      source := Z a j, map := z a j ≫ p a, source_affine := hZ a j,
      map_etale := isEtale_comp site S hS (hz a j)
        (isEtale_of_isPullback site S hS (q a) (p a) (b a) y (hw a).flip (hb a)),
      structureMap := z a j ≫ q a,
      comm := by
        simpa only [Category.assoc] using congrArg (fun k => z a j ≫ k) (hw a).w }
  refine ⟨Σ a, J a, fun a => C a.1 a.2, ?_⟩
  intro x
  obtain ⟨a, v, hv⟩ := hs (pointsMap site S hS Y.1 y.hom x)
  obtain ⟨wp, hw₁, _⟩ := exists_point_of_isPullback site S hS (hw a) x v hv.symm
  obtain ⟨j, t, ht⟩ := hsurj a wp
  refine ⟨⟨a, j⟩, t, ?_⟩
  show pointsMap site S hS (Z a j).1 ((z a j).hom ≫ (p a).hom) t = x
  rw [pointsMap_comp]
  show pointsMap site S hS (W a).1 (p a).hom
    (pointsMap site S hS (Z a j).1 (z a j).hom t) = x
  rw [ht, hw₁]

/-- The base change of a jointly surjective family along a morphism is jointly surjective. -/
private lemma pullback_cover {A : Type u} {X T : AlgebraicSpaces site S hS}
    {V : A → AlgebraicSpaces site S hS}
    (p : ∀ a, V a ⟶ X) (hp : JointlySurjective p) (f : T ⟶ X)
    (W : A → AlgebraicSpaces site S hS) (q : ∀ a, W a ⟶ T) (s : ∀ a, W a ⟶ V a)
    (hw : ∀ a, IsPullback (q a) (s a) f (p a)) : JointlySurjective q := by
  intro x
  obtain ⟨a, v, hv⟩ := hp (pointsMap site S hS T.1 f.hom x)
  obtain ⟨wp, h, _⟩ := exists_point_of_isPullback site S hS (hw a) x v hv.symm
  exact ⟨a, wp, h⟩

/-- Two morphisms out of an algebraic space agreeing after base change along a jointly
surjective étale family are equal. -/
private lemma hom_ext_pullback_cover {A : Type u}
    {X T Y : AlgebraicSpaces site S hS} {V : A → AlgebraicSpaces site S hS}
    (p : ∀ a, V a ⟶ X) (hp : ∀ a, IsEtale site S hS (p a).hom)
    (hs : JointlySurjective p)
    (f : T ⟶ X) (W : A → AlgebraicSpaces site S hS)
    (q : ∀ a, W a ⟶ T) (s : ∀ a, W a ⟶ V a)
    (hw : ∀ a, IsPullback (q a) (s a) f (p a))
    {g h : T ⟶ Y} (heq : ∀ a, q a ≫ g = q a ≫ h) : g = h :=
  hom_ext_of_fpqc_covering site S hS W q
    (etale_family_fpqc_of_points_surjective site S hS W q
      (fun a => isEtale_of_isPullback site S hS (s a) (q a) (p a) f (hw a).flip (hp a))
      (pullback_cover p hs f W q s hw)) heq

/-- Composing morphisms of realizations composes the induced morphisms of families. -/
private lemma realizationMap_comp {c : Cocone D}
    {E F G : CompatibleEtaleDiagram site S hS D}
    (r : EtaleRealization site S hS c E) (s : EtaleRealization site S hS c F)
    (t : EtaleRealization site S hS c G)
    (f : r.U ⟶ s.U) (g : s.U ⟶ t.U)
    (hf : f ≫ s.toX = r.toX) (hg : g ≫ t.toX = s.toX) (i : I) :
    (realizationMap r s f hf).app i ≫ (realizationMap s t g hg).app i =
      (realizationMap r t (f ≫ g) (by rw [Category.assoc, hg, hf])).app i := by
  apply (t.isPullback i).hom_ext
  · simp only [Category.assoc, IsPullback.lift_fst]
  · simp [Category.assoc]

/-- Two morphisms from a realization to an algebraic space over `B` which agree over `B` and
on the base change identifications are equal: pass to affine étale charts of the target, where
the affine descent condition applies. -/
private lemma realization_hom_ext_target {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c) (h₂ : AffineDescent site S hS c)
    {E : CompatibleEtaleDiagram site S hS D} (r : EtaleRealization site S hS c E)
    {Y : AlgebraicSpaces site S hS} (y : Y ⟶ B) {f g : r.U ⟶ Y}
    (hf : f ≫ y = r.toX ≫ c.pt.hom) (hg : g ≫ y = r.toX ≫ c.pt.hom)
    (hi : ∀ i, r.baseChange.app i ≫ f = r.baseChange.app i ≫ g) : f = g := by
  classical
  obtain ⟨A, C, hC⟩ := affine_base_charts y
  let W a := pullback f (C a).map
  let p a : W a ⟶ r.U := pullback.fst _ _
  let q a : W a ⟶ (C a).source := pullback.snd _ _
  have hw a : IsPullback (p a) (q a) f (C a).map := IsPullback.of_hasPullback _ _
  apply hom_ext_pullback_cover (fun a => (C a).map) (fun a => (C a).map_etale)
    hC f W p q hw
  intro a
  let V := pullback g (C a).map
  let p' : V ⟶ r.U := pullback.fst _ _
  let q' : V ⟶ (C a).source := pullback.snd _ _
  have hv : IsPullback p' q' g (C a).map := IsPullback.of_hasPullback _ _
  have hp : IsEtale site S hS (p a).hom := isEtale_of_isPullback site S hS
    (q a) (p a) (C a).map f (hw a).flip (C a).map_etale
  have hp' : IsEtale site S hS p'.hom := isEtale_of_isPullback site S hS
    q' p' (C a).map g hv.flip (C a).map_etale
  let s := canonicalRealization c (W a) (p a ≫ r.toX)
    (isEtale_comp site S hS hp r.etale)
  let t := canonicalRealization c V (p' ≫ r.toX)
    (isEtale_comp site S hS hp' r.etale)
  let α := realizationMap s r (p a) rfl
  have hres i : s.baseChange.app i ≫ p a ≫ f = s.baseChange.app i ≫ p a ≫ g := by
    have hh := congrArg (fun k => α.app i ≫ k) (hi i)
    simpa [α, realizationMap, liftToRealization, Category.assoc] using hh
  let η : _ ⟶ (Functor.const I).obj V :=
    pullbackNatTrans hv (s.baseChange ≫ (Functor.const I).map (p a))
      (s.baseChange ≫ (Functor.const I).map (q a)) (by
        intro i
        simpa only [NatTrans.comp_app, Functor.const_map_app, Category.assoc] using
          (hres i).symm.trans
            (congrArg (fun k => s.baseChange.app i ≫ k) (hw a).w))
  obtain ⟨e, he, hei⟩ := realization_lift h₁ s t η (by
    intro i
    show η.app i ≫ p' ≫ r.toX = _
    rw [← Category.assoc]
    simp only [η, pullbackNatTrans, NatTrans.comp_app, Functor.const_map_app,
      IsPullback.lift_fst, Category.assoc]
    exact (s.overX i).symm)
  have hep : e ≫ p' = p a := by
    apply realization_hom_ext_over h₁ s r
    · simpa only [Category.assoc] using he
    · rfl
    · intro i
      rw [← Category.assoc, hei]
      exact hv.lift_fst _ _ _
  have heq i : s.baseChange.app i ≫ q a = s.baseChange.app i ≫ (e ≫ q') := by
    rw [← Category.assoc, hei]
    exact (hv.lift_snd _ _ _).symm
  have hqbase : q a ≫ (C a).structureMap ≫ (C a).toBase = s.toX ≫ c.pt.hom := by
    rw [← (C a).comm, ← Category.assoc, ← (hw a).w, Category.assoc, hf]
    rfl
  have hqbase' : (e ≫ q') ≫ (C a).structureMap ≫ (C a).toBase =
      s.toX ≫ c.pt.hom := by
    calc
      (e ≫ q') ≫ (C a).structureMap ≫ (C a).toBase = (e ≫ p') ≫ (g ≫ y) := by
        simp only [Category.assoc, ← (C a).comm, hv.w_assoc]
      _ = s.toX ≫ c.pt.hom := by rw [hep, hg]; rfl
  have hbase : q a ≫ (C a).structureMap = (e ≫ q') ≫ (C a).structureMap := by
    apply etale_target_hom_ext h₁ s (C a).toBase (C a).base_etale
    · simpa only [Category.assoc] using hqbase
    · simpa only [Category.assoc] using hqbase'
    · intro i
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ (C a).structureMap) (heq i)
  have hq : q a = e ≫ q' := affine_target_hom_ext h₂ s (C a).toBase
    (C a).base_affine (C a).base_etale (C a).structureMap (C a).source_affine
    hqbase hbase heq
  calc
    p a ≫ f = q a ≫ (C a).map := (hw a).w
    _ = e ≫ q' ≫ (C a).map := by rw [hq, Category.assoc]
    _ = e ≫ p' ≫ g := by rw [← hv.w]
    _ = p a ≫ g := by rw [← Category.assoc, hep]

/-- Morphisms from the members of a jointly surjective étale family of realizations to an
algebraic space over `B`, compatible with a cocone of morphisms out of the given family, glue
to a single morphism: they agree on the fibre products by the uniqueness just proved. -/
private lemma realization_glue {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c) (h₂ : AffineDescent site S hS c)
    {E : CompatibleEtaleDiagram site S hS D} (r : EtaleRealization site S hS c E)
    {Y : AlgebraicSpaces site S hS} (y : Y ⟶ B)
    (η : E.U ⟶ (Functor.const I).obj Y)
    {A : Type u} (F : A → CompatibleEtaleDiagram site S hS D)
    (s : ∀ a, EtaleRealization site S hS c (F a))
    (p : ∀ a, (s a).U ⟶ r.U) (hp : ∀ a, IsEtale site S hS (p a).hom)
    (hs : JointlySurjective p) (ho : ∀ a, p a ≫ r.toX = (s a).toX)
    (q : ∀ a, (s a).U ⟶ Y)
    (hq : ∀ a, q a ≫ y = (s a).toX ≫ c.pt.hom)
    (hqi : ∀ a i, (s a).baseChange.app i ≫ q a =
      (realizationMap (s a) r (p a) (ho a)).app i ≫ η.app i) :
    ∃ f : r.U ⟶ Y, (f ≫ y = r.toX ≫ c.pt.hom) ∧
      ∀ i, r.baseChange.app i ≫ f = η.app i := by
  have hcover := etale_family_fpqc_of_points_surjective site S hS
    (fun a => (s a).U) p hp hs
  have hcompat (a b : A) :
      (ObjectProperty.homMk (pullback.fst (p a).hom (p b).hom) :
        AlgebraicSpaces.fiberProduct site S hS (p a) (p b) ⟶ (s a).U) ≫ q a =
      (ObjectProperty.homMk (pullback.snd (p a).hom (p b).hom) :
        AlgebraicSpaces.fiberProduct site S hS (p a) (p b) ⟶ (s b).U) ≫ q b := by
    let W := AlgebraicSpaces.fiberProduct site S hS (p a) (p b)
    let p₁ : W ⟶ (s a).U := ObjectProperty.homMk (pullback.fst (p a).hom (p b).hom)
    let p₂ : W ⟶ (s b).U := ObjectProperty.homMk (pullback.snd (p a).hom (p b).hom)
    have hw : IsPullback p₁ p₂ (p a) (p b) :=
      AlgebraicSpaces.isPullback_fiberProduct site S hS (p a) (p b)
    have hp₁ : IsEtale site S hS p₁.hom := isEtale_of_isPullback site S hS
      p₂ p₁ (p b) (p a) hw.flip (hp b)
    let t := canonicalRealization c W (p₁ ≫ (s a).toX)
      (isEtale_comp site S hS hp₁ (s a).etale)
    have ht₂ : p₂ ≫ (s b).toX = t.toX := by
      show p₂ ≫ (s b).toX = p₁ ≫ (s a).toX
      rw [← ho a, ← ho b, ← Category.assoc, ← Category.assoc, hw.w]
    apply realization_hom_ext_target h₁ h₂ t y
    · show (p₁ ≫ q a) ≫ y = (p₁ ≫ (s a).toX) ≫ c.pt.hom
      rw [Category.assoc, hq, Category.assoc]
    · show (p₂ ≫ q b) ≫ y = t.toX ≫ c.pt.hom
      rw [Category.assoc, hq, ← Category.assoc, ht₂]
    · intro i
      let α := realizationMap t (s a) p₁ rfl
      let β := realizationMap t (s b) p₂ ht₂
      have hm : α.app i ≫ (realizationMap (s a) r (p a) (ho a)).app i =
          β.app i ≫ (realizationMap (s b) r (p b) (ho b)).app i := by
        have hfa : (p₁ ≫ p a) ≫ r.toX = t.toX := by rw [Category.assoc, ho]
        have hfb : (p₂ ≫ p b) ≫ r.toX = t.toX := by
          rw [Category.assoc, ho]
          exact ht₂
        have hmid : (realizationMap t r (p₁ ≫ p a) hfa).app i =
            (realizationMap t r (p₂ ≫ p b) hfb).app i := by
          congr 2
          exact hw.w
        exact (realizationMap_comp t (s a) r p₁ (p a) rfl (ho a) i).trans
          (hmid.trans (realizationMap_comp t (s b) r p₂ (p b) ht₂ (ho b) i).symm)
      rw [← realizationMap_baseChange_assoc t (s a) p₁ rfl i,
        ← realizationMap_baseChange_assoc t (s b) p₂ ht₂ i, hqi, hqi,
        ← Category.assoc, hm, Category.assoc]
  obtain ⟨f, hf, _⟩ :=
    existsUnique_desc_of_fpqcCovering site S hS p hcover Y q hcompat
  refine ⟨f, ?_, ?_⟩
  · apply hom_ext_of_fpqc_covering site S hS (fun a => (s a).U) p hcover
    intro a
    rw [← Category.assoc, hf, hq, ← ho, Category.assoc]
  · intro i
    apply hom_ext_pullback_cover p hp hs (r.baseChange.app i)
      (fun a => (F a).U.obj i)
      (fun a => (realizationMap (s a) r (p a) (ho a)).app i)
      (fun a => (s a).baseChange.app i)
      (fun a => realizationMap_isPullback (s a) r (p a) (ho a) i)
    intro a
    rw [realizationMap_baseChange_assoc (s a) r (p a) (ho a), hf, hqi]

/-- A cocone of morphisms from a compatible family to an affine space over an affine étale
base descends to a morphism from a realization: it descends on an affine étale cover of the
realization by the affine descent condition, and those descents glue. -/
private lemma affine_target_desc {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c) (h₂ : AffineDescent site S hS c)
    {E : CompatibleEtaleDiagram site S hS D} (r : EtaleRealization site S hS c E)
    {B' Z : AlgebraicSpaces site S hS} (b : B' ⟶ B)
    (hb : IsAffineSpace site S hS B'.1) (hbe : IsEtale site S hS b.hom)
    (z : Z ⟶ B') (hZ : IsAffineSpace site S hS Z.1)
    (u : r.U ⟶ B') (hu : u ≫ b = r.toX ≫ c.pt.hom)
    (η : E.U ⟶ (Functor.const I).obj Z)
    (hη : ∀ i, η.app i ≫ z = r.baseChange.app i ≫ u) :
    ∃ f : r.U ⟶ Z, (f ≫ z ≫ b = r.toX ≫ c.pt.hom) ∧
      ∀ i, r.baseChange.app i ≫ f = η.app i := by
  classical
  obtain ⟨A, V, p, hV, hp, hs⟩ := affine_cover r.U
  let F a := (pullbackEtaleDiagram site S hS c.pt.left (V a) (coconeLegs c)
    (p a ≫ r.toX) (isEtale_comp site S hS (hp a) r.etale)).diagram
  let s a : EtaleRealization site S hS c (F a) :=
    canonicalRealization c (V a) (p a ≫ r.toX)
      (isEtale_comp site S hS (hp a) r.etale)
  let α a := realizationMap (s a) r (p a) rfl
  have hlocal a : ∃ q : V a ⟶ Z, q ≫ z = p a ≫ u ∧
      ∀ i, (s a).baseChange.app i ≫ q = (α a ≫ η).app i := by
    apply ExistsUnique.exists
    apply h₂ B' b hb hbe Z z hZ (F a) (s a) (hV a) (p a ≫ u)
    · simpa only [s, canonicalRealization, Category.assoc] using
        congrArg (fun k => p a ≫ k) hu.symm
    · intro i
      show (α a).app i ≫ η.app i ≫ z = _
      rw [hη, realizationMap_baseChange_assoc (s a) r (p a) rfl]
  choose q hq hqi using hlocal
  exact realization_glue h₁ h₂ r (z ≫ b) η F s p hp hs (fun a => rfl) q (fun a => by
    rw [← Category.assoc, hq, Category.assoc, hu]
    rfl) hqi

/-- Every cocone on the diagram receives a unique morphism from the given cocone: the legs of
the target cocone descend over affine étale charts of its vertex and glue. -/
private lemma cocone_desc {c : Cocone D}
    (h₁ : EtaleComparisonIsEquivalence site S hS c) (h₂ : AffineDescent site S hS c)
    (d : Cocone D) : ∃! f : c.pt ⟶ d.pt, ∀ i, c.ι.app i ≫ f = d.ι.app i := by
  classical
  let Y := d.pt.left
  let y : Y ⟶ B := d.pt.hom
  let η := coconeLegs d
  obtain ⟨A, C, hC⟩ := affine_base_charts y
  let P a := pullbackEtaleDiagram site S hS Y (C a).source η (C a).map (C a).map_etale
  let r a := (h₁.essentiallySurjective (P a).diagram).some
  have hcover := pullback_realizations_cover site S hS c h₁ Y η
    (fun a => (C a).source) (fun a => (C a).map) (fun a => (C a).map_etale)
    (fun i x => hC (pointsMap site S hS (D.obj i).left.1 (η.app i).hom x)) r
  have hlocal a : ∃ q : (r a).U ⟶ Y, q ≫ y = (r a).toX ≫ c.pt.hom ∧
      ∀ i, (r a).baseChange.app i ≫ q =
        (P a).diagram.projection.app i ≫ η.app i := by
    let t := (P a).second ≫ (Functor.const I).map (C a).structureMap
    have ht i : t.app i ≫ (C a).toBase =
        (P a).diagram.projection.app i ≫ (D.obj i).hom := by
      show ((P a).second.app i ≫ (C a).structureMap) ≫ (C a).toBase = _
      rw [Category.assoc, ← (C a).comm, ← Category.assoc, ← (P a).isPullback i |>.w,
        Category.assoc]
      show (P a).diagram.projection.app i ≫ (d.ι.app i).left ≫ y = _
      rw [cocone_w d i]
    obtain ⟨u, hu, _⟩ := etale_target_desc h₁ (r a) (C a).toBase (C a).base_etale t ht
    obtain ⟨f, hf, hfi⟩ := affine_target_desc h₁ h₂ (r a) (C a).toBase
      (C a).base_affine (C a).base_etale (C a).structureMap (C a).source_affine
      u hu.1 (P a).second (fun i => (hu.2 i).symm)
    refine ⟨f ≫ (C a).map, ?_, ?_⟩
    · rwa [Category.assoc, (C a).comm]
    · intro i
      rw [← Category.assoc, hfi]
      exact ((P a).isPullback i).w.symm
  choose q hq hqi using hlocal
  let r₀ := identityRealization site S hS c
  obtain ⟨f, hf, hfi⟩ := realization_glue h₁ h₂ r₀ y η
    (fun a => (P a).diagram) r (fun a => (r a).toX) (fun a => (r a).etale)
    hcover.1 (fun a => Category.comp_id _) q hq (by
      intro a i
      have hproj := congrArg (fun t => t.app i)
        (realizationMap_projection (r a) r₀ (r a).toX (Category.comp_id _))
      have hproj' : (realizationMap (r a) r₀ (r a).toX (Category.comp_id _)).app i =
          (P a).diagram.projection.app i := by
        simpa only [NatTrans.comp_app, identityDiagram, identityRealization,
          NatTrans.id_app, Category.comp_id] using hproj
      rw [hproj']
      exact hqi a i)
  have hf' : f ≫ d.pt.hom = c.pt.hom := by simpa [r₀, identityRealization] using hf
  refine ⟨Over.homMk f hf', fun i => Over.OverMorphism.ext (hfi i), ?_⟩
  · intro g hg
    apply Over.OverMorphism.ext
    apply realization_hom_ext_target h₁ h₂ r₀ y
    · simpa only [r₀, identityRealization, Category.id_comp] using g.w
    · exact hf
    · intro i
      exact (congrArg (fun t => t.left) (hg i)).trans (hfi i).symm

end Globalization

/-! ### The colimit criterion -/

/-- **Stacks 0GHL.** Let `B` be an algebraic space over `S`, let `D` be a diagram of algebraic
spaces over `B` and let `c` be a cocone on `D`. If base change along the cocone legs is an
equivalence from the small étale site of the vertex onto the limit of the small étale sites of
the members, and if every cocone of morphisms from the base changes of an affine étale
realization to an affine space over an affine étale base descends uniquely, then `c` is a
colimit of `D` in the category of algebraic spaces over `B`. -/
@[stacks 0GHL]
theorem isColimit_of_etale_local_affine_descent
    {I : Type v} [Category.{w} I]
    {B : AlgebraicSpaces site S hS} {D : I ⥤ Over B}
    (c : Cocone D)
    (h₁ : EtaleComparisonIsEquivalence site S hS c)
    (h₂ : ∀ (B' : AlgebraicSpaces site S hS) (b : B' ⟶ B),
      IsAffineSpace site S hS B'.1 →
      IsEtale site S hS b.hom →
      ∀ (Z : AlgebraicSpaces site S hS) (z : Z ⟶ B'),
        IsAffineSpace site S hS Z.1 →
        ∀ (E : CompatibleEtaleDiagram site S hS D)
          (r : EtaleRealization site S hS c E),
          IsAffineSpace site S hS r.U.1 →
          ∀ (u : r.U ⟶ B'),
            r.toX ≫ c.pt.hom = u ≫ b →
            ∀ (fᵢ : E.U ⟶ (Functor.const I).obj Z),
              (∀ i, fᵢ.app i ≫ z = r.baseChange.app i ≫ u) →
              ∃! f : r.U ⟶ Z,
                (f ≫ z = u) ∧
                  (∀ i, r.baseChange.app i ≫ f = fᵢ.app i)) :
    Nonempty (IsColimit c) :=
  ⟨IsColimit.ofExistsUnique (cocone_desc h₁ h₂)⟩

end AlgebraicGeometry.Space

end
