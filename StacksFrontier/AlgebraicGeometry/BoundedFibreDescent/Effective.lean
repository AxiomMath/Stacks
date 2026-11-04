module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GluingPoints
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.Descent.AffineStandardFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.OpenSubDatum
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.DegreeDecomposition
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentDatumInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent along a finite locally free morphism with bounded fibres

Let `f : X ⟶ Y` be a surjective finite locally free morphism of schemes, let `d` be a positive
integer, and assume every geometric fibre of `f` has at most `d` points. Let `V` be a scheme
over `X` in which any `d` points lying over one point of `Y` have a common affine open
neighbourhood. Then every descent datum on `V/X/Y` is effective.

The bound on the geometric fibres is then removed: it suffices that every finite collection of
points of `V` lying over one point of `Y` have a common affine open neighbourhood, because the
base decomposes into the strata on which `f` has a given degree. In particular every descent
datum along a surjective finite locally free radicial morphism is effective.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_isAffine_of_le_preimage`: a descent datum
  whose underlying scheme is affine and maps into an affine open of the base is effective. The
  base itself is not assumed affine.
* `AlgebraicGeometry.DescentDatum.exists_isTransitionInvariant_isAffineOpen_mem_le_preimage`:
  under the hypotheses above every point of `V` has an invariant affine open neighbourhood
  inside the preimage of a given affine open of `Y` containing its image.
* `AlgebraicGeometry.DescentDatum.isEffective_of_cardinalMk_geometricFibre_le`: the statement
  above.
* `AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_isAffineOpen`: a descent datum
  along a surjective finite locally free morphism is effective as soon as every finite nonempty
  collection of points of `V` lying over one point of `Y` has a common affine open
  neighbourhood. No bound on the fibres of `f` is assumed.
* `AlgebraicGeometry.DescentDatum.isEffective_of_universallyInjective`: every descent datum
  along a surjective finite locally free radicial morphism is effective.

## Implementation notes

Effectivity is local on `V`, so the base is never replaced by an affine scheme. The invariant
affine open neighbourhood of a point is produced inside the preimage of an affine open `Y₀` of
`Y`, and a scheme over `Y₀` is a scheme over `Y`; the gluing of the pieces happens over `V`,
not over `Y`. Concretely, the restricted datum is pulled back along the cartesian square of
the restriction `X ×_Y Y₀ ⟶ Y₀`, over whose affine base the ring-theoretic descent is
available, and its descended scheme composed with the inclusion of `Y₀` descends the original
datum, the two cartesian squares being pasted. The comparison morphism on the sources of the
two gluing isomorphisms is an isomorphism, and cancelling it carries the invariance of the
projection across.

The bound on the geometric fibres enters only through the bound it gives on each set-theoretic
fibre, hence on the equivalence class of a point under the groupoid attached to the datum. That
class contains the point, has at most `d` elements, and lies in a single fibre over `Y`, so the
hypothesis on `V` applies to it; the resulting affine open is shrunk into the preimage of `Y₀`
by prime avoidance for a finite subset of an affine open.

To drop the bound on the fibres one restricts the base to the stratum `Y_d` on which `f` has
degree `d`, which is open and closed, and over which the geometric fibres of `f` have at most
`d` points. Effectivity is again local on `V`, so it is enough to treat the datum restricted to
the preimage of a single stratum; that datum maps into the preimage of `Y_d`, so it is the
pullback of the datum over `Y_d`, to which the bounded case applies. The stratum being closed,
the comparison morphism from the pulled-back scheme to `V` is affine, which is what turns a
common affine open neighbourhood in `V` into one upstairs.

## References

* [Stacks Project, Tag 0CCI](https://stacks.math.columbia.edu/tag/0CCI)
* [Stacks Project, Tag 0H8K](https://stacks.math.columbia.edu/tag/0H8K)
* [Stacks Project, Tag 0H8L](https://stacks.math.columbia.edu/tag/0H8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-! ### Cardinalities of geometric fibres -/

/-- Isomorphic schemes have the same number of points. -/
private lemma cardinalMk_eq_of_schemeIso {A B : Scheme.{u}} (e : A ≅ B) :
    Cardinal.mk A = Cardinal.mk B :=
  Cardinal.mk_congr (Scheme.homeoOfIso e).toEquiv

/-- A uniform bound on the geometric fibres of `f` bounds the geometric fibres of every base
change of `f`, read as the second projection. -/
private lemma cardinalMk_geometricFibre_pullbackSnd_le {X Y V : Scheme.{u}} (f : X ⟶ Y)
    (g : V ⟶ Y) (c : Cardinal.{u})
    (h : ∀ p : GeometricPoint Y,
      Cardinal.mk (pullback p.hom f : Scheme.{u}) ≤ c)
    (p : GeometricPoint V) :
    Cardinal.mk (pullback p.hom (pullback.snd f g) : Scheme.{u}) ≤ c := by
  have e : (pullback p.hom (pullback.snd f g) : Scheme.{u}) ≅
      (pullback (p.hom ≫ g) f : Scheme.{u}) :=
    pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso f g p.hom ≪≫ pullbackSymmetry _ _
  exact (cardinalMk_eq_of_schemeIso e).le.trans (h (p.map g))

/-! ### Preimages of opens of the base -/

/-- The preimage in `V` of an open of the base `Y` is invariant under the gluing isomorphism of
a descent datum, because the gluing isomorphism commutes with the two maps to `Y`. -/
private lemma isTransitionInvariant_preimage_base {X Y : Scheme.{u}} {f : X ⟶ Y}
    (D : DescentDatum f) (Y₀ : Y.Opens) :
    D.IsTransitionInvariant ((D.over.hom ≫ f) ⁻¹ᵁ Y₀) := by
  refine D.isTransitionInvariant_of_le _ ?_
  rintro z ⟨w, hw, rfl⟩
  have h1 : D.over.hom (pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom w)) =
      pullback.snd (D.over.hom ≫ f) f w := by
    rw [← Scheme.Hom.comp_apply (pullback.snd f (D.over.hom ≫ f)) D.over.hom,
      ← Scheme.Hom.comp_apply, D.gluingPullbackIso_hom_snd () ()]
  have h2 : (D.over.hom ≫ f) (pullback.fst (D.over.hom ≫ f) f w) =
      f (pullback.snd (D.over.hom ≫ f) f w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  show (D.over.hom ≫ f)
      (pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom w)) ∈ Y₀
  rw [Scheme.Hom.comp_apply, h1, ← h2]
  exact hw

/-! ### The class of a point under the groupoid of a descent datum -/

/-- A point of a groupoid scheme lies in its own equivalence class, witnessed by the identity
arrow at it. -/
private lemma mem_target_image_source_preimage_self {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    u ∈ G.target.left.base '' (G.source.left.base ⁻¹' {u}) := by
  have hs : G.identity.left ≫ G.source.left = 𝟙 G.objects.left := by
    rw [← Over.comp_left, G.source_identity, Over.id_left]
  have ht : G.identity.left ≫ G.target.left = 𝟙 G.objects.left := by
    rw [← Over.comp_left, G.target_identity, Over.id_left]
  refine ⟨G.identity.left.base u, ?_, ?_⟩
  · show G.source.left.base (G.identity.left.base u) = u
    rw [← Scheme.Hom.comp_apply, hs]
    rfl
  · rw [← Scheme.Hom.comp_apply, ht]
    rfl

section Groupoid

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (E : DescentDatum f)

/-- The equivalence class of a point of `V` under the groupoid attached to a descent datum:
the targets of the arrows whose source is that point. -/
private def groupoidClass (v : E.over.left) : Set E.over.left :=
  (equivariantActionGroupoid (descentDatumToEquivariant E)).target.left.base ''
    ((equivariantActionGroupoid (descentDatumToEquivariant E)).source.left.base ⁻¹' {v})

/-- The target map of the groupoid of a descent datum along a finite locally free morphism is
finite locally free, being an isomorphism followed by a base change of that morphism. -/
private lemma isFiniteLocallyFree_descentDatumGroupoid_target_left [IsFiniteLocallyFree f] :
    IsFiniteLocallyFree
      (equivariantActionGroupoid (descentDatumToEquivariant E)).target.left := by
  have hiso : IsIso (descentDatumGroupoidArrowsIso E).hom := inferInstance
  have hbc : IsFiniteLocallyFree (pullback.fst (E.over.hom ≫ f) f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback (E.over.hom ≫ f) f).flip ‹_›
  have hcomp : IsFiniteLocallyFree
      ((descentDatumGroupoidArrowsIso E).hom ≫ pullback.fst (E.over.hom ≫ f) f) :=
    MorphismProperty.RespectsIso.precomp
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      (descentDatumGroupoidArrowsIso E).hom (pullback.fst (E.over.hom ≫ f) f) hbc
  rw [descentDatumGroupoid_target_left]
  exact hcomp

/-- The source map of the groupoid of a descent datum along a finite locally free morphism is
finite locally free, being two isomorphisms followed by a base change of that morphism. -/
private lemma isFiniteLocallyFree_descentDatumGroupoid_source_left [IsFiniteLocallyFree f] :
    IsFiniteLocallyFree
      (equivariantActionGroupoid (descentDatumToEquivariant E)).source.left := by
  have hiso : IsIso (descentDatumGroupoidArrowsIso E).hom := inferInstance
  have hiso2 : IsIso E.transitionPullbackIso.hom := inferInstance
  have hbc : IsFiniteLocallyFree (pullback.snd f (E.over.hom ≫ f)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f (E.over.hom ≫ f)) ‹_›
  have h1 : IsFiniteLocallyFree
      (E.transitionPullbackIso.hom ≫ pullback.snd f (E.over.hom ≫ f)) :=
    MorphismProperty.RespectsIso.precomp
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      E.transitionPullbackIso.hom (pullback.snd f (E.over.hom ≫ f)) hbc
  have h2 : IsFiniteLocallyFree ((descentDatumGroupoidArrowsIso E).hom ≫
      E.transitionPullbackIso.hom ≫ pullback.snd f (E.over.hom ≫ f)) :=
    MorphismProperty.RespectsIso.precomp
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      (descentDatumGroupoidArrowsIso E).hom
      (E.transitionPullbackIso.hom ≫ pullback.snd f (E.over.hom ≫ f)) h1
  rw [descentDatumGroupoid_source_left]
  exact h2

/-- The class of a point is covered by the fibre over it of the base change `X ×_Y V ⟶ V`,
read through the gluing isomorphism. -/
private lemma groupoidClass_subset_range (v : E.over.left) :
    groupoidClass E v ⊆
      Set.range (fun w : {w : (pullback f (E.over.hom ≫ f) : Scheme.{u}) //
          (pullback.snd f (E.over.hom ≫ f)) w = v} =>
        pullback.fst (E.over.hom ≫ f) f (E.transitionPullbackIso.inv w.1)) := by
  rintro x ⟨r, hr, rfl⟩
  have hsrc := descentDatumGroupoid_source_left_apply E r
  have htgt := descentDatumGroupoid_target_left_apply E r
  have hr' : (pullback.snd f (E.over.hom ≫ f))
      (E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r)) = v := by
    rw [← hsrc]; exact hr
  refine ⟨⟨E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r), hr'⟩, ?_⟩
  have hinv : E.transitionPullbackIso.inv
      (E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r)) =
      (descentDatumGroupoidArrowsIso E).hom r :=
    (Scheme.homeoOfIso E.transitionPullbackIso).symm_apply_apply _
  show pullback.fst (E.over.hom ≫ f) f
      (E.transitionPullbackIso.inv
        (E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r))) = _
  rw [hinv, ← htgt]

/-- All points of the class of `v` have the same image in the base as `v`. -/
private lemma comp_eq_of_mem_groupoidClass (v x : E.over.left) (hx : x ∈ groupoidClass E v) :
    (E.over.hom ≫ f) x = (E.over.hom ≫ f) v := by
  obtain ⟨r, hr, rfl⟩ := hx
  have hsrc := descentDatumGroupoid_source_left_apply E r
  have htgt := descentDatumGroupoid_target_left_apply E r
  have hr' : (pullback.snd f (E.over.hom ≫ f))
      (E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r)) = v := by
    rw [← hsrc]; exact hr
  have hfst : pullback.fst f (E.over.hom ≫ f)
        (E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r)) =
      E.over.hom
        (pullback.fst (E.over.hom ≫ f) f ((descentDatumGroupoidArrowsIso E).hom r)) := by
    rw [← Scheme.Hom.comp_apply E.transitionPullbackIso.hom (pullback.fst f (E.over.hom ≫ f)),
      E.gluingPullbackIso_hom_fst' () (), Scheme.Hom.comp_apply]
  have hcond : f (pullback.fst f (E.over.hom ≫ f)
        (E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r))) =
      (E.over.hom ≫ f) ((pullback.snd f (E.over.hom ≫ f))
        (E.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso E).hom r))) := by
    rw [← Scheme.Hom.comp_apply (pullback.fst f (E.over.hom ≫ f)) f,
      ← Scheme.Hom.comp_apply (pullback.snd f (E.over.hom ≫ f)) (E.over.hom ≫ f),
      pullback.condition]
  rw [htgt, ← hr', ← hcond, hfst, Scheme.Hom.comp_apply]

/-- If every `d` points of `V` lying over one point of `Y` have a common affine open
neighbourhood and every geometric fibre of `f` has at most `d` points, then every point of `V`
has an invariant affine open neighbourhood. -/
private lemma exists_isTransitionInvariant_isAffineOpen_mem {d : ℕ} [IsFiniteLocallyFree f]
    (hfib : ∀ p : GeometricPoint Y,
      Cardinal.mk (pullback p.hom f : Scheme.{u}) ≤ (d : Cardinal.{u}))
    (hU : ∀ (y : Y) (w : Fin d → E.over.left),
      (∀ i, (E.over.hom ≫ f) (w i) = y) →
        ∃ U : E.over.left.Opens, IsAffineOpen U ∧ ∀ i, w i ∈ U)
    (v : E.over.left) :
    ∃ W : E.over.left.Opens, E.IsTransitionInvariant W ∧ IsAffineOpen W ∧ v ∈ W := by
  classical
  have hsrc := isFiniteLocallyFree_descentDatumGroupoid_source_left E
  have htgt := isFiniteLocallyFree_descentDatumGroupoid_target_left E
  have hvT : v ∈ groupoidClass E v :=
    mem_target_image_source_preimage_self
      (equivariantActionGroupoid (descentDatumToEquivariant E)) v
  have hcard : Cardinal.mk (groupoidClass E v) ≤ (d : Cardinal.{u}) :=
    (Cardinal.mk_le_mk_of_subset (groupoidClass_subset_range E v)).trans
      (Cardinal.mk_range_le.trans
        (Stacks.Etale.cardinalMk_fibre_le (pullback.snd f (E.over.hom ≫ f)) _
          (cardinalMk_geometricFibre_pullbackSnd_le f (E.over.hom ≫ f) _ hfib) v))
  have hd' : (d : Cardinal.{u}) = Cardinal.mk (ULift.{u} (Fin d)) := by simp
  obtain ⟨emb⟩ :=
    (Cardinal.le_def (groupoidClass E v) (ULift.{u} (Fin d))).mp (hcard.trans_eq hd')
  have hne : Nonempty (groupoidClass E v) := ⟨⟨v, hvT⟩⟩
  obtain ⟨g, hgT, hgsurj⟩ :
      ∃ g : Fin d → E.over.left, (∀ i, g i ∈ groupoidClass E v) ∧
        ∀ t ∈ groupoidClass E v, ∃ i, g i = t := by
    refine ⟨fun i => ((Function.invFun emb (ULift.up i) : groupoidClass E v) : E.over.left),
      fun i => (Function.invFun emb (ULift.up i)).2, fun t ht => ⟨(emb ⟨t, ht⟩).down, ?_⟩⟩
    show ((Function.invFun emb (emb ⟨t, ht⟩) : groupoidClass E v) : E.over.left) = t
    rw [Function.leftInverse_invFun emb.injective ⟨t, ht⟩]
  obtain ⟨U, hUaff, hUmem⟩ :=
    hU ((E.over.hom ≫ f) v) g fun i => comp_eq_of_mem_groupoidClass E v (g i) (hgT i)
  have hTU : groupoidClass E v ⊆ (U : Set E.over.left) := by
    intro t ht
    obtain ⟨i, rfl⟩ := hgsurj t ht
    exact hUmem i
  obtain ⟨W, hWinv, hWaff, hWv⟩ :=
    GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem
      (equivariantActionGroupoid (descentDatumToEquivariant E)) v ⟨U, hUaff, hTU⟩
  exact ⟨W, isTransitionInvariant_of_isInvariantOpen E W hWinv, hWaff, hWv⟩

end Groupoid

/-- An invariant affine open of the datum restricted to an invariant open `V₀` pushes forward
to an invariant affine open of the datum contained in `V₀`. -/
private lemma exists_isTransitionInvariant_isAffineOpen_mem_le_of_restrict
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : DescentDatum f)
    (V₀ : D.over.left.Opens) (hV₀ : D.IsTransitionInvariant V₀)
    (W' : V₀.toScheme.Opens)
    (hW'inv : (D.restrictOpen V₀ hV₀).IsTransitionInvariant W')
    (hW'aff : IsAffineOpen W')
    (v : D.over.left) (hv : v ∈ V₀) (hW'v : (⟨v, hv⟩ : V₀.toScheme) ∈ W') :
    ∃ (W : D.over.left.Opens) (_ : D.IsTransitionInvariant W),
      v ∈ W ∧ IsAffineOpen W ∧ W ≤ V₀ := by
  refine ⟨V₀.ι ''ᵁ W', ?_, ⟨⟨v, hv⟩, hW'v, rfl⟩,
    hW'aff.image_of_isOpenImmersion V₀.ι, V₀.ι_image_le W'⟩
  have hoi : IsOpenImmersion
      ((((D.restrictOpen V₀ hV₀).restrictOpenHom W' hW'inv ≫
        D.restrictOpenHom V₀ hV₀).hom ())).left :=
    inferInstanceAs (IsOpenImmersion (W'.ι ≫ V₀.ι))
  have hinv : D.IsTransitionInvariant (Scheme.Hom.opensRange (W'.ι ≫ V₀.ι)) :=
    DescentDatum.isTransitionInvariant_opensRange
      ((D.restrictOpen V₀ hV₀).restrictOpenHom W' hW'inv ≫ D.restrictOpenHom V₀ hV₀)
  rwa [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι] at hinv

namespace DescentDatum

/-- **Invariant affine open neighbourhoods inside a chart of the base.** Let `f : X ⟶ Y` be
finite locally free with every geometric fibre of at most `d` points, and let `D` be a descent
datum relative to `f` whose underlying scheme `V` has the property that any `d` of its points
lying over one point of `Y` have a common affine open neighbourhood. Then every point of `V`
has an invariant affine open neighbourhood contained in the preimage of a given open of `Y`
containing its image. -/
theorem exists_isTransitionInvariant_isAffineOpen_mem_le_preimage
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsFiniteLocallyFree f] (d : ℕ)
    (hfib : ∀ p : GeometricPoint Y,
      Cardinal.mk (pullback p.hom f : Scheme.{u}) ≤ (d : Cardinal.{u}))
    (D : DescentDatum f)
    (hV : ∀ (y : Y) (v : Fin d → D.over.left),
      (∀ i, (D.over.hom ≫ f) (v i) = y) →
        ∃ U : D.over.left.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U)
    (v : D.over.left) (Y₀ : Y.Opens) (hvY₀ : (D.over.hom ≫ f) v ∈ Y₀) :
    ∃ (W : D.over.left.Opens) (_ : D.IsTransitionInvariant W),
      v ∈ W ∧ IsAffineOpen W ∧ W ≤ (D.over.hom ≫ f) ⁻¹ᵁ Y₀ := by
  classical
  set V₀ : D.over.left.Opens := (D.over.hom ≫ f) ⁻¹ᵁ Y₀
  have hV₀ : D.IsTransitionInvariant V₀ := isTransitionInvariant_preimage_base D Y₀
  have hvV₀ : v ∈ V₀ := hvY₀
  set E : DescentDatum f := D.restrictOpen V₀ hV₀
  have hUE : ∀ (y : Y) (w : Fin d → E.over.left),
      (∀ i, (E.over.hom ≫ f) (w i) = y) →
        ∃ U : E.over.left.Opens, IsAffineOpen U ∧ ∀ i, w i ∈ U := by
    intro y w hw
    obtain ⟨U, hUaff, hUmem⟩ := hV y (fun i => V₀.ι.base (w i)) hw
    obtain ⟨r, hr1, hr2⟩ := hUaff.exists_basicOpen_subset_of_finite (Set.finite_range _)
      (Set.range_subset_iff.2 hUmem) V₀ (Set.range_subset_iff.2 fun i => (w i).2)
    refine ⟨V₀.ι ⁻¹ᵁ D.over.left.basicOpen r,
      (hUaff.basicOpen r).preimage_of_isOpenImmersion V₀.ι ?_, fun i => hr1 ⟨i, rfl⟩⟩
    rwa [Scheme.Opens.opensRange_ι]
  obtain ⟨W', hW'inv, hW'aff, hW'v⟩ :=
    exists_isTransitionInvariant_isAffineOpen_mem E hfib hUE (⟨v, hvV₀⟩ : E.over.left)
  exact exists_isTransitionInvariant_isAffineOpen_mem_le_of_restrict D V₀ hV₀ W' hW'inv
    hW'aff v hvV₀ hW'v

end DescentDatum

/-! ### Transport of effectivity along a restriction of the base -/

/-- Transport of effectivity along a base restriction, with the comparison of the two
underlying schemes given abstractly by mutually inverse `σ` and `π`. -/
private theorem isEffective_of_pullbackFunctor
    {X Y X₀ Y₀ : Scheme.{u}} {f : X ⟶ Y} {f₀ : X₀ ⟶ Y₀} {ιX : X₀ ⟶ X} {ιY : Y₀ ⟶ Y}
    {comm : ιX ≫ f = f₀ ≫ ιY} (hsq : IsPullback f₀ ιX ιY f)
    (P : DescentData.PullbackFunctor f f₀ ιY ιX comm) (D : DescentDatum f)
    (gV : D.over.left ⟶ X₀) (hgV : gV ≫ ιX = D.over.hom)
    (σ : D.over.left ⟶ ((P.functor.obj D).obj ()).left)
    (π : ((P.functor.obj D).obj ()).left ⟶ D.over.left)
    (hπ : π = (P.objIso D).hom.left ≫ pullback.fst D.over.hom ιX)
    (hσπ : σ ≫ π = 𝟙 D.over.left)
    (hπσ : π ≫ σ = 𝟙 ((P.functor.obj D).obj ()).left)
    (hσhom : σ ≫ ((P.functor.obj D).obj ()).hom = gV)
    (hEff : DescentData.IsEffective (P.functor.obj D)) :
    DescentData.IsEffective D := by
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective hEff
  have hπσ' : ∀ {W : Scheme.{u}} (x : ((P.functor.obj D).obj ()).left ⟶ W),
      π ≫ σ ≫ x = x := by
    intro W x; rw [← Category.assoc, hπσ, Category.id_comp]
  have hπhom : π ≫ gV = ((P.functor.obj D).obj ()).hom := by
    rw [← hσhom, hπσ' (((P.functor.obj D).obj ()).hom)]
  have hSrcFst : P.sourceMap D ≫ pullback.fst (D.over.hom ≫ f) f =
      pullback.fst (((P.functor.obj D).obj ()).hom ≫ f₀) f₀ ≫ π := by
    rw [hπ]; exact P.sourceMap_fst D
  have hSrcSnd : P.sourceMap D ≫ pullback.snd (D.over.hom ≫ f) f =
      pullback.snd (((P.functor.obj D).obj ()).hom ≫ f₀) f₀ ≫ ιX := P.sourceMap_snd D
  have hTgtSnd : P.targetMap D ≫ pullback.snd f (D.over.hom ≫ f) =
      pullback.snd f₀ (((P.functor.obj D).obj ()).hom ≫ f₀) ≫ π := by
    rw [hπ]; exact P.targetMap_snd D
  have hcond3 : (((P.functor.obj D).obj ()).hom ≫ f₀) ≫ ιY = π ≫ D.over.hom ≫ f := by
    rw [Category.assoc, ← comm, ← hgV, ← hπhom]; simp
  have hsrc : IsPullback (pullback.fst (((P.functor.obj D).obj ()).hom ≫ f₀) f₀ ≫ π)
      (pullback.snd (((P.functor.obj D).obj ()).hom ≫ f₀) f₀ ≫ ιX) (D.over.hom ≫ f) f :=
    ((IsPullback.of_hasPullback (((P.functor.obj D).obj ()).hom ≫ f₀) f₀).paste_vert
        hsq).of_iso (Iso.refl _) ⟨π, σ, hπσ, hσπ⟩ (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simpa using hcond3) (by simp)
  have hsm : P.sourceMap D = hsrc.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [hSrcFst, hsrc.isoPullback_hom_fst]
    · rw [hSrcSnd, hsrc.isoPullback_hom_snd]
  have hiso : IsIso (P.sourceMap D) := by rw [hsm]; infer_instance
  refine DescentData.isEffective_of_isPullback (Over.mk (Q.base.hom ≫ ιY)) (σ ≫ Q.proj) ?_ ?_
  · have h1 : IsPullback (σ ≫ Q.proj) gV Q.base.hom f₀ :=
      Q.isPullback.flip.of_iso ⟨π, σ, hπσ, hσπ⟩ (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [hπσ' Q.proj]) (by simpa using hπhom.symm) (by simp) (by simp)
    have h2 := h1.paste_vert hsq
    rw [hgV] at h2
    exact h2
  · rw [← cancel_epi (P.sourceMap D)]
    have hrhs : P.sourceMap D ≫ pullback.fst (D.over.hom ≫ f) f ≫ σ ≫ Q.proj =
        pullback.fst (((P.functor.obj D).obj ()).hom ≫ f₀) f₀ ≫ Q.proj := by
      rw [← Category.assoc, hSrcFst, Category.assoc, hπσ' Q.proj]
    have hlhs : P.sourceMap D ≫ (D.gluingPullbackIso () ()).hom ≫
        pullback.snd f (D.over.hom ≫ f) ≫ σ ≫ Q.proj =
        pullback.fst (((P.functor.obj D).obj ()).hom ≫ f₀) f₀ ≫ Q.proj := by
      rw [← Category.assoc, ← P.gluing D, Category.assoc, ← Category.assoc (P.targetMap D),
        hTgtSnd, Category.assoc, hπσ' Q.proj]
      exact Q.proj_invariant
    exact hlhs.trans hrhs.symm

/-- The inclusion of the preimage of a closed open subset of the target is a closed immersion. -/
private lemma isClosedImmersion_ι_preimage {X Y : Scheme.{u}} (g : X ⟶ Y) (Y₀ : Y.Opens)
    (hclosed : IsClosed (Y₀ : Set Y)) : IsClosedImmersion (g ⁻¹ᵁ Y₀).ι :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_morphismRestrict g Y₀)
    (IsClosedImmersion.of_isPreimmersion Y₀.ι
      (by simpa only [Scheme.Opens.range_ι] using hclosed))

namespace DescentDatum

/-- Effectivity of a descent datum whose underlying scheme maps into the preimage of an open
`Y₀` of the base follows from effectivity of its pullback along the cartesian square of the
restriction `f ∣_ Y₀`, because the underlying scheme of that pullback is again `V`; the
projection from that pullback to `V` is then an isomorphism, which may be used. -/
private theorem isEffective_of_le_preimage {X Y : Scheme.{u}} {f : X ⟶ Y}
    (D : DescentDatum f) (Y₀ : Y.Opens)
    (P : DescentData.PullbackFunctor f (f ∣_ Y₀) Y₀.ι (f ⁻¹ᵁ Y₀).ι
      (morphismRestrict_ι f Y₀).symm)
    (hle : (D.over.hom ≫ f) ⁻¹ᵁ Y₀ = ⊤)
    (hEff : IsIso (pullback.fst D.over.hom (f ⁻¹ᵁ Y₀).ι) →
      DescentData.IsEffective (P.functor.obj D)) :
    DescentData.IsEffective D := by
  have hsq : IsPullback (f ∣_ Y₀) (f ⁻¹ᵁ Y₀).ι Y₀.ι f := isPullback_morphismRestrict f Y₀
  have hrange : Set.range ⇑D.over.hom ⊆ Set.range ⇑(f ⁻¹ᵁ Y₀).ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨v, rfl⟩
    have hv : v ∈ (D.over.hom ≫ f) ⁻¹ᵁ Y₀ := by rw [hle]; trivial
    simpa using hv
  have hpbV : IsPullback (𝟙 D.over.left)
      (IsOpenImmersion.lift (f ⁻¹ᵁ Y₀).ι D.over.hom hrange) D.over.hom (f ⁻¹ᵁ Y₀).ι :=
    (IsOpenImmersion.isPullback_lift_id D.over.hom (f ⁻¹ᵁ Y₀).ι hrange).flip
  have hgV : IsOpenImmersion.lift (f ⁻¹ᵁ Y₀).ι D.over.hom hrange ≫ (f ⁻¹ᵁ Y₀).ι =
      D.over.hom := IsOpenImmersion.lift_fac _ _ _
  have : IsIso (P.objIso D).hom.left :=
    inferInstanceAs (IsIso ((Over.forget (f ⁻¹ᵁ Y₀).toScheme).map (P.objIso D).hom))
  have hobj : (P.objIso D).hom.left ≫ pullback.snd D.over.hom (f ⁻¹ᵁ Y₀).ι =
      ((P.functor.obj D).obj ()).hom := by
    rw [← Over.pullback_obj_hom]
    exact Over.w (P.objIso D).hom
  have hfstinv : pullback.fst D.over.hom (f ⁻¹ᵁ Y₀).ι = hpbV.isoPullback.inv :=
    calc pullback.fst D.over.hom (f ⁻¹ᵁ Y₀).ι
        = hpbV.isoPullback.inv ≫ hpbV.isoPullback.hom ≫
            pullback.fst D.over.hom (f ⁻¹ᵁ Y₀).ι := by rw [Iso.inv_hom_id_assoc]
      _ = hpbV.isoPullback.inv := by rw [hpbV.isoPullback_hom_fst, Category.comp_id]
  have hσπ : (hpbV.isoPullback.hom ≫ inv ((P.objIso D).hom.left)) ≫
      ((P.objIso D).hom.left ≫ pullback.fst D.over.hom (f ⁻¹ᵁ Y₀).ι) = 𝟙 D.over.left := by
    rw [Category.assoc, IsIso.inv_hom_id_assoc]
    exact hpbV.isoPullback_hom_fst
  have hπσ : ((P.objIso D).hom.left ≫ pullback.fst D.over.hom (f ⁻¹ᵁ Y₀).ι) ≫
      (hpbV.isoPullback.hom ≫ inv ((P.objIso D).hom.left)) =
      𝟙 ((P.functor.obj D).obj ()).left := by
    rw [hfstinv]; simp
  have hσhom : (hpbV.isoPullback.hom ≫ inv ((P.objIso D).hom.left)) ≫
      ((P.functor.obj D).obj ()).hom =
      IsOpenImmersion.lift (f ⁻¹ᵁ Y₀).ι D.over.hom hrange := by
    rw [← hobj, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hpbV.isoPullback_hom_snd
  exact isEffective_of_pullbackFunctor hsq P D _ hgV _ _ rfl hσπ hπσ hσhom
    (hEff (by rw [hfstinv]; infer_instance))

/-- **Effective descent for an affine descent datum lying over an affine open of the base.** A
descent datum relative to a surjective flat affine morphism `f : X ⟶ Y` whose underlying scheme
is affine and which maps into an affine open `Y₀` of `Y` is effective. The base `Y` is not
assumed affine: the descended scheme is produced over `Y₀` and read as a scheme over `Y`. -/
theorem isEffective_of_isAffine_of_le_preimage
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hsurj : Surjective f) (hflat : Flat f) [IsAffineHom f]
    (D : DescentDatum f) (Y₀ : Y.Opens) (hY₀ : IsAffineOpen Y₀)
    [IsAffine D.over.left]
    (hle : (D.over.hom ≫ f) ⁻¹ᵁ Y₀ = ⊤) :
    DescentData.IsEffective D := by
  have : Flat f := hflat
  have : IsAffine Y₀.toScheme := hY₀
  have : IsAffine (f ⁻¹ᵁ Y₀).toScheme := IsAffineHom.isAffine_preimage Y₀ hY₀
  have : Surjective (f ∣_ Y₀) := IsZariskiLocalAtTarget.restrict (P := @Surjective) hsurj Y₀
  have P := DescentData.pullbackFunctor f (f ∣_ Y₀) Y₀.ι (f ⁻¹ᵁ Y₀).ι
    (morphismRestrict_ι f Y₀).symm
  refine isEffective_of_le_preimage D Y₀ P hle fun hfst => ?_
  have : IsIso (P.objIso D).hom.left :=
    inferInstanceAs (IsIso ((Over.forget (f ⁻¹ᵁ Y₀).toScheme).map (P.objIso D).hom))
  have : IsAffine ((P.functor.obj D).obj ()).left :=
    isAffine_of_isAffineHom ((P.objIso D).hom.left ≫ pullback.fst D.over.hom (f ⁻¹ᵁ Y₀).ι)
  exact isEffective_of_isAffineHom_of_surjective_of_flat inferInstance inferInstance
    (P.functor.obj D) inferInstance

/-- **Stacks Project, Tag 0H8K.** Let `f : X ⟶ Y` be a surjective finite locally free morphism
of schemes and let `d` be a positive integer such that every geometric fibre of `f` has at most
`d` points. Let `D` be a descent datum relative to `f` whose underlying scheme `V` has the
property that any `d` points of `V` lying over one point of `Y` have a common affine open
neighbourhood. Then `D` is effective. -/
@[stacks 0H8K, sga "1 VIII 7.6" "sufficiency, fibres ≤ d"]
theorem isEffective_of_cardinalMk_geometricFibre_le
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f] [IsFiniteLocallyFree f]
    (d : ℕ) (hd : 0 < d)
    (hfib : ∀ p : GeometricPoint Y,
      Cardinal.mk (pullback p.hom f : Scheme.{u}) ≤ (d : Cardinal.{u}))
    (D : DescentDatum f)
    (hV : ∀ (y : Y) (v : Fin d → D.over.left),
      (∀ i, (D.over.hom ≫ f) (v i) = y) →
        ∃ U : D.over.left.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U) :
    DescentData.IsEffective D := by
  have hflat : Flat f := IsFiniteLocallyFree.flat f
  have hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine isEffective_of_forall_exists_restrictOpen D fun v => ?_
  obtain ⟨Y₀, hY₀, hvY₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := (D.over.hom ≫ f).base v) (U := ⊤) trivial
  obtain ⟨W, hW, hvW, hWaff, hWle⟩ :=
    exists_isTransitionInvariant_isAffineOpen_mem_le_preimage d hfib D hV v Y₀ hvY₀
  refine ⟨W, hW, hvW, ?_⟩
  have : IsAffine (D.restrictOpen W hW).over.left := hWaff
  refine isEffective_of_isAffine_of_le_preimage ‹Surjective f› hflat
    (D.restrictOpen W hW) Y₀ hY₀ ?_
  exact top_le_iff.mp fun z _ => hWle z.2

/-! ### Removing the bound on the fibres -/

/-- **Effectivity over a stratum of constant degree.** A descent datum whose underlying scheme
maps into the preimage of an open and closed `Y₀ ⊆ Y` over which `f` is finite locally free of
rank `d` is effective, provided any `d + 1` of its points lying over one point of `Y` have a
common affine open neighbourhood. -/
private theorem isEffective_of_le_preimage_of_isFiniteLocallyFreeOfRank
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f] (E : DescentDatum f) (Y₀ : Y.Opens) (d : ℕ)
    (hclosed : IsClosed (Y₀ : Set Y)) (hrank : IsFiniteLocallyFreeOfRank (f ∣_ Y₀) d)
    (hle : (E.over.hom ≫ f) ⁻¹ᵁ Y₀ = ⊤)
    (hV : ∀ (y : Y) (w : Fin (d + 1) → E.over.left),
      (∀ i, (E.over.hom ≫ f) (w i) = y) →
        ∃ U : E.over.left.Opens, IsAffineOpen U ∧ ∀ i, w i ∈ U) :
    DescentData.IsEffective E := by
  have hsurj₀ : Surjective (f ∣_ Y₀) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹Surjective f› Y₀
  have hflf₀ : IsFiniteLocallyFree (f ∣_ Y₀) :=
    IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (f ∣_ Y₀) d
  -- the geometric fibres of the restriction of `f` to `Y₀` have at most `d + 1` points
  have hfib : ∀ p : GeometricPoint Y₀.toScheme,
      Cardinal.mk (pullback p.hom (f ∣_ Y₀) : Scheme.{u}) ≤ ((d + 1 : ℕ) : Cardinal.{u}) := by
    have hb := cardinalMk_pullback_le_of_degree_le (f ∣_ Y₀) (d + 1) fun k _ g => by
      obtain ⟨r, hr, hrk⟩ :=
        (boundsFiberDegrees_iff_field_baseChange (f ∣_ Y₀) (d : ℤ)).mp
          (boundsFiberDegrees_of_isFiniteLocallyFreeOfRank (f ∣_ Y₀) d) k g
      exact ⟨r, by omega, hrk⟩
    exact fun p => hb p.residueField p.hom
  -- `Y₀` is closed, so the comparison morphism from the pulled-back scheme back to `V` is affine
  have : IsClosedImmersion (f ⁻¹ᵁ Y₀).ι := isClosedImmersion_ι_preimage f Y₀ hclosed
  set P := DescentData.pullbackFunctor f (f ∣_ Y₀) Y₀.ι (f ⁻¹ᵁ Y₀).ι
    (morphismRestrict_ι f Y₀).symm
  have : IsIso (P.objIso E).hom.left :=
    inferInstanceAs (IsIso ((Over.forget (f ⁻¹ᵁ Y₀).toScheme).map (P.objIso E).hom))
  have : IsAffineHom (pullback.fst E.over.hom (f ⁻¹ᵁ Y₀).ι) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback E.over.hom (f ⁻¹ᵁ Y₀).ι).flip inferInstance
  set j : ((P.functor.obj E).obj ()).left ⟶ E.over.left :=
    (P.objIso E).hom.left ≫ pullback.fst E.over.hom (f ⁻¹ᵁ Y₀).ι with hjdef
  have : IsAffineHom j := by rw [hjdef]; infer_instance
  -- `j` carries a fibre of the pulled-back datum over `Y₀` into a fibre of `V` over `Y`
  have hπ : (P.objIso E).hom.left ≫ pullback.fst E.over.hom (f ⁻¹ᵁ Y₀).ι ≫ E.over.hom =
      ((P.functor.obj E).obj ()).hom ≫ (f ⁻¹ᵁ Y₀).ι := by
    rw [pullback.condition, ← Category.assoc, ← Over.pullback_obj_hom, Over.w]
  have hjover : j ≫ E.over.hom ≫ f = (((P.functor.obj E).obj ()).hom ≫ (f ∣_ Y₀)) ≫ Y₀.ι :=
    calc j ≫ E.over.hom ≫ f
        = ((P.objIso E).hom.left ≫
            pullback.fst E.over.hom (f ⁻¹ᵁ Y₀).ι ≫ E.over.hom) ≫ f := by
          rw [hjdef]; simp only [Category.assoc]
      _ = (((P.functor.obj E).obj ()).hom ≫ (f ⁻¹ᵁ Y₀).ι) ≫ f := by rw [hπ]
      _ = (((P.functor.obj E).obj ()).hom ≫ (f ∣_ Y₀)) ≫ Y₀.ι := by
          simp only [Category.assoc, morphismRestrict_ι]
  refine isEffective_of_le_preimage E Y₀ P hle fun _ =>
    isEffective_of_cardinalMk_geometricFibre_le (d + 1) (Nat.succ_pos d) hfib
      (P.functor.obj E) fun y w hw => ?_
  obtain ⟨U, hU, hUmem⟩ := hV (Y₀.ι y) (fun i => j (w i)) fun i => by
    rw [← Scheme.Hom.comp_apply, hjover, Scheme.Hom.comp_apply, hw i]
  exact ⟨j ⁻¹ᵁ U, hU.preimage j, hUmem⟩

/-- **Stacks Project, Tag 0CCI.** Let `f : X ⟶ Y` be a surjective finite locally free morphism
of schemes and let `D` be a descent datum relative to `f` whose underlying scheme `V` has the
property that any finite nonempty collection of points of `V` lying over one point of `Y` has a
common affine open neighbourhood. Then `D` is effective. -/
@[stacks 0CCI]
theorem isEffective_of_forall_exists_isAffineOpen
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f] [IsFiniteLocallyFree f] (D : DescentDatum f)
    (hV : ∀ (n : ℕ) (y : Y) (v : Fin (n + 1) → D.over.left),
      (∀ i, (D.over.hom ≫ f) (v i) = y) →
        ∃ U : D.over.left.Opens, IsAffineOpen U ∧ ∀ i, v i ∈ U) :
    DescentData.IsEffective D := by
  classical
  have hflat : Flat f := IsFiniteLocallyFree.flat f
  obtain ⟨Z, hZclosed, -, hZcover, hZrank⟩ :=
    exists_isClosed_isFiniteLocallyFreeOfRank_decomposition f
  refine isEffective_of_forall_exists_restrictOpen D fun v => ?_
  obtain ⟨d, hd⟩ : ∃ d, (D.over.hom ≫ f) v ∈ Z d :=
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hZcover]; trivial)
  set V₀ : D.over.left.Opens := (D.over.hom ≫ f) ⁻¹ᵁ Z d
  have hV₀ : D.IsTransitionInvariant V₀ := isTransitionInvariant_preimage_base D (Z d)
  refine ⟨V₀, hV₀, hd, ?_⟩
  set E : DescentDatum f := D.restrictOpen V₀ hV₀
  have : IsClosedImmersion V₀.ι := isClosedImmersion_ι_preimage (D.over.hom ≫ f) (Z d) (hZclosed d)
  refine isEffective_of_le_preimage_of_isFiniteLocallyFreeOfRank E (Z d) d (hZclosed d)
    (hZrank d) (top_le_iff.mp fun t _ => t.2) fun y w hw => ?_
  obtain ⟨U, hU, hUmem⟩ := hV d y (fun i => V₀.ι.base (w i)) hw
  exact ⟨V₀.ι ⁻¹ᵁ U, hU.preimage V₀.ι, hUmem⟩

/-- **Stacks Project, Tag 0H8L.** Every descent datum relative to a surjective finite locally
free radicial morphism of schemes is effective: such a morphism is universally injective, so
each of its geometric fibres is a single point. -/
@[stacks 0H8L]
theorem isEffective_of_universallyInjective
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f] [IsFiniteLocallyFree f]
    [UniversallyInjective f] (D : DescentDatum f) : DescentData.IsEffective D := by
  refine isEffective_of_cardinalMk_geometricFibre_le 1 Nat.one_pos ?_ D ?_
  · intro p
    have : UniversallyInjective (pullback.fst p.hom f) :=
      MorphismProperty.of_isPullback (P := @UniversallyInjective)
        (IsPullback.of_hasPullback p.hom f).flip ‹_›
    have hsub : Subsingleton (pullback p.hom f : Scheme.{u}) :=
      ⟨fun a b => (pullback.fst p.hom f).injective (Subsingleton.elim _ _)⟩
    simpa using Cardinal.le_one_iff_subsingleton.mpr hsub
  · intro y v hv
    obtain ⟨U, hU, hvU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := D.over.left) (x := v 0) (U := ⊤) trivial
    exact ⟨U, hU, fun i => by rw [Subsingleton.elim i 0]; exact hvU⟩

end DescentDatum

end AlgebraicGeometry

end
