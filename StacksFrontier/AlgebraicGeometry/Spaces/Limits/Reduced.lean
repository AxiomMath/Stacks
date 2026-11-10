module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.Reduced
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FinitenessConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Reducedness of a cofiltered limit of algebraic spaces

The limit of a cofiltered inverse system of algebraic spaces with affine transition morphisms
is reduced as soon as every stage is reduced.

## Main results

* `AlgebraicGeometry.Space.isReduced_limit`: a cofiltered limit of reduced algebraic spaces
  with affine transition morphisms is reduced.
* `AlgebraicGeometry.Space.isReduced_limit_of_mono`: the same conclusion from the
  cofinality-free cardinality hypothesis, at the cost of monomorphic transition morphisms.

## Implementation notes

Reducedness of an algebraic space is the étale-local property of reduced schemes,
`AlgebraicGeometry.Space.HasEtaleLocalProperty`. A reduced étale atlas of one stage is pulled
back along the inverse system: the resulting diagram of schemes indexed by the slice over that
stage has reduced terms and affine transition morphisms, so
`AlgebraicGeometry.isReduced_cofilteredLimit_of_isReduced` applies to its limit, and that limit
is a reduced étale atlas of the limit space. The size hypotheses are those of
`AlgebraicGeometry.Space.isAffineHom_limitπ`.

The two forms factor through
`AlgebraicGeometry.Space.isReduced_limit_of_relativelyRepresentable_of_preservesLimit`, which
isolates the two things either set of size hypotheses is used for: relative representability
of the projections from the limit, and preservation of the limit of the pulled-back diagram by
the underlying scheme functor. The second is stated for an arbitrary diagram of base changes of
the transition morphisms along the chosen chart, together with the pullback squares exhibiting it
as one, because that is what lets the cofinality-free form bound its stages uniformly: a base
change of a monomorphism is a monomorphism, so every such stage maps monomorphically to the one
fixed chart.

## References

* [Stacks Project, Tag 0CUI](https://stacks.math.columbia.edu/tag/0CUI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The size of a cofiltered limit of schemes with affine transition morphisms, bounded by
any one cardinal `b` which is infinite, bounds the slice of the index category at some stage
`j`, and bounds the sizes of all the stages.

This is the cofinality-free kernel of the two bounds below: the limit is covered by the
preimages of the affine opens of the stage `j`, each of which is an affine limit over the
slice at `j`, so `b * b = b` bounds everything. Which hypotheses make `b` available is the
only thing the two forms below differ in. -/
private theorem size_cofilteredLimit_le
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u})
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (E.map f)]
    (c : Cone E) (hc : IsLimit c) (j : J) {b : Cardinal.{u}}
    (hb0 : Cardinal.aleph0 ≤ b) (hbJ : Cardinal.mk (Over j) ≤ b)
    (hbE : ∀ k, (E.obj k).size ≤ b) : c.pt.size ≤ b := by
  classical
  have hπ : IsAffineHom (c.π.app j) := AlgebraicGeometry.isAffineHom_π_app E c hc j
  have : Nonempty (E.obj j).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  refine (Scheme.size_le_of_iSup_eq_top
    (fun U : (E.obj j).affineOpens => c.π.app j ⁻¹ᵁ U.1)
    ((c.π.app j).iSup_preimage_eq_top (iSup_affineOpens_eq_top _))).trans ?_
  refine max_le ((Scheme.mk_affineOpens_le_size _).trans (hbE j)) (ciSup_le' fun U => ?_)
  let O := AlgebraicGeometry.opensDiagram E j U
  let oC := AlgebraicGeometry.opensCone E c j U
  have hoC : IsLimit oC := AlgebraicGeometry.isLimitOpensCone E c hc j U
  have (k : Over j) : IsAffine (O.obj k) := U.2.preimage (E.map k.hom)
  have (k : Over j) : CompactSpace (O.obj k) := inferInstance
  have (k : Over j) : QuasiSeparatedSpace (O.obj k) := inferInstance
  have : IsAffine oC.pt := Scheme.isAffine_of_isLimit oC hoC
  change oC.pt.size ≤ b
  rw [Scheme.size_of_isAffine]
  refine max_le hb0 ?_
  let F : (Over j)ᵒᵖ ⥤ CommRingCat.{u} := O.op ⋙ Scheme.Γ
  let q := Scheme.Γ.mapCocone oC.op
  have hq : IsColimit q := Classical.choice
    (AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone O oC hoC)
  have hqT := isColimitOfPreserves (forget CommRingCat) hq
  let f : (Σ k : (Over j)ᵒᵖ, F.obj k) → q.pt :=
    fun x => (q.ι.app x.1).hom x.2
  have hsur : Function.Surjective f := by
    intro x
    obtain ⟨k, a, ha⟩ := Types.jointly_surjective_of_isColimit hqT x
    exact ⟨⟨k, a⟩, ha⟩
  apply (Cardinal.mk_le_of_surjective hsur).trans
  rw [Cardinal.mk_sigma]
  calc
    _ ≤ Cardinal.sum (fun _ : (Over j)ᵒᵖ => b) := Cardinal.sum_le_sum _ _ (fun k => by
      change Cardinal.mk Γ(O.obj k.unop, ⊤) ≤ b
      exact (Scheme.mk_sections_le_size _ ⟨⊤, isAffineOpen_top _⟩).trans
        ((Scheme.size_coe_opens_le _ _).trans (hbE k.unop.left)))
    _ = Cardinal.mk ((Over j)ᵒᵖ) * b := Cardinal.sum_const' _ _
    _ ≤ b * b := mul_le_mul'
      ((Cardinal.mk_congr (Opposite.equivToOpposite (α := Over j))).symm.trans_le hbJ) le_rfl
    _ = b := Cardinal.mul_eq_self hb0

/-- The size of a cofiltered limit of schemes with affine transition morphisms, all of size
below the site's cutoff and indexed by a category with fewer objects and morphisms than the
cofinality of that cutoff, is again below the cutoff. -/
private theorem size_cofilteredLimit_lt
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u})
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (E.map f)]
    (c : Cone E) (hc : IsLimit c)
    (hJ : Cardinal.mk J < B.cutoff.ord.cof)
    (hH : ∀ j k : J, Cardinal.mk (j ⟶ k) < B.cutoff.ord.cof)
    (hE : ∀ j, (E.obj j).size < B.cutoff) : c.pt.size < B.cutoff := by
  classical
  obtain ⟨j⟩ := IsCofiltered.nonempty (C := J)
  refine (size_cofilteredLimit_le E c hc j (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    (fun k => (le_ciSup Cardinal.bddAbove_of_small k).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans_lt ?_
  exact max_lt B.aleph0_lt_cutoff
    (max_lt ((mk_over_lt B.aleph0_lt_cutoff_cof hJ hH j).trans_le (Ordinal.cof_ord_le _))
      (Cardinal.iSup_lt_of_lt_cof_ord hJ hE))

/-- **The cofinality-free size bound for a cofiltered limit of schemes with affine
transitions.** The index category is only asked to have fewer objects than the cutoff with
all its morphism types bounded by one cardinal `ν` below it, and the stages to have sizes
bounded by one cardinal `μ` below it. Incomparable with
`AlgebraicGeometry.size_cofilteredLimit_lt`. -/
private theorem size_cofilteredLimit_lt_of_size_le
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u})
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (E.map f)]
    (c : Cone E) (hc : IsLimit c) {ν μ : Cardinal.{u}}
    (hJ : Cardinal.mk J < B.cutoff) (hν : ν < B.cutoff)
    (hH : ∀ j k : J, Cardinal.mk (j ⟶ k) ≤ ν) (hμ : μ < B.cutoff)
    (hE : ∀ j, (E.obj j).size ≤ μ) : c.pt.size < B.cutoff := by
  classical
  obtain ⟨j⟩ := IsCofiltered.nonempty (C := J)
  refine (size_cofilteredLimit_le E c hc j (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    (fun k => (hE k).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans_lt ?_
  exact max_lt B.aleph0_lt_cutoff
    (max_lt (mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hJ hν hH j) hμ)

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system in the
site with affine transition morphisms whose underlying limit of schemes has size below the
cutoff. -/
private theorem preservesLimit_toScheme_of_sizeBelow
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map f))]
    (hsize : ∀ (c : Cone (AlgebraicGeometry.underlyingDiagram E)), IsLimit c →
      c.pt.size < B.cutoff) :
    PreservesLimit E (AlgebraicGeometry.BigFppfOver.toScheme B S hS) := by
  let E' := E ⋙ AlgebraicGeometry.BigFppfOver.forget B S hS
  have : IsConnected J := IsCofiltered.isConnected _
  have : ∀ {j k : J} (f : j ⟶ k), IsAffineHom ((E' ⋙ B.inclusion).map f) :=
    fun {_ _} f => (inferInstance : IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map f)))
  have : HasLimit (E' ⋙ B.inclusion) := inferInstance
  let : CreatesLimit E' B.inclusion := createsLimitFullSubcategoryInclusion E'
    (hsize (limit.cone _) (limit.isLimit _))
  have : HasLimit E' := hasLimit_of_created E' B.inclusion
  have : PreservesLimit E' B.inclusion := inferInstance
  apply comp_preservesLimit

/-- The underlying scheme functor preserves the limit of a cofiltered inverse system in the
site with affine transition morphisms, indexed by a category with fewer objects and morphisms
than the cofinality of the site's cutoff. -/
private theorem preservesLimit_toScheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map f))]
    (hJ : Cardinal.mk J < B.cutoff.ord.cof)
    (hH : ∀ j k : J, Cardinal.mk (j ⟶ k) < B.cutoff.ord.cof) :
    PreservesLimit E (AlgebraicGeometry.BigFppfOver.toScheme B S hS) :=
  have : ∀ {j k : J} (f : j ⟶ k),
      IsAffineHom ((AlgebraicGeometry.underlyingDiagram E).map f) :=
    fun {_ _} f => (inferInstance : IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map f)))
  preservesLimit_toScheme_of_sizeBelow B S hS E fun _ hc =>
    size_cofilteredLimit_lt B (AlgebraicGeometry.underlyingDiagram E) _ hc hJ hH
      (fun j => (E.obj j).left.property)

/-- **The cofinality-free form of the preservation of the limit.** The index category is only
asked to have fewer objects than the cutoff with all its morphism types bounded by one
cardinal `ν` below it, and the stages to have sizes bounded by one cardinal `μ` below it. -/
private theorem preservesLimit_toScheme_of_size_le
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map f))]
    {ν μ : Cardinal.{u}} (hJ : Cardinal.mk J < B.cutoff) (hν : ν < B.cutoff)
    (hH : ∀ j k : J, Cardinal.mk (j ⟶ k) ≤ ν) (hμ : μ < B.cutoff)
    (hE : ∀ j, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j)).size ≤ μ) :
    PreservesLimit E (AlgebraicGeometry.BigFppfOver.toScheme B S hS) :=
  have : ∀ {j k : J} (f : j ⟶ k),
      IsAffineHom ((AlgebraicGeometry.underlyingDiagram E).map f) :=
    fun {_ _} f => (inferInstance : IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map f)))
  preservesLimit_toScheme_of_sizeBelow B S hS E fun _ hc =>
    size_cofilteredLimit_lt_of_size_le B (AlgebraicGeometry.underlyingDiagram E) _ hc hJ hν hH
      hμ hE

/-- Morphisms in a slice category inject into the morphisms of the underlying objects. -/
private theorem mk_hom_over_le {C : Type u} [Category.{u} C] {i : C} (j k : Over i) :
    Cardinal.mk (j ⟶ k) ≤ Cardinal.mk (j.left ⟶ k.left) :=
  Cardinal.mk_le_of_injective (f := fun f : j ⟶ k => f.left) fun _ _ h => Over.OverMorphism.ext h

private theorem affineData_of_isAffineHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f :=
  ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS f hF hG).out 2 1
    (a := AlgebraicGeometry.Space.IsAffineHom B S hS f)
    (b := yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f)).mp hf

private theorem relativelyRepresentable_of_isAffineHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f) :
    yoneda.relativelyRepresentable f :=
  (affineData_of_isAffineHom B S hS f hF hG hf).1

private theorem isPullback_map_of_pullbacks {C : Type u} [Category.{u} C]
    {Pj Pk Dj Dk U B : C}
    {pjD : Pj ⟶ Dj} {pjU : Pj ⟶ U} {fj : Dj ⟶ B} {f : U ⟶ B}
    {pkD : Pk ⟶ Dk} {pkU : Pk ⟶ U} {fk : Dk ⟶ B}
    (hjq : IsPullback pjD pjU fj f) (hkq : IsPullback pkD pkU fk f)
    (q : Dj ⟶ Dk) (hq : q ≫ fk = fj)
    (m : Pj ⟶ Pk) (hmD : m ≫ pkD = pjD ≫ q) (hmU : m ≫ pkU = pjU) :
    IsPullback m pjD pkD q :=
  IsPullback.of_right (by rw [hmU, hq]; exact hjq.flip) hmD hkq.flip

/-- A base change of a morphism of presheaves satisfying a scheme property stable under base
change satisfies that property. -/
private theorem presheaf_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P : MorphismProperty Scheme.{u}}
    [(MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange]
    {X Y Z W : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback snd fst g f)
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) g) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) fst :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h hg

private theorem isReduced_of_etale_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hred : AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS F
      (fun X : Scheme.{u} => IsReduced X))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f) :
    IsReduced ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) :=
  (AlgebraicGeometry.Space.exists_atlas_iff_forall_etale B S hS F
    (fun X : Scheme.{u} => IsReduced X) hF).mp hred U f hf

/-- The common core of the two forms below. The cardinality hypotheses of either form are
used for exactly two things: the projections from the limit are relatively representable
(Stacks 07SF), and the underlying scheme functor preserves the limit of the system of base
changes of the stages along a chart of one of them. Those two are the hypotheses here; the
second is stated for an arbitrary such system of base changes, together with the pullback
squares that exhibit it as one, because that is what lets the cofinality-free form below
bound its stages uniformly. -/
private theorem Space.isReduced_limit_of_relativelyRepresentable_of_preservesLimit
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hReduced : ∀ i, AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (D.obj i)
      (fun X : Scheme.{u} => IsReduced X))
    (hrelπ : ∀ i : I, yoneda.relativelyRepresentable (limit.π D i))
    (hpres : ∀ (i : I) (U₀ : AlgebraicGeometry.BigFppfOver B S hS)
      (f₀ : yoneda.obj U₀ ⟶ D.obj i) (E : Over i ⥤ AlgebraicGeometry.BigFppfOver B S hS)
      (r : ∀ j : Over i, E.obj j ⟶ U₀)
      (p : ∀ j : Over i, yoneda.obj (E.obj j) ⟶ D.obj j.left),
      (∀ j : Over i, IsPullback (p j) (yoneda.map (r j)) (D.map j.hom) f₀) →
      (∀ {j k : Over i} (q : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map q))) →
      PreservesLimit E (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) :
    AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (limit D)
      (fun X : Scheme.{u} => IsReduced X) := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, f₀, hsurj₀, hetale₀, hred₀⟩ := hReduced i
  have hrel {j : I} (f : j ⟶ i) :
      yoneda.relativelyRepresentable (D.map f) :=
    relativelyRepresentable_of_isAffineHom B S hS (D.map f) (hD j) (hD i)
      (hAffine f)
  -- Pull back the reduced atlas at `i` along the inverse system.  The resulting
  -- scheme diagram has reduced terms and affine transition maps; its limit is the
  -- desired reduced atlas of `limit D`.
  let V (j : Over i) : AlgebraicGeometry.BigFppfOver B S hS :=
    (hrel j.hom).pullback f₀
  let pd (j : Over i) : yoneda.obj (V j) ⟶ D.obj j.left :=
    (hrel j.hom).fst f₀
  let pu (j : Over i) : yoneda.obj (V j) ⟶ yoneda.obj U₀ :=
    yoneda.map ((hrel j.hom).snd f₀)
  have bmapCondition {j k : Over i} (q : j ⟶ k) :
      (pd j ≫ D.map q.left) ≫ D.map k.hom = pu j ≫ f₀ := by
    calc
      (pd j ≫ D.map q.left) ≫ D.map k.hom =
          pd j ≫ (D.map q.left ≫ D.map k.hom) := Category.assoc _ _ _
      _ = pd j ≫ D.map (q.left ≫ k.hom) := by rw [D.map_comp]
      _ = pd j ≫ D.map j.hom := by rw [q.w]
      _ = pu j ≫ f₀ := (hrel j.hom).isPullback f₀ |>.w
  let bmap {j k : Over i} (q : j ⟶ k) : V j ⟶ V k :=
    yoneda.preimage (((hrel k.hom).isPullback f₀).lift
      (pd j ≫ D.map q.left) (pu j) (bmapCondition q))
  have bmap_fst {j k : Over i} (q : j ⟶ k) :
      yoneda.map (bmap q) ≫ pd k = pd j ≫ D.map q.left := by
    dsimp [bmap]
    rw [Functor.map_preimage, IsPullback.lift_fst]
  have bmap_snd {j k : Over i} (q : j ⟶ k) :
      bmap q ≫ (hrel k.hom).snd f₀ = (hrel j.hom).snd f₀ := by
    apply yoneda.map_injective
    rw [Functor.map_comp]
    change yoneda.map (yoneda.preimage
      (((hrel k.hom).isPullback f₀).lift
        (pd j ≫ D.map q.left) (pu j) (bmapCondition q))) ≫
        yoneda.map ((hrel k.hom).snd f₀) = yoneda.map ((hrel j.hom).snd f₀)
    rw [Functor.map_preimage]
    exact (hrel k.hom).isPullback f₀ |>.lift_snd _ _ (bmapCondition q)
  have bmap_snd' {j k : Over i} (q : j ⟶ k) :
      yoneda.map (bmap q) ≫ pu k = pu j := by
    change yoneda.map (bmap q) ≫ yoneda.map ((hrel k.hom).snd f₀) =
      yoneda.map ((hrel j.hom).snd f₀)
    rw [← Functor.map_comp, bmap_snd]
  let E : Over i ⥤ AlgebraicGeometry.BigFppfOver B S hS :=
    { obj := V
      map := fun {j k} q => bmap q
      map_id j := by
        apply yoneda.map_injective
        apply (hrel j.hom).isPullback f₀ |>.hom_ext
        · calc
            yoneda.map (bmap (𝟙 j)) ≫ pd j =
                pd j ≫ D.map ((𝟙 j : j ⟶ j).left) :=
              bmap_fst (𝟙 j)
            _ = 𝟙 _ ≫ pd j := by simp
        · exact bmap_snd' (𝟙 j)
      map_comp := by
        intro j k l f g
        apply yoneda.map_injective
        apply (hrel l.hom).isPullback f₀ |>.hom_ext
        · calc
            yoneda.map (bmap (f ≫ g)) ≫ pd l =
                pd j ≫ D.map (f ≫ g).left := bmap_fst (f ≫ g)
            _ = pd j ≫ D.map f.left ≫ D.map g.left := by simp
            _ = (yoneda.map (bmap f) ≫ yoneda.map (bmap g)) ≫ pd l := by
              calc
                pd j ≫ D.map f.left ≫ D.map g.left =
                    (pd j ≫ D.map f.left) ≫ D.map g.left :=
                  (Category.assoc _ _ _).symm
                _ = (yoneda.map (bmap f) ≫ pd k) ≫ D.map g.left :=
                  congrArg (fun h => h ≫ D.map g.left) (bmap_fst f).symm
                _ = yoneda.map (bmap f) ≫ (pd k ≫ D.map g.left) :=
                  Category.assoc _ _ _
                _ = yoneda.map (bmap f) ≫ (yoneda.map (bmap g) ≫ pd l) :=
                  congrArg (fun h => yoneda.map (bmap f) ≫ h) (bmap_fst g).symm
                _ = (yoneda.map (bmap f) ≫ yoneda.map (bmap g)) ≫ pd l :=
                  (Category.assoc _ _ _).symm
        · calc
            yoneda.map (bmap (f ≫ g)) ≫ pu l = pu j := bmap_snd' (f ≫ g)
            _ = (yoneda.map (bmap f) ≫ yoneda.map (bmap g)) ≫ pu l := by
              rw [Category.assoc, bmap_snd', bmap_snd'] }
  have hEtale (j : Over i) :
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) (pd j) := by
    have := Space.etale_inverseImage_isStableUnderBaseChange B S hS
    exact presheaf_of_isPullback B S hS ((hrel j.hom).isPullback f₀).flip hetale₀
  have hredV (j : Over i) : IsReduced
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V j)) :=
    isReduced_of_etale_chart B S hS (hD j.left) (hReduced j.left) (V j) (pd j) (hEtale j)
  have hpbMap {j k : Over i} (q : j ⟶ k) :
      IsPullback (pd j) (yoneda.map (E.map q)) (D.map q.left) (pd k) := by
    have h := isPullback_map_of_pullbacks
      ((hrel j.hom).isPullback f₀) ((hrel k.hom).isPullback f₀)
      (D.map q.left) (by
        rw [← D.map_comp]
        congr 1
        exact q.w)
      (yoneda.map (E.map q)) (bmap_fst q) (by
        rw [← Functor.map_comp]
        exact congrArg yoneda.map (bmap_snd q))
    exact h.flip
  have hAffineE {j k : Over i} (q : j ⟶ k) :
      _root_.AlgebraicGeometry.IsAffineHom
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map q)) := by
    have hdata := affineData_of_isAffineHom B S hS (D.map q.left)
      (hD j.left) (hD k.left) (hAffine q.left)
    exact hdata.2.property (pd k) (pd j) (E.map q) (hpbMap q)
  have : ∀ {j k : Over i} (q : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (E.map q)) :=
    hAffineE
  have : ∀ j : Over i, IsReduced
      ((E ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj j) := hredV
  have hrelL := hrelπ i
  let W := hrelL.pullback f₀
  let F := Over.post D ⋙ Over.pullback f₀ ⋙ Over.forget (yoneda.obj U₀)
  let e : E ⋙ yoneda ≅ F := NatIso.ofComponents
    (fun j => ((hrel j.hom).isPullback f₀).isoPullback) (by
      intro j k q
      apply pullback.hom_ext
      · simp only [F, Functor.comp_map, Over.pullback_map_left, Over.forget_map,
          Over.post, Over.mk_hom, Over.homMk_left,
          Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
          pullback.lift_fst]
        exact bmap_fst q
      · simp only [F, Functor.comp_map, Over.pullback_map_left, Over.forget_map,
          Over.post, Over.mk_hom, Over.homMk_left,
          Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
        exact bmap_snd' q)
  let cP := (Over.forget (yoneda.obj U₀)).mapCone
    ((Over.pullback f₀).mapCone ((limit.cone D).overPost i))
  have hcP : IsLimit cP := AlgebraicGeometry.Space.isLimitPullbackLimitOverPost B S hS D i f₀
  let cY : Cone (E ⋙ yoneda) := (Cone.postcompose e.inv).obj cP
  have hcY : IsLimit cY := (IsLimit.postcomposeInvEquiv e cP).symm hcP
  let wIso : yoneda.obj W ≅ cY.pt := (hrelL.isPullback f₀).isoPullback
  let cE : Cone E :=
    { pt := W
      π :=
        { app := fun j => yoneda.preimage (wIso.hom ≫ cY.π.app j)
          naturality := fun j k q => yoneda.map_injective (by
            simpa using congrArg (fun f => wIso.hom ≫ f) (cY.w q).symm) } }
  have he : yoneda.mapCone cE ≅ cY :=
    Cone.ext wIso (fun j => by simp [cE])
  have hcE : IsLimit cE := isLimitOfReflects yoneda (hcY.ofIsoLimit he.symm)
  have : PreservesLimit E (AlgebraicGeometry.BigFppfOver.toScheme B S hS) :=
    hpres i U₀ f₀ E (fun j => (hrel j.hom).snd f₀) pd
      (fun j => (hrel j.hom).isPullback f₀) hAffineE
  have : ∀ {j k : Over i} (q : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom
        ((E ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) :=
    fun {_ _} q => hAffineE q
  have hWred : IsReduced ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W) :=
    isReduced_cofilteredLimit_of_isReduced
      (E ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS) _
      (isLimitOfPreserves (AlgebraicGeometry.BigFppfOver.toScheme B S hS) hcE)
  refine ⟨W, hrelL.fst f₀, ?_, ?_, hWred⟩
  · have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
      refine ⟨?_⟩
      intro X Y Y' T f g f' g' hs hg
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Surjective) (hs.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hg
    exact presheaf_of_isPullback B S hS (hrelL.isPullback f₀).flip hsurj₀
  · exact presheaf_of_isPullback B S hS (hrelL.isPullback f₀).flip hetale₀

/-- A cofiltered inverse limit of reduced algebraic spaces with affine
transition morphisms is reduced. -/
@[stacks 0CUI]
public theorem Space.isReduced_limit
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hReduced : ∀ i, AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (D.obj i)
      (fun X : Scheme.{u} => IsReduced X)) :
    AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (limit D)
      (fun X : Scheme.{u} => IsReduced X) := by
  refine Space.isReduced_limit_of_relativelyRepresentable_of_preservesLimit B S hS D hD
    hAffine hReduced (fun i => relativelyRepresentable_of_isAffineHom B S hS (limit.π D i)
      (AlgebraicGeometry.Space.isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine)
      (hD i) (AlgebraicGeometry.Space.isAffineHom_limitπ B S hS D hSize hHomSize hAffine i))
    ?_
  intro i U₀ f₀ E r p _ hEaff
  exact preservesLimit_toScheme B S hS E
    (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i)
    fun j k => (mk_hom_over_le j k).trans_lt (hHomSize j.left k.left)

/-- **A cofiltered inverse limit of reduced algebraic spaces is reduced, with no cofinality
hypothesis.** The index category is only asked to have fewer objects than the site's size
cutoff with all its morphism types bounded by one cardinal `ν` below it, in exchange for the
transition morphisms being monomorphisms.

Both uses the registered form makes of its cardinality hypotheses survive that trade. The
projections from the limit are relatively representable by
`AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_mono`; and the system of base
changes of the stages along a chart `f₀ : yoneda U₀ ⟶ D i` consists of base changes of the
transition morphisms, so when those are monomorphisms every stage of that system maps
monomorphically to `U₀` and `AlgebraicGeometry.Space.monoSizeBound B S hS U₀` bounds all of
them at once, whatever the cardinality of the slice indexing them. The two hypotheses are
incomparable, and `@[stacks 0CUI]` stays on the form carrying the source's own one. -/
public theorem Space.isReduced_limit_of_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {ν : Cardinal.{u}}
    (hSize : Cardinal.mk I < B.cutoff) (hν : ν < B.cutoff)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) ≤ ν)
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f))
    (hReduced : ∀ i, AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (D.obj i)
      (fun X : Scheme.{u} => IsReduced X)) :
    AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (limit D)
      (fun X : Scheme.{u} => IsReduced X) := by
  refine Space.isReduced_limit_of_relativelyRepresentable_of_preservesLimit B S hS D hD
    hAffine hReduced (fun i => AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_mono
      B S hS D hSize hν hHomSize hD hAffine hMono i) ?_
  intro i U₀ f₀ E r p hsq hEaff
  refine preservesLimit_toScheme_of_size_le B S hS E
    (mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHomSize i) hν
    (fun j k => (mk_hom_over_le j k).trans (hHomSize j.left k.left))
    (AlgebraicGeometry.Space.monoSizeBound_lt_cutoff B S hS U₀) fun j => ?_
  exact AlgebraicGeometry.Space.size_le_monoSizeBound_of_mono B S hS (yoneda.map (r j))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsq j) (hMono j.hom))

/-- **A cofiltered inverse limit of reduced algebraic spaces is reduced, for a system with
uniformly bounded base changes.** The index category is only asked to have fewer objects than
the site's size cutoff with all its morphism types bounded by one cardinal `ν` below it, in
exchange for `AlgebraicGeometry.Space.BaseChangeSizeBounded`: the projections from the limit are
relatively representable by
`AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_baseChangeSizeBounded`, and the
system of base changes of the stages along a chart `f₀ : yoneda U₀ ⟶ D i` is bounded by the
cardinal that hypothesis attaches to `f₀`. -/
public theorem Space.isReduced_limit_of_baseChangeSizeBounded
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {ν : Cardinal.{u}}
    (hSize : Cardinal.mk I < B.cutoff) (hν : ν < B.cutoff)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) ≤ ν)
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hB : AlgebraicGeometry.Space.BaseChangeSizeBounded B S hS D)
    (hReduced : ∀ i, AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (D.obj i)
      (fun X : Scheme.{u} => IsReduced X)) :
    AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (limit D)
      (fun X : Scheme.{u} => IsReduced X) := by
  refine Space.isReduced_limit_of_relativelyRepresentable_of_preservesLimit B S hS D hD
    hAffine hReduced (fun i =>
      AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_baseChangeSizeBounded
        B S hS D hSize hν hHomSize hD hAffine hB i) ?_
  intro i U₀ f₀ E r p hsq hEaff
  obtain ⟨μ, hμ, hbound⟩ := hB i U₀ f₀
  exact preservesLimit_toScheme_of_size_le B S hS E
    (mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHomSize i) hν
    (fun j k => (mk_hom_over_le j k).trans (hHomSize j.left k.left)) hμ
    fun j => hbound j (E.obj j) (p j) (yoneda.map (r j)) (hsq j)

end AlgebraicGeometry

end
