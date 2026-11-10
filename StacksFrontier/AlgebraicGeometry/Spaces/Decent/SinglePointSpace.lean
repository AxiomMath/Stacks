module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverZeroDimensionalLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology

/-!
# Decent algebraic spaces with one point

A decent algebraic space over a scheme `S` whose point set is a singleton is a scheme, and it is
the spectrum of a field as soon as it is reduced.

The route is the one the source gives in place of the general representability theorem. An
affine étale chart of such a space has finitely many points, all of them closed, so its space is
discrete and may be shrunk to a single point; that one-point affine chart is the spectrum of a
local ring of Krull dimension zero. The self-intersection of the shrunken chart has finitely many
points, again all closed, hence is affine, and it is étale over a zero-dimensional local ring,
hence finite locally free on both sides. The invariant functions of the resulting finite flat
equivalence relation represent the quotient, and the chart exhibits the space as that quotient.

## Main results

* `AlgebraicGeometry.Space.exists_field_isoSpec_of_subsingleton`: a nonempty reduced scheme whose
  space is a subsingleton is the spectrum of a field.
* `AlgebraicGeometry.Space.isRepresentable_of_subsingleton_points` is Stacks 047Z, part (1).
* `AlgebraicGeometry.Space.exists_iso_yoneda_spec_of_subsingleton_points` is Stacks 047Z,
  part (2).

## Implementation notes

"`|X|` is a singleton" is `Nonempty` together with `Subsingleton` on the point set of
Stacks 03BU, as in `AlgebraicGeometry.Space.isReduced_and_singleton_points_iff_hasFlatFieldCover`.
Reducedness is the étale-local property of Stacks 03E6 for reduced schemes.

Closedness of the points of an étale chart is Stacks 03K5: two points of a chart with the same
image in `|X|`, one a specialization of the other, are equal, and over a one-point space all
images agree, so the chart has no nontrivial specializations at all. With finitely many points
that makes its space discrete, and a finite discrete scheme is affine.

Finiteness of the self-intersection comes from condition (2) of Stacks 03JU, which decency
supplies through `AlgebraicGeometry.Space.IsDecentSpace.hasMonomorphicFieldRepresentative`: each
pair of points of the chart has a finite relation fibre, and the chart has finitely many points.

The passage from an étale morphism to a finite locally free one is
`AlgebraicGeometry.isFinite_of_isAffine_of_etale_over_krullDimLE_zero`, which is Stacks 06RS
followed by item (13) of Stacks 04GG; the quotient of the relation is Stacks 03BM, read through
`AlgebraicGeometry.Space.exists_quotient_of_isFiniteLocallyFree_relation`, and that the quotient
represents the space is `AlgebraicGeometry.Space.exists_iso_yoneda_of_isPullback`.

## References

* [Stacks Project, Tag 047Z](https://stacks.math.columbia.edu/tag/047Z)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Tag 06RS](https://stacks.math.columbia.edu/tag/06RS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Reduced schemes with one point -/

/-- The ring of global sections of a nonempty affine scheme whose space is a subsingleton is
nontrivial and has at most one prime ideal. -/
private theorem nontrivial_and_subsingleton_primeSpectrum_sections (Y : Scheme.{u}) [Nonempty Y]
    [Subsingleton Y] [IsAffine Y] :
    Nontrivial (Γ(Y, ⊤) : Type u) ∧ Subsingleton (PrimeSpectrum (Γ(Y, ⊤) : Type u)) := by
  classical
  have _ : Nonempty (Spec Γ(Y, ⊤)) := ⟨Y.isoSpec.hom (Classical.arbitrary Y)⟩
  exact ⟨PrimeSpectrum.nonempty_iff_nontrivial.mp ‹_›,
    ⟨fun a b ↦ Y.isoSpec.inv.injective (Subsingleton.elim _ _)⟩⟩

/-- **A nonempty reduced scheme whose space is a subsingleton is the spectrum of a field.** Such
a scheme is affine, and its ring of global sections is reduced with exactly one prime ideal. -/
theorem exists_field_isoSpec_of_subsingleton (Y : Scheme.{u}) [Nonempty Y] [Subsingleton Y]
    [IsReduced Y] : ∃ (k : Type u) (_ : Field k), Nonempty (Y ≅ Spec (.of k)) := by
  classical
  have _ : IsAffine Y := inferInstance
  have hred : IsReduced (Spec Γ(Y, ⊤)) :=
    ObjectProperty.prop_of_iso IsReduced Y.isoSpec ‹IsReduced Y›
  have _ : _root_.IsReduced (Γ(Y, ⊤) : Type u) := (affine_isReduced_iff Γ(Y, ⊤)).mp hred
  obtain ⟨_, _⟩ := nontrivial_and_subsingleton_primeSpectrum_sections Y
  have hfield : IsField (Γ(Y, ⊤) : Type u) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp ‹_›
  exact ⟨Γ(Y, ⊤), hfield.toField, ⟨Y.isoSpec⟩⟩

/-- The ring of global sections of a nonempty affine scheme whose space is a subsingleton is a
local ring of Krull dimension zero: it is nontrivial and has exactly one prime ideal. -/
private theorem krullDimLE_zero_and_isLocalRing_sections (Y : Scheme.{u}) [Nonempty Y]
    [Subsingleton Y] [IsAffine Y] :
    Ring.KrullDimLE 0 (Γ(Y, ⊤) : Type u) ∧ IsLocalRing (Γ(Y, ⊤) : Type u) := by
  classical
  obtain ⟨_, hssp⟩ := nontrivial_and_subsingleton_primeSpectrum_sections Y
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum (Γ(Y, ⊤) : Type u)) := inferInstance
  refine ((Ring.krullDimLE_zero_and_isLocalRing_tfae (Γ(Y, ⊤) : Type u)).out 2 1 rfl rfl).1
    ⟨p.asIdeal, p.isPrime, fun I hI ↦ ?_⟩
  exact congrArg PrimeSpectrum.asIdeal (hssp.allEq (⟨I, hI⟩ : PrimeSpectrum _) p)

/-! ### Étale charts of a space with one point -/

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Étaleness of morphisms into a presheaf, read as a relative property of the morphisms of
schemes underlying their representable base changes, is stable under composition. -/
private theorem presheaf_etale_isStableUnderComposition :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition := by
  have _ := inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  exact MorphismProperty.relative_isStableUnderComposition _

/-- Precomposing an étale morphism into a presheaf with the image of an étale morphism of
schemes gives an étale morphism. -/
private theorem presheaf_etale_yoneda_map_comp {V' V : BigFppfOver B S hS} (f : V' ⟶ V)
    (hf : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f)) {ψ : yoneda.obj V ⟶ X}
    (hψ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map f ≫ ψ) := by
  have _ := presheaf_etale_isStableUnderComposition B S hS
  exact MorphismProperty.comp_mem _ _ _
    ((presheaf_yoneda_map_iff B S hS AlgebraicGeometry.Etale.etale_isStableUnderBaseChange f).2
      hf) hψ

/-- **Stacks 03K5 over a one-point space.** An étale chart of an algebraic space whose charts by
affine schemes have finite fibres and whose point set is a subsingleton has no nontrivial
specializations: all its points have the same image, so Stacks 03K5 identifies any two of them
that are comparable. -/
private theorem t1Space_of_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hα : HasFiniteChartFibersAtEveryPoint B S hS X)
    (hsub : Subsingleton (points B S hS X)) (V : BigFppfOver B S hS)
    (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ) :
    T1Space ((BigFppfOver.toScheme B S hS).obj V) := by
  refine t1Space_iff_specializes_imp_eq.2 fun p q hpq ↦ ?_
  set e := schemePointsHomeomorph B S hS V with he
  have hspec : e.symm p ⤳ e.symm q := hpq.map e.symm.continuous
  have himg : pointsMap B S hS (yoneda.obj V) ψ (e.symm q) =
      pointsMap B S hS (yoneda.obj V) ψ (e.symm p) := Subsingleton.elim _ _
  have hqp : e.symm q = e.symm p :=
    eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX hα V ψ hψ
      (e.symm q) (e.symm p) himg hspec
  simpa using congrArg e hqp.symm

/-- The points of an étale chart by an affine scheme of an algebraic space with a subsingleton
point set form a finite set: the chart has finite fibres and there is at most one point to lie
over. -/
private theorem finite_of_etaleChart (hα : HasFiniteChartFibersAtEveryPoint B S hS X)
    (hsub : Subsingleton (points B S hS X)) (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ) :
    Finite ((BigFppfOver.toScheme B S hS).obj V) := by
  have hpts : Finite (points B S hS (yoneda.obj V)) := by
    refine Finite.of_finite_univ (Set.Finite.of_finite_fibers
      (pointsMap B S hS (yoneda.obj V) ψ) (Set.toFinite _) ?_)
    intro x _
    simpa using hα x V hV ψ hψ
  exact Finite.of_equiv _ (schemePointsHomeomorph B S hS V).toEquiv

/-- A decent algebraic space over `S` with a singleton point set admits a surjective étale chart
by a scheme with exactly one point. The chart is obtained by shrinking an affine chart to a
single point of its space, which is legitimate because that space is finite and discrete. -/
private theorem exists_subsingleton_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hne : Nonempty (points B S hS X))
    (hsub : Subsingleton (points B S hS X)) :
    ∃ (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X),
      Nonempty ((BigFppfOver.toScheme B S hS).obj V) ∧
        Subsingleton ((BigFppfOver.toScheme B S hS).obj V) ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf ψ := by
  classical
  have hα : HasFiniteChartFibersAtEveryPoint B S hS X :=
    hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec
  have _ : Finite (points B S hS X) := Finite.of_subsingleton
  have hqc : IsQuasiCompactSpace B S hS X :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).2 inferInstance
  obtain ⟨U, φ, hUaff, hUsurj, hUetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hqc
  have hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ :=
    (isEtale_iff_presheaf_of_yoneda B S hS φ).1 hUetale
  have _ : Finite ((BigFppfOver.toScheme B S hS).obj U) :=
    finite_of_etaleChart B S hS hα hsub U hUaff φ hφ
  have _ : T1Space ((BigFppfOver.toScheme B S hS).obj U) :=
    t1Space_of_etaleChart B S hS hX hα hsub U φ hφ
  obtain ⟨u⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj U) := by
    obtain ⟨x⟩ := hne
    obtain ⟨p, -⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U φ).1 hUsurj x
    exact ⟨schemePointsHomeomorph B S hS U p⟩
  have hopen : IsOpen ({u} : Set ((BigFppfOver.toScheme B S hS).obj U)) := isOpen_discrete _
  refine ⟨openSiteObject B S hS U ⟨{u}, hopen⟩,
    yoneda.map (openSiteObjectHom B S hS U ⟨{u}, hopen⟩) ≫ φ, ⟨⟨u, rfl⟩⟩,
    (Set.subsingleton_coe _).2 Set.subsingleton_singleton, ?_⟩
  have hι : AlgebraicGeometry.Etale
      (Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj U) ⟨{u}, hopen⟩) := inferInstance
  exact presheaf_etale_yoneda_map_comp B S hS _
    (by rw [map_openSiteObjectHom]; exact hι) hφ

end Chart

/-! ### The two parts of Stacks 047Z -/

section SinglePoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_SinglePointSpace :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a direct shortcut. -/
local instance (priority := high) hasPullback_presheaf_SinglePointSpace
    {P Q W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ W) (g : Q ⟶ W) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 047Z, part (1).** A decent algebraic space over `S` whose point set is a singleton
is a scheme. -/
@[stacks 047Z "part (1)"]
theorem isRepresentable_of_subsingleton_points (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hne : Nonempty (points B S hS X))
    (hsub : Subsingleton (points B S hS X)) : X.IsRepresentable := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let H : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have hα : HasFiniteChartFibersAtEveryPoint B S hS X :=
    hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec
  obtain ⟨V, ψ, hVne, _, hψ⟩ := exists_subsingleton_etaleChart B S hS hX hdec hne hsub
  have hVaff : IsAffine (T.obj V) := inferInstance
  -- the shrunken chart is still surjective, the space having a single point
  have hψsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) T).presheaf ψ := by
    refine (surjective_iff_surjective_pointsMap B S hS X hX V ψ).2 fun x ↦ ?_
    obtain ⟨v⟩ := hVne
    exact ⟨(schemePointsHomeomorph B S hS V).symm v, Subsingleton.elim _ _⟩
  -- the kernel pair of the chart
  have hrep : yoneda.relativelyRepresentable ψ := hX.diagonal_representable.of_diag ψ
  let R : BigFppfOver B S hS := hrep.pullback ψ
  let t : R ⟶ V := hrep.fst' ψ
  let s : R ⟶ V := hrep.snd ψ
  have hpb : IsPullback (yoneda.map t) (yoneda.map s) ψ ψ := hrep.isPullback' ψ
  have htE : Etale (T.map t) := hψ.property ψ (yoneda.map s) t hpb.flip
  have hsE : Etale (T.map s) := hψ.property ψ (yoneda.map t) s hpb
  -- the self-intersection has finitely many points: each pair of points of the chart has a
  -- finite relation fibre, and the chart has at most one point
  obtain ⟨x⟩ := hne
  have hrel : HasFiniteRelationFiberAtEveryEtaleChart B S hS X x :=
    hasFiniteRelationFiberAtEveryEtaleChart_of_hasMonomorphicFieldRepresentative B S hS X hX x
      (IsDecentSpace.hasMonomorphicFieldRepresentative B S hS X hdec x)
  have _ : Finite (points B S hS (yoneda.obj V)) :=
    Finite.of_equiv _ (schemePointsHomeomorph B S hS V).toEquiv.symm
  have hpbfin : Finite (points B S hS (pullback ψ ψ)) := by
    refine Finite.of_finite_univ (Set.Finite.of_finite_fibers
      (fun r ↦ (pointsMap B S hS (pullback ψ ψ) (pullback.fst ψ ψ) r,
        pointsMap B S hS (pullback ψ ψ) (pullback.snd ψ ψ) r)) (Set.toFinite _) ?_)
    rintro ⟨a, b⟩ -
    exact (hrel V ψ a b ((isEtale_iff_presheaf_of_yoneda B S hS ψ).2 hψ)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)).subset
        fun r hr ↦ ⟨congrArg Prod.fst hr.2, congrArg Prod.snd hr.2⟩
  have _ : Finite (points B S hS (yoneda.obj R)) :=
    Finite.of_equiv _ (pointsEquivOfIso B S hS hpb.isoPullback).symm
  have _ : Finite (T.obj R) := Finite.of_equiv _ (schemePointsHomeomorph B S hS R).toEquiv
  have _ : T1Space (T.obj R) :=
    t1Space_of_etaleChart B S hS hX hα hsub R (yoneda.map t ≫ ψ)
      (presheaf_etale_yoneda_map_comp B S hS t htE hψ)
  have hRaff : IsAffine (T.obj R) := inferInstance
  -- the one-point affine chart is the spectrum of a local ring of Krull dimension zero, over
  -- which an affine étale scheme is finite
  obtain ⟨_, _⟩ := krullDimLE_zero_and_isLocalRing_sections (T.obj V)
  have _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfin : ∀ q : T.obj R ⟶ T.obj V, Etale q → AlgebraicGeometry.IsFinite q := by
    intro q hq
    have _ : Etale (q ≫ (T.obj V).isoSpec.hom) :=
      MorphismProperty.RespectsIso.postcomp (@Etale.{u}) (T.obj V).isoSpec.hom q hq
    exact (MorphismProperty.cancel_right_of_respectsIso (@AlgebraicGeometry.IsFinite.{u}) q
      (T.obj V).isoSpec.hom).1 <| isFinite_of_isAffine_of_etale_over_krullDimLE_zero
        (Γ(T.obj V, ⊤) : Type u) (q ≫ (T.obj V).isoSpec.hom)
  have hFLF : ∀ q : T.obj R ⟶ T.obj V, Etale q → Stacks.Morphisms.IsFiniteLocallyFree q :=
    fun q hq ↦
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation q).2
      ⟨hfin q hq, inferInstance, inferInstance⟩
  have htFLF := hFLF _ htE
  have hsFLF := hFLF _ hsE
  -- the relation, read in schemes over `S`, and its quotient
  have _ : IsAffine (H.obj V).left := hVaff
  have _ : IsAffine (H.obj R).left := hRaff
  have _ : Stacks.Morphisms.IsFiniteLocallyFree (H.map t).left := htFLF
  have _ : Stacks.Morphisms.IsFiniteLocallyFree (H.map s).left := hsFLF
  have _ : IsEquivalenceRelation (H.map t) (H.map s) :=
    isEquivalenceRelation_of_isPullback B S hS ψ t s hpb
  obtain ⟨A, _, g, π, hsize, _, hsurjπ, hqpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S (H.map t) (H.map s)
  have hA : B.Contains (Spec (CommRingCat.of A)) := lt_of_le_of_lt hsize V.left.2
  obtain ⟨-, e, -, -⟩ :=
    exists_iso_yoneda_of_isPullback B S hS hX ψ t s hpb hψsurj hψ
      (U' := Over.mk (⟨g⟩ : B.obj hA ⟶ B.obj hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left) hsurjπ hqpb
  exact isRepresentable_of_natIso _ e.symm

/-- **Stacks 047Z, part (2).** A reduced decent algebraic space over `S` whose point set is a
singleton is the spectrum of a field. -/
@[stacks 047Z "part (2)"]
theorem exists_iso_yoneda_spec_of_subsingleton_points (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hne : Nonempty (points B S hS X))
    (hsub : Subsingleton (points B S hS X))
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsReduced Y)) :
    ∃ (M : BigFppfOver B S hS) (k : Type u) (_ : Field k),
      Nonempty ((BigFppfOver.toScheme B S hS).obj M ≅ Spec (.of k)) ∧
        Nonempty (X ≅ yoneda.obj M) := by
  classical
  have _ : X.IsRepresentable := isRepresentable_of_subsingleton_points B S hS hX hdec hne hsub
  let M : BigFppfOver B S hS := Functor.reprX X
  let e : yoneda.obj M ≅ X := (Functor.representableBy X).toIso
  have _ : Subsingleton (points B S hS (yoneda.obj M)) := (pointsEquivOfIso B S hS e).subsingleton
  have hneM : Nonempty (points B S hS (yoneda.obj M)) := hne.map (pointsEquivOfIso B S hS e).symm
  have _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj M) :=
    (schemePointsHomeomorph B S hS M).toEquiv.symm.subsingleton
  have _ : Nonempty ((BigFppfOver.toScheme B S hS).obj M) :=
    hneM.map (schemePointsHomeomorph B S hS M)
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj M) :=
    (exists_atlas_iff_of_representable B S hS X (fun Y : Scheme.{u} ↦ IsReduced Y) M e.symm).1
      hred
  obtain ⟨k, _, hiso⟩ :=
    exists_field_isoSpec_of_subsingleton ((BigFppfOver.toScheme B S hS).obj M)
  exact ⟨M, k, ‹Field k›, hiso, ⟨e.symm⟩⟩

end SinglePoint

end AlgebraicGeometry.Space

-- Remark 03E0 observes that a decent algebraic space with one point is a scheme; that is part (1)
-- of Stacks 047Z above.
add_to_stacks 03E0 "a decent algebraic space with one point is a scheme"
  AlgebraicGeometry.Space.isRepresentable_of_subsingleton_points

end
