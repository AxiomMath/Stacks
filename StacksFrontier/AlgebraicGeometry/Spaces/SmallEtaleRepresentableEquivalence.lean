module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares

/-!
# The small étale site of a representable algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf
site over `S`.  The presheaf `yoneda.obj U` is an algebraic space, and its small étale site
in the sense of `AlgebraicGeometry.Space.SmallEtale` — étale charts of a presheaf — is
equivalent to the small étale site of the *scheme* underlying `U`, taken in the big étale
site `AlgebraicGeometry.associatedBigEtaleSite B` carried by the same category of schemes.

The equivalence is the composite of the identification of scheme charts of a representable
presheaf with the slice over the representing object and of the comparison of the two
étale-ness conditions, and it matches the two Grothendieck topologies.

## Main definitions

* `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` is the equivalence between the
  small étale site of `yoneda.obj U` and the small étale site of the scheme underlying `U`.
* `CategoryTheory.yonedaCostructuredArrowOverEquiv` identifies the scheme charts of a
  representable presheaf with the slice category over the representing object.

## Main results

* `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_topology`: the equivalence
  carries the small étale topology of the scheme back to the small étale topology of the
  representable presheaf.
* `CategoryTheory.inducedTopology_symm_of_equivalence`: for an equivalence of categories,
  inducing a topology back along the inverse recovers the original topology.

## Implementation notes

Objects of the small étale site of a presheaf are étale charts, that is representable and
étale morphisms `yoneda.obj V ⟶ F`; for `F = yoneda.obj U` the Yoneda lemma turns such a
morphism into a morphism `V ⟶ U` of the big fppf site, and being étale as a chart becomes
being étale over `U` on underlying schemes.  The two conditions agree because the functor to
schemes preserves fibre products, which is where the fibre products of the underlying
category of a big fppf site are used.

Both inclusions of topologies are proved by induction over the generating covering families,
and the covering families correspond because both notions unfold to the same bounded étale
covering family of schemes.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory

/-- The scheme charts of a representable presheaf are the objects of the slice category over
the representing object: by the Yoneda lemma a morphism `yoneda.obj V ⟶ yoneda.obj T` is a
morphism `V ⟶ T`. -/
noncomputable def yonedaCostructuredArrowOverEquiv {C : Type u} [Category.{v} C] (T : C) :
    CostructuredArrow yoneda (yoneda.obj T) ≌ Over T where
  functor :=
    { obj := fun f => Over.mk (yonedaEquiv f.hom)
      map := fun {X Y} g => Over.homMk g.left
        ((yonedaEquiv_naturality Y.hom g.left).trans (congrArg yonedaEquiv (by simp))) }
  inverse :=
    { obj := fun f => CostructuredArrow.mk (yoneda.map f.hom)
      map := fun {X Y} g => CostructuredArrow.homMk g.left (by
        change yoneda.map g.left ≫ yoneda.map Y.hom = yoneda.map X.hom
        rw [← yoneda.map_comp]
        exact congrArg yoneda.map g.w) }
  unitIso := NatIso.ofComponents (fun f => CostructuredArrow.isoMk (Iso.refl _) (by
    have h : yoneda.map (yonedaEquiv f.hom) = f.hom := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_yoneda_map]
    simpa using h)) (by
      intro X Y f
      apply CostructuredArrow.hom_ext
      change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
      simp)
  counitIso := NatIso.ofComponents
    (fun f => Over.isoMk (Iso.refl _) (by simpa using (yonedaEquiv_yoneda_map f.hom).symm))
    (by
      intro X Y f
      apply Over.OverMorphism.ext
      change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
      simp)
  functor_unitIso_comp := by
    intro f
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- Pushing a pullback sieve forward along an equivalence is the pullback of the pushed-forward
sieve. -/
private theorem sieve_functorPushforward_pullback_equivalence
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    (R.pullback f).functorPushforward e.functor =
      (R.functorPushforward e.functor).pullback (e.functor.map f) := by
  ext Z g
  simp [Sieve.mem_functorPushforward_functor, Sieve.pullback_apply]

/-- An equivalence is cover-preserving from the topology generated by a precoverage as soon as
it carries the sieve generated by each covering presieve into the target topology. -/
private theorem coverPreserving_toGrothendieck_of_equivalence
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) (P : Precoverage C) (K : GrothendieckTopology D)
    (h : ∀ {V : C} {R : Presieve V}, R ∈ P V →
      (Sieve.generate R).functorPushforward e.functor ∈ K (e.functor.obj V)) :
    CoverPreserving P.toGrothendieck K e.functor := by
  constructor
  intro V R hR
  induction hR with
  | of V P hP => exact h hP
  | top V => simp
  | pullback V R hR W f ih =>
      rw [sieve_functorPushforward_pullback_equivalence]
      exact K.pullback_stable (e.functor.map f) ih
  | transitive V R T hR hT ihR ihT =>
      apply K.transitive ihR
      intro W g hg
      have hg' : R.arrows (e.inverse.map g ≫ e.unitInv.app V) :=
        (Sieve.mem_functorPushforward_functor (e := e) (S := R) (f := g)).mp hg
      have hg'' : ∃ (V₀ : C) (f : V₀ ⟶ V) (k : W ⟶ e.functor.obj V₀),
          R f ∧ k ≫ e.functor.map f = g := by
        refine ⟨e.inverse.obj W, e.inverse.map g ≫ e.unitInv.app V,
          e.counitInv.app W, hg', ?_⟩
        simp [Functor.map_comp]
      obtain ⟨V₀, f, k, hf, rfl⟩ := hg''
      rw [Sieve.pullback_comp, ← sieve_functorPushforward_pullback_equivalence e T f]
      exact K.pullback_stable k (ihT hf)

/-- Inducing a topology along an equivalence and then back along its inverse recovers the
original topology. -/
theorem inducedTopology_symm_of_equivalence {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (K : GrothendieckTopology D) (J : GrothendieckTopology C)
    (h : e.functor.inducedTopology K = J) :
    e.symm.functor.inducedTopology J = K := by
  subst h
  ext X R
  simp only [Functor.mem_inducedTopology_iff_of_isCoverDense]
  have hEq : Sieve.functorPushforward e.functor
      (Sieve.functorPushforward e.symm.functor R) = R.pullback (e.symm.unitInv.app X) := by
    simpa only [Equivalence.symm_inverse, Equivalence.symm_functor] using
      Sieve.functorPushforward_equivalence_eq_pullback e.symm R
  rw [hEq]
  exact K.pullback_mem_iff_of_isIso (i := e.symm.unitInv.app X) (S := R)

end CategoryTheory

namespace AlgebraicGeometry.Space

universe w

variable (B : BigFppfSite.{w}) (S : Scheme.{w}) (hS : B.Contains S)

/-- The small étale site of the presheaf represented by an object `U` of the big fppf site
over `S` is the small étale site of the scheme underlying `U`, in the big étale site carried
by the same category of schemes. -/
noncomputable def representedSmallEtaleEquivalence (U : BigFppfOver B S hS) :
    SmallEtale B S hS (yoneda.obj U) ≌
      _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property := by
  letI := B.hasPullbacks_schemes
  letI : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget B S hS) := inferInstance
  letI : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  letI : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let E := associatedBigEtaleSite B
  let T := (BigFppfOver.toScheme B S hS).obj U
  let e₀ := yonedaCostructuredArrowOverEquiv U
  let e := e₀.trans (Over.iteratedSliceEquiv U)
  let P : ObjectProperty (CostructuredArrow yoneda (yoneda.obj U)) :=
    IsEtaleChart B S hS (yoneda.obj U)
  let Q : ObjectProperty (Over U.left) := BigEtaleOver.IsEtaleOver E T U.left.property
  letI : (MorphismProperty.inverseImage (@Etale.{w} : MorphismProperty Scheme.{w})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    { of_isPullback := fun h hg => by
        change Etale ((BigFppfOver.toScheme B S hS).map _) at hg ⊢
        exact MorphismProperty.of_isPullback (h.map (BigFppfOver.toScheme B S hS)) hg }
  have hprop : Q.inverseImage e.functor = P := by
    funext V
    apply propext
    change Etale ((BigFppfOver.toScheme B S hS).map (yonedaEquiv V.hom)) ↔
      (MorphismProperty.inverseImage (@Etale.{w} : MorphismProperty Scheme.{w})
        (BigFppfOver.toScheme B S hS)).relative yoneda V.hom
    let f := yonedaEquiv V.hom
    have hmap : yoneda.map f = V.hom := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_yoneda_map]
    constructor
    · intro hf
      rw [← hmap]
      exact MorphismProperty.relative_map (F := yoneda) hf
    · intro hV
      rw [← hmap] at hV
      exact hV.2 (𝟙 _) (𝟙 _) f (by rw [hmap]; exact IsPullback.id_horiz _)
  letI : Q.IsClosedUnderIsomorphisms := by
    constructor
    intro V W i hV
    dsimp [Q] at hV ⊢
    change Etale (B.inclusion.map W.hom)
    have hi : IsIso (B.inclusion.map i.hom.left) := by
      let : IsIso i.hom.left := by
        change IsIso ((Over.forget U.left).map i.hom)
        infer_instance
      infer_instance
    have hcompEtale : Etale (B.inclusion.map i.hom.left ≫ B.inclusion.map W.hom) := by
      rw [← Functor.map_comp, Over.w i.hom]
      exact hV
    exact MorphismProperty.cancel_left_of_respectsIso
      (P := @Etale.{w}) (B.inclusion.map i.hom.left) _ |>.mp hcompEtale
  exact e.congrFullSubcategory hprop

/-- A covering family of the small étale site of `yoneda.obj U` is carried by the equivalence
to a covering family of the small étale site of the scheme underlying `U`, and conversely. -/
private theorem representedSmallEtale_mapCovering (U : BigFppfOver B S hS)
    (E : Covering (SmallEtale B S hS (yoneda.obj U))) :
    _root_.AlgebraicGeometry.SmallEtale.IsCovering (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property
        ⟨(representedSmallEtaleEquivalence B S hS U).functor.obj E.1,
          E.2.map (representedSmallEtaleEquivalence B S hS U).functor⟩ ↔
      SmallEtale.IsCovering B S hS (yoneda.obj U) E := by
  let E' : Covering (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
    ⟨(representedSmallEtaleEquivalence B S hS U).functor.obj E.1,
      E.2.map (representedSmallEtaleEquivalence B S hS U).functor⟩
  let Fsrc : Covering B.Schemes :=
    ⟨(SmallEtale.toSchemes B S hS (yoneda.obj U)).obj E.1,
      E.2.map (SmallEtale.toSchemes B S hS (yoneda.obj U))⟩
  let inc := _root_.AlgebraicGeometry.SmallEtale.inclusion (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  let forget := BigEtaleOver.forget (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  let Etgt : PreZeroHypercover ((inc.obj E'.1).left) := E'.2.map (inc ⋙ forget)
  let Ftgt : Covering B.Schemes := ⟨(inc.obj E'.1).left, Etgt⟩
  have hfamily : Ftgt = Fsrc := by
    dsimp [Ftgt, Etgt, Fsrc, E', inc, forget, representedSmallEtaleEquivalence,
      yonedaCostructuredArrowOverEquiv]
    rfl
  change CovBounded (IsEtaleCovering (κ := B.cutoff)) B.coveringBound Ftgt ↔
    B.etaleCovering Fsrc
  rw [hfamily]
  exact (etaleBounded_eq_fppfEtaleBounded B Fsrc).symm

/-- The inverse of the equivalence likewise matches covering families. -/
private theorem representedSmallEtale_mapCovering_symm (U : BigFppfOver B S hS)
    (E : Covering (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) :
    SmallEtale.IsCovering B S hS (yoneda.obj U)
        ⟨(representedSmallEtaleEquivalence B S hS U).inverse.obj E.1,
          E.2.map (representedSmallEtaleEquivalence B S hS U).inverse⟩ ↔
      _root_.AlgebraicGeometry.SmallEtale.IsCovering (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property E := by
  let e := representedSmallEtaleEquivalence B S hS U
  let E' : Covering (SmallEtale B S hS (yoneda.obj U)) :=
    ⟨e.inverse.obj E.1, E.2.map e.inverse⟩
  let E'' : Covering (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
    ⟨e.functor.obj E'.1, E'.2.map e.functor⟩
  let toSchemes := _root_.AlgebraicGeometry.SmallEtale.inclusion (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    BigEtaleOver.forget (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  let E''scheme : Covering B.Schemes :=
    ⟨toSchemes.obj E''.1, E''.2.map toSchemes⟩
  let Escheme : Covering B.Schemes := ⟨toSchemes.obj E.1, E.2.map toSchemes⟩
  have hfamily : E''scheme = Escheme := by
    dsimp [E''scheme, Escheme, E'', E', e, toSchemes, representedSmallEtaleEquivalence,
      yonedaCostructuredArrowOverEquiv]
    rfl
  refine (representedSmallEtale_mapCovering B S hS U E').symm.trans ?_
  change CovBounded (IsEtaleCovering (κ := B.cutoff)) B.coveringBound E''scheme ↔
    CovBounded (IsEtaleCovering (κ := B.cutoff)) B.coveringBound Escheme
  rw [hfamily]

/-- The scheme underlying an object of the big fppf site over `S` lies in the associated big
étale site. -/
private theorem associatedBigEtaleSite_contains_chart (U : BigFppfOver B S hS) :
    (associatedBigEtaleSite B).Contains ((BigFppfOver.toScheme B S hS).obj U) :=
  U.left.property

/-- The equivalence between the small étale site of `yoneda.obj U` and the small étale site
of the scheme underlying `U` matches their small étale topologies. -/
theorem representedSmallEtaleEquivalence_topology (U : BigFppfOver B S hS) :
    (representedSmallEtaleEquivalence B S hS U).functor.inducedTopology
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) =
      SmallEtale.topology B S hS (yoneda.obj U) := by
  let e := representedSmallEtaleEquivalence B S hS U
  let J := SmallEtale.topology B S hS (yoneda.obj U)
  let K := _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  have hChart := associatedBigEtaleSite_contains_chart B S hS U
  have hforward : CoverPreserving J K e.functor := by
    refine coverPreserving_toGrothendieck_of_equivalence e _ K ?_
    intro V R hP
    rcases (SmallEtale.mem_precoverage_iff B S hS (yoneda.obj U)).mp hP with
      ⟨E, rfl, hcov⟩
    rw [← Sieve.generate_map_eq_functorPushforward]
    apply Precoverage.generate_mem_toGrothendieck
    apply (_root_.AlgebraicGeometry.SmallEtale.mem_precoverage_iff
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) hChart).mpr
    refine ⟨E.map e.functor, ?_,
      (representedSmallEtale_mapCovering B S hS U ⟨V, E⟩).mpr hcov⟩
    simp [PreZeroHypercover.presieve₀_map]
  have hback : CoverPreserving K J e.inverse := by
    refine coverPreserving_toGrothendieck_of_equivalence e.symm _ J ?_
    intro V R hP
    rcases (_root_.AlgebraicGeometry.SmallEtale.mem_precoverage_iff
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      hChart).mp hP with ⟨E, rfl, hcov⟩
    rw [← Sieve.generate_map_eq_functorPushforward]
    apply Precoverage.generate_mem_toGrothendieck
    apply (SmallEtale.mem_precoverage_iff B S hS (yoneda.obj U)).mpr
    refine ⟨E.map e.inverse, ?_,
      (representedSmallEtale_mapCovering_symm B S hS U ⟨V, E⟩).mpr hcov⟩
    simp [PreZeroHypercover.presieve₀_map]
  have hsym : e.inverse.inducedTopology J = K := by
    apply le_antisymm
    · intro V R hR
      rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hR
      have hF := hforward.cover_preserve hR
      have hEq : Sieve.functorPushforward e.functor
          (Sieve.functorPushforward e.inverse R) = R.pullback (e.symm.unitInv.app V) :=
        Sieve.functorPushforward_equivalence_eq_pullback e.symm R
      rw [hEq] at hF
      exact (K.pullback_mem_iff_of_isIso (i := e.symm.unitInv.app V) (S := R)).mp hF
    · exact Functor.le_inducedTopology_iff.2
        (Functor.isContinuous_iff_coverPreserving.2 hback)
  have htop := inducedTopology_symm_of_equivalence e.symm J K hsym
  simpa only [Equivalence.symm_functor, Equivalence.symm_inverse] using htop

end AlgebraicGeometry.Space

end
