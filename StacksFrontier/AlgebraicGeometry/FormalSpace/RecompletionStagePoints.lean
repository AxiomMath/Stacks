module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAdicPresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionPointTopology
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentedSheafPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition

/-!
# The points of a McQuillan affine formal algebraic space, in ring terms

Let `A` be a weakly admissible topological ring presenting the fppf sheaf `X` over `S` by a
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation`. This file reads the points of `X`
as prime ideals of `A`.

## Main results

* `AlgebraicGeometry.FormalSpace.isHomeomorph_pointsMapULift_weakIdealStagePoint`: **the
  tautological point of a stage of a weak-ideal presentation is a homeomorphism on points.**

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology Space.pointTopologyULift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  (X : FppfSheaf B S hS) (P : WeakIdealColimitPresentation B S hS A X)

/-- **The tautological point of a stage of a weak-ideal presentation is a homeomorphism on
points.** The stage morphism `Spec (A ⧸ K) ⟶ X` is a representable thickening by **Stacks
0AI9** in the form `AlgebraicGeometry.FormalSpace.isThickening_quotient`, and a representable
thickening is a homeomorphism on points
(`AlgebraicGeometry.FormalSpace.isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift`).

So `|Spec (A ⧸ K)| = |X|` for every weak ideal of definition `K`, which is what reads a closed
subset of `|X|` as a closed subset of the spectrum of a quotient of `A`. -/
theorem isHomeomorph_pointsMapULift_weakIdealStagePoint
    (hA : TopologicalRing.IsWeaklyAdmissible A) (K : WeakIdeals A) :
    @IsHomeomorph _ _
      (Space.pointTopologyULift.{u + 1} B S hS
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K))).obj)
      (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS _ (weakIdealStagePoint B S hS A P K).hom) :=
  isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift
    ((relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _ _).mp
      (isThickening_quotient B S hS A X P hA K))

/-! ### The spectrum of a quotient of `A` as the point space of `X` -/

/-- The point of `X` determined by a point of the scheme underlying the stage of a weak-ideal
presentation at `K`: the stage is a homeomorphism on points by
`AlgebraicGeometry.FormalSpace.isHomeomorph_pointsMapULift_weakIdealStagePoint`, and the points
of the stage are the points of the scheme underlying it by
`AlgebraicGeometry.Space.pointsULiftHomeomorphScheme`. -/
def stagePointsMap (K : WeakIdeals A) :
    (BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj
        (P.diagram.obj K)) →
      Space.pointsULift.{u + 1} B S hS X.obj :=
  fun x ↦ Space.pointsMapULift.{u + 1} B S hS _ (weakIdealStagePoint B S hS A P K).hom
    ((Space.pointsULiftHomeomorphScheme B S hS
      ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K))).symm x)

/-- `AlgebraicGeometry.FormalSpace.stagePointsMap` is a bijection. -/
theorem bijective_stagePointsMap (hA : TopologicalRing.IsWeaklyAdmissible A)
    (K : WeakIdeals A) :
    Function.Bijective (stagePointsMap B S hS A X P K) :=
  (isHomeomorph_pointsMapULift_weakIdealStagePoint B S hS A X P hA K).bijective.comp
    (Space.pointsULiftHomeomorphScheme B S hS
      ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K))).symm.bijective

/-- The point of `X` of a composite `U ⟶ Spec (A ⧸ K) ⟶ X` named by a point of `U` is the image
under `AlgebraicGeometry.FormalSpace.stagePointsMap` of its image in the stage. -/
private theorem pointsMapULift_comp_weakIdealStagePoint_symm {A : Type u} [CommRing A]
    [TopologicalSpace A] {X : FppfSheaf B S hS} (P : WeakIdealColimitPresentation B S hS A X)
    (K : WeakIdeals A)
    {U : BigFppfOver B S hS} (c : U ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K))
    (y : (BigFppfOver.toScheme B S hS).obj U) :
    Space.pointsMapULift.{u + 1} B S hS _
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map c ≫
          weakIdealStagePoint B S hS A P K).hom
        ((Space.pointsULiftHomeomorphScheme B S hS U).symm y) =
      stagePointsMap B S hS A X P K ((BigFppfOver.toScheme B S hS).map c y) := by
  rw [ObjectProperty.FullSubcategory.comp_hom, Space.pointsMapULift_comp, Function.comp_apply,
    Space.pointsMapULift_pointsULiftHomeomorphScheme_symm]
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **The set of points of a morphism into `X` factoring through a stage.** For a morphism `c`
of the site into the stage at `K`, the set of points of the composite `U ⟶ Spec (A ⧸ K) ⟶ X` is
the image under `AlgebraicGeometry.FormalSpace.stagePointsMap` of the set of points of the
morphism of schemes underlying `c`. -/
theorem range_pointsMapULift_comp_weakIdealStagePoint (K : WeakIdeals A)
    {U : BigFppfOver B S hS}
    (c : U ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)) :
    Set.range (Space.pointsMapULift.{u + 1} B S hS _
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map c ≫
          weakIdealStagePoint B S hS A P K).hom) =
      stagePointsMap B S hS A X P K '' Set.range ((BigFppfOver.toScheme B S hS).map c) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine ⟨_, ⟨Space.pointsULiftHomeomorphScheme B S hS U x, rfl⟩, ?_⟩
    rw [← pointsMapULift_comp_weakIdealStagePoint_symm B S hS P K c,
      Homeomorph.symm_apply_apply]
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, pointsMapULift_comp_weakIdealStagePoint_symm B S hS P K c y⟩

/-! ### The image of a morphism from an affine scheme to the spectrum of a ring -/

section Affine

/-- The image of the morphism to `Spec R` attached to a ring map `R ⟶ Γ(V, ⊤)` on an affine
`V` is the image of the induced map of prime spectra. -/
private theorem range_base_isoSpec_hom_specMap {V : Scheme.{u}} [IsAffine V]
    {R : CommRingCat.{u}} (g : R ⟶ Γ(V, ⊤)) :
    Set.range (V.isoSpec.hom ≫ Spec.map g).base =
      Set.range (PrimeSpectrum.comap g.hom) := by
  have hsurj : Function.Surjective (V.isoSpec.hom.base) := fun p ↦
    ⟨V.isoSpec.inv.base p, by simp⟩
  have hcomp : ∀ x : V, (V.isoSpec.hom ≫ Spec.map g).base x =
      PrimeSpectrum.comap g.hom (V.isoSpec.hom.base x) :=
    fun x ↦ Scheme.Hom.comp_apply V.isoSpec.hom (Spec.map g) x
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨V.isoSpec.hom.base x, (hcomp x).symm⟩
  · rintro _ ⟨p, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj p
    exact ⟨x, hcomp x⟩

/-- **The image of a morphism from an affine scheme to a spectrum is the image of the induced
map of prime spectra.** The morphism is `V.toSpecΓ` followed by the spectrum of the ring map it
induces on global sections, and `V.toSpecΓ` is an isomorphism for an affine `V`. -/
theorem range_base_eq_range_comap {V : Scheme.{u}} [IsAffine V] {R : CommRingCat.{u}}
    (f : V ⟶ Spec R) :
    Set.range f.base =
      Set.range (PrimeSpectrum.comap ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom) := by
  have hf : V.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  conv_lhs => rw [← hf]
  exact range_base_isoSpec_hom_specMap _

/-- **The image of a closed immersion of an affine scheme into a spectrum is the zero locus of
the ideal it cuts out.** -/
theorem range_base_eq_zeroLocus_ker {V : Scheme.{u}} [IsAffine V] {R : CommRingCat.{u}}
    (f : V ⟶ Spec R)
    (hsurj : Function.Surjective ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom) :
    Set.range f.base =
      PrimeSpectrum.zeroLocus
        ((RingHom.ker ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom : Ideal R) : Set R) := by
  rw [range_base_eq_range_comap f, _root_.range_comap_of_surjective _ _ hsurj]

end Affine

/-! ### Compatibility of the stages with the transition morphisms -/

attribute [local instance] sheaf_hasColimits

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The tautological point of the stage at `J` factors through the stage at `K` whenever
`K ≤ J` as ideals, by the compatibility of the colimit injections with the transitions. -/
theorem sheafifiedYoneda_map_comp_weakIdealStagePoint {J K : WeakIdeals A} (f : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)) ≫
        weakIdealStagePoint B S hS A P K =
      weakIdealStagePoint B S hS A P J := by
  show ((P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f) ≫
    (colimit.ι _ K ≫ P.colimitIso.inv) = colimit.ι _ J ≫ P.colimitIso.inv
  rw [← Category.assoc, colimit.w]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The identification of the points of a stage with the points of `X` is compatible with the
transition morphisms of the presentation. -/
theorem stagePointsMap_map {J K : WeakIdeals A} (f : J ⟶ K)
    (x : (BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj
      (P.diagram.obj J))) :
    stagePointsMap B S hS A X P J x =
      stagePointsMap B S hS A X P K
        ((BigFppfOver.toScheme B S hS).map
          ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)) x) := by
  rw [← pointsMapULift_comp_weakIdealStagePoint_symm B S hS P K
      ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)) x,
    sheafifiedYoneda_map_comp_weakIdealStagePoint B S hS A X P f]
  rfl

/-! ### The ideal cut out by a point factoring through a stage -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The morphism of schemes to `Spec A` attached to a point of `X` factoring through the stage
at `K` is that factorisation, read as a morphism to `Spec (A ⧸ K)`, followed by the closed
immersion `Spec (A ⧸ K) ⟶ Spec A`. -/
theorem app_mapToScheme_comp_weakIdealStagePoint (K : WeakIdeals A) {W : BigFppfOver B S hS}
    (b : W ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)) :
    (mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app W
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫
          weakIdealStagePoint B S hS A P K) =
      ((BigFppfOver.toScheme B S hS).map b ≫ (P.quotientIso K).hom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) := by
  have h := (mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app_naturality
    ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)) W b
    (weakIdealStagePoint B S hS A P K)
  rw [h]
  show (BigFppfOver.toScheme B S hS).map b ≫
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (weakIdealStagePoint B S hS A P K ≫ weakIdealToSpecPoints B S hS A P)).down = _
  rw [weakIdealToSpecPoints_comp_stage]
  exact (Category.assoc _ _ _).symm

/-- The ring map `A ⧸ K ⟶ Γ(W, 𝒪)` cut out by a morphism `W ⟶ Spec (A ⧸ K)` of the site into
the stage at `K`: the factorisation through `AlgebraicGeometry.FormalSpace.stageIdeal` of the
ring map attached to the corresponding point of `X`. -/
def stageQuotientRingMap (K : WeakIdeals A) {W : BigFppfOver B S hS}
    (b : W ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)) :
    (A ⧸ K.1) →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ K.1))).inv ≫
    ((BigFppfOver.toScheme B S hS).map b ≫ (P.quotientIso K).hom).appTop).hom

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The ring map `A ⟶ Γ(W, 𝒪)` attached to a point of `X` factoring through the stage at `K`
factors through the quotient `A ⧸ K`. -/
theorem pointRingMap_comp_weakIdealStagePoint (K : WeakIdeals A) {W : BigFppfOver B S hS}
    (b : W ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)) (a : A) :
    pointRingMap B S hS A P W
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫
          weakIdealStagePoint B S hS A P K) a =
      stageQuotientRingMap B S hS A X P K b (Ideal.Quotient.mk K.1 a) := by
  have hmap : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        ((mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app W
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫
            weakIdealStagePoint B S hS A P K)).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk K.1) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ K.1))).inv ≫
          ((BigFppfOver.toScheme B S hS).map b ≫ (P.quotientIso K).hom).appTop) := by
    rw [app_mapToScheme_comp_weakIdealStagePoint, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have h := congrArg (fun φ : CommRingCat.of A ⟶
    CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) ↦ φ.hom a) hmap
  rw [CommRingCat.comp_apply] at h
  exact h

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **The ideal of `A` cut out by a point of `X` factoring through the stage at `K`** is the
inverse image in `A` of the ideal of `A ⧸ K` cut out by the factorisation. -/
theorem stageIdeal_comp_weakIdealStagePoint (K : WeakIdeals A) {W : BigFppfOver B S hS}
    (b : W ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)) :
    stageIdeal B S hS A P W
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫
          weakIdealStagePoint B S hS A P K) =
      Ideal.comap (Ideal.Quotient.mk K.1)
        (RingHom.ker (stageQuotientRingMap B S hS A X P K b)) := by
  refine Ideal.ext fun a ↦ ?_
  rw [stageIdeal, RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker,
    pointRingMap_comp_weakIdealStagePoint]

/-! ### The prime spectrum of a quotient of `A` as the point space of `X` -/

/-- **The point of `X` named by a prime ideal of the quotient `A ⧸ K`** by a weak ideal of
definition: the stage at `K` is the spectrum of that quotient, and its points are the points of
`X`. -/
def stagePrimeMap (K : WeakIdeals A) :
    PrimeSpectrum (A ⧸ K.1) → Space.pointsULift.{u + 1} B S hS X.obj :=
  fun p ↦ stagePointsMap B S hS A X P K ((P.quotientIso K).inv.base p)

/-- **The prime spectrum of `A ⧸ K` is the point space of `X`**, for every weak ideal of
definition `K` of a weakly admissible presenting ring. -/
theorem isHomeomorph_stagePrimeMap (hA : TopologicalRing.IsWeaklyAdmissible A)
    (K : WeakIdeals A) :
    IsHomeomorph (stagePrimeMap B S hS A X P K) :=
  ((isHomeomorph_pointsMapULift_weakIdealStagePoint B S hS A X P hA K).comp
      (Space.pointsULiftHomeomorphScheme B S hS
        ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K))).symm.isHomeomorph).comp
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (P.quotientIso K))).symm.isHomeomorph

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The identification of the prime spectrum of `A ⧸ K` with the points of `X` is compatible
with the transition maps: for `K ≤ J` the point named by a prime of `A ⧸ J` is the point named
by its image in `A ⧸ K`. -/
theorem stagePrimeMap_comap {J K : WeakIdeals A} (f : J ⟶ K) (p : PrimeSpectrum (A ⧸ J.1)) :
    stagePrimeMap B S hS A X P J p =
      stagePrimeMap B S hS A X P K
        (PrimeSpectrum.comap (Ideal.Quotient.factor (show (K.1 : Ideal A) ≤ J.1 from leOfHom f))
          p) := by
  have hiso : (P.quotientIso J).inv ≫ (BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)) =
      Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (show (K.1 : Ideal A) ≤ J.1 from leOfHom f))) ≫
        (P.quotientIso K).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact P.quotientIso_natural f
  rw [stagePrimeMap, stagePrimeMap, stagePointsMap_map B S hS A X P f]
  refine congrArg (stagePointsMap B S hS A X P K) ?_
  show ((P.quotientIso J).inv ≫ (BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f))).base p =
    (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show (K.1 : Ideal A) ≤ J.1 from leOfHom f))) ≫
      (P.quotientIso K).inv).base p
  exact congrArg (fun k : Spec (CommRingCat.of (A ⧸ J.1)) ⟶
    (BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj
      (P.diagram.obj K)) ↦ k.base p) hiso

/-! ### The ideal cutting out a closed set of points -/

/-- An ideal `𝔞 ⊆ A` **cuts out** a set `T` of points of `X` **at the stage `K`** when the primes
of `A ⧸ K` naming the points of `T` are exactly those containing the image of `𝔞`. -/
def CutsOutAtStage (K : WeakIdeals A) (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (𝔞 : Ideal A) : Prop :=
  stagePrimeMap B S hS A X P K ⁻¹' T =
    PrimeSpectrum.zeroLocus
      ((Ideal.map (Ideal.Quotient.mk K.1) 𝔞 : Ideal (A ⧸ K.1)) : Set (A ⧸ K.1))

include B S hS X P in
/-- The transition map of prime spectra attached to `L ≤ K` is a bijection: both spectra are the
point space of `X`, compatibly. -/
theorem bijective_comap_factor (hA : TopologicalRing.IsWeaklyAdmissible A)
    {K L : WeakIdeals A} (f : K ⟶ L) :
    Function.Bijective (PrimeSpectrum.comap
      (Ideal.Quotient.factor (show (L.1 : Ideal A) ≤ K.1 from leOfHom f))) := by
  have hK := (isHomeomorph_stagePrimeMap B S hS A X P hA K).bijective
  have hL := (isHomeomorph_stagePrimeMap B S hS A X P hA L).bijective
  refine ⟨fun x y hxy ↦ hK.injective ?_, fun q ↦ ?_⟩
  · rw [stagePrimeMap_comap B S hS A X P f, stagePrimeMap_comap B S hS A X P f, hxy]
  · obtain ⟨x, hx⟩ := hK.surjective (stagePrimeMap B S hS A X P L q)
    refine ⟨x, hL.injective ?_⟩
    rw [← stagePrimeMap_comap B S hS A X P f, hx]

/-- Cutting out `T` does not depend on the stage: the statements at `K` and at a smaller weak
ideal `L` are equivalent, both being the same statement about the point space of `X`. -/
theorem cutsOutAtStage_iff_of_hom (hA : TopologicalRing.IsWeaklyAdmissible A)
    {K L : WeakIdeals A} (f : K ⟶ L)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj)) (𝔞 : Ideal A) :
    CutsOutAtStage B S hS A X P K T 𝔞 ↔ CutsOutAtStage B S hS A X P L T 𝔞 := by
  have hle : (L.1 : Ideal A) ≤ K.1 := leOfHom f
  have hpre : stagePrimeMap B S hS A X P K ⁻¹' T =
      PrimeSpectrum.comap (Ideal.Quotient.factor hle) ⁻¹'
        (stagePrimeMap B S hS A X P L ⁻¹' T) :=
    Set.ext fun p ↦ by
      show stagePrimeMap B S hS A X P K p ∈ T ↔
        stagePrimeMap B S hS A X P L (PrimeSpectrum.comap (Ideal.Quotient.factor hle) p) ∈ T
      rw [stagePrimeMap_comap B S hS A X P f]
  have hmap : (Ideal.map (Ideal.Quotient.mk K.1) 𝔞 : Ideal (A ⧸ K.1)) =
      Ideal.span (Ideal.Quotient.factor hle ''
        ((Ideal.map (Ideal.Quotient.mk L.1) 𝔞 : Ideal (A ⧸ L.1)) : Set (A ⧸ L.1))) := by
    show _ = Ideal.map (Ideal.Quotient.factor hle) (Ideal.map (Ideal.Quotient.mk L.1) 𝔞)
    rw [Ideal.map_map, Ideal.Quotient.factor_comp_mk]
  have hzl : PrimeSpectrum.zeroLocus
        ((Ideal.map (Ideal.Quotient.mk K.1) 𝔞 : Ideal (A ⧸ K.1)) : Set (A ⧸ K.1)) =
      PrimeSpectrum.comap (Ideal.Quotient.factor hle) ⁻¹' PrimeSpectrum.zeroLocus
        ((Ideal.map (Ideal.Quotient.mk L.1) 𝔞 : Ideal (A ⧸ L.1)) : Set (A ⧸ L.1)) := by
    rw [PrimeSpectrum.preimage_comap_zeroLocus, hmap, PrimeSpectrum.zeroLocus_span]
  rw [CutsOutAtStage, CutsOutAtStage, hpre, hzl]
  exact ((bijective_comap_factor B S hS A X P hA f).surjective.preimage_injective).eq_iff

/-- Cutting out `T` at one stage gives it at every stage: any two weak ideals of definition are
refined by a third. -/
theorem cutsOutAtStage_of_cutsOutAtStage (hA : TopologicalRing.IsWeaklyAdmissible A)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj)) (𝔞 : Ideal A) {K₀ : WeakIdeals A}
    (h : CutsOutAtStage B S hS A X P K₀ T 𝔞) (K : WeakIdeals A) :
    CutsOutAtStage B S hS A X P K T 𝔞 := by
  let : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  obtain ⟨M, hKM, hK₀M⟩ := directed_of (· ≤ ·) K K₀
  rw [cutsOutAtStage_iff_of_hom B S hS A X P hA (homOfLE hKM) T 𝔞,
    ← cutsOutAtStage_iff_of_hom B S hS A X P hA (homOfLE hK₀M) T 𝔞]
  exact h

/-- **The ideal cutting out a closed set of points with quasi-compact complement.** Let `A` be
adic\* presenting `X`, with `I` a finitely generated ideal of definition, and let `T` be a
closed set of points of `X` whose complement is quasi-compact. Then there is a finitely
generated ideal `𝔞 ⊇ I` of `A` cutting out `T` at every stage of the presentation.

The stage at `I` is `Spec (A ⧸ I)`, whose prime spectrum is the point space of `X`, so `T`
corresponds to a closed subset with quasi-compact complement there; such a subset is the zero
locus of a finitely generated ideal `I'` of `A ⧸ I` by
`PrimeSpectrum.isCompact_isOpen_iff_ideal`, and `𝔞` is the inverse image of `I'` in `A`. It is
finitely generated because `I` and `I'` are. -/
theorem exists_fg_cutsOutAtStage (hA : TopologicalRing.IsWeaklyAdmissible A) {I : Ideal A}
    (hIdef : TopologicalRing.IsIdealOfDefinition I) (hIfg : I.FG)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) T)
    (hqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) Tᶜ) :
    ∃ 𝔞 : Ideal A, 𝔞.FG ∧ I ≤ 𝔞 ∧
      ∀ K : WeakIdeals A, CutsOutAtStage B S hS A X P K T 𝔞 := by
  have hw : TopologicalRing.IsWeakIdealOfDefinition I :=
    TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition hIdef
  have hhomeo := isHomeomorph_stagePrimeMap B S hS A X P hA (⟨I, hw⟩ : WeakIdeals A)
  have hopen : IsOpen ((stagePrimeMap B S hS A X P (⟨I, hw⟩ : WeakIdeals A) ⁻¹' T)ᶜ) := by
    rw [← Set.preimage_compl]
    exact hT.isOpen_compl.preimage hhomeo.continuous
  have hcpt : IsCompact ((stagePrimeMap B S hS A X P (⟨I, hw⟩ : WeakIdeals A) ⁻¹' T)ᶜ) := by
    rw [← Set.preimage_compl]
    exact (hhomeo.homeomorph _).isCompact_preimage.mpr hqc
  obtain ⟨I', hI'fg, hI'⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hcpt, hopen⟩
  have hzl : PrimeSpectrum.zeroLocus (I' : Set (A ⧸ I)) =
      stagePrimeMap B S hS A X P (⟨I, hw⟩ : WeakIdeals A) ⁻¹' T := compl_inj_iff.mp hI'
  have hIle : I ≤ Ideal.comap (Ideal.Quotient.mk I) I' := fun a ha ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact I'.zero_mem
  refine ⟨Ideal.comap (Ideal.Quotient.mk I) I', ?_, hIle, ?_⟩
  · refine Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective (f := Ideal.Quotient.mk I) ?_ ?_
      Ideal.Quotient.mk_surjective
    · rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
      exact hI'fg
    · rw [Ideal.mk_ker, inf_eq_right.mpr hIle]
      exact hIfg
  · refine cutsOutAtStage_of_cutsOutAtStage B S hS A X P hA T _
      (K₀ := (⟨I, hw⟩ : WeakIdeals A)) ?_
    show stagePrimeMap B S hS A X P (⟨I, hw⟩ : WeakIdeals A) ⁻¹' T =
      PrimeSpectrum.zeroLocus
        ((Ideal.map (Ideal.Quotient.mk I) (Ideal.comap (Ideal.Quotient.mk I) I') :
          Ideal (A ⧸ I)) : Set (A ⧸ I))
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective, hzl]

/-! ### The radical of the ideal cut out by a closed-immersed affine inside the closed set -/

include B S hS X P in
/-- **An affine scheme closed-immersed in `X` whose points lie in `T` cuts out an ideal whose
radical contains the ideal cutting out `T`.** This is the hypothesis `hbig` of
`AlgebraicGeometry.FormalSpace.exists_quotientSystem_formalSpectrum_iso_of_stageIdeal`.

The closed immersion factors through a stage `Spec (A ⧸ K)` of the presentation by **Stacks
0AIA**, and there its image is the zero locus of the ideal it cuts out
(`AlgebraicGeometry.FormalSpace.range_base_eq_zeroLocus_ker`, the ring map being surjective by
**Stacks 0AIC**); that image lies in the zero locus of the image of `𝔞`, because the points of
the affine lie in `T` and `𝔞` cuts out `T` at `K`. An inclusion of zero loci is the reverse
inclusion of radicals. -/
theorem le_radical_stageIdeal_of_range_subset (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj)) (𝔞 : Ideal A)
    (hcuts : ∀ K : WeakIdeals A, CutsOutAtStage B S hS A X P K T 𝔞)
    (V : BigAffineFppf B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj V) ⟶ X)
    (hg : IsClosedImmersionInto B S hS g)
    (hrange : Set.range (Space.pointsMapULift.{u + 1} B S hS _ g.hom) ⊆ T) :
    𝔞 ≤ (stageIdeal B S hS A P ((BigAffineFppf.inclusion B S hS).obj V) g).radical := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  have hsurjA : Function.Surjective
      (pointRingMap B S hS A P ((BigAffineFppf.inclusion B S hS).obj V) g) :=
    surjective_pointRingMap B S hS A P hA hset V g hg
  obtain ⟨K, b, hfac, -⟩ :=
    (isClosedImmersion_toSpec_of_weakIdealColimitPresentation B S hS A hA hset P).2 V g hg
  rw [← hfac] at hrange hsurjA ⊢
  -- the ring map `A ⧸ K ⟶ Γ(V, 𝒪)` is surjective
  have hsurjψ : Function.Surjective
      (stageQuotientRingMap B S hS A X P K ((BigAffineFppf.inclusion B S hS).map b)) := by
    intro y
    obtain ⟨a, ha⟩ := hsurjA y
    exact ⟨Ideal.Quotient.mk K.1 a,
      (pointRingMap_comp_weakIdealStagePoint B S hS A X P K
        ((BigAffineFppf.inclusion B S hS).map b) a).symm.trans ha⟩
  -- the image of `V` in `Spec (A ⧸ K)` lies in the zero locus of the image of `𝔞`
  have hsub : Set.range (((BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map b) ≫ (P.quotientIso K).hom)).base ⊆
      PrimeSpectrum.zeroLocus
        ((Ideal.map (Ideal.Quotient.mk K.1) 𝔞 : Ideal (A ⧸ K.1)) : Set (A ⧸ K.1)) := by
    rintro _ ⟨x, rfl⟩
    have hpt : (P.quotientIso K).inv.base
          (((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map b) ≫
            (P.quotientIso K).hom).base x) =
        (BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map b) x := by
      rw [show ((BigFppfOver.toScheme B S hS).map
            ((BigAffineFppf.inclusion B S hS).map b) ≫ (P.quotientIso K).hom).base x =
          (P.quotientIso K).hom.base ((BigFppfOver.toScheme B S hS).map
            ((BigAffineFppf.inclusion B S hS).map b) x) from Scheme.Hom.comp_apply _ _ x]
      simp
    have hr := range_pointsMapULift_comp_weakIdealStagePoint B S hS A X P K
      ((BigAffineFppf.inclusion B S hS).map b)
    rw [← hcuts K]
    show stagePointsMap B S hS A X P K ((P.quotientIso K).inv.base
      (((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map b) ≫
        (P.quotientIso K).hom).base x)) ∈ T
    rw [hpt]
    exact hrange (hr.ge ⟨_, ⟨x, rfl⟩, rfl⟩)
  -- read that inclusion as an inclusion of ideals
  have hideal : (Ideal.map (Ideal.Quotient.mk K.1) 𝔞 : Ideal (A ⧸ K.1)) ≤
      (RingHom.ker (stageQuotientRingMap B S hS A X P K
        ((BigAffineFppf.inclusion B S hS).map b))).radical := by
    refine (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp ?_
    exact fun p hp ↦ hsub ((range_base_eq_zeroLocus_ker
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map b) ≫
        (P.quotientIso K).hom) hsurjψ).ge hp)
  rw [stageIdeal_comp_weakIdealStagePoint B S hS A X P K
    ((BigAffineFppf.inclusion B S hS).map b), ← Ideal.comap_radical]
  exact le_trans Ideal.le_comap_map (Ideal.comap_mono hideal)

end AlgebraicGeometry.FormalSpace

end
