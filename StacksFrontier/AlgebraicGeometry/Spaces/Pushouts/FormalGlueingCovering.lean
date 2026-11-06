module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Localization
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.Topology.Constructible.MeetConstructible

/-!
# An fpqc covering adapted to a formal glueing situation

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))` the ambient
algebraic space `X` is covered, for the fpqc topology, by algebraic spaces each of which maps
to `X` through `U ⟶ X` or through `f : Y ⟶ X`. This common refinement of the two morphisms is
what reduces a statement about modules on `X` to the corresponding statements on `U` and
on `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_fpqcCovering_refining_openComplement_and_source`:
  **Stacks 0AF1**, the fpqc covering of `X` each of whose members factors through `U` or
  through `Y`.

## Implementation notes

The refinement is recorded as a factorization of every covering arrow through one of the two
arrows `U ⟶ X` and `Y ⟶ X`, rather than as a morphism of covering families; this is what the
consumers need and it avoids choosing an index map.

The proof reduces to affine étale charts `b : T ⟶ X` by Stacks 03FY and Stacks 03H6, lifts
each chart to an affine chart `W` of `Y ×_X T`, and splits `T` into the locus where the chart
misses `f⁻¹(Z)` — covered by affine opens of `T`, each factoring through `U` — and a
neighbourhood of `f⁻¹(Z)` on which the chart morphism `W ⟶ T` is flat, hence an fpqc cover of
that part. Flatness along the closed locus comes from the flatness hypothesis of the situation
through the pointed étale charts of Stacks 04NC; the local rings are compared with
`AlgebraicGeometry.ProEtale.localizationRing`, the localization of a scheme at a locally closed
set of points.

## References

* [Stacks Project, Tag 0AF1](https://stacks.math.columbia.edu/tag/0AF1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- The stalk map of the canonical morphism from the spectrum of a local ring of a scheme is
bijective at every point of that spectrum. -/
@[ega "I 2.4.2"]
private theorem fromSpecStalk_stalkMap_bijective (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    Function.Bijective ((X.fromSpecStalk x).stalkMap p).hom := by
  have := flat_fromSpecStalk X x
  let f : X.presheaf.stalk ((X.fromSpecStalk x) p) →+*
      (Spec (X.presheaf.stalk x)).presheaf.stalk p :=
    ((X.fromSpecStalk x).stalkMap p).hom
  have hf : f.Flat := Flat.stalkMap _ _
  have hinj : Function.Injective f := by
    let _ := f.toAlgebra
    have : Module.Flat (X.presheaf.stalk ((X.fromSpecStalk x) p))
        ((Spec (X.presheaf.stalk x)).presheaf.stalk p) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk ((X.fromSpecStalk x) p))
        ((Spec (X.presheaf.stalk x)).presheaf.stalk p)) := by
      show IsLocalHom ((X.fromSpecStalk x).stalkMap p).hom
      infer_instance
    have : Module.FaithfullyFlat (X.presheaf.stalk ((X.fromSpecStalk x) p))
        ((Spec (X.presheaf.stalk x)).presheaf.stalk p) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact (show f.FaithfullyFlat from this).injective
  exact ⟨hinj, (X.fromSpecStalk x).stalkMap_surjective p⟩

/-- Flatness of the stalk map at a point propagates to every point specializing to it: the point
lies in the image of the spectrum of the local ring at the specialization. -/
private theorem flatAt_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    {x y : X} (hxy : x ⤳ y) (hy : (f.stalkMap y).hom.Flat) :
    (f.stalkMap x).hom.Flat := by
  have : Flat (Spec.map (f.stalkMap y)) := Flat.SpecMap_iff.mpr hy
  have := flat_fromSpecStalk Y (f y)
  have hcomp : Flat (X.fromSpecStalk y ≫ f) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
    infer_instance
  obtain ⟨p, hp⟩ := (show x ∈ Set.range (X.fromSpecStalk y) by
    rw [Scheme.range_fromSpecStalk]
    exact hxy)
  have hstalk := @Flat.stalkMap _ _ (X.fromSpecStalk y ≫ f) hcomp p
  rw [Scheme.Hom.stalkMap_comp] at hstalk
  have := (RingHom.Flat.comp_iff_of_bijective_left
    (fromSpecStalk_stalkMap_bijective X y p)).mp hstalk
  change (f.stalkMap ((X.fromSpecStalk y) p)).hom.Flat at this
  rwa [hp] at this

/-- Every point of the spectrum of the localization of a ring along the closed set cut out by an
ideal specializes to a point of that closed set. -/
private theorem localization_point_generizes_closed
    {A : Type u} [CommRing A] (I : Ideal A)
    (p : PrimeSpectrum (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))) :
    ∃ q : PrimeSpectrum A, q ∈ PrimeSpectrum.zeroLocus (I : Set A) ∧
      PrimeSpectrum.comap
        (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))) p ⤳ q := by
  have hp : PrimeSpectrum.comap
      (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))) p ∈
        Set.range (PrimeSpectrum.comap
          (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A)))) :=
    ⟨p, rfl⟩
  rw [_root_.AlgebraicGeometry.ProEtale.localization_comap_range I (1 : A)] at hp
  rcases hp with ⟨q, hq, hspec⟩
  exact ⟨q, hq.1, hspec⟩

/-- Every point of the closed set cut out by an ideal lifts to the spectrum of the localization
of the ring along that closed set. -/
private theorem localization_closed_point_lifts
    {A : Type u} [CommRing A] (I : Ideal A) (q : PrimeSpectrum A)
    (hq : q ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ p : PrimeSpectrum (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A)),
      PrimeSpectrum.comap
        (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))) p = q := by
  have hloc : q ∈ _root_.AlgebraicGeometry.ProEtale.locallyClosedPoints I (1 : A) := by
    constructor
    · simpa [PrimeSpectrum.mem_zeroLocus] using hq
    · intro hone
      exact q.2.ne_top (q.asIdeal.eq_top_of_isUnit_mem hone isUnit_one)
  have hq' : q ∈ {p : PrimeSpectrum A |
      ∃ q ∈ _root_.AlgebraicGeometry.ProEtale.locallyClosedPoints I (1 : A), p ⤳ q} :=
    ⟨q, hloc, specializes_refl q⟩
  rw [← _root_.AlgebraicGeometry.ProEtale.localization_comap_range I (1 : A)] at hq'
  exact hq'

/-- A composite is flat when its first factor is flat and its second factor is flat at the image
of every point of the source. -/
private theorem flat_comp_of_flatAt_source {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) [Flat g]
    (h : ∀ x : X, _root_.AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom (g x)) :
    Flat (g ≫ f) := by
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x; rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.Flat.comp (h x) (Flat.stalkMap g x)

/-- Precomposing a morphism from an affine scheme with the localization along a closed subset of
the source makes it flat, provided it is flat at every point of that closed subset. -/
private theorem flat_selectedLocalization_comp
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : Spec (.of A) ⟶ X) (I : Ideal A)
    (hf : ∀ q ∈ PrimeSpectrum.zeroLocus (I : Set A),
      (f.stalkMap q).hom.Flat) :
    Flat (Spec.map (CommRingCat.ofHom
      (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A)))) ≫ f) := by
  have : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))))) := by
    rw [AlgebraicGeometry.Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (S := _root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))
        (p := _root_.AlgebraicGeometry.ProEtale.localizationSubmonoid I (1 : A)))
  refine flat_comp_of_flatAt_source _ _ fun p => ?_
  obtain ⟨q, hq, hpq⟩ := localization_point_generizes_closed I p
  exact flatAt_of_specializes f hpq (hf q hq)

/-- A finite family of flat quasi-compact morphisms which is jointly surjective on points is an
fpqc covering. -/
private theorem mem_fpqcPrecoverage_of_finite_quasiCompact
    {X : Scheme.{u}} {J : Type v} [Finite J]
    (V : J → Scheme.{u}) (g : ∀ j, V j ⟶ X)
    (hqc : ∀ j, QuasiCompact (g j))
    (hg : ∀ j, Flat (g j)) (hcover : ∀ x, ∃ j y, g j y = x) :
    Presieve.ofArrows V g ∈ Scheme.fpqcPrecoverage X := by
  have : ∀ j, QuasiCompact (g j) := hqc
  refine ⟨?_, (Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mpr ⟨hcover, hg⟩⟩
  apply (Scheme.presieve₀_mem_qcPrecoverage_iff (E := ⟨J, V, g⟩)).mpr
  constructor
  intro W hW
  apply IsCompactOpenCovered.of_finite id
    (fun j => (g j) ⁻¹ᵁ W) (fun j => (g j).isCompact_preimage hW.isCompact)
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨j, y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨j, y, rfl⟩ := hcover x
    exact ⟨j, y, hx, rfl⟩

/-- A compact open of a scheme is the union of finitely many affine opens. -/
private theorem exists_finite_affine_opens_of_isCompact
    (X : Scheme.{u}) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ (J : Type u) (_ : Finite J) (V : J → X.Opens),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = U := by
  obtain ⟨Vs, hVs, hfinite, hsup⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact hU
  refine ⟨Vs, hfinite.to_subtype, Subtype.val, fun j => hVs j.property, ?_⟩
  simpa only [sSup_eq_iSup, iSup_subtype] using hsup.symm

/-- Let `f : W ⟶ X` be a morphism from an affine scheme which is flat along a closed subset of `W`
whose image covers a closed subset `Z` of `X`, and let the complement of `Z` be covered by
opens of `X`. Then `X` has a finite affine fpqc covering each of whose members factors either
through one of those opens or through `f`. -/
private theorem exists_affine_fpqcCovering_of_closed_locus
    {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X]
    (f : Spec (.of A) ⟶ X) (I : Ideal A) (Z : Set X)
    (hZ : ∀ x ∈ Z, ∃ q ∈ PrimeSpectrum.zeroLocus (I : Set A), f q = x)
    (hf : ∀ q ∈ PrimeSpectrum.zeroLocus (I : Set A), (f.stalkMap q).hom.Flat)
    (J : Type u) [Finite J] (U : J → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : ∀ x ∉ Z, ∃ j, x ∈ U j) :
    ∃ (K : Type u) (_ : Finite K) (V : K → Scheme.{u}) (g : ∀ k, V k ⟶ X),
      (∀ k, IsAffine (V k)) ∧
      (∀ k, (V k).size ≤ max (Spec (.of A)).size X.size) ∧
      Presieve.ofArrows V g ∈ Scheme.fpqcPrecoverage X ∧
      ∀ k, (∃ (j : J) (a : V k ⟶ (U j).toScheme), a ≫ (U j).ι = g k) ∨
        (∃ b : V k ⟶ Spec (.of A), b ≫ f = g k) := by
  let L := Spec (.of (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A)))
  let l : L ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom
    (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))))
  let V : Option J → Scheme.{u} := fun k =>
    match k with
    | none => L
    | some j => (U j).toScheme
  let g : ∀ k, V k ⟶ X := fun k =>
    match k with
    | none => l ≫ f
    | some j => (U j).ι
  have hV : ∀ k, IsAffine (V k) := by
    intro k
    cases k with
    | none => dsimp [V, L]; infer_instance
    | some j => exact hU j
  have hg : ∀ k, Flat (g k) := by
    intro k
    cases k with
    | none => exact flat_selectedLocalization_comp f I hf
    | some j => dsimp [g]; infer_instance
  have hc : ∀ x, ∃ k y, g k y = x := by
    intro x
    by_cases hx : x ∈ Z
    · obtain ⟨q, hq, hqx⟩ := hZ x hx
      obtain ⟨p, hp⟩ := localization_closed_point_lifts I q hq
      refine ⟨none, p, ?_⟩
      show f (PrimeSpectrum.comap
        (algebraMap A (_root_.AlgebraicGeometry.ProEtale.localizationRing I (1 : A))) p) = x
      rw [hp, hqx]
    · obtain ⟨j, hj⟩ := hcover x hx
      exact ⟨some j, ⟨x, hj⟩, rfl⟩
  let : ∀ k, IsAffine (V k) := hV
  have hsize : ∀ k, (V k).size ≤ max (Spec (.of A)).size X.size := by
    intro k
    cases k with
    | none =>
      have : IsPreimmersion l := IsPreimmersion.of_isLocalization
        (_root_.AlgebraicGeometry.ProEtale.localizationSubmonoid I (1 : A))
      have : QuasiCompact l := inferInstance
      exact (Scheme.size_le_of_mono_quasiCompact l).trans (le_max_left _ _)
    | some j =>
      exact (Scheme.size_coe_opens_le X (U j)).trans (le_max_right _ _)
  refine ⟨Option J, inferInstance, V, g, hV, hsize,
    mem_fpqcPrecoverage_of_finite_quasiCompact V g (fun k => by
      have := hV k
      infer_instance) hg hc, ?_⟩
  intro k
  cases k with
  | none => exact Or.inr ⟨l, rfl⟩
  | some j => exact Or.inl ⟨j, 𝟙 _, Category.id_comp _⟩

/-- The same conclusion as `exists_affine_fpqcCovering_of_closed_locus` for a morphism out of an
affine scheme, with the closed locus given inside the source rather than as an ideal. -/
private theorem exists_affine_fpqcCovering_of_affine_closed_locus
    {W X : Scheme.{u}} [IsAffine W] [IsAffine X]
    (f : W ⟶ X) (Z : Set X) (C : Set W) (hC : IsClosed C)
    (hZ : ∀ x ∈ Z, ∃ w ∈ C, f w = x)
    (hf : ∀ w ∈ C, (f.stalkMap w).hom.Flat)
    (J : Type u) [Finite J] (U : J → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : ∀ x ∉ Z, ∃ j, x ∈ U j) :
    ∃ (K : Type u) (_ : Finite K) (V : K → Scheme.{u}) (g : ∀ k, V k ⟶ X),
      (∀ k, IsAffine (V k)) ∧
      (∀ k, (V k).size ≤ max W.size X.size) ∧
      Presieve.ofArrows V g ∈ Scheme.fpqcPrecoverage X ∧
      ∀ k, (∃ (j : J) (a : V k ⟶ (U j).toScheme), a ≫ (U j).ι = g k) ∨
        (∃ b : V k ⟶ W, b ≫ f = g k) := by
  let e := W.isoSpec
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    (e.inv ⁻¹' C)).mp (hC.preimage e.inv.continuous)
  have hcoverZ : ∀ x ∈ Z, ∃ q ∈ PrimeSpectrum.zeroLocus (I : Set Γ(W, ⊤)),
      (e.inv ≫ f) q = x := by
    intro x hx
    obtain ⟨w, hw, hfw⟩ := hZ x hx
    have hew : e.inv (e.hom w) = w := by
      show (e.hom ≫ e.inv) w = w
      rw [e.hom_inv_id]
      rfl
    refine ⟨e.hom w, ?_, ?_⟩
    · rw [← hI]
      show e.inv (e.hom w) ∈ C
      rwa [hew]
    · show f (e.inv (e.hom w)) = x
      rwa [hew]
  have hflat : ∀ q ∈ PrimeSpectrum.zeroLocus (I : Set Γ(W, ⊤)),
      ((e.inv ≫ f).stalkMap q).hom.Flat := by
    intro q hq
    have hw : e.inv q ∈ C := hI.ge hq
    have hcomp : ((e.inv ≫ f).stalkMap q : _ ⟶ _) =
        f.stalkMap (e.inv q) ≫ e.inv.stalkMap q :=
      Scheme.Hom.stalkMap_comp e.inv f q
    rw [hcomp]
    exact RingHom.Flat.comp (hf _ hw) (Flat.stalkMap e.inv q)
  obtain ⟨K, hK, V, g, hV, hsize, hg, hfactor⟩ :=
    exists_affine_fpqcCovering_of_closed_locus (e.inv ≫ f) I Z hcoverZ hflat J U hU hcover
  have hsize' : ∀ k, (V k).size ≤ max W.size X.size := by
    intro k
    rw [Scheme.size_congr e]
    exact hsize k
  exact ⟨K, hK, V, g, hV, hsize', hg, fun k => (hfactor k).imp id fun ⟨b, hb⟩ =>
    ⟨b ≫ e.inv, by simpa only [Category.assoc] using hb⟩⟩

/-- A morphism of the big fppf site whose underlying morphism of schemes is flat induces a flat
morphism of algebraic spaces, by the representable chart criterion of Stacks 03MJ. -/
private theorem flat_yoneda_map
    (site : BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {U V : BigFppfOver site S hS} (f : U ⟶ V)
    (hf : Flat ((BigFppfOver.toScheme site S hS).map f)) :
    IsFlat site S hS (yoneda.map f) := by
  show HoldsOnEveryEtaleChart site S hS (@Flat) (yoneda.map f)
  rw [holdsOnEveryEtaleChart_iff_representable
    (B := site) (S := S) (hS := hS) (P := @Flat)
    (hP := Flat.isEtaleLocalOnSourceAndTarget)
    (F := yoneda.obj U) (G := yoneda.obj V)]
  let e := yoneda.preimage (yoneda.obj U).reprW.hom
  let b := yoneda.preimage (yoneda.obj V).reprW.inv
  have hemap : yoneda.map e = (yoneda.obj U).reprW.hom := by
    simp [e]
  have hbmap : yoneda.map b = (yoneda.obj V).reprW.inv := by
    simp [b]
  let : IsIso (yoneda.map e) := by rw [hemap]; infer_instance
  let : IsIso (yoneda.map b) := by rw [hbmap]; infer_instance
  let : IsIso e := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful e
  let : IsIso b := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful b
  let : IsIso ((BigFppfOver.toScheme site S hS).map e) :=
    Functor.map_isIso _ e
  let : IsIso ((BigFppfOver.toScheme site S hS).map b) :=
    Functor.map_isIso _ b
  have he : Flat ((BigFppfOver.toScheme site S hS).map e) := inferInstance
  have hb : Flat ((BigFppfOver.toScheme site S hS).map b) := inferInstance
  simpa [e, b] using
    MorphismProperty.comp_mem (@Flat) _ _ (MorphismProperty.comp_mem (@Flat) _ _ he hf) hb

/-- **A family of objects of the big fppf site over `Y` whose underlying family of schemes is
an fpqc covering represents an fpqc covering of Stacks 03MQ** of the algebraic space
represented by `Y`. -/
theorem represented_fpqc_family
    (site : BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {Y : BigFppfOver site S hS}
    (I : Type v) (X : I → BigFppfOver site S hS)
    (f : ∀ i, X i ⟶ Y)
    (hcover : Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme site S hS).obj (X i))
      (fun i => (BigFppfOver.toScheme site S hS).map (f i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme site S hS).obj Y)) :
    IsFpqcCovering site S hS (fun i => yoneda.map (f i)) := by
  classical
  let SOver := Y
  let Tcat := BigAffineFppf site S hS
  let Tinc := BigAffineFppf.inclusion site S hS
  let TschFunctor := BigAffineFppf.toScheme site S hS
  let OverScheme := BigFppfOver.toScheme site S hS
  let Base := OverScheme.obj Y
  let Xs (i : I) := OverScheme.obj (X i)
  let fs (i : I) := OverScheme.map (f i)
  have hX (i : I) : site.Contains (Xs i) := (X i).left.property
  constructor
  · intro i
    exact flat_yoneda_map site S hS (f i)
      (((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp hcover.2).2 i)
  · intro T h
    let TOver : BigFppfOver site S hS := Tinc.obj T
    let tOver : TOver ⟶ SOver := yoneda.preimage h
    have htmap : yoneda.map tOver = h := by
      simp [tOver]
    let Tsch := TschFunctor.obj T
    let t : Tsch ⟶ Base := OverScheme.map tOver
    have hT : site.Contains Tsch := (TOver.left).property
    let P (i : I) : Scheme.{u} := pullback (fs i) t
    let p₁ (i : I) : P i ⟶ Tsch := pullback.snd (fs i) t
    let p₂ (i : I) : P i ⟶ Xs i := pullback.fst (fs i) t
    have hP (i : I) : site.Contains (P i) := by
      show (P i).size < site.cutoff
      exact Scheme.size_pullback_lt (κ := site.cutoff) (fs i) t (hX i) hT
    have hsiteCover : Presieve.ofArrows P p₁ ∈ Scheme.fpqcPrecoverage Tsch := by
      let : Precoverage.IsStableUnderBaseChange Scheme.fpqcPrecoverage := inferInstance
      exact Precoverage.mem_coverings_of_isPullback fs hcover t p₁ p₂
        fun i => (IsPullback.of_hasPullback (fs i) t).flip
    have : IsAffine Tsch := BigAffineFppf.isAffine_toScheme_obj site S hS T
    let E : PreZeroHypercover.{v} Tsch := ⟨I, P, p₁⟩
    let : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hsiteCover.1
    obtain ⟨n, idx, V, hVaff, hVcover⟩ :=
      QuasiCompactCover.exists_isAffineOpen_of_isCompact (𝒰 := E) (U := ⊤)
        (isCompact_univ : IsCompact ((⊤ : Tsch.Opens) : Set Tsch))
    let Z (j : Fin n) : Scheme.{u} := (V j).toScheme
    let v (j : Fin n) : Z j ⟶ P (idx j) := (V j).ι
    let q (j : Fin n) : Z j ⟶ Tsch := v j ≫ p₁ (idx j)
    have hZ (j : Fin n) : site.Contains (Z j) := by
      show (Z j).size < site.cutoff
      exact Scheme.size_lt_of_isOpenImmersion (v j) (hP (idx j))
    have hZaffine (j : Fin n) : IsAffine (Z j) := hVaff j
    let qsite (j : Fin n) : site.obj (hZ j) ⟶ TOver.left :=
      site.inclusion.preimage
        (show site.inclusion.obj (site.obj (hZ j)) ⟶ site.inclusion.obj TOver.left from q j)
    let rsite (j : Fin n) : site.obj (hZ j) ⟶ (X (idx j)).left :=
      site.inclusion.preimage
        (show site.inclusion.obj (site.obj (hZ j)) ⟶
          site.inclusion.obj ((X (idx j)).left) from v j ≫ p₂ (idx j))
    let ZOver (j : Fin n) : BigFppfOver site S hS :=
      Over.mk (rsite j ≫ (X (idx j)).hom)
    let lift₁ (j : Fin n) : ZOver j ⟶ X (idx j) :=
      Over.homMk (rsite j) (by simp [ZOver])
    let lift₂ (j : Fin n) : ZOver j ⟶ TOver :=
      Over.homMk (qsite j) (by
        apply site.inclusion.map_injective
        show site.inclusion.map (qsite j ≫ TOver.hom) =
          site.inclusion.map (rsite j ≫ (X (idx j)).hom)
        rw [Functor.map_comp, Functor.map_comp,
          site.inclusion.map_preimage, site.inclusion.map_preimage]
        have hw := congrArg site.inclusion.map (Over.w (f (idx j)))
        have ht := congrArg site.inclusion.map (Over.w tOver)
        show (v j ≫ p₁ (idx j)) ≫ site.inclusion.map TOver.hom =
          (v j ≫ p₂ (idx j)) ≫ site.inclusion.map (X (idx j)).hom
        rw [← hw, ← ht, Functor.map_comp, Functor.map_comp]
        show (v j ≫ p₁ (idx j)) ≫ t ≫ site.inclusion.map Y.hom =
          (v j ≫ p₂ (idx j)) ≫ fs (idx j) ≫ site.inclusion.map Y.hom
        simp only [Category.assoc]
        exact congrArg (fun k => v j ≫ k ≫ site.inclusion.map Y.hom)
          (pullback.condition (f := fs (idx j)) (g := t)).symm)
    let J := ULift.{u + 1} (Fin n)
    let Paff (j : J) : Tcat := ⟨ZOver j.down, hZaffine j.down⟩
    let pi (j : J) : Paff j ⟶ T := Tinc.preimage (lift₂ j.down)
    let U : PreZeroHypercover.{u + 1} T := ⟨J, Paff, pi⟩
    have hpi (j : J) : Tinc.map (pi j) = lift₂ j.down :=
      Tinc.map_preimage (show Tinc.obj (Paff j) ⟶ Tinc.obj T from lift₂ j.down)
    have hUcover :
        Presieve.map TschFunctor U.presieve₀ ∈ Scheme.fpqcPrecoverage Tsch := by
      have hflat : ∀ j : J, Flat (q j.down) := by
        intro j
        have hpflat : Flat (p₁ (idx j.down)) :=
          ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp hsiteCover.2).2
            (idx j.down)
        have hvflat : Flat (v j.down) := by
          dsimp [v, Z]
          infer_instance
        exact MorphismProperty.comp_mem @Flat _ _ hvflat hpflat
      have hsurj : ∀ x : Tsch, ∃ j : J, ∃ y : Z j.down, q j.down y = x := by
        intro x
        have hx : x ∈ ⋃ j : Fin n, p₁ (idx j) '' (V j : Set (P (idx j))) := by
          rw [hVcover]
          exact Set.mem_univ x
        simp only [Set.mem_iUnion, Set.mem_image] at hx
        rcases hx with ⟨j, z, hz, hzx⟩
        refine ⟨ULift.up j, ⟨z, hz⟩, ?_⟩
        show p₁ (idx j) (v j ⟨z, hz⟩) = x
        rw [show v j ⟨z, hz⟩ = z by rfl]
        exact hzx
      have hsource : (fun j : J => TschFunctor.obj (Paff j)) = fun j => Z j.down :=
        funext fun j => rfl
      have hmap : (fun j : J => TschFunctor.map (pi j)) = fun j : J => q j.down :=
        funext fun j => by
        show OverScheme.map (Tinc.map (pi j)) = q j.down
        rw [hpi j]
        show site.inclusion.map (qsite j.down) = q j.down
        exact site.inclusion.map_preimage _
      dsimp [U]
      rw [Presieve.map_ofArrows]
      cases hsource
      rw [hmap]
      exact mem_fpqcPrecoverage_of_finite_quasiCompact
        (fun j : J => Z j.down) (fun j => q j.down)
        (fun j => by have := hZaffine j.down; infer_instance) hflat hsurj
    refine ⟨U, ?_, hUcover, ?_⟩
    · infer_instance
    · intro j
      let i := idx j.down
      refine ⟨i, yoneda.map (lift₁ j.down), ?_⟩
      show yoneda.map (lift₁ j.down) ≫ yoneda.map (f i) =
        yoneda.map (Tinc.map (U.f j)) ≫ h
      rw [← htmap, show Tinc.map (U.f j) = lift₂ j.down from hpi j,
        ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Over.OverMorphism.ext
      apply site.inclusion.map_injective
      show site.inclusion.map (rsite j.down ≫ (f i).left) =
        site.inclusion.map (qsite j.down ≫ tOver.left)
      rw [Functor.map_comp, Functor.map_comp,
        site.inclusion.map_preimage, site.inclusion.map_preimage]
      show (v j.down ≫ p₂ i) ≫ fs i = (v j.down ≫ p₁ i) ≫ t
      simp only [Category.assoc]
      rw [pullback.condition]


/-- Flatness of the germ morphism induced by a morphism of schemes at a point is flatness of the
morphism of ringed spaces at that point. -/
theorem flatAt_of_isFlat_germ {A T : Scheme.{u}} (f : A ⟶ T) (a : A)
    (h : MorphismOfGerms.IsFlat (_root_.AlgebraicGeometry.MorphismOfGerms.ofSchemeHom f a)) :
    _root_.AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom a := by
  obtain ⟨r, hr, hflat⟩ := h
  let r₀ : _root_.AlgebraicGeometry.MorphismOfGerms.Representative
      ⟨A, a⟩ ⟨T, f a⟩ := {
    source := ⊤
    mem_source := by simp
    hom := A.topIso.hom ≫ f
    map_point := rfl
  }
  have hrr₀ : _root_.AlgebraicGeometry.MorphismOfGerms.mk r =
      _root_.AlgebraicGeometry.MorphismOfGerms.mk r₀ := hr.trans (by rfl)
  obtain ⟨W, haW, hWr, hWr₀, hEq⟩ :=
    (_root_.AlgebraicGeometry.MorphismOfGerms.mk_eq_mk_iff).mp hrr₀
  let k : W.toScheme ⟶ r.source.toScheme := A.homOfLE hWr
  let j : W.toScheme ⟶ (⊤ : A.Opens).toScheme := A.homOfLE hWr₀
  let w : W.toScheme := ⟨a, haW⟩
  have hwk : k w = ⟨a, r.mem_source⟩ := by
    simpa [k, w] using (Scheme.homOfLE_apply' hWr a haW)
  have hwj : j w = ⟨a, by simp⟩ := by
    simpa [j, w] using (Scheme.homOfLE_apply' hWr₀ a haW)
  have hkflat : (k.stalkMap w).hom.Flat := by
    show _root_.AlgebraicGeometry.IsFlatAt k.toLRSHom.toShHom w
    exact Flat.stalkMap k w
  have hjbij : Function.Bijective (j.stalkMap w).hom :=
    ConcreteCategory.bijective_of_isIso (j.stalkMap w)
  have hkcomp : ((k ≫ r.hom).stalkMap w).hom.Flat := by
    have hrflat : (r.hom.stalkMap (k w)).hom.Flat := by
      rw [hwk]
      exact hflat
    have heq := Scheme.Hom.stalkMap_comp k r.hom w
    rw [heq]
    show RingHom.Flat ((k.stalkMap w).hom.comp (r.hom.stalkMap (k w)).hom)
    exact RingHom.Flat.comp hrflat hkflat
  have hrightFlat : ((j ≫ r₀.hom).stalkMap w).hom.Flat := by
    have hleft := hkcomp
    rw [hEq] at hleft
    exact hleft
  have hr₀flat : (r₀.hom.stalkMap (j w)).hom.Flat := by
    have hright := Scheme.Hom.stalkMap_comp j r₀.hom w
    rw [hright] at hrightFlat
    change RingHom.Flat ((j.stalkMap w).hom.comp (r₀.hom.stalkMap (j w)).hom) at hrightFlat
    exact (RingHom.Flat.comp_iff_of_bijective_left hjbij).mp hrightFlat
  let p₀ : (⊤ : A.Opens).toScheme := ⟨a, by simp⟩
  have htopbij : Function.Bijective ((A.topIso.hom.stalkMap p₀).hom) :=
    ConcreteCategory.bijective_of_isIso (A.topIso.hom.stalkMap p₀)
  have hjp : j w = p₀ := by simpa [p₀] using hwj
  rw [hjp] at hr₀flat
  have hcompFlat :
      ((f.stalkMap (A.topIso.hom p₀) ≫ A.topIso.hom.stalkMap p₀).hom).Flat := by
    rw [← Scheme.Hom.stalkMap_comp]
    show ((r₀.hom.stalkMap p₀).hom).Flat
    exact hr₀flat
  have hcompRingFlat :
      ((A.topIso.hom.stalkMap p₀).hom.comp
        (f.stalkMap (A.topIso.hom p₀)).hom).Flat := by
    rw [← CommRingCat.hom_comp]
    exact hcompFlat
  exact (RingHom.Flat.comp_iff_of_bijective_left htopbij).mp hcompRingFlat


/-- Flatness of a morphism of algebraic spaces at a point transfers to the stalk map of a pointed
pair of étale charts for it. -/
private theorem flatAt_chart_of_factor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : FormalGlueingSituation B S hS)
    (W T C : BigFppfOver B S hS)
    (a : yoneda.obj W ⟶ D.Y) (b : yoneda.obj T ⟶ D.X) (h : W ⟶ T)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ D.f)
    (c : C ⟶ W) (r : yoneda.obj C ⟶ (D.Z.preimage D.f).toFunctor)
    (hr : r ≫ (D.Z.preimage D.f).ι = yoneda.map c ≫ a)
    (z : (BigFppfOver.toScheme B S hS).obj C) :
    (((BigFppfOver.toScheme B S hS).map h).stalkMap
      ((BigFppfOver.toScheme B S hS).map c z)).hom.Flat := by
  let G := BigFppfOver.toScheme B S hS
  let p := schemePointRepresentative B S hS C z
  let q := FieldValuedPoint.map B S hS (yoneda.obj C) (yoneda.map c) p
  let x := pointsMap B S hS (yoneda.obj C) r
    (p.class B S hS (yoneda.obj C))
  let e : EtaleChartAtPoint B S hS D.f
      (pointsMap B S hS (D.Z.preimage D.f).toFunctor
        (D.Z.preimage D.f).ι x) := {
    U := W
    V := T
    a := a
    b := b
    h := h
    a_etale := ha
    b_etale := hb
    comm := hcomm
    representative := q
    point := IsLocalRing.closedPoint q.carrier
    maps_to := by
      show pointsMap B S hS (yoneda.obj W) a
        (pointsMap B S hS (yoneda.obj C) (yoneda.map c)
          (p.class B S hS (yoneda.obj C))) = _
      show (pointsMap B S hS (yoneda.obj W) a ∘
        pointsMap B S hS (yoneda.obj C) (yoneda.map c)) _ = _
      rw [← pointsMap_comp, ← hr, pointsMap_comp]
      rfl }
  have he : e.sourcePoint B S hS = G.map c z := by
    show G.map c (G.map p.value (IsLocalRing.closedPoint _)) = G.map c z
    exact congrArg (G.map c) (schemePointRepresentative_point B S hS C z)
  have hflat := flatAt_of_isFlat_germ (G.map h) (e.sourcePoint B S hS)
    (D.flat_at_preimage_Z x e)
  change ((G.map h).stalkMap (e.sourcePoint B S hS)).hom.Flat at hflat
  rwa [he] at hflat

/-- A point of a chart whose image lies in a closed subspace lifts to the inverse image of that
subspace in the chart. -/
private theorem exists_lift_to_preimage_of_comm
    {C : Type*} [Category C] {F G H : C ⥤ Type u}
    (f : F ⟶ G) (Z : Subfunctor G) (a : H ⟶ F) (b : H ⟶ Z.toFunctor)
    (h : b ≫ Z.ι = a ≫ f) :
    ∃ r : H ⟶ (Z.preimage f).toFunctor, r ≫ (Z.preimage f).ι = a := by
  have hrange : Subfunctor.range a ≤ Z.preimage f := by
    intro T x hx
    obtain ⟨y, rfl⟩ := hx
    show f.app T (a.app T y) ∈ Z.obj T
    have heq := congrArg (fun k : H ⟶ G => k.app T y) h
    change (b.app T y).val = f.app T (a.app T y) at heq
    rw [← heq]
    exact (b.app T y).property
  exact ⟨Subfunctor.lift a hrange, Subfunctor.lift_ι a hrange⟩

/-- In a formal glueing situation, the morphism of charts induced by an étale chart of `X` and an
étale chart of `Y ×_X T` has flat stalk map at every point lying over `f⁻¹(Z)`. -/
private theorem flatAt_on_closed_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : FormalGlueingSituation B S hS)
    (W T : BigFppfOver B S hS)
    (a : yoneda.obj W ⟶ D.Y) (b : yoneda.obj T ⟶ D.X) (h : W ⟶ T)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ D.f) :
    ∀ w ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (D.closed_Z.2.1.snd (a ≫ D.f))),
      (((BigFppfOver.toScheme B S hS).map h).stalkMap w).hom.Flat := by
  let R := D.closed_Z.2.1
  let c := R.snd (a ≫ D.f)
  obtain ⟨r, hr⟩ := exists_lift_to_preimage_of_comm D.f D.Z
    (yoneda.map c ≫ a) (R.fst (a ≫ D.f)) (by
      simpa only [Category.assoc] using R.w (a ≫ D.f))
  intro w hw
  obtain ⟨z, rfl⟩ := hw
  exact flatAt_chart_of_factor B S hS D W T (R.pullback (a ≫ D.f))
    a b h ha hb hcomm c r hr z

/-- Étaleness after every representable base change is stable under base change. -/
private theorem presheafEtale_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} {b : F ⟶ H} {c : G ⟶ K} {d : H ⟶ K}
    (h : IsPullback a b c d)
    (hc : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b := by
  let G := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u}) G
  let : PreservesLimitsOfShape WalkingCospan G := by
    apply comp_preservesLimitsOfShape
  let : P.IsStableUnderBaseChange := ⟨by
    intro X₁ X₂ X₃ Y₁ f₁ f₂ g₁ g₂ hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Etale.{u} : MorphismProperty Scheme.{u})) (hs.map G) hg⟩
  let : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback h hc

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
private local instance (priority := high) hasPullbacks_presheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

private local instance (priority := high) hasPullback_presheaf
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf B S hS).has_limit _

/-- An affine étale chart of `X` in a formal glueing situation admits an affine surjective étale
chart of its base change to `Y`, whose composite to `Y` is again étale after every
representable base change. -/
private theorem exists_affine_source_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : FormalGlueingSituation B S hS)
    (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ D.X)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hb : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ (W : BigFppfOver B S hS)
      (a' : yoneda.obj W ⟶ pullback D.f b),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a' ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (a' ≫ pullback.fst D.f b) := by
  have hAlg := isAlgebraicSpace_pullback B S hS D.f b
    D.algebraicSpace_Y (isAlgebraicSpace_yoneda B S hS T)
    D.algebraicSpace_X
  have hTqc : IsQuasiCompactSpace B S hS (yoneda.obj T) := by
    have := hT
    exact isQuasiCompactSpace_yoneda_obj B S hS inferInstance
  have hqc : IsQuasiCompactSpace B S hS (pullback D.f b) :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry b D.f)
      (D.quasiCompact_f (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) hTqc b)
  obtain ⟨W, a', hW, hs, he⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
      B S hS _ hAlg).mp hqc
  have ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a' := by
    simpa only [Category.id_comp] using he W (𝟙 _) (presheaf_etale_id B S hS W)
  refine ⟨W, a', hW, hs, presheafEtale_comp B S hS ha ?_⟩
  exact presheafEtale_of_isPullback B S hS (IsPullback.of_hasPullback D.f b).flip hb

/-- An algebraic space over `S` has an fpqc covering by representable presheaves with affine
underlying schemes which are étale over it. -/
private theorem exists_affine_etale_fpqc_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ (I : Type u) (T : I → BigFppfOver B S hS)
      (b : ∀ i, yoneda.obj (T i) ⟶ F),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T i))) ∧
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (b i)) ∧
      IsFpqcCovering B S hS b := by
  classical
  obtain ⟨I, U, hU, H⟩ :=
    exists_zariski_cover_affine_etale_atlas B S hS F hF
  choose T a V ha hs he hV hb using H
  let b : ∀ i, yoneda.obj (T i) ⟶ F := fun i => a i ≫ (U i).ι
  have hbi : ∀ i, (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (b i) := by
    intro i
    apply presheafEtale_comp B S hS (he i)
    apply MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage
        (BigFppfOver.toScheme B S hS) ?_) _ (hU.1 i).2
    intro X Y f hf
    let : _root_.AlgebraicGeometry.IsOpenImmersion f := hf
    infer_instance
  refine ⟨I, T, b, ha, hbi, ?_⟩
  apply isFpqcCovering_of_isEtaleCovering B S hS
  refine ⟨hF, (fun i => isAlgebraicSpace_yoneda B S hS (T i)), ?_, ?_⟩
  · intro i W a ha
    exact presheafEtale_comp B S hS ha (hbi i)
  · have hcover := (isZariskiCover_iff_iUnion_points
      B S hS F hF I U hU.1).mp hU
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, y, hy⟩ := (show ∃ i y,
        pointsMap B S hS (U i).toFunctor (U i).ι y = x from by
      have hx : x ∈ ⋃ i, Set.range
          (pointsMap B S hS (U i).toFunctor (U i).ι) := by
        rw [hcover]
        trivial
      simpa only [Set.mem_iUnion, Set.mem_range] using hx)
    obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap
      B S hS (U i).toFunctor (hU.1 i).1 (T i) (a i)).mp (hs i) y
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨z, ?_⟩⟩
    dsimp [b]
    rw [pointsMap_comp, Function.comp_apply, hz, hy]

/-- To produce an fpqc covering of `X` refining a given pair of morphisms it suffices to produce
one over every affine étale chart of `X`: fpqc coverings compose. -/
private theorem exists_fpqc_refinement_of_affine_charts
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : FormalGlueingSituation B S hS)
    (H : ∀ (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ D.X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      ∃ (J : Type u) (V : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (g : ∀ j, V j ⟶ yoneda.obj T),
        (∀ j, IsAlgebraicSpace B S hS (V j)) ∧
        IsFpqcCovering B S hS g ∧
        (∀ j, (∃ a : V j ⟶ D.U.toFunctor, a ≫ D.U.ι = g j ≫ b) ∨
          (∃ a : V j ⟶ D.Y, a ≫ D.f = g j ≫ b))) :
    ∃ (I : Type u) (Xi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (g : ∀ i, Xi i ⟶ D.X),
      (∀ i, IsAlgebraicSpace B S hS (Xi i)) ∧
      IsFpqcCovering B S hS g ∧
      (∀ i, (∃ a : Xi i ⟶ D.U.toFunctor, a ≫ D.U.ι = g i) ∨
        (∃ b : Xi i ⟶ D.Y, b ≫ D.f = g i)) := by
  classical
  obtain ⟨I, T, b, hT, hb, hcov⟩ :=
    exists_affine_etale_fpqc_cover B S hS D.X D.algebraicSpace_X
  choose J V g hV hg hfactor using fun i => H (T i) (b i) (hT i) (hb i)
  refine ⟨Σ i, J i, (fun ij => V ij.1 ij.2),
    (fun ij => g ij.1 ij.2 ≫ b ij.1), (fun ij => hV ij.1 ij.2), ?_,
    (fun ij => hfactor ij.1 ij.2)⟩
  exact isFpqcCovering_comp B S hS
    (Xi := fun i => yoneda.obj (T i)) (Xij := fun ij : Σ i, J i => V ij.1 ij.2)
    D.algebraicSpace_X (fun i => isAlgebraicSpace_yoneda B S hS (T i))
    hV b g hcov hg

/-- The complement of the image of a closed immersion of finite presentation into an affine scheme
is compact, being a retrocompact constructible set. -/
private theorem isCompact_compl_range_closedImmersion
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsClosedImmersion f] [LocallyOfFinitePresentation f] :
    IsCompact (Set.range f)ᶜ := by
  have hc : Topology.IsConstructible (Set.range f) := by
    simpa only [Set.image_univ] using
      f.isConstructible_image (s := Set.univ) Topology.IsConstructible.univ
  exact (IsRetrocompact_of_IsConstructible hc.compl).isCompact

/-- A morphism to `X` whose image on points misses a closed subspace factors through the open
complement of that subspace. -/
private theorem factorsThrough_openComplement_of_range_disjoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z : Subfunctor F) (hZ : IsClosedSubspace B S hS Z)
    (T A : BigFppfOver B S hS) (b : yoneda.obj T ⟶ F) (d : A ⟶ T)
    (hd : ∀ x, (BigFppfOver.toScheme B S hS).map d x ∉
      Set.range ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd b))) :
    ∃ a : yoneda.obj A ⟶ (openComplement B S hS Z).toFunctor,
      a ≫ (openComplement B S hS Z).ι = yoneda.map d ≫ b := by
  let G := BigFppfOver.toScheme B S hS
  let U := openComplement B S hS Z
  suffices H : Subfunctor.range (yoneda.map d ≫ b) ≤ U from
    ⟨Subfunctor.lift _ H, Subfunctor.lift_ι _ H⟩
  rintro Q _ ⟨r, rfl⟩ Q' e he
  let k : Q'.unop ⟶ T := e.unop ≫ r ≫ d
  have hk : b.app Q' k ∈ Z.obj Q' := by
    change F.map e (b.app Q (r ≫ d)) ∈ Z.obj Q' at he
    rw [← b.naturality_apply] at he
    change b.app Q' (e.unop ≫ (r ≫ d)) ∈ Z.obj Q' at he
    simpa only [k, Category.assoc] using he
  let z : yoneda.obj Q'.unop ⟶ Z.toFunctor := yonedaEquiv.symm ⟨b.app Q' k, hk⟩
  have hz : z ≫ Z.ι = yoneda.map k ≫ b := by
    apply yonedaEquiv.injective
    show ((z.app Q' (𝟙 Q'.unop)).val) = b.app Q' (𝟙 _ ≫ k)
    rw [Category.id_comp]
    exact congrArg Subtype.val
      ((yonedaEquiv (X := Q'.unop) (F := Z.toFunctor)).apply_symm_apply
        ⟨b.app Q' k, hk⟩)
  let l' : Q'.unop ⟶ hZ.2.1.pullback b := hZ.2.1.lift z k hz
  have hl : l' ≫ hZ.2.1.snd b = k := hZ.2.1.lift_snd z k hz
  refine ⟨fun q => hd (G.map (e.unop ≫ r) q) ⟨G.map l' q, ?_⟩⟩
  show (G.map l' ≫ G.map (hZ.2.1.snd b)) q =
    (G.map (e.unop ≫ r) ≫ G.map d) q
  rw [← G.map_comp, hl, ← G.map_comp]
  rfl

/-- The image of the chosen chart of `Y ×_X T` covers the part of the affine chart `T` lying over
the closed subspace `Z`. -/
private theorem closed_chart_range_covered
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : FormalGlueingSituation B S hS)
    (T W : BigFppfOver B S hS) (b : yoneda.obj T ⟶ D.X)
    (a' : yoneda.obj W ⟶ pullback D.f b)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a')
    (h : W ⟶ T) (hh : yoneda.map h = a' ≫ pullback.snd D.f b) :
    ∀ x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (D.closed_Z.2.1.snd b)),
      ∃ w ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        (D.closed_Z.2.1.snd (a' ≫ pullback.fst D.f b ≫ D.f))),
        (BigFppfOver.toScheme B S hS).map h w = x := by
  let G := BigFppfOver.toScheme B S hS
  let R := D.closed_Z.2.1
  let ZT := R.pullback b
  let i : ZT ⟶ T := R.snd b
  let z : yoneda.obj ZT ⟶ D.Z.toFunctor := R.fst b
  let _ := D.iso_over_Z
  let y : yoneda.obj ZT ⟶ D.Y :=
    z ≫ inv (D.Z.fromPreimage D.f) ≫ (D.Z.preimage D.f).ι
  have hy : y ≫ D.f = yoneda.map i ≫ b := by
    dsimp [y]
    rw [Category.assoc, Category.assoc, ← Subfunctor.fromPreimage_ι,
      IsIso.inv_hom_id_assoc]
    exact R.w b
  let t : yoneda.obj ZT ⟶ pullback D.f b := pullback.lift y (yoneda.map i) hy
  let P := hs.1.pullback t
  let p : P ⟶ ZT := hs.1.snd t
  let q : P ⟶ W := yoneda.preimage (hs.1.fst t)
  have hq : yoneda.map q = hs.1.fst t := by simp [q]
  have hp : Surjective (G.map p) := hs.2 t (hs.1.fst t) p (hs.1.isPullback t)
  have hpq : q ≫ h = p ≫ i := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hh, hq, ← Category.assoc, hs.1.w t]
    show (yoneda.map p ≫ t) ≫ pullback.snd D.f b = yoneda.map p ≫ yoneda.map i
    simp only [Category.assoc, t, pullback.lift_snd]
  let k := a' ≫ pullback.fst D.f b ≫ D.f
  have hk : k = yoneda.map h ≫ b := by
    dsimp only [k]
    rw [hh, Category.assoc, pullback.condition]
  have hz : (yoneda.map p ≫ z) ≫ D.Z.ι = yoneda.map q ≫ k := by
    rw [Category.assoc, R.w b, hk, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, hpq]
  let l' : P ⟶ R.pullback k := R.lift (yoneda.map p ≫ z) q hz
  have hl' : l' ≫ R.snd k = q := R.lift_snd _ q hz
  rintro x ⟨zt, rfl⟩
  obtain ⟨pt, hpt⟩ := hp.surj zt
  refine ⟨G.map q pt, ⟨G.map l' pt, ?_⟩, ?_⟩
  · show (G.map l' ≫ G.map (R.snd k)) pt = G.map q pt
    rw [← G.map_comp, hl']
  · show (G.map q ≫ G.map h) pt = G.map i zt
    rw [← G.map_comp, hpq, G.map_comp]
    show G.map i (G.map p pt) = G.map i zt
    rw [hpt]

/-- A factorization of the underlying morphism of schemes through another morphism of the site
lifts to a factorization in the site. -/
private theorem exists_overHom_of_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A W T : BigFppfOver B S hS} (d : A ⟶ T) (h : W ⟶ T)
    (k : (BigFppfOver.toScheme B S hS).obj A ⟶
      (BigFppfOver.toScheme B S hS).obj W)
    (hk : k ≫ (BigFppfOver.toScheme B S hS).map h =
      (BigFppfOver.toScheme B S hS).map d) :
    ∃ k' : A ⟶ W, k' ≫ h = d := by
  let l : A.left ⟶ W.left := B.inclusion.preimage k
  have hl : l ≫ h.left = d.left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    show B.inclusion.map l ≫
      (BigFppfOver.toScheme B S hS).map h =
      (BigFppfOver.toScheme B S hS).map d
    dsimp only [l]
    rw [B.inclusion.map_preimage]
    exact hk
  let k' : A ⟶ W := Over.homMk l (by
    rw [← Over.w h, ← Category.assoc, hl, Over.w d])
  exact ⟨k', Over.OverMorphism.ext hl⟩

/-- The open complement and the formal-glueing morphism admit an fpqc
covering refinement. -/
@[stacks 0AF1]
theorem exists_fpqcCovering_refining_openComplement_and_source
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : FormalGlueingSituation B S hS) :
    ∃ (I : Type u)
      (Xi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (g : ∀ i, Xi i ⟶ D.X),
      (∀ i, IsAlgebraicSpace B S hS (Xi i)) ∧
      IsFpqcCovering B S hS g ∧
      (∀ i, (∃ a : Xi i ⟶ D.U.toFunctor, a ≫ D.U.ι = g i) ∨
        (∃ b : Xi i ⟶ D.Y, b ≫ D.f = g i)) := by
  classical
  apply exists_fpqc_refinement_of_affine_charts B S hS D
  intro T b hT hb
  obtain ⟨W, a', hW, hs, ha⟩ := exists_affine_source_chart B S hS D T b hT hb
  let a : yoneda.obj W ⟶ D.Y := a' ≫ pullback.fst D.f b
  let h : W ⟶ T := yoneda.preimage (a' ≫ pullback.snd D.f b)
  have hcomm : yoneda.map h ≫ b = a ≫ D.f := by
    simp only [h, Functor.map_preimage, a, Category.assoc, pullback.condition]
  let G := BigFppfOver.toScheme B S hS
  let C := D.closed_Z.2.1.pullback (a ≫ D.f)
  let c : C ⟶ W := D.closed_Z.2.1.snd (a ≫ D.f)
  have hc : _root_.AlgebraicGeometry.IsClosedImmersion (G.map c) :=
    D.closed_Z.2.2 (a ≫ D.f) (D.closed_Z.2.1.fst (a ≫ D.f)) c
      (D.closed_Z.2.1.isPullback (a ≫ D.f))
  have hflat : ∀ w ∈ Set.range (G.map c), ((G.map h).stalkMap w).hom.Flat :=
    flatAt_on_closed_chart B S hS D W T a b h ha hb hcomm
  let ZT := D.closed_Z.2.1.pullback b
  let i : ZT ⟶ T := D.closed_Z.2.1.snd b
  let z : yoneda.obj ZT ⟶ D.Z.toFunctor := D.closed_Z.2.1.fst b
  have hsquare : IsPullback z (yoneda.map i) D.Z.ι b :=
    D.closed_Z.2.1.isPullback b
  have hi : _root_.AlgebraicGeometry.IsClosedImmersion (G.map i) := D.closed_Z.2.2 b z i hsquare
  have hz : (MorphismProperty.inverseImage (@Etale.{u}) G).presheaf z :=
    presheafEtale_of_isPullback B S hS hsquare.flip hb
  have hfp : LocallyOfFinitePresentation (G.map i) :=
    D.finitePresentation_Z.1 ZT T z b i hz hb hsquare.w.symm
  let _ := hT
  let _ := hW
  let _ := hi
  let _ := hc
  let _ := hfp
  let O : (G.obj T).Opens :=
    ⟨(Set.range (G.map i))ᶜ, hi.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hO : IsCompact (O : Set (G.obj T)) :=
    isCompact_compl_range_closedImmersion (G.map i)
  obtain ⟨J, hJ, U, hU, hsup⟩ := exists_finite_affine_opens_of_isCompact (G.obj T) O hO
  let _ := hJ
  have hcover : ∀ x ∉ Set.range (G.map i), ∃ j, x ∈ U j := by
    intro x hx
    have hxO : x ∈ O := hx
    rw [← hsup] at hxO
    simpa only [TopologicalSpace.Opens.mem_iSup] using hxO
  have hclosedCover : ∀ x ∈ Set.range (G.map i),
      ∃ w ∈ Set.range (G.map c), G.map h w = x := by
    simpa only [a, Category.assoc] using
      closed_chart_range_covered B S hS D T W b a' hs h (by simp [h])
  obtain ⟨K, hK, V, g, hV, hsize, hg, hfactor⟩ :=
    exists_affine_fpqcCovering_of_affine_closed_locus (G.map h)
      (Set.range (G.map i)) (Set.range (G.map c)) hc.isClosedEmbedding.isClosed_range
      hclosedCover hflat J U hU hcover
  have hVsite (k : K) : B.Contains (V k) :=
    (hsize k).trans_lt (max_lt W.left.property T.left.property)
  let sg (k : K) : B.obj (hVsite k) ⟶ T.left := B.inclusion.preimage (g k)
  let A (k : K) : BigFppfOver B S hS := Over.mk (sg k ≫ T.hom)
  let d (k : K) : A k ⟶ T := Over.homMk (sg k)
  have hd (k : K) : G.map (d k) = g k := B.inclusion.map_preimage _
  have hcover' : Presieve.ofArrows (fun k => G.obj (A k)) (fun k => G.map (d k)) ∈
      Scheme.fpqcPrecoverage (G.obj T) := by
    simp only [hd]
    exact hg
  refine ⟨K, (fun k => yoneda.obj (A k)), (fun k => yoneda.map (d k)),
    (fun k => isAlgebraicSpace_yoneda B S hS (A k)),
    represented_fpqc_family B S hS K A d hcover', ?_⟩
  intro k
  rcases hfactor k with ⟨j, l, hl⟩ | ⟨l, hl⟩
  · refine Or.inl (factorsThrough_openComplement_of_range_disjoint B S hS D.Z D.closed_Z T (A k) b
      (d k) fun x => ?_)
    rw [hd, ← hl]
    have hx : ((l ≫ (U j).ι) x) ∈ U j := (l x).property
    have hle : U j ≤ O := by rw [← hsup]; exact le_iSup U j
    exact hle hx
  · obtain ⟨l', hl'⟩ := exists_overHom_of_comp B S hS (d k) h l (by rwa [hd])
    refine Or.inr ⟨yoneda.map l' ≫ a, ?_⟩
    rw [Category.assoc, ← hcomm, ← Category.assoc, ← Functor.map_comp, hl']

end AlgebraicGeometry.Space

end
