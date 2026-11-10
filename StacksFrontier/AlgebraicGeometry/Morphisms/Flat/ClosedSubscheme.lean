module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.Pure

/-!
# Flat closed subschemes and generalization-stable closed subsets

For a scheme `X`, taking the underlying closed subset is a bijection from the flat closed
subschemes of `X` to the closed subsets of `X` stable under generalization. A morphism of schemes
whose set-theoretic image lies in such a subscheme factors uniquely through it.

A connected component of a scheme is closed and stable under generalization, so it carries a
canonical closed subscheme structure, namely the unique one whose closed immersion is flat.

## Main definitions

* `AlgebraicGeometry.connectedComponentIdealSheaf`: the canonical closed subscheme structure on
  the connected component of a point of a scheme.

## Main results

* `AlgebraicGeometry.support_bijOn_flat_closedImmersions`: taking the support is a bijection
  between flat closed subschemes and generalization-stable closed subsets.
* `AlgebraicGeometry.existsUnique_lift_of_flat_closedImmersion`: a morphism whose image lies in
  a flat closed subscheme factors uniquely through it.
* `stableUnderGeneralization_connectedComponent`: a connected component of a topological space
  is stable under generalization.
* `AlgebraicGeometry.support_connectedComponentIdealSheaf` and
  `AlgebraicGeometry.flat_subschemeι_connectedComponentIdealSheaf`: the canonical structure on a
  connected component is supported on it and has flat closed immersion, and
  `AlgebraicGeometry.eq_connectedComponentIdealSheaf_of_flat` shows it is the only such.

## Implementation notes

Closed subschemes are represented by `AlgebraicGeometry.Scheme.IdealSheafData`, and their
underlying closed subsets by `AlgebraicGeometry.Scheme.IdealSheafData.support`. The bijection is
therefore stated as a `Set.BijOn` between the flat ideal sheaves and the generalization-stable
members of `TopologicalSpace.Closeds X`.

Flatness of a closed subscheme is equivalent to purity of each of its ideals over an affine open,
and `Ideal.zeroLocus_inj_of_pure` makes a pure ideal recoverable from its vanishing locus. The
surjectivity half of the bijection glues the affine-local pure ideals produced by
`exists_isPure_zeroLocus_eq` with `AlgebraicGeometry.Scheme.IdealSheafData.mkOfMemSupportIff`; the
required compatibility with restriction to a standard open is purity of the image ideal under a
localization, isolated as `Ideal.Pure` of `Ideal.map`.

The factorization statement records uniqueness as well as existence, since a closed immersion is
a monomorphism.

## References

* [Stacks Project, Tag 04PW](https://stacks.math.columbia.edu/tag/04PW)
* [Stacks Project, Tag 04PX](https://stacks.math.columbia.edu/tag/04PX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- A connected component of a topological space is stable under generalization: every
generalization of a point of the component again lies in the component. -/
public theorem stableUnderGeneralization_connectedComponent {α : Type*} [TopologicalSpace α]
    (x : α) : StableUnderGeneralization (connectedComponent x) := by
  intro a b hba ha
  rw [← connectedComponent_eq_iff_mem.mpr ha]
  exact isConnected_singleton.closure.subset_connectedComponent
    (specializes_iff_mem_closure.mp hba) (subset_closure rfl)

namespace AlgebraicGeometry

/-- The image of a pure ideal in a localization of the ring is pure. -/
private theorem pure_map_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (I : Ideal R) [I.Pure] :
    (I.map (algebraMap R S)).Pure := by
  apply ((Ideal.pure_tfae (I.map (algebraMap R S))).out 5 1).mp
  intro z hz
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  obtain ⟨t, htM, htr⟩ :=
    (IsLocalization.mk'_mem_map_algebraMap_iff M S I r s).mp hz
  obtain ⟨y, hy, hry⟩ := Ideal.exists_eq_mul_of_pure (I := I) htr
  have htunit : IsUnit (algebraMap R S t) := IsLocalization.map_units S ⟨t, htM⟩
  have hry' : algebraMap R S r = algebraMap R S r * algebraMap R S y := by
    apply (IsUnit.mul_right_inj htunit).mp
    simpa [map_mul, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (algebraMap R S) hry
  refine ⟨algebraMap R S y, Ideal.mem_map_of_mem _ hy, ?_⟩
  apply (IsUnit.mul_right_inj (IsLocalization.map_units S s)).mp
  calc
    algebraMap R S s * IsLocalization.mk' S r s = algebraMap R S r :=
      IsLocalization.mk'_spec' S r s
    _ = algebraMap R S r * algebraMap R S y := hry'
    _ = algebraMap R S s * (IsLocalization.mk' S r s * algebraMap R S y) := by
      rw [← IsLocalization.mk'_spec' S r s]
      ring

/-- A pure ideal of the sections over an affine open whose vanishing locus is the preimage of a
given generalization-stable closed subset. -/
private noncomputable def affinePureIdeal {X : Scheme.{u}} (Z : Closeds X)
    (hgen : StableUnderGeneralization (Z : Set X)) (U : X.affineOpens) :
    Ideal Γ(X, U) :=
  Classical.choose <|
    exists_isPure_zeroLocus_eq
      (U.2.fromSpec ⁻¹' (Z : Set X))
      (Z.isClosed.preimage U.2.fromSpec.continuous)
      (hgen.preimage U.2.fromSpec.continuous)

private lemma affinePureIdeal_spec {X : Scheme.{u}} (Z : Closeds X)
    (hgen : StableUnderGeneralization (Z : Set X)) (U : X.affineOpens) :
    (affinePureIdeal Z hgen U).Pure ∧
      PrimeSpectrum.zeroLocus (affinePureIdeal Z hgen U : Set Γ(X, U)) =
        U.2.fromSpec ⁻¹' (Z : Set X) :=
  Classical.choose_spec <|
    exists_isPure_zeroLocus_eq _ (Z.isClosed.preimage U.2.fromSpec.continuous)
      (hgen.preimage U.2.fromSpec.continuous)

/-- The pure ideals cut out by a generalization-stable closed subset are compatible with
restriction along a standard open: both sides have the same vanishing locus, and purity makes
that enough. -/
private lemma affinePureIdeal_map {X : Scheme.{u}} (Z : Closeds X)
    (hgen : StableUnderGeneralization (Z : Set X)) (U : X.affineOpens) (f : Γ(X, U)) :
    (affinePureIdeal Z hgen U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      affinePureIdeal Z hgen (X.affineBasicOpen f) := by
  let V := X.affineBasicOpen f
  let F := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
  let : Algebra Γ(X, U) Γ(X, X.basicOpen f) := F.hom.toAlgebra
  let : IsLocalization (Submonoid.powers f) Γ(X, X.basicOpen f) :=
    U.2.isLocalization_basicOpen f
  have : (affinePureIdeal Z hgen U).Pure := (affinePureIdeal_spec Z hgen U).1
  have hPureMap : ((affinePureIdeal Z hgen U).map F.hom).Pure :=
    pure_map_of_isLocalization (R := Γ(X, U)) (S := Γ(X, X.basicOpen f))
      (Submonoid.powers f) (affinePureIdeal Z hgen U)
  have hzeroMap : PrimeSpectrum.zeroLocus
      (((affinePureIdeal Z hgen U).map F.hom : Ideal Γ(X, V)) : Set Γ(X, V)) =
      PrimeSpectrum.comap F.hom ⁻¹' PrimeSpectrum.zeroLocus
        (affinePureIdeal Z hgen U : Set Γ(X, U)) := by
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus]
    exact Ideal.map_le_iff_le_comap
  have hzeroEq : PrimeSpectrum.zeroLocus
      (((affinePureIdeal Z hgen U).map F.hom : Ideal Γ(X, V)) : Set Γ(X, V)) =
      PrimeSpectrum.zeroLocus (affinePureIdeal Z hgen V : Set Γ(X, V)) := by
    rw [hzeroMap, (affinePureIdeal_spec Z hgen U).2, (affinePureIdeal_spec Z hgen V).2]
    have hmap : (fun p : PrimeSpectrum Γ(X, V) =>
        U.2.fromSpec (PrimeSpectrum.comap F.hom p)) = fun p => V.2.fromSpec p := by
      funext p
      calc
        U.2.fromSpec (PrimeSpectrum.comap F.hom p) =
            U.2.fromSpec (Spec.map F p) := by rfl
        _ = (Spec.map F ≫ U.2.fromSpec) p := (Scheme.Hom.comp_apply _ _ _).symm
        _ = V.2.fromSpec p := congrArg (fun g : Spec Γ(X, V) ⟶ X => g p)
          (U.2.map_fromSpec V.2 (homOfLE (X.basicOpen_le f)).op)
    ext p
    exact Iff.of_eq (congrArg (fun x : X => x ∈ (Z : Set X)) (congrFun hmap p))
  exact (@Ideal.zeroLocus_inj_of_pure (Γ(X, V)) _
    ((affinePureIdeal Z hgen U).map F.hom)
    (affinePureIdeal Z hgen V) hPureMap (affinePureIdeal_spec Z hgen V).1).mp hzeroEq

private lemma affinePureIdeal_mem_support_iff {X : Scheme.{u}} (Z : Closeds X)
    (hgen : StableUnderGeneralization (Z : Set X)) (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) :
    x ∈ (Z : Set X) ↔ x ∈ X.zeroLocus (U := U.1) (affinePureIdeal Z hgen U) := by
  have hzero : X.zeroLocus (U := U.1) (affinePureIdeal Z hgen U) ∩ U.1 =
      (Z : Set X) ∩ U.1 := by
    rw [← U.2.fromSpec_image_zeroLocus, (affinePureIdeal_spec Z hgen U).2]
    simp [Set.image_preimage_eq_inter_range, U.2.range_fromSpec]
  have hmem : x ∈ X.zeroLocus (U := U.1) (affinePureIdeal Z hgen U) ↔ x ∈ (Z : Set X) := by
    have h := congrArg (fun s : Set X => x ∈ s) hzero
    simpa [Set.mem_inter_iff, hxU] using h
  simpa [Scheme.mem_zeroLocus_iff] using hmem.symm

/-- The closed subscheme cut out by a generalization-stable closed subset, with pure ideals over
every affine open. -/
private noncomputable def idealSheafOfClosedGeneralizationStable {X : Scheme.{u}}
    (Z : Closeds X) (hgen : StableUnderGeneralization (Z : Set X)) : X.IdealSheafData :=
  Scheme.IdealSheafData.mkOfMemSupportIff
    (affinePureIdeal Z hgen)
    (affinePureIdeal_map Z hgen)
    (Z : Set X)
    (affinePureIdeal_mem_support_iff Z hgen)

private lemma pure_ideal_of_flat_subscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [Flat I.subschemeι] (U : X.affineOpens) : (I.ideal U).Pure := by
  have hflat : (I.subschemeι.app U.1).hom.Flat := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      (Flat.flat_appLE I.subschemeι U.2 (U.2.preimage I.subschemeι) le_rfl)
  rw [I.subschemeι_app U] at hflat
  exact (RingHom.Flat.comp_iff_of_bijective_left
    (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso U).inv)).mp hflat

private lemma flat_subscheme_of_pure_ideals {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ U, (I.ideal U).Pure) : Flat I.subschemeι := by
  rw [flat_iff]
  intro U hU V hV e
  let U₀ : X.affineOpens := ⟨U, hU⟩
  have : IsAffine (U.toScheme) := hU
  let W : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage I.subschemeι
  let g : W.toScheme ⟶ U.toScheme := I.subschemeι.resLE U W le_rfl
  have hg : Flat g := by
    have : IsAffine (W.toScheme) := hW
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Scheme.Hom.appLE_eq_app, I.subschemeι_app U₀]
    have hquot' : (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U₀))).hom.Flat := hI U₀
    have hiso {A B : CommRingCat.{u}} (e : A ⟶ B) [IsIso e] : e.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    simpa only [CommRingCat.hom_comp, RingHom.comp_assoc] using
      (((hiso U.topIso.hom).comp hquot').comp (hiso (I.subschemeObjIso U₀).inv)).comp
        (hiso W.topIso.inv)
  have hr : Flat ((𝟙 I.subscheme : I.subscheme ⟶ I.subscheme).resLE W V e) := by
    rw [Scheme.Hom.resLE_id]
    infer_instance
  have hcomp : (𝟙 I.subscheme : I.subscheme ⟶ I.subscheme).resLE W V e ≫ g =
      I.subschemeι.resLE U V e := by
    simp [g]
  have hflat : Flat (I.subschemeι.resLE U V e) := hcomp ▸
    (inferInstance : Flat ((𝟙 I.subscheme : I.subscheme ⟶ I.subscheme).resLE W V e ≫ g))
  have : IsAffine (V.toScheme) := hV
  have htop : (CommRingCat.Hom.hom ((I.subschemeι.resLE U V e).appTop)).Flat :=
    (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp hflat
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso I.subschemeι U V e)).mp htop

/-- Two closed subschemes with flat closed immersions and the same support are equal. -/
private theorem eq_of_flat_subschemeι_of_support_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    [Flat I.subschemeι] [Flat J.subschemeι] (hsup : I.support = J.support) : I = J := by
  apply Scheme.IdealSheafData.ext
  funext U
  have hzeroX : X.zeroLocus (U := U.1) (I.ideal U) =
      X.zeroLocus (U := U.1) (J.ideal U) := by
    ext x
    by_cases hx : x ∈ U.1
    · rw [← I.mem_support_iff_of_mem hx, hsup, J.mem_support_iff_of_mem hx]
    · have hK (K : X.IdealSheafData) : x ∈ X.zeroLocus (U := U.1) (K.ideal U) := by
        rw [Scheme.mem_zeroLocus_iff]
        exact fun f _ hbasic => hx (X.basicOpen_le f hbasic)
      exact iff_of_true (hK I) (hK J)
  have hzeroSpec : PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U)) =
      PrimeSpectrum.zeroLocus (J.ideal U : Set Γ(X, U)) := by
    ext p
    rw [← U.2.fromSpec_preimage_zeroLocus, ← U.2.fromSpec_preimage_zeroLocus]
    exact Iff.of_eq (congrArg (fun s : Set X => U.2.fromSpec p ∈ s) hzeroX)
  have := pure_ideal_of_flat_subscheme I U
  have := pure_ideal_of_flat_subscheme J U
  exact (Ideal.zeroLocus_inj_of_pure (I := I.ideal U) (J := J.ideal U)).mp hzeroSpec

/-- Taking the support is a bijection from the flat closed subschemes of a scheme to the closed
subsets stable under generalization. -/
@[stacks 04PW "bijection"]
public theorem support_bijOn_flat_closedImmersions (X : Scheme.{u}) :
    Set.BijOn (fun I : X.IdealSheafData => I.support)
      {I : X.IdealSheafData | Flat I.subschemeι}
      {Z : Closeds X | StableUnderGeneralization (Z : Set X)} := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro I (hI : Flat I.subschemeι)
    change StableUnderGeneralization (I.support : Set X)
    rw [← I.range_subschemeι]
    exact (Flat.generalizingMap I.subschemeι).stableUnderGeneralization_range
  · intro I (hI : Flat I.subschemeι) J (hJ : Flat J.subschemeι) hsup
    exact eq_of_flat_subschemeι_of_support_eq I J hsup
  · exact fun Z hZ => ⟨idealSheafOfClosedGeneralizationStable Z hZ,
      flat_subscheme_of_pure_ideals _ fun U => (affinePureIdeal_spec Z hZ U).1, rfl⟩

/-- A morphism whose set-theoretic image lies in a flat closed subscheme factors uniquely
through it. -/
@[stacks 04PW "factorization", ega "I 4.1.8" "special case"]
public theorem existsUnique_lift_of_flat_closedImmersion {X Y : Scheme.{u}}
    (I : X.IdealSheafData) [Flat I.subschemeι] (g : Y ⟶ X)
    (hg : Set.range g ⊆ (I.support : Set X)) :
    ∃! h : Y ⟶ I.subscheme, h ≫ I.subschemeι = g := by
  have : Surjective (pullback.fst g I.subschemeι) := by
    rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst,
      Set.preimage_eq_univ_iff]
    rintro y ⟨x, rfl⟩
    rw [I.range_subschemeι]
    exact hg ⟨x, rfl⟩
  have : IsIso (pullback.fst g I.subschemeι) := Flat.isIso_of_surjective_of_mono _
  refine ⟨inv (pullback.fst g I.subschemeι) ≫ pullback.snd g I.subschemeι, ?_, ?_⟩
  · simp [← pullback.condition]
  · exact fun h hh => (cancel_mono I.subschemeι).1 (hh.trans (by simp [← pullback.condition]))

/-- The canonical closed subscheme structure on the connected component of a point `x` of a
scheme `X`: the closed subscheme cut out by `connectedComponent x`, which is closed and stable
under generalization. It is the unique closed subscheme structure on that component whose closed
immersion into `X` is flat. -/
@[stacks 04PX, no_expose]
public noncomputable def connectedComponentIdealSheaf {X : Scheme.{u}} (x : X) :
    X.IdealSheafData :=
  idealSheafOfClosedGeneralizationStable ⟨connectedComponent x, isClosed_connectedComponent⟩
    (stableUnderGeneralization_connectedComponent x)

/-- The support of the canonical closed subscheme structure on a connected component is that
connected component, by construction. -/
private lemma support_connectedComponentIdealSheaf_aux {X : Scheme.{u}} (x : X) :
    ((connectedComponentIdealSheaf x).support : Set X) = connectedComponent x :=
  rfl

/-- The canonical closed subscheme structure on a connected component is supported on that
connected component. -/
public alias support_connectedComponentIdealSheaf := support_connectedComponentIdealSheaf_aux

/-- The closed immersion of the canonical closed subscheme structure on a connected component
into the ambient scheme is flat. -/
public instance flat_subschemeι_connectedComponentIdealSheaf {X : Scheme.{u}} (x : X) :
    Flat (connectedComponentIdealSheaf x).subschemeι :=
  flat_subscheme_of_pure_ideals _ fun U =>
    (affinePureIdeal_spec ⟨connectedComponent x, isClosed_connectedComponent⟩
      (stableUnderGeneralization_connectedComponent x) U).1

/-- The closed immersion of the canonical closed subscheme structure on a connected component has
that connected component as its set-theoretic image. -/
public theorem range_subschemeι_connectedComponentIdealSheaf {X : Scheme.{u}} (x : X) :
    Set.range (connectedComponentIdealSheaf x).subschemeι = connectedComponent x :=
  (connectedComponentIdealSheaf x).range_subschemeι.trans
    (support_connectedComponentIdealSheaf x)

/-- The canonical closed subscheme structure on a connected component is the only one supported on
that component whose closed immersion is flat. -/
public theorem eq_connectedComponentIdealSheaf_of_flat {X : Scheme.{u}} (x : X)
    (I : X.IdealSheafData) [Flat I.subschemeι]
    (hI : (I.support : Set X) = connectedComponent x) :
    I = connectedComponentIdealSheaf x :=
  eq_of_flat_subschemeι_of_support_eq _ _
    (Closeds.ext (hI.trans (support_connectedComponentIdealSheaf x).symm))

end AlgebraicGeometry

end
