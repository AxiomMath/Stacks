module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.GRing.Henselization

/-!
# G-schemes

A scheme is a G-scheme if every point has an affine open neighbourhood whose ring of sections is
a G-ring. Equivalently the scheme is locally Noetherian and the map from each local ring to its
completion is regular, and it suffices to check this at the closed points. Equivalently again,
the ring of sections is a G-ring on every affine open, or on the members of one affine open
covering, or the scheme has an open covering by G-schemes; and every open subscheme of a
G-scheme is a G-scheme.

## Main definitions

* `AlgebraicGeometry.IsGScheme`: the predicate that a scheme is a G-scheme.

## Main results

* `AlgebraicGeometry.isGScheme_tfae`: the characterizations of a G-scheme by its local rings.
* `AlgebraicGeometry.isGScheme_tfae_cover`: the characterizations by affine opens and by open
  coverings.
* `AlgebraicGeometry.IsGScheme.restrict`: every open subscheme of a G-scheme is a G-scheme.

## Implementation notes

The local ring at `x` is `X.presheaf.stalk x`, its completion is the adic completion
`AdicCompletion (IsLocalRing.maximalIdeal _) _`, and closed points are
`TopologicalSpace.closedPoints X`. A covering is a family of opens whose supremum is `⊤`.

All characterizations are proved against the pivot condition "locally Noetherian and every local
ring is a G-ring". For a Noetherian local ring, being a G-ring is the regularity of the map to its
completion (`isGRing_iff_isRegularRingHom_completion`). Passing from closed points to all points
uses that every point of a locally Noetherian scheme specializes to a closed point
(`exists_specializes_closedPoint`) and that a localization of a G-ring is a G-ring
(`isGRing_of_essFiniteType`, Tag 07PV); the source cites Tag 07PT here, which is the same
statement for a local ring.

## References

* [Stacks Project, Tag 0HA3](https://stacks.math.columbia.edu/tag/0HA3)
* [Stacks Project, Tag 0HA4](https://stacks.math.columbia.edu/tag/0HA4)
* [Stacks Project, Tag 0HA5](https://stacks.math.columbia.edu/tag/0HA5)
-/

@[expose] public section

open TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A scheme is a G-scheme if every point has an affine open neighbourhood whose ring of
sections is a G-ring. -/
@[stacks 0HA3]
public def IsGScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧ IsGRing Γ(X, U)

/-- The G-ring property is invariant under ring isomorphisms. -/
private lemma isGRing_of_ringEquiv' {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (hA : IsGRing A) : IsGRing B := by
  let := e.toRingHom.toAlgebra
  have : Algebra.FiniteType A B :=
    Algebra.FiniteType.of_surjective (Algebra.ofId A B)
      (fun b ↦ ⟨e.symm b, e.apply_symm_apply b⟩)
  have : Algebra.EssFiniteType A B := inferInstance
  exact isGRing_of_essFiniteType hA

/-- If the ring of sections on an affine open is a G-ring, then so is the local ring at each of
its points. -/
private lemma isGRing_stalk_of_affine {X : Scheme.{u}} (U : X.affineOpens)
    (hU : IsGRing Γ(X, U)) {x : X} (hxU : x ∈ U.val) :
    IsGRing (X.presheaf.stalk x) := by
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := U.2.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact isGRing_of_essFiniteType hU

/-- If every local ring of a locally Noetherian scheme is a G-ring, then so is the ring of
sections on every affine open. -/
private lemma isGRing_affine_of_stalk (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsGRing (X.presheaf.stalk x)) (U : X.affineOpens) : IsGRing Γ(X, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  refine ⟨inferInstance, fun p _ ↦ ?_⟩
  let z : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  let x : X := U.2.fromSpec z
  have hx : x ∈ U.val := by
    change z ∈ U.2.fromSpec ⁻¹ᵁ (U : X.Opens)
    rw [U.2.fromSpec_preimage_self]
    trivial
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p := U.2.isLocalization_stalk' z hx
  have hG : IsGRing (Localization.AtPrime p) := isGRing_of_ringEquiv'
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv).symm (hX x)
  have : IsNoetherianRing (Localization.AtPrime p) := hG.1
  exact (isGRing_iff_isRegularRingHom_completion (Localization.AtPrime p)).mp hG

/-- On a locally Noetherian scheme, if the local ring at `y` is a G-ring, then so is the local
ring at every generalization `x` of `y`: it is a localization of the local ring at `y`. -/
private lemma isGRing_stalk_of_specializes (X : Scheme.{u}) [IsLocallyNoetherian X] {x y : X}
    (hxy : x ⤳ y) (hy : IsGRing (X.presheaf.stalk y)) : IsGRing (X.presheaf.stalk x) := by
  obtain ⟨V, hyV⟩ : ∃ V : X.affineOpens, y ∈ V.val := by
    rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]; trivial
  have hxV : x ∈ V.val := hxy.mem_open V.1.2 hyV
  let px := (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal
  let py := (V.2.primeIdealOf ⟨y, hyV⟩).asIdeal
  have hpxy : px ≤ py := by
    change V.2.primeIdealOf ⟨x, hxV⟩ ≤ V.2.primeIdealOf ⟨y, hyV⟩
    rw [PrimeSpectrum.le_iff_specializes]
    change V.2.isoSpec.hom ⟨x, hxV⟩ ⤳ V.2.isoSpec.hom ⟨y, hyV⟩
    exact V.2.isoSpec.hom.base.hom.map_specializes
      (Topology.IsInducing.subtypeVal.specializes_iff.mp hxy)
  let S := Localization.AtPrime py
  let := X.presheaf.algebra_section_stalk ⟨y, hyV⟩
  have := V.2.isLocalization_stalk ⟨y, hyV⟩
  have hS : IsGRing S := isGRing_of_ringEquiv'
    ((IsLocalization.algEquiv py.primeCompl S (X.presheaf.stalk y)).toRingEquiv).symm hy
  have hdisj : Disjoint (py.primeCompl : Set Γ(X, V)) px :=
    Set.disjoint_left.mpr fun _ ha hpa ↦ ha (hpxy hpa)
  let P : Ideal S := px.map (algebraMap Γ(X, V) S)
  have : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint py.primeCompl S px inferInstance hdisj
  have hP : P.under Γ(X, V) = px :=
    IsLocalization.under_map_of_isPrime_disjoint py.primeCompl S inferInstance hdisj
  let T := Localization.AtPrime P
  have : Algebra.EssFiniteType S T := Algebra.EssFiniteType.of_isLocalization T P.primeCompl
  have hT : IsGRing T := isGRing_of_essFiniteType hS
  have hloc : IsLocalization.AtPrime T (P.under Γ(X, V)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization py.primeCompl T P
  have hM : (P.under Γ(X, V)).primeCompl = px.primeCompl := by
    ext a
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  have hloc' : IsLocalization px.primeCompl T := hM ▸ hloc
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := V.2.isLocalization_stalk ⟨x, hxV⟩
  exact isGRing_of_ringEquiv'
    (IsLocalization.algEquiv px.primeCompl T (X.presheaf.stalk x)).toRingEquiv hT

/-- The pivot condition: a scheme is a G-scheme if and only if it is locally Noetherian and all
of its local rings are G-rings. -/
private lemma isGScheme_iff_stalk (X : Scheme.{u}) :
    IsGScheme X ↔ IsLocallyNoetherian X ∧ ∀ x : X, IsGRing (X.presheaf.stalk x) := by
  classical
  constructor
  · intro h
    refine ⟨(isLocallyNoetherian_iff_of_iSup_eq_top (S := fun x ↦ (h x).choose)
      (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, (h x).choose_spec.1⟩)).2
        fun x ↦ (h x).choose_spec.2.1, fun x ↦ ?_⟩
    exact isGRing_stalk_of_affine _ (h x).choose_spec.2 (h x).choose_spec.1
  · rintro ⟨_, hstalk⟩ x
    obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.val := by
      rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]; trivial
    exact ⟨U, hxU, isGRing_affine_of_stalk X hstalk U⟩

/-- A scheme is a G-scheme if and only if it is locally Noetherian and the map from each local
ring to its completion is regular, if and only if it is locally Noetherian and the map from the
local ring at each closed point to its completion is regular. -/
@[stacks 0HA4]
theorem isGScheme_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsGScheme X,
      IsLocallyNoetherian X ∧ ∀ x : X,
        IsRegularRingHom (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))),
      IsLocallyNoetherian X ∧ ∀ x : X, x ∈ closedPoints X →
        IsRegularRingHom (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))] := by
  tfae_have 1 → 2 := by
    intro h
    obtain ⟨_, hstalk⟩ := (isGScheme_iff_stalk X).mp h
    exact ⟨inferInstance, fun x ↦
      (isGRing_iff_isRegularRingHom_completion (X.presheaf.stalk x)).mp (hstalk x)⟩
  tfae_have 2 → 3 := fun ⟨hN, h⟩ ↦ ⟨hN, fun x _ ↦ h x⟩
  tfae_have 3 → 1 := by
    rintro ⟨_, hclosed⟩
    refine (isGScheme_iff_stalk X).mpr ⟨inferInstance, fun x ↦ ?_⟩
    obtain ⟨y, hyclosed, hxy⟩ := exists_specializes_closedPoint X x
    exact isGRing_stalk_of_specializes X hxy
      ((isGRing_iff_isRegularRingHom_completion (X.presheaf.stalk y)).mpr (hclosed y hyclosed))
  tfae_finish

section Cover

/-- The local ring of an open subscheme at a point is the local ring of the ambient scheme at
that point, so the one is a G-ring exactly when the other is. -/
private lemma isGRing_restrict_stalk_iff {X : Scheme.{u}} (U : X.Opens) (x : U) :
    IsGRing (U.toScheme.presheaf.stalk x) ↔ IsGRing (X.presheaf.stalk x.1) :=
  ⟨isGRing_of_ringEquiv' (U.stalkIso x).commRingCatIsoToRingEquiv,
    isGRing_of_ringEquiv' (U.stalkIso x).commRingCatIsoToRingEquiv.symm⟩

/-- Every open subscheme of a scheme satisfying the pivot condition satisfies it. -/
private lemma isGScheme_restrict_of_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hstalk : ∀ x : X, IsGRing (X.presheaf.stalk x)) (U : X.Opens) : IsGScheme U.toScheme :=
  (isGScheme_iff_stalk U.toScheme).mpr
    ⟨inferInstance, fun x ↦ (isGRing_restrict_stalk_iff U x).mpr (hstalk x.1)⟩

/-- The G-ring property of every affine coordinate ring is the pivot condition. -/
private lemma forall_affineOpen_isGRing_iff (X : Scheme.{u}) :
    (∀ U : X.affineOpens, IsGRing Γ(X, U)) ↔
      IsLocallyNoetherian X ∧ ∀ x : X, IsGRing (X.presheaf.stalk x) := by
  refine ⟨fun h ↦ (isGScheme_iff_stalk X).mp fun x ↦ ?_,
    fun ⟨_, hstalk⟩ ↦ isGRing_affine_of_stalk X hstalk⟩
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.val := by
    rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]; trivial
  exact ⟨U, hxU, h U⟩

/-- The G-ring property of the coordinate rings of one affine open covering is the pivot
condition. -/
private lemma exists_affine_cover_isGRing_iff (X : Scheme.{u}) :
    (∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsGRing Γ(X, U i)) ↔
      IsLocallyNoetherian X ∧ ∀ x : X, IsGRing (X.presheaf.stalk x) := by
  constructor
  · rintro ⟨I, U, hcover, hG⟩
    refine ⟨(isLocallyNoetherian_iff_of_iSup_eq_top hcover).2 fun i ↦ (hG i).1, fun x ↦ ?_⟩
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp
      (show x ∈ (⨆ i, (U i).val : X.Opens) by simp [hcover])
    exact isGRing_stalk_of_affine (U i) (hG i) hxi
  · rintro ⟨_, hstalk⟩
    exact ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, isGRing_affine_of_stalk X hstalk⟩

/-- Having an open covering by G-schemes is the pivot condition. -/
private lemma exists_open_cover_isGScheme_iff (X : Scheme.{u}) :
    (∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsGScheme (U i).toScheme) ↔
      IsLocallyNoetherian X ∧ ∀ x : X, IsGRing (X.presheaf.stalk x) := by
  constructor
  · rintro ⟨I, U, hcover, hG⟩
    have hi i := (isGScheme_iff_stalk (U i).toScheme).mp (hG i)
    let 𝒰 := X.openCoverOfIsOpenCover U hcover
    have hNoethEach : ∀ i : 𝒰.I₀, IsLocallyNoetherian (𝒰.X i) := fun i ↦ by
      simpa [𝒰, Scheme.openCoverOfIsOpenCover] using (hi i).1
    refine ⟨(isLocallyNoetherian_iff_openCover 𝒰).2 hNoethEach, fun x ↦ ?_⟩
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ (⨆ i, U i : X.Opens) by simp [hcover])
    exact (isGRing_restrict_stalk_iff (U i) ⟨x, hxi⟩).mp ((hi i).2 ⟨x, hxi⟩)
  · rintro ⟨_, hstalk⟩
    exact ⟨X.affineOpens, fun U ↦ (U : X.Opens), iSup_affineOpens_eq_top X,
      fun U ↦ isGScheme_restrict_of_stalk hstalk U⟩

/-- A scheme is a G-scheme if and only if the ring of sections on every affine open is a G-ring,
if and only if it is a G-ring on the members of one affine open covering, if and only if the
scheme has an open covering by open subschemes which are G-schemes. -/
@[stacks 0HA5 "equivalent conditions (1)–(4)"]
theorem isGScheme_tfae_cover (X : Scheme.{u}) :
    List.TFAE [
      IsGScheme X,
      ∀ U : X.affineOpens, IsGRing Γ(X, U),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsGRing Γ(X, U i),
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsGScheme (U i).toScheme] := by
  refine List.tfae_of_forall
    (b := IsLocallyNoetherian X ∧ ∀ x : X, IsGRing (X.presheaf.stalk x)) ?_
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil] at hP
  rcases hP with rfl | rfl | rfl | rfl | hP
  · exact isGScheme_iff_stalk X
  · exact forall_affineOpen_isGRing_iff X
  · exact exists_affine_cover_isGRing_iff X
  · exact exists_open_cover_isGScheme_iff X
  · cases hP

/-- Every open subscheme of a G-scheme is a G-scheme. -/
@[stacks 0HA5 "open subschemes"]
theorem IsGScheme.restrict {X : Scheme.{u}} (hX : IsGScheme X) (U : X.Opens) :
    IsGScheme U.toScheme := by
  obtain ⟨_, hstalk⟩ := (isGScheme_iff_stalk X).mp hX
  exact isGScheme_restrict_of_stalk hstalk U

end Cover

end AlgebraicGeometry
