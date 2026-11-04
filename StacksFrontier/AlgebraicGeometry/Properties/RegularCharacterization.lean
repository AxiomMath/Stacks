module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# Characterizations of regular schemes

A scheme is regular — every point has an affine open neighbourhood with regular ring of
sections — if and only if it is locally Noetherian and all of its local rings are regular, and
it suffices to check regularity of the local rings at the closed points. Equivalently, the ring
of sections is regular on every affine open, or on the members of a single affine open covering,
or the scheme admits an open covering by regular open subschemes. Every open subscheme of a
regular scheme is again regular. Finally, a locally Noetherian scheme is regular exactly when
it is regular in codimension `k` for every `k`.

## Main results

* `AlgebraicGeometry.isRegular_tfae`: the three characterizations of a regular scheme by its
  local rings.
* `AlgebraicGeometry.isRegular_tfae_cover`: the characterizations by affine opens and by
  coverings.
* `AlgebraicGeometry.IsRegular.restrict`: open subschemes of a regular scheme are regular.
* `AlgebraicGeometry.isRegular_iff_forall_isRegularInCodimension`: regularity is the conjunction
  of Serre's conditions `(R_k)`.
* `AlgebraicGeometry.isLocallyNoetherian_of_isRegular`: the Noetherian half of the definition of
  Tag 02IS, read off globally — a regular scheme is locally Noetherian.

## Implementation notes

The entries of the first `List.TFAE` are the three items of the source, in order. The local ring
at a point `x` is the stalk `X.presheaf.stalk x`, and closed points are
`TopologicalSpace.closedPoints X`.

Passing from closed points to all points uses that every point of a locally Noetherian scheme
specializes to a closed point, together with the fact that a localization of a regular local
ring at a smaller prime is again regular. The latter is obtained from the global-dimension
characterization of regular rings, and is formulated for localizations of a Noetherian ring at
a pair of nested primes so that it applies directly to two points of one affine open.

The covering characterizations are all proved against the single pivot condition "locally
Noetherian with regular local rings", which is the second entry of `isRegular_tfae`; a covering
is a family of opens whose supremum is the top open. Since `IsRegularRing` already includes the
Noetherian condition, no separate Noetherian hypothesis appears on the coordinate rings.

The nonnegative indices `k ≥ 0` of Serre's conditions are represented by natural numbers, so
"`(R_k)` for all `k ≥ 0`" is quantification over `ℕ`; only the index given by the dimension of
the local ring at the point under consideration is actually used.

## References

* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
* [Stacks Project, Tag 02IU](https://stacks.math.columbia.edu/tag/02IU)
* [Stacks Project, Tag 0B3C](https://stacks.math.columbia.edu/tag/0B3C)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If the ring of sections on an affine open is regular, then so is the local ring at each of
its points. -/
private lemma regular_stalk_of_regular_affine {X : Scheme.{u}} (U : X.affineOpens)
    (hU : IsRegularRing Γ(X, U)) {x : X} (hxU : x ∈ U.val) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := U.2.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularRing.isRegularLocalRing_of_isLocalization
    (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk x)

/-- Every stalk of a regular scheme is a regular local ring. -/
private lemma regular_stalk_of_isRegular (X : Scheme.{u})
    (hX : IsRegular X) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  let ⟨U, hxU, hU⟩ := hX x
  regular_stalk_of_regular_affine U hU hxU

/-- If all stalks of a locally Noetherian scheme are regular, then the ring of sections on every
affine open is a regular ring. -/
private lemma regular_affine_of_regular_stalk (X : Scheme.{u})
    [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (U : X.affineOpens) : IsRegularRing Γ(X, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  rw [isRegularRing_iff]
  intro p hp
  let z : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  let x : X := U.2.fromSpec z
  have hx : x ∈ U.val := by
    show z ∈ U.2.fromSpec ⁻¹ᵁ (U : X.Opens)
    rw [U.2.fromSpec_preimage_self]
    trivial
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p := U.2.isLocalization_stalk' z hx
  have := hX x
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv).symm

/-- A localization of a Noetherian ring at a prime contained in a prime with regular
localization is itself regular. -/
public lemma regular_atPrime_of_le {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have : IsRegularRing (Localization.AtPrime q) :=
    ((IsLocalRing.isRegularRing_tfae (R := Localization.AtPrime q)).out 1 3).mp hq
  let e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime q) q
  let Q : Ideal (Localization.AtPrime q) := (e.symm ⟨p, inferInstance, hpq⟩).1
  have : Q.IsPrime := (e.symm ⟨p, inferInstance, hpq⟩).2
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    IsRegularRing.isRegularLocalRing_of_isLocalization Q (Localization.AtPrime Q)
  have hQ : Q.comap (algebraMap R (Localization.AtPrime q)) = p :=
    congr_arg Subtype.val (e.apply_symm_apply ⟨p, inferInstance, hpq⟩)
  let : Algebra R (Localization.AtPrime Q) := inferInstance
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    q.primeCompl (Localization.AtPrime Q) Q
  have : IsRegularLocalRing
      (Localization.AtPrime (Q.comap (algebraMap R (Localization.AtPrime q)))) :=
    @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime Q) _ inferInstance _ _
      (IsLocalization.algEquiv
      (Q.comap (algebraMap R (Localization.AtPrime q))).primeCompl
        (Localization.AtPrime Q) (Localization.AtPrime
          (Q.comap (algebraMap R (Localization.AtPrime q))))).toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv
    (Localization.localRingEquiv
      (Q.comap (algebraMap R (Localization.AtPrime q))) p (RingEquiv.refl R) (by
        show Q.comap (algebraMap R (Localization.AtPrime q)) = p.comap (RingHom.id R)
        simpa using hQ))

/-- A scheme is regular if and only if it is locally Noetherian with regular local rings at
every point, if and only if it is locally Noetherian with regular local rings at closed points. -/
@[stacks 02IT]
theorem isRegular_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsRegular X,
      IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x),
      IsLocallyNoetherian X ∧
        (∀ x : X, x ∈ closedPoints X → IsRegularLocalRing (X.presheaf.stalk x))] := by
  classical
  tfae_have 1 → 2 := fun h ↦
    ⟨(isLocallyNoetherian_iff_of_iSup_eq_top (S := fun x ↦ (h x).choose)
      (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, (h x).choose_spec.1⟩)).2
        fun x ↦ (h x).choose_spec.2.toIsNoetherian, regular_stalk_of_isRegular X h⟩
  tfae_have 2 → 3 := fun ⟨hN, hreg⟩ ↦ ⟨hN, fun x _ ↦ hreg x⟩
  tfae_have 3 → 1 := by
    rintro ⟨_, hclosed⟩
    have hstalk (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
      obtain ⟨y, hyclosed, hxy⟩ := exists_specializes_closedPoint X x
      obtain ⟨V, hyV⟩ : ∃ V : X.affineOpens, y ∈ V.val := by
        rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]; trivial
      have hxV : x ∈ V.val := hxy.mem_open V.1.2 hyV
      let px := V.2.primeIdealOf ⟨x, hxV⟩
      let py := V.2.primeIdealOf ⟨y, hyV⟩
      have hpxy : px ≤ py := by
        rw [PrimeSpectrum.le_iff_specializes]
        show V.2.isoSpec.hom ⟨x, hxV⟩ ⤳ V.2.isoSpec.hom ⟨y, hyV⟩
        exact V.2.isoSpec.hom.base.hom.map_specializes
          (Topology.IsInducing.subtypeVal.specializes_iff.mp hxy)
      have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
      let := X.presheaf.algebra_section_stalk ⟨y, hyV⟩
      have := V.2.isLocalization_stalk ⟨y, hyV⟩
      have := hclosed y hyclosed
      have hpy : IsRegularLocalRing (Localization.AtPrime py.asIdeal) :=
        IsRegularLocalRing.of_ringEquiv
          ((IsLocalization.algEquiv py.asIdeal.primeCompl
            (Localization.AtPrime py.asIdeal) (X.presheaf.stalk y)).toRingEquiv).symm
      have hpx : IsRegularLocalRing (Localization.AtPrime px.asIdeal) :=
        regular_atPrime_of_le px.asIdeal py.asIdeal hpxy hpy
      let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
      have := V.2.isLocalization_stalk ⟨x, hxV⟩
      exact @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime px.asIdeal) _ hpx _ _
        (IsLocalization.algEquiv px.asIdeal.primeCompl
          (Localization.AtPrime px.asIdeal) (X.presheaf.stalk x)).toRingEquiv
    intro x
    obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.val := by
      rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]; trivial
    exact ⟨U, hxU, regular_affine_of_regular_stalk X hstalk U⟩
  tfae_finish

section Cover

/-- The local ring of an open subscheme at a point is the local ring of the ambient scheme at
that point, so regularity of the one is regularity of the other. -/
private lemma isRegularLocalRing_restrict_stalk_iff {X : Scheme.{u}} (U : X.Opens) (x : U) :
    IsRegularLocalRing (U.toScheme.presheaf.stalk x) ↔
      IsRegularLocalRing (X.presheaf.stalk x.1) :=
  ⟨fun _ ↦ .of_ringEquiv (U.stalkIso x).commRingCatIsoToRingEquiv,
    fun _ ↦ .of_ringEquiv (U.stalkIso x).commRingCatIsoToRingEquiv.symm⟩

/-- A scheme all of whose affine coordinate rings are regular is regular. -/
private lemma isRegular_of_forall_affineOpen (X : Scheme.{u})
    (h : ∀ U : X.affineOpens, IsRegularRing Γ(X, U)) : IsRegular X := by
  intro x
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.val := by
    rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]; trivial
  exact ⟨U, hxU, h U⟩

/-- Regularity of every affine coordinate ring is the pivot condition. -/
private lemma forall_affineOpen_isRegularRing_iff (X : Scheme.{u}) :
    (∀ U : X.affineOpens, IsRegularRing Γ(X, U)) ↔
      IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  ⟨fun h ↦ ((isRegular_tfae X).out 1 2 rfl rfl).mp (isRegular_of_forall_affineOpen X h),
    fun ⟨_, hstalk⟩ ↦ regular_affine_of_regular_stalk X hstalk⟩

/-- Regularity of the coordinate rings of one affine open covering is the pivot condition. -/
private lemma exists_affine_cover_isRegularRing_iff (X : Scheme.{u}) :
    (∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsRegularRing Γ(X, U i)) ↔
      IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
  constructor
  · rintro ⟨I, U, hcover, hreg⟩
    refine ⟨(isLocallyNoetherian_iff_of_iSup_eq_top hcover).2 fun i ↦ (hreg i).toIsNoetherian,
      fun x ↦ ?_⟩
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp
      (show x ∈ (⨆ i, (U i).val : X.Opens) by simp [hcover])
    exact regular_stalk_of_regular_affine (U i) (hreg i) hxi
  · rintro ⟨_, hstalk⟩
    exact ⟨X.affineOpens, id, iSup_affineOpens_eq_top X,
      regular_affine_of_regular_stalk X hstalk⟩

/-- Having an open covering by regular schemes is the pivot condition. -/
private lemma exists_open_cover_isRegular_iff (X : Scheme.{u}) :
    (∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsRegular (U i).toScheme) ↔
      IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
  constructor
  · rintro ⟨I, U, hcover, hreg⟩
    have hi i := ((isRegular_tfae (U i).toScheme).out 1 2 rfl rfl).mp (hreg i)
    let 𝒰 := X.openCoverOfIsOpenCover U hcover
    have hNoethEach : ∀ i : 𝒰.I₀, IsLocallyNoetherian (𝒰.X i) := fun i ↦ by
      simpa [𝒰, Scheme.openCoverOfIsOpenCover] using (hi i).1
    refine ⟨(isLocallyNoetherian_iff_openCover 𝒰).2 hNoethEach, fun x ↦ ?_⟩
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ (⨆ i, U i : X.Opens) by simp [hcover])
    exact (isRegularLocalRing_restrict_stalk_iff (U i) ⟨x, hxi⟩).mp ((hi i).2 ⟨x, hxi⟩)
  · rintro ⟨_, hstalk⟩
    refine ⟨X.affineOpens, fun U ↦ (U : X.Opens), iSup_affineOpens_eq_top X, fun U ↦ ?_⟩
    exact ((isRegular_tfae (U : X.Opens).toScheme).out 2 1 rfl rfl).mp
      ⟨inferInstance, fun x ↦ (isRegularLocalRing_restrict_stalk_iff _ x).mpr (hstalk x.1)⟩

/-- **Stacks Project, Tag 02IU.** A scheme is regular if and only if the ring of sections is
regular on every affine open, if and only if it is regular on the members of one affine open
covering, if and only if the scheme has an open covering by regular open subschemes. -/
@[stacks 02IU "equivalent conditions"]
theorem isRegular_tfae_cover (X : Scheme.{u}) :
    List.TFAE [
      IsRegular X,
      ∀ U : X.affineOpens, IsRegularRing Γ(X, U),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsRegularRing Γ(X, U i),
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsRegular (U i).toScheme] := by
  refine List.tfae_of_forall
    (b := IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) ?_
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil] at hP
  rcases hP with rfl | rfl | rfl | rfl | hP
  · exact (isRegular_tfae X).out 1 2 rfl rfl
  · exact forall_affineOpen_isRegularRing_iff X
  · exact exists_affine_cover_isRegularRing_iff X
  · exact exists_open_cover_isRegular_iff X
  · cases hP

/-- **Stacks Project, Tag 02IU.** Every open subscheme of a regular scheme is regular. -/
@[stacks 02IU "open subschemes"]
theorem IsRegular.restrict {X : Scheme.{u}} (hX : IsRegular X) (U : X.Opens) :
    IsRegular U.toScheme := by
  have hLocX := ((isRegular_tfae X).out 1 2 rfl rfl).mp hX
  have := hLocX.1
  exact ((isRegular_tfae U.toScheme).out 2 1 rfl rfl).mp
    ⟨inferInstance, fun x ↦ (isRegularLocalRing_restrict_stalk_iff U x).mpr (hLocX.2 x.1)⟩

end Cover

/-- **Stacks Project, Tag 0B3C.** A locally Noetherian scheme is regular if and only if it is
regular in codimension `k` for every nonnegative integer `k`. -/
@[stacks 0B3C]
theorem isRegular_iff_forall_isRegularInCodimension (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsRegular X ↔ ∀ k : ℕ, IsRegularInCodimension X k := by
  refine ⟨fun h k x _ ↦ (((isRegular_tfae X).out 1 2 rfl rfl).mp h).2 x, fun h ↦ ?_⟩
  refine ((isRegular_tfae X).out 2 1 rfl rfl).mp ⟨inferInstance, fun x ↦ ?_⟩
  refine h (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).height.toNat x ?_
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast (ENat.natCast_toNat Ideal.height_ne_top_of_isPrime).ge

/-- **A regular scheme is locally Noetherian.** Regularity of a scheme asks for an affine open
neighbourhood with regular — in particular Noetherian — ring of sections around each point, and
those neighbourhoods cover. -/
theorem isLocallyNoetherian_of_isRegular {X : Scheme.{u}} (hX : IsRegular X) :
    IsLocallyNoetherian X :=
  (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1

end AlgebraicGeometry
