module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationLocalRingsAlgebra
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationLocalRingsStalk
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationSections
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Scheme.ClopenIdempotent
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperModificationOffClosedPoint

/-!
# The local rings of the algebraization of the formal neighbourhood of a curve

Let `C ⊆ X` be the closed subscheme cut out by an ideal sheaf `D` on a locally Noetherian scheme,
`A = lim Γ(Cₙ, 𝒪)` the ring of formal functions along `C`, assumed local and Noetherian, and let
`fY : Y ⟶ Spec A` be a proper morphism algebraizing the `𝔪`-adic tower
`Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`: compatible `kₙ : Xₙ ⟶ Y` exhibit `Xₙ` as
`Y ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)`. This is the output of Grothendieck's algebraization theorem in
the construction of Stacks 0D5E
(`IsPositiveConormal.exists_isProper_algebraization_bijective_appTop` in the namespace
`AlgebraicGeometry.Scheme.IdealSheafData`).

For a point `x` of `X₀` the local rings `𝒪_{Y, k₀ x}` and `𝒪_{X, x}` both surject onto the
tower of local rings `𝒪_{Xₙ, x}`, with kernels in the powers of their maximal ideals (the first
is cut out by `𝔪ⁿ⁺¹`, the second by `D^{M n + 1}` and `𝔪ⁿ⁺¹`). So their completions are
isomorphic (`IsLocalRing.adicCompletionRingEquivOfTower`), they have the same dimension and are
regular together. If `X` is regular of dimension at most two along `C`, the local rings of `Y`
at the closed points, all of which lie on `k₀(X₀)` because `Y` is proper over the local scheme
`Spec A`, are regular of dimension at most two, hence domains. Every point of `Y` specializes to
a closed point, so all local rings of `Y` are domains of dimension at most two; and `Y` is
connected because `Γ(Y, 𝒪_Y) ≅ A` is local. Hence `Y` is integral of dimension at most two.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.adicTowerPoint`: the images of a point of `X₀` in the
  members `Xₙ` of the tower.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ringKrullDim_stalk_eq_and_isRegularLocalRing_iff`:
  `𝒪_{Y, k₀ x}` and `𝒪_{X, x}` have the same dimension and are regular together.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_eq_of_isClosed_singleton`: every closed point
  of `Y` lies on `k₀(X₀)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_and_topologicalKrullDim_le_two`: `Y` is
  integral of dimension at most two when `X` is regular of dimension at most two along `C`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isIso_morphismRestrict_puncturedSpectrum_of_isPullback`:
  if moreover `dim A ≥ 2`, then `Y ⟶ Spec A` is an isomorphism over `Spec A ∖ {𝔪}`.
* `IsPositiveConormal.exists_isProper_algebraization_isIntegral` (in the same namespace):
  the algebraization of a curve with positive conormal bundle in a regular surface is integral of
  dimension at most two.
* `AlgebraicGeometry.connectedSpace_of_bijective_appTop`,
  `AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`: a scheme with local ring of global
  functions is connected; a connected Noetherian scheme with domains as local rings is
  irreducible.

## References

* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
* [Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An idempotent of a local ring is `0` or `1`. -/
theorem _root_.IsLocalRing.eq_zero_or_one_of_isIdempotentElem {A : Type*} [CommRing A]
    [IsLocalRing A] {a : A} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · exact Or.inr (h.mul_left_cancel (by rw [ha.eq, mul_one]))
  · exact Or.inl ((h.mul_left_eq_zero).mp (by rw [mul_sub, mul_one, ha.eq, sub_self]))

/-- A scheme `Y` with a bijection `R ≅ Γ(Y, 𝒪_Y)` from a local ring is nonempty and connected:
a clopen subset is the nonvanishing locus of an idempotent global section, which comes from an
idempotent of `R`, hence is `0` or `1`. -/
theorem connectedSpace_of_bijective_appTop {R : CommRingCat.{u}} [IsLocalRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) (hbij : Function.Bijective ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom) :
    ConnectedSpace Y := by
  have hne : Nonempty Y := by
    by_contra hne
    have : IsEmpty Y := not_nonempty_iff.mp hne
    have htop : (⊤ : Y.Opens) = ⊥ := by
      ext y
      exact isEmptyElim y
    have : Subsingleton Γ(Y, ⊤) := by
      rw [htop]
      infer_instance
    exact one_ne_zero (hbij.1 (Subsingleton.elim (((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom 1)
      (((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom 0)))
  rw [connectedSpace_iff_clopen]
  refine ⟨hne, fun U hU => ?_⟩
  obtain ⟨e, he, hUe⟩ := Scheme.exists_isIdempotentElem_basicOpen_eq U hU
  obtain ⟨a, rfl⟩ := hbij.2 e
  have ha : IsIdempotentElem a := hbij.1 (by rw [map_mul]; exact he)
  rcases IsLocalRing.eq_zero_or_one_of_isIdempotentElem ha with rfl | rfl
  · left
    rw [← hUe, map_zero, Scheme.basicOpen_zero]
    rfl
  · right
    rw [← hUe, map_one, Scheme.basicOpen_one]
    rfl

/-- **A connected Noetherian scheme whose local rings are domains is irreducible**: every point
lies on exactly one irreducible component, so the finitely many components are disjoint, hence
open, and connectedness leaves only one. -/
theorem irreducibleSpace_of_isDomain_stalk {Y : Scheme.{u}} [IsNoetherian Y] [ConnectedSpace Y]
    (h : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) : IrreducibleSpace Y := by
  obtain ⟨y₀⟩ := ConnectedSpace.toNonempty (α := Y)
  set Z := _root_.irreducibleComponent y₀
  have hZ : Z ∈ irreducibleComponents Y :=
    _root_.irreducibleComponent_mem_irreducibleComponents y₀
  have hcompl : Zᶜ = ⋃ Z' ∈ irreducibleComponents Y \ {Z}, Z' := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · intro hy
      refine ⟨_root_.irreducibleComponent y,
        ⟨_root_.irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        _root_.mem_irreducibleComponent⟩
      rintro hyZ
      exact hy (hyZ ▸ _root_.mem_irreducibleComponent)
    · rintro ⟨Z', ⟨hZ', hne⟩, hy⟩ hyZ
      have := h y
      exact hne (congrArg Subtype.val
        (eq_of_mem_irreducibleComponents_of_isDomain_stalk y (Z₁ := ⟨Z', hZ'⟩) (Z₂ := ⟨Z, hZ⟩)
          hy hyZ))
  have hopen : IsOpen Z := by
    rw [← isClosed_compl_iff, hcompl]
    exact ((NoetherianSpace.finite_irreducibleComponents).sdiff).isClosed_biUnion
      fun Z' hZ' => isClosed_of_mem_irreducibleComponents Z' hZ'.1
  have huniv : Z = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_of_mem_irreducibleComponents Z hZ, hopen⟩
      ⟨y₀, _root_.mem_irreducibleComponent⟩
  have hirr : IsIrreducible Z := _root_.isIrreducible_irreducibleComponent
  rw [huniv] at hirr
  exact (irreducibleSpace_def Y).mpr hirr

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

section Tower

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsLocalRing (formalNeighborhoodRing D)]
  {M : ℕ → ℕ} (hM : Monotone M)

/-- The images `xₙ ∈ Xₙ` of a point `x ∈ X₀` under the transition maps of the adic tower. -/
def adicTowerPoint (x : adicTower D (maximalIdeal (formalNeighborhoodRing D)) M 0) :
    ∀ n, adicTower D (maximalIdeal (formalNeighborhoodRing D)) M n
  | 0 => x
  | n + 1 => adicTowerSucc D _ hM n (adicTowerPoint x n)

/-- The images of a point of `X₀` in the tower all lie over the same point of `X`. -/
theorem adicTowerToScheme_adicTowerPoint
    (x : adicTower D (maximalIdeal (formalNeighborhoodRing D)) M 0) (n : ℕ) :
    adicTowerToScheme D _ M n (adicTowerPoint D hM x n) = adicTowerToScheme D _ M 0 x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    change adicTowerToScheme D _ M (n + 1) (adicTowerSucc D _ hM n (adicTowerPoint D hM x n)) = _
    rw [← Scheme.Hom.comp_apply, adicTowerSucc_adicTowerToScheme]

variable {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D)))
  (k : ∀ n, adicTower D (maximalIdeal (formalNeighborhoodRing D)) M n ⟶ Y)
  (hk : ∀ n, adicTowerSucc D _ hM n ≫ k (n + 1) = k n)
  (hcart : ∀ n, IsPullback (k n)
    (adicTowerToThickening D (maximalIdeal (formalNeighborhoodRing D)) M n) fY
    (adicThickeningι (formalNeighborhoodRing D) (maximalIdeal (formalNeighborhoodRing D)) n))

include hk in
/-- The images of a point of `X₀` in the tower all map to the same point of `Y`. -/
theorem apply_adicTowerPoint (x : adicTower D (maximalIdeal (formalNeighborhoodRing D)) M 0)
    (n : ℕ) : k n (adicTowerPoint D hM x n) = k 0 x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    change k (n + 1) (adicTowerSucc D _ hM n (adicTowerPoint D hM x n)) = _
    rw [← Scheme.Hom.comp_apply, hk n]

include hk hcart in
/-- **The local rings of `Y` along the closed fibre are those of `X` along `C`, up to
completion.** For a point `x ∈ X₀ = C_{M 0} ×_{Spec A} Spec (A ⧸ 𝔪)` (with `n ≤ M n` for all `n`)
the local rings `𝒪_{Y, k₀ x}` and `𝒪_{X, x}` both surject onto the tower `𝒪_{Xₙ, xₙ}` with kernels
in the powers of their maximal ideals, so they have isomorphic completions: they have the same
Krull dimension and one is regular exactly when the other is. -/
theorem ringKrullDim_stalk_eq_and_isRegularLocalRing_iff
    [IsNoetherianRing (formalNeighborhoodRing D)] [IsLocallyNoetherian X] [IsProper fY]
    (hMn : ∀ n, n ≤ M n) (x : adicTower D (maximalIdeal (formalNeighborhoodRing D)) M 0) :
    ringKrullDim (Y.presheaf.stalk (k 0 x)) =
        ringKrullDim (X.presheaf.stalk (adicTowerToScheme D _ M 0 x)) ∧
      (IsRegularLocalRing (Y.presheaf.stalk (k 0 x)) ↔
        IsRegularLocalRing (X.presheaf.stalk (adicTowerToScheme D _ M 0 x))) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  have : ∀ n, IsClosedImmersion (k n) := fun n => by
    rw [← (hcart n).isoPullback_hom_fst]
    infer_instance
  let p := adicTowerPoint D hM x
  have hy := apply_adicTowerPoint D hM k hk x
  have hz := adicTowerToScheme_adicTowerPoint D hM x
  let π : ∀ n, (adicTower D _ M (n + 1)).presheaf.stalk (p (n + 1)) →+*
      (adicTower D _ M n).presheaf.stalk (p n) := fun n =>
    (adicTowerSucc D _ hM n).stalkMapAt (p n) (p (n + 1)) rfl
  let φ : ∀ n, Y.presheaf.stalk (k 0 x) →+* (adicTower D _ M n).presheaf.stalk (p n) :=
    fun n => (k n).stalkMapAt (p n) (k 0 x) (hy n)
  let ψ : ∀ n, X.presheaf.stalk (adicTowerToScheme D _ M 0 x) →+*
      (adicTower D _ M n).presheaf.stalk (p n) :=
    fun n => (adicTowerToScheme D _ M n).stalkMapAt (p n) _ (hz n)
  have hφ : ∀ n, (π n).comp (φ (n + 1)) = φ n := fun n => by
    exact (Scheme.Hom.stalkMapAt_comp _ _ _ _ _ _ _).trans
      (Scheme.Hom.stalkMapAt_congr _ _ (hk n) _ _ _ _)
  have hψ : ∀ n, (π n).comp (ψ (n + 1)) = ψ n := fun n => by
    exact (Scheme.Hom.stalkMapAt_comp _ _ _ _ _ _ _).trans
      (Scheme.Hom.stalkMapAt_congr _ _ (adicTowerSucc_adicTowerToScheme D _ hM n) _ _ _ _)
  have hφs : ∀ n, Function.Surjective (φ n) := fun n =>
    Scheme.Hom.surjective_stalkMapAt _ _ _ _
  have hψs : ∀ n, Function.Surjective (ψ n) := fun n =>
    Scheme.Hom.surjective_stalkMapAt _ _ _ _
  have hφk : ∀ n, RingHom.ker (φ n) ≤ maximalIdeal (Y.presheaf.stalk (k 0 x)) ^ (n + 1) :=
    fun n => Scheme.Hom.ker_stalkMapAt_le _ _ _ _
      (ker_stalkMap_le_maximalIdeal_pow_of_isPullback fY _ n (k n) _ (hcart n) (p n))
  have hψk : ∀ n, RingHom.ker (ψ n) ≤
      maximalIdeal (X.presheaf.stalk (adicTowerToScheme D _ M 0 x)) ^ (n + 1) := fun n => by
    refine Scheme.Hom.ker_stalkMapAt_le _ _ _ _ ?_
    rw [Scheme.Hom.stalkMap_comp]
    exact ker_comp_le_maximalIdeal_pow _ ((D ^ (M n + 1)).subschemeι.stalkMap_surjective _) _
      (ker_stalkMap_le_maximalIdeal_pow_of_isPullback (thickeningToSpec D (M n)) _ n
        (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) (p n))
      ((ker_stalkMap_subschemeι_pow_le_maximalIdeal_pow D (M n) _).trans
        (Ideal.pow_le_pow_right (by have := hMn n; omega)))
  exact ⟨IsLocalRing.ringKrullDim_eq_of_tower π φ ψ hφ hψ hφs hψs hφk hψk,
    IsLocalRing.isRegularLocalRing_iff_of_tower π φ ψ hφ hψ hφs hψs hφk hψk⟩

include hcart in
/-- **The closed points of `Y` lie on the closed fibre `k₀(X₀)`.** A closed point of `Y` maps to
a closed point of `Spec A`, which is the closed point `𝔪` since `A` is local, and the points of
`Y` over `𝔪` are the image of `X₀ = Y ×_{Spec A} Spec (A ⧸ 𝔪)`. -/
theorem exists_eq_of_isClosed_singleton [IsProper fY] (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ∃ x : adicTower D (maximalIdeal (formalNeighborhoodRing D)) M 0, k 0 x = y := by
  have hcl : IsClosed ({fY y} : Set (Spec (.of (formalNeighborhoodRing D)))) := by
    have h := fY.isClosedMap _ hy
    rwa [Set.image_singleton] at h
  have hmax : (fY y).asIdeal = maximalIdeal (formalNeighborhoodRing D) :=
    IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcl)
  have hrange : fY y ∈ Set.range
      (adicThickeningι (formalNeighborhoodRing D) (maximalIdeal (formalNeighborhoodRing D)) 0) := by
    change fY y ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal (formalNeighborhoodRing D) ^ (0 + 1))))
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    refine (PrimeSpectrum.mem_zeroLocus (fY y : PrimeSpectrum _) _).mpr ?_
    rw [Ideal.mk_ker, hmax, zero_add, pow_one]
  have hmem : y ∈ Set.range (pullback.fst fY (adicThickeningι (formalNeighborhoodRing D)
      (maximalIdeal (formalNeighborhoodRing D)) 0)) := by
    rw [Scheme.Pullback.range_fst]
    exact hrange
  obtain ⟨w, rfl⟩ := hmem
  refine ⟨(hcart 0).isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]

include hk hcart in
/-- **The algebraization is integral of dimension at most two.** In the situation above (with
`A` Noetherian, `X` locally Noetherian, `n ≤ M n`, and `A ≅ Γ(Y, 𝒪_Y)`), assume the local rings
of `X` at the points of `C` are regular of dimension at most two. Then `Y` is integral and of
Krull dimension at most two. -/
theorem isIntegral_and_topologicalKrullDim_le_two
    [IsNoetherianRing (formalNeighborhoodRing D)] [IsLocallyNoetherian X] [IsProper fY]
    (hMn : ∀ n, n ≤ M n)
    (hbij : Function.Bijective
      ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ fY.appTop).hom)
    (hreg : ∀ z ∈ D.support, IsRegularLocalRing (X.presheaf.stalk z))
    (hdim : ∀ z ∈ D.support, ringKrullDim (X.presheaf.stalk z) ≤ 2) :
    IsIntegral Y ∧ topologicalKrullDim Y ≤ 2 := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace fY
  have : IsNoetherian Y := {}
  have hclosed : ∀ y : Y, IsClosed ({y} : Set Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) ≤ 2 := by
    intro y hy
    obtain ⟨x, rfl⟩ := exists_eq_of_isClosed_singleton D fY k hcart y hy
    have hz : adicTowerToScheme D _ M 0 x ∈ D.support := by
      have hr : adicTowerToScheme D _ M 0 x ∈ Set.range (D ^ (M 0 + 1)).subschemeι :=
        ⟨_, rfl⟩
      rwa [range_subschemeι, support_pow_succ] at hr
    obtain ⟨h₁, h₂⟩ := ringKrullDim_stalk_eq_and_isRegularLocalRing_iff D hM fY k hk hcart hMn x
    exact ⟨h₂.mpr (hreg _ hz), h₁ ▸ hdim _ hz⟩
  have hspec : ∀ y : Y, ∃ y' : Y, y ⤳ y' ∧ IsClosed ({y'} : Set Y) := fun y => by
    obtain ⟨y', hy', hcl⟩ := isClosed_closure.exists_closed_singleton
      (⟨y, subset_closure rfl⟩ : (closure ({y} : Set Y)).Nonempty)
    exact ⟨y', specializes_iff_mem_closure.mpr hy', hcl⟩
  have hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y) := fun y => by
    obtain ⟨y', h, hc⟩ := hspec y
    have := (hclosed y' hc).1
    have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y')
    let : Algebra (Y.presheaf.stalk y') (Y.presheaf.stalk y) :=
      (Y.presheaf.stalkSpecializes h).hom.toAlgebra
    have := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
    exact IsLocalization.isDomain_of_le_nonZeroDivisors (Y.presheaf.stalk y)
      (M := ((maximalIdeal (Y.presheaf.stalk y)).under (Y.presheaf.stalk y')).primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have : ConnectedSpace Y := connectedSpace_of_bijective_appTop fY hbij
  have : IrreducibleSpace Y := irreducibleSpace_of_isDomain_stalk hdom
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    have := hdom y
    exact isReduced_of_noZeroDivisors
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced Y, ?_⟩
  have hdimeq : topologicalKrullDim Y = Order.krullDim Y := by
    let _ : PartialOrder Y := specializationOrder Y
    exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [hdimeq, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun y => ?_
  obtain ⟨y', h, hc⟩ := hspec y
  calc ((Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight y' : ℕ∞) := by
        exact_mod_cast Order.coheight_anti (le_iff_specializes.mpr h)
    _ = ringKrullDim (Y.presheaf.stalk y') := (ringKrullDim_stalk_eq_coheight y').symm
    _ ≤ 2 := (hclosed y' hc).2

include hk hcart in
/-- **The algebraization is an isomorphism off the closed point.** Under the hypotheses of
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_and_topologicalKrullDim_le_two`, if moreover
`A` has dimension at least two, then `fY` is an isomorphism over the punctured spectrum
`Spec A ∖ {𝔪}` (`AlgebraicGeometry.isIso_morphismRestrict_puncturedSpectrum`). -/
theorem isIso_morphismRestrict_puncturedSpectrum_of_isPullback
    [IsNoetherianRing (formalNeighborhoodRing D)] [IsLocallyNoetherian X] [IsProper fY]
    (hMn : ∀ n, n ≤ M n)
    (hbij : Function.Bijective
      ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ fY.appTop).hom)
    (hreg : ∀ z ∈ D.support, IsRegularLocalRing (X.presheaf.stalk z))
    (hdim : ∀ z ∈ D.support, ringKrullDim (X.presheaf.stalk z) ≤ 2)
    (hA : 2 ≤ ringKrullDim (formalNeighborhoodRing D)) :
    IsIso (fY ∣_ puncturedSpectrum (formalNeighborhoodRing D)) := by
  obtain ⟨hint, hW⟩ := isIntegral_and_topologicalKrullDim_le_two D hM fY k hk hcart hMn hbij hreg
    hdim
  have : IsIso ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ fY.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso fY.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso _).inv fY.appTop
  exact isIso_morphismRestrict_puncturedSpectrum fY hA hW

end Tower

section PositiveConormal

variable {X : Scheme.{u}} {D : X.IdealSheafData}

open Stacks.Ample Stacks.Divisors in
/-- **The algebraization of the formal neighbourhood of a curve with positive conormal bundle in
a regular surface is integral of dimension at most two.** In the situation of
`IsPositiveConormal.exists_isProper_algebraization_bijective_appTop`,
with `X` locally Noetherian and its local rings at the points of `C` regular of dimension at most
two, the algebraization `fY : Y ⟶ Spec A` can be chosen with all the properties stated there and
with `Y` integral of Krull dimension at most two. -/
theorem IsPositiveConormal.exists_isProper_algebraization_isIntegral
    [IsEffectiveCartierDivisor D] [IsLocallyNoetherian X] {c : ℕ} (hD : IsPositiveConormal D c)
    {N : ℕ} (hgg : ∀ V : X.affineOpens, D.ideal V ^ (N + 1) ≤
      Ideal.span (chartGlobalSymbols D V N) ⊔ D.ideal V ^ (N + 2))
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsProper f]
    (hC : IsAmple D.subscheme (conormalModule D))
    (hreg : ∀ z ∈ D.support, IsRegularLocalRing (X.presheaf.stalk z))
    (hdim : ∀ z ∈ D.support, ringKrullDim (X.presheaf.stalk z) ≤ 2) :
    letI := hD.isLocalRing
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D))), IsProper fY ∧
      (∃ (𝒩 : Y.Modules) (h𝒩 : IsInvertibleModule Y 𝒩), @IsAmple Y 𝒩 h𝒩) ∧
      (∃ (k : ∀ n, adicTower D (maximalIdeal _) (positiveConormalTowerIndex N) n ⟶ Y),
        (∀ n, adicTowerSucc D _ (monotone_positiveConormalTowerIndex N) n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n)
          (adicTowerToThickening D (maximalIdeal _) (positiveConormalTowerIndex N) n)
          fY (adicThickeningι (formalNeighborhoodRing D) (maximalIdeal _) n)) ∧
      Function.Bijective
        ((Scheme.ΓSpecIso (.of (formalNeighborhoodRing D))).inv ≫ fY.appTop).hom ∧
      IsIntegral Y ∧ topologicalKrullDim Y ≤ 2 := by
  let _ := hD.isLocalRing
  have : IsNoetherianRing (formalNeighborhoodRing D) :=
    hD.isNoetherianCompleteLocalRing.isNoetherian
  obtain ⟨Y, fY, hfY, h𝒩, ⟨k, hk, hcart⟩, hbij⟩ :=
    hD.exists_isProper_algebraization_bijective_appTop hgg f hC
  have := hfY
  exact ⟨Y, fY, hfY, h𝒩, ⟨k, hk, hcart⟩, hbij,
    isIntegral_and_topologicalKrullDim_le_two D (monotone_positiveConormalTowerIndex N) fY k hk
      hcart (fun n => by simp only [positiveConormalTowerIndex]; nlinarith) hbij hreg hdim⟩

end PositiveConormal

end AlgebraicGeometry.Scheme.IdealSheafData

end
