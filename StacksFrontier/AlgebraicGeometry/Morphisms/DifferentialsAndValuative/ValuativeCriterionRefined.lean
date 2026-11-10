module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.RingTheory.Valuation.Constructions
public import StacksFrontier.RingTheory.Valuation.Domination

/-!
# A refined valuative criterion for universally closed and separated morphisms

Let `f : X ⟶ S` and `h : U ⟶ X` be quasi-compact morphisms of schemes, with `h` having dense
image. If every valuative square for `f` whose generic-point map factors through `h` has a
unique lift, then `f` is universally closed; if `f` is also quasi-separated, it is separated.

Both schemes are first replaced by their reductions, which changes neither the topology nor the
valuative squares. A valuative square for the reduced morphism is then enlarged: its generic
point is spread out over an affine chart of the reduced source and a polynomial algebra on the
field, so that the resulting flat quasi-compact morphism has a scheme-theoretic image whose
points carry valuative diagrams through the dense source, by the valuative description of the
scheme-theoretic image. The hypothesis applied to such a diagram produces a lift over a larger
valuation ring, which dominates the original one, and the lift descends.

For separatedness, the criterion is applied to the diagonal: the two projections of a valuative
square for the diagonal become two lifts of one valuative square for `f`, so uniqueness makes
them equal, giving the lift for the diagonal; the diagonal is then universally closed and a
preimmersion, hence a closed immersion.

## Main results

* `AlgebraicGeometry.universallyClosed_of_unique_lift_of_denseRange`: the refined valuative
  criterion implies that `f` is universally closed.
* `AlgebraicGeometry.isSeparated_of_unique_lift_of_denseRange`: with quasi-separatedness, the
  same criterion implies that `f` is separated.

## Implementation notes

A solid diagram in the source is represented by a `AlgebraicGeometry.ValuativeCommSq f`,
together with its generic-point map to `U` and the equation saying that this map factors the top
side through `h`. The existence and uniqueness of the dotted arrow is
`Nonempty (Unique D.commSq.LiftStruct)`. The two conclusions of the source are stated
separately.

## References

* [Stacks Project, Tag 0894](https://stacks.math.columbia.edu/tag/0894)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

universe u

private theorem isLocalHom_codRestrict_of_range_le {R L : Type u} [CommRing R] [IsLocalRing R]
    [Field L] (r : R →+* L) (B : ValuationSubring L)
    (hB : LocalSubring.range r ≤ B.toLocalSubring) :
    IsLocalHom (r.codRestrict B.toSubring fun a => (LocalSubring.le_def.mp hB).1 ⟨a, rfl⟩) := by
  change IsLocalHom ((Subring.inclusion (LocalSubring.le_def.mp hB).1).comp r.rangeRestrict)
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ (LocalSubring.le_def.mp hB).2
    (IsLocalHom.of_surjective _ r.rangeRestrict_surjective)

private theorem valuationSubring_comap_eq_of_dominates
    {R K L : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    (B : ValuationSubring L) (e : K →+* L)
    (hAB : LocalSubring.range (e.comp (algebraMap R K)) ≤ B.toLocalSubring) :
    B.comap e = (ValuationRing.valuation R K).valuationSubring := by
  let A := (ValuationRing.valuation R K).valuationSubring
  let f := e.comp (algebraMap R K)
  have hsub := (LocalSubring.le_def.mp hAB).1
  have hA_mem (x : K) : x ∈ A ↔ ∃ a : R, algebraMap R K a = x :=
    ValuationRing.mem_integer_iff R K x
  refine ValuationSubring.ext _ _ fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · change e x ∈ B at hx
    by_contra hxA
    obtain ⟨a, ha⟩ := (hA_mem x⁻¹).1 ((A.mem_or_inv_mem x).resolve_left hxA)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxA A.zero_mem
    have ha_nonunit : ¬ IsUnit a := by
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hm : x⁻¹ * algebraMap R K b = 1 := by rw [← ha, ← map_mul, hb, map_one]
      exact hxA ((hA_mem x).2 ⟨b, inv_inj.mp (inv_eq_of_mul_eq_one_left hm)⟩)
    have : IsLocalHom (f.codRestrict B.toSubring fun a => hsub ⟨a, rfl⟩) :=
      isLocalHom_codRestrict_of_range_le f B hAB
    refine ha_nonunit ((isUnit_map_iff (f.codRestrict B.toSubring fun a => hsub ⟨a, rfl⟩) a).mp ?_)
    refine isUnit_iff_exists_inv.mpr ⟨⟨e x, hx⟩, ?_⟩
    apply Subtype.ext
    change e (algebraMap R K a) * e x = 1
    rw [← map_mul, ha, inv_mul_cancel₀ hx0, map_one]
  · obtain ⟨a, rfl⟩ := (hA_mem x).1 hx
    exact hsub ⟨a, rfl⟩

private theorem ringHom_factor_of_surjective_of_ker_eq
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (hf : Function.Surjective f) (g : A →+* C)
    (hker : RingHom.ker f = RingHom.ker g) : ∃ e : B →+* C, e.comp f = g := by
  let q : A ⧸ RingHom.ker f →+* C := Ideal.Quotient.lift (RingHom.ker f) g
    fun a ha => RingHom.mem_ker.1 (by rwa [← hker])
  let e₁ : A ⧸ RingHom.ker f ≃+* B := RingHom.quotientKerEquivOfSurjective hf
  refine ⟨q.comp e₁.symm.toRingHom, ?_⟩
  ext a
  change q (e₁.symm (f a)) = g a
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply hf a]
  simp [q]

private theorem specMap_comp_ringHom {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom g) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom f) =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

private theorem ringHom_comp_eq_of_specMap_comp_eq {R₁ R₂ Q : Type u} [CommRing R₁]
    [CommRing R₂] [CommRing Q] {F : CommRingCat.{u}} {Y : Scheme.{u}} (j : Spec F ⟶ Y)
    [IsOpenImmersion j] {α : F →+* R₁} {β : F →+* R₂} (r : R₁ →+* Q) (s : R₂ →+* Q)
    {a : Spec (.of R₁) ⟶ Y} {b : Spec (.of R₂) ⟶ Y}
    (ha : Spec.map (CommRingCat.ofHom α) ≫ j = a) (hb : Spec.map (CommRingCat.ofHom β) ≫ j = b)
    (h : Spec.map (CommRingCat.ofHom r) ≫ a = Spec.map (CommRingCat.ofHom s) ≫ b) :
    r.comp α = s.comp β := by
  suffices hh : CommRingCat.ofHom (r.comp α) = CommRingCat.ofHom (s.comp β) from
    congrArg CommRingCat.Hom.hom hh
  apply Spec.map_injective
  rw [← specMap_comp_ringHom, ← specMap_comp_ringHom]
  apply (cancel_mono j).1
  simpa only [Category.assoc, ha, hb] using h

private theorem range_subset_range_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R]
    {Y Z : Scheme.{u}} (a : Spec (.of R) ⟶ Y) (j : Z ⟶ Y) [IsOpenImmersion j]
    (ha : a (closedPoint R) ∈ Set.range j) : Set.range a ⊆ Set.range j := by
  rintro _ ⟨x, rfl⟩
  exact ((specializes_closedPoint x).map a.continuous).mem_open j.isOpenEmbedding.isOpen_range ha

private theorem exists_specMap_comp_eq {R : Type u} [CommRing R] {T : CommRingCat.{u}}
    {Y : Scheme.{u}} (a : Spec (.of R) ⟶ Y) (j : Spec T ⟶ Y) [IsOpenImmersion j]
    (ha : Set.range a ⊆ Set.range j) :
    ∃ τ : T →+* R, Spec.map (CommRingCat.ofHom τ) ≫ j = a := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j a ha)).hom, ?_⟩
  change Spec.map (Spec.preimage (IsOpenImmersion.lift j a ha)) ≫ j = a
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

private theorem specMap_residue_closedPoint (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec.map (CommRingCat.ofHom (residue A)) (closedPoint (ResidueField A)) = closedPoint A :=
  comap_closedPoint (residue A)

private theorem ker_eq_of_specMap_closedPoint_eq {P K L : Type u} [CommRing P] [Field K]
    [Field L] (φ : P →+* K) (ψ : P →+* L)
    (hφψ : Spec.map (CommRingCat.ofHom ψ) (closedPoint L) =
      Spec.map (CommRingCat.ofHom φ) (closedPoint K)) :
    RingHom.ker φ = RingHom.ker ψ := by
  change PrimeSpectrum.comap ψ (closedPoint L) = PrimeSpectrum.comap φ (closedPoint K) at hφψ
  have hp := congrArg PrimeSpectrum.asIdeal hφψ
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal] at hp
  change Ideal.comap ψ (maximalIdeal L) = Ideal.comap φ (maximalIdeal K) at hp
  rw [maximalIdeal_eq_bot, maximalIdeal_eq_bot] at hp
  exact hp.symm

private theorem exists_composite_valuation_subring
    {A K T : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [CommRing T]
    (B : ValuationSubring (ResidueField A)) (τ : T →+* A)
    (hτ : ∀ t, residue A (τ t) ∈ B) :
    ∃ (C : ValuationSubring K) (ι : C →+* A) (ρ : C →+* B) (t : T →+* C),
      (algebraMap A K).comp ι = C.subtype ∧
      B.subtype.comp ρ = (residue A).comp ι ∧ ι.comp t = τ := by
  let A₀ := (ValuationRing.valuation A K).valuationSubring
  let E : A ≃+* A₀ := ValuationRing.equivInteger A K
  have : IsLocalHom E.symm.toRingHom :=
    IsLocalHom.of_surjective _ E.symm.surjective
  let B₀ := B.comap (ResidueField.map E.symm.toRingHom)
  let C := residueValuationSubring' A₀ B₀
  have hCA : C ≤ A₀ := fun _ hx => (mem_residueValuationSubring.mp hx).choose
  let ι : C →+* A := E.symm.toRingHom.comp (ValuationSubring.inclusion C A₀ hCA)
  have hres (c : C) : residue A (ι c) ∈ B := by
    have hc := (mem_residueValuationSubring.mp c.property).choose_spec
    change ResidueField.map E.symm.toRingHom (residue A₀ ⟨(c : K), hCA c.property⟩) ∈ B at hc
    have hinc : (ValuationSubring.inclusion C A₀ hCA) c =
        (⟨(c : K), hCA c.property⟩ : A₀) :=
      Subtype.ext (Subring.coe_inclusion hCA c)
    simpa only [ι, RingHom.comp_apply, hinc, ResidueField.map_residue] using hc
  let ρ : C →+* B := ((residue A).comp ι).codRestrict B.toSubring hres
  have ht (a : T) : algebraMap A K (τ a) ∈ C := by
    apply mem_residueValuationSubring.mpr
    refine ⟨(E (τ a)).property, ?_⟩
    change ResidueField.map E.symm.toRingHom (residue A₀ (E (τ a))) ∈ B
    simpa only [ResidueField.map_residue, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using hτ a
  let t : T →+* C := ((algebraMap A K).comp τ).codRestrict C.toSubring ht
  refine ⟨C, ι, ρ, t, ?_, rfl, ?_⟩
  · ext c
    change algebraMap A K (E.symm _) = (c : K)
    exact congrArg (fun a : A₀ => (a : K)) (E.apply_symm_apply _)
  · ext a
    exact E.symm_apply_apply (τ a)

private theorem hom_ext_of_comp_specMap_eq
    {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    (r : R →+* T) [IsLocalHom r] (hr : Function.Injective r)
    {X : Scheme.{u}} (a b : Spec (.of R) ⟶ X)
    (hab : Spec.map (CommRingCat.ofHom r) ≫ a = Spec.map (CommRingCat.ofHom r) ≫ b) :
    a = b := by
  have hc : a (closedPoint R) = b (closedPoint R) := by
    have hh := congrArg (fun k : Spec (.of T) ⟶ X => k (closedPoint T)) hab
    change a (PrimeSpectrum.comap r (closedPoint T)) =
      b (PrimeSpectrum.comap r (closedPoint T)) at hh
    simpa only [comap_closedPoint] using hh
  obtain ⟨F, j, hj, p, hp⟩ := X.exists_Spec_apply_eq (a (closedPoint R))
  obtain ⟨α, ha⟩ := exists_specMap_comp_eq a j
    (range_subset_range_of_closedPoint_mem a j ⟨p, hp⟩)
  obtain ⟨β, hb⟩ := exists_specMap_comp_eq b j
    (range_subset_range_of_closedPoint_mem b j ⟨p, hp.trans hc⟩)
  obtain rfl : α = β := RingHom.ext fun x =>
    hr (RingHom.congr_fun (ringHom_comp_eq_of_specMap_comp_eq j r r ha hb hab) x)
  exact ha.symm.trans hb

private theorem exists_ringHom_factor_of_range
    {R K F : Type u} [CommRing R] [CommRing K] [CommRing F]
    (i : R →+* K) (hi : Function.Injective i) (a : F →+* K)
    (ha : ∀ x, ∃ y, i y = a x) : ∃ b : F →+* R, i.comp b = a := by
  let E : R ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  refine ⟨E.symm.toRingHom.comp (a.codRestrict i.range ha), ?_⟩
  ext x
  exact congrArg Subtype.val (E.apply_symm_apply _)

private theorem exists_lift_of_valuation_extension
    {R K L : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    (B : ValuationSubring L) (e : K →+* L) (r : R →+* B) [IsLocalHom r]
    (hr : B.subtype.comp r = e.comp (algebraMap R K))
    (hB : B.comap e = (ValuationRing.valuation R K).valuationSubring)
    {X S : Scheme.{u}} (f : X ⟶ S) (a : Spec (.of K) ⟶ X)
    (b : Spec (.of R) ⟶ S) (l : Spec (.of B) ⟶ X)
    (hl : Spec.map (CommRingCat.ofHom B.subtype) ≫ l =
      Spec.map (CommRingCat.ofHom e) ≫ a)
    (hlf : l ≫ f = Spec.map (CommRingCat.ofHom r) ≫ b) :
    ∃ l₀ : Spec (.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₀ = a ∧ l₀ ≫ f = b := by
  obtain ⟨F, j, hj, p, hp⟩ := X.exists_Spec_apply_eq (l (closedPoint B))
  have hlrange := range_subset_range_of_closedPoint_mem l j ⟨p, hp⟩
  have harange : Set.range a ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : x = (Spec.map (CommRingCat.ofHom e)) (closedPoint L) := Subsingleton.elim _ _
    have hx' : a ((Spec.map (CommRingCat.ofHom e)) (closedPoint L)) =
        l ((Spec.map (CommRingCat.ofHom B.subtype)) (closedPoint L)) :=
      (congrArg (fun k : Spec (.of L) ⟶ X => k (closedPoint L)) hl).symm
    rw [hx, hx']
    exact hlrange ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ := exists_specMap_comp_eq l j hlrange
  obtain ⟨α, hα'⟩ := exists_specMap_comp_eq a j harange
  have heδ := ringHom_comp_eq_of_specMap_comp_eq j B.subtype e hδ hα' hl
  have hα (x : F) : ∃ y : R, algebraMap R K y = α x := by
    apply (ValuationRing.mem_integer_iff R K (α x)).mp
    change α x ∈ (ValuationRing.valuation R K).valuationSubring
    rw [← hB]
    change e (α x) ∈ B
    rw [← RingHom.comp_apply, ← heδ]
    exact (δ x).property
  obtain ⟨γ, hγ⟩ := exists_ringHom_factor_of_range (algebraMap R K)
    (IsFractionRing.injective R K) α hα
  have hrγ : r.comp γ = δ := by
    ext x
    change B.subtype (r (γ x)) = B.subtype (δ x)
    exact (RingHom.congr_fun hr (γ x)).trans
      ((congrArg e (RingHom.congr_fun hγ x)).trans (RingHom.congr_fun heδ x).symm)
  refine ⟨Spec.map (CommRingCat.ofHom γ) ≫ j, ?_, hom_ext_of_comp_specMap_eq r ?_ _ b ?_⟩
  · rw [← Category.assoc, specMap_comp_ringHom, hγ, hα']
  · intro x y hxy
    apply IsFractionRing.injective R K
    apply e.injective
    simpa only [← RingHom.comp_apply, hr] using congrArg B.subtype hxy
  · rw [← Category.assoc, ← Category.assoc, specMap_comp_ringHom, hrγ, hδ, hlf]

private theorem exists_lift_of_valuationSubring_of_comp_eq
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    (hvaluative : ∀ (D : ValuativeCommSq f) (g : Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct))
    {A K : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] (C : ValuationSubring K) (ι : C →+* A)
    (hι : (algebraMap A K).comp ι = C.subtype)
    (k : Spec (.of K) ⟶ U) (w : Spec (.of A) ⟶ X) (q : Spec (.of C) ⟶ S)
    (hkw : k ≫ h = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ w)
    (hιq : Spec.map (CommRingCat.ofHom ι) ≫ q = w ≫ f) :
    ∃ l : Spec (.of C) ⟶ X, l ≫ f = q ∧ Spec.map (CommRingCat.ofHom ι) ≫ l = w := by
  let DC : ValuativeCommSq f := {
    R := C
    K := K
    i₁ := k ≫ h
    i₂ := q
    commSq := ⟨by
      rw [hkw, Category.assoc, ← hιq, ← Category.assoc, specMap_comp_ringHom, hι]
      rfl⟩ }
  let lc : DC.commSq.LiftStruct := (hvaluative DC k rfl).some.default
  have hlc : Spec.map (CommRingCat.ofHom C.subtype) ≫ lc.l = k ≫ h := lc.fac_left
  have hlcf : lc.l ≫ f = q := lc.fac_right
  let DA : ValuativeCommSq f := {
    R := A
    K := K
    i₁ := k ≫ h
    i₂ := w ≫ f
    commSq := ⟨by rw [hkw, Category.assoc]⟩ }
  let la : DA.commSq.LiftStruct := ⟨w, hkw.symm, rfl⟩
  let lb : DA.commSq.LiftStruct := ⟨Spec.map (CommRingCat.ofHom ι) ≫ lc.l, by
    rw [← Category.assoc, specMap_comp_ringHom, hι, hlc], by rw [Category.assoc, hlcf, hιq]⟩
  let : Unique DA.commSq.LiftStruct := (hvaluative DA k rfl).some
  exact ⟨lc.l, hlcf, congrArg CommSq.LiftStruct.l (Subsingleton.elim lb la)⟩

private theorem hasLift_of_dominating_valuationSubring
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    (hvaluative : ∀ (D : ValuativeCommSq f) (g : Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct))
    (D : ValuativeCommSq f) {A K : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {R₀ : CommRingCat.{u}}
    (e : D.K →+* ResidueField A) (B₀ : ValuationSubring (ResidueField A))
    (hB₀ : LocalSubring.range (e.comp (algebraMap D.R D.K)) ≤ B₀.toLocalSubring)
    (τ : R₀ →+* A) (β : R₀ →+* D.R)
    (hσ : (residue A).comp τ = e.comp ((algebraMap D.R D.K).comp β))
    (k : Spec (.of K) ⟶ U) (w : Spec (.of A) ⟶ X) (s : Spec R₀ ⟶ S)
    (hkw : k ≫ h = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ w)
    (hwf : w ≫ f = Spec.map (CommRingCat.ofHom τ) ≫ s)
    (hwe : Spec.map (CommRingCat.ofHom (residue A)) ≫ w =
      Spec.map (CommRingCat.ofHom e) ≫ D.i₁)
    (hs : Spec.map (CommRingCat.ofHom β) ≫ s = D.i₂) :
    D.commSq.HasLift := by
  have hσmem (a : R₀) : residue A (τ a) ∈ B₀ := by
    rw [← RingHom.comp_apply, hσ]
    exact (LocalSubring.le_def.mp hB₀).1 ⟨β a, rfl⟩
  obtain ⟨C, ι, ρ, t, hι, hρ, ht⟩ := exists_composite_valuation_subring (K := K) B₀ τ hσmem
  let q : Spec (.of C) ⟶ S := Spec.map (CommRingCat.ofHom t) ≫ s
  have hιq : Spec.map (CommRingCat.ofHom ι) ≫ q = w ≫ f := by
    dsimp only [q]
    rw [← Category.assoc, specMap_comp_ringHom, ht, hwf]
  obtain ⟨l, hlf, hcompare⟩ := exists_lift_of_valuationSubring_of_comp_eq h f hvaluative C ι hι
    k w q hkw hιq
  let rB : D.R →+* B₀ := (e.comp (algebraMap D.R D.K)).codRestrict B₀.toSubring
    fun a => (LocalSubring.le_def.mp hB₀).1 ⟨a, rfl⟩
  have : IsLocalHom rB := isLocalHom_codRestrict_of_range_le _ B₀ hB₀
  have hρt : ρ.comp t = rB.comp β := by
    ext a
    change B₀.subtype (ρ (t a)) = e (algebraMap D.R D.K (β a))
    calc
      _ = residue A (ι (t a)) := congrArg (fun f : C →+* ResidueField A => f (t a)) hρ
      _ = residue A (τ a) := congrArg (fun f : R₀ →+* A => residue A (f a)) ht
      _ = e (algebraMap D.R D.K (β a)) := congrArg (fun f : R₀ →+* ResidueField A => f a) hσ
  have htopB : Spec.map (CommRingCat.ofHom B₀.subtype) ≫
      Spec.map (CommRingCat.ofHom ρ) ≫ l = Spec.map (CommRingCat.ofHom e) ≫ D.i₁ := by
    rw [← Category.assoc, specMap_comp_ringHom, hρ, ← specMap_comp_ringHom, Category.assoc,
      hcompare, hwe]
  have hlBf : (Spec.map (CommRingCat.ofHom ρ) ≫ l) ≫ f =
      Spec.map (CommRingCat.ofHom rB) ≫ D.i₂ := by
    rw [Category.assoc, hlf]
    dsimp only [q]
    rw [← Category.assoc, specMap_comp_ringHom, hρt, ← specMap_comp_ringHom]
    simp only [Category.assoc, hs]
  obtain ⟨l₀, hl₀, hl₀f⟩ := exists_lift_of_valuation_extension B₀ e rB rfl
    (valuationSubring_comap_eq_of_dominates B₀ e hB₀) f D.i₁ D.i₂ _ htopB hlBf
  exact ⟨⟨⟨l₀, hl₀, hl₀f⟩⟩⟩

private theorem exists_flat_spec_of_field_point {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ X) :
    ∃ (P : Type u) (_ : CommRing P) (φ : P →+* K) (g : Spec (.of P) ⟶ X),
      Function.Surjective φ ∧ Flat g ∧ Spec.map (CommRingCat.ofHom φ) ≫ g = x := by
  obtain ⟨B, j, hj, p, hp⟩ := X.exists_Spec_apply_eq (x (closedPoint K))
  have hrange := range_subset_range_of_closedPoint_mem x j ⟨p, hp⟩
  obtain ⟨α, hα⟩ := exists_specMap_comp_eq x j hrange
  let : Algebra B K := α.toAlgebra
  let φ : MvPolynomial K B →ₐ[B] K := MvPolynomial.aeval fun k : K => k
  have hφ : Function.Surjective φ := fun k => ⟨MvPolynomial.X k, by simp [φ]⟩
  refine ⟨MvPolynomial K B, inferInstance, φ.toRingHom,
    Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial K B))) ≫ j, hφ, ?_, ?_⟩
  · have : Flat (Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial K B)))) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
    exact Flat.comp _ j
  · have hring : φ.toRingHom.comp (algebraMap B (MvPolynomial K B)) = α := by
      ext b
      change φ (algebraMap B (MvPolynomial K B) b) = α b
      rw [φ.commutes]
      exact congrArg (fun r : B →+* K => r b) (RingHom.algebraMap_toAlgebra α)
    rw [← Category.assoc, specMap_comp_ringHom, hring, hα]

private theorem exists_valuationRing_diagram_of_field_point
    {U X : Scheme.{u}} (h : U ⟶ X) [QuasiCompact h] [IsSchemeTheoreticallyDominant h]
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (L : Type u) (_ : Field L) (_ : Algebra A L) (_ : IsFractionRing A L)
      (g : Spec (.of L) ⟶ U) (w : Spec (.of A) ⟶ X) (e : K →+* ResidueField A),
      g ≫ h = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ w ∧
      Spec.map (CommRingCat.ofHom (residue A)) ≫ w = Spec.map (CommRingCat.ofHom e) ≫ x := by
  obtain ⟨P, hP, φ, gP, hφ, hflat, hfac⟩ := exists_flat_spec_of_field_point x
  let v := CategoryTheory.Limits.pullback.snd h gP
  have : IsSchemeTheoreticallyDominant v := inferInstance
  have : QuasiCompact v := inferInstance
  have : IsIso v.imageι := by
    apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    simp [Scheme.Hom.imageι, Scheme.Hom.image, v.ker_eq_bot]
  obtain ⟨A, hA, hAd, hAv, L, hL, hAL, hfrac, g, i, hcomm, hclosed⟩ :=
    exists_valuationRing_of_image_point v
      ((asIso v.imageι).inv (Spec.map (CommRingCat.ofHom φ) (closedPoint K)))
  let ψ : P →+* A := (Spec.preimage (i ≫ v.imageι)).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = i ≫ v.imageι := by
    change Spec.map (Spec.preimage (i ≫ v.imageι)) = _
    exact Spec.map_preimage _
  have hker : RingHom.ker φ = RingHom.ker ((residue A).comp ψ) := by
    apply ker_eq_of_specMap_closedPoint_eq
    let xL : Spec (.of (ResidueField A)) := closedPoint (ResidueField A)
    let xA : Spec (.of A) := closedPoint A
    have hres : Spec.map (CommRingCat.ofHom (residue A)) xL = xA := specMap_residue_closedPoint A
    change Spec.map (CommRingCat.ofHom ((residue A).comp ψ)) xL = _
    rw [← specMap_comp_ringHom, hψ, Scheme.Hom.comp_apply, hres, Scheme.Hom.comp_apply,
      hclosed]
    change (asIso v.imageι).hom ((asIso v.imageι).inv
      (Spec.map (CommRingCat.ofHom φ) (closedPoint K))) = _
    exact congrArg (fun m : Spec (.of P) ⟶ Spec (.of P) =>
      m (Spec.map (CommRingCat.ofHom φ) (closedPoint K))) (asIso v.imageι).inv_hom_id
  obtain ⟨e, he⟩ := ringHom_factor_of_surjective_of_ker_eq φ hφ _ hker
  have hv : g ≫ v = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ i ≫ v.imageι := by
    simpa only [Category.assoc, Scheme.Hom.toImage_imageι] using congrArg (· ≫ v.imageι) hcomm
  refine ⟨A, hA, hAd, hAv, L, hL, hAL, hfrac, g ≫ CategoryTheory.Limits.pullback.fst h gP,
    i ≫ v.imageι ≫ gP, e, ?_, ?_⟩
  · rw [Category.assoc, CategoryTheory.Limits.pullback.condition, ← Category.assoc]
    change (g ≫ v) ≫ gP = _
    rw [hv]
    simp only [Category.assoc]
  · rw [← Category.assoc i, ← hψ, ← Category.assoc, specMap_comp_ringHom, ← he,
      ← specMap_comp_ringHom, Category.assoc, hfac]

private theorem hasLift_of_reduction_lift
    {U X S U₀ X₀ S₀ : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    (hvaluative : ∀ (D : ValuativeCommSq f) (g : Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct))
    (D : ValuativeCommSq f) {jU : U₀ ⟶ U} {jX : X₀ ⟶ X} {jS : S₀ ⟶ S}
    (h₀ : U₀ ⟶ X₀) (f₀ : X₀ ⟶ S₀) [QuasiCompact h₀] [IsSchemeTheoreticallyDominant h₀]
    (hh₀ : h₀ ≫ jX = jU ≫ h) (hf₀ : f₀ ≫ jS = jX ≫ f)
    (i₁ : Spec (.of D.K) ⟶ X₀) (i₂ : Spec (.of D.R) ⟶ S₀)
    (hi₁ : i₁ ≫ jX = D.i₁) (hi₂ : i₂ ≫ jS = D.i₂)
    (hw : i₁ ≫ f₀ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ i₂) :
    D.commSq.HasLift := by
  obtain ⟨A, hA, hAd, hAv, L, hL, hAL, hfrac, g, w, e, hgw, hwe⟩ :=
    exists_valuationRing_diagram_of_field_point h₀ i₁
  obtain ⟨R₀, jR, hjR, p, hp⟩ := S₀.exists_Spec_apply_eq (i₂ (closedPoint D.R))
  have hi₂R := range_subset_range_of_closedPoint_mem i₂ jR ⟨p, hp⟩
  have hwR : Set.range (w ≫ f₀) ⊆ Set.range jR := by
    refine range_subset_range_of_closedPoint_mem _ jR ?_
    have hh : Spec.map (CommRingCat.ofHom (residue A)) ≫ w ≫ f₀ =
        Spec.map (CommRingCat.ofHom e) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ i₂ := by
      rw [← Category.assoc, hwe, Category.assoc, hw]
    let xL : Spec (.of (ResidueField A)) := closedPoint (ResidueField A)
    let xA : Spec (.of A) := closedPoint A
    have hres : Spec.map (CommRingCat.ofHom (residue A)) xL = xA := specMap_residue_closedPoint A
    have hh' := congrArg (fun m => m xL) hh
    simp only [Scheme.Hom.comp_apply, hres] at hh'
    change (w ≫ f₀) xA ∈ _
    rw [Scheme.Hom.comp_apply, hh']
    exact hi₂R ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_specMap_comp_eq (w ≫ f₀) jR hwR
  obtain ⟨β, hβ⟩ := exists_specMap_comp_eq i₂ jR hi₂R
  have hσSpec : Spec.map (CommRingCat.ofHom ((residue A).comp τ)) =
      Spec.map (CommRingCat.ofHom (e.comp ((algebraMap D.R D.K).comp β))) := by
    apply (cancel_mono jR).1
    rw [← specMap_comp_ringHom τ, Category.assoc, hτ, ← Category.assoc, hwe, Category.assoc, hw,
      ← specMap_comp_ringHom _ e, ← specMap_comp_ringHom β]
    simp only [Category.assoc, hβ]
  have hσ : (residue A).comp τ = e.comp ((algebraMap D.R D.K).comp β) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective hσSpec)
  obtain ⟨B₀, hB₀⟩ :=
    LocalSubring.exists_le_valuationSubring (LocalSubring.range (e.comp (algebraMap D.R D.K)))
  refine hasLift_of_dominating_valuationSubring h f hvaluative D e B₀ hB₀ τ β hσ (g ≫ jU)
    (w ≫ jX) (jR ≫ jS) ?_ ?_ ?_ ?_
  · rw [Category.assoc, ← hh₀, ← Category.assoc, hgw, Category.assoc]
  · rw [Category.assoc, ← hf₀, ← Category.assoc, ← hτ, Category.assoc]
  · rw [← Category.assoc, hwe, Category.assoc, hi₁]
  · rw [← Category.assoc, hβ, hi₂]

private theorem refinedValuativeExistence
    {U X S : AlgebraicGeometry.Scheme.{u}}
    (h : U ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : AlgebraicGeometry.ValuativeCommSq f)
      (g : AlgebraicGeometry.Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct))
    (D : AlgebraicGeometry.ValuativeCommSq f) : D.commSq.HasLift := by
  let U₀ := U.nilradical.subscheme
  let X₀ := X.nilradical.subscheme
  let jU : U₀ ⟶ U := U.nilradical.subschemeι
  let jX : X₀ ⟶ X := X.nilradical.subschemeι
  have hred (Y : Scheme.{u}) : IsReduced Y.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := Y) ⊤
  have : IsReduced U₀ := hred U
  have : IsReduced X₀ := hred X
  obtain ⟨h₀, hh₀⟩ := Scheme.existsUnique_lift_nilradical_subschemeι (jU ≫ h)
  obtain ⟨f₀, hf₀⟩ := Scheme.existsUnique_lift_nilradical_subschemeι (jX ≫ f)
  obtain ⟨i₁₀, hi₁₀⟩ := Scheme.existsUnique_lift_nilradical_subschemeι D.i₁
  obtain ⟨i₂₀, hi₂₀⟩ := Scheme.existsUnique_lift_nilradical_subschemeι D.i₂
  have hsurj (Y : Scheme.{u}) : Function.Surjective Y.nilradical.subschemeι := by
    intro x
    have hx : x ∈ (Y.nilradical.support : Set Y) := by simp
    rwa [← Scheme.IdealSheafData.range_subschemeι] at hx
  let eX : X₀ ≃ₜ X := IsHomeomorph.homeomorph (jX : X₀ → X)
    ((isHomeomorph_iff_isEmbedding_surjective).2 ⟨jX.isClosedEmbedding.isEmbedding, hsurj X⟩)
  have hdense₀ : DenseRange h₀ := by
    have hdense' : DenseRange (eX.symm ∘ h ∘ jU) :=
      eX.symm.surjective.denseRange.comp
        (hdense.comp (hsurj U).denseRange h.continuous) eX.symm.continuous
    convert hdense' using 1
    funext y
    apply eX.injective
    change eX (h₀ y) = eX (eX.symm (h (jU y)))
    rw [eX.apply_symm_apply]
    change jX (h₀ y) = h (jU y)
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : U₀ ⟶ X => q y) hh₀.1
  have : QuasiCompact (h₀ ≫ jX) := by
    rw [hh₀.1]
    infer_instance
  have : QuasiCompact h₀ := QuasiCompact.of_comp h₀ jX
  have : IsDominant h₀ := ⟨hdense₀⟩
  have : IsSchemeTheoreticallyDominant h₀ := .of_isDominant h₀
  refine hasLift_of_reduction_lift h f hvaluative D h₀ f₀ hh₀.1 hf₀.1 i₁₀ i₂₀ hi₁₀.1 hi₂₀.1 ?_
  apply (cancel_mono S.nilradical.subschemeι).1
  rw [Category.assoc, hf₀.1, ← Category.assoc, hi₁₀.1, D.commSq.w, ← hi₂₀.1, Category.assoc]

-- Preserve the `CategoryStruct.toQuiver` instance used by the accepted statement.
/-- **Stacks 0894, universally closed part.**
Let `f : X ⟶ S` and `h : U ⟶ X` be quasi-compact morphisms of schemes and suppose that
`h(U)` is dense in `X`. If every valuative square for `f` whose generic-point map factors through
`h` has a unique lift, then `f` is universally closed. -/
@[stacks 0894 "universally closed conclusion"]
public lemma universallyClosed_of_unique_lift_of_denseRange
    {U X S : AlgebraicGeometry.Scheme.{u}}
    (h : U ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : AlgebraicGeometry.ValuativeCommSq f)
      (g : AlgebraicGeometry.Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct)) :
    AlgebraicGeometry.UniversallyClosed f :=
  AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion f
    (refinedValuativeExistence h f hdense hvaluative)

/-- Under the hypotheses of the refined valuative criterion, the diagonal of a quasi-separated
morphism `f` is universally closed. -/
public lemma universallyClosed_diagonal_of_unique_lift_of_denseRange
    {U X S : AlgebraicGeometry.Scheme.{u}}
    (h : U ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiCompact h] [AlgebraicGeometry.QuasiSeparated f]
    (hdense : DenseRange h)
    (hvaluative : ∀ (D : AlgebraicGeometry.ValuativeCommSq f)
      (g : AlgebraicGeometry.Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct)) :
    AlgebraicGeometry.UniversallyClosed (CategoryTheory.Limits.pullback.diagonal f) := by
  let d : X ⟶ CategoryTheory.Limits.pullback f f :=
    CategoryTheory.Limits.pullback.diagonal f
  have : AlgebraicGeometry.QuasiCompact d := inferInstance
  apply universallyClosed_of_unique_lift_of_denseRange h d hdense
  intro D g hg
  let a : AlgebraicGeometry.Spec (.of D.R) ⟶ X :=
    D.i₂ ≫ CategoryTheory.Limits.pullback.fst f f
  let b : AlgebraicGeometry.Spec (.of D.R) ⟶ X :=
    D.i₂ ≫ CategoryTheory.Limits.pullback.snd f f
  have hgen : AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ a = D.i₁ := by
    simpa [a, d] using (D.commSq.w =≫ CategoryTheory.Limits.pullback.fst f f).symm
  have hgenb : AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ b = D.i₁ := by
    simpa [b, d] using (D.commSq.w =≫ CategoryTheory.Limits.pullback.snd f f).symm
  let Df : AlgebraicGeometry.ValuativeCommSq f := {
    R := D.R
    K := D.K
    i₁ := D.i₁
    i₂ := a ≫ f
    commSq := ⟨by
      rw [← hgen]
      simp⟩ }
  have hfg : a ≫ f = b ≫ f := D.i₂ ≫= CategoryTheory.Limits.pullback.condition (f := f) (g := f)
  let : Unique Df.commSq.LiftStruct := (hvaluative Df g hg).some
  let la : Df.commSq.LiftStruct := ⟨a, hgen, rfl⟩
  let lb : Df.commSq.LiftStruct := ⟨b, hgenb, hfg.symm⟩
  have hab : a = b := congrArg CategoryTheory.CommSq.LiftStruct.l (Subsingleton.elim la lb)
  let cand : D.commSq.LiftStruct := ⟨a, hgen, by
    apply CategoryTheory.Limits.pullback.hom_ext
    · simp [a, d]
    · simp [a, b, d, hab]⟩
  have : Mono d := inferInstance
  refine ⟨{ default := cand, uniq := fun z => ?_ }⟩
  apply CategoryTheory.CommSq.LiftStruct.ext
  apply (cancel_mono d).1
  rw [z.fac_right, cand.fac_right]

/-- **Stacks 0894, separated part.**
Under the hypotheses of the refined valuative criterion, a quasi-separated morphism `f` is
separated. -/
@[stacks 0894 "separated conclusion"]
public lemma isSeparated_of_unique_lift_of_denseRange
    {U X S : AlgebraicGeometry.Scheme.{u}}
    (h : U ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiCompact h] [AlgebraicGeometry.QuasiSeparated f]
    (hdense : DenseRange h)
    (hvaluative : ∀ (D : AlgebraicGeometry.ValuativeCommSq f)
      (g : AlgebraicGeometry.Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct)) :
    AlgebraicGeometry.IsSeparated f := by
  have := universallyClosed_diagonal_of_unique_lift_of_denseRange h f hdense hvaluative
  exact ⟨AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _
    (CategoryTheory.Limits.pullback.diagonal f).isClosedMap.isClosed_range⟩

end AlgebraicGeometry

end
