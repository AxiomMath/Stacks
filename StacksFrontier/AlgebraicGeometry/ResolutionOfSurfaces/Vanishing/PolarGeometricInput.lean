module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PolarFunctions
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationIsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence

/-!
# The codimension-one points of the closed fibre of a normal modification

Let `(A, 𝔪)` be a two-dimensional Noetherian normal local domain and `f : X ⟶ Spec A` a
modification. This file supplies the geometric inputs of
`AlgebraicGeometry.forall_mem_stalkSubring_of_polar` for such an `f`:

* the codimension-one points of `X` lying over the closed point are finitely many: each of them
  is the generic point of an irreducible component of the closed fibre;
* none of them is a closed point of `X`: a closed one would be an isolated point of the closed
  fibre, and Zariski's main theorem would make `f` an isomorphism, which puts a point of
  codimension two over the closed point;
* through the closure of each of them passes a codimension-one point `Q` not over the closed
  point: the local ring of `X` at a point of that closure other than the point itself has
  dimension at least two, hence infinitely many height-one primes;
* there is an `φ ∈ 𝔪` with nonzero image in the function field vanishing at each such `Q`: the
  product of nonzero elements of the primes of `A` under the points `Q`.

## Main results

* `AlgebraicGeometry.finite_setOf_coheight_eq_one_closedFibre`: the finiteness.
* `AlgebraicGeometry.exists_polar_auxiliary`: the function `φ` with its properties.
* `AlgebraicGeometry.forall_mem_stalkSubring_of_polar_of_isModification`: the polar lemma for a
  normal modification of a two-dimensional Noetherian normal local domain.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AX9](https://stacks.math.columbia.edu/tag/0AX9)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
-/

@[expose] public noncomputable section

open CategoryTheory Order IsLocalRing TopologicalSpace

universe u

/-- **A Noetherian local domain of dimension at least two has height-one primes outside any finite
set.** Prime avoidance gives an element of the maximal ideal outside the given primes other than
the maximal ideal and outside `(0)`; a minimal prime over it has height one by Krull's principal
ideal theorem. -/
theorem exists_height_eq_one_notMem_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R] (h2 : 2 ≤ (maximalIdeal R).height)
    (S : Set (PrimeSpectrum R)) (hS : S.Finite) :
    ∃ P : PrimeSpectrum R, P.asIdeal.height = 1 ∧ P ∉ S := by
  classical
  let bot : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let s : Finset (PrimeSpectrum R) := insert bot (hS.toFinset.filter (·.asIdeal ≠ maximalIdeal R))
  have hnot : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ P ∈ s, (P.asIdeal : Set R)) := by
    intro hsub
    obtain ⟨P, hPs, hle⟩ := (Ideal.subset_union_prime (s := s) (f := fun P => P.asIdeal) bot bot
      (fun P _ _ _ => P.isPrime)).mp hsub
    have heq : P.asIdeal = maximalIdeal R := le_antisymm (le_maximalIdeal P.isPrime.ne_top) hle
    rcases Finset.mem_insert.mp hPs with rfl | hP
    · have : (maximalIdeal R).height = 0 := by
        rw [← heq]
        exact Ideal.height_bot
      rw [this] at h2
      exact absurd h2 (by norm_num)
    · exact (Finset.mem_filter.mp hP).2 heq
  obtain ⟨t, htm, htS⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_iUnion, not_exists] at htS
  have ht0 : t ≠ 0 := fun h0 => htS bot (Finset.mem_insert_self _ _) (by simp [bot, h0])
  obtain ⟨P0, hP0min, -⟩ := Ideal.exists_minimalPrimes_le
    (I := Ideal.span {t}) (J := maximalIdeal R)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr htm))
  have hP0prime : P0.IsPrime := hP0min.1.1
  have htP0 : t ∈ P0 := hP0min.1.2 (Ideal.mem_span_singleton_self t)
  have hle1 : P0.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P0 hP0min
  have hne0 : P0.height ≠ 0 := by
    intro h0
    rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot] at h0
    rw [Set.mem_singleton_iff.mp h0, Ideal.mem_bot] at htP0
    exact ht0 htP0
  refine ⟨⟨P0, hP0prime⟩, le_antisymm hle1 (Order.one_le_iff_ne_zero.mpr hne0), fun hmem => ?_⟩
  by_cases hm : P0 = maximalIdeal R
  · rw [hm] at hle1
    exact absurd (h2.trans hle1) (by norm_num)
  · exact htS ⟨P0, hP0prime⟩ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨hS.mem_toFinset.mpr hmem, hm⟩)) htP0

namespace AlgebraicGeometry

/-- A proper generization of a point is strictly smaller in the specialization order. -/
private lemma lt_of_specializes_of_ne {X : Scheme.{u}} {x y : X} (h : x ⤳ y) (hne : x ≠ y) :
    y < x :=
  lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h)
    fun h' => hne (h.antisymm (Scheme.le_iff_specializes.mp h')).eq

/-- The source of a modification of the spectrum of a Noetherian ring is a Noetherian scheme. -/
private lemma isNoetherian_source {B : Type u} [CommRing B] [IsNoetherianRing B]
    [IsDomain B] [IsIntegrallyClosed B] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    (hp : IsModification p) : IsNoetherian Y := by
  have : IsProper p := hp.isProper
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Y := (quasiCompact_iff_compactSpace p).mp inferInstance
  exact {}

/-- Over the punctured spectrum, a modification restricts to an isomorphism. -/
private lemma exists_isIso_restrict_punctured {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    ∃ V : (Spec (.of A)).Opens, (∀ x, x ∈ V ↔ x ≠ closedPoint A) ∧ IsIso (f ∣_ V) :=
  ⟨⟨{closedPoint A}ᶜ, (isClosed_singleton_closedPoint A).isOpen_compl⟩, fun _ => Iff.rfl,
    isIso_morphismRestrict_of_isModification (.of A) hdim.le f hf _ (fun h => h rfl)⟩

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
  (hdim : ringKrullDim A = 2) {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of A))
  (hf : IsModification f)

include hdim hf

omit [IsNoetherianRing A] in
/-- The generic point of the source of the modification does not lie over the closed point. -/
lemma apply_genericPoint_ne_closedPoint : f (genericPoint X) ≠ closedPoint A := by
  intro h
  rw [IsBirational.genericPoint_eq f hf.isBirational, genericPoint_eq_bot_of_affine] at h
  have hm : maximalIdeal A = ⊥ := (congrArg PrimeSpectrum.asIdeal h).symm
  have hh := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [hm, Ideal.height_bot, hdim] at hh
  exact absurd hh (by decide)

omit [IsNoetherianRing A] in
/-- A point over the closed point which is a generization of a codimension-one point over the
closed point is that point. -/
lemma eq_of_specializes_of_coheight_eq_one {y z : X} (hy1 : coheight y = 1)
    (hz : f z = closedPoint A) (hzy : z ⤳ y) : z = y := by
  by_contra hne
  have hzgen : z ≠ genericPoint X := by
    rintro rfl
    exact apply_genericPoint_ne_closedPoint hdim f hf hz
  have h1 := coheight_add_one_le (lt_of_specializes_of_ne
    ((genericPoint_spec X).specializes (Set.mem_univ z)) hzgen.symm)
  have h2 := coheight_add_one_le (lt_of_specializes_of_ne hzy hne)
  rw [hy1] at h2
  have h4 : (1 : ℕ∞) ≤ coheight z := le_trans le_add_self h1
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add h4 (le_refl 1)) h2
  exact absurd h3 (by decide)

omit [IsNoetherianRing A] in
/-- An irreducible subset of the closed fibre containing a codimension-one point of the closed
fibre lies in the closure of that point. -/
lemma subset_closure_of_isIrreducible {y : X} (hy1 : coheight y = 1)
    {Z : Set X} (hZ : IsIrreducible Z) (hZF : Z ⊆ f ⁻¹' {closedPoint A}) (hyZ : y ∈ Z) :
    Z ⊆ closure {y} := by
  obtain ⟨z, hz⟩ := QuasiSober.sober hZ.closure isClosed_closure
  have hFc : IsClosed (f ⁻¹' {closedPoint A}) :=
    (isClosed_singleton_closedPoint A).preimage f.continuous
  have hzF : z ∈ f ⁻¹' {closedPoint A} := closure_minimal hZF hFc hz.mem
  have hzy : z ⤳ y := hz.specializes (subset_closure hyZ)
  obtain rfl := eq_of_specializes_of_coheight_eq_one hdim f hf hy1 hzF hzy
  exact fun w hw => specializes_iff_mem_closure.mp (hz.specializes (subset_closure hw))

/-- **The codimension-one points of the closed fibre are finitely many.** -/
theorem finite_setOf_coheight_eq_one_closedFibre :
    {y : X | coheight y = 1 ∧ f y = closedPoint A}.Finite := by
  have := isNoetherian_source f hf
  set F : Set X := f ⁻¹' {closedPoint A}
  let S : Set F := {p | coheight (p : X) = 1}
  have hcomp : ∀ p ∈ S, closure ({p} : Set F) ∈ irreducibleComponents F := by
    intro p hp
    refine ⟨isIrreducible_singleton.closure, fun Z hZ hpZ => ?_⟩
    have hsub := subset_closure_of_isIrreducible hdim f hf hp
      (hZ.image Subtype.val continuous_subtype_val.continuousOn)
      (Subtype.coe_image_subset _ _) ⟨p, hpZ (subset_closure rfl), rfl⟩
    intro q hq
    have hq' : (q : X) ∈ closure {(p : X)} := hsub ⟨q, hq, rfl⟩
    rw [← specializes_iff_mem_closure] at hq' ⊢
    exact (Topology.IsInducing.subtypeVal.specializes_iff).mp hq'
  have hS : S.Finite :=
    Set.Finite.of_finite_image (f := fun p : F => closure ({p} : Set F))
      (NoetherianSpace.finite_irreducibleComponents.subset (Set.image_subset_iff.mpr hcomp))
      fun p _ q _ hpq => (inseparable_iff_closure_eq.mpr hpq).eq
  exact (hS.image Subtype.val).subset fun y hy => ⟨⟨y, hy.2⟩, hy.1, rfl⟩

/-- **A codimension-one point of the closed fibre is not a closed point.** A closed one would be
open in the closed fibre, whose other irreducible components do not contain it; Zariski's main
theorem would then make `f` an isomorphism, under which the point has the codimension two of the
closed point of `Spec A`. -/
theorem not_isClosed_singleton_of_coheight_eq_one {y : X} (hy1 : coheight y = 1)
    (hys : f y = closedPoint A) : ¬ IsClosed ({y} : Set X) := by
  intro hcl
  have := isNoetherian_source f hf
  set F : Set X := f ⁻¹' {closedPoint A}
  let p : F := ⟨y, hys⟩
  -- the irreducible component of any other point of the fibre avoids `p`
  have havoid : ∀ q : F, q ≠ p → p ∉ irreducibleComponent q := by
    intro q hqp hp
    have hirr := (irreducibleComponent_mem_irreducibleComponents q).1
    have hsub := subset_closure_of_isIrreducible hdim f hf hy1
      (hirr.image Subtype.val continuous_subtype_val.continuousOn)
      (Subtype.coe_image_subset _ _) ⟨p, hp, rfl⟩
    have hq : (q : X) ∈ closure {y} := hsub ⟨q, mem_irreducibleComponent, rfl⟩
    rw [hcl.closure_eq, Set.mem_singleton_iff] at hq
    exact hqp (Subtype.ext hq)
  have hopen : IsOpen ({p} : Set F) := by
    have hcompl : ({p} : Set F)ᶜ =
        ⋃ C ∈ {C ∈ irreducibleComponents F | p ∉ C}, C := by
      ext q
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
        exists_prop]
      exact ⟨fun hqp => ⟨irreducibleComponent q, ⟨irreducibleComponent_mem_irreducibleComponents q,
        havoid q hqp⟩, mem_irreducibleComponent⟩, fun ⟨C, ⟨_, hpC⟩, hqC⟩ hqp => hpC (hqp ▸ hqC)⟩
    rw [← isClosed_compl_iff, hcompl]
    exact Set.Finite.isClosed_biUnion
      (NoetherianSpace.finite_irreducibleComponents.subset fun C hC => hC.1)
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hopen' :
      IsOpen ({(f.fiberHomeo (closedPoint A)).symm p} : Set (f.fiber (closedPoint A))) := by
    have := (f.fiberHomeo (closedPoint A)).symm.isOpenMap {p} hopen
    rwa [Set.image_singleton] at this
  have : IsIso f := hf.isIso_of_isOpen_singleton_fiber _ hopen'
  have hco : coheight y = coheight (f y) := (coheight_eq_of_isOpenImmersion f).symm
  have hh := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [hdim] at hh
  have hh2 : (maximalIdeal A).height = 2 := WithBot.coe_injective (hh.trans rfl)
  have hfy : (f y).asIdeal = maximalIdeal A := by rw [hys]; rfl
  have h2 : coheight (f y) = 2 := by rw [← idealHeight_eq_coheight, hfy, hh2]
  rw [hy1, h2] at hco
  exact absurd hco (by decide)

/-- Through the closure of each codimension-one point of the closed fibre passes a
codimension-one point not over the closed point. -/
theorem exists_horizontal_through_closure {y : X} (hy1 : coheight y = 1)
    (hys : f y = closedPoint A) :
    ∃ x : X, y ⤳ x ∧ ∃ Q : X, coheight Q = 1 ∧ f Q ≠ closedPoint A ∧ Q ⤳ x := by
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hncl := not_isClosed_singleton_of_coheight_eq_one hdim f hf hy1 hys
  obtain ⟨x, hxcl, hxy⟩ : ∃ x ∈ closure ({y} : Set X), x ≠ y := by
    by_contra! h
    exact hncl (closure_subset_iff_isClosed.mp fun x hx => h x hx)
  have hyx : y ⤳ x := specializes_iff_mem_closure.mpr hxcl
  refine ⟨x, hyx, ?_⟩
  -- the local ring at `x` has dimension at least two
  have hco : (2 : ℕ∞) ≤ coheight x := by
    have := coheight_add_one_le (lt_of_specializes_of_ne hyx hxy.symm)
    rwa [hy1] at this
  have h2 : 2 ≤ (maximalIdeal (X.presheaf.stalk x)).height := by
    have hd : ringKrullDim (X.presheaf.stalk x) = coheight x := ringKrullDim_stalk_eq_coheight x
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hd
    have : (maximalIdeal (X.presheaf.stalk x)).height = coheight x := by exact_mod_cast hd
    rwa [this]
  set T : Set X := {y : X | coheight y = 1 ∧ f y = closedPoint A}
  have hT : T.Finite := finite_setOf_coheight_eq_one_closedFibre hdim f hf
  have hSfin : {P : PrimeSpectrum (X.presheaf.stalk x) | X.fromSpecStalk x P ∈ T}.Finite :=
    hT.preimage (X.fromSpecStalk x).isEmbedding.injective.injOn
  obtain ⟨P, hP1, hPS⟩ := exists_height_eq_one_notMem_of_finite h2 _ hSfin
  have hQ1 := (Stacks.Chow.coheight_fromSpecStalk_eq_height x P).trans hP1
  exact ⟨X.fromSpecStalk x P, hQ1, fun hfQ => hPS ⟨hQ1, hfQ⟩,
    Stacks.Chow.specializes_fromSpecStalk x P⟩

/-- A codimension-one point of `X` not over the closed point does not lie over the generic point
either: the modification is an isomorphism over the punctured spectrum. -/
lemma asIdeal_ne_bot_of_coheight_eq_one {Q : X} (hQ1 : coheight Q = 1)
    (hfQ : f Q ≠ closedPoint A) : (f Q).asIdeal ≠ ⊥ := by
  intro hbot
  obtain ⟨V, hV, hiso⟩ := exists_isIso_restrict_punctured hdim f hf
  have hgen : f (genericPoint X) = f Q := by
    rw [IsBirational.genericPoint_eq f hf.isBirational, genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hbot.symm
  have hQV : Q ∈ f ⁻¹ᵁ V := (hV _).mpr hfQ
  have hgV : genericPoint X ∈ f ⁻¹ᵁ V :=
    (hV _).mpr (apply_genericPoint_ne_closedPoint hdim f hf)
  have heq : (⟨Q, hQV⟩ : f ⁻¹ᵁ V) = ⟨genericPoint X, hgV⟩ :=
    (f ∣_ V).isOpenEmbedding.injective <| Subtype.ext <| (morphismRestrict_base_coe f V _).trans
      (hgen.symm.trans (morphismRestrict_base_coe f V ⟨genericPoint X, hgV⟩).symm)
  have hQg : Q = genericPoint X := congrArg Subtype.val heq
  rw [hQg, coheight_eq_zero.mpr (isMax_genericPoint X)] at hQ1
  exact zero_ne_one hQ1

/-- The map from `A` to the function field of the source of the modification is injective. -/
lemma baseFun_ne_zero {a : A} (ha : a ≠ 0) : baseFun f a ≠ 0 := by
  obtain ⟨V, hV, hiso⟩ := exists_isIso_restrict_punctured hdim f hf
  have hgV : genericPoint X ∈ f ⁻¹ᵁ V := (hV _).mpr (apply_genericPoint_ne_closedPoint hdim f hf)
  have hst : IsIso (f.stalkMap (genericPoint X)) :=
    isIso_stalkMap_of_isIso_morphismRestrict f hiso hgV
  have hinj1 : Function.Injective (f.stalkMap (genericPoint X)).hom :=
    (ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X))).1
  let P : PrimeSpectrum A := f (genericPoint X)
  have hinj2 : Function.Injective
      (algebraMap A ((Spec.structureSheaf A).presheaf.stalk P)) :=
    IsLocalization.injective _ P.asIdeal.primeCompl_le_nonZeroDivisors
  intro h0
  apply ha
  apply hinj2
  rw [map_zero]
  apply hinj1
  exact h0.trans (map_zero _).symm

/-- **The auxiliary function of the polar lemma.** There is `φ ∈ A`, with nonzero image in the
function field of `X`, vanishing at the codimension-one points of the closed fibre, and for each
such point `y`, vanishing at a codimension-one point `Q` not over the closed point which
specializes to a point of the closure of `y`. -/
theorem exists_polar_auxiliary :
    ∃ φ : A, baseFun f φ ≠ 0 ∧
      (∀ y : X, coheight y = 1 → f y = closedPoint A →
        baseRingToStalk f y φ ∈ maximalIdeal (X.presheaf.stalk y)) ∧
      (∀ y : X, coheight y = 1 → f y = closedPoint A → ∃ x : X, y ⤳ x ∧
        ∃ Q : X, coheight Q = 1 ∧ f Q ≠ closedPoint A ∧ Q ⤳ x ∧
          baseRingToStalk f Q φ ∈ maximalIdeal (X.presheaf.stalk Q)) := by
  classical
  set T : Set X := {y : X | coheight y = 1 ∧ f y = closedPoint A}
  have hT : T.Finite := finite_setOf_coheight_eq_one_closedFibre hdim f hf
  have hdata : ∀ y ∈ T, ∃ x : X, y ⤳ x ∧ ∃ Q : X, coheight Q = 1 ∧ f Q ≠ closedPoint A ∧
      Q ⤳ x ∧ ∃ a : A, a ≠ 0 ∧ a ∈ (f Q).asIdeal := by
    intro y hy
    obtain ⟨x, hyx, Q, hQ1, hfQ, hQx⟩ := exists_horizontal_through_closure hdim f hf hy.1 hy.2
    obtain ⟨a, haQ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (asIdeal_ne_bot_of_coheight_eq_one hdim f hf hQ1 hfQ)
    exact ⟨x, hyx, Q, hQ1, hfQ, hQx, a, ha0, haQ⟩
  choose! xof hxof Qof hQ1 hfQ hQx aof ha0 haQ using hdata
  let φ : A := ∏ y ∈ hT.toFinset, aof y
  have hφQ : ∀ y ∈ T, φ ∈ (f (Qof y)).asIdeal := fun y hy =>
    Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (hT.mem_toFinset.mpr hy)) (haQ y hy)
  refine ⟨φ, baseFun_ne_zero hdim f hf
    (Finset.prod_ne_zero_iff.mpr fun y hy => ha0 y (hT.mem_toFinset.mp hy)), ?_, ?_⟩
  · intro y hy1 hys
    refine baseRingToStalk_mem_maximalIdeal f φ ?_
    rw [hys]
    exact le_maximalIdeal (f (Qof y)).isPrime.ne_top (hφQ y ⟨hy1, hys⟩)
  · intro y hy1 hys
    exact ⟨xof y, hxof y ⟨hy1, hys⟩, Qof y, hQ1 y ⟨hy1, hys⟩, hfQ y ⟨hy1, hys⟩,
      hQx y ⟨hy1, hys⟩, baseRingToStalk_mem_maximalIdeal f φ (hφQ y ⟨hy1, hys⟩)⟩

/-- **The polar lemma for a normal modification.** Let `A` be a two-dimensional Noetherian normal
local domain and `f : X ⟶ Spec A` a modification with `X` normal. If `h` attaches to every point
of `X` a rational function, regular at the codimension-one points not over the closed point, and
with `h x - h y` regular at `y` for `y` near `x`, then `h x` is regular at `x` for every `x`. -/
theorem forall_mem_stalkSubring_of_polar_of_isModification [IsNormal X]
    (h : X → X.functionField)
    (hA : ∀ y : X, coheight y = 1 → f y ≠ closedPoint A → h y ∈ stalkSubring y)
    (hB : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, h x - h y ∈ stalkSubring y) :
    ∀ x : X, h x ∈ stalkSubring x := by
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨φ, hφ0, hφT, hG⟩ := exists_polar_auxiliary hdim f hf
  exact forall_mem_stalkSubring_of_polar f (finite_setOf_coheight_eq_one_closedFibre hdim f hf)
    φ hφ0 hφT hG h hA hB

end AlgebraicGeometry

end
