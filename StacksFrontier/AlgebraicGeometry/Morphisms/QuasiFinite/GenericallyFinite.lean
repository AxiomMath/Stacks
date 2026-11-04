module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.RingTheory.QuasiFinite.GenericFiniteness
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Generically finite morphisms

For a morphism locally of finite type, finiteness of the fibre over a generic point of an
irreducible component is a condition that can be checked on affine charts, and the charts can be
made progressively coarser as more separation is assumed.

With no extra hypothesis the fibre is finite exactly when it is covered by finitely many affine
opens each finite over a common affine neighbourhood of the generic point. Under
quasi-separatedness those finitely many affine opens can be replaced by a single one, because a
quasi-separated scheme admits an affine open containing any finite set of generic points. Under
quasi-compactness as well, the whole inverse image of a suitable affine neighbourhood is finite
over it: the locus where that fails is a closed subscheme missing the generic point, so it can be
shrunk away.

## Main results

* `AlgebraicGeometry.finite_preimage_singleton_iff_exists_affine_cover_isFinite` gives the
  characterization by finitely many affine opens in the source.
* `AlgebraicGeometry.finite_preimage_singleton_iff_exists_affine_opens_isFinite` gives the
  characterization by one affine open in the source for a quasi-separated morphism.
* `AlgebraicGeometry.finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict` gives
  the characterization by finiteness over an affine neighbourhood in the target for a
  quasi-compact and quasi-separated morphism.

## Implementation notes

The generic point is represented by membership in Mathlib's `genericPoints`. In the first
characterization the finite family is indexed by `Fin n`. A morphism between chosen affine opens
is expressed by `Scheme.Hom.resLE`; in the final characterization the inverse-image morphism is
Mathlib's restriction `Scheme.Hom.restrict`.

## References

* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
-/


@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-- A point whose image under an open embedding is a generic point of an irreducible component is
itself a generic point of one. -/
private lemma closure_singleton_mem_irreducibleComponents_of_isOpenEmbedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {e : A → B} (he : IsOpenEmbedding e) {a : A}
    (h : closure {e a} ∈ irreducibleComponents B) : closure {a} ∈ irreducibleComponents A := by
  have hpre : e ⁻¹' closure {e a} = closure {a} := by
    rw [he.isOpenMap.preimage_closure_eq_closure_preimage he.continuous]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact he.injective.eq_iff
  rw [← hpre]
  exact preimage_mem_irreducibleComponents h he ⟨e a, subset_closure (by simp), a, rfl⟩

/-- The basic open of the image of a section under `appLE` lies over the basic open of the
section. -/
private lemma basicOpen_appLE_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens}
    {V : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V) (g : Γ(Y, V)) :
    X.basicOpen (f.appLE V U hUV g) ≤ f ⁻¹ᵁ Y.basicOpen g := by
  rw [Scheme.basicOpen_appLE]
  exact inf_le_right

/-- A point of `U` mapping into the basic open of `g` lies in the basic open of its image under
`appLE`. -/
private lemma mem_basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) (g : Γ(Y, V)) {x : X} (hx : x ∈ U) (hfx : f x ∈ Y.basicOpen g) :
    x ∈ X.basicOpen (f.appLE V U hUV g) := by
  rw [Scheme.basicOpen_appLE]
  exact ⟨hx, hfx⟩

/-- The prime of an affine chart corresponding to a generic point of an irreducible component is
a minimal prime of that chart. -/
private lemma minimal_prime_of_generic {Y : Scheme.{u}} (V : Y.affineOpens)
    (η : Y) (hη : η ∈ genericPoints Y) (hηV : η ∈ V.1) :
    (V.2.primeIdealOf ⟨η, hηV⟩).asIdeal ∈ minimalPrimes Γ(Y,V.1) := by
  let q := V.2.primeIdealOf ⟨η,hηV⟩
  have hq : V.2.fromSpec q = η := V.2.fromSpec_primeIdealOf ⟨η,hηV⟩
  have := V.2.isOpenImmersion_fromSpec
  have he : IsOpenEmbedding V.2.fromSpec := V.2.fromSpec.isOpenEmbedding
  have hirr : closure {q} ∈ irreducibleComponents (PrimeSpectrum Γ(Y,V.1)) := by
    apply closure_singleton_mem_irreducibleComponents_of_isOpenEmbedding he
    rw [hq]
    exact hη
  exact (PrimeSpectrum.vanishingIdeal_singleton q).symm ▸
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr hirr

/-- A finite fibre over a point of an affine chart of the target leaves only finitely many primes
of an affine chart of the source contracting to it. -/
private lemma finite_primesOver_of_finite_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (η : Y) (hηV : η ∈ V.1) (hfin : (f ⁻¹' {η}).Finite) :
    {q : PrimeSpectrum Γ(X, U.1) | q.comap (f.appLE V.1 U.1 hUV).hom =
      V.2.primeIdealOf ⟨η, hηV⟩}.Finite := by
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  apply Set.Finite.of_finite_image (f := fun q : PrimeSpectrum Γ(X, U.1) => hU.fromSpec q)
  · apply hfin.subset
    rintro x ⟨q, hq, rfl⟩
    show f (hU.fromSpec q) = η
    have hmap := congrArg (fun k : Spec (CommRingCat.of Γ(X, U.1)) ⟶ Y => k q)
      (hV.SpecMap_appLE_fromSpec f hU hUV)
    simp only at hmap
    have hmap' : hV.fromSpec (q.comap (f.appLE V.1 U.1 hUV).hom) = f (hU.fromSpec q) := hmap
    rw [hq, hV.fromSpec_primeIdealOf] at hmap'
    exact hmap'.symm
  · exact hU.fromSpec.isOpenEmbedding.injective.injOn

/-- The same finiteness, stated for the primes lying over the corresponding ideal. -/
private lemma finite_primesOver_of_finite_fiber' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (η : Y) (hηV : η ∈ V.1) (hfin : (f ⁻¹' {η}).Finite) :
    letI : Algebra Γ(Y,V.1) Γ(X,U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    ((V.2.primeIdealOf ⟨η,hηV⟩).asIdeal.primesOver Γ(X,U.1)).Finite := by
  let : Algebra Γ(Y,V.1) Γ(X,U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let p := (V.2.primeIdealOf ⟨η,hηV⟩).asIdeal
  apply ((finite_primesOver_of_finite_fiber f U V hUV η hηV hfin).image
    PrimeSpectrum.asIdeal).subset
  intro q hq
  change q.IsPrime ∧ q.LiesOver p at hq
  obtain ⟨hqprime,hqlies⟩ := hq
  refine ⟨⟨q,hqprime⟩, ?_, rfl⟩
  exact PrimeSpectrum.ext ((Ideal.liesOver_iff q p).mp hqlies).symm
/-- A finite map of coordinate rings makes the induced morphism of affine charts finite. -/
private lemma isFinite_resLE_of_finite_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hr : (f.appLE V.1 U.1 hUV).hom.Finite) : IsFinite (f.resLE V.1 U.1 hUV) := by
  have : IsFinite (Spec.map (f.appLE V.1 U.1 hUV)) :=
    (IsFinite.SpecMap_iff _).mpr hr
  have hiU : IsFinite U.1.toSpecΓ := by rw [← U.2.isoSpec_hom]; infer_instance
  have hiV : IsFinite V.1.toSpecΓ := by rw [← V.2.isoSpec_hom]; infer_instance
  have hcomp : IsFinite (f.resLE V.1 U.1 hUV ≫ V.1.toSpecΓ) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE]; infer_instance
  exact IsFinite.comp_iff.mp hcomp

/-- Shrinking the target to a basic open makes the induced morphism of charts finite, when the
fibre over a generic point is finite. -/
private lemma exists_finite_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (U : X.affineOpens) (V : Y.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (η : Y) (hη : η ∈ genericPoints Y)
    (hηV : η ∈ V.1) (hfin : (f ⁻¹' {η}).Finite) :
    ∃ g : Γ(Y,V.1), η ∈ Y.basicOpen g ∧
      IsFinite (f.resLE (Y.basicOpen g)
        (X.basicOpen (f.appLE V.1 U.1 hUV g)) (by simp [Scheme.basicOpen_appLE])) := by
  let R := Γ(Y,V.1)
  let S := Γ(X,U.1)
  let : Algebra R S := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  have hft : Algebra.FiniteType R S :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE V.2 U.2 hUV)
  let p := (V.2.primeIdealOf ⟨η,hηV⟩).asIdeal
  have hmin : p ∈ minimalPrimes R := minimal_prime_of_generic V η hη hηV
  have hpr : (p.primesOver S).Finite :=
    finite_primesOver_of_finite_fiber' f U V hUV η hηV hfin
  obtain ⟨g, hg, hgf⟩ :=
    Algebra.exists_localization_away_map_finite_of_mem_minimalPrimes_of_finite_primesOver hmin hpr
  let W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
  let t := f.appLE V.1 U.1 hUV g
  let T : X.affineOpens := ⟨X.basicOpen t, U.2.basicOpen t⟩
  have hTW : T.1 ≤ f ⁻¹ᵁ W.1 := by
    exact basicOpen_appLE_le_preimage f hUV g
  refine ⟨g, ?_, ?_⟩
  · have hq : V.2.primeIdealOf ⟨η,hηV⟩ ∈ PrimeSpectrum.basicOpen g := by
      simpa only [PrimeSpectrum.mem_basicOpen] using hg
    have hm : V.2.fromSpec (V.2.primeIdealOf ⟨η,hηV⟩) ∈ Y.basicOpen g := by
      show V.2.primeIdealOf ⟨η,hηV⟩ ∈ V.2.fromSpec ⁻¹ᵁ Y.basicOpen g
      rw [V.2.fromSpec_preimage_basicOpen]
      exact hq
    simpa [W, V.2.fromSpec_primeIdealOf] using hm
  · have : IsLocalization.Away g Γ(Y,Y.basicOpen g) := V.2.isLocalization_basicOpen g
    have : IsLocalization.Away t Γ(X,X.basicOpen t) := U.2.isLocalization_basicOpen t
    exact isFinite_resLE_of_finite_appLE f T W hTW (by
      show (f.appLE (Y.basicOpen g)
        (X.basicOpen (f.appLE V.1 U.1 hUV g)) _).hom.Finite
      rw [V.2.appLE_eq_away_map f U.2 hUV g]
      exact hgf _ _)

/-- Finiteness of a restricted morphism is inherited by a further shrinking of the target. -/
private lemma isFinite_resLE_inf_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V W : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V) (hWV : W ≤ V)
    (hfin : IsFinite (f.resLE V U hUV)) :
    IsFinite (f.resLE W (U ⊓ f ⁻¹ᵁ W) inf_le_right) := by
  let g := f.resLE W (U ⊓ f ⁻¹ᵁ W) inf_le_right
  let iU := X.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U)
  let iV := Y.homOfLE hWV
  let f0 := f.resLE V U hUV
  have H : iU ≫ f0 = g ≫ iV := by
    apply (cancel_mono V.ι).mp
    simp [g,iU,iV,f0, Scheme.Hom.resLE_comp_ι]
  have H' : f0 ⁻¹ᵁ iV.opensRange = iU.opensRange := by
    ext x
    simp only [Scheme.opensRange_homOfLE, Scheme.Hom.resLE_preimage, Opens.map_coe,
      Scheme.Hom.coe_image, Set.mem_preimage, Set.mem_image, SetLike.mem_coe, Opens.coe_inf,
      Set.preimage_inter, Set.mem_inter_iff, f0, iV, iU]
    constructor
    · rintro ⟨x₁, hx₁, hxeq⟩
      exact ⟨x.2, hxeq ▸ hx₁⟩
    · rintro ⟨-, hx⟩
      exact ⟨⟨f (U.ι x), hWV hx⟩, hx, rfl⟩
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    (IsOpenImmersion.isPullback g iU iV f0 H H').flip hfin

/-- A point lying in each of finitely many basic opens lies in the basic open of their product. -/
private lemma mem_basicOpen_finset_prod {Y : Scheme.{u}} {V : Y.Opens} {ι : Type*}
    (g : ι → Γ(Y, V)) (s : Finset ι) (η : Y) (hηV : η ∈ V)
    (h : ∀ i ∈ s, η ∈ Y.basicOpen (g i)) : η ∈ Y.basicOpen (s.prod g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Scheme.basicOpen_one] using hηV
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    exact ⟨h a (Finset.mem_insert_self ..), ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)⟩

/-- The basic open of a product of sections is contained in the basic open of each factor. -/
private lemma basicOpen_finset_prod_le {Y : Scheme.{u}} {V : Y.Opens} {ι : Type*}
    (g : ι → Γ(Y, V)) (s : Finset ι) (i : ι) (hi : i ∈ s) :
    Y.basicOpen (s.prod g) ≤ Y.basicOpen (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hi
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact inf_le_left
    · exact inf_le_right.trans (ih hi)

/-- A finite fibre over a generic point is covered by finitely many affine opens, each finite over
a common affine neighbourhood of that point. -/
private lemma finite_cover_forward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (η : Y) (hη : η ∈ genericPoints Y)
    (h : (f ⁻¹' {η}).Finite) :
    ∃ (n : ℕ) (U : Fin n → X.affineOpens) (V : Y.affineOpens),
      (η ∈ V.1) ∧ (f ⁻¹' {η} ⊆ ⋃ i, (U i).1) ∧
        ∀ i, ∃ hUi : (U i).1 ≤ f ⁻¹ᵁ V.1, IsFinite (f.resLE V.1 (U i).1 hUi) := by
  classical
  let F := f ⁻¹' {η}
  let : Fintype F := h.fintype
  let n := Fintype.card F
  let e : Fin n ≃ F := (Fintype.equivFin F).symm
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hηV₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  let V : Y.affineOpens := ⟨V₀,hV₀⟩
  have hchart (i : Fin n) : ∃ U : X.affineOpens, (e i).1 ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    have hxi : (e i).1 ∈ f ⁻¹ᵁ V.1 := by
      have heq : f (e i).1 = η := (e i).2
      simpa [heq] using hηV₀
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxi (f ⁻¹ᵁ V.1).isOpen
    exact ⟨⟨U, hU⟩, hxU, hUV⟩
  choose U₀ hmem hUV using hchart
  choose g hg hfg using fun i ↦ exists_finite_basicOpen f (U₀ i) V (hUV i) η hη hηV₀ h
  let G : Γ(Y, V.1) := (Finset.univ : Finset (Fin n)).prod g
  let W : Y.affineOpens := ⟨Y.basicOpen G, V.2.basicOpen G⟩
  have hηW : η ∈ W.1 := mem_basicOpen_finset_prod g Finset.univ η hηV₀ fun i _ ↦ hg i
  have hWle (i : Fin n) : W.1 ≤ Y.basicOpen (g i) :=
    basicOpen_finset_prod_le g Finset.univ i (Finset.mem_univ i)
  let U (i : Fin n) : X.affineOpens :=
    ⟨X.basicOpen (f.appLE V.1 (U₀ i).1 (hUV i) G), (U₀ i).2.basicOpen _⟩
  refine ⟨n, U, W, hηW, ?_, ?_⟩
  · intro x hx
    let i : Fin n := e.symm ⟨x, hx⟩
    have hi : x ∈ (U₀ i).1 := by
      have he : (e i).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      simpa [he] using hmem i
    have hxi : x ∈ (U i).1 := by
      have hfx : f x = η := by simpa using hx
      exact mem_basicOpen_appLE f (hUV i) G hi (by rwa [hfx])
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  · intro i
    have hUi : (U i).1 ≤ f ⁻¹ᵁ W.1 := by
      exact basicOpen_appLE_le_preimage f (hUV i) G
    refine ⟨hUi, ?_⟩
    have hfin' := isFinite_resLE_inf_preimage f
      (basicOpen_appLE_le_preimage f (hUV i) (g i)) (hWle i) (hfg i)
    have heq : (U i).1 =
        X.basicOpen (f.appLE V.1 (U₀ i).1 (hUV i) (g i)) ⊓ f ⁻¹ᵁ W.1 := by
      show X.basicOpen (f.appLE V.1 (U₀ i).1 (hUV i) G) =
        X.basicOpen (f.appLE V.1 (U₀ i).1 (hUV i) (g i)) ⊓ f ⁻¹ᵁ Y.basicOpen G
      rw [Scheme.basicOpen_appLE, Scheme.basicOpen_appLE]
      have hp : f ⁻¹ᵁ Y.basicOpen G ≤ f ⁻¹ᵁ Y.basicOpen (g i) := f.preimage_mono (hWle i)
      rw [inf_assoc, inf_eq_right.mpr hp]
    exact (f.resLE_congr hUi rfl heq @IsFinite).mpr hfin'

/-- A point specializing to a generic point of an irreducible component equals it. -/
private lemma eq_of_specializes_generic {Y : Scheme.{u}} {η y : Y}
    (hη : η ∈ genericPoints Y) (hy : y ⤳ η) : y = η := by
  have hsub : closure ({η} : Set Y) ⊆ closure {y} := hy.closure_subset
  have heq : closure ({η} : Set Y) = closure {y} :=
    subset_antisymm hsub (hη.2 (isIrreducible_singleton.closure) hsub)
  exact Inseparable.eq (hy.antisymm (specializes_iff_closure_subset.mpr heq.symm.le))
/-- A point of a finite fibre over a generic point is itself a generic point of the source. -/
private lemma generic_of_finite_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (η : Y) (hη : η ∈ genericPoints Y)
    (hfin : (f ⁻¹' {η}).Finite) {x : X} (hx : f x = η) :
    x ∈ genericPoints X := by
  have : Finite (f.fiber η) := (f.fiberHomeo η).finite_iff.mpr hfin
  have : DiscreteTopology (f ⁻¹' {η}) := (f.fiberHomeo η).discreteTopology
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let z : genericPoints X := genericPoints.ofComponent C
  have hzC : IsGenericPoint (z : X) C.1 := genericPoints.isGenericPoint_ofComponent C
  have hzx : (z : X) ⤳ x := hzC.specializes mem_irreducibleComponent
  have hzη : f (z : X) = η :=
    eq_of_specializes_generic hη (by simpa [hx] using hzx.map f.continuous)
  have hzsub : (⟨(z : X), hzη⟩ : f ⁻¹' {η}) ⤳ ⟨x,hx⟩ :=
    (subtype_specializes_iff _ _).mpr hzx
  have hzxEq : (z : X) = x := congrArg Subtype.val (specializes_iff_eq.mp hzsub)
  exact hzxEq ▸ z.2

/-- A generic point lying in an open subscheme is a generic point of that subscheme. -/
private lemma generic_of_open {X : Scheme.{u}} (U : X.Opens) (x : X)
    (hx : x ∈ U) (hgen : x ∈ genericPoints X) :
    (⟨x,hx⟩ : U.toScheme) ∈ genericPoints U.toScheme := by
  let y : U.toScheme := ⟨x,hx⟩
  exact closure_singleton_mem_irreducibleComponents_of_isOpenEmbedding
    (e := U.ι) U.ι.isOpenEmbedding (a := y) hgen
/-- For a quasi-separated morphism, a finite fibre over a generic point is contained in a single
affine open which is finite over an affine neighbourhood of that point. -/
private lemma finite_one_forward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiSeparated f]
    (η : Y) (hη : η ∈ genericPoints Y) (h : (f ⁻¹' {η}).Finite) :
    ∃ (V : Y.affineOpens) (U : X.affineOpens)
      (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
      (η ∈ V.1) ∧ (f ⁻¹' {η} ⊆ U.1) ∧ IsFinite (f.resLE V.1 U.1 hUV) := by
  classical
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hηV₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  let V : Y.affineOpens := ⟨V₀, hV₀⟩
  let S : X.Opens := f ⁻¹ᵁ V.1
  have : IsAffine V.1.toScheme := V.2
  have : QuasiSeparatedSpace V.1.toScheme := quasiSeparatedSpace_of_isAffine _
  have : QuasiSeparatedSpace S.toScheme := quasiSeparatedSpace_of_quasiSeparated (f ∣_ V.1)
  let F := f ⁻¹' {η}
  have : Finite F := h.to_subtype
  let E : F → S.toScheme := fun x => ⟨x.1, by
    have hx : f x.1 = η := x.2
    simpa [S, hx] using hηV₀⟩
  have hEgen (i : F) : E i ∈ genericPoints S.toScheme :=
    generic_of_open S i.1 (E i).2 (generic_of_finite_fiber f η hη h i.2)
  have hEinj : Function.Injective E := fun i j hij =>
    Subtype.ext (congrArg (fun z : S.toScheme => z.1) hij)
  have hZinj : Function.Injective (fun i : F => closure ({E i} : Set S.toScheme)) := by
    intro i j hij
    apply hEinj
    have hi : IsGenericPoint (E i) (closure {E i}) := rfl
    change closure {E i} = closure {E j} at hij
    have hj : IsGenericPoint (E j) (closure {E i}) :=
      hij.symm ▸ (show IsGenericPoint (E j) (closure {E j}) from rfl)
    exact hi.eq hj
  obtain ⟨U₀, hU₀aff, hU₀mem⟩ :=
    exists_affine_open_containing_generic_points
      (X := S.toScheme) (Z := fun i : F => closure ({E i} : Set S.toScheme))
      hEgen hZinj E (fun i => rfl)
  let Ubase : X.affineOpens := ⟨S.ι ''ᵁ U₀,
    (S.ι.isAffineOpen_iff_of_isOpenImmersion).mpr hU₀aff⟩
  have hUV : Ubase.1 ≤ f ⁻¹ᵁ V.1 := S.ι_image_le U₀
  have hcover : f ⁻¹' {η} ⊆ Ubase.1 := by
    intro x hx
    show x ∈ S.ι ''ᵁ U₀
    exact ⟨E ⟨x, hx⟩, hU₀mem ⟨x, hx⟩, rfl⟩
  obtain ⟨g, hηg, hgfin⟩ := exists_finite_basicOpen f Ubase V hUV η hη hηV₀ h
  let W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
  let U : X.affineOpens := ⟨X.basicOpen (f.appLE V.1 Ubase.1 hUV g), Ubase.2.basicOpen _⟩
  have hUW : U.1 ≤ f ⁻¹ᵁ W.1 := by
    exact basicOpen_appLE_le_preimage f hUV g
  refine ⟨W, U, hUW, hηg, ?_, hgfin⟩
  intro x hx
  have hfx : f x = η := by simpa using hx
  exact mem_basicOpen_appLE f hUV g (hcover hx) (by rwa [hfx])

/-- For a quasi-compact quasi-separated morphism, a finite fibre over a generic point makes the
whole inverse image of some affine neighbourhood finite over it. -/
private lemma finite_restrict_forward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    (η : Y) (hη : η ∈ genericPoints Y) (h : (f ⁻¹' {η}).Finite) :
    ∃ V : Y.affineOpens, (η ∈ V.1) ∧ IsFinite (f ∣_ V.1) := by
  obtain ⟨V, U, hUV, hηV, hcover, hfin⟩ := finite_one_forward f η hη h
  let S : X.Opens := f ⁻¹ᵁ V.1
  let O : S.toScheme.Opens := S.ι ⁻¹ᵁ U.1
  let Z : Closeds S.toScheme := ⟨(O : Set S.toScheme)ᶜ, O.isOpen.isClosed_compl⟩
  let I : S.toScheme.IdealSheafData := .vanishingIdeal Z
  let g : I.subscheme ⟶ V.1.toScheme := I.subschemeι ≫ (f ∣_ V.1)
  have : QuasiCompact g := by dsimp [g]; infer_instance
  let ηV : V.1.toScheme := ⟨η, hηV⟩
  have hηVgen : ηV ∈ genericPoints V.1.toScheme := generic_of_open V.1 η hηV hη
  have hηNot : ηV ∉ Set.range g := by
    rintro ⟨z, hz⟩
    let s : S.toScheme := I.subschemeι z
    have hsZ : s ∈ Z := by
      have hsrange : s ∈ Set.range I.subschemeι := ⟨z, rfl⟩
      simpa [I, Z, Scheme.IdealSheafData.range_subschemeι] using hsrange
    have hgs : (f ∣_ V.1) s = ηV := by simpa [g, s] using hz
    have hfx : f s.1 = η := by
      simpa [morphismRestrict_base_coe] using congrArg Subtype.val hgs
    exact hsZ (hcover hfx)
  obtain ⟨N, hηN, hgN⟩ :=
    exists_open_nhds_disjoint_range_of_quasiCompact g ηV hηVgen hηNot
  let OY : Y.Opens := V.1.ι ''ᵁ N
  have hηOY : η ∈ OY := by
    show η ∈ V.1.ι ''ᵁ N
    exact ⟨ηV, hηN, rfl⟩
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hηW₀, hWOY⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hηOY OY.isOpen
  let W : Y.affineOpens := ⟨W₀, hW₀⟩
  have hWV : W.1 ≤ V.1 := hWOY.trans (V.1.ι_image_le N)
  have hsub : f ⁻¹ᵁ W.1 ≤ U.1 := by
    intro x hxW
    by_contra hnotU
    have hxV : f x ∈ V.1 := hWV hxW
    let s : S.toScheme := ⟨x, hxV⟩
    have hsZ : s ∈ Z := hnotU
    obtain ⟨z, hz⟩ : s ∈ Set.range I.subschemeι := by
      simpa [I, Z, Scheme.IdealSheafData.range_subschemeι] using hsZ
    have hgzn : g z ∈ N := by
      have hfxN : f x ∈ OY := hWOY hxW
      obtain ⟨y, hy, hyx⟩ := hfxN
      have hsy : (f ∣_ V.1) s = y :=
        Subtype.ext ((morphismRestrict_base_coe f V.1 s).trans hyx.symm)
      have hgz : g z = y := (congrArg (f ∣_ V.1) hz).trans hsy
      exact hgz.symm ▸ hy
    have hzN : z ∈ g ⁻¹ᵁ N := hgzn
    rw [hgN] at hzN
    simp at hzN
  have hfin' := isFinite_resLE_inf_preimage f hUV hWV hfin
  have heq : U.1 ⊓ f ⁻¹ᵁ W.1 = f ⁻¹ᵁ W.1 := inf_eq_right.mpr hsub
  have hfin'' : IsFinite (f.resLE W.1 (f ⁻¹ᵁ W.1) le_rfl) :=
    (f.resLE_congr (inf_le_right : U.1 ⊓ f ⁻¹ᵁ W.1 ≤ f ⁻¹ᵁ W.1)
      rfl heq @IsFinite).mp hfin'
  refine ⟨W, hηW₀, ?_⟩
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hfin''

/-- The converse direction: a cover of the fibre by finitely many affine opens finite over a common
affine neighbourhood forces the fibre to be finite. -/
private lemma finite_preimage_singleton_of_affine_cover_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (n : ℕ) (U : Fin n → X.affineOpens) (V : Y.affineOpens)
    (hηV : η ∈ V.1) (hcover : f ⁻¹' {η} ⊆ ⋃ i, (U i).1)
    (hfin : ∀ i, ∃ hUi : (U i).1 ≤ f ⁻¹ᵁ V.1,
      IsFinite (f.resLE V.1 (U i).1 hUi)) :
    (f ⁻¹' {η}).Finite := by
  refine (Set.finite_iUnion (f := fun i ↦ f ⁻¹' {η} ∩ (U i).1) ?_).subset ?_
  · intro i
    obtain ⟨hUi, hi⟩ := hfin i
    let g := f.resLE V.1 (U i).1 hUi
    have : IsFinite g := hi
    have hf := g.finite_preimage_singleton ⟨η, hηV⟩
    exact hf.image (fun x : (U i).1 ↦ (x : X)) |>.subset (by
      rintro x ⟨hx, hxi⟩
      refine ⟨⟨x, hxi⟩, ?_, rfl⟩
      apply Subtype.ext
      simpa [g] using hx)
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨i, hx, hxi⟩


/-- **Stacks Project, Tag 02NW, conditions (1) and (2).** For a morphism locally of finite
type, the fibre over a generic point of an irreducible component is finite exactly when it is
covered by finitely many affine opens which are finite over a common affine neighbourhood of
that generic point. -/
@[stacks 02NW "conditions (1) and (2)"]
theorem finite_preimage_singleton_iff_exists_affine_cover_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (η : Y) (hη : η ∈ genericPoints Y) :
    (f ⁻¹' {η}).Finite ↔
      ∃ (n : ℕ) (U : Fin n → X.affineOpens) (V : Y.affineOpens),
        (η ∈ V.1) ∧
          (f ⁻¹' {η} ⊆ ⋃ i, (U i).1) ∧
            ∀ i, ∃ hUi : (U i).1 ≤ f ⁻¹ᵁ V.1, IsFinite (f.resLE V.1 (U i).1 hUi) := by
  constructor
  · exact finite_cover_forward f η hη
  · rintro ⟨n, U, V, hηV, hcover, hfin⟩
    exact finite_preimage_singleton_of_affine_cover_isFinite f η n U V hηV hcover hfin

/-- **Stacks Project, Tag 02NW, condition (3).** For a quasi-separated morphism locally of
finite type, the fibre over a generic point of an irreducible component is finite exactly when
one affine open containing the fibre is finite over an affine neighbourhood of that point. -/
@[stacks 02NW "condition (3)"]
theorem finite_preimage_singleton_iff_exists_affine_opens_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiSeparated f]
    (η : Y) (hη : η ∈ genericPoints Y) :
    (f ⁻¹' {η}).Finite ↔
      ∃ (V : Y.affineOpens) (U : X.affineOpens)
        (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        (η ∈ V.1) ∧ (f ⁻¹' {η} ⊆ U.1) ∧ IsFinite (f.resLE V.1 U.1 hUV) := by
  constructor
  · exact finite_one_forward f η hη
  · rintro ⟨V, U, hUV, hηV, hcover, hfin⟩
    exact finite_preimage_singleton_of_affine_cover_isFinite f η 1 (fun _ ↦ U) V hηV
      (fun x hx ↦ Set.mem_iUnion.mpr ⟨0, hcover hx⟩) (fun _ ↦ ⟨hUV, hfin⟩)

/-- **Stacks Project, Tag 02NW, condition (4).** For a quasi-compact and quasi-separated
morphism locally of finite type, finiteness of the fibre over a generic point of an
irreducible component is equivalent to finiteness over some affine neighbourhood of the
point. -/
@[stacks 02NW "condition (4)", stacks 03S1 "forward direction over an affine open"]
theorem finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (η : Y) (hη : η ∈ genericPoints Y) :
    (f ⁻¹' {η}).Finite ↔
      ∃ V : Y.affineOpens, (η ∈ V.1) ∧ IsFinite (f ∣_ V.1) := by
  constructor
  · exact finite_restrict_forward f η hη
  · rintro ⟨V, hηV, hfin⟩
    have : IsFinite (f ∣_ V.1) := hfin
    have hf := (f ∣_ V.1).finite_preimage_singleton ⟨η, hηV⟩
    exact hf.image (fun x : (f ⁻¹ᵁ V.1 : Scheme) ↦ x.1) |>.subset (by
      intro x hx
      have hfx : f x = η := by simpa using hx
      have hxV : x ∈ f ⁻¹ᵁ V.1 := by simpa [hfx] using hηV
      let x' : (f ⁻¹ᵁ V.1).toScheme := ⟨x, hxV⟩
      refine ⟨x', ?_, rfl⟩
      exact Subtype.ext ((morphismRestrict_base_coe f V.1 x').trans hfx))

end AlgebraicGeometry
