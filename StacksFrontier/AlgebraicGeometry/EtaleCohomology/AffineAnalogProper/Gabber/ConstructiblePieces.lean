module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosedVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.CellCase
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.ZariskiLocalConstancy
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleReduction

/-!
# A constructible sheaf on the spectrum of an absolutely integrally closed ring is piecewise
constant

Let `C` be an absolutely integrally closed ring and `G` a constructible abelian sheaf on
`(Spec C)_étale`. Then `Spec C` is covered by finitely many basic locally closed sets
`V(L) ∩ D(g)` on each of which `G` is constant with finite value
(`Stacks.EtaleCohomology.IsConstantOnSet`).

By definition `G` is finite locally constant on the strata of a finite partition of `Spec C`
into constructible locally closed subschemes, and a constructible subset of `Spec C` is a finite
union of basic locally closed sets (Mathlib's `PrimeSpectrum.exists_constructibleSetData_iff`).
On the reduced subscheme `Spec ((C/√(L))_g)` of such a basic set, whose local rings are strictly
henselian (Stacks 0DCS), finite local constancy is Zariski-local constancy
(`Stacks.EtaleCohomology.exists_opens_etaleAbelianInverseImage_iso_constant`), and finitely many
basic opens suffice by quasi-compactness.

## Main definitions

* `Stacks.EtaleCohomology.cellRing`, `Stacks.EtaleCohomology.cellImmersion`: the reduced
  subscheme `Spec ((C/√(L))_g)` of a basic locally closed set and its immersion.

## Main results

* `Stacks.EtaleCohomology.exists_pieces_of_isConstructibleOnEveryBigSite`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- **Finite local constancy on a reduced immersed subscheme inside a stratum.** -/
theorem isFiniteLocallyConstant_etaleAbelianInverseImage_of_isImmersion (B : BigEtaleSite.{u})
    (X : B.Scheme) {V : Scheme.{u}} (F : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : ConstructibleStratification B X ⊤)
    (hs : ∀ i, ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (((AlgebraicGeometry.smallEtaleBaseChange B (s.inclusion i)).sheafPullback
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj
          ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.obj F)))
    (j : V ⟶ X.obj) [IsImmersion j] [IsReduced V] (t : Fin s.n)
    (ht : Set.range j.base ⊆ Set.range (B.inclusion.map (s.inclusion t)).base) :
    ConstantSheaf.IsFiniteLocallyConstant V.smallEtaleTopology
      ((etaleAbelianInverseImage.{u, 0} j).obj F) := by
  have hV : B.Contains V :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit j X.property
  have := s.isImmersion t
  obtain ⟨g, hg⟩ := Scheme.exists_comp_eq_of_isImmersion_of_isReduced
    (B.inclusion.map (s.inclusion t)) j ht
  let gB : B.obj V hV ⟶ s.piece t := ObjectProperty.homMk g
  let jB : B.obj V hV ⟶ X := ObjectProperty.homMk j
  have hgB : gB ≫ s.inclusion t = jB := by
    ext1
    exact hg
  have hB := isFiniteLocallyConstant_smallEtaleSheafPullback_comp B AddCommGrpCat.{u + 1}
    (s.inclusion t) gB _ (hs t)
  rw [hgB] at hB
  rw [SmallEtale.isFiniteLocallyConstant_abelian_iff_toEtaleSite B V hV]
  exact ConstantSheaf.isFiniteLocallyConstant_congr _
    ((SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{u + 1} jB
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map jB))
      (Functor.sheafAdjunctionContinuous _ _ _ _)).app F) (hF := hB)

variable {C : Type u} [CommRing C]

/-- A point `x` of `Spec C` lies in the image of `Spec (C ⧸ 𝔞)` if and only if `𝔞 ≤ x`. -/
theorem mem_range_specMap_quotient_mk (𝔞 : Ideal C) (x : Spec (.of C)) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).base ↔
      𝔞 ≤ x.asIdeal := by
  have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := 𝔞))
  rw [Ideal.mk_ker] at h
  change x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk 𝔞)) ↔ _
  rw [h]
  rfl

/-- The radical ideal of the equations of a basic locally closed set. -/
abbrev cellIdeal (L : List C) : Ideal C := (Ideal.span {b | b ∈ L}).radical

/-- The ring of the reduced subscheme of the basic locally closed set `V(L) ∩ D(g)`. -/
abbrev cellRing (L : List C) (g : C) : Type u :=
  Localization.Away (Ideal.Quotient.mk (cellIdeal L) g)

/-- The immersion of the reduced subscheme of the basic locally closed set `V(L) ∩ D(g)`. -/
def cellImmersion (L : List C) (g : C) : Spec (.of (cellRing L g)) ⟶ Spec (.of C) :=
  basicOpenImmersion (Ideal.Quotient.mk (cellIdeal L) g) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (cellIdeal L)))

/-- The morphism `cellImmersion L g` is an immersion of schemes. -/
instance (L : List C) (g : C) : IsImmersion (cellImmersion L g) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (cellIdeal L)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold cellImmersion
  infer_instance

/-- The quotient of `C` by the radical ideal `cellIdeal L` is reduced. -/
instance (L : List C) : IsReduced (C ⧸ cellIdeal L) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)

/-- The scheme `Spec (cellRing L g)` is reduced. -/
instance (L : List C) (g : C) : IsReduced (Spec (.of (cellRing L g))) := inferInstance

/-- If `C` is absolutely integrally closed, then so is `cellRing L g`. -/
theorem isAbsolutelyIntegrallyClosed_cellRing (hC : IsAbsolutelyIntegrallyClosed C)
    (L : List C) (g : C) : IsAbsolutelyIntegrallyClosed (cellRing L g) :=
  isAbsolutelyIntegrallyClosed_localization (C ⧸ cellIdeal L)
    (Submonoid.powers (Ideal.Quotient.mk (cellIdeal L) g)) (cellRing L g)
    (isAbsolutelyIntegrallyClosed_quotient C _ hC)

/-- The image of a prime `z` of `cellRing L g` under `cellImmersion L g` is the preimage of `z`
under the ring map `C → C ⧸ cellIdeal L → cellRing L g`. -/
theorem cellImmersion_base_asIdeal (L : List C) (g : C) (z : Spec (.of (cellRing L g))) :
    ((cellImmersion L g).base z).asIdeal =
      z.asIdeal.comap ((algebraMap (C ⧸ cellIdeal L) (cellRing L g)).comp
        (Ideal.Quotient.mk (cellIdeal L))) := by
  unfold cellImmersion
  rw [← Spec.map_comp, Spec.map_base]
  rfl

/-- An element `c` of `C` lies in the image under `cellImmersion L g` of a prime `z` if and only if
its image in `cellRing L g` lies in `z`. -/
private theorem cellImmersion_base_mem_iff {L : List C} {g c : C}
    {z : Spec (.of (cellRing L g))} :
    c ∈ ((cellImmersion L g).base z).asIdeal ↔
      algebraMap (C ⧸ cellIdeal L) (cellRing L g) (Ideal.Quotient.mk (cellIdeal L) c) ∈
        z.asIdeal := by
  rw [cellImmersion_base_asIdeal]
  rfl

/-- The image of `cellImmersion L g` is the basic locally closed set `cellSet L g`. -/
theorem range_cellImmersion (L : List C) (g : C) :
    Set.range (cellImmersion L g).base = cellSet L g := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change (∀ b ∈ L, b ∈ ((cellImmersion L g).base z).asIdeal) ∧
      g ∉ ((cellImmersion L g).base z).asIdeal
    refine ⟨fun b hb => ?_, fun hg => ?_⟩
    · rw [cellImmersion_base_mem_iff, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.le_radical (Ideal.subset_span (show b ∈ {b | b ∈ L} from hb))), map_zero]
      exact z.asIdeal.zero_mem
    · rw [cellImmersion_base_mem_iff] at hg
      exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hg
        (IsLocalization.Away.algebraMap_isUnit _))
  · rintro ⟨hL, hg⟩
    have hle : cellIdeal L ≤ x.asIdeal := x.isPrime.radical_le_iff.mpr (Ideal.span_le.mpr hL)
    obtain ⟨x', rfl⟩ := (mem_range_specMap_quotient_mk _ x).mpr hle
    have hx' : Ideal.Quotient.mk (cellIdeal L) g ∉ x'.asIdeal := fun h =>
      hg (by rwa [specMap_base_asIdeal])
    obtain ⟨z, rfl⟩ := (mem_range_basicOpenImmersion _ x').mpr hx'
    exact ⟨z, rfl⟩

variable (G : Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- A list of pieces is *good* for `G` when `G` is constant with finite value on each of them. -/
def GoodPieces (pieces : List (List C × C × AddCommGrpCat.{u + 1})) : Prop :=
  ∀ p ∈ pieces, Finite p.2.2 ∧ IsConstantOnSet G (cellSet p.1 p.2.1) p.2.2

/-- If each of the sets `Q i`, `i ∈ s`, is covered by the union of a list of pieces good for `G`,
then so is their union `⋃ i ∈ s, Q i`. -/
theorem exists_goodPieces_biUnion {ι : Type*} (s : Finset ι) (Q : ι → Set (Spec (.of C)))
    (h : ∀ i ∈ s, ∃ pieces, GoodPieces G pieces ∧ Q i ⊆ piecesUnion pieces) :
    ∃ pieces, GoodPieces G pieces ∧ (⋃ i ∈ s, Q i) ⊆ piecesUnion pieces := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], fun p hp => absurd hp List.not_mem_nil, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨p₁, hp₁, hQ₁⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨p₂, hp₂, hQ₂⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨p₁ ++ p₂, fun p hp => (List.mem_append.mp hp).elim (hp₁ p) (hp₂ p), fun x hx => ?_⟩
    simp only [Finset.mem_insert, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨j, rfl | hj, hxj⟩ := hx
    · obtain ⟨p, hp, hxp⟩ := hQ₁ hxj
      exact ⟨p, List.mem_append_left _ hp, hxp⟩
    · obtain ⟨p, hp, hxp⟩ := hQ₂ (Set.mem_biUnion hj hxj)
      exact ⟨p, List.mem_append_right _ hp, hxp⟩

/-- If the inverse image of `G` to an open `O` of `Spec (cellRing L g)` containing the basic open
of the image of `c` is constant with value `E`, then `G` is constant with value `E` on
`cellSet L (g * c)`. -/
theorem isConstantOnSet_cellSet_mul_of_iso (L : List C) (g c : C)
    (O : (Spec (.of (cellRing L g))).Opens) {E : AddCommGrpCat.{u + 1}}
    (hO : ∀ z : Spec (.of (cellRing L g)),
      (algebraMap (C ⧸ cellIdeal L) (cellRing L g)).comp (Ideal.Quotient.mk (cellIdeal L)) c ∉
        z.asIdeal → z ∈ O)
    (e : Nonempty ((etaleAbelianInverseImage.{u, 0} O.ι).obj
      ((etaleAbelianInverseImage.{u, 0} (cellImmersion L g)).obj G) ≅
        (constantSheaf O.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) :
    IsConstantOnSet G (cellSet L (g * c)) E := by
  intro W ι _ _ hsub
  have hrange : Set.range ι.base ⊆ Set.range (O.ι ≫ cellImmersion L g).base := by
    intro x hx
    obtain ⟨hxL, hxc⟩ := mem_cellSet_mul.mp (hsub hx)
    obtain ⟨z, rfl⟩ := (range_cellImmersion L g).superset hxL
    exact ⟨⟨z, hO z fun h => hxc ((cellImmersion_base_mem_iff).mpr h)⟩, rfl⟩
  obtain ⟨ι', hι'⟩ :=
    Scheme.exists_comp_eq_of_isImmersion_of_isReduced (O.ι ≫ cellImmersion L g) ι hrange
  obtain ⟨e⟩ := e
  exact ⟨(etaleAbelianInverseImageCompIso'.{u, 0} ι' (O.ι ≫ cellImmersion L g) ι
      hι'.symm).app G ≪≫
    (etaleAbelianInverseImage.{u, 0} ι').mapIso
      ((etaleAbelianInverseImageCompIso'.{u, 0} O.ι (cellImmersion L g) _ rfl).app G ≪≫ e) ≪≫
    (etaleAbelianInverseImageConstantIso.{u, 0} ι').app E⟩

/-- Around each point `y` of an open `U` of `Spec (cellRing L g)` there is a basic open, cut out
by the image of an element `c` of `C`, contained in `U`. -/
theorem exists_basicOpen_subset_cellRing (L : List C) (g : C)
    (U : (Spec (.of (cellRing L g))).Opens) (y : Spec (.of (cellRing L g))) (hy : y ∈ U) :
    ∃ c : C, (algebraMap (C ⧸ cellIdeal L) (cellRing L g)).comp
        (Ideal.Quotient.mk (cellIdeal L)) c ∉ y.asIdeal ∧
      ∀ z : Spec (.of (cellRing L g)), (algebraMap (C ⧸ cellIdeal L) (cellRing L g)).comp
        (Ideal.Quotient.mk (cellIdeal L)) c ∉ z.asIdeal → z ∈ U := by
  obtain ⟨_, ⟨h, rfl⟩, hyh, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := (y : PrimeSpectrum (cellRing L g))) (u := (U : Set (Spec (.of (cellRing L g)))))
    hy U.isOpen
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (Ideal.Quotient.mk (cellIdeal L) g)) h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hiff : ∀ z : Spec (.of (cellRing L g)), (algebraMap (C ⧸ cellIdeal L) (cellRing L g)).comp
      (Ideal.Quotient.mk (cellIdeal L)) c ∉ z.asIdeal ↔
        IsLocalization.mk' (cellRing L g) (Ideal.Quotient.mk (cellIdeal L) c) s ∉ z.asIdeal :=
    fun z => by simp only [RingHom.comp_apply, IsLocalization.mk'_mem_iff]
  exact ⟨c, (hiff y).mpr hyh, fun z hz => hsub ((hiff z).mp hz)⟩

/-- **A basic locally closed set on whose reduced subscheme `G` is finite locally constant is
covered by finitely many basic locally closed sets on which `G` is constant**, when `C` is
absolutely integrally closed. -/
theorem exists_goodPieces_of_isFiniteLocallyConstant (hC : IsAbsolutelyIntegrallyClosed C)
    (L : List C) (g : C)
    (hflc : ConstantSheaf.IsFiniteLocallyConstant (Spec (.of (cellRing L g))).smallEtaleTopology
      ((etaleAbelianInverseImage.{u, 0} (cellImmersion L g)).obj G)) :
    ∃ pieces, GoodPieces G pieces ∧ cellSet L g ⊆ piecesUnion pieces := by
  classical
  let D := cellRing L g
  let φ : C →+* D := (algebraMap (C ⧸ cellIdeal L) D).comp (Ideal.Quotient.mk (cellIdeal L))
  choose O hyO E hE e using exists_opens_etaleAbelianInverseImage_iso_constant
    (AbsolutelyIntegrallyClosed.strictlyHenselianLocalRing_stalk
      (isAbsolutelyIntegrallyClosed_cellRing hC L g)) _ hflc
  choose c hcy hcO using fun y => exists_basicOpen_subset_cellRing L g (O y) y (hyO y)
  obtain ⟨t, ht⟩ := (isCompact_univ (X := Spec (.of D))).elim_finite_subcover
    (fun y => {z : Spec (.of D) | φ (c y) ∉ z.asIdeal})
    (fun y => (PrimeSpectrum.basicOpen (φ (c y))).isOpen)
    (fun z _ => Set.mem_iUnion.mpr ⟨z, hcy z⟩)
  refine ⟨t.toList.map fun y => (L, g * c y, E y), ?_, ?_⟩
  · intro p hp
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hp
    exact ⟨hE y, isConstantOnSet_cellSet_mul_of_iso G L g (c y) (O y) (hcO y) (e y)⟩
  · intro x hx
    obtain ⟨z, rfl⟩ := (range_cellImmersion L g).superset hx
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
    exact ⟨(L, g * c y, E y), List.mem_map.mpr ⟨y, Finset.mem_toList.mpr hy, rfl⟩,
      mem_cellSet_mul.mpr ⟨(range_cellImmersion L g).subset ⟨z, rfl⟩,
        (cellImmersion_base_mem_iff).not.mpr hzy⟩⟩

/-- The basic locally closed set `cellSet (List.ofFn b.g) b.f` is the set `b.toSet` described by
the basic constructible set data `b`. -/
theorem cellSet_ofFn_eq_toSet (b : PrimeSpectrum.BasicConstructibleSetData C) :
    cellSet (List.ofFn b.g) b.f = b.toSet := by
  refine Set.ext fun (x : PrimeSpectrum C) => ?_
  change (∀ a ∈ List.ofFn b.g, a ∈ x.asIdeal) ∧ b.f ∉ x.asIdeal ↔
    x ∈ PrimeSpectrum.zeroLocus (Set.range b.g) \ PrimeSpectrum.zeroLocus {b.f}
  rw [Set.mem_sdiff, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus,
    Set.range_subset_iff, Set.singleton_subset_iff, List.forall_mem_ofFn_iff]
  rfl

/-- **A constructible sheaf on the spectrum of an absolutely integrally closed ring is
piecewise constant.** If `C` is absolutely integrally closed and `G` is a constructible abelian
sheaf on `(Spec C)_étale`, then finitely many basic locally closed sets `V(L) ∩ D(g)` cover
`Spec C` with `G` constant of finite value on each of them. -/
theorem exists_goodPieces_of_isConstructibleOnEveryBigSite (hC : IsAbsolutelyIntegrallyClosed C)
    (hG : IsConstructibleOnEveryBigSite G) :
    ∃ pieces, GoodPieces G pieces ∧ ∀ x : Spec (.of C), ∃ p ∈ pieces, x ∈ cellSet p.1 p.2.1 := by
  classical
  let B := BigEtaleSite.containing (Spec (.of C))
  have hX : B.Contains (Spec (.of C)) := BigEtaleSite.contains_containing _
  obtain ⟨s, hs⟩ := hG B hX ⟨⊤, isAffineOpen_top _⟩
  let S : Fin s.n → Set (Spec (.of C)) :=
    fun t => Set.range (B.inclusion.map (s.inclusion t)).base
  have hSc : ∀ t, Topology.IsConstructible (S t) := by
    intro t
    have h := (s.constructible t).image_of_isOpenEmbedding
      (⊤ : (Spec (.of C)).Opens).ι.isOpenEmbedding
      (by simp)
    rwa [Set.image_preimage_eq_of_subset (by simp)] at h
  have hpieces : ∀ t ∈ (Finset.univ : Finset (Fin s.n)),
      ∃ pieces, GoodPieces G pieces ∧ S t ⊆ piecesUnion pieces := by
    intro t _
    obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr (hSc t)
    obtain ⟨pieces, hgood, hsub⟩ := exists_goodPieces_biUnion G T
      (fun b => cellSet (List.ofFn b.g) b.f) (fun b hb => by
        have hbS : cellSet (List.ofFn b.g) b.f ⊆ S t := by
          rw [cellSet_ofFn_eq_toSet, ← hT]
          exact Set.subset_biUnion_of_mem (u := fun b => b.toSet) hb
        exact exists_goodPieces_of_isFiniteLocallyConstant G hC _ _
          (isFiniteLocallyConstant_etaleAbelianInverseImage_of_isImmersion B
            (B.obj (Spec (.of C)) hX) G s hs (cellImmersion (List.ofFn b.g) b.f) t
            (by rwa [range_cellImmersion])))
    refine ⟨pieces, hgood, fun x hx => hsub ?_⟩
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (show x ∈ T.toSet from hT ▸ hx)
    exact Set.mem_biUnion hb (by rwa [cellSet_ofFn_eq_toSet])
  obtain ⟨pieces, hgood, hsub⟩ := exists_goodPieces_biUnion G Finset.univ S hpieces
  refine ⟨pieces, hgood, fun x => hsub ?_⟩
  have hx : x ∈ ((⊤ : (Spec (.of C)).Opens) : Set (Spec (.of C))) := trivial
  rw [s.covers] at hx
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_biUnion (Finset.mem_univ t) ht

end Stacks.EtaleCohomology
