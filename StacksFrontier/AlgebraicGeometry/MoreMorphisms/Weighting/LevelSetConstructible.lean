module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FiniteCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of the level sets of a weighting

Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let `w : X → ℤ` be a weighting
of `f`.  Then every level set `{x | w x = n}` is locally constructible in `X`.

## Main results

* `AlgebraicGeometry.isLocallyConstructible_weighting_levelSet`: the level sets of a weighting of
  a locally quasi-finite morphism are locally constructible.

## Implementation notes

Local constructibility is local on the source and on the target, so one reduces at once to `X`
and `Y` affine.  There Zariski's Main Theorem
(`Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization`) writes `f` as an
open immersion `j : X ⟶ T` followed by a finite morphism `p : T ⟶ Y`.

A finite morphism to an affine scheme becomes, after a surjective finite locally free base change
`g : Y' ⟶ Y`, a closed subscheme of a finite locally free `Z' ⟶ Y'` which is covered
set-theoretically by finitely many sections of `Z' ⟶ Y'`
(`Stacks.Morphisms.exists_finiteLocallyFree_cover_closedImmersion`).  Local constructibility
descends along `g` because `g` is surjective, quasi-compact and locally of finite presentation,
so it suffices to treat the base-changed situation; weightings pull back along base change by
`AlgebraicGeometry.IsWeighting.comp_of_isPullback`.

In the base-changed situation the ranges of the finitely many sections form a finite closed cover
of `Z'`.  Over the locus where any two of them are either equal or disjoint these ranges are
*clopen*, and the source decomposes accordingly into open-and-closed pieces, each of which maps
homeomorphically onto an open subscheme of the base by a finite morphism with trivial residue
field extensions.  For such a piece the weighting condition applied to the identity base change
identifies `w` with its own weighted fibre sum pulled back, so `w` is locally constant there and
its level sets are open.  The required locus in the base is cut out by the finitely many
constructible conditions "`s i` lands in the range of `s j`"; the finitely many Boolean patterns
of these conditions partition the base into constructible pieces, and each constructible piece of
an affine scheme is the range of an affine morphism locally of finite presentation
(by `PrimeSpectrum.exists_constructibleSetData_iff`), which is the finitely presented base change
needed to reduce to one pattern.

## References

* [Stacks Project, Tag 0F3G](https://stacks.math.columbia.edu/tag/0F3G)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 03HW](https://stacks.math.columbia.edu/tag/03HW)
-/

public section

open CategoryTheory CategoryTheory.Limits Topology PrimeSpectrum

universe u

namespace AlgebraicGeometry

/-- A weighting of a finite morphism which is injective on points and has trivial separable
residue degrees is locally constant: the weighting condition for the identity base change
identifies `w` with the pullback of its own weighted fibre sum. -/
private theorem isLocallyConstant_of_isFinite_of_injective_of_finSepDegree_eq_one
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsFinite f]
    {w : X → ℤ} (hw : IsWeighting f w)
    (hinj : Function.Injective (fun x : X => f x))
    (hdegree : ∀ x : X,
      @Field.finSepDegree (Y.residueField (f x)) (X.residueField x)
        inferInstance inferInstance ((f.residueFieldMap x).hom.toAlgebra) = 1) :
    IsLocallyConstant w := by
  let P := pullback f (𝟙 Y)
  let h : P ⟶ X := pullback.fst f (𝟙 Y)
  let π : P ⟶ Y := pullback.snd f (𝟙 Y)
  have hsquare : IsPullback h π f (𝟙 Y) := IsPullback.of_hasPullback f (𝟙 Y)
  have hlift : pullback.lift h π pullback.condition = 𝟙 P := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, Category.id_comp]
  have hsum : IsLocallyConstant (separableDegreeWeightedFiberSum π (w ∘ h)) := by
    apply hw h π (𝟙 Y) pullback.condition
    · infer_instance
    · rw [hlift]
      infer_instance
    · infer_instance
  have hsumf : IsLocallyConstant (separableDegreeWeightedFiberSum f w) := by
    have hbase := separableDegreeWeightedFiberSum_comp_of_isPullback f h π (𝟙 Y) hsquare
      (fun y => f.finite_preimage_singleton y) w
    have heq : separableDegreeWeightedFiberSum f w =
        separableDegreeWeightedFiberSum π (w ∘ h) := by
      funext y
      simpa [Function.comp] using congrFun hbase y
    rwa [heq]
  have heq : separableDegreeWeightedFiberSum f w ∘ f = w := by
    funext x
    let K := Y.residueField (f x)
    let A : Algebra K (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
    unfold separableDegreeWeightedFiberSum
    dsimp only [Function.comp_apply]
    rw [finsum_eq_single _ x (by
      intro y hy
      have hneq : f y ≠ f x := fun hEq => hy (hinj hEq)
      simp [hneq])]
    simp only [↓reduceIte]
    change w x * ↑(@Field.finSepDegree K (X.residueField x)
      inferInstance inferInstance A) = w x
    rw [hdegree x]
    simp
  rw [← heq]
  exact hsumf.comp_continuous f.continuous

/-- A level set of a locally constant function is open, hence locally constructible. -/
private theorem isLocallyConstructible_levelSet
    {X β : Type*} [TopologicalSpace X] {w : X → β} (hw : IsLocallyConstant w) (n : β) :
    IsLocallyConstructible {x : X | w x = n} := by
  intro x
  let U : Set X := {y | w y = w x}
  have hU : IsOpen U := hw.isOpen_fiber (w x)
  refine ⟨U, hU.mem_nhds rfl, hU, ?_⟩
  by_cases h : w x = n
  · convert IsConstructible.univ using 1
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact y.property.trans h
  · convert IsConstructible.empty using 1
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hn => h (y.property.symm.trans hn)

/-- The locus where membership in each of a family of sets is prescribed by a Boolean vector. -/
private def membershipPattern {X ι : Type*} (C : ι → Set X) (b : ι → Bool) : Set X :=
  {x | ∀ i, (x ∈ C i) ↔ (b i = true)}

/-- A Boolean membership pattern of finitely many constructible sets is constructible. -/
private theorem isConstructible_membershipPattern
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (C : ι → Set X) (hC : ∀ i, IsConstructible (C i)) (b : ι → Bool) :
    IsConstructible (membershipPattern C b) := by
  have heq : membershipPattern C b = ⋂ i, if b i then C i else (C i)ᶜ := by
    ext x
    simp only [membershipPattern, Set.mem_ofPred_eq, Set.mem_iInter]
    refine forall_congr' fun i => ?_
    cases b i <;> simp
  rw [heq]
  exact IsConstructible.iInter fun i => by cases b i <;> simp [hC]

/-- The Boolean membership patterns of a family of sets cover the whole space. -/
private theorem membershipPattern_iUnion_eq_univ {X ι : Type*} (C : ι → Set X) :
    (⋃ b : ι → Bool, membershipPattern C b) = Set.univ := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨fun i => decide (x ∈ C i), ?_⟩
  intro i
  by_cases hx : x ∈ C i <;> simp [hx]

/-- A constructible subset of the spectrum of a ring is the image of the spectrum of a finitely
presented algebra. -/
private theorem exists_finitePresentation_comap_range
    {R : Type u} [CommRing R] {s : Set (PrimeSpectrum R)} (hs : IsConstructible s) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S),
      f.FinitePresentation ∧ Set.range (PrimeSpectrum.comap f) = s := by
  obtain ⟨data, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hs
  let S := ∀ i : data, Localization.Away
    (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f)
  let : CommRing S := inferInstance
  let : Algebra R S := inferInstance
  have hfp : Algebra.FinitePresentation R S := by
    have hcomponent (i : data) : Algebra.FinitePresentation R
        (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f)) := by
      let I : Ideal R := Ideal.span (Set.range i.1.g)
      let Q := R ⧸ I
      let r : Q := Ideal.Quotient.mk I i.1.f
      let A := Localization.Away r
      have hI : I.FG := Submodule.fg_span (Set.finite_range i.1.g)
      let : Algebra.FinitePresentation R Q := Algebra.FinitePresentation.quotient hI
      let : Algebra.FinitePresentation Q A := inferInstance
      exact Algebra.FinitePresentation.trans R Q A
    let : ∀ i : data, Algebra.FinitePresentation R
        (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f)) := hcomponent
    exact Algebra.FinitePresentation.pi _
  let f : R →+* S := algebraMap R S
  refine ⟨S, inferInstance, f, RingHom.finitePresentation_algebraMap.mpr hfp, ?_⟩
  change Set.range (PrimeSpectrum.comap (algebraMap R S)) = data.toSet
  rw [← PrimeSpectrum.iUnion_range_comap_comp_evalRingHom,
    PrimeSpectrum.ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  congr! with _ _ C
  let I := Ideal.span (Set.range C.1.g)
  let r := Ideal.Quotient.mk I C.1.f
  trans comap (Ideal.Quotient.mk I) ''
      Set.range (comap (algebraMap _ (Localization.Away r)))
  · rw [← Set.range_comp]
    rfl
  · rw [localization_away_comap_range _ r, ← comap_basicOpen,
      TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk,
      Set.image_preimage_eq_inter_range,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      BasicConstructibleSetData.toSet, Set.sdiff_eq_compl_inter,
      basicOpen_eq_zeroLocus_compl, Ideal.mk_ker, zeroLocus_span]

/-- A constructible subset of an affine scheme is the range of a morphism from an affine scheme
which is locally of finite presentation. -/
@[ega "IV 1.8.3" "affine target X"]
private theorem exists_affine_finitePresentation_range
    {Y : Scheme.{u}} [IsAffine Y] {C : Set Y} (hC : IsConstructible C) :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (g : V ⟶ Y),
      LocallyOfFinitePresentation g ∧ Set.range g = C := by
  let e := Y.isoSpec
  have hC' : IsConstructible (e.inv ⁻¹' C) := e.inv.isConstructible_preimage hC
  obtain ⟨S, hS, φ, hφ, hrange⟩ := exists_finitePresentation_comap_range hC'
  let := hS
  let g := Spec.map (CommRingCat.ofHom φ) ≫ e.inv
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ)) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr hφ
  refine ⟨Spec (.of S), inferInstance, g, inferInstance, ?_⟩
  change Set.range (e.inv ∘ (Spec.map (CommRingCat.ofHom φ))) = C
  change Set.range (Spec.map (CommRingCat.ofHom φ)) = e.inv ⁻¹' C at hrange
  rw [Set.range_comp, hrange, Set.image_preimage_eq _ e.inv.surjective]

/-- Local constructibility descends along a surjective quasi-compact morphism locally of finite
presentation. -/
theorem isLocallyConstructible_of_surjective_finitePresentation
    {X Y : Scheme.{u}} (g : X ⟶ Y) [Surjective g]
    [LocallyOfFinitePresentation g] [QuasiCompact g] {C : Set Y}
    (hC : IsLocallyConstructible (g ⁻¹' C)) : IsLocallyConstructible C := by
  simpa only [Set.image_preimage_eq _ g.surjective] using g.isLocallyConstructible_image hC

/-- To check that a subset of the source of `f : X ⟶ Y` with `Y` affine is locally
constructible it suffices to check it after base change along affine morphisms locally of finite
presentation realizing the members of a finite constructible cover of `Y`. -/
private theorem isLocallyConstructible_of_finitePresentation_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    {ι : Type*} [Finite ι] (C : ι → Set Y)
    (hC : ∀ i, IsConstructible (C i)) (hcover : ⋃ i, C i = Set.univ)
    {E : Set X}
    (hE : ∀ (V : Scheme.{u}) [IsAffine V] (g : V ⟶ Y),
      LocallyOfFinitePresentation g →
      (∃ i, Set.range g = C i) →
      IsLocallyConstructible (pullback.fst f g ⁻¹' E)) :
    IsLocallyConstructible E := by
  classical
  choose V hV g hfp hrange using fun i => exists_affine_finitePresentation_range (hC i)
  have hpart (i : ι) : IsLocallyConstructible (E ∩ f ⁻¹' C i) := by
    let := hV i
    let := hfp i
    have : QuasiCompact (g i) := inferInstance
    have himage := (pullback.fst f (g i)).isLocallyConstructible_image
      (hE (V i) (g i) (hfp i) ⟨i, hrange i⟩)
    rwa [Set.image_preimage_eq_inter_range, AlgebraicGeometry.Scheme.Pullback.range_fst,
      hrange i] at himage
  have hdecomp : E = ⋃ i, E ∩ f ⁻¹' C i := by
    simp only [← Set.inter_iUnion, ← Set.preimage_iUnion, hcover,
      Set.preimage_univ, Set.inter_univ]
  rw [hdecomp]
  exact IsLocallyConstructible.iUnion hpart

/-- A morphism whose residue field map at a point is an isomorphism has separable residue degree
one at that point. -/
theorem finSepDegree_eq_one_of_isIso_residueFieldMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (hres : IsIso (f.residueFieldMap x)) :
    let : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Field.finSepDegree (Y.residueField (f x)) (X.residueField x) = 1 := by
  let K := Y.residueField (f x)
  let L := X.residueField x
  let : Algebra K L := (f.residueFieldMap x).hom.toAlgebra
  let e : L ≃+* K := (asIso (f.residueFieldMap x)).symm.commRingCatIsoToRingEquiv
  have hRing : e.toRingHom.comp (algebraMap K L) = RingHom.id K := by
    change ((asIso (f.residueFieldMap x)).inv.hom).comp
      (f.residueFieldMap x).hom = RingHom.id K
    exact congrArg CommRingCat.Hom.hom (Iso.hom_inv_id (asIso (f.residueFieldMap x)))
  let ae : L ≃ₐ[K] K := AlgEquiv.ofRingEquiv (f := e) (fun a => DFunLike.congr_fun hRing a)
  simpa [K, L, Field.finSepDegree_self] using (Field.finSepDegree_eq_of_equiv K L K ae)

/-- A section `s` of `p` satisfies `p (s y) = y`. -/
private theorem apply_section_of_comp_eq_id
    {Y Z : Scheme.{u}} (s : Y ⟶ Z) (p : Z ⟶ Y) (hs : s ≫ p = 𝟙 Y) (y : Y) : p (s y) = y := by
  simpa using congrArg (fun g : Y ⟶ Y => g y) hs

/-- A section of a morphism induces an isomorphism on residue fields. -/
private theorem isIso_residueFieldMap_of_section
    {Y Z : Scheme.{u}} (s : Y ⟶ Z) (p : Z ⟶ Y) (hs : s ≫ p = 𝟙 Y) (y : Y) :
    IsIso (s.residueFieldMap y) := by
  refine (ConcreteCategory.isIso_iff_bijective (s.residueFieldMap y)).2 ?_
  constructor
  · exact RingHom.injective _
  · intro a
    have hp := apply_section_of_comp_eq_id s p hs y
    let e := Y.residueFieldCongr hp
    have h' : p.residueFieldMap (s y) ≫ s.residueFieldMap y = e.hom := by
      have h := Scheme.Hom.residueFieldMap_congr hs y
      rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_id] at h
      change p.residueFieldMap (s y) ≫ s.residueFieldMap y = e.hom at h
      exact h
    refine ⟨p.residueFieldMap (s y) (e.inv a), ?_⟩
    calc
      s.residueFieldMap y (p.residueFieldMap (s y) (e.inv a)) = e.hom (e.inv a) :=
        congrArg (fun k : Y.residueField (p (s y)) ⟶ Y.residueField y => k (e.inv a)) h'
      _ = a := e.inv_hom_id_apply a

/-- A weighting of a morphism which factors as an immersion followed by a finite morphism that is
a homeomorphism, with trivial residue field extensions, is locally constant. -/
private theorem isLocallyConstant_of_isImmersion_of_isFinite_of_isHomeomorph
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y)
    [IsImmersion j] [IsFinite p] (hp : IsHomeomorph p)
    {w : X → ℤ} (hw : IsWeighting (j ≫ p) w)
    (hres : ∀ x, IsIso ((j ≫ p).residueFieldMap x)) : IsLocallyConstant w := by
  let O := j.coborderRange
  let V : Y.Opens := ⟨p '' (O : Set Z), hp.isOpenMap _ O.isOpen⟩
  have hOV : O ≤ p ⁻¹ᵁ V := fun z hz => ⟨z, hz, rfl⟩
  let q : O.toScheme ⟶ V.toScheme := p.resLE V O hOV
  have hsq : IsPullback O.ι q p V.ι := by
    apply (IsOpenImmersion.isPullback q O.ι V.ι p ?_ ?_).flip
    · simp [q]
    · simp only [Scheme.Opens.opensRange_ι]
      ext z
      change p z ∈ p '' (O : Set Z) ↔ z ∈ O
      symm
      exact ⟨fun hz => ⟨z, hz, rfl⟩, fun ⟨z', hz', heq⟩ => hp.injective heq ▸ hz'⟩
  have : IsFinite q := MorphismProperty.of_isPullback hsq inferInstance
  let k := j.liftCoborder ≫ q
  have hk : k ≫ V.ι = j ≫ p := by simp [k, q, O]
  have hbase : IsPullback (𝟙 X) k (j ≫ p) V.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hk.symm⟩
  have hwk : IsWeighting k w := IsWeighting.comp_of_isPullback hw hbase
  apply isLocallyConstant_of_isFinite_of_injective_of_finSepDegree_eq_one hwk
  · intro x x' hxx'
    apply j.isEmbedding.injective
    apply hp.injective
    simpa only [← Scheme.Hom.comp_apply, hk] using congrArg V.ι hxx'
  · intro x
    apply finSepDegree_eq_one_of_isIso_residueFieldMap k x
    have : IsIso ((k ≫ V.ι).residueFieldMap x) := by
      rw [hk]
      exact hres x
    have : IsIso (V.ι.residueFieldMap (k x) ≫ k.residueFieldMap x) := by
      rwa [Scheme.residueFieldMap_comp] at this
    exact IsIso.of_isIso_comp_left (V.ι.residueFieldMap (k x)) (k.residueFieldMap x)

/-- The base change of a section of `p : Z ⟶ Y` along `g : V ⟶ Y`, as a section of the projection
`pullback.snd p g`. -/
private noncomputable def sectionBaseChange
    {Y Z V : Scheme.{u}} (p : Z ⟶ Y) (g : V ⟶ Y) (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y) :
    V ⟶ pullback p g :=
  pullback.lift (g ≫ s) (𝟙 V) (by simp [Category.assoc, hs])

private theorem sectionBaseChange_fst
    {Y Z V : Scheme.{u}} (p : Z ⟶ Y) (g : V ⟶ Y) (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y) :
    sectionBaseChange p g s hs ≫ pullback.fst p g = g ≫ s :=
  pullback.lift_fst _ _ _

private theorem sectionBaseChange_snd
    {Y Z V : Scheme.{u}} (p : Z ⟶ Y) (g : V ⟶ Y) (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y) :
    sectionBaseChange p g s hs ≫ pullback.snd p g = 𝟙 V :=
  pullback.lift_snd _ _ _

private theorem isPullback_sectionBaseChange
    {Y Z V : Scheme.{u}} (p : Z ⟶ Y) (g : V ⟶ Y) (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y) :
    IsPullback g (sectionBaseChange p g s hs) s (pullback.fst p g) := by
  have hfst (c : PullbackCone s (pullback.fst p g)) :
      (c.snd ≫ pullback.snd p g) ≫ g = c.fst := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← c.condition,
      Category.assoc, hs, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (sectionBaseChange_fst p g s hs).symm
    (fun c => c.snd ≫ pullback.snd p g) hfst ?_ ?_)
  · intro c
    apply pullback.hom_ext
    · rw [Category.assoc, sectionBaseChange_fst, ← Category.assoc, hfst]
      exact c.condition
    · simp [Category.assoc, sectionBaseChange_snd]
  · intro c m _ hm
    rw [← hm]
    simp [Category.assoc, sectionBaseChange_snd]

private theorem range_sectionBaseChange
    {Y Z V : Scheme.{u}} (p : Z ⟶ Y) (g : V ⟶ Y) (s : Y ⟶ Z) (hs : s ≫ p = 𝟙 Y) :
    Set.range (sectionBaseChange p g s hs) = pullback.fst p g ⁻¹' Set.range s := by
  simpa using Scheme.image_preimage_eq_of_isPullback
    (isPullback_sectionBaseChange p g s hs) Set.univ

/-- A member of a finite closed cover whose members are pairwise either equal or disjoint is
open and closed. -/
private theorem isClopen_of_finite_closed_cover_eq_or_disjoint
    {α ι : Type*} [TopologicalSpace α] [Finite ι] (C : ι → Set α)
    (hC : ∀ i, IsClosed (C i)) (hcover : ⋃ i, C i = Set.univ)
    (hpair : ∀ i j, C i = C j ∨ Disjoint (C i) (C j)) (i : ι) : IsClopen (C i) := by
  have hcompl : (C i)ᶜ = ⋃ j : {j // Disjoint (C i) (C j)}, C j.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
      have hd : Disjoint (C i) (C j) := (hpair i j).resolve_left (fun heq => hx (heq ▸ hj))
      exact Set.mem_iUnion.mpr ⟨⟨j, hd⟩, hj⟩
    · rintro hx hxi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp j.2 hxi hj
  refine ⟨hC i, ?_⟩
  have hclosed : IsClosed (C i)ᶜ := by
    rw [hcompl]
    exact isClosed_iUnion_of_finite fun j => hC j.1
  simpa using hclosed.isOpen_compl

/-- A weighting of a morphism which factors as an immersion into a scheme covered by the clopen
ranges of sections of a finite morphism is locally constant. -/
private theorem isLocallyConstant_of_clopen_sections
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y)
    [IsImmersion j] [IsFinite p]
    {ι : Type*} (s : ι → (Y ⟶ Z)) (hs : ∀ i, s i ≫ p = 𝟙 Y)
    (hclopen : ∀ i, IsClopen (Set.range (s i)))
    (hcover : ∀ z : Z, ∃ i, z ∈ Set.range (s i))
    {w : X → ℤ} (hw : IsWeighting (j ≫ p) w) :
    IsLocallyConstant w := by
  let O (i : ι) : Z.Opens := ⟨Set.range (s i), (hclopen i).isOpen⟩
  have hlocal (i : ι) : IsLocallyConstant (w ∘ (j ⁻¹ᵁ O i).ι) := by
    have : IsClosedImmersion (O i).ι :=
      IsClosedImmersion.of_isPreimmersion _ (by
        rw [Scheme.Opens.range_ι]
        change IsClosed (Set.range (s i))
        exact (hclopen i).isClosed)
    let q := (O i).ι ≫ p
    have hbij : Function.Bijective q := by
      constructor
      · rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
        obtain ⟨y, rfl⟩ := hz
        obtain ⟨y', rfl⟩ := hz'
        apply Subtype.ext
        change p (s i y) = p (s i y') at h
        rw [← apply_section_of_comp_eq_id (s i) p (hs i) y, h,
          apply_section_of_comp_eq_id (s i) p (hs i) y']
      · intro y
        refine ⟨⟨s i y, ⟨y, rfl⟩⟩, ?_⟩
        exact apply_section_of_comp_eq_id (s i) p (hs i) y
    have hq : IsHomeomorph q :=
      isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
        ⟨q.continuous, q.isClosedMap, hbij⟩
    have hcomp : (j ∣_ O i) ≫ q = (j ⁻¹ᵁ O i).ι ≫ (j ≫ p) := by
      simp only [q, ← Category.assoc, morphismRestrict_ι]
    have hwi : IsWeighting ((j ∣_ O i) ≫ q) (w ∘ (j ⁻¹ᵁ O i).ι) := by
      rw [hcomp]
      exact IsWeighting.comp_isOpenImmersion _ hw
    apply isLocallyConstant_of_isImmersion_of_isFinite_of_isHomeomorph (j ∣_ O i) q hq hwi
    intro x
    have hqres (z : (O i).toScheme) : IsIso (q.residueFieldMap z) := by
      obtain ⟨y, hy⟩ := z.2
      have hp : IsIso (p.residueFieldMap z.1) := by
        rw [← hy]
        exact isIso_residueFieldMap_of_mem_range_section p (s i) (hs i) y
      rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' hp (isIso_residueFieldMap_of_isPreimmersion (O i).ι z)
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (hqres _)
      (isIso_residueFieldMap_of_isPreimmersion (j ∣_ O i) x)
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨i, hi⟩ := hcover (j x)
  let x' : (j ⁻¹ᵁ O i).toScheme := ⟨x, hi⟩
  obtain ⟨U, hU, hxU, hc⟩ := (hlocal i).exists_open x'
  refine ⟨(j ⁻¹ᵁ O i).ι '' U, (j ⁻¹ᵁ O i).ι.isOpenMap U hU, ⟨x', hxU, rfl⟩, ?_⟩
  rintro y ⟨y', hy', rfl⟩
  exact hc y' hy'

/-- The morphism between base changes induced by a factorization `j ≫ p`. -/
noncomputable def baseChangeFactor
    {X Z Y V : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y) (g : V ⟶ Y) :
    pullback (j ≫ p) g ⟶ pullback p g :=
  pullback.lift (pullback.fst (j ≫ p) g ≫ j) (pullback.snd (j ≫ p) g)
    (by rw [Category.assoc, pullback.condition])

private theorem baseChangeFactor_fst
    {X Z Y V : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y) (g : V ⟶ Y) :
    baseChangeFactor j p g ≫ pullback.fst p g = pullback.fst (j ≫ p) g ≫ j :=
  pullback.lift_fst _ _ _

/-- The morphism between base changes induced by a factorization is compatible with the
projections to the base. -/
theorem baseChangeFactor_snd
    {X Z Y V : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y) (g : V ⟶ Y) :
    baseChangeFactor j p g ≫ pullback.snd p g = pullback.snd (j ≫ p) g :=
  pullback.lift_snd _ _ _

/-- The morphism between base changes induced by a factorization `j ≫ p` is itself a base
change of `j`, along the first projection of `pullback p g`. -/
theorem isPullback_baseChangeFactor
    {X Z Y V : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y) (g : V ⟶ Y) :
    IsPullback (pullback.fst (j ≫ p) g) (baseChangeFactor j p g) j (pullback.fst p g) := by
  have H : IsPullback (baseChangeFactor j p g ≫ pullback.snd p g)
      (pullback.fst (j ≫ p) g) g (j ≫ p) := by
    rw [baseChangeFactor_snd]
    exact (IsPullback.of_hasPullback (j ≫ p) g).flip
  exact (H.of_right (baseChangeFactor_fst j p g) (IsPullback.of_hasPullback p g).flip).flip

private instance isImmersion_baseChangeFactor
    {X Z Y V : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y) (g : V ⟶ Y) [IsImmersion j] :
    IsImmersion (baseChangeFactor j p g) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeFactor j p g) inferInstance

/-- A weighting of `j ≫ p` pulls back to a weighting of `baseChangeFactor j p g ≫ pullback.snd p g`.
-/
private theorem isWeighting_baseChangeFactor_snd
    {X Z Y V : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y) (g : V ⟶ Y)
    [LocallyOfFiniteType (j ≫ p)] [LocallyQuasiFinite (j ≫ p)] {w : X → ℤ}
    (hw : IsWeighting (j ≫ p) w) :
    IsWeighting (baseChangeFactor j p g ≫ pullback.snd p g) (w ∘ pullback.fst (j ≫ p) g) := by
  rw [baseChangeFactor_snd]
  exact IsWeighting.comp_of_isPullback hw (IsPullback.of_hasPullback (j ≫ p) g)

/-- Over a base on which the finitely many sections of `p` have pairwise prescribed incidence,
the base-changed sections have clopen ranges. -/
private theorem isClopen_range_sectionBaseChange
    {Y Z V : Scheme.{u}} (p : Z ⟶ Y) (g : V ⟶ Y)
    {ι : Type*} [Finite ι] (s : ι → (Y ⟶ Z))
    (hs : ∀ i, s i ≫ p = 𝟙 Y) (hc : ∀ i, IsClosedImmersion (s i))
    (hcover : ∀ z : Z, ∃ i, z ∈ Set.range (s i))
    (b : ι × ι → Bool)
    (hb : ∀ y : V, ∀ i j, (s i (g y) ∈ Set.range (s j)) ↔ b (i, j) = true) :
    ∀ i, IsClopen (Set.range (sectionBaseChange p g (s i) (hs i))) := by
  let t i := sectionBaseChange p g (s i) (hs i)
  have ht (i : ι) : t i ≫ pullback.snd p g = 𝟙 V := sectionBaseChange_snd _ _ _ _
  have htrange (i : ι) : Set.range (t i) = pullback.fst p g ⁻¹' Set.range (s i) :=
    range_sectionBaseChange _ _ _ _
  have htc (i : ι) : IsClosed (Set.range (t i)) := by
    have := hc i
    rw [htrange]
    exact (s i).isClosedEmbedding.isClosed_range.preimage (pullback.fst p g).continuous
  have htcov : ⋃ i, Set.range (t i) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := hcover (pullback.fst p g z)
    exact ⟨i, (htrange i).symm ▸ hi⟩
  have huniq (i j : ι) (y y' : V) (h : t i y = t j y') : y = y' := by
    rw [← apply_section_of_comp_eq_id (t i) _ (ht i) y, h,
      apply_section_of_comp_eq_id (t j) _ (ht j) y']
  have hcollision (i j : ι) (y : V) : t i y = t j y ↔ b (i, j) = true := by
    have hmem : t i y ∈ Set.range (t j) ↔ s i (g y) ∈ Set.range (s j) := by
      rw [htrange]
      change pullback.fst p g (t i y) ∈ Set.range (s j) ↔ _
      rw [← Scheme.Hom.comp_apply, sectionBaseChange_fst]
      rfl
    rw [← hb y i j, ← hmem]
    refine ⟨fun h => ⟨y, h.symm⟩, ?_⟩
    rintro ⟨y', h⟩
    obtain rfl := huniq i j y y' h.symm
    exact h.symm
  apply isClopen_of_finite_closed_cover_eq_or_disjoint _ htc htcov
  intro i j
  by_cases hij : b (i, j) = true
  · exact Or.inl (congrArg Set.range (funext fun y => (hcollision i j y).mpr hij))
  · right
    rw [Set.disjoint_left]
    rintro z ⟨y, rfl⟩ ⟨y', hy'⟩
    obtain rfl := huniq i j y y' hy'.symm
    exact hij ((hcollision i j y).mp hy'.symm)

/-- The level sets of a weighting of `j ≫ p` are locally constructible when `Y` is affine and
`p` is a finite morphism covered set-theoretically by finitely many closed sections. -/
private theorem isLocallyConstructible_weighting_levelSet_of_finite_sections
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y)
    [IsAffine Y] [IsImmersion j] [IsFinite p]
    {ι : Type*} [Finite ι] (s : ι → (Y ⟶ Z))
    (hs : ∀ i, s i ≫ p = 𝟙 Y) (hc : ∀ i, IsClosedImmersion (s i))
    (hcover : ∀ z : Z, ∃ i, z ∈ Set.range (s i))
    {w : X → ℤ} (hw : IsWeighting (j ≫ p) w) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} := by
  have : IsAffine Z := isAffine_of_isAffineHom p
  have hfp (i : ι) : LocallyOfFinitePresentation (s i) := by
    have : LocallyOfFinitePresentation (s i ≫ p) := by rw [hs]; infer_instance
    exact AlgebraicGeometry.locallyOfFinitePresentation_of_comp (s i) p
  let C (a : ι × ι) : Set Y := s a.1 ⁻¹' Set.range (s a.2)
  have hC (a : ι × ι) : IsConstructible (C a) := by
    have := hc a.2
    have := hfp a.2
    apply (s a.1).isConstructible_preimage
    simpa using (s a.2).isConstructible_image IsConstructible.univ
  apply isLocallyConstructible_of_finitePresentation_cover (j ≫ p)
    (membershipPattern C) (isConstructible_membershipPattern C hC)
    (membershipPattern_iUnion_eq_univ C)
  intro V _ g hg hgb
  obtain ⟨b, hb⟩ := hgb
  let t i := sectionBaseChange p g (s i) (hs i)
  have ht (i : ι) : t i ≫ pullback.snd p g = 𝟙 V := sectionBaseChange_snd _ _ _ _
  have htclopen : ∀ i, IsClopen (Set.range (t i)) :=
    isClopen_range_sectionBaseChange p g s hs hc hcover b (by
      intro y i k
      have hy : g y ∈ membershipPattern C b := hb ▸ Set.mem_range_self y
      exact hy (i, k))
  have htcover : ∀ z : ↥(pullback p g), ∃ i, z ∈ Set.range (t i) := by
    intro z
    obtain ⟨i, hi⟩ := hcover (pullback.fst p g z)
    refine ⟨i, ?_⟩
    rwa [range_sectionBaseChange]
  exact isLocallyConstructible_levelSet
    (isLocallyConstant_of_clopen_sections (baseChangeFactor j p g)
      (pullback.snd p g) t ht htclopen htcover (isWeighting_baseChangeFactor_snd j p g hw)) n

/-- The level sets of a weighting of a morphism to an affine scheme that factors as an immersion
followed by a finite morphism are locally constructible. -/
private theorem isLocallyConstructible_weighting_levelSet_of_isImmersion_isFinite
    {X T Y : Scheme.{u}} (j : X ⟶ T) (p : T ⟶ Y)
    [IsAffine Y] [IsImmersion j] [IsFinite p]
    {w : X → ℤ} (hw : IsWeighting (j ≫ p) w) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} := by
  obtain ⟨V, g, hgs, hgf, _, _, Z, q, i, hi, hiq, hqf, m, s, hs, hcov⟩ :=
    Stacks.Morphisms.exists_finiteLocallyFree_cover_closedImmersion p
  have := hgs
  obtain ⟨hgfin, _, hgfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp hgf
  have := hgfin
  have := hgfp
  have : IsAffine V := isAffine_of_isAffineHom g
  have := hi
  obtain ⟨hqfin, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation q).mp hqf
  have := hqfin
  have hw' : IsWeighting ((baseChangeFactor j p g ≫ i) ≫ q)
      (w ∘ pullback.fst (j ≫ p) g) := by
    rw [Category.assoc, hiq]
    exact isWeighting_baseChangeFactor_snd j p g hw
  exact isLocallyConstructible_of_surjective_finitePresentation (pullback.fst (j ≫ p) g)
    (isLocallyConstructible_weighting_levelSet_of_finite_sections
      (baseChangeFactor j p g ≫ i) q s (fun k => (hs k).2) (fun k => (hs k).1)
      (fun z => by
        obtain ⟨k, y, hy⟩ := hcov z
        exact ⟨k, y, hy⟩) hw' n)

/-- The affine case of the constructibility of the level sets of a weighting. -/
private theorem isLocallyConstructible_weighting_levelSet_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    {w : X → ℤ} (hw : IsWeighting f w) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} := by
  obtain ⟨T, j, p, hj, _, hp, heq⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization f
  have := hj
  have := hp
  apply isLocallyConstructible_weighting_levelSet_of_isImmersion_isFinite j p
  rwa [← heq]

/-- **Stacks Project, Tag 0F3G.** The level sets of a weighting of a locally quasi-finite
morphism are locally constructible in the source.

Quasi-finiteness being local, the hypothesis is `AlgebraicGeometry.LocallyQuasiFinite` together
with `AlgebraicGeometry.LocallyOfFiniteType`, which is Stacks 01TD's pointwise characterization
of a locally quasi-finite morphism. -/
@[stacks 0F3G]
theorem isLocallyConstructible_weighting_levelSet
    {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    {w : X → ℤ} (hw : IsWeighting f w) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := f ⁻¹ᵁ U) hxU
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let k := f.resLE U V hVU
  have hcomp : k ≫ U.ι = V.ι ≫ f := f.resLE_comp_ι hVU
  have hsq : IsPullback (𝟙 V.toScheme) k (V.ι ≫ f) U.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hcomp.symm⟩
  have hwk : IsWeighting k (w ∘ V.ι) :=
    IsWeighting.comp_of_isPullback (IsWeighting.comp_isOpenImmersion V.ι hw) hsq
  have : LocallyOfFiniteType k := MorphismProperty.of_isPullback hsq inferInstance
  have : LocallyQuasiFinite k := MorphismProperty.of_isPullback hsq inferInstance
  exact ⟨V, V.isOpen.mem_nhds hxV, V.isOpen,
    (isLocallyConstructible_weighting_levelSet_of_isAffine hwk n).isConstructible⟩

end AlgebraicGeometry

end
