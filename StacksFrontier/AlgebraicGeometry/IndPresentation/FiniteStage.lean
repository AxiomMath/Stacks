module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Tower
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.TowerResidue
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples

/-!
# Universal homeomorphisms at a finite stage

A finite-type algebra which is presented as a filtered colimit of finitely presented algebras
with surjective transition maps is already a universal homeomorphism over the base at every
sufficiently late stage.  The same assertion holds with the additional requirement that the
canonical maps on residue fields are isomorphisms.

## Main results

* `AlgebraicGeometry.eventually_universalHomeomorphism_of_isColimit` gives the universal
  homeomorphism assertion.
* `AlgebraicGeometry.eventually_universalHomeomorphism_and_isIso_residueFieldMap_of_isColimit`
  gives the assertion including the residue-field condition.

## Implementation notes

The filtered system is a diagram of commutative `A`-algebras.  Its specified colimit cocone has
apex `B'`, so the structure maps to `B'` are retained.  "For all sufficiently large indices"
means that there is an index `i` such that the conclusion holds at every `j` equipped with a
morphism `i ⟶ j`.

The two statements are read off the two halves of a single induction, kept private in
`AlgebraicGeometry.FilteredStage`, which runs over the finite elementary towers of Tag 0CNE and
Tag 0CND:  a finite subset of the apex is captured at some stage, the elementary square-cube and
prime-power relations witnessing its tower are themselves captured at a later stage, and from
there on the stage satisfies the same characterization as the apex.  The surjectivity hypothesis
on the transition maps is what makes the kernel of each structure map to the apex consist of
nilpotents, which is the input to the universal-homeomorphism criterion of Tag 04DF.

The characterizations consumed here are the library's:
`AlgebraicGeometry.universalHomeomorphism_spec_iff_finite_adjoin_tower` (Tag 0CNE) and
`AlgebraicGeometry.universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube`
(Tag 0CND).

No `@[stacks]` tag is attached here.  These two statements are an auxiliary input to Tag 0EUJ,
not an assertion of it; the tag is placed where Tag 0EUJ's own statements are proved.

## References

* [Stacks Project, Tag 0CNE](https://stacks.math.columbia.edu/tag/0CNE)
* [Stacks Project, Tag 0CND](https://stacks.math.columbia.edu/tag/0CND)
* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace AlgebraicGeometry

namespace FilteredStage


private abbrev algebraCoconeRange {R : Type u} [CommRing R] {J : Type v}
    [Category.{w} J] {F : J ⥤ CommAlgCat.{u} R} (c : Cocone F) (j : J) :
    Subalgebra R (c.pt : Type u) := (c.ι.app j).hom.range

private theorem directed_algebraCoconeRange {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] [IsFilteredOrEmpty J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) : Directed (· ≤ ·) (algebraCoconeRange c) := by
  have hle : ∀ {i j : J}, (i ⟶ j) → algebraCoconeRange c i ≤ algebraCoconeRange c j := by
    rintro i j f y ⟨a, rfl⟩
    exact ⟨(F.map f).hom a, ConcreteCategory.congr_hom (c.w f) a⟩
  exact fun i j => ⟨IsFiltered.max i j, hle (IsFiltered.leftToMax i j),
    hle (IsFiltered.rightToMax i j)⟩

private theorem iSup_algebraCoconeRange_eq_top {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) (hc : IsColimit c) : ⨆ j, algebraCoconeRange c j = ⊤ := by
  set T := ⨆ j, algebraCoconeRange c j
  have hmem (j : J) (y : (F.obj j : Type u)) : (c.ι.app j).hom y ∈ T :=
    le_iSup (algebraCoconeRange c) j ⟨y, rfl⟩
  let d : Cocone F :=
    { pt := CommAlgCat.of R T
      ι.app j := CommAlgCat.ofHom ((c.ι.app j).hom.codRestrict T (hmem j))
      ι.naturality i j f := by
        apply CommAlgCat.hom_ext
        ext a
        exact Subtype.ext (ConcreteCategory.congr_hom (c.w f) a) }
  have hid : hc.desc d ≫ CommAlgCat.ofHom T.val = 𝟙 _ := by
    refine hc.hom_ext fun j => ?_
    rw [← Category.assoc, hc.fac, Category.comp_id]
    apply CommAlgCat.hom_ext
    ext a
    rfl
  refine eq_top_iff.2 fun x _ => ?_
  have h : T.val ((hc.desc d).hom x) = x := ConcreteCategory.congr_hom hid x
  exact h ▸ ((hc.desc d).hom x).property

private theorem exists_algebraCocone_rep {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] [IsFiltered J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) (hc : IsColimit c) (x : (c.pt : Type u)) :
    ∃ j : J, ∃ y : (F.obj j : Type u), (c.ι.app j).hom y = x := by
  have : Nonempty J := IsFiltered.nonempty
  have hx : x ∈ (↑(⨆ j, algebraCoconeRange c j) : Set (c.pt : Type u)) := by
    rw [iSup_algebraCoconeRange_eq_top c hc]
    trivial
  rw [Subalgebra.coe_iSup_of_directed (directed_algebraCoconeRange c)] at hx
  obtain ⟨_, ⟨j, rfl⟩, y, hy⟩ := hx
  exact ⟨j, y, hy⟩

private theorem exists_common_successor {J : Type v} [Category.{w} J] [IsFiltered J]
    (s : Finset J) : ∃ j : J, ∀ i ∈ s, Nonempty (i ⟶ j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
      exact ⟨j, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs i j
      refine ⟨k, ?_⟩
      intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ⟨f⟩
      · obtain ⟨h⟩ := hj x hx
        exact ⟨h ≫ g⟩

private lemma eventually_eq_zero
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    {i : I} (x : B.obj i) (hx : ι.app i x = 0) :
    ∃ (j : I) (f : i ⟶ j), B.map f x = 0 := by
  classical
  let J := CategoryTheory.Under i
  let D : J ⥤ CategoryTheory.Under (B.obj i) := CategoryTheory.Under.post B
  let c := (Cocone.mk (CommAlgCat.of A B') ι).underPost i
  have hc : IsColimit c := hcol.underPost i
  let init : J := CategoryTheory.Under.mk (𝟙 i)
  let toJ : ∀ j : J, init ⟶ j := fun j => CategoryTheory.Under.homMk j.hom
  let fstage (j : J) : B.obj i →ₐ[A] B.obj j.right := (D.obj j).hom.hom
  let K : Ideal (B.obj i) := ⨆ j : J, RingHom.ker (fstage j).toRingHom
  have hcomp {j k : J} (f : j ⟶ k) : (B.map f.right).hom.comp (fstage j) = fstage k := by
    ext y
    have h := congrArg B.map (CategoryTheory.Under.w f).symm
    rw [Functor.map_comp] at h
    exact (ConcreteCategory.congr_hom h y).symm
  have hdir : Directed (· ≤ ·) (fun j : J => RingHom.ker (fstage j).toRingHom) := by
    intro j k
    obtain ⟨l, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j k
    have hle {m : J} (h : m ⟶ l) : RingHom.ker (fstage m).toRingHom ≤
        RingHom.ker (fstage l).toRingHom := fun z hz => by
      have hz' : fstage m z = 0 := hz
      refine RingHom.mem_ker.mpr ?_
      change fstage l z = 0
      rw [← hcomp h, AlgHom.comp_apply, hz', map_zero]
    exact ⟨l, hle f, hle g⟩
  let : Nonempty J := ⟨init⟩
  have hK_mem {z : B.obj i} (hz : z ∈ K) :
      ∃ j : J, z ∈ RingHom.ker (fstage j).toRingHom :=
    (Submodule.mem_iSup_of_directed _ hdir).mp hz
  let Q := (B.obj i) ⧸ K
  let q : B.obj i →ₐ[A] Q := Ideal.Quotient.mkₐ A K
  have hker (j : J) : RingHom.ker (fstage j).toRingHom ≤ RingHom.ker q.toRingHom := by
    intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply le_iSup (fun k : J => RingHom.ker (fstage k).toRingHom) j
    exact RingHom.mem_ker.mp hz
  let qmap : ∀ j : J, B.obj j.right →ₐ[A] Q := fun j =>
    AlgHom.liftOfSurjective (fstage j) (hsurj j.hom) q (hker j)
  let d : Cocone D := {
    pt := CategoryTheory.Under.mk (CommAlgCat.ofHom q)
    ι.app j := CategoryTheory.Under.homMk (CommAlgCat.ofHom (qmap j)) (by
      apply CommAlgCat.hom_ext
      ext z
      exact AlgHom.liftOfSurjective_apply (fstage j) (hsurj j.hom) q (hker j) z)
    ι.naturality := by
      intro j k f
      apply CategoryTheory.CommaMorphism.ext
      · exact Subsingleton.elim _ _
      · apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro z
        obtain ⟨w, rfl⟩ := hsurj j.hom z
        change qmap k ((B.map f.right).hom ((fstage j) w)) = qmap j ((fstage j) w)
        have harg : (B.map f.right).hom ((fstage j) w) = fstage k w := by
          rw [← AlgHom.comp_apply, hcomp f]
        rw [harg]
        exact (AlgHom.liftOfSurjective_apply (fstage k)
          (hsurj k.hom) q (hker k) w).trans
          (AlgHom.liftOfSurjective_apply (fstage j) (hsurj j.hom) q (hker j) w).symm }
  have hinit : fstage init = AlgHom.id A (B.obj i) := by
    ext y
    change (B.map (𝟙 i)).hom y = y
    simp
  have hqmap : qmap init = q := by
    apply AlgHom.ext
    intro y
    have hy := AlgHom.liftOfSurjective_apply (fstage init) (hsurj init.hom)
      q (hker init) y
    simpa [qmap, hinit] using hy
  have hfac := hc.fac d init
  have hzero : q x = 0 := by
    have hfac' := congrArg CategoryTheory.Under.Hom.right hfac
    have hfacval := ConcreteCategory.congr_hom hfac' x
    have hx' : (c.ι.app init).right.hom x = 0 := by
      change (ι.app i).hom x = 0
      exact hx
    change (hc.desc d).right.hom ((c.ι.app init).right.hom x) = qmap init x at hfacval
    rw [hx', map_zero] at hfacval
    simpa [hqmap] using hfacval.symm
  obtain ⟨j, hxj⟩ := hK_mem (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  exact ⟨j.right, j.hom, by
    change fstage j x = 0
    exact RingHom.mem_ker.mp hxj⟩

private lemma exists_stage_killing_finset
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    {i : I} (s : Finset (B.obj i)) (hs : ∀ x ∈ s, (ι.app i).hom x = 0) :
    ∃ (j : I) (f : i ⟶ j), ∀ x ∈ s, (B.map f).hom x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨i, 𝟙 i, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨j, f, hkill⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
      have hzero : (ι.app j).hom ((B.map f).hom x) = 0 := by
        calc
          _ = (ι.app i).hom x := by
            exact ConcreteCategory.congr_hom (ι.naturality f) x
          _ = 0 := hs x (Finset.mem_insert_self x s)
      obtain ⟨k, g, hg⟩ := eventually_eq_zero B ι hcol hsurj
        ((B.map f).hom x) hzero
      refine ⟨k, f ≫ g, ?_⟩
      intro y hy
      rw [Functor.map_comp, CommAlgCat.comp_apply]
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hg
      · have h := hkill y hy
        change (B.map g).hom ((B.map f).hom y) = 0
        rw [h, map_zero]

private lemma exists_stage_surjective_to_apex
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B']
    [Algebra.FiniteType A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι)) :
    ∃ i : I, Function.Surjective (ι.app i).hom := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B')
  let T := { x : B' // x ∈ s }
  choose ix yx hyx using fun x : T => exists_algebraCocone_rep
    (Cocone.mk (CommAlgCat.of A B') ι) hcol x.1
  let stages : Finset I := Finset.univ.image ix
  obtain ⟨j, hj⟩ := exists_common_successor stages
  let fj : ∀ x : T, ix x ⟶ j := fun x =>
    Classical.choice (hj (ix x) (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩))
  have hgens : ∀ x ∈ s, x ∈ algebraCoconeRange (Cocone.mk (CommAlgCat.of A B') ι) j := by
    intro x hx
    let x' : T := ⟨x, hx⟩
    refine ⟨(B.map (fj x')).hom (yx x'), ?_⟩
    calc
      (ι.app j).hom ((B.map (fj x')).hom (yx x')) =
          (ι.app (ix x')).hom (yx x') := by
            exact ConcreteCategory.congr_hom (ι.naturality (fj x')) (yx x')
      _ = x := hyx x'
  have hadjoin : Algebra.adjoin A (s : Set B') ≤
      algebraCoconeRange (Cocone.mk (CommAlgCat.of A B') ι) j :=
    Algebra.adjoin_le_iff.mpr hgens
  refine ⟨j, ?_⟩
  intro z
  have hz : z ∈ algebraCoconeRange (Cocone.mk (CommAlgCat.of A B') ι) j := by
    apply hadjoin
    rw [hs]
    trivial
  exact hz

private lemma kernel_le_nilradical_of_universalHomeomorphism
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (h : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op)) :
    RingHom.ker f ≤ nilradical A := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) := by
    have hs := (universalHomeomorphism_iff_integral_universallyInjective_surjective
      (Scheme.Spec.map (CommRingCat.ofHom f).op)).mp h |>.2.2
    rw [surjective_iff] at hs
    exact fun p => by
      obtain ⟨q, hq⟩ := hs p
      refine ⟨q, ?_⟩
      exact hq
  intro x hx
  apply mem_nilradical.mpr
  rw [nilpotent_iff_mem_prime]
  intro p hp
  let p' : PrimeSpectrum A := ⟨p, hp⟩
  obtain ⟨q, hq⟩ := hsurj p'
  have hxq : f x ∈ q.asIdeal := by rw [RingHom.mem_ker.mp hx]; exact q.asIdeal.zero_mem
  have : x ∈ p := by
    have hcomap : Ideal.comap f q.asIdeal = p := congrArg PrimeSpectrum.asIdeal hq
    rw [← hcomap]
    exact Ideal.mem_comap.mpr hxq
  exact this

private lemma universalHomeomorphism_of_surjective_nil_kernel
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical A) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom f).op) := by
  let g := Scheme.Spec.map (CommRingCat.ofHom f).op
  have hint : IsIntegralHom g := by
    change IsIntegralHom (Spec.map (CommRingCat.ofHom f))
    rw [IsIntegralHom.SpecMap_iff]
    exact RingHom.isIntegral_of_surjective f hf
  have hclosed : IsClosedImmersion g := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom f))
    exact IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f) hf
  have hinj : UniversallyInjective g := by
    have : IsClosedImmersion g := hclosed
    infer_instance
  have hsurj : Surjective g := by
    refine ⟨fun p => ?_⟩
    change ∃ q : PrimeSpectrum B, PrimeSpectrum.comap f q = p
    have hrange : Set.range (PrimeSpectrum.comap f) =
      PrimeSpectrum.zeroLocus (RingHom.ker f) :=
      range_comap_of_surjective B f hf
    have hp : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker f) := by
      change RingHom.ker f ≤ p.asIdeal
      have : p.asIdeal.IsPrime := p.isPrime
      exact le_trans hker (nilradical_le_prime p.asIdeal)
    exact Set.mem_range.mp (hrange ▸ hp)
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective g).mpr
    ⟨hint, hinj, hsurj⟩

private lemma image_property_iff
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (hker : RingHom.ker (algebraMap A S) ≤ nilradical A) (r : Prop) :
    let C := (Algebra.ofId A S).range
    (UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op) ∧
      (r → ∀ x, IsIso ((Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap A S)).op).residueFieldMap x))) ↔
    (UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap C S)).op) ∧
      (r → ∀ x, IsIso ((Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap C S)).op).residueFieldMap x))) := by
  let C := (Algebra.ofId A S).range
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap C S)).op
  let g := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op
  have hsurj : Function.Surjective (algebraMap A C) := by
    rintro ⟨x, a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  have hker' : RingHom.ker (algebraMap A C) ≤ nilradical A := by
    intro a ha
    apply hker
    have H := congrArg (algebraMap C S) (RingHom.mem_ker.mp ha)
    exact RingHom.mem_ker.mpr (by simpa using H)
  have hg : UniversalHomeomorphism g :=
    universalHomeomorphism_of_surjective_nil_kernel _ hsurj hker'
  have : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (algebraMap A C)) hsurj
  have hcomp : f ≫ g = Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hUH : UniversalHomeomorphism (f ≫ g) ↔
      UniversalHomeomorphism f := by
    constructor
    · exact fun h => universalHomeomorphism_hasTwoOutOfThreeProperty.of_postcomp
        f g hg h
    · exact fun h => universalHomeomorphism_hasTwoOutOfThreeProperty.comp_mem
        f g h hg
  have hres (x : Spec (.of S)) :
      IsIso ((f ≫ g).residueFieldMap x) ↔ IsIso (f.residueFieldMap x) := by
    rw [Scheme.residueFieldMap_comp]
    exact @isIso_comp_left_iff _ _ _ _ _
      (g.residueFieldMap (f x)) (f.residueFieldMap x)
      (isIso_residueFieldMap_of_isClosedImmersion g (f x))
  change (_ ∧ (r → ∀ x, IsIso ((Scheme.Spec.map
    (CommRingCat.ofHom (algebraMap A S)).op).residueFieldMap x))) ↔ _
  rw [← hcomp, hUH]
  simp only [hres]
  rfl

private lemma fin_prefix_range {S : Type*} {n : ℕ} (b : Fin n → S) (i : Fin n) :
    Set.range (fun j : Fin i => b (Fin.castLE i.isLt.le j)) =
      Set.range (fun j : {j : Fin n // j < i} => b j) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨Fin.castLE i.isLt.le j, j.isLt⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.1.1, j.2⟩, rfl⟩

private lemma mem_adjoin_image_base_iff {A S : Type u} [CommRing A] [CommRing S]
    [Algebra A S] (s : Set S) (x : S) :
    x ∈ Algebra.adjoin (Algebra.ofId A S).range s ↔ x ∈ Algebra.adjoin A s := by
  change x ∈ (Algebra.adjoin (Algebra.ofId A S).range s).restrictScalars A ↔ _
  exact SetLike.ext_iff.mp (IsScalarTower.adjoin_range_toAlgHom A A S s) x

private def ElementaryRelation (A : Type u) [CommRing A] {S : Type u} [CommRing S]
    [Algebra A S] {n : ℕ} (b : Fin n → S) (p : Option ℕ) (k : Fin n) : Prop :=
  match p with
  | none => b k ^ 2 ∈ Algebra.adjoin A (Set.range fun q : {q : Fin n // q < k} => b q) ∧
      b k ^ 3 ∈ Algebra.adjoin A (Set.range fun q : {q : Fin n // q < k} => b q)
  | some p => p.Prime ∧
      (p : S) * b k ∈ Algebra.adjoin A (Set.range fun q : {q : Fin n // q < k} => b q) ∧
      b k ^ p ∈ Algebra.adjoin A (Set.range fun q : {q : Fin n // q < k} => b q)

private lemma exists_elementary_generators
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] [Algebra.FiniteType A S]
    (h : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op))
    (r : Prop) (hres : r → ∀ x, IsIso ((Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A S)).op).residueFieldMap x)) :
    ∃ (n : ℕ) (b : Fin n → S) (p : Fin n → Option ℕ),
      Algebra.adjoin A (Set.range b) = ⊤ ∧
      (∀ k, ElementaryRelation A b (p k) k) ∧ (r → ∀ k, p k = none) := by
  classical
  let C := (Algebra.ofId A S).range
  have hinj : Function.Injective (algebraMap C S) := Subtype.val_injective
  have hC := (image_property_iff (kernel_le_nilradical_of_universalHomeomorphism _ h) r).mp
    ⟨h, hres⟩
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := S)
  have generates {n : ℕ} (b : Fin n → S)
      (hb : (s : Set S) ⊆ Algebra.adjoin C (Set.range b)) :
      Algebra.adjoin A (Set.range b) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hs]
    apply Algebra.adjoin_le_iff.mpr
    exact fun x hx => (mem_adjoin_image_base_iff _ _).mp (hb hx)
  by_cases hr : r
  · obtain ⟨n, b, hb, hsteps⟩ :=
      (universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube
        hinj).mp ⟨hC.1, hC.2 hr⟩ s
    refine ⟨n, b, fun _ => none, generates b hb, ?_, by simp⟩
    intro k
    simpa only [ElementaryRelation, fin_prefix_range, C, mem_adjoin_image_base_iff] using hsteps k
  · obtain ⟨n, b, hb, hsteps⟩ :=
      (universalHomeomorphism_spec_iff_finite_adjoin_tower C S hinj).mp hC.1 s
    have H (k : Fin n) : ∃ p, ElementaryRelation A b p k := by
      rcases hsteps k with h | ⟨p, hp, h1, h2⟩
      · refine ⟨none, ?_⟩
        exact ⟨(mem_adjoin_image_base_iff _ _).mp h.1,
          (mem_adjoin_image_base_iff _ _).mp h.2⟩
      · exact ⟨some p, hp, (mem_adjoin_image_base_iff _ _).mp h1,
          (mem_adjoin_image_base_iff _ _).mp h2⟩
    choose p hp using H
    exact ⟨n, b, p, generates b hb, hp, fun h => (hr h).elim⟩

private lemma property_of_elementary_generators
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (hker : RingHom.ker (algebraMap A S) ≤ nilradical A)
    {n : ℕ} (b : Fin n → S) (p : Fin n → Option ℕ)
    (hg : Algebra.adjoin A (Set.range b) = ⊤)
    (hr : ∀ k, ElementaryRelation A b (p k) k)
    (r : Prop) (hp : r → ∀ k, p k = none) :
    UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op) ∧
      (r → ∀ x, IsIso ((Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap A S)).op).residueFieldMap x)) := by
  let C := (Algebra.ofId A S).range
  have hinj : Function.Injective (algebraMap C S) := Subtype.val_injective
  have hgen (E : Finset S) : (E : Set S) ⊆ Algebra.adjoin C (Set.range b) := by
    intro x hx
    apply (mem_adjoin_image_base_iff _ _).mpr
    rw [hg]
    trivial
  apply (image_property_iff hker r).mpr
  constructor
  · apply (universalHomeomorphism_spec_iff_finite_adjoin_tower C S hinj).mpr
    intro E
    refine ⟨n, b, hgen E, ?_⟩
    intro k
    have hk := hr k
    cases hpk : p k with
    | none =>
        rw [hpk] at hk
        exact Or.inl ⟨(mem_adjoin_image_base_iff _ _).mpr hk.1,
          (mem_adjoin_image_base_iff _ _).mpr hk.2⟩
    | some q =>
        rw [hpk] at hk
        exact Or.inr ⟨q, hk.1, (mem_adjoin_image_base_iff _ _).mpr hk.2.1,
          (mem_adjoin_image_base_iff _ _).mpr hk.2.2⟩
  · intro h
    apply ((universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube
      hinj).mpr ?_).2
    intro E
    refine ⟨n, b, hgen E, ?_⟩
    intro k
    have hk := hr k
    rw [hp h k] at hk
    simpa only [ElementaryRelation, fin_prefix_range, C, mem_adjoin_image_base_iff] using hk

private lemma map_mem_adjoin_range
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] {K : Type*}
    (f : S →ₐ[A] T) (b : K → S) {x : S}
    (hx : x ∈ Algebra.adjoin A (Set.range b)) :
    f x ∈ Algebra.adjoin A (Set.range fun k => f (b k)) := by
  change f x ∈ Algebra.adjoin A (Set.range (f ∘ b))
  rw [Set.range_comp, Algebra.adjoin_image]
  exact ⟨x, hx, rfl⟩

/-- Generators of the source of a surjective algebra map map to generators of the target. -/
private lemma adjoin_range_eq_top_of_surjective
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] {K : Type*} (φ : S →ₐ[A] T) (hφ : Function.Surjective φ)
    (c : K → T) (h : ∀ x, φ x ∈ Algebra.adjoin A (Set.range c)) :
    Algebra.adjoin A (Set.range c) = ⊤ :=
  eq_top_iff.mpr fun z _ => by
    obtain ⟨x, rfl⟩ := hφ z
    exact h x

private lemma elementaryRelation_map
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (f : S →ₐ[A] T)
    {n : ℕ} (b : Fin n → S) (p : Option ℕ) (k : Fin n)
    (h : ElementaryRelation A b p k) :
    ElementaryRelation A (fun k => f (b k)) p k := by
  cases p with
  | none =>
      exact ⟨by simpa only [map_pow] using
          map_mem_adjoin_range f (fun q : {q : Fin n // q < k} => b q) h.1,
        by simpa only [map_pow] using
          map_mem_adjoin_range f (fun q : {q : Fin n // q < k} => b q) h.2⟩
  | some p =>
      exact ⟨h.1, by simpa only [map_mul, map_natCast] using
          map_mem_adjoin_range f (fun q : {q : Fin n // q < k} => b q) h.2.1,
        by simpa only [map_pow] using
          map_mem_adjoin_range f (fun q : {q : Fin n // q < k} => b q) h.2.2⟩

private lemma exists_preimage_mem_adjoin
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] {K : Type*}
    (f : S →ₐ[A] T) (b : K → S) (b' : K → T) (hb : ∀ k, f (b k) = b' k)
    {x : T} (hx : x ∈ Algebra.adjoin A (Set.range b')) :
    ∃ y ∈ Algebra.adjoin A (Set.range b), f y = x := by
  have hr : Set.range b' = f '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext k
    exact (hb k).symm
  rw [hr, Algebra.adjoin_image] at hx
  exact hx

private lemma exists_stage_generators_and_relations
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    {i : I} [Algebra.FiniteType A (B.obj i)]
    (hi : Function.Surjective (ι.app i).hom)
    {n : ℕ} (b' : Fin n → B') (hg : Algebra.adjoin A (Set.range b') = ⊤)
    (c e : Fin n × Bool → ℕ)
    (hr : ∀ z, (c z : B') * b' z.1 ^ e z ∈ Algebra.adjoin A
      (Set.range fun q : {q : Fin n // q < z.1} => b' q)) :
    ∃ (j : I) (_f : i ⟶ j) (b : Fin n → B.obj j),
      Algebra.adjoin A (Set.range b) = ⊤ ∧
      ∀ z, (c z : B.obj j) * b z.1 ^ e z ∈ Algebra.adjoin A
        (Set.range fun q : {q : Fin n // q < z.1} => b q) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B.obj i)
  choose b hb using fun k : Fin n => hi (b' k)
  let ψ : B.obj i →ₐ[A] B' := (ι.app i).hom
  change ∀ k, ψ (b k) = b' k at hb
  have hg' (x : B') : x ∈ Algebra.adjoin A (Set.range b') := by rw [hg]; trivial
  choose genLift genMem genEq using fun x : {x : B.obj i // x ∈ s} =>
    exists_preimage_mem_adjoin ψ b b' hb (hg' (ψ x.1))
  choose relLift relMem relEq using fun z : Fin n × Bool =>
    exists_preimage_mem_adjoin ψ
      (fun q : {q : Fin n // q < z.1} => b q)
      (fun q : {q : Fin n // q < z.1} => b' q) (fun q => hb q) (hr z)
  let genDiff : {x : B.obj i // x ∈ s} → B.obj i := fun x => x.1 - genLift x
  let relDiff : Fin n × Bool → B.obj i := fun z =>
    (c z : B.obj i) * b z.1 ^ e z - relLift z
  let bad := Finset.univ.image genDiff ∪ Finset.univ.image relDiff
  have hbad : ∀ x ∈ bad, ψ x = 0 := by
    intro x hx
    simp only [bad, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · simp only [genDiff, map_sub, genEq, sub_self]
    · simp only [relDiff, map_sub, map_mul, map_natCast, map_pow, hb, relEq, sub_self]
  obtain ⟨j, f, hkill⟩ := exists_stage_killing_finset B ι hcol hsurj bad hbad
  let φ : B.obj i →ₐ[A] B.obj j := (B.map f).hom
  let bj : Fin n → B.obj j := fun k => φ (b k)
  have key {K : Type _} {u v : B.obj i} (g : K → B.obj i) (hu : u - v ∈ bad)
      (hv : v ∈ Algebra.adjoin A (Set.range g)) :
      φ u ∈ Algebra.adjoin A (Set.range fun k => φ (g k)) := by
    have h : φ u = φ v := sub_eq_zero.mp (by rw [← map_sub]; exact hkill _ hu)
    rw [h]
    exact map_mem_adjoin_range φ g hv
  refine ⟨j, f, bj, ?_, ?_⟩
  · have H : Algebra.adjoin A (s : Set (B.obj i)) ≤
        (Algebra.adjoin A (Set.range bj)).comap φ := by
      apply Algebra.adjoin_le_iff.mpr
      intro x hx
      let xt : {x : B.obj i // x ∈ s} := ⟨x, hx⟩
      exact key b (v := genLift xt)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨xt, Finset.mem_univ _, rfl⟩))
        (genMem xt)
    rw [hs] at H
    exact adjoin_range_eq_top_of_surjective φ (hsurj f) bj fun x =>
      H (show x ∈ (⊤ : Subalgebra A (B.obj i)) from trivial)
  · intro z
    simpa only [map_mul, map_natCast, map_pow] using
      key (fun q : {q : Fin n // q < z.1} => b q) (v := relLift z)
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩))
        (relMem z)

private lemma exists_stage_elementary_generators
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    {i : I} [Algebra.FiniteType A (B.obj i)] (hi : Function.Surjective (ι.app i).hom)
    {n : ℕ} (b' : Fin n → B') (p : Fin n → Option ℕ)
    (hg : Algebra.adjoin A (Set.range b') = ⊤)
    (hr : ∀ k, ElementaryRelation A b' (p k) k) :
    ∃ (j : I) (_f : i ⟶ j) (b : Fin n → B.obj j),
      Algebra.adjoin A (Set.range b) = ⊤ ∧ ∀ k, ElementaryRelation A b (p k) k := by
  let c : Fin n × Bool → ℕ := fun z => match p z.1 with
    | none => 1
    | some q => if z.2 then 1 else q
  let e : Fin n × Bool → ℕ := fun z => match p z.1 with
    | none => if z.2 then 3 else 2
    | some q => if z.2 then q else 1
  have hrel (z : Fin n × Bool) : (c z : B') * b' z.1 ^ e z ∈ Algebra.adjoin A
      (Set.range fun q : {q : Fin n // q < z.1} => b' q) := by
    have hk := hr z.1
    cases hp : p z.1 with
    | none =>
        rw [hp] at hk
        cases hz : z.2
        · simpa [c, e, hp, hz] using hk.1
        · simpa [c, e, hp, hz] using hk.2
    | some q =>
        rw [hp] at hk
        cases hz : z.2
        · simpa [c, e, hp, hz] using hk.2.1
        · simpa [c, e, hp, hz] using hk.2.2
  obtain ⟨j, f, b, hgen, hrels⟩ :=
    exists_stage_generators_and_relations B ι hcol hsurj hi b' hg c e hrel
  refine ⟨j, f, b, hgen, ?_⟩
  intro k
  have h1 := hrels (k, false)
  have h2 := hrels (k, true)
  have hk := hr k
  cases hp : p k with
  | none =>
      exact ⟨by simpa [c, e, hp] using h1, by simpa [c, e, hp] using h2⟩
  | some q =>
      rw [hp] at hk
      exact ⟨hk.1, by simpa [c, e, hp] using h1, by simpa [c, e, hp] using h2⟩

private lemma eventually_property
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B'] [Algebra.FiniteType A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hfp : ∀ i, Algebra.FinitePresentation A (B.obj i))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    (hUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op))
    (r : Prop) (hres : r → ∀ x, IsIso ((Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A B')).op).residueFieldMap x)) :
    ∃ i : I, ∀ {j : I} (_ : i ⟶ j),
      UniversalHomeomorphism
          (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (B.obj j))).op) ∧
        (r → ∀ x, IsIso ((Scheme.Spec.map
          (CommRingCat.ofHom (algebraMap A (B.obj j))).op).residueFieldMap x)) := by
  obtain ⟨i, hi⟩ := exists_stage_surjective_to_apex B ι hcol
  let := hfp i
  obtain ⟨n, b', p, hgen, hrel, hp⟩ := exists_elementary_generators hUH r hres
  obtain ⟨j, f, b, hg, hr⟩ := exists_stage_elementary_generators B ι hcol hsurj hi b' p hgen hrel
  refine ⟨j, ?_⟩
  intro k g
  let φ : B.obj j →ₐ[A] B.obj k := (B.map g).hom
  have hker : RingHom.ker (algebraMap A (B.obj k)) ≤ nilradical A := by
    intro a ha
    apply kernel_le_nilradical_of_universalHomeomorphism _ hUH
    let ψ : B.obj k →ₐ[A] B' := (ι.app k).hom
    have h := congrArg ψ (RingHom.mem_ker.mp ha)
    exact RingHom.mem_ker.mpr (by simpa only [AlgHom.commutes, map_zero] using h)
  have hgenk : Algebra.adjoin A (Set.range fun l => φ (b l)) = ⊤ :=
    adjoin_range_eq_top_of_surjective φ (hsurj g) _ fun x =>
      map_mem_adjoin_range φ b (by rw [hg]; trivial)
  exact property_of_elementary_generators hker (fun l => φ (b l)) p hgenk
    (fun l => elementaryRelation_map φ b (p l) l (hr l)) r hp

private lemma eventually_at_finite_stage
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B'] [Algebra.FiniteType A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hfp : ∀ i, Algebra.FinitePresentation A (B.obj i))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op)] :
    (∃ i : I, ∀ {j : I} (_ : i ⟶ j),
      UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (B.obj j))).op)) ∧
    ((∀ x : Spec (.of B'),
        IsIso ((Scheme.Spec.map
          (CommRingCat.ofHom (algebraMap A B')).op).residueFieldMap x)) →
      ∃ i : I, ∀ {j : I} (_ : i ⟶ j),
        UniversalHomeomorphism
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (B.obj j))).op) ∧
        (∀ x : Spec (.of (B.obj j)),
          IsIso ((Scheme.Spec.map
            (CommRingCat.ofHom (algebraMap A (B.obj j))).op).residueFieldMap x))) := by
  constructor
  · obtain ⟨i, hi⟩ := eventually_property B ι hcol hfp hsurj inferInstance False
      (fun h => h.elim)
    exact ⟨i, fun f => (hi f).1⟩
  · intro hres
    obtain ⟨i, hi⟩ := eventually_property B ι hcol hfp hsurj inferInstance True
      (fun _ => hres)
    exact ⟨i, fun f => ⟨(hi f).1, (hi f).2 trivial⟩⟩

-- Keep the quiver instance used by the accepted statement; the proof imports add
-- a definitionally equal alternative through `ReflQuiver`.

end FilteredStage

/-- A finite-type universal homeomorphism which is a filtered colimit of finitely presented
algebras with surjective transition maps is a universal homeomorphism at every sufficiently
late stage. -/
public theorem eventually_universalHomeomorphism_of_isColimit
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B'] [Algebra.FiniteType A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hfp : ∀ i, Algebra.FinitePresentation A (B.obj i))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op)] :
    ∃ i : I, ∀ {j : I} (_ : i ⟶ j),
      UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (B.obj j))).op) :=
  (FilteredStage.eventually_at_finite_stage B ι hcol hfp hsurj).1

/-- If, in addition, the original universal homeomorphism induces isomorphisms on residue
fields, then every sufficiently late stage has both properties. -/
public theorem eventually_universalHomeomorphism_and_isIso_residueFieldMap_of_isColimit
    {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B'] [Algebra.FiniteType A B']
    {I : Type (u + 1)} [Category.{u} I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{u} A)
    (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of A B'))
    (hcol : IsColimit (Cocone.mk (CommAlgCat.of A B') ι))
    (hfp : ∀ i, Algebra.FinitePresentation A (B.obj i))
    (hsurj : ∀ {i j} (f : i ⟶ j), Function.Surjective (B.map f))
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op)]
    (hres : ∀ x : Spec (.of B'),
      IsIso ((Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap A B')).op).residueFieldMap x)) :
    ∃ i : I, ∀ {j : I} (_ : i ⟶ j),
      UniversalHomeomorphism
          (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (B.obj j))).op) ∧
        (∀ x : Spec (.of (B.obj j)),
          IsIso ((Scheme.Spec.map
            (CommRingCat.ofHom (algebraMap A (B.obj j))).op).residueFieldMap x)) :=
  (FilteredStage.eventually_at_finite_stage B ι hcol hfp hsurj).2 hres

end AlgebraicGeometry

end
