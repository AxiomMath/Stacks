module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.Topology.Irreducible
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantNorm
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantPointsHelpers
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.GenericOrbitInvariantAffine
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.RingTheory.Ideal.Operations
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# An invariant affine principal open around finitely many generic orbits

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` finite and of finite presentation,
let `u₁, …, u_m` be points of `U` whose `R`-orbits consist of generic points of irreducible
components of `U`, let `j : U → Spec A` be an immersion, and let `I ⊆ A` be an ideal with
`j(U) ∩ V(I) = ∅` and `V(I) ∪ j(U)` closed. Then some `h ∈ I` has `j⁻¹ D(h)` an `R`-invariant
affine open of `U` containing `u₁, …, u_m`.

## Main results

* `AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen'`:
  [Stacks, Tag 0ABF], with no hypothesis beyond its own.

### What is assumed

Nothing. The proof reduces to the affine, finite locally free case through [Stacks, Tag 0ABC]
(`AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening`), which
carries [Stacks, Tag 06AD] — *a thickening of an affine scheme is affine* — as the universally
quantified hypothesis `H06AD`. That hypothesis is passed along by
`AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen` and discharged in
`AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen'`, where the tag
attribute sits, by `Stacks.Thickenings.forall_isAffine_of_isThickening`, the 06AD proved in
`StacksFrontier.AlgebraicGeometry.Thickenings.Affine`.

## Implementation notes

After [Stacks, Tag 0ABC] produces the invariant affine open `V` and the invariant affine
thickening `V' ⊆ V` of finite presentation over which the restricted groupoid has finite locally
free structure maps, prime avoidance ([Stacks, Tag 00DS], `Ideal.subset_union_prime`) supplies
`f ∈ I` vanishing on `U \ V` and nowhere on the orbits of the given points. The function
`g = Norm_s(t^♯(j^♯ f))` on `V'` is invariant by [Stacks, Tag 03BH]
(`AlgebraicGeometry.GroupoidScheme.det_lmul_targetMap_mem_invariantRing`). Because `V(I) ∪ j(U)`
is closed, `U ∩ D(f) → D(f)` is a closed immersion, so `g` is the restriction of a function on
`D(f)`, i.e. of `n/fᵏ` for some `n ∈ A`; the element `h = f · n` works.

The non-vanishing of the norm at a point is read off from the determinant of multiplication on
the fibre: it is nonzero exactly when the pulled-back function is a unit there, which holds
because `f` does not vanish anywhere on the orbit.

## References

* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 03BH](https://stacks.math.columbia.edu/tag/03BH)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0ABC](https://stacks.math.columbia.edu/tag/0ABC)
* [Stacks Project, Tag 0ABF](https://stacks.math.columbia.edu/tag/0ABF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct
open Stacks.Thickenings

universe u v

namespace AlgebraicGeometry

private theorem exists_mem_ideal_avoiding_finite_primes {A : Type u} [CommRing A]
    (I : Ideal A) (s : Finset (PrimeSpectrum A))
    (h : ∀ p ∈ s, ¬ I ≤ p.asIdeal) :
    ∃ f ∈ I, ∀ p ∈ s, f ∉ p.asIdeal := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨p₀, -⟩ := hs
    have hnot : ¬ ((I : Set A) ⊆ ⋃ q ∈ (↑s : Set (PrimeSpectrum A)), (q.asIdeal : Set A)) := by
      rw [Ideal.subset_union_prime p₀ p₀ (fun q _ _ _ => q.isPrime)]
      exact fun ⟨q, hq, hle⟩ => h q hq hle
    obtain ⟨f, hfI, hf⟩ := Set.not_subset.mp hnot
    refine ⟨f, hfI, fun q hq hmem => hf ?_⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr hq) hmem
  · refine ⟨0, I.zero_mem, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hs]

private theorem exists_mem_product_avoiding_finite_primes {A : Type u} [CommRing A]
    (I K : Ideal A) (s : Finset (PrimeSpectrum A))
    (hI : ∀ p ∈ s, ¬ I ≤ p.asIdeal)
    (hK : ∀ p ∈ s, ¬ K ≤ p.asIdeal) :
    ∃ f, f ∈ I ∧ f ∈ K ∧ ∀ p ∈ s, f ∉ p.asIdeal := by
  have hnot : ∀ p ∈ s, ¬ I * K ≤ p.asIdeal := by
    intro p hp hle
    rcases p.isPrime.mul_le.mp hle with h | h
    · exact hI p hp h
    · exact hK p hp h
  obtain ⟨f, hf, hn⟩ := exists_mem_ideal_avoiding_finite_primes (I * K) s hnot
  exact ⟨f, Ideal.mul_le_left hf, Ideal.mul_le_right hf, hn⟩

private theorem isClosed_range_on_basicOpen {X : Scheme.{u}}
    {A : Type u} [CommRing A]
    (j : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (f : A)
    (hfI : f ∈ I)
    (hclosed : IsClosed (PrimeSpectrum.zeroLocus (I : Set A) ∪
      Set.range (j : X → Spec (CommRingCat.of A)))) :
    IsClosed {p : (Spec (CommRingCat.of A)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) |
      p.1 ∈ Set.range (j : X → Spec (CommRingCat.of A))} := by
  let U : (Spec (CommRingCat.of A)).Opens :=
    (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)
  have hU : U = PrimeSpectrum.basicOpen f :=
    basicOpen_eq_of_affine (R := CommRingCat.of A) (f := (f : CommRingCat.of A))
  have hpre : IsClosed {p : U |
      p.1 ∈ PrimeSpectrum.zeroLocus (I : Set A) ∪
        Set.range (j : X → Spec (CommRingCat.of A))} :=
    hclosed.preimage continuous_subtype_val
  have heq : {p : U |
      p.1 ∈ PrimeSpectrum.zeroLocus (I : Set A) ∪
        Set.range (j : X → Spec (CommRingCat.of A))} =
      {p : U |
        p.1 ∈ Set.range (j : X → Spec (CommRingCat.of A))} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro (hp | hp)
      · have hfmem : f ∈ p.1.asIdeal :=
          ((PrimeSpectrum.mem_zeroLocus p.1 (I : Set A)).mp hp) hfI
        have hpD : p.1 ∈ PrimeSpectrum.basicOpen f := by rw [← hU]; exact p.2
        exact False.elim ((PrimeSpectrum.mem_basicOpen f p.1).mp hpD hfmem)
      · exact hp
    · exact fun hp => Or.inr hp
  exact heq ▸ hpre

private theorem isClosedImmersion_restrict_basicOpen {X : Scheme.{u}}
    {A : Type u} [CommRing A]
    (j : X ⟶ Spec (CommRingCat.of A)) [IsImmersion j]
    (I : Ideal A) (f : A) (hfI : f ∈ I)
    (hclosed : IsClosed (PrimeSpectrum.zeroLocus (I : Set A) ∪
      Set.range (j : X → Spec (CommRingCat.of A)))) :
    let U := (Spec (CommRingCat.of A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)
    IsClosedImmersion (j ∣_ U) := by
  dsimp
  apply IsClosedImmersion.of_isPreimmersion
  let U := (Spec (CommRingCat.of A)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)
  have hrange : Set.range (j ∣_ (Spec (CommRingCat.of A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) =
      {p : (Spec (CommRingCat.of A)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) |
        p.1 ∈ Set.range (j : X → Spec (CommRingCat.of A))} := by
    ext p
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x.1, ?_⟩
      calc
        j x.1 = ((j ∣_ U) x).1 := (morphismRestrict_base_coe j U x).symm
        _ = p.1 := congrArg Subtype.val hx
    · rintro ⟨y, hy⟩
      have hyU : y ∈ j ⁻¹ᵁ U := by
        change j y ∈ U
        rw [hy]
        exact p.2
      let z : j ⁻¹ᵁ U := ⟨y, hyU⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      calc
        ((j ∣_ U) z).1 = j y := morphismRestrict_base_coe j U z
        _ = p.1 := hy
  rw [hrange]; exact isClosed_range_on_basicOpen j I f hfI hclosed

private lemma over_eqToHom_symm_apply {S : Scheme} {X Y : Over S} (e : X = Y)
    (x : X.left) :
    (eqToHom e.symm).left ((eqToHom e).left x) = x := by
  cases e
  rfl

lemma exists_point_over_pullback {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (x : X.left) (y : Y.left)
    (h : f.left x = g.left y) :
    ∃ z : (pullback f g).left,
      (pullback.fst f g).left z = x ∧ (pullback.snd f g).left z = y := by
  let e := PreservesPullback.iso (Over.forget S) f g
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨e.inv p, ?_, ?_⟩
  · change ((PreservesPullback.iso (Over.forget S) f g).inv ≫
      (Over.forget S).map (pullback.fst f g)) p = x
    rw [PreservesPullback.iso_inv_fst]
    exact hp₁
  · change ((PreservesPullback.iso (Over.forget S) f g).inv ≫
      (Over.forget S).map (pullback.snd f g)) p = y
    rw [PreservesPullback.iso_inv_snd]
    exact hp₂

private lemma exists_arrow_in_restriction {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (R : GroupoidScheme.Restriction G g)
    (x y : R.groupoid.objects.left) (a : G.arrows.left)
    (hs : G.source.left a = R.hom.mapObjects.left x)
    (ht : G.target.left a = R.hom.mapObjects.left y) :
    ∃ b : R.groupoid.arrows.left,
      R.groupoid.source.left b = x ∧ R.groupoid.target.left b = y := by
  let x₀ : U'.left := (eqToHom R.objects_eq).left x
  let y₀ : U'.left := (eqToHom R.objects_eq).left y
  have hx : R.hom.mapObjects.left x = g.left x₀ := by
    rw [R.mapObjects_eq]
    rfl
  have hy : R.hom.mapObjects.left y = g.left y₀ := by
    rw [R.mapObjects_eq]
    rfl
  obtain ⟨p₁, hp₁x, hp₁a⟩ := exists_point_over_pullback g G.target y₀ a (by
    calc
      g.left y₀ = R.hom.mapObjects.left y := hy.symm
      _ = G.target.left a := ht.symm)
  obtain ⟨p₂, hp₂a, hp₂x⟩ := exists_point_over_pullback G.source g a x₀ (by
    calc
      G.source.left a = R.hom.mapObjects.left x := hs
      _ = g.left x₀ := hx)
  obtain ⟨p, hpfst, hpsnd⟩ := exists_point_over_pullback
      (pullback.snd g G.target) (pullback.fst G.source g) p₁ p₂ (by
        rw [hp₁a, hp₂a])
  have hcast : (eqToHom R.arrows_eq).left ((eqToHom R.arrows_eq.symm).left p) = p :=
    over_eqToHom_symm_apply R.arrows_eq.symm p
  refine ⟨(eqToHom R.arrows_eq.symm).left p, ?_, ?_⟩
  · rw [R.source_eq]
    change (eqToHom R.objects_eq.symm).left ((restrictionSource G g).left
      ((eqToHom R.arrows_eq).left ((eqToHom R.arrows_eq.symm).left p))) = x
    rw [hcast]
    have hs₀ : (restrictionSource G g).left p = x₀ := by
      change (pullback.snd G.source g).left
        ((pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left p) = x₀
      rw [hpsnd, hp₂x]
    rw [hs₀]
    exact over_eqToHom_symm_apply R.objects_eq x
  · rw [R.target_eq]
    change (eqToHom R.objects_eq.symm).left ((restrictionTarget G g).left
      ((eqToHom R.arrows_eq).left ((eqToHom R.arrows_eq.symm).left p))) = y
    rw [hcast]
    have ht₀ : (restrictionTarget G g).left p = y₀ := by
      change (pullback.fst g G.target).left
        ((pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left p) = y₀
      rw [hpfst, hp₁x]
    rw [ht₀]
    exact over_eqToHom_symm_apply R.objects_eq y

private lemma eval_appTop_ne_zero_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) (x : X) :
    X.Γevaluation x (f.appTop s) ≠ 0 ↔ Y.Γevaluation (f x) s ≠ 0 := by
  rw [← Scheme.Γevaluation_naturality_apply f x s]; exact map_ne_zero_iff _ (RingHom.injective _)

private theorem finite_orbit_of_isFinite_source {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left] (x : G.objects.left) :
    {y : G.objects.left | ∃ r : G.arrows.left,
      G.source.left r = x ∧ G.target.left r = y}.Finite := by
  have h := G.source.left.finite_preimage_singleton x
  have heq : {y : G.objects.left | ∃ r : G.arrows.left,
      G.source.left r = x ∧ G.target.left r = y} =
      G.target.left.base '' (G.source.left.base ⁻¹' ({x} : Set G.objects.left)) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [heq]; exact h.image G.target.left.base

private theorem exists_basic_function_vanishing_outside_open {X : Scheme.{u}}
    {A : Type u} [CommRing A]
    (j : X ⟶ Spec (CommRingCat.of A)) [IsImmersion j]
    (V : X.Opens) (x : X) (hx : x ∈ V) :
    ∃ a : A, a ∉ (j x).asIdeal ∧ ∀ y, y ∉ V → a ∈ (j y).asIdeal := by
  classical
  have hInducing : Topology.IsInducing j.base := j.isEmbedding.isInducing
  obtain ⟨O, hO, hpre⟩ := hInducing.isOpen_iff.mp V.2
  have hxO : j.base x ∈ O := by
    change x ∈ j.base ⁻¹' O
    rw [hpre]
    exact hx
  obtain ⟨D, ⟨a, rfl⟩, hxa, hDO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxO hO
  refine ⟨a, ?_, ?_⟩
  · exact (PrimeSpectrum.mem_basicOpen a (j.base x)).mp hxa
  · intro y hyV
    have hyO : j.base y ∉ O := by
      intro hy
      have hyPre : y ∈ j.base ⁻¹' O := hy
      have hyV' : y ∈ V.carrier := hpre ▸ hyPre
      exact hyV hyV'
    have hyD : j.base y ∉ PrimeSpectrum.basicOpen a := fun h => hyO (hDO h)
    by_contra ha
    exact hyD ((PrimeSpectrum.mem_basicOpen a (j.base y)).2 ha)

private theorem exists_ideal_element_avoiding_orbits_in_open {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    {A : Type u} [CommRing A]
    (j : G.objects.left ⟶ Spec (CommRingCat.of A)) [IsImmersion j]
    (I : Ideal A)
    (hdisj : Disjoint (Set.range (j : G.objects.left → Spec (CommRingCat.of A)))
      (PrimeSpectrum.zeroLocus (I : Set A)))
    (V : G.objects.left.Opens)
    (horbit : ∀ (i : ι) (r : G.arrows.left), G.source.left r = x i →
      G.target.left r ∈ V) :
    ∃ f ∈ I, (∀ y, y ∉ V → f ∈ (j y).asIdeal) ∧
      ∀ (i : ι) (r : G.arrows.left), G.source.left r = x i →
        f ∉ (j (G.target.left r)).asIdeal := by
  classical
  let O : Set G.objects.left := ⋃ i,
    {y | ∃ r : G.arrows.left, G.source.left r = x i ∧ G.target.left r = y}
  have hO : O.Finite := Set.finite_iUnion fun i => finite_orbit_of_isFinite_source G (x i)
  let P : Set (PrimeSpectrum A) := j.base '' O
  have hP : P.Finite := hO.image j.base
  let K : Ideal A := ⨅ y : {y : G.objects.left // y ∉ V}, (j y.1).asIdeal
  have hNotI : ∀ p ∈ hP.toFinset, ¬ I ≤ p.asIdeal := by
    intro p hp hle
    have hmemP : p ∈ P := hP.mem_toFinset.mp hp
    rcases hmemP with ⟨y, hy, rfl⟩
    have hrange : j y ∈ Set.range (j : G.objects.left → Spec (CommRingCat.of A)) :=
      ⟨y, rfl⟩
    have hzero : j y ∈ PrimeSpectrum.zeroLocus (I : Set A) :=
      (PrimeSpectrum.mem_zeroLocus (j y) (I : Set A)).mpr hle
    exact (Set.disjoint_left.mp hdisj) hrange hzero
  have hNotK : ∀ p ∈ hP.toFinset, ¬ K ≤ p.asIdeal := by
    intro p hp hle
    have hmemP : p ∈ P := hP.mem_toFinset.mp hp
    rcases hmemP with ⟨y, hy, rfl⟩
    have hyV : y ∈ V := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      rcases hi with ⟨r, hr, rfl⟩
      exact horbit i r hr
    obtain ⟨a, haKnot, haOutside⟩ :=
      exists_basic_function_vanishing_outside_open j V y hyV
    have haK : a ∈ K := by
      change a ∈ (⨅ z : {z : G.objects.left // z ∉ V}, (j z.1).asIdeal)
      rw [Ideal.mem_iInf]
      exact fun z => haOutside z.1 z.2
    exact haKnot (hle haK)
  obtain ⟨f, hfI, hfK, havoid⟩ :=
    exists_mem_product_avoiding_finite_primes I K hP.toFinset hNotI hNotK
  refine ⟨f, hfI, ?_, ?_⟩
  · intro y hyV
    change f ∈ (⨅ z : {z : G.objects.left // z ∉ V}, (j z.1).asIdeal) at hfK
    exact (Ideal.mem_iInf.mp hfK) ⟨y, hyV⟩
  · intro i r hsource
    apply havoid
    apply hP.mem_toFinset.mpr
    refine ⟨G.target.left r, ?_, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨r, hsource, rfl⟩⟩

/-- **[Stacks, Tag 0ABF], granted [Stacks, Tag 06AD].** Let `G` be a groupoid scheme whose
source and target are finite and of finite presentation, let `x : ι → U` be finitely many points
whose orbits consist of generic points of irreducible components of the object scheme, let
`j : U ⟶ Spec A` be an immersion, and let `I` be an ideal of `A` whose vanishing locus misses
the image of `j` and whose union with that image is closed. Then some `h ∈ I` has `j ⁻¹ D(h)` an
invariant affine open of the object scheme containing all the `x i`.

The hypothesis `H06AD` is [Stacks, Tag 06AD] — a thickening of an affine scheme is affine — and
is the only thing assumed; it enters only through [Stacks, Tag 0ABC]. It is discharged by
`Stacks.Thickenings.forall_isAffine_of_isThickening` in
`AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen'`, which is where the
tag attribute sits. -/
theorem exists_mem_ideal_invariant_affine_preimage_basicOpen
    (H06AD : ∀ (Y Y' : Scheme.{u}) (i : Y ⟶ Y'), IsThickening i → IsAffine Y → IsAffine Y')
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    (hs : FinitePresentation G.source.left)
    (ht : FinitePresentation G.target.left)
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z)
    {A : Type u} [CommRing A]
    (j : G.objects.left ⟶ Spec (CommRingCat.of A)) [IsImmersion j]
    (I : Ideal A)
    (hdisj : Disjoint (Set.range (j : G.objects.left → Spec (CommRingCat.of A)))
      (PrimeSpectrum.zeroLocus (I : Set A)))
    (hclosed : IsClosed (PrimeSpectrum.zeroLocus (I : Set A) ∪
      Set.range (j : G.objects.left → Spec (CommRingCat.of A)))) :
    ∃ h : A, h ∈ I ∧
      (let W := j ⁻¹ᵁ PrimeSpectrum.basicOpen h
       Stacks.Groupoids.IsInvariantOpen G W ∧ IsAffineOpen W ∧ ∀ i, x i ∈ W) := by
  classical
  let : IsSeparated j := inferInstance
  let : IsSeparated (terminal.from (Spec (CommRingCat.of A))) := inferInstance
  have hsepComp : IsSeparated (j ≫ terminal.from (Spec (CommRingCat.of A))) := inferInstance
  have hsepU : IsSeparated (terminal.from G.objects.left) := by
    simpa only [terminal.comp_from] using hsepComp
  let : Scheme.IsSeparated G.objects.left := ⟨hsepU⟩
  let : QuasiSeparatedSpace G.objects.left := inferInstance
  obtain ⟨V, Z, hxZ, hInvV, hAffV, _, hAffZ, hThick, _, hFLF⟩ :=
    exists_invariant_affine_open_with_finiteLocallyFree_thickening
      H06AD G hs ht x hx
  have hxV : ∀ i, x i ∈ V := by
    intro i
    obtain ⟨z, hz⟩ := hxZ i
    change x i ∈ (↑V : Set G.objects.left)
    rw [← V.range_ι]; exact ⟨Z.subschemeι z, hz⟩
  have horbit : ∀ (i : ι) (r : G.arrows.left), G.source.left r = x i →
      G.target.left r ∈ V := by
    intro i r hsource
    apply hInvV r
    simpa [hsource] using hxV i
  obtain ⟨f, hfI, hfOutside, hfOrbit⟩ :=
    exists_ideal_element_avoiding_orbits_in_open G x j I hdisj V horbit
  let U' : Over S := Over.mk (Z.subschemeι ≫ V.ι ≫ G.objects.hom)
  let g : U' ⟶ G.objects := Over.homMk (Z.subschemeι ≫ V.ι) (by rfl)
  let R := AlgebraicGeometry.GroupoidScheme.restrict G g
  let G' := R.groupoid
  let objIsoOver := eqToIso R.objects_eq
  let objIso : G'.objects.left ≅ U'.left := (Over.forget S).mapIso objIsoOver
  have : IsAffine U'.left := by simpa [U'] using hAffZ
  let : IsIso objIso.hom := inferInstance
  have : IsAffine G'.objects.left := IsAffine.of_isIso objIso.hom
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree G'.source.left := by
    simpa [G', R] using hFLF.1
  let : Stacks.Morphisms.IsFiniteLocallyFree G'.source.left := hflf
  let : IsAffineHom G'.source.left := hflf.toIsAffineHom
  have : IsAffine G'.arrows.left := isAffine_of_isAffineHom G'.source.left
  let fSpec : Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
  let fZ : Γ(G'.objects.left, ⊤) :=
    (Scheme.Hom.appTop (R.hom.mapObjects.left ≫ j)) fSpec
  have hfZAmbient (z : G'.objects.left) :
      (G'.objects.left.Γevaluation z).hom fZ ≠ 0 ↔
        (Spec (CommRingCat.of A)).evaluation ⊤
          (j (R.hom.mapObjects.left z)) (by simp) fSpec ≠ 0 :=
    eval_appTop_ne_zero_iff (R.hom.mapObjects.left ≫ j) fSpec z
  obtain ⟨hfinite', hprojective', hnorm⟩ :=
    GroupoidScheme.det_lmul_targetMap_mem_invariantRing G' fZ
  let : Algebra Γ(G'.objects.left, ⊤) Γ(G'.arrows.left, ⊤) := (sourceMap G').toAlgebra
  let : Module.Finite Γ(G'.objects.left, ⊤) Γ(G'.arrows.left, ⊤) := hfinite'
  let : Module.Projective Γ(G'.objects.left, ⊤) Γ(G'.arrows.left, ⊤) := hprojective'
  let normZ : Γ(G'.objects.left, ⊤) :=
    ProjectiveDeterminant.det
      (Algebra.lmul Γ(G'.objects.left, ⊤) Γ(G'.arrows.left, ⊤) (targetMap G' fZ))
  have hnormEq : sourceMap G' normZ = targetMap G' normZ := RingHom.mem_eqLocus.mp hnorm
  have htargetEvalNonzero (r : G'.arrows.left)
      (hsource : (G'.objects.left.Γevaluation (G'.source.left r)).hom normZ ≠ 0) :
      (G'.arrows.left.Γevaluation r).hom (targetMap G' fZ) ≠ 0 := by
    have hnatural :
        (G'.source.left.residueFieldMap r).hom.comp
            (G'.objects.left.Γevaluation (G'.source.left r)).hom =
          (G'.arrows.left.Γevaluation r).hom.comp (sourceMap G') := by
      ext a
      exact Scheme.Γevaluation_naturality_apply G'.source.left r a
    intro hz
    apply hsource
    change (G'.objects.left.Γevaluation (G'.source.left r)).hom
      (Algebra.projectiveNorm Γ(G'.objects.left, ⊤) (targetMap G' fZ)) = 0
    exact Algebra.projectiveNorm_eq_zero_of_field_hom Γ(G'.objects.left, ⊤)
      (G'.objects.left.Γevaluation (G'.source.left r)).hom
      (G'.arrows.left.Γevaluation r).hom (G'.source.left.residueFieldMap r).hom
      hnatural.symm (targetMap G' fZ) hz
  have htargetNormNonzero (r : G'.arrows.left)
      (hsource : (G'.objects.left.Γevaluation (G'.source.left r)).hom normZ ≠ 0) :
      (G'.objects.left.Γevaluation (G'.target.left r)).hom normZ ≠ 0 := by
    apply (eval_appTop_ne_zero_iff G'.target.left normZ r).mp
    change (G'.arrows.left.Γevaluation r).hom (targetMap G' normZ) ≠ 0
    rw [← hnormEq]; exact (eval_appTop_ne_zero_iff G'.source.left normZ r).mpr hsource
  let normSubscheme : Γ(U'.left, ⊤) := (Scheme.Hom.appTop objIso.inv) normZ
  have : IsAffine V.toScheme := hAffV
  obtain ⟨normV, hnormV⟩ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine Z.subschemeι).2 normSubscheme
  let specOpen : (Spec (CommRingCat.of A)).Opens :=
    (Spec (CommRingCat.of A)).basicOpen fSpec
  have hbasicOpen : specOpen = PrimeSpectrum.basicOpen f :=
    by simpa [specOpen, fSpec] using
      (basicOpen_eq_of_affine' (R := CommRingCat.of A) (f := fSpec))
  have hmemSpec (p : PrimeSpectrum A) : p ∈ specOpen ↔ f ∉ p.asIdeal := by
    rw [hbasicOpen]; exact PrimeSpectrum.mem_basicOpen f p
  have hevalSpec (p : Spec (CommRingCat.of A)) :
      (Spec (CommRingCat.of A)).evaluation ⊤ p (by simp) fSpec ≠ 0 ↔ p ∈ specOpen :=
    (Spec (CommRingCat.of A)).evaluation_ne_zero_iff_mem_basicOpen p (by simp) fSpec
  let sourceOpen : G.objects.left.Opens := j ⁻¹ᵁ specOpen
  have hsourceOpenV : sourceOpen ≤ V := fun y hy =>
    by_contra fun hyV => (hmemSpec _).mp hy (hfOutside y hyV)
  let normSource : Γ(sourceOpen.toScheme, ⊤) :=
    (Scheme.Hom.appTop (G.objects.left.homOfLE hsourceOpenV)) normV
  let : IsClosedImmersion (j ∣_ specOpen) :=
    isClosedImmersion_restrict_basicOpen j I f hfI hclosed
  have : IsAffine specOpen.toScheme :=
    (isAffineOpen_top (Spec (CommRingCat.of A))).basicOpen fSpec
  obtain ⟨normOpen, hnormOpen⟩ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (j ∣_ specOpen)).2 normSource
  let openIso : specOpen.toScheme ≅ Spec (CommRingCat.of (Localization.Away f)) :=
    (Spec (CommRingCat.of A)).isoOfEq hbasicOpen ≪≫
      basicOpenIsoSpecAway (R := CommRingCat.of A) (f := (f : CommRingCat.of A))
  let normAway : Localization.Away f := (Scheme.ΓSpecIso
    (CommRingCat.of (Localization.Away f))).hom (openIso.inv.appTop normOpen)
  have hcomp : openIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) = specOpen.ι := by
    dsimp [openIso]
    rw [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
    exact Scheme.isoOfEq_hom_ι _ _
  have hcontract (pOpen : specOpen.toScheme) :
      (openIso.hom pOpen).asIdeal.comap (algebraMap A (Localization.Away f)) =
        pOpen.1.asIdeal := by
    have hp := congrArg (fun g => g pOpen) hcomp
    exact congrArg PrimeSpectrum.asIdeal hp
  have hbasicNorm :
      (Spec (CommRingCat.of (Localization.Away f))).basicOpen
          (openIso.inv.appTop normOpen) = PrimeSpectrum.basicOpen normAway := by
    simpa [normAway] using (basicOpen_eq_of_affine'
      (R := CommRingCat.of (Localization.Away f))
      (f := openIso.inv.appTop normOpen))
  obtain ⟨power, numerator, hnum⟩ := IsLocalization.Away.surj f normAway
  let h : A := f * numerator
  have hhI : h ∈ I := by
    dsimp [h]
    exact Ideal.mul_mem_right numerator I hfI
  let hSpec : Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv h
  let W : G.objects.left.Opens := j ⁻¹ᵁ PrimeSpectrum.basicOpen h
  have hWleSource : W ≤ sourceOpen := by
    intro y hy
    change j y ∈ specOpen
    rw [hbasicOpen]
    exact (PrimeSpectrum.basicOpen_mul_le_left f numerator) hy
  have hbasicOpenH : (Spec (CommRingCat.of A)).basicOpen hSpec =
      PrimeSpectrum.basicOpen h := by
    simpa [hSpec] using
      (basicOpen_eq_of_affine' (R := CommRingCat.of A) (f := hSpec))
  have hWleV : W ≤ V := le_trans hWleSource hsourceOpenV
  have hAffineW : IsAffineOpen W := by
    change IsAffine W
    have : IsClosedImmersion (j ∣_ (Spec (CommRingCat.of A)).basicOpen hSpec) :=
      isClosedImmersion_restrict_basicOpen j I h hhI hclosed
    have : IsAffine ((Spec (CommRingCat.of A)).basicOpen hSpec).toScheme :=
      (isAffineOpen_top (Spec (CommRingCat.of A))).basicOpen hSpec
    simpa only [W, ← hbasicOpenH] using
      (IsClosedImmersion.isAffine_surjective_of_isAffine
        (j ∣_ (Spec (CommRingCat.of A)).basicOpen hSpec)).1
  have hnormV_iff_normAway (ySource : sourceOpen.toScheme) :
      (V.toScheme.Γevaluation ((G.objects.left.homOfLE hsourceOpenV) ySource)).hom
          normV ≠ 0 ↔
        normAway ∉ (openIso.hom (⟨j ySource.1, ySource.2⟩ : specOpen.toScheme)).asIdeal := by
    let pOpen : specOpen.toScheme := ⟨j ySource.1, ySource.2⟩
    let pAway : Spec (CommRingCat.of (Localization.Away f)) := openIso.hom pOpen
    have hmap : (j ∣_ specOpen) ySource = pOpen := by
      apply Subtype.ext
      exact morphismRestrict_base_coe j specOpen ySource
    calc
      _ ↔ (sourceOpen.toScheme.Γevaluation ySource).hom normSource ≠ 0 :=
        (eval_appTop_ne_zero_iff (G.objects.left.homOfLE hsourceOpenV) normV ySource).symm
      _ ↔ (sourceOpen.toScheme.Γevaluation ySource).hom
          ((Scheme.Hom.appTop (j ∣_ specOpen)) normOpen) ≠ 0 := by rw [hnormOpen]
      _ ↔ (specOpen.toScheme.Γevaluation ((j ∣_ specOpen) ySource)).hom normOpen ≠ 0 :=
        eval_appTop_ne_zero_iff (j ∣_ specOpen) normOpen ySource
      _ ↔ (specOpen.toScheme.Γevaluation pOpen).hom normOpen ≠ 0 := by rw [hmap]
      _ ↔ (Spec (CommRingCat.of (Localization.Away f))).evaluation ⊤ pAway (by simp)
          (openIso.inv.appTop normOpen) ≠ 0 := by
            have h' := (eval_appTop_ne_zero_iff openIso.inv normOpen pAway).symm
            have heq : openIso.inv pAway = pOpen := by simp [pAway]
            rw [heq] at h'
            exact h'
      _ ↔ pAway ∈ (Spec (CommRingCat.of (Localization.Away f))).basicOpen
          (openIso.inv.appTop normOpen) :=
        (Spec (CommRingCat.of (Localization.Away f))).evaluation_ne_zero_iff_mem_basicOpen
          pAway (by simp) (openIso.inv.appTop normOpen)
      _ ↔ normAway ∉ pAway.asIdeal := by
        rw [hbasicNorm]; exact PrimeSpectrum.mem_basicOpen normAway pAway
  have hW_iff_normV (ySource : sourceOpen.toScheme) :
      ySource.1 ∈ W ↔
        (V.toScheme.Γevaluation ((G.objects.left.homOfLE hsourceOpenV) ySource)).hom
          normV ≠ 0 := by
    let p : PrimeSpectrum A := j ySource.1
    let pOpen : specOpen.toScheme := ⟨p, ySource.2⟩
    let pAway : Spec (CommRingCat.of (Localization.Away f)) := openIso.hom pOpen
    have hf : f ∉ p.asIdeal := (hmemSpec p).mp ySource.2
    have hfactor : IsUnit ((algebraMap A (Localization.Away f)) f ^ power) :=
      (IsLocalization.Away.algebraMap_isUnit f).pow power
    calc
      ySource.1 ∈ W ↔ numerator ∉ p.asIdeal := by
        change p ∈ PrimeSpectrum.basicOpen (f * numerator) ↔ _
        rw [PrimeSpectrum.basicOpen_mul]
        change (f ∉ p.asIdeal ∧ numerator ∉ p.asIdeal) ↔ _
        simp [hf]
      _ ↔ normAway ∉ pAway.asIdeal := by
        have hcontract' : numerator ∈ p.asIdeal ↔
            (algebraMap A (Localization.Away f)) numerator ∈ pAway.asIdeal := by
          change numerator ∈ pOpen.1.asIdeal ↔
            numerator ∈ pAway.asIdeal.comap (algebraMap A (Localization.Away f))
          rw [hcontract pOpen]
        rw [← hnum] at hcontract'
        exact not_congr (hcontract'.trans
          (Ideal.mul_unit_mem_iff_mem pAway.asIdeal hfactor))
      _ ↔ (V.toScheme.Γevaluation
          ((G.objects.left.homOfLE hsourceOpenV) ySource)).hom normV ≠ 0 :=
        (hnormV_iff_normAway ySource).symm
  have hnormZAtThickeningPoint (z : Z.subscheme) :
      (G'.objects.left.Γevaluation (objIso.inv z)).hom normZ ≠ 0 ↔
        (V.toScheme.Γevaluation (Z.subschemeι z)).hom normV ≠ 0 := by
    calc
      (G'.objects.left.Γevaluation (objIso.inv z)).hom normZ ≠ 0 ↔
          (U'.left.Γevaluation z).hom normSubscheme ≠ 0 :=
        (eval_appTop_ne_zero_iff objIso.inv normZ z).symm
      _ ↔ (U'.left.Γevaluation z).hom
            ((Scheme.Hom.appTop Z.subschemeι) normV) ≠ 0 := by
        rw [hnormV]
      _ ↔ (V.toScheme.Γevaluation (Z.subschemeι z)).hom normV ≠ 0 :=
        eval_appTop_ne_zero_iff Z.subschemeι normV z
  have hZsurj : Function.Surjective Z.subschemeι.base := hThick.2
  have hsourceNormZ (y : G.objects.left) (hyW : y ∈ W)
      (ySource : sourceOpen.toScheme) (hys : ySource.1 = y) :
      ∃ z : Z.subscheme, Z.subschemeι z =
          (G.objects.left.homOfLE hsourceOpenV) ySource ∧
        (G'.objects.left.Γevaluation (objIso.inv z)).hom normZ ≠ 0 := by
    let yV : V.toScheme := (G.objects.left.homOfLE hsourceOpenV) ySource
    obtain ⟨z, hz⟩ := hZsurj yV
    refine ⟨z, ?_, ?_⟩
    · exact hz
    · apply (hnormZAtThickeningPoint z).2
      rw [hz]; exact (hW_iff_normV ySource).1 (by simpa only [hys] using hyW)
  have hpointInW (y : G.objects.left)
      (ySource : sourceOpen.toScheme) (hys : ySource.1 = y)
      (z : Z.subscheme) (hz : Z.subschemeι z =
        (G.objects.left.homOfLE hsourceOpenV) ySource)
      (hnorm : (G'.objects.left.Γevaluation (objIso.inv z)).hom normZ ≠ 0) : y ∈ W := by
    apply hys ▸ (hW_iff_normV ySource).2
    rw [← hz]
    exact (hnormZAtThickeningPoint z).mp hnorm
  let toU : G'.objects.left ⟶ U'.left := (eqToHom R.objects_eq).left
  have hmapObj (z : Z.subscheme) :
      R.hom.mapObjects.left (objIso.inv z) = g.left z := by
    rw [R.mapObjects_eq]
    change g.left (toU (objIso.inv z)) = g.left z
    simpa [toU, objIso, objIsoOver] using
      congrArg g.left (over_eqToHom_symm_apply R.objects_eq.symm z)
  have hsubToV (q : sourceOpen.toScheme) :
      V.ι ((G.objects.left.homOfLE hsourceOpenV) q) = sourceOpen.ι q :=
    congrArg (fun k : sourceOpen.toScheme ⟶ G.objects.left => k q)
      (Scheme.homOfLE_ι G.objects.left hsourceOpenV)
  have hlift (z : Z.subscheme) (q : sourceOpen.toScheme) (h : V.ι (Z.subschemeι z) = q.1) :
      Z.subschemeι z = (G.objects.left.homOfLE hsourceOpenV) q := by
    apply V.ι.isEmbedding.injective
    rw [hsubToV]
    exact h
  have hInvW : Stacks.Groupoids.IsInvariantOpen G W := by
    intro a ha
    let ySource : sourceOpen.toScheme := ⟨G.source.left a, hWleSource ha⟩
    obtain ⟨zs, hzs, hnorms⟩ := hsourceNormZ (G.source.left a) ha ySource rfl
    have hsourceV : G.source.left a ∈ V := hWleV ha
    have htargetV : G.target.left a ∈ V := hInvV a hsourceV
    let yTargetV : V.toScheme := ⟨G.target.left a, htargetV⟩
    obtain ⟨zt, hzt⟩ := hZsurj yTargetV
    let xR : G'.objects.left := objIso.inv zs
    let yR : G'.objects.left := objIso.inv zt
    have hmapSource : R.hom.mapObjects.left xR = G.source.left a := by
      rw [hmapObj]
      calc
        g.left zs = V.ι (Z.subschemeι zs) := rfl
        _ = V.ι ((G.objects.left.homOfLE hsourceOpenV) ySource) := by exact congrArg V.ι hzs
        _ = sourceOpen.ι ySource := hsubToV ySource
        _ = G.source.left a := by change ySource.1 = _; rfl
    have hmapTarget : R.hom.mapObjects.left yR = G.target.left a := by
      rw [hmapObj]
      calc
        g.left zt = V.ι (Z.subschemeι zt) := rfl
        _ = V.ι yTargetV := congrArg V.ι hzt
        _ = G.target.left a := rfl
    obtain ⟨b, hbs, hbt⟩ := exists_arrow_in_restriction G g R xR yR a
      (hmapSource.symm) (hmapTarget.symm)
    have hnormt := htargetNormNonzero b (by
      rw [hbs]; exact hnorms)
    have hftArrow := htargetEvalNonzero b (by
      rw [hbs]; exact hnorms)
    have hftObj : (G'.objects.left.Γevaluation (G'.target.left b)).hom fZ ≠ 0 := by
      have h := (eval_appTop_ne_zero_iff G'.target.left fZ b).mp hftArrow
      exact h
    have hftAmbient :
        (Spec (CommRingCat.of A)).evaluation ⊤ (j (G.target.left a)) (by simp)
          fSpec ≠ 0 := by
      have hObj := (hfZAmbient yR).mp (by rw [← hbt]; exact hftObj)
      simpa [hmapTarget] using hObj
    have htSpec : j (G.target.left a) ∈ specOpen := (hevalSpec _).mp hftAmbient
    let yTargetSource : sourceOpen.toScheme := ⟨G.target.left a, htSpec⟩
    have hztSource := hlift zt yTargetSource (by rw [hzt]; rfl)
    exact hpointInW (G.target.left a) yTargetSource rfl zt hztSource (by
      change (G'.objects.left.Γevaluation yR).hom normZ ≠ 0
      rw [← hbt]
      exact hnormt)
  have hnormAtChosen (i : ι) (z : Z.subscheme)
      (hzi : (Z.subschemeι ≫ V.ι) z = x i) :
      (G'.objects.left.Γevaluation (objIso.inv z)).hom normZ ≠ 0 := by
    let R₀ := Γ(G'.objects.left, ⊤)
    let B₀ := Γ(G'.arrows.left, ⊤)
    let k := G'.objects.left.residueField (objIso.inv z)
    let : Algebra R₀ k := (G'.objects.left.Γevaluation (objIso.inv z)).hom.toAlgebra
    let F := k ⊗[R₀] B₀
    let : Algebra k F := Algebra.TensorProduct.leftAlgebra
    have : Module.Finite k F := Module.Finite.base_change R₀ k B₀
    let : FiniteDimensional k F := inferInstance
    let t : F := Algebra.TensorProduct.includeRight (targetMap G' fZ)
    have htUnit : IsUnit t := by
      by_contra htu
      have hspan : Ideal.span ({t} : Set F) ≠ ⊤ := by
        intro heq
        apply htu
        exact Ideal.span_singleton_eq_top.mp heq
      obtain ⟨M, hM, hspanM⟩ := Ideal.exists_le_maximal _ hspan
      have htM : t ∈ M := hspanM (Ideal.subset_span (by simp))
      let qPrime : PrimeSpectrum F := ⟨M, hM.isPrime⟩
      let qSpec : Spec (CommRingCat.of F) := ⟨qPrime, qPrime.2⟩
      let fB := Spec.map (CommRingCat.ofHom (sourceMap G'))
      let inc : B₀ →+* F :=
        (Algebra.TensorProduct.includeRight : B₀ →ₐ[R₀] k ⊗[R₀] B₀).toRingHom
      let qArrowSpec := Spec.map (CommRingCat.ofHom inc) qSpec
      have hqMem : targetMap G' fZ ∈ qArrowSpec.asIdeal := by
        change inc (targetMap G' fZ) ∈ qPrime.asIdeal
        exact htM
      let objPoint := objIso.inv z
      let pObj := G'.objects.left.isoSpec.hom objPoint
      have hbase : fB qArrowSpec = pObj := by
        have hcomp : inc.comp (sourceMap G') =
            (Algebra.TensorProduct.includeLeftRingHom : k →+* F).comp
              (G'.objects.left.Γevaluation objPoint).hom := by
          change (Algebra.TensorProduct.includeRight.toRingHom.comp
            (algebraMap R₀ B₀) : R₀ →+* F) =
              Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap R₀ k)
          exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
            (R := R₀) (A := k) (B := B₀)).symm
        have hspec : Spec.map (CommRingCat.ofHom (algebraMap k F)) qSpec =
            ((⊥ : PrimeSpectrum k) : Spec (CommRingCat.of k)) :=
          Subsingleton.elim _ _
        change (Spec.map (CommRingCat.ofHom (sourceMap G')))
          (Spec.map (CommRingCat.ofHom inc) qSpec) = _
        rw [← Scheme.Hom.comp_apply, ← Spec.map_comp]
        change Spec.map (CommRingCat.ofHom (inc.comp (sourceMap G'))) qSpec = _
        rw [show inc.comp (sourceMap G') =
          (Algebra.TensorProduct.includeLeftRingHom : k →+* F).comp
            (G'.objects.left.Γevaluation objPoint).hom from hcomp]
        change Spec.map ((CommRingCat.ofHom
          (G'.objects.left.Γevaluation objPoint).hom) ≫
            (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : k →+* F)))
          qSpec = _
        rw [Spec.map_comp, Scheme.Hom.comp_apply, hspec]
        change Spec.map (CommRingCat.ofHom
            (G'.objects.left.Γevaluation objPoint).hom)
            ((⊥ : PrimeSpectrum k) : Spec (CommRingCat.of k)) =
          G'.objects.left.toSpecΓ objPoint
        rw [Scheme.toSpecΓ_apply]
        change Spec.map (G'.objects.left.presheaf.Γgerm objPoint ≫
            G'.objects.left.residue objPoint)
            ((⊥ : PrimeSpectrum k) : Spec (CommRingCat.of k)) = _
        rw [Spec.map_comp]
        change (Spec.map (G'.objects.left.presheaf.Γgerm objPoint))
          ((Spec.map (G'.objects.left.residue objPoint))
            (default : Spec (G'.objects.left.residueField objPoint))) = _
        rw [Scheme.SpecMap_residue_apply]
      have hnat := congrArg (fun k : G'.arrows.left ⟶ Spec (CommRingCat.of R₀) =>
          k (G'.arrows.left.isoSpec.inv qArrowSpec))
        (Scheme.isoSpec_hom_naturality G'.source.left)
      have hsourceQ : G'.source.left (G'.arrows.left.isoSpec.inv qArrowSpec) = objPoint := by
        apply G'.objects.left.isoSpec.hom.isEmbedding.injective
        simp only [Scheme.Hom.comp_apply] at hnat
        rw [show G'.arrows.left.isoSpec.hom
          (G'.arrows.left.isoSpec.inv qArrowSpec) = qArrowSpec by simp] at hnat
        change fB qArrowSpec = _ at hnat
        exact hnat.symm.trans hbase
      let a := R.hom.mapArrows.left (G'.arrows.left.isoSpec.inv qArrowSpec)
      have hmapSrc : G.source.left a = x i := by
        have hcomm : R.hom.mapArrows.left ≫ G.source.left =
            G'.source.left ≫ R.hom.mapObjects.left :=
          congrArg Over.Hom.left R.hom.map_source
        have hpoint := congrArg (fun k : G'.arrows.left ⟶ G.objects.left =>
            k (G'.arrows.left.isoSpec.inv qArrowSpec)) hcomm
        have hsourceMap : G.source.left a = R.hom.mapObjects.left objPoint := by
          simpa [a, Scheme.Hom.comp_apply, hsourceQ] using hpoint
        calc
          G.source.left a = R.hom.mapObjects.left objPoint := hsourceMap
          _ = g.left z := by
            dsimp [objPoint]
            exact hmapObj z
          _ = x i := hzi
      have hspecTarget : j (G.target.left a) ∈ specOpen :=
        (hmemSpec _).mpr (hfOrbit i a hmapSrc)
      have hmapTargetArrow : G.target.left a =
          R.hom.mapObjects.left (G'.target.left (G'.arrows.left.isoSpec.inv qArrowSpec)) := by
        have hcomm : R.hom.mapArrows.left ≫ G.target.left =
            G'.target.left ≫ R.hom.mapObjects.left :=
          congrArg Over.Hom.left R.hom.map_target
        have hpoint := congrArg (fun k : G'.arrows.left ⟶ G.objects.left =>
            k (G'.arrows.left.isoSpec.inv qArrowSpec)) hcomm
        simpa [a, Scheme.Hom.comp_apply] using hpoint
      have hObjEval : (G'.objects.left.Γevaluation
          (G'.target.left (G'.arrows.left.isoSpec.inv qArrowSpec))).hom fZ ≠ 0 := by
        apply (hfZAmbient _).mpr
        rw [← hmapTargetArrow]
        exact (hevalSpec _).2 hspecTarget
      have hArrowEval : (G'.arrows.left.Γevaluation
          (G'.arrows.left.isoSpec.inv qArrowSpec)).hom (targetMap G' fZ) ≠ 0 := by
        apply (eval_appTop_ne_zero_iff G'.target.left fZ
          (G'.arrows.left.isoSpec.inv qArrowSpec)).mpr
        exact hObjEval
      have hb := (G'.arrows.left.evaluation_ne_zero_iff_mem_basicOpen
        (G'.arrows.left.isoSpec.inv qArrowSpec) (by simp) (targetMap G' fZ)).mp hArrowEval
      rw [← Scheme.toSpecΓ_preimage_basicOpen] at hb
      change G'.arrows.left.isoSpec.hom
        (G'.arrows.left.isoSpec.inv qArrowSpec) ∈
          PrimeSpectrum.basicOpen (targetMap G' fZ) at hb
      rw [show G'.arrows.left.isoSpec.hom
        (G'.arrows.left.isoSpec.inv qArrowSpec) = qArrowSpec by simp] at hb
      change targetMap G' fZ ∉ qArrowSpec.asIdeal at hb
      exact hb hqMem
    have hdet : LinearMap.det (Algebra.lmul k F t) ≠ 0 :=
      (det_lmul_ne_zero_iff_isUnit (k := k) (F := F) t).mpr htUnit
    have hdetEq := algebraMap_det_lmul (R := R₀) (B := B₀) (k := k) (targetMap G' fZ)
    change (G'.objects.left.Γevaluation (objIso.inv z)).hom normZ ≠ 0
    change (algebraMap R₀ k)
      (ProjectiveDeterminant.det (Algebra.lmul R₀ B₀ (targetMap G' fZ))) ≠ 0
    rw [hdetEq]
    exact hdet
  have hxW : ∀ i, x i ∈ W := by
    intro i
    let yV : V.toScheme := ⟨x i, hxV i⟩
    obtain ⟨z, hz⟩ := hZsurj yV
    have hzi : (Z.subschemeι ≫ V.ι) z = x i := congrArg V.ι hz
    let r : G.arrows.left := G.identity.left (x i)
    have hsource : G.source.left r = x i := by
      simpa using congr_fun (congrArg (fun k => k.left.base) G.source_identity) (x i)
    have hfnot : f ∉ (j (G.target.left r)).asIdeal := hfOrbit i r hsource
    have htarget : G.target.left r = x i := by
      simpa using congr_fun (congrArg (fun k => k.left.base) G.target_identity) (x i)
    rw [htarget] at hfnot
    have hspec : j (x i) ∈ specOpen := (hmemSpec _).mpr hfnot
    let ySource : sourceOpen.toScheme := ⟨x i, hspec⟩
    have hnorm := hnormAtChosen i z hzi
    exact hpointInW (x i) ySource rfl z (hlift z ySource hzi) hnorm
  refine ⟨h, hhI, ?_⟩
  change Stacks.Groupoids.IsInvariantOpen G W ∧ IsAffineOpen W ∧ ∀ i, x i ∈ W
  exact ⟨hInvW, hAffineW, hxW⟩

/-- **[Stacks, Tag 0ABF].** Let `G` be a groupoid scheme whose source and target are finite and
of finite presentation, let `x : ι → U` be finitely many points whose orbits consist of generic
points of irreducible components of the object scheme, let `j : U ⟶ Spec A` be an immersion, and
let `I` be an ideal of `A` whose vanishing locus misses the image of `j` and whose union with
that image is closed. Then some `h ∈ I` has `j ⁻¹ D(h)` an invariant affine open of the object
scheme containing all the `x i`.

Nothing is assumed beyond the hypotheses of the tag. This is
`AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen`, which carries
[Stacks, Tag 06AD] as the hypothesis `H06AD`, with that hypothesis discharged by
`Stacks.Thickenings.forall_isAffine_of_isThickening`, which is Tag 06AD. -/
@[stacks 0ABF]
theorem exists_mem_ideal_invariant_affine_preimage_basicOpen'
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    (hs : FinitePresentation G.source.left)
    (ht : FinitePresentation G.target.left)
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z)
    {A : Type u} [CommRing A]
    (j : G.objects.left ⟶ Spec (CommRingCat.of A)) [IsImmersion j]
    (I : Ideal A)
    (hdisj : Disjoint (Set.range (j : G.objects.left → Spec (CommRingCat.of A)))
      (PrimeSpectrum.zeroLocus (I : Set A)))
    (hclosed : IsClosed (PrimeSpectrum.zeroLocus (I : Set A) ∪
      Set.range (j : G.objects.left → Spec (CommRingCat.of A)))) :
    ∃ h : A, h ∈ I ∧
      (let W := j ⁻¹ᵁ PrimeSpectrum.basicOpen h
       Stacks.Groupoids.IsInvariantOpen G W ∧ IsAffineOpen W ∧ ∀ i, x i ∈ W) :=
  exists_mem_ideal_invariant_affine_preimage_basicOpen
    Stacks.Thickenings.forall_isAffine_of_isThickening G hs ht x hx j I hdisj hclosed

end AlgebraicGeometry

end
