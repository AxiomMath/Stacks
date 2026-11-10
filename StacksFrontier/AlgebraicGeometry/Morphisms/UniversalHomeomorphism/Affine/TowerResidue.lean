module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Subalgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCube
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Tower
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Order.Zorn
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples

/-!
# Universal homeomorphisms with unchanged residue fields

For an injective map of commutative rings, the induced map on spectra is a universal
homeomorphism inducing isomorphisms on residue fields exactly when every finite set in the
larger ring is contained in an algebra obtained by successively adjoining elements whose
squares and cubes belong to the algebra generated at the preceding stage.

## Main definitions

No new definitions are introduced.

## Main results

* `universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube`
  characterizes universal homeomorphisms which induce isomorphisms on residue fields.

## Implementation notes

The inclusion of rings is represented by an injective algebra map. The intermediate algebra
`A[b₁, ..., bᵢ₋₁]` is represented by `Algebra.adjoin A` applied to the range of the prefix of
the finite sequence of generators. The forward direction is a Zorn argument over the
subalgebras all of whose finite subsets admit such a tower; the reverse direction reads the
surjectivity of the residue-field maps off the fact that a subfield containing the square and
the cube of an element contains the element.

## References

* [Stacks Project, Tag 0CND](https://stacks.math.columbia.edu/tag/0CND)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private def HasFiniteSquareCubeTower {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (E : Finset B) : Prop :=
  ∃ (n : ℕ) (b : Fin n → B),
    (↑E : Set B) ⊆ Algebra.adjoin A (Set.range b) ∧
      ∀ i : Fin n,
        b i ^ 2 ∈ Algebra.adjoin A
            (Set.range (fun j : Fin i ↦ b (Fin.castLE i.isLt.le j))) ∧
          b i ^ 3 ∈ Algebra.adjoin A
            (Set.range (fun j : Fin i ↦ b (Fin.castLE i.isLt.le j)))

private def SquareCubeGood {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (C : Subalgebra A B) : Prop :=
  ∀ E : Finset B, (↑E : Set B) ⊆ C → HasFiniteSquareCubeTower (A := A) E

/-- Two sets each supported over `C` after adjoining `b` share a common finite support. -/
private lemma exists_common_support_adjoin {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (C : Subalgebra A B) (b : B) {S T : Set B}
    (hS : ∃ D : Finset B, (↑D : Set B) ⊆ C ∧ S ⊆ Algebra.adjoin A ((↑D : Set B) ∪ {b}))
    (hT : ∃ D : Finset B, (↑D : Set B) ⊆ C ∧ T ⊆ Algebra.adjoin A ((↑D : Set B) ∪ {b})) :
    ∃ D : Finset B, (↑D : Set B) ⊆ C ∧ S ⊆ Algebra.adjoin A ((↑D : Set B) ∪ {b}) ∧
      T ⊆ Algebra.adjoin A ((↑D : Set B) ∪ {b}) := by
  classical
  obtain ⟨D, hD, hSD⟩ := hS
  obtain ⟨D', hD', hTD'⟩ := hT
  exact ⟨D ∪ D', by simpa only [Finset.coe_union] using Set.union_subset hD hD',
    hSD.trans (Algebra.adjoin_mono fun _ _ => by aesop),
    hTD'.trans (Algebra.adjoin_mono fun _ _ => by aesop)⟩

private lemma exists_finite_support_adjoin {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (C : Subalgebra A B) (b y : B)
    (hy : y ∈ Algebra.adjoin A ((C : Set B) ∪ {b})) :
    ∃ D : Finset B, (↑D : Set B) ⊆ C ∧
      y ∈ Algebra.adjoin A ((↑D : Set B) ∪ {b}) := by
  classical
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
      by_cases hxc : x ∈ C
      · exact ⟨{x}, by simpa using hxc, Algebra.subset_adjoin (by simp)⟩
      · obtain rfl : x = b := by simpa [hxc] using hx
        exact ⟨∅, by simp, Algebra.subset_adjoin (by simp)⟩
  | algebraMap r =>
      exact ⟨∅, by simp, Subalgebra.algebraMap_mem _ _⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨D, hD, hxD, hyD⟩ := exists_common_support_adjoin C b
        (S := {x}) (T := {y}) (by simpa using ihx) (by simpa using ihy)
      exact ⟨D, hD, add_mem (hxD rfl) (hyD rfl)⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨D, hD, hxD, hyD⟩ := exists_common_support_adjoin C b
        (S := {x}) (T := {y}) (by simpa using ihx) (by simpa using ihy)
      exact ⟨D, hD, mul_mem (hxD rfl) (hyD rfl)⟩

private lemma exists_finset_support_adjoin {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (C : Subalgebra A B) (b : B) (E : Finset B)
    (hE : ∀ x ∈ E, x ∈ Algebra.adjoin A ((C : Set B) ∪ {b})) :
    ∃ D : Finset B, (↑D : Set B) ⊆ C ∧
      (↑E : Set B) ⊆ Algebra.adjoin A ((↑D : Set B) ∪ {b}) := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert x E hx ih =>
      obtain ⟨D, hD, hxD, hE'⟩ := exists_common_support_adjoin C b (S := {x}) (T := ↑E)
        (by simpa using exists_finite_support_adjoin C b x (hE x (Finset.mem_insert_self _ _)))
        (ih fun y hy => hE y (Finset.mem_insert_of_mem hy))
      exact ⟨D, hD, by simpa [Set.insert_subset_iff] using And.intro hxD hE'⟩

private lemma fin_snoc_castLE_lt {B : Type*} {n : ℕ} (s : Fin n → B) (b : B)
    (i : Fin n) (j : Fin i) :
    Fin.snoc (α := fun _ : Fin (n + 1) => B) s b
        (Fin.castLE i.castSucc.isLt.le j) = s (Fin.castLE i.isLt.le j) := by
  rw [show Fin.castLE i.castSucc.isLt.le j = (Fin.castLE i.isLt.le j).castSucc from Fin.ext rfl,
    Fin.snoc_castSucc]

private lemma fin_snoc_castLE_last {B : Type*} {n : ℕ} (s : Fin n → B) (b : B)
    (j : Fin n) :
    Fin.snoc (α := fun _ : Fin (n + 1) => B) s b
        (Fin.castLE (Fin.last n).isLt.le j) = s j := by
  rw [show Fin.castLE (Fin.last n).isLt.le j = j.castSucc from Fin.ext rfl, Fin.snoc_castSucc]

private lemma range_snoc_castLE_castSucc {B : Type*} {n : ℕ} (s : Fin n → B) (b : B)
    (i : Fin n) :
    Set.range (fun k : Fin i.castSucc ↦
        (Fin.snoc (α := fun _ : Fin (n + 1) => B) s b) (Fin.castLE i.castSucc.isLt.le k)) =
      Set.range (fun k : Fin i ↦ s (Fin.castLE i.isLt.le k)) := by
  exact congrArg Set.range (funext (fin_snoc_castLE_lt s b i))

private lemma range_snoc_castLE_last {B : Type*} {n : ℕ} (s : Fin n → B) (b : B) :
    Set.range (fun k : Fin (Fin.last n) ↦
        (Fin.snoc (α := fun _ : Fin (n + 1) => B) s b) (Fin.castLE (Fin.last n).isLt.le k)) =
      Set.range s := by
  exact congrArg Set.range (funext (fin_snoc_castLE_last s b))

private lemma squareCubeTower_snoc {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (n : ℕ) (s : Fin n → B)
    (hsteps : ∀ i : Fin n,
      s i ^ 2 ∈ Algebra.adjoin A
          (Set.range (fun j : Fin i ↦ s (Fin.castLE i.isLt.le j))) ∧
        s i ^ 3 ∈ Algebra.adjoin A
          (Set.range (fun j : Fin i ↦ s (Fin.castLE i.isLt.le j))))
    (b : B)
    (h2 : b ^ 2 ∈ Algebra.adjoin A (Set.range s))
    (h3 : b ^ 3 ∈ Algebra.adjoin A (Set.range s))
    (E : Finset B)
    (hE : (↑E : Set B) ⊆ Algebra.adjoin A (Set.range s ∪ {b})) :
    HasFiniteSquareCubeTower (A := A) E := by
  refine ⟨n + 1, Fin.snoc (α := fun _ : Fin (n + 1) => B) s b, ?_, fun i => ?_⟩
  · rwa [Fin.range_snoc, Set.insert_eq, Set.union_comm]
  · cases i using Fin.lastCases with
    | last =>
        rw [range_snoc_castLE_last]
        simpa using And.intro h2 h3
    | cast j =>
        rw [range_snoc_castLE_castSucc]
        simpa using hsteps j

private lemma squareCubeGood_adjoin {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (C : Subalgebra A B) (hgood : SquareCubeGood C) (b : B)
    (hb2 : b ^ 2 ∈ C) (hb3 : b ^ 3 ∈ C) :
    SquareCubeGood (Algebra.adjoin A ((C : Set B) ∪ {b})) := by
  classical
  intro E hE
  obtain ⟨D, hD, hED⟩ := exists_finset_support_adjoin C b E (fun x hx => hE hx)
  let F : Finset B := insert (b ^ 2) (insert (b ^ 3) D)
  have hF : (↑F : Set B) ⊆ C := by
    simp only [F, Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨hb2, hb3, hD⟩
  obtain ⟨n, s, hFtower, hsteps⟩ := hgood F hF
  have hgen : (↑D : Set B) ∪ {b} ⊆ Algebra.adjoin A (Set.range s ∪ {b}) := by
    rintro x (hx | rfl)
    · exact Algebra.adjoin_mono Set.subset_union_left (hFtower (by simp [F, hx]))
    · exact Algebra.subset_adjoin (Or.inr rfl)
  exact squareCubeTower_snoc n s hsteps b (hFtower (by simp [F])) (hFtower (by simp [F])) E
    (hED.trans (Algebra.adjoin_le_iff.mpr hgen))

private lemma map_mem_of_mem_adjoin {A B K : Type*} [CommRing A] [CommRing B] [Field K]
    [Algebra A B] (φ : B →+* K) (F : Subfield K) (hbase : ∀ a, φ (algebraMap A B a) ∈ F)
    {s : Set B} (hs : ∀ x ∈ s, φ x ∈ F) {z : B} (hz : z ∈ Algebra.adjoin A s) : φ z ∈ F := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap a => exact hbase a
  | add x z _ _ ihx ihz => simpa only [map_add] using F.add_mem ihx ihz
  | mul x z _ _ ihx ihz => simpa only [map_mul] using F.mul_mem ihx ihz

private theorem residueField_map_surjective_of_finite_squareCubeTowers
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (htower : ∀ E : Finset B, HasFiniteSquareCubeTower (A := A) E)
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : p = q.comap (algebraMap A B)) :
    Function.Surjective (Ideal.ResidueField.map p q (algebraMap A B) hpq) := by
  classical
  let F : Subfield q.ResidueField := (Ideal.ResidueField.map p q (algebraMap A B) hpq).fieldRange
  have hbase (a : A) :
      algebraMap B q.ResidueField (algebraMap A B a) ∈ F :=
    RingHom.mem_fieldRange.mpr ⟨algebraMap A p.ResidueField a,
      Ideal.ResidueField.map_algebraMap p q (algebraMap A B) hpq a⟩
  have hgen (y : B) : algebraMap B q.ResidueField y ∈ F := by
    obtain ⟨n, b, hy, hsteps⟩ := htower {y}
    have hindex : ∀ m : ℕ, ∀ i : Fin n, i.val = m →
        algebraMap B q.ResidueField (b i) ∈ F := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
          intro i him
          have hs : ∀ x ∈ Set.range (fun j : Fin i ↦ b (Fin.castLE i.isLt.le j)),
              algebraMap B q.ResidueField x ∈ F := by
            rintro _ ⟨j, rfl⟩
            exact ih j.val (by omega) (Fin.castLE i.isLt.le j) rfl
          have key {z : B} (hz : z ∈ Algebra.adjoin A (Set.range
              (fun j : Fin i ↦ b (Fin.castLE i.isLt.le j)))) :
              algebraMap B q.ResidueField z ∈ F :=
            map_mem_of_mem_adjoin (algebraMap B q.ResidueField) F hbase hs hz
          exact Subfield.mem_of_sq_mem_of_cube_mem F
            (by simpa only [map_pow] using key (hsteps i).1)
            (by simpa only [map_pow] using key (hsteps i).2)
    exact map_mem_of_mem_adjoin (algebraMap B q.ResidueField) F hbase
      (Set.forall_mem_range.mpr fun i => hindex i.val i rfl) (z := y) (hy (by simp))
  intro x
  obtain ⟨y, z, hz, hx⟩ := Ideal.exists_div_algebraMap_residueField_eq q x
  rw [← hx]
  exact RingHom.mem_fieldRange.mp (F.div_mem (hgen y) (hgen z))

private lemma squareCubeGood_iSup_of_isChain {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (c : Set (Subalgebra A B)) (hc : ∀ C ∈ c, SquareCubeGood C)
    (hch : IsChain (· ≤ ·) c) [Nonempty c] :
    SquareCubeGood (⨆ i : c, (i : Subalgebra A B)) := by
  let K : c → Subalgebra A B := fun i => i.1
  have hdir : Directed (· ≤ ·) K := hch.directedOn.directed_val
  intro E hE
  have hE' : (↑E : Set B) ⊆ ⋃ i, (K i : Set B) := by
    rwa [← Subalgebra.coe_iSup_of_directed hdir]
  obtain ⟨i, hi⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion
    (f := fun i => (K i : Set B)) hdir hE'
  exact hc i.1 i.2 E hi

private lemma exists_sq_mem_cube_mem_of_ne_top {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B]
    (hAB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hres : ∀ x : Spec (.of B), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op).residueFieldMap x))
    (C : Subalgebra A B) (hC : C ≠ ⊤) :
    ∃ b : B, b ∉ C ∧ b ^ 2 ∈ C ∧ b ^ 3 ∈ C := by
  have := universalHomeomorphism_specMap_to_subring C
    (universalHomeomorphism_specMap_to_subalgebra hAB C)
  let e := subalgebraToSubringEquiv C
  let fCB := Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op
  let gIso : Spec (.of C) ≅ Spec (.of C.toSubring) :=
    Scheme.Spec.mapIso e.symm.toCommRingCatIso.op
  let g := gIso.hom
  have hcomp : fCB ≫ g =
      Scheme.Spec.map (CommRingCat.ofHom C.toSubring.subtype).op := by
    change Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫
      Spec.map e.symm.toCommRingCatIso.hom =
      Spec.map (CommRingCat.ofHom C.toSubring.subtype)
    rw [← Spec.map_comp]
    congr 1
  have hsubres : ∀ x : Spec (.of B), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom C.toSubring.subtype).op).residueFieldMap x) := by
    intro x
    rw [← hcomp, Scheme.residueFieldMap_comp]
    have hgres : IsIso (g.residueFieldMap (fCB x)) := inferInstance
    exact IsIso.comp_isIso' hgres (isIso_residueFieldMap_specMap_to_subalgebra hAB hres C x)
  exact exists_not_mem_and_sq_mem_and_cube_mem_of_universalHomeomorphism_of_residueFieldMap_isIso
    C.toSubring hsubres fun h => hC (Subalgebra.toSubring_injective (by simpa using h))

private lemma squareCubeGood_top {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B]
    (hAB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hres : ∀ x : Spec (.of B), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op).residueFieldMap x)) :
    SquareCubeGood (⊤ : Subalgebra A B) := by
  classical
  have hbottom : SquareCubeGood (⊥ : Subalgebra A B) := fun E hE =>
    ⟨0, Fin.elim0, by simpa [Algebra.adjoin_empty] using hE, fun i => i.elim0⟩
  obtain ⟨C, -, hCgood, hCmax⟩ := zorn_le_nonempty₀ {C : Subalgebra A B | SquareCubeGood C}
    (fun c hc hch y hy =>
      have : Nonempty c := ⟨⟨y, hy⟩⟩
      ⟨⨆ i : c, (i : Subalgebra A B), squareCubeGood_iSup_of_isChain c hc hch,
        fun z hz => le_iSup (fun i : c => i.1) ⟨z, hz⟩⟩)
    ⊥ hbottom
  suffices hCeq : C = ⊤ from hCeq ▸ hCgood
  by_contra hCne
  obtain ⟨b, hbC, hb2, hb3⟩ := exists_sq_mem_cube_mem_of_ne_top hAB hres C hCne
  exact hbC (hCmax (squareCubeGood_adjoin C hCgood b hb2 hb3)
    (fun x hx => Algebra.subset_adjoin (Or.inl hx)) (Algebra.subset_adjoin (Or.inr rfl)))

private lemma range_castLE_eq_range_lt {B : Type*} {n : ℕ} (b : Fin n → B) (i : Fin n) :
    Set.range (fun j : Fin i ↦ b (Fin.castLE i.isLt.le j)) =
      Set.range (fun j : {j : Fin n // j < i} ↦ b j) := by
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨Fin.castLE i.isLt.le j, j.isLt⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.val.val, j.property⟩, rfl⟩

private lemma isIso_residueFieldMap_specMap_of_surjective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hsurj : ∀ (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
      (hpq : p = q.comap (algebraMap A B)),
      Function.Surjective (Ideal.ResidueField.map p q (algebraMap A B) hpq))
    (x : Spec (.of B)) :
    IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op).residueFieldMap x) := by
  let pSpec : Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B)) x
  let p : Ideal A := pSpec.asIdeal
  let q : Ideal B := x.asIdeal
  have : p.IsPrime := pSpec.isPrime
  have : q.IsPrime := x.isPrime
  have hpq : p = q.comap (algebraMap A B) := by
    simpa [p, q, pSpec, Spec.map_apply] using
      (PrimeSpectrum.comap_asIdeal (algebraMap A B) x)
  let ρ := Ideal.ResidueField.map p q (algebraMap A B) hpq
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  let eP := Scheme.Spec.residueFieldIso (.of A) pSpec
  let eQ := Scheme.Spec.residueFieldIso (.of B) x
  have hbridge : (eP.inv ≫ f.residueFieldMap x ≫ eQ.hom).hom = ρ := by
    simpa [eP, eQ, f, p, q, pSpec, ρ, Spec.map_apply] using
      specResidueFieldMap_bridge (CommRingCat.ofHom (algebraMap A B)) x
  have : IsIso (eP.inv ≫ f.residueFieldMap x ≫ eQ.hom) := by
    rw [(CommRingCat.hom_ext hbridge : _ = CommRingCat.ofHom ρ)]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨ρ.injective, hsurj p q hpq⟩
  have : IsIso (f.residueFieldMap x ≫ eQ.hom) := IsIso.of_isIso_comp_left eP.inv _
  exact IsIso.of_isIso_comp_right (f.residueFieldMap x) eQ.hom

/-- An injective extension induces a universal homeomorphism with unchanged residue fields
if and only if each finite subset is contained in an algebra generated by a sequence whose
successive elements have square and cube in the algebra generated by their predecessors. -/
@[stacks 0CND]
public theorem universalHomeomorphism_and_residueFieldIso_iff_finite_adjoin_square_cube
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : Function.Injective (algebraMap A B)) :
    let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
    (UniversalHomeomorphism f ∧ (∀ x, IsIso (f.residueFieldMap x))) ↔
      ∀ E : Finset B, ∃ (n : ℕ) (b : Fin n → B),
        (↑E : Set B) ⊆ Algebra.adjoin A (Set.range b) ∧
      ∀ i : Fin n,
        b i ^ 2 ∈ Algebra.adjoin A
            (Set.range (fun j : Fin i ↦ b (Fin.castLE i.isLt.le j))) ∧
          b i ^ 3 ∈ Algebra.adjoin A
              (Set.range (fun j : Fin i ↦ b (Fin.castLE i.isLt.le j))) := by
  intro f
  constructor
  · rintro ⟨hUH, hres⟩ E
    exact squareCubeGood_top hUH hres E fun _ _ => trivial
  · intro hfinite
    refine ⟨(universalHomeomorphism_spec_iff_finite_adjoin_tower A B hAB).mpr fun E => ?_,
      isIso_residueFieldMap_specMap_of_surjective
        (residueField_map_surjective_of_finite_squareCubeTowers hfinite)⟩
    obtain ⟨n, b, hE, hsteps⟩ := hfinite E
    exact ⟨n, b, hE, fun i => Or.inl (by simpa only [range_castLE_eq_range_lt] using hsteps i)⟩

end AlgebraicGeometry

end
