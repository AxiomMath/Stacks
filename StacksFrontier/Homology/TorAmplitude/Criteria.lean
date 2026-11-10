module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Data.Int.Interval
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.TorAmplitude.Triangle

/-!
# Criteria for Tor amplitude of a complex

Let `R` be a commutative ring. This file records the two standard criteria that reduce a
Tor-amplitude bound on an object of the derived category `D(R)` to Tor-amplitude bounds on
pieces concentrated in a single degree:

* for a bounded complex, the bound follows from bounds on its terms `K^i`;
* for a bounded object of `D(R)`, the bound follows from bounds on its cohomology modules
  `H^i(K)`.

In both cases the degree-`i` piece must have Tor amplitude in `[a - i, b - i]`, and in both
cases the finite-Tor-dimension statement is a consequence: a finite complex of modules of
finite Tor dimension has finite Tor dimension, and likewise for an object of `D^b(R)` all of
whose cohomology modules have finite Tor dimension.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitude_and_finiteTorDimension_of_bounded_complex`:
  Tor amplitude of a bounded complex from Tor amplitude of its terms, Stacks 066H.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_of_cohomology`: Tor amplitude of a bounded
  derived object from Tor amplitude of its cohomology modules, Stacks 066I.

## Implementation notes

Tor amplitude is the predicate `Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn` of
`StacksFrontier.Homology.TorAmplitude.Triangle`, taken relative to a derived tensoring datum
`Stacks.TorAmplitudeTriangle.DerivedTensoring`; the derived tensoring datum is a parameter, so no
instance of it has to be constructed here. A module is regarded as an object of `D(R)` by placing
it in degree zero via `DerivedCategory.singleFunctor`, and finite Tor dimension is expressed as the
existence of an interval in which the object has Tor amplitude.

The proof of Stacks 066H is an induction on the length of the complex, splitting off the top
term with the distinguished triangle attached to the stupid truncation
`HomologicalComplex.stupidTrunc`; the proof of Stacks 066I is an induction on the length of the
cohomological support, splitting the object with the truncation triangle of the standard
t-structure. Both inductions are fed by part (2) of Stacks 0655.

## References

* [Stacks Project, Tag 066H](https://stacks.math.columbia.edu/tag/066H)
* [Stacks Project, Tag 066I](https://stacks.math.columbia.edu/tag/066I)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ComplexShape HomologicalComplex

namespace StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

variable {R : Type} [CommRing R]

/-! ### Stability properties of Tor amplitude -/

/-- Tor amplitude in `[a, b]` implies Tor amplitude in any larger interval. -/
private lemma hasTorAmplitudeIn_mono (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    {X : Stacks.TorAmplitudeTriangle.DerivedCat R} {a b a' b' : ℤ}
    (h : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D X a b) (ha : a' ≤ a) (hb : b ≤ b') :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D X a' b' := by
  intro M i hi
  apply h M i
  omega

/-- A zero object has Tor amplitude in every interval. -/
private lemma hasTorAmplitudeIn_of_isZero (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    {X : Stacks.TorAmplitudeTriangle.DerivedCat R} (hX : IsZero X) (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D X a b := by
  intro M i _
  exact (DerivedCategory.homologyFunctor (ModuleCat.{0} R) i).map_isZero
    ((D.derTensor M).map_isZero hX)

/-- If a module placed in degree zero has Tor amplitude in `[a - i, b - i]`, then the same
module placed in degree `i` has Tor amplitude in `[a, b]`. -/
private lemma hasTorAmplitudeIn_singleFunctor (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    (X : ModuleCat.{0} R) (i a b : ℤ)
    (h : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
      ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj X) (a - i) (b - i)) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
      ((DerivedCategory.singleFunctor (ModuleCat.{0} R) i).obj X) a b := by
  intro M j hj
  have hz := h M (-i + j) (by omega)
  let e₁ : ((DerivedCategory.singleFunctor (ModuleCat.{0} R) i).obj X) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj X)⟦-i⟧ :=
    ((DerivedCategory.singleFunctors (ModuleCat.{0} R)).shiftIso (-i) i 0 (by omega)).symm.app X
  let e₂ : (D.derTensor M).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{0} R) i).obj X) ≅
      ((D.derTensor M).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj X))⟦-i⟧ :=
    (D.derTensor M).mapIso e₁ ≪≫
      ((D.derTensor M).commShiftIso (-i)).app _
  let e₃ := (DerivedCategory.homologyFunctor (ModuleCat.{0} R) j).mapIso e₂ ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{0} R) 0).shiftIso
      (-i) j (-i + j) rfl).app _
  exact hz.of_iso e₃

/-! ### Tor amplitude of a bounded complex (Stacks 066H) -/

/-- The Tor-amplitude bound of Stacks 066H for a complex with explicit strict bounds
`[l, l + n]`, proved by induction on `n`. -/
private lemma hasTorAmplitudeIn_of_strict_bounds
  (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    (a b l c : ℤ) (n : ℕ) (hn : l + n = c)
    (K : CochainComplex (ModuleCat.{0} R) ℤ)
    (hge : K.IsStrictlyGE l) (hle : K.IsStrictlyLE c)
    (hK : ∀ i : ℤ, Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
      ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj (K.X i))
      (a - i) (b - i)) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D (DerivedCategory.Q.obj K) a b := by
  induction n generalizing c K with
  | zero =>
      have hc : c = l := by omega
      subst c
      let _ : K.IsStrictlyGE l := hge
      let _ : K.IsStrictlyLE l := by simpa using hle
      obtain ⟨X, ⟨e⟩⟩ := CochainComplex.exists_iso_single K l
      exact hasTorAmplitudeIn_of_iso D
        (DerivedCategory.Q.mapIso e ≪≫
          (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{0} R) l).symm.app X).symm
        (hasTorAmplitudeIn_singleFunctor D X l a b
        (hasTorAmplitudeIn_of_iso D
          ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).mapIso
            ((HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℤ) l).mapIso e ≪≫
              HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) l X))
          (hK l)))
  | succ n ih =>
      let _ : K.IsStrictlyLE c := hle
      obtain ⟨f, g, h, hT⟩ := DerivedCategory.exists_distTriang_singleFunctor_obj_X_stupidTrunc K c
      let T := Triangle.mk f g h
      apply Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₂_of_obj₁_obj₃ D T hT a b
      · exact hasTorAmplitudeIn_singleFunctor D (K.X c) c a b (hK c)
      · apply ih (c := c - 1) (by omega)
        · rw [CochainComplex.isStrictlyGE_iff] at hge ⊢
          intro i hi
          exact IsZero.of_iso (hge i hi)
              (K.stupidTruncXIso _
                (DerivedCategory.embeddingUpIntLE_f_toNat (c - 1) i (by omega)))
        · infer_instance
        · intro i
          by_cases hi : i ≤ c - 1
          · exact hasTorAmplitudeIn_of_iso D
              ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).mapIso
                (K.stupidTruncXIso _
                  (DerivedCategory.embeddingUpIntLE_f_toNat (c - 1) i hi)).symm) (hK i)
          · exact hasTorAmplitudeIn_of_isZero D
              ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).map_isZero
                (DerivedCategory.isZero_stupidTrunc_X_of_lt K (by omega))) _ _

/-- **Stacks 066H.** A bounded complex whose term in degree `i` has Tor amplitude in
`[a - i, b - i]` has Tor amplitude in `[a, b]`. In particular, if every term of a bounded
complex has finite Tor dimension, then the complex has finite Tor dimension. -/
@[stacks 066H]
theorem hasTorAmplitude_and_finiteTorDimension_of_bounded_complex
    {R : Type} [CommRing R] (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    (K : CochainComplex (ModuleCat.{0} R) ℤ)
    (_hK : ∃ m n : ℤ, K.IsStrictlyGE m ∧ K.IsStrictlyLE n) :
    (∀ a b : ℤ, (∀ i : ℤ, Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
          ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj (K.X i))
          (a - i) (b - i)) →
        Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D (DerivedCategory.Q.obj K) a b) ∧
      ((∀ i : ℤ, ∃ aᵢ bᵢ : ℤ, Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
          ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).obj (K.X i)) aᵢ bᵢ) →
        ∃ a' b' : ℤ, Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
          (DerivedCategory.Q.obj K) a' b') := by
  obtain ⟨m, n, hm, hn⟩ := _hK
  let c := max m n
  have hc : K.IsStrictlyLE c := by
    rw [CochainComplex.isStrictlyLE_iff] at hn ⊢
    intro i hi
    exact hn i (lt_of_le_of_lt (le_max_right _ _) hi)
  have hmc : m ≤ c := le_max_left _ _
  refine ⟨fun a b h => hasTorAmplitudeIn_of_strict_bounds D a b m c (c - m).toNat (by omega)
    K hm hc h, fun h => ?_⟩
  choose a b hab using h
  let s := Finset.range ((c - m).toNat + 1)
  have ha_nonempty :
      (s.image (fun k : ℕ => a (m + (k : ℤ)) + (m + k))).Nonempty := by
    refine ⟨a m + m, Finset.mem_image.mpr ⟨0, ?_, by simp⟩⟩
    simp [s]
  have hb_nonempty :
      (s.image (fun k : ℕ => b (m + (k : ℤ)) + (m + k))).Nonempty := by
    refine ⟨b m + m, Finset.mem_image.mpr ⟨0, ?_, by simp⟩⟩
    simp [s]
  let a' := (s.image (fun k : ℕ => a (m + (k : ℤ)) + (m + k))).min' ha_nonempty
  let b' := (s.image (fun k : ℕ => b (m + (k : ℤ)) + (m + k))).max' hb_nonempty
  refine ⟨a', b', hasTorAmplitudeIn_of_strict_bounds D a' b' m c (c - m).toNat
    (by omega) K hm hc (fun i => ?_)⟩
  by_cases hi : m ≤ i ∧ i ≤ c
  · obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k ∈ s ∧ m + k = i := by
      refine ⟨(i - m).toNat, ?_, by omega⟩
      simp only [s, Finset.mem_range]
      omega
    exact hasTorAmplitudeIn_mono D (hab (m + k)) (by
      dsimp [a']
      have := Finset.min'_le
        (s.image (fun k : ℕ => a (m + (k : ℤ)) + (m + k)))
        (a (m + k) + (m + k)) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
      omega) (by
      dsimp [b']
      have := Finset.le_max'
        (s.image (fun k : ℕ => b (m + (k : ℤ)) + (m + k)))
        (b (m + k) + (m + k)) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
      omega)
  · have hXi : IsZero (K.X i) := by
      push Not at hi
      rcases lt_or_ge i m with him | him
      · rw [CochainComplex.isStrictlyGE_iff] at hm
        exact hm i him
      · rw [CochainComplex.isStrictlyLE_iff] at hc
        exact hc i (hi him)
    exact hasTorAmplitudeIn_of_isZero D
      ((DerivedCategory.singleFunctor (ModuleCat.{0} R) 0).map_isZero hXi) _ _

/-! ### Tor amplitude from the cohomology modules (Stacks 066I) -/

/-- An object concentrated in degree `c` has Tor amplitude in `[a, b]` as soon as its
degree-`c` cohomology, placed in degree zero, has Tor amplitude in `[a - c, b - c]`. -/
private lemma hasTorAmplitudeIn_of_isGE_isLE (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    (X : DerivedCategory (ModuleCat R)) (c a b : ℤ) [X.IsGE c] [X.IsLE c]
    (h : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) c).obj X))
      (a - c) (b - c)) : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D X a b := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X c
  let q : ((DerivedCategory.homologyFunctor (ModuleCat R) c).obj X) ≅ Y :=
    (DerivedCategory.homologyFunctor (ModuleCat R) c).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) c).app Y
  let e' : X ≅ (DerivedCategory.singleFunctor (ModuleCat R) c).obj
      ((DerivedCategory.homologyFunctor (ModuleCat R) c).obj X) :=
    e ≪≫ (DerivedCategory.singleFunctor (ModuleCat R) c).mapIso q.symm
  exact hasTorAmplitudeIn_of_iso D e'.symm
    (hasTorAmplitudeIn_singleFunctor D _ c a b h)

/-- Below the truncation degree, the inclusion of the truncation `τ_{<c}` induces an
isomorphism on cohomology. -/
private lemma isIso_homology_truncLT (R : Type) [CommRing R]
    (c i : ℤ) (hi : i < c) (X : DerivedCategory (ModuleCat R)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      ((DerivedCategory.TStructure.t.truncLTι c).app X)) := by
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      ((DerivedCategory.TStructure.t.truncLTι c).app X)) := by
    change Epi ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      ((DerivedCategory.TStructure.t.triangleLTGE c).obj X).mor₁)
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff
      ((DerivedCategory.TStructure.t.triangleLTGE c).obj X)
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished c X) i]
    exact (DerivedCategory.isZero_of_isGE _ c i hi).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      ((DerivedCategory.TStructure.t.truncLTι c).app X)) := by
    change Mono ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      ((DerivedCategory.TStructure.t.triangleLTGE c).obj X).mor₁)
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      ((DerivedCategory.TStructure.t.triangleLTGE c).obj X)
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished c X) (i - 1) i (by omega)]
    exact (DerivedCategory.isZero_of_isGE _ c (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- In the truncation degree, the projection to the truncation `τ_{≥c}` induces an
isomorphism on cohomology. -/
private lemma isIso_homology_truncGE (R : Type) [CommRing R]
    (c : ℤ) (X : DerivedCategory (ModuleCat R)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) c).map
      ((DerivedCategory.TStructure.t.truncGEπ c).app X)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE c).obj X
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished c X
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) c).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT c (c + 1) rfl]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (c - 1) (c + 1) (by omega)).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat R) c).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT c]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (c - 1) c (by omega)).eq_of_src _ _
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) c).map T.mor₂)
  exact isIso_of_mono_of_epi _

/-- The Tor-amplitude bound of Stacks 066I for an object with cohomological support in
`[c, c + n]`, proved by induction on `n`. -/
private lemma hasTorAmplitudeIn_of_cohomology_aux
    (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    (a b c : ℤ) (n : ℕ)
    (X : DerivedCategory (ModuleCat R)) [X.IsGE c] [hle : X.IsLE (c + n)]
    (h : ∀ i : ℤ, Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X))
      (a - i) (b - i)) : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D X a b := by
  induction n generalizing X with
  | zero =>
      have : X.IsLE c := by simpa only [Nat.cast_zero, add_zero] using hle
      exact hasTorAmplitudeIn_of_isGE_isLE D X c a b (h c)
  | succ n ih =>
      let d : ℤ := c + n + 1
      have h₁ : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
          ((DerivedCategory.TStructure.t.truncLT d).obj X) a b := by
        have : ((DerivedCategory.TStructure.t.truncLT d).obj X).IsLE (c + (n : ℤ)) :=
          DerivedCategory.TStructure.t.isLE_of_le _ (d - 1) (c + n) (by
            dsimp [d]
            omega)
        apply ih
        intro i
        by_cases hi : i < d
        · have := isIso_homology_truncLT R d i hi X
          exact hasTorAmplitudeIn_of_iso D
            ((DerivedCategory.singleFunctor (ModuleCat R) 0).mapIso
              (asIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
                ((DerivedCategory.TStructure.t.truncLTι d).app X))).symm) (h i)
        · exact hasTorAmplitudeIn_of_isZero D
            ((DerivedCategory.singleFunctor (ModuleCat R) 0).map_isZero
              (DerivedCategory.isZero_of_isLE
                ((DerivedCategory.TStructure.t.truncLT d).obj X) (d - 1) i (by omega))) _ _
      have : X.IsLE d := DerivedCategory.TStructure.t.isLE_of_le _ (c + (n + 1 : ℕ)) d (by
        dsimp [d]
        omega)
      have h₃ : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
          ((DerivedCategory.TStructure.t.truncGE d).obj X) a b := by
        apply hasTorAmplitudeIn_of_isGE_isLE D _ d a b
        have := isIso_homology_truncGE R d X
        exact hasTorAmplitudeIn_of_iso D
          ((DerivedCategory.singleFunctor (ModuleCat R) 0).mapIso
            (asIso ((DerivedCategory.homologyFunctor (ModuleCat R) d).map
              ((DerivedCategory.TStructure.t.truncGEπ d).app X)))) (h d)
      exact Stacks.TorAmplitudeTriangle.hasTorAmplitudeIn_obj₂_of_obj₁_obj₃ D
        ((DerivedCategory.TStructure.t.triangleLTGE d).obj X)
        (DerivedCategory.TStructure.t.triangleLTGE_distinguished d X) a b h₁ h₃

/-- **Stacks 066I.** A bounded derived object has Tor amplitude in `[a, b]` if its degree-`i`
cohomology module has Tor amplitude in `[a - i, b - i]` for every `i`. In particular, if all
of its cohomology modules have finite Tor dimension, then so does the derived object. -/
@[stacks 066I]
theorem hasTorAmplitudeIn_of_cohomology (R : Type) [CommRing R]
    (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    (K : DerivedCategory.Bounded (ModuleCat R)) :
    (∀ a b : ℤ,
      (∀ i : ℤ,
        Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
          ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj))
          (a - i) (b - i)) →
        Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D K.obj a b) ∧
      ((∀ i : ℤ, ∃ a b : ℤ,
        Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
          ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj)) a b) →
        ∃ a b : ℤ, Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D K.obj a b) := by
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := K.property
  let _ : K.obj.IsGE c := hc
  let _ : K.obj.IsLE d := hd
  have first : ∀ a b : ℤ,
      (∀ i : ℤ, Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
          ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj))
        (a - i) (b - i)) → Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D K.obj a b := by
    intro a b h
    by_cases hcd : c ≤ d
    · let _ : K.obj.IsLE (c + ((d - c).toNat : ℤ)) := by
        apply DerivedCategory.TStructure.t.isLE_of_le _ d _ (by omega)
      exact hasTorAmplitudeIn_of_cohomology_aux D a b c (d - c).toNat K.obj h
    · exact hasTorAmplitudeIn_of_isZero D
        (DerivedCategory.TStructure.t.isZero K.obj d c (by omega)) a b
  refine ⟨first, fun h => ?_⟩
  choose lo hi htor using h
  let s : Finset ℤ := Finset.Icc c d
  let N : ℤ := ∑ i ∈ s, (|lo i + i| + |hi i + i|)
  refine ⟨-N, N, first _ _ fun i => ?_⟩
  by_cases hi_mem : i ∈ s
  · have hle : |lo i + i| + |hi i + i| ≤ ∑ j ∈ s, (|lo j + j| + |hi j + j|) :=
      Finset.single_le_sum (s := s) (f := fun j => |lo j + j| + |hi j + j|)
        (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hi_mem
    have := neg_abs_le (lo i + i)
    have := le_abs_self (hi i + i)
    have := abs_nonneg (lo i + i)
    have := abs_nonneg (hi i + i)
    refine hasTorAmplitudeIn_mono D (htor i) ?_ ?_ <;> dsimp [N] <;> omega
  · have hout : i < c ∨ d < i := by
      simp only [s, Finset.mem_Icc] at hi_mem
      omega
    have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj) := by
      rcases hout with hout | hout
      exacts [DerivedCategory.isZero_of_isGE K.obj c i hout,
        DerivedCategory.isZero_of_isLE K.obj d i hout]
    exact hasTorAmplitudeIn_of_isZero D
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).map_isZero hz) _ _

end

end StacksDraft.TorAmplitude
