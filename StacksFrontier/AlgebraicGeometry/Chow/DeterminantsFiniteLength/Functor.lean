module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension

/-!
# The determinant functor

For a local ring `R`, formation of the determinant of a finite-length `R`-module is
functorial for isomorphisms: an isomorphism of modules carries admissible sequences to
admissible sequences and symbols to symbols, hence induces a linear equivalence of
determinants, and this assignment respects identities and composition. The values are
one-dimensional vector spaces over the residue field of `R`.

## Main definitions

* `Module.FiniteLength.determinantEquiv` is the equivalence of determinants induced by an
  isomorphism of modules.
* `Module.FiniteLength.FiniteLengthModuleIso` is the groupoid of finite-length modules and
  their isomorphisms.
* `Module.FiniteLength.OneDimensionalVectorSpaceIso` is the groupoid of one-dimensional
  vector spaces and their isomorphisms.
* `Module.FiniteLength.DeterminantFunctor` packages a functor together with its prescribed
  action on objects and isomorphisms.

## Main results

* `Module.FiniteLength.determinantFunctor` is the determinant functor.
* `Module.FiniteLength.determinantEquiv_symbol`, `Module.FiniteLength.determinantEquiv_refl`
  and `Module.FiniteLength.determinantEquiv_trans` specify it on symbols and make it
  functorial.
* `Module.FiniteLength.determinantEquiv_ext` says that an equivalence of determinants is
  determined by its values on symbols.

## Implementation notes

The two groupoids in the displayed equation of the source are modeled as cores of full
subcategories of module categories. The comparison isomorphisms in `DeterminantFunctor`
identify its values with the determinant spaces of Tag 02P6. The field `mapLinearEquiv` is
the map denoted `det_κ(u)` in the source; compatibility with symbols specifies this map,
and `map_iso` identifies it with the functor's action.

## References

* [Stacks Project, Tag 05M7](https://stacks.math.columbia.edu/tag/05M7)
-/

@[expose] public section

noncomputable section

open CategoryTheory
universe u v

namespace Module.FiniteLength
/-- Isomorphic modules have the same length. -/
public lemma moduleLength_eq_of_equiv {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    moduleLength R M = moduleLength R N := by
  change (Module.length R M).toNat = (Module.length R N).toNat
  exact congrArg ENat.toNat e.length_eq

/-- The image under an isomorphism of the span of the entries preceding an index is the span
of the entries preceding the corresponding index of the transported sequence. -/
public lemma spanBefore_map_equiv {R : Type u} {M N : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (E : M ≃ₗ[R] N) {n m : ℕ} (h : n = m) (e : Fin n → M) (i : Fin n) :
    Submodule.map (E : M →ₗ[R] N) (spanBefore (R := R) e i) =
      spanBefore (R := R)
        (fun j : Fin m => E (e (Fin.cast h.symm j))) (Fin.cast h i) := by
  rw [spanBefore, spanBefore, Submodule.map_span, Set.image_image]
  congr 1
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.cast h j, by simpa using hj, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.cast h.symm j, Fin.lt_def.mpr (by simpa using Fin.lt_def.mp hj), by simp⟩

/-- An isomorphism of modules carries a member of the span of the preceding entries to a member
of the span of the preceding entries of the transported sequence. -/
private theorem map_mem_spanBefore_of_equiv {R : Type u} {M N : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (E : M ≃ₗ[R] N) {n m : ℕ} (h : n = m) (e : Fin n → M) (i : Fin n) {x : M}
    (hx : x ∈ spanBefore (R := R) e i) :
    E x ∈ spanBefore (R := R) (fun j : Fin m => E (e (Fin.cast h.symm j))) (Fin.cast h i) := by
  rw [← spanBefore_map_equiv E h e i]
  exact ⟨x, hx, rfl⟩

/-- An isomorphism of modules carries an admissible sequence to an admissible sequence. -/
public lemma admissibleSequence_map_equiv {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) {n m : ℕ} (h : n = m)
    (e : Fin n → M) (he : IsAdmissibleSequence (R := R) e) :
    IsAdmissibleSequence (R := R)
      (fun j : Fin m => E (e (Fin.cast h.symm j))) := by
  intro i r hr
  simpa [map_smul] using map_mem_spanBefore_of_equiv E h e (Fin.cast h.symm i) (he _ r hr)

/-- The admissible sequence obtained by applying an isomorphism of modules entrywise. -/
public def admissibleSequenceMap {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N)
    (e : AdmissibleSequence R M) : AdmissibleSequence R N :=
  ⟨fun j => E (e.1 (Fin.cast h.symm j)),
    admissibleSequence_map_equiv E h e.1 e.2⟩

/-- The bijection of admissible sequences induced by an isomorphism of modules. -/
public def admissibleSequenceEquiv {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N) :
    AdmissibleSequence R M ≃ AdmissibleSequence R N where
  toFun := admissibleSequenceMap E h
  invFun := admissibleSequenceMap E.symm h.symm
  left_inv e := by
    apply Subtype.ext
    funext i
    change E.symm (E (e.1 (Fin.cast h.symm (Fin.cast h i)))) = e.1 i
    simp
  right_inv e := by
    apply Subtype.ext
    funext i
    change E (E.symm (e.1 (Fin.cast h (Fin.cast h.symm i)))) = e.1 i
    simp

/-- Transporting a sequence with one entry updated is the transported sequence with the
corresponding entry updated. -/
public lemma mapSequence_update {R : Type u} {M N : Type v}
    [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) {n m : ℕ} (h : n = m)
    (e : Fin n → M) (i : Fin n) (x : M) :
    (fun j : Fin m => E ((Function.update e i x) (Fin.cast h.symm j))) =
      Function.update (fun j : Fin m => E (e (Fin.cast h.symm j))) (Fin.cast h i) (E x) := by
  funext j
  show E ((Function.update e i x) (Fin.cast h.symm j)) =
    (Function.update (fun k => E (e (Fin.cast h.symm k))) (Fin.cast h i) (E x)) j
  by_cases hj : j = Fin.cast h i
  · subst j
    simp
  · have hji : Fin.cast h.symm j ≠ i := by
      intro hh
      apply hj
      simpa using congrArg (Fin.cast h) hh
    simp [hj, hji]

/-- The equivalence of free vector spaces on admissible symbols induced by an isomorphism of
modules. -/
public def determinantFreeEquiv {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N) :
    DeterminantFree R M ≃ₗ[IsLocalRing.ResidueField R]
      DeterminantFree R N :=
  Finsupp.mapDomain.linearEquiv (R := IsLocalRing.ResidueField R)
    (M := IsLocalRing.ResidueField R) (admissibleSequenceEquiv E h)

/-- `determinantFreeEquiv` relabels a single symbol. -/
public lemma determinantFreeEquiv_single {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N)
    (e : AdmissibleSequence R M) (c : IsLocalRing.ResidueField R) :
    determinantFreeEquiv E h (Finsupp.single e c) =
      Finsupp.single (admissibleSequenceMap E h e) c := by
  classical simp [determinantFreeEquiv, admissibleSequenceEquiv]

/-- The inverse of `determinantFreeEquiv` is the map induced by the inverse isomorphism. -/
public lemma determinantFreeEquiv_symm {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N) :
    (determinantFreeEquiv E h).symm = determinantFreeEquiv E.symm h.symm := by
  simp [determinantFreeEquiv, admissibleSequenceEquiv]

/-- `determinantFreeEquiv` carries each admissible relation to an admissible relation: one
check for each of the three constructors, after transporting the spans involved. -/
public lemma determinantRelation_map {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N)
    {z : DeterminantFree R M} (hz : DeterminantRelation z) :
    DeterminantRelation (determinantFreeEquiv E h z) := by
  classical
  cases hz with
  | dependent e a ha =>
      let ea := admissibleSequenceMap E h e
      have ha' : ea.1 (Fin.cast h a) ∈
          spanBefore (R := R) ea.1 (Fin.cast h a) := by
        exact map_mem_spanBefore_of_equiv E h e.1 a ha
      have hs : determinantFreeEquiv E h (Finsupp.single e 1) = Finsupp.single ea 1 := by
        simpa [ea] using determinantFreeEquiv_single E h e (1 : IsLocalRing.ResidueField R)
      rw [hs]
      exact DeterminantRelation.dependent ea (Fin.cast h a) ha'
  | unitChange e a unit replacement x ha hx hreplacement =>
      let ea := admissibleSequenceMap E h e
      have hseqRaw := mapSequence_update E h e.1 a replacement
      have hreplacement' : IsAdmissibleSequence (R := R)
          (Function.update ea.1 (Fin.cast h a) (E replacement)) :=
        hseqRaw ▸ admissibleSequence_map_equiv E h
          (Function.update e.1 a replacement) hreplacement
      let replacementSeq : AdmissibleSequence R N :=
        ⟨Function.update ea.1 (Fin.cast h a) (E replacement), hreplacement'⟩
      have hseq : admissibleSequenceMap E h
          ⟨Function.update e.1 a replacement, hreplacement⟩ = replacementSeq :=
        Subtype.ext (mapSequence_update E h e.1 a replacement)
      have ha' : ea.1 (Fin.cast h a) = (unit : R) • E replacement + E x := by
        change E (e.1 a) = (unit : R) • E replacement + E x
        simpa [ea, map_add, map_smul] using congrArg E ha
      have hx' : E x ∈ spanBefore (R := R) ea.1 (Fin.cast h a) :=
        map_mem_spanBefore_of_equiv E h e.1 a hx
      have hs : determinantFreeEquiv E h
          (Finsupp.single e 1 - IsLocalRing.residue R unit •
            Finsupp.single ⟨Function.update e.1 a replacement, hreplacement⟩ 1) =
          Finsupp.single ea 1 - IsLocalRing.residue R unit • Finsupp.single replacementSeq 1 := by
        rw [map_sub, map_smul,
          determinantFreeEquiv_single E h e (1 : IsLocalRing.ResidueField R),
          determinantFreeEquiv_single E h
            ⟨Function.update e.1 a replacement, hreplacement⟩ (1 : IsLocalRing.ResidueField R),
          hseq]
      rw [hs]
      exact DeterminantRelation.unitChange ea (Fin.cast h a) unit
        (E replacement) (E x) ha' hx' replacementSeq.2
  | swap e a b hba ha hswap =>
      let ea := admissibleSequenceMap E h e
      let a' := Fin.cast h a
      let b' := Fin.cast h b
      let sourceSwap : Fin (moduleLength R M) → M :=
        Function.update (Function.update e.1 b (e.1 a)) a (e.1 b)
      have hab : a ≠ b := by
        intro hab
        subst b
        simp at hba
      have ha'b' : a' ≠ b' := fun hab' => hab ((Fin.castOrderIso h).injective hab')
      have hswapRaw : (fun j : Fin (moduleLength R N) =>
          E (sourceSwap (Fin.cast h.symm j))) =
          Function.update (Function.update ea.1 b' (ea.1 a')) a' (ea.1 b') := by
        funext j
        change E (sourceSwap (Fin.cast h.symm j)) =
          (Function.update (Function.update
            (fun k => E (e.1 (Fin.cast h.symm k))) b' (E (e.1 a)))
            a' (E (e.1 b))) j
        by_cases hja : j = a'
        · subst j
          simp [sourceSwap, a', b']
        · by_cases hjb : j = b'
          · subst j
            simp [sourceSwap, a', b', hab.symm]
          · have hja' : Fin.cast h.symm j ≠ a := by
              intro hh
              apply hja
              simpa using congrArg (Fin.cast h) hh
            have hjb' : Fin.cast h.symm j ≠ b := by
              intro hh
              apply hjb
              simpa using congrArg (Fin.cast h) hh
            simp [sourceSwap, a', b', hja, hjb, hja', hjb']
      have hswapProp : IsAdmissibleSequence (R := R)
          (Function.update (Function.update ea.1 b' (ea.1 a')) a' (ea.1 b')) :=
        hswapRaw ▸ admissibleSequence_map_equiv E h sourceSwap hswap
      let eswap : AdmissibleSequence R N :=
        ⟨Function.update (Function.update ea.1 b' (ea.1 a')) a' (ea.1 b'), hswapProp⟩
      have hswapSeq : admissibleSequenceMap E h ⟨sourceSwap, hswap⟩ = eswap :=
        Subtype.ext hswapRaw
      have hba' : b'.val + 1 = a'.val := by
        simpa [a', b'] using hba
      have ha' : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
          r • ea.1 a' ∈ spanBefore (R := R) ea.1 b' := by
        intro r hr
        have hmap := map_mem_spanBefore_of_equiv E h e.1 b (ha r hr)
        rw [map_smul] at hmap
        exact hmap
      have hs : determinantFreeEquiv E h
          (Finsupp.single e 1 + Finsupp.single
            ⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hswap⟩ 1) =
          Finsupp.single ea 1 + Finsupp.single eswap 1 := by
        rw [map_add,
          determinantFreeEquiv_single E h e (1 : IsLocalRing.ResidueField R),
          determinantFreeEquiv_single E h
            ⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hswap⟩
            (1 : IsLocalRing.ResidueField R), hswapSeq]
      rw [hs]
      exact DeterminantRelation.swap ea a' b' hba' ha' eswap.2

/-- `determinantFreeEquiv` carries the subspace generated by the admissible relations onto
the subspace generated by the admissible relations. -/
public lemma determinantRelations_map {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N) :
    Submodule.map (determinantFreeEquiv E h : _ →ₗ[IsLocalRing.ResidueField R] _)
        (determinantRelations R M) = determinantRelations R N := by
  classical
  rw [determinantRelations, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact determinantRelation_map E h hx
  · intro hz
    refine ⟨determinantFreeEquiv E h |>.symm z, ?_, ?_⟩
    · rw [determinantFreeEquiv_symm]
      simpa using determinantRelation_map E.symm h.symm hz
    · simp

/-- The equivalence of determinants induced by an isomorphism of modules. -/
public def determinantEquiv {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N) :
    determinant R M ≃ₗ[IsLocalRing.ResidueField R]
      determinant R N :=
  Submodule.Quotient.equiv (determinantRelations R M)
    (determinantRelations R N) (determinantFreeEquiv E h)
    (determinantRelations_map E h)

/-- `determinantEquiv` takes the symbol of a sequence to the symbol of its image. -/
public lemma determinantEquiv_symbol {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    (h : moduleLength R M = moduleLength R N)
    (e : AdmissibleSequence R M) :
    determinantEquiv E h (symbol e) =
      symbol (admissibleSequenceMap E h e) := by
  simp [determinantEquiv, symbol, determinantFreeEquiv_single]

/-- Two linear maps out of a determinant that agree on every symbol are equal. -/
public lemma linearMap_eq_of_determinant_symbols {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f g : determinant R M →ₗ[IsLocalRing.ResidueField R]
      determinant R N)
    (h : ∀ e : AdmissibleSequence R M,
      f (symbol e) = g (symbol e)) : f = g := by
  classical
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (determinantRelations R M) x ?_
  intro z
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | single e c =>
      have hs : Submodule.Quotient.mk (Finsupp.single e c) =
          c • symbol e := by
        rw [← Finsupp.smul_single_one e c, Submodule.Quotient.mk_smul]
        rfl
      simpa only [hs, map_smul] using congrArg (c • ·) (h e)

/-- Two equivalences of determinants that agree on every symbol are equal. -/
public lemma determinantEquiv_ext {R : Type u} {M N : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f g : determinant R M ≃ₗ[IsLocalRing.ResidueField R]
      determinant R N)
    (h : ∀ e : AdmissibleSequence R M,
      f (symbol e) = g (symbol e)) : f = g :=
  LinearEquiv.toLinearMap_injective
    (linearMap_eq_of_determinant_symbols f.toLinearMap g.toLinearMap h)

/-- Transporting an admissible sequence along a composite isomorphism is the composite of the
transports. -/
public lemma admissibleSequenceMap_trans {R : Type u} {M N P : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (E₁ : M ≃ₗ[R] N) (E₂ : N ≃ₗ[R] P)
    (h₁ : moduleLength R M = moduleLength R N)
    (h₂ : moduleLength R N = moduleLength R P)
    (e : AdmissibleSequence R M) :
    admissibleSequenceMap E₂ h₂ (admissibleSequenceMap E₁ h₁ e) =
      admissibleSequenceMap (E₁.trans E₂) (h₁.trans h₂) e := by
  apply Subtype.ext
  funext i
  simp [admissibleSequenceMap, LinearEquiv.trans_apply]

/-- `determinantEquiv` of a composite isomorphism is the composite of the equivalences. -/
public lemma determinantEquiv_trans {R : Type u} {M N P : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (E₁ : M ≃ₗ[R] N) (E₂ : N ≃ₗ[R] P)
    (h₁ : moduleLength R M = moduleLength R N)
    (h₂ : moduleLength R N = moduleLength R P) :
    (determinantEquiv E₁ h₁).trans (determinantEquiv E₂ h₂) =
      determinantEquiv (E₁.trans E₂) (h₁.trans h₂) := by
  apply determinantEquiv_ext
  intro e
  simp only [LinearEquiv.trans_apply, determinantEquiv_symbol]
  rw [admissibleSequenceMap_trans]

/-- `determinantEquiv` of an identity isomorphism is the identity. -/
public lemma determinantEquiv_refl {R : Type u} {M : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] :
    determinantEquiv (LinearEquiv.refl R M) rfl = LinearEquiv.refl _ _ := by
  apply determinantEquiv_ext
  intro e
  simp [determinantEquiv_symbol, admissibleSequenceMap]
/-- The groupoid of finite-length `R`-modules and their isomorphisms. -/
public abbrev FiniteLengthModuleIso (R : Type u) [CommRing R] :=
  Core (ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{v} R => IsFiniteLength R M))

/-- The groupoid of one-dimensional `k`-vector spaces and their isomorphisms. -/
public abbrev OneDimensionalVectorSpaceIso (k : Type u) [Field k] :=
  Core (ObjectProperty.FullSubcategory
    (fun V : ModuleCat.{v} k => Module.finrank k V = 1))

/-- The linear equivalence underlying a morphism of the groupoid of finite-length modules. -/
public def underlyingLinearEquiv {R : Type u} [CommRing R]
    {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N) : M.of.obj ≃ₗ[R] N.of.obj :=
  CategoryTheory.Iso.toLinearEquiv
    ((ObjectProperty.ι (fun X : ModuleCat.{v} R => IsFiniteLength R X)).mapIso f.iso)

/-- The equivalence underlying an identity morphism is the identity. -/
public lemma underlyingLinearEquiv_id {R : Type u} [CommRing R]
    (M : FiniteLengthModuleIso.{u, v} R) :
    underlyingLinearEquiv (𝟙 M) = LinearEquiv.refl R M.of.obj := by
  ext x
  simp [underlyingLinearEquiv]

/-- The equivalence underlying a composite morphism is the composite. -/
public lemma underlyingLinearEquiv_comp {R : Type u} [CommRing R]
    {M N P : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N) (g : N ⟶ P) :
    underlyingLinearEquiv (f ≫ g) =
      (underlyingLinearEquiv f).trans (underlyingLinearEquiv g) := by
  ext x
  simp [underlyingLinearEquiv]

/-- A determinant functor, including the identification of its value on each module with
the determinant vector space of Tag 02P6. -/
public structure DeterminantFunctor (R : Type u) [CommRing R] [IsLocalRing R] where
  /-- The functor on finite-length modules and isomorphisms. -/
  toFunctor : FiniteLengthModuleIso R ⥤
    OneDimensionalVectorSpaceIso (IsLocalRing.ResidueField R)
  /-- The value on an object is canonically its determinant vector space. -/
  objIso (M : FiniteLengthModuleIso.{u, v} R) : (toFunctor.obj M).of.obj ≅
    ModuleCat.of (IsLocalRing.ResidueField R) (determinant R M.of.obj)
  /-- The linear equivalence on determinants induced by a module isomorphism. -/
  mapLinearEquiv {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N) :
    determinant R M.of.obj ≃ₗ[IsLocalRing.ResidueField R]
      determinant R N.of.obj
  /-- Isomorphic modules have the same length. -/
  map_length {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N) :
    moduleLength R M.of.obj = moduleLength R N.of.obj
  /-- An isomorphism carries an admissible sequence to an admissible sequence. -/
  map_admissible {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N)
      (e : AdmissibleSequence R M.of.obj) :
    IsAdmissibleSequence (R := R)
      (fun i ↦ f.iso.hom.hom.hom (e.1 (Fin.cast (map_length f).symm i)))
  /-- On symbols, the induced equivalence applies the module isomorphism entrywise. -/
  map_symbol {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N)
      (e : AdmissibleSequence R M.of.obj) :
    mapLinearEquiv f (symbol e) =
      symbol
        ⟨fun i ↦ f.iso.hom.hom.hom (e.1 (Fin.cast (map_length f).symm i)),
          map_admissible f e⟩
  /-- Under the object identifications, `mapLinearEquiv` is the morphism supplied by the
  functor. -/
  map_iso {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N) :
    (objIso M).inv ≫ (toFunctor.map f).iso.hom.hom ≫ (objIso N).hom =
      ModuleCat.ofHom (mapLinearEquiv f).toLinearMap

/-- **Stacks Project, Tag 05M7.** The determinant of a finite-length module over a local
ring, together with the maps induced by module isomorphisms, is a functor to the groupoid
of one-dimensional vector spaces over the residue field. -/
@[stacks 05M7]
public noncomputable def determinantFunctor (R : Type u) [CommRing R] [IsLocalRing R] :
    DeterminantFunctor.{u, v} R := by
  let toF : FiniteLengthModuleIso.{u, v} R ⥤
      OneDimensionalVectorSpaceIso (IsLocalRing.ResidueField R) := {
    obj := fun M =>
      ⟨⟨ModuleCat.of (IsLocalRing.ResidueField R) (determinant R M.of.obj),
        finrank_determinant_eq_one M.of.property⟩⟩
    map := fun f =>
      let E := underlyingLinearEquiv f
      let h := moduleLength_eq_of_equiv E
      (Core.isoMk (ObjectProperty.isoMk
        (fun V : ModuleCat (IsLocalRing.ResidueField R) =>
          Module.finrank (IsLocalRing.ResidueField R) V = 1)
        (determinantEquiv E h).toModuleIso)).hom
    map_id := by
      intro M
      apply Core.hom_ext
      apply ObjectProperty.hom_ext
      change ModuleCat.ofHom
          (determinantEquiv (underlyingLinearEquiv (𝟙 M))
            (moduleLength_eq_of_equiv (underlyingLinearEquiv (𝟙 M)))).toLinearMap =
        ModuleCat.ofHom LinearMap.id
      rw [underlyingLinearEquiv_id]
      have hh : moduleLength_eq_of_equiv (LinearEquiv.refl R M.of.obj) = rfl :=
        Subsingleton.elim _ _
      rw [hh, determinantEquiv_refl]
      rfl
    map_comp := by
      intro M N P f g
      apply Core.hom_ext
      apply ObjectProperty.hom_ext
      change ModuleCat.ofHom
          (determinantEquiv (underlyingLinearEquiv (f ≫ g))
            (moduleLength_eq_of_equiv (underlyingLinearEquiv (f ≫ g)))).toLinearMap =
        ModuleCat.ofHom
          ((determinantEquiv (underlyingLinearEquiv g)
              (moduleLength_eq_of_equiv (underlyingLinearEquiv g))).toLinearMap.comp
            (determinantEquiv (underlyingLinearEquiv f)
              (moduleLength_eq_of_equiv (underlyingLinearEquiv f))).toLinearMap)
      rw [underlyingLinearEquiv_comp]
      have hh :
          moduleLength_eq_of_equiv
              ((underlyingLinearEquiv f).trans (underlyingLinearEquiv g)) =
            (moduleLength_eq_of_equiv (underlyingLinearEquiv f)).trans
              (moduleLength_eq_of_equiv (underlyingLinearEquiv g)) :=
        Subsingleton.elim _ _
      rw [hh, ← determinantEquiv_trans]
      rfl }
  let mapEquiv := fun {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N) =>
    determinantEquiv (underlyingLinearEquiv f)
      (moduleLength_eq_of_equiv (underlyingLinearEquiv f))
  let mapLength := fun {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N) =>
    moduleLength_eq_of_equiv (underlyingLinearEquiv f)
  let mapAdmissible := fun {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N)
      (e : AdmissibleSequence R M.of.obj) =>
    admissibleSequence_map_equiv (underlyingLinearEquiv f)
      (moduleLength_eq_of_equiv (underlyingLinearEquiv f)) e.1 e.2
  let mapSymbol : ∀ {M N : FiniteLengthModuleIso.{u, v} R} (f : M ⟶ N)
      (e : AdmissibleSequence R M.of.obj),
      mapEquiv f (symbol e) =
        symbol ⟨
          (fun i => f.iso.hom.hom.hom (e.1 (Fin.cast (mapLength f).symm i))),
          mapAdmissible f e⟩ := by
    intro M N f e
    exact determinantEquiv_symbol (underlyingLinearEquiv f)
      (moduleLength_eq_of_equiv (underlyingLinearEquiv f)) e
  exact ⟨toF, (fun M => Iso.refl _), mapEquiv, mapLength, mapAdmissible, mapSymbol,
    (fun {M N} f => rfl)⟩

end Module.FiniteLength

end
