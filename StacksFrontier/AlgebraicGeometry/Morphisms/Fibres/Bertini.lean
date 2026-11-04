module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.GeometricallyIrreducible.AdjoinTranscendental
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
public import StacksFrontier.RingTheory.GeometricallyIrreducible.SeparableClosure
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Subalgebra
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower
public import StacksCore.Tactic.StacksAttribute

/-!
# An irreducibility lemma for a general linear combination

Let `K/k` be a finitely generated geometrically irreducible field extension. If a linear
combination of independent variables with coefficients in `K`, together with a suitable
constant linear combination of those coefficients, is algebraically independent over `k`, then
adjoining the first linear combination to the rational function field over `k` leaves a
geometrically irreducible extension.

The rational function field `K(x₁, …, xₙ)` is any field `Ω` generated over `K` by algebraically
independent elements `x i`. The two additional members of the algebraically independent family
are indexed by `Bool`, with `false` the variable linear combination and `true` the constant one.

## Main results

* `Algebra.isGeometricallyIrreducible_adjoin_linearCombination`: `Ω` is geometrically
  irreducible over the subfield generated over `k` by the `x i` and `∑ gᵢxᵢ`.

## References

* [Stacks Project, Tag 0G4D](https://stacks.math.columbia.edu/tag/0G4D)
* [Jou, pages 71–72]
-/

@[expose] public section

namespace Algebra

universe u

attribute [local instance] Polynomial.algebra
open scoped RatFunc

private theorem linearCombination_delta_transcendental
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (n : ℕ) (x : Fin n → Ω) (ξ δ : Ω)
    (hind : AlgebraicIndependent k
      (Sum.elim x (Bool.rec ξ δ))) :
    Transcendental (Algebra.adjoin k (Set.range x ∪ {ξ})) δ := by
  let y : Fin n ⊕ Bool → Ω := Sum.elim x (Bool.rec ξ δ)
  have ht := hind.transcendental_adjoin
    (s := Set.range Sum.inl ∪ {Sum.inr false}) (i := Sum.inr true) (by simp)
  have him : y '' (Set.range Sum.inl ∪ {Sum.inr false}) = Set.range x ∪ {ξ} := by
    ext z; simp [y]
  rwa [him] at ht

private noncomputable def translatePolynomial
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (c : Fin n → k) (a : k) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (fun i ↦ MvPolynomial.X i +
    MvPolynomial.C (algebraMap k K (a * c i)))

private theorem translatePolynomial_comp
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (c : Fin n → k) (a : k) :
    (translatePolynomial k K n c a).comp
        (translatePolynomial k K n c (-a)) = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [translatePolynomial]

private noncomputable def translatePolynomialEquiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (c : Fin n → k) (a : k) :
    MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K := by
  let f := translatePolynomial k K n c a
  have hleft (z : MvPolynomial (Fin n) K) :
      translatePolynomial k K n c (-a) (translatePolynomial k K n c a z) = z := by
    simpa [neg_neg, AlgHom.comp_apply] using
      congrArg (fun h : MvPolynomial (Fin n) K →ₐ[K] _ => h z)
        (translatePolynomial_comp k K n c (-a))
  have hright (z : MvPolynomial (Fin n) K) :
      translatePolynomial k K n c a (translatePolynomial k K n c (-a) z) = z := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun h : MvPolynomial (Fin n) K →ₐ[K] _ => h z)
        (translatePolynomial_comp k K n c a)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      rw [← hleft x, ← hleft y, h]
    · intro y
      exact ⟨translatePolynomial k K n c (-a) y, hright y⟩
  exact AlgEquiv.ofBijective f hf

private noncomputable def translateFractionRing
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (c : Fin n → k) (a : k) :
    FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin n) K) :=
  IsFractionRing.algEquivOfAlgEquiv (translatePolynomialEquiv k K n c a)

private noncomputable def translateField
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (n : ℕ) (x : Fin n → Ω) (c : Fin n → k)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hx : AlgebraicIndependent K x) (a : k) : Ω ≃ₐ[K] Ω := by
  let e : FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K] Ω :=
    hx.aevalEquivField.trans ((IntermediateField.equivOfEq hgen).trans
      IntermediateField.topEquiv)
  exact e.symm.trans ((translateFractionRing k K n c a).trans e)

private theorem translateField_apply
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (n : ℕ) (x : Fin n → Ω) (c : Fin n → k)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hx : AlgebraicIndependent K x) (a : k) (i : Fin n) :
    translateField k K Ω n x c hgen hx a (x i) =
      x i + algebraMap k Ω (a * c i) := by
  let e : FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K] Ω :=
    hx.aevalEquivField.trans ((IntermediateField.equivOfEq hgen).trans
      IntermediateField.topEquiv)
  have he : e (algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X i)) = x i := by
    simp [e]
  have he' : e.symm (x i) = algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X i) :=
    e.injective (by simpa using he.symm)
  show e ((translateFractionRing k K n c a) (e.symm (x i))) = _
  rw [he', translateFractionRing, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp [translatePolynomialEquiv, e, translatePolynomial]
  simp only [IsScalarTower.algebraMap_apply k K Ω a,
    IsScalarTower.algebraMap_apply k K Ω (c i)]

private theorem translateField_apply_linearCombination
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (n : ℕ) (x : Fin n → Ω) (g : Fin n → K) (c : Fin n → k)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hx : AlgebraicIndependent K x) (a : k) :
    translateField k K Ω n x c hgen hx a
        (∑ i, algebraMap K Ω (g i) * x i) =
      (∑ i, algebraMap K Ω (g i) * x i) +
        algebraMap k Ω a *
          ∑ i, algebraMap K Ω (algebraMap k K (c i) * g i) := by
  simp_rw [map_sum, map_mul, AlgEquiv.commutes, translateField_apply, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, IsScalarTower.algebraMap_apply k K Ω (c i)]
  ring

private theorem fg_top_of_fg_subfield
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (L : IntermediateField k Ω) (hfg : (⊤ : IntermediateField k Ω).FG) :
    (⊤ : IntermediateField L Ω).FG := by
  have : Algebra.EssFiniteType k Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType L Ω := Algebra.EssFiniteType.of_comp k L Ω
  exact IntermediateField.fg_top L Ω

private theorem fg_top_adjoin_variables
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (n : ℕ) (x : Fin n → Ω)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hfg : (⊤ : IntermediateField k K).FG) :
    (⊤ : IntermediateField k Ω).FG := by
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  have hfgΩ : (⊤ : IntermediateField K Ω).FG := by
    rw [← hgen]
    exact IntermediateField.fg_adjoin_of_finite (Set.finite_range x)
  have : Algebra.EssFiniteType K Ω := IntermediateField.fg_top_iff.mp hfgΩ
  have : Algebra.EssFiniteType k Ω := Algebra.EssFiniteType.comp k K Ω
  exact IntermediateField.fg_top k Ω

private theorem mem_range_of_isSeparable
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (h : Algebra.IsGeometricallyIrreducible F E) {z : E} (hz : IsSeparable F z) :
    z ∈ Set.range (algebraMap F E) := by
  have hz' : z ∈ separableClosure F E := hz
  rwa [(separableClosure.eq_bot_iff_geometricallyIrreducible F E).mpr h] at hz'

/-- Inverting the equivalences in a commuting square of algebra maps. -/
private theorem comp_symm_eq_of_comp_eq
    {F E F' E' : Type*} [Field F] [Field E] [Field F'] [Field E']
    [Algebra F E] [Algebra F' E']
    (f : F ≃+* F') (g : E ≃+* E')
    (hcomm : (algebraMap F' E').comp f = g.toRingHom.comp (algebraMap F E)) :
    (algebraMap F E).comp f.symm = g.symm.toRingHom.comp (algebraMap F' E') := by
  ext a
  apply g.injective
  simpa using (RingHom.congr_fun hcomm (f.symm a)).symm

private theorem isGeometricallyIrreducible_of_equiv
    {F E F' E' : Type u} [Field F] [Field E] [Field F'] [Field E']
    [Algebra F E] [Algebra F' E']
    (f : F ≃+* F') (g : E ≃+* E')
    (hcomm : (algebraMap F' E').comp f = g.toRingHom.comp (algebraMap F E))
    (h : Algebra.IsGeometricallyIrreducible F E) :
    Algebra.IsGeometricallyIrreducible F' E' := by
  refine (separableClosure.eq_bot_iff_geometricallyIrreducible F' E').mp
    (le_antisymm (fun z hz ↦ ?_) bot_le)
  have hz' := _root_.IsSeparable.of_equiv_equiv f.symm g.symm
    (comp_symm_eq_of_comp_eq f g hcomm) hz
  obtain ⟨a, ha⟩ := mem_range_of_isSeparable h hz'
  exact ⟨f a, by simpa [ha] using RingHom.congr_fun hcomm a⟩

private theorem exists_adjoin_eq_of_isSeparable
    {F E I : Type u} [Field F] [Field E] [Algebra F E] [Infinite I]
    (hfg : (⊤ : IntermediateField F E).FG)
    (z : I → E) (hz : ∀ i, IsSeparable F (z i)) :
    ∃ i j, i ≠ j ∧ IntermediateField.adjoin F {z i} =
      IntermediateField.adjoin F {z j} := by
  have : Module.Finite F (separableClosure F E) := part2 F E hfg
  have : Finite (IntermediateField F (separableClosure F E)) :=
    Field.finite_intermediateField_of_exists_primitive_element F _
      (Field.exists_primitive_element F _)
  let f (i : I) : IntermediateField F (separableClosure F E) :=
    IntermediateField.adjoin F {⟨z i, hz i⟩}
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨i, j, hne, ?_⟩
  simpa [f, IntermediateField.adjoin_map] using congrArg
    (fun L : IntermediateField F (separableClosure F E) ↦ L.map (separableClosure F E).val) hij

private theorem isSeparable_of_le
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {L M : IntermediateField F E} (hLM : L ≤ M) {z : E}
    (hz : IsSeparable L z) : IsSeparable M z := by
  let : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  have : IsScalarTower L M E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact hz.tower_top M

private theorem mem_adjoin_of_isSeparable_of_transcendental
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (hL : Algebra.IsGeometricallyIrreducible F L)
    {t z : E} (ht : Transcendental L t)
    (hz : IsSeparable (IntermediateField.adjoin F {t}) z)
    (hzL : z ∈ IntermediateField.adjoin (IntermediateField.adjoin F {t})
      (Set.range (algebraMap L E))) :
    z ∈ IntermediateField.adjoin F {t} := by
  let M := IntermediateField.adjoin (IntermediateField.adjoin F {t})
    (Set.range (algebraMap L E))
  have hM : Algebra.IsGeometricallyIrreducible (IntermediateField.adjoin F {t}) M :=
    AlgebraicGeometry.geometricallyIrreducible_specMap_adjoin_of_transcendental ht
  let z' : M := ⟨z, hzL⟩
  have hz' : IsSeparable (IntermediateField.adjoin F {t}) z' :=
    hz.of_algHom _ M.val
  obtain ⟨a, ha⟩ := mem_range_of_isSeparable hM hz'
  exact (show (a : E) = z from congrArg (fun q : M ↦ (q : E)) ha) ▸ a.property

/-- `t` lies in every intermediate field generated over `F⟮t⟯`. -/
private theorem self_mem_adjoin_adjoin {F E : Type u} [Field F] [Field E] [Algebra F E]
    (t : E) (s : Set E) : t ∈ IntermediateField.adjoin (IntermediateField.adjoin F {t}) s :=
  (IntermediateField.adjoin (IntermediateField.adjoin F {t}) s).algebraMap_mem
    ⟨t, IntermediateField.mem_adjoin_simple_self F t⟩

private theorem exists_mem_adjoin_of_separable_family
    {F E I : Type u} [Field F] [Field E] [Algebra F E] [Infinite I]
    (hE : Algebra.IsGeometricallyIrreducible F E)
    (S : IntermediateField F E) (hfg : (⊤ : IntermediateField S E).FG)
    (t z : I → E) (ht : ∀ i, t i ∈ S)
    (hgen : ∀ i j, i ≠ j → IntermediateField.adjoin F {t i, t j} = S)
    (hind : ∀ i j, i ≠ j → Transcendental (IntermediateField.adjoin F {t i}) (t j))
    (hz : ∀ i, IsSeparable (IntermediateField.adjoin F {t i}) (z i)) :
    ∃ j, z j ∈ IntermediateField.adjoin F {t j} := by
  have hzS (i : I) : IsSeparable S (z i) :=
    isSeparable_of_le (IntermediateField.adjoin_simple_le_iff.mpr (ht i)) (hz i)
  obtain ⟨i, j, hij, heq⟩ := exists_adjoin_eq_of_isSeparable hfg z hzS
  let A := IntermediateField.adjoin F {t i}
  let U := IntermediateField.adjoin A {z i}
  let L : IntermediateField F E := U.restrictScalars F
  have hL : Algebra.IsGeometricallyIrreducible F L :=
    isGeometricallyIrreducible_of_subalgebra F E hE L.toSubalgebra
  have : Algebra.IsAlgebraic A U :=
    IntermediateField.isAlgebraic_adjoin_simple (hz i).isIntegral
  have : IsScalarTower A U E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hjU : Transcendental U (t j) :=
    (Algebra.IsAlgebraic.transcendental_iff A U).mp (hind i j hij)
  have hj : Transcendental L (t j) := hjU
  refine ⟨j, mem_adjoin_of_isSeparable_of_transcendental L hL hj (hz j) ?_⟩
  let M := IntermediateField.adjoin (IntermediateField.adjoin F {t j})
    (Set.range (algebraMap L E))
  have hLi : z i ∈ L := IntermediateField.subset_adjoin A {z i} (by simp)
  have hti : t i ∈ L := by
    show algebraMap A E ⟨t i, IntermediateField.mem_adjoin_simple_self F (t i)⟩ ∈ U
    exact U.algebraMap_mem _
  have hLM : L.toSubfield ≤ M.toSubfield := fun a ha ↦
    IntermediateField.subset_adjoin _ _ ⟨⟨a, ha⟩, rfl⟩
  have htj : t j ∈ M := self_mem_adjoin_adjoin (t j) _
  have hSM : S.toSubfield ≤ M.toSubfield := by
    rw [← hgen i j hij]
    apply IntermediateField.adjoin_le_subfield
    · rintro a ⟨b, rfl⟩
      exact hLM (L.algebraMap_mem b)
    · intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact hLM hti
      · exact Set.mem_singleton_iff.mp ha ▸ htj
  have hsup : (IntermediateField.adjoin S {z i}).toSubfield ≤ M.toSubfield := by
    apply IntermediateField.adjoin_le_subfield
    · rintro a ⟨b, rfl⟩
      exact hSM b.property
    · intro a ha
      exact Set.mem_singleton_iff.mp ha ▸ hLM hLi
  apply hsup
  rw [heq]
  exact IntermediateField.mem_adjoin_simple_self S (z j)

private def subfieldRingEquivOfMemIff
    {F F' E E' : Type u} [Field F] [Field F'] [Field E] [Field E']
    [Algebra F E] [Algebra F' E']
    (L : IntermediateField F E) (M : IntermediateField F' E')
    (e : E ≃+* E') (he : ∀ z, z ∈ L ↔ e z ∈ M) : L ≃+* M where
  toFun z := ⟨e z, (he z).mp z.property⟩
  invFun z := ⟨e.symm z, (he _).mpr (by simp)⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z)
  right_inv z := Subtype.ext (e.apply_symm_apply z)
  map_mul' z w := Subtype.ext (map_mul e (z : E) (w : E))
  map_add' z w := Subtype.ext (map_add e (z : E) (w : E))

private theorem map_adjoin_of_translate
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {ι : Type*} (x : ι → E) (d : ι → F) (e : E ≃ₐ[F] E)
    (he : ∀ i, e (x i) = x i + algebraMap F E (d i)) :
    (IntermediateField.adjoin F (Set.range x)).map e.toAlgHom =
      IntermediateField.adjoin F (Set.range x) := by
  let B := IntermediateField.adjoin F (Set.range x)
  apply le_antisymm
  · rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [AlgEquiv.coe_toAlgHom, he]
    exact B.add_mem (IntermediateField.subset_adjoin F _ ⟨i, rfl⟩) (B.algebraMap_mem _)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    have hx : e (x i) ∈ B.map e.toAlgHom :=
      ⟨x i, IntermediateField.subset_adjoin F _ ⟨i, rfl⟩, rfl⟩
    simpa [he] using (B.map e.toAlgHom).sub_mem hx ((B.map e.toAlgHom).algebraMap_mem (d i))

private theorem mem_adjoin_map_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (B : IntermediateField F E) (e : E ≃ₐ[F] E)
    (hB : B.map e.toAlgHom = B) (t z : E) :
    z ∈ IntermediateField.adjoin B {t} ↔ e z ∈ IntermediateField.adjoin B {e t} := by
  have h : ((IntermediateField.adjoin B {t}).restrictScalars F).map e.toAlgHom =
      (IntermediateField.adjoin B {e t}).restrictScalars F := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.map_sup, hB,
      IntermediateField.adjoin_map]
    simp
  refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · have : e z ∈ ((IntermediateField.adjoin B {t}).restrictScalars F).map e.toAlgHom :=
      ⟨z, hz, rfl⟩
    rwa [h] at this
  · obtain ⟨w, hw, hew⟩ :
        e z ∈ ((IntermediateField.adjoin B {t}).restrictScalars F).map e.toAlgHom := by
      rwa [h]
    exact e.injective hew ▸ hw

private theorem transcendental_map_adjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (B : IntermediateField F E) (e : E ≃ₐ[F] E)
    (hB : B.map e.toAlgHom = B) {t z : E}
    (hz : Transcendental (IntermediateField.adjoin B {t}) z) :
    Transcendental (IntermediateField.adjoin B {e t}) (e z) := by
  let f := subfieldRingEquivOfMemIff (IntermediateField.adjoin B {t})
    (IntermediateField.adjoin B {e t}) e.toRingEquiv (mem_adjoin_map_iff B e hB t)
  intro ha
  apply hz
  have hc : (algebraMap (IntermediateField.adjoin B {t}) E).comp f.symm =
      e.symm.toRingHom.comp (algebraMap (IntermediateField.adjoin B {e t}) E) := rfl
  simpa using ha.ringHom_of_comp_eq f.symm e.symm f.symm.injective hc

private theorem isSeparable_map_adjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (B : IntermediateField F E) (e : E ≃ₐ[F] E)
    (hB : B.map e.toAlgHom = B) {t z : E}
    (hz : IsSeparable (IntermediateField.adjoin B {t}) z) :
    IsSeparable (IntermediateField.adjoin B {e t}) (e z) := by
  let f := subfieldRingEquivOfMemIff (IntermediateField.adjoin B {t})
    (IntermediateField.adjoin B {e t}) e.toRingEquiv (mem_adjoin_map_iff B e hB t)
  exact _root_.IsSeparable.of_equiv_equiv f e.toRingEquiv rfl hz

private theorem adjoin_pair_affine
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (x y : E) (a b : F) (hab : a ≠ b) :
    IntermediateField.adjoin F
      {x + algebraMap F E a * y, x + algebraMap F E b * y} =
      IntermediateField.adjoin F {x, y} := by
  let L := IntermediateField.adjoin F {x + algebraMap F E a * y, x + algebraMap F E b * y}
  let M := IntermediateField.adjoin F {x, y}
  have hx : x ∈ M := IntermediateField.subset_adjoin F _ (by simp)
  have hy : y ∈ M := IntermediateField.subset_adjoin F _ (by simp)
  have ha : x + algebraMap F E a * y ∈ L := IntermediateField.subset_adjoin F _ (by simp)
  have hb : x + algebraMap F E b * y ∈ L := IntermediateField.subset_adjoin F _ (by simp)
  have hn : algebraMap F E b - algebraMap F E a ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ hab ((algebraMap F E).injective h).symm
  have hyL : y ∈ L := by
    have heq : (x + algebraMap F E b * y - (x + algebraMap F E a * y)) /
        (algebraMap F E b - algebraMap F E a) = y := by
      apply (div_eq_iff hn).mpr
      ring
    rw [← heq]
    exact L.div_mem (L.sub_mem hb ha) (L.sub_mem (L.algebraMap_mem _) (L.algebraMap_mem _))
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro z (rfl | rfl) <;> exact M.add_mem hx (M.mul_mem (M.algebraMap_mem _) hy)
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro z (rfl | rfl)
    · simpa using L.sub_mem ha (L.mul_mem (L.algebraMap_mem a) hyL)
    · exact hyL

private theorem transcendental_add_mul
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {x y : E} (hx : IsAlgebraic F x) (hy : Transcendental F y)
    {a : F} (ha : a ≠ 0) : Transcendental F (x + algebraMap F E a * y) := by
  intro h
  apply hy
  have h' := (h.sub hx).mul (isAlgebraic_algebraMap (R := F) a⁻¹)
  have hn : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ha
  have heq : (x + algebraMap F E a * y - x) / algebraMap F E a = y := by
    apply (div_eq_iff hn).mpr
    ring
  rwa [map_inv₀, ← div_eq_mul_inv, heq] at h'

private theorem isGeometricallyIrreducible_adjoin_of_translations
    {k E : Type u} [Field k] [Field E] [Algebra k E] [Infinite k]
    (B : IntermediateField k E)
    (hE : Algebra.IsGeometricallyIrreducible B E)
    (hfg : (⊤ : IntermediateField B E).FG)
    (ξ δ : E) (htrans : Transcendental (IntermediateField.adjoin B {ξ}) δ)
    (σ : k → E ≃ₐ[k] E)
    (hB : ∀ a, B.map (σ a).toAlgHom = B)
    (hξ : ∀ a, σ a ξ = ξ + algebraMap k E a * δ)
    (hδ : ∀ a, σ a δ = δ) :
    Algebra.IsGeometricallyIrreducible (IntermediateField.adjoin B {ξ}) E := by
  refine (separableClosure.eq_bot_iff_geometricallyIrreducible _ E).mp
    (le_antisymm (fun θ hθ ↦ ?_) bot_le)
  let t (a : k) : E := ξ + algebraMap k E a * δ
  let S := IntermediateField.adjoin B {ξ, δ}
  have ht (a : k) : t a ∈ S := by
    apply S.add_mem (IntermediateField.subset_adjoin B _ (by simp))
    apply S.mul_mem _ (IntermediateField.subset_adjoin B _ (by simp))
    exact S.algebraMap_mem (algebraMap k B a)
  have hgen (a b : k) (hab : a ≠ b) : IntermediateField.adjoin B {t a, t b} = S := by
    simpa only [t, ← IsScalarTower.algebraMap_apply k B E] using
      adjoin_pair_affine (F := B) ξ δ (algebraMap k B a) (algebraMap k B b)
        fun h ↦ hab ((algebraMap k B).injective h)
  have hind (a b : k) (hab : a ≠ b) :
      Transcendental (IntermediateField.adjoin B {t a}) (t b) := by
    have hδa : Transcendental (IntermediateField.adjoin B {t a}) δ := by
      have h := transcendental_map_adjoin B (σ a) (hB a) htrans
      rwa [hξ a, hδ a] at h
    let A := IntermediateField.adjoin B {t a}
    have : IsScalarTower k A E := IsScalarTower.of_algebraMap_eq fun r ↦
      IsScalarTower.algebraMap_apply k B E r
    have hx : IsAlgebraic A (t a) :=
      isAlgebraic_algebraMap (R := A)
        ⟨t a, IntermediateField.mem_adjoin_simple_self B (t a)⟩
    have h := transcendental_add_mul hx hδa
      (a := algebraMap k A (b - a)) ((map_ne_zero (algebraMap k A)).mpr (sub_ne_zero.mpr hab.symm))
    have heq : t a + algebraMap A E (algebraMap k A (b - a)) * δ = t b := by
      rw [← IsScalarTower.algebraMap_apply k A E]
      dsimp [t]
      rw [map_sub]
      ring
    rwa [heq] at h
  have hz (a : k) : IsSeparable (IntermediateField.adjoin B {t a}) (σ a θ) := by
    have h := isSeparable_map_adjoin B (σ a) (hB a) hθ
    rwa [hξ a] at h
  obtain ⟨a, ha⟩ := exists_mem_adjoin_of_separable_family hE S
    (fg_top_of_fg_subfield B E S hfg) t (fun a ↦ σ a θ) ht hgen hind hz
  have hmem : θ ∈ IntermediateField.adjoin B {ξ} :=
    (mem_adjoin_map_iff B (σ a) (hB a) ξ θ).mpr (by simpa only [hξ a, t] using ha)
  exact ⟨⟨θ, hmem⟩, rfl⟩

private theorem isGeometricallyIrreducible_linearCombination_of_infinite
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] [Infinite k]
    (n : ℕ) (x : Fin n → Ω) (g : Fin n → K)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hx : AlgebraicIndependent K x)
    (hE : Algebra.IsGeometricallyIrreducible (IntermediateField.adjoin k (Set.range x)) Ω)
    (hfg : (⊤ : IntermediateField k K).FG) (c : Fin n → k)
    (hind : AlgebraicIndependent k
      (Sum.elim x (Bool.rec (∑ i, algebraMap K Ω (g i) * x i)
        (∑ i, algebraMap K Ω (algebraMap k K (c i) * g i))))) :
    Algebra.IsGeometricallyIrreducible
      (IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K Ω (g i) * x i})) Ω := by
  let B := IntermediateField.adjoin k (Set.range x)
  let ξ : Ω := ∑ i, algebraMap K Ω (g i) * x i
  let δ : Ω := ∑ i, algebraMap K Ω (algebraMap k K (c i) * g i)
  have htrans : Transcendental (IntermediateField.adjoin B {ξ}) δ := by
    show Transcendental ((IntermediateField.adjoin B {ξ}).restrictScalars k) δ
    rw [IntermediateField.adjoin_adjoin_left]
    exact IntermediateField.transcendental_adjoin_iff.mpr
      (linearCombination_delta_transcendental k Ω n x ξ δ hind)
  let σ (a : k) : Ω ≃ₐ[k] Ω := (translateField k K Ω n x c hgen hx a).restrictScalars k
  have hB (a : k) : B.map (σ a).toAlgHom = B :=
    map_adjoin_of_translate x (fun i ↦ a * c i) (σ a)
      (translateField_apply k K Ω n x c hgen hx a)
  have hξ (a : k) : σ a ξ = ξ + algebraMap k Ω a * δ :=
    translateField_apply_linearCombination k K Ω n x g c hgen hx a
  have hδ (a : k) : σ a δ = δ := by
    dsimp [σ, δ]
    simp only [map_sum, AlgEquiv.commutes]
  have h := isGeometricallyIrreducible_adjoin_of_translations B hE
    (fg_top_of_fg_subfield k Ω B (fg_top_adjoin_variables k K Ω n x hgen hfg))
    ξ δ htrans σ hB hξ hδ
  change Algebra.IsGeometricallyIrreducible
    ((IntermediateField.adjoin B {ξ}).restrictScalars k) Ω at h
  rwa [IntermediateField.adjoin_adjoin_left] at h

private theorem adjoin_base_le
    (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    (s : Set E) : (IntermediateField.adjoin F s).toSubfield ≤
      (IntermediateField.adjoin K s).toSubfield := by
  apply IntermediateField.adjoin_le_subfield
  · rintro z ⟨a, rfl⟩
    rw [IsScalarTower.algebraMap_apply F K E]
    exact IntermediateField.algebraMap_mem _ _
  · exact IntermediateField.subset_adjoin K s

private theorem mem_adjoin_range_iff
    {F K E : Type u} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    (t z : E) : z ∈ IntermediateField.adjoin (IntermediateField.adjoin F {t})
      (Set.range (algebraMap K E)) ↔ z ∈ IntermediateField.adjoin K {t} := by
  let A := IntermediateField.adjoin F {t}
  let D := IntermediateField.adjoin A (Set.range (algebraMap K E))
  let C := IntermediateField.adjoin K {t}
  constructor
  · apply IntermediateField.adjoin_le_subfield
    · rintro z ⟨a, rfl⟩
      exact adjoin_base_le F K E {t} a.property
    · exact C.set_range_subset
  · apply IntermediateField.adjoin_le_subfield
    · exact IntermediateField.subset_adjoin A _
    · intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      exact self_mem_adjoin_adjoin t _

private theorem isGeometricallyIrreducible_adjoin_transcendental
    {F K E : Type u} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    (hK : Algebra.IsGeometricallyIrreducible F K) {t : E} (ht : Transcendental K t)
    [Algebra (IntermediateField.adjoin F {t}) (IntermediateField.adjoin K {t})]
    [IsScalarTower (IntermediateField.adjoin F {t}) (IntermediateField.adjoin K {t}) E] :
    Algebra.IsGeometricallyIrreducible (IntermediateField.adjoin F {t})
      (IntermediateField.adjoin K {t}) := by
  let A := IntermediateField.adjoin F {t}
  let D := IntermediateField.adjoin A (Set.range (algebraMap K E))
  let C := IntermediateField.adjoin K {t}
  let e : D ≃+* C := subfieldRingEquivOfMemIff D C (RingEquiv.refl E)
    (mem_adjoin_range_iff t)
  have hD : Algebra.IsGeometricallyIrreducible A D :=
    AlgebraicGeometry.geometricallyIrreducible_specMap_adjoin_of_transcendental ht
  exact isGeometricallyIrreducible_of_equiv (RingEquiv.refl A) e
    (RingHom.ext fun a ↦ Subtype.ext (IsScalarTower.algebraMap_apply A C E a).symm) hD

private theorem isGeometricallyIrreducible_of_equiv_overfield
    {F K F' K' E : Type u} [Field F] [Field K] [Field F'] [Field K'] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [Algebra F' K'] [Algebra F' E] [Algebra K' E] [IsScalarTower F' K' E]
    (eF : F ≃+* F') (eK : K ≃+* K')
    (heF : ∀ a, algebraMap F' E (eF a) = algebraMap F E a)
    (heK : ∀ a, algebraMap K' E (eK a) = algebraMap K E a)
    (h : Algebra.IsGeometricallyIrreducible F K) :
    Algebra.IsGeometricallyIrreducible F' K' := by
  apply isGeometricallyIrreducible_of_equiv eF eK _ h
  ext a
  apply (algebraMap K' E).injective
  show algebraMap K' E (algebraMap F' K' (eF a)) =
    algebraMap K' E (eK (algebraMap F K a))
  rw [← IsScalarTower.algebraMap_apply F' K' E, heF, heK,
    ← IsScalarTower.algebraMap_apply F K E]

private theorem isGeometricallyIrreducible_adjoin_of_restrictScalars_eq
    {F K E : Type u} [Field F] [Field K] [Field E]
    [Algebra F E] [Algebra K E]
    (B : IntermediateField F E) (C : IntermediateField K E)
    [Algebra B C] [IsScalarTower B C E]
    (t : E) (ht : Transcendental C t)
    (h : Algebra.IsGeometricallyIrreducible B C)
    (B' : IntermediateField F E) (C' : IntermediateField K E)
    [Algebra B' C'] [IsScalarTower B' C' E]
    (hB : (IntermediateField.adjoin B {t}).restrictScalars F = B')
    (hC : (IntermediateField.adjoin C {t}).restrictScalars K = C') :
    Algebra.IsGeometricallyIrreducible B' C' := by
  let A := IntermediateField.adjoin B {t}
  let D := IntermediateField.adjoin C {t}
  let : Algebra A D := (Subfield.inclusion (adjoin_base_le B C E {t})).toAlgebra
  have : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hD : Algebra.IsGeometricallyIrreducible A D :=
    isGeometricallyIrreducible_adjoin_transcendental h ht
  let eB : A ≃+* B' := (IntermediateField.equivOfEq hB).toRingEquiv
  let eC : D ≃+* C' := (IntermediateField.equivOfEq hC).toRingEquiv
  exact isGeometricallyIrreducible_of_equiv_overfield (E := E) eB eC
    (fun _ ↦ rfl) (fun _ ↦ rfl) hD

private theorem isGeometricallyIrreducible_adjoin_finset
    {F K E : Type u} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    {ι : Type*} (x : ι → E) (hx : AlgebraicIndependent K x)
    (hK : Algebra.IsGeometricallyIrreducible F K) (s : Finset ι) :
    ∀ [Algebra (IntermediateField.adjoin F (x '' (s : Set ι)))
        (IntermediateField.adjoin K (x '' (s : Set ι)))]
      [IsScalarTower (IntermediateField.adjoin F (x '' (s : Set ι)))
        (IntermediateField.adjoin K (x '' (s : Set ι))) E],
    Algebra.IsGeometricallyIrreducible (IntermediateField.adjoin F (x '' (s : Set ι)))
      (IntermediateField.adjoin K (x '' (s : Set ι))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro _ _
    have hF : IntermediateField.adjoin F (x '' (↑(∅ : Finset ι) : Set ι)) = ⊥ := by simp
    have hK' : IntermediateField.adjoin K (x '' (↑(∅ : Finset ι) : Set ι)) = ⊥ := by simp
    let eF := (IntermediateField.botEquiv F E).symm.trans (IntermediateField.equivOfEq hF.symm)
    let eK := (IntermediateField.botEquiv K E).symm.trans (IntermediateField.equivOfEq hK'.symm)
    refine isGeometricallyIrreducible_of_equiv eF.toRingEquiv eK.toRingEquiv
      (RingHom.ext fun a ↦ Subtype.ext ?_) hK
    simp only [RingHom.comp_apply]
    rw [← IntermediateField.algebraMap_apply
        (IntermediateField.adjoin K (x '' (↑(∅ : Finset ι) : Set ι))),
      ← IsScalarTower.algebraMap_apply
        (IntermediateField.adjoin F (x '' (↑(∅ : Finset ι) : Set ι)))
        (IntermediateField.adjoin K (x '' (↑(∅ : Finset ι) : Set ι))) E]
    simpa [eF, eK] using IsScalarTower.algebraMap_apply F K E a
  | @insert i s hi ih =>
    intro _ _
    let B := IntermediateField.adjoin F (x '' (s : Set ι))
    let C := IntermediateField.adjoin K (x '' (s : Set ι))
    let B' := IntermediateField.adjoin F (x '' (↑(insert i s) : Set ι))
    let C' := IntermediateField.adjoin K (x '' (↑(insert i s) : Set ι))
    let : Algebra B C := (Subfield.inclusion (adjoin_base_le F K E (x '' (s : Set ι)))).toAlgebra
    have : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hC : Algebra.IsGeometricallyIrreducible B C := ih
    have ht : Transcendental C (x i) :=
      IntermediateField.transcendental_adjoin_iff.mpr (hx.transcendental_adjoin hi)
    apply isGeometricallyIrreducible_adjoin_of_restrictScalars_eq B C (x i) ht hC B' C' <;>
    · rw [IntermediateField.adjoin_adjoin_left]
      congr 1
      simp [Finset.coe_insert]

private theorem isGeometricallyIrreducible_of_adjoin_eq_top
    (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    {ι : Type*} [Finite ι] (x : ι → E) (hx : AlgebraicIndependent K x)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hK : Algebra.IsGeometricallyIrreducible F K) :
    Algebra.IsGeometricallyIrreducible (IntermediateField.adjoin F (Set.range x)) E := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let s : Set E := x '' (↑(Finset.univ : Finset ι) : Set ι)
  let B := IntermediateField.adjoin F s
  let C := IntermediateField.adjoin K s
  let : Algebra B C := (Subfield.inclusion (adjoin_base_le F K E s)).toAlgebra
  have : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hC : Algebra.IsGeometricallyIrreducible B C :=
    isGeometricallyIrreducible_adjoin_finset x hx hK Finset.univ
  have hgen' : C = ⊤ := by simpa only [C, s, Finset.coe_univ, Set.image_univ] using hgen
  let e : C ≃+* E :=
    ((IntermediateField.equivOfEq hgen').trans IntermediateField.topEquiv).toRingEquiv
  have h := isGeometricallyIrreducible_of_equiv (RingEquiv.refl B) e rfl hC
  have hB : B = IntermediateField.adjoin F (Set.range x) := by
    simp only [B, s, Finset.coe_univ, Set.image_univ]
  exact isGeometricallyIrreducible_of_equiv (IntermediateField.equivOfEq hB).toRingEquiv
    (RingEquiv.refl E) rfl h

private theorem algebraicIndependent_adjoin_transcendental
    {F E L : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    {ι : Type*} {x : ι → E} (hx : AlgebraicIndependent F x)
    {t : L} (ht : Transcendental E t) :
    AlgebraicIndependent (IntermediateField.adjoin F {t}) (algebraMap E L ∘ x) := by
  have ht' : AlgebraicIndependent E (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have h := (hx.sumElim_comp ht').comp (Equiv.sumComm ι Unit)
    (Equiv.sumComm ι Unit).injective
  have heq : (Sum.elim (fun _ : Unit => t) (algebraMap E L ∘ x)) ∘
      (Equiv.sumComm ι Unit) = Sum.elim (algebraMap E L ∘ x) (fun _ : Unit => t) := by
    funext i
    cases i <;> rfl
  rw [heq] at h
  have h' := (AlgebraicIndependent.sumElim_iff.mp h).2
  rw [Set.range_const] at h'
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr h'

/-- Elements of `F⟮s⟯` map into `F⟮t⟯⟮image of s⟯` under the base change. -/
private theorem algebraMap_mem_adjoin_image
    {F E L : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    (t : L) (s : Set E) {z : E} (hz : z ∈ IntermediateField.adjoin F s) :
    algebraMap E L z ∈
      IntermediateField.adjoin (IntermediateField.adjoin F {t}) (algebraMap E L '' s) := by
  let M := IntermediateField.adjoin (IntermediateField.adjoin F {t}) (algebraMap E L '' s)
  have hle : (IntermediateField.adjoin F s).toSubfield ≤ M.toSubfield.comap (algebraMap E L) := by
    apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨a, rfl⟩
      show algebraMap E L (algebraMap F E a) ∈ M
      rw [← IsScalarTower.algebraMap_apply F E L]
      exact M.algebraMap_mem (algebraMap F (IntermediateField.adjoin F {t}) a)
    · intro b hb
      exact IntermediateField.subset_adjoin _ _ ⟨b, hb, rfl⟩
  exact hle hz

private theorem adjoin_adjoin_transcendental_eq_top
    {F E L : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    {ι : Type*} (x : ι → E)
    (hx : IntermediateField.adjoin F (Set.range x) = ⊤)
    (t : L) (ht : IntermediateField.adjoin E {t} = ⊤) :
    IntermediateField.adjoin (IntermediateField.adjoin F {t})
      (Set.range (algebraMap E L ∘ x)) = ⊤ := by
  let A := IntermediateField.adjoin F {t}
  let M := IntermediateField.adjoin A (Set.range (algebraMap E L ∘ x))
  have hE : ∀ z : E, algebraMap E L z ∈ M := by
    intro z
    have hz : z ∈ IntermediateField.adjoin F (Set.range x) := by rw [hx]; trivial
    simpa [M, A, Set.range_comp] using algebraMap_mem_adjoin_image t (Set.range x) hz
  have hle : (IntermediateField.adjoin E {t}).toSubfield ≤ M.toSubfield := by
    apply IntermediateField.adjoin_le_subfield
    · rintro z ⟨a, rfl⟩
      exact hE a
    · intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact self_mem_adjoin_adjoin t _
  exact top_unique fun z _ ↦ hle (by rw [ht]; trivial)

private theorem ratFunc_ringHom_ext {F L : Type*} [Field F] [CommRing L]
    {f g : RatFunc F →+* L} (hC : ∀ a, f (RatFunc.C a) = g (RatFunc.C a))
    (hX : f RatFunc.X = g RatFunc.X) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial F))
    (Polynomial.ringHom_ext (by simpa using hC) (by simpa using hX))

private theorem ratFunc_algebraMap_C
    {F E : Type u} [Field F] [Field E] [Algebra F E] (a : F) :
    algebraMap (RatFunc F) (RatFunc E) (RatFunc.C a) = RatFunc.C (algebraMap F E a) := by
  rw [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply
    (Polynomial F) (RatFunc F) (RatFunc E),
    IsScalarTower.algebraMap_apply (Polynomial F) (Polynomial E) (RatFunc E)]
  simp [RingHom.algebraMap_toAlgebra]

private theorem ratFunc_algebraMap_X
    {F E : Type u} [Field F] [Field E] [Algebra F E] :
    algebraMap (RatFunc F) (RatFunc E) RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply
    (Polynomial F) (RatFunc F) (RatFunc E),
    IsScalarTower.algebraMap_apply (Polynomial F) (Polynomial E) (RatFunc E)]
  simp [RingHom.algebraMap_toAlgebra]

private theorem isGeometricallyIrreducible_of_adjoin_transcendental
    {F E L : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    {t : L} (ht : Transcendental E t)
    (hgen : IntermediateField.adjoin E {t} = ⊤)
    (h : Algebra.IsGeometricallyIrreducible (IntermediateField.adjoin F {t}) L) :
    Algebra.IsGeometricallyIrreducible F E := by
  let A := IntermediateField.adjoin F {t}
  let f : RatFunc F ≃+* A := (RatFunc.algEquivOfTranscendental t (ht.of_tower_top F)).toRingEquiv
  let g : RatFunc E ≃ₐ[E] L := (RatFunc.algEquivOfTranscendental t ht).trans
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  have hc : (algebraMap A L).comp f =
      g.toRingHom.comp (algebraMap (RatFunc F) (RatFunc E)) := by
    apply ratFunc_ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, ratFunc_algebraMap_C]
      show ((RatFunc.algEquivOfTranscendental t (ht.of_tower_top F)) (RatFunc.C a) : L) =
        g (RatFunc.C (algebraMap F E a))
      rw [← RatFunc.algebraMap_eq_C, AlgEquiv.commutes,
        ← RatFunc.algebraMap_eq_C, AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply F E L a
    · simp only [RingHom.comp_apply, ratFunc_algebraMap_X]
      show ((RatFunc.algEquivOfTranscendental t (ht.of_tower_top F)) RatFunc.X : L) =
        ((RatFunc.algEquivOfTranscendental t ht) RatFunc.X : L)
      simp only [RatFunc.algEquivOfTranscendental_X]
  exact (AlgebraicGeometry.GeometricallyIrreducible.iff_ratFunc F E).mpr
    (isGeometricallyIrreducible_of_equiv f.symm g.symm.toRingEquiv
      (comp_symm_eq_of_comp_eq f g.toRingEquiv hc) h)

private theorem adjoin_baseChange_comm
    {F E L : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    (s : Set E) (t : L) :
    (IntermediateField.adjoin (IntermediateField.adjoin F {t})
      (algebraMap E L '' s)).toSubfield =
      (IntermediateField.adjoin (IntermediateField.adjoin F s) {t}).toSubfield := by
  let A := IntermediateField.adjoin F {t}
  let B := IntermediateField.adjoin F s
  let D := IntermediateField.adjoin A (algebraMap E L '' s)
  let C := IntermediateField.adjoin B {t}
  have htC : t ∈ C := IntermediateField.mem_adjoin_simple_self B t
  have hAD : t ∈ D := self_mem_adjoin_adjoin t _
  apply le_antisymm
  · apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨a, rfl⟩
      exact adjoin_base_le F B L {t} a.property
    · rintro _ ⟨b, hb, rfl⟩
      exact C.algebraMap_mem ⟨b, IntermediateField.subset_adjoin F s hb⟩
  · apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨b, rfl⟩
      exact algebraMap_mem_adjoin_image t s b.property
    · intro z hz
      rwa [Set.mem_singleton_iff.mp hz]

/-- Let `K/k` be a finitely generated geometrically irreducible extension and let `Ω` be generated
over `K` by algebraically independent elements `x₁, …, xₙ`. If `x₁, …, xₙ`, `∑ gᵢxᵢ` and
`∑ cᵢgᵢ` are algebraically independent over `k`, then `Ω` is geometrically irreducible over the
subfield generated over `k` by the `xᵢ` and `∑ gᵢxᵢ`. -/
@[stacks 0G4D]
theorem isGeometricallyIrreducible_adjoin_linearCombination
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (n : ℕ) (_hn : 0 < n) (x : Fin n → Ω) (g : Fin n → K)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hx : AlgebraicIndependent K x)
    (hK : Algebra.IsGeometricallyIrreducible k K)
    (hfg : (⊤ : IntermediateField k K).FG)
    (c : Fin n → k)
    (hind : AlgebraicIndependent k
      (Sum.elim x (Bool.rec
        (∑ i, algebraMap K Ω (g i) * x i)
        (∑ i, algebraMap K Ω ((algebraMap k K (c i)) * g i))))) :
    let ξ : Ω := ∑ i, algebraMap K Ω (g i) * x i
    let F : IntermediateField k Ω :=
      IntermediateField.adjoin k (Set.range x ∪ {ξ})
    letI : Algebra F Ω := F.toSubalgebra.toAlgebra
    Algebra.IsGeometricallyIrreducible F Ω := by
  classical
  let L := RatFunc Ω
  let T : L := RatFunc.X
  let k' := IntermediateField.adjoin k {T}
  let K' := IntermediateField.adjoin K {T}
  let : Algebra k' K' := (Subfield.inclusion (adjoin_base_le k K L {T})).toAlgebra
  have : IsScalarTower k' K' L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k' K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k K' L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let x' : Fin n → L := algebraMap Ω L ∘ x
  let g' : Fin n → K' := algebraMap K K' ∘ g
  let c' : Fin n → k' := algebraMap k k' ∘ c
  have hT : Transcendental Ω T := RatFunc.transcendental_X
  have hx' : AlgebraicIndependent K' x' := algebraicIndependent_adjoin_transcendental hx hT
  have hgen' : IntermediateField.adjoin K' (Set.range x') = ⊤ :=
    adjoin_adjoin_transcendental_eq_top x hgen T RatFunc.adjoin_X
  have hK' : Algebra.IsGeometricallyIrreducible k' K' :=
    isGeometricallyIrreducible_adjoin_transcendental hK (hT.of_tower_top K)
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType K K' := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton T))
  have : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  have : Algebra.EssFiniteType k' K' := Algebra.EssFiniteType.of_comp k k' K'
  have hfg' : (⊤ : IntermediateField k' K').FG := IntermediateField.fg_top k' K'
  have : Infinite (RatFunc k) := Infinite.of_injective
    (algebraMap (Polynomial k) (RatFunc k)) (IsFractionRing.injective (Polynomial k) (RatFunc k))
  have : Infinite k' := Infinite.of_injective
    (RatFunc.algEquivOfTranscendental T (hT.of_tower_top k))
    (RatFunc.algEquivOfTranscendental T (hT.of_tower_top k)).injective
  let ξ : Ω := ∑ i, algebraMap K Ω (g i) * x i
  let δ : Ω := ∑ i, algebraMap K Ω (algebraMap k K (c i) * g i)
  have hξ : (∑ i, algebraMap K' L (g' i) * x' i) = algebraMap Ω L ξ := by
    dsimp only [g', x', ξ, Function.comp_apply]
    simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply K K' L,
      IsScalarTower.algebraMap_apply K Ω L]
  have hδ : (∑ i, algebraMap K' L (algebraMap k' K' (c' i) * g' i)) =
      algebraMap Ω L δ := by
    dsimp only [g', c', δ, Function.comp_apply]
    simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply k k' K',
      ← IsScalarTower.algebraMap_apply k K' L, ← IsScalarTower.algebraMap_apply K K' L,
      ← IsScalarTower.algebraMap_apply K Ω L, ← IsScalarTower.algebraMap_apply k K L]
  have hind' : AlgebraicIndependent k'
      (Sum.elim x' (Bool.rec (∑ i, algebraMap K' L (g' i) * x' i)
        (∑ i, algebraMap K' L (algebraMap k' K' (c' i) * g' i)))) := by
    have h := algebraicIndependent_adjoin_transcendental hind hT
    rw [hξ, hδ]
    convert h using 1
    · funext i
      cases i with
      | inl i => rfl
      | inr b => cases b <;> rfl
    · rfl
  have hL := isGeometricallyIrreducible_linearCombination_of_infinite k' K' L n x' g'
    hgen' hx' (isGeometricallyIrreducible_of_adjoin_eq_top k' K' L x' hx' hgen' hK')
    hfg' c' hind'
  rw [hξ] at hL
  have hs : Set.range x' ∪ {algebraMap Ω L ξ} =
      algebraMap Ω L '' (Set.range x ∪ {ξ}) := by
    simp only [Set.image_union, Set.image_singleton, ← Set.range_comp, x']
  rw [hs] at hL
  let F := IntermediateField.adjoin k (Set.range x ∪ {ξ})
  let D := IntermediateField.adjoin k' (algebraMap Ω L '' (Set.range x ∪ {ξ}))
  let C := IntermediateField.adjoin F {T}
  let e : D ≃+* C := subfieldRingEquivOfMemIff D C (RingEquiv.refl L) fun z ↦
    Iff.of_eq (congrArg (fun S : Subfield L ↦ z ∈ S)
      (adjoin_baseChange_comm (Set.range x ∪ {ξ}) T))
  have hC : Algebra.IsGeometricallyIrreducible C L :=
    isGeometricallyIrreducible_of_equiv e (RingEquiv.refl L) rfl hL
  exact isGeometricallyIrreducible_of_adjoin_transcendental hT RatFunc.adjoin_X hC

end Algebra

end
