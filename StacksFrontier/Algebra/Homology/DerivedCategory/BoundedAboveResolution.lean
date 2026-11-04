module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bounded above resolution engine

Let `A` be an abelian category, let `R` be a weak Serre class in `A` and let `G` be a class of
objects of `A` which contains the zero object, is closed under binary biproducts and under
isomorphism, and covers epimorphisms onto objects of `R` (`CoversEpis`). Then every cochain
complex `X` with `X^i = 0` for `i > a` whose cohomology objects all lie in `R` receives a
quasi-isomorphism from a cochain complex `Y` with `Y^i = 0` for `i > a` and every term in `G`
(`exists_quasiIso_isStrictlyLE_of_coversEpis`).

## Main definitions

* `Stacks.Homology.BoundedAboveResolution.CoversEpis` - the hypothesis that a class `G` of
  objects of an abelian category epimorphically covers, after refinement, every epimorphism onto
  an object of an ambient class `R`.
* `CategoryTheory.ObjectProperty.descExtend` - a morphism out of a complex extended along
  `ComplexShape.embeddingUpIntLE`, built from a morphism to the restriction.

## Main results

* `Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis` - the
  engine described above.

## Implementation notes

`Y` is built degree by degree downwards from `a`, as a `ℕ`-indexed chain complex of layers
(`resolution`) which is extended back to a `ℤ`-indexed cochain complex along
`ComplexShape.embeddingUpIntLE`. In each degree the new term is the biproduct of an object of `G`
covering the cohomology of `X` in that degree, which makes the map surjective on cohomology, and
an object of `G` covering, up to refinement, those cocycles of the previously built term whose
image in `X` is a boundary, which makes the map injective on cohomology; that these two
properties in every degree suffice is `quasiIso_of_epi_of_cover`. A `Layer` in degree `i` carries
an object of `G`, its map to `X^i`, its differential and the preceding degree with its own map to
`X`, so consecutive layers compose without transport.

Morphisms *out of* an extended complex are not provided by Mathlib -
`ComplexShape.Embedding.homEquiv` constructs only morphisms *into* one - so they are built here
as `ObjectProperty.descExtend`, the boundary case `i ≤ a < i + 1` being handled by
`X.d i (i + 1) = 0`.

The intermediate layers are chosen, not canonical: `CoversEpis` asserts that a cover exists and
the recursion picks one at each degree with `Nonempty.some`, which is why `Classical.choice`
appears in the axioms of every declaration of the construction. Nothing in the public interface
extracts data from an existence statement: the engine's conclusion is existential, and every
definition which does make such a choice is private to this module.

Two classes are separated here because the consumers need them separated: for [Stacks, Tag 0FCL]
the terms of the resolution are asked to lie in the very Serre class `P` whose objects the
cohomology lies in, which is the case `G = P`, while for [Stacks, Tag 0960] the terms must be
finite affine shriek sums whereas the cohomology is merely constructible.

## References

* [Stacks project, Tag 0FCL](https://stacks.math.columbia.edu/tag/0FCL)
* [Stacks project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
-/

universe v u

namespace CategoryTheory.ObjectProperty

open Limits ZeroObject ComplexShape

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Any morphism into the target of an epimorphism factors through it after an epimorphism of its
source: the refinement of `τ` by `σ` is the pullback of the two. -/
public lemma exists_epi_fac_of_epi {T V W : A} (τ : T ⟶ W) (σ : V ⟶ W) [Epi σ] :
    ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (v : T' ⟶ V), p ≫ τ = v ≫ σ :=
  ⟨pullback τ σ, pullback.fst τ σ, inferInstance, pullback.snd τ σ, pullback.condition⟩

private lemma isZero_extend_X_of_not_le (K : ChainComplex A ℕ) (a i : ℤ) (hi : ¬ i ≤ a) :
    IsZero ((K.extend (embeddingUpIntLE a)).X i) :=
  HomologicalComplex.isZero_extend_X K (embeddingUpIntLE a) i
    (fun n => by rw [embeddingUpIntLE_f]; omega)

private lemma embeddingUpIntLE_f_toNat {a i : ℤ} (hi : i ≤ a) :
    (embeddingUpIntLE a).f (a - i).toNat = i := by
  rw [embeddingUpIntLE_f]; omega
section Desc

variable (X : CochainComplex A ℤ) (K : ChainComplex A ℕ) (a : ℤ)
  (φ : K ⟶ X.restriction (embeddingUpIntLE a))

/-- Auxiliary definition for `descExtend`. -/
public noncomputable def descF (i : ℤ) : (K.extend (embeddingUpIntLE a)).X i ⟶ X.X i :=
  if hi : i ≤ a then
    (K.extendXIso _ (embeddingUpIntLE_f_toNat hi)).hom ≫ φ.f (a - i).toNat ≫
      (X.restrictionXIso _ (embeddingUpIntLE_f_toNat hi)).hom
  else 0

/-- In a degree `i = (embeddingUpIntLE a).f n` coming from `n : ℕ`, the component `descF X K a φ i`
is `φ.f n`, transported along the identifications of the degree-`i` objects of the extension of `K`
and of `X` with the degree-`n` objects of `K` and of the restriction of `X`. -/
public lemma descF_eq {n : ℕ} {i : ℤ} (h : (embeddingUpIntLE a).f n = i) :
    descF X K a φ i =
      (K.extendXIso _ h).hom ≫ φ.f n ≫ (X.restrictionXIso _ h).hom := by
  have hi : i ≤ a := by rw [embeddingUpIntLE_f] at h; omega
  have h1 : descF X K a φ i = (K.extendXIso _ (embeddingUpIntLE_f_toNat hi)).hom ≫
      φ.f (a - i).toNat ≫ (X.restrictionXIso _ (embeddingUpIntLE_f_toNat hi)).hom :=
    dite_eq_left hi
  obtain rfl : (a - i).toNat = n :=
    (embeddingUpIntLE a).injective_f ((embeddingUpIntLE_f_toNat hi).trans h.symm)
  rw [h1]

private lemma descF_eq_zero {i : ℤ} (hi : ¬ i ≤ a) : descF X K a φ i = 0 := dite_eq_right hi

/-- The maps `descF X K a φ i` commute with the differentials of the extension of `K` and of `X`,
when `X` is strictly `≤ a`. -/
public lemma descF_comm [X.IsStrictlyLE a] (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    descF X K a φ i ≫ X.d i j = (K.extend (embeddingUpIntLE a)).d i j ≫ descF X K a φ j := by
  change i + 1 = j at hij
  by_cases hi : i ≤ a
  · have hn := embeddingUpIntLE_f_toNat (a := a) hi
    by_cases hj : j ≤ a
    · have hm := embeddingUpIntLE_f_toNat (a := a) hj
      obtain ⟨m, hm2⟩ : ∃ m : ℕ, (a - j).toNat = m := ⟨_, rfl⟩
      rw [hm2] at hm
      rw [show (a - i).toNat = m + 1 by omega] at hn
      rw [descF_eq X K a φ hn, descF_eq X K a φ hm,
        HomologicalComplex.extend_d_eq K (embeddingUpIntLE a) hn hm]
      have hc := φ.comm (m + 1) m
      rw [HomologicalComplex.restriction_d_eq X (embeddingUpIntLE a) hn hm] at hc
      have hc' : φ.f (m + 1) ≫ (X.restrictionXIso (embeddingUpIntLE a) hn).hom ≫ X.d i j =
          K.d (m + 1) m ≫ φ.f m ≫ (X.restrictionXIso (embeddingUpIntLE a) hm).hom := by
        rw [← Category.assoc (K.d (m + 1) m), ← hc]; simp
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hc']
    · rw [(X.isZero_of_isStrictlyLE a j (by omega)).eq_of_tgt (X.d i j) 0, comp_zero,
        descF_eq_zero X K a φ hj, comp_zero]
  · rw [descF_eq_zero X K a φ hi, zero_comp,
      (isZero_extend_X_of_not_le K a i hi).eq_of_src
          ((K.extend (embeddingUpIntLE a)).d i j) 0, zero_comp]

/-- A morphism out of an extended complex, from a morphism to the restriction. -/
@[expose] public noncomputable def descExtend [X.IsStrictlyLE a] :
    K.extend (embeddingUpIntLE a) ⟶ X where
  f i := descF X K a φ i
  comm' i j hij := descF_comm X K a φ i j hij

/-- The degree-`i` component of `descExtend X K a φ` is `descF X K a φ i`. -/
public lemma descExtend_f [X.IsStrictlyLE a] (i : ℤ) :
    (descExtend X K a φ).f i = descF X K a φ i := rfl
end Desc

end CategoryTheory.ObjectProperty

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Homology.BoundedAboveResolution

open ZeroObject ComplexShape

variable {A : Type*} [Category A] [Abelian A]

/-- A class `G` of objects of an abelian category **covers epimorphisms** onto a class `R` when
every epimorphism `f : V ⟶ W` with `W` in `R` can be refined by an object of `G`: there are an
object `V'` of `G`, which is moreover in `R`, and a map `g : V' ⟶ V` with `g ≫ f` epimorphic.

The ambient class `R` is only ever asked to be a weak Serre class; it is what the kernels and
pullbacks occurring in the construction are tested against, while `G` controls the terms of the
resolution which comes out. -/
public def CoversEpis (R : ObjectProperty A) (G : A → Prop) : Prop :=
  ∀ ⦃V W : A⦄ (f : V ⟶ W), Epi f → R W →
    ∃ (V' : A) (g : V' ⟶ V), G V' ∧ R V' ∧ Epi (g ≫ f)

/-- The sequence `X^(i-1) ⟶ Z^i ⟶ H^i` is exact. -/
private lemma exact_toCycles_homologyπ (X : CochainComplex A ℤ) (i : ℤ) :
    (ShortComplex.mk (X.toCycles (i - 1) i) (X.homologyπ i)
      (X.toCycles_comp_homologyπ _ _)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (X.homologyIsCokernel (i - 1) i (by simp))

/-- A map of cochain complexes which is surjective on cohomology, and injective on cohomology up
to refinements, is a quasi-isomorphism.

Surjectivity in degree `i` is witnessed by an object `C` mapping to the degree-`i` cocycles of
`Y` and onto the degree-`i` cohomology of `X`; injectivity is witnessed by the ability to refine
any cocycle of `Y` whose image in `X` is a boundary to a boundary of `Y`. -/
private lemma quasiIso_of_epi_of_cover {X Y : CochainComplex A ℤ} (φ : Y ⟶ X)
    (hepi : ∀ i : ℤ, ∃ (C : A) (γ : C ⟶ Y.X i) (c : C ⟶ X.cycles i), γ ≫ Y.d i (i + 1) = 0 ∧
      c ≫ X.iCycles i = γ ≫ φ.f i ∧ Epi (c ≫ X.homologyπ i))
    (hcov : ∀ (i : ℤ) ⦃T : A⦄ (t : T ⟶ Y.X i), t ≫ Y.d i (i + 1) = 0 →
      (∃ u : T ⟶ X.X (i - 1), t ≫ φ.f i = u ≫ X.d (i - 1) i) →
      ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ Y.X (i - 1)),
        p ≫ t = s ≫ Y.d (i - 1) i) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := by simp
  have hE : Epi (HomologicalComplex.homologyMap φ i) := by
    obtain ⟨C, γ, c, hγd, hγc, hce⟩ := hepi i
    have hlift : Y.liftCycles γ (i + 1) hnext hγd ≫ HomologicalComplex.cyclesMap φ i = c := by
      rw [← cancel_mono (X.iCycles i)]
      simp [hγc]
    have : (Y.liftCycles γ (i + 1) hnext hγd ≫ Y.homologyπ i) ≫
        HomologicalComplex.homologyMap φ i = c ≫ X.homologyπ i := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality, reassoc_of% hlift]
    exact epi_of_epi_fac this
  have hM : Mono (HomologicalComplex.homologyMap φ i) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro T t ht
    obtain ⟨T₀, π, hπ, q, hq⟩ := ObjectProperty.exists_epi_fac_of_epi t (Y.homologyπ i)
    have hz : (q ≫ HomologicalComplex.cyclesMap φ i) ≫ X.homologyπ i = 0 := by
      rw [Category.assoc, ← HomologicalComplex.homologyπ_naturality, ← reassoc_of% hq, ht,
        comp_zero]
    obtain ⟨W, e, he, u, hu⟩ := (ShortComplex.exact_iff_exact_up_to_refinements _).1
      (exact_toCycles_homologyπ X i)
      (q ≫ HomologicalComplex.cyclesMap φ i) hz
    obtain ⟨T', p, hp, s, hs⟩ := hcov i ((e ≫ q) ≫ Y.iCycles i) (by simp)
      ⟨u, by
        dsimp at hu
        simp only [Category.assoc]
        rw [← HomologicalComplex.cyclesMap_i, reassoc_of% hu]
        simp⟩
    have key : (p ≫ e ≫ q) ≫ Y.homologyπ i = 0 := by
      have h1 : p ≫ e ≫ q = s ≫ Y.toCycles (i - 1) i := by
        rw [← cancel_mono (Y.iCycles i)]
        simpa using hs
      rw [h1, Category.assoc, Y.toCycles_comp_homologyπ, comp_zero]
    have : Epi (p ≫ e ≫ π) := by have := hp; have := he; have := hπ; infer_instance
    rw [← cancel_epi (p ≫ e ≫ π), comp_zero, Category.assoc, Category.assoc, hq]
    simpa using key
  exact isIso_of_mono_of_epi _

section Resolution

variable (R : ObjectProperty A) [R.IsWeakSerreClass] (G : A → Prop) (X : CochainComplex A ℤ)

/-- The data produced by one step of the descending induction: an object `Y₀` of the ambient
class, a differential `d₀` into the previous layer, a map `f₀` to the degree-`i` term of `X`
commuting with the differentials, a witness that `Y₀` covers the degree-`i` cohomology of `X`,
and the property that every cocycle of the previous layer whose image in `X` is a boundary is,
up to refinement, a boundary of `d₀`. -/
private structure StepData (i j : ℤ) {Y₁ Y₂ : A} (d₁ : Y₁ ⟶ Y₂) (f₁ : Y₁ ⟶ X.X j) where
  /-- The new layer. -/
  Y₀ : A
  /-- The new layer lies in the ambient class. -/
  hY₀ : R Y₀
  /-- The differential into the previous layer. -/
  d₀ : Y₀ ⟶ Y₁
  /-- The map to the degree-`i` term of `X`. -/
  f₀ : Y₀ ⟶ X.X i
  /-- The composite of two consecutive differentials vanishes. -/
  zero : d₀ ≫ d₁ = 0
  /-- The maps to `X` commute with the differentials. -/
  comm : f₀ ≫ X.d i j = d₀ ≫ f₁
  /-- The new layer covers the degree-`i` cohomology of `X`. -/
  epiH : ∃ (C : A) (γ : C ⟶ Y₀) (c : C ⟶ X.cycles i), γ ≫ d₀ = 0 ∧
    c ≫ X.iCycles i = γ ≫ f₀ ∧ Epi (c ≫ X.homologyπ i)
  /-- Cocycles of the previous layer which become boundaries in `X` are, up to refinement,
  boundaries of `d₀`. -/
  cover : ∀ ⦃T : A⦄ (t : T ⟶ Y₁), t ≫ d₁ = 0 → (∃ u : T ⟶ X.X i, t ≫ f₁ = u ≫ X.d i j) →
    ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ Y₀), p ≫ t = s ≫ d₀

/-- The second summand of a step: an object of `G` inside the ambient class which covers, up to
refinement, every cocycle of the previous layer whose image in `X` is a boundary. -/
private lemma exists_prop_boundary_cover (hP : CoversEpis R G)
    (hX : ∀ k, R (X.homology k)) (i j : ℤ) (hij : i + 1 = j)
    {Y₁ Y₂ : A} (hY₁ : R Y₁) (hY₂ : R Y₂) (d₁ : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X.X j) (f₂ : Y₂ ⟶ X.X (j + 1))
    (hcomm : f₁ ≫ X.d j (j + 1) = d₁ ≫ f₂) :
    ∃ (E : A) (_ : G E) (_ : R E) (dE : E ⟶ Y₁) (fE : E ⟶ X.X i),
      dE ≫ d₁ = 0 ∧ fE ≫ X.d i j = dE ≫ f₁ ∧
      ∀ ⦃T : A⦄ (t : T ⟶ Y₁), t ≫ d₁ = 0 →
        (∃ u : T ⟶ X.X i, t ≫ f₁ = u ≫ X.d i j) →
        ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ E), p ≫ t = s ≫ dE := by
  have hK : R (kernel d₁) := R.prop_kernel d₁ hY₁ hY₂
  have hcycle : (kernel.ι d₁ ≫ f₁) ≫ X.d j (j + 1) = 0 := by
    calc
      (kernel.ι d₁ ≫ f₁) ≫ X.d j (j + 1) =
          kernel.ι d₁ ≫ (f₁ ≫ X.d j (j + 1)) := by rw [Category.assoc]
      _ = kernel.ι d₁ ≫ (d₁ ≫ f₂) := by rw [hcomm]
      _ = 0 := by simp
  let c := X.liftCycles (kernel.ι d₁ ≫ f₁) (j + 1) (by simp) hcycle
  let m := c ≫ X.homologyπ j
  let W := kernel m
  have hW : R W := R.prop_kernel m hK (hX j)
  have hz : (kernel.ι m ≫ c) ≫ X.homologyπ j = 0 := by
    calc
      (kernel.ι m ≫ c) ≫ X.homologyπ j = kernel.ι m ≫ (c ≫ X.homologyπ j) := by
        simp only [Category.assoc]
      _ = kernel.ι m ≫ m := by rfl
      _ = 0 := kernel.condition m
  obtain ⟨W', e, he, u, hu⟩ :=
    (ShortComplex.exact_iff_exact_up_to_refinements _).1
      (exact_toCycles_homologyπ X j) (kernel.ι m ≫ c) hz
  obtain ⟨E, σ, hQE, hE, hepi⟩ := hP e inferInstance hW
  have hi : i = j - 1 := by omega
  subst i
  let dE := σ ≫ e ≫ kernel.ι m ≫ kernel.ι d₁
  let fE := σ ≫ u
  have hc : c ≫ X.iCycles j = kernel.ι d₁ ≫ f₁ := by
    dsimp [c]
    exact X.liftCycles_i (kernel.ι d₁ ≫ f₁) (j + 1) (by simp) hcycle
  refine ⟨E, hQE, hE, dE, fE, ?_, ?_, ?_⟩
  · simp [dE, Category.assoc]
  · have huc : σ ≫ e ≫ kernel.ι m ≫ c ≫ X.iCycles j =
        σ ≫ u ≫ X.d (j - 1) j := by
      have h := congrArg (fun z => σ ≫ z ≫ X.iCycles j) hu
      simpa only [Category.assoc, X.toCycles_i] using h
    calc
      fE ≫ X.d (j - 1) j = σ ≫ u ≫ X.d (j - 1) j := by simp [fE, Category.assoc]
      _ = σ ≫ e ≫ kernel.ι m ≫ c ≫ X.iCycles j := huc.symm
      _ = dE ≫ f₁ := by simp [dE, Category.assoc, hc]
  · rintro T t ht ⟨v, hv⟩
    let k := kernel.lift d₁ t ht
    have hcycles : k ≫ c ≫ X.iCycles j = t ≫ f₁ := by
      calc
        k ≫ c ≫ X.iCycles j = k ≫ (c ≫ X.iCycles j) := rfl
        _ = k ≫ (kernel.ι d₁ ≫ f₁) := by rw [hc]
        _ = t ≫ f₁ := by rw [← Category.assoc, kernel.lift_ι]
    have hcyclev : (v ≫ X.toCycles (j - 1) j) ≫ X.iCycles j = t ≫ f₁ := by
      calc
        (v ≫ X.toCycles (j - 1) j) ≫ X.iCycles j = v ≫ X.d (j - 1) j := by
          rw [Category.assoc, X.toCycles_i]
        _ = t ≫ f₁ := hv.symm
    have hk : k ≫ c = v ≫ X.toCycles (j - 1) j := by
      apply (cancel_mono (X.iCycles j)).1
      simpa using hcycles.trans hcyclev.symm
    have hzT : k ≫ m = 0 := by
      calc
        k ≫ m = k ≫ (c ≫ X.homologyπ j) := by rfl
        _ = (k ≫ c) ≫ X.homologyπ j := by
          simp only [Category.assoc]
        _ = (v ≫ X.toCycles (j - 1) j) ≫ X.homologyπ j := by rw [hk]
        _ = 0 := by rw [Category.assoc, X.toCycles_comp_homologyπ, comp_zero]
    let w := kernel.lift m k hzT
    obtain ⟨T', p, hp, s, hs⟩ := ObjectProperty.exists_epi_fac_of_epi w (σ ≫ e)
    refine ⟨T', p, hp, s, ?_⟩
    have hkι : k ≫ kernel.ι d₁ = t := kernel.lift_ι d₁ t ht
    have hwι : w ≫ kernel.ι m = k := kernel.lift_ι m k hzT
    calc
      p ≫ t = p ≫ (k ≫ kernel.ι d₁) := by rw [hkι]
      _ = p ≫ (w ≫ kernel.ι m) ≫ kernel.ι d₁ := by rw [hwι]
      _ = (p ≫ w) ≫ kernel.ι m ≫ kernel.ι d₁ := by simp [Category.assoc]
      _ = (s ≫ σ ≫ e) ≫ kernel.ι m ≫ kernel.ι d₁ := by rw [hs]
      _ = s ≫ dE := by simp [dE, Category.assoc]

/-- One step of the descending induction exists: the new layer is the biproduct of a cover of the
degree-`i` cohomology of `X` and a cover of the boundaries, both taken in `G`. -/
private lemma nonempty_stepData (hP : CoversEpis R G)
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hX : ∀ i, R (X.homology i)) (i j : ℤ) (hij : i + 1 = j)
    {Y₁ Y₂ : A} (hY₁ : R Y₁) (hY₂ : R Y₂) (d₁ : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X.X j) (f₂ : Y₂ ⟶ X.X (j + 1))
    (hcomm : f₁ ≫ X.d j (j + 1) = d₁ ≫ f₂) :
    Nonempty {s : StepData R X i j d₁ f₁ // G s.Y₀} := by
  obtain ⟨C, γ, hQC, hC, hγ⟩ := hP (X.homologyπ i) inferInstance (hX i)
  obtain ⟨E, hQE, hE, dE, fE, hdE, hfE, hcov⟩ :=
    exists_prop_boundary_cover R G X hP hX i j hij hY₁ hY₂ d₁ f₁ f₂ hcomm
  let s : StepData R X i j d₁ f₁ :=
    { Y₀ := C ⊞ E
      hY₀ := R.prop_biprod hC hE
      d₀ := biprod.desc 0 dE
      f₀ := biprod.desc (γ ≫ X.iCycles i) fE
      zero := by apply biprod.hom_ext' <;> simp [hdE]
      comm := by apply biprod.hom_ext' <;> simp [hfE]
      epiH := ⟨C, biprod.inl, γ, by simp, by simp, hγ⟩
      cover := by
        intro T t ht hu
        obtain ⟨T', p, hp, s, hs⟩ := hcov t ht hu
        exact ⟨T', p, hp, s ≫ biprod.inr, by simpa using hs⟩ }
  exact ⟨⟨s, hQbiprod hQC hQE⟩⟩

/-- The state carried by the descending induction at degree `i`: the layer `Y` in degree `i`,
its map `f` to `X`, and the previous layer `Z` with its own map to `X`. -/
private structure Layer (i : ℤ) where
  /-- The layer in degree `i`. -/
  Y : A
  /-- The layer lies in the ambient class. -/
  hY : R Y
  /-- The layer lies in `G`. -/
  hQ : G Y
  /-- Its map to the degree-`i` term of `X`. -/
  f : Y ⟶ X.X i
  /-- The layer in degree `i + 1`. -/
  Z : A
  /-- It lies in the ambient class. -/
  hZ : R Z
  /-- Its map to the degree-`i + 1` term of `X`. -/
  Zf : Z ⟶ X.X (i + 1)
  /-- The differential. -/
  d : Y ⟶ Z
  /-- The maps to `X` commute with the differentials. -/
  comm : f ≫ X.d i (i + 1) = d ≫ Zf

/-- The layer which starts the induction, in the degree just above the bound. -/
private def Layer.zero (i : ℤ) (hQzero : G (0 : A)) : Layer R G X i where
  Y := 0
  hY := R.prop_zero
  hQ := hQzero
  f := 0
  Z := 0
  hZ := R.prop_zero
  Zf := 0
  d := 0
  comm := by simp

/-- The step data chosen at a layer. -/
private def Layer.step {i j : ℤ}
    (s : Layer R G X j) (hij : i + 1 = j) (hP : CoversEpis R G)
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hX : ∀ k, R (X.homology k)) :
    {d : StepData R X i j s.d s.f // G d.Y₀} :=
  (nonempty_stepData R G X hP hQbiprod hX i j hij s.hY s.hZ s.d s.f s.Zf s.comm).some

/-- The layer one degree lower. -/
private def Layer.next {i j : ℤ}
    (s : Layer R G X j) (hij : i + 1 = j) (hP : CoversEpis R G)
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hX : ∀ k, R (X.homology k)) : Layer R G X i := by
  let d := Layer.step R G X s hij hP hQbiprod hX
  let e := X.XIsoOfEq hij.symm
  exact
    { Y := d.val.Y₀
      hY := d.val.hY₀
      hQ := d.property
      f := d.val.f₀
      Z := s.Y
      hZ := s.hY
      Zf := s.f ≫ e.hom
      d := d.val.d₀
      comm := by
        calc
          d.val.f₀ ≫ X.d i (i + 1) = d.val.f₀ ≫ (X.d i j ≫ e.hom) := by
            rw [← X.d_comp_XIsoOfEq_hom hij.symm i]
          _ = d.val.d₀ ≫ s.f ≫ e.hom := by
            rw [← Category.assoc, d.val.comm]
            simp [Category.assoc] }

/-- The degree of the layer preceding the `n`-th one. -/
private def prevDeg (a : ℤ) : ℕ → ℤ
  | 0 => a - ((0 : ℕ) : ℤ) + 1
  | n + 1 => a - (n : ℤ)

private lemma layerAdjacency (a : ℤ) (n : ℕ) :
    a - ((n + 1 : ℕ) : ℤ) + 1 = prevDeg a (n + 1) := by
  simp [prevDeg]
  omega

section

variable (hP : CoversEpis R G) (hQzero : G (0 : A))
  (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E)) (hX : ∀ i, R (X.homology i)) (a : ℤ)

/-- The `n`-th layer of the resolution, in degree `a - n`. -/
private def layer : (n : ℕ) → Layer R G X (a - (n : ℤ))
  | 0 => Layer.next R G X (Layer.zero R G X (prevDeg a 0) hQzero)
      (by simp [prevDeg]) hP hQbiprod hX
  | n + 1 => Layer.next R G X (layer n) (layerAdjacency a n) hP hQbiprod hX

/-- The layer preceding the `n`-th one. -/
private def prevLayer : (n : ℕ) → Layer R G X (prevDeg a n)
  | 0 => Layer.zero R G X (prevDeg a 0) hQzero
  | n + 1 => layer R G X hP hQzero hQbiprod hX a n

/-- The step data used to build the `n`-th layer. -/
private def layerStep (n : ℕ) :
    {d : StepData R X (a - (n : ℤ)) (prevDeg a n)
      (prevLayer R G X hP hQzero hQbiprod hX a n).d
      (prevLayer R G X hP hQzero hQbiprod hX a n).f // G d.Y₀} :=
  match n with
  | 0 => Layer.step R G X (Layer.zero R G X (prevDeg a 0) hQzero)
      (by simp [prevDeg]) hP hQbiprod hX
  | n + 1 => Layer.step R G X (layer R G X hP hQzero hQbiprod hX a n)
      (layerAdjacency a n) hP hQbiprod hX

/-- The differential of the resolution, from the `n + 1`-st to the `n`-th layer. -/
private def layerD (n : ℕ) :
    (layer R G X hP hQzero hQbiprod hX a (n + 1)).Y ⟶
      (layer R G X hP hQzero hQbiprod hX a n).Y :=
  (layer R G X hP hQzero hQbiprod hX a (n + 1)).d

/-- The resolution, as a `ℕ`-indexed chain complex of layers. -/
private def resolution : ChainComplex A ℕ :=
  ChainComplex.of (fun n => (layer R G X hP hQzero hQbiprod hX a n).Y)
    (layerD R G X hP hQzero hQbiprod hX a)
    (by
      intro n
      change (layerStep R G X hP hQzero hQbiprod hX a (n + 2)).val.d₀ ≫
        (layerStep R G X hP hQzero hQbiprod hX a (n + 1)).val.d₀ = 0
      exact (layerStep R G X hP hQzero hQbiprod hX a (n + 2)).val.zero)

private lemma resolution_d (n : ℕ) :
    (resolution R G X hP hQzero hQbiprod hX a).d (n + 1) n =
      layerD R G X hP hQzero hQbiprod hX a n := by
  unfold resolution
  exact ChainComplex.of_d
    (fun n => (layer R G X hP hQzero hQbiprod hX a n).Y)
    (layerD R G X hP hQzero hQbiprod hX a) n

/-- The map from the resolution to the restriction of `X`. -/
private def resolutionHom :
    resolution R G X hP hQzero hQbiprod hX a ⟶ X.restriction (embeddingUpIntLE a) where
  f n := (layer R G X hP hQzero hQbiprod hX a n).f
  comm' n m hnm := by
    obtain rfl : n = m + 1 := hnm.symm
    rw [resolution_d]
    change (layer R G X hP hQzero hQbiprod hX a (m + 1)).f ≫
      X.d (a - ((m + 1 : ℕ) : ℤ)) (a - (m : ℤ)) =
        layerD R G X hP hQzero hQbiprod hX a m ≫
          (layer R G X hP hQzero hQbiprod hX a m).f
    simpa [embeddingUpIntLE_f, prevDeg, layerD, layerStep, prevLayer, layer, Layer.next] using
      (layerStep R G X hP hQzero hQbiprod hX a (m + 1)).val.comm

/-- The identification of a term of the extended resolution with a layer. -/
private def layerExtendXIso {n : ℕ} {i : ℤ} (h : (embeddingUpIntLE a).f n = i) :
    ((resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a)).X i ≅
      (layer R G X hP hQzero hQbiprod hX a n).Y :=
  (resolution R G X hP hQzero hQbiprod hX a).extendXIso (embeddingUpIntLE a) h

private lemma resolution_extend_d_eq (n : ℕ) {i j : ℤ}
    (hi : (embeddingUpIntLE a).f (n + 1) = i) (hj : (embeddingUpIntLE a).f n = j) :
    ((resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a)).d i j =
      (layerExtendXIso R G X hP hQzero hQbiprod hX a hi).hom ≫
        layerD R G X hP hQzero hQbiprod hX a n ≫
        (layerExtendXIso R G X hP hQzero hQbiprod hX a hj).inv := by
  rw [← resolution_d]
  exact HomologicalComplex.extend_d_eq _ _ hi hj

private lemma descExtend_resolution_f [X.IsStrictlyLE a] (n : ℕ) :
    (ObjectProperty.descExtend X (resolution R G X hP hQzero hQbiprod hX a) a
      (resolutionHom R G X hP hQzero hQbiprod hX a)).f (a - (n : ℤ)) =
      (layerExtendXIso R G X hP hQzero hQbiprod hX a (embeddingUpIntLE_f a n)).hom ≫
        (layer R G X hP hQzero hQbiprod hX a n).f := by
  have h : (resolutionHom R G X hP hQzero hQbiprod hX a).f n ≫
      (X.restrictionXIso (embeddingUpIntLE a) (embeddingUpIntLE_f a n)).hom =
      (layer R G X hP hQzero hQbiprod hX a n).f := Category.comp_id _
  rw [ObjectProperty.descExtend_f,
    ObjectProperty.descF_eq X (resolution R G X hP hQzero hQbiprod hX a) a
      (resolutionHom R G X hP hQzero hQbiprod hX a) (embeddingUpIntLE_f a n), h]
  rfl

private lemma layer_epiH (n : ℕ) :
    ∃ (C : A) (γ : C ⟶ (layer R G X hP hQzero hQbiprod hX a n).Y)
      (c : C ⟶ X.cycles (a - (n : ℤ))),
      γ ≫ (layer R G X hP hQzero hQbiprod hX a n).d = 0 ∧
      c ≫ X.iCycles (a - (n : ℤ)) = γ ≫ (layer R G X hP hQzero hQbiprod hX a n).f ∧
      Epi (c ≫ X.homologyπ (a - (n : ℤ))) := by
  cases n with
  | zero => exact (layerStep R G X hP hQzero hQbiprod hX a 0).val.epiH
  | succ n => exact (layerStep R G X hP hQzero hQbiprod hX a (n + 1)).val.epiH

private lemma layer_cover (n : ℕ) ⦃T : A⦄
    (t : T ⟶ (layer R G X hP hQzero hQbiprod hX a n).Y)
    (ht : t ≫ (layer R G X hP hQzero hQbiprod hX a n).d = 0)
    (hu : ∃ u : T ⟶ X.X (a - ((n + 1 : ℕ) : ℤ)),
      t ≫ (layer R G X hP hQzero hQbiprod hX a n).f =
        u ≫ X.d (a - ((n + 1 : ℕ) : ℤ)) (a - (n : ℤ))) :
    ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p)
      (s : T' ⟶ (layer R G X hP hQzero hQbiprod hX a (n + 1)).Y),
      p ≫ t = s ≫ layerD R G X hP hQzero hQbiprod hX a n := by
  obtain ⟨T', p, hp, s, hs⟩ :=
    (layerStep R G X hP hQzero hQbiprod hX a (n + 1)).val.cover t ht hu
  refine ⟨T', p, hp, s, ?_⟩
  simpa [layerD, layerStep, prevLayer, layer, Layer.next] using hs

private lemma comp_extend_d_eq_zero (n : ℕ) {C : A}
    (γ : C ⟶ (layer R G X hP hQzero hQbiprod hX a n).Y)
    (hγd : γ ≫ (layer R G X hP hQzero hQbiprod hX a n).d = 0) :
    (γ ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a (embeddingUpIntLE_f a n)).inv) ≫
      ((resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a)).d
        (a - (n : ℤ)) (a - (n : ℤ) + 1) = 0 := by
  cases n with
  | zero =>
      exact (ObjectProperty.isZero_extend_X_of_not_le
        (resolution R G X hP hQzero hQbiprod hX a) a _ (by omega)).eq_of_tgt _ 0
  | succ m =>
      have h2 : (embeddingUpIntLE a).f m = a - ((m + 1 : ℕ) : ℤ) + 1 := by
        rw [embeddingUpIntLE_f]; omega
      have hγd' : γ ≫ layerD R G X hP hQzero hQbiprod hX a m = 0 := by
        show γ ≫ (layer R G X hP hQzero hQbiprod hX a (m + 1)).d = 0
        exact hγd
      rw [resolution_extend_d_eq R G X hP hQzero hQbiprod hX a m
        (embeddingUpIntLE_f a (m + 1)) h2]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hγd', zero_comp]

private lemma comp_layer_d_eq_zero (n : ℕ) ⦃T : A⦄
    (t : T ⟶ ((resolution R G X hP hQzero hQbiprod hX a).extend
      (embeddingUpIntLE a)).X (a - (n : ℤ)))
    (ht : t ≫ ((resolution R G X hP hQzero hQbiprod hX a).extend
      (embeddingUpIntLE a)).d (a - (n : ℤ)) (a - (n : ℤ) + 1) = 0) :
    (t ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a (embeddingUpIntLE_f a n)).hom) ≫
      (layer R G X hP hQzero hQbiprod hX a n).d = 0 := by
  cases n with
  | zero =>
      exact (isZero_zero A).eq_of_tgt _ 0
  | succ m =>
      have h2 : (embeddingUpIntLE a).f m = a - ((m + 1 : ℕ) : ℤ) + 1 := by
        rw [embeddingUpIntLE_f]; omega
      show _ ≫ layerD R G X hP hQzero hQbiprod hX a m = 0
      rw [resolution_extend_d_eq R G X hP hQzero hQbiprod hX a m
        (embeddingUpIntLE_f a (m + 1)) h2] at ht
      rw [← cancel_mono (layerExtendXIso R G X hP hQzero hQbiprod hX a h2).inv, zero_comp]
      simp only [Category.assoc] at ht ⊢
      exact ht

end

/-- The complex of layers, extended to a `ℤ`-indexed cochain complex, together with its map to
`X` and the two conditions which make that map a quasi-isomorphism. -/
private lemma exists_complex_of_coversEpis (hP : CoversEpis R G) (hQzero : G (0 : A))
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hQiso : ∀ ⦃V W : A⦄ (e : V ⟶ W), IsIso e → G V → G W)
    (hX : ∀ i, R (X.homology i)) (a : ℤ) [X.IsStrictlyLE a] :
    ∃ (Y : CochainComplex A ℤ) (_ : Y.IsStrictlyLE a) (φ : Y ⟶ X),
      (∀ i, G (Y.X i)) ∧
      (∀ i : ℤ, ∃ (C : A) (γ : C ⟶ Y.X i) (c : C ⟶ X.cycles i),
        γ ≫ Y.d i (i + 1) = 0 ∧ c ≫ X.iCycles i = γ ≫ φ.f i ∧
          Epi (c ≫ X.homologyπ i)) ∧
      (∀ (i : ℤ) ⦃T : A⦄ (t : T ⟶ Y.X i), t ≫ Y.d i (i + 1) = 0 →
        (∃ u : T ⟶ X.X (i - 1), t ≫ φ.f i = u ≫ X.d (i - 1) i) →
        ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ Y.X (i - 1)),
          p ≫ t = s ≫ Y.d (i - 1) i) := by
  refine ⟨(resolution R G X hP hQzero hQbiprod hX a).extend (embeddingUpIntLE a),
    inferInstance,
    ObjectProperty.descExtend X (resolution R G X hP hQzero hQbiprod hX a) a
      (resolutionHom R G X hP hQzero hQbiprod hX a), ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ≤ a
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, i = a - (n : ℤ) := ⟨(a - i).toNat, by omega⟩
      subst i
      let e := (layerExtendXIso R G X hP hQzero hQbiprod hX a
        (embeddingUpIntLE_f a n)).symm
      exact hQiso e.hom inferInstance (layer R G X hP hQzero hQbiprod hX a n).hQ
    · have hzero := ObjectProperty.isZero_extend_X_of_not_le
        (resolution R G X hP hQzero hQbiprod hX a) a i hi
      exact hQiso (IsZero.iso (isZero_zero _) hzero).hom inferInstance hQzero
  · intro i
    by_cases hi : i ≤ a
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = a - (n : ℤ) := ⟨(a - i).toNat, by omega⟩
      obtain ⟨C, γ, c, hγd, hγc, hce⟩ := layer_epiH R G X hP hQzero hQbiprod hX a n
      refine ⟨C, γ ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a
        (embeddingUpIntLE_f a n)).inv, c,
        comp_extend_d_eq_zero R G X hP hQzero hQbiprod hX a n γ hγd, ?_, hce⟩
      rw [descExtend_resolution_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact hγc
    · exact ⟨0, 0, 0, by simp, by simp, (X.isZero_of_isLE a i (by omega)).epi _⟩
  · intro i T t ht hu
    by_cases hi : i ≤ a
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = a - (n : ℤ) := ⟨(a - i).toNat, by omega⟩
      have h1 : (embeddingUpIntLE a).f (n + 1) = a - (n : ℤ) - 1 := by
        rw [embeddingUpIntLE_f]; omega
      have hbdry : ∃ u : T ⟶ X.X (a - ((n + 1 : ℕ) : ℤ)),
          (t ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a
            (embeddingUpIntLE_f a n)).hom) ≫
              (layer R G X hP hQzero hQbiprod hX a n).f =
            u ≫ X.d (a - ((n + 1 : ℕ) : ℤ)) (a - (n : ℤ)) := by
        obtain ⟨u, hu⟩ := hu
        refine ⟨u ≫ (X.XIsoOfEq (show a - (n : ℤ) - 1 =
          a - ((n + 1 : ℕ) : ℤ) by omega)).hom, ?_⟩
        rw [descExtend_resolution_f] at hu
        simp only [Category.assoc] at hu ⊢
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d]
        exact hu
      obtain ⟨T', p, hp, s, hs⟩ := layer_cover R G X hP hQzero hQbiprod hX a n
        (t ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a
          (embeddingUpIntLE_f a n)).hom)
        (comp_layer_d_eq_zero R G X hP hQzero hQbiprod hX a n t ht) hbdry
      refine ⟨T', p, hp, s ≫ (layerExtendXIso R G X hP hQzero hQbiprod hX a h1).inv, ?_⟩
      rw [resolution_extend_d_eq R G X hP hQzero hQbiprod hX a n h1 (embeddingUpIntLE_f a n)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, ← hs]
      simp
    · refine ⟨T, 𝟙 T, inferInstance, 0, ?_⟩
      rw [Category.id_comp, zero_comp]
      exact (ObjectProperty.isZero_extend_X_of_not_le
        (resolution R G X hP hQzero hQbiprod hX a) a i hi).eq_of_tgt t 0

/-- **The bounded above resolution engine.** Let `A` be an abelian category, let `R` be a weak
Serre class in `A` and let `G` be a class of objects of `A` which contains the zero object, is
closed under binary biproducts and under isomorphism, and covers epimorphisms onto objects of
`R`. Then every cochain complex `X` with `X^i = 0` for `i > a` whose cohomology objects all lie
in `R` receives a quasi-isomorphism from a cochain complex `Y` with `Y^i = 0` for `i > a` and
every term in `G`.

The complex `Y` is built degree by degree downwards from `a`: in each degree the new term is the
biproduct of an object of `G` covering the cohomology of `X` in that degree, which makes the map
surjective on cohomology, and an object of `G` covering, up to refinement, those cocycles of the
previously built term whose image in `X` is a boundary, which makes the map injective on
cohomology. -/
@[sga "4½ Etat_0 3.1.9" "Part 1, special case"]
public theorem exists_quasiIso_isStrictlyLE_of_coversEpis
    (hP : CoversEpis R G) (hQzero : G (0 : A))
    (hQbiprod : ∀ ⦃C E : A⦄, G C → G E → G (C ⊞ E))
    (hQiso : ∀ ⦃V W : A⦄ (e : V ⟶ W), IsIso e → G V → G W)
    (a : ℤ) [X.IsStrictlyLE a] (hX : ∀ i, R (X.homology i)) :
    ∃ (Y : CochainComplex A ℤ) (_ : Y.IsStrictlyLE a) (f : Y ⟶ X) (_ : QuasiIso f),
      ∀ i, G (Y.X i) := by
  obtain ⟨Y, hY, f, hGY, hepi, hcov⟩ :=
    exists_complex_of_coversEpis R G X hP hQzero hQbiprod hQiso hX a
  exact ⟨Y, hY, f, quasiIso_of_epi_of_cover f hepi hcov, hGY⟩

end Resolution

end Stacks.Homology.BoundedAboveResolution

end
