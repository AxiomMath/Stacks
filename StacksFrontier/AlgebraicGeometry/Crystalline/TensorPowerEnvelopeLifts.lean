module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDPAlgHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeTaylorFormula

/-!
# Maps out of the completed divided power envelopes of the tensor powers of a presentation

Let `P = A[x_i] → C` be a surjective polynomial presentation in an affine crystalline situation,
`D(n)` the `p`-adically completed divided power envelope of the kernel of
`P ⊗_A ⋯ ⊗_A P → C` on the `(n + 1)`-fold tensor power (the cosimplicial ring of
[Stacks, Tag 07JN] and [Stacks, Proposition 60.21.3, Tag 07LG]).  This module provides two maps
out of these rings that the proof of [Stacks, Lemma 60.21.4, Tag 07LH] uses.

* `Crystalline.exists_completedTensorPowerOneLift` — **the universal property of `D(1)`**: two
  divided power `A`-algebra maps `u, v : D(0) → D_R` into a completed divided power ring, congruent
  modulo the divided power ideal, are the restrictions of one map `w : D(1) → D_R` along the two
  coprojections.
* `Crystalline.exists_completedTensorPowerRetract` — **the retract of
  [Stacks, Lemma 60.17.5, Tag 07L5] at a tensor power**: for a smooth presentation `P' → C` and a
  surjection `q : P ⊗ ⋯ ⊗ P ↠ P'` over `C`, there are divided power `A`-algebra maps
  `a : D(n) → D'` and `b : D' → D(n)` with `a ∘ b = id`, `a` being the completion of the map of
  envelopes induced by `q`.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers Simplicial

universe u

namespace Crystalline

section TensorPower

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance

include hf in
/-- `p` is nilpotent modulo the divided power ideal of the envelope of a tensor power. -/
theorem tensorPowerEnvelope_prime_nilpotent (n : ℕ) :
    IsNilpotent (Ideal.Quotient.mk (tensorPowerEnvelope s f n).object.ideal
      (s.p : (tensorPowerEnvelope s f n).object)) :=
  presentationEnvelope_prime_nilpotent s (tensorPowerPresentation s f n)
    (tensorPowerPresentation_surjective s f hf n)

/-- **The completed reindexing map `D(m) → D(n)`** of a map of finite ordinals, as an
`A`-algebra map: the `p`-adic completion of the reindexing of the envelopes.  Its underlying ring
map is the transition map `Crystalline.CosimplicialDPAlgebra.completedRingMap` of the completed
cosimplicial envelope. -/
abbrev completedReindex {m n : SimplexCategory} (φ : m ⟶ n) :
    AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope s f m.len).object) s.p)
        (tensorPowerEnvelope s f m.len).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope s f n.len).object) s.p)
        (tensorPowerEnvelope s f n.len).object where
  toRingHom := (envelopeDPAlgebra s f).completedRingMap s.p φ
  commutes' c :=
    (adicCompletionRingMap_of ((envelopeDPAlgebra s f).map φ).toRingHom (map_pAdicIdeal_le s.p _)
      (algebraMap (s.A : Type u) ((envelopeDPAlgebra s f).carrier m.len) c)).trans
      (congrArg (AdicCompletion.of _ _) (((envelopeDPAlgebra s f).map φ).commutes c))

/-- The completed reindexing map extends the reindexing of the envelopes. -/
theorem completedReindex_of {m n : SimplexCategory} (φ : m ⟶ n)
    (b : (tensorPowerEnvelope s f m.len).object) :
    completedReindex s f φ (AdicCompletion.of _ _ b) =
      AdicCompletion.of _ _ ((envelopeReindex s f φ).1 b) :=
  adicCompletionRingMap_of _ _ b

/-- The completed reindexing map is the transition map of the completed cosimplicial
envelope. -/
theorem completedReindex_toRingHom {m n : SimplexCategory} (φ : m ⟶ n) :
    (completedReindex s f φ).toRingHom = (envelopeDPAlgebra s f).completedRingMap s.p φ :=
  rfl

include hf in
/-- The completed reindexing map is a divided power morphism. -/
theorem isDPMorphism_completedReindex {m n : SimplexCategory} (φ : m ⟶ n) :
    IsDPMorphism (completionDividedPowers s.p (tensorPowerEnvelope s f m.len).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent s f hf m.len))
      (completionDividedPowers s.p (tensorPowerEnvelope s f n.len).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent s f hf n.len))
      (completedReindex s f φ).toRingHom := by
  have h : completedReindex s f φ = completedDPAlgHom s.p s.A
      (tensorPowerEnvelope s f m.len).object.dividedPowers
      (tensorPowerEnvelope_prime_nilpotent s f hf m.len)
      (tensorPowerEnvelope s f n.len).object.dividedPowers
      (tensorPowerEnvelope_prime_nilpotent s f hf n.len) (envelopeReindexAlgHomOfSimplex s f φ)
      (envelopeReindex s f φ).1.isDPMorphism :=
    completedAlgHom_ext s.p s.A fun b ↦ by
      rw [completedReindex_of]
      exact (completedDPAlgHom_of s.p s.A _ (tensorPowerEnvelope_prime_nilpotent s f hf m.len) _
        (tensorPowerEnvelope_prime_nilpotent s f hf n.len) (envelopeReindexAlgHomOfSimplex s f φ)
        (envelopeReindex s f φ).1.isDPMorphism b).symm
  rw [h]
  exact isDPMorphism_completedDPAlgHom s.p s.A _ _ _ _ _ _

/-- The reindexing renames the coordinates. -/
theorem envelopeReindex_envelopeCoord {m n : SimplexCategory} (φ : m ⟶ n)
    (q : Fin (m.len + 1) × ι) :
    (envelopeReindex s f φ).1 (envelopeCoord (tensorPowerEnvelope s f m.len) q) =
      envelopeCoord (tensorPowerEnvelope s f n.len) (φ.toOrderHom q.1, q.2) := by
  rw [envelopeCoord, envelopeReindex_polynomial, MvPolynomial.rename_X]
  rfl

/-- The reindexing of the envelopes is compatible with the structure maps. -/
private theorem envelopeReindex_structureMap {m n : SimplexCategory} (φ : m ⟶ n)
    (c : (s.A : Type u)) :
    (envelopeReindex s f φ).1 ((tensorPowerEnvelope s f m.len).structureMap c) =
      (tensorPowerEnvelope s f n.len).structureMap c :=
  congrArg (fun q : DPMorphism _ _ ↦ q c) (envelopeReindex s f φ).2

/-- The completed reindexing maps compose. -/
theorem completedReindex_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) :
    (completedReindex s f ψ).comp (completedReindex s f φ) =
      completedReindex s f (φ ≫ ψ) :=
  completedAlgHom_ext s.p s.A fun b ↦ by
    rw [AlgHom.comp_apply, completedReindex_of, completedReindex_of, completedReindex_of,
      envelopeReindex_comp]

/-- The completed reindexing map of an identity is the identity. -/
theorem completedReindex_id (n : SimplexCategory) :
    completedReindex s f (𝟙 n) = AlgHom.id _ _ :=
  completedAlgHom_ext s.p s.A fun b ↦ by
    rw [completedReindex_of, envelopeReindex_id, AlgHom.id_apply]

end TensorPower

section DegreeOne

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)
  {R : Type u} [CommRing R] [Algebra (s.A : Type u) R] {JR : Ideal R} (hR : DividedPowers JR)
  (hpR : IsNilpotent (Ideal.Quotient.mk JR (s.p : R)))

attribute [local instance] tensorPowerEnvelopeAlgebraInstance

/-- A divided power `A`-algebra map, read as a divided power morphism of the completions. -/
abbrev dpMorphismOfAlgHom {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂] {J₁ : Ideal B₁}
    {J₂ : Ideal B₂} {h₁ : DividedPowers J₁} {h₂ : DividedPowers J₂} (φ : B₁ →+* B₂)
    (hφ : IsDPMorphism h₁ h₂ φ) : DPMorphism h₁ h₂ :=
  ⟨φ, hφ.1, hφ.2⟩

include hf in
/-- The completion `w : D(1) → D_R` of a divided power `A`-algebra map `w₀` restricts to `t`
along the coprojection of the vertex `i` as soon as `w₀` sends the coordinates of `i` to the
images under `t` of the coordinates of `D(0)`. -/
private theorem completedTensorPowerOne_comp_const_eq (i : Fin 2)
    (w₀ : DPMorphism (tensorPowerEnvelope s f 1).object.dividedPowers
      (completionDPRing s.p hR hpR).dividedPowers)
    (hw₀ : ∀ c, w₀ ((tensorPowerEnvelope s f 1).structureMap c) =
      algebraMap (s.A : Type u) (AdicCompletion (pAdicIdeal (A := R) s.p) R) c)
    (w : AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope s f 1).object) s.p)
        (tensorPowerEnvelope s f 1).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := R) s.p) R)
    (hw : ∀ b, w (AdicCompletion.of _ _ b) = w₀ b)
    (t : AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope s f 0).object) s.p)
        (tensorPowerEnvelope s f 0).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := R) s.p) R)
    (ht : IsDPMorphism (completionDividedPowers s.p (tensorPowerEnvelope s f 0).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent s f hf 0))
      (completionDividedPowers s.p hR hpR) t.toRingHom)
    (hwt : ∀ j, w₀ (envelopeCoord (tensorPowerEnvelope s f 1) (i, j)) =
      t (AdicCompletion.of _ _ (envelopeCoord (tensorPowerEnvelope s f 0) ((0 : Fin 1), j)))) :
    w.comp (completedReindex s f (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)) = t := by
  refine completedAlgHom_ext s.p s.A fun b ↦ ?_
  rw [AlgHom.comp_apply, completedReindex_of, hw]
  change (w₀.comp (envelopeReindex s f (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).1) b =
    ((dpMorphismOfAlgHom (h₂ := (completionDPRing s.p hR hpR).dividedPowers) t.toRingHom ht).comp
      (completionDPMorphism _ _ s.p (tensorPowerEnvelope_prime_nilpotent s f hf 0))) b
  congr 1
  refine envelope_dpMorphism_ext _ _ _ ?_ fun ⟨k, j⟩ ↦ ?_
  · refine DPMorphism.ext (funext fun c ↦ ?_)
    change w₀ ((envelopeReindex s f (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).1
      ((tensorPowerEnvelope s f 0).structureMap c)) =
        t (AdicCompletion.of _ _ ((tensorPowerEnvelope s f 0).structureMap c))
    rw [envelopeReindex_structureMap s f (SimplexCategory.const ⦋0⦌ ⦋1⦌ i), hw₀]
    exact (t.commutes c).symm
  · obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
    change w₀ ((envelopeReindex s f (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).1
      (envelopeCoord (tensorPowerEnvelope s f 0) (0, j))) =
        t (AdicCompletion.of _ _ (envelopeCoord (tensorPowerEnvelope s f 0) (0, j)))
    rw [envelopeReindex_envelopeCoord]
    exact hwt j

include hf in
/-- **The universal property of `D(1)`**: two divided power `A`-algebra maps `u, v : D(0) → D_R`
into a completed divided power ring which are congruent modulo its divided power ideal are the
restrictions of one divided power `A`-algebra map `w : D(1) → D_R` along the two coprojections,
`w ∘ σ = v` for the vertex `0` and `w ∘ δ = u` for the vertex `1`. -/
theorem exists_completedTensorPowerOneLift
    (u v : AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope s f 0).object) s.p)
        (tensorPowerEnvelope s f 0).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := R) s.p) R)
    (hu : IsDPMorphism (completionDividedPowers s.p (tensorPowerEnvelope s f 0).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent s f hf 0))
      (completionDividedPowers s.p hR hpR) u.toRingHom)
    (hv : IsDPMorphism (completionDividedPowers s.p (tensorPowerEnvelope s f 0).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent s f hf 0))
      (completionDividedPowers s.p hR hpR) v.toRingHom)
    (huv : ∀ x, u x - v x ∈ completionIdeal JR s.p hpR) :
    ∃ w : AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope s f 1).object) s.p)
        (tensorPowerEnvelope s f 1).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := R) s.p) R,
      IsDPMorphism (completionDividedPowers s.p (tensorPowerEnvelope s f 1).object.dividedPowers
          (tensorPowerEnvelope_prime_nilpotent s f hf 1))
        (completionDividedPowers s.p hR hpR) w.toRingHom ∧
      w.comp (completedReindex s f (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)) = v ∧
      w.comp (completedReindex s f (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) = u := by
  classical
  set E₀ := tensorPowerEnvelope s f 0
  set E₁ := tensorPowerEnvelope s f 1
  set C : DividedPowerRing.{u} := completionDPRing s.p hR hpR
  set hp₀ := tensorPowerEnvelope_prime_nilpotent s f hf 0
  set hp₁ := tensorPowerEnvelope_prime_nilpotent s f hf 1
  let ofDP₀ := completionDPMorphism E₀.object.ideal E₀.object.dividedPowers s.p hp₀
  let vDP : DPMorphism (completionDividedPowers s.p E₀.object.dividedPowers hp₀) C.dividedPowers :=
    dpMorphismOfAlgHom v.toRingHom hv
  let deg := (envelopeReindex s f (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)).1
  let m₀ : DPMorphism E₁.object.dividedPowers C.dividedPowers := (vDP.comp ofDP₀).comp deg
  let c₀ : ι → C := fun i ↦ v (AdicCompletion.of _ _ (envelopeCoord E₀ ((0 : Fin 1), i)))
  let c₁ : ι → C := fun i ↦ u (AdicCompletion.of _ _ (envelopeCoord E₀ ((0 : Fin 1), i)))
  let vals : Fin 2 × ι → C := fun q ↦ if q.1 = 0 then c₀ q.2 else c₁ q.2
  have hm₀ : ∀ q : Fin 2 × ι, m₀ (envelopeCoord E₁ q) = c₀ q.2 := fun q ↦ by
    change v (AdicCompletion.of _ _ (deg (envelopeCoord E₁ q))) = _
    rw [envelopeReindex_envelopeCoord]
    congr 3
  have hvals : ∀ q, vals q - m₀ (envelopeCoord E₁ q) ∈ C.ideal := fun q ↦ by
    rw [hm₀]
    by_cases hq : q.1 = 0
    · simp only [vals, ite_eq_left hq, sub_self]
      exact C.ideal.zero_mem
    · simp only [vals, ite_eq_right hq]
      exact huv _
  obtain ⟨w₀, hw₀A, hw₀⟩ := exists_envelope_dpMorphism E₁ C (m₀.comp E₁.structureMap) vals
    (envelope_eval₂Hom_map_le_of_sub_mem E₁ C m₀ vals hvals)
  have hstr : ∀ c : (s.A : Type u), m₀ (E₁.structureMap c) =
      algebraMap (s.A : Type u) (AdicCompletion (pAdicIdeal (A := R) s.p) R) c := fun c ↦ by
    change v (AdicCompletion.of _ _ (deg (E₁.structureMap c))) = _
    rw [envelopeReindex_structureMap s f (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)]
    exact v.commutes c
  have hw₀c : ∀ c, w₀ (E₁.structureMap c) =
      algebraMap (s.A : Type u) (AdicCompletion (pAdicIdeal (A := R) s.p) R) c := fun c ↦
    (congrArg (fun q : DPMorphism _ _ ↦ q c) hw₀A).trans (hstr c)
  let w₀Alg : E₁.object →ₐ[(s.A : Type u)] AdicCompletion (pAdicIdeal (A := R) s.p) R :=
    { w₀.toRingHom with commutes' := hw₀c }
  obtain ⟨w, hwDP, hwof⟩ := exists_completedDPAlgHom s.p s.A E₁.object.dividedPowers hp₁ hR hpR
    w₀Alg w₀.isDPMorphism
  refine ⟨w, hwDP, completedTensorPowerOne_comp_const_eq s f hf hR hpR 0 w₀ hw₀c w hwof v hv
    fun j ↦ ?_, completedTensorPowerOne_comp_const_eq s f hf hR hpR 1 w₀ hw₀c w hwof u hu
    fun j ↦ ?_⟩
  · rw [hw₀]
    exact ite_eq_left rfl
  · rw [hw₀]
    exact ite_eq_right (by simp)

end DegreeOne

section Retract

variable (s : AffineCrystallineSituation.{u, u})

/-- The divided power envelope of a presentation is an algebra over the base through its
structure map. -/
abbrev presentationEnvelopeAlgebraInst {P : Type u} [CommRing P] [Algebra s.A P]
    (g : P →ₐ[s.A] s.C) : Algebra (s.A : Type u) (presentationEnvelope s g).object :=
  (presentationEnvelope s g).structureMap.toRingHom.toAlgebra

attribute [local instance] presentationEnvelopeAlgebraInst

/-- **The retract of [Stacks, Lemma 60.17.5, Tag 07L5], as divided power algebra maps.**  For a
smooth presentation `P' → C` and a surjection `q : P ↠ P'` of `A`-algebras with `f' ∘ q = g`, the
completed envelopes `D` of `g` and `D'` of `f'` are related by divided power `A`-algebra maps
`a : D → D'` and `b : D' → D` with `a ∘ b = id`; `a` is the completion of the map of envelopes
induced by `q`. -/
theorem exists_completedEnvelopeRetractAlgHom {P P' : Type u} [CommRing P] [Algebra s.A P]
    [CommRing P'] [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P']
    (q : P →ₐ[s.A] P') (f' : P' →ₐ[s.A] s.C) (hq : Function.Surjective q)
    (hf' : Function.Surjective f') (g : P →ₐ[s.A] s.C) (hfq : f'.comp q = g)
    (hgs : Function.Surjective g)
    (hg : IsNilpotent (Ideal.Quotient.mk (presentationEnvelope s g).object.ideal
      (s.p : (presentationEnvelope s g).object))) :
    ∃ (a : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s g).object) s.p)
          (presentationEnvelope s g).object →ₐ[(s.A : Type u)]
        AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
          (presentationEnvelope s f').object)
      (b : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
          (presentationEnvelope s f').object →ₐ[(s.A : Type u)]
        AdicCompletion (pAdicIdeal (A := (presentationEnvelope s g).object) s.p)
          (presentationEnvelope s g).object),
      IsDPMorphism (completionDividedPowers s.p (presentationEnvelope s g).object.dividedPowers hg)
        (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers
          (presentationEnvelope_prime_nilpotent s f' hf')) a.toRingHom ∧
      IsDPMorphism (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers
          (presentationEnvelope_prime_nilpotent s f' hf'))
        (completionDividedPowers s.p (presentationEnvelope s g).object.dividedPowers hg)
        b.toRingHom ∧
      a.comp b = AlgHom.id _ _ ∧
      (∀ x : P, a (AdicCompletion.of _ _ ((presentationEnvelope s g).algebraMap.toRingHom x)) =
        AdicCompletion.of _ _ ((presentationEnvelope s f').algebraMap.toRingHom (q x))) ∧
      (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
        completedEnvelopeAugmentation s g hgs ∧
      (completedEnvelopeAugmentation s g hgs).comp b.toRingHom =
        completedEnvelopeAugmentation s f' hf' := by
  subst hfq
  obtain ⟨ρ, hρstr, hρalg, -, -, a, b, hab, haρ, hbstr⟩ :=
    exists_completedEnvelopeRetract s q f' hq hf'
  have hρ : ∀ x, ρ ((presentationEnvelope s (f'.comp q)).algebraMap.toRingHom x) =
      (presentationEnvelope s f').algebraMap.toRingHom (q x) := fun x ↦
    congrArg (fun r : P →+* _ ↦ r x) hρalg
  have hρs : ∀ c, ρ ((presentationEnvelope s (f'.comp q)).structureMap c) =
      (presentationEnvelope s f').structureMap c := fun c ↦
    congrArg (fun r : DPMorphism _ _ ↦ r c) hρstr
  have haρ' : ∀ x y, ρ x = y → a (AdicCompletion.of _ _ x) = AdicCompletion.of _ _ y :=
    fun x y h ↦ (haρ x).trans (congrArg _ h)
  let aAlg : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s (f'.comp q)).object) s.p)
        (presentationEnvelope s (f'.comp q)).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
        (presentationEnvelope s f').object :=
    { a.toRingHom with commutes' := fun c ↦ haρ' _ _ (hρs c) }
  let bAlg : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
        (presentationEnvelope s f').object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := (presentationEnvelope s (f'.comp q)).object) s.p)
        (presentationEnvelope s (f'.comp q)).object :=
    { b.toRingHom with
      commutes' := hbstr }
  have haug := completedEnvelopeAugmentation_comp_of_dpMorphism s q f' hf' hgs ρ hρalg a haρ
  have hab' : ∀ w, a (b w) = w := fun w ↦ congrArg (fun r : DPMorphism _ _ ↦ r w) hab
  refine ⟨aAlg, bAlg, a.isDPMorphism, b.isDPMorphism, AlgHom.ext hab', fun x ↦ ?_, haug, ?_⟩
  · exact haρ' _ _ (hρ x)
  · ext w
    have h1 := DFunLike.congr_fun haug (b.toRingHom w)
    rw [RingHom.comp_apply] at h1
    exact h1.symm.trans (congrArg _ (hab' w))

end Retract

section Surjection

variable (s : AffineCrystallineSituation.{u, u})

/-- **A tensor power of the canonical presentation surjects onto a smooth presentation**,
extending a given lift of the variables on the first factor.  The other factors send the
variable `x_c(k + 1)` to the `k`-th of finitely many generators of `P'` when `c` is its image in
`C`, and to the given lift of `c` otherwise; so the image contains the generators. -/
theorem exists_tensorPowerSurjection (P' : Type u) [CommRing P'] [Algebra s.A P']
    [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C)
    (g : MvPolynomial s.C s.A →ₐ[s.A] P') (hg : f'.comp g = canonicalPresentation s) :
    ∃ (n : ℕ) (q : MvPolynomial (Fin (n + 1) × s.C) s.A →ₐ[s.A] P'),
      Function.Surjective q ∧ f'.comp q = tensorPowerPresentation s (canonicalPresentation s) n ∧
        ∀ c, q (MvPolynomial.X ((0 : Fin (n + 1)), c)) = g (MvPolynomial.X c) := by
  classical
  obtain ⟨m, q₀, hq₀⟩ := exists_mvPolynomial_surjection_of_smooth (s.A : Type u) P'
  have hgc : ∀ c, f' (g (MvPolynomial.X c)) = c := fun c ↦ by
    simpa [canonicalPresentation] using
      congrArg (fun r : MvPolynomial s.C s.A →ₐ[s.A] s.C ↦ r (MvPolynomial.X c)) hg
  let vals : Fin (m + 1) × s.C → P' := fun q ↦
    Fin.cases (g (MvPolynomial.X q.2))
      (fun j : Fin m ↦ if q.2 = f' (q₀ (MvPolynomial.X j)) then q₀ (MvPolynomial.X j)
        else g (MvPolynomial.X q.2)) q.1
  refine ⟨m, MvPolynomial.aeval vals, fun y ↦ ?_, ?_, fun c ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := hq₀ y
    refine ⟨MvPolynomial.rename (fun j : Fin m ↦ (j.succ, f' (q₀ (MvPolynomial.X j)))) z, ?_⟩
    have : (MvPolynomial.aeval vals).comp
        (MvPolynomial.rename (fun j : Fin m ↦ (j.succ, f' (q₀ (MvPolynomial.X j))))) = q₀ := by
      refine MvPolynomial.algHom_ext fun j ↦ ?_
      simp [vals]
    exact congrArg (fun r : MvPolynomial (Fin m) s.A →ₐ[s.A] P' ↦ r z) this
  · refine MvPolynomial.algHom_ext fun q ↦ ?_
    obtain ⟨k, c⟩ := q
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, tensorPowerPresentation,
      MvPolynomial.rename_X, canonicalPresentation]
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · simpa [vals] using hgc c
    · simp only [vals, Fin.cases_succ]
      split_ifs with h
      · simp [h]
      · simpa using hgc c
  · simp [vals]

end Surjection

section Augmentation

variable (s : AffineCrystallineSituation.{u, u})

attribute [local instance] presentationEnvelopeAlgebraInst

/-- **The augmentation kills the completed divided power ideal.** -/
theorem completedEnvelopeAugmentation_eq_of_sub_mem {P : Type u} [CommRing P] [Algebra s.A P]
    (g : P →ₐ[s.A] s.C) (hg : Function.Surjective g)
    {z w : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s g).object) s.p)
      (presentationEnvelope s g).object}
    (h : z - w ∈ completionIdeal (presentationEnvelope s g).object.ideal s.p
      (presentationEnvelope_prime_nilpotent s g hg)) :
    completedEnvelopeAugmentation s g hg z = completedEnvelopeAugmentation s g hg w := by
  refine completedEnvelopeAugmentation_congr s g hg ?_
  rwa [← sub_eq_zero, ← map_sub]

/-- **A divided power `A`-algebra map of completed envelopes lying over a map of presentations is
compatible with the augmentations.** -/
theorem completedEnvelopeAugmentation_comp_of_algebraMap {P₁ P₂ : Type u} [CommRing P₁]
    [Algebra s.A P₁] [CommRing P₂] [Algebra s.A P₂] (g₁ : P₁ →ₐ[s.A] s.C)
    (hg₁ : Function.Surjective g₁) (g₂ : P₂ →ₐ[s.A] s.C) (hg₂ : Function.Surjective g₂)
    (r : P₁ →ₐ[s.A] P₂) (hr : g₂.comp r = g₁)
    (φ : AdicCompletion (pAdicIdeal (A := (presentationEnvelope s g₁).object) s.p)
        (presentationEnvelope s g₁).object →+*
      AdicCompletion (pAdicIdeal (A := (presentationEnvelope s g₂).object) s.p)
        (presentationEnvelope s g₂).object)
    (hφ : IsDPMorphism (completionDividedPowers s.p (presentationEnvelope s g₁).object.dividedPowers
        (presentationEnvelope_prime_nilpotent s g₁ hg₁))
      (completionDividedPowers s.p (presentationEnvelope s g₂).object.dividedPowers
        (presentationEnvelope_prime_nilpotent s g₂ hg₂)) φ)
    (hφr : ∀ y, φ (AdicCompletion.of _ _ ((presentationEnvelope s g₁).algebraMap.toRingHom y)) =
      AdicCompletion.of _ _ ((presentationEnvelope s g₂).algebraMap.toRingHom (r y))) :
    (completedEnvelopeAugmentation s g₂ hg₂).comp φ = completedEnvelopeAugmentation s g₁ hg₁ := by
  ext x
  obtain ⟨u, hu⟩ := exists_sub_algebraMap_mem_completionIdeal
    (presentationEnvelope s g₁).object.ideal s.p (presentationEnvelope_prime_nilpotent s g₁ hg₁) x
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_envelopeIdeal s g₁ hg₁ u
  have hof : ∀ t ∈ (presentationEnvelope s g₁).object.ideal,
      AdicCompletion.of (pAdicIdeal (A := (presentationEnvelope s g₁).object) s.p) _ t ∈
        completionIdeal (presentationEnvelope s g₁).object.ideal s.p
          (presentationEnvelope_prime_nilpotent s g₁ hg₁) := fun t ht ↦
    (completionDPMorphism _ (presentationEnvelope s g₁).object.dividedPowers s.p
      (presentationEnvelope_prime_nilpotent s g₁ hg₁)).ideal_comp (Ideal.mem_map_of_mem _ ht)
  have hx : x - AdicCompletion.of _ _ ((presentationEnvelope s g₁).algebraMap.toRingHom y) ∈
      completionIdeal (presentationEnvelope s g₁).object.ideal s.p
        (presentationEnvelope_prime_nilpotent s g₁ hg₁) := by
    have := Ideal.add_mem _ hu (hof _ hy)
    rwa [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_sub,
      sub_add_sub_cancel] at this
  have hφx : φ x - φ (AdicCompletion.of _ _ ((presentationEnvelope s g₁).algebraMap.toRingHom y))
      ∈ completionIdeal (presentationEnvelope s g₂).object.ideal s.p
        (presentationEnvelope_prime_nilpotent s g₂ hg₂) := by
    rw [← map_sub]
    exact hφ.1 (Ideal.mem_map_of_mem _ hx)
  rw [RingHom.comp_apply, completedEnvelopeAugmentation_eq_of_sub_mem s g₂ hg₂ hφx, hφr,
    completedEnvelopeAugmentation_eq_of_sub_mem s g₁ hg₁ hx]
  have h1 := completedEnvelopeAugmentation_algebraMap s g₂ hg₂ (r y)
  have h2 := completedEnvelopeAugmentation_algebraMap s g₁ hg₁ y
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h1 h2
  rw [h1, h2, ← hr, AlgHom.comp_apply]

end Augmentation

end Crystalline

end
