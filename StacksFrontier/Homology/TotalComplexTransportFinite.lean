module

public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Algebra.Homology.MatrixActionTotal

/-!
# Additive functors and coproducts with finitely many nonzero terms

An additive functor preserves a coproduct of a family all but finitely many of whose members are
zero: such a coproduct is a finite biproduct in disguise. Consequently an additive functor
commutes with the total complex of a bicomplex whose antidiagonals have finite support, without
any assumption on infinite coproducts.

## Main results

* `CategoryTheory.Functor.preservesColimit_discrete_of_finite_support`.
* `HomologicalComplex₂.isIso_totalMap_of_finite_support`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- Summing the images of the Kronecker-delta maps `X j ⟶ X i` against a family `g` over a finset
containing the support of `X` gives back `g j`. -/
private theorem sum_map_dite_comp (G : C ⥤ D) [G.Additive] {ι : Type*} [DecidableEq ι]
    (X : ι → C) (s : Finset ι) (hs : ∀ i ∉ s, IsZero (X i)) {Z : D} (g : ∀ i, G.obj (X i) ⟶ Z)
    (j : ι) :
    ∑ i ∈ s, G.map (if h : j = i then eqToHom (by rw [h]) else 0) ≫ g i = g j := by
  have := Finset.sum_dite_eq s j (fun i h => G.map (eqToHom (congrArg X h)) ≫ g i)
  simp only [apply_dite G.map, dite_comp, G.map_zero, zero_comp, this]
  split_ifs with hj
  · simp
  · exact (G.map_isZero (hs j hj)).eq_of_src _ _

/-- **An additive functor preserves coproducts with finitely many nonzero terms.** -/
theorem preservesColimit_discrete_of_finite_support (G : C ⥤ D) [G.Additive] {ι : Type*}
    (X : ι → C) (s : Finset ι) (hs : ∀ i ∉ s, IsZero (X i)) :
    PreservesColimit (Discrete.functor X) G := by
  classical
  constructor
  intro c hc
  let p : ∀ i, c.pt ⟶ X i := fun i => hc.desc (Cofan.mk (X i)
    fun j => if h : j = i then eqToHom (by rw [h]) else 0)
  have hp : ∀ i j, c.ι.app ⟨j⟩ ≫ p i = if h : j = i then eqToHom (by rw [h]; rfl) else 0 :=
    fun i j => by rw [hc.fac]; rfl
  have hid : ∑ i ∈ s, p i ≫ c.ι.app ⟨i⟩ = 𝟙 c.pt := by
    refine hc.hom_ext fun ⟨j⟩ => ?_
    rw [comp_sum, comp_id]
    simp_rw [← assoc, hp]
    exact sum_map_dite_comp (𝟭 C) X s hs (fun i => c.ι.app ⟨i⟩) j
  refine ⟨{
    desc t := ∑ i ∈ s, G.map (p i) ≫ t.ι.app ⟨i⟩
    fac t jj := ?_
    uniq t m hm := ?_ }⟩
  · obtain ⟨j⟩ := jj
    change G.map (c.ι.app ⟨j⟩) ≫ _ = _
    rw [comp_sum]
    simp_rw [← assoc, ← G.map_comp, hp]
    exact sum_map_dite_comp G X s hs (fun i => t.ι.app ⟨i⟩) j
  · have : m = G.map (𝟙 c.pt) ≫ m := by rw [G.map_id, id_comp]
    rw [this, ← hid, G.map_sum, sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [G.map_comp, assoc]
    exact congrArg _ (hm ⟨i⟩)

end CategoryTheory.Functor

namespace HomologicalComplex₂

variable {D : Type*} {D' : Type*} [Category D] [Category D']
  [Preadditive D] [Preadditive D']
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  (Φ : D ⥤ D') [Φ.Additive] (K : HomologicalComplex₂ D c₁ c₂)
  [K.HasTotal c₁₂] [(mapBicomplex Φ K).HasTotal c₁₂]

/-- **An additive functor commutes with totalisation of a bicomplex whose antidiagonals have
finite support.** -/
theorem isIso_totalMap_of_finite_support
    (h : ∀ n : I₁₂, ∃ s : Finset ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}),
      ∀ i ∉ s, IsZero ((K.X i.1.1).X i.1.2)) :
    IsIso (totalMap (c₁₂ := c₁₂) Φ K) := by
  have : ∀ n, IsIso ((totalMap (c₁₂ := c₁₂) Φ K).f n) := fun n => by
    obtain ⟨s, hs⟩ := h n
    have := Functor.preservesColimit_discrete_of_finite_support Φ
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c₁₂) n) s hs
    exact isIso_totalMapf_of_preservesColimit (c₁₂ := c₁₂) Φ K n
  exact HomologicalComplex.Hom.isIso_of_components _

end HomologicalComplex₂
