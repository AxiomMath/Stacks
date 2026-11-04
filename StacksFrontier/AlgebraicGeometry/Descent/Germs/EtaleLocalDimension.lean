module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Étale morphisms preserve the local dimension

An étale morphism of schemes does not change the topological Krull dimension at a point: the
dimension of the source at a point equals the dimension of the target at its image.

## Main results

* `Topology.topologicalKrullDim_le_of_continuous_of_specializes_injective`: a continuous map out
  of a sober space which is injective on specialisations does not increase the Krull dimension.
* `Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_specializes_injective`: a continuous open
  map between sober Kolmogorov spaces which is injective on specialisations and lifts
  generalisations preserves the local Krull dimension. This is the purely topological content of
  Tag 04N4.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_of_etale` states that the local dimensions of the
  source and the target of an étale morphism agree at corresponding points.

## Implementation notes

The dimension at a point is `topologicalKrullDimAt`, an infimum over open neighbourhoods, so
each inequality is proved by exhibiting a comparison of neighbourhoods. For `≤` the
neighbourhood is pulled back and the comparison uses injectivity on specialisations; for `≥` the
neighbourhood is pushed forward, using openness and the lifting of generalisations. These four
hypotheses are the only input, so the argument is carried out once, in
`Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_specializes_injective`, and Tag 04N4 supplies
them for an étale morphism: injectivity on specialisations comes from the discreteness of its
fibres, and the lifting of generalisations from flatness.

## References

* [Stacks Project, Tag 04N4](https://stacks.math.columbia.edu/tag/04N4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Topology

/-- If `f` is injective on specialisations, then a strict specialisation in the source gives a
strict inclusion of the singleton closures of the images. -/
lemma closureSingleton_lt_of_specializes_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f)
    (hinj : ∀ ⦃x y⦄, x ⤳ y → f x = f y → x = y) {x y : X}
    (hxy : x ⤳ y) (hne : x ≠ y) :
    IrreducibleCloseds.closureSingleton (f y) <
      IrreducibleCloseds.closureSingleton (f x) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe]
    exact closure_minimal (Set.singleton_subset_iff.mpr (hxy.map hf).mem_closure)
      isClosed_closure
  · intro heq
    have hcl : closure ({f x} : Set Y) = closure {f y} :=
      (congrArg IrreducibleCloseds.carrier heq).symm
    have hfx : f y ⤳ f x := by
      rw [specializes_iff_mem_closure, ← hcl]
      exact subset_closure rfl
    exact hne (hinj hxy ((hxy.map hf).antisymm hfx).eq)

/-- A continuous map from a sober space into a Kolmogorov space which is injective on
specialisations does not increase the Krull dimension. -/
lemma topologicalKrullDim_le_of_continuous_of_specializes_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [T0Space Y]
    (f : X → Y) (hf : Continuous f)
    (hinj : ∀ ⦃x y⦄, x ⤳ y → f x = f y → x = y) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  unfold topologicalKrullDim
  simp only [Order.krullDim]
  refine iSup_le fun p => ?_
  let x : Fin (p.length + 1) → X :=
    fun i => (p.toFun i).isIrreducible'.genericPoint
  have hx : ∀ i, IsGenericPoint (x i) (p.toFun i).carrier := fun i =>
    (p.toFun i).isIrreducible'.isGenericPoint_genericPoint (p.toFun i).isClosed'
  refine le_iSup (fun q : LTSeries (IrreducibleCloseds Y) =>
    (q.length : WithBot ℕ∞)) ⟨p.length,
      fun i => IrreducibleCloseds.closureSingleton (f (x i)), ?_⟩
  intro i
  have hxne : x i.succ ≠ x i.castSucc := by
    intro h
    have h₁ := hx i.succ
    have h₂ := hx i.castSucc
    rw [IsGenericPoint] at h₁ h₂
    have hcarrier : (p.toFun i.succ).carrier = (p.toFun i.castSucc).carrier := by
      rw [← h₁, ← h₂, h]
    exact (ne_of_gt (p.step i)) (IrreducibleCloseds.ext hcarrier)
  exact closureSingleton_lt_of_specializes_injective f hf hinj
    (Topology.specializes_succ_castSucc_of_isGenericPoint p x hx i) hxne

/-- A continuous open map between sober Kolmogorov spaces which is injective on specialisations
and lifts generalisations preserves the local Krull dimension. This is the purely topological
content of Stacks Tag 04N4. -/
theorem topologicalKrullDimAt_eq_of_isOpenMap_of_specializes_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] [T0Space X] [T0Space Y]
    (f : X → Y) (hcont : Continuous f) (hopen : IsOpenMap f)
    (hinj : ∀ ⦃x y⦄, x ⤳ y → f x = f y → x = y) (hgen : GeneralizingMap f) (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (f x) := by
  change (⨅ A : {A : Set X // x ∈ A ∧ IsOpen A}, topologicalKrullDim (↥A.1)) =
    ⨅ B : {B : Set Y // f x ∈ B ∧ IsOpen B}, topologicalKrullDim (↥B.1)
  apply le_antisymm
  · refine le_iInf fun B => ?_
    let A : {A : Set X // x ∈ A ∧ IsOpen A} :=
      ⟨f ⁻¹' B.1, by simpa using B.2.1, B.2.2.preimage hcont⟩
    let g : (↥A.1) → (↥B.1) := Subtype.map f fun z hz => hz
    have : QuasiSober ↥A.1 := A.2.2.isOpenEmbedding_subtypeVal.quasiSober
    exact (iInf_le _ A).trans <|
      topologicalKrullDim_le_of_continuous_of_specializes_injective g
        (hcont.subtype_map _) (by
          intro z w hzw hEq
          exact Subtype.ext (hinj ((subtype_specializes_iff z w).mp hzw)
            (congrArg Subtype.val hEq)))
  · refine le_iInf fun A => ?_
    have himage : IsOpen (f '' A.1) := hopen _ A.2.2
    let B : {B : Set Y // f x ∈ B ∧ IsOpen B} := ⟨f '' A.1, ⟨x, A.2.1, rfl⟩, himage⟩
    let g : (↥A.1) → (↥B.1) := Subtype.map f fun z hz => ⟨z, hz, rfl⟩
    have : QuasiSober ↥B.1 := himage.isOpenEmbedding_subtypeVal.quasiSober
    have hsurj : Function.Surjective g := by
      rintro ⟨y, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    have hgen' : GeneralizingMap g := by
      intro z w hzw
      rw [subtype_specializes_iff] at hzw
      obtain ⟨z', hspec, hfz⟩ := hgen hzw
      exact ⟨⟨z', A.2.2.stableUnderGeneralization hspec z.2⟩,
        (subtype_specializes_iff _ _).2 hspec, Subtype.ext hfz⟩
    exact (iInf_le _ B).trans <|
      topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap g
        (hcont.subtype_map _) hsurj (Or.inr hgen')

end Topology

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04N4.** An étale morphism preserves the local Krull dimension at
corresponding points. -/
@[stacks 04N4]
theorem topologicalKrullDimAt_eq_of_etale
    {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    topologicalKrullDimAt U u = topologicalKrullDimAt V (f u) := by
  have hdiscrete (v : V) : _root_.IsDiscrete (f ⁻¹' {v}) := by
    have hqf := locallyQuasiFinite_of_etale f
    have : LocallyOfFiniteType f := hqf.1
    have : LocallyQuasiFinite f := hqf.2
    exact f.isDiscrete_preimage_singleton v
  have hinj : ∀ ⦃x y : U⦄, x ⤳ y → f x = f y → x = y := by
    intro x y hxy hEq
    exact (hdiscrete (f x)).eq_of_specializes hxy (by simp) (by simp [hEq])
  exact Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_specializes_injective (f : U → V)
    f.continuous f.isOpenMap hinj (Flat.generalizingMap f) u

end AlgebraicGeometry
