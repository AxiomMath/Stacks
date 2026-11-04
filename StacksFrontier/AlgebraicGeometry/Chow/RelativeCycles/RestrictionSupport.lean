module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a restricted family of cycles

Restricting a family of cycles to open subschemes `U ⊆ X` and `V ⊆ S` intersects its support
with `U`: viewed inside `X`, the support of the restricted family is `U ∩ Supp(α)`.

## Main results

* `Stacks.Chow.image_supportOfFamily_restrictedFamily` — the support of the restricted family,
  mapped into `X`, is the intersection of the support of `α` with the image of `U`.

## Implementation notes

An open subscheme is represented by an open immersion `j : U ⟶ X`, so the intersection
`U ∩ Supp(α)` is written `Set.range j ∩ Supp(α)`. Local finiteness of type for `U ⟶ V` is
deduced from the square rather than assumed.

## References

* [Stacks Project, Tag 0H4V](https://stacks.math.columbia.edu/tag/0H4V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The topological support of a function composed with an open continuous map is the inverse
image of its topological support. -/
private theorem tsupport_comp_openMap {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (g : A → B) (hg : IsOpenMap g) (hc : Continuous g)
    (c : B → ℤ) : tsupport (c ∘ g) = g ⁻¹' tsupport c := by
  change closure (g ⁻¹' {y | c y ≠ 0}) = g ⁻¹' closure {y | c y ≠ 0}
  exact (hg.preimage_closure_eq_closure_preimage hc _).symm

/-- The support of a restricted family of cycles, mapped back into the original total space, is
the intersection of the original support with the open subscheme. -/
@[stacks 0H4V "support_restriction"]
theorem image_supportOfFamily_restrictedFamily
    {X S U V : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ V)
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (r : ℕ) (α : FamilyOfCycles f r) :
    letI : LocallyOfFiniteType fU := by
      let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
      exact locallyOfFiniteType_of_comp fU i
    j '' (supportOfFamily fU (restrictedFamily f fU j i h r α).1) =
      Set.range j ∩ supportOfFamily f α := by
  let : LocallyOfFiniteType fU := by
    let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
    exact locallyOfFiniteType_of_comp fU i
  let β := (restrictedFamily f fU j i h r α).1
  have hcoeff (t : V) (y : fU.fiber t) :
      (β t : AlgebraicCycle (fU.fiber t) ℤ) y =
        (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ)
          (restrictedFiberMap f fU j i h t y) :=
    (restrictedFamily f fU j i h r α).2 t y
  have htsupport (t : V) :
      tsupport (β t : AlgebraicCycle (fU.fiber t) ℤ) =
        (restrictedFiberMap f fU j i h t) ⁻¹'
          tsupport (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ) := by
    let m := restrictedFiberMap f fU j i h t
    have : IsOpenImmersion m := restrictedFiberMap_isOpenImmersion f fU j i h t
    have hm : (β t : AlgebraicCycle (fU.fiber t) ℤ) =
        (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ) ∘ m :=
      funext (hcoeff t)
    rw [hm]
    exact tsupport_comp_openMap m (m.isOpenEmbedding.isOpenMap) m.continuous _
  change j '' supportOfFamily fU β = Set.range j ∩ supportOfFamily f α
  ext x
  simp only [Set.mem_image, mem_supportOfFamily, Set.mem_range, Set.mem_inter_iff]
  constructor
  · rintro ⟨u, ⟨t, y, hy, hyu⟩, hux⟩
    refine ⟨⟨u, hux⟩, ⟨i t, restrictedFiberMap f fU j i h t y, ?_, ?_⟩⟩
    · rwa [htsupport t] at hy
    · have hmap := congrArg (fun q : fU.fiber t ⟶ X => q y) (restrictedFiberMap_fiberι
        f fU j i h t)
      change f.fiberι (i t) (restrictedFiberMap f fU j i h t y) = j (fU.fiberι t y) at hmap
      exact hmap.trans ((congrArg j hyu).trans hux)
  · rintro ⟨⟨u, hux⟩, ⟨s, z, hz, hzx⟩⟩
    let t : V := fU u
    have hs : s = i t := by
      calc
        s = f (f.fiberι s z) := by
          symm
          change f.fiberι s z ∈ f ⁻¹' {s}
          rw [← f.range_fiberι]
          exact ⟨z, rfl⟩
        _ = f x := congrArg f hzx
        _ = f (j u) := congrArg f hux.symm
        _ = i t := by simpa [t] using congrArg (fun q : U ⟶ S => q u) h
    subst s
    refine ⟨u, ⟨t, fU.asFiber u, ?_, ?_⟩, hux⟩
    · rw [htsupport t]
      change restrictedFiberMap f fU j i h t (fU.asFiber u) ∈
        tsupport (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ)
      have hz' : restrictedFiberMap f fU j i h t (fU.asFiber u) = z := by
        apply (f.fiberι (i t)).isEmbedding.injective
        calc
          f.fiberι (i t) (restrictedFiberMap f fU j i h t (fU.asFiber u)) =
              j (fU.fiberι t (fU.asFiber u)) :=
            congrArg (fun q : fU.fiber t ⟶ X => q (fU.asFiber u))
              (restrictedFiberMap_fiberι f fU j i h t)
          _ = j u := by rw [Scheme.Hom.fiberι_asFiber]
          _ = f.fiberι (i t) z := hux.trans hzx.symm
      rwa [hz']
    · rw [Scheme.Hom.fiberι_asFiber]

end Stacks.Chow
