module

public import StacksCore.FieldTheory.AlgebraicClosure

/-!
# Relative algebraic closedness along a square of ring isomorphisms

Being algebraically closed in an extension is a property of the algebra map, so it transports
along any pair of ring isomorphisms `k ≃+* k'` and `K ≃+* K'` intertwining the two algebra maps.
No common base field is required, and in particular the two isomorphisms are not assumed to be
algebra maps for any third field.

## Main results

* `IsAlgClosedIn.of_ringEquiv_square`: relative algebraic closedness transports along a
  commutative square of ring isomorphisms and algebra maps.

## References

* [Stacks Project, Tag 037I](https://stacks.math.columbia.edu/tag/037I)
-/

@[expose] public section

universe u

/-- Relative algebraic closedness transports along a commutative square whose horizontal maps are
ring isomorphisms and whose vertical maps are the two algebra maps. -/
theorem IsAlgClosedIn.of_ringEquiv_square {k K k' K' : Type u} [Field k] [Field K] [Field k']
    [Field K'] [Algebra k K] [Algebra k' K'] (eBase : k ≃+* k') (eTop : K ≃+* K')
    (hcompat : ∀ a, eTop (algebraMap k K a) = algebraMap k' K' (eBase a))
    (h : IsAlgClosedIn k K) : IsAlgClosedIn k' K' := by
  let : Algebra k K' := ((algebraMap k' K').comp eBase.toRingHom).toAlgebra
  let eTopAlg : K ≃ₐ[k] K' := { eTop with commutes' := hcompat }
  have hcustom : IsAlgClosedIn k K' := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hy : eTopAlg.symm x ∈ (⊥ : IntermediateField k K) :=
      h ▸ mem_algebraicClosure_iff.2 ((isAlgebraic_algHom_iff eTopAlg.toAlgHom
        eTopAlg.injective).mp (by simpa using mem_algebraicClosure_iff.1 hx))
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hy
    exact ⟨a, by simpa using congrArg eTopAlg ha⟩
  refine eq_bot_iff.2 fun x hx => ?_
  have hcomp : (algebraMap k K').comp eBase.symm.toRingHom =
      (RingHom.id K').comp (algebraMap k' K') := by
    ext a
    exact congrArg (algebraMap k' K') (eBase.apply_symm_apply a)
  have hx : x ∈ (⊥ : IntermediateField k K') :=
    hcustom ▸ mem_algebraicClosure_iff.2 ((isAlgebraic_ringHom_iff_of_comp_eq (f := eBase.symm)
      (g := RingHom.id K') (RingHom.injective _) hcomp).2 (mem_algebraicClosure_iff.1 hx))
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hx
  exact ⟨eBase a, ha⟩

end
