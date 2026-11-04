module

public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData

/-!
# A morphism vanishing at the associated points of its target is zero

Let `X` be a locally Noetherian scheme and `f : A ⟶ F` a morphism of quasi-coherent
`𝒪_X`-modules whose stalk map vanishes at every associated point of `F`. Then `f = 0`: the
projection `F ⟶ coker f` is injective on the stalk at every associated point of `F`, hence a
monomorphism by [Stacks, Tag 0AVL], and `f` composed with it is zero.

The same holds with the target twisted by an invertible module. For `f : A ⟶ F ⊗_{𝒪_X} L` with
`L` invertible, vanishing of the stalk maps at the associated points of `F` — not of `F ⊗ L` —
already forces `f = 0`: tensoring on the right by `L^{⊗ -1}` keeps the stalk maps zero, the
untwisted statement applies to the twisted morphism composed with the cancellation isomorphism
`(F ⊗ L) ⊗ L^{⊗ -1} ≅ F`, and tensoring by an invertible module reflects vanishing.

## Main results

* `AlgebraicGeometry.eq_zero_of_stalkFunctor_map_eq_zero_on_associatedPoints`: the untwisted
  statement.
* `AlgebraicGeometry.eq_zero_of_stalkLinearMap_eq_zero_on_associatedPoints_tensorInvertible`:
  the statement with the target twisted by an invertible module.

## Implementation notes

The associated points of a sheaf of modules are duplicated in this library:
`Stacks.Divisors.associatedPoints`, which carries the attribute for [Stacks, Tag 02OJ] and over
which the embedded-point characterization of [Stacks, Tag 05AL] is stated, and
`Stacks.AlgebraicGeometry.AssociatedPointsMono.associatedPoints`, over which [Stacks, Tag 0AVL]
is stated. The statements here use the former — it is the one the consumers of this file
quantify over — and pass it directly into Tag 0AVL, both predicates being reducible
abbreviations of the same condition on the stalk.

Why the twist rather than a comparison of `Ass(F ⊗ L)` with `Ass(F)`: the two sets are equal,
`L` being locally trivial, but the equality is a local computation on stalks, whereas the twist
reduces the twisted statement to the untwisted one by cancelling an invertible factor, which is
already available.

## References

* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **A morphism vanishing on the stalks at the associated points of its target is zero.** The
projection to the cokernel of `f` is then injective on those stalks, so it is a monomorphism by
[Stacks, Tag 0AVL], and `f` composed with it is zero. -/
theorem eq_zero_of_stalkFunctor_map_eq_zero_on_associatedPoints [IsLocallyNoetherian X]
    {A F : X.Modules} [A.IsQuasicoherent] [F.IsQuasicoherent] (f : A ⟶ F)
    (hf : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      (Scheme.Modules.stalkFunctor X x).map f = 0) : f = 0 := by
  have _ : Mono (cokernel.π f) := by
    refine Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints
      _ fun x ↦ ?_
    by_cases hx : x ∈ Stacks.Divisors.associatedPoints F
    · exact Or.inl ((ModuleCat.mono_iff_injective _).1
        (Scheme.Modules.mono_stalkFunctor_map_cokernel_π f x (hf x hx)))
    · exact Or.inr hx
  exact (cancel_mono (cokernel.π f)).1 (by simp)

/-- **The same with the target twisted by an invertible module.** A morphism with values in
`F ⊗_{𝒪_X} L`, for `L` invertible, whose stalk maps vanish at the associated points of `F` is
zero: tensoring on the right by `L^{⊗ -1}` keeps them zero, so the twisted morphism followed by
the cancellation isomorphism `(F ⊗ L) ⊗ L^{⊗ -1} ≅ F` is zero by the untwisted statement, and
tensoring by an invertible module reflects vanishing. -/
theorem eq_zero_of_stalkLinearMap_eq_zero_on_associatedPoints_tensorInvertible
    [IsLocallyNoetherian X] {A F L : X.Modules} [A.IsQuasicoherent] [F.IsQuasicoherent]
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L]
    (f : A ⟶ Scheme.Modules.tensorObj F L)
    (hf : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      stalkLinearMap A (Scheme.Modules.tensorObj F L) f x = 0) : f = 0 := by
  have _ := Scheme.Modules.isInvertible_tensorInverse L
  have _ : (Scheme.Modules.tensorObj A (Scheme.Modules.tensorInverse L)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorObj _ _ (inferInstanceAs A.IsQuasicoherent)
      (AlgebraicGeometry.isQuasicoherent_of_isInvertible (Scheme.Modules.tensorInverse L))
  have e := Scheme.Modules.tensorInverseCancelIso F L
  have hz : Scheme.Modules.tensorRightMap f (Scheme.Modules.tensorInverse L) ≫ e.hom = 0 := by
    refine eq_zero_of_stalkFunctor_map_eq_zero_on_associatedPoints _ fun x hx ↦ ?_
    have h0 : (Scheme.Modules.stalkFunctor X x).map
        (Scheme.Modules.tensorRightMap f (Scheme.Modules.tensorInverse L)) = 0 :=
      (Scheme.Modules.stalkLinearMap_eq_zero_iff _ x).1
        (stalkLinearMap_tensorRightMap_eq_zero f (Scheme.Modules.tensorInverse L) x (hf x hx))
    exact ((Scheme.Modules.stalkFunctor X x).map_comp _ e.hom).trans (by rw [h0, zero_comp])
  exact Scheme.Modules.eq_zero_of_tensorRightMap_eq_zero (Scheme.Modules.tensorInverse L) f
    ((cancel_mono e.hom).1 (hz.trans zero_comp.symm))

end AlgebraicGeometry

end
