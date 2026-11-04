module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.LocalMultiplicity

/-!
# The multiplicity of the diagonal pair over a field, at the local rings

Let `k` be a field, `X` a scheme over `k` and `V`, `W` the closed subschemes of `X` cut out by
two quasi-coherent sheaves of ideals `I`, `J`. At a point `x` of `X` the local ring
`B = 𝒪_{X ×_k X, Δ(x)}` is a localization of `A ⊗_R A`, for `A = 𝒪_{X, x}` and
`R = 𝒪_{Spec k, f(x)}`, carrying a retraction of the multiplication map
(`Stacks.Intersection.Diagonal.stalk_sup_comap_diagonal_eq`), and `R` is a field, because the
spectrum of a field has a single point and its local ring there is the field itself. The
algebraic reduction to the diagonal
(`Stacks.Intersection.Diagonal.localIntersectionMultiplicity_sup_map_eq`) therefore applies with
`R` as the ground field, and gives the equality of Tor-formula intersection multiplicities

`e(X ×_k X, Δ · V ×_k W, Δ(x)) = e(X, V · W, x)`

at every point `x`, with no hypothesis on `X` or on the two ideal sheaves.

## Main results

* `Stacks.Intersection.Diagonal.isField_stalk_spec` — the local ring of the spectrum of a field
  is a field.
* `Stacks.Intersection.Diagonal.localIntersectionMultiplicity_stalk_comap_diagonal_eq` —
  **the equality of multiplicities at a point**: the multiplicity of the pair `Δ`, `V ×_k W` at
  `Δ(x)` on `X ×_k X` equals the multiplicity of the pair `V`, `W` at `x` on `X`.

## Implementation notes

The ground field used is the local ring `R = 𝒪_{Spec k, f(x)}` and not `k` itself: the
presentation of `B` as a localization of a tensor square emitted by
`Stacks.Intersection.Diagonal.diagonal_stalk_isLocalization` is over `R`, so taking `R` as the
ground field makes the two statements line up with no transport of tensor products. All that is
needed of `k` is that `R` is a field, which is `isField_stalk_spec`: the local ring of `Spec k`
at its unique point is the localization of `k` at the complement of a prime, every element of
which is a unit.

## References

* [Stacks Project, Lemma 43.19.2 (Tag 0B0U)](https://stacks.math.columbia.edu/tag/0B0U)
* [Stacks Project, Lemma 43.19.1 (Tag 0B0T)](https://stacks.math.columbia.edu/tag/0B0T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Intersection.Diagonal

/-- **The local ring of the spectrum of a field is a field.** The spectrum of a field `k` has a
single point, whose local ring is the localization of `k` at the complement of the zero ideal;
every element of that multiplicative set is a unit, so the localization map is bijective. -/
theorem isField_stalk_spec (k : Type u) [Field k] (z : Spec (CommRingCat.of k)) :
    IsField ((Spec (CommRingCat.of k)).presheaf.stalk z) := by
  have he : closure ({z} : Set (Spec (CommRingCat.of k))) = Set.univ :=
    Set.eq_univ_of_forall fun c =>
      (Subsingleton.elim (α := PrimeSpectrum (CommRingCat.of k)) z c) ▸
        subset_closure (Set.mem_singleton z)
  refine isField_stalk_of_closure_mem_irreducibleComponents (Spec (CommRingCat.of k)) z
    ⟨isIrreducible_singleton.closure, fun t _ _ => ?_⟩
  rw [he]
  exact Set.subset_univ t

/-- **The equality of multiplicities of the reduction to the diagonal, at a point.** Let `k` be a
field, `f : X ⟶ Spec k` a scheme over `k`, and `I`, `J` two quasi-coherent sheaves of ideals on
`X`, cutting out closed subschemes `V`, `W`. At every point `x` of `X` the Tor-formula
intersection multiplicity of the diagonal `Δ` and the product `V ×_k W` at the point `Δ(x)` of
`X ×_k X` equals the Tor-formula intersection multiplicity of `V` and `W` at `x`:

`e(X ×_k X, Δ · V ×_k W, Δ(x)) = e(X, V · W, x)`.

The diagonal is read through the kernel of its local ring map at `x`, and `V ×_k W` through the
stalk at `Δ(x)` of the ideal sheaf `pr₁^* I ⊔ pr₂^* J` that cuts it out. No hypothesis on `X` or
on the ideal sheaves is used; this is the local heart of part (2) of [Stacks, Tag 0B0U]. -/
theorem localIntersectionMultiplicity_stalk_comap_diagonal_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (I J : X.IdealSheafData) (x : X) :
    (RingHom.ker ((pullback.diagonal f).stalkMap x).hom).localIntersectionMultiplicity
        ((pullback f f : Scheme.{u}).presheaf.stalk (pullback.diagonal f x) ⧸
          AlgebraicGeometry.IdealSheafData.stalk
            (I.comap (pullback.fst f f) ⊔ J.comap (pullback.snd f f))
            (pullback.diagonal f x)) =
      (AlgebraicGeometry.IdealSheafData.stalk I x).localIntersectionMultiplicity
        (X.presheaf.stalk x ⧸ AlgebraicGeometry.IdealSheafData.stalk J x) := by
  let := (f.stalkMap x).hom.toAlgebra
  let : Field ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)) :=
    (isField_stalk_spec k (f.base x)).toField
  obtain ⟨φ, hleft, hright, hd, M, hM⟩ := diagonal_stalk_isLocalization f x
  rw [stalk_sup_comap_diagonal_eq f I J x, ←
    hleft.trans (CommRingCat.hom_comp _ _), ← hright.trans (CommRingCat.hom_comp _ _)]
  exact localIntersectionMultiplicity_sup_map_eq φ M hM
    ((pullback.diagonal f).stalkMap x).hom hd.symm _ _

end Stacks.Intersection.Diagonal

end
