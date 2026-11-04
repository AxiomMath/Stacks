module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.SourceShift
public import StacksFrontier.RingTheory.Dualizing.SocleOfInjectiveHull

/-!
# `RHom_A(κ⟦n⟧, ω_A^•) ≅ κ⟦-n⟧` for a normalized dualizing complex

Let `(A, 𝔪, κ)` be a Noetherian local ring and let `ω_A^•` be a dualizing complex for `A` which
is normalized in the sense of [Stacks, Section 47.16]. Then

`RHom_A(κ, ω_A^•) ≅ κ`,

which is `Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingle`, and therefore also

`RHom_A(κ⟦n⟧, ω_A^•) ≅ κ⟦-n⟧`     for every `n : ℤ`.

The passage from the first to the second is *not* formal: derived Hom carries no commutation
with the shift in its contravariant variable by construction, and the commutation in the
covariant variable does not give it. It is
`Dualizing.dualizingDerivedHomSourceShift` of
`StacksFrontier/RingTheory/Dualizing/DerivedHomDuality/HomShift/SourceShift.lean`.

The case `n = 1` is the first of the two computations the duality step in the proof of
[Stacks, Tag 0AXD] rests on: a nonzero `α : Rf_*ω_X^• ⟶ κ⟦1⟧` is carried by
`RHom_A(-, ω_A^•)` to a nonzero `β : κ⟦-1⟧ ⟶ Rf_*𝒪_X`, which contradicts [Stacks, Tag 0AXC].

## Main results

* `Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingleShift` —
  `RHom_A(κ⟦n⟧, ω_A^•) ≅ κ⟦-n⟧`.
* `Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingleShiftOne` — the case `n = 1`,
  `RHom_A(κ⟦1⟧, ω_A^•) ≅ κ⟦-1⟧`.

## Implementation notes

The derived category of `A`-modules is taken at the standard model, which is the model baked
into the types of `Dualizing.dualizingDerivedHomFunctor` and
`Dualizing.IsNormalizedDualizingComplex`; it is forced here rather than chosen.

Both statements are `Nonempty` of an isomorphism rather than a chosen isomorphism, matching
`Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingle`, whose own proof chooses an
injective hull of the residue field and is therefore only an existence statement.

## References

* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0A7Q](https://stacks.math.columbia.edu/tag/0A7Q)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- **`RHom_A(κ⟦n⟧, ω_A^•) ≅ κ⟦-n⟧` for a normalized dualizing complex.** Let `A` be a
Noetherian local ring with residue field `κ` and let `ω_A^•` be a dualizing complex for `A`
normalized in the sense of [Stacks, Section 47.16]. Then the internal derived Hom from the
`n`-shift of the residue field into `ω_A^•` is the `(-n)`-shift of the residue field.

This is `Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingle`, which computes the
unshifted value, composed with `Dualizing.dualizingDerivedHomSourceShift`, the commutation of
derived Hom with the shift in its contravariant variable. -/
theorem nonempty_iso_dualizingDerivedHom_residueFieldSingleShift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (hω : IsNormalizedDualizingComplex.{u, v} ω) (n : ℤ) :
    Nonempty ((dualizingDerivedHomFunctor A ω).obj
        (Opposite.op ((CategoryTheory.shiftFunctor
          (DerivedCategory (ModuleCat.{max v u} A)) n).obj (residueFieldSingle.{u, v} A))) ≅
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (-n)).obj
        (residueFieldSingle.{u, v} A)) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingDerivedHom_residueFieldSingle.{u, v} ω hω
  exact ⟨dualizingDerivedHomSourceShift.{u, v} A ω n (residueFieldSingle.{u, v} A) ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (-n)).mapIso e⟩

/-- **`RHom_A(κ⟦1⟧, ω_A^•) ≅ κ⟦-1⟧` for a normalized dualizing complex**, the case `n = 1` of
`Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingleShift`.

This is the computation `RHom_A(κ[1], ω_A^•) = RHom_A(κ, ω_A^•)[-1] = κ[-1]` which the duality
step in the proof of [Stacks, Tag 0AXD] performs on the target of the morphism it dualizes. -/
theorem nonempty_iso_dualizingDerivedHom_residueFieldSingleShiftOne
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (hω : IsNormalizedDualizingComplex.{u, v} ω) :
    Nonempty ((dualizingDerivedHomFunctor A ω).obj
        (Opposite.op ((CategoryTheory.shiftFunctor
          (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).obj
            (residueFieldSingle.{u, v} A))) ≅
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (-1 : ℤ)).obj
        (residueFieldSingle.{u, v} A)) :=
  nonempty_iso_dualizingDerivedHom_residueFieldSingleShift.{u, v} ω hω 1

end Dualizing

end
