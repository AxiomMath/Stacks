module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Smooth.FieldExtensionCompleteIntersectionColimit

/-!
# A field extension essentially of finite type is a localization of a global complete intersection

Let `F ⊆ B` be a field extension which is essentially of finite type, i.e. finitely generated as a
field extension. Then there is an `F`-subalgebra `C ⊆ B` which is a global complete intersection
over `F` and of which `B` is a localization; and this presentation of `B` as a localization is
preserved by base change along any `F`-algebra `R`, so that `R ⊗[F] B` is a localization of
`R ⊗[F] C`.

## Main results

* `Stacks.EssFiniteType.exists_isGlobalCompleteIntersectionOver_isLocalization`: the subalgebra
  `C`, with `B` the localization of `C` at the multiplicative set of elements of `C` that are
  invertible in `B`.
* `Stacks.EssFiniteType.isLocalization_tensorProduct`: base change of a localization,
  `R ⊗[F] B` is the localization of `R ⊗[F] C` at the image of the multiplicative set.
* `Stacks.EssFiniteType.exists_isGlobalCompleteIntersectionOver_isLocalization_tensorProduct`:
  the two combined.

## Implementation notes

"Finitely generated as a field extension" is `Algebra.EssFiniteType F B`, which by
`IntermediateField.fg_top_iff` says `B = F(x_1, …, x_n)` for finitely many `x_i ∈ B`.

The subalgebra `C` is produced by applying
`Subalgebra.exists_finset_subset_isGlobalCompleteIntersectionOver` to the finite set
`Algebra.EssFiniteType.finset F B` of essential generators: that gives a global complete
intersection `C` containing those generators, hence containing the finite-type subalgebra
`Algebra.EssFiniteType.subalgebra F B` of which `B` is already a localization. Enlarging the
subalgebra keeps `B` a localization, which is the private lemma
`Stacks.EssFiniteType.isLocalization_comap_isUnit_of_le`: the surjectivity half of the universal
property is inherited from the smaller subalgebra, and the two other halves hold for any
subalgebra of `B`, the inverted set being by construction a set of units of `B` and the inclusion
of a subalgebra being injective.

The multiplicative set is `(IsUnit.submonoid B).comap (algebraMap C B)`, the elements of `C` which
become invertible in `B`; this is Mathlib's choice in `Algebra.EssFiniteType.submonoid` and the
only possible one, since the localization of `C` at anything larger is the zero ring and at
anything smaller may be too small.

For the base change the `(R ⊗[F] C)`-algebra structure on `R ⊗[F] B` is not an instance — it is
`Algebra.TensorProduct.map (AlgHom.id F R) (IsScalarTower.toAlgHom F C B)` — so
`isLocalization_tensorProduct` takes the structure as an instance argument together with the
hypothesis `H` pinning its structure map to that algebra homomorphism, in the style of
`Algebra.IsPushout.tensorProduct_tensorProduct`; a caller who builds the structure by
`AlgHom.toAlgebra` discharges `H` by `rfl`. The combined statement existentially quantifies over
the structure instead, as is enough for a property of the ring `R ⊗[F] B` such as being Gorenstein.

The mechanism of the base change is that `Algebra.isLocalization_iff_isPushout` turns the assertion
into the pushout square `C → B`, `R ⊗[F] C → R ⊗[F] B`, which is the right-hand square of
```
  F  →  C  →  B
  ↓     ↓     ↓
  R  → R⊗C → R⊗B
```
whose left-hand square and whose outer rectangle are both the defining pushout squares of a tensor
product; so `Algebra.IsPushout.comp_iff` applies.

## References

* [StacksProject 0BJN](https://stacks.math.columbia.edu/tag/0BJN)
* [StacksProject 07BV](https://stacks.math.columbia.edu/tag/07BV)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EssFiniteType

/-- **Enlarging a subalgebra keeps the ambient ring a localization of it.** If `S` is the
localization of a subalgebra `A₀` at the elements of `A₀` invertible in `S`, and `A₀ ≤ A` is a
larger subalgebra, then `S` is the localization of `A` at the elements of `A` invertible in `S`.

Only the solvability of `z · a = a'` with `a, a' ∈ A` and `a` invertible in `S` has to be
transported, and it is inherited from `A₀`; that the inverted elements become units is true by
construction, and injectivity of `A → S` makes the third condition vacuous. -/
private theorem isLocalization_comap_isUnit_of_le {F S : Type*} [CommRing F] [CommRing S]
    [Algebra F S] {A₀ A : Subalgebra F S} (hle : A₀ ≤ A)
    (h : IsLocalization ((IsUnit.submonoid S).comap (algebraMap A₀ S)) S) :
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap A S)) S := by
  rw [isLocalization_iff] at h ⊢
  refine ⟨fun y => y.2, fun z => ?_, fun {x y} hxy => ⟨1, by rw [Subtype.ext hxy]⟩⟩
  obtain ⟨⟨x, y⟩, e⟩ := h.2.1 z
  exact ⟨⟨⟨x.1, hle x.2⟩, ⟨⟨y.1.1, hle y.1.2⟩, y.2⟩⟩, e⟩

/-- **A field extension essentially of finite type is a localization of a global complete
intersection subalgebra.** Let `B/F` be an extension of fields which is finitely generated as a
field extension. Then there is an `F`-subalgebra `C ⊆ B` which is a global complete intersection
over `F` and such that `B` is the localization of `C` at the multiplicative set of elements of `C`
that are invertible in `B`.

The subalgebra is obtained from Tag 07BV applied to a finite set of essential generators of `B`
over `F`: it is a global complete intersection containing a finite-type subalgebra of which `B` is
already a localization. -/
theorem exists_isGlobalCompleteIntersectionOver_isLocalization (F B : Type*) [Field F] [Field B]
    [Algebra F B] [Algebra.EssFiniteType F B] :
    ∃ C : Subalgebra F B, IsGlobalCompleteIntersectionOver F C ∧
      IsLocalization ((IsUnit.submonoid B).comap (algebraMap C B)) B := by
  obtain ⟨C, hsC, hC⟩ := Subalgebra.exists_finset_subset_isGlobalCompleteIntersectionOver
    (k := F) (K := B) (Algebra.EssFiniteType.finset F B)
  exact ⟨C, hC, isLocalization_comap_isUnit_of_le (Algebra.adjoin_le hsC)
    (Algebra.EssFiniteType.isLocalization F B)⟩

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (F R C B : Type*) [CommRing F] [CommRing R] [CommRing C] [CommRing B] [Algebra F R]
  [Algebra F C] [Algebra F B] [Algebra C B] [IsScalarTower F C B]

/-- The `(R ⊗[F] C)`-algebra structure on `R ⊗[F] B` induced by a `C`-algebra `B`, namely
`Algebra.TensorProduct.map (AlgHom.id F R) (IsScalarTower.toAlgHom F C B)`. This is not an
instance: it would compete with the two tensor factors for the `Algebra (R ⊗[F] C) _` slot. -/
noncomputable abbrev baseChangeAlgebra : Algebra (R ⊗[F] C) (R ⊗[F] B) :=
  (Algebra.TensorProduct.map (AlgHom.id F R) (IsScalarTower.toAlgHom F C B)).toAlgebra

/-- **A localization stays a localization after base change.** Let `B` be the localization of an
`F`-algebra `C` at a multiplicative set `M ⊆ C`, and let `R` be any `F`-algebra. Then `R ⊗[F] B`
is the localization of `R ⊗[F] C` at the image of `M`, for the `(R ⊗[F] C)`-algebra structure on
`R ⊗[F] B` induced by `C → B`.

The structure is an instance argument pinned by `H`; `baseChangeAlgebra` is the intended value,
for which `H` is `rfl`. -/
theorem isLocalization_tensorProduct (M : Submonoid C) [IsLocalization M B]
    [Algebra (R ⊗[F] C) (R ⊗[F] B)]
    (H : algebraMap (R ⊗[F] C) (R ⊗[F] B) =
      (Algebra.TensorProduct.map (AlgHom.id F R) (IsScalarTower.toAlgHom F C B)).toRingHom) :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[F] C) M) (R ⊗[F] B) := by
  let : Algebra C (R ⊗[F] B) := ((algebraMap B (R ⊗[F] B)).comp (algebraMap C B)).toAlgebra
  have : IsScalarTower C B (R ⊗[F] B) := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C (R ⊗[F] C) (R ⊗[F] B) := .of_algebraMap_eq fun c => by
    rw [H]; simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower F (R ⊗[F] C) (R ⊗[F] B) := .of_algebraMap_eq fun a => by
    rw [H]; simp [Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower R (R ⊗[F] C) (R ⊗[F] B) := .of_algebraMap_eq fun r => by
    rw [H]; simp [Algebra.TensorProduct.algebraMap_apply]
  rw [Algebra.isLocalization_iff_isPushout M B]
  exact ((Algebra.IsPushout.comp_iff F C R (S' := R ⊗[F] C) (T' := R ⊗[F] B)).mp
    inferInstance).symm

end BaseChange

section Combined

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Clause (A) of Tag 0BJN, the localization input.** Let `B/F` be an extension of fields which
is finitely generated as a field extension and let `R` be any `F`-algebra. Then there is an
`F`-subalgebra `C ⊆ B` which is a global complete intersection over `F`, and a multiplicative set
`M ⊆ C`, such that `B` is the localization of `C` at `M` and `R ⊗[F] B` is the localization of
`R ⊗[F] C` at the image of `M`.

The `(R ⊗[F] C)`-algebra structure on `R ⊗[F] B` is existentially quantified; it is the one
induced by `C → B`, see `Stacks.EssFiniteType.baseChangeAlgebra`. -/
theorem exists_isGlobalCompleteIntersectionOver_isLocalization_tensorProduct (F B : Type*)
    [Field F] [Field B] [Algebra F B] [Algebra.EssFiniteType F B] (R : Type*) [CommRing R]
    [Algebra F R] :
    ∃ (C : Subalgebra F B) (M : Submonoid C) (_ : Algebra (R ⊗[F] C) (R ⊗[F] B)),
      IsGlobalCompleteIntersectionOver F C ∧ IsLocalization M B ∧
        IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[F] C) M) (R ⊗[F] B) := by
  obtain ⟨C, hC, hloc⟩ := exists_isGlobalCompleteIntersectionOver_isLocalization F B
  let inst : Algebra (R ⊗[F] C) (R ⊗[F] B) := baseChangeAlgebra F R C B
  refine ⟨C, _, inst, hC, hloc, ?_⟩
  exact isLocalization_tensorProduct F R C B _ rfl

end Combined

end Stacks.EssFiniteType

end

