module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Sequence

/-!
# Bases for the sectionwise exterior powers of a finite free presheaf of modules

`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Sequence` builds `PresheafOfModules.finFree O r`, the
free presheaf of modules of rank `r` over a presheaf of commutative rings `O`, whose sections over
`X` are the `r`-tuples of sections of `O`. Its sectionwise exterior power of degree `n` is the
degree-`n` piece of the Koszul complex `K_•(O, f₁, …, f_r)` of Stacks tag 062L.

This file equips those exterior powers with a basis which is **natural in `X`**: the index type is
the set of `n`-element subsets of `Fin r`, which does not depend on the object, and the restriction
maps carry each basis vector to the basis vector with the same index. So the degree-`n` piece of
the Koszul complex is free of rank `C(r, n)` over the structure presheaf, uniformly in `X`.

## Main definitions

* `PresheafOfModules.finFreeSingle`: the `k`-th standard basis section of `finFree O r`.
* `PresheafOfModules.finFreeBasis`: the standard basis of the sections of `finFree O r`.
* `PresheafOfModules.finFreeWedge`: the exterior product of standard basis sections indexed by a
  tuple `i : Fin n → Fin r`, as a section of the degree-`n` sectionwise exterior power.
* `PresheafOfModules.exteriorFinFreeBasis`: **the basis of the sections of the degree-`n`
  sectionwise exterior power of `finFree O r`**, indexed by the `n`-element subsets of `Fin r`.

## Main results

* `Module.Basis.repr_map_of_map_basis`: a semilinear map which takes a basis to a basis transports
  coordinates by the ring homomorphism.
* `PresheafOfModules.map_finFreeWedge` and `PresheafOfModules.map_exteriorFinFreeBasis`:
  restriction fixes the exterior products of standard basis sections, hence the basis vectors.

## Implementation notes

**Everything is spelled with `(O ⋙ forget₂ CommRingCat RingCat).obj X` as the ring of sections.**
A presheaf of modules is indexed by a presheaf of rings, so that is the spelling in which the
module instance on the sections of `finFree O r` and on the sections of its exterior powers is
found. Writing `O.obj X` instead names the same ring, but its `Semiring` instance is reached
through `CommRingCat` rather than through `RingCat`, and a definitional unfolding that compares the
two exhausts the elaborator's budget on these types; so a statement mixing the two spellings is
written only where the consumer forces it.

**The standard basis section is given a name of its own.** The sections of `finFree O r` over `X`
are the functions `Fin r → O(X)` definitionally, so `Pi.single k 1` is such a section; but the
module instances Lean finds at the two spellings of that type are different terms, and an exterior
power formed at the wrong one is not the one the sectionwise exterior algebra talks about.
`finFreeSingle` fixes the spelling once, and every statement below is phrased through it.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
-/

@[expose] public section

open CategoryTheory Opposite

open scoped ExteriorAlgebra

universe u v w

/-- **A semilinear map matching two bases transports coordinates along its ring homomorphism.**
If `u` is `ρ`-semilinear and carries the `i`-th vector of a basis `b` of the source to the `i`-th
vector of a basis `b'` of the target, then the `i`-th coordinate of `u m` is the image under `ρ`
of the `i`-th coordinate of `m`. -/
theorem Module.Basis.repr_map_of_map_basis {ι : Type*} [Finite ι] {R S M N : Type*}
    [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (b : Module.Basis ι R M) (b' : Module.Basis ι S N) {ρ : R →+* S} (u : M →ₛₗ[ρ] N)
    (hu : ∀ i, u (b i) = b' i) (m : M) (i : ι) :
    b'.repr (u m) i = ρ (b.repr m i) := by
  have := Fintype.ofFinite ι
  conv_lhs => rw [← b.sum_repr m]
  rw [map_sum]
  have h : ∀ j, u (b.repr m j • b j) = ρ (b.repr m j) • b' j := fun j => by
    rw [map_smulₛₗ, hu]
  rw [Finset.sum_congr rfl fun j _ => h j, b'.repr_sum_self]

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- A local section of a sectionwise exterior power restricts by semilinear base change of the
exterior algebra of the sections. -/
theorem exteriorAlgebraPieceVal_map (n : ℤ)
    (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)) {A B : Cᵒᵖ} (g : A ⟶ B)
    (x : (exteriorAlgebraPiece n F).obj A) :
    exteriorAlgebraPieceVal n F B ((exteriorAlgebraPiece n F).map g x) =
      ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ CommRingCat RingCat).map g).hom (F.restrictₛₗ g)
        (exteriorAlgebraPieceVal n F A x) := rfl

/-- **The `k`-th standard basis section of the free presheaf of modules of rank `r`**: the tuple
whose `k`-th entry is `1` and whose other entries vanish. -/
noncomputable def finFreeSingle (r : ℕ) (A : Cᵒᵖ) (k : Fin r) : (finFree O r).obj A :=
  Pi.single k 1

/-- The `l`-th entry of the `k`-th standard basis section is `1` if `l = k` and `0` otherwise. -/
theorem finFreeSingle_apply (r : ℕ) (A : Cᵒᵖ) (k l : Fin r) :
    finFreeSingle O r A k l =
      if l = k then (1 : (O ⋙ forget₂ CommRingCat RingCat).obj A) else 0 :=
  Pi.single_apply k 1 l

/-- **Restriction fixes the standard basis sections.** -/
@[simp]
theorem map_finFreeSingle (r : ℕ) {A B : Cᵒᵖ} (g : A ⟶ B) (k : Fin r) :
    (finFree O r).map g (finFreeSingle O r A k) = finFreeSingle O r B k := by
  funext l
  rw [finFree_map_apply, finFreeSingle_apply, finFreeSingle_apply]
  split_ifs <;> simp

/-- **The standard basis of the sections of the free presheaf of modules of rank `r`.** -/
noncomputable def finFreeBasis (r : ℕ) (A : Cᵒᵖ) :
    Module.Basis (Fin r) ((O ⋙ forget₂ CommRingCat RingCat).obj A) ((finFree O r).obj A) :=
  Pi.basisFun _ (Fin r)

/-- The `k`-th vector of the standard basis is the `k`-th standard basis section. -/
@[simp]
theorem finFreeBasis_apply (r : ℕ) (A : Cᵒᵖ) (k : Fin r) :
    finFreeBasis O r A k = finFreeSingle O r A k :=
  Pi.basisFun_apply _ (Fin r) k

/-- **The exterior product of the standard basis sections indexed by a tuple**, as a local section
of the degree-`n` sectionwise exterior power of `finFree O r`. -/
noncomputable def finFreeWedge (r n : ℕ) (A : Cᵒᵖ) (i : Fin n → Fin r) :
    (exteriorAlgebraPiece (n : ℤ) (finFree O r)).obj A :=
  exteriorPower.ιMulti ((O ⋙ forget₂ CommRingCat RingCat).obj A) n
    (fun j => finFreeSingle O r A (i j))

/-- In the exterior algebra of the sections, `finFreeWedge O r n A i` is the exterior product of
the standard basis sections `finFreeSingle O r A (i j)`. -/
theorem exteriorAlgebraPieceVal_finFreeWedge (r n : ℕ) (A : Cᵒᵖ) (i : Fin n → Fin r) :
    exteriorAlgebraPieceVal (n : ℤ) (finFree O r) A (finFreeWedge O r n A i) =
      ExteriorAlgebra.ιMulti ((O ⋙ forget₂ CommRingCat RingCat).obj A) n
        (fun j => finFreeSingle O r A (i j)) :=
  rfl

/-- **Restriction fixes the exterior products of standard basis sections.** -/
@[simp]
theorem map_finFreeWedge (r n : ℕ) {A B : Cᵒᵖ} (g : A ⟶ B) (i : Fin n → Fin r) :
    (exteriorAlgebraPiece (n : ℤ) (finFree O r)).map g (finFreeWedge O r n A i) =
      finFreeWedge O r n B i := by
  refine exteriorAlgebraPieceVal_injective (n : ℤ) (finFree O r) B ?_
  rw [exteriorAlgebraPieceVal_map, exteriorAlgebraPieceVal_finFreeWedge,
    ExteriorAlgebra.mapₛₗ_ιMulti, exteriorAlgebraPieceVal_finFreeWedge]
  exact congrArg (ExteriorAlgebra.ιMulti _ n)
    (funext fun j => map_finFreeSingle O r g (i j))

/-- **The basis of the sections of the degree-`n` sectionwise exterior power of `finFree O r`**,
indexed by the `n`-element subsets of `Fin r`: the basis vector at a subset is the exterior product
of the corresponding standard basis sections, taken in increasing order. -/
noncomputable def exteriorFinFreeBasis (r n : ℕ) (A : Cᵒᵖ) :
    Module.Basis ↑(Set.powersetCard (Fin r) n) ((O ⋙ forget₂ CommRingCat RingCat).obj A)
      ((exteriorAlgebraPiece (n : ℤ) (finFree O r)).obj A) :=
  Module.Basis.exteriorPower n (finFreeBasis O r A)

/-- The basis vector of `exteriorFinFreeBasis` at an `n`-element subset `t` of `Fin r` is
`finFreeWedge` of the increasing enumeration of `t`. -/
theorem exteriorFinFreeBasis_apply (r n : ℕ) (A : Cᵒᵖ)
    (t : ↑(Set.powersetCard (Fin r) n)) :
    exteriorFinFreeBasis O r n A t =
      finFreeWedge O r n A (fun j => (Set.powersetCard.ofFinEmbEquiv.symm t) j) :=
  (exteriorPower.basis_apply _ n (finFreeBasis O r A) t).trans
    (congrArg (exteriorPower.ιMulti _ n) (funext fun _ => finFreeBasis_apply O r A _))

/-- **Restriction fixes the basis vectors of the sectionwise exterior powers.** -/
theorem map_exteriorFinFreeBasis (r n : ℕ) {A B : Cᵒᵖ} (g : A ⟶ B)
    (t : ↑(Set.powersetCard (Fin r) n)) :
    (exteriorAlgebraPiece (n : ℤ) (finFree O r)).map g (exteriorFinFreeBasis O r n A t) =
      exteriorFinFreeBasis O r n B t := by
  rw [exteriorFinFreeBasis_apply, exteriorFinFreeBasis_apply, map_finFreeWedge]

end PresheafOfModules

end
