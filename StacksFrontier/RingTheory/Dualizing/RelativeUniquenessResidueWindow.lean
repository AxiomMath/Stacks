module

public import StacksFrontier.Homology.Tor.ResidueLength
public import StacksFrontier.Homology.Devissage.DerivedTensorExtensionScalars

/-!
# The residue-field window of the duality route to [stacks 0E2D]

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` reduces [stacks 0E2D] — through
duality rather than through the tensor--Hom diagonal of [stacks 0BYN] — to the implication

> `RHom_A(P, A) ≅ A`  ⟹  `P ≅ A`   for `P` with bounded coherent cohomology,

and discharges the half of that implication which is pure adjunction: `P ⊗ᴸ_A ω ≅ ω`.  The other
half is a local computation, which says that `P ⊗ᴸ_A κ` is **the residue field in degree zero**
for every residue field `κ = A / m`: concentrated there, and one-dimensional there.

Both halves are proved here, at the tensor product of the tensor--Hom adjunction of
[stacks 0A63] — the one in which the route's own statements are phrased.  Two things have to be
brought together.

* `StacksDraft.ResidueDevissage.eq_zero_of_iso_of_isTorsionBySet` is the step for an arbitrary
  **exact endofunctor** `F` of `D(A)` with `F(T) ≅ T`, where `T` is bounded with finite
  cohomology killed by `m` and nonzero at both ends.  It needs no condition on `A` at all.

* `F = P ⊗ᴸ_A -` is exact.  The tensor of `StacksDraft.DerivedHom.DerivedHomAdjunction` is a
  bifunctor on a product category and carries **no** shift or exactness data; those live on the
  derived tensor product of [stacks 068I].  The two bifunctors are identified by
  `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral`, and this file restricts that isomorphism
  to the slice with the **first** variable fixed — the companion of
  `StacksDraft.CompactDevissage.derivedTensorFlipIso`, which does the second — and transports the
  shift commutation and the exactness across it.  So the exactness of `P ⊗ᴸ_A -` in the
  adjunction's vocabulary is a theorem here, not a hypothesis.

## Main definitions

* `Dualizing.derivedTensorSliceIso` — the two spellings of `P ⊗ᴸ_A -` agree: the slice of the
  derived tensor product of [stacks 068I] with the first variable fixed is the corresponding
  slice of the tensor of [stacks 0A63].

## Main results

* `Dualizing.derivedTensorSlice_commShift`, `Dualizing.derivedTensorSlice_isTriangulated` —
  **`P ⊗ᴸ_A -` is exact in the adjunction's vocabulary**, by transport across that isomorphism.
* `Dualizing.eq_zero_of_derivedTensor_iso_of_isTorsionBySet` — **the degree half of the local
  computation.**  If `P ⊗ᴸ_A T ≅ T` for a bounded `T` whose cohomology is finite and killed by
  the maximal ideal and nonzero at both ends, and if `P ⊗ᴸ_A κ` has cohomology concentrated in
  `[c, d]` and nonvanishing in those two degrees, then `c = d = 0`.
* `Dualizing.nonempty_homology_derivedTensor_iso_residueField_of_isTorsionBySet` — **the length
  half.**  In the same situation, with `H^a(T)` nonzero and `P ⊗ᴸ_A κ` having no cohomology below
  degree zero, `H⁰(P ⊗ᴸ_A κ) ≅ κ`.

## What this does and does not give the route

At `T = ω ⊗ᴸ_A κ`, whose cohomology is killed by `m` because `κ` is, and `P ⊗ᴸ_A T ≅ T` coming
from `P ⊗ᴸ_A ω ≅ ω`, the two conclusions together say that `P ⊗ᴸ_A κ` is `κ` in degree zero.  The
two are independent: the degree half rests on the extremal-degree theorem, which sees only which
degrees are nonzero and never how large they are, while the length half is a `κ`-dimension count
and uses no upper bound on the window at all.  The count is
`StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_iso_of_isTorsionBySet` of
`StacksFrontier.Homology.Tor.ResidueLength`, and like the dévissage it is no condition on `A`.

The passage from "fibre concentrated and one-dimensional at every maximal ideal" to the tensor
unit is `Dualizing.nonempty_iso_derivedTensorUnit_of_maximalFibre_finrank` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessPerfectionChain`.  Between the two sits a
**change of spelling of the fibre**: that chain states its hypothesis for the object
`(totalDerivedExtensionScalars (algebraMap A m.ResidueField)).functor.obj P` of
`D(m.ResidueField)` and a `finrank` over `m.ResidueField`, while the two statements here are about
`P ⊗ᴸ_A κ[0]` in `D(A)` and the `A`-module structure of its cohomology.  The two scalar rings are
not the same type — `Ideal.ResidueField m` is the residue field of `Localization.AtPrime m`, and
for `m` maximal it is compared with `A / m` only through the bijectivity of the algebra map,
`Ideal.bijective_algebraMap_quotient_residueField`.

That change of spelling is proved in `StacksFrontier.Homology.Perfect.DerivedTensorFibre`: for a
pseudo-coherent object, `Hⁱ` of the `D(m.ResidueField)` fibre, restricted along `A → κ(m)`, **is**
`Hⁱ(P ⊗ᴸ_A κ(m)[0])` in `D(A)`. Only the *vanishing* half of that comparison used to be recorded —
by `StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology` of
`StacksFrontier.Homology.Perfect.Local` together with
`StacksDraft.Perfect.isZero_homology_derivedTensor_single_residueField_of_fibreCohomologyVanishes`
and its converse — whose proofs construct the comparison and then discard it, because restriction
of scalars neither creates nor destroys the vanishing of a cohomology module and nothing more is
needed for a vanishing statement.  A statement about the *dimension* of `H⁰` needs the
isomorphism, and it is now there; the two consequences in the shape the two statements of this
module produce, where the window outputs an `A`-module isomorphism with `A / m` and the chain asks
for a `κ(m)` dimension, are
`StacksDraft.Perfect.finrank_homology_totalDerivedExtensionScalars_eq_one_of_nonempty_iso_quotient`
and `StacksDraft.Perfect.finrank_homology_totalDerivedExtensionScalars_eq_zero_of_isZero`.

Those two are stated for the canonical derived tensor product of [stacks 068I], not for the
tensor of [stacks 0A63] that the two statements below are about; the comparison of the two at a
pair of objects and the resulting change of spelling in *this* module's vocabulary are
`Dualizing.canonicalTensorIsoDerivedHomTensor` and
`Dualizing.maximalFibre_finrank_of_fibre_concentrated` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`, the second of which
delivers the perfection chain's hypothesis `hfib` verbatim from the conclusions of the two
statements below.  That module also runs the two statements below together — the degree half
discharging the length half's lower-bound hypothesis — and records the one hypothesis of the
fixed object `T = ω ⊗ᴸ_A κ` that is not a theorem: its cohomological lower bound.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

section TensorSlice

variable (A : Type u) [CommRing A]

/-- The comparison from the derived tensor product of [stacks 068I] with a fixed object in the
**first** variable to the tensor of the tensor--Hom adjunction of [stacks 0A63]: the value of
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` at a pair whose first entry is held fixed.

This is the companion of `StacksDraft.CompactDevissage.derivedTensorFlipIso`, which holds the
second entry fixed instead. -/
def derivedTensorSliceIso (P : DerivedCategory (ModuleCat.{max u v} A)) :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral.{u, v} A).obj P ≅
      (Functor.curry.obj
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} A).tensor).obj P where
  hom :=
    { app X := (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom.app (P, X)
      naturality X Y g := by
        simpa [CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral] using
          (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom.naturality
            (Prod.mkHom (𝟙 P) g) }
  inv :=
    { app X := (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).inv.app (P, X)
      naturality X Y g := by
        simp [CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral] }
  hom_inv_id := by
    ext X
    exact (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom_inv_id_app (P, X)
  inv_hom_id := by
    ext X
    exact (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).inv_hom_id_app (P, X)

/-- **The tensor of [stacks 0A63] with a fixed object in the first variable commutes with the
shift.**  The structure `StacksDraft.DerivedHom.DerivedHomAdjunction` carries no shift data; this
is transported from the derived tensor product of [stacks 068I] across
`Dualizing.derivedTensorSliceIso`. -/
instance derivedTensorSlice_commShift (P : DerivedCategory (ModuleCat.{max u v} A)) :
    ((Functor.curry.obj
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).tensor).obj P).CommShift ℤ :=
  Functor.CommShift.ofIso (derivedTensorSliceIso.{u, v} A P) ℤ

/-- **The tensor of [stacks 0A63] with a fixed object in the first variable is exact.**
Transported from [stacks 068I] across `Dualizing.derivedTensorSliceIso`, whose compatibility with
the shift is the one `Dualizing.derivedTensorSlice_commShift` was defined by. -/
instance derivedTensorSlice_isTriangulated (P : DerivedCategory (ModuleCat.{max u v} A)) :
    ((Functor.curry.obj
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).tensor).obj P).IsTriangulated := by
  let i := derivedTensorSliceIso.{u, v} A P
  let _ := Functor.CommShift.ofIso_compatibility i ℤ
  exact Functor.isTriangulated_of_iso i

end TensorSlice

section ResidueWindow

variable (A : Type u) [CommRing A]

/-- **The first step of the local computation of the duality route to [stacks 0E2D]:
`P ⊗ᴸ_A κ` is concentrated in degree zero.**

Let `m` be a maximal ideal, `κ = A / m`, and let `T` be an object of `D(A)` with cohomology
concentrated in `[a, b]`, every cohomology module finite and killed by `m`, and `H^a(T)` and
`H^b(T)` nonzero.  Suppose `P ⊗ᴸ_A T ≅ T`.  If `P ⊗ᴸ_A κ` has cohomology concentrated in
`[c, d]` and does not vanish in those two degrees, then `c = 0` and `d = 0`.

Everything is at the tensor product of the tensor--Hom adjunction of [stacks 0A63], in which the
route's own statements are phrased; its exactness in the second variable is
`Dualizing.derivedTensorSlice_isTriangulated`.  The mathematics is
`StacksDraft.ResidueDevissage.eq_zero_of_iso_of_isTorsionBySet`: the dévissage of a `κ`-vector
space feeding the extremal-degree theorem, and the conclusion read back off the fixed object.

**No condition on `A` is used** — not Noetherian, not local, nothing.  At `T = ω ⊗ᴸ_A κ` and
`P = RHom_A(K, ω)` this is the step the rigidity argument of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` asks for; what that argument still
wants of `P ⊗ᴸ_A κ` beyond this is that it be one-dimensional in degree zero, which is a length
count rather than a degree count. -/
theorem eq_zero_of_derivedTensor_iso_of_isTorsionBySet
    (m : Ideal A) [m.IsMaximal] (P T : DerivedCategory (ModuleCat.{u} A)) (a b c d : ℤ)
    (ha : T.IsGE a) (hb : T.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hGE : ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ m)))).IsGE c)
    (hLE : ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ m)))).IsLE d)
    (hc : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) c).obj
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
        (P, (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ m))))))
    (hd : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).obj
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
        (P, (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ m))))))
    (hbot : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj T))
    (htop : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).obj T))
    (e : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, T) ≅ T) :
    c = 0 ∧ d = 0 :=
  StacksDraft.ResidueDevissage.eq_zero_of_iso_of_isTorsionBySet
    ((Functor.curry.obj
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor).obj P)
    m T a b c d ha hb hkill hfin hGE hLE hc hd hbot htop e

/-- **The second step of the local computation of the duality route to [stacks 0E2D]:
`P ⊗ᴸ_A κ` is one-dimensional in degree zero.**

Let `m` be a maximal ideal, `κ = A / m`, and let `T` be an object of `D(A)` with cohomology
concentrated in `[a, b]`, every cohomology module finite and killed by `m`, and `H^a(T)` nonzero.
Suppose `P ⊗ᴸ_A T ≅ T`.  If `P ⊗ᴸ_A κ` has no cohomology below degree zero, then

`H⁰(P ⊗ᴸ_A κ) ≅ κ`.

This is the length count rather than the degree count, and it is independent of
`Dualizing.eq_zero_of_derivedTensor_iso_of_isTorsionBySet`: it uses no upper bound on the window of
`P ⊗ᴸ_A κ` at all, while that theorem sees only which degrees are nonzero and never how large they
are.  Together the two say that `P ⊗ᴸ_A κ` is `κ` in degree zero, which is what the rigidity
argument of `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` asks of it.

Everything is at the tensor product of the tensor--Hom adjunction of [stacks 0A63]; the mathematics
is `StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_iso_of_isTorsionBySet` and the
exactness in the second variable is `Dualizing.derivedTensorSlice_isTriangulated`.

**No condition on `A` is used** — not Noetherian, not local, nothing. -/
theorem nonempty_homology_derivedTensor_iso_residueField_of_isTorsionBySet
    (m : Ideal A) [m.IsMaximal] (P T : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (ha : T.IsGE a) (hb : T.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hGE : ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ m)))).IsGE 0)
    (hbot : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj T))
    (e : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, T) ≅ T) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
        (P, (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ m)))) ≅ ModuleCat.of A (A ⧸ m)) :=
  StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_iso_of_isTorsionBySet
    ((Functor.curry.obj
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor).obj P)
    m T a b ha hb hkill hfin hGE hbot e

end ResidueWindow

end Dualizing

end
