module

public import StacksFrontier.Homology.Tor.DerivedTensorTopDegree
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindowTop

/-!
# The one-sided local computation read on `P` itself

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindowTop` computes the derived fibre
of the duality route to [stacks 0E2D] from the top of the window alone:
`Dualizing.fibre_isLE_zero_and_homology_iso_residueField_of_derivedTensor_isLE_of_iso` says that
`P ⊗ᴸ_A κ(m)` has **no cohomology above degree zero** and is `κ(m)` there, at every maximal
ideal, with no lower bound on the fixed object `T = ω ⊗ᴸ_A κ(m)` — the hypothesis refuted at the
Artinian witness of `StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`.

The module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation` records what the remaining
**rigidity step** has to do, and asserts as its starting point that the conclusion above "puts
`P` in degrees `≤ 0` with cyclic `H⁰`".  **That assertion was not a theorem anywhere in the
library.**  This file proves it:

* `Dualizing.isLE_zero_of_forall_derivedFibre_isLE_zero` — `P` itself lies in `D^{≤ 0}`;
* `Dualizing.nonempty_tensor_homology_zero_iso_quotient` — `H⁰(P) ⊗_A κ(m) ≅ κ(m)`, so `H⁰(P)`
  needs **one generator** at every maximal ideal;
* `Dualizing.isLE_zero_and_tensor_homology_zero_iso_quotient` — the two together, from the
  conclusion of the one-sided computation.

## How, and what it does not use

Both come from one general fact about the top of a cohomological window,
`Stacks.DerivedTensor.nonempty_homology_top_derivedTensor_single_iso` of
`StacksFrontier.Homology.Tor.DerivedTensorTopDegree`: for `X` in `D^{≤ p}`,

`H^p(X ⊗ᴸ_A N[0]) ≅ H^p(X) ⊗_A N`.

At `N = A / m` the right-hand side is a residue tensor of a finite module, so Nakayama's lemma at
every maximal ideal at once
(`StacksDraft.Nakayama.subsingleton_of_forall_subsingleton_tensor_quotient`) turns the vanishing
of the fibre above degree zero into the vanishing of `H^p(P)` for `p > 0`, and the window of `P`
drops to zero one degree at a time.  At `p = 0` the same isomorphism identifies `H⁰(P) ⊗_A κ(m)`
with `H⁰(P ⊗ᴸ_A κ(m))`, which the length half of the one-sided computation has already computed
to be `κ(m)`.

This route is elementary and uses **no condition on `A`** in its core: the Noetherian hypothesis
appears only in the composed statement, and only to supply the finiteness of the cohomology
modules of `P` from pseudo-coherence ([stacks 066E]).  In particular it does not go through
[stacks 068V]: the half of that tag which passes from fibre vanishing at every maximal ideal to
vanishing, which the module documentation cited, is `StacksDraft.Perfect`'s own
`homology_isZero_of_maximal_fibres` and is private to
`StacksFrontier.Homology.Perfect.Local` — and it reads the vanishing off a localization, where the
argument here reads it off the ordinary tensor product.

## What remains of the rigidity step, exactly

The conclusion `P.IsLE 0` together with one generator for `H⁰(P)` at every maximal ideal is
**not** `P ≅ A`, and the gap is not a degree count:

* the fibres of `A ⧸ I` satisfy both conclusions for every proper `I`, so no amount of fibre
  information at `m` can separate `A` from a proper quotient;
* what is still missing for the perfection chain is the **lower** bound
  `(P ⊗ᴸ_A κ(m)).IsGE 0`, which is the hypothesis `hGE` of
  `Dualizing.isPerfect_of_fibre_concentrated` and, through it, of
  `Dualizing.nonempty_iso_derivedTensorUnit_of_fibre_concentrated`.  Equivalently
  `τ^{≤ -1}P = 0` **and** `H⁰(P)` locally free of rank one: for `P` concentrated in degree zero
  the fibre is `H⁰(P) ⊗ᴸ_A κ(m)`, whose lower cohomology is the Tor of a module, and that
  vanishes exactly in the locally free case.  By [stacks 068V] a lower bound uniform in `m` is of
  the same strength as perfectness of `P`, which is what
  `Dualizing.isPerfect_of_fibre_concentrated` says — so the remaining step cannot be obtained
  from the window of the fibre at all, and must use the hypothesis `P ⊗ᴸ_A ω ≅ ω` itself rather
  than its reduction modulo `m`.

Of those two conjuncts the **second** is closed, over a *local* ring, in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessRigidityFreeness`:
`Dualizing.free_homology_zero_of_ext_zero_of_nonempty_tensor_homology_iso` gets `H⁰(P)` free of
rank one out of the one-generator conclusion above together with the rigidity hypothesis read in
degree zero — `Ext⁰_A(P, A[0]) ≅ A`, which by [stacks 06XS] says that the `A`-dual of `H⁰(P)` is
free of rank one — and no count enters.  **That leaves the first conjunct, `τ^{≤ -1}P = 0`,
untouched**: it is independent of the second, not a consequence of it.  The degree-zero reading
of the route's object-level hypothesis is itself not assembled anywhere in the library; see that
module's documentation for both points, and for where the residue of the duality route sits
once that conjunct is the only one left.

Beyond that the duality route additionally needs `ω` to be a dualizing complex for `A`, which the
source of [stacks 0E2D] does not assume and which is unconditional only over a field.  **So
[stacks 0E2D] is not closed by this file and its registrations are unchanged.**

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

variable (A : Type u) [CommRing A]

/-- **The top cohomology of the derived fibre is the residue tensor of the top cohomology of
`P`.**  For `P` in `D^{≤ p}` and a maximal ideal `m`,

`H^p(P ⊗ᴸ_A κ(m)) ≅ H^p(P) ⊗_A A / m`,

at the tensor of the tensor--Hom adjunction of [stacks 0A63] — the vocabulary the duality route
to [stacks 0E2D] is phrased in.

This is `Stacks.DerivedTensor.nonempty_homology_top_derivedTensor_single_iso` transported across
`Dualizing.canonicalTensorIsoDerivedHomTensor`, which identifies the canonical derived tensor
product of [stacks 068I] with the adjunction's tensor at every pair.  **`P` is not assumed
bounded below**, and no hypothesis on `A` is used. -/
theorem nonempty_homology_top_derivedFibre_iso_tensor_quotient (m : Ideal A) [m.IsMaximal]
    (P : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) (hP : P.IsLE p) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj (derivedFibre A P m) ≅
      ModuleCat.of A (TensorProduct A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj P)
        (ModuleCat.of A (A ⧸ m)))) := by
  obtain ⟨e⟩ := Stacks.DerivedTensor.nonempty_homology_top_derivedTensor_single_iso A P p hP
    (ModuleCat.of A (A ⧸ m))
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).mapIso
    (canonicalTensorIsoDerivedHomTensor A P (residueSingle A m)).symm ≪≫ e⟩

/-- **`P` lies in degrees `≤ 0` as soon as every derived fibre does.**  Let `P` be an object of
`D(A)` bounded above and with finite cohomology modules.  If `P ⊗ᴸ_A κ(m)` has no cohomology above
degree zero for every maximal ideal `m`, then neither has `P`.

This is the first half of the rigidity step the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation` starts from, and the
hypothesis is exactly the conclusion of the degree half of the one-sided computation,
`Dualizing.eq_zero_of_derivedTensor_isLE_of_iso_of_isTorsionBySet`.

**No hypothesis on `A` is used**; the finiteness of the cohomology of `P` is carried rather than
deduced for that reason. -/
theorem isLE_zero_of_forall_derivedFibre_isLE_zero
    (P : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) (hP : P.IsLE p)
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (hLE : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsLE 0) :
    P.IsLE 0 := by
  refine Stacks.DerivedTensor.isLE_zero_of_forall_isLE_zero_derivedTensor_quotient A P p hP hfin
    (fun m hm => ?_)
  have := hm
  have h := hLE m hm
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (canonicalTensorIsoDerivedHomTensor A P (residueSingle A m)).symm 0

/-- **`H⁰(P)` needs one generator at `m`.**  For `P` in `D^{≤ 0}` whose derived fibre at a maximal
ideal `m` has cohomology `A / m` in degree zero,

`H⁰(P) ⊗_A A / m ≅ A / m`.

By Nakayama's lemma this says that the localization of `H⁰(P)` at `m` is generated by a single
element — the "cyclic `H⁰`" of the rigidity step's starting point, in the only sense in which it
is a theorem: a finite module with one-dimensional residue tensors at every maximal ideal need
not be cyclic globally.

This is `Dualizing.nonempty_homology_top_derivedFibre_iso_tensor_quotient` at `p = 0` composed
with the length half of the one-sided computation,
`Dualizing.nonempty_homology_derivedFibre_iso_residueField_of_isLE_of_isTorsionBySet`. -/
theorem nonempty_tensor_homology_zero_iso_quotient (m : Ideal A) [m.IsMaximal]
    (P : DerivedCategory (ModuleCat.{u} A)) (hP : P.IsLE 0)
    (hone : Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (derivedFibre A P m) ≅ ModuleCat.of A (A ⧸ m))) :
    Nonempty (ModuleCat.of A (TensorProduct A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)
      (ModuleCat.of A (A ⧸ m))) ≅ ModuleCat.of A (A ⧸ m)) := by
  obtain ⟨e⟩ := nonempty_homology_top_derivedFibre_iso_tensor_quotient A m P 0 hP
  exact hone.map fun f => e.symm ≪≫ f

/-- **The one-sided local computation read on `P` itself.**  Let `A` be Noetherian and let `P` be
a pseudo-coherent object of `D(A)`, bounded above, whose derived fibre at every maximal ideal `m`
has no cohomology above degree zero and has cohomology `A / m` there — the conclusion of
`Dualizing.fibre_isLE_zero_and_homology_iso_residueField_of_derivedTensor_isLE_of_iso`.  Then

`P` lies in `D^{≤ 0}`  and  `H⁰(P) ⊗_A A / m ≅ A / m` at every maximal ideal `m`.

This is the starting point the remaining rigidity step of the duality route to [stacks 0E2D] was
asserted to have, now proved.  **It is not the rigidity step**: see the module documentation for
exactly what is left, namely the *lower* bound on the fibre, which by [stacks 068V] is of the
same strength as perfectness of `P` and cannot come from the window of the fibre.

The Noetherian hypothesis is used only through [stacks 066E], to get the finiteness of the
cohomology modules of `P` out of pseudo-coherence; the two halves
`Dualizing.isLE_zero_of_forall_derivedFibre_isLE_zero` and
`Dualizing.nonempty_tensor_homology_zero_iso_quotient` use no hypothesis on `A` at all. -/
theorem isLE_zero_and_tensor_homology_zero_iso_quotient [IsNoetherianRing A]
    (P : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) (hP : P.IsLE p)
    (hPpc : StacksDraft.PseudoCoherence.IsPseudoCoherent P)
    (hfib : ∀ (m : Ideal A) (_ : m.IsMaximal), (derivedFibre A P m).IsLE 0 ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (derivedFibre A P m) ≅ ModuleCat.of A (A ⧸ m))) :
    P.IsLE 0 ∧ ∀ (m : Ideal A) (_ : m.IsMaximal),
      Nonempty (ModuleCat.of A (TensorProduct A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj P)
        (ModuleCat.of A (A ⧸ m))) ≅ ModuleCat.of A (A ⧸ m)) := by
  have hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P) :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      P 0 A).2.1.mp hPpc).2
  have h0 : P.IsLE 0 := isLE_zero_of_forall_derivedFibre_isLE_zero A P p hP hfin
    (fun m hm => (hfib m hm).1)
  refine ⟨h0, fun m hm => ?_⟩
  have := hm
  exact nonempty_tensor_homology_zero_iso_quotient A m P h0 (hfib m hm).2

end Dualizing

end
