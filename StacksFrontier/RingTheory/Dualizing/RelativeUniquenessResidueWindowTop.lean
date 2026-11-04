module

public import StacksFrontier.Homology.Tor.DerivedTensorProductIsLE
public import StacksFrontier.Homology.Tor.ResidueDevissageTop
public import StacksFrontier.Homology.Tor.ResidueLengthTop
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation

/-!
# The residue-field window of the duality route, from the top alone

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindow` computes the window of
`P ⊗ᴸ_A κ` from a fixed object `T` with `P ⊗ᴸ_A T ≅ T`, and asks `T` to be bounded on **both**
sides.  The module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation` records why the lower
bound is a genuine condition and not a theorem: at the Artinian witness
`A = k[x, y]/(x, y)²` of `StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation` the object
`T = ω ⊗ᴸ_A κ` is unbounded below, `ω = Hom_k(A, k)` being a dualizing complex of infinite
projective dimension.

**This file removes that hypothesis from both halves of the computation.**  The degree half is
the one-sided dévissage
`StacksDraft.ResidueDevissage.eq_zero_of_isLE_of_iso_of_isTorsionBySet` and the length half is
the top-end count
`StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_isLE_of_iso_of_isTorsionBySet`,
both run at `F = P ⊗ᴸ_A -`.  The way-out right exactness of that functor — the price both halves
pay for dropping the lower bound — is here a **theorem** rather than a hypothesis:
`Dualizing.wayOut_derivedTensorSlice`, which is
`CochainComplex.DerivedTensor.isLE_tensor` transported to the route's own vocabulary across
`Dualizing.canonicalTensorIsoDerivedHomTensor`.

## What is traded for what

The one-sided statements ask `P` to be bounded above and nothing else of `P`; the two-sided ones
ask nothing of `P` but ask `T` to be bounded below.  For the duality route the trade is
favourable: `P = RHom_A(K, ω)` is assumed to have bounded coherent cohomology there, so
`P.IsLE p` is available, while `T.IsGE a` is the condition refuted above.

## What this closes, and what it does not

`Dualizing.fibre_isLE_zero_and_homology_iso_residueField_of_derivedTensor_isLE_of_iso` is the
one-sided computation in one statement: `P ⊗ᴸ_A κ` has **no cohomology above degree zero** and is
**one-dimensional there**.  Two of the three things a one-sided local computation needs, as
listed in the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`, are therefore in place —
the extremal-degree theorem at the top, `StacksDraft.ExtremalDegrees.extremalDegrees_top` with
the way-out bound that lets it be applied, and the top-end mirror of the length count.  **The
third is not**, and this file does not touch it:

* **A rigidity step that is not a degree count.**  The conclusion above puts `P` in degrees
  `≤ 0` with `H⁰(P)` needing one generator at every maximal ideal — that much is now a theorem,
  `Dualizing.isLE_zero_and_tensor_homology_zero_iso_quotient` of
  `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessRigidity`, which reads the conclusion below
  back on `P` itself.  It cannot give `P ≅ A`, since the fibres of `A ⧸ I` look the same for
  every proper `I`.  The last step has to use `P ⊗ᴸ_A ω ≅ ω` itself rather than its reduction
  modulo `m`.

Equivalently: the two-sided computation concludes that `P ⊗ᴸ_A κ` is concentrated in degree zero
— no cohomology *below* it either — and that lower bound is what
`Dualizing.isPerfect_of_fibre_concentrated` and the perfection chain consume.  Nothing here
produces it, and nothing in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessRigidity` does either: by [stacks 068V] such
a bound is of the same strength as perfectness of `P`.

So [stacks 0E2D] is **not** closed by this file, and its registration is unchanged.  Beyond the
rigidity step the duality route additionally needs `ω` to be a dualizing complex for `A`, which
the source does not assume and which is unconditional only over a field.

## Main results

* `Dualizing.isLE_derivedHomTensor` — **the tensor of [stacks 0A63] is right t-exact in both
  variables**, with no lower bound on either factor.
* `Dualizing.wayOut_derivedTensorSlice` — the same in the shape of the way-out hypothesis:
  for `P` in `D^{≤ p}`, the functor `P ⊗ᴸ_A -` carries `D^{≤ n}` into `D^{≤ n + p}`.
* `Dualizing.eq_zero_of_derivedTensor_isLE_of_iso_of_isTorsionBySet` — **the degree half with no
  lower bound on the fixed object**: the top of the window of `P ⊗ᴸ_A κ` is degree zero.
* `Dualizing.nonempty_homology_derivedFibre_iso_residueField_of_isLE_of_isTorsionBySet` — **the
  length half with no lower bound on the fixed object**: `H⁰(P ⊗ᴸ_A κ) ≅ κ`.
* `Dualizing.fibre_isLE_zero_and_homology_iso_residueField_of_derivedTensor_isLE_of_iso` — **the
  two composed**, the degree half discharging the length half's hypothesis on the window.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

section WayOut

variable (A : Type u) [CommRing A]

/-- **The tensor of the tensor--Hom adjunction of [stacks 0A63] is right t-exact in both
variables**: the tensor product of an object of `D^{≤ a}(A)` with an object of `D^{≤ b}(A)` lies
in `D^{≤ a + b}(A)`.  Neither factor is assumed bounded below.

`CochainComplex.DerivedTensor.isLE_canonicalDerivedTensorProduct` is the statement for the
canonical derived tensor product of [stacks 068I], and
`Dualizing.canonicalTensorIsoDerivedHomTensor` identifies the two at every pair. -/
theorem isLE_derivedHomTensor (P Q : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    [P.IsLE a] [Q.IsLE b] :
    ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, Q)).IsLE (a + b) := by
  have := CochainComplex.DerivedTensor.isLE_canonicalDerivedTensorProduct P Q a b
  exact DerivedCategory.TStructure.t.isLE_of_iso (canonicalTensorIsoDerivedHomTensor A P Q) (a + b)

/-- **`P ⊗ᴸ_A -` is way-out right exact with slack `p`, for `P` in `D^{≤ p}`.**  This is the
hypothesis `hway` of `StacksDraft.ExtremalDegrees.isLE_map_of_homology_of_wayOut` and of
`StacksDraft.ResidueDevissage.eq_zero_of_isLE_of_iso_of_isTorsionBySet`, verbatim, in the
vocabulary the duality route to [stacks 0E2D] is phrased in: a single `p` carrying `D^{≤ n}` into
`D^{≤ n + p}` for every `n`, with no lower bound anywhere. -/
theorem wayOut_derivedTensorSlice (P : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) (hP : P.IsLE p)
    (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (hY : Y.IsLE n) :
    (((Functor.curry.obj
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor).obj
        P).obj Y).IsLE (n + p) := by
  have := hP
  have := hY
  have h : ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, Y)).IsLE (n + p) := by
    have := isLE_derivedHomTensor A P Y p n
    exact DerivedCategory.TStructure.t.isLE_of_le _ (p + n) (n + p) (by omega)
  exact h

end WayOut

section ResidueWindowTop

variable (A : Type u) [CommRing A]

/-- **The degree half of the local computation of the duality route to [stacks 0E2D], with no
lower bound on the fixed object: the top of the window of `P ⊗ᴸ_A κ` is degree zero.**

Let `m` be a maximal ideal, `κ = A / m`, let `P` lie in `D^{≤ p}`, and let `T` lie in `D^{≤ b}`
with every cohomology module finite and killed by `m` and with `H^b(T) ≠ 0`.  Suppose
`P ⊗ᴸ_A T ≅ T`.  If `P ⊗ᴸ_A κ` lies in `D^{≤ d}` and its `d`-th cohomology is nonzero, then
`d = 0`.

Compared with `Dualizing.eq_zero_of_derivedTensor_iso_of_isTorsionBySet` this drops `T.IsGE a`,
the nonvanishing of `H^a(T)`, and the whole lower half of the window of `P ⊗ᴸ_A κ`, and adds the
single hypothesis `P.IsLE p`.  That hypothesis is what makes `P ⊗ᴸ_A -` way-out right exact
(`Dualizing.wayOut_derivedTensorSlice`), and it is available in the route, where `P` has bounded
coherent cohomology by assumption — whereas `T.IsGE a` is refuted at the Artinian witness the
route was built to reach.

**No condition on `A` is used** — not Noetherian, not local, nothing.  The mathematics is
`StacksDraft.ResidueDevissage.eq_zero_of_isLE_of_iso_of_isTorsionBySet`, and the exactness of
`P ⊗ᴸ_A -` in the adjunction's vocabulary is
`Dualizing.derivedTensorSlice_commShift` and `Dualizing.derivedTensorSlice_isTriangulated`. -/
theorem eq_zero_of_derivedTensor_isLE_of_iso_of_isTorsionBySet
    (m : Ideal A) [m.IsMaximal] (P T : DerivedCategory (ModuleCat.{u} A)) (b d p : ℤ)
    (hP : P.IsLE p) (hb : T.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hLE : (derivedFibre A P m).IsLE d)
    (hd : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).obj
      (derivedFibre A P m)))
    (htop : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).obj T))
    (e : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, T) ≅ T) :
    d = 0 :=
  StacksDraft.ResidueDevissage.eq_zero_of_isLE_of_iso_of_isTorsionBySet
    ((Functor.curry.obj
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor).obj P)
    m T b d p hb (wayOut_derivedTensorSlice A P p hP) hkill hfin hLE hd htop e

/-- **The length half of the local computation with no lower bound on the fixed object:
`H⁰(P ⊗ᴸ_A κ) ≅ κ`.**

Same data as `Dualizing.eq_zero_of_derivedTensor_isLE_of_iso_of_isTorsionBySet`, with the window
of `P ⊗ᴸ_A κ` already known to stop at degree zero.  This is
`StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_isLE_of_iso_of_isTorsionBySet`
at `F = P ⊗ᴸ_A -`, whose way-out hypothesis is `Dualizing.wayOut_derivedTensorSlice`.

Like its two-sided companion
`Dualizing.nonempty_homology_derivedTensor_iso_residueField_of_isTorsionBySet` it is a length
count and not a degree count, and it uses no *lower* bound on the window of `P ⊗ᴸ_A κ` at all,
where that one uses no upper bound.

**No condition on `A` is used.** -/
theorem nonempty_homology_derivedFibre_iso_residueField_of_isLE_of_isTorsionBySet
    (m : Ideal A) [m.IsMaximal] (P T : DerivedCategory (ModuleCat.{u} A)) (b p : ℤ)
    (hP : P.IsLE p) (hb : T.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hLE : (derivedFibre A P m).IsLE 0)
    (htop : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).obj T))
    (e : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, T) ≅ T) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (derivedFibre A P m) ≅
      ModuleCat.of A (A ⧸ m)) :=
  StacksDraft.ResidueLength.nonempty_homology_iso_residueField_of_isLE_of_iso_of_isTorsionBySet
    ((Functor.curry.obj
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor).obj P)
    m T b p hb (wayOut_derivedTensorSlice A P p hP) hkill hfin hLE htop e

/-- **The one-sided local computation: `P ⊗ᴸ_A κ` is `κ` in degree zero and nothing above.**

Let `m` be a maximal ideal, `κ = A / m`, let `P` lie in `D^{≤ p}`, and let `T` lie in `D^{≤ b}`
with every cohomology module finite and killed by `m` and with `H^b(T) ≠ 0`.  Suppose
`P ⊗ᴸ_A T ≅ T`, and let `P ⊗ᴸ_A κ` lie in `D^{≤ d}` with nonzero `d`-th cohomology.  Then
`d = 0`, so `P ⊗ᴸ_A κ` has no cohomology above degree zero, and `H⁰(P ⊗ᴸ_A κ) ≅ κ`.

**Nothing is bounded below.**  The two halves are independent, as in the two-sided
`Dualizing.fibre_eq_residueField_of_derivedTensor_iso_of_isTorsionBySet`: the degree half sees
only which degrees are nonzero, and the length half uses no lower bound on the window.  What the
degree half contributes to the composition is the hypothesis `(P ⊗ᴸ_A κ).IsLE 0` of the length
half, which is therefore a consequence rather than an assumption.

**This is not yet the full local computation.**  The two-sided statement concludes that
`P ⊗ᴸ_A κ` is concentrated in degree zero — no cohomology *below* it either — and that lower
bound is what `Dualizing.isPerfect_of_fibre_concentrated` and the perfection chain consume.  It
is not a degree count and it is not available here; see the module documentation. -/
theorem fibre_isLE_zero_and_homology_iso_residueField_of_derivedTensor_isLE_of_iso
    (m : Ideal A) [m.IsMaximal] (P T : DerivedCategory (ModuleCat.{u} A)) (b d p : ℤ)
    (hP : P.IsLE p) (hb : T.IsLE b)
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hLE : (derivedFibre A P m).IsLE d)
    (hd : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).obj
      (derivedFibre A P m)))
    (htop : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).obj T))
    (e : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
      (P, T) ≅ T) :
    d = 0 ∧ (derivedFibre A P m).IsLE 0 ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (derivedFibre A P m) ≅ ModuleCat.of A (A ⧸ m)) := by
  have hd0 : d = 0 := eq_zero_of_derivedTensor_isLE_of_iso_of_isTorsionBySet A m P T b d p hP hb
    hkill hfin hLE hd htop e
  subst hd0
  exact ⟨rfl, hLE, nonempty_homology_derivedFibre_iso_residueField_of_isLE_of_isTorsionBySet
    A m P T b p hP hb hkill hfin hLE htop e⟩

end ResidueWindowTop

end Dualizing

end
