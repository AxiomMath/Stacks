module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DirectSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DistinguishedTriangles

/-!
# Tor amplitude of a finite direct sum, from the summands

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)`. A finite direct
sum of objects of `D(O)` of Tor amplitude in `[a, b]` again has Tor amplitude in `[a, b]`, and a
finite direct sum of objects of finite Tor dimension has finite Tor dimension.

Stacks 08G3 is the converse direction — Tor amplitude of a direct sum passes to each summand —
and is `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_biprod`. The direction
proved here is the one an induction over a bounded complex consumes, together with that converse
and the two-out-of-three rules of Stacks 08G2: the derived tensor product of a strictly perfect
complex `P` with an object `M` is built by finitely many distinguished triangles out of direct
summands of finite direct sums of shifts of `M`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_biprod`: a binary direct sum of
  objects of Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_biprod`: a binary direct sum
  of objects of finite Tor dimension has finite Tor dimension, in the interval obtained by
  merging the two.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_biproduct`: a direct sum of a
  finite family of objects of Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_biproduct`: a direct sum of
  a finite family of objects of finite Tor dimension has finite Tor dimension.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_retract_biproduct`: a retract
  of a direct sum of a finite family of objects of Tor amplitude in `[a, b]` has Tor amplitude
  in `[a, b]`. This is the composite step the induction above consumes at each term of `P`.

## Implementation notes

The binary case is clause (2) of Stacks 08G2 read at the split triangle
`K ⟶ K ⊞ L ⟶ L ⟶ K⟦1⟧`, which is distinguished in any pretriangulated category
(`CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished`). So it uses nothing
about the derived tensor product beyond exactness of each `- ⊗^L_O F[0]`, which is the
`exact_left` field of `Stacks.SheafOfModules.DerivedTensorProduct`.

The finite case does not iterate the binary case: that would need an isomorphism splitting
`⨁ f` off its first summand, which Mathlib states only for the binary biproduct. It uses instead
that each `- ⊗^L_O F[0]` is exact, hence additive, hence so is its composite with a cohomology
functor; `CategoryTheory.Limits.biproduct.total` writes the identity of `⨁ f` as the sum of the
idempotents `π j ≫ ι j`, and an additive functor carries that sum to a sum each of whose terms
factors through a zero object. The index type is therefore in `Type`, as
`CategoryTheory.Limits.biproduct.total` requires and as
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_coproduct_of_smallIndex` already asks in this
directory. Its finiteness is needed only for that one rewrite, so the hypothesis is `Finite` and
the `Fintype` structure is chosen inside the proof.

Merging two intervals for the binary finite-Tor-dimension statement is `min`/`max`. For a finite
family the two bounds are produced from `Int.self_le_toNat` and `Finset.le_sup` rather than from
a lattice supremum on `ℤ`, which has neither a bottom nor a top element, so that the statement
needs no nonemptiness hypothesis on the index type.

## References

* [Stacks Project, Tag 08G2](https://stacks.math.columbia.edu/tag/08G2)
* [Stacks Project, Tag 08G3](https://stacks.math.columbia.edu/tag/08G3)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-- **Tor amplitude passes from two summands to their direct sum.** If `K` and `L` have Tor
amplitude in `[a, b]` then so does `K ⊞ L`.

The split triangle `K ⟶ K ⊞ L ⟶ L ⟶ K⟦1⟧` is distinguished, so this is clause (2) of
Stacks 08G2. -/
theorem hasTorAmplitude_biprod (K L : RingedSite.DerivedModules.{u, v, w, d} X) (a b : ℤ)
    (hK : HasTorAmplitude T K a b) (hL : HasTorAmplitude T L a b) :
    HasTorAmplitude T (K ⊞ L) a b :=
  hasTorAmplitude_obj₂ T _ (binaryBiproductTriangle_distinguished K L) a b hK hL

/-- **Finite Tor dimension passes from two summands to their direct sum**, in the interval
obtained by merging the two. -/
theorem hasFiniteTorDimension_biprod (K L : RingedSite.DerivedModules.{u, v, w, d} X)
    (hK : HasFiniteTorDimension T K) (hL : HasFiniteTorDimension T L) :
    HasFiniteTorDimension T (K ⊞ L) := by
  obtain ⟨a, b, hab⟩ := hK
  obtain ⟨c, e, hce⟩ := hL
  exact ⟨min a c, max b e, hasTorAmplitude_biprod T K L _ _
    (hab.mono (min_le_left a c) (le_max_left b e))
    (hce.mono (min_le_right a c) (le_max_right b e))⟩

/-- **Tor amplitude passes from a finite family to its direct sum.** If every `f j` has Tor
amplitude in `[a, b]` then so does `⨁ f`.

Each `- ⊗^L_O F[0]` is exact, hence additive, and so is its composite with the degree-`i`
cohomology functor; the identity of `⨁ f` is the sum of the idempotents `π j ≫ ι j`, and the
image of each of those factors through a zero object. -/
theorem hasTorAmplitude_biproduct {ι : Type}
    [Finite ι] (f : ι → RingedSite.DerivedModules.{u, v, w, d} X) [HasBiproduct f] (a b : ℤ)
    (hf : ∀ j, HasTorAmplitude T (f j) a b) : HasTorAmplitude T (⨁ f) a b := by
  let _ := Fintype.ofFinite ι
  intro F i hi
  let G := T.tensorModule F ⋙
    DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i
  show IsZero (G.obj (⨁ f))
  rw [IsZero.iff_id_eq_zero, ← G.map_id, ← biproduct.total, G.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [G.map_comp, (hf j F i hi).eq_of_tgt (G.map (biproduct.π f j)) 0, zero_comp]

/-- **Finite Tor dimension passes from a finite family to its direct sum.** -/
theorem hasFiniteTorDimension_biproduct {ι : Type}
    [Finite ι] (f : ι → RingedSite.DerivedModules.{u, v, w, d} X) [HasBiproduct f]
    (hf : ∀ j, HasFiniteTorDimension T (f j)) : HasFiniteTorDimension T (⨁ f) := by
  let _ := Fintype.ofFinite ι
  choose a b hab using hf
  let A : ℤ := -((Finset.univ.sup fun k => (-(a k)).toNat : ℕ) : ℤ)
  let B : ℤ := ((Finset.univ.sup fun k => (b k).toNat : ℕ) : ℤ)
  have key : ∀ (g : ι → ℤ) j, g j ≤ ((Finset.univ.sup fun k => (g k).toNat : ℕ) : ℤ) :=
    fun g j => (Int.self_le_toNat _).trans <|
      Nat.cast_le.2 (Finset.le_sup (f := fun k => (g k).toNat) (Finset.mem_univ j))
  exact ⟨A, B, hasTorAmplitude_biproduct T f A B
    fun j => (hab j).mono (neg_le.2 (key (fun k => -(a k)) j)) (key b j)⟩

/-- **A retract of a direct sum of a finite family of objects of Tor amplitude in `[a, b]` has
Tor amplitude in `[a, b]`.** This is the retract statement of Stacks 08G3 composed with the
direct-sum statement above, and it is the step the induction over a strictly perfect complex `P`
consumes at each term: `P^i` is a direct summand of a finite free `O`-module, so `P^i ⊗^L_O M`
is a retract of a finite direct sum of copies of `M`. -/
theorem hasTorAmplitude_of_retract_biproduct {ι : Type} [Finite ι]
    (f : ι → RingedSite.DerivedModules.{u, v, w, d} X) [HasBiproduct f]
    {M : RingedSite.DerivedModules.{u, v, w, d} X} (i : M ⟶ ⨁ f) (r : (⨁ f) ⟶ M)
    (hir : i ≫ r = 𝟙 M) (a b : ℤ) (hf : ∀ j, HasTorAmplitude T (f j) a b) :
    HasTorAmplitude T M a b :=
  hasTorAmplitude_of_retract T i r hir a b (hasTorAmplitude_biproduct T f a b hf)

end Stacks.SheafOfModules.DerivedTensorProduct

end
