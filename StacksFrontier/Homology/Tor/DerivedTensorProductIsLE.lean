module

public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorBoundedAbove

/-!
# Right t-exactness of a derived tensor product of `D(R)`

`CochainComplex.DerivedTensor.isLE_of_kFlatComparison` bounds any object which is compared with
the termwise tensor product of K-flat representatives.  The `comparison` field of
`CochainComplex.DerivedTensor.DerivedTensorProduct` is exactly such a comparison, so the bound
holds for every derived tensor product in that sense, and in particular for the canonical one of
[stacks 0BYI] — with **no lower bound on either factor**, so that `K ⊗ᴸ -` is way-out right
exact, the hypothesis of `StacksDraft.ExtremalDegrees.isLE_map_of_homology_of_wayOut`.

## Main results

* `CochainComplex.DerivedTensor.isLE_tensor` — for an arbitrary derived tensor product of
  `D(R)`: the tensor product of an object of `D^{≤ a}` and an object of `D^{≤ b}` lies in
  `D^{≤ a + b}`.
* `CochainComplex.DerivedTensor.isLE_canonicalDerivedTensorProduct` — the same for the canonical
  derived tensor product of [stacks 0BYI].
* `CochainComplex.DerivedTensor.wayOut_tensor` — the bound in the shape of the way-out
  hypothesis: for `K` in `D^{≤ p}`, the functor `K ⊗ᴸ -` carries `D^{≤ m}` into `D^{≤ m + p}`
  for every `m`.

## References

* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u

variable {R : Type u} [CommRing R]

/-- **A derived tensor product of `D(R)` is right t-exact in both variables**: the tensor
product of an object of `D^{≤ a}(R)` with an object of `D^{≤ b}(R)` lies in `D^{≤ a + b}(R)`.
Neither factor is assumed bounded below. -/
theorem isLE_tensor (T : DerivedTensorProduct R) (K L : DObj R) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] : ((T.tensor.obj K).obj L).IsLE (a + b) :=
  isLE_of_kFlatComparison.{u, u} ((T.tensor.obj K).obj L) K L a b
    fun P Q eP eQ hP hQ => ⟨(T.tensor.mapIso eP).app L ≪≫
      (T.tensor.obj (DerivedCategory.Q.obj P)).mapIso eQ ≪≫ T.comparison P Q hP hQ⟩

/-- **The canonical derived tensor product of [stacks 0BYI] is right t-exact in both
variables**, with no lower bound on either factor. -/
theorem isLE_canonicalDerivedTensorProduct (K L : DObj R) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] :
    (((canonicalDerivedTensorProduct R).tensor.obj K).obj L).IsLE (a + b) :=
  isLE_tensor (canonicalDerivedTensorProduct R) K L a b

/-- **`K ⊗ᴸ -` is way-out right exact with slack `p`, for `K` in `D^{≤ p}`.**  This is
`CochainComplex.DerivedTensor.isLE_tensor` written in the shape
`StacksDraft.ExtremalDegrees.isLE_map_of_homology_of_wayOut` asks its functor for: a single `p`
such that `D^{≤ m}` lands in `D^{≤ m + p}` for every `m`, with no lower bound anywhere. -/
theorem wayOut_tensor (T : DerivedTensorProduct R) (K : DObj R) (p : ℤ) (hK : K.IsLE p)
    (L : DObj R) (m : ℤ) (hL : L.IsLE m) : ((T.tensor.obj K).obj L).IsLE (m + p) := by
  have := hK
  have := hL
  have := isLE_tensor T K L p m
  exact DerivedCategory.TStructure.t.isLE_of_le _ (p + m) (m + p) (by omega)

end CochainComplex.DerivedTensor

end
