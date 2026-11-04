module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-!
# Derived tensor products of bounded above complexes with constructible cohomology

Let `X` be a scheme and `Λ` a Noetherian ring. Stacks Tag 0961 asserts that for `K` and `L` in
`D_c^-(X_étale, Λ)` the derived tensor product `K ⊗_Λ^L L` is again in `D_c^-(X_étale, Λ)`: it
is bounded above and its cohomology sheaves are constructible.

The conclusion has two halves. Boundedness above is the estimate `K ⊗^L L` lies in degrees
`≤ a + b` when `K` lies in degrees `≤ a` and `L` in degrees `≤ b`. Constructibility of the
cohomology sheaves reduces to the case of bounded `K` and `L`, by replacing `K` and `L` in
degree `i` by the bounded truncations `τ^{> i-b-1}K` and `τ^{> i-a-1}L`, which compute `H^i` of
the derived tensor product because the same estimate puts the two error terms in degrees
`≤ i - 1`.

This file proves **both halves**, the second one reduced to the bounded case; see
"What is not proved".

## Main results

* `Stacks.EtaleCohomology.minus_derivedTensor`: **Tag 0961, boundedness above** — the derived
  tensor product of two bounded above objects is bounded above.
* `Stacks.EtaleCohomology.isConstructible_derivedTensor`: **Tag 0961, the reduction of the
  constructible cohomology of `K ⊗^L_Λ L` to the case of bounded `K` and `L`.**

## Implementation notes

`D_c(X_étale, Λ)` is the predicate `Stacks.EtaleCohomology.IsConstructible` of Tag 095W, and
boundedness above is membership in the negative part
`CategoryTheory.Triangulated.TStructure.minus` of the canonical t-structure, as in
`CategoryTheory.DerivedCategory.Minus`; the conjunction of the two is membership in
`D_c^-(X_étale, Λ)`, which this development does not name as a subcategory of its own.

The derived tensor product enters as an abstract bifunctor `T` on
`D(X_étale, Λ)`, exact in each variable, together with the hypothesis
`hbound : K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b)`. This is the generality of
`Stacks.ConstantSheaf.prop_homology_of_isLE_add`, which the reduction instantiates, and it is
forced: the derived tensor product of this development,
`Stacks.SheafOfModules.DerivedTensorProduct`, is a bifunctor on the derived category of sheaves
of modules over a *ring sheaf* on a ringed site, whereas constructibility is a property of
`ModuleCat`-valued sheaves, and the comparison of the two derived categories along
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor` — the content of Tag 094H's
transport — is not available here. Exactness in each variable is a field of that structure, and
`hbound` for it is
`Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor`, so a client with the transport in hand
owes neither.

The constructible sheaves of `Λ`-modules are a weak Serre subcategory of all of them by Tag
03RZ (3), `AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf`; the
reduction uses only that this property contains zero and is closed under isomorphism, both of
which are part of that class. That theorem is available at coefficient universe
`ModuleCat.{max (u + 1) w} Λ`, which is therefore the universe here, as in
`Stacks.EtaleCohomology.isConstructible_derivedPullback` for Tag 095Y: the small étale site has
objects in `Type (u + 1)` and morphisms in `Type u`, so `max (u + 1) w` is the smallest
coefficient universe receiving the colimits that compute an inverse image to a stratum.

## What is not proved

The **bounded case** is not proved, so Tag 0961 is not proved. The source derives the bounded
case from Tag 0960: on a quasi-compact quasi-separated scheme a bounded above object of
`D_c(X_étale, Λ)` has a bounded above representative whose terms are *flat* constructible
sheaves, and such a representative computes the derived tensor product as the ordinary total
tensor complex, whose terms are constructible by Tag 095I,
`Stacks.EtaleCohomology.isConstructibleModuleSheaf_tensor`, and whose cohomology sheaves are
then constructible because Tag 03RZ (3) is a weak Serre condition. Tag 0960 is not formalized in
this library, in any form: neither the flat constructible representative nor the equivalent
statement for finite sums of extensions by zero of the constant sheaf from affine étale objects.

Equivalently, and more atomically, what is missing is that the sheaves `Tor_j^Λ(F, G)` are
constructible for `F` and `G` constructible, which is what the bounded case reduces to by
dévissage along the truncation triangles — the weak Serre property of Tag 03RZ (3) propagates
the conclusion along the long exact sequences. Over a Noetherian `Λ` this holds because on a
stratification both sheaves are locally constant with finitely generated values and `Tor` of two
finitely generated modules over a Noetherian ring is finitely generated; none of that is
formalized here either. Tag 095I is the case `j = 0` and is the only case available.

## References

* [Stacks Project, Tag 0961](https://stacks.math.columbia.edu/tag/0961)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 095I](https://stacks.math.columbia.edu/tag/095I)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)]

variable (T : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))

/-- **Stacks 0961, boundedness above.** If `K` and `L` are bounded above objects of the derived
category of small-étale sheaves of `Λ`-modules and the bifunctor `T` carries degrees `≤ a` and
`≤ b` to degrees `≤ a + b`, then `(T.obj K).obj L` is bounded above. For the derived tensor
product this is `K ⊗_Λ^L L ∈ D^-(X_étale, Λ)`.

Neither constructibility nor Noetherian-ness of `Λ` enters: this half of the conclusion is the
boundedness estimate on a single pair of degrees. -/
theorem minus_derivedTensor
    (hbound : ∀ (K L : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) (a b : ℤ), K.IsLE a → L.IsLE b →
      ((T.obj K).obj L).IsLE (a + b))
    (K L : DerivedCategory.Minus (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))) :
    (DerivedCategory.TStructure.t (C := Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).minus ((T.obj K.obj).obj L.obj) := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  exact ⟨a + b, hbound K.obj L.obj a b ha hb⟩

variable [IsNoetherianRing Λ]
  [∀ (S S' : B.Scheme) (f : S' ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B S'.obj S'.property)).IsRightAdjoint]
  [∀ (S : B.Scheme) (V : SmallEtale B S.obj S.property),
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]
  [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
  [∀ L, (T.flip.obj L).CommShift ℤ] [∀ L, (T.flip.obj L).IsTriangulated]

/-- **Stacks 0961, the reduction of the constructible half to the bounded case.** Let `T` be a
bifunctor on the derived category of small-étale sheaves of `Λ`-modules which is exact in each
variable and carries degrees `≤ a` and `≤ b` to degrees `≤ a + b`. If `(T.obj K).obj L` has
constructible cohomology sheaves for bounded `K` and `L` with constructible cohomology sheaves,
then so it does for `K` and `L` merely bounded above.

In degree `i` the two factors may be replaced by the bounded truncations `τ^{> i-b-1}K` and
`τ^{> i-a-1}L`, since the boundedness estimate puts both error terms in degrees `≤ i - 1`, where
they do not contribute to `H^i`. Propagating constructibility through that replacement needs
only that it contains zero and is closed under isomorphism, both consequences of the weak Serre
property of Tag 03RZ (3). -/
theorem isConstructible_derivedTensor
    (hbound : ∀ (K L : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) (a b : ℤ), K.IsLE a → L.IsLE b →
      ((T.obj K).obj L).IsLE (a + b))
    (hbounded : ∀ K L : DerivedCategory.Bounded
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)),
      IsConstructible B X Λ K.obj → IsConstructible B X Λ L.obj →
        IsConstructible B X Λ ((T.obj K.obj).obj L.obj))
    (K L : DerivedCategory.Minus (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B X Λ K.obj) (hL : IsConstructible B X Λ L.obj) :
    IsConstructible B X Λ ((T.obj K.obj).obj L.obj) :=
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, w, r} B X Λ
  Stacks.ConstantSheaf.prop_homology_of_isLE_add T
    (fun F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ) =>
      IsConstructibleModuleSheaf B X Λ F)
    hbound hbounded K L hK hL

end Stacks.EtaleCohomology

end
