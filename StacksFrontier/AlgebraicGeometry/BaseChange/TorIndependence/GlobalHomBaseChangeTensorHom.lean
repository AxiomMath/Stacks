module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalHomBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect
public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfectTensorFactor
public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPseudoCoherent
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison

/-!
# Moving the base-changed structure sheaf out of the derived internal Hom

For a scheme `Y` and objects `K`, `L`, `M` of `D(𝒪_Y)`, the natural map

`K ⊗^𝐋_{𝒪_Y} R𝓗om_{𝒪_Y}(M, L) ⟶ R𝓗om_{𝒪_Y}(M, K ⊗^𝐋_{𝒪_Y} L)`

of Stacks 0BYS is an isomorphism in each of the three cases of Stacks 0ATN.  For
`f : Y ⟶ Spec R` and an `R`-algebra `R'` of finite Tor dimension over `R`, the tensor factor
`Lf^*((R')^~)` of `AlgebraicGeometry.GlobalHomBaseChange.baseChangeStructureSheafComplex` falls
under case (3).

## Main results

* `AlgebraicGeometry.GlobalHomBaseChange.isIso_derivedTensorHomDiagonal_of_isPerfect`,
  `AlgebraicGeometry.GlobalHomBaseChange.isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor`
  and `AlgebraicGeometry.GlobalHomBaseChange.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent`:
  Stacks 0ATN parts (1), (2) and (3) on a scheme.
* `isIso_derivedTensorHomDiagonal_baseChangeStructureSheafComplex`: the case of the tensor factor
  `Lf^*((R')^~)`.

## References

* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.GlobalHomBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### Moving the base-changed structure sheaf out of the derived internal Hom

The natural map

`L ⊗^𝐋_{𝒪_X} R𝓗om_{𝒪_X}(M, K) ⟶ R𝓗om_{𝒪_X}(M, L ⊗^𝐋_{𝒪_X} K)`

of Stacks 0BYS is invertible in each of the two cases of Stacks 0AA7, by Stacks 0ATN, and in
case (2) the tensor factor it is applied to is the complex `Lf^*((R')^~)`, whose finite Tor
dimension is `hasFiniteTorDimension_baseChangeStructureSheafComplex`.
-/

section TensorHomDiagonal

variable (Y : Scheme.{u})

/-- **The canonical diagonal of Stacks 0BYS on the ringed space of a scheme is the one of its
ringed site.**  Both are characterised by the complex-level morphism of Stacks 0BYR between the
chosen representatives, read through the same two comparisons, and that characterisation pins
the morphism. -/
public theorem derivedTensorHomDiagonal_eq_ringedSite (K L M : DerivedCategory
    (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf)) :
    Stacks.SheafOfModules.derivedTensorHomDiagonal Y.toRingedSpace.sheaf K L M =
      RingedSite.derivedTensorHomDiagonal
        (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf) K L M :=
  RingedSite.eq_derivedTensorHomDiagonal
    (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf) K L M
    (Stacks.SheafOfModules.derivedTensorHomDiagonal_eq Y.toRingedSpace.sheaf K L M)

/-- **Stacks 0ATN part (1) on a scheme.**  For objects `K`, `L`, `M` of `D(𝒪_Y)` with `M`
perfect, the diagonal of Stacks 0BYS

`K ⊗^𝐋_{𝒪_Y} R𝓗om_{𝒪_Y}(M, L) ⟶ R𝓗om_{𝒪_Y}(M, K ⊗^𝐋_{𝒪_Y} L)`

is an isomorphism, for arbitrary `K` and `L`. -/
public theorem isIso_derivedTensorHomDiagonal_of_isPerfect (K L M : DerivedCategory
    (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf))
    (hM : (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf).IsPerfect M) :
    IsIso (Stacks.SheafOfModules.derivedTensorHomDiagonal Y.toRingedSpace.sheaf K L M) := by
  rw [derivedTensorHomDiagonal_eq_ringedSite]
  exact RingedSite.isIso_derivedTensorHomDiagonal_of_isPerfect
    (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf) K L M hM

/-- **Stacks 0ATN part (2) on a scheme.**  The diagonal of Stacks 0BYS is an isomorphism when
the tensor factor `K` is perfect, for arbitrary `L` and `M`. -/
public theorem isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor (K L M : DerivedCategory
    (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf))
    (hK : (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf).IsPerfect K) :
    IsIso (Stacks.SheafOfModules.derivedTensorHomDiagonal Y.toRingedSpace.sheaf K L M) := by
  rw [derivedTensorHomDiagonal_eq_ringedSite]
  exact RingedSite.isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor
    (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf) K L M hK

/-- **Tor amplitude of Stacks 08CG read against the derived tensor product of the ringed site.**
The Tor amplitude of a ringed space is measured against
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, indexed by the structure sheaf,
while the statements of Stacks 0ATN measure finite Tor dimension against
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, indexed by the ringed site.  The two are
the same quantified statement over two constructions of the derived tensor product of Stacks 06YU,
each made opaque with `irreducible_def`, and `AlgebraicGeometry.RingedSite.derivedTensorObjIso`
identifies their bifunctors at every pair of objects, so the two notions agree term by term in the
test module. -/
public theorem hasTorAmplitude_ringedSite (E : DerivedCategory
    (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf)) (a b : ℤ)
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace E a b) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf)) E a b := by
  intro F i hi
  exact (h F i hi).of_iso
    ((DerivedCategory.homologyFunctor
        (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf) i).mapIso
      (RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf) E
        ((DerivedCategory.singleFunctor
          (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf) 0).obj F)))

/-- **Finite Tor dimension of Stacks 08CG read against the derived tensor product of the ringed
site**, `hasTorAmplitude_ringedSite` quantified over the interval. -/
public theorem hasFiniteTorDimension_ringedSite (E : DerivedCategory
    (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf))
    (h : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension Y.toRingedSpace E) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf)) E :=
  let ⟨a, b, hab⟩ := h
  ⟨a, b, hasTorAmplitude_ringedSite Y E a b hab⟩

/-- **Stacks 0ATN part (3) on a scheme**, with the Tor-dimension hypothesis stated in the
vocabulary of Stacks 08CG on the ringed space.  For objects `K`, `L`, `M` of `D(𝒪_Y)` with `M`
pseudo-coherent, `L` cohomologically bounded below and the tensor factor `K` of finite Tor
dimension, the diagonal of Stacks 0BYS is an isomorphism. -/
public theorem isIso_derivedTensorHomDiagonal_of_isPseudoCoherent (K L M : DerivedCategory
    (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf))
    (hM : (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf).IsPseudoCoherent M)
    (hL : DerivedCategoryB.IsBoundedBelow L)
    (hK : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension Y.toRingedSpace K) :
    IsIso (Stacks.SheafOfModules.derivedTensorHomDiagonal Y.toRingedSpace.sheaf K L M) := by
  rw [derivedTensorHomDiagonal_eq_ringedSite]
  exact RingedSite.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent
    (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf) K L M hM hL
    (hasFiniteTorDimension_ringedSite Y K hK)

/-- **Moving `Lf^*((R')^~)` out of a derived internal Hom.**  Let `f : Y ⟶ Spec R`, let
`R'` be an `R`-algebra of finite Tor dimension over `R`, let `M` be a pseudo-coherent object of
`D(𝒪_Y)` and let `K` be cohomologically bounded below.  Then the diagonal of Stacks 0BYS

`Lf^*((R')^~) ⊗^𝐋_{𝒪_Y} R𝓗om_{𝒪_Y}(M, K) ⟶ R𝓗om_{𝒪_Y}(M, Lf^*((R')^~) ⊗^𝐋_{𝒪_Y} K)`

is an isomorphism.

For the cartesian square over `g = Spec(φ)` the tensor factor is `g'_*𝒪_{Y'}`, by Stacks 08IB;
its finite Tor dimension is `hasFiniteTorDimension_baseChangeStructureSheafComplex`, and the
statement is then Stacks 0ATN part (3). -/
public theorem isIso_derivedTensorHomDiagonal_baseChangeStructureSheafComplex
    (R R' : CommRingCat.{u}) (φ : R ⟶ R') (f : Y ⟶ Spec R)
    (hφ : StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical R (algebraComplex R R' φ))
    (K M : DerivedCategory
      (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf))
    (hM : (Stacks.SheafOfModules.ringedSite Y.toRingedSpace.sheaf).IsPseudoCoherent M)
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    IsIso (Stacks.SheafOfModules.derivedTensorHomDiagonal Y.toRingedSpace.sheaf
      (baseChangeStructureSheafComplex R R' φ f) K M) :=
  isIso_derivedTensorHomDiagonal_of_isPseudoCoherent Y _ K M hM hK
    (hasFiniteTorDimension_baseChangeStructureSheafComplex R R' φ f hφ)

end TensorHomDiagonal

end AlgebraicGeometry.GlobalHomBaseChange

end
