module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.DerivedTensorResidueFieldSkyscraper
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.StalkLength
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback

/-!
# The direct image of a residue-field skyscraper along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and `z : Z`. This file identifies the direct
image of the residue-field skyscraper at `z` with the residue-field skyscraper at `i(z)`:

`i_* 𝒪_z ≅ 𝒪_{i(z)}`,

where `𝒪_z` denotes `AlgebraicGeometry.residueFieldSkyscraperSheaf Z z`, the skyscraper sheaf of
`𝒪_Z`-modules at `z` whose value is the residue field `κ(z)`.

## Main results

* `IsLocalRing.maximalIdeal_eq_comap_of_surjective`: for a surjective homomorphism of local rings
  the maximal ideal of the source is the preimage of the maximal ideal of the target.
* `IsLocalRing.idealResidueFieldRestrictScalarsIso`: a surjective homomorphism `φ : A → B` of
  local rings identifies `κ(𝔪_B)`, read as an `A`-module along `φ`, with `κ(𝔪_A)`.
* `AlgebraicGeometry.restrictScalarsResidueFieldStalkModuleIso`: the same identification at the
  two stalk rings of a closed immersion.
* `AlgebraicGeometry.pushforwardResidueFieldSkyscraperIso`: **the direct image of the
  residue-field skyscraper.** For a closed immersion `i : Z ⟶ X` of schemes and `z : Z`, the
  direct image `i_* 𝒪_z` is the residue-field skyscraper `𝒪_{i(z)}` on `X`.

## Implementation notes

*Where the two halves come from.* Pushing a skyscraper forward is already known in the model the
residue-field skyscraper is built in: `Stacks.RingedSpace.pushforwardSkyscraperObjIso`
identifies `f_*` of the skyscraper at `x` with value `N` with the skyscraper at `f x` whose value
is `N` read along the `RingCat`-valued germ map `Stacks.RingedSpace.stalkRingMap`, for an
arbitrary morphism of ringed spaces. So the only thing a closed immersion is needed for is the
*value*: the germ map `𝒪_{X,i(z)} → 𝒪_{Z,z}` of a closed immersion is surjective, and a
surjective homomorphism of local rings induces an isomorphism of residue fields.

*The `ideal` in the names.*  The residue field used throughout the residue-field-skyscraper
development is `Ideal.ResidueField` of the maximal ideal, not `IsLocalRing.ResidueField`; the
latter already has `IsLocalRing.residueFieldEquivOfSurjective`
(`StacksFrontier/RingTheory/LocalRing/CotangentQuotient.lean`) for a surjection of local rings, at
the other spelling. The prefix keeps the two apart.

*Why surjectivity suffices, with no locality hypothesis.* For a surjective `φ : A → B` the
preimage `φ⁻¹(𝔪_B)` is a maximal ideal of `A`, since `A ⧸ φ⁻¹(𝔪_B) ≅ B ⧸ 𝔪_B` is a field; as `A`
is local that preimage *is* `𝔪_A`. So `φ` is automatically a local homomorphism, and
`RingHom.SurjectiveOnStalks.residueFieldMap_bijective` turns `Ideal.ResidueField.map` into a ring
isomorphism. Its `A`-linearity, for the `A`-module structure that restriction of scalars along
`φ` puts on `κ(𝔪_B)`, is `Ideal.ResidueField.map_algebraMap`.

*Spellings of the structure sheaf.* Everything here is stated for the `RingCat`-valued structure
sheaf, which is what `AlgebraicGeometry.Scheme.Modules` is a category of modules over. The three
spellings `X.ringCatSheaf`, `RingedSpaceModuleAdjunction.structureSheafRing X.toRingedSpace` and
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` of that sheaf agree definitionally, and
likewise `AlgebraicGeometry.Scheme.Modules.pushforward i` and
`RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom`, as
`StacksFrontier/Topology/Sheaves/ClosedImmersion/StalkLength.lean` records; so the statements below
are about Mathlib's own direct image of modules on schemes.

No `stacks` attribute is carried: this is a step inside the proof of [Stacks, Tag 0G0R], not a
tagged result of the source.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace IsLocalRing

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  {φ : A →+* B}

/-- **A surjection of local rings is local.** For a surjective homomorphism `φ : A → B` of local
rings the maximal ideal of `A` is the preimage of the maximal ideal of `B`: the preimage is a
maximal ideal, because `A ⧸ φ⁻¹(𝔪_B)` is isomorphic to the field `B ⧸ 𝔪_B`, and a local ring has
only one maximal ideal. -/
public theorem maximalIdeal_eq_comap_of_surjective (hφ : Function.Surjective φ) :
    maximalIdeal A = (maximalIdeal B).comap φ :=
  (eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective φ hφ)).symm

/-- **A surjection of local rings is an isomorphism on residue fields.** The homomorphism
`κ(𝔪_A) → κ(𝔪_B)` induced by a surjective `φ : A → B`, which exists because `𝔪_A` is the
preimage of `𝔪_B`, is bijective: a surjective homomorphism is surjective on stalks. -/
public def idealResidueFieldEquivOfSurjective (hφ : Function.Surjective φ) :
    (maximalIdeal A).ResidueField ≃+* (maximalIdeal B).ResidueField :=
  RingEquiv.ofBijective _
    ((RingHom.surjectiveOnStalks_of_surjective hφ).residueFieldMap_bijective
      (maximalIdeal A) (maximalIdeal B) (maximalIdeal_eq_comap_of_surjective hφ))

/-- `idealResidueFieldEquivOfSurjective` is `A`-linear, for the `A`-module structure that
restriction of scalars along `φ` puts on `κ(𝔪_B)`: it sends `algebraMap A κ(𝔪_A) a` to
`algebraMap B κ(𝔪_B) (φ a)`, by `Ideal.ResidueField.map_algebraMap`, and scalar multiplication on
either side is multiplication by the image of the scalar. -/
public def idealResidueFieldLinearEquivOfSurjective (hφ : Function.Surjective φ) :
    (maximalIdeal A).ResidueField ≃ₗ[A]
      ((ModuleCat.restrictScalars.{u, u, u} φ).obj
        (ModuleCat.of B (maximalIdeal B).ResidueField)) where
  toFun := idealResidueFieldEquivOfSurjective hφ
  map_add' _ _ := map_add _ _ _
  map_smul' a x := by
    change idealResidueFieldEquivOfSurjective hφ (a • x) =
      φ a • idealResidueFieldEquivOfSurjective hφ x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * idealResidueFieldEquivOfSurjective hφ x)
      (Ideal.ResidueField.map_algebraMap _ _ φ (maximalIdeal_eq_comap_of_surjective hφ) a)
  invFun := (idealResidueFieldEquivOfSurjective hφ).symm
  left_inv := (idealResidueFieldEquivOfSurjective hφ).left_inv
  right_inv := (idealResidueFieldEquivOfSurjective hφ).right_inv

/-- **The residue field of the target of a surjection, read over the source.** For a surjective
homomorphism `φ : A → B` of local rings, the residue field `κ(𝔪_B)` with scalars restricted along
`φ` is the residue field `κ(𝔪_A)`. -/
public def idealResidueFieldRestrictScalarsIso (hφ : Function.Surjective φ) :
    (ModuleCat.restrictScalars.{u, u, u} φ).obj
        (ModuleCat.of B (maximalIdeal B).ResidueField) ≅
      ModuleCat.of A (maximalIdeal A).ResidueField :=
  (idealResidueFieldLinearEquivOfSurjective hφ).toModuleIso.symm

end IsLocalRing

namespace AlgebraicGeometry

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z)

/-- **The residue field at `z` read over the stalk at `i(z)`.** For a closed immersion
`i : Z ⟶ X` of schemes, the residue field at `z` with scalars restricted along the germ map
`𝒪_{X,i(z)} → 𝒪_{Z,z}` is the residue field at `i(z)`.

The germ map of a closed immersion is surjective — in the `CommRingCat`-valued spelling that is
`AlgebraicGeometry.Scheme.Hom.stalkMap_surjective`, and
`Stacks.ClosedImmersion.surjective_stalkRingMap_of_surjective_stalkMap` transfers it to the
`RingCat`-valued germ map the sheaf-of-modules machinery uses — so
`IsLocalRing.idealResidueFieldRestrictScalarsIso` applies. -/
public def restrictScalarsResidueFieldStalkModuleIso :
    (ModuleCat.restrictScalars.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom).obj
        (residueFieldStalkModule Z z) ≅
      residueFieldStalkModule X (i.base z) :=
  IsLocalRing.idealResidueFieldRestrictScalarsIso
    (A := ToType (StacksDraft.StalkRingComparison.stalkRing X (i.base z)))
    (B := ToType (StacksDraft.StalkRingComparison.stalkRing Z z))
    (Stacks.ClosedImmersion.surjective_stalkRingMap_of_surjective_stalkMap
      i.toLRSHom.toShHom z (i.stalkMap_surjective z))

/-- **The direct image of a residue-field skyscraper along a closed immersion.** For a closed
immersion `i : Z ⟶ X` of schemes and `z : Z`, the direct image of the skyscraper sheaf at `z`
with value the residue field `κ(z)` is the skyscraper sheaf at `i(z)` with value the residue
field `κ(i(z))`:

`i_* 𝒪_z ≅ 𝒪_{i(z)}`.

This is the identification with which the proof of Case I of [Stacks, Tag 0G0R] feeds its closed
immersion `i : Y_s ×_k Y_s ⟶ X ×_S Y` into [Stacks, Tag 0G03].

The direct image of a skyscraper is a skyscraper by
`Stacks.RingedSpace.pushforwardSkyscraperObjIso`, with its value read along the germ map; that
value is identified with the residue field at `i(z)` by
`AlgebraicGeometry.restrictScalarsResidueFieldStalkModuleIso`, and the skyscraper at `i(z)` is
functorial in its value. -/
public def pushforwardResidueFieldSkyscraperIso :
    (Scheme.Modules.pushforward i).obj (residueFieldSkyscraperSheaf Z z) ≅
      residueFieldSkyscraperSheaf X (i.base z) :=
  Stacks.RingedSpace.pushforwardSkyscraperObjIso i.toLRSHom.toShHom z
      (residueFieldStalkModule Z z) ≪≫
    (SheafOfModules.skyscraperFunctor X.ringCatSheaf (i.base z)).mapIso
      (restrictScalarsResidueFieldStalkModuleIso i z)

end AlgebraicGeometry

end
