module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIsoGeneral
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public noncomputable section

/-!
# Derived extension of scalars followed by a derived tensor product, with explicit structure

Let `f : R →+* A` be a homomorphism of commutative rings and let `ω` be an object of `D(A)`. This
file assembles the functor

`Ψ : D(R) ⥤ D(A)`, `Ψ = (- ⊗ᴸ_R A) ⋙ (- ⊗ᴸ_A ω)`

and equips it with the three properties that the compact-generator dévissage of
`StacksFrontier/Homology/Devissage/CompactGeneratedNatTransLocallySmall.lean` asks of its two
functors: a commutation with the shift, exactness, and preservation of direct sums indexed by the
module universe.

All three are *explicit*: nothing here is a field of a structure obtained by `Classical.choice`, so
every one of them may be unfolded and computed with. That is the point of the file. The derived
change-of-rings tensor product of [stacks 06Y6] is available as
`CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings`, but that construction is
`Classical.choice` of a `Nonempty` witness, so its own `Functor.CommShift` carries no coherence
with anything and cannot be fed to a dévissage. The two factors used here carry theirs by
construction:

* the shift datum and the exactness of derived extension of scalars are the fields
  `commShift` and `isTriangulated` of
  `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`, which is a structure the
  caller supplies and whose existence is
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars_exists`;
* those of the derived tensor product with a fixed object in the second variable are the instances
  `CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral_left_commShift` and
  `..._left_isTriangulated`, transported from the derived tensor product over `ULift.{v} A` along
  the scalar equivalence.

Direct sums are the only one of the three that is new. Both factors are *left adjoints*, and a
left adjoint preserves every colimit:

* derived extension of scalars is left adjoint to derived restriction of scalars by [stacks 0GMT],
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`, which applies to any
  model carrying the total-left-derived universal property and so to the supplied structure;
* tensoring with a fixed object is left adjoint to the internal derived Hom out of that object.
  The adjunction is not recorded anywhere as an `CategoryTheory.Adjunction`; what the library has
  is the field `homEquiv` of `StacksDraft.DerivedHom.DerivedHomAdjunction` together with its two
  naturality fields, which is exactly the data of `CategoryTheory.Adjunction.mkOfHomEquiv`. That
  is `derivedTensorFlipAdjunction`.

The two tensor products then have to be reconciled: `homEquiv` is a field of the tensor--Hom
adjunction of [stacks 0A63] and the shift data above belong to the derived tensor product of
[stacks 068I]. `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` identifies the two bifunctors,
and `derivedTensorFlipIso` is its value in the second variable at a fixed object.

## Main definitions

* `StacksDraft.CompactDevissage.derivedTensorFlipAdjunction` — tensoring with a fixed object in
  the second variable is a left adjoint.
* `StacksDraft.CompactDevissage.derivedTensorFlipIso` — the two spellings of that functor agree.
* `StacksDraft.CompactDevissage.derivedExtensionTensor` — the functor `Ψ`.

## Main results

* `StacksDraft.CompactDevissage.preservesColimitsOfShape_derivedTensorFlip` — the derived tensor
  product with a fixed object preserves all colimits of a given shape.
* `StacksDraft.CompactDevissage.derivedExtensionTensor_commShift`,
  `..._isTriangulated`, `..._preservesColimitsOfShape` — the three dévissage hypotheses for `Ψ`.

## References

* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [The Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace StacksDraft.CompactDevissage

section TensorFlip

variable (A : Type u) [CommRing A]

/-- **Tensoring with a fixed object in the second variable is a left adjoint.** For the canonical
tensor--Hom adjunction of [stacks 0A63] over the ring, the functor `K ↦ K ⊗ᴸ L` is left adjoint to
the internal derived Hom `M ↦ RHom(L, M)`.

The data is already present in `StacksDraft.DerivedHom.DerivedHomAdjunction`: its field `homEquiv`
is the bijection the adjunction needs, and its fields `homEquiv_naturality_left` and
`homEquiv_naturality_right` are the two naturality conditions of
`CategoryTheory.Adjunction.mkOfHomEquiv`. Only the right-hand naturality has to be transposed,
since the structure states it for the forward direction of `homEquiv` and the adjunction asks for
it in the backward direction. -/
@[sga "4½ Etat_0 6.2" "special case", sga "5 IIIB 5.2" "special case"]
def derivedTensorFlipAdjunction (L : DerivedCategory (ModuleCat.{max u v} A)) :
    (Functor.curry.obj
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} A).tensor).flip.obj L ⊣
      (Functor.curry.obj
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} A).hom).obj (Opposite.op L) :=
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (d.homEquiv X L Y).toEquiv.symm
      homEquiv_naturality_left_symm := fun g a => d.homEquiv_naturality_left g a
      homEquiv_naturality_right := by
        intro X Y Y' a g
        apply (d.homEquiv X L Y').injective
        simpa using (d.homEquiv_naturality_right g ((d.homEquiv X L Y).symm a)).symm }

/-- The comparison from the derived tensor product of [stacks 068I] with a fixed object in the
second variable to the tensor of the tensor--Hom adjunction of [stacks 0A63], as a natural
transformation: the value of `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` at a pair whose
second entry is held fixed. -/
def derivedTensorFlipNatTrans (L : DerivedCategory (ModuleCat.{max u v} A)) :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral.{u, v} A).flip.obj L ⟶
      (Functor.curry.obj
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} A).tensor).flip.obj L where
  app X := (Dualizing.derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom.app (X, L)
  naturality X Y g := by
    simpa [CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral] using
      (Dualizing.derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom.naturality
        (Prod.mkHom g (𝟙 L))

/-- `StacksDraft.CompactDevissage.derivedTensorFlipNatTrans` is an isomorphism: it is the
restriction to a slice of the isomorphism of bifunctors
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral`. -/
def derivedTensorFlipIso (L : DerivedCategory (ModuleCat.{max u v} A)) :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral.{u, v} A).flip.obj L ≅
      (Functor.curry.obj
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} A).tensor).flip.obj L where
  hom := derivedTensorFlipNatTrans.{u, v} A L
  inv :=
    { app X := (Dualizing.derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).inv.app (X, L)
      naturality X Y g := by
        simp [CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral] }
  hom_inv_id := by
    ext X
    exact (Dualizing.derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom_inv_id_app (X, L)
  inv_hom_id := by
    ext X
    exact (Dualizing.derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).inv_hom_id_app (X, L)

/-- **The derived tensor product with a fixed object in the second variable preserves every
colimit.** Being a right adjoint, the internal derived Hom gives no colimit preservation at all;
it is the *left* adjointness of `- ⊗ᴸ L`, which
`StacksDraft.CompactDevissage.derivedTensorFlipAdjunction` supplies from the `homEquiv` field of
the tensor--Hom adjunction, that does. In particular the direct sums indexed by the module
universe, which is what the compact-generator dévissage asks for, are preserved. -/
instance preservesColimitsOfShape_derivedTensorFlip
    (L : DerivedCategory (ModuleCat.{max u v} A)) (J : Type*) [Category J] :
    PreservesColimitsOfShape J
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral.{u, v}
        A).flip.obj L) :=
  have : ((CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral.{u, v}
      A).flip.obj L).IsLeftAdjoint :=
    (Adjunction.ofNatIsoLeft (derivedTensorFlipAdjunction.{u, v} A L)
      (derivedTensorFlipIso.{u, v} A L).symm).isLeftAdjoint
  inferInstance

end TensorFlip

section ExtensionTensor

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **The functor `Ψ = (- ⊗ᴸ_R A) ⋙ (- ⊗ᴸ_A ω)`.** Derived extension of scalars along `f`, for a
supplied total left derived model `E`, followed by the derived tensor product over `A` with a
fixed object `ω` of `D(A)`.

Both factors carry their shift datum and their exactness explicitly, so `Ψ` does too; see the
module documentation for why the derived change-of-rings tensor product of [stacks 06Y6] does
not. -/
def derivedExtensionTensor (f : R →+* A)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u} f)
    (ω : DerivedCategory (ModuleCat.{max v u} A)) :
    DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} A) :=
  E.functor ⋙
    (CochainComplex.DerivedTensor.canonicalDerivedTensorFunctorGeneral.{u, v} A).flip.obj ω

/-- `Ψ` commutes with the shift: both factors do, and the datum is the composite one. -/
instance derivedExtensionTensor_commShift (f : R →+* A)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u} f)
    (ω : DerivedCategory (ModuleCat.{max v u} A)) :
    (derivedExtensionTensor.{u, v} f E ω).CommShift ℤ := by
  dsimp only [derivedExtensionTensor]
  infer_instance

/-- `Ψ` is an exact functor of triangulated categories, for the composite shift datum. -/
instance derivedExtensionTensor_isTriangulated (f : R →+* A)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u} f)
    (ω : DerivedCategory (ModuleCat.{max v u} A)) :
    (derivedExtensionTensor.{u, v} f E ω).IsTriangulated := by
  dsimp only [derivedExtensionTensor]
  infer_instance

/-- **`Ψ` preserves every colimit, in particular the direct sums indexed by the module
universe.** Both factors are left adjoints: derived extension of scalars by [stacks 0GMT], which
applies to the supplied model because it carries the total-left-derived universal property, and
the derived tensor product with a fixed object by
`StacksDraft.CompactDevissage.preservesColimitsOfShape_derivedTensorFlip`. -/
instance derivedExtensionTensor_preservesColimitsOfShape (f : R →+* A)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u} f)
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (J : Type*) [Category J] :
    PreservesColimitsOfShape J (derivedExtensionTensor.{u, v} f E ω) := by
  have hE : E.functor ⊣ (ModuleCat.restrictScalars.{max v u, u, u} f).mapDerivedCategory :=
    @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
      R A _ _ f _ _ E.functor E.comparison E.isLeftDerived
  have : E.functor.IsLeftAdjoint := hE.isLeftAdjoint
  dsimp only [derivedExtensionTensor]
  infer_instance

end ExtensionTensor

end StacksDraft.CompactDevissage

end
