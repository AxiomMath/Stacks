module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldVersalLift
public import StacksFrontier.Deformation.Artin.Versality.DualNumbersIsomorphismClasses

/-!
# The two presentations of the dual numbers agree

The dual numbers `k[ε]` occur in the deformation-theoretic part of the library under two
descriptions, built for two different purposes and never yet compared.

* `Deformation.artinianDualNumbers` is the value of the square-zero-extension functor
  `Deformation.squareZeroExtensionArtinian` at the one-dimensional vector space
  `FGModuleCat.of k (ULift k)`. The `ULift` is there so that the functor can take the
  vector-space universe to be independent of the field's; the `Λ`-algebra structure is the one
  `TrivSqZeroExt` carries for a module with compatible scalar towers.
* `Deformation.Artin.squareZeroArtinianObj` is the trivial square-zero extension as the
  Artin site forms it, `Deformation.Artin.squareZeroRing` applied to a `ModuleCat`, with the
  `Λ`-algebra structure declared by hand as `RingHom.toAlgebra` of the composite
  `Λ ⟶ k ⟶ k[M]`. At `M = ModuleCat.of k k` it is the dual numbers again.

This file exhibits the isomorphism of `Deformation.ArtinianLocalAlgCat Λ k` between them, so
that a statement proved at one presentation can be moved to the other — the intended consumer
being `Deformation.surjective_mapIsomorphismClasses_of_iso`, which transports surjectivity of
`Deformation.mapIsomorphismClasses` along exactly such an isomorphism of the Artinian point.

## Main definitions

* `Deformation.Artin.artinianDualNumbersAlgEquiv` — the underlying `Λ`-algebra isomorphism.
* `Deformation.Artin.artinianDualNumbersIso` — the isomorphism of
  `Deformation.ArtinianLocalAlgCat Λ k`.

## Main results

* `Deformation.Artin.surjective_mapIsomorphismClasses_squareZeroArtinianObj_of_artinianDualNumbers`
  and its converse
  `Deformation.Artin.surjective_mapIsomorphismClasses_artinianDualNumbers_of_squareZeroArtinianObj`
  — surjectivity of `Deformation.mapIsomorphismClasses` passes between the two presentations.

## Implementation notes

The two `Λ`-algebra structures on the carrier are *not* the same instance:
`RingHom.toAlgebra` defines `r • x` to be `algebraMap r * x`, whereas the structure
`TrivSqZeroExt` carries acts componentwise. They agree on `algebraMap`, which is all an
`AlgEquiv` asks of them, so the comparison is stated as an `AlgEquiv` over `Λ` and the
algebra instances are the ones the two objects already carry — nothing is rebuilt.

The two right actions of `k` that the two square-zero extensions are formed with are both
`Module.compHom` along the unopposing map, `Deformation.Artin.oppositeModule` on the site side
and a `local instance` of the same shape inside
`StacksFrontier.Deformation.TangentSpace.Functor` on the other. That is why the ring structures
match definitionally and the multiplicative part of the comparison needs no `mul_comm`: had
either side picked up `Semiring.toOppositeModule` instead, the two rings would multiply the
module component on opposite sides. Keeping `M` abstract in
`Deformation.Artin.squareZeroArtinianObj` is what pins the site's instance; see the
implementation note there.

The underlying map is the `ULift` isomorphism on the module component, so each of the
structure fields of the `AlgEquiv` holds by `rfl`.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u u₁ v₁ u₂ v₂

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The comparison -/

/-- The two presentations of the dual numbers `k[ε]` are isomorphic as `Λ`-algebras: the
square-zero extension by `ULift k` that `Deformation.squareZeroExtensionArtinian` forms and
the one by `ModuleCat.of k k` that the Artin site forms differ only by `ULift.down` on the
module component. -/
public def artinianDualNumbersAlgEquiv :
    (Deformation.artinianDualNumbers.{u, u, u} Λ k) ≃ₐ[Λ]
      (squareZeroArtinianObj Λ k (ModuleCat.of k k)) where
  toFun x := ⟨x.fst, x.snd.down⟩
  invFun x := ⟨x.fst, ULift.up x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The comparison of the two presentations preserves the first coordinate, which is the
coordinate both of them read their residue field off. -/
public theorem artinianDualNumbersAlgEquiv_fst
    (x : Deformation.artinianDualNumbers.{u, u, u} Λ k) :
    TrivSqZeroExt.fst (artinianDualNumbersAlgEquiv x) = TrivSqZeroExt.fst x := rfl

/-- The two presentations of the dual numbers are isomorphic as objects of `𝒞_Λ`. Both record
their residue field through the first projection, which
`Deformation.Artin.artinianDualNumbersAlgEquiv_fst` preserves. -/
public def artinianDualNumbersIso :
    Deformation.artinianDualNumbers.{u, u, u} Λ k ≅
      squareZeroArtinianObj Λ k (ModuleCat.of k k) where
  hom :=
    { hom := artinianDualNumbersAlgEquiv.toAlgHom
      isLocal := isLocalHom_toRingHom artinianDualNumbersAlgEquiv
      residue_comm := fun _ ↦ rfl }
  inv :=
    { hom := artinianDualNumbersAlgEquiv.symm.toAlgHom
      isLocal := isLocalHom_toRingHom artinianDualNumbersAlgEquiv.symm
      residue_comm := fun _ ↦ rfl }
  hom_inv_id := Deformation.ArtinianLocalAlgCat.hom_ext
    (AlgHom.ext artinianDualNumbersAlgEquiv.symm_apply_apply)
  inv_hom_id := Deformation.ArtinianLocalAlgCat.hom_ext
    (AlgHom.ext artinianDualNumbersAlgEquiv.apply_symm_apply)

/-! ### Transporting surjectivity of the map on isomorphism classes -/

section Transport

variable {𝓕 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)}
  (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
  (φ : BasedFunctor 𝓕 𝓖)

/-- Surjectivity of `Deformation.mapIsomorphismClasses` at the dual numbers as the Artin site
forms them follows from surjectivity at the square-zero-extension presentation. -/
public theorem surjective_mapIsomorphismClasses_squareZeroArtinianObj_of_artinianDualNumbers
    (h : Function.Surjective (Deformation.mapIsomorphismClasses h𝓕 h𝓖 φ
      (Deformation.artinianDualNumbers.{u, u, u} Λ k))) :
    Function.Surjective (Deformation.mapIsomorphismClasses h𝓕 h𝓖 φ
      (squareZeroArtinianObj Λ k (ModuleCat.of k k))) :=
  Deformation.surjective_mapIsomorphismClasses_of_iso h𝓕 h𝓖 φ artinianDualNumbersIso h

/-- Surjectivity of `Deformation.mapIsomorphismClasses` at the square-zero-extension
presentation of the dual numbers follows from surjectivity at the site's presentation. -/
public theorem surjective_mapIsomorphismClasses_artinianDualNumbers_of_squareZeroArtinianObj
    (h : Function.Surjective (Deformation.mapIsomorphismClasses h𝓕 h𝓖 φ
      (squareZeroArtinianObj Λ k (ModuleCat.of k k)))) :
    Function.Surjective (Deformation.mapIsomorphismClasses h𝓕 h𝓖 φ
      (Deformation.artinianDualNumbers.{u, u, u} Λ k)) :=
  Deformation.surjective_mapIsomorphismClasses_of_iso h𝓕 h𝓖 φ
    artinianDualNumbersIso.symm h

end Transport

end Deformation.Artin
