module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksCore.Tactic.StacksAttribute

/-!
# Picard classes of pullbacks

Let `φ : X ⟶ Y` be a morphism of schemes and let `L` be an invertible `𝒪_Y`-module. Then `φ^*L`
is an invertible `𝒪_X`-module (Tag 0B8L), so it has a class in `Pic(X)`. This file records that
class and the computation rules it obeys: it depends only on the isomorphism class of `L`, it is
additive in `L` for the tensor product (Tag 01CD), it kills the structure sheaf, and it turns a
composite of morphisms into an iterated pullback.

Together these say that `L ↦ [φ^*L]` is the composite of a pullback homomorphism
`Pic(Y) ⟶ Pic(X)` with the class map, but they are stated one at a time rather than through
such a homomorphism. The homomorphism cannot be obtained here from the monoidal functoriality
of `φ^*`: the monoidal structure on sheaves of modules that
`Stacks.PullbackMonoidalSheaf.pullbackMonoidal` is stated for localises the unit comparison at
`Stacks.SheafOfModules.sheafifyUnitIso`, whereas the one
`Stacks.SheafPicardGroup.classMonoidHom` consumes localises it at `Iso.refl`, so the two have
different unit objects and a `Functor.Monoidal` structure for one is not one for the other. The
rules below mention no monoidal structure at all and so are free of that mismatch.

## Main definitions

* `Stacks.SheafOfModules.schemeTensor`: the tensor product sheaf on a scheme, in the spelling
  the Picard group is stated at.
* `Stacks.SheafOfModules.pullbackPicardClass`: the class in `Pic(X)` of the pullback along
  `φ : X ⟶ Y` of an invertible `𝒪_Y`-module.

## Main results

* `Stacks.SheafOfModules.pullbackPicardClass_congr`: isomorphic modules have the same pullback
  class.
* `Stacks.SheafOfModules.pullbackPicardClass_comp`: the class for a composite `φ ≫ ψ` is the
  class for `φ` of the pullback along `ψ`.
* `Stacks.SheafOfModules.pullbackPicardClass_tensorSheaf`: the pullback class is additive for
  the tensor product sheaf.
* `Stacks.SheafOfModules.pullbackPicardClass_id`: the pullback class along the identity is the
  Picard class.
* `Stacks.SheafOfModules.pullbackPicardClass_unit`: the pullback class of the structure sheaf
  vanishes.
* `Stacks.SheafOfModules.picardClass_eq_neg_of_isTrivial_tensorSheaf` and
  `Stacks.SheafOfModules.pullbackPicardClass_eq_neg_of_isTrivial_tensorSheaf`: two invertible
  modules whose tensor product is trivial have opposite classes, and opposite pullback
  classes.
* `Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf`: an invertible module has an
  invertible tensor inverse.
* `Stacks.SheafOfModules.picardClass_schemeTensor₃`, `picardClass_schemeTensor₄`,
  `pullbackPicardClass_schemeTensor₃` and `pullbackPicardClass_schemeTensor₄`: the class, and
  the pullback class, of a three- or four-fold left-nested tensor product.
* `Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff`: the pullback class vanishes exactly
  when the pullback is trivial.

## Implementation notes

Invertibility is carried as an explicit argument, not as an instance. Instance search cannot
supply it: the invertibility classes of the library are keyed on
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`, while the sheaves produced by
`RingedSpaceModuleAdjunction.modulePullback` live over `Stacks.RingedSpace.ringSheaf X`, and
`structureSheafRing` is a plain `def`. The two are equal by `rfl`, but instance search runs at
reducible transparency and so does not cross that boundary: `inferInstance` does not find
`IsInvertible X.presheaf X.ringCatIsSheaf` for the unit module
`SheafOfModules.unit (structureSheafRing X.toRingedSpace)` even though
`Stacks.SheafOfModules.isInvertible_unit` is an instance, and likewise for the tensor product
sheaf of two modules of that type. Elaboration of an explicit argument unfolds at default
transparency and crosses it.

Because the argument is a proof of a `Prop`, two spellings of it are definitionally equal, so
no rewrite below is sensitive to which one is supplied; the hypothesis slots may be left as `_`
in a `rw` and are solved by matching.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- `M ⊗_{𝒪_X} N`, for sheaves of modules on a scheme, in the spelling the Picard group is
stated at. -/
noncomputable abbrev schemeTensor (X : Scheme.{u})
    (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
      (X.ringCatIsSheaf)⟩).obj (M)).obj (N))

variable {X Y Z : Scheme.{u}}

/-- **The class in `Pic(X)` of the pullback of an invertible `𝒪_Y`-module along `φ : X ⟶ Y`.**
The pullback is invertible by Stacks Tag 0B8L. -/
@[ega "0 5.4.8" "partial"]
noncomputable def pullbackPicardClass (φ : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L) :
    Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf :=
  haveI := hL
  Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
    ((modulePullback φ.toLRSHom.toShHom).obj L)
    (Stacks.RingedSpace.modulePullback_isInvertible _ L)

/-- The tensor product sheaf of two invertible modules on a scheme is invertible, Stacks
Tag 01CT, with the invertibility hypotheses explicit. -/
theorem isInvertible_schemeTensor (X : Scheme.{u})
    (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf (schemeTensor X M N) :=
  have := hM
  have := hN
  Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf X.ringCatIsSheaf M N

/-- The pullback class of `L` along `φ` is the Picard class of `φ^*L`, for any proof `h` that
`φ^*L` is invertible. -/
theorem pullbackPicardClass_eq_picardClass (φ : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (h : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((modulePullback φ.toLRSHom.toShHom).obj L)) :
    pullbackPicardClass φ L hL =
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
        ((modulePullback φ.toLRSHom.toShHom).obj L) h :=
  rfl

/-- **The pullback class vanishes exactly when the pullback is trivial.** -/
theorem pullbackPicardClass_eq_zero_iff (φ : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L) :
    pullbackPicardClass φ L hL = 0 ↔
      Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatIsSheaf
        ((modulePullback φ.toLRSHom.toShHom).obj L) :=
  Stacks.SheafOfModules.picardClass_eq_zero_iff X.presheaf X.ringCatIsSheaf _ _

/-- **Isomorphic invertible modules have the same pullback class.** -/
theorem pullbackPicardClass_congr (φ : X ⟶ Y)
    (L N : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (hN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf N)
    (e : L ≅ N) : pullbackPicardClass φ L hL = pullbackPicardClass φ N hN :=
  (X.picardClass_eq_iff _ _ _ _).mpr
    ⟨(modulePullback φ.toLRSHom.toShHom).mapIso e⟩

/-- **The pullback class of a composite is the pullback class of the pullback.** -/
theorem pullbackPicardClass_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatIsSheaf L)
    (h : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf
      ((modulePullback ψ.toLRSHom.toShHom).obj L)) :
    pullbackPicardClass (φ ≫ ψ) L hL =
      pullbackPicardClass φ ((modulePullback ψ.toLRSHom.toShHom).obj L) h :=
  (X.picardClass_eq_iff _ _ _ _).mpr
    ⟨(RingedSpaceModuleAdjunction.modulePullbackComp φ.toLRSHom.toShHom
      ψ.toLRSHom.toShHom).app L⟩

/-- **The pullback class along the identity is the Picard class.** -/
theorem pullbackPicardClass_id (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M) :
    pullbackPicardClass (𝟙 X) M hM =
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf M hM :=
  (X.picardClass_eq_iff _ _ _ _).mpr
    ⟨(RingedSpaceModuleAdjunction.modulePullbackId X.toRingedSpace).app M⟩

/-- **The pullback class of the structure sheaf vanishes.** -/
theorem pullbackPicardClass_unit (φ : X ⟶ Y)
    (h : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))) :
    pullbackPicardClass φ (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) h = 0 := by
  rw [pullbackPicardClass_eq_zero_iff]
  exact ⟨modulePullbackObjUnitIso φ.toLRSHom.toShHom⟩

/-- **The pullback class is additive for the tensor product sheaf**, by Stacks Tag 01CD. -/
theorem pullbackPicardClass_tensorSheaf (φ : X ⟶ Y)
    (L N : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (hN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf N)
    (hLN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf
      (schemeTensor Y L N)) :
    pullbackPicardClass φ (schemeTensor Y L N) hLN =
      pullbackPicardClass φ L hL + pullbackPicardClass φ N hN := by
  have := hL
  have := hN
  have := hLN
  have hpL := Stacks.RingedSpace.modulePullback_isInvertible φ.toLRSHom.toShHom L
  have hpN := Stacks.RingedSpace.modulePullback_isInvertible φ.toLRSHom.toShHom N
  have htens : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (schemeTensor X ((modulePullback φ.toLRSHom.toShHom).obj L)
        ((modulePullback φ.toLRSHom.toShHom).obj N)) :=
    Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf X.ringCatIsSheaf _ _
  have e : (modulePullback φ.toLRSHom.toShHom).obj (schemeTensor Y L N) ≅
      schemeTensor X ((modulePullback φ.toLRSHom.toShHom).obj L)
        ((modulePullback φ.toLRSHom.toShHom).obj N) :=
    (Stacks.RingedSpace.comparisonBifunctorIso φ.toLRSHom.toShHom).app (L, N)
  rw [pullbackPicardClass_eq_picardClass φ (schemeTensor Y L N) hLN
        (Stacks.RingedSpace.modulePullback_isInvertible φ.toLRSHom.toShHom
          (schemeTensor Y L N)),
    pullbackPicardClass_eq_picardClass φ L hL hpL,
    pullbackPicardClass_eq_picardClass φ N hN hpN,
    Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf X.ringCatIsSheaf _ _ hpL hpN htens]
  exact (X.picardClass_eq_iff _ _ _ _).mpr ⟨e⟩

/-- **If the tensor product of two invertible modules is trivial, their Picard classes are
negatives of one another.** -/
theorem picardClass_eq_neg_of_isTrivial_tensorSheaf (X : Scheme.{u})
    (L N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N)
    (hLN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf (schemeTensor X L N))
    (h : Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatIsSheaf (schemeTensor X L N)) :
    Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf N hN =
      -Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL := by
  have key : Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf N hN +
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL = 0 := by
    rw [add_comm, Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf X.ringCatIsSheaf L N
      hL hN hLN]
    exact (Stacks.SheafOfModules.picardClass_eq_zero_iff X.presheaf X.ringCatIsSheaf _ hLN).mpr h
  exact eq_neg_of_add_eq_zero_left key

/-- **If the tensor product of two invertible modules is trivial, their pullback classes are
negatives of one another.** -/
theorem pullbackPicardClass_eq_neg_of_isTrivial_tensorSheaf (φ : X ⟶ Y)
    (L N : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (hN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf N)
    (hLN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf (schemeTensor Y L N))
    (h : Stacks.SheafOfModules.IsTrivial Y.presheaf Y.ringCatIsSheaf (schemeTensor Y L N)) :
    pullbackPicardClass φ N hN = -pullbackPicardClass φ L hL := by
  have hu : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) :=
    Stacks.SheafOfModules.isInvertible_unit Y.presheaf Y.ringCatIsSheaf
  have key : pullbackPicardClass φ N hN + pullbackPicardClass φ L hL = 0 := by
    rw [add_comm, ← pullbackPicardClass_tensorSheaf φ L N hL hN hLN,
      pullbackPicardClass_congr φ (schemeTensor Y L N)
        (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) hLN hu h.some,
      pullbackPicardClass_unit φ hu]
  exact eq_neg_of_add_eq_zero_left key

/-! ### Iterated tensor products

Invertibility, Picard classes and pullback classes of the three- and four-fold left-nested
tensor products. -/

/-- A three-fold left-nested tensor product of invertible modules is invertible. -/
theorem isInvertible_schemeTensor₃ (X : Scheme.{u})
    (M N P : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N)
    (hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (schemeTensor X (schemeTensor X M N) P) :=
  isInvertible_schemeTensor X _ P (isInvertible_schemeTensor X M N hM hN) hP

/-- A four-fold left-nested tensor product of invertible modules is invertible. -/
theorem isInvertible_schemeTensor₄ (X : Scheme.{u})
    (M N P Q : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N)
    (hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P)
    (hQ : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf Q) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (schemeTensor X (schemeTensor X (schemeTensor X M N) P) Q) :=
  isInvertible_schemeTensor X _ Q (isInvertible_schemeTensor₃ X M N P hM hN hP) hQ

/-- The Picard class of a tensor product is the sum of the classes. -/
theorem picardClass_schemeTensor (X : Scheme.{u})
    (M N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N) :
    Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf (schemeTensor X M N)
        (isInvertible_schemeTensor X M N hM hN) =
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf M hM +
        Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf N hN :=
  (Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf X.ringCatIsSheaf M N hM hN
    (isInvertible_schemeTensor X M N hM hN)).symm

/-- The Picard class of a three-fold tensor product. -/
theorem picardClass_schemeTensor₃ (X : Scheme.{u})
    (M N P : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N)
    (hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P) :
    Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
        (schemeTensor X (schemeTensor X M N) P) (isInvertible_schemeTensor₃ X M N P hM hN hP) =
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf M hM +
        Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf N hN +
        Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf P hP :=
  by rw [picardClass_schemeTensor X _ P (isInvertible_schemeTensor X M N hM hN) hP,
    picardClass_schemeTensor X M N hM hN]

/-- The Picard class of a four-fold tensor product. -/
theorem picardClass_schemeTensor₄ (X : Scheme.{u})
    (M N P Q : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N)
    (hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P)
    (hQ : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf Q) :
    Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
        (schemeTensor X (schemeTensor X (schemeTensor X M N) P) Q)
        (isInvertible_schemeTensor₄ X M N P Q hM hN hP hQ) =
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf M hM +
        Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf N hN +
        Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf P hP +
        Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf Q hQ :=
  by rw [picardClass_schemeTensor X _ Q (isInvertible_schemeTensor₃ X M N P hM hN hP) hQ,
    picardClass_schemeTensor₃ X M N P hM hN hP]

/-- The pullback class of a tensor product is the sum of the pullback classes. -/
theorem pullbackPicardClass_schemeTensor (φ : X ⟶ Y)
    (M N : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf N) :
    pullbackPicardClass φ (schemeTensor Y M N) (isInvertible_schemeTensor Y M N hM hN) =
      pullbackPicardClass φ M hM + pullbackPicardClass φ N hN :=
  pullbackPicardClass_tensorSheaf φ M N hM hN (isInvertible_schemeTensor Y M N hM hN)

/-- The pullback class of a three-fold tensor product. -/
theorem pullbackPicardClass_schemeTensor₃ (φ : X ⟶ Y)
    (M N P : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf N)
    (hP : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf P) :
    pullbackPicardClass φ (schemeTensor Y (schemeTensor Y M N) P)
        (isInvertible_schemeTensor₃ Y M N P hM hN hP) =
      pullbackPicardClass φ M hM + pullbackPicardClass φ N hN + pullbackPicardClass φ P hP :=
  by rw [pullbackPicardClass_schemeTensor φ _ P (isInvertible_schemeTensor Y M N hM hN) hP,
    pullbackPicardClass_schemeTensor φ M N hM hN]

/-- The pullback class of a four-fold tensor product. -/
theorem pullbackPicardClass_schemeTensor₄ (φ : X ⟶ Y)
    (M N P Q : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M)
    (hN : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf N)
    (hP : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf P)
    (hQ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf Q) :
    pullbackPicardClass φ (schemeTensor Y (schemeTensor Y (schemeTensor Y M N) P) Q)
        (isInvertible_schemeTensor₄ Y M N P Q hM hN hP hQ) =
      pullbackPicardClass φ M hM + pullbackPicardClass φ N hN + pullbackPicardClass φ P hP +
        pullbackPicardClass φ Q hQ :=
  by rw [pullbackPicardClass_schemeTensor φ _ Q (isInvertible_schemeTensor₃ Y M N P hM hN hP) hQ,
    pullbackPicardClass_schemeTensor₃ φ M N P hM hN hP]

/-- **An invertible sheaf of modules on a scheme has an invertible tensor inverse**: a module
`N`, itself invertible, whose tensor product with `L` is trivial. This is the existence half of
Stacks Tag 0B8K together with the cancellation of an invertible factor. -/
theorem exists_invertible_isTrivial_tensorSheaf
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) :
    ∃ N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
      Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N ∧
        Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatIsSheaf (schemeTensor X L N) := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := X.ringCatIsSheaf) L).mp hL
  refine ⟨N, ?_, ⟨e⟩⟩
  have h1 : Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatIsSheaf (schemeTensor X N L) :=
    ⟨Stacks.SheafOfModules.tensorSheafBraiding X.presheaf X.ringCatIsSheaf N L ≪≫ e⟩
  exact Stacks.SheafOfModules.isInvertible_of_tensorSheaf_isInvertible X.presheaf
    X.ringCatIsSheaf N L (Stacks.SheafOfModules.isInvertible_of_isTrivial h1)

end Stacks.SheafOfModules

end
