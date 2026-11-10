module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness

/-!
# Functoriality of the graded `S`-module of twisted global sections on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring and `X = Proj 𝒮`. A morphism `φ : ℰ ⟶ ℱ`
of `𝒪_X`-modules induces, degree by degree, a morphism `ℰ(n) ⟶ ℱ(n)` of twists and hence a map

`⨁_{n ∈ ℤ} Γ(X, ℰ(n)) → ⨁_{n ∈ ℤ} Γ(X, ℱ(n))`

on twisted global sections. That map preserves the grading by construction and is `S`-linear,
because twisting a morphism commutes with multiplication by a homogeneous scalar. Taking the
morphism to be the inclusion, respectively the projection, of a summand of a finite direct sum
identifies the twisted global sections of `⨁_{j} ℰ_j` with `⨁_{j} ⨁_{n ∈ ℤ} Γ(X, ℰ_j(n))`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafMap`: the `n`-th twist of a morphism
  of modules, a morphism `ℰ(n) ⟶ ℱ(n)`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsMapComponent`: that morphism on
  global sections, a map `Γ(X, ℰ(n)) → Γ(X, ℱ(n))`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsMap`: the induced additive map on
  twisted global sections.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.IsTwistedSectionsSMul`: the formula
  characterizing the `S`-action on twisted global sections.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsLinearMap`: the induced map as an
  `S`-linear map.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsOfDirectSum` and
  `twistedSectionsToDirectSum`: the two `S`-linear comparison maps attached to a finite family of
  modules with inclusions and projections.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsDirectSumEquiv`: those two
  maps as an `S`-linear equivalence.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsBiproductEquiv` and
  `twistedGlobalSectionsBiproductTwistingSheafEquiv`: the same for a categorical biproduct, and
  for a finite family of twisting sheaves.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.tensorSheafMap_add_left`: tensoring a sum of
  morphisms with an identity, on the left-hand factor.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafMap_id`, `twistSheafMap_comp`,
  `twistSheafMap_add`, `twistSheafMap_zero`: the twist of a morphism is functorial and additive.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafMap_comp_twistSheafScalarMap`: twisting
  a morphism commutes with multiplication by a homogeneous scalar.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsMap_id`,
  `twistedSectionsMap_comp`, `twistedSectionsMap_add`, `twistedSectionsMap_zero`,
  `twistedSectionsMap_sum`: the same laws on twisted global sections.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsMap_smul`: the induced map is
  `S`-linear.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.isTwistedSectionsSMul_twistedGlobalSectionsModule`:
  the canonical module structure satisfies the characterizing formula.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.hasBiproduct_of_fin`: a finite family of modules
  on `Proj 𝒮` has a biproduct.

## Implementation notes

The twist of a morphism is `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap` against
the identity of the twisting sheaf, the same spelling in which
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap` is written. Both laws needed
below are then instances of bifunctoriality: the commutation with a homogeneous scalar is
`Stacks.AlgebraicGeometry.TwistMultTransport.tensorSheafMap_comp` used twice, once in each order,
with the two identities absorbed. Additivity in the morphism is `tensorSheafMap_add_left`, the
left-hand companion of `tensorSheafMap_id_add`; it is proved from
`Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext`, which is only available from a
`Proj` file, and that is why it lives here.

The `S`-module structure on twisted global sections is not an instance: it is the datum
`Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule`, which is not unique as
data but is unique once the action of a homogeneous scalar on a homogeneous section is prescribed.
Everything below therefore takes a bare `Module S` instance together with
`IsTwistedSectionsSMul`, the prescription, as an explicit hypothesis, and
`isTwistedSectionsSMul_twistedGlobalSectionsModule` discharges it for the canonical datum. With
that shape `S`-linearity reduces, by `DirectSum.sum_support_decompose`, to the homogeneous case,
and the homogeneous case to an equality of two additive maps out of a direct sum, checked on the
summands by `DirectSum.addHom_ext`.

The finite direct sum is handled through the inclusions, the projections and the two relations
they satisfy, taken as hypotheses rather than through a biproduct, because `SheafOfModules` has no
`CategoryTheory.Limits.HasFiniteBiproducts` instance: the category is abelian, so the instance is
available, but only locally from `CategoryTheory.Limits.HasBiproducts.of_hasFiniteProducts`. The
biproduct form is the instantiation `twistedGlobalSectionsBiproductEquiv`, which binds
`CategoryTheory.Limits.HasBiproduct` and reads the three relations off
`CategoryTheory.Limits.biproduct.ι_π_self`, `biproduct.ι_π_ne` and `biproduct.total`.

**No `stacks` attribute.** Tag 01MN is the twist and Tag 03GK the module structure, and both
already carry bare attributes elsewhere in this library, at
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` and at
`AlgebraicGeometry.ProjectiveSpectrum.Proj.globalSectionsPairing`; the functoriality recorded here
is the statement of no tag.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (twistingSheaf twistSheafOfModules twistedGlobalSections)
open Stacks.SheafOfModules.TensorStalkRingedSpace
  (toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)
open Stacks.AlgebraicGeometry.ProjTwistTheta (tensorSheaf_hom_ext)
open Stacks.AlgebraicGeometry.TwistMultTransport (tensorSheafMap_id tensorSheafMap_comp)
open scoped Stacks.GradedLocalization TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

/-! ### Tensoring a sum of morphisms with an identity

The left-hand companion of `tensorSheafMap_id_add`, checked on the images of pure tensors of
sections. -/

/-- Tensoring a sum of morphisms with an identity gives the sum of the tensors. The ringed space
and the right-hand factor are explicit, because neither is determined by the morphisms. -/
public theorem tensorSheafMap_add_left (X : RingedSpace.{u, u})
    (B : SheafOfModules.{u} (structureSheafRing X))
    {A A' : SheafOfModules.{u} (structureSheafRing X)} (f f' : A ⟶ A') :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((f + f'), (𝟙 B)) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
            ((f, (𝟙 B)) : (_, _) ⟶ (_, _))) +
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
              ((f', (𝟙 B)) : (_, _) ⟶ (_, _))) := by
  refine tensorSheaf_hom_ext _ _ fun U x y => ?_
  obtain ⟨U⟩ := U
  simp only [SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add,
    LinearMap.add_apply]
  rw [tensorSheafMap_app_toTensorSheafSection X A B A' B (f + f') (𝟙 B) U x y,
    tensorSheafMap_app_toTensorSheafSection X A B A' B f (𝟙 B) U x y,
    tensorSheafMap_app_toTensorSheafSection X A B A' B f' (𝟙 B) U x y]
  simp only [toTensorSheafSection, SheafOfModules.add_val, PresheafOfModules.add_app,
    ModuleCat.hom_add, LinearMap.add_apply, TensorProduct.add_tmul]
  exact map_add _ _ _

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable {E F G : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))}

/-! ### The twist of a morphism -/

/-- **The `n`-th twist of a morphism `ℰ ⟶ ℱ` of modules on `Proj 𝒮`**, a morphism
`ℰ(n) ⟶ ℱ(n)`: the morphism tensored with the identity of the `n`-th twisting sheaf. -/
public noncomputable def twistSheafMap (φ : E ⟶ F) (n : ℤ) :
    twistSheafOfModules 𝒮 E n ⟶ twistSheafOfModules 𝒮 F n :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
    (X := (E, twistingSheaf 𝒮 n)) (Y := (F, twistingSheaf 𝒮 n))
    (φ, 𝟙 (twistingSheaf 𝒮 n))

/-- The twist of an identity is the identity. -/
public theorem twistSheafMap_id (n : ℤ) :
    twistSheafMap 𝒮 (𝟙 E) n = 𝟙 (twistSheafOfModules 𝒮 E n) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map_id (E, twistingSheaf 𝒮 n)

/-- The twist of a composite is the composite of the twists. -/
public theorem twistSheafMap_comp (φ : E ⟶ F) (ψ : F ⟶ G) (n : ℤ) :
    twistSheafMap 𝒮 (φ ≫ ψ) n = twistSheafMap 𝒮 φ n ≫ twistSheafMap 𝒮 ψ n := by
  let tensorFunctor := Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))
  let firstMap : (E, twistingSheaf 𝒮 n) ⟶ (F, twistingSheaf 𝒮 n) :=
    (φ, 𝟙 (twistingSheaf 𝒮 n))
  let secondMap : (F, twistingSheaf 𝒮 n) ⟶ (G, twistingSheaf 𝒮 n) :=
    (ψ, 𝟙 (twistingSheaf 𝒮 n))
  refine (congrArg tensorFunctor.map ?_).trans (tensorFunctor.map_comp firstMap secondMap)
  exact Prod.ext rfl (Category.comp_id (𝟙 (twistingSheaf 𝒮 n))).symm

/-- The twist of a sum of morphisms is the sum of the twists. -/
public theorem twistSheafMap_add (φ ψ : E ⟶ F) (n : ℤ) :
    twistSheafMap 𝒮 (φ + ψ) n = twistSheafMap 𝒮 φ n + twistSheafMap 𝒮 ψ n :=
  tensorSheafMap_add_left (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twistingSheaf 𝒮 n) φ ψ

/-- The twist of the zero morphism is the zero morphism. -/
public theorem twistSheafMap_zero (n : ℤ) :
    twistSheafMap 𝒮 (0 : E ⟶ F) n = 0 :=
  AlgebraicGeometry.SheafOfModules.tensorSheafMap_zero_left
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace (𝟙 (twistingSheaf 𝒮 n))

/-- **Twisting a morphism commutes with multiplication by a homogeneous scalar of degree `i`**,
for a degree `k` with `i + n = k`: both composites are the morphism tensored with multiplication
by the scalar. -/
public theorem twistSheafMap_comp_twistSheafScalarMap (φ : E ⟶ F) (i : ℕ) (n k : ℤ)
    (hk : (i : ℤ) + n = k) (a : 𝒮 i) :
    twistSheafMap 𝒮 φ n ≫ twistSheafScalarMap 𝒮 F i n k hk a =
      twistSheafScalarMap 𝒮 E i n k hk a ≫ twistSheafMap 𝒮 φ k := by
  let tensorFunctor := Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))
  let twistMap : (E, twistingSheaf 𝒮 n) ⟶ (F, twistingSheaf 𝒮 n) :=
    (φ, 𝟙 (twistingSheaf 𝒮 n))
  let scalarMap : (F, twistingSheaf 𝒮 n) ⟶ (F, twistingSheaf 𝒮 k) :=
    (𝟙 F, twistScalarSheafMap 𝒮 i n k hk a)
  let scalarMap' : (E, twistingSheaf 𝒮 n) ⟶ (E, twistingSheaf 𝒮 k) :=
    (𝟙 E, twistScalarSheafMap 𝒮 i n k hk a)
  let twistMap' : (E, twistingSheaf 𝒮 k) ⟶ (F, twistingSheaf 𝒮 k) :=
    (φ, 𝟙 (twistingSheaf 𝒮 k))
  have hcomp : twistMap ≫ scalarMap = scalarMap' ≫ twistMap' :=
    Prod.ext ((Category.comp_id φ).trans (Category.id_comp φ).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact (tensorFunctor.map_comp twistMap scalarMap).symm.trans
    ((congrArg tensorFunctor.map hcomp).trans (tensorFunctor.map_comp scalarMap' twistMap'))

/-! ### The twist of a morphism on global sections -/

/-- The `n`-th twist of a morphism `ℰ ⟶ ℱ`, read on global sections: the additive map
`Γ(Proj 𝒮, ℰ(n)) → Γ(Proj 𝒮, ℱ(n))`. -/
public noncomputable def twistedSectionsMapComponent (φ : E ⟶ F) (n : ℤ) :
    twistedSectionsComponent 𝒮 E n →+ twistedSectionsComponent 𝒮 F n :=
  ((twistSheafMap 𝒮 φ n).val.app (op ⊤)).hom.toAddMonoidHom

/-- The twist of an identity acts as the identity on global sections. -/
public theorem twistedSectionsMapComponent_id (n : ℤ) :
    twistedSectionsMapComponent 𝒮 (𝟙 E) n =
      AddMonoidHom.id (twistedSectionsComponent 𝒮 E n) := by
  refine AddMonoidHom.ext fun s => ?_
  change ((twistSheafMap 𝒮 (𝟙 E) n).val.app (op ⊤)).hom s = s
  rw [twistSheafMap_id]
  rfl

/-- The twist of a composite acts as the composite on global sections. -/
public theorem twistedSectionsMapComponent_comp (φ : E ⟶ F) (ψ : F ⟶ G) (n : ℤ) :
    twistedSectionsMapComponent 𝒮 (φ ≫ ψ) n =
      (twistedSectionsMapComponent 𝒮 ψ n).comp (twistedSectionsMapComponent 𝒮 φ n) := by
  refine AddMonoidHom.ext fun s => ?_
  change ((twistSheafMap 𝒮 (φ ≫ ψ) n).val.app (op ⊤)).hom s = _
  rw [twistSheafMap_comp]
  rfl

/-- The twist of a sum of morphisms acts as the sum on global sections. -/
public theorem twistedSectionsMapComponent_add (φ ψ : E ⟶ F) (n : ℤ)
    (s : twistedSectionsComponent 𝒮 E n) :
    twistedSectionsMapComponent 𝒮 (φ + ψ) n s =
      twistedSectionsMapComponent 𝒮 φ n s + twistedSectionsMapComponent 𝒮 ψ n s := by
  change ((twistSheafMap 𝒮 (φ + ψ) n).val.app (op ⊤)).hom s = _
  rw [twistSheafMap_add]
  rfl

/-- The twist of the zero morphism annihilates every global section. -/
public theorem twistedSectionsMapComponent_zero (n : ℤ)
    (s : twistedSectionsComponent 𝒮 E n) :
    twistedSectionsMapComponent 𝒮 (0 : E ⟶ F) n s = 0 := by
  change ((twistSheafMap 𝒮 (0 : E ⟶ F) n).val.app (op ⊤)).hom s = 0
  rw [twistSheafMap_zero]
  rfl

/-- **Multiplication by a homogeneous scalar commutes with the twist of a morphism**, on global
sections. -/
public theorem twistedSectionsMapComponent_homogeneousScalarTwistedSections
    (φ : E ⟶ F) (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 E n) :
    twistedSectionsMapComponent 𝒮 φ ((i : ℤ) + n)
        (homogeneousScalarTwistedSections 𝒮 E i n a s) =
      homogeneousScalarTwistedSections 𝒮 F i n a (twistedSectionsMapComponent 𝒮 φ n s) :=
  congrArg
    (fun m : twistSheafOfModules 𝒮 E n ⟶ twistSheafOfModules 𝒮 F ((i : ℤ) + n) =>
      (m.val.app (op ⊤)).hom s)
    (twistSheafMap_comp_twistSheafScalarMap 𝒮 φ i n ((i : ℤ) + n) rfl a).symm

/-! ### The induced map on twisted global sections -/

/-- **A morphism `ℰ ⟶ ℱ` of modules on `Proj 𝒮` on twisted global sections**: the degreewise
twist of the morphism, read on global sections and summed over the degrees. -/
public noncomputable def twistedSectionsMap (φ : E ⟶ F) :
    twistedGlobalSections 𝒮 E →+ twistedGlobalSections 𝒮 F :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n).comp
      (twistedSectionsMapComponent 𝒮 φ n)

/-- The induced map sends a homogeneous section to the twist of that section, in the same
degree. -/
@[simp]
public theorem twistedSectionsMap_of (φ : E ⟶ F) (n : ℤ)
    (s : twistedSectionsComponent 𝒮 E n) :
    twistedSectionsMap 𝒮 φ
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 E m) n s) =
      DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n
        (twistedSectionsMapComponent 𝒮 φ n s) :=
  DirectSum.toAddMonoid_of _ n s

/-- The identity induces the identity on twisted global sections. -/
public theorem twistedSectionsMap_id :
    twistedSectionsMap 𝒮 (𝟙 E) = AddMonoidHom.id (twistedGlobalSections 𝒮 E) :=
  DirectSum.addHom_ext fun n s => by
    rw [twistedSectionsMap_of, twistedSectionsMapComponent_id]
    rfl

/-- A composite induces the composite on twisted global sections. -/
public theorem twistedSectionsMap_comp (φ : E ⟶ F) (ψ : F ⟶ G) :
    twistedSectionsMap 𝒮 (φ ≫ ψ) =
      (twistedSectionsMap 𝒮 ψ).comp (twistedSectionsMap 𝒮 φ) :=
  DirectSum.addHom_ext fun n s => by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, twistedSectionsMap_of,
      twistedSectionsMapComponent_comp]

/-- The map induced by a composite, evaluated at a section. -/
private theorem twistedSectionsMap_comp_apply (φ : E ⟶ F) (ψ : F ⟶ G)
    (x : twistedGlobalSections 𝒮 E) :
    twistedSectionsMap 𝒮 (φ ≫ ψ) x = twistedSectionsMap 𝒮 ψ (twistedSectionsMap 𝒮 φ x) :=
  DFunLike.congr_fun (twistedSectionsMap_comp 𝒮 φ ψ) x

/-- A sum of morphisms induces the sum on twisted global sections. -/
public theorem twistedSectionsMap_add (φ ψ : E ⟶ F) :
    twistedSectionsMap 𝒮 (φ + ψ) = twistedSectionsMap 𝒮 φ + twistedSectionsMap 𝒮 ψ :=
  DirectSum.addHom_ext fun n s => by
    rw [twistedSectionsMap_of, twistedSectionsMapComponent_add, map_add,
      AddMonoidHom.add_apply, twistedSectionsMap_of, twistedSectionsMap_of]

/-- The zero morphism induces the zero map on twisted global sections. -/
public theorem twistedSectionsMap_zero :
    twistedSectionsMap 𝒮 (0 : E ⟶ F) = 0 :=
  DirectSum.addHom_ext fun n s => by
    rw [twistedSectionsMap_of, twistedSectionsMapComponent_zero, map_zero]
    rfl

/-- The induced map on twisted global sections, as an additive map in the morphism. -/
public noncomputable def twistedSectionsMapAddHom (E F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) :
    (E ⟶ F) →+ (twistedGlobalSections 𝒮 E →+ twistedGlobalSections 𝒮 F) where
  toFun φ := twistedSectionsMap 𝒮 φ
  map_zero' := twistedSectionsMap_zero 𝒮
  map_add' := twistedSectionsMap_add 𝒮

/-- A finite sum of morphisms induces the sum of the maps on twisted global sections. -/
public theorem twistedSectionsMap_sum {ι : Type*} (t : Finset ι) (f : ι → (E ⟶ F))
    (x : twistedGlobalSections 𝒮 E) :
    twistedSectionsMap 𝒮 (∑ j ∈ t, f j) x = ∑ j ∈ t, twistedSectionsMap 𝒮 (f j) x :=
  (DFunLike.congr_fun (map_sum (twistedSectionsMapAddHom 𝒮 E F) f t) x).trans
    (AddMonoidHom.finsetSum_apply _ _ _)

/-! ### `S`-linearity -/

/-- The formula characterizing the `S`-action on the twisted global sections of `ℱ`: a
homogeneous scalar of degree `i` carries the degree-`n` summand to the degree-`i + n` summand by
the homogeneous scalar action on sections. -/
public abbrev IsTwistedSectionsSMul (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
    [Module S (twistedGlobalSections 𝒮 F)] : Prop :=
  ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n),
    (a : S) • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
        twistedGlobalSections 𝒮 F) =
      DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((i : ℤ) + n)
        (homogeneousScalarTwistedSections 𝒮 F i n a s)

/-- The canonical graded `S`-module structure on twisted global sections satisfies the
characterizing formula. -/
public theorem isTwistedSectionsSMul_twistedGlobalSectionsModule (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
    (D : TwistedGlobalSectionsModule 𝒮 F) :
    letI := D.moduleInst
    IsTwistedSectionsSMul 𝒮 F :=
  D.smul_homogeneous

variable [Module S (twistedGlobalSections 𝒮 E)] [Module S (twistedGlobalSections 𝒮 F)]

/-- The induced map commutes with multiplication by a homogeneous scalar. -/
public theorem twistedSectionsMap_smul_homogeneous
    (hE : IsTwistedSectionsSMul 𝒮 E) (hF : IsTwistedSectionsSMul 𝒮 F)
    (φ : E ⟶ F) (i : ℕ) (a : 𝒮 i) (x : twistedGlobalSections 𝒮 E) :
    twistedSectionsMap 𝒮 φ ((a : S) • x) = (a : S) • twistedSectionsMap 𝒮 φ x := by
  have key : (twistedSectionsMap 𝒮 φ).comp (DistribSMul.toAddMonoidHom _ (a : S)) =
      (DistribSMul.toAddMonoidHom _ (a : S)).comp (twistedSectionsMap 𝒮 φ) := by
    refine DirectSum.addHom_ext fun n s => ?_
    change twistedSectionsMap 𝒮 φ ((a : S) •
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 E m) n s)) =
      (a : S) • twistedSectionsMap 𝒮 φ
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 E m) n s)
    rw [hE i n a s, twistedSectionsMap_of, twistedSectionsMap_of,
      hF i n a (twistedSectionsMapComponent 𝒮 φ n s),
      twistedSectionsMapComponent_homogeneousScalarTwistedSections]
  exact DFunLike.congr_fun key x

/-- **The induced map on twisted global sections is `S`-linear.** -/
public theorem twistedSectionsMap_smul
    (hE : IsTwistedSectionsSMul 𝒮 E) (hF : IsTwistedSectionsSMul 𝒮 F)
    (φ : E ⟶ F) (a : S) (x : twistedGlobalSections 𝒮 E) :
    twistedSectionsMap 𝒮 φ (a • x) = a • twistedSectionsMap 𝒮 φ x := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒮 a, Finset.sum_smul, map_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ =>
    twistedSectionsMap_smul_homogeneous 𝒮 hE hF φ i (DirectSum.decompose 𝒮 a i) x

/-- **A morphism `ℰ ⟶ ℱ` of modules on `Proj 𝒮` as an `S`-linear map on twisted global
sections.** -/
public noncomputable def twistedSectionsLinearMap
    (hE : IsTwistedSectionsSMul 𝒮 E) (hF : IsTwistedSectionsSMul 𝒮 F) (φ : E ⟶ F) :
    twistedGlobalSections 𝒮 E →ₗ[S] twistedGlobalSections 𝒮 F where
  toFun := twistedSectionsMap 𝒮 φ
  map_add' := (twistedSectionsMap 𝒮 φ).map_add
  map_smul' := twistedSectionsMap_smul 𝒮 hE hF φ

/-- The `S`-linear map induced by a morphism is the additive map induced by it. -/
@[simp]
public theorem twistedSectionsLinearMap_apply
    (hE : IsTwistedSectionsSMul 𝒮 E) (hF : IsTwistedSectionsSMul 𝒮 F) (φ : E ⟶ F)
    (x : twistedGlobalSections 𝒮 E) :
    twistedSectionsLinearMap 𝒮 hE hF φ x = twistedSectionsMap 𝒮 φ x := rfl

/-! ### Twisted global sections of a finite direct sum

A finite family of modules together with inclusions and projections satisfying the two biproduct
relations; the categorical biproduct is the instantiation at the end. -/

section FiniteDirectSum

variable {r : ℕ}
  (N : Fin r → SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
  (P : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
  [∀ j, Module S (twistedGlobalSections 𝒮 (N j))] [Module S (twistedGlobalSections 𝒮 P)]

/-- The `S`-linear map into the twisted global sections of `𝒫` assembled from the inclusions of
the summands. -/
public noncomputable def twistedSectionsOfDirectSum
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j)) (hP : IsTwistedSectionsSMul 𝒮 P)
    (incl : ∀ j, N j ⟶ P) :
    (⨁ j : Fin r, twistedGlobalSections 𝒮 (N j)) →ₗ[S] twistedGlobalSections 𝒮 P :=
  DirectSum.toModule S (Fin r) (twistedGlobalSections 𝒮 P)
    fun j => twistedSectionsLinearMap 𝒮 (hN j) hP (incl j)

/-- The `S`-linear map out of the twisted global sections of `𝒫` assembled from the projections
to the summands. -/
public noncomputable def twistedSectionsToDirectSum
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j)) (hP : IsTwistedSectionsSMul 𝒮 P)
    (prj : ∀ j, P ⟶ N j) :
    twistedGlobalSections 𝒮 P →ₗ[S] ⨁ j : Fin r, twistedGlobalSections 𝒮 (N j) :=
  ∑ j : Fin r,
    (DirectSum.lof S (Fin r) (fun k : Fin r => twistedGlobalSections 𝒮 (N k)) j).comp
      (twistedSectionsLinearMap 𝒮 hP (hN j) (prj j))

/-- The value of the map assembled from the projections: the sum of the images of the
projections, each placed in its own summand. -/
public theorem twistedSectionsToDirectSum_apply
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j)) (hP : IsTwistedSectionsSMul 𝒮 P)
    (prj : ∀ j, P ⟶ N j) (x : twistedGlobalSections 𝒮 P) :
    twistedSectionsToDirectSum 𝒮 N P hN hP prj x =
      ∑ j : Fin r,
        DirectSum.lof S (Fin r) (fun k : Fin r => twistedGlobalSections 𝒮 (N k)) j
          (twistedSectionsMap 𝒮 (prj j) x) := by
  simp only [twistedSectionsToDirectSum, LinearMap.sum_apply, LinearMap.comp_apply,
    twistedSectionsLinearMap_apply]

/-- The value of the map assembled from the inclusions on a single summand. -/
public theorem twistedSectionsOfDirectSum_lof
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j)) (hP : IsTwistedSectionsSMul 𝒮 P)
    (incl : ∀ j, N j ⟶ P) (j : Fin r) (s : twistedGlobalSections 𝒮 (N j)) :
    twistedSectionsOfDirectSum 𝒮 N P hN hP incl
        (DirectSum.lof S (Fin r) (fun k : Fin r => twistedGlobalSections 𝒮 (N k)) j s) =
      twistedSectionsMap 𝒮 (incl j) s := by
  simp only [twistedSectionsOfDirectSum, DirectSum.toModule_lof,
    twistedSectionsLinearMap_apply]

/-- The projections undo the inclusions on twisted global sections. -/
public theorem twistedSectionsToDirectSum_comp_ofDirectSum
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j)) (hP : IsTwistedSectionsSMul 𝒮 P)
    (incl : ∀ j, N j ⟶ P) (prj : ∀ j, P ⟶ N j)
    (hself : ∀ j, incl j ≫ prj j = 𝟙 (N j))
    (hne : ∀ j k, j ≠ k → incl j ≫ prj k = 0) :
    (twistedSectionsToDirectSum 𝒮 N P hN hP prj).comp
        (twistedSectionsOfDirectSum 𝒮 N P hN hP incl) = LinearMap.id := by
  refine DirectSum.linearMap_ext S fun j => LinearMap.ext fun s => ?_
  have hc : ∀ k : Fin r,
      twistedSectionsMap 𝒮 (prj k) (twistedSectionsMap 𝒮 (incl j) s) =
        twistedSectionsMap 𝒮 (incl j ≫ prj k) s := fun k =>
    (twistedSectionsMap_comp_apply 𝒮 (incl j) (prj k) s).symm
  have hvanish : ∀ k : Fin r, k ∈ Finset.univ → k ≠ j →
      DirectSum.lof S (Fin r) (fun l : Fin r => twistedGlobalSections 𝒮 (N l)) k
          (twistedSectionsMap 𝒮 (prj k) (twistedSectionsMap 𝒮 (incl j) s)) = 0 := by
    intro k _ hkj
    rw [hc k, hne j k (Ne.symm hkj), twistedSectionsMap_zero, AddMonoidHom.zero_apply,
      map_zero]
  simp only [LinearMap.comp_apply, twistedSectionsOfDirectSum_lof,
    twistedSectionsToDirectSum_apply, LinearMap.id_coe, id_eq]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) hvanish, hc j, hself j,
    twistedSectionsMap_id, AddMonoidHom.id_apply]

/-- The inclusions undo the projections on twisted global sections. -/
public theorem twistedSectionsOfDirectSum_comp_toDirectSum
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j)) (hP : IsTwistedSectionsSMul 𝒮 P)
    (incl : ∀ j, N j ⟶ P) (prj : ∀ j, P ⟶ N j)
    (htotal : ∑ j : Fin r, prj j ≫ incl j = 𝟙 P) :
    (twistedSectionsOfDirectSum 𝒮 N P hN hP incl).comp
        (twistedSectionsToDirectSum 𝒮 N P hN hP prj) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  have hc : ∀ k : Fin r,
      twistedSectionsOfDirectSum 𝒮 N P hN hP incl
          (DirectSum.lof S (Fin r) (fun l : Fin r => twistedGlobalSections 𝒮 (N l)) k
            (twistedSectionsMap 𝒮 (prj k) x)) =
        twistedSectionsMap 𝒮 (prj k ≫ incl k) x := by
    intro k
    rw [twistedSectionsOfDirectSum_lof, twistedSectionsMap_comp_apply]
  simp only [LinearMap.comp_apply, twistedSectionsToDirectSum_apply, map_sum,
    LinearMap.id_coe, id_eq]
  rw [Finset.sum_congr rfl fun k _ => hc k, ← twistedSectionsMap_sum, htotal,
    twistedSectionsMap_id, AddMonoidHom.id_apply]

/-- **Twisted global sections commute with a finite direct sum of modules, `S`-linearly**: the
twisted global sections of `𝒫` are the direct sum of the twisted global sections of the
summands. -/
public noncomputable def twistedGlobalSectionsDirectSumEquiv
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j)) (hP : IsTwistedSectionsSMul 𝒮 P)
    (incl : ∀ j, N j ⟶ P) (prj : ∀ j, P ⟶ N j)
    (hself : ∀ j, incl j ≫ prj j = 𝟙 (N j))
    (hne : ∀ j k, j ≠ k → incl j ≫ prj k = 0)
    (htotal : ∑ j : Fin r, prj j ≫ incl j = 𝟙 P) :
    twistedGlobalSections 𝒮 P ≃ₗ[S] ⨁ j : Fin r, twistedGlobalSections 𝒮 (N j) :=
  LinearEquiv.ofLinearMap (twistedSectionsToDirectSum 𝒮 N P hN hP prj)
    (twistedSectionsOfDirectSum 𝒮 N P hN hP incl)
    (twistedSectionsToDirectSum_comp_ofDirectSum 𝒮 N P hN hP incl prj hself hne)
    (twistedSectionsOfDirectSum_comp_toDirectSum 𝒮 N P hN hP incl prj htotal)

end FiniteDirectSum

/-- A finite family of modules on `Proj 𝒮` has a biproduct: the category has finite products, and
in a preadditive category a finite product is a biproduct. No such instance is declared for
`SheafOfModules`, so the biproduct statements below bind `CategoryTheory.Limits.HasBiproduct` and
this discharges it. -/
public theorem hasBiproduct_of_fin {r : ℕ}
    (N : Fin r → SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) :
    HasBiproduct N :=
  HasBiproduct.of_hasProduct N

section Biproduct

variable {r : ℕ}
  (N : Fin r → SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
  [HasBiproduct N]
  [∀ j, Module S (twistedGlobalSections 𝒮 (N j))]
  [Module S (twistedGlobalSections 𝒮 (biproduct N))]

/-- **Twisted global sections commute with a finite biproduct of modules, `S`-linearly.** The
three relations the general statement asks for are the standard biproduct identities. -/
public noncomputable def twistedGlobalSectionsBiproductEquiv
    (hN : ∀ j, IsTwistedSectionsSMul 𝒮 (N j))
    (hB : IsTwistedSectionsSMul 𝒮 (biproduct N)) :
    twistedGlobalSections 𝒮 (biproduct N) ≃ₗ[S]
      ⨁ j : Fin r, twistedGlobalSections 𝒮 (N j) :=
  twistedGlobalSectionsDirectSumEquiv 𝒮 N (biproduct N) hN hB
    (fun j => biproduct.ι N j) (fun j => biproduct.π N j)
    (fun j => biproduct.ι_π_self N j) (fun _ _ hjk => biproduct.ι_π_ne N hjk)
    biproduct.total

end Biproduct

section TwistingSheaves

variable {r : ℕ} (d : Fin r → ℤ)
  [HasBiproduct fun j => twistingSheaf 𝒮 (d j)]
  [∀ j, Module S (twistedGlobalSections 𝒮 (twistingSheaf 𝒮 (d j)))]
  [Module S (twistedGlobalSections 𝒮 (biproduct fun j => twistingSheaf 𝒮 (d j)))]

/-- **Twisted global sections of a finite direct sum of twisting sheaves**: the twisted global
sections of `⨁_{j} 𝒪(d j)` are, `S`-linearly, the direct sum of those of the `𝒪(d j)`. -/
public noncomputable def twistedGlobalSectionsBiproductTwistingSheafEquiv
    (hd : ∀ j, IsTwistedSectionsSMul 𝒮 (twistingSheaf 𝒮 (d j)))
    (hB : IsTwistedSectionsSMul 𝒮 (biproduct fun j => twistingSheaf 𝒮 (d j))) :
    twistedGlobalSections 𝒮 (biproduct fun j => twistingSheaf 𝒮 (d j)) ≃ₗ[S]
      ⨁ j : Fin r, twistedGlobalSections 𝒮 (twistingSheaf 𝒮 (d j)) :=
  twistedGlobalSectionsBiproductEquiv 𝒮 (fun j => twistingSheaf 𝒮 (d j)) hd hB

end TwistingSheaves

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
