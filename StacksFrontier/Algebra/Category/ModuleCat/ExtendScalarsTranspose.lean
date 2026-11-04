module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Transposing a linear map under extension of scalars

Let `g : A → A₂` be a homomorphism of commutative rings. An `A`-linear map `M ⟶ N|_A` into an
`A₂`-module, read over `A`, has a transpose `A₂ ⊗_A M ⟶ N` under the adjunction between
extension and restriction of scalars. This file records that transpose, its compatibility with
isomorphisms of its source and of its target, the resulting invariance of its invertibility, and
the structure map `A → A₂` as a morphism of `A`-modules.

## Main definitions

* `ModuleCat.ofSelfHom`: an `S`-linear map out of the regular module `S`, given the image of `1`.
* `ModuleCat.extendScalarsTranspose`: the transpose `A₂ ⊗_A M ⟶ N` of an `A`-linear map
  `M ⟶ N|_A`.
* `ModuleCat.structureHom`: the structure map `A → A₂`, as a morphism `A ⟶ A₂|_A` of
  `A`-modules.
* `ModuleCat.extendScalarsSelfGen`: the element `1 ⊗ 1` of `A₂ ⊗_A A`.

## Main results

* `ModuleCat.unit_comp_restrictScalars_map_extendScalarsTranspose`: the transpose is adjoint to
  the original map.
* `ModuleCat.extendScalarsTranspose_one_tmul` and
  `ModuleCat.extendScalarsTranspose_smul_one_tmul`: the same adjointness read on elements — the
  transpose sends `1 ⊗ m` to the value of the original map at `m` and `x • (1 ⊗ m)` to `x` times
  it, which with additivity computes it on all of `A₂ ⊗_A M`.
* `ModuleCat.extendScalarsTranspose_congr` and
  `ModuleCat.isIso_extendScalarsTranspose_of_iso`: transposes of maps identified by isomorphisms
  of their sources and targets agree up to those isomorphisms, so one is invertible as soon as
  the other is.
* `ModuleCat.extendScalarsTranspose_structureHom_gen` and
  `ModuleCat.extendScalarsSelfInv_comp`: the transpose of the structure map carries `1 ⊗ 1` to
  `1`, and is therefore split by `x ↦ x • (1 ⊗ 1)`.

## Implementation notes

The transpose is written as `extendScalars.map v ≫ counit` rather than through
`CategoryTheory.Adjunction.homEquiv`, because that is the shape in which it appears in the
comparison of [stacks 0DJ8]: the comparison there is a whiskering of a unit followed by the
counit of `ModuleCat.extendRestrictScalarsAdj`.

Maps out of `(ModuleCat.extendScalars g).obj M` are built through `ModuleCat.ofSelfHom` and the
adjunction rather than by giving a function on pure tensors. The carrier of that object is a
tensor product over `A` of an object of `ModuleCat A`, and the `A₂`-module structure on it is
found by instance search only after unfolding `ModuleCat.restrictScalars`, which `Mathlib`
arranges with a transparency option that is not available here.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe u

namespace ModuleCat

/-- An `S`-linear map out of the regular module, given the image of `1`. -/
def ofSelfHom {S : Type u} [CommRing S] (N : ModuleCat.{u} S) (y : N) :
    ModuleCat.of S S ⟶ N :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton S N y)

/-- `ModuleCat.ofSelfHom N y` sends `x` to `x • y`. -/
@[simp]
theorem ofSelfHom_apply {S : Type u} [CommRing S] (N : ModuleCat.{u} S) (y : N) (x : S) :
    (ofSelfHom N y).hom x = x • y :=
  rfl

variable {A A₂ : Type u} [CommRing A] [CommRing A₂] (g : A →+* A₂)

/-- **The transpose of an `A`-linear map into an `A₂`-module.** Under the adjunction between
extension and restriction of scalars along `g : A → A₂`, a morphism `M ⟶ N|_A` of `A`-modules
becomes a morphism `A₂ ⊗_A M ⟶ N` of `A₂`-modules. -/
def extendScalarsTranspose {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N) :
    (ModuleCat.extendScalars.{u, u, u} g).obj M ⟶ N :=
  (ModuleCat.extendScalars.{u, u, u} g).map v ≫
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).counit.app N

/-- **The transpose is adjoint to the original map.** Precomposing the transpose, read over `A`,
with the unit of the adjunction returns the original map. -/
theorem unit_comp_restrictScalars_map_extendScalarsTranspose
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N) :
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app M ≫
        (ModuleCat.restrictScalars.{u} g).map (extendScalarsTranspose g v) = v :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).homEquiv M N |>.apply_symm_apply v

/-- **The transpose on the pure tensors `1 ⊗ m`.** The unit of the adjunction is `m ↦ 1 ⊗ m`, so
the adjointness above reads on elements as: the transpose of `v` sends `1 ⊗ m` to `v m`. Together
with `A₂`-linearity and additivity this computes the transpose on all of `A₂ ⊗_A M`. -/
theorem extendScalarsTranspose_one_tmul {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N) (m : M) :
    (extendScalarsTranspose g v).hom
        (show (ModuleCat.extendScalars.{u, u, u} g).obj M from (1 : A₂) ⊗ₜ[A, g] m) =
      v.hom m :=
  DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
    (unit_comp_restrictScalars_map_extendScalarsTranspose g v)) m |>.symm.symm

/-- **The transpose on an arbitrary pure tensor.** `x ⊗ m` is `x • (1 ⊗ m)`, so the transpose
sends it to `x` times the value of the original map at `m`. With additivity this computes the
transpose on all of `A₂ ⊗_A M`. -/
theorem extendScalarsTranspose_smul_one_tmul {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N) (x : A₂) (m : M) :
    (extendScalarsTranspose g v).hom
        (x • (show (ModuleCat.extendScalars.{u, u, u} g).obj M from (1 : A₂) ⊗ₜ[A, g] m)) =
      x • (show N from v.hom m) := by
  rw [map_smul, extendScalarsTranspose_one_tmul]

/-- **Transposes of identified maps agree.** If an isomorphism of the sources and one of the
targets carry `v` to `v'`, they carry the transpose of `v` to the transpose of `v'`. -/
theorem extendScalarsTranspose_congr {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N)
    (v' : M' ⟶ (ModuleCat.restrictScalars.{u} g).obj N')
    (e : M ≅ M') (f : N ≅ N')
    (hcomm : v ≫ (ModuleCat.restrictScalars.{u} g).map f.hom = e.hom ≫ v') :
    extendScalarsTranspose g v ≫ f.hom =
      (ModuleCat.extendScalars.{u, u, u} g).map e.hom ≫ extendScalarsTranspose g v' := by
  dsimp only [extendScalarsTranspose]
  rw [Category.assoc, ← Adjunction.counit_naturality, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, hcomm, CategoryTheory.Functor.map_comp, Category.assoc]

/-- **Invertibility of a transpose is unchanged by isomorphisms of the source and the target.** -/
theorem isIso_extendScalarsTranspose_of_iso {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N)
    (v' : M' ⟶ (ModuleCat.restrictScalars.{u} g).obj N')
    (e : M ≅ M') (f : N ≅ N')
    (hcomm : v ≫ (ModuleCat.restrictScalars.{u} g).map f.hom = e.hom ≫ v')
    (h : IsIso (extendScalarsTranspose g v')) : IsIso (extendScalarsTranspose g v) := by
  have hcomp : IsIso (extendScalarsTranspose g v ≫ f.hom) := by
    rw [extendScalarsTranspose_congr g v v' e f hcomm]
    infer_instance
  exact IsIso.of_isIso_comp_right _ f.hom

/-- The structure map `A → A₂`, as a morphism of `A`-modules into `A₂` read over `A`. -/
def structureHom : ModuleCat.of A A ⟶ (ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of A₂ A₂) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of A₂ A₂))
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun a x => by
        change g (a * x) = g a * g x
        rw [g.map_mul] }

/-- `ModuleCat.structureHom g` sends `a` to `g a`. -/
@[simp]
theorem structureHom_apply (a : A) : (structureHom g).hom a = g a :=
  rfl

/-- The element `1 ⊗ 1` of `A₂ ⊗_A A`. -/
def extendScalarsSelfGen : (ModuleCat.extendScalars.{u, u, u} g).obj (ModuleCat.of A A) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app (ModuleCat.of A A)).hom (1 : A)

/-- The transpose of the structure map carries the generator `1 ⊗ 1` of `A₂ ⊗_A A` to `1`. -/
theorem extendScalarsTranspose_structureHom_gen :
    (extendScalarsTranspose g (structureHom g)).hom (extendScalarsSelfGen g) = 1 :=
  (extendScalarsTranspose_one_tmul g (structureHom g) 1).trans (map_one g)

/-- The transpose of the structure map is split by `x ↦ x • (1 ⊗ 1)`. -/
theorem extendScalarsSelfInv_comp :
    ofSelfHom _ (extendScalarsSelfGen g) ≫ extendScalarsTranspose g (structureHom g) =
      𝟙 (ModuleCat.of A₂ A₂) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rw [ModuleCat.comp_apply, ofSelfHom_apply, map_smul,
    extendScalarsTranspose_structureHom_gen]
  simp

end ModuleCat

end
