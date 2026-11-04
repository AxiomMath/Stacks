module

public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.SurjectionSiteStructureResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The augmentation ideal and the conormal sheaf on `C_{B/A}`, with sections in `Type u`

Let `A → B` be a ring map and let `C_{B/A}` be the site of [Stacks, Tag 08PR]. Remark 08R7 works
with the kernel `𝒥 = ker(𝒪 → B̲)` of the augmentation, with `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`, with the
two-term complex `𝒥 → Ω` and with `Tor₀^𝒪(𝒥, B̲) = 𝒥 ⊗_𝒪 B̲`, the sheaf the remark writes
`𝒥/𝒥²`, together with its map to `Ω`. This file builds those presheaves explicitly, as functors
of the augmented algebra, with sections in `Type u`:

* over `(P, α)` the ideal `J = ker(α)`, as an `A`-module, with the inclusion `J ⊂ P` and the
  augmentation `P → B` as maps of `A`-modules;
* over `(P, α)` the `B`-module `B ⊗_{P,α} J`, which is `𝒥 ⊗_𝒪 B̲` evaluated at `(P, α)`;
* the differential `j ↦ 1 ⊗ dj`, both as a map of `A`-modules `J → B ⊗_P Ω_{P/A}` and as a map
  of `B`-modules `B ⊗_P J → B ⊗_P Ω_{P/A}`.

The chaotic topology on `C_{B/A}` makes every presheaf a sheaf, so these are the sheaves of the
remark.

## Main definitions

* `CommAlgCat.polynomialSiteIdealPresheaf`: `𝒥`, as a presheaf of `A`-modules.
* `CommAlgCat.polynomialSiteIdealToCotangent`: `d : 𝒥 → Ω`, as a map of presheaves of
  `A`-modules.
* `CommAlgCat.polynomialSiteConormalPresheaf`: `𝒥 ⊗_𝒪 B̲`, as a presheaf of `B`-modules.
* `CommAlgCat.polynomialSiteConormalToCotangent`: `d : 𝒥 ⊗_𝒪 B̲ → Ω`, as a map of presheaves of
  `B`-modules.

## Implementation notes

**Why `B ⊗_P J` and not `J/J²`.** The remark identifies `Tor₀^𝒪(𝒥, B̲)` with `𝒥/𝒥²`. The
sections of `𝒥 ⊗_𝒪 B̲` over `(P, α)` are `B ⊗_P J`, and these are `J/J²` exactly when `α` is
surjective; for a non-surjective `α`, `J/J²` is a module over the image of `P` in `B` only, so it
is not a `B̲`-module at all. The `B̲`-module the remark needs -- the one whose `Lπ_!` lives in
`D(B)` and receives the map of the remark's last display -- is therefore `𝒥 ⊗_𝒪 B̲`, which is
what is built here. On every term of the standard resolution the augmentation is surjective and
`B ⊗_{P_n} J_n = J_n/J_n²`; that identification is proved where it is used.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace CommAlgCat

section Over

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}

/-- The ideal `J = ker(α)` of an `A`-algebra `P` augmented to `B` by `α`. -/
abbrev overIdeal (X : Over B) : Ideal (X.left : Type u) :=
  RingHom.ker (augmentationRingHom X)

/-- A morphism over `B` carries the augmentation ideal into the augmentation ideal. -/
theorem map_mem_overIdeal {X Y : Over B} (f : X ⟶ Y) {p : (X.left : Type u)}
    (hp : p ∈ overIdeal X) : f.left p ∈ overIdeal Y := by
  rw [RingHom.mem_ker] at hp ⊢
  exact (RingHom.congr_fun (augmentationRingHom_comp f) p).trans hp

/-- The augmentation ideal `J = ker(α)`, as an `A`-module. -/
@[sga "3 VIIB 2.1" "more general", sga "3 VIIB 2.6" "partial"]
def overIdealModule (X : Over B) : ModuleCat.{u} A :=
  ModuleCat.of A (overIdeal X)

/-- The map of augmentation ideals induced by a morphism over `B`. -/
def overIdealModuleMap {X Y : Over B} (f : X ⟶ Y) :
    overIdealModule X ⟶ overIdealModule Y :=
  ModuleCat.ofHom
    { toFun := fun j => ⟨f.left j.1, map_mem_overIdeal f j.2⟩
      map_add' := fun x y => Subtype.ext (map_add f.left.hom x.1 y.1)
      map_smul' := fun a x => Subtype.ext (f.left.hom.toLinearMap.map_smul a x.1) }

/-- **The augmentation ideal as a functor of the augmented algebra**, with values in
`A`-modules: `(P, α) ↦ ker(α)`. -/
@[sga "3 VIIB 2.6" "object assignment"]
def overIdealFunctor : Over B ⥤ ModuleCat.{u} A where
  obj := overIdealModule
  map := overIdealModuleMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion `J ⊂ P`, as a natural map of `A`-modules. -/
def overIdealInclusion : overIdealFunctor (B := B) ⟶ overModuleFunctor A B where
  app _ := ModuleCat.ofHom
    { toFun := fun j => j.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- The augmentation ideal is the kernel of the augmentation: `ι ≫ α = 0`. -/
theorem overIdealInclusion_comp_augmentation (X : Over B) :
    (overIdealInclusion (B := B)).app X ≫ (overModuleAugmentation A B).app X = 0 := by
  ext j
  exact j.2

/-- The `B`-module `B ⊗_{P,α} J`: the sections over `(P, α)` of `𝒥 ⊗_𝒪 B̲ = Tor₀^𝒪(𝒥, B̲)`. -/
def overConormal (X : Over B) : ModuleCat.{u} B :=
  (ModuleCat.extendScalars (augmentationRingHom X)).obj
    (ModuleCat.of (X.left : Type u) (overIdeal X))

/-- The pure tensor `1 ⊗ j` of `CommAlgCat.overConormal`. -/
def overConormalMk (X : Over B) (j : overIdeal X) : overConormal X :=
  (1 : B) ⊗ₜ j

/-- Two `B`-linear maps out of `B ⊗_P J` agreeing on every `1 ⊗ j` are equal. -/
theorem overConormal_hom_ext {X : Over B} {N : ModuleCat.{u} B} (f g : overConormal X ⟶ N)
    (h : ∀ j, f (overConormalMk X j) = g (overConormalMk X j)) : f = g :=
  ModuleCat.ExtendScalars.hom_ext h

/-- The `P`-linear map `J → B ⊗_Q J'`, `j ↦ 1 ⊗ g j`, attached to a map `g : P ⟶ Q` lying over
`B`; it is adjoint to `CommAlgCat.overConormalPush`. -/
def overConormalPushAdjoint {X Y : Over B} (f : X ⟶ Y) :
    ModuleCat.of (X.left : Type u) (overIdeal X) ⟶
      (ModuleCat.restrictScalars (augmentationRingHom X)).obj (overConormal Y) := by
  let P := (X.left : Type u)
  let Q := (Y.left : Type u)
  letI : Algebra P Q := f.left.hom.toRingHom.toAlgebra
  letI : Algebra Q (B : Type u) := (augmentationRingHom Y).toAlgebra
  exact ModuleCat.ofHom
    (X := ModuleCat.of P (overIdeal X))
    (Y := (ModuleCat.restrictScalars (augmentationRingHom X)).obj (overConormal Y))
    { toFun := fun j => overConormalMk Y ⟨f.left j.1, map_mem_overIdeal f j.2⟩
      map_add' := by
        intro x y
        change (1 : (B : Type u)) ⊗ₜ[Q] (⟨f.left (x.1 + y.1), _⟩ : overIdeal Y) = _
        rw [show (⟨f.left (x.1 + y.1), map_mem_overIdeal f (x + y).2⟩ : overIdeal Y) =
          ⟨f.left x.1, map_mem_overIdeal f x.2⟩ + ⟨f.left y.1, map_mem_overIdeal f y.2⟩ from
            Subtype.ext (map_add f.left.hom x.1 y.1), TensorProduct.tmul_add]
        rfl
      map_smul' := by
        intro p x
        change (1 : (B : Type u)) ⊗ₜ[Q]
            (⟨f.left (p * x.1), map_mem_overIdeal f (p • x).2⟩ : overIdeal Y) =
          augmentationRingHom X p • ((1 : (B : Type u)) ⊗ₜ[Q]
            (⟨f.left x.1, map_mem_overIdeal f x.2⟩ : overIdeal Y))
        rw [show (⟨f.left (p * x.1), map_mem_overIdeal f (p • x).2⟩ : overIdeal Y) =
            (f.left p : Q) • (⟨f.left x.1, map_mem_overIdeal f x.2⟩ : overIdeal Y) from
            Subtype.ext (map_mul f.left.hom p x.1),
          TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        congr 1
        change augmentationRingHom Y (f.left p) * 1 = augmentationRingHom X p * 1
        rw [← RingHom.congr_fun (augmentationRingHom_comp f) p]
        rfl }

/-- The `B`-linear map `B ⊗_P J → B ⊗_Q J'` induced by a morphism over `B`. -/
def overConormalPush {X Y : Over B} (f : X ⟶ Y) : overConormal X ⟶ overConormal Y :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (augmentationRingHom X)
    (overConormalPushAdjoint f)

/-- `CommAlgCat.overConormalPush` sends `1 ⊗ j` to `1 ⊗ g j`. -/
@[simp]
theorem overConormalPush_mk {X Y : Over B} (f : X ⟶ Y) (j : overIdeal X) :
    overConormalPush f (overConormalMk X j) =
      overConormalMk Y ⟨f.left j.1, map_mem_overIdeal f j.2⟩ := by
  have key : overConormalPush f (overConormalMk X j) =
      (1 : (B : Type u)) • (overConormalPushAdjoint f) j :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (augmentationRingHom X) (overConormalPushAdjoint f) (1 : (B : Type u)) j
  rw [key, one_smul]
  rfl

/-- **`𝒥 ⊗_𝒪 B̲` as a functor of the augmented algebra**: `(P, α) ↦ B ⊗_{P,α} ker(α)`. -/
def overConormalFunctor : Over B ⥤ ModuleCat.{u} B where
  obj := overConormal
  map := overConormalPush
  map_id X := by
    refine overConormal_hom_ext _ _ fun j => ?_
    rw [overConormalPush_mk]
    rfl
  map_comp {X Y Z} f g := by
    refine overConormal_hom_ext _ _ fun j => ?_
    rw [overConormalPush_mk, ConcreteCategory.comp_apply, overConormalPush_mk,
      overConormalPush_mk]
    rfl

/-- The `P`-linear map `J → B ⊗_P Ω[P⁄A]`, `j ↦ 1 ⊗ dj`. It is `P`-linear because
`d(pj) = p dj + j dp` and `j` acts by `α(j) = 0` on `B ⊗_P Ω[P⁄A]`. -/
@[ega "0 20.5.11" "partial"]
def overConormalDifferentialAdjoint (X : Over B) :
    ModuleCat.of (X.left : Type u) (overIdeal X) ⟶
      (ModuleCat.restrictScalars (augmentationRingHom X)).obj (overDifferentials X) := by
  let P := (X.left : Type u)
  letI : Algebra P (B : Type u) := (augmentationRingHom X).toAlgebra
  exact ModuleCat.ofHom
    (X := ModuleCat.of P (overIdeal X))
    (Y := (ModuleCat.restrictScalars (augmentationRingHom X)).obj (overDifferentials X))
    { toFun := fun j => overDifferentialsMk X j.1
      map_add' := by
        intro x y
        change (1 : (B : Type u)) ⊗ₜ[P] KaehlerDifferential.D A P (x.1 + y.1) = _
        rw [map_add, TensorProduct.tmul_add]
        rfl
      map_smul' := by
        intro p x
        change (1 : (B : Type u)) ⊗ₜ[P] KaehlerDifferential.D A P (p * x.1) =
          augmentationRingHom X p • ((1 : (B : Type u)) ⊗ₜ[P] KaehlerDifferential.D A P x.1)
        rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        have hx : x.1 • (1 : (B : Type u)) = 0 := by
          rw [Algebra.smul_def, mul_one]
          exact x.2
        rw [hx, TensorProduct.zero_tmul, add_zero]
        congr 1 }

/-- **The differential `d : B ⊗_P J → B ⊗_P Ω[P⁄A]`**, `1 ⊗ j ↦ 1 ⊗ dj`. -/
def overConormalDifferential (X : Over B) : overConormal X ⟶ overDifferentials X :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (augmentationRingHom X)
    (overConormalDifferentialAdjoint X)

/-- `CommAlgCat.overConormalDifferential` sends `1 ⊗ j` to `1 ⊗ dj`. -/
@[simp]
theorem overConormalDifferential_mk (X : Over B) (j : overIdeal X) :
    overConormalDifferential X (overConormalMk X j) = overDifferentialsMk X j.1 := by
  have key : overConormalDifferential X (overConormalMk X j) =
      (1 : (B : Type u)) • (overConormalDifferentialAdjoint X) j :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (augmentationRingHom X) (overConormalDifferentialAdjoint X) (1 : (B : Type u)) j
  rw [key, one_smul]
  rfl

/-- The differential `d : 𝒥 ⊗_𝒪 B̲ → Ω`, as a natural transformation of functors of the augmented
algebra. -/
def overConormalToDifferentials : overConormalFunctor (B := B) ⟶ overDifferentialsFunctor where
  app := overConormalDifferential
  naturality X Y f := by
    refine overConormal_hom_ext _ _ fun j => ?_
    change overConormalDifferential Y (overConormalPush f (overConormalMk X j)) =
      overDifferentialsPush f.left (augmentationRingHom_comp f)
        (overConormalDifferential X (overConormalMk X j))
    rw [overConormalDifferential_mk, overConormalPush_mk, overConormalDifferential_mk]
    exact (overDifferentialsPush_mk f.left (augmentationRingHom_comp f) j.1).symm

/-- The `A`-linear map `J → 𝒥 ⊗_𝒪 B̲ = B ⊗_P J`, `j ↦ 1 ⊗ j`. -/
def overIdealToConormal (X : Over B) :
    overIdealModule X ⟶ (ModuleCat.restrictScalars (algebraMap A B)).obj (overConormal X) :=
  ModuleCat.ofHom (X := overIdealModule X)
    (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj (overConormal X))
    { toFun := fun j => overConormalMk X j
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro a (x : overIdeal X)
        let : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
        change (1 : (B : Type u)) ⊗ₜ[(X.left : Type u)] (a • x) =
          algebraMap A B a • ((1 : (B : Type u)) ⊗ₜ[(X.left : Type u)] x)
        rw [← IsScalarTower.algebraMap_smul (X.left : Type u) a x,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        conv_rhs => rw [TensorProduct.smul_tmul']
        congr 1
        rw [Algebra.smul_def, Algebra.smul_def]
        exact congrArg (· * (1 : (B : Type u))) (X.hom.hom.commutes a) }

/-- **The differential `d : 𝒥 → Ω`**, `j ↦ 1 ⊗ dj`, as a natural map of `A`-modules. -/
def overIdealToDifferentials :
    overIdealFunctor (B := B) ⟶
      overDifferentialsFunctor ⋙ ModuleCat.restrictScalars (algebraMap A B) where
  app X := overIdealToConormal X ≫
    (ModuleCat.restrictScalars (algebraMap A B)).map (overConormalDifferential X)
  naturality X Y f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (j : overIdeal X) => ?_)
    change overConormalDifferential Y (overConormalMk Y ⟨f.left j.1, map_mem_overIdeal f j.2⟩) =
      overDifferentialsPush f.left (augmentationRingHom_comp f)
        (overConormalDifferential X (overConormalMk X j))
    rw [overConormalDifferential_mk, overConormalDifferential_mk]
    exact (overDifferentialsPush_mk f.left (augmentationRingHom_comp f) j.1).symm

end Over

/-! ### The presheaves on the site -/

section Site

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- The inclusion of the site's objects into `Over B`, read on the opposite of the site. -/
abbrev polynomialSiteToOver : (polynomialSite A B)ᵒᵖ ⥤ Over B :=
  unopUnop (PolynomialAugmentation A B) ⋙ (IsPolynomialAlgebraOver A B).ι

/-- **The augmentation ideal `𝒥 = ker(𝒪 → B̲)` on `C_{B/A}`**, as a presheaf of `A`-modules with
sections in `Type u`: over `(P, α)` it is `ker(α)`. -/
def polynomialSiteIdealPresheaf : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} A :=
  polynomialSiteToOver A B ⋙ overIdealFunctor

/-- **The structure sheaf `𝒪`**, as a presheaf of `A`-modules: over `(P, α)` it is `P`. -/
def polynomialSiteStructureModulePresheaf : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} A :=
  polynomialSiteToOver A B ⋙ overModuleFunctor A B

/-- **The constant sheaf `B̲`**, as a presheaf of `A`-modules. -/
def polynomialSiteBaseModulePresheaf : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} A :=
  polynomialSiteToOver A B ⋙ (Functor.const (Over B)).obj (ModuleCat.of A (B : Type u))

/-- The inclusion `𝒥 ⊂ 𝒪`. -/
def polynomialSiteIdealInclusion :
    polynomialSiteIdealPresheaf A B ⟶ polynomialSiteStructureModulePresheaf A B :=
  Functor.whiskerLeft (polynomialSiteToOver A B) overIdealInclusion

/-- The augmentation `𝒪 → B̲`, as a map of presheaves of `A`-modules. -/
def polynomialSiteModuleAugmentation :
    polynomialSiteStructureModulePresheaf A B ⟶ polynomialSiteBaseModulePresheaf A B :=
  Functor.whiskerLeft (polynomialSiteToOver A B) (overModuleAugmentation A B)

/-- `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`, as a presheaf of `A`-modules. -/
abbrev polynomialSiteCotangentModulePresheafOverBase : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} A :=
  polynomialCotangentModulePresheaf A B ⋙ ModuleCat.restrictScalars (algebraMap A B)

/-- **The differential `d : 𝒥 → Ω`** on `C_{B/A}`, as a map of presheaves of `A`-modules: over
`(P, α)` it is `j ↦ 1 ⊗ dj : ker(α) → B ⊗_P Ω_{P/A}`. -/
def polynomialSiteIdealToCotangent :
    polynomialSiteIdealPresheaf A B ⟶ polynomialSiteCotangentModulePresheafOverBase A B :=
  Functor.whiskerLeft (polynomialSiteToOver A B) overIdealToDifferentials

/-- **The sheaf `𝒥 ⊗_𝒪 B̲ = Tor₀^𝒪(𝒥, B̲)`** on `C_{B/A}`, the sheaf Remark 08R7 writes `𝒥/𝒥²`,
as a presheaf of `B`-modules with sections in `Type u`: over `(P, α)` it is `B ⊗_{P,α} ker(α)`,
which is `ker(α)/ker(α)²` whenever `α` is surjective. -/
def polynomialSiteConormalPresheaf : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B :=
  polynomialSiteToOver A B ⋙ overConormalFunctor

/-- **The differential `d : 𝒥 ⊗_𝒪 B̲ → Ω`** on `C_{B/A}`, as a map of presheaves of `B`-modules:
over `(P, α)` it is `1 ⊗ j ↦ 1 ⊗ dj : B ⊗_P ker(α) → B ⊗_P Ω_{P/A}`. -/
def polynomialSiteConormalToCotangent :
    polynomialSiteConormalPresheaf A B ⟶ polynomialCotangentModulePresheaf A B :=
  Functor.whiskerLeft (polynomialSiteToOver A B) overConormalToDifferentials

end Site

end CommAlgCat

end
