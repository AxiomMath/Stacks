module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification

/-!
# The base-change presheaf of a module on an affine scheme

Let `R` be a commutative ring and `N` an `R`-module. The presheaf

`U ↦ 𝒪_{Spec R}(U) ⊗_R N`

of `𝒪_{Spec R}`-modules maps to the associated sheaf `Ñ` by `a ⊗ n ↦ a • (toOpen N U) n`. This
morphism is locally injective and locally surjective: on a basic open `D(f)` it is the
base-change identification `R_f ⊗_R N ≅ N_f`, and the basic opens are a basis of `Spec R`.

## Main definitions

* `Stacks.AffineBaseChange.specRestrictₗ`: a restriction map of the structure sheaf of
  `Spec R`, as an `R`-linear map.
* `Stacks.AffineBaseChange.presheaf`: the presheaf `U ↦ 𝒪(U) ⊗_R N` of `𝒪_{Spec R}`-modules.
* `Stacks.AffineBaseChange.toTilde`: the morphism `U ↦ 𝒪(U) ⊗_R N` into the underlying
  presheaf of `Ñ`.

## Main results

* `Stacks.AffineBaseChange.algebraMap_restrict`: the restriction maps of the structure sheaf of
  an affine scheme commute with the structure map from the base ring.
* `Stacks.AffineBaseChange.bijective_toTildeₗ_basicOpen`: on a basic open the comparison is
  bijective.
* `Stacks.AffineBaseChange.isLocallySurjective_toTilde` and
  `isLocallyInjective_toTilde`: the comparison is locally bijective, as morphisms of presheaves
  of modules over `𝒪_{Spec R}`.

## Implementation notes

The scalars of `𝒪(U) ⊗_R N` are those of the left factor, so the presheaf is built with
`PresheafOfModules.ofPresheaf` from the presheaf of abelian groups `U ↦ 𝒪(U) ⊗_R N` together
with the scalar law; the restriction maps are `LinearMap.rTensor N (specRestrictₗ i)`, which
needs the restriction maps of the structure sheaf to be `R`-linear and that is
`algebraMap_restrict`.

The two local bijectivity statements are deduced from bijectivity on basic opens and
`PrimeSpectrum.isBasis_basic_opens`. Bijectivity on `D(f)` is `IsBaseChange`: Mathlib's
`IsLocalizedModule.Away f (tilde.toOpen N (basicOpen f)).hom` together with
`isLocalizedModule_iff_isBaseChange` for the localization `Γ(Spec R, D(f))` of `R` away from
`f`. The comparison agrees with `IsBaseChange.equiv` on pure tensors, hence everywhere.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AffineBaseChange

variable {R : CommRingCat.{u}} (N : ModuleCat.{u} R)

/-- The basic open `D(f)` of `Spec R`, as an open of the scheme `Spec R`. -/
abbrev specBasicOpen (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

/-! ### The structure sheaf of an affine scheme as a presheaf of `R`-algebras -/

/-- The restriction maps of the structure sheaf of `Spec R` commute with the structure map
`R ⟶ 𝒪(U)`: `𝒪` is a presheaf of `R`-algebras. -/
theorem algebraMap_restrict {U V : (Spec R).Opens} (i : V ⟶ U) (r : R) :
    (Spec R).presheaf.map i.op (algebraMap R Γ(Spec R, U) r) =
      algebraMap R Γ(Spec R, V) r := by
  rw [IsAffineOpen.algebraMap_Spec_obj, IsAffineOpen.algebraMap_Spec_obj]
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op ≫
    (Spec R).presheaf.map i.op).hom r = _
  rw [← (Spec R).presheaf.map_comp]
  rfl

/-- A restriction map of the structure sheaf of `Spec R`, as an `R`-linear map. -/
def specRestrictₗ {U V : (Spec R).Opens} (i : V ⟶ U) : Γ(Spec R, U) →ₗ[R] Γ(Spec R, V) where
  toFun a := (Spec R).presheaf.map i.op a
  map_add' a b := map_add ((Spec R).presheaf.map i.op).hom a b
  map_smul' r a := by
    change (Spec R).presheaf.map i.op (r • a) = r • (Spec R).presheaf.map i.op a
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_restrict i r]

/-- `specRestrictₗ i` is the restriction map of the structure sheaf along `i`. -/
@[simp]
theorem specRestrictₗ_apply {U V : (Spec R).Opens} (i : V ⟶ U) (a : Γ(Spec R, U)) :
    specRestrictₗ (R := R) i a = (Spec R).presheaf.map i.op a := rfl

/-- `specRestrictₗ i` is multiplicative. -/
theorem specRestrictₗ_mul {U V : (Spec R).Opens} (i : V ⟶ U) (a b : Γ(Spec R, U)) :
    specRestrictₗ (R := R) i (a * b) = specRestrictₗ i a * specRestrictₗ i b :=
  map_mul ((Spec R).presheaf.map i.op).hom a b

/-- `specRestrictₗ i` sends `1` to `1`. -/
theorem specRestrictₗ_one {U V : (Spec R).Opens} (i : V ⟶ U) :
    specRestrictₗ (R := R) i 1 = 1 :=
  map_one ((Spec R).presheaf.map i.op).hom

/-- Restriction along the identity of `U` is the identity. -/
theorem specRestrictₗ_id (U : (Spec R).Opens) (a : Γ(Spec R, U)) :
    specRestrictₗ (R := R) (𝟙 U) a = a := by
  simpa only [specRestrictₗ_apply, op_id] using
    CategoryTheory.Functor.map_id_apply (Spec R).presheaf (op U) a

/-- Restriction along a composite `W ⟶ V ⟶ U` is the composite of the restrictions. -/
theorem specRestrictₗ_comp {U V W : (Spec R).Opens} (i : V ⟶ U) (j : W ⟶ V) (a : Γ(Spec R, U)) :
    specRestrictₗ (R := R) (j ≫ i) a = specRestrictₗ j (specRestrictₗ i a) := by
  simpa only [specRestrictₗ_apply, op_comp] using
    CategoryTheory.Functor.map_comp_apply (Spec R).presheaf i.op j.op a

/-! ### The base-change presheaf -/

/-- The presheaf of abelian groups `U ↦ 𝒪(U) ⊗_R N` on `Spec R`. -/
def presheafAb : ((Spec R).Opens)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (Γ(Spec R, U.unop) ⊗[R] N)
  map {_ _} i := AddCommGrpCat.ofHom
    (LinearMap.rTensor N (specRestrictₗ (R := R) i.unop)).toAddMonoidHom
  map_id U := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    induction x using TensorProduct.inductionOn with
    | tmul a n => exact congrArg (fun b => b ⊗ₜ[R] n) (specRestrictₗ_id (R := R) U.unop a)
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp {_ _ _} i j := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    induction x using TensorProduct.inductionOn with
    | tmul a n => exact congrArg (fun b => b ⊗ₜ[R] n) (specRestrictₗ_comp i.unop j.unop a)
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The sections `𝒪(U) ⊗_R N` of `presheafAb N` form a module over `𝒪(U)`, acting on the left
factor. -/
instance presheafAbModule (U : ((Spec R).Opens)ᵒᵖ) :
    Module ((Spec R).ringCatSheaf.obj.obj U) ((presheafAb N).obj U) :=
  inferInstanceAs (Module Γ(Spec R, U.unop) (Γ(Spec R, U.unop) ⊗[R] N))

/-- The restriction maps of the base-change presheaf are semilinear over the restriction maps
of the structure sheaf. -/
theorem rTensor_smul {U V : (Spec R).Opens} (i : V ⟶ U) (a : Γ(Spec R, U))
    (y : Γ(Spec R, U) ⊗[R] N) :
    LinearMap.rTensor (N : Type u) (specRestrictₗ (R := R) i) (a • y) =
      specRestrictₗ (R := R) i a •
        LinearMap.rTensor (N : Type u) (specRestrictₗ (R := R) i) y := by
  induction y using TensorProduct.inductionOn with
  | tmul b n =>
      rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        TensorProduct.smul_tmul']
      exact congrArg (fun c => c ⊗ₜ[R] (n : N)) (specRestrictₗ_mul i a b)
  | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]

/-- **The base-change presheaf of an `R`-module on `Spec R`**: the presheaf of
`𝒪_{Spec R}`-modules whose sections over `U` are `𝒪(U) ⊗_R N`. -/
def presheaf : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (presheafAb N) fun {_ _} i a x => rTensor_smul N i.unop a x

/-- The sections of `presheaf N` over `U` are `𝒪(U) ⊗_R N`. -/
@[simp]
theorem presheaf_obj (U : ((Spec R).Opens)ᵒᵖ) :
    ((presheaf N).obj U : Type u) = (Γ(Spec R, U.unop) ⊗[R] N) := rfl

/-- The restriction maps of `presheaf N` send `a ⊗ n` to `a|_V ⊗ n`. -/
theorem presheaf_map {U V : ((Spec R).Opens)ᵒᵖ} (i : U ⟶ V) (a : Γ(Spec R, U.unop)) (n : N) :
    (presheaf N).map i (a ⊗ₜ[R] n) = (specRestrictₗ (R := R) i.unop a) ⊗ₜ[R] n := rfl

/-! ### The comparison with the associated sheaf -/

/-- `AlgebraicGeometry.tilde.toOpen` as an `R`-linear map into the sections of `Ñ`. -/
def toOpenₗ (U : (Spec R).Opens) : N →ₗ[R] Γ(tilde N, U) := (tilde.toOpen N U).hom

/-- Restricting `toOpenₗ N U n` to `V` gives `toOpenₗ N V n`. -/
theorem toOpenₗ_res {U V : (Spec R).Opens} (i : V ⟶ U) (n : N) :
    (tilde N).val.presheaf.map i.op (toOpenₗ N U n) = toOpenₗ N V n := rfl

/-- **The comparison map on sections.** The base change of `N` to `𝒪(U)` maps to the sections of
the associated sheaf by `a ⊗ n ↦ a • (toOpen N U) n`. -/
def toTildeₗ (U : (Spec R).Opens) :
    Γ(Spec R, U) ⊗[R] N →ₗ[Γ(Spec R, U)] Γ(tilde N, U) :=
  (toOpenₗ N U).liftBaseChange Γ(Spec R, U)

/-- `toTildeₗ N U` sends `a ⊗ n` to `a • toOpenₗ N U n`. -/
@[simp]
theorem toTildeₗ_tmul (U : (Spec R).Opens) (a : Γ(Spec R, U)) (n : N) :
    toTildeₗ N U (a ⊗ₜ[R] n) = a • toOpenₗ N U n := rfl

/-- A restriction map of `Ñ`, as an additive map whose target type is written as the module of
sections rather than as a restriction of scalars. -/
def tildeRestrict {U V : (Spec R).Opens} (i : V ⟶ U) : Γ(tilde N, U) →+ Γ(tilde N, V) :=
  AddMonoidHom.mk' (fun x => (tilde N).val.map i.op x)
    fun x y => map_add ((tilde N).val.map i.op).hom x y

/-- The maps `toTildeₗ N U` commute with the restriction maps of `𝒪(-) ⊗_R N` and of `Ñ`. -/
theorem toTildeₗ_naturality {U V : (Spec R).Opens} (i : V ⟶ U) (x : Γ(Spec R, U) ⊗[R] N) :
    tildeRestrict N i (toTildeₗ N U x) =
      toTildeₗ N V (LinearMap.rTensor (N : Type u) (specRestrictₗ (R := R) i) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a n =>
      rw [toTildeₗ_tmul, LinearMap.rTensor_tmul, toTildeₗ_tmul]
      exact ((tilde N).val.map_smul i.op a (toOpenₗ N U n)).trans rfl
  | add x y hx hy =>
      rw [map_add (toTildeₗ N U), map_add (tildeRestrict N i), hx, hy,
        map_add (LinearMap.rTensor (N : Type u) (specRestrictₗ (R := R) i)),
        map_add (toTildeₗ N V)]

/-- The maps `toTildeₗ N U` commute with the restriction maps of `presheaf N` and of `Ñ`. -/
theorem toTildeₗ_naturality' {U V : (Spec R).Opens} (i : V ⟶ U) (x : (presheaf N).obj (op U)) :
    toTildeₗ N V ((presheaf N).map i.op x) = tildeRestrict N i (toTildeₗ N U x) :=
  (toTildeₗ_naturality N i x).symm

/-- **The comparison morphism.** The base-change presheaf of `N` maps to the underlying presheaf
of the associated sheaf `Ñ`. -/
def toTilde : presheaf N ⟶ (tilde N).val :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (toTildeₗ N U.unop).toAddMonoidHom
      naturality := fun {_ _} i => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
        (toTildeₗ_naturality N i.unop x).symm) }
    fun U a x => (toTildeₗ N U.unop).map_smul a x

/-- The component of `toTilde N` at `U` is `toTildeₗ N U`. -/
theorem toTilde_app (U : ((Spec R).Opens)ᵒᵖ) (x : Γ(Spec R, U.unop) ⊗[R] N) :
    PresheafOfModules.Hom.app (toTilde N) U x = toTildeₗ N U.unop x := rfl

/-! ### Functoriality -/

section Functoriality

variable {N N' : ModuleCat.{u} R} (f : N ⟶ N')

/-- Functoriality of the base-change presheaf in the module. -/
def presheafMapₗ (U : (Spec R).Opens) :
    Γ(Spec R, U) ⊗[R] N →ₗ[Γ(Spec R, U)] Γ(Spec R, U) ⊗[R] N' :=
  LinearMap.baseChange Γ(Spec R, U) f.hom

/-- `presheafMapₗ f U` sends `a ⊗ n` to `a ⊗ f n`. -/
@[simp]
theorem presheafMapₗ_tmul (U : (Spec R).Opens) (a : Γ(Spec R, U)) (n : N) :
    presheafMapₗ f U (a ⊗ₜ[R] n) = a ⊗ₜ[R] f n := by
  simp [presheafMapₗ]

/-- The maps `presheafMapₗ f U` commute with the restriction maps of the base-change
presheaves. -/
theorem presheafMapₗ_naturality {U V : (Spec R).Opens} (i : V ⟶ U) (x : Γ(Spec R, U) ⊗[R] N) :
    LinearMap.rTensor (N' : Type u) (specRestrictₗ (R := R) i) (presheafMapₗ f U x) =
      presheafMapₗ f V (LinearMap.rTensor (N : Type u) (specRestrictₗ (R := R) i) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a n => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- Functoriality of the base-change presheaf in the module, as a morphism of presheaves of
`𝒪_{Spec R}`-modules. -/
def presheafMap : presheaf N ⟶ presheaf N' :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (presheafMapₗ f U.unop).toAddMonoidHom
      naturality := fun {_ _} i => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
        (presheafMapₗ_naturality f i.unop x).symm) }
    fun U a x => (presheafMapₗ f U.unop).map_smul a x

/-- The component of `presheafMap f` at `U` is `presheafMapₗ f U`. -/
theorem presheafMap_app (U : ((Spec R).Opens)ᵒᵖ) (x : Γ(Spec R, U.unop) ⊗[R] N) :
    PresheafOfModules.Hom.app (presheafMap f) U x = presheafMapₗ f U.unop x := rfl

/-- `tilde.map f` on sections, as a linear map over the sections of the structure sheaf. -/
def tildeMapₗ (U : (Spec R).Opens) : Γ(tilde N, U) →ₗ[Γ(Spec R, U)] Γ(tilde N', U) :=
  ((tilde.map f).val.app (op U)).hom

/-- `tildeMapₗ f U` sends `toOpenₗ N U n` to `toOpenₗ N' U (f n)`. -/
theorem tildeMapₗ_toOpenₗ (U : (Spec R).Opens) (n : N) :
    tildeMapₗ f U (toOpenₗ N U n) = toOpenₗ N' U (f n) :=
  congrFun (congrArg (fun g => (ConcreteCategory.hom g : N → _)) (tilde.toOpen_map_app f U)) n

/-- **The comparison is natural in the module.** -/
theorem toTildeₗ_map (U : (Spec R).Opens) (x : Γ(Spec R, U) ⊗[R] N) :
    tildeMapₗ f U (toTildeₗ N U x) = toTildeₗ N' U (presheafMapₗ f U x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a n =>
      rw [presheafMapₗ_tmul, toTildeₗ_tmul, toTildeₗ_tmul, map_smul, tildeMapₗ_toOpenₗ]
  | add x y hx hy =>
      rw [map_add (toTildeₗ N U), map_add (tildeMapₗ f U), hx, hy,
        map_add (presheafMapₗ f U), map_add (toTildeₗ N' U)]

/-- The components of `toTilde` commute with `presheafMap f` and `tilde.map f`. -/
theorem toTilde_map_app (U : ((Spec R).Opens)ᵒᵖ) (x : Γ(Spec R, U.unop) ⊗[R] N) :
    (tilde.map f).val.app U (PresheafOfModules.Hom.app (toTilde N) U x) =
      PresheafOfModules.Hom.app (toTilde N') U
        (PresheafOfModules.Hom.app (presheafMap f) U x) :=
  toTildeₗ_map f U.unop x

end Functoriality

/-! ### Local bijectivity -/

/-- **The comparison is bijective on a basic open.** Over `D(f)` it is the base-change
identification `R_f ⊗_R N ≅ N_f`. -/
theorem bijective_toTildeₗ_basicOpen (f : R) :
    Function.Bijective (toTildeₗ N (specBasicOpen f)) := by
  have hloc : IsLocalizedModule (Submonoid.powers f)
      (toOpenₗ N (specBasicOpen f)) :=
    inferInstanceAs (IsLocalizedModule (Submonoid.powers f)
      (tilde.toOpen N (specBasicOpen f)).hom)
  have hbc : IsBaseChange Γ(Spec R, specBasicOpen f)
      (toOpenₗ N (specBasicOpen f)) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) _ _).1 hloc
  have heq : (hbc.equiv : Γ(Spec R, specBasicOpen f) ⊗[R] N →ₗ[_] _) =
      toTildeₗ N (specBasicOpen f) := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext fun a => LinearMap.ext fun n => ?_
    exact hbc.equiv_tmul a n
  exact heq ▸ hbc.equiv.bijective

/-- The comparison is surjective on a basic open. -/
theorem surjective_toTildeₗ_basicOpen (f : R) :
    Function.Surjective (toTildeₗ N (specBasicOpen f)) :=
  (bijective_toTildeₗ_basicOpen N f).2

/-- The comparison is injective on a basic open. -/
theorem injective_toTildeₗ_basicOpen (f : R) :
    Function.Injective (toTildeₗ N (specBasicOpen f)) :=
  (bijective_toTildeₗ_basicOpen N f).1

/-- Every point of an open of `Spec R` has a basic open neighbourhood inside it. -/
theorem exists_basicOpen_le {U : (Spec R).Opens} {x : ↥(Spec R)} (hx : x ∈ U) :
    ∃ f : R, x ∈ specBasicOpen f ∧
      specBasicOpen f ≤ U := by
  obtain ⟨V, ⟨g, rfl⟩, hxV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.1 PrimeSpectrum.isBasis_basic_opens) hx
  exact ⟨g, hxV, hVU⟩

/-- The comparison morphism `toTilde N` is locally surjective. -/
instance isLocallySurjective_toTilde :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥(Spec R)) (toTilde N) := by
  constructor
  intro U s
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨f, hxf, hfU⟩ := exists_basicOpen_le (U := U) hx
  exact ⟨specBasicOpen f, homOfLE hfU, surjective_toTildeₗ_basicOpen N f _, hxf⟩

/-- The comparison morphism `toTilde N` is locally injective. -/
instance isLocallyInjective_toTilde :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology ↥(Spec R)) (toTilde N) := by
  constructor
  intro U a b hab
  have hab' : toTildeₗ N U.unop a = toTildeₗ N U.unop b := hab
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨f, hxf, hfU⟩ := exists_basicOpen_le (U := U.unop) hx
  refine ⟨specBasicOpen f, homOfLE hfU, ?_, hxf⟩
  have key : toTildeₗ N (specBasicOpen f) ((presheaf N).map (homOfLE hfU).op a) =
      toTildeₗ N (specBasicOpen f) ((presheaf N).map (homOfLE hfU).op b) := by
    rw [toTildeₗ_naturality' N (homOfLE hfU) a, toTildeₗ_naturality' N (homOfLE hfU) b, hab']
  exact injective_toTildeₗ_basicOpen N f key

end Stacks.AffineBaseChange
